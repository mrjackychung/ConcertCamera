package com.concertcam

import android.Manifest
import android.app.Activity
import android.app.AlertDialog
import android.content.ClipData
import android.content.ClipboardManager
import android.content.pm.PackageManager
import android.content.res.Configuration
import android.graphics.Bitmap
import android.graphics.Color
import android.graphics.PointF
import android.graphics.Typeface
import android.graphics.drawable.GradientDrawable
import android.hardware.Sensor
import android.hardware.SensorEvent
import android.hardware.SensorEventListener
import android.hardware.SensorManager
import android.hardware.camera2.CameraCharacteristics
import android.hardware.camera2.CameraManager
import android.hardware.camera2.CameraMetadata
import android.media.MediaRecorder
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.os.SystemClock
import android.util.Size
import android.view.GestureDetector
import android.view.HapticFeedbackConstants
import android.view.Gravity
import android.view.MotionEvent
import android.view.ScaleGestureDetector
import android.view.TextureView
import android.view.View
import android.view.WindowManager
import android.widget.Button
import android.widget.FrameLayout
import android.widget.HorizontalScrollView
import android.widget.LinearLayout
import android.widget.ScrollView
import android.widget.SeekBar
import android.widget.TextView
import android.widget.Toast
import kotlin.math.abs
import kotlin.math.hypot
import kotlin.math.ln
import kotlin.math.min
import kotlin.math.pow
import kotlin.math.roundToInt
import kotlin.math.sqrt

class MainActivity : Activity(), SensorEventListener {

    // ===== 可调参数 =====
    private val STABLE = 0.25f           // 角速度低于此值(rad/s)算"稳定对准"
    private val LOCK_AFTER_MS = 5000f    // 稳定多久后自动锁定
    private val PAN_ANGLE = 0.26f        // 净转动超过约15°算"换目标"
    private val RELOCK_SETTLE_MS = 3000f // 换目标后稳定多久才解锁重新对焦
    private val CLIP_HI = 0.05f          // 高光溢出比例超过此值就压曝光
    private val SHUTTERS = intArrayOf(30, 50, 60, 100, 125, 250, 500, 1000, 2000, 4000)

    private data class Lens(val label: String, val openId: String, val phys: String?, val nz: Float, val soft: Boolean = false)
    private class Stat(val mean: Float, val clip: Float)

    private lateinit var cm: CameraManager
    private lateinit var sm: SensorManager
    private lateinit var root: FrameLayout
    private lateinit var mainTv: TextureView
    private lateinit var pipTv: TextureView
    private lateinit var lensBadge: TextView
    private lateinit var recPill: TextView
    private lateinit var afPill: TextView
    private lateinit var expPill: TextView
    private lateinit var lockBox: FrameLayout
    private lateinit var expHead: TextView
    private lateinit var expNote: TextView
    private lateinit var bAutoExp: Button
    private var lastLensName = ""
    private var dragging = false
    private val lensInfo = mutableMapOf<String, Pair<String, Float>>()
    private lateinit var ring: View
    private lateinit var zoomRail: ZoomRail
    private lateinit var expPanel: LinearLayout
    private lateinit var evRow: LinearLayout
    private lateinit var shRow: LinearLayout
    private lateinit var isoRow: LinearLayout
    private lateinit var evLabel: TextView
    private lateinit var shLabel: TextView
    private lateinit var isoLabel: TextView
    private lateinit var evBar: SeekBar
    private lateinit var shBar: SeekBar
    private lateinit var isoBar: SeekBar
    private lateinit var bRec: Button
    private lateinit var bMode: Button
    private lateinit var bGear: Button
    private lateinit var fan: FrameLayout
    private class FanItem(val title: String, val state: () -> String,
                          val opts: () -> List<Pair<String, () -> Unit>> = { emptyList() },
                          val act: (() -> Unit)? = null)
    private val fanItems = mutableListOf<FanItem>()
    private val fanViews = mutableListOf<Button>()
    private val hidePanel = Runnable { expPanel.visibility = View.GONE }

    private val ui = Handler(Looper.getMainLooper())
    private val cams = mutableListOf<Cam>()
    private val lenses = mutableListOf<Lens>()
    private val ex = Expo()
    private var frontId: String? = null
    private var allIds = listOf<String>()

    private var lensIdx = 0
    private var mode = 0            // 0 后置 1 前置 2 前后同录
    private var res4k = false
    private var stab = 1
    private var recording = false
    private var auto = true
    private var recStart = 0L
    private var askedPerm = false
    private var lastErr = "无"
    private var lw = 0; private var lh = 0; private var lPortrait: Boolean? = null
    private var bmp: Bitmap? = null
    private var recover = 0

    // 陀螺仪状态
    private var last = 0L
    private var ema = 0f
    private var vx = 0f; private var vy = 0f; private var vz = 0f
    private var stableMs = 0f
    private var settleMs = 0f
    private var moved = false

    private val startRunnable = Runnable { startAll() }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        window.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)
        cm = getSystemService(CAMERA_SERVICE) as CameraManager
        sm = getSystemService(SENSOR_SERVICE) as SensorManager
        scanLenses()
        buildUi()
    }

    private fun dp(v: Int) = (v * resources.displayMetrics.density).toInt()
    private fun chars(id: String) = cm.getCameraCharacteristics(id)

    // ===================== 镜头扫描 =====================
    private fun eqMm(c: CameraCharacteristics): Int {
        val f = c.get(CameraCharacteristics.LENS_INFO_AVAILABLE_FOCAL_LENGTHS)?.firstOrNull() ?: return 0
        val s = c.get(CameraCharacteristics.SENSOR_INFO_PHYSICAL_SIZE) ?: return 0
        return Math.round(f * 43.27f / hypot(s.width, s.height))
    }

    private fun valid(c: CameraCharacteristics): Boolean {
        val caps = c.get(CameraCharacteristics.REQUEST_AVAILABLE_CAPABILITIES) ?: return false
        if (!caps.contains(CameraMetadata.REQUEST_AVAILABLE_CAPABILITIES_BACKWARD_COMPATIBLE)) return false
        return c.get(CameraCharacteristics.SCALER_STREAM_CONFIGURATION_MAP)
            ?.getOutputSizes(MediaRecorder::class.java)?.isNotEmpty() == true
    }

    private fun lensName(r: Float) = if (r < 0.8f) "超广角" else if (r < 1.6f) "主摄" else "长焦"
    private fun fmtX(v: Float) = if (abs(v - v.roundToInt()) < 0.05f) "${v.roundToInt()}x" else "%.1fx".format(v)

    private fun lensLabel(eq: Int, ref: Int, tag: String): Pair<String, Float> {
        val r = if (eq == 0 || ref == 0) 1f else eq.toFloat() / ref
        val name = if (r < 0.8f) "超广角" else if (r < 1.6f) "主摄" else "长焦"
        return Pair("$name %.1fx (%s) %dmm".format(r, tag, eq), r)
    }

    private fun scanLenses() {
        val listed = cm.cameraIdList.toList()
        val hidden = (0..9).map { it.toString() }.filter { it !in listed }.filter {
            try { chars(it); true } catch (_: Exception) { false }
        }
        allIds = listed + hidden
        frontId = allIds.firstOrNull {
            val c = chars(it)
            c.get(CameraCharacteristics.LENS_FACING) == CameraCharacteristics.LENS_FACING_FRONT && valid(c)
        }
        val backs = allIds.filter {
            val c = chars(it)
            c.get(CameraCharacteristics.LENS_FACING) == CameraCharacteristics.LENS_FACING_BACK && valid(c)
        }
        val physSet = backs.flatMap { chars(it).physicalCameraIds }.toSet()
        val ref = backs.firstOrNull { it !in physSet }?.let { eqMm(chars(it)) } ?: 0
        fun ratio(e: Int) = if (e == 0 || ref == 0) 1f else e.toFloat() / ref
        for (id in backs) {
            val r0 = ratio(eqMm(chars(id)))
            lensInfo[id] = lensName(r0) to r0
            for (pp in chars(id).physicalCameraIds) try {
                val r1 = ratio(eqMm(chars(pp))); lensInfo[pp] = lensName(r1) to r1
            } catch (_: Exception) {}
        }
        for (id in backs) {
            if (id in physSet) continue
            val c = chars(id)
            val zr = c.get(CameraCharacteristics.CONTROL_ZOOM_RATIO_RANGE)
            val items = c.physicalCameraIds.mapNotNull { p ->
                try { p to eqMm(chars(p)) } catch (_: Exception) { null }
            }.sortedBy { it.second }
            if (items.isEmpty()) {
                lenses += Lens(lensLabel(eqMm(c), ref, "ID$id").first, id, null, 1f)
                continue
            }
            for ((p, e) in items) {
                if (p in backs) {
                    lenses += Lens(lensLabel(e, ref, "直连ID$p").first, p, null, 1f)
                } else {
                    val (label, r) = lensLabel(e, ref, "物理流$p")
                    val nz = if (zr == null) 1f else r.coerceIn(zr.lower, zr.upper)
                    lenses += Lens(label, id, p, nz)
                }
            }
            lenses += Lens("系统镜头·软锁1x (ID$id)", id, null, 1f, true)
        }
        for (id in backs) if (id in physSet && lenses.none { it.openId == id })
            lenses += Lens(lensLabel(eqMm(chars(id)), ref, "直连ID$id").first, id, null, 1f)
        lensIdx = lenses.indexOfFirst { it.label.startsWith("主摄") }.coerceAtLeast(0)
    }

    // ===================== 界面（竖屏优先） =====================
    private fun bg(color: Int, r: Int) = GradientDrawable().apply { setColor(color); cornerRadius = dp(r).toFloat() }

    private fun chip(txt: String = "", click: () -> Unit) = Button(this).apply {
        textSize = 12f; isAllCaps = false; setTextColor(Color.WHITE)
        background = bg(Color.argb(150, 50, 50, 50), 18)
        minHeight = 0; minimumHeight = 0; minWidth = 0; minimumWidth = 0
        setPadding(dp(12), 0, dp(12), 0)
        text = txt
        setOnClickListener { click() }
    }

    private fun sRow(l: TextView, b: SeekBar) = LinearLayout(this).apply {
        orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL
        addView(l, LinearLayout.LayoutParams(dp(104), -2))
        addView(b, LinearLayout.LayoutParams(0, -2, 1f))
    }

    private fun label() = TextView(this).apply { setTextColor(Color.WHITE); textSize = 12f }

    private fun onBar(bar: SeekBar, f: (Int) -> Unit) = bar.setOnSeekBarChangeListener(object : SeekBar.OnSeekBarChangeListener {
        override fun onProgressChanged(s: SeekBar, p: Int, user: Boolean) { if (user) { touchExp(); f(p) } }
        override fun onStartTrackingTouch(s: SeekBar) { dragging = true }
        override fun onStopTrackingTouch(s: SeekBar) { dragging = false }
    })

    private fun buildUi() {
        root = FrameLayout(this).apply { setBackgroundColor(Color.BLACK) }
        mainTv = TextureView(this)
        root.addView(mainTv)
        pipTv = TextureView(this).apply { visibility = View.GONE }
        root.addView(pipTv, FrameLayout.LayoutParams(dp(90), dp(160), Gravity.TOP or Gravity.END).apply {
            setMargins(0, dp(40), dp(10), 0)
        })
        fun pill(sp: Float, bold: Boolean = false) = TextView(this).apply {
            setTextColor(Color.WHITE); textSize = sp
            background = bg(Color.argb(150, 0, 0, 0), 14)
            setPadding(dp(10), dp(4), dp(10), dp(4))
            if (bold) typeface = Typeface.DEFAULT_BOLD
        }
        lensBadge = pill(20f, true)       // 当前镜头：最醒目
        root.addView(lensBadge, FrameLayout.LayoutParams(-2, -2, Gravity.TOP or Gravity.CENTER_HORIZONTAL).apply { topMargin = dp(34) })
        recPill = pill(13f, true).apply { setTextColor(Color.rgb(255, 90, 90)); visibility = View.GONE }
        afPill = pill(12f)
        expPill = pill(12f).apply { setOnClickListener { togglePanel() } }   // 点它展开曝光滑杆
        root.addView(LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            listOf(recPill, afPill, expPill).forEach { addView(it, LinearLayout.LayoutParams(-2, -2).apply { bottomMargin = dp(4) }) }
        }, FrameLayout.LayoutParams(-2, -2, Gravity.TOP or Gravity.START).apply { setMargins(dp(10), dp(34), 0, 0) })
        // 对焦锁定框（类似苹果的黄框）：锁定时显示在对焦点
        lockBox = FrameLayout(this).apply {
            background = GradientDrawable().apply { setStroke(dp(2), Color.YELLOW); setColor(Color.TRANSPARENT) }
            visibility = View.GONE
            addView(TextView(this@MainActivity).apply { text = "🔒 锁定"; setTextColor(Color.YELLOW); textSize = 11f },
                FrameLayout.LayoutParams(-2, -2, Gravity.BOTTOM or Gravity.CENTER_HORIZONTAL))
        }
        root.addView(lockBox, FrameLayout.LayoutParams(dp(76), dp(76)))
        ring = View(this).apply {
            background = GradientDrawable().apply { shape = GradientDrawable.OVAL; setStroke(dp(2), Color.YELLOW); setColor(Color.TRANSPARENT) }
            visibility = View.GONE
        }
        root.addView(ring, FrameLayout.LayoutParams(dp(64), dp(64)))

        // ---- 曝光面板 ----
        evLabel = label(); shLabel = label(); isoLabel = label()
        evBar = SeekBar(this); shBar = SeekBar(this); isoBar = SeekBar(this).apply { max = 100 }
        evRow = sRow(evLabel, evBar); shRow = sRow(shLabel, shBar); isoRow = sRow(isoLabel, isoBar)
        expHead = label().apply { textSize = 13f; typeface = Typeface.DEFAULT_BOLD }
        bAutoExp = chip("恢复自动") { setExpMode(0) }
        expNote = label().apply {
            setTextColor(Color.rgb(255, 190, 120)); visibility = View.GONE
            text = "本机相机不开放手动 ISO / 快门（系统限制），只能调曝光补偿"
        }
        val head = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL
            addView(expHead, LinearLayout.LayoutParams(0, -2, 1f))
            addView(bAutoExp, LinearLayout.LayoutParams(-2, dp(30)))
        }
        expPanel = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL; visibility = View.GONE
            addView(head); addView(evRow); addView(shRow); addView(isoRow); addView(expNote)
        }
        // 拖哪一项就切到对应的控制方式：拖EV=自动曝光；拖快门=快门优先；拖ISO=手动
        onBar(evBar) { p ->
            val c = curChars() ?: return@onBar
            val r = c.get(CameraCharacteristics.CONTROL_AE_COMPENSATION_RANGE) ?: return@onBar
            if (ex.mode == 2) ex.mode = 0
            ex.ev = (r.lower + p) * Cam.evStep(c); ex.off = 0f
            applyExp(); updRows()
        }
        onBar(shBar) { p ->
            if (cams.firstOrNull()?.manualOk != true) return@onBar
            if (ex.mode == 0) { seedFromActual(); ex.mode = 1 }
            ex.shutterDen = SHUTTERS[p]
            applyExp(); updRows()
        }
        onBar(isoBar) { p ->
            val ir = curChars()?.get(CameraCharacteristics.SENSOR_INFO_SENSITIVITY_RANGE) ?: return@onBar
            if (cams.firstOrNull()?.manualOk != true) return@onBar
            if (ex.mode == 0) seedFromActual()
            ex.mode = 2
            ex.iso = progToIso(p, ir.lower, ir.upper)
            applyExp(); updRows()
        }

        // ---- 右侧操作条（单手拇指区） ----
        zoomRail = ZoomRail(this).apply {
            onPreset = { z -> cams.firstOrNull()?.preset(z) }
            onFree = { z -> cams.firstOrNull()?.setZoom(z) }
        }
        bRec = Button(this).apply {
            textSize = 26f; setTextColor(Color.WHITE)
            background = GradientDrawable().apply { shape = GradientDrawable.OVAL; setColor(Color.rgb(220, 40, 40)); setStroke(dp(3), Color.WHITE) }
            setOnClickListener { toggleRec() }
        }
        bMode = chip { cycleMode() }
        bGear = chip("⚙ 设置") {}
        // 点击=打开菜单；长按后不抬手直接滑到图标上，放手即设置；悬停在带子菜单的图标上会展开下一层
        bGear.setOnTouchListener { v, e ->
            when (e.actionMasked) {
                MotionEvent.ACTION_DOWN -> { v.parent.requestDisallowInterceptTouchEvent(true); ui.postDelayed(gearLong, 350) }
                MotionEvent.ACTION_MOVE -> if (fanDragging) fanTouch(e.rawX, e.rawY, e.actionMasked)
                MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                    ui.removeCallbacks(gearLong)
                    if (fanDragging) fanTouch(e.rawX, e.rawY, e.actionMasked)
                    else if (e.actionMasked == MotionEvent.ACTION_UP) { if (fan.visibility == View.VISIBLE) closeFan() else openFanAtView(bGear) }
                }
            }
            true
        }
        val rail = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL; gravity = Gravity.CENTER_HORIZONTAL
            setPadding(dp(4), dp(8), dp(4), dp(8))
            addView(zoomRail, LinearLayout.LayoutParams(dp(72), dp(240)))
            addView(bRec, LinearLayout.LayoutParams(dp(76), dp(76)).apply { setMargins(0, dp(14), 0, dp(14)) })
            addView(bMode, LinearLayout.LayoutParams(dp(72), dp(40)))
            addView(bGear, LinearLayout.LayoutParams(dp(72), dp(40)).apply { topMargin = dp(8) })
        }
        root.addView(ScrollView(this).apply { isVerticalScrollBarEnabled = false; addView(rail) },
            FrameLayout.LayoutParams(dp(84), -2, Gravity.END or Gravity.CENTER_VERTICAL))

        // 曝光滑杆面板：在操作条左边，拇指够得着，8秒无操作自动收起
        expPanel.background = bg(Color.argb(180, 0, 0, 0), 14)
        expPanel.setPadding(dp(10), dp(8), dp(10), dp(8))
        root.addView(expPanel, FrameLayout.LayoutParams(dp(300), -2, Gravity.END or Gravity.CENTER_VERTICAL).apply { rightMargin = dp(88) })

        // ---- 扇形菜单项（精简为5项；有子选项的，悬停/点击会展开下一层） ----
        if (lenses.size > 1) fanItems += FanItem("镜头", { lenses.getOrNull(lensIdx)?.label?.substringBefore(" (") ?: "无" },
            { lenses.mapIndexed { i, l -> o(l.label.substringBefore(" (")) { setLens(i) } } })
        fanItems += FanItem("画质", { if (res4k) "4K" else "1080p" }, { listOf(o("1080p") { setRes(false) }, o("4K") { setRes(true) }) })
        fanItems += FanItem("防抖", { stabNames[stab.coerceIn(0, 3)] },
            { (curChars()?.let { Cam.stabModes(it) } ?: listOf(0)).map { m -> o(stabNames[m]) { setStab(m) } } })
        fanItems += FanItem("曝光", { expNames[ex.mode] }, act = { togglePanel() })
        fanItems += FanItem("锁焦", { if (cams.firstOrNull()?.locked == true) "锁定" else if (auto) "自动" else "关" },
            { listOf(
                o("自动") { auto = true; cams.firstOrNull()?.setLock(false); resetGyro() },
                o("锁定") { cams.firstOrNull()?.setLock(true) },
                o("关") { auto = false; cams.firstOrNull()?.setLock(false); resetGyro() }) })
        fan = FrameLayout(this).apply {
            setBackgroundColor(Color.argb(90, 0, 0, 0)); isClickable = true; visibility = View.GONE
            setOnClickListener { closeFan() }
        }
        root.addView(fan, FrameLayout.LayoutParams(-1, -1))

        // ---- 手势：双指缩放 + 单击对焦/测光 ----
        val sd = ScaleGestureDetector(this, object : ScaleGestureDetector.SimpleOnScaleGestureListener() {
            override fun onScale(d: ScaleGestureDetector): Boolean {
                cams.firstOrNull()?.let { it.setZoom(it.zoom * d.scaleFactor) }
                return true
            }
        })
        val gd = GestureDetector(this, object : GestureDetector.SimpleOnGestureListener() {
            override fun onLongPress(e: MotionEvent) { openFan(e.x, e.y); fanDragging = true }

            override fun onSingleTapUp(e: MotionEvent): Boolean {
                val u = (e.x - mainTv.x) / mainTv.width
                val v = (e.y - mainTv.y) / mainTv.height
                if (u in 0f..1f && v in 0f..1f) {
                    cams.firstOrNull()?.tapFocus(u, v)
                    ex.off = 0f; resetGyro()
                    showRing(e.x, e.y)
                }
                return true
            }
        })
        root.setOnTouchListener { _, e ->
            if (fanDragging) fanTouch(e.rawX, e.rawY, e.actionMasked)
            else { sd.onTouchEvent(e); if (!sd.isInProgress) gd.onTouchEvent(e) }
            true
        }
        setContentView(root)
        root.addOnLayoutChangeListener { _, _, _, _, _, _, _, _, _ -> root.post { layoutMain() } }
        refreshUi()
        ui.post(object : Runnable { override fun run() { tick(); ui.postDelayed(this, 250) } })
        ui.post(object : Runnable { override fun run() { autoExposure(); ui.postDelayed(this, 300) } })
    }

    private fun showRing(x: Float, y: Float) {
        ring.animate().cancel()
        ring.translationX = x - dp(32); ring.translationY = y - dp(32)
        ring.alpha = 1f; ring.visibility = View.VISIBLE
        ring.animate().alpha(0f).setDuration(1200).withEndAction { ring.visibility = View.GONE }.start()
    }

    /** 竖屏：预览9:16贴顶，下方放控制面板；横屏：16:9居中 */
    private fun layoutMain() {
        val w = root.width; val hh = root.height
        if (w == 0 || hh == 0) return
        val portrait = hh > w
        var tw: Int; var th: Int
        if (portrait) { tw = w; th = w * 16 / 9; if (th > hh) { th = hh; tw = th * 9 / 16 } }
        else { tw = w; th = w * 9 / 16; if (th > hh) { th = hh; tw = th * 16 / 9 } }
        if (tw != lw || th != lh || portrait != lPortrait) {
            lw = tw; lh = th; lPortrait = portrait
            mainTv.layoutParams = FrameLayout.LayoutParams(tw, th, Gravity.CENTER)
            (pipTv.layoutParams as FrameLayout.LayoutParams).apply {
                width = if (portrait) dp(90) else dp(200); height = if (portrait) dp(160) else dp(113)
                pipTv.layoutParams = this
            }
        }
        ui.postDelayed({ cams.forEach { it.applyTransform() } }, 150)
    }

    override fun onConfigurationChanged(c: Configuration) {
        super.onConfigurationChanged(c)
        root.post { layoutMain() }
        ui.postDelayed({ cams.forEach { it.applyTransform() } }, 300)
    }

    private fun stabName() = listOf("防抖:关", "防抖:光学", "防抖:光学+电子", "防抖:增强")[stab.coerceIn(0, 3)]

    private fun refreshUi() {
        bRec.text = if (recording) "■" else "●"
        bMode.text = listOf("后置", "前置", "前后同录")[mode]
        if (fan.visibility == View.VISIBLE) refreshFan()
    }

    // ===================== 扇形菜单（点击 / 长按滑动选择 / 悬停展开下一层） =====================
    private val stabNames = listOf("关", "光学", "光学+电", "增强")
    private val expNames = listOf("自动", "快门优先", "手动")
    private val fanPos = mutableListOf<PointF>()
    private val subViews = mutableListOf<Button>()
    private val subPos = mutableListOf<PointF>()
    private val subOpts = mutableListOf<Pair<String, () -> Unit>>()
    private var fanAx = 0f; private var fanAy = 0f
    private var fanDragging = false
    private var hoverMain = -1; private var hoverSub = -1; private var subOf = -1
    private val dwell = Runnable { if (hoverMain >= 0 && hoverMain != subOf && fanItems[hoverMain].opts().isNotEmpty()) openSub(hoverMain) }
    private val gearLong = Runnable { openFanAtView(bGear); fanDragging = true }

    private fun o(label: String, f: () -> Unit): Pair<String, () -> Unit> = label to f
    private fun applyExp() { cams.firstOrNull()?.applyExposure() }

    private fun styleBtn(b: Button, hovered: Boolean, selected: Boolean, dim: Boolean) {
        b.background = GradientDrawable().apply {
            shape = GradientDrawable.OVAL
            setColor(if (hovered) Color.argb(245, 80, 70, 10) else Color.argb(225, 30, 30, 30))
            setStroke(dp(if (hovered || selected) 3 else 1),
                if (hovered) Color.YELLOW else if (selected) Color.rgb(90, 200, 255) else Color.WHITE)
        }
        val sc = if (hovered) 1.25f else 1f
        b.scaleX = sc; b.scaleY = sc
        b.alpha = if (dim) 0.4f else 1f
    }

    private fun mkFanBtn(sp: Float) = Button(this).apply {
        isAllCaps = false; textSize = sp; setTextColor(Color.WHITE)
        setPadding(0, 0, 0, 0); minWidth = 0; minHeight = 0; minimumWidth = 0; minimumHeight = 0
    }

    private fun openFanAtView(v: View) {
        val a = IntArray(2); val r = IntArray(2)
        v.getLocationInWindow(a); root.getLocationInWindow(r)
        openFan(a[0] - r[0] + v.width / 2f, a[1] - r[1] + v.height / 2f)
    }

    /** 以(ax,ay)为圆心向屏幕内侧弹出两圈半圆扇形 */
    private fun openFan(ax: Float, ay: Float) {
        closeFan()
        root.performHapticFeedback(HapticFeedbackConstants.LONG_PRESS)
        fanAx = ax; fanAy = ay
        val leftDir = ax > root.width / 2f
        val sz = dp(62)
        val rad = dp(110).toFloat()
        val cnt = fanItems.size
        for (i in 0 until cnt) {
            val th = Math.toRadians(90.0 + i * 180.0 / maxOf(1, cnt - 1))
            val dx = (Math.cos(th) * rad).toFloat() * (if (leftDir) 1f else -1f)
            val dy = (-Math.sin(th) * rad).toFloat()
            val cx = (ax + dx).coerceIn(sz / 2f + dp(4), root.width - sz / 2f - dp(4))
            val cy = (ay + dy).coerceIn(sz / 2f + dp(40), root.height - sz / 2f - dp(8))
            val b = mkFanBtn(10.5f)
            b.setOnClickListener {
                val fi = fanItems[i]
                if (fi.opts().isNotEmpty()) { if (subOf == i) closeSub() else openSub(i) }
                else { fi.act?.invoke(); refreshFan() }
            }
            styleBtn(b, false, false, false)
            fan.addView(b, FrameLayout.LayoutParams(sz, sz).apply { leftMargin = (cx - sz / 2f).toInt(); topMargin = (cy - sz / 2f).toInt() })
            fanViews += b; fanPos += PointF(cx, cy)
            b.translationX = ax - cx; b.translationY = ay - cy; b.alpha = 0f; b.scaleX = 0.3f; b.scaleY = 0.3f
            b.animate().translationX(0f).translationY(0f).alpha(1f).scaleX(1f).scaleY(1f).setDuration(180).start()
        }
        fan.visibility = View.VISIBLE
        refreshFan()
    }

    /** 在某个图标外侧再弹出它的选项（下一层） */
    private fun openSub(i: Int) {
        closeSub()
        val fi = fanItems[i]
        val opts = fi.opts()
        if (opts.isEmpty()) { fi.act?.invoke(); refreshFan(); return }
        subOf = i
        val p = fanPos[i]
        val phi = Math.atan2((-(p.y - fanAy)).toDouble(), (p.x - fanAx).toDouble())
        val sz = dp(56); val rad = dp(92).toFloat()
        val n = opts.size
        val cur = fi.state()
        for ((k, op) in opts.withIndex()) {
            val th = phi + (k - (n - 1) / 2.0) * Math.toRadians(40.0)
            val cx = (p.x + (Math.cos(th) * rad).toFloat()).coerceIn(sz / 2f + dp(4), root.width - sz / 2f - dp(4))
            val cy = (p.y - (Math.sin(th) * rad).toFloat()).coerceIn(sz / 2f + dp(40), root.height - sz / 2f - dp(8))
            val b = mkFanBtn(11f)
            b.text = op.first
            b.setOnClickListener { op.second(); closeFan() }
            styleBtn(b, false, op.first == cur, false)
            fan.addView(b, FrameLayout.LayoutParams(sz, sz).apply { leftMargin = (cx - sz / 2f).toInt(); topMargin = (cy - sz / 2f).toInt() })
            subViews += b; subPos += PointF(cx, cy); subOpts += op
            b.translationX = p.x - cx; b.translationY = p.y - cy; b.alpha = 0f; b.scaleX = 0.3f; b.scaleY = 0.3f
            b.animate().translationX(0f).translationY(0f).alpha(1f).scaleX(1f).scaleY(1f).setDuration(150).start()
        }
        restyleMain()
    }

    private fun closeSub() {
        subViews.forEach { fan.removeView(it) }
        subViews.clear(); subPos.clear(); subOpts.clear()
        subOf = -1; hoverSub = -1
        if (fanViews.isNotEmpty()) restyleMain()
    }

    private fun restyleMain() {
        for ((i, b) in fanViews.withIndex()) styleBtn(b, i == hoverMain, i == subOf, subOf >= 0 && i != subOf && i != hoverMain)
    }

    private fun restyleSub() {
        val cur = if (subOf >= 0) fanItems[subOf].state() else ""
        for ((k, b) in subViews.withIndex()) styleBtn(b, k == hoverSub, subOpts[k].first == cur, false)
    }

    private fun hitTest(x: Float, y: Float): Pair<Boolean, Int>? {
        val rs = dp(34).toFloat(); val rm = dp(37).toFloat()
        for (k in subPos.indices) if (hypot(x - subPos[k].x, y - subPos[k].y) < rs) return Pair(true, k)
        for (i in fanPos.indices) if (hypot(x - fanPos[i].x, y - fanPos[i].y) < rm) return Pair(false, i)
        return null
    }

    /** 手指不抬起的滑动选择：移到图标上高亮，放手即设置；悬停约0.45秒展开下一层 */
    private fun fanTouch(rx: Float, ry: Float, action: Int) {
        val loc = IntArray(2); root.getLocationOnScreen(loc)
        val hit = hitTest(rx - loc[0], ry - loc[1])
        if (action == MotionEvent.ACTION_CANCEL) { fanDragging = false; return }
        if (action == MotionEvent.ACTION_UP) {
            fanDragging = false
            ui.removeCallbacks(dwell)
            if (hit == null) return                       // 空白处放手：菜单保持打开，可以再点
            if (hit.first) { subOpts[hit.second].second(); closeFan() }
            else {
                val fi = fanItems[hit.second]
                if (fi.opts().isNotEmpty()) openSub(hit.second) else { fi.act?.invoke(); closeFan() }
            }
            return
        }
        val nm = if (hit != null && !hit.first) hit.second else -1
        val ns = if (hit != null && hit.first) hit.second else -1
        if (nm != hoverMain) {
            hoverMain = nm
            ui.removeCallbacks(dwell)
            if (nm >= 0) { root.performHapticFeedback(HapticFeedbackConstants.CLOCK_TICK); ui.postDelayed(dwell, 450) }
            restyleMain()
        }
        if (ns != hoverSub) {
            hoverSub = ns
            if (ns >= 0) root.performHapticFeedback(HapticFeedbackConstants.CLOCK_TICK)
            restyleSub()
        }
    }

    private fun refreshFan() {
        for ((i, b) in fanViews.withIndex()) {
            val fi = fanItems[i]
            val st = fi.state()
            b.text = if (st.isEmpty()) fi.title else fi.title + "\n" + st
        }
    }

    private fun closeFan() {
        ui.removeCallbacks(dwell)
        fan.visibility = View.GONE
        fan.removeAllViews()
        fanViews.clear(); fanPos.clear(); subViews.clear(); subPos.clear(); subOpts.clear()
        subOf = -1; hoverMain = -1; hoverSub = -1; fanDragging = false
    }

    private fun touchExp() {
        if (expPanel.visibility == View.VISIBLE) { ui.removeCallbacks(hidePanel); ui.postDelayed(hidePanel, 8000) }
    }

    private fun showExp() { refreshSliders(); expPanel.visibility = View.VISIBLE; touchExp() }
    private fun togglePanel() { if (expPanel.visibility == View.VISIBLE) expPanel.visibility = View.GONE else showExp() }

    private fun toast(s: String) = runOnUiThread { Toast.makeText(this, s, Toast.LENGTH_LONG).show() }

    private fun curChars(): CameraCharacteristics? {
        val id = if (mode == 1) frontId else lenses.getOrNull(lensIdx)?.openId
        return id?.let { chars(it) }
    }

    // ===================== 曝光滑杆 =====================
    private fun nearestShutter(den: Int) = SHUTTERS.indices.minByOrNull { Math.abs(SHUTTERS[it] - den) } ?: 2
    private fun isoToProg(iso: Int, lo: Int, hi: Int) = (100 * ln(iso.toFloat() / lo) / ln(hi.toFloat() / lo)).toInt().coerceIn(0, 100)
    private fun progToIso(p: Int, lo: Int, hi: Int) = (lo * (hi.toFloat() / lo).pow(p / 100f)).toInt()

    /** 用当前实际曝光作为手动的起点（避免画面突然变亮变暗） */
    private fun seedFromActual() {
        val cam = cams.firstOrNull()
        cam?.resIso?.let { ex.iso = it }
        cam?.resExp?.let { if (it > 0) ex.shutterDen = SHUTTERS[nearestShutter((1e9 / it).toInt())] }
        shBar.progress = nearestShutter(ex.shutterDen)
        cam?.isoRange?.let { isoBar.progress = isoToProg(ex.iso, it.lower, it.upper) }
    }

    private fun updRows() {
        val cam = cams.firstOrNull()
        val manual = cam?.manualOk ?: false
        expHead.text = "曝光 · " + expNames[ex.mode]
        bAutoExp.visibility = if (ex.mode != 0) View.VISIBLE else View.GONE
        shRow.visibility = if (manual) View.VISIBLE else View.GONE
        isoRow.visibility = if (manual) View.VISIBLE else View.GONE
        expNote.visibility = if (manual) View.GONE else View.VISIBLE
        evRow.alpha = if (ex.mode == 2) 0.45f else 1f
        shRow.alpha = if (ex.mode == 0) 0.6f else 1f
        isoRow.alpha = if (ex.mode == 2) 1f else 0.6f
        val den = if (ex.mode == 0) (cam?.resExp?.let { if (it > 0) (1e9 / it).toInt() else null } ?: ex.shutterDen) else ex.shutterDen
        val iso = if (ex.mode == 0) (cam?.resIso ?: ex.iso) else ex.iso
        evLabel.text = "EV %+.1f".format(ex.ev)
        shLabel.text = "快门 1/$den" + if (ex.mode == 0) " 自动" else ""
        isoLabel.text = "ISO $iso" + if (ex.mode != 2) " 自动" else ""
    }

    private fun refreshSliders() {
        val c = curChars() ?: return
        c.get(CameraCharacteristics.CONTROL_AE_COMPENSATION_RANGE)?.let { r ->
            evBar.max = r.upper - r.lower
            evBar.progress = (Math.round(ex.ev / Cam.evStep(c)) - r.lower).coerceIn(0, evBar.max)
        }
        shBar.max = SHUTTERS.size - 1; shBar.progress = nearestShutter(ex.shutterDen)
        c.get(CameraCharacteristics.SENSOR_INFO_SENSITIVITY_RANGE)?.let { isoBar.progress = isoToProg(ex.iso, it.lower, it.upper) }
        updRows()
    }

    // ===================== 曝光自动化（舞台强光/激光） =====================
    private fun sampleLuma(): Stat? {
        val w = mainTv.width; val h = mainTv.height
        if (w == 0 || h == 0 || !mainTv.isAvailable) return null
        val bw = 48; val bh = (48f * h / w).toInt().coerceAtLeast(16)
        var b = bmp
        if (b == null || b.width != bw || b.height != bh) { b = Bitmap.createBitmap(bw, bh, Bitmap.Config.ARGB_8888); bmp = b }
        mainTv.getBitmap(b)
        val px = IntArray(bw * bh)
        b.getPixels(px, 0, bw, 0, 0, bw, bh)
        val u = if (ex.tapU >= 0f) ex.tapU else 0.5f
        val v = if (ex.tapV >= 0f) ex.tapV else 0.5f
        val spot = ex.spot
        val x0 = if (spot) ((u - 0.16f) * bw).toInt().coerceIn(0, bw - 1) else 0
        val x1 = if (spot) ((u + 0.16f) * bw).toInt().coerceIn(x0 + 1, bw) else bw
        val y0 = if (spot) ((v - 0.16f) * bh).toInt().coerceIn(0, bh - 1) else 0
        val y1 = if (spot) ((v + 0.16f) * bh).toInt().coerceIn(y0 + 1, bh) else bh
        var sum = 0L; var clip = 0; var n = 0
        for (y in y0 until y1) for (x in x0 until x1) {
            val p = px[y * bw + x]
            val l = (((p shr 16) and 255) * 299 + ((p shr 8) and 255) * 587 + (p and 255) * 114) / 1000
            sum += l; if (l >= 248) clip++; n++
        }
        return if (n == 0) null else Stat(sum.toFloat() / n, clip.toFloat() / n)
    }

    private fun autoExposure() {
        val cam = cams.firstOrNull() ?: return
        if (!cam.running) return
        if (ex.mode == 0) {
            if (!ex.protect || (cam.locked && ex.lockAe)) return
            val s = sampleLuma() ?: return
            var off = ex.off
            if (s.clip > CLIP_HI) off -= 0.33f
            else if (s.clip < 0.004f && off < 0f && ++recover % 4 == 0) off += 0.33f
            off = off.coerceIn(-3f, 0f)
            if (off != ex.off) { ex.off = off; cam.applyExposure() }
        } else if (ex.mode == 1) {
            val ir = cam.isoRange ?: return
            val s = sampleLuma() ?: return
            val target = 110f * 2f.pow(ex.ev / 2.2f)
            var iso = ex.iso.toFloat()
            if (s.clip > 0.04f || s.mean > target + 18f) iso *= if (s.clip > 0.12f) 0.7f else 0.9f
            else if (s.mean < target - 18f && s.clip < 0.01f) iso *= 1.1f
            val ni = iso.toInt().coerceIn(ir.lower, ir.upper)
            if (ni != ex.iso) { ex.iso = ni; cam.applyExposure() }
        }
    }

    // ===================== 控制逻辑 =====================
    private fun buildPresets() {
        val r = curChars()?.get(CameraCharacteristics.CONTROL_ZOOM_RATIO_RANGE)
        if (r == null) { zoomRail.marks = listOf(1f); zoomRail.visibility = View.GONE; return }
        val list = (listOf(r.lower).filter { it < 0.9f } + listOf(1f, 2f, 3f, 5f, 10f)).filter { it <= r.upper }
        zoomRail.marks = list
        zoomRail.visibility = if (list.size >= 2) View.VISIBLE else View.GONE
    }

    private fun setStab(m: Int) {
        if (recording) { toast("请先停止录制"); return }
        stab = m
        if (m >= 2) toast("电子防抖会裁切画面(视角变窄)，但手持更稳")
        rebuild()
    }

    private fun setRes(b: Boolean) { if (recording) { toast("请先停止录制"); return }; res4k = b; rebuild() }

    private fun setLens(i: Int) {
        if (recording) { toast("请先停止录制"); return }
        lensIdx = i
        if (mode == 1) mode = 0
        rebuild()
    }

    private fun setExpMode(n: Int) {
        val cam = cams.firstOrNull()
        if (n >= 1 && cam?.manualOk != true) { toast("本机相机不开放手动ISO/快门（系统限制）"); return }
        if (ex.mode == 0 && n >= 1) seedFromActual()
        ex.mode = n; ex.off = 0f
        cam?.applyExposure(); refreshSliders(); refreshUi()
    }

    private fun dualOk(): Boolean {
        val f = frontId ?: return false
        val b = lenses.getOrNull(lensIdx)?.openId ?: return false
        return try { cm.concurrentCameraIds.any { it.contains(b) && it.contains(f) } } catch (_: Exception) { false }
    }

    private fun cycleMode() {
        if (recording) { toast("请先停止录制"); return }
        var n = (mode + 1) % 3
        if (n == 1 && frontId == null) n = 2
        if (n == 2 && !dualOk()) { toast("本机系统不支持前后摄同时开启"); n = 0 }
        mode = n
        rebuild()
    }

    private fun toggleRec() {
        recording = !recording
        if (recording) recStart = SystemClock.elapsedRealtime()
        rebuild()
        if (!recording) toast("已保存到 Movies/ConcertCam")
    }

    private fun granted() =
        checkSelfPermission(Manifest.permission.CAMERA) == PackageManager.PERMISSION_GRANTED &&
            checkSelfPermission(Manifest.permission.RECORD_AUDIO) == PackageManager.PERMISSION_GRANTED

    private fun want() = when {
        mode == 2 -> Size(1280, 720)
        res4k -> Size(3840, 2160)
        else -> Size(1920, 1080)
    }

    private fun rebuild() {
        ui.removeCallbacks(startRunnable)
        cams.forEach { it.close() }
        cams.clear()
        pipTv.visibility = if (mode == 2) View.VISIBLE else View.GONE
        resetGyro()
        refreshUi()
        ui.postDelayed(startRunnable, 500)
    }

    private fun mk(tv: TextureView, id: String, phys: String?, nz: Float, soft: Boolean, audio: Boolean, tag: String, e: Expo) =
        Cam(this, cm, tv, id, phys, want(), audio, tag, nz, soft, stab, e,
            { msg -> lastErr = msg; toast(msg) },
            { msg ->
                lastErr = msg; toast(msg)
                runOnUiThread { if (recording) { recording = false; rebuild() } }
            })

    private fun startAll() {
        if (!granted()) return
        try {
            val l = lenses.getOrNull(lensIdx)
            curChars()?.let { val m = Cam.stabModes(it); if (stab !in m) stab = if (1 in m) 1 else 0 }
            buildPresets()
            when (mode) {
                0 -> if (l != null) cams += mk(mainTv, l.openId, l.phys, l.nz, l.soft, true, "back", ex)
                1 -> cams += mk(mainTv, frontId!!, null, 1f, false, true, "front", ex)
                else -> {
                    cams += mk(mainTv, l!!.openId, null, 1f, true, true, "back", ex)
                    cams += mk(pipTv, frontId!!, null, 1f, false, false, "front",
                        Expo().apply { ev = 0f; spot = false; protect = false })
                }
            }
            cams.forEach { it.start(recording) }
            refreshSliders()
        } catch (e: Exception) {
            lastErr = "启动失败: ${e.message}"; toast(lastErr)
        }
    }

    // ===================== 陀螺仪：自动锁焦 / 自动解锁 =====================
    private fun resetGyro() {
        stableMs = 0f; settleMs = 0f; moved = false; vx = 0f; vy = 0f; vz = 0f
    }

    override fun onSensorChanged(e: SensorEvent) {
        val dt = if (last == 0L) 0f else (e.timestamp - last) / 1e9f
        last = e.timestamp
        if (dt <= 0f || dt > 0.5f) return
        val x = e.values[0]; val y = e.values[1]; val z = e.values[2]
        val m = sqrt(x * x + y * y + z * z)
        ema += (m - ema) * min(1f, dt / 0.5f)

        val cam = cams.firstOrNull() ?: return
        if (!auto) return
        if (!cam.locked) {
            if (ema < STABLE) stableMs += dt * 1000f else stableMs = 0f
            if (stableMs >= LOCK_AFTER_MS) { cam.setLock(true); resetGyro() }
        } else {
            val k = maxOf(0f, 1f - dt / 20f)
            vx = vx * k + x * dt; vy = vy * k + y * dt; vz = vz * k + z * dt
            if (sqrt(vx * vx + vy * vy + vz * vz) > PAN_ANGLE) moved = true
            if (moved) {
                if (ema < STABLE) settleMs += dt * 1000f else settleMs = 0f
                if (settleMs >= RELOCK_SETTLE_MS) { cam.setLock(false); resetGyro() }
            }
        }
    }

    override fun onAccuracyChanged(s: Sensor?, a: Int) {}

    private fun tick() {
        val cam = cams.firstOrNull()
        // ---- 当前镜头（醒目）：优先用系统实际在用的物理镜头 ----
        if (cam == null) lensBadge.visibility = View.GONE
        else {
            val key = cam.activeId ?: lenses.getOrNull(lensIdx)?.let { it.phys ?: it.openId }
            val info = key?.let { lensInfo[it] }
            val name = if (mode == 1) "前置" else info?.first ?: "镜头"
            val r = if (mode == 1) 1f else info?.second ?: 1f
            val z = cam.zoom
            lensBadge.text = name + " " + fmtX(r) + if (z >= r * 1.1f && mode != 1) "  ➜  " + fmtX(z) else ""
            lensBadge.setTextColor(when (name) {
                "超广角" -> Color.rgb(110, 200, 255)
                "长焦" -> Color.rgb(255, 180, 80)
                else -> Color.WHITE
            })
            lensBadge.visibility = View.VISIBLE
            if (name != lastLensName) {
                if (lastLensName.isNotEmpty()) lensBadge.animate().scaleX(1.3f).scaleY(1.3f).setDuration(120)
                    .withEndAction { lensBadge.animate().scaleX(1f).scaleY(1f).setDuration(180).start() }.start()
                lastLensName = name
            }
        }
        // ---- 对焦状态 + 锁定框 ----
        val locked = cam?.locked == true
        afPill.visibility = if (cam == null) View.GONE else View.VISIBLE
        afPill.text = when {
            locked && moved -> "🔒 检测到换目标，稳定后重新对焦"
            locked -> "🔒 对焦已锁定 · 点屏幕重新对焦"
            auto -> "对焦中 · %.0f 秒后自动锁定".format(maxOf(0f, (LOCK_AFTER_MS - stableMs) / 1000f))
            else -> "自动对焦"
        }
        afPill.setTextColor(if (locked) Color.YELLOW else Color.WHITE)
        if (locked && mainTv.width > 0) {
            val u = if (ex.tapU >= 0f) ex.tapU else 0.5f
            val v = if (ex.tapV >= 0f) ex.tapV else 0.5f
            lockBox.translationX = mainTv.x + u * mainTv.width - dp(38)
            lockBox.translationY = mainTv.y + v * mainTv.height - dp(38)
            lockBox.visibility = View.VISIBLE
        } else lockBox.visibility = View.GONE
        // ---- 曝光读数（点击展开滑杆） ----
        val iso = cam?.resIso
        val den = cam?.resExp?.let { if (it > 0) (1e9 / it).toInt() else null }
        expPill.visibility = if (cam == null) View.GONE else View.VISIBLE
        expPill.text = "${expNames[ex.mode]} · ISO ${iso ?: "-"} · 1/${den ?: "-"}  ▾"
        // ---- 录制计时 ----
        recPill.visibility = if (recording) View.VISIBLE else View.GONE
        if (recording) {
            val sec = (SystemClock.elapsedRealtime() - recStart) / 1000
            recPill.text = "● REC %02d:%02d".format(sec / 60, sec % 60)
        }
        zoomRail.zoom = cam?.zoom ?: 1f; zoomRail.invalidate()
        if (expPanel.visibility == View.VISIBLE && !dragging) {      // 自动时，滑杆跟随实际值
            val ir = cam?.isoRange
            if (ex.mode == 0) {
                cam?.resExp?.let { if (it > 0) shBar.progress = nearestShutter((1e9 / it).toInt()) }
                if (ir != null) cam?.resIso?.let { isoBar.progress = isoToProg(it, ir.lower, ir.upper) }
            } else if (ex.mode == 1 && ir != null) isoBar.progress = isoToProg(ex.iso, ir.lower, ir.upper)
            updRows()
        }
        refreshUi()
    }

    override fun onResume() {
        super.onResume()
        sm.getDefaultSensor(Sensor.TYPE_GYROSCOPE)?.let { sm.registerListener(this, it, SensorManager.SENSOR_DELAY_GAME) }
        if (granted()) rebuild()
        else if (!askedPerm) {
            askedPerm = true
            requestPermissions(arrayOf(Manifest.permission.CAMERA, Manifest.permission.RECORD_AUDIO), 1)
        }
    }

    override fun onPause() {
        super.onPause()
        sm.unregisterListener(this)
        ui.removeCallbacks(startRunnable)
        cams.forEach { it.close() }
        cams.clear()
        recording = false
        last = 0L
    }

    override fun onRequestPermissionsResult(code: Int, p: Array<out String>, r: IntArray) {
        if (granted()) rebuild() else toast("需要相机和麦克风权限")
    }
}
