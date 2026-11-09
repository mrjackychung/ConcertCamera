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
import android.widget.SeekBar
import android.widget.TextView
import android.widget.Toast
import kotlin.math.hypot
import kotlin.math.ln
import kotlin.math.min
import kotlin.math.pow
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
    private lateinit var status: TextView
    private lateinit var ring: View
    private lateinit var presetBar: LinearLayout
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
    private lateinit var bExpo: Button
    private lateinit var bLens: Button
    private lateinit var bRes: Button
    private lateinit var bStab: Button
    private lateinit var bAuto: Button
    private lateinit var bLock: Button
    private lateinit var bExpMode: Button
    private lateinit var bProt: Button
    private lateinit var bSpot: Button
    private lateinit var bAeLock: Button
    private lateinit var bDiag: Button

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
        addView(l, LinearLayout.LayoutParams(dp(130), -2))
        addView(b, LinearLayout.LayoutParams(0, -2, 1f))
    }

    private fun label() = TextView(this).apply { setTextColor(Color.WHITE); textSize = 12f }

    private fun onBar(bar: SeekBar, f: (Int) -> Unit) = bar.setOnSeekBarChangeListener(object : SeekBar.OnSeekBarChangeListener {
        override fun onProgressChanged(s: SeekBar, p: Int, user: Boolean) { if (user) f(p) }
        override fun onStartTrackingTouch(s: SeekBar) {}
        override fun onStopTrackingTouch(s: SeekBar) {}
    })

    private fun buildUi() {
        root = FrameLayout(this).apply { setBackgroundColor(Color.BLACK) }
        mainTv = TextureView(this)
        root.addView(mainTv)
        pipTv = TextureView(this).apply { visibility = View.GONE }
        root.addView(pipTv, FrameLayout.LayoutParams(dp(90), dp(160), Gravity.TOP or Gravity.END).apply {
            setMargins(0, dp(40), dp(10), 0)
        })
        status = TextView(this).apply { setTextColor(Color.WHITE); textSize = 12f; setShadowLayer(4f, 0f, 0f, Color.BLACK) }
        root.addView(status, FrameLayout.LayoutParams(-2, -2, Gravity.TOP or Gravity.START).apply { setMargins(dp(12), dp(36), 0, 0) })
        ring = View(this).apply {
            background = GradientDrawable().apply { shape = GradientDrawable.OVAL; setStroke(dp(2), Color.YELLOW); setColor(Color.TRANSPARENT) }
            visibility = View.GONE
        }
        root.addView(ring, FrameLayout.LayoutParams(dp(64), dp(64)))

        // ---- 曝光面板 ----
        evLabel = label(); shLabel = label(); isoLabel = label()
        evBar = SeekBar(this); shBar = SeekBar(this); isoBar = SeekBar(this).apply { max = 100 }
        evRow = sRow(evLabel, evBar); shRow = sRow(shLabel, shBar); isoRow = sRow(isoLabel, isoBar)
        expPanel = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL; visibility = View.GONE
            addView(evRow); addView(shRow); addView(isoRow)
        }
        onBar(evBar) { p ->
            val c = curChars() ?: return@onBar
            val r = c.get(CameraCharacteristics.CONTROL_AE_COMPENSATION_RANGE) ?: return@onBar
            ex.ev = (r.lower + p) * Cam.evStep(c); ex.off = 0f
            cams.firstOrNull()?.applyExposure(); updLabels()
        }
        onBar(shBar) { p -> ex.shutterDen = SHUTTERS[p]; cams.firstOrNull()?.applyExposure(); updLabels() }
        onBar(isoBar) { p ->
            val ir = curChars()?.get(CameraCharacteristics.SENSOR_INFO_SENSITIVITY_RANGE) ?: return@onBar
            if (ex.mode == 2) { ex.iso = progToIso(p, ir.lower, ir.upper); cams.firstOrNull()?.applyExposure(); updLabels() }
        }

        // ---- 主操作行 ----
        presetBar = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER }
        bRec = Button(this).apply {
            textSize = 24f; setTextColor(Color.WHITE)
            background = GradientDrawable().apply { shape = GradientDrawable.OVAL; setColor(Color.rgb(220, 40, 40)) }
            setOnClickListener { toggleRec() }
        }
        bMode = chip { cycleMode() }
        bExpo = chip("曝光▲") { expPanel.visibility = if (expPanel.visibility == View.GONE) View.VISIBLE else View.GONE }
        val action = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER
            addView(bMode, LinearLayout.LayoutParams(dp(96), dp(44)))
            addView(bRec, LinearLayout.LayoutParams(dp(72), dp(72)).apply { setMargins(dp(20), dp(4), dp(20), dp(4)) })
            addView(bExpo, LinearLayout.LayoutParams(dp(96), dp(44)))
        }

        // ---- 设置条(可横向滑动) ----
        bLens = chip { cycleLens() }
        bRes = chip { if (!recording) { res4k = !res4k; rebuild() } else toast("请先停止录制") }
        bStab = chip { cycleStab() }
        bAuto = chip { auto = !auto; resetGyro(); refreshUi() }
        bLock = chip { cams.firstOrNull()?.let { it.setLock(!it.locked); resetGyro() } }
        bExpMode = chip { cycleExpMode() }
        bProt = chip { ex.protect = !ex.protect; ex.off = 0f; cams.firstOrNull()?.applyExposure(); refreshUi() }
        bSpot = chip { ex.spot = !ex.spot; cams.firstOrNull()?.applyExposure(); refreshUi() }
        bAeLock = chip { ex.lockAe = !ex.lockAe; refreshUi() }
        bDiag = chip("诊断信息") { showDiag() }
        val chips = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            listOf(bLens, bRes, bStab, bAuto, bLock, bExpMode, bProt, bSpot, bAeLock, bDiag).forEach {
                addView(it, LinearLayout.LayoutParams(-2, dp(36)).apply { rightMargin = dp(6) })
            }
        }
        val scroll = HorizontalScrollView(this).apply { isHorizontalScrollBarEnabled = false; addView(chips) }

        val panel = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL; isClickable = true
            setBackgroundColor(Color.argb(120, 0, 0, 0))
            setPadding(dp(8), dp(6), dp(8), dp(10))
            addView(expPanel); addView(presetBar); addView(action); addView(scroll)
        }
        root.addView(panel, FrameLayout.LayoutParams(-1, -2, Gravity.BOTTOM))

        // ---- 手势：双指缩放 + 单击对焦/测光 ----
        val sd = ScaleGestureDetector(this, object : ScaleGestureDetector.SimpleOnScaleGestureListener() {
            override fun onScale(d: ScaleGestureDetector): Boolean {
                cams.firstOrNull()?.let { it.setZoom(it.zoom * d.scaleFactor) }
                return true
            }
        })
        val gd = GestureDetector(this, object : GestureDetector.SimpleOnGestureListener() {
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
        root.setOnTouchListener { _, e -> sd.onTouchEvent(e); if (!sd.isInProgress) gd.onTouchEvent(e); true }
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
            mainTv.layoutParams = FrameLayout.LayoutParams(tw, th, if (portrait) Gravity.TOP or Gravity.CENTER_HORIZONTAL else Gravity.CENTER)
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
        bLens.text = lenses.getOrNull(lensIdx)?.label ?: "无后置镜头"
        bRes.text = if (res4k) "4K" else "1080p"
        bStab.text = stabName()
        bAuto.text = if (auto) "自动锁焦:开" else "自动锁焦:关"
        bLock.text = if (cams.firstOrNull()?.locked == true) "解锁对焦" else "手动锁焦"
        bExpMode.text = "曝光:" + listOf("自动", "快门优先", "手动")[ex.mode]
        bProt.text = if (ex.protect) "高光保护:开" else "高光保护:关"
        bSpot.text = if (ex.spot) "测光:点击处" else "测光:全局"
        bAeLock.text = if (ex.lockAe) "锁焦时锁曝光:开" else "锁焦时锁曝光:关"
    }

    private fun toast(s: String) = runOnUiThread { Toast.makeText(this, s, Toast.LENGTH_LONG).show() }

    private fun curChars(): CameraCharacteristics? {
        val id = if (mode == 1) frontId else lenses.getOrNull(lensIdx)?.openId
        return id?.let { chars(it) }
    }

    // ===================== 曝光滑杆 =====================
    private fun nearestShutter(den: Int) = SHUTTERS.indices.minByOrNull { Math.abs(SHUTTERS[it] - den) } ?: 2
    private fun isoToProg(iso: Int, lo: Int, hi: Int) = (100 * ln(iso.toFloat() / lo) / ln(hi.toFloat() / lo)).toInt().coerceIn(0, 100)
    private fun progToIso(p: Int, lo: Int, hi: Int) = (lo * (hi.toFloat() / lo).pow(p / 100f)).toInt()

    private fun updLabels() {
        evLabel.text = "曝光补偿 %+.1f EV".format(ex.ev)
        shLabel.text = "快门 1/${ex.shutterDen}"
        isoLabel.text = "ISO ${ex.iso}" + if (ex.mode == 1) "(自动)" else ""
    }

    private fun refreshSliders() {
        val c = curChars() ?: return
        c.get(CameraCharacteristics.CONTROL_AE_COMPENSATION_RANGE)?.let { r ->
            evBar.max = r.upper - r.lower
            evBar.progress = (Math.round(ex.ev / Cam.evStep(c)) - r.lower).coerceIn(0, evBar.max)
        }
        shBar.max = SHUTTERS.size - 1; shBar.progress = nearestShutter(ex.shutterDen)
        c.get(CameraCharacteristics.SENSOR_INFO_SENSITIVITY_RANGE)?.let { isoBar.progress = isoToProg(ex.iso, it.lower, it.upper) }
        evRow.visibility = if (ex.mode != 2) View.VISIBLE else View.GONE
        shRow.visibility = if (ex.mode >= 1) View.VISIBLE else View.GONE
        isoRow.visibility = if (ex.mode >= 1) View.VISIBLE else View.GONE
        isoBar.isEnabled = ex.mode == 2
        updLabels()
    }

    private fun cycleExpMode() {
        val cam = cams.firstOrNull()
        val manual = curChars()?.get(CameraCharacteristics.REQUEST_AVAILABLE_CAPABILITIES)
            ?.contains(CameraMetadata.REQUEST_AVAILABLE_CAPABILITIES_MANUAL_SENSOR) == true
        if (!manual) { toast("本机相机不开放手动ISO/快门，只能使用自动曝光"); return }
        val n = (ex.mode + 1) % 3
        if (ex.mode == 0) { // 从自动切到手动系：沿用当前实际曝光作为起点
            cam?.resIso?.let { ex.iso = it }
            cam?.resExp?.let { if (it > 0) ex.shutterDen = SHUTTERS[nearestShutter((1e9 / it).toInt())] }
        }
        ex.mode = n; ex.off = 0f
        cam?.applyExposure(); refreshSliders(); refreshUi()
        expPanel.visibility = View.VISIBLE
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
        presetBar.removeAllViews()
        val r = curChars()?.get(CameraCharacteristics.CONTROL_ZOOM_RATIO_RANGE) ?: return
        val list = (listOf(r.lower).filter { it < 0.9f } + listOf(1f, 2f, 3f, 5f)).filter { it <= r.upper }
        for (z in list) {
            val b = chip("%.1fx".format(z).replace(".0x", "x")) { cams.firstOrNull()?.preset(z) }
            presetBar.addView(b, LinearLayout.LayoutParams(dp(56), dp(34)).apply { setMargins(dp(3), dp(2), dp(3), dp(2)) })
        }
    }

    private fun cycleStab() {
        if (recording) { toast("请先停止录制"); return }
        val modes = curChars()?.let { Cam.stabModes(it) } ?: return
        stab = modes[(modes.indexOf(stab) + 1) % modes.size]
        if (stab >= 2) toast("电子防抖会裁切画面(视角变窄)，但手持更稳")
        rebuild()
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

    private fun cycleLens() {
        if (recording) { toast("请先停止录制"); return }
        if (lenses.size <= 1) { toast("本机只开放了一个系统镜头，请用 0.6x/1x/3x 按钮切换镜头（会自动锁住不乱切）"); return }
        lensIdx = (lensIdx + 1) % lenses.size
        if (mode == 1) mode = 0
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

    private fun showDiag() {
        val txt = buildString {
            appendLine("Android ${Build.VERSION.SDK_INT}  ${Build.MODEL}")
            for (id in allIds) {
                val c = chars(id)
                appendLine("ID$id${if (id !in cm.cameraIdList) "(隐藏)" else ""} 朝向=${c.get(CameraCharacteristics.LENS_FACING)} ${eqMm(c)}mm 可录像=${valid(c)} " +
                    "缩放=${c.get(CameraCharacteristics.CONTROL_ZOOM_RATIO_RANGE)} 防抖=${Cam.stabModes(c)} " +
                    "ISO=${c.get(CameraCharacteristics.SENSOR_INFO_SENSITIVITY_RANGE)} EV=${c.get(CameraCharacteristics.CONTROL_AE_COMPENSATION_RANGE)}")
                for (p in c.physicalCameraIds) {
                    try { appendLine("   └物理$p ${eqMm(chars(p))}mm") } catch (_: Exception) { appendLine("   └物理$p 无法读取") }
                }
            }
            appendLine("可同时开启: " + try { cm.concurrentCameraIds.toString() } catch (_: Exception) { "无" })
            lenses.forEach { appendLine("镜头项: ${it.label} open=${it.openId} phys=${it.phys}") }
            appendLine("当前: ${lenses.getOrNull(lensIdx)?.label}")
            appendLine("系统实际使用的物理镜头ID: ${cams.firstOrNull()?.activeId}")
            appendLine("最近错误: $lastErr")
        }
        AlertDialog.Builder(this).setTitle("诊断信息").setMessage(txt)
            .setPositiveButton("复制") { _, _ ->
                (getSystemService(CLIPBOARD_SERVICE) as ClipboardManager).setPrimaryClip(ClipData.newPlainText("diag", txt))
            }.setNegativeButton("关闭", null).show()
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
        val af = when {
            cam == null -> ""
            cam.locked -> "🔒 焦距已锁定" + if (moved) "（换目标，稳定后重新对焦）" else "（点屏幕可重新对焦）"
            auto -> "对焦中 稳定 %.1f/%.0fs（点屏幕指定对焦点）".format(stableMs / 1000f, LOCK_AFTER_MS / 1000f)
            else -> "自动对焦（自动锁焦已关）"
        }
        val iso = cam?.resIso
        val den = cam?.resExp?.let { if (it > 0) (1e9 / it).toInt() else null }
        val expT = listOf("自动", "快门优先", "手动")[ex.mode] + "  ISO ${iso ?: "-"}  1/${den ?: "-"}" +
            if (ex.mode == 0) "  EV %+.1f".format(ex.ev + ex.off) else ""
        var t = "%.1fx  %dp  镜头ID:%s\n%s\n%s".format(cam?.zoom ?: 1f, cam?.size?.height ?: 0, cam?.activeId ?: "-", af, expT)
        if (recording) {
            val s = (SystemClock.elapsedRealtime() - recStart) / 1000
            t += "\n● REC %02d:%02d".format(s / 60, s % 60)
        }
        status.text = t
        if (ex.mode == 1) { isoLabel.text = "ISO ${ex.iso}(自动)"; cam?.isoRange?.let { isoBar.progress = isoToProg(ex.iso, it.lower, it.upper) } }
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
