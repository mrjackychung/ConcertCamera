package com.concertcam

import android.Manifest
import android.app.Activity
import android.app.AlertDialog
import android.content.ClipData
import android.content.ClipboardManager
import android.content.pm.PackageManager
import android.content.res.Configuration
import android.graphics.Color
import android.hardware.Sensor
import android.hardware.SensorEvent
import android.hardware.SensorEventListener
import android.hardware.SensorManager
import android.hardware.camera2.CameraCharacteristics
import android.hardware.camera2.CameraMetadata
import android.hardware.camera2.CameraManager
import android.media.MediaRecorder
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.os.SystemClock
import android.util.Size
import android.view.Gravity
import android.view.ScaleGestureDetector
import android.view.TextureView
import android.view.View
import android.view.WindowManager
import android.widget.Button
import android.widget.FrameLayout
import android.widget.LinearLayout
import android.widget.TextView
import android.widget.Toast
import kotlin.math.hypot
import kotlin.math.min
import kotlin.math.sqrt

class MainActivity : Activity(), SensorEventListener {

    // ===== 可调参数 =====
    private val STABLE = 0.25f           // 角速度低于此值(rad/s)算"稳定对准"
    private val LOCK_AFTER_MS = 5000f    // 稳定多久后自动锁定
    private val PAN_ANGLE = 0.26f        // 净转动超过约15°算"换目标"
    private val RELOCK_SETTLE_MS = 3000f // 换目标后稳定多久才解锁重新对焦

    /** nz: 该镜头的原生缩放倍率(相对主摄)；soft: 系统镜头+软锁定 */
    private data class Lens(val label: String, val openId: String, val phys: String?, val nz: Float, val soft: Boolean = false)

    private lateinit var cm: CameraManager
    private lateinit var sm: SensorManager
    private lateinit var root: FrameLayout
    private lateinit var mainTv: TextureView
    private lateinit var pipTv: TextureView
    private lateinit var status: TextView
    private lateinit var bRec: Button
    private lateinit var bMode: Button
    private lateinit var bLens: Button
    private lateinit var bRes: Button
    private lateinit var bStab: Button
    private lateinit var bAuto: Button
    private lateinit var bLock: Button
    private lateinit var bDiag: Button
    private lateinit var presetBar: LinearLayout

    private val ui = Handler(Looper.getMainLooper())
    private val cams = mutableListOf<Cam>()
    private val lenses = mutableListOf<Lens>()
    private var frontId: String? = null

    private var lensIdx = 0
    private var mode = 0            // 0 后置 1 前置 2 前后同录
    private var res4k = false
    private var stab = 1            // 0 关 1 光学 2 光学+电子 3 增强
    private var recording = false
    private var auto = true
    private var recStart = 0L
    private var askedPerm = false
    private var lastErr = "无"
    private var lw = 0
    private var lh = 0

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

    private fun eqMm(c: CameraCharacteristics): Int {
        val f = c.get(CameraCharacteristics.LENS_INFO_AVAILABLE_FOCAL_LENGTHS)?.firstOrNull() ?: return 0
        val s = c.get(CameraCharacteristics.SENSOR_INFO_PHYSICAL_SIZE) ?: return 0
        return Math.round(f * 43.27f / hypot(s.width, s.height))
    }

    /** 只保留能录像的普通镜头（过滤景深/黑白等辅助镜头） */
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
        frontId = cm.cameraIdList.firstOrNull {
            val c = chars(it)
            c.get(CameraCharacteristics.LENS_FACING) == CameraCharacteristics.LENS_FACING_FRONT && valid(c)
        }
        val backs = cm.cameraIdList.filter {
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
                val (label, r) = lensLabel(e, ref, "物理$p")
                val nz = if (zr == null) 1f else r.coerceIn(zr.lower, zr.upper)
                lenses += Lens(label, id, p, nz)
            }
            lenses += Lens("系统镜头·软锁1x (ID$id)", id, null, 1f, true)
        }
        lensIdx = lenses.indexOfFirst { it.label.startsWith("主摄") }.coerceAtLeast(0)
    }

    private fun buildUi() {
        root = FrameLayout(this).apply { setBackgroundColor(Color.BLACK) }
        mainTv = TextureView(this)
        root.addView(mainTv)
        pipTv = TextureView(this).apply { visibility = View.GONE }
        root.addView(pipTv, FrameLayout.LayoutParams(dp(200), dp(113), Gravity.TOP or Gravity.START).apply {
            setMargins(dp(12), dp(12), 0, 0)
        })
        status = TextView(this).apply { setTextColor(Color.WHITE); textSize = 13f; setShadowLayer(4f, 0f, 0f, Color.BLACK) }
        root.addView(status, FrameLayout.LayoutParams(-2, -2, Gravity.BOTTOM or Gravity.START).apply {
            setMargins(dp(16), 0, 0, dp(12))
        })

        fun btn(click: () -> Unit) = Button(this).apply {
            textSize = 11f; alpha = 0.85f; isAllCaps = false; setPadding(4, 0, 4, 0)
            setOnClickListener { click() }
        }
        bRec = btn { toggleRec() }
        bMode = btn { cycleMode() }
        bLens = btn { cycleLens() }
        bRes = btn { if (!recording) { res4k = !res4k; rebuild() } else toast("请先停止录制") }
        bStab = btn { cycleStab() }
        bAuto = btn { auto = !auto; resetGyro(); refreshUi() }
        bLock = btn { cams.firstOrNull()?.let { it.setLock(!it.locked); resetGyro() } }
        bDiag = btn { showDiag() }; bDiag.text = "诊断信息"
        val col = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            listOf(bRec, bMode, bLens, bRes, bStab, bAuto, bLock, bDiag).forEach {
                addView(it, LinearLayout.LayoutParams(dp(132), dp(38)))
            }
        }
        root.addView(col, FrameLayout.LayoutParams(-2, -2, Gravity.END or Gravity.CENTER_VERTICAL).apply { rightMargin = dp(8) })

        presetBar = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL }
        root.addView(presetBar, FrameLayout.LayoutParams(-2, -2, Gravity.BOTTOM or Gravity.CENTER_HORIZONTAL).apply { bottomMargin = dp(8) })

        val sd = ScaleGestureDetector(this, object : ScaleGestureDetector.SimpleOnScaleGestureListener() {
            override fun onScale(d: ScaleGestureDetector): Boolean {
                cams.firstOrNull()?.let { it.setZoom(it.zoom * d.scaleFactor) }
                return true
            }
        })
        root.setOnTouchListener { _, e -> sd.onTouchEvent(e); true }
        setContentView(root)
        root.addOnLayoutChangeListener { _, _, _, _, _, _, _, _, _ -> root.post { layoutMain() } }
        refreshUi()
        ui.post(object : Runnable {
            override fun run() { tick(); ui.postDelayed(this, 250) }
        })
    }

    /** 主预览按16:9居中；预览矫正在布局后重新计算 */
    private fun layoutMain() {
        val w = root.width; val hh = root.height
        if (w == 0 || hh == 0) return
        var tw = w; var th = w * 9 / 16
        if (th > hh) { th = hh; tw = hh * 16 / 9 }
        if (tw != lw || th != lh) {
            lw = tw; lh = th
            mainTv.layoutParams = FrameLayout.LayoutParams(tw, th, Gravity.CENTER)
        }
        ui.postDelayed({ cams.forEach { it.applyTransform() } }, 150)
    }

    override fun onConfigurationChanged(c: Configuration) {
        super.onConfigurationChanged(c)
        ui.postDelayed({ cams.forEach { it.applyTransform() } }, 250)
    }

    private fun stabName() = listOf("防抖:关", "防抖:光学", "防抖:光学+电子", "防抖:增强")[stab.coerceIn(0, 3)]

    private fun refreshUi() {
        bRec.text = if (recording) "■ 停止录制" else "● 开始录制"
        bMode.text = listOf("后置", "前置", "前后同录")[mode]
        bLens.text = lenses.getOrNull(lensIdx)?.label ?: "无后置镜头"
        bRes.text = if (res4k) "4K" else "1080p"
        bStab.text = stabName()
        bAuto.text = if (auto) "自动锁焦:开" else "自动锁焦:关"
        bLock.text = if (cams.firstOrNull()?.locked == true) "解锁对焦" else "手动锁焦"
    }

    private fun toast(s: String) = runOnUiThread { Toast.makeText(this, s, Toast.LENGTH_LONG).show() }

    private fun curChars(): CameraCharacteristics? {
        val id = if (mode == 1) frontId else lenses.getOrNull(lensIdx)?.openId
        return id?.let { chars(it) }
    }

    private fun buildPresets() {
        presetBar.removeAllViews()
        val r = curChars()?.get(CameraCharacteristics.CONTROL_ZOOM_RATIO_RANGE) ?: return
        val list = (listOf(r.lower).filter { it < 0.9f } + listOf(1f, 2f, 3f, 5f)).filter { it <= r.upper }
        for (z in list) {
            val b = Button(this).apply {
                text = "%.1fx".format(z).replace(".0x", "x"); textSize = 12f; alpha = 0.85f; isAllCaps = false
                setPadding(2, 0, 2, 0)
                setOnClickListener { cams.firstOrNull()?.preset(z) }
            }
            presetBar.addView(b, LinearLayout.LayoutParams(dp(58), dp(40)))
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
        if (lenses.size <= 1) { toast("本机只开放了一个系统镜头，请用底部 0.6x/1x/3x 按钮切换镜头（会自动锁住不乱切）"); return }
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

    private fun mk(tv: TextureView, id: String, phys: String?, nz: Float, soft: Boolean, audio: Boolean, tag: String) =
        Cam(this, cm, tv, id, phys, want(), audio, tag, nz, soft, stab,
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
                0 -> if (l != null) cams += mk(mainTv, l.openId, l.phys, l.nz, l.soft, true, "back")
                1 -> cams += mk(mainTv, frontId!!, null, 1f, false, true, "front")
                else -> {
                    cams += mk(mainTv, l!!.openId, null, 1f, true, true, "back")
                    cams += mk(pipTv, frontId!!, null, 1f, false, false, "front")
                }
            }
            cams.forEach { it.start(recording) }
        } catch (e: Exception) {
            lastErr = "启动失败: ${e.message}"; toast(lastErr)
        }
    }

    private fun showDiag() {
        val txt = buildString {
            appendLine("Android ${Build.VERSION.SDK_INT}  ${Build.MODEL}")
            for (id in cm.cameraIdList) {
                val c = chars(id)
                appendLine("ID$id 朝向=${c.get(CameraCharacteristics.LENS_FACING)} ${eqMm(c)}mm 可录像=${valid(c)} " +
                    "缩放=${c.get(CameraCharacteristics.CONTROL_ZOOM_RATIO_RANGE)} 防抖=${Cam.stabModes(c)}")
                for (p in c.physicalCameraIds) {
                    try { appendLine("   └物理$p ${eqMm(chars(p))}mm") } catch (_: Exception) { appendLine("   └物理$p 无法读取") }
                }
            }
            appendLine("可同时开启: " + try { cm.concurrentCameraIds.toString() } catch (_: Exception) { "无" })
            appendLine("当前: ${lenses.getOrNull(lensIdx)?.label}")
            appendLine("系统实际使用的物理镜头ID: ${cams.firstOrNull()?.activeId}")
            appendLine("最近错误: $lastErr")
        }
        AlertDialog.Builder(this).setTitle("诊断信息").setMessage(txt)
            .setPositiveButton("复制") { _, _ ->
                (getSystemService(CLIPBOARD_SERVICE) as ClipboardManager).setPrimaryClip(ClipData.newPlainText("diag", txt))
            }.setNegativeButton("关闭", null).show()
    }

    // ===== 陀螺仪：自动锁焦 / 自动解锁 =====
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
            cam.locked -> "🔒 焦距/曝光已锁定" + if (moved) "（检测到换目标，稳定后重新对焦）" else ""
            auto -> "自动对焦中  稳定 %.1f / %.0f s".format(stableMs / 1000f, LOCK_AFTER_MS / 1000f)
            else -> "自动对焦（自动锁焦已关）"
        }
        var t = "%.1fx  %dp  实际镜头ID:%s\n%s".format(cam?.zoom ?: 1f, cam?.size?.height ?: 0, cam?.activeId ?: "-", af)
        if (recording) {
            val s = (SystemClock.elapsedRealtime() - recStart) / 1000
            t += "\n● REC %02d:%02d".format(s / 60, s % 60)
        }
        status.text = t
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
