package com.concertcam

import android.Manifest
import android.app.Activity
import android.content.pm.PackageManager
import android.graphics.Color
import android.hardware.Sensor
import android.hardware.SensorEvent
import android.hardware.SensorEventListener
import android.hardware.SensorManager
import android.hardware.camera2.CameraCharacteristics
import android.hardware.camera2.CameraManager
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
    private val STABLE = 0.25f        // 角速度低于此值(rad/s)算"稳定对准"
    private val LOCK_AFTER_MS = 5000f // 稳定多久后自动锁定
    private val PAN_ANGLE = 0.26f     // 净转动超过约15°算"换目标"
    private val RELOCK_SETTLE_MS = 3000f // 换目标后稳定多久才解锁重新对焦

    private data class Lens(val label: String, val openId: String, val phys: String?)

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
    private lateinit var bAuto: Button
    private lateinit var bLock: Button

    private val ui = Handler(Looper.getMainLooper())
    private val cams = mutableListOf<Cam>()
    private val lenses = mutableListOf<Lens>()
    private var frontId: String? = null

    private var lensIdx = 0
    private var mode = 0            // 0 后置 1 前置 2 前后同录
    private var res4k = false
    private var recording = false
    private var auto = true
    private var zoom = 1f
    private var recStart = 0L
    private var askedPerm = false

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

    private fun eqMm(c: CameraCharacteristics): Int {
        val f = c.get(CameraCharacteristics.LENS_INFO_AVAILABLE_FOCAL_LENGTHS)?.firstOrNull() ?: return 0
        val s = c.get(CameraCharacteristics.SENSOR_INFO_PHYSICAL_SIZE) ?: return 0
        return Math.round(f * 43.27f / hypot(s.width, s.height))
    }

    private fun scanLenses() {
        for (id in cm.cameraIdList) {
            val c = cm.getCameraCharacteristics(id)
            when (c.get(CameraCharacteristics.LENS_FACING)) {
                CameraCharacteristics.LENS_FACING_FRONT -> if (frontId == null) frontId = id
                CameraCharacteristics.LENS_FACING_BACK -> {
                    lenses += Lens("ID$id ${eqMm(c)}mm", id, null)
                    for (p in c.physicalCameraIds) {
                        val pc = cm.getCameraCharacteristics(p)
                        lenses += Lens("ID$id→物理$p ${eqMm(pc)}mm", id, p)
                    }
                }
            }
        }
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
            textSize = 12f; alpha = 0.85f; isAllCaps = false
            setOnClickListener { click() }
        }
        bRec = btn { toggleRec() }
        bMode = btn { cycleMode() }
        bLens = btn { cycleLens() }
        bRes = btn { if (!recording) { res4k = !res4k; rebuild() } }
        bAuto = btn { auto = !auto; resetGyro(); refreshUi() }
        bLock = btn { cams.firstOrNull()?.let { it.setLock(!it.locked); resetGyro() } }
        val col = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            listOf(bRec, bMode, bLens, bRes, bAuto, bLock).forEach { addView(it, LinearLayout.LayoutParams(dp(130), dp(46))) }
        }
        root.addView(col, FrameLayout.LayoutParams(-2, -2, Gravity.END or Gravity.CENTER_VERTICAL).apply { rightMargin = dp(8) })

        val sd = ScaleGestureDetector(this, object : ScaleGestureDetector.SimpleOnScaleGestureListener() {
            override fun onScale(d: ScaleGestureDetector): Boolean {
                zoom *= d.scaleFactor
                cams.firstOrNull()?.let { zoom = it.setZoom(zoom) }
                return true
            }
        })
        root.setOnTouchListener { _, e -> sd.onTouchEvent(e); true }
        setContentView(root)
        root.post {
            val w = root.width; val hh = root.height
            var tw = w; var th = w * 9 / 16
            if (th > hh) { th = hh; tw = hh * 16 / 9 }
            mainTv.layoutParams = FrameLayout.LayoutParams(tw, th, Gravity.CENTER)
        }
        refreshUi()
        ui.post(object : Runnable {
            override fun run() { tick(); ui.postDelayed(this, 250) }
        })
    }

    private fun refreshUi() {
        bRec.text = if (recording) "■ 停止录制" else "● 开始录制"
        bMode.text = listOf("后置", "前置", "前后同录")[mode]
        bLens.text = lenses.getOrNull(lensIdx)?.label ?: "无后置镜头"
        bRes.text = if (res4k) "4K" else "1080p"
        bAuto.text = if (auto) "自动锁焦:开" else "自动锁焦:关"
        val l = cams.firstOrNull()?.locked == true
        bLock.text = if (l) "解锁对焦" else "手动锁焦"
    }

    private fun toast(s: String) = runOnUiThread { Toast.makeText(this, s, Toast.LENGTH_LONG).show() }

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
        if (lenses.isEmpty()) return
        lensIdx = (lensIdx + 1) % lenses.size
        zoom = 1f
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
        ui.postDelayed(startRunnable, 450)
    }

    private fun mk(tv: TextureView, id: String, phys: String?, audio: Boolean, tag: String) =
        Cam(this, cm, tv, id, phys, want(), audio, tag) { msg ->
            toast(msg)
            runOnUiThread { if (recording) { recording = false; refreshUi() } }
        }

    private fun startAll() {
        if (!granted()) return
        try {
            val l = lenses.getOrNull(lensIdx)
            when (mode) {
                0 -> if (l != null) cams += mk(mainTv, l.openId, l.phys, true, "back")
                1 -> cams += mk(mainTv, frontId!!, null, true, "front")
                else -> {
                    cams += mk(mainTv, l!!.openId, null, true, "back")
                    cams += mk(pipTv, frontId!!, null, false, "front")
                }
            }
            cams.firstOrNull()?.zoom = zoom
            cams.forEach { it.start(recording) }
        } catch (e: Exception) {
            toast("启动失败: ${e.message}")
        }
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
            if (stableMs >= LOCK_AFTER_MS) {
                cam.setLock(true)
                resetGyro()
            }
        } else {
            // 带衰减的转动积分：手抖会互相抵消，真正摇镜头才会累积
            val k = maxOf(0f, 1f - dt / 20f)
            vx = vx * k + x * dt; vy = vy * k + y * dt; vz = vz * k + z * dt
            if (sqrt(vx * vx + vy * vy + vz * vz) > PAN_ANGLE) moved = true
            if (moved) {
                if (ema < STABLE) settleMs += dt * 1000f else settleMs = 0f
                if (settleMs >= RELOCK_SETTLE_MS) {
                    cam.setLock(false)
                    resetGyro()
                }
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
        var t = "%.1fx  ${cam?.size?.width ?: 0}p\n$af".format(zoom)
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
