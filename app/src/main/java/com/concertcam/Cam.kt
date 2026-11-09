package com.concertcam

import android.annotation.SuppressLint
import android.app.Activity
import android.content.ContentValues
import android.graphics.Matrix
import android.graphics.RectF
import android.graphics.SurfaceTexture
import android.hardware.camera2.*
import android.hardware.camera2.params.MeteringRectangle
import android.hardware.camera2.params.OutputConfiguration
import android.hardware.camera2.params.SessionConfiguration
import android.media.MediaRecorder
import android.net.Uri
import android.os.Build
import android.os.Handler
import android.os.HandlerThread
import android.os.ParcelFileDescriptor
import android.provider.MediaStore
import android.util.Size
import android.view.Surface
import android.view.TextureView
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale
import java.util.concurrent.Executor

/** 曝光/测光设置（跨相机重建保留） */
class Expo {
    @Volatile var mode = 0          // 0 自动(点测光+EV+高光保护) 1 固定快门·自动ISO 2 手动
    @Volatile var ev = -1f          // 曝光补偿(档)，演唱会默认-1
    @Volatile var off = 0f          // 高光保护自动下调(<=0)
    @Volatile var shutterDen = 60   // 快门 1/x
    @Volatile var iso = 200
    @Volatile var spot = true       // 点测光(跟随点击位置)
    @Volatile var protect = true    // 高光保护(强光/激光自动压曝光)
    @Volatile var lockAe = false    // 自动锁焦时是否同时锁曝光
    @Volatile var tapU = -1f        // 上次点击位置(0~1，相对预览)
    @Volatile var tapV = -1f
}

/**
 * 一路相机。physId != null：直接锁定某颗物理镜头。
 * soft = true：用系统逻辑镜头，但监测实际使用的物理镜头，一旦要切换就把缩放压回去（软锁定）。
 * stab：0 关 / 1 光学 / 2 光学+电子 / 3 增强(预览防抖)
 */
class Cam(
    private val act: Activity,
    private val cm: CameraManager,
    private val tv: TextureView,
    private val openId: String,
    physId: String?,
    want: Size,
    private val audio: Boolean,
    private val tag: String,
    nativeZoom: Float,
    private var soft: Boolean,
    private val stab: Int,
    private val ex: Expo,
    private val onInfo: (String) -> Unit,
    private val onErr: (String) -> Unit
) {
    companion object {
        fun evStep(c: CameraCharacteristics): Float =
            c.get(CameraCharacteristics.CONTROL_AE_COMPENSATION_STEP)?.toFloat() ?: 0.33f

        fun stabModes(c: CameraCharacteristics): List<Int> {
            val l = mutableListOf(0)
            if (c.get(CameraCharacteristics.LENS_INFO_AVAILABLE_OPTICAL_STABILIZATION)
                    ?.contains(CameraMetadata.LENS_OPTICAL_STABILIZATION_MODE_ON) == true) l += 1
            val vs = c.get(CameraCharacteristics.CONTROL_AVAILABLE_VIDEO_STABILIZATION_MODES) ?: IntArray(0)
            if (vs.contains(CameraMetadata.CONTROL_VIDEO_STABILIZATION_MODE_ON)) l += 2
            if (Build.VERSION.SDK_INT >= 33 &&
                vs.contains(CameraMetadata.CONTROL_VIDEO_STABILIZATION_MODE_PREVIEW_STABILIZATION)) l += 3
            return l
        }
    }

    private var phys = physId
    init { if (physId == null) soft = true }
    private val chars = cm.getCameraCharacteristics(openId)
    private val ht = HandlerThread("cam$openId").also { it.start() }
    private val h = Handler(ht.looper)
    private val exec = Executor { h.post(it) }
    private var dev: CameraDevice? = null
    private var ses: CameraCaptureSession? = null
    private var req: CaptureRequest.Builder? = null
    private var mr: MediaRecorder? = null
    private var pfd: ParcelFileDescriptor? = null
    private var uri: Uri? = null
    private var surf: Surface? = null
    @Volatile private var lastFocus: Float? = null
    @Volatile private var closed = false
    private var manualFocus = false

    @Volatile var locked = false
    @Volatile var activeId: String? = null

    private val zr = chars.get(CameraCharacteristics.CONTROL_ZOOM_RATIO_RANGE)
    private var zMin = if (zr == null) 1f else nativeZoom.coerceIn(zr.lower, zr.upper)
    private var zCap = zr?.upper ?: 1f
    @Volatile var zoom = zMin

    private var frames = 0
    private var lockedId: String? = null
    private var lastAdj = 0L

    val size: Size = chars.get(CameraCharacteristics.SCALER_STREAM_CONFIGURATION_MAP)!!
        .getOutputSizes(MediaRecorder::class.java)
        .filter { it.width * 9 == it.height * 16 && it.width <= want.width }
        .maxByOrNull { it.width } ?: want

    private val evStepV = evStep(chars)
    val evRange = chars.get(CameraCharacteristics.CONTROL_AE_COMPENSATION_RANGE)
    val isoRange = chars.get(CameraCharacteristics.SENSOR_INFO_SENSITIVITY_RANGE)
    private val expRange = chars.get(CameraCharacteristics.SENSOR_INFO_EXPOSURE_TIME_RANGE)
    val manualOk = chars.get(CameraCharacteristics.REQUEST_AVAILABLE_CAPABILITIES)
        ?.contains(CameraMetadata.REQUEST_AVAILABLE_CAPABILITIES_MANUAL_SENSOR) == true
    private var afRect: MeteringRectangle? = null
    private var aeRect: MeteringRectangle? = null
    @Volatile var running = false
    @Volatile var resIso: Int? = null
    @Volatile var resExp: Long? = null

    private val cb = object : CameraCaptureSession.CaptureCallback() {
        override fun onCaptureCompleted(s: CameraCaptureSession, r: CaptureRequest, res: TotalCaptureResult) {
            lastFocus = res.get(CaptureResult.LENS_FOCUS_DISTANCE)
            res.get(CaptureResult.SENSOR_SENSITIVITY)?.let { resIso = it }
            res.get(CaptureResult.SENSOR_EXPOSURE_TIME)?.let { resExp = it }
            val id = res.get(CaptureResult.LOGICAL_MULTI_CAMERA_ACTIVE_PHYSICAL_ID) ?: return
            activeId = id
            if (!soft) return
            val lk = lockedId
            if (lk == null) {
                if (++frames > 20) lockedId = id
            } else if (id != lk && zoom > zMin) {
                val now = System.nanoTime()
                if (now - lastAdj > 400_000_000L) {   // 系统想切镜头：把缩放压回去
                    lastAdj = now
                    zCap = zoom * 0.95f
                    setZoom(zCap)
                }
            }
        }
    }

    fun start(recording: Boolean) {
        if (!tv.isAvailable) {
            tv.surfaceTextureListener = object : TextureView.SurfaceTextureListener {
                override fun onSurfaceTextureAvailable(s: SurfaceTexture, w: Int, hh: Int) {
                    tv.surfaceTextureListener = null
                    start(recording)
                }
                override fun onSurfaceTextureSizeChanged(s: SurfaceTexture, w: Int, hh: Int) {}
                override fun onSurfaceTextureDestroyed(s: SurfaceTexture) = true
                override fun onSurfaceTextureUpdated(s: SurfaceTexture) {}
            }
            return
        }
        openCam(recording)
    }

    @SuppressLint("MissingPermission")
    private fun openCam(recording: Boolean) {
        try {
            cm.openCamera(openId, object : CameraDevice.StateCallback() {
                override fun onOpened(d: CameraDevice) {
                    if (closed) { d.close(); return }
                    dev = d
                    makeSession(recording)
                }
                override fun onDisconnected(d: CameraDevice) { d.close() }
                override fun onError(d: CameraDevice, e: Int) { d.close(); onErr("相机错误码 $e ($tag)") }
            }, h)
        } catch (e: Exception) {
            onErr("打开失败($tag): ${e.message}")
        }
    }

    /** 修正 TextureView 的旋转/拉伸（横屏必须做） */
    fun applyTransform() {
        act.runOnUiThread {
            val vw = tv.width.toFloat(); val vh = tv.height.toFloat()
            if (vw == 0f || vh == 0f) return@runOnUiThread
            val rot = act.display?.rotation ?: Surface.ROTATION_0
            val m = Matrix()
            if (rot == Surface.ROTATION_90 || rot == Surface.ROTATION_270) {
                val view = RectF(0f, 0f, vw, vh)
                val buf = RectF(0f, 0f, size.height.toFloat(), size.width.toFloat())
                val cx = view.centerX(); val cy = view.centerY()
                buf.offset(cx - buf.centerX(), cy - buf.centerY())
                m.setRectToRect(view, buf, Matrix.ScaleToFit.FILL)
                val s = maxOf(vh / size.height, vw / size.width)
                m.postScale(s, s, cx, cy)
                m.postRotate(90f * (rot - 2), cx, cy)
            } else if (rot == Surface.ROTATION_180) {
                m.postRotate(180f, vw / 2, vh / 2)
            }
            tv.setTransform(m)
        }
    }

    private fun makeSession(recording: Boolean) {
        try {
            surf?.release()
            val st = tv.surfaceTexture!!
            st.setDefaultBufferSize(size.width, size.height)
            applyTransform()
            val ps = Surface(st)
            surf = ps
            val list = mutableListOf(ps)
            if (recording) { prepareRecorder(); list += mr!!.surface }

            val b = dev!!.createCaptureRequest(CameraDevice.TEMPLATE_RECORD)
            list.forEach { b.addTarget(it) }
            b.set(CaptureRequest.CONTROL_AF_MODE, CaptureRequest.CONTROL_AF_MODE_CONTINUOUS_VIDEO)
            // 防抖
            val oisOk = chars.get(CameraCharacteristics.LENS_INFO_AVAILABLE_OPTICAL_STABILIZATION)
                ?.contains(CameraMetadata.LENS_OPTICAL_STABILIZATION_MODE_ON) == true
            b.set(CaptureRequest.LENS_OPTICAL_STABILIZATION_MODE,
                if (stab >= 1 && oisOk) CameraMetadata.LENS_OPTICAL_STABILIZATION_MODE_ON
                else CameraMetadata.LENS_OPTICAL_STABILIZATION_MODE_OFF)
            val vs = chars.get(CameraCharacteristics.CONTROL_AVAILABLE_VIDEO_STABILIZATION_MODES) ?: IntArray(0)
            if (stab == 2 && vs.contains(CameraMetadata.CONTROL_VIDEO_STABILIZATION_MODE_ON))
                b.set(CaptureRequest.CONTROL_VIDEO_STABILIZATION_MODE, CameraMetadata.CONTROL_VIDEO_STABILIZATION_MODE_ON)
            if (stab == 3 && Build.VERSION.SDK_INT >= 33 &&
                vs.contains(CameraMetadata.CONTROL_VIDEO_STABILIZATION_MODE_PREVIEW_STABILIZATION))
                b.set(CaptureRequest.CONTROL_VIDEO_STABILIZATION_MODE, CameraMetadata.CONTROL_VIDEO_STABILIZATION_MODE_PREVIEW_STABILIZATION)
            if (zr != null) b.set(CaptureRequest.CONTROL_ZOOM_RATIO, zoom)
            if (ex.tapU >= 0f) computeRects(ex.tapU, ex.tapV)
            afRect?.let { b.set(CaptureRequest.CONTROL_AF_REGIONS, arrayOf(it)) }
            setExp(b)
            req = b

            val p = phys
            val cfgs = list.map { s -> OutputConfiguration(s).also { if (p != null) it.setPhysicalCameraId(p) } }
            val sc = SessionConfiguration(SessionConfiguration.SESSION_REGULAR, cfgs, exec,
                object : CameraCaptureSession.StateCallback() {
                    override fun onConfigured(s: CameraCaptureSession) {
                        if (closed) { s.close(); return }
                        ses = s
                        running = true
                        try {
                            s.setRepeatingRequest(b.build(), cb, h)
                            if (recording) mr?.start()
                        } catch (e: Exception) { onErr("开始失败($tag): ${e.message}") }
                    }
                    override fun onConfigureFailed(s: CameraCaptureSession) {
                        s.close()
                        if (phys != null && !closed) {
                            onInfo("本机不允许直接指定该物理镜头，已改用系统镜头+软锁定")
                            phys = null; soft = true
                            discardRecorder()
                            makeSession(recording)
                        } else onErr("会话配置失败($tag)：分辨率/防抖组合可能不被支持")
                    }
                })
            sc.sessionParameters = b.build()
            dev!!.createCaptureSession(sc)
        } catch (e: Exception) {
            onErr("启动失败($tag): ${e.message}")
        }
    }

    private fun prepareRecorder() {
        val ts = SimpleDateFormat("yyyyMMdd_HHmmss", Locale.US).format(Date())
        val v = ContentValues().apply {
            put(MediaStore.Video.Media.DISPLAY_NAME, "Concert_${tag}_$ts.mp4")
            put(MediaStore.Video.Media.MIME_TYPE, "video/mp4")
            put(MediaStore.Video.Media.RELATIVE_PATH, "Movies/ConcertCam")
            put(MediaStore.Video.Media.IS_PENDING, 1)
        }
        uri = act.contentResolver.insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, v)!!
        pfd = act.contentResolver.openFileDescriptor(uri!!, "rw")
        val r = MediaRecorder(act)
        if (audio) r.setAudioSource(MediaRecorder.AudioSource.MIC)
        r.setVideoSource(MediaRecorder.VideoSource.SURFACE)
        r.setOutputFormat(MediaRecorder.OutputFormat.MPEG_4)
        r.setOutputFile(pfd!!.fileDescriptor)
        r.setVideoEncodingBitRate(if (size.width >= 3840) 50_000_000 else if (size.width >= 1920) 24_000_000 else 10_000_000)
        r.setVideoFrameRate(30)
        r.setVideoSize(size.width, size.height)
        r.setVideoEncoder(MediaRecorder.VideoEncoder.H264)
        if (audio) {
            r.setAudioEncoder(MediaRecorder.AudioEncoder.AAC)
            r.setAudioEncodingBitRate(192_000)
            r.setAudioSamplingRate(48_000)
        }
        r.setOrientationHint(rotNeeded())
        r.prepare()
        mr = r
    }

    private fun discardRecorder() {
        try { mr?.release() } catch (_: Exception) {}
        mr = null
        try { pfd?.close() } catch (_: Exception) {}
        pfd = null
        uri?.let { try { act.contentResolver.delete(it, null, null) } catch (_: Exception) {} }
        uri = null
    }

    /** 画面需要顺时针旋转多少度才是正的（同录像方向） */
    private fun rotNeeded(): Int {
        val sensor = chars.get(CameraCharacteristics.SENSOR_ORIENTATION) ?: 90
        val front = chars.get(CameraCharacteristics.LENS_FACING) == CameraCharacteristics.LENS_FACING_FRONT
        val rotDeg = (act.display?.rotation ?: Surface.ROTATION_0) * 90
        return if (front) (sensor + rotDeg) % 360 else (sensor - rotDeg + 360) % 360
    }

    /** 预览上的点(u,v 0~1) → 传感器坐标的对焦/测光区域 */
    private fun computeRects(u: Float, v: Float) {
        val ar = chars.get(CameraCharacteristics.SENSOR_INFO_ACTIVE_ARRAY_SIZE) ?: return
        val (xn, yn) = when (rotNeeded()) {
            0 -> u to v
            90 -> v to (1f - u)
            180 -> (1f - u) to (1f - v)
            else -> (1f - v) to u
        }
        val aw = ar.width().toFloat(); val ah = ar.height().toFloat()
        val z = zoom.coerceAtLeast(1f)
        val vw = aw / z
        val vh = minOf(ah, aw * 9f / 16f) / z
        val x = ar.left + aw / 2 + (xn - 0.5f) * vw
        val y = ar.top + ah / 2 + (yn - 0.5f) * vh
        val side = aw / 8f
        val l = (x - side / 2).coerceIn(ar.left.toFloat(), ar.right - side)
        val t = (y - side / 2).coerceIn(ar.top.toFloat(), ar.bottom - side)
        val r = MeteringRectangle(l.toInt(), t.toInt(), side.toInt(), side.toInt(), MeteringRectangle.METERING_WEIGHT_MAX)
        afRect = r; aeRect = r
    }

    private fun setExp(b: CaptureRequest.Builder) {
        if (ex.mode == 0 || !manualOk) {
            b.set(CaptureRequest.CONTROL_AE_MODE, CaptureRequest.CONTROL_AE_MODE_ON)
            evRange?.let { rg ->
                val idx = Math.round((ex.ev + ex.off) / evStepV).coerceIn(rg.lower, rg.upper)
                b.set(CaptureRequest.CONTROL_AE_EXPOSURE_COMPENSATION, idx)
            }
            val r = aeRect
            b.set(CaptureRequest.CONTROL_AE_REGIONS,
                arrayOf(if (ex.spot && r != null) r else MeteringRectangle(0, 0, 0, 0, 0)))
        } else {
            b.set(CaptureRequest.CONTROL_AE_MODE, CaptureRequest.CONTROL_AE_MODE_OFF)
            var t = 1_000_000_000L / ex.shutterDen
            expRange?.let { t = t.coerceIn(it.lower, it.upper) }
            b.set(CaptureRequest.SENSOR_EXPOSURE_TIME, t)
            b.set(CaptureRequest.SENSOR_SENSITIVITY, isoRange?.let { ex.iso.coerceIn(it.lower, it.upper) } ?: ex.iso)
            b.set(CaptureRequest.SENSOR_FRAME_DURATION, maxOf(33_333_333L, t))
        }
    }

    fun applyExposure() { val b = req ?: return; setExp(b); push() }

    /** 点击对焦：解除锁定，对焦并测光到点击处 */
    fun tapFocus(u: Float, v: Float) {
        ex.tapU = u; ex.tapV = v
        computeRects(u, v)
        val b = req ?: return
        val s = ses ?: return
        try {
            locked = false; manualFocus = false
            b.set(CaptureRequest.CONTROL_AE_LOCK, false)
            b.set(CaptureRequest.CONTROL_AWB_LOCK, false)
            b.set(CaptureRequest.CONTROL_AF_MODE, CaptureRequest.CONTROL_AF_MODE_CONTINUOUS_VIDEO)
            afRect?.let { b.set(CaptureRequest.CONTROL_AF_REGIONS, arrayOf(it)) }
            setExp(b)
            b.set(CaptureRequest.CONTROL_AF_TRIGGER, CaptureRequest.CONTROL_AF_TRIGGER_CANCEL)
            s.capture(b.build(), null, h)
            b.set(CaptureRequest.CONTROL_AF_TRIGGER, CaptureRequest.CONTROL_AF_TRIGGER_IDLE)
            push()
        } catch (_: Exception) {}
    }

    private fun push() {
        try { ses?.setRepeatingRequest(req!!.build(), cb, h) } catch (_: Exception) {}
    }

    /** 变焦预设：选定一档后把系统锁在对应镜头上（下限=该档，系统想切换时自动压回） */
    fun preset(t: Float) {
        val r = zr ?: return
        if (phys != null) { setZoom(t); return }
        zCap = r.upper
        zMin = t.coerceIn(r.lower, r.upper)
        lockedId = null; frames = 0
        setZoom(zMin)
    }

    fun setZoom(z: Float): Float {
        if (zr == null) return 1f
        zoom = z.coerceIn(zMin, maxOf(zMin, zCap))
        req?.set(CaptureRequest.CONTROL_ZOOM_RATIO, zoom)
        push()
        return zoom
    }

    /** 锁定/解锁 对焦 + 曝光 + 白平衡 */
    fun setLock(on: Boolean) {
        val b = req ?: return
        val s = ses ?: return
        try {
            if (on) {
                val d = lastFocus
                if (d != null && d > 0f) {
                    manualFocus = true
                    b.set(CaptureRequest.CONTROL_AF_MODE, CaptureRequest.CONTROL_AF_MODE_OFF)
                    b.set(CaptureRequest.LENS_FOCUS_DISTANCE, d)
                } else {
                    manualFocus = false
                    b.set(CaptureRequest.CONTROL_AF_TRIGGER, CaptureRequest.CONTROL_AF_TRIGGER_START)
                    s.capture(b.build(), null, h)
                    b.set(CaptureRequest.CONTROL_AF_TRIGGER, CaptureRequest.CONTROL_AF_TRIGGER_IDLE)
                }
                b.set(CaptureRequest.CONTROL_AE_LOCK, ex.lockAe && ex.mode == 0)
                b.set(CaptureRequest.CONTROL_AWB_LOCK, true)
            } else {
                b.set(CaptureRequest.CONTROL_AE_LOCK, false)
                b.set(CaptureRequest.CONTROL_AWB_LOCK, false)
                b.set(CaptureRequest.CONTROL_AF_MODE, CaptureRequest.CONTROL_AF_MODE_CONTINUOUS_VIDEO)
                if (!manualFocus) {
                    b.set(CaptureRequest.CONTROL_AF_TRIGGER, CaptureRequest.CONTROL_AF_TRIGGER_CANCEL)
                    s.capture(b.build(), null, h)
                    b.set(CaptureRequest.CONTROL_AF_TRIGGER, CaptureRequest.CONTROL_AF_TRIGGER_IDLE)
                }
            }
            locked = on
            push()
        } catch (_: Exception) {}
    }

    fun close() {
        closed = true
        running = false
        try { ses?.stopRepeating() } catch (_: Exception) {}
        mr?.let { try { it.stop() } catch (_: Exception) {}; it.release() }
        mr = null
        try { pfd?.close() } catch (_: Exception) {}
        uri?.let {
            try {
                act.contentResolver.update(it, ContentValues().apply {
                    put(MediaStore.Video.Media.IS_PENDING, 0)
                }, null, null)
            } catch (_: Exception) {}
        }
        uri = null
        try { ses?.close() } catch (_: Exception) {}
        try { dev?.close() } catch (_: Exception) {}
        surf?.release()
        ht.quitSafely()
    }
}
