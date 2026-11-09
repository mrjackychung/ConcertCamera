package com.concertcam

import android.annotation.SuppressLint
import android.app.Activity
import android.content.ContentValues
import android.graphics.SurfaceTexture
import android.hardware.camera2.*
import android.hardware.camera2.params.OutputConfiguration
import android.hardware.camera2.params.SessionConfiguration
import android.media.MediaRecorder
import android.net.Uri
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

/** 一路相机：预览 + (可选)录像。physId != null 时锁定到某颗物理镜头，系统不会自动切镜头。 */
class Cam(
    private val act: Activity,
    private val cm: CameraManager,
    private val tv: TextureView,
    private val openId: String,
    private val physId: String?,
    want: Size,
    private val audio: Boolean,
    private val tag: String,
    private val onErr: (String) -> Unit
) {
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
    var zoom = 1f
    private val zoomRange = chars.get(CameraCharacteristics.CONTROL_ZOOM_RATIO_RANGE)

    val size: Size = chars.get(CameraCharacteristics.SCALER_STREAM_CONFIGURATION_MAP)!!
        .getOutputSizes(MediaRecorder::class.java)
        .filter { it.width * 9 == it.height * 16 && it.width <= want.width }
        .maxByOrNull { it.width } ?: want

    private val cb = object : CameraCaptureSession.CaptureCallback() {
        override fun onCaptureCompleted(s: CameraCaptureSession, r: CaptureRequest, res: TotalCaptureResult) {
            lastFocus = res.get(CaptureResult.LENS_FOCUS_DISTANCE)
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

    private fun makeSession(recording: Boolean) {
        try {
            val st = tv.surfaceTexture!!
            st.setDefaultBufferSize(size.width, size.height)
            val ps = Surface(st)
            surf = ps
            val list = mutableListOf(ps)
            if (recording) { prepareRecorder(); list += mr!!.surface }

            val b = dev!!.createCaptureRequest(CameraDevice.TEMPLATE_RECORD)
            list.forEach { b.addTarget(it) }
            b.set(CaptureRequest.CONTROL_AF_MODE, CaptureRequest.CONTROL_AF_MODE_CONTINUOUS_VIDEO)
            val ois = chars.get(CameraCharacteristics.LENS_INFO_AVAILABLE_OPTICAL_STABILIZATION)
            if (ois?.contains(CaptureRequest.LENS_OPTICAL_STABILIZATION_MODE_ON) == true)
                b.set(CaptureRequest.LENS_OPTICAL_STABILIZATION_MODE, CaptureRequest.LENS_OPTICAL_STABILIZATION_MODE_ON)
            zoomRange?.let { b.set(CaptureRequest.CONTROL_ZOOM_RATIO, zoom.coerceIn(it.lower, it.upper)) }
            req = b

            val cfgs = list.map { s ->
                OutputConfiguration(s).also { if (physId != null) it.setPhysicalCameraId(physId) }
            }
            val sc = SessionConfiguration(SessionConfiguration.SESSION_REGULAR, cfgs, exec,
                object : CameraCaptureSession.StateCallback() {
                    override fun onConfigured(s: CameraCaptureSession) {
                        if (closed) { s.close(); return }
                        ses = s
                        try {
                            s.setRepeatingRequest(b.build(), cb, h)
                            if (recording) mr?.start()
                        } catch (e: Exception) { onErr("开始失败($tag): ${e.message}") }
                    }
                    override fun onConfigureFailed(s: CameraCaptureSession) {
                        onErr("会话配置失败($tag)：该镜头/分辨率/组合可能不被支持")
                    }
                })
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
        // 界面固定横屏(rotation=90)
        val sensor = chars.get(CameraCharacteristics.SENSOR_ORIENTATION) ?: 90
        val front = chars.get(CameraCharacteristics.LENS_FACING) == CameraCharacteristics.LENS_FACING_FRONT
        r.setOrientationHint(if (front) (sensor + 90) % 360 else (sensor - 90 + 360) % 360)
        r.prepare()
        mr = r
    }

    private fun push() {
        try { ses?.setRepeatingRequest(req!!.build(), cb, h) } catch (_: Exception) {}
    }

    /** 缩放；返回实际生效的倍率 */
    fun setZoom(z: Float): Float {
        val r = zoomRange ?: return 1f
        zoom = z.coerceIn(r.lower, r.upper)
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
                b.set(CaptureRequest.CONTROL_AE_LOCK, true)
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
