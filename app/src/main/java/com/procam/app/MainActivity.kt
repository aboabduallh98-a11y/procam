package com.procam.app

import android.Manifest
import android.annotation.SuppressLint
import android.app.Activity
import android.app.AlertDialog
import android.content.ContentValues
import android.content.Context
import android.content.pm.PackageManager
import android.graphics.Bitmap
import android.graphics.Color
import android.graphics.ImageFormat
import android.graphics.Matrix
import android.graphics.SurfaceTexture
import android.graphics.Typeface
import android.graphics.drawable.GradientDrawable
import android.hardware.camera2.CameraAccessException
import android.hardware.camera2.CameraCaptureSession
import android.hardware.camera2.CameraCharacteristics
import android.hardware.camera2.CameraDevice
import android.hardware.camera2.CameraManager
import android.hardware.camera2.CameraMetadata
import android.hardware.camera2.CaptureRequest
import android.hardware.camera2.CaptureResult
import android.hardware.camera2.DngCreator
import android.hardware.camera2.TotalCaptureResult
import android.hardware.camera2.params.OutputConfiguration
import android.hardware.camera2.params.SessionConfiguration
import android.hardware.display.DisplayManager
import android.media.Image
import android.media.ImageReader
import android.media.MediaCodecList
import android.media.MediaRecorder
import android.net.Uri
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.HandlerThread
import android.os.Looper
import android.os.ParcelFileDescriptor
import android.os.SystemClock
import android.provider.MediaStore
import android.util.Range
import android.util.Size
import android.view.Gravity
import android.view.KeyEvent
import android.view.Surface
import android.view.TextureView
import android.view.View
import android.view.ViewGroup
import android.view.WindowManager
import android.widget.FrameLayout
import android.widget.HorizontalScrollView
import android.widget.LinearLayout
import android.widget.SeekBar
import android.widget.TextView
import android.widget.Toast
import java.text.SimpleDateFormat
import java.util.ArrayList
import java.util.Date
import java.util.Locale
import java.util.concurrent.Executor
import java.util.concurrent.Executors
import kotlin.math.abs
import kotlin.math.hypot
import kotlin.math.ln
import kotlin.math.max
import kotlin.math.min
import kotlin.math.pow
import kotlin.math.roundToInt

private const val MATCH = ViewGroup.LayoutParams.MATCH_PARENT
private const val WRAP = ViewGroup.LayoutParams.WRAP_CONTENT

class MainActivity : Activity() {

    private enum class Ctl { EV, ISO, SS, FOCUS }

    private class CamOption(
        val logicalId: String,
        val physicalId: String?,
        val label: String,
        val facing: Int
    )

    // ------------------------------------------------------------------ views
    private lateinit var root: FrameLayout
    private lateinit var holder: FrameLayout
    private lateinit var textureView: TextureView
    private lateinit var overlay: AidsOverlay
    private lateinit var flashView: View
    private lateinit var shutter: View
    private lateinit var photoChip: TextView
    private lateinit var videoChip: TextView
    private lateinit var lensChip: TextView
    private lateinit var resChip: TextView
    private lateinit var fpsChip: TextView
    private lateinit var codecChip: TextView
    private lateinit var mbpsChip: TextView
    private lateinit var rawChip: TextView
    private lateinit var histChip: TextView
    private lateinit var zebraChip: TextView
    private lateinit var peakChip: TextView
    private lateinit var gridChip: TextView
    private lateinit var evChip: TextView
    private lateinit var isoChip: TextView
    private lateinit var ssChip: TextView
    private lateinit var focusChip: TextView
    private lateinit var wbChip: TextView
    private lateinit var panel: LinearLayout
    private lateinit var panelLabel: TextView
    private lateinit var seek: SeekBar
    private lateinit var autoBtn: TextView
    private lateinit var timerText: TextView

    // --------------------------------------------------------------- threading
    private val mainHandler = Handler(Looper.getMainLooper())
    private val uiExec = Executor { r -> mainHandler.post(r) }
    private val aidsExec = Executors.newSingleThreadExecutor()
    private lateinit var bgThread: HandlerThread
    private lateinit var bgHandler: Handler
    private val rawLock = Any()

    // ------------------------------------------------------------------ camera
    private lateinit var cameraManager: CameraManager
    private var options: List<CamOption> = emptyList()
    private var optIndex = 0
    private var device: CameraDevice? = null
    private var session: CameraCaptureSession? = null
    private var chars: CameraCharacteristics? = null
    private var opening = false
    private var resumed = false
    private var sessionGen = 0
    private var previewSurface: Surface? = null
    private var previewSize = Size(1920, 1080)
    private var holderW = 0
    private var holderH = 0
    private var permAsked = false

    private var jpegReader: ImageReader? = null
    private var rawReader: ImageReader? = null
    private var jpegSize: Size? = null
    private var rawSize: Size? = null
    private var rawSupported = false
    private var rawEnabled = false

    // خصائص الجهاز
    private var isoRange: Range<Int> = Range(100, 800)
    private var expRange: Range<Long> = Range(1_000_000L, 100_000_000L)
    private var aeCompRange: Range<Int> = Range(0, 0)
    private var aeCompStep = 0f
    private var minFocus = 0f
    private var awbModes: IntArray = intArrayOf(CameraMetadata.CONTROL_AWB_MODE_AUTO)
    private var fpsRanges: List<Range<Int>> = emptyList()

    // ------------------------------------------------------------------- modes
    private var isVideo = false
    private var recording = false
    private var hevcSupported = false

    // إعدادات الفيديو
    private var videoSizes: List<Size> = emptyList()
    private var videoSize: Size? = null
    private var fpsOptions: List<Int> = listOf(30)
    private var fps = 30
    private var hevc = false
    private var bitrateMbps = 30

    // ---------------------------------------------------------- manual controls
    private var autoExp = true
    private var iso = 100
    private var expNs = 10_000_000L
    private var ev = 0
    private var autoFocus = true
    private var focusDiopter = 0f
    private var awbMode = CameraMetadata.CONTROL_AWB_MODE_AUTO
    @Volatile private var lastIso = 100
    @Volatile private var lastExp = 10_000_000L
    private var activeCtl: Ctl? = null
    private var suppressSeek = false

    // ----------------------------------------------------------------- aids
    private var zebraOn = false
    private var peakOn = false
    private var histOn = false
    private var gridOn = false

    // -------------------------------------------------------------- recorder
    private var recorder: MediaRecorder? = null
    private var recUri: Uri? = null
    private var recPfd: ParcelFileDescriptor? = null
    private var recSurface: Surface? = null
    private var recStartMs = 0L
    private var lastRot = -1

    // RAW: ربط الصورة مع بياناتها
    private val pendingImages = HashMap<Long, Image>()
    private val pendingResults = HashMap<Long, TotalCaptureResult>()

    private inline fun safe(block: () -> Unit) {
        try {
            block()
        } catch (e: Exception) {
        }
    }

    private fun dp(v: Int): Int = (v * resources.displayMetrics.density).roundToInt()

    private fun toast(msg: String) {
        runOnUiThread { Toast.makeText(this, msg, Toast.LENGTH_SHORT).show() }
    }

    private fun hasPermission(p: String) =
        checkSelfPermission(p) == PackageManager.PERMISSION_GRANTED

    // ================================================================ lifecycle
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        window.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)
        cameraManager = getSystemService(Context.CAMERA_SERVICE) as CameraManager
        hevcSupported = try {
            MediaCodecList(MediaCodecList.REGULAR_CODECS).codecInfos.any { info ->
                info.isEncoder && info.supportedTypes.any { it.equals("video/hevc", true) }
            }
        } catch (e: Exception) {
            false
        }
        buildOptions()
        buildUi()
        setContentView(root)
        textureView.surfaceTextureListener = object : TextureView.SurfaceTextureListener {
            override fun onSurfaceTextureAvailable(st: SurfaceTexture, w: Int, h: Int) {
                if (resumed) openCamera()
            }

            override fun onSurfaceTextureSizeChanged(st: SurfaceTexture, w: Int, h: Int) {}

            override fun onSurfaceTextureDestroyed(st: SurfaceTexture): Boolean {
                previewSurface = null
                return true
            }

            override fun onSurfaceTextureUpdated(st: SurfaceTexture) {}
        }
    }

    override fun onResume() {
        super.onResume()
        resumed = true
        hideSystemUi()
        bgThread = HandlerThread("cam-bg").also { it.start() }
        bgHandler = Handler(bgThread.looper)
        val dm = getSystemService(Context.DISPLAY_SERVICE) as DisplayManager
        dm.registerDisplayListener(displayListener, mainHandler)
        mainHandler.postDelayed(aidsRunnable, 300)
        if (!hasPermission(Manifest.permission.CAMERA)) {
            if (!permAsked) {
                permAsked = true
                requestPermissions(
                    arrayOf(Manifest.permission.CAMERA, Manifest.permission.RECORD_AUDIO), 1
                )
            }
            return
        }
        if (textureView.isAvailable) openCamera()
    }

    override fun onPause() {
        resumed = false
        mainHandler.removeCallbacks(aidsRunnable)
        mainHandler.removeCallbacks(timerRunnable)
        closeCamera()
        safe {
            val dm = getSystemService(Context.DISPLAY_SERVICE) as DisplayManager
            dm.unregisterDisplayListener(displayListener)
        }
        if (::bgThread.isInitialized) bgThread.quitSafely()
        super.onPause()
    }

    override fun onWindowFocusChanged(hasFocus: Boolean) {
        super.onWindowFocusChanged(hasFocus)
        if (hasFocus) hideSystemUi()
    }

    override fun onRequestPermissionsResult(
        requestCode: Int,
        permissions: Array<out String>,
        grantResults: IntArray
    ) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults)
        if (hasPermission(Manifest.permission.CAMERA)) {
            if (resumed && textureView.isAvailable) openCamera()
        } else {
            toast("التطبيق يحتاج إذن الكاميرا ليعمل")
        }
    }

    override fun onKeyDown(keyCode: Int, event: KeyEvent?): Boolean {
        if (keyCode == KeyEvent.KEYCODE_VOLUME_UP || keyCode == KeyEvent.KEYCODE_VOLUME_DOWN) {
            onShutter()
            return true
        }
        return super.onKeyDown(keyCode, event)
    }

    @Suppress("DEPRECATION")
    private fun hideSystemUi() {
        window.decorView.systemUiVisibility = (View.SYSTEM_UI_FLAG_FULLSCREEN
                or View.SYSTEM_UI_FLAG_HIDE_NAVIGATION
                or View.SYSTEM_UI_FLAG_IMMERSIVE_STICKY
                or View.SYSTEM_UI_FLAG_LAYOUT_STABLE
                or View.SYSTEM_UI_FLAG_LAYOUT_HIDE_NAVIGATION
                or View.SYSTEM_UI_FLAG_LAYOUT_FULLSCREEN)
    }

    private val displayListener = object : DisplayManager.DisplayListener {
        override fun onDisplayAdded(displayId: Int) {}
        override fun onDisplayRemoved(displayId: Int) {}
        override fun onDisplayChanged(displayId: Int) {
            val rot = displayRotationDegrees()
            if (rot == lastRot) return
            lastRot = rot
            applyTransform()
            if (isVideo && !recording && device != null) startSession()
        }
    }

    // ================================================================ cameras
    private fun buildOptions() {
        val list = ArrayList<CamOption>()
        try {
            val all = cameraManager.cameraIdList.toSet()
            for (id in cameraManager.cameraIdList) {
                val ch = cameraManager.getCameraCharacteristics(id)
                val caps = ch.get(CameraCharacteristics.REQUEST_AVAILABLE_CAPABILITIES) ?: IntArray(0)
                if (!caps.contains(CameraMetadata.REQUEST_AVAILABLE_CAPABILITIES_BACKWARD_COMPATIBLE)) continue
                val facing = ch.get(CameraCharacteristics.LENS_FACING) ?: CameraMetadata.LENS_FACING_BACK
                list.add(CamOption(id, null, labelFor(id, ch, facing, false), facing))
                if (caps.contains(CameraMetadata.REQUEST_AVAILABLE_CAPABILITIES_LOGICAL_MULTI_CAMERA)) {
                    for (pid in ch.physicalCameraIds) {
                        if (all.contains(pid)) continue
                        try {
                            val pch = cameraManager.getCameraCharacteristics(pid)
                            list.add(CamOption(id, pid, labelFor(pid, pch, facing, true), facing))
                        } catch (e: Exception) {
                        }
                    }
                }
            }
        } catch (e: Exception) {
        }
        options = list.sortedBy { if (it.facing == CameraMetadata.LENS_FACING_BACK) 0 else 1 }
    }

    private fun labelFor(id: String, ch: CameraCharacteristics, facing: Int, physical: Boolean): String {
        val f = ch.get(CameraCharacteristics.LENS_INFO_AVAILABLE_FOCAL_LENGTHS)?.firstOrNull()
        val sz = ch.get(CameraCharacteristics.SENSOR_INFO_PHYSICAL_SIZE)
        val eq = if (f != null && sz != null) {
            (f * 43.27f / hypot(sz.width, sz.height)).roundToInt()
        } else null
        val side = when (facing) {
            CameraMetadata.LENS_FACING_FRONT -> "Front"
            CameraMetadata.LENS_FACING_BACK -> "Back"
            else -> "Ext"
        }
        return side + (if (eq != null) " ${eq}mm" else "") + (if (physical) " (phys)" else "") + " #" + id
    }

    @SuppressLint("MissingPermission")
    private fun openCamera() {
        if (device != null || opening) return
        if (!hasPermission(Manifest.permission.CAMERA)) return
        if (!textureView.isAvailable) return
        val opt = options.getOrNull(optIndex)
        if (opt == null) {
            toast("لم يتم العثور على كاميرا")
            return
        }
        opening = true
        try {
            chars = try {
                cameraManager.getCameraCharacteristics(opt.physicalId ?: opt.logicalId)
            } catch (e: Exception) {
                cameraManager.getCameraCharacteristics(opt.logicalId)
            }
            loadCharacteristics()
            updateLensChip()
            cameraManager.openCamera(opt.logicalId, stateCb, mainHandler)
        } catch (e: Exception) {
            opening = false
            onCameraFailed("تعذر فتح الكاميرا")
        }
    }

    private val stateCb = object : CameraDevice.StateCallback() {
        override fun onOpened(camera: CameraDevice) {
            opening = false
            if (!resumed) {
                camera.close()
                return
            }
            device = camera
            startSession()
        }

        override fun onDisconnected(camera: CameraDevice) {
            opening = false
            camera.close()
            if (device === camera) {
                device = null
                session = null
            }
        }

        override fun onError(camera: CameraDevice, error: Int) {
            opening = false
            camera.close()
            if (device === camera) {
                device = null
                session = null
            }
            onCameraFailed("حدث خطأ في الكاميرا")
        }
    }

    private fun onCameraFailed(msg: String) {
        toast(msg)
        closeCamera()
        if (optIndex != 0 && resumed) {
            optIndex = 0
            updateLensChip()
            openCamera()
        }
    }

    private fun closeCamera() {
        sessionGen++
        if (recording) stopRecording(false)
        discardRecorder()
        safe { session?.close() }
        session = null
        safe { device?.close() }
        device = null
        releaseReaders()
        synchronized(rawLock) {
            for (img in pendingImages.values) safe { img.close() }
            pendingImages.clear()
            pendingResults.clear()
        }
        opening = false
    }

    private fun releaseReaders() {
        safe { jpegReader?.close() }
        safe { rawReader?.close() }
        jpegReader = null
        rawReader = null
    }

    private fun loadCharacteristics() {
        val c = chars ?: return
        isoRange = c.get(CameraCharacteristics.SENSOR_INFO_SENSITIVITY_RANGE) ?: Range(100, 800)
        expRange = c.get(CameraCharacteristics.SENSOR_INFO_EXPOSURE_TIME_RANGE) ?: Range(1_000_000L, 100_000_000L)
        aeCompRange = c.get(CameraCharacteristics.CONTROL_AE_COMPENSATION_RANGE) ?: Range(0, 0)
        aeCompStep = c.get(CameraCharacteristics.CONTROL_AE_COMPENSATION_STEP)?.toFloat() ?: 0f
        minFocus = c.get(CameraCharacteristics.LENS_INFO_MINIMUM_FOCUS_DISTANCE) ?: 0f
        awbModes = c.get(CameraCharacteristics.CONTROL_AWB_AVAILABLE_MODES)
            ?: intArrayOf(CameraMetadata.CONTROL_AWB_MODE_AUTO)
        fpsRanges = c.get(CameraCharacteristics.CONTROL_AE_AVAILABLE_TARGET_FPS_RANGES)?.toList()
            ?: emptyList()

        iso = iso.coerceIn(isoRange.lower, isoRange.upper)
        expNs = expNs.coerceIn(expRange.lower, max(expRange.lower, expRange.upper))
        ev = ev.coerceIn(aeCompRange.lower, aeCompRange.upper)
        focusDiopter = focusDiopter.coerceIn(0f, max(0f, minFocus))
        if (!awbModes.contains(awbMode)) awbMode = CameraMetadata.CONTROL_AWB_MODE_AUTO

        val map = c.get(CameraCharacteristics.SCALER_STREAM_CONFIGURATION_MAP)
        val caps = c.get(CameraCharacteristics.REQUEST_AVAILABLE_CAPABILITIES) ?: IntArray(0)

        // أحجام الصور
        val jpegs = map?.getOutputSizes(ImageFormat.JPEG)?.toList() ?: emptyList()
        jpegSize = jpegs.filter { abs(it.width.toDouble() / it.height - 4.0 / 3.0) < 0.02 }
            .maxByOrNull { it.width.toLong() * it.height }
            ?: jpegs.maxByOrNull { it.width.toLong() * it.height }
        rawSize = map?.getOutputSizes(ImageFormat.RAW_SENSOR)?.maxByOrNull { it.width.toLong() * it.height }
        rawSupported = caps.contains(CameraMetadata.REQUEST_AVAILABLE_CAPABILITIES_RAW) && rawSize != null
        if (!rawSupported) rawEnabled = false

        // أحجام الفيديو
        val rec = map?.getOutputSizes(MediaRecorder::class.java)?.toList() ?: emptyList()
        val wanted = listOf(Size(3840, 2160), Size(2560, 1440), Size(1920, 1080), Size(1280, 720))
        var vs = wanted.filter { w -> rec.any { it.width == w.width && it.height == w.height } }
        if (vs.isEmpty()) vs = rec.sortedByDescending { it.width * it.height }.take(3)
        videoSizes = vs
        val cur = videoSize
        if (cur == null || !vs.contains(cur)) {
            videoSize = vs.firstOrNull { it.width == 1920 } ?: vs.firstOrNull()
        }

        // معدلات الإطارات
        val fo = listOf(24, 25, 30, 60).filter { fpsRangeFor(it) != null }
        fpsOptions = if (fo.isEmpty()) listOf(30) else fo
        if (!fpsOptions.contains(fps)) fps = fpsOptions.firstOrNull { it == 30 } ?: fpsOptions.first()

        runOnUiThread {
            refreshVideoChips()
            refreshCtlChips()
            refreshPanel()
        }
    }

    private fun fpsRangeFor(f: Int): Range<Int>? {
        return fpsRanges.firstOrNull { it.lower == f && it.upper == f }
            ?: fpsRanges.filter { it.upper == f }.maxByOrNull { it.lower }
    }

    private fun choosePreviewSize(target: Size): Size {
        val map = chars?.get(CameraCharacteristics.SCALER_STREAM_CONFIGURATION_MAP)
        val list = map?.getOutputSizes(SurfaceTexture::class.java)?.toList() ?: emptyList()
        val ratio = target.width.toDouble() / target.height
        val fit = list.filter { it.width <= 1920 && it.height <= 1080 }
        return fit.filter { abs(it.width.toDouble() / it.height - ratio) < 0.02 }
            .maxByOrNull { it.width * it.height }
            ?: fit.maxByOrNull { it.width * it.height }
            ?: Size(1280, 720)
    }

    // ================================================================ session
    private fun startSession() {
        val dev = device ?: return
        val st = textureView.surfaceTexture ?: return
        val opt = options.getOrNull(optIndex) ?: return
        val gen = ++sessionGen

        safe { session?.close() }
        session = null
        discardRecorder()
        releaseReaders()

        val target = if (isVideo) (videoSize ?: Size(1920, 1080)) else (jpegSize ?: Size(4, 3))
        previewSize = choosePreviewSize(target)
        st.setDefaultBufferSize(previewSize.width, previewSize.height)
        if (previewSurface == null) previewSurface = Surface(st)
        fitPreview()

        val surfaces = ArrayList<Surface>()
        surfaces.add(previewSurface!!)
        recSurface = null

        if (isVideo) {
            if (prepareRecorder()) {
                val rs = recorder?.surface
                if (rs != null) {
                    recSurface = rs
                    surfaces.add(rs)
                }
            }
        } else {
            jpegSize?.let { s ->
                val r = ImageReader.newInstance(s.width, s.height, ImageFormat.JPEG, 3)
                r.setOnImageAvailableListener(jpegListener, bgHandler)
                jpegReader = r
                surfaces.add(r.surface)
            }
            if (rawEnabled && rawSupported) {
                rawSize?.let { s ->
                    val r = ImageReader.newInstance(s.width, s.height, ImageFormat.RAW_SENSOR, 3)
                    r.setOnImageAvailableListener(rawListener, bgHandler)
                    rawReader = r
                    surfaces.add(r.surface)
                }
            }
        }

        val pid = opt.physicalId
        val outs = surfaces.map { s ->
            val o = OutputConfiguration(s)
            if (pid != null) o.setPhysicalCameraId(pid)
            o
        }

        try {
            val cb = object : CameraCaptureSession.StateCallback() {
                override fun onConfigured(s: CameraCaptureSession) {
                    if (gen != sessionGen || device == null) {
                        safe { s.close() }
                        return
                    }
                    session = s
                    updatePreview()
                }

                override fun onConfigureFailed(s: CameraCaptureSession) {
                    if (gen != sessionGen) return
                    onCameraFailed("هذا الإعداد أو هذه العدسة غير مدعومة على جهازك")
                }
            }
            dev.createCaptureSession(
                SessionConfiguration(SessionConfiguration.SESSION_REGULAR, outs, uiExec, cb)
            )
        } catch (e: Exception) {
            onCameraFailed("تعذر بدء المعاينة")
        }
    }

    private val previewCb = object : CameraCaptureSession.CaptureCallback() {
        override fun onCaptureCompleted(
            session: CameraCaptureSession,
            request: CaptureRequest,
            result: TotalCaptureResult
        ) {
            result.get(CaptureResult.SENSOR_SENSITIVITY)?.let { lastIso = it }
            result.get(CaptureResult.SENSOR_EXPOSURE_TIME)?.let { lastExp = it }
        }
    }

    private fun applySettings(b: CaptureRequest.Builder, still: Boolean) {
        val c = chars ?: return
        b.set(CaptureRequest.CONTROL_MODE, CameraMetadata.CONTROL_MODE_AUTO)
        if (autoExp) {
            b.set(CaptureRequest.CONTROL_AE_MODE, CameraMetadata.CONTROL_AE_MODE_ON)
            b.set(CaptureRequest.CONTROL_AE_EXPOSURE_COMPENSATION, ev)
        } else {
            b.set(CaptureRequest.CONTROL_AE_MODE, CameraMetadata.CONTROL_AE_MODE_OFF)
            b.set(CaptureRequest.SENSOR_SENSITIVITY, iso)
            b.set(CaptureRequest.SENSOR_EXPOSURE_TIME, expNs)
            if (isVideo && !still) {
                b.set(CaptureRequest.SENSOR_FRAME_DURATION, 1_000_000_000L / fps)
            }
        }
        if (autoFocus) {
            b.set(
                CaptureRequest.CONTROL_AF_MODE,
                if (isVideo) CameraMetadata.CONTROL_AF_MODE_CONTINUOUS_VIDEO
                else CameraMetadata.CONTROL_AF_MODE_CONTINUOUS_PICTURE
            )
        } else {
            b.set(CaptureRequest.CONTROL_AF_MODE, CameraMetadata.CONTROL_AF_MODE_OFF)
            b.set(CaptureRequest.LENS_FOCUS_DISTANCE, focusDiopter)
        }
        b.set(CaptureRequest.CONTROL_AWB_MODE, awbMode)
        if (isVideo && !still) {
            fpsRangeFor(fps)?.let { b.set(CaptureRequest.CONTROL_AE_TARGET_FPS_RANGE, it) }
        }
        val ois = c.get(CameraCharacteristics.LENS_INFO_AVAILABLE_OPTICAL_STABILIZATION)
        if (ois != null && ois.contains(CameraMetadata.LENS_OPTICAL_STABILIZATION_MODE_ON)) {
            b.set(CaptureRequest.LENS_OPTICAL_STABILIZATION_MODE, CameraMetadata.LENS_OPTICAL_STABILIZATION_MODE_ON)
        }
    }

    private fun updatePreview() {
        val dev = device ?: return
        val s = session ?: return
        val ps = previewSurface ?: return
        try {
            val b = dev.createCaptureRequest(
                if (isVideo) CameraDevice.TEMPLATE_RECORD else CameraDevice.TEMPLATE_PREVIEW
            )
            b.addTarget(ps)
            val rs = recSurface
            if (isVideo && rs != null) b.addTarget(rs)
            applySettings(b, false)
            s.setRepeatingRequest(b.build(), previewCb, bgHandler)
        } catch (e: CameraAccessException) {
        } catch (e: IllegalStateException) {
        } catch (e: IllegalArgumentException) {
        }
    }

    // ================================================================ layout
    private fun fitPreview() {
        val cw = root.width
        val chh = root.height
        if (cw == 0 || chh == 0) {
            root.post { fitPreview() }
            return
        }
        val scale = min(cw.toFloat() / previewSize.width, chh.toFloat() / previewSize.height)
        val lp = FrameLayout.LayoutParams(
            (previewSize.width * scale).toInt(),
            (previewSize.height * scale).toInt(),
            Gravity.CENTER
        )
        holderW = lp.width
        holderH = lp.height
        holder.layoutParams = lp
        applyTransform()
    }

    @Suppress("DEPRECATION")
    private fun displayRotationDegrees(): Int = when (windowManager.defaultDisplay.rotation) {
        Surface.ROTATION_90 -> 90
        Surface.ROTATION_180 -> 180
        Surface.ROTATION_270 -> 270
        else -> 0
    }

    private fun outputOrientation(): Int {
        val c = chars ?: return 0
        val sensor = c.get(CameraCharacteristics.SENSOR_ORIENTATION) ?: 0
        val rot = displayRotationDegrees()
        val facing = c.get(CameraCharacteristics.LENS_FACING) ?: CameraMetadata.LENS_FACING_BACK
        return if (facing == CameraMetadata.LENS_FACING_FRONT) (sensor + rot) % 360
        else (sensor - rot + 360) % 360
    }

    private fun applyTransform() {
        val m = Matrix()
        if (outputOrientation() == 180) m.postRotate(180f, holderW / 2f, holderH / 2f)
        textureView.setTransform(m)
    }

    // ================================================================ photo
    private fun takePhoto() {
        val dev = device ?: return
        val s = session ?: return
        val jr = jpegReader ?: return
        try {
            val b = dev.createCaptureRequest(CameraDevice.TEMPLATE_STILL_CAPTURE)
            b.addTarget(jr.surface)
            val rr = rawReader
            if (rawEnabled && rr != null) b.addTarget(rr.surface)
            applySettings(b, true)
            b.set(CaptureRequest.JPEG_ORIENTATION, outputOrientation())
            b.set(CaptureRequest.JPEG_QUALITY, 98.toByte())
            s.capture(b.build(), stillCb, bgHandler)
        } catch (e: Exception) {
            toast("تعذر التقاط الصورة")
        }
    }

    private val stillCb = object : CameraCaptureSession.CaptureCallback() {
        override fun onCaptureCompleted(
            session: CameraCaptureSession,
            request: CaptureRequest,
            result: TotalCaptureResult
        ) {
            if (rawReader != null) onRawResult(result)
            runOnUiThread { flashFeedback() }
        }
    }

    private fun flashFeedback() {
        flashView.alpha = 0.6f
        flashView.animate().alpha(0f).setDuration(180).start()
    }

    private val jpegListener = ImageReader.OnImageAvailableListener { reader ->
        val img = reader.acquireNextImage() ?: return@OnImageAvailableListener
        try {
            val buf = img.planes[0].buffer
            val bytes = ByteArray(buf.remaining())
            buf.get(bytes)
            val uri = insertMedia(
                MediaStore.Images.Media.EXTERNAL_CONTENT_URI, "image/jpeg", ".jpg", "DCIM/ProCam"
            )
            if (uri != null) {
                contentResolver.openOutputStream(uri)?.use { it.write(bytes) }
                finishPending(uri)
            }
        } catch (e: Exception) {
            toast("تعذر حفظ الصورة")
        } finally {
            img.close()
        }
    }

    private val rawListener = ImageReader.OnImageAvailableListener { reader ->
        val img = reader.acquireNextImage() ?: return@OnImageAvailableListener
        var result: TotalCaptureResult? = null
        synchronized(rawLock) {
            result = pendingResults.remove(img.timestamp)
            if (result == null) {
                pendingImages[img.timestamp] = img
                if (pendingImages.size > 2) {
                    val oldest = pendingImages.keys.minOrNull()
                    if (oldest != null) pendingImages.remove(oldest)?.close()
                }
            }
        }
        val r = result
        if (r != null) saveDng(img, r)
    }

    private fun onRawResult(r: TotalCaptureResult) {
        val ts = r.get(CaptureResult.SENSOR_TIMESTAMP) ?: return
        var img: Image? = null
        synchronized(rawLock) {
            img = pendingImages.remove(ts)
            if (img == null) pendingResults[ts] = r
        }
        val i = img
        if (i != null) saveDng(i, r)
    }

    private fun saveDng(img: Image, result: TotalCaptureResult) {
        val c = chars
        if (c == null) {
            img.close()
            return
        }
        try {
            val dng = DngCreator(c, result)
            val exif = when (outputOrientation()) {
                90 -> 6
                180 -> 3
                270 -> 8
                else -> 1
            }
            dng.setOrientation(exif)
            val uri = insertMedia(
                MediaStore.Images.Media.EXTERNAL_CONTENT_URI, "image/x-adobe-dng", ".dng", "DCIM/ProCam"
            )
            if (uri != null) {
                contentResolver.openOutputStream(uri)?.use { dng.writeImage(it, img) }
                finishPending(uri)
            }
            dng.close()
        } catch (e: Exception) {
            toast("تعذر حفظ ملف RAW")
        } finally {
            img.close()
        }
    }

    private fun insertMedia(collection: Uri, mime: String, ext: String, rel: String): Uri? {
        val name = "PROCAM_" + SimpleDateFormat("yyyyMMdd_HHmmss_SSS", Locale.US).format(Date()) + ext
        val cv = ContentValues()
        cv.put(MediaStore.MediaColumns.DISPLAY_NAME, name)
        cv.put(MediaStore.MediaColumns.MIME_TYPE, mime)
        cv.put(MediaStore.MediaColumns.RELATIVE_PATH, rel)
        cv.put(MediaStore.MediaColumns.IS_PENDING, 1)
        return contentResolver.insert(collection, cv)
    }

    private fun finishPending(uri: Uri) {
        val cv = ContentValues()
        cv.put(MediaStore.MediaColumns.IS_PENDING, 0)
        contentResolver.update(uri, cv, null, null)
    }

    // ================================================================ video
    @Suppress("DEPRECATION")
    private fun prepareRecorder(): Boolean {
        discardRecorder()
        val vs = videoSize ?: return false
        try {
            val uri = insertMedia(
                MediaStore.Video.Media.EXTERNAL_CONTENT_URI, "video/mp4", ".mp4", "DCIM/ProCam"
            ) ?: return false
            recUri = uri
            val pfd = contentResolver.openFileDescriptor(uri, "w") ?: return false
            recPfd = pfd
            val r = if (Build.VERSION.SDK_INT >= 31) MediaRecorder(this) else MediaRecorder()
            val audio = hasPermission(Manifest.permission.RECORD_AUDIO)
            if (audio) r.setAudioSource(MediaRecorder.AudioSource.MIC)
            r.setVideoSource(MediaRecorder.VideoSource.SURFACE)
            r.setOutputFormat(MediaRecorder.OutputFormat.MPEG_4)
            r.setOutputFile(pfd.fileDescriptor)
            r.setVideoEncodingBitRate(bitrateMbps * 1_000_000)
            r.setVideoFrameRate(fps)
            r.setVideoSize(vs.width, vs.height)
            r.setVideoEncoder(
                if (hevc) MediaRecorder.VideoEncoder.HEVC else MediaRecorder.VideoEncoder.H264
            )
            if (audio) {
                r.setAudioEncoder(MediaRecorder.AudioEncoder.AAC)
                r.setAudioEncodingBitRate(192_000)
                r.setAudioSamplingRate(48_000)
            }
            r.setOrientationHint(outputOrientation())
            r.prepare()
            recorder = r
            return true
        } catch (e: Exception) {
            discardRecorder()
            toast("إعدادات الفيديو غير مدعومة، جرّب دقة أو كودك آخر")
            return false
        }
    }

    /** يلغي مسجّل لم يُستخدم ويحذف ملفه الفارغ. */
    private fun discardRecorder() {
        if (recording) return
        val r = recorder
        recorder = null
        recSurface = null
        if (r != null) {
            safe { r.reset() }
            safe { r.release() }
        }
        safe { recPfd?.close() }
        recPfd = null
        val u = recUri
        recUri = null
        if (u != null) safe { contentResolver.delete(u, null, null) }
    }

    private fun startRecording() {
        val r = recorder
        if (r == null || session == null) {
            toast("التسجيل غير جاهز بهذه الإعدادات")
            return
        }
        try {
            r.start()
            recording = true
            recStartMs = SystemClock.elapsedRealtime()
            timerText.visibility = View.VISIBLE
            mainHandler.post(timerRunnable)
            updateShutterUi()
            setUiLockedForRecording(true)
        } catch (e: Exception) {
            toast("تعذر بدء التسجيل")
            startSession()
        }
    }

    private fun stopRecording(restart: Boolean) {
        val r = recorder ?: return
        recording = false
        mainHandler.removeCallbacks(timerRunnable)
        safe { session?.stopRepeating() }
        safe { session?.abortCaptures() }
        var ok = true
        try {
            r.stop()
        } catch (e: RuntimeException) {
            ok = false
        }
        safe { r.release() }
        recorder = null
        recSurface = null
        safe { recPfd?.close() }
        recPfd = null
        val u = recUri
        recUri = null
        if (u != null) {
            if (ok) safe { finishPending(u) } else safe { contentResolver.delete(u, null, null) }
        }
        runOnUiThread {
            timerText.visibility = View.GONE
            updateShutterUi()
            setUiLockedForRecording(false)
            Toast.makeText(
                this,
                if (ok) "تم حفظ الفيديو في DCIM/ProCam" else "التسجيل قصير جداً ولم يُحفظ",
                Toast.LENGTH_SHORT
            ).show()
        }
        if (restart && resumed) startSession()
    }

    private val timerRunnable = object : Runnable {
        override fun run() {
            if (!recording) return
            val s = (SystemClock.elapsedRealtime() - recStartMs) / 1000
            timerText.text = String.format(Locale.US, "● %02d:%02d", s / 60, s % 60)
            mainHandler.postDelayed(this, 500)
        }
    }

    private fun setUiLockedForRecording(locked: Boolean) {
        val a = if (locked) 0.4f else 1f
        for (v in listOf(photoChip, videoChip, lensChip, resChip, fpsChip, codecChip, mbpsChip)) {
            v.alpha = a
        }
    }

    // ================================================================ aids
    private val aidsRunnable = object : Runnable {
        override fun run() {
            if (resumed && (zebraOn || peakOn || histOn) && device != null &&
                textureView.isAvailable && textureView.width > 0 && textureView.height > 0
            ) {
                val w = 480
                val h = max(1, (w.toFloat() * textureView.height / textureView.width).roundToInt())
                val bmp = try {
                    textureView.getBitmap(w, h)
                } catch (e: Exception) {
                    null
                }
                if (bmp != null) aidsExec.execute { analyze(bmp, w, h) }
            }
            mainHandler.postDelayed(this, 200)
        }
    }

    private fun analyze(bmp: Bitmap, w: Int, h: Int) {
        val px = IntArray(w * h)
        bmp.getPixels(px, 0, w, 0, 0, w, h)
        bmp.recycle()
        val luma = IntArray(w * h)
        val hist = IntArray(64)
        for (i in px.indices) {
            val p = px[i]
            val l = (((p shr 16) and 255) * 77 + ((p shr 8) and 255) * 150 + (p and 255) * 29) shr 8
            luma[i] = l
            hist[l shr 2]++
        }
        var zb: Bitmap? = null
        var pk: Bitmap? = null
        if (zebraOn) {
            val out = IntArray(w * h)
            for (y in 0 until h) {
                for (x in 0 until w) {
                    val i = y * w + x
                    if (luma[i] >= 240 && ((((x + y) shr 2) and 1) == 0)) out[i] = 0xDDFF2020.toInt()
                }
            }
            val b = Bitmap.createBitmap(w, h, Bitmap.Config.ARGB_8888)
            b.setPixels(out, 0, w, 0, 0, w, h)
            zb = b
        }
        if (peakOn) {
            val out = IntArray(w * h)
            for (y in 1 until h - 1) {
                for (x in 1 until w - 1) {
                    val i = y * w + x
                    val lap = abs(4 * luma[i] - luma[i - 1] - luma[i + 1] - luma[i - w] - luma[i + w])
                    if (lap > 45) out[i] = 0xFF00FF55.toInt()
                }
            }
            val b = Bitmap.createBitmap(w, h, Bitmap.Config.ARGB_8888)
            b.setPixels(out, 0, w, 0, 0, w, h)
            pk = b
        }
        mainHandler.post {
            overlay.zebra = if (zebraOn) zb else null
            overlay.peak = if (peakOn) pk else null
            overlay.hist = if (histOn) hist else null
            overlay.invalidate()
        }
    }

    private fun refreshAidsOverlay() {
        overlay.showHist = histOn
        overlay.showGrid = gridOn
        if (!zebraOn) overlay.zebra = null
        if (!peakOn) overlay.peak = null
        if (!histOn) overlay.hist = null
        overlay.invalidate()
    }

    // ================================================================ controls
    private fun expMaxCap(): Long {
        val cap = if (isVideo) 1_000_000_000L / fps else 500_000_000L
        return max(expRange.lower, min(expRange.upper, cap))
    }

    private fun posToIso(p: Int): Int {
        val mn = max(1, isoRange.lower).toDouble()
        val mx = max(mn, isoRange.upper.toDouble())
        return (mn * (mx / mn).pow(p / 100.0)).roundToInt().coerceIn(isoRange.lower, isoRange.upper)
    }

    private fun isoToPos(v: Int): Int {
        val mn = max(1, isoRange.lower).toDouble()
        val mx = max(mn, isoRange.upper.toDouble())
        if (mx <= mn) return 0
        return (100.0 * ln(max(mn, v.toDouble()) / mn) / ln(mx / mn)).roundToInt().coerceIn(0, 100)
    }

    private fun posToExp(p: Int): Long {
        val mn = max(1L, expRange.lower).toDouble()
        val cap = expMaxCap()
        val mx = max(mn, cap.toDouble())
        return (mn * (mx / mn).pow(p / 100.0)).toLong().coerceIn(expRange.lower, cap)
    }

    private fun expToPos(v: Long): Int {
        val mn = max(1L, expRange.lower).toDouble()
        val mx = max(mn, expMaxCap().toDouble())
        if (mx <= mn) return 0
        return (100.0 * ln(max(mn, v.toDouble()) / mn) / ln(mx / mn)).roundToInt().coerceIn(0, 100)
    }

    private fun fmtShutter(ns: Long): String {
        val s = ns / 1e9
        return if (s >= 0.5) String.format(Locale.US, "%.1fs", s) else "1/" + (1.0 / s).roundToInt()
    }

    private fun fmtFocus(): String =
        if (focusDiopter < 0.05f) "INF" else "${(100f / focusDiopter).roundToInt()}cm"

    private fun wbName(m: Int): String = when (m) {
        CameraMetadata.CONTROL_AWB_MODE_AUTO -> "AUTO"
        CameraMetadata.CONTROL_AWB_MODE_INCANDESCENT -> "2800K"
        CameraMetadata.CONTROL_AWB_MODE_FLUORESCENT -> "4000K"
        CameraMetadata.CONTROL_AWB_MODE_WARM_FLUORESCENT -> "3000K"
        CameraMetadata.CONTROL_AWB_MODE_DAYLIGHT -> "5500K"
        CameraMetadata.CONTROL_AWB_MODE_CLOUDY_DAYLIGHT -> "6500K"
        CameraMetadata.CONTROL_AWB_MODE_TWILIGHT -> "TWILIGHT"
        CameraMetadata.CONTROL_AWB_MODE_SHADE -> "7500K"
        else -> "WB"
    }

    private fun goManual() {
        if (autoExp) {
            autoExp = false
            iso = lastIso.coerceIn(isoRange.lower, isoRange.upper)
            expNs = lastExp.coerceIn(expRange.lower, expMaxCap())
        }
    }

    private fun selectCtl(c: Ctl) {
        activeCtl = if (activeCtl == c) null else c
        refreshPanel()
    }

    private fun refreshPanel() {
        val c = activeCtl
        if (c == null) {
            panel.visibility = View.GONE
            refreshCtlChips()
            return
        }
        panel.visibility = View.VISIBLE
        suppressSeek = true
        seek.isEnabled = true
        when (c) {
            Ctl.EV -> {
                seek.max = max(1, aeCompRange.upper - aeCompRange.lower)
                seek.progress = ev - aeCompRange.lower
                seek.isEnabled = aeCompRange.upper > aeCompRange.lower
            }
            Ctl.ISO -> {
                seek.max = 100
                seek.progress = isoToPos(if (autoExp) lastIso else iso)
            }
            Ctl.SS -> {
                seek.max = 100
                seek.progress = expToPos(if (autoExp) lastExp else expNs)
            }
            Ctl.FOCUS -> {
                seek.max = 100
                seek.isEnabled = minFocus > 0f
                seek.progress = if (minFocus > 0f) (focusDiopter / minFocus * 100f).roundToInt().coerceIn(0, 100) else 0
            }
        }
        suppressSeek = false
        refreshPanelLabel()
        refreshCtlChips()
    }

    private fun refreshPanelLabel() {
        panelLabel.text = when (activeCtl) {
            Ctl.EV -> "EV " + String.format(Locale.US, "%+.1f", ev * aeCompStep)
            Ctl.ISO -> "ISO " + (if (autoExp) lastIso else iso)
            Ctl.SS -> "SS " + fmtShutter(if (autoExp) lastExp else expNs)
            Ctl.FOCUS -> "FOCUS " + (if (autoFocus) "AF" else fmtFocus())
            else -> ""
        }
    }

    private fun refreshCtlChips() {
        evChip.text = "EV\n" + String.format(Locale.US, "%+.1f", ev * aeCompStep)
        isoChip.text = "ISO\n" + (if (autoExp) "AUTO" else iso.toString())
        ssChip.text = "SS\n" + (if (autoExp) "AUTO" else fmtShutter(expNs))
        focusChip.text = "FOCUS\n" + (if (autoFocus) "AF" else fmtFocus())
        wbChip.text = "WB\n" + wbName(awbMode)
        styleChip(evChip, activeCtl == Ctl.EV)
        styleChip(isoChip, activeCtl == Ctl.ISO)
        styleChip(ssChip, activeCtl == Ctl.SS)
        styleChip(focusChip, activeCtl == Ctl.FOCUS)
    }

    private fun refreshVideoChips() {
        val vs = videoSize
        resChip.text = if (vs != null) resName(vs) else "RES"
        fpsChip.text = "$fps fps"
        codecChip.text = if (hevc) "HEVC" else "H.264"
        mbpsChip.text = "$bitrateMbps Mbps"
        rawChip.text = "RAW " + (if (rawEnabled) "ON" else "OFF")
        styleChip(rawChip, rawEnabled)
    }

    private fun resName(s: Size): String = when (s.height) {
        2160 -> "4K"
        1440 -> "1440p"
        1080 -> "1080p"
        720 -> "720p"
        else -> "${s.width}x${s.height}"
    }

    private fun updateLensChip() {
        runOnUiThread { lensChip.text = options.getOrNull(optIndex)?.label ?: "Camera" }
    }

    private fun setMode(video: Boolean) {
        if (recording || video == isVideo) return
        isVideo = video
        updateModeUi()
        if (!autoExp) expNs = expNs.coerceIn(expRange.lower, expMaxCap())
        refreshPanel()
        if (device != null) startSession()
    }

    private fun updateModeUi() {
        styleChip(photoChip, !isVideo)
        styleChip(videoChip, isVideo)
        val vv = if (isVideo) View.VISIBLE else View.GONE
        val pv = if (isVideo) View.GONE else View.VISIBLE
        resChip.visibility = vv
        fpsChip.visibility = vv
        codecChip.visibility = vv
        mbpsChip.visibility = vv
        rawChip.visibility = pv
        updateShutterUi()
    }

    private fun updateShutterUi() {
        val g = GradientDrawable()
        if (isVideo) {
            g.setColor(0xFFE53935.toInt())
            g.cornerRadius = if (recording) dp(14).toFloat() else dp(36).toFloat()
        } else {
            g.setColor(Color.WHITE)
            g.cornerRadius = dp(36).toFloat()
        }
        g.setStroke(dp(4), 0x66FFFFFF)
        shutter.background = g
    }

    private fun onShutter() {
        if (device == null || session == null) return
        if (isVideo) {
            if (recording) stopRecording(true) else startRecording()
        } else {
            takePhoto()
        }
    }

    // ================================================================ UI build
    private fun styleChip(t: TextView, active: Boolean) {
        val g = GradientDrawable()
        g.cornerRadius = dp(8).toFloat()
        g.setColor(if (active) 0xFFFFC107.toInt() else 0x99000000.toInt())
        t.background = g
        t.setTextColor(if (active) Color.BLACK else Color.WHITE)
    }

    private fun chip(text: String, onClick: () -> Unit): TextView {
        val t = TextView(this)
        t.text = text
        t.textSize = 12f
        t.typeface = Typeface.DEFAULT_BOLD
        t.gravity = Gravity.CENTER
        t.minWidth = dp(54)
        t.setPadding(dp(10), dp(6), dp(10), dp(6))
        styleChip(t, false)
        t.setOnClickListener { onClick() }
        return t
    }

    private fun addTo(row: LinearLayout, v: View) {
        val lp = LinearLayout.LayoutParams(WRAP, WRAP)
        lp.setMargins(dp(3), dp(3), dp(3), dp(3))
        row.addView(v, lp)
    }

    private fun pick(title: String, items: List<String>, onPick: (Int) -> Unit) {
        AlertDialog.Builder(this)
            .setTitle(title)
            .setItems(items.toTypedArray()) { d, i ->
                onPick(i)
                d.dismiss()
            }
            .show()
    }

    private fun buildUi() {
        root = FrameLayout(this)
        root.setBackgroundColor(Color.BLACK)

        holder = FrameLayout(this)
        textureView = TextureView(this)
        holder.addView(textureView, FrameLayout.LayoutParams(MATCH, MATCH))
        overlay = AidsOverlay(this)
        holder.addView(overlay, FrameLayout.LayoutParams(MATCH, MATCH))
        root.addView(holder, FrameLayout.LayoutParams(MATCH, MATCH, Gravity.CENTER))

        flashView = View(this)
        flashView.setBackgroundColor(Color.WHITE)
        flashView.alpha = 0f
        flashView.isClickable = false
        root.addView(flashView, FrameLayout.LayoutParams(MATCH, MATCH))

        // ---- الشريط العلوي
        val topScroll = HorizontalScrollView(this)
        topScroll.isHorizontalScrollBarEnabled = false
        val topRow = LinearLayout(this)
        topRow.orientation = LinearLayout.HORIZONTAL
        topScroll.addView(topRow, FrameLayout.LayoutParams(WRAP, WRAP))

        resChip = chip("1080p") {
            if (!recording) pick("Resolution", videoSizes.map { resName(it) }) { i ->
                videoSize = videoSizes[i]
                refreshVideoChips()
                startSession()
            }
        }
        fpsChip = chip("30 fps") {
            if (!recording) pick("Frame rate", fpsOptions.map { "$it fps" }) { i ->
                fps = fpsOptions[i]
                if (!autoExp) expNs = expNs.coerceIn(expRange.lower, expMaxCap())
                refreshVideoChips()
                refreshPanel()
                startSession()
            }
        }
        codecChip = chip("H.264") {
            if (!recording) pick("Codec", listOf("H.264", "HEVC (H.265)")) { i ->
                if (i == 1 && !hevcSupported) {
                    toast("HEVC غير مدعوم على هذا الجهاز")
                } else {
                    hevc = i == 1
                    refreshVideoChips()
                    startSession()
                }
            }
        }
        mbpsChip = chip("30 Mbps") {
            if (!recording) {
                val opts = listOf(10, 20, 30, 50, 75, 100)
                pick("Bitrate", opts.map { "$it Mbps" }) { i ->
                    bitrateMbps = opts[i]
                    refreshVideoChips()
                    startSession()
                }
            }
        }
        rawChip = chip("RAW OFF") {
            if (!rawSupported) {
                toast("RAW غير مدعوم على هذه العدسة")
            } else {
                rawEnabled = !rawEnabled
                refreshVideoChips()
                startSession()
            }
        }
        histChip = chip("HIST") {
            histOn = !histOn
            styleChip(histChip, histOn)
            refreshAidsOverlay()
        }
        zebraChip = chip("ZEBRA") {
            zebraOn = !zebraOn
            styleChip(zebraChip, zebraOn)
            refreshAidsOverlay()
        }
        peakChip = chip("PEAK") {
            peakOn = !peakOn
            styleChip(peakChip, peakOn)
            refreshAidsOverlay()
        }
        gridChip = chip("GRID") {
            gridOn = !gridOn
            styleChip(gridChip, gridOn)
            refreshAidsOverlay()
        }
        for (c in listOf(resChip, fpsChip, codecChip, mbpsChip, rawChip, histChip, zebraChip, peakChip, gridChip)) {
            addTo(topRow, c)
        }
        val topLp = FrameLayout.LayoutParams(MATCH, WRAP, Gravity.TOP)
        topLp.rightMargin = dp(120)
        root.addView(topScroll, topLp)

        // ---- العمود الأيمن
        val right = LinearLayout(this)
        right.orientation = LinearLayout.VERTICAL
        right.gravity = Gravity.CENTER_HORIZONTAL
        photoChip = chip("PHOTO") { setMode(false) }
        videoChip = chip("VIDEO") { setMode(true) }
        shutter = View(this)
        shutter.setOnClickListener { onShutter() }
        lensChip = chip("Camera") {
            if (!recording && options.isNotEmpty()) {
                pick("Lens", options.map { it.label }) { i ->
                    optIndex = i
                    closeCamera()
                    openCamera()
                }
            }
        }
        lensChip.textSize = 10f
        addTo(right, photoChip)
        addTo(right, videoChip)
        val sLp = LinearLayout.LayoutParams(dp(72), dp(72))
        sLp.setMargins(0, dp(12), 0, dp(12))
        right.addView(shutter, sLp)
        addTo(right, lensChip)
        val rLp = FrameLayout.LayoutParams(dp(104), WRAP, Gravity.END or Gravity.CENTER_VERTICAL)
        rLp.rightMargin = dp(8)
        root.addView(right, rLp)

        // ---- الأسفل: شريط القيمة + أزرار التحكم
        val bottom = LinearLayout(this)
        bottom.orientation = LinearLayout.VERTICAL

        panel = LinearLayout(this)
        panel.orientation = LinearLayout.HORIZONTAL
        panel.gravity = Gravity.CENTER_VERTICAL
        panel.setBackgroundColor(0x99000000.toInt())
        panel.setPadding(dp(10), dp(2), dp(10), dp(2))
        panel.visibility = View.GONE
        panelLabel = TextView(this)
        panelLabel.setTextColor(Color.WHITE)
        panelLabel.textSize = 13f
        panelLabel.typeface = Typeface.DEFAULT_BOLD
        panelLabel.minWidth = dp(110)
        panel.addView(panelLabel, LinearLayout.LayoutParams(WRAP, WRAP))
        seek = SeekBar(this)
        panel.addView(seek, LinearLayout.LayoutParams(0, WRAP, 1f))
        autoBtn = chip("AUTO") {
            when (activeCtl) {
                Ctl.EV -> ev = 0
                Ctl.ISO, Ctl.SS -> autoExp = true
                Ctl.FOCUS -> autoFocus = true
                else -> {}
            }
            refreshPanel()
            updatePreview()
        }
        addTo(panel, autoBtn)
        bottom.addView(panel, LinearLayout.LayoutParams(MATCH, WRAP))

        seek.setOnSeekBarChangeListener(object : SeekBar.OnSeekBarChangeListener {
            override fun onProgressChanged(sb: SeekBar, p: Int, fromUser: Boolean) {
                if (!fromUser || suppressSeek) return
                when (activeCtl) {
                    Ctl.EV -> ev = p + aeCompRange.lower
                    Ctl.ISO -> {
                        goManual()
                        iso = posToIso(p)
                    }
                    Ctl.SS -> {
                        goManual()
                        expNs = posToExp(p)
                    }
                    Ctl.FOCUS -> {
                        autoFocus = false
                        focusDiopter = p / 100f * minFocus
                    }
                    else -> {}
                }
                refreshPanelLabel()
                refreshCtlChips()
                updatePreview()
            }

            override fun onStartTrackingTouch(sb: SeekBar) {}
            override fun onStopTrackingTouch(sb: SeekBar) {}
        })

        val ctlRow = LinearLayout(this)
        ctlRow.orientation = LinearLayout.HORIZONTAL
        ctlRow.gravity = Gravity.CENTER
        evChip = chip("EV") { selectCtl(Ctl.EV) }
        isoChip = chip("ISO") { selectCtl(Ctl.ISO) }
        ssChip = chip("SS") { selectCtl(Ctl.SS) }
        focusChip = chip("FOCUS") { selectCtl(Ctl.FOCUS) }
        wbChip = chip("WB") { showWbDialog() }
        for (c in listOf(evChip, isoChip, ssChip, focusChip, wbChip)) {
            c.minWidth = dp(70)
            addTo(ctlRow, c)
        }
        bottom.addView(ctlRow, LinearLayout.LayoutParams(MATCH, WRAP))
        val bLp = FrameLayout.LayoutParams(MATCH, WRAP, Gravity.BOTTOM)
        bLp.rightMargin = dp(120)
        root.addView(bottom, bLp)

        // ---- مؤقت التسجيل
        timerText = TextView(this)
        timerText.setTextColor(Color.WHITE)
        timerText.textSize = 16f
        timerText.typeface = Typeface.DEFAULT_BOLD
        timerText.setPadding(dp(12), dp(4), dp(12), dp(4))
        val tg = GradientDrawable()
        tg.setColor(0xCCE53935.toInt())
        tg.cornerRadius = dp(10).toFloat()
        timerText.background = tg
        timerText.visibility = View.GONE
        val tLp = FrameLayout.LayoutParams(WRAP, WRAP, Gravity.TOP or Gravity.CENTER_HORIZONTAL)
        tLp.topMargin = dp(48)
        root.addView(timerText, tLp)

        updateModeUi()
        refreshVideoChips()
        refreshCtlChips()
        updateLensChip()
    }

    private fun showWbDialog() {
        val modes = awbModes.toList()
        pick("White balance", modes.map { wbName(it) }) { i ->
            awbMode = modes[i]
            refreshCtlChips()
            updatePreview()
        }
    }
}
