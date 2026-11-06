package com.procam.app

import android.content.Context
import android.graphics.Bitmap
import android.graphics.Canvas
import android.graphics.Paint
import android.graphics.RectF
import android.view.View
import kotlin.math.sqrt

/**
 * طبقة فوق المعاينة: Zebra + Focus Peaking + Histogram + شبكة التأطير.
 */
class AidsOverlay(context: Context) : View(context) {

    var zebra: Bitmap? = null
    var peak: Bitmap? = null
    var hist: IntArray? = null
    var showHist = false
    var showGrid = false

    private val dst = RectF()
    private val bmpPaint = Paint().apply { isFilterBitmap = false }
    private val gridPaint = Paint().apply {
        color = 0x99FFFFFF.toInt()
        strokeWidth = 2f
    }
    private val histBg = Paint().apply { color = 0x99000000.toInt() }
    private val histPaint = Paint().apply { color = 0xFFFFFFFF.toInt() }
    private val histHot = Paint().apply { color = 0xFFFF5252.toInt() }

    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)
        val w = width.toFloat()
        val h = height.toFloat()
        dst.set(0f, 0f, w, h)

        zebra?.let { canvas.drawBitmap(it, null, dst, bmpPaint) }
        peak?.let { canvas.drawBitmap(it, null, dst, bmpPaint) }

        if (showGrid) {
            canvas.drawLine(w / 3f, 0f, w / 3f, h, gridPaint)
            canvas.drawLine(2f * w / 3f, 0f, 2f * w / 3f, h, gridPaint)
            canvas.drawLine(0f, h / 3f, w, h / 3f, gridPaint)
            canvas.drawLine(0f, 2f * h / 3f, w, 2f * h / 3f, gridPaint)
        }

        val hs = hist
        if (showHist && hs != null && hs.isNotEmpty()) {
            val d = resources.displayMetrics.density
            val bw = 160f * d
            val bh = 64f * d
            val left = 10f * d
            val top = 10f * d
            canvas.drawRect(left, top, left + bw, top + bh, histBg)
            var mx = 1
            for (v in hs) if (v > mx) mx = v
            val step = bw / hs.size
            for (i in hs.indices) {
                val frac = sqrt(hs[i].toFloat() / mx.toFloat())
                val p = if (i >= hs.size - 2) histHot else histPaint
                canvas.drawRect(
                    left + i * step,
                    top + bh - frac * bh,
                    left + (i + 1) * step - 1f,
                    top + bh,
                    p
                )
            }
        }
    }
}
