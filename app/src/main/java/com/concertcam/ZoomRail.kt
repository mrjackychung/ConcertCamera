package com.concertcam

import android.content.Context
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.Typeface
import android.view.HapticFeedbackConstants
import android.view.MotionEvent
import android.view.View
import kotlin.math.abs
import kotlin.math.floor
import kotlin.math.ln
import kotlin.math.min
import kotlin.math.pow
import kotlin.math.roundToInt

/** 右边缘竖向变焦条：手指在上面滑动=连续变焦，经过刻度会吸附并"咔"一下(切换并锁定对应镜头) */
class ZoomRail(ctx: Context) : View(ctx) {
    var marks: List<Float> = listOf(1f)
        set(v) { field = v; invalidate() }
    var zoom = 1f
    var onPreset: ((Float) -> Unit)? = null
    var onFree: ((Float) -> Unit)? = null
    private var snapped = -1
    private val d = resources.displayMetrics.density

    private val pill = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.argb(120, 0, 0, 0) }
    private val line = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.argb(200, 255, 255, 255); strokeWidth = 2 * d }
    private val dot = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.WHITE }
    private val thumb = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.YELLOW }
    private val txt = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        textSize = 14 * d; color = Color.WHITE; textAlign = Paint.Align.RIGHT
        setShadowLayer(4f, 0f, 0f, Color.BLACK)
    }

    private fun top() = 22 * d
    private fun bottom() = height - 22 * d
    private fun posToY(p: Float): Float {
        val n = marks.size
        return if (n <= 1) (top() + bottom()) / 2 else bottom() - p * (bottom() - top()) / (n - 1)
    }
    private fun yToPos(y: Float): Float {
        val n = marks.size
        return if (n <= 1) 0f else ((bottom() - y) / (bottom() - top()) * (n - 1)).coerceIn(0f, (n - 1).toFloat())
    }
    private fun zoomToPos(z: Float): Float {
        val n = marks.size
        if (n <= 1 || z <= marks[0]) return 0f
        if (z >= marks[n - 1]) return (n - 1).toFloat()
        var i = 0
        while (i < n - 2 && z > marks[i + 1]) i++
        return i + ln(z / marks[i]) / ln(marks[i + 1] / marks[i])
    }
    private fun posToZoom(p: Float): Float {
        val n = marks.size
        val i = min(floor(p).toInt(), n - 2).coerceAtLeast(0)
        return marks[i] * (marks[i + 1] / marks[i]).pow(p - i)
    }
    private fun label(m: Float) = if (m == m.toInt().toFloat()) "${m.toInt()}x" else "%.1fx".format(m)

    override fun onDraw(c: Canvas) {
        if (marks.size < 2) return
        val w = width.toFloat()
        val cx = w - 22 * d
        c.drawRoundRect(w - 44 * d, 0f, w, height.toFloat(), 22 * d, 22 * d, pill)
        c.drawLine(cx, top(), cx, bottom(), line)
        for ((i, m) in marks.withIndex()) {
            val y = posToY(i.toFloat())
            val active = abs(zoom - m) / m < 0.04f
            txt.color = if (active) Color.YELLOW else Color.WHITE
            txt.typeface = if (active) Typeface.DEFAULT_BOLD else Typeface.DEFAULT
            c.drawCircle(cx, y, 4 * d, dot)
            c.drawText(label(m), cx - 16 * d, y + 5 * d, txt)
        }
        c.drawCircle(cx, posToY(zoomToPos(zoom)), 11 * d, thumb)
    }

    override fun onTouchEvent(e: MotionEvent): Boolean {
        if (marks.size < 2) return false
        when (e.actionMasked) {
            MotionEvent.ACTION_DOWN -> { parent?.requestDisallowInterceptTouchEvent(true); snapped = -1; handle(e.y) }
            MotionEvent.ACTION_MOVE -> handle(e.y)
            MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> snapped = -1
        }
        return true
    }

    private fun handle(y: Float) {
        val pos = yToPos(y)
        val j = pos.roundToInt()
        if (abs(pos - j) < 0.2f) {          // 靠近刻度：吸附 + 切换并锁定该档镜头
            if (j != snapped) {
                snapped = j
                performHapticFeedback(HapticFeedbackConstants.CLOCK_TICK)
                onPreset?.invoke(marks[j])
            }
        } else {                           // 刻度之间：连续变焦
            snapped = -1
            onFree?.invoke(posToZoom(pos))
        }
    }
}
