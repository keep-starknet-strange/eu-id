package eu.euid.bench

import android.app.Activity
import android.graphics.Typeface
import android.net.Uri
import android.os.Bundle
import android.util.Log
import android.view.ViewGroup
import android.widget.Button
import android.widget.LinearLayout
import android.widget.ScrollView
import android.widget.TextView
import org.json.JSONObject
import java.io.IOException

class MainActivity : Activity() {
    private lateinit var runButton: Button
    private lateinit var output: TextView

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        setContentView(buildContentView())

        if (intent.action == ACTION_TEST_LOOP) {
            startBenchmark(intent.data, finishAfterRun = true)
        }
    }

    private fun buildContentView(): LinearLayout {
        runButton = Button(this).apply {
            text = "Run benchmark suite"
            setOnClickListener { startBenchmark(outputUri = null, finishAfterRun = false) }
        }
        output = TextView(this).apply {
            text = "Ready"
            typeface = Typeface.MONOSPACE
            setTextIsSelectable(true)
        }
        val scroll = ScrollView(this).apply {
            addView(
                output,
                ViewGroup.LayoutParams(
                    ViewGroup.LayoutParams.MATCH_PARENT,
                    ViewGroup.LayoutParams.WRAP_CONTENT,
                ),
            )
        }
        return LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            val padding = (16 * resources.displayMetrics.density).toInt()
            setPadding(padding, padding, padding, padding)
            addView(runButton)
            addView(
                scroll,
                LinearLayout.LayoutParams(0, 0, 1f).apply {
                    width = ViewGroup.LayoutParams.MATCH_PARENT
                },
            )
        }
    }

    private fun startBenchmark(outputUri: Uri?, finishAfterRun: Boolean) {
        runButton.isEnabled = false
        output.text = "Running identity cold sample…"
        val pinning = intent.getStringExtra(EXTRA_PINNING)

        Thread(
            null,
            {
                val json = runCatching { BenchRunner.runSuite(applicationContext, pinning) }
                    .getOrElse { error ->
                        Log.e(TAG, "Benchmark suite failed", error)
                        JSONObject().put("error", error.message ?: error.javaClass.simpleName).toString()
                    }

                if (outputUri != null) {
                    runCatching { writeResult(outputUri, json) }
                        .onFailure { Log.e(TAG, "Could not write Game Loop result", it) }
                } else if (finishAfterRun) {
                    Log.e(TAG, "Game Loop launch did not provide an output URI")
                }

                runOnUiThread {
                    output.text = json
                    runButton.isEnabled = true
                    if (finishAfterRun) finish()
                }
            },
            WORKER_NAME,
            WORKER_STACK_BYTES,
        ).start()
    }

    private fun writeResult(uri: Uri, json: String) {
        val stream = contentResolver.openOutputStream(uri, "wt")
            ?: throw IOException("ContentResolver returned no output stream")
        stream.bufferedWriter(Charsets.UTF_8).use { it.write(json) }
    }

    private companion object {
        const val TAG = "EuIdBench"
        const val ACTION_TEST_LOOP = "com.google.intent.action.TEST_LOOP"
        const val EXTRA_PINNING = "pinning"
        const val WORKER_NAME = "eu-id-bench"
        const val WORKER_STACK_BYTES = 32L * 1024 * 1024
    }
}
