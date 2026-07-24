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
            val scenario = intent.getIntExtra(EXTRA_SCENARIO, FIRST_GAME_LOOP_SCENARIO)
            startBenchmark(
                outputUri = intent.data,
                finishAfterRun = true,
                allPerformanceCores = true,
                scenario = scenario,
            )
        }
    }

    private fun buildContentView(): LinearLayout {
        runButton = Button(this).apply {
            text = "Run full-PQ benchmark"
            setOnClickListener {
                startBenchmark(
                    outputUri = null,
                    finishAfterRun = false,
                    allPerformanceCores = true,
                    scenario = 0,
                )
            }
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

    private fun startBenchmark(
        outputUri: Uri?,
        finishAfterRun: Boolean,
        allPerformanceCores: Boolean,
        scenario: Int,
    ) {
        runButton.isEnabled = false
        output.text = "Proving ML-DSA-65 issuer + device + TS13 revocation…"

        Thread(
            null,
            {
                val json = runCatching {
                    BenchRunner.runSuite(applicationContext, allPerformanceCores, scenario)
                }
                    .getOrElse { error ->
                        Log.e(TAG, "Full-PQ benchmark failed", error)
                        JSONObject()
                            .put("ok", false)
                            .put("error", error.message ?: error.javaClass.simpleName)
                            .toString()
                    }

                if (finishAfterRun) {
                    val gameLoopOutput = requireNotNull(outputUri) {
                        "Game Loop launch did not provide an output URI"
                    }
                    writeResult(gameLoopOutput, json)
                }

                runOnUiThread {
                    output.text = json
                    runButton.isEnabled = true
                    if (finishAfterRun) {
                        finish()
                        Runtime.getRuntime().exit(0)
                    }
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
        const val TAG = "EuIdFullPqBench"
        const val ACTION_TEST_LOOP = "com.google.intent.action.TEST_LOOP"
        const val EXTRA_SCENARIO = "scenario"
        const val FIRST_GAME_LOOP_SCENARIO = 1
        const val WORKER_NAME = "eu-id-full-pq-bench"
        const val WORKER_STACK_BYTES = 64L * 1024 * 1024
    }
}
