package eu.euid.bench

import android.content.Context
import android.os.Build
import org.json.JSONArray
import org.json.JSONObject
import java.io.File
import java.security.MessageDigest

object BenchRunner {
    const val ITERATIONS = 5
    const val PINNING_UNPINNED = "unpinned"
    const val PINNING_A55 = "a55"
    const val PINNING_A77 = "a77"

    private val validPinning = setOf(PINNING_UNPINNED, PINNING_A55, PINNING_A77)

    init {
        System.loadLibrary("eu_id_ffi")
    }

    @JvmStatic
    external fun identity(iters: Int): String

    @JvmStatic
    external fun mdoc(iters: Int): String

    @JvmStatic
    external fun p256(iters: Int): String

    @JvmStatic
    external fun sha256(iters: Int): String

    fun runSuite(context: Context, requestedPinning: String?): String {
        val pinning = requestedPinning?.takeIf(validPinning::contains) ?: PINNING_UNPINNED
        val thermalBefore = thermalTemperatures()
        val cold = JSONObject(identity(1))

        val benches = JSONObject()
            .put("identity", JSONObject(identity(ITERATIONS)))
            .put("mdoc", JSONObject(mdoc(ITERATIONS)))
            .put("p256", JSONObject(p256(ITERATIONS)))
            .put("sha256", JSONObject(sha256(ITERATIONS)))

        val meta = JSONObject()
            .put("model", Build.MODEL)
            .put("soc_features", cpuFeatures())
            .put("cores", Runtime.getRuntime().availableProcessors())
            .put("api", Build.VERSION.SDK_INT)
            .put("branch", BuildConfig.BENCH_BRANCH)
            .put("git", BuildConfig.BENCH_GIT)
            .put("stwo_rev", BuildConfig.STWO_REV)
            .put("apk_sha256", apkSha256(context))
            .put("thermal_before_c", thermalBefore)
            .put("thermal_after_c", thermalTemperatures())
            .put("pinning", pinning)

        return JSONObject()
            .put("meta", meta)
            .put("identity_cold_ms", cold.getLong("prove_ms"))
            .put("benches", benches)
            .toString()
    }

    private fun cpuFeatures(): String = runCatching {
        File("/proc/cpuinfo").useLines { lines ->
            lines.firstOrNull {
                it.substringBefore(':').trim().equals("Features", ignoreCase = true)
            }?.substringAfter(':')?.trim().orEmpty()
        }
    }.getOrDefault("")

    private fun thermalTemperatures(): JSONArray {
        val values = JSONArray()
        File("/sys/class/thermal").listFiles { file ->
            file.isDirectory && file.name.startsWith("thermal_zone")
        }?.sortedBy(File::getName)?.forEach { zone ->
            runCatching { zone.resolve("temp").readText().trim().toDouble() }
                .getOrNull()
                ?.let { raw -> values.put(if (kotlin.math.abs(raw) >= 1_000) raw / 1_000 else raw) }
        }
        return values
    }

    private fun apkSha256(context: Context): String {
        val digest = MessageDigest.getInstance("SHA-256")
        File(context.applicationInfo.sourceDir).inputStream().buffered().use { input ->
            val buffer = ByteArray(DEFAULT_BUFFER_SIZE)
            while (true) {
                val read = input.read(buffer)
                if (read < 0) break
                digest.update(buffer, 0, read)
            }
        }
        return digest.digest().joinToString("") {
            (it.toInt() and 0xff).toString(16).padStart(2, '0')
        }
    }
}
