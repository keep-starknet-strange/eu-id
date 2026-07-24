package eu.euid.bench

import android.content.Context
import android.os.Build
import android.os.PowerManager
import android.provider.Settings
import org.json.JSONArray
import org.json.JSONObject
import java.io.File
import java.io.InputStream
import java.security.MessageDigest
import java.util.zip.ZipFile

internal enum class MldsaVariant(
    val resultName: String,
    val libraryName: String,
) {
    BASELINE("A_mldsa_baseline", "eu_id_ffi_mldsa_baseline"),
    PACKED("B_mldsa_packed_candidate", "eu_id_ffi_mldsa_packed");

    val fileName: String
        get() = "lib$libraryName.so"
}

private const val MANUAL_SCENARIO = 0
private val GAME_LOOP_VARIANTS = listOf(
    MldsaVariant.BASELINE,
    MldsaVariant.PACKED,
    MldsaVariant.PACKED,
    MldsaVariant.BASELINE,
    MldsaVariant.PACKED,
    MldsaVariant.BASELINE,
    MldsaVariant.BASELINE,
    MldsaVariant.PACKED,
)

internal fun mldsaVariantForScenario(scenario: Int): MldsaVariant =
    if (scenario == MANUAL_SCENARIO) {
        MldsaVariant.BASELINE
    } else {
        requireNotNull(GAME_LOOP_VARIANTS.getOrNull(scenario - 1)) {
            "ML-DSA Game Loop scenario must be in 1..${GAME_LOOP_VARIANTS.size}, got $scenario"
        }
    }

internal fun requireAllBigForGameLoop(scenario: Int, allPerformanceCores: Boolean) {
    require(scenario == MANUAL_SCENARIO || allPerformanceCores) {
        "ML-DSA Game Loop scenarios must use all detected performance cores"
    }
}

object BenchRunner {
    const val PROFILE_NAME = "full_pq_mdoc_mldsa65_ts13_revocation_paired"

    @JvmStatic
    external fun fullPq(allPerformanceCores: Boolean): String

    fun runSuite(context: Context, allPerformanceCores: Boolean, scenario: Int): String {
        requireAllBigForGameLoop(scenario, allPerformanceCores)
        val variant = mldsaVariantForScenario(scenario)
        System.loadLibrary(variant.libraryName)
        val topology = cpuTopology()
        val frequencyBefore = frequencySnapshot(topology.performanceCpuIds)
        val thermalBefore = thermalTemperatures()
        val thermalStatusBefore = thermalStatus(context)
        val benchmark = JSONObject(fullPq(allPerformanceCores))
        check(benchmark.getString("core_metric") == topology.metric) {
            "Kotlin/native CPU topology metric mismatch"
        }
        benchmark
            .put("performance_cpu_ids", intArray(topology.performanceCpuIds))
            .put("efficiency_cpu_ids", intArray(topology.efficiencyCpuIds))
            .put("cpu_metric_values", metricArray(topology.values))
            .put("frequency_before", frequencyBefore)
            .put("frequency_after", frequencySnapshot(topology.performanceCpuIds))
        val meta = JSONObject()
            .put("model", Build.MODEL)
            .put("build_fingerprint", Build.FINGERPRINT)
            .put("kernel", System.getProperty("os.version", ""))
            .put("unit_id_sha256", unitIdSha256(context))
            .put("scenario", scenario)
            .put("soc_features", cpuFeatures())
            .put("cores", Runtime.getRuntime().availableProcessors())
            .put("api", Build.VERSION.SDK_INT)
            .put("branch", BuildConfig.BENCH_BRANCH)
            .put("git", BuildConfig.BENCH_GIT)
            .put("stwo_rev", BuildConfig.STWO_REV)
            .put("apk_sha256", apkSha256(context))
            .put("variant", variant.resultName)
            .put("selected_so", variant.fileName)
            .put("selected_so_sha256", selectedSoSha256(context, variant.fileName))
            .put("thermal_before_c", thermalBefore)
            .put("thermal_after_c", thermalTemperatures())
            .put("thermal_status_before", thermalStatusBefore)
            .put("thermal_status_after", thermalStatus(context))

        val profile = JSONObject()
            .put("name", PROFILE_NAME)
            .put("issuer_auth", "ML-DSA-65")
            .put("device_auth", "ML-DSA-65")
            .put("revocation_auth", "ML-DSA-65")
            .put("age_predicate", true)
            .put("nationality_predicate", true)
            .put("ts13_revocation", true)
            .put(
                "thread_policy",
                if (allPerformanceCores) {
                    "all_detected_performance_cores"
                } else {
                    "single_highest_capacity_performance_core"
                },
            )
            .put("fresh_process_proofs", 1)
            .put("pcs_blowup", 3)
            .put("pcs_queries", 36)
            .put("pcs_pow_bits", 20)
            .put("timing_scope", "prove plus public-statement cold/warm verification")
            .put("peak_scope", "timed prove/verify window; fixture and serialization excluded")
            .put("cold_verify_scope", "fresh canonical tree-0 reconstruction; process already initialized")

        return JSONObject()
            .put("meta", meta)
            .put("profile", profile)
            .put("benchmark", benchmark)
            .put("ok", benchmark.getBoolean("ok"))
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

    private data class CpuTopology(
        val metric: String,
        val values: List<Pair<Int, Long>>,
    ) {
        private val minimum = values.minOf { it.second }
        val performanceCpuIds = values.filter { it.second > minimum }.map { it.first }
        val efficiencyCpuIds = values.filter { it.second == minimum }.map { it.first }
    }

    private fun cpuTopology(): CpuTopology {
        val cpuIds = File("/sys/devices/system/cpu").listFiles { file ->
            file.isDirectory && file.name.matches(Regex("""cpu\d+"""))
        }?.map { it.name.removePrefix("cpu").toInt() }?.sorted().orEmpty()
        for ((metric, suffix) in listOf(
            "cpu_capacity" to "cpu_capacity",
            "cpuinfo_max_freq" to "cpufreq/cpuinfo_max_freq",
        )) {
            val values = cpuIds.mapNotNull { cpuId ->
                File("/sys/devices/system/cpu/cpu$cpuId/$suffix")
                    .takeIf { it.isFile }
                    ?.readText()
                    ?.trim()
                    ?.toLongOrNull()
                    ?.let { cpuId to it }
            }
            if (values.size == cpuIds.size && values.map { it.second }.distinct().size > 1) {
                return CpuTopology(metric, values)
            }
        }
        error("Could not identify heterogeneous Android CPU topology")
    }

    private fun frequencySnapshot(cpuIds: List<Int>): JSONObject = JSONObject()
        .put("scaling_max_khz", cpuFileValues(cpuIds, "cpufreq/scaling_max_freq"))
        .put("scaling_cur_khz", cpuFileValues(cpuIds, "cpufreq/scaling_cur_freq"))

    private fun cpuFileValues(cpuIds: List<Int>, suffix: String): JSONArray =
        metricArray(
            cpuIds.mapNotNull { cpuId ->
                File("/sys/devices/system/cpu/cpu$cpuId/$suffix")
                    .takeIf { it.isFile }
                    ?.readText()
                    ?.trim()
                    ?.toLongOrNull()
                    ?.let { cpuId to it }
            },
        )

    private fun intArray(values: List<Int>): JSONArray =
        JSONArray().also { array -> values.forEach { array.put(it) } }

    private fun metricArray(values: List<Pair<Int, Long>>): JSONArray =
        JSONArray().also { array ->
            values.forEach { (cpuId, value) ->
                array.put(JSONArray().put(cpuId).put(value))
            }
        }

    private fun apkSha256(context: Context): String =
        File(context.applicationInfo.sourceDir).inputStream().buffered().use(::sha256)

    private fun selectedSoSha256(context: Context, fileName: String): String =
        ZipFile(context.applicationInfo.sourceDir).use { apk ->
            val entryName = "lib/arm64-v8a/$fileName"
            val entry = requireNotNull(apk.getEntry(entryName)) {
                "Selected native library is missing from APK: $entryName"
            }
            apk.getInputStream(entry).buffered().use(::sha256)
        }

    private fun sha256(input: InputStream): String {
        val digest = MessageDigest.getInstance("SHA-256")
        val buffer = ByteArray(DEFAULT_BUFFER_SIZE)
        while (true) {
            val read = input.read(buffer)
            if (read < 0) break
            digest.update(buffer, 0, read)
        }
        return digest.digest().joinToString("") {
            (it.toInt() and 0xff).toString(16).padStart(2, '0')
        }
    }

    private fun unitIdSha256(context: Context): String {
        val unitId = Settings.Secure.getString(
            context.contentResolver,
            Settings.Secure.ANDROID_ID,
        ).orEmpty()
        return MessageDigest.getInstance("SHA-256")
            .digest(unitId.toByteArray(Charsets.UTF_8))
            .joinToString("") { (it.toInt() and 0xff).toString(16).padStart(2, '0') }
    }

    private fun thermalStatus(context: Context): Int =
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q) {
            context.getSystemService(PowerManager::class.java).currentThermalStatus
        } else {
            -1
        }
}
