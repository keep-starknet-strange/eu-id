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

internal const val PRODUCT_LIBRARY_NAME = "euid_zk_sdk"
internal const val PRODUCT_LIBRARY_FILE = "libeuid_zk_sdk.so"
internal const val PRODUCT_LIBRARY_SLOT = "sdk-product"
internal const val PRODUCT_MANIFEST_ASSET = "sdk_product_build_manifest.json"
internal const val PRODUCT_STATEMENT = "sdk_identity_product"
internal const val REQUIRED_CARGO_NDK_VERSION = "4.1.2"
private const val MANUAL_SCENARIO = 0
private const val LAST_GAME_LOOP_SCENARIO = 8

internal fun requireAllBigForGameLoop(scenario: Int, allPerformanceCores: Boolean) {
    require(scenario in MANUAL_SCENARIO..LAST_GAME_LOOP_SCENARIO) {
        "P-256 benchmark scenario must be in 0..$LAST_GAME_LOOP_SCENARIO, got $scenario"
    }
    require(scenario == MANUAL_SCENARIO || allPerformanceCores) {
        "P-256 Game Loop scenarios must use all detected performance cores"
    }
}

internal data class BenchmarkProfile(
    val apiEntrypoint: String,
    val proofScope: String,
    val proofEncoding: String,
    val revocation: Boolean,
)

internal fun benchmarkProfile(statement: String): BenchmarkProfile =
    when (statement) {
        PRODUCT_STATEMENT -> BenchmarkProfile(
            apiEntrypoint = "proveIdentity/verifyIdentity",
            proofScope =
                "mdoc_issuer_es256_device_es256_age_nationality_validity_request_context_revocation",
            proofEncoding = "v8_bincode_zstd_envelope",
            revocation = true,
        )
        else -> error("Unknown native benchmark statement: $statement")
    }

object BenchRunner {
    @JvmStatic
    external fun identity(allPerformanceCores: Boolean): String

    fun runSuite(context: Context, allPerformanceCores: Boolean, scenario: Int): String {
        requireAllBigForGameLoop(scenario, allPerformanceCores)
        System.loadLibrary(PRODUCT_LIBRARY_NAME)
        val thermalBefore = thermalTemperatures()
        val thermalStatusBefore = thermalStatus(context)
        val benchmark = JSONObject(identity(allPerformanceCores))
        val statement = benchmark.getString("statement")
        val benchmarkProfile = benchmarkProfile(statement)
        val nativeBuild = JSONObject(
            context.assets.open(PRODUCT_MANIFEST_ASSET).bufferedReader().use { it.readText() },
        )
        require(nativeBuild.getString("library_slot") == PRODUCT_LIBRARY_SLOT) {
            "Native build manifest slot does not match $PRODUCT_LIBRARY_NAME"
        }
        require(nativeBuild.getString("statement") == statement) {
            "Native build manifest statement does not match loaded library result"
        }
        require(nativeBuild.getBoolean("revocation")) {
            "Native build manifest must require revocation"
        }
        require(nativeBuild.getString("cargo_ndk") == REQUIRED_CARGO_NDK_VERSION) {
            "Native build manifest reports the wrong cargo-ndk version"
        }
        require(benchmark.getString("library_slot") == PRODUCT_LIBRARY_SLOT) {
            "Loaded native library reports the wrong build slot"
        }
        require(benchmark.getString("build_id") == nativeBuild.getString("build_id")) {
            "Loaded native library does not match its packaged build manifest"
        }
        require(benchmark.getString("cargo_profile") == nativeBuild.getString("cargo_profile")) {
            "Loaded native library reports the wrong Cargo profile"
        }
        require(benchmark.getString("lto") == nativeBuild.getString("lto")) {
            "Loaded native library reports the wrong LTO mode"
        }
        val thermalAfter = thermalTemperatures()
        val thermalStatusAfter = thermalStatus(context)

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
            .put("native_build", nativeBuild)
            .put("apk_sha256", apkSha256(context))
            .put("variant", statement)
            .put("library_slot", PRODUCT_LIBRARY_SLOT)
            .put("selected_so", PRODUCT_LIBRARY_FILE)
            .put("selected_so_sha256", selectedSoSha256(context, PRODUCT_LIBRARY_FILE))
            .put("thermal_before_c", thermalBefore)
            .put("thermal_after_c", thermalAfter)
            .put("thermal_status_before", thermalStatusBefore)
            .put("thermal_status_after", thermalStatusAfter)

        val profile = JSONObject()
            .put("api_entrypoint", benchmarkProfile.apiEntrypoint)
            .put("proof_scope", benchmarkProfile.proofScope)
            .put("proof_encoding", benchmarkProfile.proofEncoding)
            .put("revocation", benchmarkProfile.revocation)
            .put("fresh_process_proofs", 1)
            .put(
                "thread_policy",
                if (allPerformanceCores) {
                    "all_detected_performance_cores"
                } else {
                    "single_highest_capacity_performance_core"
                },
            )

        return JSONObject()
            .put("meta", meta)
            .put("profile", profile)
            .put("benchmark", benchmark)
            .put("ok", benchmark.optBoolean("ok", false))
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
