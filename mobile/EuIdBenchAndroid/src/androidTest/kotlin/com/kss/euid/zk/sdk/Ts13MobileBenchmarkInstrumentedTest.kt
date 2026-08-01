package com.kss.euid.zk.sdk

// Firebase Test Lab runs one host APK and one test APK.
import android.os.Build
import android.os.SystemClock
import android.system.Os
import android.util.Log
import androidx.test.ext.junit.runners.AndroidJUnit4
import androidx.test.platform.app.InstrumentationRegistry
import com.sun.jna.Library
import com.sun.jna.Memory
import com.sun.jna.Native
import java.io.File
import java.util.concurrent.TimeUnit
import org.json.JSONArray
import org.json.JSONObject
import org.junit.Assert.assertArrayEquals
import org.junit.Assert.assertEquals
import org.junit.Assert.assertTrue
import org.junit.Test
import org.junit.runner.RunWith

@RunWith(AndroidJUnit4::class)
class Ts13MobileBenchmarkInstrumentedTest {

    @Test
    fun proveIdentity_emitsBenchmarkResult() {
        val fixture = JSONObject(
            InstrumentationRegistry.getInstrumentation().context.assets
                .open(FIXTURE_ASSET)
                .bufferedReader()
                .use { it.readText() },
        )
        assertEquals(FIXTURE_SCHEMA, fixture.getString("schema"))
        assertEquals(TS13_PROFILE, fixture.getString("profile"))
        assertEquals(TS13_PROOF_SYSTEM, fixture.getString("proofSystem"))
        assertEquals(PRIVACY_CLAIM, fixture.getString("privacyClaim"))
        assertEquals("proveIdentity", fixture.getString("proveApi"))
        assertEquals("verifyIdentity", fixture.getString("verifyApi"))
        assertEquals("IdentityStatement", fixture.getString("statementType"))
        assertEquals("IdentityWitness", fixture.getString("witnessType"))
        val statementFixture = fixture.getJSONObject("statement")
        val witnessFixture = fixture.getJSONObject("witness")
        val circuitHash = statementFixture.getString("circuitHash").decodeHex()

        val revocationEpoch = statementFixture.getLong("revocationEpoch")
        require(revocationEpoch in 0L..UInt.MAX_VALUE.toLong())
        val statement = IdentityStatement(
            circuitHash = circuitHash,
            zkSystemId = statementFixture.getString("zkSystemId"),
            documentType = statementFixture.getString("documentType"),
            namespace = statementFixture.getString("namespace"),
            elementIdentifier = statementFixture.getString("elementIdentifier"),
            expectedValueCbor = statementFixture.getString("expectedValueCbor").decodeHex(),
            timestampEpochSeconds = statementFixture.getLong("timestampEpochSeconds"),
            sessionTranscript = statementFixture.getString("sessionTranscript").decodeHex(),
            trustedIssuerPublicKey =
                statementFixture.getString("trustedIssuerPublicKey").decodeHex(),
            revocationPublicKey =
                statementFixture.getString("revocationPublicKey").decodeHex(),
            revocationEpoch = revocationEpoch.toUInt(),
        )
        val witness = IdentityWitness(
            document = witnessFixture.getString("document").decodeHex(),
            revocationIdLo = witnessFixture.getString("revocationIdLo").toULong(),
            revocationIdHi = witnessFixture.getString("revocationIdHi").toULong(),
            revocationSignature =
                witnessFixture.getString("revocationSignature").decodeHex(),
        )

        val arguments = InstrumentationRegistry.getArguments()
        val requestedRayonThreads = arguments.getString(RAYON_THREADS_ARGUMENT)?.let {
            parseRayonThreads(it)
        }
        val requestedAffinity = arguments.getString(AFFINITY_CPU_IDS_ARGUMENT)?.let {
            parseCpuList(it)
        }
        val topology = readCpuTopology()
        require(
            requestedAffinity == null || topology.allowed.cpuIds.containsAll(requestedAffinity),
        ) { "Requested affinity contains a CPU that is not allowed" }

        val previousRayonThreads = Os.getenv(RAYON_THREADS_ENV)
        var affinityApplied = false
        try {
            requestedRayonThreads?.let {
                Os.setenv(RAYON_THREADS_ENV, it.toString(), true)
            }
            requestedAffinity?.let {
                setCurrentThreadAffinity(it)
                affinityApplied = true
            }
            val effectiveAffinity = readCurrentThreadAllowedCpus()
            requestedAffinity?.let { assertEquals(it, effectiveAffinity.cpuIds) }

            val timingFile = File(
                InstrumentationRegistry.getInstrumentation().targetContext.cacheDir,
                PROVE_TIMING_FILE,
            )
            assertTrue(!timingFile.exists() || timingFile.delete())
            val previousProveTiming = Os.getenv(PROVE_TIMING_ENV)
            val previousProveTimingFile = Os.getenv(PROVE_TIMING_FILE_ENV)
            val proveStarted = SystemClock.elapsedRealtimeNanos()
            val proof = try {
                Os.setenv(PROVE_TIMING_ENV, "1", true)
                Os.setenv(PROVE_TIMING_FILE_ENV, timingFile.absolutePath, true)
                proveIdentity(statement, witness)
            } finally {
                runCleanup(
                    { restoreEnvironment(PROVE_TIMING_FILE_ENV, previousProveTimingFile) },
                    { restoreEnvironment(PROVE_TIMING_ENV, previousProveTiming) },
                )
            }
            val proveMs = elapsedMilliseconds(proveStarted)
            val phaseTimings = timingFile.useLines { lines ->
                lines
                    .filter { it.isNotBlank() }
                    .map { line ->
                        require(line.startsWith(PROVE_TIMING_PREFIX))
                        JSONObject(line.removePrefix(PROVE_TIMING_PREFIX))
                    }.toList()
            }
            val runtimeConfiguration = phaseTimings.single {
                it.getString("scope") == "sdk" &&
                    it.getString("phase") == "runtime_configuration"
            }
            val actualRayonThreads = runtimeConfiguration.getInt("rayon_threads")
            val proofThreadStackBytes =
                runtimeConfiguration.getLong("proof_thread_stack_bytes")
            val proofWorkerStackBytes =
                runtimeConfiguration.getLong("proof_worker_stack_bytes")
            assertTrue(actualRayonThreads > 0)
            assertTrue(proofThreadStackBytes > 0)
            assertTrue(proofWorkerStackBytes > 0)
            requestedRayonThreads?.let { assertEquals(it, actualRayonThreads) }
            assertTrue(
                phaseTimings.any {
                    it.getString("scope") == "sdk" && it.getString("phase") == "total"
                },
            )
            assertTrue(
                phaseTimings.any {
                    it.getString("scope") == "eu_id_prover" &&
                        it.getString("phase") == "witness_generation"
                },
            )
            val airCoreTimings = phaseTimings.filter {
                it.getString("scope") == "air_core"
            }
            assertTrue(airCoreTimings.any { it.getString("phase") == "total" })
            assertTrue(
                airCoreTimings.all {
                    !it.isNull("vm_rss_kib") && !it.isNull("vm_hwm_kib")
                },
            )

            assertTrue(proof.size >= ENVELOPE_HEADER_BYTES)
            assertArrayEquals(ENVELOPE_MAGIC, proof.copyOfRange(0, ENVELOPE_MAGIC.size))
            assertEquals(ENVELOPE_VERSION, readU16Le(proof, 8))
            assertArrayEquals(circuitHash, proof.copyOfRange(10, 42))
            val bodyCapacity = readU32Le(proof, 42)
            assertEquals(ENVELOPE_HEADER_BYTES.toLong() + bodyCapacity, proof.size.toLong())

            val verifyStarted = SystemClock.elapsedRealtimeNanos()
            verifyIdentity(statement, proof)
            val verifyMs = elapsedMilliseconds(verifyStarted)
            val vmHwmKib = vmHwmKib()
            assertTrue(vmHwmKib > 0)

            val result = JSONObject()
                .put("event", "ts13_mobile_benchmark_v1")
                .put("model", Build.MODEL)
                .put("api", Build.VERSION.SDK_INT)
                .put("available_processors", Runtime.getRuntime().availableProcessors())
                .put("requested_rayon_threads", requestedRayonThreads ?: JSONObject.NULL)
                .put("actual_rayon_threads", actualRayonThreads)
                .put("proof_thread_stack_bytes", proofThreadStackBytes)
                .put("proof_worker_stack_bytes", proofWorkerStackBytes)
                .put(
                    "requested_affinity_cpu_ids",
                    requestedAffinity?.let { JSONArray(it) } ?: JSONObject.NULL,
                )
                .put("cpu_topology", topology.toJson(effectiveAffinity))
                .put("prove_ms", proveMs)
                .put("verify_ms", verifyMs)
                .put("envelope_bytes", proof.size)
                .put("vm_hwm_kib", vmHwmKib)
                .put("phase_timings", JSONArray(phaseTimings))
            Log.i(LOG_TAG, result.toString())
            assertTrue(timingFile.delete())
        } finally {
            runCleanup(
                {
                    if (requestedRayonThreads != null) {
                        restoreEnvironment(RAYON_THREADS_ENV, previousRayonThreads)
                    }
                },
                {
                    if (affinityApplied) {
                        setCurrentThreadAffinity(topology.allowed.cpuIds)
                    }
                },
            )
        }
    }

    private fun restoreEnvironment(name: String, previousValue: String?) {
        if (previousValue == null) {
            Os.unsetenv(name)
        } else {
            Os.setenv(name, previousValue, true)
        }
    }

    private fun runCleanup(vararg actions: () -> Unit) {
        var firstFailure: Throwable? = null
        for (action in actions) {
            try {
                action()
            } catch (failure: Throwable) {
                if (firstFailure == null) {
                    firstFailure = failure
                } else {
                    firstFailure.addSuppressed(failure)
                }
            }
        }
        firstFailure?.let { throw it }
    }

    private data class AllowedCpus(
        val statusPath: String,
        val specification: String,
        val cpuIds: List<Int>,
    )

    private data class CpuInfo(
        val id: Int,
        val capacity: Long?,
        val maximumFrequencyKhz: Long?,
    )

    private data class CpuTopology(
        val onlineSource: String,
        val onlineSpecification: String,
        val onlineCpuIds: List<Int>,
        val allowed: AllowedCpus,
        val cpus: List<CpuInfo>,
    ) {
        fun toJson(effectiveAffinity: AllowedCpus): JSONObject = JSONObject()
            .put("online_source", onlineSource)
            .put("online_specification", onlineSpecification)
            .put("online_cpu_ids", JSONArray(onlineCpuIds))
            .put("allowed_status_path", allowed.statusPath)
            .put("allowed_before_specification", allowed.specification)
            .put("allowed_before_cpu_ids", JSONArray(allowed.cpuIds))
            .put("allowed_during_specification", effectiveAffinity.specification)
            .put("allowed_during_cpu_ids", JSONArray(effectiveAffinity.cpuIds))
            .put(
                "cpus",
                JSONArray().apply {
                    cpus.forEach { cpu ->
                        put(
                            JSONObject()
                                .put("id", cpu.id)
                                .put("capacity", cpu.capacity ?: JSONObject.NULL)
                                .put(
                                    "maximum_frequency_khz",
                                    cpu.maximumFrequencyKhz ?: JSONObject.NULL,
                                ),
                        )
                    }
                },
            )
    }

    private fun readCpuTopology(): CpuTopology {
        val allowed = readCurrentThreadAllowedCpus()
        val onlineFile = File(CPU_ONLINE_PATH)
        val sysfsOnlineSpecification = runCatching { onlineFile.readText().trim() }
            .getOrNull()
            ?.takeIf { it.isNotEmpty() }
        val onlineSpecification = sysfsOnlineSpecification ?: allowed.specification
        val onlineCpuIds = parseCpuList(onlineSpecification)
        return CpuTopology(
            onlineSource =
                if (sysfsOnlineSpecification != null) {
                    CPU_ONLINE_PATH
                } else {
                    allowed.statusPath
                },
            onlineSpecification = onlineSpecification,
            onlineCpuIds = onlineCpuIds,
            allowed = allowed,
            cpus = onlineCpuIds.map { cpu ->
                CpuInfo(
                    id = cpu,
                    capacity = readLong("/sys/devices/system/cpu/cpu$cpu/cpu_capacity"),
                    maximumFrequencyKhz =
                        readLong(
                            "/sys/devices/system/cpu/cpu$cpu/cpufreq/cpuinfo_max_freq",
                        ),
                )
            },
        )
    }

    private fun readCurrentThreadAllowedCpus(): AllowedCpus {
        val paths = listOf(
            "/proc/thread-self/status",
            "/proc/self/task/${Os.gettid()}/status",
            "/proc/self/status",
        )
        for (path in paths) {
            val status = runCatching { File(path).readLines() }.getOrNull() ?: continue
            val specification = status.firstNotNullOfOrNull { line ->
                line
                    .takeIf { it.startsWith("Cpus_allowed_list:") }
                    ?.substringAfter(':')
                    ?.trim()
            } ?: continue
            return AllowedCpus(path, specification, parseCpuList(specification))
        }
        error("Cpus_allowed_list is absent from the current thread status")
    }

    private fun readLong(path: String): Long? =
        runCatching { File(path).readText().trim().toLong() }.getOrNull()

    private fun setCurrentThreadAffinity(cpus: List<Int>) {
        require(cpus.isNotEmpty()) { "Affinity CPU list must not be empty" }
        check(Native.SIZE_T_SIZE == java.lang.Long.BYTES) {
            "The benchmark supports only a 64-bit size_t"
        }
        Memory(CPU_SET_BYTES.toLong()).use { mask ->
            mask.clear()
            for (cpu in cpus) {
                val offset = (cpu / 8).toLong()
                val bit = 1 shl (cpu % 8)
                mask.setByte(offset, ((mask.getByte(offset).toInt() and 0xff) or bit).toByte())
            }
            val result = libc.sched_setaffinity(0, CPU_SET_BYTES.toLong(), mask)
            check(result == 0) {
                "sched_setaffinity failed with errno ${Native.getLastError()}"
            }
        }
    }

    private fun String.decodeHex(): ByteArray {
        require(length % 2 == 0) { "hex value must have an even length" }
        return ByteArray(length / 2) { index ->
            val high = Character.digit(this[index * 2], 16)
            val low = Character.digit(this[index * 2 + 1], 16)
            require(high >= 0 && low >= 0) { "hex value contains a non-hex character" }
            ((high shl 4) or low).toByte()
        }
    }

    private fun elapsedMilliseconds(startedNanos: Long): Long =
        TimeUnit.NANOSECONDS.toMillis(SystemClock.elapsedRealtimeNanos() - startedNanos)

    private fun readU16Le(bytes: ByteArray, offset: Int): Int =
        (bytes[offset].toInt() and 0xff) or
            ((bytes[offset + 1].toInt() and 0xff) shl 8)

    private fun readU32Le(bytes: ByteArray, offset: Int): Long =
        (bytes[offset].toLong() and 0xff) or
            ((bytes[offset + 1].toLong() and 0xff) shl 8) or
            ((bytes[offset + 2].toLong() and 0xff) shl 16) or
            ((bytes[offset + 3].toLong() and 0xff) shl 24)

    private fun vmHwmKib(): Long {
        val line = File("/proc/self/status").useLines { lines ->
            lines.firstOrNull { it.startsWith("VmHWM:") }
        } ?: error("VmHWM is absent from /proc/self/status")
        return line.removePrefix("VmHWM:").trim().substringBefore(' ').toLong()
    }

    private companion object {
        const val AFFINITY_CPU_IDS_ARGUMENT = "affinity_cpu_ids"
        const val CPU_ONLINE_PATH = "/sys/devices/system/cpu/online"
        const val CPU_SET_BYTES = CPU_SET_MAX_CPUS / 8
        const val FIXTURE_ASSET = "ts13_mobile_benchmark_fixture_v1.json"
        const val FIXTURE_SCHEMA = "euid-ts13-mobile-fixture-v1"
        const val LOG_TAG = "Ts13MobileBenchmark"
        const val PROVE_TIMING_ENV = "EUID_PROVE_TIMING"
        const val PROVE_TIMING_FILE_ENV = "EUID_PROVE_TIMING_FILE"
        const val PROVE_TIMING_FILE = "ts13-prove-timing.jsonl"
        const val PROVE_TIMING_PREFIX = "EUID_PROVE_TIMING "
        const val RAYON_THREADS_ARGUMENT = "rayon_threads"
        const val RAYON_THREADS_ENV = "RAYON_NUM_THREADS"
        const val PRIVACY_CLAIM =
            "public-input unlinkable; transcript zero knowledge pending"
        const val TS13_PROFILE = "ts13-pid-age-over-18-unlinkable-demo-v1"
        const val TS13_PROOF_SYSTEM = "stwo-euid-ts13-demo-v1"
        const val ENVELOPE_HEADER_BYTES = 46
        const val ENVELOPE_VERSION = 4
        val ENVELOPE_MAGIC = "EUIDTS13".toByteArray(Charsets.US_ASCII)
        val libc: LibC by lazy { Native.load("c", LibC::class.java) }
    }

    private interface LibC : Library {
        fun sched_setaffinity(pid: Int, cpuSetSize: Long, mask: Memory): Int
    }
}
