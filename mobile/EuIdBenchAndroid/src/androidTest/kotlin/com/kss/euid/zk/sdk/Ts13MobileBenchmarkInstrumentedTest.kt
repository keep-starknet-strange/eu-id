package com.kss.euid.zk.sdk

import android.os.Build
import android.os.SystemClock
import android.system.Os
import android.util.Log
import androidx.test.ext.junit.runners.AndroidJUnit4
import androidx.test.platform.app.InstrumentationRegistry
import java.io.File
import java.util.concurrent.TimeUnit
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
        val circuitHashHex = statementFixture.getString("circuitHash")
        val circuitHash = circuitHashHex.decodeHex()
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
            revocationSignature = witnessFixture.getString("revocationSignature").decodeHex(),
        )

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
        assertEquals(EXPECTED_PHASE_COUNT, phaseTimings.size)

        val runtimeConfiguration = phaseTimings.single {
            it.getString("scope") == "sdk" &&
                it.getString("phase") == "runtime_configuration"
        }
        val actualRayonThreads = runtimeConfiguration.getInt("rayon_threads")
        val proofThreadStackBytes = runtimeConfiguration.getLong("proof_thread_stack_bytes")
        val proofWorkerStackBytes = runtimeConfiguration.getLong("proof_worker_stack_bytes")
        assertEquals(PROOF_WORKER_COUNT, actualRayonThreads)
        assertEquals(PROOF_THREAD_STACK_BYTES, proofThreadStackBytes)
        assertEquals(PROOF_WORKER_STACK_BYTES, proofWorkerStackBytes)
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
        val airCoreTimings = phaseTimings.filter { it.getString("scope") == "air_core" }
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

        logJson(
            JSONObject()
                .put("event", "ts13_mobile_benchmark_v1")
                .put("circuit_hash", circuitHashHex)
                .put("model", Build.MODEL)
                .put("api", Build.VERSION.SDK_INT)
                .put("available_processors", Runtime.getRuntime().availableProcessors())
                .put("actual_rayon_threads", actualRayonThreads)
                .put("proof_thread_stack_bytes", proofThreadStackBytes)
                .put("proof_worker_stack_bytes", proofWorkerStackBytes)
                .put("prove_ms", proveMs)
                .put("verify_ms", verifyMs)
                .put("envelope_bytes", proof.size)
                .put("vm_hwm_kib", vmHwmKib)
                .put("phase_count", phaseTimings.size),
        )
        phaseTimings.forEachIndexed { index, timing ->
            logJson(
                JSONObject()
                    .put("event", "ts13_mobile_benchmark_phase_v1")
                    .put("phase_index", index)
                    .put("phase_count", phaseTimings.size)
                    .put("timing", timing),
            )
        }
        assertTrue(timingFile.delete())
    }

    private fun restoreEnvironment(name: String, previousValue: String?) {
        if (previousValue == null) {
            Os.unsetenv(name)
        } else {
            Os.setenv(name, previousValue, true)
        }
    }

    private fun logJson(record: JSONObject) {
        val message = record.toString()
        require(message.toByteArray(Charsets.UTF_8).size <= MAX_LOG_RECORD_BYTES) {
            "The benchmark JSON record exceeds the safe Android log size"
        }
        Log.i(LOG_TAG, message)
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
        const val FIXTURE_ASSET = "ts13_mobile_benchmark_fixture_v1.json"
        const val FIXTURE_SCHEMA = "euid-ts13-mobile-fixture-v1"
        const val LOG_TAG = "Ts13MobileBenchmark"
        const val MAX_LOG_RECORD_BYTES = 3_000
        const val EXPECTED_PHASE_COUNT = 25
        const val PROOF_WORKER_COUNT = 6
        const val MEBIBYTE_BYTES = 1024L * 1024L
        const val PROOF_THREAD_STACK_BYTES = 2L * MEBIBYTE_BYTES
        const val PROOF_WORKER_STACK_BYTES = 16L * MEBIBYTE_BYTES
        const val PROVE_TIMING_ENV = "EUID_PROVE_TIMING"
        const val PROVE_TIMING_FILE_ENV = "EUID_PROVE_TIMING_FILE"
        const val PROVE_TIMING_FILE = "ts13-prove-timing.jsonl"
        const val PROVE_TIMING_PREFIX = "EUID_PROVE_TIMING "
        const val PRIVACY_CLAIM =
            "public-input unlinkable; transcript zero knowledge pending"
        const val TS13_PROFILE = "ts13-pid-age-over-18-unlinkable-demo-v1"
        const val TS13_PROOF_SYSTEM = "stwo-euid-ts13-demo-v1"
        const val ENVELOPE_HEADER_BYTES = 46
        const val ENVELOPE_VERSION = 4
        val ENVELOPE_MAGIC = "EUIDTS13".toByteArray(Charsets.US_ASCII)
    }
}
