package com.kss.euid.zk.sdk

// Firebase Test Lab runs one host APK and one test APK.
import android.os.Build
import android.os.SystemClock
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

        val proveStarted = SystemClock.elapsedRealtimeNanos()
        val proof = proveIdentity(statement, witness)
        val proveMs = elapsedMilliseconds(proveStarted)

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

        val result = buildString {
            append("{\"event\":\"ts13_mobile_benchmark_v1\"")
            append(",\"model\":").append(JSONObject.quote(Build.MODEL))
            append(",\"api\":").append(Build.VERSION.SDK_INT)
            append(",\"available_processors\":")
                .append(Runtime.getRuntime().availableProcessors())
            append(",\"prove_ms\":").append(proveMs)
            append(",\"verify_ms\":").append(verifyMs)
            append(",\"envelope_bytes\":").append(proof.size)
            append(",\"vm_hwm_kib\":").append(vmHwmKib)
            append('}')
        }
        Log.i(LOG_TAG, result)
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
        const val PRIVACY_CLAIM =
            "public-input unlinkable; transcript zero knowledge pending"
        const val TS13_PROFILE = "ts13-pid-age-over-18-unlinkable-demo-v1"
        const val TS13_PROOF_SYSTEM = "stwo-euid-ts13-demo-v1"
        const val ENVELOPE_HEADER_BYTES = 46
        const val ENVELOPE_VERSION = 4
        val ENVELOPE_MAGIC = "EUIDTS13".toByteArray(Charsets.US_ASCII)
    }
}
