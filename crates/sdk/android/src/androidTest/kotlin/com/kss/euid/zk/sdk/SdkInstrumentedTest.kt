package com.kss.euid.zk.sdk

import androidx.test.ext.junit.runners.AndroidJUnit4
import org.junit.Assert.assertEquals
import org.junit.Assert.assertFalse
import org.junit.Assert.assertThrows
import org.junit.Assert.assertTrue
import org.junit.Test
import org.junit.runner.RunWith

/**
 * Exercises the real UniFFI surface on a device/emulator: the calls cross into
 * the bundled `libeuid_zk_sdk.so`, so this also proves the native lib loads for
 * the test device's ABI. Run with `./gradlew connectedAndroidTest` (needs a
 * running emulator/device).
 *
 * Exercises the ML-DSA mdoc product contract exposed by verifyIdentity.
 */
@RunWith(AndroidJUnit4::class)
class SdkInstrumentedTest {

    private fun sampleStatement() = ZkPublicStatement(
        specId = "stwo-euid-pid-v1",
        version = 1u,
        doctype = "eu.europa.ec.eudi.pid.1",
        namespace = "eu.europa.ec.eudi.pid.1",
        issuerPublicKeyHash = ByteArray(32) { 0x11 },
        todayEpochDay = 7305,
        nonce = byteArrayOf(0xab.toByte(), 0xcd.toByte(), 0xef.toByte()),
        predicateMode = PredicateMode.AND,
        ageThresholdYears = 18u,
        acceptedNumericCountries = listOf(56u, 196u, 300u),
        natMode = NatMode.ANY,
    )

    private fun malformedWitness() = ZkMdocWitness(
        document = byteArrayOf(),
        trustedIssuerPublicKeys = emptyList(),
    )

    @Test
    fun proveIdentity_rejectsMalformedMdoc() {
        assertThrows(ZkException.Prove::class.java) {
            proveIdentity(sampleStatement(), malformedWitness())
        }
    }

    @Test
    fun verifyIdentity_rejectsMalformedProof() {
        val result = verifyIdentity(sampleStatement(), "not an mdoc proof".toByteArray())
        assertFalse(result.ok)
    }

}
