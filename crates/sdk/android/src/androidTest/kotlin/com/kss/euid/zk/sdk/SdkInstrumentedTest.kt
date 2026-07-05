package com.kss.euid.zk.sdk

import androidx.test.ext.junit.runners.AndroidJUnit4
import org.junit.Assert.assertFalse
import org.junit.Assert.assertTrue
import org.junit.Test
import org.junit.runner.RunWith

/**
 * Exercises the real UniFFI surface on a device/emulator: the calls cross into
 * the bundled `libeuid_zk_sdk.so`, so this also proves the native lib loads for
 * the test device's ABI. Run with `./gradlew connectedAndroidTest` (needs a
 * running emulator/device).
 *
 * These assert the legacy POC contract exposed by proveIdentity/verifyIdentity.
 * The promoted product path is proveMdocPid/verifyMdocPid.
 */
@RunWith(AndroidJUnit4::class)
class SdkInstrumentedTest {

    private fun sampleStatement() = ZkPublicStatement(
        specId = "stwo-euid-pid-v1",
        version = 1u,
        doctype = "eu.europa.ec.eudi.pid.1",
        namespace = "eu.europa.ec.eudi.pid.1",
        issuerKeyX = ByteArray(32) { 0x11 },
        issuerKeyY = ByteArray(32) { 0x22 },
        todayEpochDay = 7305,
        nonce = byteArrayOf(0xab.toByte(), 0xcd.toByte(), 0xef.toByte()),
        predicateMode = PredicateMode.AND,
        ageThresholdYears = 18u,
        acceptedNumericCountries = listOf(56u, 196u, 300u),
        natMode = NatMode.ANY,
    )

    private fun sampleWitness() = ZkWitness(
        issuerSigR = ByteArray(32) { 1 },
        issuerSigS = ByteArray(32) { 2 },
        sigStructure = ByteArray(16) { 3 },
        mso = ByteArray(16) { 4 },
        birthDateItem = ByteArray(8) { 5 },
        nationalityItem = ByteArray(8) { 6 },
        birthDate = "1990-01-01",
        nationalities = listOf(300u),
        digestIds = emptyMap(),
    )

    @Test
    fun proveThenVerify_roundTrips() {
        val statement = sampleStatement()
        val proof = proveIdentity(statement, sampleWitness())
        assertTrue(verifyIdentity(statement, proof).ok)
    }

    @Test
    fun verify_rejectsMismatchedProof() {
        val result = verifyIdentity(sampleStatement(), "not the statement".toByteArray())
        assertFalse(result.ok)
    }

    @Test
    fun verify_rejectsProofForADifferentStatement() {
        val a = sampleStatement()
        val b = sampleStatement().copy(ageThresholdYears = 21u)
        val proofForA = proveIdentity(a, sampleWitness())
        assertFalse(verifyIdentity(b, proofForA).ok)
    }
}
