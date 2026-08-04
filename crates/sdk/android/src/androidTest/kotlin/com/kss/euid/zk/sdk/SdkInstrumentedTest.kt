package com.kss.euid.zk.sdk

import androidx.test.ext.junit.runners.AndroidJUnit4
import org.junit.Assert.assertFalse
import org.junit.Assert.assertThrows
import org.junit.Test
import org.junit.runner.RunWith
import java.security.MessageDigest

/**
 * Tests the UniFFI interface on an emulator or device.
 * Each call enters the bundled `libeuid_zk_sdk.so`.
 * This also confirms that the native library supports the device ABI.
 *
 * These tests check the production mdoc contract.
 * The Rust SDK tests contain the complete valid round trip.
 * The Android tests contain small boundary checks that need no test-only interface or credential asset.
 *
 * Run `./gradlew connectedAndroidTest` while an emulator or device is active.
 */
@RunWith(AndroidJUnit4::class)
class SdkInstrumentedTest {

    private fun hex(value: String): ByteArray =
        value.chunked(2).map { it.toInt(16).toByte() }.toByteArray()

    private fun sessionTranscript(): ByteArray {
        val handoverType = "OpenID4VPHandover".toByteArray()
        val handoverHash = MessageDigest.getInstance("SHA-256").digest("android-sdk-test".toByteArray())
        return byteArrayOf(0x83.toByte(), 0xf6.toByte(), 0xf6.toByte(), 0x82.toByte(), 0x71) +
            handoverType + byteArrayOf(0x58, 0x20) + handoverHash
    }

    private fun sampleStatement() = ZkPublicStatement(
        specId = "stwo-euid-pid-v1",
        version = 2u,
        profileId = productProfileId(),
        circuitHash = productCircuitHash(),
        rootPolicyHash = productRootPolicyHash(),
        doctype = "eu.europa.ec.eudi.pid.1",
        namespace = "eu.europa.ec.eudi.pid.1",
        issuerPublicKeyX = hex("6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296"),
        issuerPublicKeyY = hex("4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5"),
        nowEpochSeconds = 1_785_715_200uL,
        sessionTranscript = sessionTranscript(),
        predicateMode = PredicateMode.AND,
        ageThresholdYears = 18u,
        acceptedAlpha2Countries = listOf("BE", "CY", "GR"),
        revocationPublicKeyX = hex("6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296"),
        revocationPublicKeyY = hex("4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5"),
        revocationEpoch = 1u,
    )

    private fun malformedWitness() = ZkMdocWitness(
        document = byteArrayOf(),
        revocationIdLo = 0uL,
        revocationIdHi = ULong.MAX_VALUE,
        revocationSignatureR = ByteArray(32) { 1 },
        revocationSignatureS = ByteArray(32) { 1 },
    )

    @Test
    fun proveIdentity_rejectsMalformedMdoc() {
        assertThrows(ZkException.InvalidInput::class.java) {
            proveIdentity(sampleStatement(), malformedWitness())
        }
    }

    @Test
    fun verifyIdentity_rejectsMalformedProof() {
        val result = verifyIdentity(sampleStatement(), "not the statement".toByteArray())
        assertFalse(result.ok)
    }
}
