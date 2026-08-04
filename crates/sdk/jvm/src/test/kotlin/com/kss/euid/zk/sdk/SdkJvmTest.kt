package com.kss.euid.zk.sdk

import kotlin.test.Test
import kotlin.test.assertContentEquals
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertFalse
import kotlin.test.assertTrue
import java.security.MessageDigest

class SdkJvmTest {
    private fun hex(value: String): ByteArray =
        value.chunked(2).map { it.toInt(16).toByte() }.toByteArray()

    private fun sessionTranscript(): ByteArray {
        val handoverType = "OpenID4VPHandover".toByteArray()
        val handoverHash = MessageDigest.getInstance("SHA-256").digest("jvm-sdk-test".toByteArray())
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
    fun productPinsAreNonemptyAndMatchTheSampleStatement() {
        val statement = sampleStatement()
        assertTrue(productProfileId().isNotEmpty())
        assertTrue(productCircuitHash().isNotEmpty())
        assertTrue(productRootPolicyHash().isNotEmpty())
        assertEquals(productProfileId(), statement.profileId)
        assertEquals(productCircuitHash(), statement.circuitHash)
        assertContentEquals(productRootPolicyHash(), statement.rootPolicyHash)
    }

    @Test
    fun verifyIdentityRejectsMalformedProofWithoutPanicking() {
        val result = verifyIdentity(sampleStatement(), "not the statement".toByteArray())
        assertFalse(result.ok)
    }

    @Test
    fun proveIdentityMapsMalformedDocumentsToInvalidInput() {
        assertFailsWith<ZkException.InvalidInput> {
            proveIdentity(sampleStatement(), malformedWitness())
        }
    }
}
