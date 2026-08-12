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

    private fun sampleProductStatement() = ProductPublicStatementV2(
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

    private fun sampleStatement() = ZkPublicStatement.ProductV2(sampleProductStatement())

    private fun malformedWitness() = ZkMdocWitness.ProductV2(ProductMdocWitnessV2(
        document = byteArrayOf(),
        revocationIdLo = 0uL,
        revocationIdHi = ULong.MAX_VALUE,
        revocationSignatureR = ByteArray(32) { 1 },
        revocationSignatureS = ByteArray(32) { 1 },
    ))

    @Test
    fun productPinsAreNonemptyAndMatchTheSampleStatement() {
        val statement = sampleProductStatement()
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

    @Test
    fun walletCompatibilitySurfaceSelectsTheP256ProductVariant() {
        val contract = zkContractV1()
        assertEquals("stwo-euid-v1", contract.systemName)
        assertEquals("stwo-euid-pid-v1", contract.specIdPid)
        assertEquals(PredicateMode.AND, predicateModeFromToken("and"))
        assertEquals(300u, isoAlpha2ToNumeric("GR"))
        assertEquals(ZkSystemKind.P256, zkSystem())

        val productV1 = ZkPublicStatement.ProductV1(
            ProductPublicStatementV1(
                specId = contract.specIdPid,
                version = 1u,
                doctype = contract.doctypePid,
                namespace = contract.pidNamespace,
                issuerKey = IssuerKey.P256(
                    x = hex("6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296"),
                    y = hex("4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5"),
                ),
                todayEpochDay = (1_785_715_200L / 86_400L).toInt(),
                nonce = sessionTranscript(),
                predicateMode = PredicateMode.AND,
                ageThresholdYears = 18u,
                acceptedNumericCountries = listOf(56u, 196u, 300u),
                natMode = NatMode.ANY,
            ),
        )
        if (System.getProperty(LEGACY_PRODUCT_V1_DEMO_PROPERTY).toBoolean()) {
            assertFalse(verifyIdentity(productV1, "not a proof".toByteArray()).ok)
        } else {
            assertFailsWith<ZkException.UnsupportedProofSystem> {
                verifyIdentity(productV1, "not a proof".toByteArray())
            }
        }
        val currentWalletP256Demo =
            System.getProperty(CURRENT_WALLET_P256_DEMO_PROPERTY).toBoolean()
        val ts13Compatibility = ZkPublicStatement.Ts13DemoV1(
            IdentityStatement(
                circuitHash = ts13DemoCircuitHash(),
                zkSystemId = contract.specIdPid,
                documentType = contract.doctypePid,
                namespace = contract.pidNamespace,
                elementIdentifier = resultAgeOver(18u),
                expectedValueCbor = byteArrayOf(0xf5.toByte()),
                timestampEpochSeconds = 1_785_715_200L,
                sessionTranscript = sessionTranscript(),
                trustedIssuerPublicKey =
                    sampleProductStatement().issuerPublicKeyX +
                        sampleProductStatement().issuerPublicKeyY,
                revocationPublicKey = demoRevocationPublicKey(),
                revocationEpoch = demoRevocationEpoch(),
            ),
        )
        if (currentWalletP256Demo) {
            assertTrue(ts13DemoCircuitHash().isNotEmpty())
            assertEquals(64, demoRevocationPublicKey().size)
            assertTrue(demoRevocationEpoch() > 0u)
            assertFalse(verifyIdentity(ts13Compatibility, "not a proof".toByteArray()).ok)
        } else {
            assertTrue(ts13DemoCircuitHash().isEmpty())
            assertFailsWith<ZkException.UnsupportedProofSystem> {
                verifyIdentity(ts13Compatibility, byteArrayOf())
            }
        }
    }

    private companion object {
        const val LEGACY_PRODUCT_V1_DEMO_PROPERTY = "legacyProductV1Demo"
        const val CURRENT_WALLET_P256_DEMO_PROPERTY = "currentWalletP256Demo"
    }
}
