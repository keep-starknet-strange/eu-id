package com.kss.euid.zk.sdk

import org.junit.Assert.assertEquals
import org.junit.Test

class WalletFfiContractTest {

    @Test
    fun walletUsedSurfaceCompiles() {
        val zkContract: () -> ZkContract = ::zkContractV1
        val zkSystemKind: () -> ZkSystemKind = ::zkSystem
        val circuitHash: () -> ByteArray = ::ts13DemoCircuitHash
        val issuerPublicKey: () -> ByteArray = ::demoIssuerPublicKey
        val revocationPublicKey: () -> ByteArray = ::demoRevocationPublicKey
        val revocationEpoch: () -> UInt = ::demoRevocationEpoch
        val revocationWitness: (ByteArray) -> DemoRevocationWitness = ::demoRevocationWitness
        val mintMdoc: (ByteArray, ByteArray) -> ByteArray = ::demoMintMlDsaSignedPidMdoc
        val deviceAuth: (ByteArray, String) -> ByteArray = ::demoDeviceAuthSigStructure
        val buildWitness: (ByteArray, ByteArray, String, ByteArray) -> ByteArray =
            ::demoBuildMlDsaWitness
        val prove: (ZkPublicStatement, ZkMdocWitness) -> ByteArray = ::proveIdentity
        val verify: (ZkPublicStatement, ByteArray) -> ZkVerifyResult = ::verifyIdentity
        val predicateFromToken: (String) -> PredicateMode? = ::predicateModeFromToken
        val predicateUsesAge: (PredicateMode) -> Boolean = ::predicateModeUsesAge
        val predicateUsesNat: (PredicateMode) -> Boolean = ::predicateModeUsesNat
        val ageResult: (UInt) -> String = ::resultAgeOver
        val countryCode: (String) -> UInt? = ::isoAlpha2ToNumeric

        val identityStatement = IdentityStatement(
            circuitHash = byteArrayOf(),
            zkSystemId = "",
            documentType = "",
            namespace = "",
            elementIdentifier = "",
            expectedValueCbor = byteArrayOf(),
            timestampEpochSeconds = 0,
            sessionTranscript = byteArrayOf(),
            trustedIssuerPublicKey = byteArrayOf(),
            revocationPublicKey = byteArrayOf(),
            revocationEpoch = 0u,
        )
        val identityWitness = IdentityWitness(
            document = byteArrayOf(),
            revocationIdLo = 0uL,
            revocationIdHi = 1uL,
            revocationSignature = byteArrayOf(),
        )
        val productStatement = ProductPublicStatementV1(
            specId = "",
            version = 1u,
            doctype = "",
            namespace = "",
            issuerKey = IssuerKey.MlDsa(pkHash = byteArrayOf()),
            todayEpochDay = 0,
            nonce = byteArrayOf(),
            predicateMode = PredicateMode.AGE,
            ageThresholdYears = null,
            acceptedNumericCountries = null,
            natMode = NatMode.ANY,
        )
        val productWitness = ProductMdocWitnessV1(
            document = byteArrayOf(),
            trustedIssuers = TrustedIssuers.PublicKeys(v1 = emptyList()),
        )
        val contract = ZkContract(
            systemName = "",
            specIdPid = "",
            pidNamespace = "",
            doctypePid = "",
            elementBirthDate = "",
            elementNationality = "",
            paramPredicateMode = "",
            paramMinAge = "",
            paramAcceptedCountries = "",
            paramNatMode = "",
            paramVersion = "",
            paramNumAttributes = "",
            paramCircuitHash = "",
            resultNatInSet = "",
        )

        val functions = listOf<Any>(
            zkContract,
            zkSystemKind,
            circuitHash,
            issuerPublicKey,
            revocationPublicKey,
            revocationEpoch,
            revocationWitness,
            mintMdoc,
            deviceAuth,
            buildWitness,
            prove,
            verify,
            predicateFromToken,
            predicateUsesAge,
            predicateUsesNat,
            ageResult,
            countryCode,
        )
        val publicStatements: List<ZkPublicStatement> = listOf(
            ZkPublicStatement.ProductV1(productStatement),
            ZkPublicStatement.Ts13DemoV1(identityStatement),
        )
        val namedCalls = listOf<Any>(
            {
                demoMintMlDsaSignedPidMdoc(
                    p256IssuerSigned = byteArrayOf(),
                    devicePublicKey = byteArrayOf(),
                )
            },
            {
                verifyIdentity(
                    statement = publicStatements.last(),
                    proof = byteArrayOf(),
                )
            },
        )
        val witnesses: List<ZkMdocWitness> = listOf(
            ZkMdocWitness.ProductV1(productWitness),
            ZkMdocWitness.Ts13DemoV1(identityWitness),
        )
        val issuerKeys: List<IssuerKey> = listOf(
            IssuerKey.P256(x = byteArrayOf(), y = byteArrayOf()),
            IssuerKey.MlDsa(pkHash = byteArrayOf()),
        )
        val trustedIssuers: List<TrustedIssuers> = listOf(
            TrustedIssuers.Certificates(v1 = emptyList()),
            TrustedIssuers.PublicKeys(v1 = emptyList()),
        )
        val enums = listOf<Any>(
            PredicateMode.AGE,
            PredicateMode.NAT,
            PredicateMode.AND,
            PredicateMode.OR,
            NatMode.ANY,
            ZkSystemKind.P256,
            ZkSystemKind.ML_DSA,
        )
        val records = listOf<Any>(
            DemoRevocationWitness(idLo = 0uL, idHi = 1uL, signature = byteArrayOf()),
            ZkVerifyResult(ok = true),
            contract,
        )
        val errors: List<ZkException> = listOf(
            ZkException.InvalidInput(""),
            ZkException.Prove(""),
            ZkException.Verify(""),
            ZkException.UnsupportedProofSystem(),
            ZkException.UnsupportedCircuitHash(),
            ZkException.UnsupportedDemoCredentialShape(),
            ZkException.MalformedSessionTranscript(),
            ZkException.InvalidPublicContext(),
            ZkException.InvalidPrivateCredential(),
            ZkException.InvalidRevocationWitness(),
            ZkException.ProofGenerationFailed(),
            ZkException.MalformedProofEnvelope(),
            ZkException.ProofContextMismatch(),
            ZkException.ProofVerificationFailed(),
        )

        assertEquals(17, functions.size)
        assertEquals(2, namedCalls.size)
        assertEquals(2, publicStatements.size)
        assertEquals(2, witnesses.size)
        assertEquals(2, issuerKeys.size)
        assertEquals(2, trustedIssuers.size)
        assertEquals(7, enums.size)
        assertEquals(3, records.size)
        assertEquals(14, errors.size)
    }
}
