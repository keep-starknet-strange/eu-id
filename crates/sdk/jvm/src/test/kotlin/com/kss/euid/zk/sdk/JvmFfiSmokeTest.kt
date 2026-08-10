package com.kss.euid.zk.sdk

import org.junit.Assert.assertEquals
import org.junit.Test

class JvmFfiSmokeTest {

    @Test
    fun packagedNativeLibraryLoadsAndMatchesWalletContract() {
        assertEquals(DEMO_REVOCATION_EPOCH, demoRevocationEpoch())
        assertEquals(ML_DSA_65_PUBLIC_KEY_BYTES, demoRevocationPublicKey().size)
        assertEquals(ZkSystemKind.ML_DSA, zkSystem())
        assertEquals(WALLET_SYSTEM_NAME, zkContractV1().systemName)
        assertEquals(CYPRUS_NUMERIC_CODE, isoAlpha2ToNumeric("cy"))
        assertEquals(UNITED_STATES_NUMERIC_CODE, isoAlpha2ToNumeric("US"))
    }

    private companion object {
        const val DEMO_REVOCATION_EPOCH: UInt = 17u
        const val ML_DSA_65_PUBLIC_KEY_BYTES = 1_952
        const val WALLET_SYSTEM_NAME = "stwo-euid-v1"
        const val CYPRUS_NUMERIC_CODE: UInt = 196u
        const val UNITED_STATES_NUMERIC_CODE: UInt = 840u
    }
}
