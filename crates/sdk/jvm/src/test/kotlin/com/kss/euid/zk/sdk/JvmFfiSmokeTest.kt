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
    }

    private companion object {
        const val DEMO_REVOCATION_EPOCH: UInt = 17u
        const val ML_DSA_65_PUBLIC_KEY_BYTES = 1_952
        const val WALLET_SYSTEM_NAME = "stwo-euid-v1"
    }
}
