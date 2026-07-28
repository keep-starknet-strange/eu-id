package eu.euid.bench

import org.junit.Assert.assertEquals
import org.junit.Assert.assertThrows
import org.junit.Test

class BenchRunnerTest {
    @Test
    fun gameLoopScenariosCounterbalanceOriginalOrder() {
        assertEquals(
            listOf(
                P256Variant.RANGE8_CANDIDATE,
                P256Variant.RANGE16_BASELINE,
                P256Variant.RANGE16_BASELINE,
                P256Variant.RANGE8_CANDIDATE,
                P256Variant.RANGE16_BASELINE,
                P256Variant.RANGE8_CANDIDATE,
                P256Variant.RANGE8_CANDIDATE,
                P256Variant.RANGE16_BASELINE,
            ),
            (1..8).map(::p256VariantForScenario),
        )
        assertEquals(
            listOf(
                "libeuid_zk_sdk_p256_range16.so",
                "libeuid_zk_sdk_p256_range8.so",
            ),
            P256Variant.values().map(P256Variant::fileName),
        )
        assertEquals(
            listOf(
                "p256-range16" to "p256_range16_build_manifest.json",
                "p256-range8" to "p256_range8_build_manifest.json",
            ),
            P256Variant.values().map { it.manifestSlot to it.manifestAssetName },
        )
    }

    @Test
    fun manualRunUsesRange16Baseline() {
        assertEquals(P256Variant.RANGE16_BASELINE, p256VariantForScenario(0))
    }

    @Test
    fun invalidGameLoopScenarioIsRejected() {
        assertThrows(IllegalArgumentException::class.java) {
            p256VariantForScenario(9)
        }
    }

    @Test
    fun gameLoopRejectsSingleCorePolicy() {
        assertThrows(IllegalArgumentException::class.java) {
            requireAllBigForGameLoop(scenario = 1, allPerformanceCores = false)
        }
        requireAllBigForGameLoop(scenario = 8, allPerformanceCores = true)
    }

    @Test
    fun nativeStatementSelectsTruthfulProfile() {
        assertEquals(
            BenchmarkProfile(
                apiEntrypoint = "native_ts13_circuit_core",
                proofScope =
                    "mdoc_issuer_es256_device_es256_age_over_18_equality_sorted_pair_revocation",
                proofEncoding = "raw_bincode",
                revocation = true,
            ),
            benchmarkProfile("ts13_n1_age_over_18_revocation"),
        )
        assertThrows(IllegalStateException::class.java) {
            benchmarkProfile("unknown")
        }
    }
}
