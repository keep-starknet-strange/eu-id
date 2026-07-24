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
}
