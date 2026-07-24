package eu.euid.bench

import org.junit.Assert.assertEquals
import org.junit.Assert.assertThrows
import org.junit.Test

class BenchRunnerTest {
    @Test
    fun gameLoopScenariosUseAbbaThenBaab() {
        assertEquals(
            listOf(
                MldsaVariant.BASELINE,
                MldsaVariant.PACKED,
                MldsaVariant.PACKED,
                MldsaVariant.BASELINE,
                MldsaVariant.PACKED,
                MldsaVariant.BASELINE,
                MldsaVariant.BASELINE,
                MldsaVariant.PACKED,
            ),
            (1..8).map(::mldsaVariantForScenario),
        )
        assertEquals(
            listOf(
                "libeu_id_ffi_mldsa_baseline.so",
                "libeu_id_ffi_mldsa_packed.so",
            ),
            MldsaVariant.values().map(MldsaVariant::fileName),
        )
    }

    @Test
    fun manualRunUsesBaseline() {
        assertEquals(MldsaVariant.BASELINE, mldsaVariantForScenario(0))
    }

    @Test
    fun invalidGameLoopScenarioIsRejected() {
        assertThrows(IllegalArgumentException::class.java) {
            mldsaVariantForScenario(9)
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
