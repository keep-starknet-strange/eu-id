package eu.euid.bench

import org.junit.Assert.assertEquals
import org.junit.Assert.assertThrows
import org.junit.Test

class BenchRunnerTest {
    @Test
    fun gameLoopScenariosUseAbbaThenBaab() {
        assertEquals(
            listOf(
                MldsaVariant.REFERENCE,
                MldsaVariant.CANDIDATE,
                MldsaVariant.CANDIDATE,
                MldsaVariant.REFERENCE,
                MldsaVariant.CANDIDATE,
                MldsaVariant.REFERENCE,
                MldsaVariant.REFERENCE,
                MldsaVariant.CANDIDATE,
            ),
            (1..8).map(::mldsaVariantForScenario),
        )
        assertEquals(
            listOf(
                "libeu_id_ffi_mldsa_reference.so",
                "libeu_id_ffi_mldsa_candidate.so",
            ),
            MldsaVariant.values().map(MldsaVariant::fileName),
        )
        assertEquals(
            listOf(
                "mldsa-reference" to "mldsa_reference_build_manifest.json",
                "mldsa-candidate" to "mldsa_candidate_build_manifest.json",
            ),
            MldsaVariant.values().map { it.manifestSlot to it.manifestAssetName },
        )
    }

    @Test
    fun manualRunUsesCandidate() {
        assertEquals(MldsaVariant.CANDIDATE, mldsaVariantForScenario(0))
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

    @Test
    fun nativeVariantCannotChangeWithinOneProcess() {
        val guard = MldsaVariantLoadGuard()
        guard.requireCompatible(MldsaVariant.REFERENCE)
        guard.recordLoaded(MldsaVariant.REFERENCE)
        guard.requireCompatible(MldsaVariant.REFERENCE)
        assertThrows(IllegalArgumentException::class.java) {
            guard.requireCompatible(MldsaVariant.CANDIDATE)
        }
    }
}
