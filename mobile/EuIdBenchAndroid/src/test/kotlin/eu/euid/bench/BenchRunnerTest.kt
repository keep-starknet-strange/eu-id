package eu.euid.bench

import org.junit.Assert.assertEquals
import org.junit.Assert.assertThrows
import org.junit.Test

class BenchRunnerTest {
    @Test
    fun productLibraryHasOneCanonicalPackageIdentity() {
        assertEquals("euid_zk_sdk", PRODUCT_LIBRARY_NAME)
        assertEquals("libeuid_zk_sdk.so", PRODUCT_LIBRARY_FILE)
        assertEquals("sdk-product", PRODUCT_LIBRARY_SLOT)
        assertEquals("sdk_product_build_manifest.json", PRODUCT_MANIFEST_ASSET)
        assertEquals("4.1.2", REQUIRED_CARGO_NDK_VERSION)
    }

    @Test
    fun invalidGameLoopScenarioIsRejected() {
        assertThrows(IllegalArgumentException::class.java) {
            requireAllBigForGameLoop(scenario = 9, allPerformanceCores = true)
        }
    }

    @Test
    fun gameLoopRejectsSingleCorePolicy() {
        requireAllBigForGameLoop(scenario = 0, allPerformanceCores = false)
        assertThrows(IllegalArgumentException::class.java) {
            requireAllBigForGameLoop(scenario = 1, allPerformanceCores = false)
        }
        requireAllBigForGameLoop(scenario = 8, allPerformanceCores = true)
    }

    @Test
    fun nativeStatementSelectsTruthfulProfile() {
        assertEquals(
            BenchmarkProfile(
                apiEntrypoint = "proveIdentity/verifyIdentity",
                proofScope =
                    "mdoc_issuer_es256_device_es256_age_nationality_validity_request_context_revocation",
                proofEncoding = "v8_bincode_zstd_envelope",
                revocation = true,
            ),
            benchmarkProfile(PRODUCT_STATEMENT),
        )
        assertThrows(IllegalStateException::class.java) {
            benchmarkProfile("unknown")
        }
    }
}
