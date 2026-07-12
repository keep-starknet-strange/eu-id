// C ABI for the quantum-safe mobile benchmark harness.
// Keep this declaration synchronized with src/lib.rs.

#ifndef EU_ID_FFI_H
#define EU_ID_FFI_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct EuIdBench {
    uint64_t prove_ms;
    uint64_t verify_ms;
    uint64_t peak_bytes;
    uint64_t n_blocks;
    uint8_t digest[32];
    int32_t ok;
} EuIdBench;

// `preimage` must point to at least `len` readable bytes (or `len == 0`).
// `iters` is clamped to at least one. The result is plain data.
EuIdBench eu_id_bench_sha256(const uint8_t *preimage, size_t len, uint32_t iters);

#ifdef __cplusplus
}
#endif

#endif // EU_ID_FFI_H
