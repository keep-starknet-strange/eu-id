// C ABI for the eu-id SHA-256 mobile benchmark harness.
//
// One function: prove → verify SHA-256 of a preimage `iters` times under a
// peak-memory sampler, all measured inside Rust, returned as a flat struct.
//
// Hand-written to match `#[repr(C)] struct EuIdBench` in src/lib.rs. Keep
// the two in sync.

#ifndef EU_ID_FFI_H
#define EU_ID_FFI_H

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct EuIdBench {
    uint64_t prove_ms;    // median prove wall-clock over `iters`, ms
    uint64_t verify_ms;   // median verify wall-clock over `iters`, ms
    uint64_t peak_bytes;  // peak phys_footprint across the window, bytes
    uint64_t n_blocks;    // padded 512-bit blocks the message hashed to
    uint8_t  digest[32];  // claimed SHA-256 digest
    int32_t  ok;          // 1 = success, 0 = prove/verify failed or panicked
} EuIdBench;

// `preimage` must point to at least `len` readable bytes (or len == 0).
// `iters` is clamped to >= 1. The result is plain data; nothing to free.
EuIdBench eu_id_bench_sha256(const uint8_t *preimage, size_t len, uint32_t iters);

#ifdef __cplusplus
}
#endif

#endif // EU_ID_FFI_H
