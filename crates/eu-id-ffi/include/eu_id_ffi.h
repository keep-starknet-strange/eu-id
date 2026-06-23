// C ABI for the eu-id mobile benchmark harness.
//
// One function per primitive: prove → verify `iters` times under a peak-memory
// sampler, all measured inside Rust, returned as a flat struct.
//   - eu_id_bench_sha256 — SHA-256 of a preimage
//   - eu_id_bench_p256   — one P-256 ECDSA signature verification
//
// Hand-written to match the `#[repr(C)]` structs in src/lib.rs. Keep the two
// in sync.

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

typedef struct EuIdP256Bench {
    uint64_t prove_ms;    // median build+prove wall-clock over `iters`, ms
    uint64_t verify_ms;   // median verify wall-clock over `iters`, ms
    uint64_t peak_bytes;  // peak phys_footprint across the window, bytes
    int32_t  verified;    // 1 = STARK proof verified against its public inputs
    int32_t  ok;          // 1 = success, 0 = build/prove/verify failed or panicked
} EuIdP256Bench;

// Prove → verify one P-256 ECDSA signature. Each of `z` (message hash),
// `r`, `s`, `qx`, `qy` must point to 32 readable big-endian bytes (CryptoKit's
// raw r||s and x||y encoding). `iters` is clamped to >= 1. Plain data; nothing
// to free.
EuIdP256Bench eu_id_bench_p256(const uint8_t *z, const uint8_t *r, const uint8_t *s,
                               const uint8_t *qx, const uint8_t *qy, uint32_t iters);

#ifdef __cplusplus
}
#endif

#endif // EU_ID_FFI_H
