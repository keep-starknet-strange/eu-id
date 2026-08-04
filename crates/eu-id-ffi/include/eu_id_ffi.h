// C ABI for the eu-id mobile benchmark harness.
//
// Each function runs and verifies its standalone packed workload in Rust.
// Each result includes the peak memory footprint.
//
// Keep these declarations synchronized with the `#[repr(C)]` types in
// `src/lib.rs`.

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
    uint64_t n_blocks;    // native padded 512-bit block count
    uint8_t  digest[32];  // native SHA-256 benchmark metadata
    int32_t  ok;          // 1 = success, 0 = prove/verify failed or panicked
} EuIdBench;

// `preimage` must identify at least `len` readable bytes.
// `len` must not exceed 16 MiB.
// Set `preimage` to null only when `len` is zero.
// The function changes an `iters` value of zero to one.
// Values above 100 fail.
// The caller does not free the result.
EuIdBench eu_id_bench_sha256(const uint8_t *preimage, size_t len, uint32_t iters);

// Standalone P-256 ECDSA prover.

typedef struct EuIdP256Bench {
    uint64_t prove_ms;    // median build+prove wall-clock over `iters`, ms
    uint64_t verify_ms;   // median verify wall-clock over `iters`, ms
    uint64_t peak_bytes;  // peak phys_footprint across the window, bytes
    int32_t  verified;    // 1 = proof verified against the five caller-supplied fields
    int32_t  ok;          // 1 = build+prove completed; check `verified`; 0 = failed/panicked
} EuIdP256Bench;

// Create and verify a proof for one P-256 ECDSA signature.
// Each input pointer must identify 32 readable big-endian bytes.
// The inputs use the CryptoKit raw `r||s` and `x||y` encodings.
// The function changes an `iters` value of zero to one.
// Values above 100 fail.
// The caller does not free the result.
EuIdP256Bench eu_id_bench_p256(const uint8_t *z, const uint8_t *r, const uint8_t *s,
                               const uint8_t *qx, const uint8_t *qy, uint32_t iters);

#ifdef __cplusplus
}
#endif

#endif // EU_ID_FFI_H
