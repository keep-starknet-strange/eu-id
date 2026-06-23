// C ABI for the eu-id mobile benchmark harness.
//
// One function per workload: prove → verify `iters` times under a peak-memory
// sampler, all measured inside Rust, returned as a flat struct.
//   - eu_id_bench_sha256   — SHA-256 of a preimage
//   - eu_id_bench_p256     — one P-256 ECDSA signature verification
//   - eu_id_bench_identity — the combined, cross-bound identity proof
//                            (P256 + SHA + digest-bind bridge + age + nationality)
//
// Hand-written to match the `#[repr(C)]` structs in src/lib.rs. Keep them in
// sync.

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

// ---- Standalone P-256 ECDSA prover ----

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

// ---- Combined identity prover (prove_identity / verify_identity) ----

// Credential + policy to prove. Matches `#[repr(C)] struct EuIdIdentityInput`
// in src/lib.rs. The credential is always signed with the built-in demo issuer
// (proving cost is independent of the issuer key).
typedef struct EuIdIdentityInput {
    uint16_t       birth_year;     // credential: birth year (e.g. 2000)
    uint8_t        birth_month;    // credential: birth month, 1..=12
    uint8_t        birth_day;      // credential: birth day, 1..=31
    uint16_t       nationality;    // credential: ISO-3166-1 numeric (276 = DE)
    uint16_t       current_year;   // policy: reference "today" year
    uint8_t        current_month;  // policy: reference month, 1..=12
    uint8_t        current_day;    // policy: reference day, 1..=31
    uint32_t       min_age_years;  // policy: minimum age (PRD headline is 18)
    const uint32_t *accepted;      // policy: accepted ISO codes (null iff len 0)
    size_t         accepted_len;   // number of accepted codes
} EuIdIdentityInput;

// Result of the combined prove -> verify. Matches `#[repr(C)] struct
// EuIdIdentityBench` in src/lib.rs.
typedef struct EuIdIdentityBench {
    uint64_t prove_ms;    // median prove_identity wall-clock over `iters`, ms
    uint64_t verify_ms;   // median verify_identity wall-clock over `iters`, ms
    uint64_t peak_bytes;  // peak phys_footprint across the window, bytes
    uint64_t proof_bytes; // serialized (bincode) combined proof size, bytes
    int32_t  ok;          // 1 = prove+verify succeeded, 0 = failed or panicked
} EuIdIdentityBench;

// Prove -> verify a bound identity statement for `input`'s credential + policy
// `iters` times (clamped to >= 1) under the peak-memory sampler. Drives the full
// P256 + SHA + bridge + age + nationality composition. `input` must point to a
// valid EuIdIdentityInput. The result is plain data; nothing to free.
EuIdIdentityBench eu_id_bench_identity(const EuIdIdentityInput *input, uint32_t iters);

#ifdef __cplusplus
}
#endif

#endif // EU_ID_FFI_H
