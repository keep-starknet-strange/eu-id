//! Thin C-ABI surface over the eu-id provers for the mobile benchmark harness.
//! The design rule: keep each FFI entry point to **one function per workload**,
//! do the proving *and* the measurement inside Rust, and return a small flat
//! struct — so FFI/UI overhead stays out of the measured window and the numbers
//! are honest.
//!
//! Three entry points share that rule:
//! - [`eu_id_bench_sha256`] — the standalone SHA-256 STARK prover.
//! - [`eu_id_bench_p256`] — the standalone P-256 ECDSA verification prover.
//! - [`eu_id_bench_identity`] — the combined, cross-bound identity proof
//!   (`eu_id_prover`: P256 ECDSA + SHA-256 + digest-bind bridge + age +
//!   nationality).
//!
//! Memory is sampled as mach `phys_footprint` (the figure iOS jetsam
//! actually enforces) by a background thread polling at a fixed cadence while
//! `prove`/`verify` run on the calling thread ([`with_peak_sampler`], shared by
//! all three entry points).
//!
//! Panics must never unwind across the `extern "C"` boundary (UB), so the
//! whole body runs inside `catch_unwind` and failure is surfaced via the
//! `ok` field rather than a panic.

use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

use eu_id_prover::{
    prove_identity, verify_identity, Credential, Date, IssuerKey, Policy, PublicStatement,
};
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo_p256::proof::{verify_current_air_monolithic, P256ProofDraft};
use stwo_p256::types::{AffinePoint, EcdsaVerifyInput, Signature, U256};
use stwo_sha256::stark::{native_digest, prove_sha256, verify_sha256_proof, ProverConfig};
use stwo_sha256::trace::min_log_size;
use stwo_sha256::witness::compute_sha256_witness;

// ============================ SHA-256 ============================

/// Flat result returned by [`eu_id_bench_sha256`]. `#[repr(C)]` so the
/// layout matches the hand-written `eu_id_ffi.h` struct exactly.
///
/// `ok` is the only field the caller must check first: `1` means the
/// timing/digest fields are meaningful, `0` means the prove or verify path
/// failed (or panicked) and the other fields are zeroed.
#[repr(C)]
pub struct EuIdBench {
    /// Median prove wall-clock over `iters` runs, milliseconds.
    pub prove_ms: u64,
    /// Median verify wall-clock over `iters` runs, milliseconds.
    pub verify_ms: u64,
    /// Peak `phys_footprint` observed across the whole measured window,
    /// bytes. Compare against the iOS jetsam budget (~1.3–1.5 GB).
    pub peak_bytes: u64,
    /// Number of padded 512-bit blocks the message hashed to.
    pub n_blocks: u64,
    /// The 32-byte digest the prover claims, for the caller to check
    /// against an independent SHA-256.
    pub digest: [u8; 32],
    /// `1` = success, `0` = prove/verify failed or panicked.
    pub ok: i32,
}

impl EuIdBench {
    fn failed() -> Self {
        Self {
            prove_ms: 0,
            verify_ms: 0,
            peak_bytes: 0,
            n_blocks: 0,
            digest: [0u8; 32],
            ok: 0,
        }
    }
}

/// Prove → verify SHA-256 of `preimage[..len]` `iters` times under a peak
/// memory sampler, and return the median timings, peak footprint, and
/// claimed digest.
///
/// # Safety
/// `preimage` must point to at least `len` readable bytes (or `len` may be
/// `0`, in which case `preimage` is not dereferenced). The returned struct
/// is plain data — there is nothing to free.
#[no_mangle]
pub unsafe extern "C" fn eu_id_bench_sha256(
    preimage: *const u8,
    len: usize,
    iters: u32,
) -> EuIdBench {
    // Copy the caller's bytes into Rust-owned memory before doing anything
    // else, so the rest of the body touches no raw pointers.
    let message: Vec<u8> = if len == 0 {
        Vec::new()
    } else if preimage.is_null() {
        return EuIdBench::failed();
    } else {
        std::slice::from_raw_parts(preimage, len).to_vec()
    };

    let iters = iters.max(1);

    // Any panic inside the prover (e.g. an unsupported config) is caught
    // here and turned into `ok = 0` rather than unwinding into C.
    catch_unwind(AssertUnwindSafe(|| run_bench(&message, iters)))
        .unwrap_or_else(|_| EuIdBench::failed())
}

fn run_bench(message: &[u8], iters: u32) -> EuIdBench {
    // Size `log_n_rows` to the witness so any message length proves — the
    // same shaping `prove_demo` does (ProverConfig::default()'s
    // log_n_rows = 4 only fits ~1 KiB messages).
    let witness = compute_sha256_witness(message);
    let n_blocks = witness.blocks.len();
    let config = ProverConfig {
        log_n_rows: min_log_size(n_blocks),
        ..ProverConfig::default()
    };
    let expected = native_digest(message);

    // prove → verify the message `iters` times inside the shared peak-footprint
    // sampler window; the witness sizing above is excluded, matching the laptop
    // harness (only the prove/verify path is measured).
    let ((mut prove_samples, mut verify_samples, digest, mut ok), peak) = with_peak_sampler(|| {
        let mut prove_samples = Vec::with_capacity(iters as usize);
        let mut verify_samples = Vec::with_capacity(iters as usize);
        let mut digest = [0u8; 32];
        let mut ok = true;

        for _ in 0..iters {
            let t0 = Instant::now();
            let proof = match prove_sha256(message, &config) {
                Ok(p) => p,
                Err(_) => {
                    ok = false;
                    break;
                }
            };
            prove_samples.push(t0.elapsed().as_millis() as u64);
            digest = proof.digest;

            let t1 = Instant::now();
            if verify_sha256_proof(&proof).is_err() {
                ok = false;
                break;
            }
            verify_samples.push(t1.elapsed().as_millis() as u64);
        }
        (prove_samples, verify_samples, digest, ok)
    });

    // A digest disagreement with the independent native hash is also a
    // failure, even if prove+verify both "succeeded".
    if digest != expected.0 {
        ok = false;
    }

    if !ok {
        return EuIdBench::failed();
    }

    EuIdBench {
        prove_ms: median(&mut prove_samples),
        verify_ms: median(&mut verify_samples),
        peak_bytes: peak,
        n_blocks: n_blocks as u64,
        digest,
        ok: 1,
    }
}

// ============================ P-256 ECDSA ============================

/// Flat result returned by [`eu_id_bench_p256`]. `#[repr(C)]` so the layout
/// matches the hand-written `eu_id_ffi.h` struct exactly.
///
/// Check `ok` first: `1` means the timing fields are meaningful, `0` means the
/// draft build, prove, or verify path failed (or panicked) and the rest is
/// zeroed. `verified` is the verifier's verdict — `1` iff the STARK proof
/// verified against the public statement it embeds. A signature that proves but
/// reports `verified == 0` is a soundness red flag, surfaced like a digest
/// mismatch rather than hidden behind `ok`.
#[repr(C)]
pub struct EuIdP256Bench {
    /// Median wall-clock to build the witness and prove one signature over
    /// `iters` runs, milliseconds.
    pub prove_ms: u64,
    /// Median verify wall-clock over `iters` runs, milliseconds.
    pub verify_ms: u64,
    /// Peak `phys_footprint` observed across the whole measured window, bytes.
    pub peak_bytes: u64,
    /// `1` iff the monolithic STARK proof verified against its public inputs.
    pub verified: i32,
    /// `1` = draft+prove succeeded (timings meaningful), `0` = failed/panicked.
    pub ok: i32,
}

impl EuIdP256Bench {
    fn failed() -> Self {
        Self {
            prove_ms: 0,
            verify_ms: 0,
            peak_bytes: 0,
            verified: 0,
            ok: 0,
        }
    }
}

/// Build → prove → verify one P-256 ECDSA signature `iters` times under a peak
/// memory sampler, returning median timings, peak footprint, and the verifier's
/// verdict.
///
/// The statement is five 32-byte **big-endian** field elements — `z` (message
/// hash), the signature `(r, s)`, and the public key `(qx, qy)` — which is
/// exactly CryptoKit's raw `r‖s` / `x‖y` encoding, so the Swift caller signs
/// with CryptoKit and hands the bytes straight through. Proving the signature
/// is the whole workload; there is no message-size axis because the AIR covers
/// exactly one signature.
///
/// # Safety
/// Each of `z`, `r`, `s`, `qx`, `qy` must point to at least 32 readable bytes.
/// `iters` is clamped to `>= 1`. The returned struct is plain data — there is
/// nothing to free.
#[no_mangle]
pub unsafe extern "C" fn eu_id_bench_p256(
    z: *const u8,
    r: *const u8,
    s: *const u8,
    qx: *const u8,
    qy: *const u8,
    iters: u32,
) -> EuIdP256Bench {
    if [z, r, s, qx, qy].iter().any(|p| p.is_null()) {
        return EuIdP256Bench::failed();
    }

    // Copy the caller's bytes into Rust-owned `U256`s before touching the
    // prover, so the rest of the body holds no raw pointers.
    let read32 = |p: *const u8| -> [u8; 32] {
        let mut out = [0u8; 32];
        // SAFETY: non-null checked above; the caller guarantees 32 readable
        // bytes at each pointer per the function contract.
        out.copy_from_slice(unsafe { std::slice::from_raw_parts(p, 32) });
        out
    };
    let input = EcdsaVerifyInput {
        message_hash: U256(read32(z)),
        signature: Signature {
            r: U256(read32(r)),
            s: U256(read32(s)),
        },
        public_key: AffinePoint {
            x: U256(read32(qx)),
            y: U256(read32(qy)),
        },
    };

    let iters = iters.max(1);

    catch_unwind(AssertUnwindSafe(|| run_bench_p256(input, iters)))
        .unwrap_or_else(|_| EuIdP256Bench::failed())
}

fn run_bench_p256(input: EcdsaVerifyInput, iters: u32) -> EuIdP256Bench {
    let mut prove_samples = Vec::with_capacity(iters as usize);
    let mut verify_samples = Vec::with_capacity(iters as usize);
    let mut verified = true;

    // `prove_ms` covers witness build + prove together, mirroring how the
    // SHA-256 path's prove call regenerates its own witness — the full cost of
    // turning inputs into a proof.
    let (ok, peak_bytes) = with_peak_sampler(|| {
        for _ in 0..iters {
            let t0 = Instant::now();
            let draft = match P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![
                input.clone()
            ]) {
                Ok(d) => d,
                Err(_) => return false,
            };
            let proof = match draft.prove_current_air_monolithic::<Blake2sMerkleChannel>() {
                Ok(p) => p,
                Err(_) => return false,
            };
            prove_samples.push(t0.elapsed().as_millis() as u64);

            // Bind verification to the statement the proof itself embeds — the
            // same self-binding the crate's own end-to-end tests use.
            let expected = proof.claim.public_inputs.instances.clone();
            let t1 = Instant::now();
            let outcome = verify_current_air_monolithic::<Blake2sMerkleChannel>(proof, &expected);
            verify_samples.push(t1.elapsed().as_millis() as u64);
            if outcome.is_err() {
                verified = false;
            }
        }
        true
    });

    if !ok {
        return EuIdP256Bench::failed();
    }

    EuIdP256Bench {
        prove_ms: median(&mut prove_samples),
        verify_ms: median(&mut verify_samples),
        peak_bytes,
        verified: i32::from(verified),
        ok: 1,
    }
}

// ====================== Combined identity proof ======================

/// Flat input describing the credential + policy [`eu_id_bench_identity`] proves.
/// `#[repr(C)]` so the layout matches the hand-written `eu_id_ffi.h` struct
/// exactly.
///
/// The credential fields are the simplified POC layout's semantic values
/// ([`eu_id_prover::Credential`]); the policy fields are the relying party's
/// `{ reference date, age threshold, accepted nationality set }`. The credential
/// is always signed with the built-in **demo issuer** ([`IssuerKey::demo`]) and
/// verified against the matching public statement — the benchmark measures
/// proving cost, which does not depend on the issuer key.
#[repr(C)]
pub struct EuIdIdentityInput {
    /// Credential birth year (e.g. `2000`).
    pub birth_year: u16,
    /// Credential birth month, `1..=12`.
    pub birth_month: u8,
    /// Credential birth day, `1..=31`.
    pub birth_day: u8,
    /// Credential nationality (ISO-3166-1 numeric, e.g. `276` = Germany).
    pub nationality: u16,
    /// Policy reference "today" — year.
    pub current_year: u16,
    /// Policy reference "today" — month, `1..=12`.
    pub current_month: u8,
    /// Policy reference "today" — day, `1..=31`.
    pub current_day: u8,
    /// Policy minimum age in years (the PRD headline is 18).
    pub min_age_years: u32,
    /// Pointer to `accepted_len` ISO-3166-1 numeric codes — the accepted
    /// nationality set. May be null iff `accepted_len == 0`.
    pub accepted: *const u32,
    /// Number of codes `accepted` points to.
    pub accepted_len: usize,
}

/// Flat result returned by [`eu_id_bench_identity`]. `#[repr(C)]` so the layout
/// matches the hand-written `eu_id_ffi.h` struct exactly.
///
/// `ok` is the field to check first: `1` means the timing/size fields are
/// meaningful, `0` means prove or verify failed (a false statement, a malformed
/// input, or a panic) and the others are zeroed.
#[repr(C)]
pub struct EuIdIdentityBench {
    /// Median `prove_identity` wall-clock over `iters` runs, milliseconds.
    pub prove_ms: u64,
    /// Median `verify_identity` wall-clock over `iters` runs, milliseconds.
    pub verify_ms: u64,
    /// Peak `phys_footprint` observed across the whole measured window,
    /// bytes. Compare against the iOS jetsam budget (~1.3–1.5 GB).
    pub peak_bytes: u64,
    /// Serialized (bincode) size of the combined proof, bytes.
    pub proof_bytes: u64,
    /// `1` = prove + verify succeeded, `0` = failed or panicked.
    pub ok: i32,
}

impl EuIdIdentityBench {
    fn failed() -> Self {
        Self {
            prove_ms: 0,
            verify_ms: 0,
            peak_bytes: 0,
            proof_bytes: 0,
            ok: 0,
        }
    }
}

/// Prove → verify a bound identity statement for `input`'s credential + policy
/// `iters` times under the peak-memory sampler, and return the median timings,
/// peak footprint, and serialized proof size.
///
/// The combined-prover counterpart of [`eu_id_bench_sha256`] / [`eu_id_bench_p256`]:
/// it drives the full [`eu_id_prover`] composition (P256 ECDSA, SHA-256, the
/// digest-bind bridge, and the age + nationality predicates), which is
/// **cross-bound** — the signature is over `SHA-256(C)`, and the age /
/// nationality predicates reason about the credential's signed bytes. The
/// credential is signed with the built-in demo issuer and verified against the
/// matching statement `{ Q, policy }`, so an honest over-age, in-set credential
/// yields `ok = 1`; a false statement (e.g. under age, or a nationality outside
/// the accepted set) cannot be proved and yields `ok = 0`.
///
/// The composition is dominated by P256, which has no rayon path yet, so the
/// crate's `parallel` feature (SHA-only) barely moves the combined number —
/// parallelizing the cost driver is a benchmarking follow-up.
///
/// # Safety
/// `input` must point to a valid [`EuIdIdentityInput`]; its `accepted` pointer
/// must address `accepted_len` readable `u32`s (or be null iff
/// `accepted_len == 0`). The returned struct is plain data — there is nothing to
/// free.
#[no_mangle]
pub unsafe extern "C" fn eu_id_bench_identity(
    input: *const EuIdIdentityInput,
    iters: u32,
) -> EuIdIdentityBench {
    if input.is_null() {
        return EuIdIdentityBench::failed();
    }
    // Copy the caller's input into Rust-owned values before doing anything else,
    // so the rest of the body touches no raw pointers.
    let input = &*input;
    let accepted: Vec<u32> = if input.accepted_len == 0 {
        Vec::new()
    } else if input.accepted.is_null() {
        return EuIdIdentityBench::failed();
    } else {
        std::slice::from_raw_parts(input.accepted, input.accepted_len).to_vec()
    };

    let credential = Credential::new(
        input.birth_year,
        input.birth_month,
        input.birth_day,
        input.nationality,
    );
    let policy = Policy {
        current_date: Date {
            year: u32::from(input.current_year),
            month: u32::from(input.current_month),
            day: u32::from(input.current_day),
        },
        min_age_years: input.min_age_years,
        accepted_nationalities: accepted,
    };
    let iters = iters.max(1);

    // Any panic inside the prover is caught here and turned into `ok = 0` rather
    // than unwinding into C.
    catch_unwind(AssertUnwindSafe(|| {
        run_identity_bench(&credential, &policy, iters)
    }))
    .unwrap_or_else(|_| EuIdIdentityBench::failed())
}

fn run_identity_bench(credential: &Credential, policy: &Policy, iters: u32) -> EuIdIdentityBench {
    let issuer = IssuerKey::demo();
    // The relying party's statement: the demo issuer's *public* key (the trusted
    // anchor) + the policy, built independently of the proof — exactly what
    // `verify_identity` checks against.
    let statement = PublicStatement::new(issuer.public_key(), policy.clone());

    let ((mut prove_samples, mut verify_samples, last_proof, ok), peak) = with_peak_sampler(|| {
        let mut prove_samples = Vec::with_capacity(iters as usize);
        let mut verify_samples = Vec::with_capacity(iters as usize);
        let mut last_proof = None;
        let mut ok = true;

        for _ in 0..iters {
            let t0 = Instant::now();
            let proof = match prove_identity(credential, &issuer, policy) {
                Ok(p) => p,
                // A false statement (e.g. under age) is rejected at witness
                // generation — there is no proof to verify.
                Err(_) => {
                    ok = false;
                    break;
                }
            };
            prove_samples.push(t0.elapsed().as_millis() as u64);

            let t1 = Instant::now();
            if verify_identity(&proof, &statement).is_err() {
                ok = false;
                break;
            }
            verify_samples.push(t1.elapsed().as_millis() as u64);
            last_proof = Some(proof);
        }
        (prove_samples, verify_samples, last_proof, ok)
    });

    if !ok {
        return EuIdIdentityBench::failed();
    }

    // Serialized proof size, measured *after* the sampler stops so it cannot
    // inflate the peak. Best-effort: a serialize failure (shouldn't happen for a
    // valid proof) reports 0 without failing the run.
    let proof_bytes = last_proof
        .as_ref()
        .and_then(|p| bincode::serialize(p).ok())
        .map(|b| b.len() as u64)
        .unwrap_or(0);

    EuIdIdentityBench {
        prove_ms: median(&mut prove_samples),
        verify_ms: median(&mut verify_samples),
        peak_bytes: peak,
        proof_bytes,
        ok: 1,
    }
}

// ============================ Shared helpers ============================

/// Run `work` while a background thread samples mach `phys_footprint` at a fixed
/// 10 ms cadence (matching the laptop harness), and return `work`'s result
/// alongside the peak footprint (bytes) seen across the whole window. All FFI
/// entry points measure peak memory through this one sampler, so laptop and
/// phone numbers come from a single code path.
fn with_peak_sampler<T>(work: impl FnOnce() -> T) -> (T, u64) {
    // `stop` ends the sampler; `peak` holds the max `phys_footprint` seen.
    let stop = Arc::new(AtomicBool::new(false));
    let peak = Arc::new(AtomicU64::new(0));
    let sampler = {
        let stop = Arc::clone(&stop);
        let peak = Arc::clone(&peak);
        thread::spawn(move || {
            while !stop.load(Ordering::Relaxed) {
                if let Some(f) = phys_footprint() {
                    peak.fetch_max(f, Ordering::Relaxed);
                }
                thread::sleep(Duration::from_millis(10));
            }
            // Final sample after the work stops, in case the peak landed
            // between the last poll and shutdown.
            if let Some(f) = phys_footprint() {
                peak.fetch_max(f, Ordering::Relaxed);
            }
        })
    };

    let result = work();

    stop.store(true, Ordering::Relaxed);
    let _ = sampler.join();
    (result, peak.load(Ordering::Relaxed))
}

fn median(samples: &mut [u64]) -> u64 {
    if samples.is_empty() {
        return 0;
    }
    samples.sort_unstable();
    samples[samples.len() / 2]
}

/// Current process physical memory in bytes. On Apple `physical_mem`
/// resolves to mach `phys_footprint` — the figure iOS jetsam enforces,
/// matching the laptop harness. macOS and the iOS
/// simulator share the Darwin kernel, so this also works under the
/// simulator (where it reports the host Mac's footprint, not a phone's).
/// Returns `None` if the platform query fails.
fn phys_footprint() -> Option<u64> {
    memory_stats::memory_stats().map(|s| s.physical_mem as u64)
}

#[cfg(test)]
mod tests {
    use super::*;

    // FIPS 180-4 Appendix B.1: SHA-256("abc").
    const ABC_DIGEST: [u8; 32] = [
        0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22,
        0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00,
        0x15, 0xad,
    ];

    #[test]
    fn bench_abc_round_trips() {
        let msg = b"abc";
        let r = unsafe { eu_id_bench_sha256(msg.as_ptr(), msg.len(), 1) };
        assert_eq!(r.ok, 1, "prove/verify should succeed");
        assert_eq!(r.digest, ABC_DIGEST, "digest must match FIPS test vector");
        assert_eq!(r.n_blocks, 1);
        assert!(r.peak_bytes > 0, "sampler should observe nonzero footprint");
    }

    #[test]
    fn null_preimage_is_handled() {
        let r = unsafe { eu_id_bench_sha256(std::ptr::null(), 8, 1) };
        assert_eq!(r.ok, 0, "null ptr with nonzero len must fail cleanly");
    }

    #[test]
    fn p256_null_pointer_is_handled() {
        let b = [0u8; 32];
        // A single null field element must fail cleanly, never deref.
        let r = unsafe {
            eu_id_bench_p256(
                std::ptr::null(),
                b.as_ptr(),
                b.as_ptr(),
                b.as_ptr(),
                b.as_ptr(),
                1,
            )
        };
        assert_eq!(r.ok, 0, "null field element must fail cleanly");
        assert_eq!(r.verified, 0);
    }

    #[test]
    fn null_identity_input_is_handled() {
        let r = unsafe { eu_id_bench_identity(std::ptr::null(), 1) };
        assert_eq!(r.ok, 0, "null input must fail cleanly");
    }

    // Validates the big-endian (z, r, s, qx, qy) marshalling contract the Swift
    // caller relies on: a real signature handed in as raw bytes must prove and
    // verify. Release-only — a full STARK prove/verify is slow in debug.
    #[test]
    #[cfg_attr(
        debug_assertions,
        ignore = "release-only: full STARK prove/verify is slow in debug"
    )]
    fn p256_bench_proves_and_verifies_real_signature() {
        use ecdsa::signature::Signer;
        use p256::ecdsa::{Signature as P256Signature, SigningKey};
        use sha2::{Digest, Sha256};

        let signing_key = SigningKey::from_bytes((&[7u8; 32]).into()).expect("valid signing key");
        let verifying_key = signing_key.verifying_key();
        let message = b"eu-id-ffi p256 bench fixture";
        let digest = Sha256::digest(message);
        let signature: P256Signature = signing_key.sign(message);
        let encoded = verifying_key.to_encoded_point(false);

        let z_bytes: [u8; 32] = digest.into();
        let r_bytes: [u8; 32] = signature.r().to_bytes().into();
        let s_bytes: [u8; 32] = signature.s().to_bytes().into();
        let x_bytes: [u8; 32] = encoded.x().expect("x")[..].try_into().expect("x len");
        let y_bytes: [u8; 32] = encoded.y().expect("y")[..].try_into().expect("y len");

        let r = unsafe {
            eu_id_bench_p256(
                z_bytes.as_ptr(),
                r_bytes.as_ptr(),
                s_bytes.as_ptr(),
                x_bytes.as_ptr(),
                y_bytes.as_ptr(),
                1,
            )
        };
        assert_eq!(r.ok, 1, "real signature should build + prove");
        assert_eq!(r.verified, 1, "real signature proof should verify");
        assert!(r.peak_bytes > 0, "sampler should observe nonzero footprint");
    }

    /// Round-trip the combined prover over a known-good fixture credential: an
    /// honest, over-18, in-set credential proves and verifies, and the sampler /
    /// size fields are populated. `#[ignore]` — a full P256-dominated STARK
    /// prove/verify is slow; run with `--release --ignored`.
    #[test]
    #[ignore = "slow: full combined STARK prove/verify (P256-dominated); run with --release --ignored"]
    fn identity_bench_round_trips() {
        let fixture = eu_id_prover::fixtures::valid_over_18();
        let cred = fixture.signed.credential;
        let policy = fixture.policy;
        // `accepted` must outlive the call — `input` holds a raw pointer into it.
        let accepted = policy.accepted_nationalities.clone();
        let input = EuIdIdentityInput {
            birth_year: cred.birth_year,
            birth_month: cred.birth_month,
            birth_day: cred.birth_day,
            nationality: cred.nationality,
            current_year: policy.current_date.year as u16,
            current_month: policy.current_date.month as u8,
            current_day: policy.current_date.day as u8,
            min_age_years: policy.min_age_years,
            accepted: accepted.as_ptr(),
            accepted_len: accepted.len(),
        };

        let r = unsafe { eu_id_bench_identity(&input, 1) };
        assert_eq!(r.ok, 1, "an honest over-18 credential should prove + verify");
        assert!(r.peak_bytes > 0, "sampler should observe nonzero footprint");
        assert!(
            r.proof_bytes > 0,
            "a successful proof has nonzero serialized size"
        );
    }
}
