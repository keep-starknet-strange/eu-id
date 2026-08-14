//! Provides a thin C ABI for the mobile benchmark harness.
//! Each workload has one FFI function.
//! Rust performs the proof and measurement.
//! Each function returns a small flat structure.
//! This design excludes FFI and UI overhead from the measurement.
//!
//! Two entry points share that rule:
//! - [`eu_id_bench_sha256`] — the standalone packed SHA-256 workload.
//! - [`eu_id_bench_p256`] — the standalone P-256 ECDSA verification prover.
//!
//! A background thread samples mach `phys_footprint` at a fixed interval.
//! iOS jetsam uses this value.
//! Proof operations run on the calling thread.
//! Both entry points use `with_peak_sampler`.
//!
//! A panic must not unwind across the `extern "C"` boundary.
//! Each function uses `catch_unwind` and reports failure in the `ok` field.

// Use mimalloc for every component prover measurement.
// This keeps the host and device harnesses on the same allocator.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo_p256::proof::{verify_current_air_monolithic, P256ProofDraft};
use stwo_p256::public_inputs::PublicEcdsaInputClaim;
use stwo_p256::types::{AffinePoint, EcdsaVerifyInput, Signature, U256};
use stwo_sha256::native::n_blocks_for;
use stwo_sha256::stark::{native_digest, prove_sha256, verify_sha256_proof, ProverConfig};
use stwo_sha256::trace::min_log_size;

const MAX_FFI_PREIMAGE_BYTES: usize = 16 * 1024 * 1024;
const MAX_BENCH_ITERATIONS: u32 = 100;
const PEAK_SAMPLE_INTERVAL: Duration = Duration::from_millis(10);

// ============================ SHA-256 ============================

/// Flat result returned by [`eu_id_bench_sha256`]. `#[repr(C)]` so the
/// layout matches the hand-written `eu_id_ffi.h` struct exactly.
///
/// Check `ok` before all other fields.
/// A value of `1` means that the timing and native digest metadata are valid.
/// A value of `0` means that proof work failed.
/// In this case, all other fields are zero.
#[repr(C)]
pub struct EuIdBench {
    /// Median prove wall-clock over `iters` runs, milliseconds.
    pub prove_ms: u64,
    /// Median verify wall-clock over `iters` runs, milliseconds.
    pub verify_ms: u64,
    /// Peak `phys_footprint` observed across the whole measured window,
    /// bytes. Compare against the iOS jetsam budget (~1.3–1.5 GB).
    pub peak_bytes: u64,
    /// Native number of padded 512-bit blocks for the message.
    pub n_blocks: u64,
    /// The native 32-byte SHA-256 digest, for the caller to check
    /// independently of the standalone proof.
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

/// Run the standalone packed SHA-256 arithmetic workload for `preimage[..len]`
/// `iters` times under a peak memory sampler, and return the median timings,
/// peak footprint, and native digest metadata.
///
/// # Safety
/// `preimage` must point to at least `len` readable bytes (or `len` may be
/// `0`, in which case `preimage` is not dereferenced). `len` must not exceed
/// 16 MiB. `iters` must not exceed 100. The returned struct is plain data.
#[no_mangle]
pub unsafe extern "C" fn eu_id_bench_sha256(
    preimage: *const u8,
    len: usize,
    iters: u32,
) -> EuIdBench {
    catch_unwind(AssertUnwindSafe(|| {
        if len > MAX_FFI_PREIMAGE_BYTES || iters > MAX_BENCH_ITERATIONS {
            return EuIdBench::failed();
        }
        let message: Vec<u8> = if len == 0 {
            Vec::new()
        } else if preimage.is_null() {
            return EuIdBench::failed();
        } else {
            // SAFETY: the size is bounded above. The caller guarantees that
            // `preimage` identifies `len` readable bytes.
            unsafe { std::slice::from_raw_parts(preimage, len) }.to_vec()
        };
        run_bench(&message, iters.max(1))
    }))
    .unwrap_or_else(|_| EuIdBench::failed())
}

fn run_bench(message: &[u8], iters: u32) -> EuIdBench {
    // Size `log_n_rows` to the native padded message shape so any message
    // length proves through the one-message packed facade.
    let n_blocks = n_blocks_for(message.len());
    let config = ProverConfig {
        log_n_rows: min_log_size(n_blocks),
        ..ProverConfig::default()
    };
    let digest = native_digest(message).0;

    // Prove → verify the one-message packed workload `iters` times inside the
    // shared peak-footprint sampler window. The native metadata shaping above
    // is excluded, matching the laptop harness (only the arithmetic workload
    // is measured). The standalone facade intentionally has no exact digest or
    // padded-stream consumer.
    let ((mut prove_samples, mut verify_samples, ok), peak) = with_peak_sampler(|| {
        let mut prove_samples = Vec::with_capacity(iters as usize);
        let mut verify_samples = Vec::with_capacity(iters as usize);
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

            let t1 = Instant::now();
            if verify_sha256_proof(&proof).is_err() {
                ok = false;
                break;
            }
            verify_samples.push(t1.elapsed().as_millis() as u64);
        }
        (prove_samples, verify_samples, ok)
    });

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
/// Check `ok` before all other fields.
/// A value of `1` means that the timing fields are valid.
/// A value of `0` means that proof work failed.
/// In this case, all other fields are zero.
///
/// `verified` contains the verifier result.
/// A value of `1` means that the proof matches the five caller-supplied fields.
/// A proved signature with `verified == 0` indicates a possible soundness error.
#[repr(C)]
pub struct EuIdP256Bench {
    /// Median wall-clock to build the witness and prove one signature over
    /// `iters` runs, milliseconds.
    pub prove_ms: u64,
    /// Median verify wall-clock over `iters` runs, milliseconds.
    pub verify_ms: u64,
    /// Peak `phys_footprint` observed across the whole measured window, bytes.
    pub peak_bytes: u64,
    /// `1` if and only if the STARK proof verified against the caller's public inputs.
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

/// Runs one P-256 ECDSA build, proof, and verification for each iteration.
///
/// Reports median times, peak memory, and the verifier result.
///
/// The statement contains five 32-byte big-endian values.
/// They are `z`, `r`, `s`, `qx`, and `qy`.
/// This format matches the raw CryptoKit `r‖s` and `x‖y` encoding.
/// The Swift caller can pass the CryptoKit bytes without conversion.
/// The workload proves one signature.
///
/// # Safety
/// Each of `z`, `r`, `s`, `qx`, `qy` must point to at least 32 readable bytes.
/// The function changes an `iters` value of zero to one. `iters` must not
/// exceed 100. The returned struct is plain data.
#[no_mangle]
pub unsafe extern "C" fn eu_id_bench_p256(
    z: *const u8,
    r: *const u8,
    s: *const u8,
    qx: *const u8,
    qy: *const u8,
    iters: u32,
) -> EuIdP256Bench {
    catch_unwind(AssertUnwindSafe(|| {
        if [z, r, s, qx, qy].iter().any(|p| p.is_null()) || iters > MAX_BENCH_ITERATIONS {
            return EuIdP256Bench::failed();
        }
        let read32 = |p: *const u8| -> [u8; 32] {
            let mut out = [0u8; 32];
            // SAFETY: non-null checked above. The caller guarantees 32
            // readable bytes at each pointer.
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
        run_bench_p256(input, iters.max(1))
    }))
    .unwrap_or_else(|_| EuIdP256Bench::failed())
}

fn run_bench_p256(input: EcdsaVerifyInput, iters: u32) -> EuIdP256Bench {
    let expected = PublicEcdsaInputClaim::from_inputs(std::slice::from_ref(&input)).instances;
    let mut prove_samples = Vec::with_capacity(iters as usize);
    let mut verify_samples = Vec::with_capacity(iters as usize);
    let mut verified = true;

    // `prove_ms` includes witness construction and proof generation.
    // The SHA-256 proof path measures the same work.
    let (ok, peak_bytes) = with_peak_sampler(|| {
        for _ in 0..iters {
            let t0 = Instant::now();
            let draft = match P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![
                input.clone()
            ]) {
                Ok(d) => d,
                Err(err) => {
                    eprintln!("p256 draft error: {err:?}");
                    return false;
                }
            };
            let proof = match draft.prove_current_air_monolithic::<Blake2sMerkleChannel>() {
                Ok(p) => p,
                Err(err) => {
                    eprintln!("p256 prove error: {err:?}");
                    return false;
                }
            };
            prove_samples.push(t0.elapsed().as_millis() as u64);

            // Bind verification to the caller-supplied statement. This local
            // component benchmark does not pin a preprocessed root. The SDK
            // product verifier reconstructs and pins its root independently.
            let t1 = Instant::now();
            let outcome =
                verify_current_air_monolithic::<Blake2sMerkleChannel>(proof, &expected, None);
            verify_samples.push(t1.elapsed().as_millis() as u64);
            if let Err(err) = outcome {
                eprintln!("p256 verify error: {err:?}");
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

// ============================ Shared helpers ============================

/// Runs `work` while a background thread samples mach `phys_footprint`.
///
/// The thread uses the same 10 ms interval as the laptop harness.
/// Returns the work result and the peak memory in bytes.
/// All FFI entry points use this sampler.
fn with_peak_sampler<T>(work: impl FnOnce() -> T) -> (T, u64) {
    let sampler = PeakSampler::start();
    let result = work();
    (result, sampler.finish())
}

struct PeakSampler {
    stop: Arc<AtomicBool>,
    peak: Arc<AtomicU64>,
    thread: Option<JoinHandle<()>>,
    #[cfg(test)]
    finished: Arc<AtomicBool>,
}

impl PeakSampler {
    fn start() -> Self {
        let stop = Arc::new(AtomicBool::new(false));
        let peak = Arc::new(AtomicU64::new(0));
        let sampler_stop = Arc::clone(&stop);
        let sampler_peak = Arc::clone(&peak);
        #[cfg(test)]
        let finished = Arc::new(AtomicBool::new(false));
        #[cfg(test)]
        let sampler_finished = Arc::clone(&finished);
        let thread = thread::spawn(move || {
            while !sampler_stop.load(Ordering::Relaxed) {
                if let Some(footprint) = phys_footprint() {
                    sampler_peak.fetch_max(footprint, Ordering::Relaxed);
                }
                thread::sleep(PEAK_SAMPLE_INTERVAL);
            }
            if let Some(footprint) = phys_footprint() {
                sampler_peak.fetch_max(footprint, Ordering::Relaxed);
            }
            #[cfg(test)]
            sampler_finished.store(true, Ordering::SeqCst);
        });
        Self {
            stop,
            peak,
            thread: Some(thread),
            #[cfg(test)]
            finished,
        }
    }

    fn finish(mut self) -> u64 {
        self.stop_and_join();
        self.peak.load(Ordering::Relaxed)
    }

    fn stop_and_join(&mut self) {
        self.stop.store(true, Ordering::Relaxed);
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}

impl Drop for PeakSampler {
    fn drop(&mut self) {
        self.stop_and_join();
    }
}

fn median(samples: &mut [u64]) -> u64 {
    if samples.is_empty() {
        return 0;
    }
    samples.sort_unstable();
    samples[samples.len() / 2]
}

/// Returns the current process physical memory in bytes.
///
/// On Apple systems, `physical_mem` returns mach `phys_footprint`.
/// iOS jetsam and the laptop harness use this value.
/// The iOS simulator reports the host Mac value.
/// Returns `None` when the platform query fails.
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
    fn standalone_packed_abc_benchmark_round_trips() {
        let msg = b"abc";
        let r = unsafe { eu_id_bench_sha256(msg.as_ptr(), msg.len(), 1) };
        assert_eq!(r.ok, 1, "packed arithmetic prove/verify should succeed");
        assert_eq!(
            r.digest, ABC_DIGEST,
            "native digest must match FIPS test vector"
        );
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
    fn oversized_inputs_fail_before_pointer_reads_or_allocations() {
        let dangling = std::ptr::NonNull::<u8>::dangling().as_ptr();
        let sha = unsafe { eu_id_bench_sha256(dangling, MAX_FFI_PREIMAGE_BYTES + 1, 1) };
        assert_eq!(sha.ok, 0);
    }

    #[test]
    fn excessive_iterations_fail_without_starting_proof_work() {
        let sha = unsafe { eu_id_bench_sha256(std::ptr::null(), 0, MAX_BENCH_ITERATIONS + 1) };
        assert_eq!(sha.ok, 0);
        let dangling = std::ptr::NonNull::<u8>::dangling().as_ptr();
        let p256 = unsafe {
            eu_id_bench_p256(
                dangling,
                dangling,
                dangling,
                dangling,
                dangling,
                MAX_BENCH_ITERATIONS + 1,
            )
        };
        assert_eq!(p256.ok, 0);
    }

    #[test]
    fn rust_layout_matches_the_c_header() {
        use std::mem::{align_of, offset_of, size_of};

        assert_eq!(align_of::<EuIdBench>(), align_of::<u64>());
        assert_eq!(size_of::<EuIdBench>(), 72);
        assert_eq!(offset_of!(EuIdBench, digest), 32);
        assert_eq!(offset_of!(EuIdBench, ok), 64);

        assert_eq!(size_of::<EuIdP256Bench>(), 32);
        assert_eq!(offset_of!(EuIdP256Bench, verified), 24);
        assert_eq!(offset_of!(EuIdP256Bench, ok), 28);
    }

    #[test]
    fn sampler_thread_is_joined_when_work_panics() {
        let sampler = PeakSampler::start();
        let finished = Arc::clone(&sampler.finished);
        let outcome = catch_unwind(AssertUnwindSafe(move || {
            let _sampler = sampler;
            panic!("injected sampler-work panic");
        }));
        assert!(outcome.is_err());
        assert!(finished.load(Ordering::SeqCst));
    }

    // Validate the big-endian `(z, r, s, qx, qy)` Swift interface.
    // Raw signature bytes must prove and verify.
    // Run this test only in a release build.
    #[test]
    #[cfg_attr(
        debug_assertions,
        ignore = "release-only: full STARK prove/verify is slow in debug"
    )]
    fn p256_bench_proves_and_verifies_real_signature() {
        use p256::ecdsa::signature::Signer;
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
}
