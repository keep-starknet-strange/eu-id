//! Thin C-ABI surface for the quantum-safe mobile benchmark build.
//!
//! The current entry point runs the standalone SHA-256 STARK prover. Proving,
//! verification, and measurement stay inside Rust so FFI/UI overhead does not
//! affect the result. Panics are caught at the ABI boundary and reported via
//! [`EuIdBench::ok`].

// One allocator for every prover entry point on-device: mimalloc. System
// malloc cost ~4% of single-core prove; the criterion benches already pin
// mimalloc, so this keeps shipped and benched numbers on the same allocator.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

use stwo_sha256::stark::{native_digest, prove_sha256, verify_sha256_proof, ProverConfig};
use stwo_sha256::trace::min_log_size;
use stwo_sha256::witness::compute_sha256_witness;

/// Flat result returned by [`eu_id_bench_sha256`].
#[repr(C)]
pub struct EuIdBench {
    /// Median prove wall-clock over `iters` runs, milliseconds.
    pub prove_ms: u64,
    /// Median verify wall-clock over `iters` runs, milliseconds.
    pub verify_ms: u64,
    /// Peak process physical footprint observed during proving and verification.
    pub peak_bytes: u64,
    /// Number of padded 512-bit blocks in the SHA-256 witness.
    pub n_blocks: u64,
    /// Digest claimed by the proof.
    pub digest: [u8; 32],
    /// `1` on success, `0` on invalid input, prover failure, or panic.
    pub ok: i32,
}

impl EuIdBench {
    fn failed() -> Self {
        Self {
            prove_ms: 0,
            verify_ms: 0,
            peak_bytes: 0,
            n_blocks: 0,
            digest: [0; 32],
            ok: 0,
        }
    }
}

/// Prove and verify SHA-256 of `preimage[..len]` `iters` times.
///
/// # Safety
///
/// `preimage` must point to at least `len` readable bytes. A null pointer is
/// accepted only when `len == 0`.
#[no_mangle]
pub unsafe extern "C" fn eu_id_bench_sha256(
    preimage: *const u8,
    len: usize,
    iters: u32,
) -> EuIdBench {
    let message = if len == 0 {
        Vec::new()
    } else if preimage.is_null() {
        return EuIdBench::failed();
    } else {
        // SAFETY: checked non-null above; the caller guarantees `len` readable bytes.
        unsafe { std::slice::from_raw_parts(preimage, len) }.to_vec()
    };

    catch_unwind(AssertUnwindSafe(|| run_bench(&message, iters.max(1))))
        .unwrap_or_else(|_| EuIdBench::failed())
}

fn run_bench(message: &[u8], iters: u32) -> EuIdBench {
    let witness = compute_sha256_witness(message);
    let n_blocks = witness.blocks.len();
    let config = ProverConfig {
        log_n_rows: min_log_size(n_blocks),
        ..ProverConfig::default()
    };
    let expected = native_digest(message);

    let ((mut prove_samples, mut verify_samples, digest, mut ok), peak_bytes) =
        with_peak_sampler(|| {
            let mut prove_samples = Vec::with_capacity(iters as usize);
            let mut verify_samples = Vec::with_capacity(iters as usize);
            let mut digest = [0; 32];
            let mut ok = true;

            for _ in 0..iters {
                let started = Instant::now();
                let proof = match prove_sha256(message, &config) {
                    Ok(proof) => proof,
                    Err(_) => {
                        ok = false;
                        break;
                    }
                };
                prove_samples.push(started.elapsed().as_millis() as u64);
                digest = proof.digest;

                let started = Instant::now();
                if verify_sha256_proof(&proof).is_err() {
                    ok = false;
                    break;
                }
                verify_samples.push(started.elapsed().as_millis() as u64);
            }

            (prove_samples, verify_samples, digest, ok)
        });

    if digest != expected.0 {
        ok = false;
    }
    if !ok {
        return EuIdBench::failed();
    }

    EuIdBench {
        prove_ms: median(&mut prove_samples),
        verify_ms: median(&mut verify_samples),
        peak_bytes,
        n_blocks: n_blocks as u64,
        digest,
        ok: 1,
    }
}

fn with_peak_sampler<T>(work: impl FnOnce() -> T) -> (T, u64) {
    let stop = Arc::new(AtomicBool::new(false));
    let peak = Arc::new(AtomicU64::new(0));
    let sampler = {
        let stop = Arc::clone(&stop);
        let peak = Arc::clone(&peak);
        thread::spawn(move || {
            while !stop.load(Ordering::Relaxed) {
                if let Some(footprint) = phys_footprint() {
                    peak.fetch_max(footprint, Ordering::Relaxed);
                }
                thread::sleep(Duration::from_millis(10));
            }
            if let Some(footprint) = phys_footprint() {
                peak.fetch_max(footprint, Ordering::Relaxed);
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

fn phys_footprint() -> Option<u64> {
    memory_stats::memory_stats().map(|stats| stats.physical_mem as u64)
}

#[cfg(test)]
mod tests {
    use super::*;

    const ABC_DIGEST: [u8; 32] = [
        0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22,
        0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00,
        0x15, 0xad,
    ];

    #[test]
    fn bench_abc_round_trips() {
        let message = b"abc";
        let result = unsafe { eu_id_bench_sha256(message.as_ptr(), message.len(), 1) };
        assert_eq!(result.ok, 1);
        assert_eq!(result.digest, ABC_DIGEST);
        assert_eq!(result.n_blocks, 1);
        assert!(result.peak_bytes > 0);
    }

    #[test]
    fn null_preimage_is_handled() {
        let result = unsafe { eu_id_bench_sha256(std::ptr::null(), 8, 1) };
        assert_eq!(result.ok, 0);
    }
}
