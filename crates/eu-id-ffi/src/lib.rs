//! Thin C-ABI surface over the standalone SHA-256 prover for the mobile
//! benchmark harness. The design rule: keep the FFI to **one function**, do the
//! proving *and* the measurement inside Rust, and return a small flat
//! struct — so FFI/UI overhead stays out of the measured window and the
//! numbers are honest.
//!
//! Memory is sampled as mach `phys_footprint` (the figure iOS jetsam
//! actually enforces) by a background thread polling
//! at a fixed cadence while `prove`/`verify` run on the calling thread.
//!
//! Panics must never unwind across the `extern "C"` boundary (UB), so the
//! whole body runs inside `catch_unwind` and failure is surfaced via the
//! `ok` field rather than a panic.

use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

use stwo_sha256::stark::{native_digest, prove_sha256, verify_sha256_proof, ProverConfig};
use stwo_sha256::trace::min_log_size;
use stwo_sha256::witness::compute_sha256_witness;

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

    // Background peak-footprint sampler. `stop` ends it; `peak` holds the
    // max `phys_footprint` seen. 10 ms cadence matches the laptop harness.
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

    stop.store(true, Ordering::Relaxed);
    let _ = sampler.join();

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
        peak_bytes: peak.load(Ordering::Relaxed),
        n_blocks: n_blocks as u64,
        digest,
        ok: 1,
    }
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
}
