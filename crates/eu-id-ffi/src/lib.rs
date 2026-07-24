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

#[cfg(feature = "jni")]
mod android_jni;

#[cfg(feature = "jni")]
#[allow(dead_code)]
#[path = "../../eu-id-prover/tests/mldsa_fixture.rs"]
mod mldsa_fixture;

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

// ====================== Full-PQ mdoc + revocation ======================

/// One canonical full-PQ mdoc measurement for the Android Game Loop harness.
///
/// The proof contains ML-DSA-65 issuer and device authentication, the product
/// age/nationality predicates, and one ML-DSA-65 TS13 revocation statement.
#[cfg(feature = "jni")]
#[repr(C)]
pub struct EuIdFullPqBench {
    pub prove_ms: u64,
    pub process_cpu_ms: u64,
    pub cold_verify_ms: u64,
    pub cold_tree0_root_ms: u64,
    pub cold_stark_verify_ms: u64,
    pub warm_verify_ms: u64,
    pub warm_tree0_root_ms: u64,
    pub warm_stark_verify_ms: u64,
    pub peak_bytes: u64,
    pub proof_bytes: u64,
    pub rayon_threads: u32,
    pub worker_cpu_mask: u64,
    pub excluded_cpu_mask: u64,
    pub core_metric: u32,
    pub ok: i32,
}

#[cfg(feature = "jni")]
#[derive(Clone, Copy, Default)]
struct BenchmarkThreading {
    rayon_threads: u32,
    worker_cpu_mask: u64,
    excluded_cpu_mask: u64,
    core_metric: u32,
}

#[cfg(feature = "jni")]
impl EuIdFullPqBench {
    fn failed(threading: BenchmarkThreading) -> Self {
        Self {
            prove_ms: 0,
            process_cpu_ms: 0,
            cold_verify_ms: 0,
            cold_tree0_root_ms: 0,
            cold_stark_verify_ms: 0,
            warm_verify_ms: 0,
            warm_tree0_root_ms: 0,
            warm_stark_verify_ms: 0,
            peak_bytes: 0,
            proof_bytes: 0,
            rayon_threads: threading.rayon_threads,
            worker_cpu_mask: threading.worker_cpu_mask,
            excluded_cpu_mask: threading.excluded_cpu_mask,
            core_metric: threading.core_metric,
            ok: 0,
        }
    }
}

#[cfg(feature = "jni")]
struct BenchmarkCores {
    worker_cpu_ids: Vec<usize>,
    excluded_cpu_ids: Vec<usize>,
    metric: u32,
}

#[cfg(all(feature = "jni", not(target_os = "android")))]
const CORE_METRIC_HOST_AVAILABLE: u32 = 0;
#[cfg(all(feature = "jni", target_os = "android"))]
const CORE_METRIC_CPU_CAPACITY: u32 = 1;
#[cfg(all(feature = "jni", target_os = "android"))]
const CORE_METRIC_CPUINFO_MAX_FREQ: u32 = 2;

/// Prove once and verify twice (cold then cached) using the same fixture and
/// production PCS configuration as `pq_perf_probe`.
#[cfg(feature = "jni")]
#[no_mangle]
pub extern "C" fn eu_id_bench_full_pq(all_performance_cores: bool) -> EuIdFullPqBench {
    const BENCHMARK_RAYON_STACK_BYTES: usize = 64 * 1024 * 1024;

    let cores = match benchmark_cores(all_performance_cores) {
        Ok(cores) => cores,
        Err(error) => {
            eprintln!("full-PQ benchmark core selection failed: {error}");
            return EuIdFullPqBench::failed(BenchmarkThreading::default());
        }
    };
    let worker_cpu_mask = match cpu_mask(&cores.worker_cpu_ids) {
        Ok(mask) => mask,
        Err(error) => {
            eprintln!("full-PQ benchmark worker mask failed: {error}");
            return EuIdFullPqBench::failed(BenchmarkThreading::default());
        }
    };
    let excluded_cpu_mask = match cpu_mask(&cores.excluded_cpu_ids) {
        Ok(mask) => mask,
        Err(error) => {
            eprintln!("full-PQ benchmark excluded mask failed: {error}");
            return EuIdFullPqBench::failed(BenchmarkThreading::default());
        }
    };
    let pool = match build_benchmark_pool(&cores.worker_cpu_ids, BENCHMARK_RAYON_STACK_BYTES) {
        Ok(pool) => pool,
        Err(error) => {
            eprintln!("full-PQ benchmark Rayon pool failed: {error}");
            return EuIdFullPqBench::failed(BenchmarkThreading::default());
        }
    };
    let threading = BenchmarkThreading {
        rayon_threads: pool.current_num_threads() as u32,
        worker_cpu_mask,
        excluded_cpu_mask,
        core_metric: cores.metric,
    };
    if threading.rayon_threads as usize != cores.worker_cpu_ids.len() {
        eprintln!(
            "full-PQ benchmark requested {} Rayon threads, got {}",
            cores.worker_cpu_ids.len(),
            threading.rayon_threads
        );
        return EuIdFullPqBench::failed(threading);
    }

    catch_unwind(AssertUnwindSafe(|| {
        pool.install(|| run_full_pq_bench(threading))
    }))
    .unwrap_or_else(|_| EuIdFullPqBench::failed(threading))
}

#[cfg(all(feature = "jni", not(target_os = "android")))]
fn benchmark_cores(all_performance_cores: bool) -> Result<BenchmarkCores, String> {
    let count = std::thread::available_parallelism()
        .map(std::num::NonZeroUsize::get)
        .unwrap_or(1);
    let worker_cpu_ids = if all_performance_cores {
        (0..count).collect()
    } else {
        vec![0]
    };
    Ok(BenchmarkCores {
        worker_cpu_ids,
        excluded_cpu_ids: Vec::new(),
        metric: CORE_METRIC_HOST_AVAILABLE,
    })
}

#[cfg(all(feature = "jni", target_os = "android"))]
fn benchmark_cores(all_performance_cores: bool) -> Result<BenchmarkCores, String> {
    let allowed = android_allowed_cpu_ids()?;
    for (metric, suffix) in [
        (CORE_METRIC_CPU_CAPACITY, "cpu_capacity"),
        (CORE_METRIC_CPUINFO_MAX_FREQ, "cpufreq/cpuinfo_max_freq"),
    ] {
        if let Some(values) = android_cpu_metric(&allowed, suffix) {
            if let (Some(performance_cpu_ids), Some(worker_cpu_ids)) = (
                select_performance_core_ids(&values),
                select_worker_cpu_ids(&values, all_performance_cores),
            ) {
                let excluded_cpu_ids = allowed
                    .iter()
                    .copied()
                    .filter(|cpu_id| !performance_cpu_ids.contains(cpu_id))
                    .collect();
                return Ok(BenchmarkCores {
                    worker_cpu_ids,
                    excluded_cpu_ids,
                    metric,
                });
            }
        }
    }
    Err("neither cpu_capacity nor cpuinfo_max_freq identified a heterogeneous cluster".to_owned())
}

#[cfg(all(feature = "jni", target_os = "android"))]
fn android_allowed_cpu_ids() -> Result<Vec<usize>, String> {
    let mut mask = unsafe { std::mem::zeroed::<libc::cpu_set_t>() };
    // SAFETY: `mask` is a valid writable cpu_set_t and its exact size is supplied.
    let result = unsafe {
        libc::sched_getaffinity(
            0,
            std::mem::size_of::<libc::cpu_set_t>(),
            std::ptr::addr_of_mut!(mask),
        )
    };
    if result != 0 {
        return Err(std::io::Error::last_os_error().to_string());
    }
    let cpu_ids = (0..libc::CPU_SETSIZE as usize)
        // SAFETY: `mask` was initialized by a successful sched_getaffinity call,
        // and every probed CPU index is below CPU_SETSIZE.
        .filter(|cpu_id| unsafe { libc::CPU_ISSET(*cpu_id, &mask) })
        .collect::<Vec<_>>();
    if cpu_ids.is_empty() {
        return Err("sched_getaffinity returned an empty CPU set".to_owned());
    }
    Ok(cpu_ids)
}

#[cfg(all(feature = "jni", target_os = "android"))]
fn android_cpu_metric(cpu_ids: &[usize], suffix: &str) -> Option<Vec<(usize, u64)>> {
    cpu_ids
        .iter()
        .map(|cpu_id| {
            let path = format!("/sys/devices/system/cpu/cpu{cpu_id}/{suffix}");
            let value = std::fs::read_to_string(path)
                .ok()?
                .trim()
                .parse::<u64>()
                .ok()?;
            Some((*cpu_id, value))
        })
        .collect()
}

#[cfg(all(feature = "jni", any(target_os = "android", test)))]
fn select_performance_core_ids(metrics: &[(usize, u64)]) -> Option<Vec<usize>> {
    let minimum = metrics.iter().map(|(_, value)| *value).min()?;
    let selected = metrics
        .iter()
        .filter_map(|(cpu_id, value)| (*value > minimum).then_some(*cpu_id))
        .collect::<Vec<_>>();
    (!selected.is_empty()).then_some(selected)
}

#[cfg(all(feature = "jni", any(target_os = "android", test)))]
fn select_worker_cpu_ids(
    metrics: &[(usize, u64)],
    all_performance_cores: bool,
) -> Option<Vec<usize>> {
    let performance = select_performance_core_ids(metrics)?;
    if all_performance_cores {
        return Some(performance);
    }
    metrics
        .iter()
        .filter(|(cpu_id, _)| performance.contains(cpu_id))
        .max_by_key(|(cpu_id, value)| (*value, *cpu_id))
        .map(|(cpu_id, _)| vec![*cpu_id])
}

#[cfg(feature = "jni")]
fn cpu_mask(cpu_ids: &[usize]) -> Result<u64, String> {
    cpu_ids.iter().try_fold(0_u64, |mask, cpu_id| {
        let bit = 1_u64
            .checked_shl((*cpu_id).try_into().unwrap_or(u32::MAX))
            .ok_or_else(|| format!("CPU {cpu_id} cannot be represented in the result mask"))?;
        if mask & bit != 0 {
            return Err(format!("CPU {cpu_id} appears more than once"));
        }
        Ok(mask | bit)
    })
}

#[cfg(feature = "jni")]
fn build_benchmark_pool(
    cpu_ids: &[usize],
    stack_bytes: usize,
) -> Result<rayon::ThreadPool, String> {
    if cpu_ids.is_empty() {
        return Err("no worker CPUs selected".to_owned());
    }

    #[cfg(target_os = "android")]
    let builder = {
        let worker_cpu_ids = Arc::new(cpu_ids.to_vec());
        rayon::ThreadPoolBuilder::new()
            .num_threads(cpu_ids.len())
            .stack_size(stack_bytes)
            .spawn_handler(move |rayon_thread| {
                let cpu_id = worker_cpu_ids[rayon_thread.index()];
                let (sender, receiver) = std::sync::mpsc::sync_channel(0);
                let mut builder = std::thread::Builder::new();
                if let Some(name) = rayon_thread.name() {
                    builder = builder.name(name.to_owned());
                }
                if let Some(stack_size) = rayon_thread.stack_size() {
                    builder = builder.stack_size(stack_size);
                }
                let _worker = builder.spawn(move || {
                    let pin_result = pin_current_thread(cpu_id);
                    let pinned = pin_result.is_ok();
                    let _ = sender.send(pin_result);
                    if pinned {
                        rayon_thread.run();
                    }
                })?;
                match receiver.recv() {
                    Ok(result) => result,
                    Err(error) => Err(std::io::Error::new(std::io::ErrorKind::BrokenPipe, error)),
                }
            })
    };
    #[cfg(not(target_os = "android"))]
    let builder = rayon::ThreadPoolBuilder::new()
        .num_threads(cpu_ids.len())
        .stack_size(stack_bytes);

    builder.build().map_err(|error| error.to_string())
}

#[cfg(all(feature = "jni", target_os = "android"))]
fn pin_current_thread(cpu_id: usize) -> std::io::Result<()> {
    if cpu_id >= libc::CPU_SETSIZE as usize {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!("CPU {cpu_id} exceeds CPU_SETSIZE"),
        ));
    }
    let mut mask = unsafe { std::mem::zeroed::<libc::cpu_set_t>() };
    // SAFETY: `mask` is a valid cpu_set_t and `cpu_id` was bounded above.
    unsafe {
        libc::CPU_ZERO(&mut mask);
        libc::CPU_SET(cpu_id, &mut mask);
    }
    // SAFETY: `mask` is initialized and its exact size is supplied.
    let result = unsafe {
        libc::sched_setaffinity(
            0,
            std::mem::size_of::<libc::cpu_set_t>(),
            std::ptr::addr_of!(mask),
        )
    };
    if result == 0 {
        Ok(())
    } else {
        Err(std::io::Error::last_os_error())
    }
}

#[cfg(feature = "jni")]
fn run_full_pq_bench(threading: BenchmarkThreading) -> EuIdFullPqBench {
    use eu_id_prover::mdoc::{
        extract_pid_mdoc, mdoc_production_pcs_config, openid4vp_session_transcript,
        prove_mdoc_circuit, verify_mdoc_circuit_with_pcs_config_profiled,
        verify_mdoc_circuit_with_pcs_config_profiled_fresh, MdocCircuitStatement, MdocPidRequest,
        MdocRevocationKey, MdocRevocationPublicInputs, MdocRevocationRangeWitness,
        MdocRevocationSignature,
    };
    use eu_id_prover::ts13::ts13_mso_derived_revocation_id;
    use eu_id_prover::{Date, Policy};

    const REVOCATION_BOUND_OFFSET: u64 = 0x1122_3344_5566_7788;
    const REVOCATION_EPOCH: u32 = 7;

    // Fixture construction and mdoc extraction are intentionally outside the
    // measurement window, matching the canonical host performance probe.
    let session_transcript = openid4vp_session_transcript(b"firebase-full-pq-benchmark");
    let fixture = mldsa_fixture::mldsa_full_pq_fixture_with_transcript(&session_transcript);
    let request = MdocPidRequest::eudi_pid(session_transcript)
        .with_trusted_mldsa_issuer_public_keys(vec![fixture.issuer_pk]);
    let extracted = match extract_pid_mdoc(&fixture.document, &request) {
        Ok(extracted) => extracted,
        Err(error) => {
            eprintln!("full-PQ fixture extraction failed: {error:?}");
            return EuIdFullPqBench::failed(threading);
        }
    };
    let policy = Policy {
        current_date: Date {
            year: 2026,
            month: 7,
            day: 3,
        },
        min_age_years: 18,
        accepted_nationalities: vec![276, 250],
        accepted_nationalities_alpha2: vec![*b"DE", *b"FR"],
    };
    let statement = match MdocCircuitStatement::from_extracted(&extracted, policy) {
        Ok(statement) => statement,
        Err(error) => {
            eprintln!("full-PQ statement construction failed: {error:?}");
            return EuIdFullPqBench::failed(threading);
        }
    };
    let revocation_id = ts13_mso_derived_revocation_id(&extracted.mso);
    let Some(revocation_id_lo) = revocation_id.checked_sub(REVOCATION_BOUND_OFFSET) else {
        return EuIdFullPqBench::failed(threading);
    };
    let Some(revocation_id_hi) = revocation_id.checked_add(REVOCATION_BOUND_OFFSET) else {
        return EuIdFullPqBench::failed(threading);
    };
    let (revocation_public_key, revocation_signature) = mldsa_fixture::mldsa_revocation_fixture(
        revocation_id_lo,
        revocation_id_hi,
        REVOCATION_EPOCH,
    );
    let statement = statement
        .with_ts13_revocation(MdocRevocationPublicInputs {
            revocation_public_key: MdocRevocationKey::MlDsa(revocation_public_key),
            epoch: REVOCATION_EPOCH,
        })
        .with_ts13_revocation_range(MdocRevocationRangeWitness {
            id: revocation_id,
            id_lo: revocation_id_lo,
            id_hi: revocation_id_hi,
        })
        .with_ts13_revocation_signature(MdocRevocationSignature::MlDsa(revocation_signature));
    let verifier_statement = match bincode::serialize(&statement)
        .ok()
        .and_then(|bytes| bincode::deserialize::<MdocCircuitStatement>(&bytes).ok())
    {
        Some(statement) if statement.ts13_revocation_range.is_none() => statement,
        _ => {
            eprintln!("full-PQ public verifier statement round-trip failed");
            return EuIdFullPqBench::failed(threading);
        }
    };

    let (measurement, peak_bytes) = with_peak_sampler(|| {
        let cpu_started = process_cpu_time();
        let prove_started = Instant::now();
        let proof = prove_mdoc_circuit(&extracted, &statement)
            .map_err(|error| format!("full-PQ prove failed: {error:?}"))?;
        let prove_ms = prove_started.elapsed().as_millis() as u64;
        let process_cpu_ms = process_cpu_time().saturating_sub(cpu_started).as_millis() as u64;
        let cold = verify_mdoc_circuit_with_pcs_config_profiled_fresh(
            &proof,
            &verifier_statement,
            mdoc_production_pcs_config(),
        )
        .map_err(|error| format!("full-PQ cold verify failed: {error:?}"))?;
        let warm = verify_mdoc_circuit_with_pcs_config_profiled(
            &proof,
            &verifier_statement,
            mdoc_production_pcs_config(),
        )
        .map_err(|error| format!("full-PQ warm verify failed: {error:?}"))?;
        Ok::<_, String>((proof, prove_ms, process_cpu_ms, cold, warm))
    });
    let (proof, prove_ms, process_cpu_ms, cold, warm) = match measurement {
        Ok(measurement) => measurement,
        Err(error) => {
            eprintln!("{error}");
            return EuIdFullPqBench::failed(threading);
        }
    };
    if cold.tree0_cache_hit || !warm.tree0_cache_hit {
        eprintln!(
            "full-PQ verifier cache contract failed: cold_hit={}, warm_hit={}",
            cold.tree0_cache_hit, warm.tree0_cache_hit
        );
        return EuIdFullPqBench::failed(threading);
    }
    let proof_bytes = match bincode::serialize(&proof) {
        Ok(bytes) => bytes.len() as u64,
        Err(error) => {
            eprintln!("full-PQ proof serialization failed: {error}");
            return EuIdFullPqBench::failed(threading);
        }
    };

    EuIdFullPqBench {
        prove_ms,
        process_cpu_ms,
        cold_verify_ms: cold.total.as_millis() as u64,
        cold_tree0_root_ms: cold.tree0_canonical_root.as_millis() as u64,
        cold_stark_verify_ms: cold.stark_verify.as_millis() as u64,
        warm_verify_ms: warm.total.as_millis() as u64,
        warm_tree0_root_ms: warm.tree0_canonical_root.as_millis() as u64,
        warm_stark_verify_ms: warm.stark_verify.as_millis() as u64,
        peak_bytes,
        proof_bytes,
        rayon_threads: threading.rayon_threads,
        worker_cpu_mask: threading.worker_cpu_mask,
        excluded_cpu_mask: threading.excluded_cpu_mask,
        core_metric: threading.core_metric,
        ok: 1,
    }
}

#[cfg(target_os = "android")]
fn process_cpu_time() -> Duration {
    let mut time = unsafe { std::mem::zeroed::<libc::timespec>() };
    // SAFETY: `time` points to a writable timespec for this process clock.
    if unsafe { libc::clock_gettime(libc::CLOCK_PROCESS_CPUTIME_ID, &mut time) } != 0 {
        return Duration::ZERO;
    }
    Duration::new(time.tv_sec as u64, time.tv_nsec as u32)
}

#[cfg(not(target_os = "android"))]
fn process_cpu_time() -> Duration {
    Duration::ZERO
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

    #[cfg(feature = "jni")]
    #[test]
    #[ignore = "slow: full ML-DSA issuer+device+revocation proof; run in release mode"]
    fn full_pq_bench_round_trips() {
        let result = eu_id_bench_full_pq(true);
        assert_eq!(result.ok, 1);
        assert_eq!(
            result.rayon_threads,
            std::thread::available_parallelism()
                .map(std::num::NonZeroUsize::get)
                .unwrap_or(1) as u32
        );
        assert_ne!(result.worker_cpu_mask, 0);
        assert_eq!(result.excluded_cpu_mask, 0);
        assert_eq!(result.core_metric, CORE_METRIC_HOST_AVAILABLE);
        assert!(result.prove_ms > 0);
        assert!(result.cold_verify_ms > 0);
        assert!(result.warm_verify_ms > 0);
        assert!(result.proof_bytes > 0);
        assert!(result.peak_bytes > 0);
    }

    #[cfg(feature = "jni")]
    #[test]
    fn runtime_policy_selects_single_prime_or_all_performance_cores() {
        let metrics = [(0, 512), (1, 512), (2, 768), (3, 768), (4, 1024)];
        assert_eq!(select_performance_core_ids(&metrics), Some(vec![2, 3, 4]));
        assert_eq!(select_worker_cpu_ids(&metrics, false), Some(vec![4]));
        assert_eq!(select_worker_cpu_ids(&metrics, true), Some(vec![2, 3, 4]));
        assert_eq!(select_performance_core_ids(&[(0, 1024), (1, 1024)]), None);
        assert_eq!(select_worker_cpu_ids(&[(0, 1024), (1, 1024)], false), None);
        assert_eq!(select_performance_core_ids(&[]), None);
    }
}
