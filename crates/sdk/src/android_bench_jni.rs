use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, OnceLock};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use jni::objects::JClass;
use jni::sys::{jboolean, jstring};
use jni::JNIEnv;

use crate::{prove_identity, verify_identity, PredicateMode, ZkMdocWitness, ZkPublicStatement};

const CORE_METRIC_HOST_AVAILABLE: u32 = 0;
const PRODUCT_STATEMENT: &str = "sdk_identity_product";
#[cfg(target_os = "android")]
const CORE_METRIC_CPU_CAPACITY: u32 = 1;
#[cfg(target_os = "android")]
const CORE_METRIC_CPUINFO_MAX_FREQ: u32 = 2;

type CpuMetric = (usize, u64);

#[derive(Clone)]
struct CpuTopology {
    performance: Vec<CpuMetric>,
    efficiency_cpu_ids: Vec<usize>,
    metrics: Vec<CpuMetric>,
    metric: u32,
}

#[cfg(any(test, target_os = "android"))]
type CpuClusterSplit = (Vec<CpuMetric>, Vec<usize>);

#[derive(Default)]
struct CpuFrequencySnapshot {
    scaling_max_khz: Vec<CpuMetric>,
    scaling_cur_khz: Vec<CpuMetric>,
}

#[derive(Clone)]
struct BenchmarkThreading {
    all_performance_cores: bool,
    worker_cpu_ids: Vec<usize>,
    performance_cpu_ids: Vec<usize>,
    efficiency_cpu_ids: Vec<usize>,
    cpu_metric_values: Vec<CpuMetric>,
    core_metric: u32,
}

struct IdentityBenchResult {
    prove_ms: u64,
    process_cpu_ms: u64,
    verify_ms: u64,
    peak_bytes: u64,
    proof_bytes: u64,
    frequency_before: CpuFrequencySnapshot,
    frequency_after: CpuFrequencySnapshot,
    threading: BenchmarkThreading,
    ok: bool,
}

fn core_metric_name(metric: u32) -> &'static str {
    match metric {
        CORE_METRIC_HOST_AVAILABLE => "host_available_parallelism",
        1 => "cpu_capacity",
        2 => "cpuinfo_max_freq",
        _ => "unknown",
    }
}

fn cpu_ids_json(cpu_ids: &[usize]) -> String {
    format!(
        "[{}]",
        cpu_ids
            .iter()
            .map(usize::to_string)
            .collect::<Vec<_>>()
            .join(",")
    )
}

fn cpu_metrics_json(metrics: &[(usize, u64)]) -> String {
    format!(
        "[{}]",
        metrics
            .iter()
            .map(|(cpu_id, value)| format!("[{cpu_id},{value}]"))
            .collect::<Vec<_>>()
            .join(",")
    )
}

fn frequency_snapshot_json(snapshot: &CpuFrequencySnapshot) -> String {
    let scaling_max_khz = cpu_metrics_json(&snapshot.scaling_max_khz);
    let scaling_cur_khz = cpu_metrics_json(&snapshot.scaling_cur_khz);
    format!(r#"{{"scaling_max_khz":{scaling_max_khz},"scaling_cur_khz":{scaling_cur_khz}}}"#)
}

fn build_metadata() -> (&'static str, &'static str, &'static str, &'static str) {
    (
        option_env!("EUID_BENCH_BUILD_ID").unwrap_or("untracked"),
        option_env!("EUID_BENCH_LIBRARY_SLOT").unwrap_or("untracked"),
        option_env!("EUID_BENCH_CARGO_PROFILE").unwrap_or("untracked"),
        option_env!("EUID_BENCH_LTO").unwrap_or("untracked"),
    )
}

fn failed_json() -> String {
    let (build_id, library_slot, cargo_profile, lto) = build_metadata();
    format!(
        r#"{{"statement":"{PRODUCT_STATEMENT}","build_id":"{build_id}","library_slot":"{library_slot}","cargo_profile":"{cargo_profile}","lto":"{lto}","prove_ms":0,"process_cpu_ms":0,"verify_ms":0,"peak_bytes":0,"proof_bytes":0,"rayon_threads":0,"worker_cpu_ids":[],"performance_cpu_ids":[],"efficiency_cpu_ids":[],"cpu_metric_values":[],"frequency_before":{{"scaling_max_khz":[],"scaling_cur_khz":[]}},"frequency_after":{{"scaling_max_khz":[],"scaling_cur_khz":[]}},"core_metric":"unknown","ok":false}}"#
    )
}

fn result_json(result: IdentityBenchResult) -> String {
    let worker_cpu_ids = cpu_ids_json(&result.threading.worker_cpu_ids);
    let performance_cpu_ids = cpu_ids_json(&result.threading.performance_cpu_ids);
    let efficiency_cpu_ids = cpu_ids_json(&result.threading.efficiency_cpu_ids);
    let cpu_metric_values = cpu_metrics_json(&result.threading.cpu_metric_values);
    let frequency_before = frequency_snapshot_json(&result.frequency_before);
    let frequency_after = frequency_snapshot_json(&result.frequency_after);
    let core_metric = core_metric_name(result.threading.core_metric);
    let statement = PRODUCT_STATEMENT;
    let (build_id, library_slot, cargo_profile, lto) = build_metadata();
    let rayon_threads = result.threading.worker_cpu_ids.len();
    let IdentityBenchResult {
        prove_ms,
        process_cpu_ms,
        verify_ms,
        peak_bytes,
        proof_bytes,
        ok,
        ..
    } = result;
    format!(
        r#"{{"statement":"{statement}","build_id":"{build_id}","library_slot":"{library_slot}","cargo_profile":"{cargo_profile}","lto":"{lto}","prove_ms":{prove_ms},"process_cpu_ms":{process_cpu_ms},"verify_ms":{verify_ms},"peak_bytes":{peak_bytes},"proof_bytes":{proof_bytes},"rayon_threads":{rayon_threads},"worker_cpu_ids":{worker_cpu_ids},"performance_cpu_ids":{performance_cpu_ids},"efficiency_cpu_ids":{efficiency_cpu_ids},"cpu_metric_values":{cpu_metric_values},"frequency_before":{frequency_before},"frequency_after":{frequency_after},"core_metric":"{core_metric}","ok":{ok}}}"#
    )
}

fn benchmark_fixture() -> (ZkPublicStatement, ZkMdocWitness) {
    let fixture = eu_id_prover::mdoc::demo_mdoc_circuit_fixture();
    let issuer_key = fixture.statement.issuer_input.public_key.clone();
    let (revocation, revocation_witness) =
        eu_id_prover::ts13::demo_ts13_revocation_inputs(&fixture.extracted.mso);
    let mut accepted_alpha2_countries = fixture
        .statement
        .policy
        .accepted_nationalities
        .iter()
        .map(|country| String::from_utf8(country.to_vec()).expect("fixture alpha-2 is ASCII"))
        .collect::<Vec<_>>();
    accepted_alpha2_countries.sort_unstable();
    accepted_alpha2_countries.dedup();
    (
        ZkPublicStatement {
            spec_id: "stwo-euid-pid-v1".to_string(),
            version: 2,
            profile_id: crate::product_profile_id(),
            circuit_hash: crate::product_circuit_hash(),
            root_policy_hash: crate::product_root_policy_hash(),
            doctype: fixture.request.doctype,
            namespace: fixture.request.namespace,
            issuer_public_key_x: issuer_key.x.0.to_vec(),
            issuer_public_key_y: issuer_key.y.0.to_vec(),
            now_epoch_seconds: 20_637 * 86_400 + 43_200,
            session_transcript: fixture.request.session_transcript,
            predicate_mode: PredicateMode::And,
            age_threshold_years: Some(fixture.statement.policy.min_age_years),
            accepted_alpha2_countries: Some(accepted_alpha2_countries),
            revocation_public_key_x: revocation.revocation_public_key.x.0.to_vec(),
            revocation_public_key_y: revocation.revocation_public_key.y.0.to_vec(),
            revocation_epoch: revocation.epoch,
        },
        ZkMdocWitness {
            document: fixture.document,
            revocation_id_lo: revocation_witness.id_lo,
            revocation_id_hi: revocation_witness.id_hi,
            revocation_signature_r: revocation_witness.signature.r.0.to_vec(),
            revocation_signature_s: revocation_witness.signature.s.0.to_vec(),
        },
    )
}

fn run_identity_benchmark(threading: BenchmarkThreading) -> IdentityBenchResult {
    let (statement, witness) = benchmark_fixture();
    let (prove_statement, verify_statement) = (statement.clone(), statement);
    let monitored_cpu_ids = threading.performance_cpu_ids.clone();
    let (
        (prove_ms, process_cpu_ms, verify_ms, proof_bytes, frequency_before, frequency_after, ok),
        peak_bytes,
    ) = with_peak_sampler(|| {
        let frequency_before = cpu_frequency_snapshot(&monitored_cpu_ids);
        let cpu_started = process_cpu_time();
        let started = Instant::now();
        let proof = match prove_identity(prove_statement, witness) {
            Ok(proof) => proof,
            Err(error) => {
                eprintln!("SDK proveIdentity benchmark failed: {error}");
                return (
                    0,
                    0,
                    0,
                    0,
                    frequency_before,
                    CpuFrequencySnapshot::default(),
                    false,
                );
            }
        };
        let prove_ms = started.elapsed().as_millis() as u64;
        let process_cpu_ms = process_cpu_time().saturating_sub(cpu_started).as_millis() as u64;
        let frequency_after = cpu_frequency_snapshot(&monitored_cpu_ids);
        let proof_bytes = proof.len() as u64;

        let started = Instant::now();
        let ok = match verify_identity(verify_statement, proof) {
            Ok(result) => result.ok,
            Err(error) => {
                eprintln!("SDK verifyIdentity benchmark failed: {error}");
                false
            }
        };
        (
            prove_ms,
            process_cpu_ms,
            started.elapsed().as_millis() as u64,
            proof_bytes,
            frequency_before,
            frequency_after,
            ok,
        )
    });

    IdentityBenchResult {
        prove_ms,
        process_cpu_ms,
        verify_ms,
        peak_bytes,
        proof_bytes,
        frequency_before,
        frequency_after,
        threading,
        ok,
    }
}

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
                if let Some(stats) = memory_stats::memory_stats() {
                    sampler_peak.fetch_max(stats.physical_mem as u64, Ordering::Relaxed);
                }
                thread::sleep(Duration::from_millis(10));
            }
            if let Some(stats) = memory_stats::memory_stats() {
                sampler_peak.fetch_max(stats.physical_mem as u64, Ordering::Relaxed);
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

static THREADING: OnceLock<Result<BenchmarkThreading, String>> = OnceLock::new();

fn configure_threading(all_performance_cores: bool) -> Result<BenchmarkThreading, String> {
    let configured = THREADING.get_or_init(|| initialize_threading(all_performance_cores));
    match configured {
        Ok(threading) if threading.all_performance_cores == all_performance_cores => {
            pin_current_thread(&threading.worker_cpu_ids)?;
            Ok(threading.clone())
        }
        Ok(_) => Err("Rayon was already configured with a different benchmark policy".to_string()),
        Err(error) => Err(error.clone()),
    }
}

fn initialize_threading(all_performance_cores: bool) -> Result<BenchmarkThreading, String> {
    let topology = benchmark_topology()?;
    let performance_cpu_ids = topology
        .performance
        .iter()
        .map(|(cpu_id, _)| *cpu_id)
        .collect::<Vec<_>>();
    let worker_cpu_ids = if all_performance_cores {
        performance_cpu_ids.clone()
    } else {
        vec![topology
            .performance
            .iter()
            .max_by_key(|(_, value)| *value)
            .map(|(cpu_id, _)| *cpu_id)
            .ok_or_else(|| "no performance CPU selected".to_string())?]
    };
    build_global_pool(&worker_cpu_ids)?;
    let rayon_threads = rayon::current_num_threads();
    if rayon_threads != worker_cpu_ids.len() {
        return Err(format!(
            "requested {} Rayon workers, got {rayon_threads}",
            worker_cpu_ids.len()
        ));
    }

    Ok(BenchmarkThreading {
        all_performance_cores,
        worker_cpu_ids,
        performance_cpu_ids,
        efficiency_cpu_ids: topology.efficiency_cpu_ids,
        cpu_metric_values: topology.metrics,
        core_metric: topology.metric,
    })
}

#[cfg(not(target_os = "android"))]
fn benchmark_topology() -> Result<CpuTopology, String> {
    let count = std::thread::available_parallelism()
        .map(std::num::NonZeroUsize::get)
        .unwrap_or(1);
    Ok(CpuTopology {
        performance: (0..count).map(|cpu_id| (cpu_id, 1)).collect(),
        efficiency_cpu_ids: Vec::new(),
        metrics: (0..count).map(|cpu_id| (cpu_id, 1)).collect(),
        metric: CORE_METRIC_HOST_AVAILABLE,
    })
}

#[cfg(target_os = "android")]
fn benchmark_topology() -> Result<CpuTopology, String> {
    let allowed = android_allowed_cpu_ids()?;
    for (metric, suffix) in [
        (CORE_METRIC_CPU_CAPACITY, "cpu_capacity"),
        (CORE_METRIC_CPUINFO_MAX_FREQ, "cpufreq/cpuinfo_max_freq"),
    ] {
        if let Some(values) = android_cpu_metric(&allowed, suffix) {
            if let Some((performance, efficiency_cpu_ids)) = split_cpu_clusters(&values) {
                return Ok(CpuTopology {
                    performance,
                    efficiency_cpu_ids,
                    metrics: values,
                    metric,
                });
            }
        }
    }
    Err("neither cpu_capacity nor cpuinfo_max_freq identified a heterogeneous cluster".to_string())
}

#[cfg(target_os = "android")]
fn android_allowed_cpu_ids() -> Result<Vec<usize>, String> {
    let mut mask = unsafe { std::mem::zeroed::<libc::cpu_set_t>() };
    // SAFETY: `mask` is writable for exactly the supplied cpu_set_t size.
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
    let cpu_ids = (0..libc::CPU_SETSIZE)
        // SAFETY: sched_getaffinity initialized `mask`. Indices are bounded by CPU_SETSIZE.
        .filter(|cpu_id| unsafe { libc::CPU_ISSET(*cpu_id, &mask) })
        .collect::<Vec<_>>();
    if cpu_ids.is_empty() {
        return Err("sched_getaffinity returned an empty CPU set".to_string());
    }
    Ok(cpu_ids)
}

#[cfg(target_os = "android")]
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

#[cfg(any(test, target_os = "android"))]
fn split_cpu_clusters(metrics: &[CpuMetric]) -> Option<CpuClusterSplit> {
    let minimum = metrics.iter().map(|(_, value)| *value).min()?;
    let performance = metrics
        .iter()
        .copied()
        .filter(|(_, value)| *value > minimum)
        .collect::<Vec<_>>();
    if performance.is_empty() {
        return None;
    }
    let efficiency = metrics
        .iter()
        .filter_map(|(cpu_id, value)| (*value == minimum).then_some(*cpu_id))
        .collect();
    Some((performance, efficiency))
}

#[cfg(target_os = "android")]
fn build_global_pool(cpu_ids: &[usize]) -> Result<(), String> {
    let worker_cpu_ids = Arc::new(cpu_ids.to_vec());
    rayon::ThreadPoolBuilder::new()
        .num_threads(cpu_ids.len())
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
                let pin_result = pin_current_thread(&[cpu_id]);
                let pinned = pin_result.is_ok();
                let _ = sender.send(pin_result);
                if pinned {
                    rayon_thread.run();
                }
            })?;
            match receiver.recv() {
                Ok(result) => result.map_err(std::io::Error::other),
                Err(error) => Err(std::io::Error::new(std::io::ErrorKind::BrokenPipe, error)),
            }
        })
        .build_global()
        .map_err(|error| error.to_string())
}

#[cfg(not(target_os = "android"))]
fn build_global_pool(cpu_ids: &[usize]) -> Result<(), String> {
    rayon::ThreadPoolBuilder::new()
        .num_threads(cpu_ids.len())
        .build_global()
        .map_err(|error| error.to_string())
}

#[cfg(target_os = "android")]
fn pin_current_thread(cpu_ids: &[usize]) -> Result<(), String> {
    if cpu_ids.is_empty() || cpu_ids.iter().any(|cpu_id| *cpu_id >= libc::CPU_SETSIZE) {
        return Err("invalid empty or out-of-range CPU affinity set".to_string());
    }
    let mut mask = unsafe { std::mem::zeroed::<libc::cpu_set_t>() };
    // SAFETY: `mask` is valid and every CPU index was bounded above.
    unsafe {
        libc::CPU_ZERO(&mut mask);
        for cpu_id in cpu_ids {
            libc::CPU_SET(*cpu_id, &mut mask);
        }
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
        Err(std::io::Error::last_os_error().to_string())
    }
}

#[cfg(not(target_os = "android"))]
fn pin_current_thread(_cpu_ids: &[usize]) -> Result<(), String> {
    Ok(())
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

#[cfg(target_os = "android")]
fn cpu_frequency_snapshot(cpu_ids: &[usize]) -> CpuFrequencySnapshot {
    CpuFrequencySnapshot {
        scaling_max_khz: android_cpu_metric(cpu_ids, "cpufreq/scaling_max_freq")
            .unwrap_or_default(),
        scaling_cur_khz: android_cpu_metric(cpu_ids, "cpufreq/scaling_cur_freq")
            .unwrap_or_default(),
    }
}

#[cfg(not(target_os = "android"))]
fn cpu_frequency_snapshot(_cpu_ids: &[usize]) -> CpuFrequencySnapshot {
    CpuFrequencySnapshot::default()
}

fn into_jstring(env: &JNIEnv<'_>, value: String) -> jstring {
    env.new_string(value)
        .map(|value| value.into_raw())
        .unwrap_or(std::ptr::null_mut())
}

fn catch_json(work: impl FnOnce() -> String) -> String {
    catch_unwind(AssertUnwindSafe(work)).unwrap_or_else(|_| failed_json())
}

fn jni_json(env: &JNIEnv<'_>, work: impl FnOnce() -> String) -> jstring {
    let value = catch_json(work);
    catch_unwind(AssertUnwindSafe(|| into_jstring(env, value))).unwrap_or(std::ptr::null_mut())
}

#[no_mangle]
#[allow(non_snake_case)]
pub extern "system" fn Java_eu_euid_bench_BenchRunner_identity(
    env: JNIEnv<'_>,
    _class: JClass<'_>,
    all_performance_cores: jboolean,
) -> jstring {
    jni_json(&env, || {
        let threading = match configure_threading(all_performance_cores != 0) {
            Ok(threading) => threading,
            Err(error) => {
                eprintln!("SDK identity benchmark thread setup failed: {error}");
                return failed_json();
            }
        };
        result_json(run_identity_benchmark(threading))
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cluster_split_excludes_only_the_minimum_tier() {
        let (performance, efficiency) =
            split_cpu_clusters(&[(0, 512), (1, 512), (2, 768), (3, 1024)])
                .expect("heterogeneous topology splits");
        assert_eq!(performance, vec![(2, 768), (3, 1024)]);
        assert_eq!(efficiency, vec![0, 1]);
        assert!(split_cpu_clusters(&[(0, 1024), (1, 1024)]).is_none());
    }

    #[test]
    fn result_json_records_the_exact_thread_policy() {
        let result = IdentityBenchResult {
            prove_ms: 1,
            process_cpu_ms: 2,
            verify_ms: 3,
            peak_bytes: 4,
            proof_bytes: 5,
            frequency_before: CpuFrequencySnapshot {
                scaling_max_khz: vec![(2, 2_000_000), (3, 3_000_000)],
                scaling_cur_khz: vec![(2, 1_500_000), (3, 2_500_000)],
            },
            frequency_after: CpuFrequencySnapshot {
                scaling_max_khz: vec![(2, 2_000_000), (3, 3_000_000)],
                scaling_cur_khz: vec![(2, 1_800_000), (3, 2_800_000)],
            },
            threading: BenchmarkThreading {
                all_performance_cores: true,
                worker_cpu_ids: vec![2, 3],
                performance_cpu_ids: vec![2, 3],
                efficiency_cpu_ids: vec![0, 1],
                cpu_metric_values: vec![(0, 512), (1, 512), (2, 768), (3, 1024)],
                core_metric: 1,
            },
            ok: true,
        };
        let (build_id, library_slot, cargo_profile, lto) = build_metadata();
        assert_eq!(
            result_json(result),
            format!(
                r#"{{"statement":"sdk_identity_product","build_id":"{build_id}","library_slot":"{library_slot}","cargo_profile":"{cargo_profile}","lto":"{lto}","prove_ms":1,"process_cpu_ms":2,"verify_ms":3,"peak_bytes":4,"proof_bytes":5,"rayon_threads":2,"worker_cpu_ids":[2,3],"performance_cpu_ids":[2,3],"efficiency_cpu_ids":[0,1],"cpu_metric_values":[[0,512],[1,512],[2,768],[3,1024]],"frequency_before":{{"scaling_max_khz":[[2,2000000],[3,3000000]],"scaling_cur_khz":[[2,1500000],[3,2500000]]}},"frequency_after":{{"scaling_max_khz":[[2,2000000],[3,3000000]],"scaling_cur_khz":[[2,1800000],[3,2800000]]}},"core_metric":"cpu_capacity","ok":true}}"#
            )
        );
    }

    #[test]
    fn failed_json_keeps_the_product_metadata_schema() {
        let failed = failed_json();
        assert!(failed.contains(r#""statement":"sdk_identity_product""#));
        assert!(failed.contains(r#""library_slot":""#));
        assert!(failed.ends_with(r#""ok":false}"#));
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

    #[test]
    fn wrapper_panics_become_failed_json() {
        assert_eq!(catch_json(|| panic!("injected JNI panic")), failed_json());
    }
}
