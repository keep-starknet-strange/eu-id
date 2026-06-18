//! Peak-memory + machine-readable report driver for the combined identity prover.
//!
//! Criterion (`benches/identity_bench.rs`) owns the statistically-rigorous
//! timing; this driver owns the rest of the picture — peak memory, proof size,
//! and a machine-readable JSON results file — and prints a human table. Both
//! funnel through the same per-stage proving primitives (`common/stages.rs`), so
//! they measure identical paths.
//!
//! For each standalone component (P256, SHA, age, nat) and the full combined
//! STARK (`pipeline`) it records median prove / verify wall-clock, peak
//! `phys_footprint` during proving, and serialized proof size. It also measures
//! the **end-to-end** relying-party path (`prove_identity` → `verify_identity`,
//! which additionally builds the witness + P256 draft and signs) — the figure
//! the on-device harness reproduces and the one to weigh against the iOS jetsam
//! budget. Finally it prints the headline P256-vs-combined comparison.
//!
//! ## One process per stage
//!
//! `phys_footprint` is process-global and the allocator does not return freed
//! pages to the OS, so measuring several stages in one process makes every later
//! stage inherit the earlier high-water mark (a tiny predicate would falsely
//! report gigabytes). So the driver re-executes itself **once per stage** (a
//! child sets `BENCH_STAGE`), and each child measures exactly one stage in a
//! fresh address space. Its peak is then its own. Peak memory is sampled the
//! same way as the FFI / mobile harness (a background thread polling mach
//! `phys_footprint` via the `memory-stats` crate), so laptop and device numbers
//! come from one method.
//!
//! ```bash
//! # Single-threaded (the honest baseline), write the committed laptop results:
//! BENCH_LABEL=m4max-single cargo run --release -p eu-id-prover --example bench_report \
//!     -- docs/benchmarks/laptop-m4max.json
//! # Stwo rayon paths on, to quantify the parallel delta (stdout only):
//! BENCH_LABEL=m4max-parallel cargo run --release -p eu-id-prover --example bench_report \
//!     --features parallel
//! ```

use std::hint::black_box;
use std::process::Command;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

use eu_id_prover::generator::PipelineWitness;
use eu_id_prover::{fixtures, prove_identity, verify_identity, IssuerKey, PublicStatement};
use serde::{Deserialize, Serialize};

#[path = "../benches/common/stages.rs"]
mod stages;

/// The measured stages, in cost order. `pipeline` is the combined STARK with the
/// witness pre-built; `pipeline_e2e` is the relying-party path including witness
/// + draft generation and signing.
const STAGES: [&str; 6] = ["p256", "sha", "age", "nat", "pipeline", "pipeline_e2e"];

/// One stage's measured numbers — the machine-readable result schema, sharing
/// the FFI harness's vocabulary (`prove_ms` / `verify_ms` / `peak_bytes` /
/// `proof_bytes`).
#[derive(Serialize, Deserialize, Clone)]
struct StageResult {
    stage: String,
    prove_ms: u64,
    verify_ms: u64,
    peak_bytes: u64,
    proof_bytes: u64,
}

/// The whole report — checked in as the machine-readable laptop results.
#[derive(Serialize)]
struct Report {
    /// Free-form machine label (`BENCH_LABEL` env), e.g. `m4max-single`.
    label: String,
    /// Logical cores visible to the process.
    logical_cores: usize,
    /// Whether the Stwo rayon paths are compiled in (`--features parallel`).
    threaded: bool,
    /// Iterations the medians are taken over.
    iters: u32,
    /// Fixture credential the numbers are produced from.
    fixture: String,
    /// Per-component STARK prove/verify (witnesses + draft pre-built), plus the
    /// combined STARK (`pipeline`) and the end-to-end relying-party path
    /// (`pipeline_e2e`). Each is measured in its own process.
    stages: Vec<StageResult>,
    /// Combined STARK prove time as a multiple of the standalone P256 prove time.
    pipeline_over_p256_prove: f64,
    /// P256 prove time as a fraction of the combined STARK prove time.
    p256_share_of_pipeline_prove: f64,
}

fn main() {
    let iters: u32 = std::env::var("BENCH_ITERS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(3)
        .max(1);

    // Child mode: measure exactly one stage in this fresh process, print its
    // result as one compact JSON line, exit.
    if let Ok(stage) = std::env::var("BENCH_STAGE") {
        let result = measure_one(&stage, iters);
        println!(
            "{}",
            serde_json::to_string(&result).expect("serialize stage")
        );
        return;
    }

    run_parent(iters);
}

/// Parent: spawn one child per stage (each a fresh address space, so peaks are
/// isolated), collect the results, print the table + comparison, and write the
/// machine-readable JSON.
fn run_parent(iters: u32) {
    let out_path = std::env::args().nth(1);
    let label = std::env::var("BENCH_LABEL").unwrap_or_else(|_| "laptop".to_string());
    let threaded = cfg!(feature = "parallel");
    let logical_cores = thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(0);

    println!(
        "build: {} | {logical_cores} logical cores | label={label} | iters={iters}",
        if threaded {
            "parallel (Stwo rayon)"
        } else {
            "single-threaded"
        },
    );

    let exe = std::env::current_exe().expect("current exe path");
    println!("\nmeasuring each stage in its own process (isolated peak memory)…");
    println!(
        "\n{:<13} {:>10} {:>11} {:>11} {:>12}",
        "stage", "prove_ms", "verify_ms", "peak_mib", "proof_kib"
    );

    let mut stage_results: Vec<StageResult> = Vec::with_capacity(STAGES.len());
    for stage in STAGES {
        let output = Command::new(&exe)
            .env("BENCH_STAGE", stage)
            .env("BENCH_ITERS", iters.to_string())
            .output()
            .unwrap_or_else(|e| panic!("spawn child for stage {stage}: {e}"));
        if !output.status.success() {
            panic!(
                "child for stage {stage} failed:\n{}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
        let stdout = String::from_utf8_lossy(&output.stdout);
        let line = stdout
            .lines()
            .rev()
            .find(|l| l.trim_start().starts_with('{'))
            .unwrap_or_else(|| panic!("no JSON from child for stage {stage}:\n{stdout}"));
        let result: StageResult = serde_json::from_str(line.trim())
            .unwrap_or_else(|e| panic!("parse child JSON for stage {stage}: {e}\n{line}"));
        print_row(&result);
        print_result_line(&result);
        stage_results.push(result);
    }

    // Headline comparison: how much of the combined cost is P256?
    let p256 = find(&stage_results, "p256");
    let pipeline = find(&stage_results, "pipeline");
    let pipeline_over_p256_prove = ratio(pipeline.prove_ms, p256.prove_ms);
    let p256_share_of_pipeline_prove = ratio(p256.prove_ms, pipeline.prove_ms);
    println!(
        "\ncomparison: combined STARK prove is {:.2}× the standalone P256 prove \
         (P256 is {:.0}% of it); the rest is SHA + bridge + predicates + shared FRI.",
        pipeline_over_p256_prove,
        p256_share_of_pipeline_prove * 100.0,
    );

    let report = Report {
        label,
        logical_cores,
        threaded,
        iters,
        fixture: "valid_over_18".to_string(),
        stages: stage_results,
        pipeline_over_p256_prove,
        p256_share_of_pipeline_prove,
    };

    let json = serde_json::to_string_pretty(&report).expect("serialize report");
    if let Some(path) = out_path {
        match std::fs::write(&path, format!("{json}\n")) {
            Ok(()) => println!("\nwrote machine-readable results to {path}"),
            Err(e) => eprintln!("\nfailed to write {path}: {e}"),
        }
    } else {
        println!("\n----- JSON -----\n{json}");
    }
}

/// Child: measure one named stage in this process and return its result. One
/// honest over-18 credential drives every stage; proving cost is independent of
/// the credential's values.
fn measure_one(stage: &str, iters: u32) -> StageResult {
    let fixture = fixtures::valid_over_18();
    let witness = fixture.pipeline_witness();
    match stage {
        "p256" => measure_p256(&witness, iters),
        "sha" => measure_sha(&witness, iters),
        "age" => measure_age(&witness, iters),
        "nat" => measure_nat(&witness, iters),
        "pipeline" => measure_pipeline(&witness, iters),
        "pipeline_e2e" => measure_pipeline_e2e(&fixture, iters),
        other => panic!("unknown stage {other}"),
    }
}

// ---- Per-stage measurement (each runs alone in a child process) ------------
//
// Each measure proves the stage fresh under the peak sampler, then builds one
// proof *after* the peak window for the size + verify timing.

fn measure_p256(w: &PipelineWitness, iters: u32) -> StageResult {
    let (prove_ms, peak) = isolated_prove(iters, || {
        black_box(stages::prove_p256(w));
    });
    let proof = stages::prove_p256(w);
    let instances = stages::p256_instances(&proof);
    let verify_ms = median(timed(iters, || stages::verify_p256(&proof, &instances)));
    result(
        "p256",
        prove_ms,
        verify_ms,
        peak,
        stages::p256_proof_bytes(&proof),
    )
}

fn measure_sha(w: &PipelineWitness, iters: u32) -> StageResult {
    let (prove_ms, peak) = isolated_prove(iters, || {
        black_box(stages::prove_sha(w));
    });
    let proof = stages::prove_sha(w);
    let verify_ms = median(timed(iters, || stages::verify_sha(&proof)));
    result(
        "sha",
        prove_ms,
        verify_ms,
        peak,
        stages::sha_proof_bytes(&proof),
    )
}

fn measure_age(w: &PipelineWitness, iters: u32) -> StageResult {
    let (prove_ms, peak) = isolated_prove(iters, || {
        black_box(stages::prove_age(w));
    });
    let proof = stages::prove_age(w);
    let verify_ms = median(timed(iters, || stages::verify_age(&proof)));
    result(
        "age",
        prove_ms,
        verify_ms,
        peak,
        stages::age_proof_bytes(&proof),
    )
}

fn measure_nat(w: &PipelineWitness, iters: u32) -> StageResult {
    let (prove_ms, peak) = isolated_prove(iters, || {
        black_box(stages::prove_nat(w));
    });
    let proof = stages::prove_nat(w);
    let verify_ms = median(timed(iters, || stages::verify_nat(&proof)));
    result(
        "nat",
        prove_ms,
        verify_ms,
        peak,
        stages::nat_proof_bytes(&proof),
    )
}

fn measure_pipeline(w: &PipelineWitness, iters: u32) -> StageResult {
    let (prove_ms, peak) = isolated_prove(iters, || {
        black_box(stages::prove_pipeline(w));
    });
    let proof = stages::prove_pipeline(w);
    let instances = stages::pipeline_instances(&proof);
    let verify_ms = median(timed(iters, || stages::verify_pipeline(&proof, &instances)));
    result(
        "pipeline",
        prove_ms,
        verify_ms,
        peak,
        stages::pipeline_proof_bytes(&proof),
    )
}

/// The end-to-end relying-party path: `prove_identity` (which signs and builds
/// the witness + P256 draft inside the timed region) → `verify_identity`.
fn measure_pipeline_e2e(fixture: &fixtures::Fixture, iters: u32) -> StageResult {
    let issuer = IssuerKey::demo();
    let credential = fixture.signed.credential;
    let policy = fixture.policy.clone();
    let statement = PublicStatement::new(issuer.public_key(), policy.clone());

    let (prove_ms, peak) = isolated_prove(iters, || {
        black_box(prove_identity(&credential, &issuer, &policy).expect("e2e proves"));
    });
    let proof = prove_identity(&credential, &issuer, &policy).expect("e2e proves");
    let proof_bytes = bincode::serialize(&proof).map(|b| b.len()).unwrap_or(0);
    let verify_ms = median(timed(iters, || {
        verify_identity(&proof, &statement).expect("e2e verifies");
    }));
    result("pipeline_e2e", prove_ms, verify_ms, peak, proof_bytes)
}

// ---- Measurement primitives ------------------------------------------------

/// Prove `iters` times under the peak sampler, each iteration discarding its
/// proof so nothing accumulates. Returns the median prove wall-clock (ms) and
/// the peak `phys_footprint` (bytes) over the whole loop.
fn isolated_prove(iters: u32, prove: impl Fn()) -> (u64, u64) {
    let (samples, peak) = with_peak_sampler(|| timed(iters, &prove));
    (median(samples), peak)
}

/// Run `op` `iters` times, returning per-run wall-clock in milliseconds.
fn timed(iters: u32, op: impl Fn()) -> Vec<u64> {
    (0..iters)
        .map(|_| {
            let t = Instant::now();
            op();
            t.elapsed().as_millis() as u64
        })
        .collect()
}

fn result(name: &str, prove_ms: u64, verify_ms: u64, peak: u64, proof_bytes: usize) -> StageResult {
    StageResult {
        stage: name.to_string(),
        prove_ms,
        verify_ms,
        peak_bytes: peak,
        proof_bytes: proof_bytes as u64,
    }
}

fn print_row(r: &StageResult) {
    println!(
        "{:<13} {:>10} {:>11} {:>11.0} {:>12.1}",
        r.stage,
        r.prove_ms,
        r.verify_ms,
        r.peak_bytes as f64 / (1024.0 * 1024.0),
        r.proof_bytes as f64 / 1024.0,
    );
}

/// A grep-friendly one-line summary per stage, mirroring the FFI harness's
/// `RESULT` lines so host-side capture is uniform across laptop and device.
fn print_result_line(r: &StageResult) {
    println!(
        "RESULT stage={} prove_ms={} verify_ms={} peak_mib={:.0} proof_kib={:.1}",
        r.stage,
        r.prove_ms,
        r.verify_ms,
        r.peak_bytes as f64 / (1024.0 * 1024.0),
        r.proof_bytes as f64 / 1024.0,
    );
}

fn find<'a>(results: &'a [StageResult], stage: &str) -> &'a StageResult {
    results
        .iter()
        .find(|r| r.stage == stage)
        .unwrap_or_else(|| panic!("stage {stage} measured"))
}

fn ratio(num: u64, den: u64) -> f64 {
    if den == 0 {
        0.0
    } else {
        num as f64 / den as f64
    }
}

fn median(mut samples: Vec<u64>) -> u64 {
    if samples.is_empty() {
        return 0;
    }
    samples.sort_unstable();
    samples[samples.len() / 2]
}

/// Run `work` while a background thread samples mach `phys_footprint` at a fixed
/// 10 ms cadence, returning `work`'s result alongside the peak footprint (bytes)
/// across the whole window. This is the same sampler the FFI harness uses
/// (`eu_id_ffi`'s `with_peak_sampler`), replicated here because that helper is
/// crate-private and `eu-id-prover` sits below `eu-id-ffi` in the dependency
/// graph — keeping the *method* identical is what makes laptop and device peaks
/// comparable.
fn with_peak_sampler<T>(work: impl FnOnce() -> T) -> (T, u64) {
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

/// Current process physical memory in bytes. On Apple `physical_mem` resolves to
/// mach `phys_footprint` — the figure iOS jetsam enforces.
fn phys_footprint() -> Option<u64> {
    memory_stats::memory_stats().map(|s| s.physical_mem as u64)
}
