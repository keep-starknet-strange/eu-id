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
//!
//! ## Proof-size byte-breakdown baseline
//!
//! A separate `BENCH_BREAKDOWN` mode decomposes the combined proof into its
//! serialized `CommitmentSchemeProof` fields, attributes the width-linear streams
//! (`queried_values` + OODS) to modules by committed-column count, and records the
//! real over-the-wire (zstd) transport size. It writes its own results file so
//! the size baseline stays independent of the (run-to-run noisy) timing/memory
//! stages above. Proof size is timing- and threading-independent, so it proves the
//! pipeline once with no memory sampling.
//!
//! ```bash
//! BENCH_BREAKDOWN=1 BENCH_LABEL=m4max cargo run --release -p eu-id-prover \
//!     --example bench_report -- docs/benchmarks/proof-size-breakdown.json
//! ```

use std::hint::black_box;
use std::process::Command;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

use eu_id_prover::generator::PipelineWitness;
use eu_id_prover::{
    fixtures, prove_identity, prove_with_column_breakdown, verify_identity, IssuerKey,
    ModuleColumns, Proof, PublicStatement,
};
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

/// The proof-size baseline, written to its own results file by the
/// `BENCH_BREAKDOWN` mode so it stays independent of the timing/memory stage
/// baseline (which is run-to-run noisy and narrated separately).
#[derive(Serialize)]
struct BreakdownReport {
    /// Free-form machine label (`BENCH_LABEL` env).
    label: String,
    /// Fixture credential the proof is produced from.
    fixture: String,
    /// Where the ~7.3 MiB combined proof's bytes live.
    byte_breakdown: ByteBreakdown,
}

/// Per-field bincode byte sizes of the combined `stark_proof`'s inner
/// `CommitmentSchemeProof`, the per-module attribution of the width-linear
/// streams, and the real over-the-wire (zstd) transport size. The
/// size-reduction baseline — every later task is measured against this.
#[derive(Serialize)]
struct ByteBreakdown {
    /// `bincode::serialize(&Proof)` length — the whole proof, the figure the SDK
    /// compresses for transport (includes the small per-module claim metadata
    /// alongside the inner STARK proof).
    proof_bincode_bytes: u64,
    /// `bincode::serialize(&Proof.stark_proof)` length — just the inner STARK
    /// proof, the sum of the per-field sizes below.
    stark_proof_bincode_bytes: u64,
    /// Per-`CommitmentSchemeProof`-field bincode sizes.
    fields: FieldSizes,
    /// Committed columns per commitment tree (0=preprocessed, 1=trace,
    /// 2=interaction, 3+=composition / quotient).
    tree_columns: Vec<usize>,
    /// Per-module attribution of the width-linear streams (`queried_values` +
    /// OODS `sampled_values`) by committed-column count.
    modules: Vec<ModuleAttribution>,
    /// The width-linear bytes living in the shared composition / quotient tree
    /// (tree 3+), not attributable to a single module.
    composition_width_bytes: u64,
    /// zstd-12 of `proof_bincode_bytes` — the real Bluetooth payload (matches
    /// the SDK's `compress_stark_proof_for_ffi`).
    ffi_compressed_bytes: u64,
    /// `proof_bincode_bytes / ffi_compressed_bytes`.
    compression_ratio: f64,
}

/// Bincode size of each `CommitmentSchemeProof` field, in bytes.
#[derive(Serialize)]
struct FieldSizes {
    /// `config` (the `PcsConfig`) — a handful of bytes.
    config: u64,
    /// `commitments` — the per-tree Merkle roots (one hash each).
    commitments: u64,
    /// `sampled_values` — the OODS mask evaluations (`SecureField`, width-linear).
    sampled_values: u64,
    /// `decommitments` — the Merkle auth-path hash witnesses (depth-driven).
    decommitments: u64,
    /// `queried_values` — the opened column values (`BaseField`, width × queries).
    queried_values: u64,
    /// `proof_of_work` — one `u64` grinding nonce.
    proof_of_work: u64,
    /// `fri_proof` — the FRI layer commitments + witnesses (depth-driven).
    fri_proof: u64,
}

/// One module's committed-column counts and its attributed share of the
/// width-linear proof bytes.
#[derive(Serialize)]
struct ModuleAttribution {
    name: String,
    preprocessed_cols: usize,
    trace_cols: usize,
    interaction_cols: usize,
    total_cols: usize,
    /// Attributed `queried_values` bytes (by column share, per tree).
    queried_bytes: u64,
    /// Attributed OODS `sampled_values` bytes (by column share, per tree).
    oods_bytes: u64,
    /// `queried_bytes + oods_bytes` — the module's width-linear footprint.
    width_bytes: u64,
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

    // Breakdown mode: decompose the combined proof's bytes and write the
    // size baseline to its own results file, independent of the timing stages.
    if std::env::var("BENCH_BREAKDOWN").is_ok() {
        run_breakdown();
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

/// Breakdown mode: prove the combined pipeline once, decompose its serialized
/// bytes, print the human table, and write the machine-readable size
/// baseline to the optional output path. No stage children, no memory sampling —
/// proof size is timing- and threading-independent.
fn run_breakdown() {
    let out_path = std::env::args().nth(1);
    let label = std::env::var("BENCH_LABEL").unwrap_or_else(|_| "laptop".to_string());

    let byte_breakdown = report_byte_breakdown();
    let report = BreakdownReport {
        label,
        fixture: "valid_over_18".to_string(),
        byte_breakdown,
    };

    let json = serde_json::to_string_pretty(&report).expect("serialize breakdown report");
    if let Some(path) = out_path {
        match std::fs::write(&path, format!("{json}\n")) {
            Ok(()) => println!("\nwrote proof-size breakdown to {path}"),
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
    let nonce_instances = stages::pipeline_nonce_instances(&proof);
    let verify_ms = median(timed(iters, || {
        stages::verify_pipeline(&proof, &instances, &nonce_instances)
    }));
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
    let nonce = fixtures::demo_nonce_statement();
    let statement = PublicStatement::new(issuer.public_key(), policy.clone(), nonce.clone());

    let (prove_ms, peak) = isolated_prove(iters, || {
        black_box(prove_identity(&credential, &issuer, &policy, &nonce).expect("e2e proves"));
    });
    let proof = prove_identity(&credential, &issuer, &policy, &nonce).expect("e2e proves");
    let proof_bytes = bincode::serialize(&proof).map(|b| b.len()).unwrap_or(0);
    let verify_ms = median(timed(iters, || {
        verify_identity(&proof, &statement).expect("e2e verifies");
    }));
    result("pipeline_e2e", prove_ms, verify_ms, peak, proof_bytes)
}

// ---- Proof byte-breakdown (size baseline) ----------------------------------
//
// Decompose the combined proof into its serialized parts and attribute the
// width-linear streams (`queried_values`, OODS) to modules by committed-column
// count, so the size-reduction tasks are prioritised against real numbers. Size
// is timing- and threading-independent, so this runs once in the parent.

fn bincode_len<T: serde::Serialize>(v: &T) -> u64 {
    bincode::serialized_size(v).expect("bincode serialized_size")
}

/// zstd-12 of `raw` — mirrors the SDK's `compress_stark_proof_for_ffi`, so the
/// recorded over-the-wire size and ratio match the real Bluetooth payload.
fn zstd_wire(raw: &[u8]) -> Vec<u8> {
    zstd::bulk::compress(raw, 12).expect("zstd compress")
}

/// A module's committed-column count in commitment tree `tree`
/// (0=preprocessed, 1=trace, 2=interaction; composition trees have none).
fn module_cols_in_tree(m: &ModuleColumns, tree: usize) -> usize {
    match tree {
        0 => m.preprocessed,
        1 => m.trace,
        2 => m.interaction,
        _ => 0,
    }
}

/// Prove the combined pipeline once and decompose its serialized bytes. The
/// width-linear streams (`queried_values` + OODS) are attributed per module by
/// committed-column share within each tree; the depth-driven streams
/// (`decommitments`, `fri_proof`) are governed by the tallest column (P256's
/// `log_size`) and reported as shared fields.
fn report_byte_breakdown() -> ByteBreakdown {
    let fixture = fixtures::valid_over_18();
    let witness = fixture.pipeline_witness();
    let draft = witness
        .p256_draft
        .as_ref()
        .expect("honest fixture carries a valid P256 draft");
    let nonce_draft =
        stwo_p256::proof::P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![
            fixtures::demo_nonce_statement().ecdsa_input(),
        ])
        .expect("demo nonce builds a proof draft");
    let (proof, cols): (Proof, Vec<ModuleColumns>) = prove_with_column_breakdown(
        draft,
        &nonce_draft,
        &witness.sha_witness,
        witness.sha_log_n_rows,
        witness.sha_group_width,
        &witness.age_public,
        &witness.age_dob,
        &witness.nat_public,
        &witness.nat_private,
    )
    .expect("breakdown pipeline proves");

    let csp = &proof.stark_proof; // derefs to CommitmentSchemeProof
    let fields = FieldSizes {
        config: bincode_len(&csp.config),
        commitments: bincode_len(&csp.commitments),
        sampled_values: bincode_len(&csp.sampled_values),
        decommitments: bincode_len(&csp.decommitments),
        queried_values: bincode_len(&csp.queried_values),
        proof_of_work: bincode_len(&csp.proof_of_work),
        fri_proof: bincode_len(&csp.fri_proof),
    };

    // Per-tree column counts and serialized bytes for the two width-linear
    // streams. The combined proof's column counts must equal the sum of the
    // per-module layout counts (the verifier commits against the same sizes) —
    // assert it so a layout drift is caught here, not silently mis-attributed.
    let n_trees = csp.queried_values.len();
    let tree_columns: Vec<usize> = (0..n_trees).map(|t| csp.queried_values[t].len()).collect();
    for (t, &n_cols) in tree_columns.iter().enumerate().take(3) {
        let module_sum: usize = cols.iter().map(|m| module_cols_in_tree(m, t)).sum();
        assert_eq!(
            module_sum, n_cols,
            "tree {t}: module column sum {module_sum} != committed column count {n_cols}"
        );
    }

    // Attribute each width-linear stream to modules by per-tree column share.
    let mut queried_by_module = vec![0u64; cols.len()];
    let mut oods_by_module = vec![0u64; cols.len()];
    for t in 0..n_trees {
        let q_cols = csp.queried_values[t].len();
        let s_cols = csp.sampled_values[t].len();
        let q_bytes = bincode_len(&csp.queried_values[t]);
        let s_bytes = bincode_len(&csp.sampled_values[t]);
        for (i, m) in cols.iter().enumerate() {
            let mc = module_cols_in_tree(m, t);
            if mc == 0 {
                continue;
            }
            if q_cols > 0 {
                queried_by_module[i] += q_bytes * mc as u64 / q_cols as u64;
            }
            if s_cols > 0 {
                oods_by_module[i] += s_bytes * mc as u64 / s_cols as u64;
            }
        }
    }

    let modules: Vec<ModuleAttribution> = cols
        .iter()
        .enumerate()
        .map(|(i, m)| ModuleAttribution {
            name: m.name.to_string(),
            preprocessed_cols: m.preprocessed,
            trace_cols: m.trace,
            interaction_cols: m.interaction,
            total_cols: m.total(),
            queried_bytes: queried_by_module[i],
            oods_bytes: oods_by_module[i],
            width_bytes: queried_by_module[i] + oods_by_module[i],
        })
        .collect();

    // Whatever width-linear bytes the modules do not account for live in the
    // shared composition / quotient tree (tree 3+) plus per-tree rounding.
    let total_width = fields.queried_values + fields.sampled_values;
    let attributed_width: u64 = modules.iter().map(|m| m.width_bytes).sum();
    let composition_width_bytes = total_width.saturating_sub(attributed_width);

    let proof_bincode = bincode::serialize(&proof).expect("serialize proof");
    let proof_bincode_bytes = proof_bincode.len() as u64;
    let stark_proof_bincode_bytes = bincode_len(&proof.stark_proof);
    let ffi_compressed_bytes = zstd_wire(&proof_bincode).len() as u64;
    let compression_ratio = if ffi_compressed_bytes == 0 {
        0.0
    } else {
        proof_bincode_bytes as f64 / ffi_compressed_bytes as f64
    };

    let breakdown = ByteBreakdown {
        proof_bincode_bytes,
        stark_proof_bincode_bytes,
        fields,
        tree_columns,
        modules,
        composition_width_bytes,
        ffi_compressed_bytes,
        compression_ratio,
    };
    print_byte_breakdown(&breakdown);
    breakdown
}

fn print_byte_breakdown(b: &ByteBreakdown) {
    let kib = |n: u64| n as f64 / 1024.0;
    let pct = |n: u64| 100.0 * n as f64 / b.stark_proof_bincode_bytes as f64;

    println!("\n===== proof byte-breakdown (size baseline) =====");
    println!(
        "whole Proof bincode: {:.1} KiB  |  over-the-wire (zstd-12): {:.1} KiB  ({:.2}× ratio)",
        kib(b.proof_bincode_bytes),
        kib(b.ffi_compressed_bytes),
        b.compression_ratio,
    );
    println!(
        "inner stark_proof bincode: {:.1} KiB (field sizes below sum to this)",
        kib(b.stark_proof_bincode_bytes),
    );

    println!("\n{:<16} {:>12} {:>8}", "field", "KiB", "%");
    let f = &b.fields;
    for (name, bytes) in [
        ("queried_values", f.queried_values),
        ("sampled_values", f.sampled_values),
        ("decommitments", f.decommitments),
        ("fri_proof", f.fri_proof),
        ("commitments", f.commitments),
        ("proof_of_work", f.proof_of_work),
        ("config", f.config),
    ] {
        println!("{name:<16} {:>12.1} {:>7.1}%", kib(bytes), pct(bytes));
    }

    println!(
        "\ncommitted columns per tree (0=preproc,1=trace,2=interaction,3=composition): {:?}",
        b.tree_columns,
    );
    println!("\nper-module width-linear (queried_values + OODS), attributed by column count:");
    println!(
        "{:<8} {:>9} {:>9} {:>11} {:>11} {:>8}",
        "module", "cols", "queried", "oods", "width", "%width"
    );
    let total_width = f.queried_values + f.sampled_values;
    let wpct = |n: u64| {
        if total_width == 0 {
            0.0
        } else {
            100.0 * n as f64 / total_width as f64
        }
    };
    for m in &b.modules {
        println!(
            "{:<8} {:>9} {:>8.1}K {:>10.1}K {:>10.1}K {:>7.1}%",
            m.name,
            m.total_cols,
            kib(m.queried_bytes),
            kib(m.oods_bytes),
            kib(m.width_bytes),
            wpct(m.width_bytes),
        );
    }
    println!(
        "{:<8} {:>9} {:>8} {:>11} {:>10.1}K {:>7.1}%",
        "composit",
        "—",
        "—",
        "—",
        kib(b.composition_width_bytes),
        wpct(b.composition_width_bytes),
    );
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
