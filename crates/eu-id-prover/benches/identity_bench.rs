//! Laptop criterion benchmark for the combined identity prover.
//!
//! Times prove and verify for each standalone component — P256 ECDSA, SHA-256,
//! the age predicate, the nationality predicate — and for the full combined
//! STARK (`pipeline`), so the per-stage breakdown and the P256-vs-combined
//! comparison fall straight out of the report. The stage definitions are shared
//! with the peak-memory + JSON report driver (`examples/bench_report.rs`) via
//! `common/stages.rs`, so both measure the identical proving paths.
//!
//! All inputs (witnesses, the P256 draft) are built once, outside the measured
//! window, so each benchmark times only the STARK prove / verify.
//!
//! ```bash
//! cargo bench -p eu-id-prover                       # single-threaded (baseline)
//! cargo bench -p eu-id-prover --features parallel   # Stwo rayon paths on
//! ```

use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};
use eu_id_prover::fixtures;

#[path = "common/stages.rs"]
mod stages;

fn bench_identity(c: &mut Criterion) {
    // One honest over-18 credential drives every stage. Proving cost is
    // independent of the credential's values, so a single fixture is enough.
    let witness = fixtures::valid_over_18().pipeline_witness();
    let stages = stages::stages(&witness);

    for stage in &stages {
        let mut group = c.benchmark_group(stage.name);

        // P256, SHA, and the full pipeline are sub-second to seconds-scale;
        // cap the sample count (and shorten warm-up for the slowest) so the
        // suite finishes in minutes rather than tens of minutes. The fast
        // predicate stages keep criterion's defaults.
        if matches!(stage.name, "p256" | "sha" | "pipeline") {
            group.sample_size(10);
            group.warm_up_time(Duration::from_millis(500));
        }

        group.bench_function("prove", |b| b.iter(|| (stage.prove)()));
        group.bench_function("verify", |b| b.iter(|| (stage.verify)()));

        // Criterion does not report proof size; surface it here so a single run
        // captures the full timing + size picture per stage.
        println!(
            "[{}] proof size: {} bytes ({:.1} KiB)",
            stage.name,
            stage.proof_bytes,
            stage.proof_bytes as f64 / 1024.0,
        );

        group.finish();
    }
}

criterion_group!(benches, bench_identity);
criterion_main!(benches);
