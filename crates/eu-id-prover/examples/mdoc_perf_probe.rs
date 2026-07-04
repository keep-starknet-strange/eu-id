//! Exact-iteration mdoc perf probe for WO-M3 A/B gates.
//!
//! Criterion owns the general laptop benchmark. This probe exists for work-order
//! gates that require a fixed small N and one machine-readable line item:
//! prove median, verify median, proof bytes, and committed shape cells.

use std::hint::black_box;
use std::time::{Duration, Instant};

use eu_id_prover::mdoc::{
    demo_mdoc_circuit_fixture, demo_mdoc_module_shapes, mdoc_proof_byte_breakdown,
    prove_mdoc_circuit, verify_mdoc_circuit, MdocProofByteBreakdown,
};
use serde::Serialize;
use stwo::core::pcs::PcsConfig;

#[derive(Serialize)]
struct Report {
    feature_mode: &'static str,
    rayon_num_threads: Option<String>,
    iters: usize,
    proof_bytes: usize,
    prove_ms_median: u128,
    verify_ms_median: u128,
    pcs_config: PcsConfig,
    shape_cells: u64,
    modules: Vec<ModuleShape>,
    byte_breakdown: MdocProofByteBreakdown,
}

#[derive(Serialize)]
struct ModuleShape {
    name: &'static str,
    cells: u64,
}

fn main() {
    let iters = std::env::var("BENCH_ITERS")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(5)
        .max(1);
    let fixture = demo_mdoc_circuit_fixture();

    let mut prove_times = Vec::with_capacity(iters);
    let mut proof = None;
    for _ in 0..iters {
        let start = Instant::now();
        let next = prove_mdoc_circuit(&fixture.extracted, &fixture.statement)
            .expect("mdoc circuit proves");
        prove_times.push(start.elapsed());
        black_box(&next);
        proof = Some(next);
    }
    let proof = proof.expect("at least one proof iteration ran");
    let proof_bytes = bincode::serialize(&proof)
        .expect("mdoc proof serializes")
        .len();
    verify_mdoc_circuit(&proof, &fixture.statement).expect("mdoc circuit verifies");

    let mut verify_times = Vec::with_capacity(iters);
    for _ in 0..iters {
        let start = Instant::now();
        verify_mdoc_circuit(&proof, &fixture.statement).expect("mdoc circuit verifies");
        verify_times.push(start.elapsed());
    }

    let modules = demo_mdoc_module_shapes()
        .expect("mdoc module shapes")
        .into_iter()
        .map(|shape| ModuleShape {
            name: shape.name,
            cells: shape_cells(&shape.layout),
        })
        .collect::<Vec<_>>();
    let shape_cells = modules.iter().map(|module| module.cells).sum();

    let report = Report {
        feature_mode: if cfg!(feature = "ec-coprocessor") {
            "ec-coprocessor"
        } else {
            "legacy-p256-air"
        },
        rayon_num_threads: std::env::var("RAYON_NUM_THREADS").ok(),
        iters,
        proof_bytes,
        prove_ms_median: median(&mut prove_times).as_millis(),
        verify_ms_median: median(&mut verify_times).as_millis(),
        pcs_config: proof.stark_proof.config,
        shape_cells,
        modules,
        byte_breakdown: mdoc_proof_byte_breakdown(&proof),
    };
    println!("{}", serde_json::to_string_pretty(&report).unwrap());
}

fn median(values: &mut [Duration]) -> Duration {
    values.sort_unstable();
    values[values.len() / 2]
}

fn shape_cells(layout: &air_core::TreeLayout) -> u64 {
    layout
        .preprocessed
        .iter()
        .chain(&layout.trace)
        .chain(&layout.interaction)
        .map(|&log_size| 1u64 << log_size)
        .sum()
}
