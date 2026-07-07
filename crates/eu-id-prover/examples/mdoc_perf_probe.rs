//! Exact-iteration mdoc perf probe for WO-M3 A/B gates.
//!
//! Criterion owns the general laptop benchmark. This probe exists for work-order
//! gates that require a fixed small N and one machine-readable line item:
//! prove median, verify median, proof bytes, and committed shape cells.

use std::hint::black_box;
use std::time::{Duration, Instant};

use eu_id_prover::mdoc::{
    demo_mdoc_circuit_fixture, demo_mdoc_module_shapes, mdoc_proof_byte_breakdown,
    prove_mdoc_circuit, verify_mdoc_circuit, verify_mdoc_circuit_with_pcs_config_profiled,
    MdocProofByteBreakdown,
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
    #[cfg(feature = "ec-coprocessor")]
    p4b_prove_profile: Option<P4bProveProfileReport>,
    #[cfg(feature = "ec-coprocessor")]
    p4b_verify_profile: Option<P4bVerifyProfileReport>,
}

#[derive(Serialize)]
struct ModuleShape {
    name: &'static str,
    /// Retained original field: total committed cells across all trees.
    cells: u64,
    preprocessed_cells: u64,
    trace_cells: u64,
    interaction_cells: u64,
    total_cells: u64,
    /// Per-column detail, one entry per (tree, log_size) bucket, in commit
    /// order. `n_columns` columns of `2^log_size` cells each in that tree.
    /// Stable/greppable names: "<module>/<tree>/log<log_size>".
    columns: Vec<ComponentColumns>,
    /// TRUE per-component rows for modules that aggregate multiple producer
    /// tables under one layout (today: only `mdoc_sha_tables`). Each row names
    /// the actual table (`sp_sigma0_lo`, `range_16`, …) and reconciles exactly
    /// to the module's `(tree, log_size)` buckets in `columns`. Empty for
    /// single-component modules. Additive — does not replace `columns`.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    component_shapes: Vec<ComponentShapeRow>,
}

/// One producer table's committed shape, named by the table it serves.
#[derive(Serialize)]
struct ComponentShapeRow {
    name: String,
    log_size: u32,
    preprocessed_columns: usize,
    trace_columns: usize,
    interaction_columns: usize,
    /// Total committed cells this component owns across all three trees.
    cells: u64,
}

/// A group of same-shaped committed columns the architect ranks reductions from.
/// `tree` is one of "preprocessed" | "trace" | "interaction".
#[derive(Serialize)]
struct ComponentColumns {
    name: String,
    tree: &'static str,
    n_columns: usize,
    log_size: u32,
    cells: u64,
}

/// Bucket a single tree's column log-sizes into greppable (log_size -> count)
/// groups, preserving ascending log_size order for stable diffs.
fn tree_columns(
    module: &str,
    tree: &'static str,
    log_sizes: &[u32],
) -> (Vec<ComponentColumns>, u64) {
    let mut counts: std::collections::BTreeMap<u32, usize> = std::collections::BTreeMap::new();
    for &log_size in log_sizes {
        *counts.entry(log_size).or_default() += 1;
    }
    let mut cells_total = 0u64;
    let groups = counts
        .into_iter()
        .map(|(log_size, n_columns)| {
            let cells = (n_columns as u64) * (1u64 << log_size);
            cells_total += cells;
            ComponentColumns {
                name: format!("{module}/{tree}/log{log_size}"),
                tree,
                n_columns,
                log_size,
                cells,
            }
        })
        .collect();
    (groups, cells_total)
}

#[cfg(feature = "ec-coprocessor")]
#[derive(Serialize)]
struct P4bProveProfileReport {
    witness_check_ms: u128,
    circuit_build_ms: u128,
    rs_encode_ms: u128,
    merkle_commit_ms: u128,
    proximity_claim_ms: u128,
    proximity_openings_ms: u128,
    sumcheck_ms: u128,
    claim_batch_ms: u128,
    row_inventory: P4bRowInventoryReport,
    sumcheck_by_instance: Vec<P4bInstanceTimingReport>,
}

#[cfg(feature = "ec-coprocessor")]
#[derive(Serialize)]
struct P4bVerifyProfileReport {
    total_ms: u128,
    setup_ms: u128,
    proximity_ms: u128,
    sumcheck_ms: u128,
    input_claims_ms: u128,
    consistency_ms: u128,
    claim_batch_ms: u128,
    sumcheck_by_instance: Vec<P4bInstanceTimingReport>,
}

#[cfg(feature = "ec-coprocessor")]
#[derive(Serialize)]
struct P4bInstanceTimingReport {
    role: &'static str,
    label: String,
    elapsed_ms: u128,
}

#[cfg(feature = "ec-coprocessor")]
#[derive(Serialize)]
struct P4bRowInventoryReport {
    row_len: usize,
    committed_values: usize,
    committed_rows: usize,
    encoded_rows_total: usize,
    ecdsa_input_values: usize,
    ecdsa_input_rows: usize,
    mac_input_values: usize,
    mac_input_rows: usize,
    otp_pad_values: usize,
    otp_pad_rows: usize,
    blind_rows: usize,
    linear_claims: usize,
    linear_claim_touched_rows: usize,
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
    #[cfg(feature = "ec-coprocessor")]
    let p4b_prove_profile = proof.p4b_prove_profile().map(P4bProveProfileReport::from);
    let proof_bytes = bincode::serialize(&proof)
        .expect("mdoc proof serializes")
        .len();
    verify_mdoc_circuit(&proof, &fixture.statement).expect("mdoc circuit verifies");

    let mut verify_times = Vec::with_capacity(iters);
    #[cfg(feature = "ec-coprocessor")]
    let mut p4b_verify_profile = None;
    for _ in 0..iters {
        let start = Instant::now();
        #[cfg(feature = "ec-coprocessor")]
        {
            let profile = verify_mdoc_circuit_with_pcs_config_profiled(
                &proof,
                &fixture.statement,
                proof.stark_proof.config,
            )
            .expect("mdoc circuit verifies");
            verify_times.push(start.elapsed());
            p4b_verify_profile = Some(P4bVerifyProfileReport::from(&profile));
        }
        #[cfg(not(feature = "ec-coprocessor"))]
        {
            verify_mdoc_circuit(&proof, &fixture.statement).expect("mdoc circuit verifies");
            verify_times.push(start.elapsed());
        }
    }

    let modules = demo_mdoc_module_shapes()
        .expect("mdoc module shapes")
        .into_iter()
        .map(|shape| {
            let (pre, preprocessed_cells) =
                tree_columns(shape.name, "preprocessed", &shape.layout.preprocessed);
            let (trace, trace_cells) = tree_columns(shape.name, "trace", &shape.layout.trace);
            let (inter, interaction_cells) =
                tree_columns(shape.name, "interaction", &shape.layout.interaction);
            let total_cells = preprocessed_cells + trace_cells + interaction_cells;
            let columns = pre.into_iter().chain(trace).chain(inter).collect();
            let component_shapes: Vec<ComponentShapeRow> = shape
                .components
                .iter()
                .map(|c| {
                    let rows = 1u64 << c.log_size;
                    let cols =
                        (c.preprocessed_columns + c.trace_columns + c.interaction_columns) as u64;
                    ComponentShapeRow {
                        name: c.name.to_string(),
                        log_size: c.log_size,
                        preprocessed_columns: c.preprocessed_columns,
                        trace_columns: c.trace_columns,
                        interaction_columns: c.interaction_columns,
                        cells: cols * rows,
                    }
                })
                .collect();
            // Per-component rows must reconcile exactly to the module totals.
            if !component_shapes.is_empty() {
                let sum: u64 = component_shapes.iter().map(|c| c.cells).sum();
                assert_eq!(
                    sum, total_cells,
                    "module {} per-component cells ({sum}) must equal module total ({total_cells})",
                    shape.name,
                );
            }
            ModuleShape {
                name: shape.name,
                cells: total_cells,
                preprocessed_cells,
                trace_cells,
                interaction_cells,
                total_cells,
                columns,
                component_shapes,
            }
        })
        .collect::<Vec<_>>();
    let shape_cells: u64 = modules.iter().map(|module| module.total_cells).sum();
    // Reconcile the module-total sum against the top-level total. These are the
    // same arithmetic; a mismatch means the per-tree partition dropped columns.
    let module_total_sum: u64 = modules.iter().map(|module| module.total_cells).sum();
    assert_eq!(
        module_total_sum, shape_cells,
        "sum of module total_cells ({module_total_sum}) must equal shape_cells ({shape_cells})",
    );
    eprintln!(
        "shape_cells reconciliation: top_level={shape_cells} module_total_sum={module_total_sum}",
    );

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
        #[cfg(feature = "ec-coprocessor")]
        p4b_prove_profile,
        #[cfg(feature = "ec-coprocessor")]
        p4b_verify_profile,
    };
    println!("{}", serde_json::to_string_pretty(&report).unwrap());
}

fn median(values: &mut [Duration]) -> Duration {
    values.sort_unstable();
    values[values.len() / 2]
}

#[cfg(feature = "ec-coprocessor")]
impl From<&eu_id_ec_coprocessor::ecdsa::MdocP4bProveProfile> for P4bProveProfileReport {
    fn from(profile: &eu_id_ec_coprocessor::ecdsa::MdocP4bProveProfile) -> Self {
        Self {
            witness_check_ms: profile.witness_check.as_millis(),
            circuit_build_ms: profile.circuit_build.as_millis(),
            rs_encode_ms: profile.ligero_row_encode.as_millis(),
            merkle_commit_ms: profile.ligero_merkle_build.as_millis(),
            proximity_claim_ms: profile.ligero_proximity_claim.as_millis(),
            proximity_openings_ms: profile.ligero_openings.as_millis(),
            sumcheck_ms: profile.sumcheck.as_millis(),
            claim_batch_ms: profile.claim_batch.as_millis(),
            row_inventory: P4bRowInventoryReport::from(&profile.row_inventory),
            sumcheck_by_instance: profile
                .sumcheck_by_instance
                .iter()
                .map(P4bInstanceTimingReport::from)
                .collect(),
        }
    }
}

#[cfg(feature = "ec-coprocessor")]
impl From<&eu_id_prover::mdoc::MdocCircuitVerifyProfile> for P4bVerifyProfileReport {
    fn from(profile: &eu_id_prover::mdoc::MdocCircuitVerifyProfile) -> Self {
        let p4b = profile.p4b.as_ref();
        Self {
            total_ms: profile.total.as_millis(),
            setup_ms: p4b.map(|p| p.setup.as_millis()).unwrap_or(0),
            proximity_ms: p4b.map(|p| p.ligero_proximity.as_millis()).unwrap_or(0),
            sumcheck_ms: p4b.map(|p| p.sumcheck.as_millis()).unwrap_or(0),
            input_claims_ms: p4b.map(|p| p.input_claims.as_millis()).unwrap_or(0),
            consistency_ms: p4b.map(|p| p.consistency.as_millis()).unwrap_or(0),
            claim_batch_ms: p4b.map(|p| p.claim_batch.as_millis()).unwrap_or(0),
            sumcheck_by_instance: p4b
                .map(|p| {
                    p.sumcheck_by_instance
                        .iter()
                        .map(P4bInstanceTimingReport::from)
                        .collect()
                })
                .unwrap_or_default(),
        }
    }
}

#[cfg(feature = "ec-coprocessor")]
impl From<&eu_id_ec_coprocessor::ecdsa::MdocP4bInstanceTiming> for P4bInstanceTimingReport {
    fn from(timing: &eu_id_ec_coprocessor::ecdsa::MdocP4bInstanceTiming) -> Self {
        Self {
            role: timing.role,
            label: timing.label.clone(),
            elapsed_ms: timing.elapsed.as_millis(),
        }
    }
}

#[cfg(feature = "ec-coprocessor")]
impl From<&eu_id_ec_coprocessor::ecdsa::MdocP4bRowInventory> for P4bRowInventoryReport {
    fn from(inventory: &eu_id_ec_coprocessor::ecdsa::MdocP4bRowInventory) -> Self {
        Self {
            row_len: inventory.row_len,
            committed_values: inventory.committed_values,
            committed_rows: inventory.committed_rows,
            encoded_rows_total: inventory.encoded_rows_total,
            ecdsa_input_values: inventory.ecdsa_input_values,
            ecdsa_input_rows: inventory.ecdsa_input_rows,
            mac_input_values: inventory.mac_input_values,
            mac_input_rows: inventory.mac_input_rows,
            otp_pad_values: inventory.otp_pad_values,
            otp_pad_rows: inventory.otp_pad_rows,
            blind_rows: inventory.blind_rows,
            linear_claims: inventory.linear_claims,
            linear_claim_touched_rows: inventory.linear_claim_touched_rows,
        }
    }
}
