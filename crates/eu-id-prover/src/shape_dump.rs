//! Diagnostic: dump the committed column shape of every module and component.
//!
//! Run with:
//! `cargo test -p eu-id-prover --release shape_dump -- --nocapture --ignored`

use air_core::relations::{SharedDigestRelation, SharedFieldRelation};
use air_core::{AirProver, Ch, Mc};
use predicates::nat::NationalityPredicate;
use predicates::{AgeRangeCheck, PredicateProver};
use stwo::core::pcs::PcsConfig;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::PolyOps;
use stwo::prover::CommitmentSchemeProver;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::TraceLocationAllocator;
use stwo_p256::components::digest_bind::module::DigestBindProver;
use stwo_p256::components::digest_bind::SharedScalarZRelation;
use stwo_p256::proof::air::P256Prover;
use stwo_sha256::air::Sha256Prover;
use stwo_sha256::stark::{prove_sha256_from_witness, ProverConfig};

use crate::{bridge_log_size, bridge_rows, credential_exposure, fixtures};

fn tree_stats(name: &str, sizes: &[u32]) -> (usize, u64) {
    let cols = sizes.len();
    let cells: u64 = sizes.iter().map(|&s| 1u64 << s).sum();
    let min = sizes.iter().min().copied().unwrap_or(0);
    let max = sizes.iter().max().copied().unwrap_or(0);
    println!("    {name:<14} cols={cols:>6}  cells={cells:>10}  log_size min/max={min}/{max}");
    (cols, cells)
}

#[test]
#[ignore = "diagnostic dump, run manually with --nocapture"]
fn shape_dump() {
    let pw = fixtures::valid_over_18().pipeline_witness();
    let draft = pw.p256_draft.as_ref().expect("valid fixture has a draft");
    let sha_proof = prove_sha256_from_witness(
        &pw.sha_witness,
        &ProverConfig {
            log_n_rows: pw.sha_log_n_rows,
            group_width: pw.sha_group_width,
            pcs_config: PcsConfig::default(),
        },
    )
    .expect("shape dump SHA proof");
    let sha_stark_bytes = bincode::serialize(&sha_proof.stark_proof)
        .expect("serialize SHA STARK proof")
        .len();
    println!("  sha standalone STARK proof bytes = {sha_stark_bytes}");
    #[cfg(feature = "gkr-spike")]
    {
        let sha_gkr_bytes = bincode::serialize(&sha_proof.xor_8_gkr_proof)
            .expect("serialize SHA xor_8 GKR proof")
            .len();
        println!("  sha xor_8 GKR proof bytes = {sha_gkr_bytes}");
    }

    // Mirror `prove()`'s module construction exactly.
    let scalar_z_handle = SharedScalarZRelation::new();
    let digest_handle = SharedDigestRelation::new();
    let field_handle = SharedFieldRelation::new();

    let mut p256 = P256Prover::new(draft)
        .expect("p256 prover")
        .with_z_binding(scalar_z_handle.clone());
    let mut sha = Sha256Prover::new(&pw.sha_witness, pw.sha_log_n_rows, pw.sha_group_width)
        .with_digest_handle(digest_handle.clone())
        .with_field_handle(credential_exposure(), field_handle.clone());

    let instances = p256.proof_claim().public_inputs.instances.clone();
    let rows = bridge_rows(&instances);
    let bridge_log = bridge_log_size(rows.len());
    let mut bridge = DigestBindProver::new(rows, bridge_log, scalar_z_handle, digest_handle);

    let mut age = AgeRangeCheck::new(PcsConfig::default())
        .prover(&pw.age_public, &pw.age_dob)
        .expect("age prover")
        .with_dob_binding(field_handle.clone());
    let mut nat = NationalityPredicate::new(PcsConfig::default())
        .prover(&pw.nat_public, &pw.nat_private)
        .expect("nat prover")
        .with_nat_binding(field_handle.clone());

    let config = p256.pcs_config();
    let mut modules: [(&str, &mut dyn AirProver); 5] = [
        ("p256", &mut p256),
        ("sha256", &mut sha),
        ("digest_bind", &mut bridge),
        ("age", &mut age),
        ("nat", &mut nat),
    ];

    println!("\n=== per-module committed columns (from Air::layout) ===");
    let mut grand = (0usize, 0u64);
    for (name, m) in modules.iter() {
        let layout = m.layout();
        println!("  module {name}");
        let p = tree_stats("preprocessed", &layout.preprocessed);
        let t = tree_stats("trace", &layout.trace);
        let i = tree_stats("interaction", &layout.interaction);
        println!(
            "    TOTAL          cols={:>6}  cells={:>10}",
            p.0 + t.0 + i.0,
            p.1 + t.1 + i.1
        );
        grand.0 += p.0 + t.0 + i.0;
        grand.1 += p.1 + t.1 + i.1;
    }
    println!(
        "  GRAND TOTAL      cols={:>6}  cells={:>10}",
        grand.0, grand.1
    );

    // Per-component breakdown needs built components, which need claimed sums
    // from the interaction phase — so run the real commit phases (everything
    // `air_core::prove` does before `stark_prove`).
    let max_bound = modules
        .iter()
        .map(|(_, m)| m.max_constraint_log_degree_bound())
        .max()
        .unwrap();
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(max_bound + config.fri_config.log_blowup_factor)
            .circle_domain()
            .half_coset,
    );
    let channel = &mut Ch::default();
    let mut commitment_scheme = CommitmentSchemeProver::<SimdBackend, Mc>::new(config, &twiddles);
    if modules
        .iter()
        .any(|(_, m)| m.store_polynomial_coefficients())
    {
        commitment_scheme.set_store_polynomials_coefficients();
    }
    let mut tb = commitment_scheme.tree_builder();
    for (_, m) in modules.iter_mut() {
        m.write_preprocessed(&mut tb);
    }
    tb.commit(channel);
    for (_, m) in modules.iter() {
        m.mix_public(channel);
    }
    let mut tb = commitment_scheme.tree_builder();
    for (_, m) in modules.iter_mut() {
        m.write_trace(&mut tb);
    }
    tb.commit(channel);
    for (_, m) in modules.iter_mut() {
        m.draw_relations(channel);
    }
    let mut tb = commitment_scheme.tree_builder();
    for (_, m) in modules.iter_mut() {
        m.write_interaction(&mut tb);
    }
    for (_, m) in modules.iter() {
        m.mix_claimed_sums(channel);
    }
    tb.commit(channel);

    // Debug: per-family claimed-sum totals (imbalance hunting).
    {
        let mut grand =
            stwo::core::fields::qm31::QM31::from(stwo::core::fields::m31::M31::from(0u32));
        for (name, m) in modules.iter() {
            let s: stwo::core::fields::qm31::QM31 = m
                .claimed_sums()
                .into_iter()
                .fold(grand - grand, |a, b| a + b);
            println!("  module {name} claimed-sum total = {s:?}");
            grand = grand + s;
        }
        println!("  GRAND claimed-sum total = {grand:?}");
    }
    let preprocessed_ids: Vec<PreProcessedColumnId> = modules
        .iter()
        .flat_map(|(_, m)| m.preprocessed_column_ids())
        .collect();
    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&preprocessed_ids);
    for (_, m) in modules.iter_mut() {
        m.build_components(&mut allocator);
    }

    println!("\n=== per-component committed columns (from Component::trace_log_degree_bounds) ===");
    for (name, m) in modules.iter() {
        println!("  module {name}: {} components", m.components().len());
        for (idx, c) in m.components().iter().enumerate() {
            let bounds = c.trace_log_degree_bounds();
            let empty: Vec<u32> = Vec::new();
            let tree = |i: usize| bounds.get(i).map(Vec::as_slice).unwrap_or(&empty);
            let (pre, base, inter) = (tree(0).to_vec(), tree(1).to_vec(), tree(2).to_vec());
            let log = base.iter().chain(inter.iter()).max().copied().unwrap_or(0);
            println!(
                "    [{idx:>3}] pre={:>4} base={:>5} inter={:>5} total={:>5}  max_col_log={log}",
                pre.len(),
                base.len(),
                inter.len(),
                pre.len() + base.len() + inter.len(),
            );
        }
    }

    drop(modules);
    let ic = p256.interaction_claim();
    println!(
        "  p256.prepared_table_projective_source.total = {:?}",
        ic.prepared_table_projective_source.total()
    );
    println!(
        "  p256.fake_glv_projective_source.total = {:?}",
        ic.fake_glv_projective_source.total()
    );
    println!("  p256.final_add.total = {:?}", ic.final_add.total());
}
