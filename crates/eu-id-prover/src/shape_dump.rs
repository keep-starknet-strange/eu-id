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

use stwo_p256::proof::P256ProofDraft;

use crate::{bridge_log_size, bridge_rows, credential_exposure, fixtures};

const NONCE_P256_PREPROCESSED_NAMESPACE: &str = "nonce_p256";

fn tree_stats(name: &str, sizes: &[u32]) -> (usize, u64) {
    let cols = sizes.len();
    let cells: u64 = sizes.iter().map(|&s| 1u64 << s).sum();
    let min = sizes.iter().min().copied().unwrap_or(0);
    let max = sizes.iter().max().copied().unwrap_or(0);
    println!("    {name:<14} cols={cols:>6}  cells={cells:>10}  log_size min/max={min}/{max}");
    (cols, cells)
}

fn layout_stats(name: &str, layout: &air_core::TreeLayout) -> (usize, u64) {
    println!("  module {name}");
    let p = tree_stats("preprocessed", &layout.preprocessed);
    let t = tree_stats("trace", &layout.trace);
    let i = tree_stats("interaction", &layout.interaction);
    println!(
        "    TOTAL          cols={:>6}  cells={:>10}",
        p.0 + t.0 + i.0,
        p.1 + t.1 + i.1
    );
    (p.0 + t.0 + i.0, p.1 + t.1 + i.1)
}

#[test]
#[ignore = "diagnostic dump, run manually with --nocapture"]
#[allow(clippy::drop_non_drop)]
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

    // Mirror `prove()`'s module construction exactly.
    let scalar_z_handle = SharedScalarZRelation::new();
    let digest_handle = SharedDigestRelation::new();
    let field_handle = SharedFieldRelation::new();

    let mut p256 = P256Prover::new(draft)
        .expect("p256 prover")
        .with_z_binding(scalar_z_handle.clone());
    let nonce_statement = fixtures::demo_nonce_statement();
    let nonce_draft = P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![
        nonce_statement.ecdsa_input(),
    ])
    .expect("nonce draft");
    let mut nonce_p256 = P256Prover::new(&nonce_draft)
        .expect("nonce p256 prover")
        .with_preprocessed_namespace(NONCE_P256_PREPROCESSED_NAMESPACE);
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
    let mut modules: [(&str, &mut dyn AirProver); 6] = [
        ("p256", &mut p256),
        ("nonce_p256", &mut nonce_p256),
        ("sha256", &mut sha),
        ("digest_bind", &mut bridge),
        ("age", &mut age),
        ("nat", &mut nat),
    ];

    println!("\n=== per-module committed columns (from Air::layout) ===");
    let mut grand = (0usize, 0u64);
    let mut grand_post = (0usize, 0u64);
    for (name, m) in modules.iter() {
        let layout = m.layout();
        let stats = layout_stats(name, &layout);
        grand.0 += stats.0;
        grand.1 += stats.1;
        let post_interaction = m.post_interaction_log_sizes();
        if !post_interaction.is_empty() {
            println!("    optional post-interaction tree");
            let post_stats = tree_stats("post", &post_interaction);
            grand_post.0 += post_stats.0;
            grand_post.1 += post_stats.1;
        }
    }
    println!(
        "  GRAND TOTAL      cols={:>6}  cells={:>10}",
        grand.0, grand.1
    );
    if grand_post.0 != 0 {
        println!(
            "  GRAND + POST     cols={:>6}  cells={:>10}",
            grand.0 + grand_post.0,
            grand.1 + grand_post.1
        );
    }

    println!("\n=== mdoc per-module committed columns (from Air::layout) ===");
    let mut mdoc_grand = (0usize, 0u64);
    for shape in crate::mdoc::demo_mdoc_module_shapes().expect("mdoc module shapes") {
        let stats = layout_stats(shape.name, &shape.layout);
        mdoc_grand.0 += stats.0;
        mdoc_grand.1 += stats.1;
    }
    println!(
        "  MDOC GRAND TOTAL cols={:>6}  cells={:>10}",
        mdoc_grand.0, mdoc_grand.1
    );
    let mdoc_waste = crate::mdoc::demo_mdoc_sizing_waste().expect("mdoc sizing waste");
    println!("\n=== mdoc Phase 0b sizing waste ===");
    for row in &mdoc_waste.sha {
        println!(
            "  sha {:<12} natural_log={} shared_log={} wasted_cells={}",
            row.name, row.natural_log, row.shared_log, row.wasted_cells
        );
    }
    println!("  sha total wasted cells = {}", mdoc_waste.sha_wasted_cells);
    println!(
        "  p256 namespaced content-identical preprocessed cells = {}",
        mdoc_waste.p256_namespaced_identical_preprocessed_cells
    );
    println!(
        "  combined accepted waste cells = {}",
        mdoc_waste.combined_wasted_cells()
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
    for (_, m) in modules.iter_mut() {
        m.prove_post_interaction(channel);
    }
    if modules
        .iter()
        .any(|(_, m)| !m.post_interaction_log_sizes().is_empty())
    {
        let mut tb = commitment_scheme.tree_builder();
        for (_, m) in modules.iter_mut() {
            m.write_post_interaction(&mut tb);
        }
        tb.commit(channel);
    }

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
            grand += s;
        }
        println!("  GRAND claimed-sum total = {grand:?}");
    }
    let mut seen_preprocessed_ids = std::collections::HashSet::new();
    let preprocessed_ids: Vec<PreProcessedColumnId> = modules
        .iter()
        .flat_map(|(_, m)| m.preprocessed_column_ids())
        .filter(|id| seen_preprocessed_ids.insert(id.clone()))
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
