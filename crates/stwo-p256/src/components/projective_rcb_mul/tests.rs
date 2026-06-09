//! Tests for the projective RCB multiplication AIR family.
//!
//! Relocated verbatim out of `mod.rs` (test module body, dedented one level).

use super::*;
use crate::constants::{P256_GX, P256_GY};
use crate::curve::point_double;
use crate::fp_solinas_air::FpSolinasReductionTraceError;
use crate::prepared_table::PreparedAffinePoint;
use crate::projective::{
    ProjectiveEcError, ProjectiveEcOp, ProjectiveEcRow, ProjectiveEcTraceClaim,
};
use crate::range_checks::{
    RangeCheckClaim, RangeCheckInteractionClaim, RangeCheckRelation, SignedCarryRangeClaim,
    RANGE13_BITS, RANGE16_BITS,
};
use crate::scalar::scalar_mod_mul::columns::padded_log_size;
use crate::types::{AffinePoint, U256};
use num_traits::Zero;
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::qm31::SecureField;
use stwo::core::fri::FriConfig;
use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig, TreeVec};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::core::verifier::verify;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::PolyOps;
use stwo::prover::{prove, CommitmentSchemeProver, ComponentProver};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    assert_constraints_on_polys, FrameworkEval, TraceLocationAllocator,
};

fn generator() -> PreparedAffinePoint {
    PreparedAffinePoint::from_affine(AffinePoint {
        x: U256::from_le_u64s(&P256_GX),
        y: U256::from_le_u64s(&P256_GY),
    })
}

fn one_row_trace(op: ProjectiveEcOp, rhs: PreparedAffinePoint) -> ProjectiveEcTraceClaim {
    let lhs = generator();
    let output = match op {
        ProjectiveEcOp::Double => {
            PreparedAffinePoint::from_affine(point_double(&lhs.to_option().unwrap()).output)
        }
        ProjectiveEcOp::MixedAdd => {
            let output =
                crate::curve::point_add(&lhs.to_option().unwrap(), &rhs.to_option().unwrap())
                    .output;
            PreparedAffinePoint::from_affine(output)
        }
    };
    ProjectiveEcTraceClaim {
        rows: vec![ProjectiveEcRow::new(
            M31::from_u32_unchecked(0),
            M31::from_u32_unchecked(0),
            op,
            &lhs,
            &rhs,
            &output,
        )],
    }
}

fn low_ram_proof_layer_config(max_constraint_log_degree_bound: u32) -> PcsConfig {
    let fri_config = FriConfig::new(5, 4, 64, 1);
    PcsConfig {
        pow_bits: 0,
        fri_config,
        lifting_log_size: Some(
            (max_constraint_log_degree_bound + fri_config.log_blowup_factor).max(10),
        ),
    }
}

fn prove_and_verify_raw_product_chunk_component(claim: &ProjectiveRcbAirTraceClaim) {
    let log_size = claim.component_log_sizes().raw_product_chunk;
    let mut ids_allocator = TraceLocationAllocator::default();
    let sizing_component = ProjectiveRcbRawProductChunkComponent::new(
        &mut ids_allocator,
        ProjectiveRcbRawProductChunkEval {
            log_size,
            relations: ProjectiveRcbMulComponentRelations::dummy(),
            schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        },
        SecureField::zero(),
    );
    let ids = ids_allocator.preprocessed_columns().clone();
    let max_constraint_log_degree_bound = sizing_component.max_constraint_log_degree_bound();
    let config = low_ram_proof_layer_config(max_constraint_log_degree_bound);
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(
            config
                .lifting_log_size
                .unwrap_or(max_constraint_log_degree_bound + config.fri_config.log_blowup_factor),
        )
        .circle_domain()
        .half_coset,
    );

    let mut channel = Blake2sChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);
    commitment_scheme.set_store_polynomials_coefficients();

    let preprocessed = claim
        .gen_preprocessed_trace(&ids)
        .expect("raw preprocessed trace generates");
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(preprocessed.clone());
    tree_builder.commit(&mut channel);

    let base = gen_projective_rcb_raw_product_chunk_base_trace(claim, log_size)
        .expect("raw base trace generates");
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(base.clone());
    tree_builder.commit(&mut channel);

    let relations = ProjectiveRcbMulComponentRelations::draw(&mut channel);
    let (interaction_traces, interaction_claim) = claim.gen_interaction_trace(&relations);
    let interaction = interaction_traces.raw_product_chunk;
    let mut component_allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let component = ProjectiveRcbRawProductChunkComponent::new(
        &mut component_allocator,
        ProjectiveRcbRawProductChunkEval {
            log_size,
            relations: relations.clone(),
            schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        },
        interaction_claim.raw_product_chunk,
    );
    let trace_polys = TreeVec::new(vec![preprocessed, base, interaction.clone()]).map(|trace| {
        trace
            .into_iter()
            .map(|column| column.interpolate())
            .collect::<Vec<_>>()
    });
    assert_constraints_on_polys(
        &trace_polys,
        CanonicCoset::new(log_size),
        |eval| {
            ProjectiveRcbRawProductChunkEval {
                log_size,
                relations: relations.clone(),
                schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
            }
            .evaluate(eval);
        },
        interaction_claim.raw_product_chunk,
    );

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction);
    tree_builder.commit(&mut channel);
    let proof = prove(
        &[&component as &dyn ComponentProver<SimdBackend>],
        &mut channel,
        commitment_scheme,
    )
    .expect("raw product chunk component proves");

    let mut verifier_channel = Blake2sChannel::default();
    let commitment_scheme =
        &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(proof.config);
    let sizes = component.trace_log_degree_bounds();
    commitment_scheme.commit(proof.commitments[0], &sizes[0], &mut verifier_channel);
    commitment_scheme.commit(proof.commitments[1], &sizes[1], &mut verifier_channel);
    let verifier_relations = ProjectiveRcbMulComponentRelations::draw(&mut verifier_channel);
    let mut verifier_allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let verifier_component = ProjectiveRcbRawProductChunkComponent::new(
        &mut verifier_allocator,
        ProjectiveRcbRawProductChunkEval {
            log_size,
            relations: verifier_relations,
            schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        },
        interaction_claim.raw_product_chunk,
    );
    commitment_scheme.commit(proof.commitments[2], &sizes[2], &mut verifier_channel);

    verify(
        &[&verifier_component],
        &mut verifier_channel,
        commitment_scheme,
        proof,
    )
    .expect("raw product chunk component verifies");
}

/// Minimal recording `EvalAtRow` that evaluates the *polynomial* constraints of
/// a component over one committed base-trace row and collects each constraint's
/// value instead of asserting it is zero. LogUp relations are skipped (the C1
/// pin is a pure polynomial constraint), so there is no `LogupAtRow` and hence
/// no double-panic-on-failure abort — failures are observable as a non-zero
/// recorded value rather than an uncatchable `SIGABRT`.
struct RecordingMulEvaluator<'a> {
    base: &'a [Vec<M31>],
    col_index: usize,
    row: usize,
    constraints: Vec<SecureField>,
}

impl EvalAtRow for RecordingMulEvaluator<'_> {
    type F = M31;
    type EF = SecureField;

    fn next_interaction_mask<const N: usize>(
        &mut self,
        interaction: usize,
        offsets: [isize; N],
    ) -> [Self::F; N] {
        // The mul component reads only same-row base-trace masks.
        assert_eq!(interaction, 1, "mul component reads only the base trace");
        let col = self.col_index;
        self.col_index += 1;
        offsets.map(|offset| {
            assert_eq!(offset, 0, "mul component reads only offset-0 masks");
            self.base[col][self.row]
        })
    }

    fn add_constraint<G>(&mut self, constraint: G)
    where
        Self::EF: std::ops::Mul<G, Output = Self::EF> + From<G>,
    {
        self.constraints.push(Self::EF::from(constraint));
    }

    fn combine_ef(values: [Self::F; 4]) -> Self::EF {
        SecureField::from_m31_array(values)
    }

    // LogUp is irrelevant to the polynomial C1 pin; skip it so no LogupAtRow is
    // constructed (its Drop would otherwise abort on a failing-constraint panic).
    fn add_to_relation<R: stwo_constraint_framework::Relation<Self::F, Self::EF>>(
        &mut self,
        _entry: stwo_constraint_framework::RelationEntry<'_, Self::F, Self::EF, R>,
    ) {
    }

    fn finalize_logup(&mut self) {}

    fn finalize_logup_in_pairs(&mut self) {}
}

/// Returns whether every polynomial constraint of the mul component holds on all
/// active rows of `claim`'s base trace. Drives the real
/// [`ProjectiveRcbMulEval::evaluate`] logic via [`RecordingMulEvaluator`].
fn mul_component_constraints_hold(claim: &ProjectiveRcbAirTraceClaim) -> bool {
    let log_size = claim.component_log_sizes().mul;
    let base = gen_projective_rcb_mul_base_trace(claim, log_size)
        .expect("mul base trace generates")
        .into_iter()
        .map(|column| column.to_cpu().values)
        .collect::<Vec<_>>();
    let row_count = 1usize << log_size;
    for row in 0..row_count {
        let eval = RecordingMulEvaluator {
            base: &base,
            col_index: 0,
            row,
            constraints: Vec::new(),
        };
        let eval = ProjectiveRcbMulEval {
            log_size,
            relations: ProjectiveRcbMulComponentRelations::dummy(),
        }
        .evaluate(eval);
        if eval
            .constraints
            .iter()
            .any(|value| *value != SecureField::zero())
        {
            return false;
        }
    }
    true
}

/// C1 soundness regression: the committed `correction_product_digit` must be
/// pinned to the convolution of range-checked 13-bit correction digits with the
/// constant P-256 modulus limbs. Without that pin a malicious prover can forge
/// `correction_product_digit` (compensating via `result_limb` so the per-digit
/// reduction recurrence still holds) and have a FALSE Fp product reduce
/// correctly — every Fp multiply, hence every ECDSA verification, becomes
/// forgeable.
///
/// The forgery here keeps every range-checked column inside its table and keeps
/// the recurrence satisfied, touching only `correction_product_digit` (+1) and
/// `result_limb` (-1) on one reduction digit. Pre-fix this is ACCEPTED
/// (demonstrating C1); post-fix the convolution-pin constraint REJECTS it.
#[test]
fn solinas_reduction_rejects_out_of_range_correction_digit() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let honest =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");

    assert!(
        mul_component_constraints_hold(&honest),
        "honest mul-component trace must satisfy all constraints"
    );

    // Forge one mul's reduction: shift a real product digit away from the
    // convolution while compensating `result_limb` so the recurrence holds and
    // `result_limb` stays a valid 13-bit value.
    let mut forged = honest.clone();
    let reduction = &mut forged.rows[0].muls[0].reduction;
    let digit = reduction
        .rows
        .iter()
        .position(|row| row.digit_index < N_LIMBS && row.result_limb >= 1)
        .expect("a reduction digit with a positive result limb exists");
    reduction.rows[digit].correction_product_digit += 1;
    reduction.rows[digit].result_limb -= 1;

    // The recurrence `folded - cpd - result_limb + prev_carry - 2^13*carry`
    // is preserved by the (+1, -1) shift, so only the convolution pin can fire.
    assert_eq!(
        i128::from(forged.rows[0].muls[0].reduction.rows[digit].folded_digit)
            - forged.rows[0].muls[0].reduction.rows[digit].correction_product_digit
            - i128::from(forged.rows[0].muls[0].reduction.rows[digit].result_limb)
            + forged.rows[0].muls[0].reduction.rows[digit].prev_carry
            - crate::fp_solinas::FP_SOLINAS_LIMB_BASE
                * forged.rows[0].muls[0].reduction.rows[digit].carry,
        0,
        "forged row must keep the reduction recurrence satisfied"
    );

    assert!(
        !mul_component_constraints_hold(&forged),
        "forged correction_product_digit must be rejected by the convolution pin (C1)"
    );
}

fn prove_and_verify_mul_component(claim: &ProjectiveRcbAirTraceClaim) {
    let log_size = claim.component_log_sizes().mul;
    let mut ids_allocator = TraceLocationAllocator::default();
    let sizing_component = ProjectiveRcbMulComponent::new(
        &mut ids_allocator,
        ProjectiveRcbMulEval {
            log_size,
            relations: ProjectiveRcbMulComponentRelations::dummy(),
        },
        SecureField::zero(),
    );
    let ids = ids_allocator.preprocessed_columns().clone();
    let max_constraint_log_degree_bound = sizing_component.max_constraint_log_degree_bound();
    let config = low_ram_proof_layer_config(max_constraint_log_degree_bound);
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(
            config
                .lifting_log_size
                .unwrap_or(max_constraint_log_degree_bound + config.fri_config.log_blowup_factor),
        )
        .circle_domain()
        .half_coset,
    );

    let mut channel = Blake2sChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);
    commitment_scheme.set_store_polynomials_coefficients();

    let preprocessed = claim
        .gen_preprocessed_trace(&ids)
        .expect("mul preprocessed trace generates");
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(preprocessed.clone());
    tree_builder.commit(&mut channel);

    let base =
        gen_projective_rcb_mul_base_trace(claim, log_size).expect("mul base trace generates");
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(base.clone());
    tree_builder.commit(&mut channel);

    let relations = ProjectiveRcbMulComponentRelations::draw(&mut channel);
    let (interaction_traces, interaction_claim) = claim.gen_interaction_trace(&relations);
    let interaction = interaction_traces.mul;
    let mut component_allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let component = ProjectiveRcbMulComponent::new(
        &mut component_allocator,
        ProjectiveRcbMulEval {
            log_size,
            relations: relations.clone(),
        },
        interaction_claim.mul,
    );
    if component.trace_log_degree_bounds().len() > 2 {
        assert_eq!(
            interaction.len(),
            component.trace_log_degree_bounds()[2].len(),
            "mul interaction trace width must match component allocation"
        );
    }
    let trace_polys = TreeVec::new(vec![preprocessed, base, interaction.clone()]).map(|trace| {
        trace
            .into_iter()
            .map(|column| column.interpolate())
            .collect::<Vec<_>>()
    });
    assert_constraints_on_polys(
        &trace_polys,
        CanonicCoset::new(log_size),
        |eval| {
            ProjectiveRcbMulEval {
                log_size,
                relations: relations.clone(),
            }
            .evaluate(eval);
        },
        interaction_claim.mul,
    );

    channel.mix_felts(&[interaction_claim.mul]);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction);
    tree_builder.commit(&mut channel);

    let proof = prove(
        &[&component as &dyn ComponentProver<SimdBackend>],
        &mut channel,
        commitment_scheme,
    )
    .expect("mul component proves");
    drop(proof);
}

fn prove_and_verify_folded_contribution_component(claim: &ProjectiveRcbAirTraceClaim) {
    let log_size = claim.component_log_sizes().folded_contribution;
    let mut ids_allocator = TraceLocationAllocator::default();
    let sizing_component = ProjectiveRcbFoldedContributionComponent::new(
        &mut ids_allocator,
        ProjectiveRcbFoldedContributionEval {
            log_size,
            relations: ProjectiveRcbMulComponentRelations::dummy(),
            schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        },
        SecureField::zero(),
    );
    let ids = ids_allocator.preprocessed_columns().clone();
    let max_constraint_log_degree_bound = sizing_component.max_constraint_log_degree_bound();
    let config = low_ram_proof_layer_config(max_constraint_log_degree_bound);
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(
            config
                .lifting_log_size
                .unwrap_or(max_constraint_log_degree_bound + config.fri_config.log_blowup_factor),
        )
        .circle_domain()
        .half_coset,
    );

    let mut channel = Blake2sChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);
    commitment_scheme.set_store_polynomials_coefficients();

    let preprocessed = claim
        .gen_preprocessed_trace(&ids)
        .expect("folded contribution preprocessed trace generates");
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(preprocessed.clone());
    tree_builder.commit(&mut channel);

    let base = gen_projective_rcb_folded_contribution_base_trace(claim, log_size)
        .expect("folded contribution base trace generates");
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(base.clone());
    tree_builder.commit(&mut channel);

    let relations = ProjectiveRcbMulComponentRelations::draw(&mut channel);
    let (interaction_traces, interaction_claim) = claim.gen_interaction_trace(&relations);
    let interaction = interaction_traces.folded_contribution;
    let mut component_allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let component = ProjectiveRcbFoldedContributionComponent::new(
        &mut component_allocator,
        ProjectiveRcbFoldedContributionEval {
            log_size,
            relations: relations.clone(),
            schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        },
        interaction_claim.folded_contribution,
    );
    assert_eq!(
        interaction.len(),
        component.trace_log_degree_bounds()[2].len(),
        "folded contribution interaction trace width must match component allocation"
    );
    let trace_polys = TreeVec::new(vec![preprocessed, base, interaction.clone()]).map(|trace| {
        trace
            .into_iter()
            .map(|column| column.interpolate())
            .collect::<Vec<_>>()
    });
    assert_constraints_on_polys(
        &trace_polys,
        CanonicCoset::new(log_size),
        |eval| {
            ProjectiveRcbFoldedContributionEval {
                log_size,
                relations: relations.clone(),
                schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
            }
            .evaluate(eval);
        },
        interaction_claim.folded_contribution,
    );

    channel.mix_felts(&[interaction_claim.folded_contribution]);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction);
    tree_builder.commit(&mut channel);

    let proof = prove(
        &[&component as &dyn ComponentProver<SimdBackend>],
        &mut channel,
        commitment_scheme,
    )
    .expect("folded contribution component proves");

    let mut verifier_channel = Blake2sChannel::default();
    let commitment_scheme =
        &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(proof.config);
    let sizes = component.trace_log_degree_bounds();
    commitment_scheme.commit(proof.commitments[0], &sizes[0], &mut verifier_channel);
    commitment_scheme.commit(proof.commitments[1], &sizes[1], &mut verifier_channel);
    let verifier_relations = ProjectiveRcbMulComponentRelations::draw(&mut verifier_channel);
    let mut verifier_allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let verifier_component = ProjectiveRcbFoldedContributionComponent::new(
        &mut verifier_allocator,
        ProjectiveRcbFoldedContributionEval {
            log_size,
            relations: verifier_relations,
            schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        },
        interaction_claim.folded_contribution,
    );
    verifier_channel.mix_felts(&[interaction_claim.folded_contribution]);
    commitment_scheme.commit(proof.commitments[2], &sizes[2], &mut verifier_channel);

    verify(
        &[&verifier_component],
        &mut verifier_channel,
        commitment_scheme,
        proof,
    )
    .expect("folded contribution component verifies");
}

fn prove_and_verify_folded_digit_component(claim: &ProjectiveRcbAirTraceClaim) {
    let log_size = claim.component_log_sizes().folded_digit;
    let mut ids_allocator = TraceLocationAllocator::default();
    let sizing_component = ProjectiveRcbFoldedDigitComponent::new(
        &mut ids_allocator,
        ProjectiveRcbFoldedDigitEval {
            log_size,
            relations: ProjectiveRcbMulComponentRelations::dummy(),
            schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        },
        SecureField::zero(),
    );
    let ids = ids_allocator.preprocessed_columns().clone();
    let max_constraint_log_degree_bound = sizing_component.max_constraint_log_degree_bound();
    let config = low_ram_proof_layer_config(max_constraint_log_degree_bound);
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(
            config
                .lifting_log_size
                .unwrap_or(max_constraint_log_degree_bound + config.fri_config.log_blowup_factor),
        )
        .circle_domain()
        .half_coset,
    );

    let mut channel = Blake2sChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);
    commitment_scheme.set_store_polynomials_coefficients();

    let preprocessed = claim
        .gen_preprocessed_trace(&ids)
        .expect("folded digit preprocessed trace generates");
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(preprocessed.clone());
    tree_builder.commit(&mut channel);

    let base = gen_projective_rcb_folded_digit_base_trace(claim, log_size)
        .expect("folded digit base trace generates");
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(base.clone());
    tree_builder.commit(&mut channel);

    let relations = ProjectiveRcbMulComponentRelations::draw(&mut channel);
    let (interaction_traces, interaction_claim) = claim.gen_interaction_trace(&relations);
    let interaction = interaction_traces.folded_digit;
    let mut component_allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let component = ProjectiveRcbFoldedDigitComponent::new(
        &mut component_allocator,
        ProjectiveRcbFoldedDigitEval {
            log_size,
            relations: relations.clone(),
            schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        },
        interaction_claim.folded_digit,
    );
    let trace_polys = TreeVec::new(vec![preprocessed, base, interaction.clone()]).map(|trace| {
        trace
            .into_iter()
            .map(|column| column.interpolate())
            .collect::<Vec<_>>()
    });
    assert_constraints_on_polys(
        &trace_polys,
        CanonicCoset::new(log_size),
        |eval| {
            ProjectiveRcbFoldedDigitEval {
                log_size,
                relations: relations.clone(),
                schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
            }
            .evaluate(eval);
        },
        interaction_claim.folded_digit,
    );

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction);
    tree_builder.commit(&mut channel);

    let proof = prove(
        &[&component as &dyn ComponentProver<SimdBackend>],
        &mut channel,
        commitment_scheme,
    )
    .expect("folded digit component proves");

    let mut verifier_channel = Blake2sChannel::default();
    let commitment_scheme =
        &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(proof.config);
    let sizes = component.trace_log_degree_bounds();
    commitment_scheme.commit(proof.commitments[0], &sizes[0], &mut verifier_channel);
    commitment_scheme.commit(proof.commitments[1], &sizes[1], &mut verifier_channel);
    let verifier_relations = ProjectiveRcbMulComponentRelations::draw(&mut verifier_channel);
    let mut verifier_allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let verifier_component = ProjectiveRcbFoldedDigitComponent::new(
        &mut verifier_allocator,
        ProjectiveRcbFoldedDigitEval {
            log_size,
            relations: verifier_relations,
            schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        },
        interaction_claim.folded_digit,
    );
    commitment_scheme.commit(proof.commitments[2], &sizes[2], &mut verifier_channel);

    verify(
        &[&verifier_component],
        &mut verifier_channel,
        commitment_scheme,
        proof,
    )
    .expect("folded digit component verifies");
}

fn prove_and_verify_projective_range13_provider(claim: &ProjectiveRcbAirTraceClaim) {
    let range13 = RangeCheckClaim::new(RANGE13_BITS);
    let ids = vec![crate::range_checks::range_check_value_column_id(
        RANGE13_BITS,
    )];
    let max_constraint_log_degree_bound =
        RangeCheckEval::new(RangeCheckRelation::dummy(), RANGE13_BITS)
            .max_constraint_log_degree_bound();
    let config = low_ram_proof_layer_config(max_constraint_log_degree_bound);
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(
            config
                .lifting_log_size
                .unwrap_or(max_constraint_log_degree_bound + config.fri_config.log_blowup_factor),
        )
        .circle_domain()
        .half_coset,
    );

    let mut channel = Blake2sChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);
    commitment_scheme.set_store_polynomials_coefficients();

    let values = range13.gen_preprocessed_column();
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(vec![values.clone()]);
    tree_builder.commit(&mut channel);

    let multiplicity = range13.gen_multiplicity_trace(claim.range13_lookup_values());
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(vec![multiplicity.clone()]);
    tree_builder.commit(&mut channel);

    let relation = RangeCheckRelation::draw(&mut channel);
    let (interaction, interaction_claim) =
        RangeCheckInteractionClaim::gen_interaction_trace(&multiplicity, &values, &relation);
    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let component = RangeCheckComponent::new(
        &mut allocator,
        RangeCheckEval::new(relation.clone(), RANGE13_BITS),
        interaction_claim.claimed_sum,
    );
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction);
    tree_builder.commit(&mut channel);

    let proof = prove(
        &[&component as &dyn ComponentProver<SimdBackend>],
        &mut channel,
        commitment_scheme,
    )
    .expect("projective range13 provider proves");

    let mut verifier_channel = Blake2sChannel::default();
    let commitment_scheme =
        &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(proof.config);
    let sizes = component.trace_log_degree_bounds();
    commitment_scheme.commit(proof.commitments[0], &sizes[0], &mut verifier_channel);
    commitment_scheme.commit(proof.commitments[1], &sizes[1], &mut verifier_channel);
    let verifier_relation = RangeCheckRelation::draw(&mut verifier_channel);
    let mut verifier_allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let verifier_component = RangeCheckComponent::new(
        &mut verifier_allocator,
        RangeCheckEval::new(verifier_relation, RANGE13_BITS),
        interaction_claim.claimed_sum,
    );
    commitment_scheme.commit(proof.commitments[2], &sizes[2], &mut verifier_channel);

    verify(
        &[&verifier_component],
        &mut verifier_channel,
        commitment_scheme,
        proof,
    )
    .expect("projective range13 provider verifies");
}

fn prove_and_verify_projective_signed_carry_provider(claim: &ProjectiveRcbAirTraceClaim) {
    let signed_carry = projective_rcb_signed_carry_claim();
    let eval = SignedCarryRangeEval::new(
        RangeCheckRelation::dummy(),
        projective_rcb_signed_carry_log_size(),
        PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
    );
    let ids = vec![eval.value_column_id(), eval.active_column_id()];
    let max_constraint_log_degree_bound = eval.max_constraint_log_degree_bound();
    let config = low_ram_proof_layer_config(max_constraint_log_degree_bound);
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(
            config
                .lifting_log_size
                .unwrap_or(max_constraint_log_degree_bound + config.fri_config.log_blowup_factor),
        )
        .circle_domain()
        .half_coset,
    );

    let mut channel = Blake2sChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);
    commitment_scheme.set_store_polynomials_coefficients();

    let values = signed_carry.gen_value_column();
    let active = signed_carry.gen_active_column();
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(vec![values.clone(), active]);
    tree_builder.commit(&mut channel);

    let multiplicity = signed_carry.gen_multiplicity_trace(
        claim
            .signed_carry_lookup_values()
            .expect("carry values fit"),
    );
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(vec![multiplicity.clone()]);
    tree_builder.commit(&mut channel);

    let relation = RangeCheckRelation::draw(&mut channel);
    let (interaction, interaction_claim) =
        RangeCheckInteractionClaim::gen_interaction_trace(&multiplicity, &values, &relation);
    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let component = SignedCarryRangeComponent::new(
        &mut allocator,
        SignedCarryRangeEval::new(
            relation.clone(),
            projective_rcb_signed_carry_log_size(),
            PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
        ),
        interaction_claim.claimed_sum,
    );
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction);
    tree_builder.commit(&mut channel);

    let proof = prove(
        &[&component as &dyn ComponentProver<SimdBackend>],
        &mut channel,
        commitment_scheme,
    )
    .expect("projective signed-carry provider proves");

    let mut verifier_channel = Blake2sChannel::default();
    let commitment_scheme =
        &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(proof.config);
    let sizes = component.trace_log_degree_bounds();
    commitment_scheme.commit(proof.commitments[0], &sizes[0], &mut verifier_channel);
    commitment_scheme.commit(proof.commitments[1], &sizes[1], &mut verifier_channel);
    let verifier_relation = RangeCheckRelation::draw(&mut verifier_channel);
    let mut verifier_allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let verifier_component = SignedCarryRangeComponent::new(
        &mut verifier_allocator,
        SignedCarryRangeEval::new(
            verifier_relation,
            projective_rcb_signed_carry_log_size(),
            PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
        ),
        interaction_claim.claimed_sum,
    );
    commitment_scheme.commit(proof.commitments[2], &sizes[2], &mut verifier_channel);

    verify(
        &[&verifier_component],
        &mut verifier_channel,
        commitment_scheme,
        proof,
    )
    .expect("projective signed-carry provider verifies");
}

fn prove_and_verify_projective_arithmetic_components(claim: &ProjectiveRcbAirTraceClaim) {
    let log_sizes = claim.component_log_sizes();
    let mut sizing_allocator = TraceLocationAllocator::default();
    let zero_claim = ProjectiveRcbAirComponentInteractionClaim {
        mul: SecureField::zero(),
        raw_product_chunk: SecureField::zero(),
        folded_contribution: SecureField::zero(),
        folded_digit: SecureField::zero(),
    };
    let dummy = ProjectiveRcbMulComponentRelations::dummy();
    let _sizing_mul = ProjectiveRcbMulComponent::new(
        &mut sizing_allocator,
        ProjectiveRcbMulEval {
            log_size: log_sizes.mul,
            relations: dummy.clone(),
        },
        zero_claim.mul,
    );
    let _sizing_raw = ProjectiveRcbRawProductChunkComponent::new(
        &mut sizing_allocator,
        ProjectiveRcbRawProductChunkEval {
            log_size: log_sizes.raw_product_chunk,
            relations: dummy.clone(),
            schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        },
        zero_claim.raw_product_chunk,
    );
    let _sizing_contribution = ProjectiveRcbFoldedContributionComponent::new(
        &mut sizing_allocator,
        ProjectiveRcbFoldedContributionEval {
            log_size: log_sizes.folded_contribution,
            relations: dummy.clone(),
            schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        },
        zero_claim.folded_contribution,
    );
    let _sizing_digit = ProjectiveRcbFoldedDigitComponent::new(
        &mut sizing_allocator,
        ProjectiveRcbFoldedDigitEval {
            log_size: log_sizes.folded_digit,
            relations: dummy,
            schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        },
        zero_claim.folded_digit,
    );
    let ids = sizing_allocator.preprocessed_columns().clone();
    let max_constraint_log_degree_bound = [
        _sizing_mul.max_constraint_log_degree_bound(),
        _sizing_raw.max_constraint_log_degree_bound(),
        _sizing_contribution.max_constraint_log_degree_bound(),
        _sizing_digit.max_constraint_log_degree_bound(),
    ]
    .into_iter()
    .max()
    .expect("arithmetic components exist");
    let config = low_ram_proof_layer_config(max_constraint_log_degree_bound);
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(
            config
                .lifting_log_size
                .unwrap_or(max_constraint_log_degree_bound + config.fri_config.log_blowup_factor),
        )
        .circle_domain()
        .half_coset,
    );

    let mut channel = Blake2sChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);
    commitment_scheme.set_store_polynomials_coefficients();

    let preprocessed = claim
        .gen_proof_slice_preprocessed_trace(&ids)
        .expect("arithmetic preprocessed trace generates");
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(preprocessed);
    tree_builder.commit(&mut channel);

    let mut base = Vec::new();
    base.extend(gen_projective_rcb_mul_base_trace(claim, log_sizes.mul).expect("mul base"));
    base.extend(
        gen_projective_rcb_raw_product_chunk_base_trace(claim, log_sizes.raw_product_chunk)
            .expect("raw base"),
    );
    base.extend(
        gen_projective_rcb_folded_contribution_base_trace(claim, log_sizes.folded_contribution)
            .expect("contribution base"),
    );
    base.extend(
        gen_projective_rcb_folded_digit_base_trace(claim, log_sizes.folded_digit)
            .expect("digit base"),
    );
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(base);
    tree_builder.commit(&mut channel);

    let relations = ProjectiveRcbMulComponentRelations::draw(&mut channel);
    let (interaction_traces, interaction_claim) = claim.gen_interaction_trace(&relations);
    let mut interaction = Vec::new();
    interaction.extend(interaction_traces.mul);
    interaction.extend(interaction_traces.raw_product_chunk);
    interaction.extend(interaction_traces.folded_contribution);
    interaction.extend(interaction_traces.folded_digit);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction);
    tree_builder.commit(&mut channel);

    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let mul = ProjectiveRcbMulComponent::new(
        &mut allocator,
        ProjectiveRcbMulEval {
            log_size: log_sizes.mul,
            relations: relations.clone(),
        },
        interaction_claim.mul,
    );
    let raw = ProjectiveRcbRawProductChunkComponent::new(
        &mut allocator,
        ProjectiveRcbRawProductChunkEval {
            log_size: log_sizes.raw_product_chunk,
            relations: relations.clone(),
            schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        },
        interaction_claim.raw_product_chunk,
    );
    let contribution = ProjectiveRcbFoldedContributionComponent::new(
        &mut allocator,
        ProjectiveRcbFoldedContributionEval {
            log_size: log_sizes.folded_contribution,
            relations: relations.clone(),
            schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        },
        interaction_claim.folded_contribution,
    );
    let digit = ProjectiveRcbFoldedDigitComponent::new(
        &mut allocator,
        ProjectiveRcbFoldedDigitEval {
            log_size: log_sizes.folded_digit,
            relations,
            schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        },
        interaction_claim.folded_digit,
    );
    let proof = prove(
        &[
            &mul as &dyn ComponentProver<SimdBackend>,
            &raw as &dyn ComponentProver<SimdBackend>,
            &contribution as &dyn ComponentProver<SimdBackend>,
            &digit as &dyn ComponentProver<SimdBackend>,
        ],
        &mut channel,
        commitment_scheme,
    )
    .expect("projective arithmetic components prove");
    drop(proof);
}

#[test]
fn projective_rcb_air_rows_verify_double() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");

    claim
        .verify_against_projective_trace(&trace)
        .expect("claim verifies");
    assert_eq!(claim.active_row_count(), 1);
    assert_eq!(claim.mul_row_count(), PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP);
    assert_eq!(
        claim.raw_product_chunk_count(),
        PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP * PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS
    );
    assert_eq!(
        claim.folded_digit_row_count(),
        PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP * FP_SOLINAS_REDUCTION_DIGITS
    );
    assert_eq!(
        claim.folded_contribution_row_count(),
        PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP * PROJECTIVE_RCB_FOLDED_CONTRIBUTION_ROWS
    );
    assert_eq!(
        claim.reduction_row_count(),
        PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP * FP_SOLINAS_REDUCTION_DIGITS
    );
    claim
        .internal_interaction_claim(&ProjectiveRcbMulComponentRelations::dummy())
        .verify_balanced()
        .expect("internal relations balance");
}

#[test]
fn projective_rcb_air_rows_verify_mixed_add() {
    let g = generator();
    let rhs = PreparedAffinePoint::from_affine(point_double(&g.to_option().unwrap()).output);
    let trace = one_row_trace(ProjectiveEcOp::MixedAdd, rhs);
    let claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");

    claim
        .verify_against_projective_trace(&trace)
        .expect("claim verifies");
    assert_eq!(claim.active_row_count(), 1);
    assert_eq!(claim.mul_row_count(), PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP);
}

#[test]
fn projective_rcb_air_rows_skip_operand_infinity_mixed_add() {
    let lhs = generator();
    let output = lhs.clone();
    let trace = ProjectiveEcTraceClaim {
        rows: vec![ProjectiveEcRow::new(
            M31::from_u32_unchecked(0),
            M31::from_u32_unchecked(0),
            ProjectiveEcOp::MixedAdd,
            &lhs,
            &PreparedAffinePoint::infinity(),
            &output,
        )],
    };
    let claim = ProjectiveRcbAirTraceClaim::from_projective_trace(&trace)
        .expect("valid infinity-add RCB AIR trace");

    claim
        .verify_against_projective_trace(&trace)
        .expect("claim verifies");
    assert_eq!(claim.mul_row_count(), 0);
}

#[test]
fn projective_rcb_air_rows_detect_mutated_reduction_digit() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let mut claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
    claim.rows[0].muls[0].reduction.rows[0].folded_digit ^= 1;

    let err = claim
        .verify_against_projective_trace(&trace)
        .expect_err("mutated reduction row must fail");

    assert!(matches!(
        err,
        ProjectiveRcbAirError::FpSolinasReduction(
            FpSolinasReductionTraceError::TraceRowsMismatch
                | FpSolinasReductionTraceError::ReductionEquationMismatch { .. }
        ) | ProjectiveRcbAirError::FoldedReductionDigitMismatch { .. }
    ));
}

#[test]
fn projective_rcb_air_rows_detect_mutated_raw_product_digit() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let mut claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
    claim.rows[0].muls[0].raw_product_chunks[0].digits[0] ^= 1;

    let err = claim
        .verify_against_projective_trace(&trace)
        .expect_err("mutated raw product chunk must fail");

    assert!(matches!(
        err,
        ProjectiveRcbAirError::RawProductChunkDigitMismatch { .. }
            | ProjectiveRcbAirError::RawProductChunkMismatch { .. }
    ));
    assert!(matches!(
        claim
            .internal_interaction_claim(&ProjectiveRcbMulComponentRelations::dummy())
            .verify_balanced()
            .expect_err("mutated relation tuple must imbalance"),
        ProjectiveRcbAirError::RelationImbalance {
            relation: "ProjectiveRcbRawProductChunkDigit"
        }
    ));
}

#[test]
fn projective_rcb_air_rows_detect_mutated_raw_product_schedule_metadata() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let mut claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
    claim.rows[0].muls[0].raw_product_chunks[0].digit_use_counts[0] += 1;

    let err = claim
        .verify_against_projective_trace(&trace)
        .expect_err("mutated raw product schedule metadata must fail");

    assert!(matches!(
        err,
        ProjectiveRcbAirError::RawProductChunkUseCountMismatch { .. }
            | ProjectiveRcbAirError::RawProductChunkMismatch { .. }
    ));
}

#[test]
fn projective_rcb_air_rows_detect_mutated_folded_digit() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let mut claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
    claim.rows[0].muls[0].folded_digits.rows[0].folded_digit ^= 1;

    let err = claim
        .verify_against_projective_trace(&trace)
        .expect_err("mutated folded digit must fail");

    assert!(matches!(
        err,
        ProjectiveRcbAirError::FoldedDigitMismatch
            | ProjectiveRcbAirError::FoldedDigitEquationMismatch { .. }
            | ProjectiveRcbAirError::FoldedReductionDigitMismatch { .. }
    ));
}

#[test]
fn projective_rcb_air_rows_detect_mutated_folded_digit_contribution_group() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let mut claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
    claim.rows[0].muls[0].folded_digits.rows[0].contribution_groups[0].contribution_sum += 1;

    let err = claim
        .verify_against_projective_trace(&trace)
        .expect_err("mutated folded digit contribution group must fail");

    assert!(matches!(
        err,
        ProjectiveRcbAirError::FoldedDigitContributionSumMismatch { .. }
            | ProjectiveRcbAirError::FoldedDigitMismatch
    ));
}

#[test]
fn projective_rcb_air_rows_detect_mutated_folded_digit_schedule_metadata() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let mut claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
    claim.rows[0].muls[0].folded_digits.rows[0].contribution_groups[0].group_index += 1;

    let err = claim
        .verify_against_projective_trace(&trace)
        .expect_err("mutated folded digit schedule metadata must fail");

    assert!(matches!(
        err,
        ProjectiveRcbAirError::FoldedDigitMismatch
            | ProjectiveRcbAirError::FoldedDigitContributionSumMismatch { .. }
    ));
}

#[test]
fn projective_rcb_air_rows_detect_mutated_folded_contribution() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let mut claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
    claim.rows[0].muls[0].folded_contributions.rows[0].contribution_sum += 1;

    let err = claim
        .verify_against_projective_trace(&trace)
        .expect_err("mutated folded contribution row must fail");

    assert!(matches!(
        err,
        ProjectiveRcbAirError::FoldedContributionMismatch
            | ProjectiveRcbAirError::FoldedContributionSumMismatch { .. }
            | ProjectiveRcbAirError::FoldedDigitMismatch
            | ProjectiveRcbAirError::FoldedDigitEquationMismatch { .. }
    ));
}

#[test]
fn projective_rcb_air_rows_detect_mutated_folded_contribution_schedule_metadata() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let mut claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
    claim.rows[0].muls[0].folded_contributions.rows[0].terms[0].matrix_coeff += 1;

    let err = claim
        .verify_against_projective_trace(&trace)
        .expect_err("mutated folded contribution schedule metadata must fail");

    assert!(matches!(
        err,
        ProjectiveRcbAirError::FoldedContributionMismatch
            | ProjectiveRcbAirError::FoldedContributionSumMismatch { .. }
            | ProjectiveRcbAirError::FoldedDigitMismatch
            | ProjectiveRcbAirError::FoldedDigitEquationMismatch { .. }
    ));
}

#[test]
fn projective_rcb_air_rows_detect_mutated_projective_output() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let mut claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
    claim.rows[0].output_projective.x = crate::limbs::P256M31BigInt::zero();

    let err = claim
        .verify_against_projective_trace(&trace)
        .expect_err("mutated output must fail");

    assert!(matches!(
        err,
        ProjectiveRcbAirError::TraceRowsMismatch { .. }
            | ProjectiveRcbAirError::Projective(ProjectiveEcError::InvalidProjectiveInfinity)
    ));
}

#[test]
fn projective_rcb_mul_eval_allocates_expected_width() {
    let mut allocator = TraceLocationAllocator::default();
    let component = ProjectiveRcbMulComponent::new(
        &mut allocator,
        ProjectiveRcbMulEval {
            log_size: 6,
            relations: ProjectiveRcbMulComponentRelations::dummy(),
        },
        SecureField::zero(),
    );

    assert_eq!(
        PROJECTIVE_RCB_MUL_TRACE_COLUMNS,
        1 + 2
            + 3 * N_LIMBS
            + 1
            + 5 * FP_SOLINAS_REDUCTION_DIGITS
            + PROJECTIVE_RCB_MUL_CORRECTION_DIGIT_TRACE_COLUMNS
    );
    assert_eq!(
        component.trace_log_degree_bounds()[1].len(),
        PROJECTIVE_RCB_MUL_TRACE_COLUMNS
    );
    assert_eq!(PROJECTIVE_RCB_MUL_LIMB_RELATION_ARITY, 5);
    assert_eq!(PROJECTIVE_RCB_FOLDED_DIGIT_RELATION_ARITY, 4);
    assert_eq!(PROJECTIVE_RCB_FOLDED_CARRY_RELATION_ARITY, 4);
    assert_eq!(
        ProjectiveRcbMulEval {
            log_size: 6,
            relations: ProjectiveRcbMulComponentRelations::dummy(),
        }
        .max_constraint_log_degree_bound(),
        7
    );
}

#[test]
fn projective_rcb_raw_product_chunk_constraints_fit_m31_for_admitted_ranges() {
    assert!(
        projective_rcb_raw_product_chunk_fits_m31(),
        "raw-product chunk equations must fit M31 under admitted witness ranges"
    );
}

#[test]
fn projective_rcb_raw_product_chunk_wrapped_reconstruction_exceeds_raw_carry_range() {
    let limb_base = FP_SOLINAS_LIMB_BASE;
    let product_sum = PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS as i128 * (limb_base - 1).pow(2);
    let wrapped_reconstruction = product_sum + ((1i128 << 31) - 1);
    let low_digit = wrapped_reconstruction % limb_base;
    let first_carry = (wrapped_reconstruction - low_digit) / limb_base;

    assert!(
        first_carry >= (1i128 << 16),
        "a one-modulus wrapped reconstruction must not fit the raw carry range"
    );
}

#[test]
fn projective_rcb_raw_product_chunk_eval_allocates_expected_width() {
    let mut allocator = TraceLocationAllocator::default();
    let component = ProjectiveRcbRawProductChunkComponent::new(
        &mut allocator,
        ProjectiveRcbRawProductChunkEval {
            log_size: 8,
            relations: ProjectiveRcbMulComponentRelations::dummy(),
            schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        },
        SecureField::zero(),
    );

    assert_eq!(PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS, 8);
    assert_eq!(PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS, 69);
    assert_eq!(
        PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS,
        1 + 2 + PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS * 4 + 1 + 3 + 3
    );
    assert_eq!(
        component.trace_log_degree_bounds()[1].len(),
        PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS
    );
    assert!(allocator.preprocessed_columns().contains(
        &ProjectiveRcbRawProductChunkScheduleColumnIds::coeff(PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC)
    ));
    assert!(allocator.preprocessed_columns().contains(
        &ProjectiveRcbRawProductChunkScheduleColumnIds::digit_use_count(
            PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
            2
        )
    ));
    assert_eq!(PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGIT_RELATION_ARITY, 6);
    assert!(projective_rcb_raw_product_chunk_fits_m31());
    assert_eq!(
        ProjectiveRcbRawProductChunkEval {
            log_size: 8,
            relations: ProjectiveRcbMulComponentRelations::dummy(),
            schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        }
        .max_constraint_log_degree_bound(),
        9
    );
}

#[test]
fn projective_rcb_raw_product_chunk_schedule_columns_match_fixed_rows() {
    let columns = projective_rcb_raw_product_chunk_schedule_columns();
    let log_size = padded_log_size(PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS);
    let row_count = 1usize << log_size;

    assert_eq!(
        columns.len(),
        3 + 3 * PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS + 3
    );
    assert!(columns
        .iter()
        .all(|column| column.values.len() == row_count));
    assert_eq!(
        columns[0].values[..PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS]
            .iter()
            .filter(|&&value| value == m31(1))
            .count(),
        PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS
    );
    assert_eq!(columns[1].values[0], m31(0));
    assert_eq!(columns[2].values[0], m31(0));
    assert_eq!(
        columns[1].values[PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS - 1],
        m31_usize(FP_SOLINAS_RAW_LIMBS - 1)
    );
    assert_eq!(
        projective_rcb_raw_product_chunk_schedule_evals().len(),
        columns.len()
    );
}

#[test]
fn projective_rcb_folded_contribution_eval_allocates_expected_width() {
    let mut allocator = TraceLocationAllocator::default();
    let component = ProjectiveRcbFoldedContributionComponent::new(
        &mut allocator,
        ProjectiveRcbFoldedContributionEval {
            log_size: 9,
            relations: ProjectiveRcbMulComponentRelations::dummy(),
            schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        },
        SecureField::zero(),
    );

    assert_eq!(
        PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TRACE_COLUMNS,
        1 + 2 + 4 * 4 + 1
    );
    assert_eq!(
        component.trace_log_degree_bounds()[1].len(),
        PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TRACE_COLUMNS
    );
    assert!(allocator.preprocessed_columns().contains(
        &ProjectiveRcbFoldedContributionScheduleColumnIds::active(
            PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC
        )
    ));
    assert!(allocator.preprocessed_columns().contains(
        &ProjectiveRcbFoldedContributionScheduleColumnIds::matrix_coeff(
            PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
            3
        )
    ));
    assert_eq!(PROJECTIVE_RCB_FOLDED_CONTRIBUTION_RELATION_ARITY, 5);
    assert!(projective_rcb_folded_contribution_fits_m31());
    assert_eq!(
        ProjectiveRcbFoldedContributionEval {
            log_size: 9,
            relations: ProjectiveRcbMulComponentRelations::dummy(),
            schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        }
        .max_constraint_log_degree_bound(),
        10
    );
}

#[test]
fn projective_rcb_folded_contribution_schedule_columns_match_fixed_rows() {
    let columns = projective_rcb_folded_contribution_schedule_columns();
    let log_size = padded_log_size(PROJECTIVE_RCB_FOLDED_CONTRIBUTION_ROWS);
    let row_count = 1usize << log_size;
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
    let fixed_rows = &claim.rows[0].muls[0].folded_contributions.rows;

    assert_eq!(
        columns.len(),
        3 + 5 * PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS
    );
    assert!(columns
        .iter()
        .all(|column| column.values.len() == row_count));
    assert_eq!(
        columns[0].values[..PROJECTIVE_RCB_FOLDED_CONTRIBUTION_ROWS]
            .iter()
            .filter(|&&value| value == m31(1))
            .count(),
        PROJECTIVE_RCB_FOLDED_CONTRIBUTION_ROWS
    );
    assert_eq!(columns[1].values[0], m31(0));
    assert_eq!(columns[2].values[0], m31(0));
    assert_eq!(
        columns[1].values[PROJECTIVE_RCB_FOLDED_CONTRIBUTION_ROWS - 1],
        m31_usize(FP_SOLINAS_REDUCTION_DIGITS - 1)
    );
    assert_eq!(fixed_rows.len(), PROJECTIVE_RCB_FOLDED_CONTRIBUTION_ROWS);
    for (row_index, row) in fixed_rows.iter().enumerate() {
        assert_eq!(columns[0].values[row_index], m31(1));
        assert_eq!(columns[1].values[row_index], m31_usize(row.digit_index));
        assert_eq!(columns[2].values[row_index], m31_usize(row.group_index));
        for (term_index, term) in row.terms.iter().enumerate() {
            let base = 3 + 5 * term_index;
            assert_eq!(columns[base].values[row_index], m31(u32::from(term.active)));
            assert_eq!(
                columns[base + 1].values[row_index],
                m31_usize(term.raw_coeff)
            );
            assert_eq!(
                columns[base + 2].values[row_index],
                m31_usize(term.raw_chunk)
            );
            assert_eq!(
                columns[base + 3].values[row_index],
                m31_usize(term.raw_offset)
            );
            assert_eq!(
                columns[base + 4].values[row_index],
                m31_i128(i128::from(term.matrix_coeff))
            );
        }
    }
    assert_eq!(
        projective_rcb_folded_contribution_schedule_evals().len(),
        columns.len()
    );
}

#[test]
fn projective_rcb_folded_digit_eval_allocates_expected_width() {
    let mut allocator = TraceLocationAllocator::default();
    let component = ProjectiveRcbFoldedDigitComponent::new(
        &mut allocator,
        ProjectiveRcbFoldedDigitEval {
            log_size: 9,
            relations: ProjectiveRcbMulComponentRelations::dummy(),
            schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        },
        SecureField::zero(),
    );

    assert_eq!(PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS, 10);
    assert_eq!(
        PROJECTIVE_RCB_FOLDED_DIGIT_TRACE_COLUMNS,
        1 + 2 + PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS * 3 + 3
    );
    assert_eq!(
        component.trace_log_degree_bounds()[1].len(),
        PROJECTIVE_RCB_FOLDED_DIGIT_TRACE_COLUMNS
    );
    assert!(allocator.preprocessed_columns().contains(
        &ProjectiveRcbFoldedDigitScheduleColumnIds::active(PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC)
    ));
    assert!(allocator.preprocessed_columns().contains(
        &ProjectiveRcbFoldedDigitScheduleColumnIds::group_index(
            PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
            PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS - 1
        )
    ));
    assert_eq!(PROJECTIVE_RCB_FOLDED_DIGIT_RELATION_ARITY, 4);
    assert_eq!(PROJECTIVE_RCB_FOLDED_CARRY_RELATION_ARITY, 4);
    assert!(projective_rcb_folded_digit_contribution_sum_fits_m31());
    assert_eq!(
        ProjectiveRcbFoldedDigitEval {
            log_size: 9,
            relations: ProjectiveRcbMulComponentRelations::dummy(),
            schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        }
        .max_constraint_log_degree_bound(),
        10
    );
}

#[test]
fn projective_rcb_folded_digit_schedule_columns_match_fixed_rows() {
    let columns = projective_rcb_folded_digit_schedule_columns();
    let log_size = padded_log_size(FP_SOLINAS_REDUCTION_DIGITS);
    let row_count = 1usize << log_size;
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
    let fixed_rows = &claim.rows[0].muls[0].folded_digits.rows;

    assert_eq!(columns.len(), 2 + 2 * PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS);
    assert!(columns
        .iter()
        .all(|column| column.values.len() == row_count));
    assert_eq!(
        columns[0].values[..FP_SOLINAS_REDUCTION_DIGITS]
            .iter()
            .filter(|&&value| value == m31(1))
            .count(),
        FP_SOLINAS_REDUCTION_DIGITS
    );
    assert_eq!(columns[1].values[0], m31(0));
    assert_eq!(
        columns[1].values[FP_SOLINAS_REDUCTION_DIGITS - 1],
        m31_usize(FP_SOLINAS_REDUCTION_DIGITS - 1)
    );
    assert_eq!(fixed_rows.len(), FP_SOLINAS_REDUCTION_DIGITS);
    for (row_index, row) in fixed_rows.iter().enumerate() {
        assert_eq!(columns[0].values[row_index], m31(1));
        assert_eq!(columns[1].values[row_index], m31_usize(row.digit_index));
        for (group_index, group) in row.contribution_groups.iter().enumerate() {
            let base = 2 + 2 * group_index;
            assert_eq!(
                columns[base].values[row_index],
                m31(u32::from(group.active))
            );
            assert_eq!(
                columns[base + 1].values[row_index],
                m31_usize(group.group_index)
            );
        }
    }
    assert_eq!(
        projective_rcb_folded_digit_schedule_evals().len(),
        columns.len()
    );
}

#[test]
fn projective_rcb_air_preprocessed_trace_uses_global_claim_sizes() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
    let ids = claim.preprocessed_column_ids();
    let preprocessed = claim
        .gen_preprocessed_trace(&ids)
        .expect("registered schedule columns generate");
    let log_sizes = claim.component_log_sizes();

    assert_eq!(
        ids.len(),
        (3 + 3 * PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS + 3)
            + (3 + 5 * PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS)
            + (2 + 2 * PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS)
    );
    assert_eq!(preprocessed.len(), ids.len());
    assert_eq!(
        preprocessed[0].domain.log_size(),
        log_sizes.raw_product_chunk
    );
    assert_eq!(
        preprocessed[3 + 3 * PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS + 3]
            .domain
            .log_size(),
        log_sizes.folded_contribution
    );
    assert_eq!(
        preprocessed[(3 + 3 * PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS + 3)
            + (3 + 5 * PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS)]
            .domain
            .log_size(),
        log_sizes.folded_digit
    );
    assert!(
        ids.contains(&ProjectiveRcbRawProductChunkScheduleColumnIds::coeff(
            PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC
        ))
    );
    assert!(ids.contains(
        &ProjectiveRcbFoldedContributionScheduleColumnIds::matrix_coeff(
            PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
            3
        )
    ));
    assert!(
        ids.contains(&ProjectiveRcbFoldedDigitScheduleColumnIds::group_index(
            PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
            PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS - 1,
        ))
    );
    claim
        .verify_preprocessed_trace()
        .expect("full schedule preprocessed trace verifies");
}

#[test]
fn projective_rcb_air_preprocessed_trace_rejects_unknown_column_id() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
    let err = claim
        .gen_preprocessed_trace(&[PreProcessedColumnId {
            id: "p256_projective_rcb_missing".to_string(),
        }])
        .expect_err("unknown preprocessed column must fail");

    assert!(matches!(
        err,
        ProjectiveRcbAirError::PreprocessedColumnMissing { .. }
    ));
}

#[test]
fn projective_rcb_air_base_trace_materializes_component_columns() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
    let base = claim.gen_base_trace().expect("base trace materializes");
    let log_sizes = claim.component_log_sizes();
    let raw_start = PROJECTIVE_RCB_MUL_TRACE_COLUMNS;
    let folded_contribution_start = raw_start + PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS;
    let folded_digit_start =
        folded_contribution_start + PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TRACE_COLUMNS;

    assert_eq!(
        base.len(),
        PROJECTIVE_RCB_MUL_TRACE_COLUMNS
            + PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS
            + PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TRACE_COLUMNS
            + PROJECTIVE_RCB_FOLDED_DIGIT_TRACE_COLUMNS
    );
    assert_eq!(base[0].domain.log_size(), log_sizes.mul);
    assert_eq!(
        base[raw_start].domain.log_size(),
        log_sizes.raw_product_chunk
    );
    assert_eq!(
        base[folded_contribution_start].domain.log_size(),
        log_sizes.folded_contribution
    );
    assert_eq!(
        base[folded_digit_start].domain.log_size(),
        log_sizes.folded_digit
    );
    assert_eq!(
        base[0]
            .to_cpu()
            .iter()
            .filter(|&&value| value == m31(1))
            .count(),
        claim.mul_row_count()
    );
    claim
        .verify_base_trace()
        .expect("base trace shape verifies");
}

#[test]
fn projective_rcb_air_interaction_trace_materializes_paired_logup_columns() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
    let relations = ProjectiveRcbMulComponentRelations::dummy();
    let (traces, interaction_claim) = claim.gen_interaction_trace(&relations);
    let log_sizes = claim.component_log_sizes();

    assert_eq!(traces.mul.len(), projective_rcb_mul_interaction_columns());
    assert_eq!(
        traces.raw_product_chunk.len(),
        projective_rcb_raw_product_chunk_interaction_columns()
    );
    assert_eq!(
        traces.folded_contribution.len(),
        projective_rcb_folded_contribution_interaction_columns()
    );
    assert_eq!(
        traces.folded_digit.len(),
        projective_rcb_folded_digit_interaction_columns()
    );
    assert!(traces
        .mul
        .iter()
        .all(|column| column.domain.log_size() == log_sizes.mul));
    assert!(traces
        .raw_product_chunk
        .iter()
        .all(|column| column.domain.log_size() == log_sizes.raw_product_chunk));
    assert!(traces
        .folded_contribution
        .iter()
        .all(|column| column.domain.log_size() == log_sizes.folded_contribution));
    assert!(traces
        .folded_digit
        .iter()
        .all(|column| column.domain.log_size() == log_sizes.folded_digit));
    assert_ne!(interaction_claim.total(), secure_zero());
    claim
        .verify_interaction_trace(&relations)
        .expect("interaction trace shape verifies");
}

#[test]
fn projective_rcb_air_range_lookup_consumers_balance_with_providers() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
    let relations = ProjectiveRcbMulComponentRelations::dummy();

    let range13_values = claim.range13_lookup_values();
    assert_eq!(
        range13_values.len(),
        claim.mul_row_count()
            * (3 * N_LIMBS
                + 2 * FP_SOLINAS_REDUCTION_DIGITS
                + crate::fp_solinas::FP_SOLINAS_SIGNED_CORRECTION_LIMBS
                + PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS * PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS
                + FP_SOLINAS_REDUCTION_DIGITS)
    );
    let range13 = RangeCheckClaim::new(RANGE13_BITS);
    let range13_preprocessed = range13.gen_preprocessed_column();
    let range13_multiplicity = range13.gen_multiplicity_trace(range13_values);
    let (_, range13_provider) =
        crate::range_checks::RangeCheckInteractionClaim::gen_interaction_trace(
            &range13_multiplicity,
            &range13_preprocessed,
            &relations.range13,
        );
    assert_eq!(
        range13_provider.claimed_sum + claim.range13_consumer_claimed_sum(&relations.range13),
        secure_zero()
    );

    let raw_product_carry16_values = claim.raw_product_carry16_lookup_values();
    assert_eq!(
        raw_product_carry16_values.len(),
        claim.mul_row_count() * PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS
    );
    let range16 = RangeCheckClaim::new(RANGE16_BITS);
    let range16_preprocessed = range16.gen_preprocessed_column();
    let range16_multiplicity = range16.gen_multiplicity_trace(raw_product_carry16_values);
    let (_, range16_provider) =
        crate::range_checks::RangeCheckInteractionClaim::gen_interaction_trace(
            &range16_multiplicity,
            &range16_preprocessed,
            &relations.raw_product_carry16,
        );
    assert_eq!(
        range16_provider.claimed_sum
            + claim.raw_product_carry16_consumer_claimed_sum(&relations.raw_product_carry16),
        secure_zero()
    );

    let signed_carry_values = claim
        .signed_carry_lookup_values()
        .expect("signed carries fit fixed bound");
    assert_eq!(
        signed_carry_values.len(),
        claim.mul_row_count() * 4 * FP_SOLINAS_REDUCTION_DIGITS
    );
    let max_abs = signed_carry_values
        .iter()
        .map(|value| value.abs())
        .max()
        .unwrap_or_default();
    assert!(max_abs <= PROJECTIVE_RCB_SIGNED_CARRY_BOUND);
    let signed_carry = SignedCarryRangeClaim::new(
        projective_rcb_signed_carry_log_size(),
        PROJECTIVE_RCB_SIGNED_CARRY_BOUND,
        PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
    );
    let signed_carry_preprocessed = signed_carry.gen_value_column();
    let signed_carry_multiplicity = signed_carry.gen_multiplicity_trace(signed_carry_values);
    let (_, signed_carry_provider) =
        crate::range_checks::RangeCheckInteractionClaim::gen_interaction_trace(
            &signed_carry_multiplicity,
            &signed_carry_preprocessed,
            &relations.signed_carry,
        );
    assert_eq!(
        signed_carry_provider.claimed_sum
            + claim
                .signed_carry_consumer_claimed_sum(&relations.signed_carry)
                .expect("signed carry consumer sum generates"),
        secure_zero()
    );
}

#[test]
fn projective_rcb_air_proof_slice_materializes_registered_traces() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
    let relations = ProjectiveRcbMulComponentRelations::dummy();
    let ids = claim.proof_slice_preprocessed_column_ids(&relations);
    let preprocessed = claim
        .gen_proof_slice_preprocessed_trace(&ids)
        .expect("proof preprocessed trace generates");
    let base = claim
        .gen_proof_slice_base_trace()
        .expect("proof base trace generates");
    let (interaction, interaction_claim) = claim
        .gen_proof_slice_interaction_trace(&relations)
        .expect("proof interaction trace generates");
    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let components =
        ProjectiveRcbAirComponents::new(&mut allocator, &claim, &interaction_claim, &relations);

    assert!(
        ids.contains(&crate::range_checks::range_check_value_column_id(
            RANGE13_BITS
        ))
    );
    assert!(
        ids.contains(&crate::range_checks::range_check_value_column_id(
            RANGE16_BITS
        ))
    );
    assert!(
        ids.contains(&crate::range_checks::signed_carry_value_column_id(
            PROJECTIVE_RCB_SIGNED_CARRY_EQUATION
        ))
    );
    assert!(
        ids.contains(&crate::range_checks::signed_carry_active_column_id(
            PROJECTIVE_RCB_SIGNED_CARRY_EQUATION
        ))
    );
    assert_eq!(preprocessed.len(), ids.len());
    let component_bounds = components.trace_log_degree_bounds();
    assert_eq!(preprocessed.len(), component_bounds.0[0].len());
    assert_eq!(base.len(), component_bounds.0[1].len());
    assert_eq!(interaction.len(), component_bounds.0[2].len());
    assert_eq!(
        base.len(),
        PROJECTIVE_RCB_MUL_TRACE_COLUMNS
            + PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS
            + PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TRACE_COLUMNS
            + PROJECTIVE_RCB_FOLDED_DIGIT_TRACE_COLUMNS
            + 3
    );
    assert_eq!(interaction_claim.total(), secure_zero());
    assert!(!interaction.is_empty());
    assert_eq!(components.mul.log_size(), claim.component_log_sizes().mul);
    assert_eq!(
        components.raw_product_chunk.log_size(),
        claim.component_log_sizes().raw_product_chunk
    );
    assert_eq!(components.range13.log_size(), RANGE13_BITS);
    assert_eq!(components.raw_product_carry16.log_size(), RANGE16_BITS);
    assert_eq!(
        components.signed_carry.log_size(),
        projective_rcb_signed_carry_log_size()
    );
    claim
        .verify_proof_slice_traces(&relations)
        .expect("proof slice trace shape verifies");
}

#[test]
fn projective_rcb_arithmetic_components_prove_together() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");

    prove_and_verify_projective_arithmetic_components(&claim);
}

#[test]
fn projective_rcb_mul_component_proves_and_verifies() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");

    prove_and_verify_mul_component(&claim);
}

#[test]
fn projective_rcb_folded_contribution_component_proves_and_verifies() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");

    prove_and_verify_folded_contribution_component(&claim);
}

#[test]
fn projective_rcb_folded_digit_component_proves_and_verifies() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");

    prove_and_verify_folded_digit_component(&claim);
}

#[test]
fn projective_rcb_range13_provider_proves_and_verifies() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");

    prove_and_verify_projective_range13_provider(&claim);
}

#[test]
fn projective_rcb_signed_carry_provider_proves_and_verifies() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");

    prove_and_verify_projective_signed_carry_provider(&claim);
}

#[test]
fn projective_rcb_raw_product_chunk_component_proves_and_verifies() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");

    prove_and_verify_raw_product_chunk_component(&claim);
}
