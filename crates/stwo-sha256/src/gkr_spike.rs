//! Feature-gated WO-S1 helpers for proving the SHA `xor_8` lookup relation
//! with Stwo's GKR LogUp argument.
//!
//! This module is intentionally SHA-local. The default LogUp path does not
//! import or call it unless `gkr-spike` is enabled.

use num_traits::Zero;
use stwo::core::channel::Channel;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::fields::FieldExpOps;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::lookups::gkr_prover::{prove_batch, Layer};
use stwo::prover::lookups::gkr_verifier::{
    partially_verify_batch, Gate, GkrArtifact, GkrBatchProof, GkrError,
};
use stwo::prover::lookups::mle::Mle;
use stwo::prover::lookups::sumcheck::SumcheckProof;
use stwo::prover::lookups::utils::UnivariatePoly;
use stwo_constraint_framework::Relation;

use crate::multiplicities::xor_8_multiplicities;
use crate::preprocessed::LOG_SIZE_16;
use crate::relations::Sha256Relations;
use crate::tables::build_xor_8_table;
use crate::types::Sha256Witness;

pub const XOR_8_GKR_INSTANCE_COUNT: usize = 1;

pub struct Xor8GkrProof {
    pub proof: GkrBatchProof,
    pub artifact: GkrArtifact,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Xor8GkrProofWire {
    pub sumcheck_round_polys: Vec<Vec<Vec<SecureField>>>,
    pub layer_masks_by_instance: Vec<Vec<Vec<[SecureField; 2]>>>,
    pub output_claims_by_instance: Vec<Vec<SecureField>>,
}

impl From<&GkrBatchProof> for Xor8GkrProofWire {
    fn from(proof: &GkrBatchProof) -> Self {
        Self {
            sumcheck_round_polys: proof
                .sumcheck_proofs
                .iter()
                .map(|sumcheck| {
                    sumcheck
                        .round_polys
                        .iter()
                        .map(|poly| poly.iter().copied().collect())
                        .collect()
                })
                .collect(),
            layer_masks_by_instance: proof
                .layer_masks_by_instance
                .iter()
                .map(|instance| {
                    instance
                        .iter()
                        .map(|mask| mask.columns().to_vec())
                        .collect()
                })
                .collect(),
            output_claims_by_instance: proof.output_claims_by_instance.clone(),
        }
    }
}

impl From<Xor8GkrProofWire> for GkrBatchProof {
    fn from(wire: Xor8GkrProofWire) -> Self {
        Self {
            sumcheck_proofs: wire
                .sumcheck_round_polys
                .into_iter()
                .map(|round_polys| SumcheckProof {
                    round_polys: round_polys.into_iter().map(UnivariatePoly::new).collect(),
                })
                .collect(),
            layer_masks_by_instance: wire
                .layer_masks_by_instance
                .into_iter()
                .map(|instance| {
                    instance
                        .into_iter()
                        .map(stwo::prover::lookups::gkr_verifier::GkrMask::new)
                        .collect()
                })
                .collect(),
            output_claims_by_instance: wire.output_claims_by_instance,
        }
    }
}

pub fn prove_xor_8_gkr(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    log_n_rows: u32,
    channel: &mut impl Channel,
) -> Xor8GkrProof {
    let layers = xor_8_layers(relations, witness, log_n_rows);
    let (proof, artifact) = prove_batch(channel, layers);
    Xor8GkrProof { proof, artifact }
}

pub fn verify_xor_8_gkr(
    proof: &GkrBatchProof,
    channel: &mut impl Channel,
) -> Result<GkrArtifact, GkrError> {
    partially_verify_batch(vec![Gate::LogUp; XOR_8_GKR_INSTANCE_COUNT], proof, channel)
}

pub fn xor_8_output_claims_balance(proof: &GkrBatchProof) -> bool {
    xor_8_table_claim_value(proof) == SecureField::zero()
}

pub fn xor_8_table_claim_value(proof: &GkrBatchProof) -> SecureField {
    let [numerator, denominator] = xor_8_table_output_claim(proof);
    numerator * denominator.inverse()
}

pub fn xor_8_table_output_claim(proof: &GkrBatchProof) -> [SecureField; 2] {
    assert_eq!(
        proof.output_claims_by_instance.len(),
        XOR_8_GKR_INSTANCE_COUNT,
        "xor_8 table-only GKR instance count"
    );
    proof.output_claims_by_instance[0]
        .clone()
        .try_into()
        .expect("LogUp output claim shape")
}

pub fn xor_8_table_claim_matches(proof: &GkrBatchProof, claimed_sum: SecureField) -> bool {
    xor_8_table_claim_value(proof) == claimed_sum
}

pub fn xor_8_multiplicity_mle(witness: &Sha256Witness) -> Mle<SimdBackend, SecureField> {
    Mle::<SimdBackend, SecureField>::new(
        xor_8_multiplicities(witness)
            .into_iter()
            .map(|m| SecureField::from(BaseField::from(m)))
            .collect(),
    )
}

pub fn xor_8_table_denominator_mle_eval(
    relations: &Sha256Relations,
    point: &[SecureField],
) -> SecureField {
    relations.xor_8.eval_fixed_table_denominator_mle(point)
}

pub fn xor_8_layers(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    log_n_rows: u32,
) -> Vec<Layer<SimdBackend>> {
    let _ = log_n_rows;
    vec![xor_8_table_layer(relations, witness)]
}

fn xor_8_table_layer(relations: &Sha256Relations, witness: &Sha256Witness) -> Layer<SimdBackend> {
    let mults = xor_8_multiplicities(witness);
    let rows = build_xor_8_table();
    let mut numerators = Vec::with_capacity(1 << LOG_SIZE_16);
    let mut denominators = Vec::with_capacity(1 << LOG_SIZE_16);
    for (mult, row) in mults.into_iter().zip(rows) {
        numerators.push(-SecureField::from(BaseField::from(mult)));
        denominators.push(xor_8_denominator(relations, row.x, row.y, row.z));
    }
    Layer::LogUpGeneric {
        numerators: Mle::<SimdBackend, SecureField>::new(numerators.into_iter().collect()),
        denominators: Mle::<SimdBackend, SecureField>::new(denominators.into_iter().collect()),
    }
}

fn xor_8_denominator(relations: &Sha256Relations, x: u32, y: u32, z: u32) -> SecureField {
    relations
        .xor_8
        .combine(&[BaseField::from(x), BaseField::from(y), BaseField::from(z)])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gkr_lookups::mle_eval::{
        build_trace as build_mle_eval_trace, MleCoeffColumnOracle, MleEvalProverComponent,
        MleEvalVerifierComponent,
    };
    use crate::relations::Sha256Relations;
    use crate::trace::min_log_size;
    use crate::witness::compute_sha256_witness;
    use stwo::core::air::accumulation::PointEvaluationAccumulator;
    use stwo::core::air::{Component, Components};
    use stwo::core::channel::Blake2sChannel;
    use stwo::core::circle::CirclePoint;
    use stwo::core::fields::m31::BaseField;
    use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig, TreeVec};
    use stwo::core::poly::circle::CanonicCoset;
    use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
    use stwo::core::verifier::verify;
    use stwo::core::ColumnVec;
    use stwo::prover::backend::simd::column::BaseColumn;
    use stwo::prover::backend::simd::SimdBackend;
    use stwo::prover::backend::Column;
    use stwo::prover::lookups::mle::Mle;
    use stwo::prover::poly::circle::{CircleEvaluation, PolyOps, SecureEvaluation};
    use stwo::prover::poly::BitReversedOrder;
    use stwo::prover::{prove, CommitmentSchemeProver, ComponentProver};
    use stwo_constraint_framework::{
        EvalAtRow, FrameworkComponent, FrameworkEval, PointEvaluator, TraceLocationAllocator,
    };

    const MLE_COEFFS_TRACE: usize = 1;
    const MLE_EVAL_TRACE: usize = 2;
    const POST_INTERACTION_MLE_EVAL_TRACE: usize = 3;
    const MLE_TEST_LOG_EXPAND: u32 = 1;

    #[test]
    fn xor_8_gkr_round_trip_balances_one_block() {
        let witness = compute_sha256_witness(b"abc");
        let log_n_rows = min_log_size(witness.blocks.len());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let mut prover_channel = Blake2sChannel::default();
        let gkr = prove_xor_8_gkr(&relations, &witness, log_n_rows, &mut prover_channel);

        let mut verifier_channel = Blake2sChannel::default();
        let artifact =
            verify_xor_8_gkr(&gkr.proof, &mut verifier_channel).expect("GKR proof verifies");

        assert_eq!(
            artifact.n_variables_by_instance.len(),
            XOR_8_GKR_INSTANCE_COUNT
        );
        assert_eq!(artifact.n_variables_by_instance[0], LOG_SIZE_16 as usize);
        assert_eq!(
            artifact.claims_to_verify_by_instance[0][1],
            xor_8_table_denominator_mle_eval(&relations, &artifact.ood_point),
            "fixed-table denominator MLE claim must be verifier-derived",
        );
        assert_eq!(
            -artifact.claims_to_verify_by_instance[0][0],
            mle_eval_at_point(&xor_8_multiplicity_mle(&witness), &artifact.ood_point),
            "GKR numerator claim must be the negated committed multiplicity MLE",
        );
    }

    #[test]
    fn xor_8_gkr_rejects_output_claim_tamper() {
        let witness = compute_sha256_witness(b"abc");
        let log_n_rows = min_log_size(witness.blocks.len());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let mut gkr = prove_xor_8_gkr(
            &relations,
            &witness,
            log_n_rows,
            &mut Blake2sChannel::default(),
        );
        gkr.proof.output_claims_by_instance[0][0] += SecureField::from(BaseField::from(1));

        assert!(
            verify_xor_8_gkr(&gkr.proof, &mut Blake2sChannel::default()).is_err(),
            "tampered output claim must reject"
        );
    }

    #[test]
    fn xor_8_table_denominator_mle_matches_bruteforce_eval() {
        let witness = compute_sha256_witness(b"abc");
        let log_n_rows = min_log_size(witness.blocks.len());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let gkr = prove_xor_8_gkr(
            &relations,
            &witness,
            log_n_rows,
            &mut Blake2sChannel::default(),
        );
        let artifact = verify_xor_8_gkr(&gkr.proof, &mut Blake2sChannel::default()).unwrap();
        let rows = build_xor_8_table();
        let denominators = rows
            .into_iter()
            .map(|row| xor_8_denominator(&relations, row.x, row.y, row.z))
            .collect();

        assert_eq!(
            xor_8_table_denominator_mle_eval(&relations, &artifact.ood_point),
            mle_eval_at_point(
                &Mle::<SimdBackend, SecureField>::new(denominators),
                &artifact.ood_point,
            ),
        );
    }

    #[test]
    fn vendored_mle_eval_component_proves_and_verifies_random_mle() {
        const N_VARIABLES: usize = 5;

        let log_size = N_VARIABLES as u32;
        let coeffs = random_secure_fields(1 << N_VARIABLES);
        let eval_point = random_secure_fields(N_VARIABLES);
        let mle = Mle::<SimdBackend, SecureField>::new(coeffs.into_iter().collect());
        let claim = mle_eval_at_point(&mle, &eval_point);
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(
                log_size + MLE_TEST_LOG_EXPAND + PcsConfig::default().fri_config.log_blowup_factor,
            )
            .circle_domain()
            .half_coset,
        );
        let config = PcsConfig::default();
        let mut commitment_scheme =
            CommitmentSchemeProver::<_, Blake2sMerkleChannel>::new(config, &twiddles);
        let channel = &mut Blake2sChannel::default();

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(vec![]);
        tree_builder.commit(channel);

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(build_mle_coeff_trace(&mle));
        tree_builder.commit(channel);

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(build_mle_eval_trace(&mle, &eval_point, claim));
        tree_builder.commit(channel);

        let trace_location_allocator = &mut TraceLocationAllocator::default();
        let coeff_component = MleCoeffColumnComponent::new(
            trace_location_allocator,
            MleCoeffColumnEval::new(MLE_COEFFS_TRACE, N_VARIABLES),
            SecureField::zero(),
        );
        let eval_component = MleEvalProverComponent::generate(
            trace_location_allocator,
            &coeff_component,
            &eval_point,
            mle,
            claim,
            MLE_EVAL_TRACE,
        );
        let prover_components: &[&dyn ComponentProver<SimdBackend>] =
            &[&coeff_component, &eval_component];
        let proof = prove(prover_components, channel, commitment_scheme)
            .expect("vendored MLE eval proof should prove");

        let trace_location_allocator = &mut TraceLocationAllocator::default();
        let coeff_component = MleCoeffColumnComponent::new(
            trace_location_allocator,
            MleCoeffColumnEval::new(MLE_COEFFS_TRACE, N_VARIABLES),
            SecureField::zero(),
        );
        let eval_component = MleEvalVerifierComponent::new(
            trace_location_allocator,
            &coeff_component,
            &eval_point,
            claim,
            MLE_EVAL_TRACE,
        );
        let components = Components {
            components: vec![&coeff_component as &dyn Component, &eval_component],
            n_preprocessed_columns: 0,
        };
        let log_sizes = components.column_log_sizes();
        let channel = &mut Blake2sChannel::default();
        let commitment_scheme =
            &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(proof.config);
        // F-ROOT note: tree 0 is EMPTY here (`&[]`, no preprocessed columns) and
        // this is a #[cfg(test)] spike — no preprocessed content exists to
        // forge, so no root pin is needed.
        commitment_scheme.commit(proof.commitments[0], &[], channel);
        commitment_scheme.commit(proof.commitments[1], &log_sizes[1], channel);
        commitment_scheme.commit(proof.commitments[2], &log_sizes[2], channel);

        verify(&components.components, channel, commitment_scheme, proof)
            .expect("vendored MLE eval proof should verify");
    }

    #[ignore = "diagnostic: global-bound pad reproduction currently hits pinned-Stwo lifted-domain OOB"]
    #[test]
    fn vendored_mle_eval_component_proves_and_verifies_with_pad_column() {
        const N_VARIABLES: usize = 5;
        const PAD_LOG_SIZE: u32 = 8;

        let log_size = N_VARIABLES as u32;
        let coeffs = random_secure_fields(1 << N_VARIABLES);
        let eval_point = random_secure_fields(N_VARIABLES);
        let mle = Mle::<SimdBackend, SecureField>::new(coeffs.into_iter().collect());
        let claim = mle_eval_at_point(&mle, &eval_point);
        let max_log_size = PAD_LOG_SIZE.max(log_size + MLE_TEST_LOG_EXPAND);
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(max_log_size + PcsConfig::default().fri_config.log_blowup_factor)
                .circle_domain()
                .half_coset,
        );
        let config = PcsConfig::default();
        let mut commitment_scheme =
            CommitmentSchemeProver::<_, Blake2sMerkleChannel>::new(config, &twiddles);
        let channel = &mut Blake2sChannel::default();

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(vec![]);
        tree_builder.commit(channel);

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(build_mle_coeff_trace(&mle));
        tree_builder.commit(channel);

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(build_mle_eval_trace(&mle, &eval_point, claim));
        tree_builder.extend_evals(vec![zero_base_eval(PAD_LOG_SIZE)]);
        tree_builder.commit(channel);

        let trace_location_allocator = &mut TraceLocationAllocator::default();
        let coeff_component = MleCoeffColumnComponent::new(
            trace_location_allocator,
            MleCoeffColumnEval::new(MLE_COEFFS_TRACE, N_VARIABLES),
            SecureField::zero(),
        );
        let eval_component = MleEvalProverComponent::generate_with_pad_column(
            trace_location_allocator,
            &coeff_component,
            &eval_point,
            mle,
            claim,
            MLE_EVAL_TRACE,
            PAD_LOG_SIZE,
        )
        .with_max_constraint_log_degree_bound(PAD_LOG_SIZE + 1);
        let prover_components: &[&dyn ComponentProver<SimdBackend>] =
            &[&coeff_component, &eval_component];
        let proof = prove(prover_components, channel, commitment_scheme)
            .expect("padded vendored MLE eval proof should prove");

        let trace_location_allocator = &mut TraceLocationAllocator::default();
        let coeff_component = MleCoeffColumnComponent::new(
            trace_location_allocator,
            MleCoeffColumnEval::new(MLE_COEFFS_TRACE, N_VARIABLES),
            SecureField::zero(),
        );
        let eval_component = MleEvalVerifierComponent::new_with_pad_column(
            trace_location_allocator,
            &coeff_component,
            &eval_point,
            claim,
            MLE_EVAL_TRACE,
            PAD_LOG_SIZE,
        )
        .with_max_constraint_log_degree_bound(PAD_LOG_SIZE + 1);
        let components = Components {
            components: vec![&coeff_component as &dyn Component, &eval_component],
            n_preprocessed_columns: 0,
        };
        let log_sizes = components.column_log_sizes();
        let channel = &mut Blake2sChannel::default();
        let commitment_scheme =
            &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(proof.config);
        // F-ROOT note: tree 0 is EMPTY here (`&[]`, no preprocessed columns) and
        // this is a #[cfg(test)] spike — no preprocessed content exists to
        // forge, so no root pin is needed.
        commitment_scheme.commit(proof.commitments[0], &[], channel);
        commitment_scheme.commit(proof.commitments[1], &log_sizes[1], channel);
        commitment_scheme.commit(proof.commitments[2], &log_sizes[2], channel);

        verify(&components.components, channel, commitment_scheme, proof)
            .expect("padded vendored MLE eval proof should verify");
    }

    #[ignore = "diagnostic: global-bound fourth-tree reproduction currently hits pinned-Stwo lifted-domain OOB"]
    #[test]
    fn vendored_mle_eval_component_proves_and_verifies_on_fourth_tree() {
        const N_VARIABLES: usize = 5;
        const PAD_LOG_SIZE: u32 = 8;

        let log_size = N_VARIABLES as u32;
        let coeffs = random_secure_fields(1 << N_VARIABLES);
        let eval_point = random_secure_fields(N_VARIABLES);
        let mle = Mle::<SimdBackend, SecureField>::new(coeffs.into_iter().collect());
        let claim = mle_eval_at_point(&mle, &eval_point);
        let max_log_size = PAD_LOG_SIZE.max(log_size + MLE_TEST_LOG_EXPAND);
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(max_log_size + PcsConfig::default().fri_config.log_blowup_factor)
                .circle_domain()
                .half_coset,
        );
        let config = PcsConfig::default();
        let mut commitment_scheme =
            CommitmentSchemeProver::<_, Blake2sMerkleChannel>::new(config, &twiddles);
        let channel = &mut Blake2sChannel::default();

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(vec![]);
        tree_builder.commit(channel);

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(build_mle_coeff_trace(&mle));
        tree_builder.commit(channel);

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(vec![]);
        tree_builder.commit(channel);

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(build_mle_eval_trace(&mle, &eval_point, claim));
        tree_builder.extend_evals(vec![zero_base_eval(PAD_LOG_SIZE)]);
        tree_builder.commit(channel);

        let trace_location_allocator = &mut TraceLocationAllocator::default();
        let coeff_component = MleCoeffColumnComponent::new(
            trace_location_allocator,
            MleCoeffColumnEval::new(MLE_COEFFS_TRACE, N_VARIABLES),
            SecureField::zero(),
        );
        let eval_component = MleEvalProverComponent::generate_with_pad_column(
            trace_location_allocator,
            &coeff_component,
            &eval_point,
            mle,
            claim,
            POST_INTERACTION_MLE_EVAL_TRACE,
            PAD_LOG_SIZE,
        )
        .with_max_constraint_log_degree_bound(PAD_LOG_SIZE + 1);
        let prover_components: &[&dyn ComponentProver<SimdBackend>] =
            &[&coeff_component, &eval_component];
        let proof = prove(prover_components, channel, commitment_scheme)
            .expect("fourth-tree vendored MLE eval proof should prove");

        let trace_location_allocator = &mut TraceLocationAllocator::default();
        let coeff_component = MleCoeffColumnComponent::new(
            trace_location_allocator,
            MleCoeffColumnEval::new(MLE_COEFFS_TRACE, N_VARIABLES),
            SecureField::zero(),
        );
        let eval_component = MleEvalVerifierComponent::new_with_pad_column(
            trace_location_allocator,
            &coeff_component,
            &eval_point,
            claim,
            POST_INTERACTION_MLE_EVAL_TRACE,
            PAD_LOG_SIZE,
        )
        .with_max_constraint_log_degree_bound(PAD_LOG_SIZE + 1);
        let components = Components {
            components: vec![&coeff_component as &dyn Component, &eval_component],
            n_preprocessed_columns: 0,
        };
        let log_sizes = components.column_log_sizes();
        let channel = &mut Blake2sChannel::default();
        let commitment_scheme =
            &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(proof.config);
        // F-ROOT note: tree 0 is EMPTY here (`&[]`, no preprocessed columns) and
        // this is a #[cfg(test)] spike — no preprocessed content exists to
        // forge, so no root pin is needed.
        commitment_scheme.commit(proof.commitments[0], &[], channel);
        commitment_scheme.commit(proof.commitments[1], &log_sizes[1], channel);
        commitment_scheme.commit(proof.commitments[2], &log_sizes[2], channel);
        commitment_scheme.commit(proof.commitments[3], &log_sizes[3], channel);

        verify(&components.components, channel, commitment_scheme, proof)
            .expect("fourth-tree vendored MLE eval proof should verify");
    }

    type MleCoeffColumnComponent = FrameworkComponent<MleCoeffColumnEval>;

    struct MleCoeffColumnEval {
        interaction: usize,
        n_variables: usize,
    }

    impl MleCoeffColumnEval {
        const fn new(interaction: usize, n_variables: usize) -> Self {
            Self {
                interaction,
                n_variables,
            }
        }
    }

    impl FrameworkEval for MleCoeffColumnEval {
        fn log_size(&self) -> u32 {
            self.n_variables as u32
        }

        fn max_constraint_log_degree_bound(&self) -> u32 {
            self.log_size()
        }

        fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
            let _ = eval_mle_coeff_col(self.interaction, &mut eval);
            eval
        }
    }

    impl MleCoeffColumnOracle for MleCoeffColumnComponent {
        fn evaluate_at_point(
            &self,
            _point: CirclePoint<SecureField>,
            mask: &TreeVec<ColumnVec<Vec<SecureField>>>,
        ) -> SecureField {
            let mut accumulator =
                PointEvaluationAccumulator::new(SecureField::from(BaseField::from(1)));
            let mut eval = PointEvaluator::new(
                mask.sub_tree(self.trace_locations()),
                &mut accumulator,
                SecureField::from(BaseField::from(1)),
                self.log_size(),
                SecureField::zero(),
            );

            eval_mle_coeff_col(self.interaction, &mut eval)
        }
    }

    fn eval_mle_coeff_col<E: EvalAtRow>(interaction: usize, eval: &mut E) -> E::EF {
        let [mle_coeff_col_eval] = eval.next_extension_interaction_mask(interaction, [0]);
        mle_coeff_col_eval
    }

    fn build_mle_coeff_trace(
        mle: &Mle<SimdBackend, SecureField>,
    ) -> Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
        let log_size = mle.n_variables() as u32;
        let trace_domain = CanonicCoset::new(log_size).circle_domain();
        let mle_coeffs_col_by_coords = mle.clone().into_evals().into_secure_column_by_coords();
        SecureEvaluation::new(trace_domain, mle_coeffs_col_by_coords)
            .into_coordinate_evals()
            .into_iter()
            .collect()
    }

    fn zero_base_eval(log_size: u32) -> CircleEvaluation<SimdBackend, BaseField, BitReversedOrder> {
        let domain = CanonicCoset::new(log_size).circle_domain();
        let col: BaseColumn = std::iter::repeat_n(BaseField::zero(), 1usize << log_size).collect();
        CircleEvaluation::new(domain, col)
    }

    fn mle_eval_at_point(
        evaluation: &Mle<SimdBackend, SecureField>,
        point: &[SecureField],
    ) -> SecureField {
        fn eval(mle_evals: &[SecureField], p: &[SecureField]) -> SecureField {
            match p {
                [] => mle_evals[0],
                &[p_i, ref p @ ..] => {
                    let (lhs, rhs) = mle_evals.split_at(mle_evals.len() / 2);
                    let lhs_eval = eval(lhs, p);
                    let rhs_eval = eval(rhs, p);
                    p_i * (rhs_eval - lhs_eval) + lhs_eval
                }
            }
        }

        let mle_evals = evaluation
            .clone()
            .into_evals()
            .to_cpu()
            .into_iter()
            .map(SecureField::from)
            .collect::<Vec<_>>();

        eval(&mle_evals, point)
    }

    fn random_secure_fields(len: usize) -> Vec<SecureField> {
        let mut state = 0x9e3779b97f4a7c15_u64;
        (0..len)
            .map(|_| {
                state ^= state << 7;
                state ^= state >> 9;
                state = state.wrapping_mul(0xbf58476d1ce4e5b9);
                SecureField::from(BaseField::from((state & 0x3fff_ffff) as u32))
                    + SecureField::from(BaseField::from(((state >> 31) & 0x3fff_ffff) as u32))
                        * SecureField::from(2)
            })
            .collect()
    }
}
