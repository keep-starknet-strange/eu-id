//! AIR for the hinted mod-p multiplication (see the module docs in [`super`]
//! for the three carry identities and the integer-lifting bounds worksheet).
//!
//! One row per mul. The three identities are enforced as UNGATED degree-≤2
//! extension-field constraints whose coefficients are powers of a challenge
//! `z` drawn from the channel AFTER the base trace is committed (same
//! transcript position as the LogUp relations). All-zero padding rows satisfy
//! the identities trivially, so no gating (and no padding witnesses) are
//! needed. Every committed limb is range-checked: Range13 for 13-bit limbs,
//! a `[−12, 12]` signed table for the carry high parts.

use stwo::core::channel::Channel;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::SecureField;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::ComponentProver;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry, TraceLocationAllocator,
};
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};
use stwo_p256_utils::scalar_arithmetic::words_to_limbs;

use crate::components::projective_rcb_mul::relation::ProjectiveRcbMulResultRelation;
use crate::constants::P256_MODULUS;
use crate::range_checks::{
    add_range_check, range_check_value_column_id, RangeCheckClaim, RangeCheckEval,
    RangeCheckRelation, SignedCarryRangeClaim, SignedCarryRangeEval, RANGE13_BITS,
};

use super::trace::{
    gen_hinted_mul_schedule_columns, hinted_mul_schedule_active_id,
    hinted_mul_schedule_mul_index_id, hinted_mul_schedule_source_index_id, HintedMulRelations,
    HintedMulTraceClaim,
};
use super::witness::{HINTED_MUL_C_COEFFS, HINTED_MUL_H_COEFFS, HINTED_MUL_Q_LIMBS};

/// Signed-table parameters for the carry high parts.
pub const HINTED_MUL_H_HI_EQUATION: &str = "hinted_mul_h_hi";
pub const HINTED_MUL_H_HI_TABLE_LOG_SIZE: u32 = 5;

/// The post-commitment challenge: `z` and everything `evaluate` derives from
/// it. Drawn via [`HintedMulChallenge::draw`] at the same transcript position
/// as the LogUp relations (after the base-tree commitment).
#[derive(Clone, Debug)]
pub struct HintedMulChallenge {
    /// `z^0 … z^(HINTED_MUL_C_COEFFS − 1)`.
    pub z_powers: [SecureField; HINTED_MUL_C_COEFFS],
    /// `P(z)` for the field prime's limb polynomial.
    pub p_at_z: SecureField,
    /// `z − β`.
    pub z_minus_beta: SecureField,
}

impl HintedMulChallenge {
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self::from_z(channel.draw_secure_felt())
    }

    pub fn from_z(z: SecureField) -> Self {
        let one = SecureField::from(M31::from_u32_unchecked(1));
        let mut z_powers = [one; HINTED_MUL_C_COEFFS];
        for i in 1..HINTED_MUL_C_COEFFS {
            z_powers[i] = z_powers[i - 1] * z;
        }
        let p_limbs = words_to_limbs(&P256_MODULUS);
        let mut p_at_z = SecureField::from(M31::from_u32_unchecked(0));
        for (i, &limb) in p_limbs.iter().enumerate() {
            p_at_z += z_powers[i] * SecureField::from(M31::from_u32_unchecked(limb));
        }
        let beta = SecureField::from(M31::from_u32_unchecked(1 << LIMB_BITS));
        Self {
            z_powers,
            p_at_z,
            z_minus_beta: z - beta,
        }
    }
}

pub type HintedMulComponent = FrameworkComponent<HintedMulEval>;

#[derive(Clone)]
pub struct HintedMulEval {
    pub log_size: u32,
    pub challenge: HintedMulChallenge,
    pub range13: RangeCheckRelation,
    pub signed_h: RangeCheckRelation,
    pub mul_result: ProjectiveRcbMulResultRelation,
}

impl FrameworkEval for HintedMulEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(hinted_mul_schedule_active_id(self.log_size));
        let source_index =
            eval.get_preprocessed_column(hinted_mul_schedule_source_index_id(self.log_size));
        let mul_index =
            eval.get_preprocessed_column(hinted_mul_schedule_mul_index_id(self.log_size));

        // Base columns in `push_row_values` order. Every limb is range-checked
        // as it is read, which keeps the logup emission order identical to the
        // column order (the interaction generator mirrors exactly this).
        let read_range13 = |eval: &mut E, count: usize| -> Vec<E::F> {
            (0..count)
                .map(|_| {
                    let mask = eval.next_trace_mask();
                    add_range_check(eval, &self.range13, active.clone(), mask.clone());
                    mask
                })
                .collect()
        };
        let a = read_range13(&mut eval, N_LIMBS);
        let b = read_range13(&mut eval, N_LIMBS);
        let mut groups: Vec<(Vec<E::F>, Vec<E::F>, Vec<E::F>, Vec<E::F>)> = Vec::new();
        for _ in 0..3 {
            let q = read_range13(&mut eval, HINTED_MUL_Q_LIMBS);
            let value = read_range13(&mut eval, N_LIMBS);
            let h_lo = read_range13(&mut eval, HINTED_MUL_H_COEFFS);
            let h_hi: Vec<E::F> = (0..HINTED_MUL_H_COEFFS)
                .map(|_| {
                    let mask = eval.next_trace_mask();
                    add_range_check(&mut eval, &self.signed_h, active.clone(), mask.clone());
                    mask
                })
                .collect();
            groups.push((q, value, h_lo, h_hi));
        }

        // PROVIDE (yield, `-active`) the mul's operand/result limbs under the
        // silo's external relation, so consumers are untouched by the swap.
        let result = &groups[2].1;
        for (role, limbs) in [(0u32, &a), (1u32, &b), (2u32, result)] {
            for (limb_index, limb) in limbs.iter().enumerate() {
                eval.add_to_relation(RelationEntry::new(
                    &self.mul_result,
                    -E::EF::from(active.clone()),
                    &[
                        source_index.clone(),
                        mul_index.clone(),
                        E::F::from(M31::from_u32_unchecked(role)),
                        E::F::from(M31::from_u32_unchecked(limb_index as u32)),
                        limb.clone(),
                    ],
                ));
            }
        }

        // The three carry identities at z (ungated; degree ≤ 2).
        let at_z = |limbs: &[E::F], shift: usize| -> E::EF {
            let mut acc = E::EF::from(SecureField::from(M31::from_u32_unchecked(0)));
            for (i, limb) in limbs.iter().enumerate() {
                acc = acc + E::EF::from(self.challenge.z_powers[shift + i]) * limb.clone();
            }
            acc
        };
        let beta = E::F::from(M31::from_u32_unchecked(1 << LIMB_BITS));
        let h_at_z = |h_lo: &[E::F], h_hi: &[E::F]| -> E::EF {
            let mut acc = E::EF::from(SecureField::from(M31::from_u32_unchecked(0)));
            for i in 0..HINTED_MUL_H_COEFFS {
                acc = acc
                    + E::EF::from(self.challenge.z_powers[i])
                        * (h_lo[i].clone() + beta.clone() * h_hi[i].clone());
            }
            acc
        };

        let a_at_z = at_z(&a, 0);
        let b_lo_at_z = at_z(&b[..N_LIMBS / 2], 0);
        let b_hi_at_z = at_z(&b[N_LIMBS / 2..], 0);
        let p_at_z = E::EF::from(self.challenge.p_at_z);
        let z_minus_beta = E::EF::from(self.challenge.z_minus_beta);

        // (1) A(z)·B_lo(z) − Q1(z)·P(z) − M1(z) − (z−β)·H1(z) = 0
        // (2) A(z)·B_hi(z) − Q2(z)·P(z) − M2(z) − (z−β)·H2(z) = 0
        for (half_at_z, (q, value, h_lo, h_hi)) in
            [b_lo_at_z, b_hi_at_z].into_iter().zip(groups.iter().take(2))
        {
            eval.add_constraint(
                a_at_z.clone() * half_at_z
                    - at_z(q, 0) * p_at_z.clone()
                    - at_z(value, 0)
                    - z_minus_beta.clone() * h_at_z(h_lo, h_hi),
            );
        }
        // (3) M1(z) + z^10·M2(z) − Q3(z)·P(z) − R(z) − (z−β)·H3(z) = 0
        let (q3, r, h3_lo, h3_hi) = &groups[2];
        eval.add_constraint(
            at_z(&groups[0].1, 0) + at_z(&groups[1].1, N_LIMBS / 2)
                - at_z(q3, 0) * p_at_z
                - at_z(r, 0)
                - z_minus_beta * h_at_z(h3_lo, h3_hi),
        );

        eval.finalize_logup_in_pairs();
        eval
    }
}

/// Standalone slice: the check component plus its two table providers.
pub struct HintedMulSliceComponents {
    pub check: HintedMulComponent,
    pub range13: FrameworkComponent<RangeCheckEval>,
    pub signed_h: FrameworkComponent<SignedCarryRangeEval>,
}

impl HintedMulSliceComponents {
    pub fn new(
        allocator: &mut TraceLocationAllocator,
        log_size: u32,
        claimed_sums: &HintedMulSliceClaimedSums,
        challenge: &HintedMulChallenge,
        relations: &HintedMulRelations,
    ) -> Self {
        Self {
            check: HintedMulComponent::new(
                allocator,
                HintedMulEval {
                    log_size,
                    challenge: challenge.clone(),
                    range13: relations.range13.clone(),
                    signed_h: relations.signed_h.clone(),
                    mul_result: relations.mul_result.clone(),
                },
                claimed_sums.check,
            ),
            range13: FrameworkComponent::new(
                allocator,
                RangeCheckEval::new(relations.range13.clone(), RANGE13_BITS),
                claimed_sums.range13,
            ),
            signed_h: FrameworkComponent::new(
                allocator,
                SignedCarryRangeEval::new(
                    relations.signed_h.clone(),
                    HINTED_MUL_H_HI_TABLE_LOG_SIZE,
                    HINTED_MUL_H_HI_EQUATION,
                ),
                claimed_sums.signed_h,
            ),
        }
    }

    pub fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![&self.check, &self.range13, &self.signed_h]
    }

    pub fn components(&self) -> Vec<&dyn stwo::core::air::Component> {
        vec![&self.check, &self.range13, &self.signed_h]
    }
}

pub struct HintedMulSliceClaimedSums {
    pub check: SecureField,
    pub range13: SecureField,
    pub signed_h: SecureField,
}

pub fn hinted_mul_signed_table_claim() -> SignedCarryRangeClaim {
    SignedCarryRangeClaim::new(
        HINTED_MUL_H_HI_TABLE_LOG_SIZE,
        super::witness::HINTED_MUL_H_HI_BOUND,
        HINTED_MUL_H_HI_EQUATION,
    )
}

/// Preprocessed ids in commit order: schedule, Range13 value, signed table.
pub fn hinted_mul_slice_preprocessed_ids(log_size: u32) -> Vec<PreProcessedColumnId> {
    let signed = hinted_mul_signed_table_claim();
    vec![
        hinted_mul_schedule_active_id(log_size),
        hinted_mul_schedule_source_index_id(log_size),
        hinted_mul_schedule_mul_index_id(log_size),
        range_check_value_column_id(RANGE13_BITS),
        crate::range_checks::signed_carry_value_column_id(&signed.equation_name),
        crate::range_checks::signed_carry_active_column_id(&signed.equation_name),
    ]
}

pub fn gen_hinted_mul_slice_preprocessed_trace(
    claim: &HintedMulTraceClaim,
) -> stwo::core::ColumnVec<crate::scalar::scalar_mod_mul::columns::M31ColumnEval> {
    let mut columns = gen_hinted_mul_schedule_columns(claim);
    columns.push(RangeCheckClaim::new(RANGE13_BITS).gen_preprocessed_column());
    let signed = hinted_mul_signed_table_claim();
    columns.push(signed.gen_value_column());
    columns.push(signed.gen_active_column());
    columns
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use std::ops::Deref;
    use stwo::core::channel::{Blake2sChannel, Blake2sM31Channel};
    use stwo::core::fields::qm31::SecureField;
    use stwo::core::fri::FriConfig;
    use stwo::core::pcs::PcsConfig;
    use stwo::core::poly::circle::CanonicCoset;
    use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
    use stwo::prover::poly::circle::PolyOps;
    use stwo::prover::{prove, CommitmentSchemeProver};
    use stwo_constraint_framework::{
        assert_constraints_on_trace, FrameworkEval as _, PREPROCESSED_TRACE_IDX,
    };

    use super::super::trace::{
        gen_hinted_mul_base_trace, gen_hinted_mul_interaction_trace, hinted_mul_range13_uses,
        hinted_mul_signed_uses, HintedMulScheduledRow,
    };
    use super::super::witness::HintedMulWitness;
    use super::*;
    use crate::debug::MockCommitmentScheme;
    use crate::range_checks::RangeCheckInteractionClaim;

    fn test_claim(muls: usize) -> HintedMulTraceClaim {
        let rows = (0..muls)
            .map(|i| {
                let mut a = [0u32; N_LIMBS];
                let mut b = [0u32; N_LIMBS];
                // Spread bits across limbs so convolutions and carries are
                // exercised; keep limbs 13-bit.
                for k in 0..N_LIMBS {
                    a[k] = ((i as u32 + 1) * 2741 + 97 * k as u32) % 8192;
                    b[k] = ((i as u32 + 3) * 4099 + 53 * k as u32) % 8192;
                }
                HintedMulScheduledRow {
                    source_index: i as u32 / 4,
                    mul_index: i as u32 % 4,
                    witness: HintedMulWitness::new(&a, &b).expect("witness builds"),
                }
            })
            .collect();
        HintedMulTraceClaim { rows }
    }

    fn dummy_relations() -> HintedMulRelations {
        let mut channel = Blake2sM31Channel::default();
        HintedMulRelations {
            range13: RangeCheckRelation::draw(&mut channel),
            signed_h: RangeCheckRelation::draw(&mut channel),
            mul_result: ProjectiveRcbMulResultRelation::draw(&mut channel),
        }
    }

    /// Trace-domain constraint check of the check component alone (honest
    /// completeness at an arbitrary z; honest traces satisfy the identities
    /// at EVERY z).
    #[test]
    fn hinted_mul_honest_trace_satisfies_constraints() {
        let claim = test_claim(5);
        let log_size = claim.log_size();
        let relations = dummy_relations();
        let challenge = HintedMulChallenge::from_z(SecureField::from_m31_array(
            core::array::from_fn(|i| M31::from_u32_unchecked(17 + 13 * i as u32)),
        ));

        let schedule = gen_hinted_mul_schedule_columns(&claim);
        let base = gen_hinted_mul_base_trace(&claim);
        let (interaction, interaction_claim) =
            gen_hinted_mul_interaction_trace(&claim, &base, &schedule, &relations);

        let mut commitment_scheme = MockCommitmentScheme::default();
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(gen_hinted_mul_slice_preprocessed_trace(&claim));
        tree_builder.finalize_interaction();
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(base);
        tree_builder.finalize_interaction();
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(interaction);
        tree_builder.finalize_interaction();

        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(
            &hinted_mul_slice_preprocessed_ids(log_size),
        );
        let components = HintedMulSliceComponents::new(
            &mut allocator,
            log_size,
            &HintedMulSliceClaimedSums {
                check: interaction_claim.claimed_sum,
                range13: SecureField::from(M31::from_u32_unchecked(0)),
                signed_h: SecureField::from(M31::from_u32_unchecked(0)),
            },
            &challenge,
            &relations,
        );

        let trace = commitment_scheme.trace_domain_evaluations();
        let mut component_trace = trace
            .sub_tree(components.check.trace_locations())
            .map(|tree| tree.into_iter().cloned().collect_vec());
        component_trace[PREPROCESSED_TRACE_IDX] = components
            .check
            .preprocessed_column_indices()
            .iter()
            .map(|idx| trace[PREPROCESSED_TRACE_IDX][*idx])
            .collect();
        let component_eval = components.check.deref();
        assert_constraints_on_trace(
            &component_trace,
            log_size,
            |eval| {
                let _ = component_eval.evaluate(eval);
            },
            components.check.claimed_sum(),
        );
    }

    /// Full standalone PCS prove + verify. This is also the dedicated stwo
    /// degree test: the slice's own bound (`log_size + 1` with paired logup,
    /// i.e. degree-3 logup columns) must survive real OODS/FRI.
    #[test]
    fn hinted_mul_slice_proves_and_verifies() {
        run_slice(None).expect("honest hinted-mul slice proves and verifies");
    }

    /// Forged result limb: identities are violated at the drawn z; the prover
    /// must fail (constraints unsatisfied).
    #[test]
    fn hinted_mul_slice_rejects_forged_result_limb() {
        let result = run_slice(Some(Box::new(|claim: &mut HintedMulTraceClaim| {
            let row = &mut claim.rows[1].witness;
            row.r[0] = (row.r[0] + 1) % 8192;
        })));
        assert!(result.is_err(), "forged r limb must not prove");
    }

    /// Forged quotient limb: same rejection through identity 1.
    #[test]
    fn hinted_mul_slice_rejects_forged_quotient_limb() {
        let result = run_slice(Some(Box::new(|claim: &mut HintedMulTraceClaim| {
            let row = &mut claim.rows[0].witness;
            row.q1[2] = (row.q1[2] + 1) % 8192;
        })));
        assert!(result.is_err(), "forged q1 limb must not prove");
    }

    /// Forged carry coefficient: rejection through its identity.
    #[test]
    fn hinted_mul_slice_rejects_forged_carry() {
        let result = run_slice(Some(Box::new(|claim: &mut HintedMulTraceClaim| {
            let row = &mut claim.rows[2].witness;
            row.h3[7] += 1;
        })));
        assert!(result.is_err(), "forged h3 coefficient must not prove");
    }

    type Mutation = Box<dyn Fn(&mut HintedMulTraceClaim)>;

    /// Drives the standalone slice end to end: commit preprocessed → commit
    /// base (check columns + the two deterministic provider multiplicities) →
    /// draw z + relations → commit interaction → prove → verify. Mutations
    /// are applied to the claim BEFORE trace generation, exactly like a
    /// malicious prover supplying a forged witness.
    fn run_slice(mutate: Option<Mutation>) -> Result<(), String> {
        let mut claim = test_claim(6);
        if let Some(mutate) = mutate {
            mutate(&mut claim);
        }
        let log_size = claim.log_size();
        let ids = hinted_mul_slice_preprocessed_ids(log_size);
        let config = PcsConfig {
            pow_bits: 0,
            fri_config: FriConfig::new(5, 2, 16, 1),
            lifting_log_size: None,
        };
        // Range13's provider table at log13 dominates the bound.
        let max_bound = RANGE13_BITS + 1;
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(max_bound + config.fri_config.log_blowup_factor)
                .circle_domain()
                .half_coset,
        );
        let mut channel = Blake2sChannel::default();
        let mut commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

        let preprocessed = gen_hinted_mul_slice_preprocessed_trace(&claim);
        let preprocessed_bounds: Vec<u32> =
            preprocessed.iter().map(|c| c.domain.log_size()).collect();
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(preprocessed);
        tree_builder.commit(&mut channel);

        // Base tree: check columns, then the (deterministic, pre-randomness)
        // provider multiplicities, in component-allocation order.
        let base = gen_hinted_mul_base_trace(&claim);
        let range13_claim = RangeCheckClaim::new(RANGE13_BITS);
        let range13_multiplicity =
            range13_claim.gen_multiplicity_trace(hinted_mul_range13_uses(&claim));
        let signed_claim = hinted_mul_signed_table_claim();
        let signed_multiplicity =
            signed_claim.gen_multiplicity_trace(hinted_mul_signed_uses(&claim));
        let mut base_tree = base.clone();
        base_tree.push(range13_multiplicity.clone());
        base_tree.push(signed_multiplicity.clone());
        let base_bounds: Vec<u32> = base_tree.iter().map(|c| c.domain.log_size()).collect();
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(base_tree);
        tree_builder.commit(&mut channel);

        // Post-commitment randomness: z first, then the LogUp relations.
        let challenge = HintedMulChallenge::draw(&mut channel);
        let relations = HintedMulRelations {
            range13: RangeCheckRelation::draw(&mut channel),
            signed_h: RangeCheckRelation::draw(&mut channel),
            mul_result: ProjectiveRcbMulResultRelation::draw(&mut channel),
        };

        let schedule = gen_hinted_mul_schedule_columns(&claim);
        let (check_interaction, interaction_claim) =
            gen_hinted_mul_interaction_trace(&claim, &base, &schedule, &relations);
        let (range13_interaction, range13_provider) =
            RangeCheckInteractionClaim::gen_interaction_trace(
                &range13_multiplicity,
                &range13_claim.gen_preprocessed_column(),
                &relations.range13,
            );
        let (signed_interaction, signed_provider) =
            RangeCheckInteractionClaim::gen_interaction_trace(
                &signed_multiplicity,
                &signed_claim.gen_value_column(),
                &relations.signed_h,
            );

        // The check's range/signed consumers must balance against the two
        // providers; the mul-result provides have no consumer in this
        // standalone slice and are excluded (mirrors the projective harness).
        let balance = interaction_claim.range13_consumer_claimed_sum
            + interaction_claim.signed_h_consumer_claimed_sum
            + range13_provider.claimed_sum
            + signed_provider.claimed_sum;
        if balance != SecureField::from(M31::from_u32_unchecked(0)) {
            return Err("range relations unbalanced".to_string());
        }

        let mut interaction_tree = check_interaction;
        interaction_tree.extend(range13_interaction);
        interaction_tree.extend(signed_interaction);
        let interaction_bounds: Vec<u32> =
            interaction_tree.iter().map(|c| c.domain.log_size()).collect();
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(interaction_tree);
        tree_builder.commit(&mut channel);

        let claimed_sums = HintedMulSliceClaimedSums {
            check: interaction_claim.claimed_sum,
            range13: range13_provider.claimed_sum,
            signed_h: signed_provider.claimed_sum,
        };
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
        let components = HintedMulSliceComponents::new(
            &mut allocator,
            log_size,
            &claimed_sums,
            &challenge,
            &relations,
        );
        let proof = prove(
            &components.component_provers(),
            &mut channel,
            commitment_scheme,
        )
        .map_err(|error| format!("prove failed: {error}"))?;

        // Verify with a fresh transcript mirroring the same draw order.
        let mut channel = Blake2sChannel::default();
        let commitment_scheme_verifier =
            &mut stwo::core::pcs::CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);
        commitment_scheme_verifier.commit(proof.commitments[0], &preprocessed_bounds, &mut channel);
        commitment_scheme_verifier.commit(proof.commitments[1], &base_bounds, &mut channel);
        let verifier_challenge = HintedMulChallenge::draw(&mut channel);
        let verifier_relations = HintedMulRelations {
            range13: RangeCheckRelation::draw(&mut channel),
            signed_h: RangeCheckRelation::draw(&mut channel),
            mul_result: ProjectiveRcbMulResultRelation::draw(&mut channel),
        };
        commitment_scheme_verifier.commit(proof.commitments[2], &interaction_bounds, &mut channel);
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
        let components = HintedMulSliceComponents::new(
            &mut allocator,
            log_size,
            &claimed_sums,
            &verifier_challenge,
            &verifier_relations,
        );
        stwo::core::verifier::verify(
            &components.components(),
            &mut channel,
            commitment_scheme_verifier,
            proof,
        )
        .map_err(|error| format!("verify failed: {error}"))
    }
}
