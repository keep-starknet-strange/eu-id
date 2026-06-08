//! FinalAdd AIR — in-AIR EC addition `S = R_1 + R_2` and `r_x = x(S)` binding.
//!
//! # What this closes
//!
//! `final_check_air.rs` proves `r_check = r_x mod n` and `r_check = public r`,
//! but `r_x` was a FREE witness: nothing tied it to the proven scalar-mult
//! outputs. This component closes that gap by proving, IN-AIR, the
//! x-coordinate of the final ECDSA point and forwarding it to the final check.
//!
//! # The pinned hints `R_i`
//!
//! For each signature, the prepared table proves a per-cert *signed hint point*
//! `R_i` (= the `DoubleR` row's `lhs`), which `PreparedTableCanonicalRelation`
//! role `R` already pins in-AIR. `R_i = ±h_i` where `h_i = u_i · base_i`; for an
//! ACTIVE cert `fake_glv_scalar` forces `s2_sign_bit == 1`, so `R_i = -h_i`.
//! The prepared table yields `R_i` on [`FinalCheckHintRelation`] keyed
//! `(sig_id, cert_id, point)`; this component CONSUMES `R_1` (cert0 = `u1·G`)
//! and `R_2` (cert1 = `u2·Q`).
//!
//! # Why the negation cancels
//!
//! `R_final = h1 + h2 = (-R_1) + (-R_2) = -(R_1 + R_2)`. Negation preserves the
//! x-coordinate, so `x(R_final) = x(R_1 + R_2)`. Hence this component computes
//! `S = R_1 + R_2` and binds `r_x = x(S) = x(R_final)`. No per-coordinate
//! negation gadget is needed.
//!
//! # Architecture (mirrors `public_key_curve_air.rs`)
//!
//! The two modular multiplications of the chord-addition x-coordinate formula
//! are laid out as a single-source [`ProjectiveRcbAirTraceClaim`] carrying two
//! [`ProjectiveRcbMulRow`]s, proven by the *exact* `projective_air` mod-`p` mul
//! machinery (`raw_product_chunk` / `folded_contribution` / `folded_digit` /
//! `range13` / `signed_carry`, all reused unchanged). A [`FinalAddCheckEval`]
//! component witnesses the affine operands, consumes the mul provider tuples to
//! bind them, and proves the same-row x-coordinate identity.
//!
//! | `mul_index` | computes          | result    |
//! |-------------|-------------------|-----------|
//! | 0           | `lambda * dx`     | `p1`      |
//! | 1           | `lambda * lambda` | `lamsq`   |
//! | 2           | `dx * dx_inv`     | `1`/`0`   |
//!
//! with `dx = (x2 - x1) mod p`, and the witnessed `lambda` is the chord slope.
//! Mul 2 binds `dx · dx_inv ≡ 1` on the both-finite branch (witnessing
//! `dx != 0`, i.e. `x1 != x2`), so the doubling/inverse degeneracy where
//! `lambda` would be a free witness is rejected in-AIR.
//!
//! # The x-coordinate identity (chord addition, distinct finite case)
//!
//! `lambda = (y2 - y1) / (x2 - x1)`, `x3 = lambda^2 - x1 - x2`. We prove:
//! - `dx + x1 ≡ x2 (mod p)`           (defines `dx`)
//! - `dy + y1 ≡ y2 (mod p)`           (defines `dy = (y2 - y1) mod p`)
//! - `p1 == dy`                       (`lambda*(x2-x1) ≡ y2-y1`; both canonical)
//! - `x3 + x1 + x2 ≡ lamsq (mod p)`   (`x3 = lambda^2 - x1 - x2`)
//!
//! On the **distinct-add** branch, the four chord identities are gated by
//! `distinct_add` (which itself requires `both_finite = (1 - r1_inf)(1 - r2_inf)`).
//! The infinity branches use `x3 = x2` (when `R_1 = ∞`) or `x3 = x1`
//! (when `R_2 = ∞`); the `R_1 = R_2 = ∞` case is rejected
//! (`active · r1_inf · r2_inf = 0`).
//!
//! # Doubling (`R_1 = R_2`)
//!
//! When the witness commits to `double_add = 1`, the row enforces
//! `r1.x = r2.x` and `r1.y = r2.y` (so the `x3 + x1 + x2 ≡ lamsq` reduction
//! becomes `x3 + 2·x1 ≡ lamsq`). The `dx`/`dy`/`dx_inv` columns are
//! repurposed to carry the tangent slope's denominator (`2·y1`), numerator
//! (`3·x1^2 − 3`) and its inverse:
//! - `dx + 0 ≡ 2·y1 (mod p)`           (`dx = denom = 2·y1`)
//! - `dy + 3 ≡ 3·x1_sq (mod p)`        (`dy = numer = 3·x1_sq − 3`)
//! - `p1 == dy`                        (re-used: `lambda · denom ≡ numer`)
//! - `dx · dx_inv ≡ 1`                 (re-used: `denom != 0`, i.e. `y1 != 0`)
//!
//! `x1_sq = x1 · x1 mod p` is proven through a new mul `MUL_X1_SQUARED`
//! (idle = `0·0 = 0` on non-doubling rows).
//!
//! # Additive-inverse (`R_1 = -R_2`)
//!
//! Rejected in-AIR: `active · inverse_add = 0` makes the row unprovable. The
//! resulting EC sum would be `∞`, an invalid ECDSA result.
//!
//! `x3` is provided to `final_check_air` on [`FinalAddOutputRelation`] keyed
//! `(sig_id, x3[N_LIMBS])`, which the final check consumes as its `r_x`.

use stwo::core::{
    air::Component,
    channel::Channel,
    fields::{m31::M31, qm31::SecureField},
    pcs::TreeVec,
    utils::{bit_reverse_index, coset_index_to_circle_domain_index},
    ColumnVec,
};
use stwo::prover::backend::simd::{
    m31::{LOG_N_LANES, N_LANES},
    qm31::PackedQM31,
    SimdBackend,
};
use stwo::prover::ComponentProver;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    TraceLocationAllocator,
};
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};

use crate::constants::P256_MODULUS;
use crate::limbs::{EvalP256BigIntExt, P256EvalBigInt, P256M31BigInt};
use crate::prepared_table::{
    FinalCheckHintRelation, PreparedAffinePoint, PREPARED_TABLE_EC_POINT_COLUMNS,
};
use crate::projective::{ProjectiveEcOp, ProjectivePoint};
use crate::projective_air::{
    add_projective_rcb_mul_row, gen_projective_rcb_folded_contribution_base_trace,
    gen_projective_rcb_folded_digit_base_trace, gen_projective_rcb_mul_base_trace,
    gen_projective_rcb_raw_product_chunk_base_trace, projective_rcb_mul_row_fraction_count,
    projective_rcb_mul_padding_fraction_pairs, projective_rcb_mul_row_fraction_pairs,
    projective_rcb_signed_carry_bound, projective_rcb_signed_carry_log_size, ProjectiveRcbAirError,
    ProjectiveRcbAirRow, ProjectiveRcbAirTraceClaim, ProjectiveRcbFoldedContributionComponent,
    ProjectiveRcbFoldedContributionEval, ProjectiveRcbFoldedDigitComponent,
    ProjectiveRcbFoldedDigitEval, ProjectiveRcbMulColumns, ProjectiveRcbMulComponentRelations,
    ProjectiveRcbMulRow, ProjectiveRcbMulStep, ProjectiveRcbRawProductChunkComponent,
    ProjectiveRcbRawProductChunkEval, PROJECTIVE_RCB_MUL_ROLE_LHS, PROJECTIVE_RCB_MUL_ROLE_RESULT,
    PROJECTIVE_RCB_MUL_ROLE_RHS, PROJECTIVE_RCB_SCHEDULE_NAMESPACE_FINAL_ADD,
    PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
};
use crate::range_checks::{
    encode_signed_carry, range_check_value_column_id, signed_carry_active_column_id,
    signed_carry_value_column_id, RangeCheckClaim, RangeCheckComponent, RangeCheckEval,
    RangeCheckInteractionClaim, RangeCheckRelation, SignedCarryRangeClaim,
    SignedCarryRangeComponent, SignedCarryRangeEval, RANGE13_BITS,
};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};
use crate::types::{AffinePoint, U256};

use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

pub mod air;
pub mod relation;
pub mod trace;

pub use air::*;
pub use relation::*;
pub use trace::*;

use air::{
    FinalAddCheckComponent, FinalAddCheckEval, FinalAddMulComponent, FinalAddMulEval,
    FINAL_ADD_MUL_PROVIDER_FRACTIONS,
};
use trace::{
    dx_inv_result_value, final_add_range13_uses, final_add_signed_carry_claim,
    final_add_signed_carry_uses,
};

/// `lambda · denom ≡ numer (mod p)`. `denom = (x2 − x1)` on the distinct
/// branch and `denom = 2·y1` on the doubling branch (both stored in the same
/// `dx` column, switched by the active branch selector).
const MUL_LAMBDA_DX: u32 = 0;
const MUL_LAMBDA_SQUARED: u32 = 1;
/// `denom · denom_inv ≡ (distinct_add + double_add) (mod p)` — witnesses
/// `denom != 0` on either finite branch (rejects `x1 == x2` for distinct and
/// `y1 == 0` for doubling).
const MUL_DX_INV: u32 = 2;
/// `x1 · x1 ≡ x1_sq (mod p)` — feeds the doubling slope numerator
/// `numer + 3 ≡ 3·x1_sq (mod p)`. Idle (`0·0 = 0`) on the infinity branches.
const MUL_X1_SQUARED: u32 = 3;
pub const FINAL_ADD_MUL_COUNT: usize = 4;

const ROLE_LHS: u32 = PROJECTIVE_RCB_MUL_ROLE_LHS;
const ROLE_RHS: u32 = PROJECTIVE_RCB_MUL_ROLE_RHS;
const ROLE_RESULT: u32 = PROJECTIVE_RCB_MUL_ROLE_RESULT;

/// Quotient bound for the chord-addition reductions.
/// - `dx`, `dy`: `q ∈ {0, 1}` (single subtraction of `p`).
/// - `x3 + x1 + x2 ≡ lamsq`: `x3 + x1 + x2 < 3p`, `lamsq < p`, so `q ∈ {0, 1, 2}`.
const FINAL_ADD_QUOTIENT_BOUND: i64 = 2;

// ---------------------------------------------------------------------------
// Components bundle
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalAddLogSizes {
    mul: u32,
    raw_product_chunk: u32,
    folded_contribution: u32,
    folded_digit: u32,
    check: u32,
}

impl FinalAddLogSizes {
    fn from_claim(claim: &FinalAddClaim) -> Self {
        let projective = claim.mul_trace.component_log_sizes();
        Self {
            mul: projective.mul,
            raw_product_chunk: projective.raw_product_chunk,
            folded_contribution: projective.folded_contribution,
            folded_digit: projective.folded_digit,
            check: padded_log_size(1),
        }
    }
}

#[derive(Clone, Debug)]
pub struct FinalAddInteractionClaim {
    pub mul: SecureField,
    pub raw_product_chunk: SecureField,
    pub folded_contribution: SecureField,
    pub folded_digit: SecureField,
    pub check: SecureField,
    pub range13: RangeCheckInteractionClaim,
    pub signed_carry: RangeCheckInteractionClaim,
    /// FinalCheckHint consumer sum (use, `+active`) for `R_1`, `R_2`.
    pub hint_consumer_claimed_sum: SecureField,
    /// FinalAddOutput provider sum (yield, `-active`).
    pub output_provider_claimed_sum: SecureField,
}

impl FinalAddInteractionClaim {
    pub fn zero() -> Self {
        let zero = secure_zero();
        Self {
            mul: zero,
            raw_product_chunk: zero,
            folded_contribution: zero,
            folded_digit: zero,
            check: zero,
            range13: RangeCheckInteractionClaim { claimed_sum: zero },
            signed_carry: RangeCheckInteractionClaim { claimed_sum: zero },
            hint_consumer_claimed_sum: zero,
            output_provider_claimed_sum: zero,
        }
    }

    /// Internal total: every relation that nets to zero WITHIN the sub-graph.
    /// `mul_limb`/raw/fold families + `FinalAddMulResult` + own range13/signed
    /// carry providers all balance internally; the boundary-crossing relations
    /// (`FinalCheckHint`, `FinalAddOutput`) are excluded.
    pub fn internal_total(&self) -> SecureField {
        self.mul
            + self.raw_product_chunk
            + self.folded_contribution
            + self.folded_digit
            + self.check
            + self.range13.claimed_sum
            + self.signed_carry.claimed_sum
            - self.hint_consumer_claimed_sum
            - self.output_provider_claimed_sum
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[
            self.mul,
            self.raw_product_chunk,
            self.folded_contribution,
            self.folded_digit,
            self.check,
            self.range13.claimed_sum,
            self.signed_carry.claimed_sum,
            self.hint_consumer_claimed_sum,
            self.output_provider_claimed_sum,
        ]);
    }
}

pub struct FinalAddComponents {
    mul: FinalAddMulComponent,
    raw_product_chunk: ProjectiveRcbRawProductChunkComponent,
    folded_contribution: ProjectiveRcbFoldedContributionComponent,
    folded_digit: ProjectiveRcbFoldedDigitComponent,
    check: FinalAddCheckComponent,
    range13: RangeCheckComponent,
    signed_carry: SignedCarryRangeComponent,
}

impl FinalAddComponents {
    pub fn new(
        allocator: &mut TraceLocationAllocator,
        log_sizes: FinalAddLogSizes,
        interaction_claim: &FinalAddInteractionClaim,
        relations: &FinalAddRelations,
    ) -> Self {
        Self {
            mul: FinalAddMulComponent::new(
                allocator,
                FinalAddMulEval {
                    log_size: log_sizes.mul,
                    mul_relations: relations.mul.clone(),
                    result_relation: relations.result.clone(),
                },
                interaction_claim.mul,
            ),
            raw_product_chunk: ProjectiveRcbRawProductChunkComponent::new(
                allocator,
                ProjectiveRcbRawProductChunkEval {
                    log_size: log_sizes.raw_product_chunk,
                    relations: relations.mul.clone(),
                    schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_FINAL_ADD,
                },
                interaction_claim.raw_product_chunk,
            ),
            folded_contribution: ProjectiveRcbFoldedContributionComponent::new(
                allocator,
                ProjectiveRcbFoldedContributionEval {
                    log_size: log_sizes.folded_contribution,
                    relations: relations.mul.clone(),
                    schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_FINAL_ADD,
                },
                interaction_claim.folded_contribution,
            ),
            folded_digit: ProjectiveRcbFoldedDigitComponent::new(
                allocator,
                ProjectiveRcbFoldedDigitEval {
                    log_size: log_sizes.folded_digit,
                    relations: relations.mul.clone(),
                    schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_FINAL_ADD,
                },
                interaction_claim.folded_digit,
            ),
            check: FinalAddCheckComponent::new(
                allocator,
                FinalAddCheckEval {
                    log_size: log_sizes.check,
                    result_relation: relations.result.clone(),
                    hint_relation: relations.hint.clone(),
                    output_relation: relations.output.clone(),
                    range13: relations.mul.range13.clone(),
                    signed_carry: relations.mul.signed_carry.clone(),
                },
                interaction_claim.check,
            ),
            range13: RangeCheckComponent::new(
                allocator,
                RangeCheckEval::new(relations.mul.range13.clone(), RANGE13_BITS),
                interaction_claim.range13.claimed_sum,
            ),
            signed_carry: SignedCarryRangeComponent::new(
                allocator,
                SignedCarryRangeEval::new(
                    relations.mul.signed_carry.clone(),
                    projective_rcb_signed_carry_log_size(),
                    PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
                ),
                interaction_claim.signed_carry.claimed_sum,
            ),
        }
    }

    pub fn components(&self) -> Vec<&dyn Component> {
        vec![
            &self.mul as &dyn Component,
            &self.raw_product_chunk as &dyn Component,
            &self.folded_contribution as &dyn Component,
            &self.folded_digit as &dyn Component,
            &self.check as &dyn Component,
            &self.range13 as &dyn Component,
            &self.signed_carry as &dyn Component,
        ]
    }

    pub fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            &self.mul as &dyn ComponentProver<SimdBackend>,
            &self.raw_product_chunk as &dyn ComponentProver<SimdBackend>,
            &self.folded_contribution as &dyn ComponentProver<SimdBackend>,
            &self.folded_digit as &dyn ComponentProver<SimdBackend>,
            &self.check as &dyn ComponentProver<SimdBackend>,
            &self.range13 as &dyn ComponentProver<SimdBackend>,
            &self.signed_carry as &dyn ComponentProver<SimdBackend>,
        ]
    }

    pub fn trace_log_degree_bounds(&self) -> TreeVec<ColumnVec<u32>> {
        TreeVec::concat_cols(
            self.components()
                .into_iter()
                .map(|component| component.trace_log_degree_bounds()),
        )
    }

    pub fn max_constraint_log_degree_bound(&self) -> u32 {
        self.components()
            .into_iter()
            .map(|component| component.max_constraint_log_degree_bound())
            .max()
            .unwrap_or(0)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalAddProofClaim {
    log_sizes: FinalAddLogSizes,
}

impl FinalAddProofClaim {
    pub fn from_claim(claim: &FinalAddClaim) -> Self {
        Self {
            log_sizes: FinalAddLogSizes::from_claim(claim),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_sizes.mul as u64);
        channel.mix_u64(self.log_sizes.raw_product_chunk as u64);
        channel.mix_u64(self.log_sizes.folded_contribution as u64);
        channel.mix_u64(self.log_sizes.folded_digit as u64);
        channel.mix_u64(self.log_sizes.check as u64);
    }

    pub fn log_sizes(&self) -> FinalAddLogSizes {
        self.log_sizes
    }

    /// Preprocessed column ids this sub-graph reads, derived from log sizes
    /// (schedule columns via the allocator + shared range/signed-carry values).
    pub fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut allocator = TraceLocationAllocator::default();
        let _ = FinalAddComponents::new(
            &mut allocator,
            self.log_sizes,
            &FinalAddInteractionClaim::zero(),
            &FinalAddRelations {
                mul: ProjectiveRcbMulComponentRelations::dummy(),
                result: FinalAddMulResultRelation::dummy(),
                hint: FinalCheckHintRelation::dummy(),
                output: FinalAddOutputRelation::dummy(),
            },
        );
        allocator.preprocessed_columns().clone()
    }
}

pub fn gen_final_add_interaction_trace(
    claim: &FinalAddClaim,
    relations: &FinalAddRelations,
    log_sizes: FinalAddLogSizes,
) -> Result<(Vec<M31ColumnEval>, FinalAddInteractionClaim), FinalAddError> {
    let mut columns = Vec::new();

    // Mul family: standard mul fractions ++ FinalAddMulResult provider, one
    // LogupTraceGenerator / one finalize_last.
    let (mul_interaction, mul_sum) =
        gen_mul_family_interaction_trace(claim, relations, log_sizes.mul);
    columns.extend(mul_interaction);

    // Three non-mul families, reused unchanged.
    let (projective_traces, projective_claim) = claim.mul_trace.gen_interaction_trace(&relations.mul);
    columns.extend(projective_traces.raw_product_chunk);
    columns.extend(projective_traces.folded_contribution);
    columns.extend(projective_traces.folded_digit);

    // Check family (consumers + output provider).
    let (check_interaction, check_sum, hint_sum, output_sum) =
        gen_check_interaction_trace(claim, relations, log_sizes.check);
    columns.extend(check_interaction);

    // Shared range providers.
    let range13 = RangeCheckClaim::new(RANGE13_BITS);
    let range13_values = range13.gen_preprocessed_column();
    let range13_multiplicity = range13.gen_multiplicity_trace(final_add_range13_uses(claim));
    let (range13_trace, range13_claim) = RangeCheckInteractionClaim::gen_interaction_trace(
        &range13_multiplicity,
        &range13_values,
        &relations.mul.range13,
    );
    columns.extend(range13_trace);

    let signed_carry = final_add_signed_carry_claim();
    let signed_carry_values = signed_carry.gen_value_column();
    let signed_carry_multiplicity =
        signed_carry.gen_multiplicity_trace(final_add_signed_carry_uses(claim)?);
    let (signed_carry_trace, signed_carry_claim) = RangeCheckInteractionClaim::gen_interaction_trace(
        &signed_carry_multiplicity,
        &signed_carry_values,
        &relations.mul.signed_carry,
    );
    columns.extend(signed_carry_trace);

    Ok((
        columns,
        FinalAddInteractionClaim {
            mul: mul_sum,
            raw_product_chunk: projective_claim.raw_product_chunk,
            folded_contribution: projective_claim.folded_contribution,
            folded_digit: projective_claim.folded_digit,
            check: check_sum,
            range13: range13_claim,
            signed_carry: signed_carry_claim,
            hint_consumer_claimed_sum: hint_sum,
            output_provider_claimed_sum: output_sum,
        },
    ))
}

fn gen_mul_family_interaction_trace(
    claim: &FinalAddClaim,
    relations: &FinalAddRelations,
    log_size: u32,
) -> (Vec<M31ColumnEval>, SecureField) {
    let padded_rows = 1usize << log_size;
    let standard_count = projective_rcb_mul_row_fraction_count();
    let provider_count = FINAL_ADD_MUL_PROVIDER_FRACTIONS;
    let total = standard_count + provider_count;

    let mut storage: Vec<Vec<(SecureField, SecureField)>> = (0..padded_rows)
        .map(|_| {
            let mut v = projective_rcb_mul_padding_fraction_pairs();
            v.extend((0..provider_count).map(|_| (secure_zero(), secure_one())));
            v
        })
        .collect();

    for (mul_index, mul) in claim.mul_trace.rows[0].muls.iter().enumerate() {
        let coset_index = mul_index;
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        );
        let mut pairs = projective_rcb_mul_row_fraction_pairs(0, mul_index, mul, &relations.mul);
        pairs.extend(provider_fraction_pairs(mul_index, mul, &relations.result));
        storage[row] = pairs;
    }

    let mut logup = LogupTraceGenerator::new(log_size);
    for column in 0..total {
        let mut col = logup.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let mut numerators = [secure_zero(); N_LANES];
            let mut denominators = [secure_one(); N_LANES];
            for lane in 0..N_LANES {
                let row = vec_row * N_LANES + lane;
                let (numerator, denominator) = storage[row][column];
                numerators[lane] = numerator;
                denominators[lane] = denominator;
            }
            col.write_frac(
                vec_row,
                PackedQM31::from_array(numerators),
                PackedQM31::from_array(denominators),
            );
        }
        col.finalize_col();
    }
    logup.finalize_last()
}

fn provider_fraction_pairs(
    mul_index: usize,
    mul: &ProjectiveRcbMulRow,
    relation: &FinalAddMulResultRelation,
) -> Vec<(SecureField, SecureField)> {
    let mut pairs = Vec::with_capacity(FINAL_ADD_MUL_PROVIDER_FRACTIONS);
    for (role, limbs) in [
        (ROLE_LHS, mul.trace.lhs.limbs()),
        (ROLE_RHS, mul.trace.rhs.limbs()),
        (ROLE_RESULT, mul.trace.result.limbs()),
    ] {
        for (limb_index, limb) in limbs.iter().enumerate() {
            pairs.push((
                secure_from_i64(-1),
                relation.combine(&[
                    M31::from_u32_unchecked(mul_index as u32),
                    M31::from_u32_unchecked(role),
                    M31::from_u32_unchecked(limb_index as u32),
                    *limb,
                ]),
            ));
        }
    }
    pairs
}

#[allow(clippy::type_complexity)]
fn gen_check_interaction_trace(
    claim: &FinalAddClaim,
    relations: &FinalAddRelations,
    log_size: u32,
) -> (Vec<M31ColumnEval>, SecureField, SecureField, SecureField) {
    let padded_rows = 1usize << log_size;
    let (fractions, hint_sum, output_sum) = check_fraction_pairs(claim, relations);
    let fraction_count = fractions.len();

    let active_row = bit_reverse_index(coset_index_to_circle_domain_index(0, log_size), log_size);
    let mut storage: Vec<Vec<(SecureField, SecureField)>> = (0..padded_rows)
        .map(|_| vec![(secure_zero(), secure_one()); fraction_count])
        .collect();
    storage[active_row] = fractions;

    let mut logup = LogupTraceGenerator::new(log_size);
    for column in 0..fraction_count {
        let mut col = logup.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let mut numerators = [secure_zero(); N_LANES];
            let mut denominators = [secure_one(); N_LANES];
            for lane in 0..N_LANES {
                let row = vec_row * N_LANES + lane;
                let (numerator, denominator) = storage[row][column];
                numerators[lane] = numerator;
                denominators[lane] = denominator;
            }
            col.write_frac(
                vec_row,
                PackedQM31::from_array(numerators),
                PackedQM31::from_array(denominators),
            );
        }
        col.finalize_col();
    }
    let (trace, check_sum) = logup.finalize_last();
    (trace, check_sum, hint_sum, output_sum)
}

/// Check consumer/provider fractions, in the EXACT order `FinalAddCheckEval`
/// emits them:
/// 1. hint consume R_1 (sig,0), R_2 (sig,1)  (use, +active)
/// 2. mul-result consume tuples (mul 0..1, roles lhs/rhs/result)  (use, +active)
/// 3. output provide (sig, x3)  (yield, -active)
/// 4. range13 uses for witnessed limbs
/// 5. signed-carry uses for the 3·N_LIMBS carries
fn check_fraction_pairs(
    claim: &FinalAddClaim,
    relations: &FinalAddRelations,
) -> (Vec<(SecureField, SecureField)>, SecureField, SecureField) {
    let mut pairs = Vec::new();
    let mut hint_sum = secure_zero();
    let mut output_sum = secure_zero();

    // 1. hint consumes, numerator `(1 - inf)` (active row only): an inactive
    //    cert (inf == 1) contributes a zero-numerator fraction so it has no
    //    yield to match.
    for (cert_id, point) in [(0u32, &claim.r1), (1u32, &claim.r2)] {
        let numerator = if point.inf.0 == 1 { secure_zero() } else { secure_from_i64(1) };
        let mut values = Vec::with_capacity(FINAL_CHECK_HINT_RELATION_ARITY);
        values.push(claim.sig_id);
        values.push(M31::from_u32_unchecked(cert_id));
        values.extend(point.x.limbs().iter().copied());
        values.extend(point.y.limbs().iter().copied());
        values.push(point.inf);
        let denom = relations.hint.combine(&values);
        pairs.push((numerator, denom));
        hint_sum += numerator / denom;
    }

    // 2. mul-result consumes.
    let consume = |pairs: &mut Vec<(SecureField, SecureField)>, mul_index: u32, role: u32, value: &P256M31BigInt| {
        for (limb_index, limb) in value.limbs().iter().enumerate() {
            pairs.push((
                secure_from_i64(1),
                relations.result.combine(&[
                    M31::from_u32_unchecked(mul_index),
                    M31::from_u32_unchecked(role),
                    M31::from_u32_unchecked(limb_index as u32),
                    *limb,
                ]),
            ));
        }
    };
    consume(&mut pairs, MUL_LAMBDA_DX, ROLE_LHS, &claim.lambda);
    consume(&mut pairs, MUL_LAMBDA_DX, ROLE_RHS, &claim.dx);
    consume(&mut pairs, MUL_LAMBDA_DX, ROLE_RESULT, &claim.dy);
    consume(&mut pairs, MUL_LAMBDA_SQUARED, ROLE_LHS, &claim.lambda);
    consume(&mut pairs, MUL_LAMBDA_SQUARED, ROLE_RHS, &claim.lambda);
    consume(&mut pairs, MUL_LAMBDA_SQUARED, ROLE_RESULT, &claim.lamsq);
    consume(&mut pairs, MUL_DX_INV, ROLE_LHS, &claim.dx);
    consume(&mut pairs, MUL_DX_INV, ROLE_RHS, &claim.dx_inv);
    // dx · dx_inv result = both_finite (1 if both finite, else 0).
    consume(&mut pairs, MUL_DX_INV, ROLE_RESULT, &dx_inv_result_value(claim));
    // Task 6 doubling: MUL_X1_SQUARED proves `r1.x · r1.x ≡ x1_sq (mod p)`,
    // consumed by the check eval the same way as the other muls so its
    // provider/consumer pair balances in the FinalAddInternal totals.
    consume(&mut pairs, MUL_X1_SQUARED, ROLE_LHS, &claim.r1.x);
    consume(&mut pairs, MUL_X1_SQUARED, ROLE_RHS, &claim.r1.x);
    consume(&mut pairs, MUL_X1_SQUARED, ROLE_RESULT, &claim.x1_sq);

    // 3. output provide.
    {
        let mut values = Vec::with_capacity(FINAL_ADD_OUTPUT_RELATION_ARITY);
        values.push(claim.sig_id);
        values.extend(claim.x3.limbs().iter().copied());
        let denom = relations.output.combine(&values);
        pairs.push((secure_from_i64(-1), denom));
        output_sum += secure_from_i64(-1) / denom;
    }

    // 4. range13 uses.
    for value in [
        &claim.r1.x,
        &claim.r1.y,
        &claim.r2.x,
        &claim.r2.y,
        &claim.dx,
        &claim.dy,
        &claim.lambda,
        &claim.lamsq,
        &claim.x3,
        &claim.dx_inv,
        &dx_inv_result_value(claim),
        // Task 6: every limb of `x1_sq` is also range-checked by the AIR
        // (see the `.chain(columns.x1_sq.limbs())` in the eval's range13
        // chain), so the trace gen must emit matching multiplicities.
        &claim.x1_sq,
    ] {
        for limb in value.limbs() {
            pairs.push((secure_from_i64(1), relations.mul.range13.combine(&[*limb])));
        }
    }

    // 5. signed-carry uses.
    for carry in claim
        .dx_carries
        .iter()
        .chain(claim.dy_carries.iter())
        .chain(claim.x3_carries.iter())
    {
        pairs.push((
            secure_from_i64(1),
            relations.mul.signed_carry.combine(&[encode_signed_carry(*carry)]),
        ));
    }

    (pairs, hint_sum, output_sum)
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn secure_zero() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(0))
}
fn secure_one() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(1))
}
fn secure_from_i64(value: i64) -> SecureField {
    if value < 0 {
        -SecureField::from(M31::from_u32_unchecked((-value) as u32))
    } else {
        SecureField::from(M31::from_u32_unchecked(value as u32))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY};
    use crate::curve::scalar_mul;

    fn generator() -> AffinePoint {
        AffinePoint {
            x: U256::from_le_u64s(&P256_GX),
            y: U256::from_le_u64s(&P256_GY),
        }
    }

    fn mul(k: u64) -> AffinePoint {
        scalar_mul(&U256::from_le_u64s(&[k, 0, 0, 0]), &generator()).expect("nonzero")
    }

    /// Native `R = R_1 + R_2` x-coordinate, for the test oracle.
    fn add_x(a: &AffinePoint, b: &AffinePoint) -> U256 {
        crate::curve::point_add(a, b).output.x
    }

    #[test]
    fn final_add_distinct_chord_add_matches_native_x() {
        // R_1 = 7G, R_2 = 11G (distinct, finite). x3 must equal x(R_1 + R_2).
        let r1 = mul(7);
        let r2 = mul(11);
        let claim = FinalAddClaim::from_hints(M31::from_u32_unchecked(0), &r1, false, &r2, false)
            .expect("distinct add witness");
        assert_eq!(claim.x3.to_u256(), add_x(&r1, &r2));
    }

    #[test]
    fn final_add_r1_infinity_yields_x2() {
        // R_1 = ∞ (cert0 inactive), R_2 = 11G. x3 == x(R_2).
        let r2 = mul(11);
        let claim =
            FinalAddClaim::from_hints(M31::from_u32_unchecked(0), &generator(), true, &r2, false)
                .expect("r1=inf witness");
        assert_eq!(claim.x3.to_u256(), r2.x);
    }

    #[test]
    fn final_add_r2_infinity_yields_x1() {
        let r1 = mul(7);
        let claim =
            FinalAddClaim::from_hints(M31::from_u32_unchecked(0), &r1, false, &generator(), true)
                .expect("r2=inf witness");
        assert_eq!(claim.x3.to_u256(), r1.x);
    }

    #[test]
    fn final_add_supports_finite_doubling() {
        // R_1 == R_2 = 7G => doubling. After Task 6 the AIR supports this
        // branch (lambda = (3·x² − 3) / (2·y)) and the witness builder
        // produces a valid `FinalAddClaim`.
        let r = mul(7);
        let claim = FinalAddClaim::from_hints(M31::from_u32_unchecked(0), &r, false, &r, false)
            .expect("finite doubling now supported by witness builder");
        let expected = crate::curve::point_double(&r).output;
        assert_eq!(claim.x3.to_u256(), expected.x);
    }

    #[test]
    fn final_add_rejects_both_infinity() {
        let err = FinalAddClaim::from_hints(
            M31::from_u32_unchecked(0),
            &generator(),
            true,
            &generator(),
            true,
        )
        .expect_err("both inf rejected");
        assert!(matches!(err, FinalAddError::BothInfinity { .. }));
    }

    #[test]
    fn final_add_base_and_interaction_trace_shapes_balance() {
        let r1 = mul(7);
        let r2 = mul(11);
        let claim = FinalAddClaim::from_hints(M31::from_u32_unchecked(0), &r1, false, &r2, false)
            .expect("witness");
        let log_sizes = FinalAddLogSizes::from_claim(&claim);
        let _base = gen_final_add_base_trace(&claim, log_sizes).expect("base trace");
        let _pre = final_add_preprocessed_columns(&claim).expect("preprocessed");
    }

    /// Native binding oracle: a mutated `x3` (the bound `r_x`) must fail
    /// `verify()` — the chord-addition `x3 + x1 + x2 ≡ lamsq` identity no longer
    /// holds, so the witness is rejected before any proof is generated.
    #[test]
    fn final_add_rejects_mutated_x3() {
        let r1 = mul(7);
        let r2 = mul(11);
        let mut claim =
            FinalAddClaim::from_hints(M31::from_u32_unchecked(0), &r1, false, &r2, false)
                .expect("witness");
        // Flip the low limb of x3.
        let mut limbs = *claim.x3.limbs();
        limbs[0] = limbs[0] + M31::from_u32_unchecked(1);
        claim.x3 = P256M31BigInt::from_limbs(limbs);
        assert!(matches!(
            claim.verify(),
            Err(FinalAddError::ReductionMismatch { which: "x3", .. })
        ));
    }

    /// A mutated slope `lambda` must fail `verify()`: the `lambda·dx == dy`
    /// binding (mul result `p1 == dy`) breaks once the mul re-derives `p1` from
    /// the mutated `lambda`.
    #[test]
    fn final_add_rejects_mutated_lambda() {
        let r1 = mul(7);
        let r2 = mul(11);
        let mut claim =
            FinalAddClaim::from_hints(M31::from_u32_unchecked(0), &r1, false, &r2, false)
                .expect("witness");
        let mut limbs = *claim.lambda.limbs();
        limbs[0] = limbs[0] + M31::from_u32_unchecked(1);
        claim.lambda = P256M31BigInt::from_limbs(limbs);
        // The mul trace still encodes the true lambda, so the witnessed-lambda
        // copy no longer matches the mul lhs.
        assert!(claim.verify().is_err());
    }
}
