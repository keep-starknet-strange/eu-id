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
    air::Component, channel::Channel, fields::m31::M31, fields::qm31::SecureField, pcs::TreeVec,
    ColumnVec,
};
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::ComponentProver;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::TraceLocationAllocator;

use crate::prepared_table::FinalCheckHintRelation;
use crate::projective_air::{
    projective_rcb_signed_carry_log_size, ProjectiveRcbFoldedContributionComponent,
    ProjectiveRcbFoldedContributionEval, ProjectiveRcbFoldedDigitComponent,
    ProjectiveRcbFoldedDigitEval, ProjectiveRcbMulComponentRelations,
    ProjectiveRcbRawProductChunkComponent, ProjectiveRcbRawProductChunkEval,
    PROJECTIVE_RCB_MUL_ROLE_LHS, PROJECTIVE_RCB_MUL_ROLE_RESULT, PROJECTIVE_RCB_MUL_ROLE_RHS,
    PROJECTIVE_RCB_SCHEDULE_NAMESPACE_FINAL_ADD, PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
};
use crate::range_checks::{
    RangeCheckComponent, RangeCheckEval, SignedCarryRangeComponent, SignedCarryRangeEval,
    RANGE13_BITS,
};
use crate::scalar::scalar_mod_mul::columns::padded_log_size;

pub mod air;
pub mod interaction;
pub mod relation;
pub mod trace;

pub use air::*;
pub use interaction::*;
pub use relation::*;
pub use trace::*;

#[cfg(test)]
mod tests;

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

