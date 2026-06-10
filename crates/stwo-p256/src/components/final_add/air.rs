//! AIR constraint evaluation for the FinalAdd component: the mul-provider and
//! check `FrameworkEval` impls, their column reader structs, the per-branch
//! reduction constraint builders, and AIR-shape constants.
//!
//! Split out of `mod.rs` (pure relocation, no behavioral change).

use stwo::core::fields::m31::M31;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry,
};
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};

use crate::constants::P256_MODULUS;
use crate::limbs::{EvalP256BigIntExt, P256EvalBigInt, P256M31BigInt};
use crate::prepared_table::{
    FinalCheckHintRelation, PREPARED_TABLE_EC_POINT_COLUMNS,
};
use crate::projective_air::{
    add_projective_rcb_mul_row, ProjectiveRcbMulColumns, ProjectiveRcbMulComponentRelations,
};
use crate::range_checks::RangeCheckRelation;
use crate::types::U256;

use super::*;

// ---------------------------------------------------------------------------
// Mul-provider evaluator (clone of PublicKeyMulEval shape)
// ---------------------------------------------------------------------------

pub type FinalAddMulComponent = FrameworkComponent<FinalAddMulEval>;
pub type FinalAddCheckComponent = FrameworkComponent<FinalAddCheckEval>;

#[derive(Clone)]
pub struct FinalAddMulEval {
    pub(crate) log_size: u32,
    pub(crate) mul_relations: ProjectiveRcbMulComponentRelations,
    pub(crate) result_relation: FinalAddMulResultRelation,
}

impl FrameworkEval for FinalAddMulEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.next_trace_mask();
        let source_index = eval.next_trace_mask();
        let mul_index = eval.next_trace_mask();
        let columns = ProjectiveRcbMulColumns::read(&mut eval);

        eval.add_constraint(
            active.clone() * (E::F::from(M31::from_u32_unchecked(1)) - active.clone()),
        );
        add_projective_rcb_mul_row(
            &mut eval,
            self.mul_relations.as_refs(),
            active.clone(),
            // No identity fast-path here (final-add operands are not affine-z=1):
            // reduce_gate == gate, so every mul keeps its full reduction.
            active.clone(),
            source_index.clone(),
            mul_index.clone(),
            &columns,
        );
        provide_mul_limbs(&mut eval, &self.result_relation, &active, &mul_index, ROLE_LHS, columns.lhs.limbs());
        provide_mul_limbs(&mut eval, &self.result_relation, &active, &mul_index, ROLE_RHS, columns.rhs.limbs());
        provide_mul_limbs(&mut eval, &self.result_relation, &active, &mul_index, ROLE_RESULT, columns.result.limbs());
        eval.finalize_logup();
        eval
    }
}

fn provide_mul_limbs<E: EvalAtRow>(
    eval: &mut E,
    relation: &FinalAddMulResultRelation,
    active: &E::F,
    mul_index: &E::F,
    role: u32,
    limbs: &[E::F; N_LIMBS],
) {
    for (limb_index, limb) in limbs.iter().enumerate() {
        eval.add_to_relation(RelationEntry::new(
            relation,
            -E::EF::from(active.clone()),
            &[
                mul_index.clone(),
                E::F::from(M31::from_u32_unchecked(role)),
                E::F::from(M31::from_u32_unchecked(limb_index as u32)),
                limb.clone(),
            ],
        ));
    }
}

pub const FINAL_ADD_MUL_PROVIDER_FRACTIONS: usize = 3 * N_LIMBS;

// ---------------------------------------------------------------------------
// Check evaluator
// ---------------------------------------------------------------------------

struct FinalAddCheckColumns<E: EvalAtRow> {
    active: E::F,
    sig_id: E::F,
    r1: EvalPoint<E>,
    r2: EvalPoint<E>,
    /// Witnessed `double_add` ∈ {0, 1}: the row commits to the doubling
    /// tangent identity instead of the distinct chord identity.
    double_add: E::F,
    /// Witnessed `inverse_add` ∈ {0, 1}: the row commits to `R_1 = -R_2`
    /// (output ∞). The AIR forbids this via `active · inverse_add = 0`.
    inverse_add: E::F,
    dx: P256EvalBigInt<E>,
    dy: P256EvalBigInt<E>,
    lambda: P256EvalBigInt<E>,
    lamsq: P256EvalBigInt<E>,
    x3: P256EvalBigInt<E>,
    dx_inv: P256EvalBigInt<E>,
    /// Witnessed `dx · dx_inv mod p` result: limb0 = `distinct_add + double_add`,
    /// rest 0. (= 1 on either finite branch, 0 on infinity branches.)
    dx_inv_result: P256EvalBigInt<E>,
    /// `x1_sq = r1.x · r1.x mod p`, used by the doubling slope-numer reduction.
    x1_sq: P256EvalBigInt<E>,
    dx_q: E::F,
    dx_carries: [E::F; N_LIMBS],
    dy_q: E::F,
    dy_carries: [E::F; N_LIMBS],
    x3_q: E::F,
    x3_carries: [E::F; N_LIMBS],
    /// Witnessed `both_finite = (1 − r1.inf)·(1 − r2.inf)` as a degree-1 gate
    /// column (lessons.md #44 idiom). Inlining the degree-2 product makes
    /// every gate that multiplies it degree 3, over the `log_size + 1`
    /// (degree-2) composition budget — a latent completeness hazard that
    /// activates once no larger component pads the global composition domain.
    /// The defining constraint is ungated, so padding rows hold `1` (their
    /// inf flags are forced to 0).
    both_finite: E::F,
    /// Witnessed bit splits pinning the reduction quotients to their ternary
    /// ranges at degree ≤ 2: `q = b0 + 2·b1` with `b0, b1 ∈ {0,1}` and
    /// `b0·b1 = 0` gives exactly `q ∈ {0, 1, 2}` (the inline ternary checks
    /// `gate·q·(q−1)·(q−2)` are degree 4). All split constraints are ungated;
    /// padding/off-branch rows hold all-zero quotients and bits.
    dy_q_b0: E::F,
    dy_q_b1: E::F,
    x3_q_b0: E::F,
    x3_q_b1: E::F,
}

struct EvalPoint<E: EvalAtRow> {
    x: P256EvalBigInt<E>,
    y: P256EvalBigInt<E>,
    inf: E::F,
}

impl<E: EvalAtRow> EvalPoint<E> {
    fn read(eval: &mut E) -> Self {
        Self {
            x: eval.next_p256_bigint(),
            y: eval.next_p256_bigint(),
            inf: eval.next_trace_mask(),
        }
    }
    fn relation_values(&self) -> Vec<E::F> {
        let mut v = Vec::with_capacity(PREPARED_TABLE_EC_POINT_COLUMNS);
        v.extend(self.x.limbs().iter().cloned());
        v.extend(self.y.limbs().iter().cloned());
        v.push(self.inf.clone());
        v
    }
}

impl<E: EvalAtRow> FinalAddCheckColumns<E> {
    fn read(eval: &mut E) -> Self {
        Self {
            active: eval.next_trace_mask(),
            sig_id: eval.next_trace_mask(),
            r1: EvalPoint::read(eval),
            r2: EvalPoint::read(eval),
            double_add: eval.next_trace_mask(),
            inverse_add: eval.next_trace_mask(),
            dx: eval.next_p256_bigint(),
            dy: eval.next_p256_bigint(),
            lambda: eval.next_p256_bigint(),
            lamsq: eval.next_p256_bigint(),
            x3: eval.next_p256_bigint(),
            dx_inv: eval.next_p256_bigint(),
            dx_inv_result: eval.next_p256_bigint(),
            x1_sq: eval.next_p256_bigint(),
            dx_q: eval.next_trace_mask(),
            dx_carries: core::array::from_fn(|_| eval.next_trace_mask()),
            dy_q: eval.next_trace_mask(),
            dy_carries: core::array::from_fn(|_| eval.next_trace_mask()),
            x3_q: eval.next_trace_mask(),
            x3_carries: core::array::from_fn(|_| eval.next_trace_mask()),
            both_finite: eval.next_trace_mask(),
            dy_q_b0: eval.next_trace_mask(),
            dy_q_b1: eval.next_trace_mask(),
            x3_q_b0: eval.next_trace_mask(),
            x3_q_b1: eval.next_trace_mask(),
        }
    }
}

/// Number of base-trace columns of the check component.
pub const CHECK_TRACE_COLUMNS: usize = 1 // active
    + 1 // sig_id
    + 2 * (2 * N_LIMBS + 1) // r1, r2 points
    + 2 // double_add, inverse_add
    + 8 * N_LIMBS // dx, dy, lambda, lamsq, x3, dx_inv, dx_inv_result, x1_sq
    + 3 * (1 + N_LIMBS) // (q + carries) × 3
    + 1 // both_finite (witnessed degree-1 gate)
    + 4; // dy_q/x3_q bit splits (b0, b1 each)

#[derive(Clone)]
pub struct FinalAddCheckEval {
    pub(crate) log_size: u32,
    pub(crate) result_relation: FinalAddMulResultRelation,
    pub(crate) hint_relation: FinalCheckHintRelation,
    pub(crate) output_relation: FinalAddOutputRelation,
    pub(crate) range13: RangeCheckRelation,
    pub(crate) signed_carry: RangeCheckRelation,
}

impl FrameworkEval for FinalAddCheckEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let one = E::F::from(M31::from_u32_unchecked(1));
        let three = E::F::from(M31::from_u32_unchecked(3));
        let columns = FinalAddCheckColumns::read(&mut eval);
        let active = columns.active.clone();

        eval.add_constraint(active.clone() * (one.clone() - active.clone()));

        // Gate witnesses to zero on padding rows.
        for limb in columns
            .r1
            .x
            .limbs()
            .iter()
            .chain(columns.r1.y.limbs())
            .chain(columns.r2.x.limbs())
            .chain(columns.r2.y.limbs())
            .chain(columns.dx.limbs())
            .chain(columns.dy.limbs())
            .chain(columns.lambda.limbs())
            .chain(columns.lamsq.limbs())
            .chain(columns.x3.limbs())
            .chain(columns.dx_inv.limbs())
            .chain(columns.dx_inv_result.limbs())
            .chain(columns.x1_sq.limbs())
        {
            eval.add_constraint((one.clone() - active.clone()) * limb.clone());
        }
        for value in [
            columns.sig_id.clone(),
            columns.r1.inf.clone(),
            columns.r2.inf.clone(),
            columns.double_add.clone(),
            columns.inverse_add.clone(),
            columns.dx_q.clone(),
            columns.dy_q.clone(),
            columns.x3_q.clone(),
        ] {
            eval.add_constraint((one.clone() - active.clone()) * value);
        }

        // inf flags boolean.
        eval.add_constraint(columns.r1.inf.clone() * (one.clone() - columns.r1.inf.clone()));
        eval.add_constraint(columns.r2.inf.clone() * (one.clone() - columns.r2.inf.clone()));
        // Witnessed `both_finite = (1 − r1.inf)·(1 − r2.inf)` (ungated degree-2
        // definition; padding rows hold 1 since their inf flags are 0). All
        // gates below use the degree-1 column so every constraint stays within
        // the log_size + 1 (degree-2) composition budget.
        eval.add_constraint(
            columns.both_finite.clone()
                - (one.clone() - columns.r1.inf.clone())
                    * (one.clone() - columns.r2.inf.clone()),
        );
        // Reject R_1 = R_2 = ∞ (=> R_final = ∞). With both inf flags boolean,
        // inf1·inf2 = both_finite − 1 + inf1 + inf2 (degree 1 via the column).
        eval.add_constraint(
            active.clone()
                * (columns.both_finite.clone() + columns.r1.inf.clone()
                    + columns.r2.inf.clone()
                    - one.clone()),
        );

        // -------- Branch selectors --------
        //
        // Witnessed: double_add, inverse_add (both bool).
        // Derived: both_finite, r1_only, r2_only, distinct_add (degree 2).
        // Sum constraint: distinct_add + double_add + inverse_add + r1_only +
        // r2_only = active. Since the boolean flags pin each in {0,1} and the
        // infinity-derived selectors are mutually exclusive with both_finite,
        // exactly one is 1 on an active row.
        //
        // The active · inverse_add = 0 constraint makes the additive-inverse
        // branch unprovable: an honest prover with R_1 = -R_2 cannot select
        // any other branch (the dx/dy/x3 reductions or the slope mul would
        // fail), so the witness is uncompletable.
        eval.add_constraint(
            columns.double_add.clone() * (one.clone() - columns.double_add.clone()),
        );
        eval.add_constraint(
            columns.inverse_add.clone() * (one.clone() - columns.inverse_add.clone()),
        );
        // Mutual exclusion of double_add / inverse_add needs no constraint of
        // its own: `active · inverse_add = 0` below already forces
        // inverse_add = 0 on active rows (the former degree-3
        // `active · double_add · inverse_add` was redundant and over the
        // degree-2 budget).
        // Reject R_final = ∞ (additive-inverse case).
        eval.add_constraint(active.clone() * columns.inverse_add.clone());

        // Degree-1 witnessed gate (defined above next to the inf booleans).
        let both_finite = columns.both_finite.clone();
        // Degree-1 forms via the witnessed gate: with
        // bf = (1 − inf1)(1 − inf2) (enforced above),
        // inf1·(1 − inf2) = 1 − bf − inf2 and inf2·(1 − inf1) = 1 − bf − inf1
        // hold pointwise, keeping the passthrough bindings below at degree 2.
        let r1_only = one.clone() - both_finite.clone() - columns.r2.inf.clone();
        let r2_only = one.clone() - both_finite.clone() - columns.r1.inf.clone();
        // distinct_add = both_finite - double_add - inverse_add (degree 2).
        let distinct_add = both_finite.clone()
            - columns.double_add.clone()
            - columns.inverse_add.clone();
        // distinct_add must itself be bool — distinct_add * (1 - distinct_add) = 0.
        eval.add_constraint(
            distinct_add.clone() * (one.clone() - distinct_add.clone()),
        );
        // double_add only makes sense when both finite (rejects double_add on
        // infinity branches): double_add * (1 - both_finite) = 0.
        eval.add_constraint(
            columns.double_add.clone() * (one.clone() - both_finite.clone()),
        );
        eval.add_constraint(
            columns.inverse_add.clone() * (one.clone() - both_finite.clone()),
        );

        // double_add forces r1.x = r2.x and r1.y = r2.y limb-wise.
        for i in 0..N_LIMBS {
            eval.add_constraint(
                columns.double_add.clone()
                    * (columns.r2.x.limbs()[i].clone() - columns.r1.x.limbs()[i].clone()),
            );
            eval.add_constraint(
                columns.double_add.clone()
                    * (columns.r2.y.limbs()[i].clone() - columns.r1.y.limbs()[i].clone()),
            );
        }

        // -------- Hint consumes (unchanged) --------
        let r1_gate = active.clone() * (one.clone() - columns.r1.inf.clone());
        let r2_gate = active.clone() * (one.clone() - columns.r2.inf.clone());
        consume_hint(&mut eval, &self.hint_relation, &r1_gate, &columns.sig_id, 0, &columns.r1);
        consume_hint(&mut eval, &self.hint_relation, &r2_gate, &columns.sig_id, 1, &columns.r2);

        // -------- Mul consumes --------
        // lambda · dx = dy (semantically `lambda · denom = numer` per branch).
        consume_mul(&mut eval, &self.result_relation, &active, MUL_LAMBDA_DX, ROLE_LHS, columns.lambda.limbs());
        consume_mul(&mut eval, &self.result_relation, &active, MUL_LAMBDA_DX, ROLE_RHS, columns.dx.limbs());
        consume_mul(&mut eval, &self.result_relation, &active, MUL_LAMBDA_DX, ROLE_RESULT, columns.dy.limbs());
        consume_mul(&mut eval, &self.result_relation, &active, MUL_LAMBDA_SQUARED, ROLE_LHS, columns.lambda.limbs());
        consume_mul(&mut eval, &self.result_relation, &active, MUL_LAMBDA_SQUARED, ROLE_RHS, columns.lambda.limbs());
        consume_mul(&mut eval, &self.result_relation, &active, MUL_LAMBDA_SQUARED, ROLE_RESULT, columns.lamsq.limbs());
        // dx · dx_inv = dx_inv_result, with dx_inv_result pinned to
        // (distinct_add + double_add). Forces dx invertible on either finite
        // branch (⟹ x1 != x2 for distinct, ⟹ y1 != 0 for doubling).
        consume_mul(&mut eval, &self.result_relation, &active, MUL_DX_INV, ROLE_LHS, columns.dx.limbs());
        consume_mul(&mut eval, &self.result_relation, &active, MUL_DX_INV, ROLE_RHS, columns.dx_inv.limbs());
        consume_mul(&mut eval, &self.result_relation, &active, MUL_DX_INV, ROLE_RESULT, columns.dx_inv_result.limbs());
        // x1 · x1 = x1_sq.
        consume_mul(&mut eval, &self.result_relation, &active, MUL_X1_SQUARED, ROLE_LHS, columns.r1.x.limbs());
        consume_mul(&mut eval, &self.result_relation, &active, MUL_X1_SQUARED, ROLE_RHS, columns.r1.x.limbs());
        consume_mul(&mut eval, &self.result_relation, &active, MUL_X1_SQUARED, ROLE_RESULT, columns.x1_sq.limbs());

        // Provide x3 to the final check (yield, -active).
        let mut out_values = Vec::with_capacity(FINAL_ADD_OUTPUT_RELATION_ARITY);
        out_values.push(columns.sig_id.clone());
        out_values.extend(columns.x3.limbs().iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.output_relation,
            -E::EF::from(active.clone()),
            &out_values,
        ));

        // Range-check every witnessed limb.
        for limb in columns
            .r1
            .x
            .limbs()
            .iter()
            .chain(columns.r1.y.limbs())
            .chain(columns.r2.x.limbs())
            .chain(columns.r2.y.limbs())
            .chain(columns.dx.limbs())
            .chain(columns.dy.limbs())
            .chain(columns.lambda.limbs())
            .chain(columns.lamsq.limbs())
            .chain(columns.x3.limbs())
            .chain(columns.dx_inv.limbs())
            .chain(columns.dx_inv_result.limbs())
            .chain(columns.x1_sq.limbs())
        {
            crate::range_checks::add_range_check(&mut eval, &self.range13, active.clone(), limb.clone());
        }

        // -------- dx_inv_result pinning --------
        // Pin limb0 = (distinct_add + double_add), higher limbs 0.
        let denom_inv_target = distinct_add.clone() + columns.double_add.clone();
        eval.add_constraint(
            active.clone()
                * (columns.dx_inv_result.limbs()[0].clone() - denom_inv_target.clone()),
        );
        for limb in columns.dx_inv_result.limbs().iter().skip(1) {
            eval.add_constraint(active.clone() * limb.clone());
        }

        // -------- Quotient bounds (all degree ≤ 2; lessons.md #44) --------
        // The former gated ternary checks `gate·q·(q−1)·(q−2)` were degree 4,
        // over the log_size + 1 (degree-2) composition budget. Replace them
        // with ungated witnessed bit splits: `q = b0 + 2·b1`, `b0, b1` bool,
        // `b0·b1 = 0` ⟺ `q ∈ {0, 1, 2}` on EVERY row (strictly stronger than
        // the former gated checks; padding/off-branch rows hold q = bits = 0).
        let finite_finite = distinct_add.clone() + columns.double_add.clone();
        // dx_q ∈ {0, 1} everywhere (ungated boolean; off-branch zero below).
        eval.add_constraint(columns.dx_q.clone() * (columns.dx_q.clone() - one.clone()));
        // dy_q ∈ {0, 1, 2} everywhere; ∈ {0, 1} on the distinct branch.
        eval.add_constraint(
            columns.dy_q.clone()
                - columns.dy_q_b0.clone()
                - (columns.dy_q_b1.clone() + columns.dy_q_b1.clone()),
        );
        eval.add_constraint(columns.dy_q_b0.clone() * (one.clone() - columns.dy_q_b0.clone()));
        eval.add_constraint(columns.dy_q_b1.clone() * (one.clone() - columns.dy_q_b1.clone()));
        eval.add_constraint(columns.dy_q_b0.clone() * columns.dy_q_b1.clone());
        eval.add_constraint(distinct_add.clone() * columns.dy_q_b1.clone());
        // x3_q ∈ {0, 1, 2} everywhere.
        eval.add_constraint(
            columns.x3_q.clone()
                - columns.x3_q_b0.clone()
                - (columns.x3_q_b1.clone() + columns.x3_q_b1.clone()),
        );
        eval.add_constraint(columns.x3_q_b0.clone() * (one.clone() - columns.x3_q_b0.clone()));
        eval.add_constraint(columns.x3_q_b1.clone() * (one.clone() - columns.x3_q_b1.clone()));
        eval.add_constraint(columns.x3_q_b0.clone() * columns.x3_q_b1.clone());
        // On non-finite-finite rows the q must be zero.
        eval.add_constraint((one.clone() - finite_finite.clone()) * columns.dx_q.clone());
        eval.add_constraint((one.clone() - finite_finite.clone()) * columns.dy_q.clone());
        eval.add_constraint((one.clone() - finite_finite.clone()) * columns.x3_q.clone());

        // -------- Distinct-branch reductions: dx + x1 ≡ x2, dy + y1 ≡ y2 --------
        add_sub_reduction(
            &mut eval,
            &self.signed_carry,
            &distinct_add,
            &columns.dx,
            &columns.r1.x,
            &columns.r2.x,
            &columns.dx_q,
            &columns.dx_carries,
        );
        add_sub_reduction(
            &mut eval,
            &self.signed_carry,
            &distinct_add,
            &columns.dy,
            &columns.r1.y,
            &columns.r2.y,
            &columns.dy_q,
            &columns.dy_carries,
        );

        // -------- Doubling-branch reductions:
        // dx + q·p ≡ 2·y1, dy + 3 + q·p ≡ 3·x1_sq --------
        add_two_y1_reduction(
            &mut eval,
            &columns.double_add,
            &columns.dx,
            &columns.r1.y,
            &columns.dx_q,
            &columns.dx_carries,
        );
        add_slope_numer_reduction(
            &mut eval,
            &columns.double_add,
            &columns.dy,
            &columns.x1_sq,
            &three,
            &columns.dy_q,
            &columns.dy_carries,
        );

        // x3 reduction: x3 + r1.x + r2.x ≡ lamsq. On doubling rows r2.x = r1.x
        // (forced above), so this becomes x3 + 2·x1 ≡ lamsq automatically.
        add_x3_reduction(
            &mut eval,
            &self.signed_carry,
            &finite_finite,
            &columns.x3,
            &columns.r1.x,
            &columns.r2.x,
            &columns.lamsq,
            &columns.x3_q,
            &columns.x3_carries,
        );

        // Infinity branches: x3 = x2 (R_1 = ∞) or x3 = x1 (R_2 = ∞).
        for i in 0..N_LIMBS {
            eval.add_constraint(
                r1_only.clone() * (columns.x3.limbs()[i].clone() - columns.r2.x.limbs()[i].clone()),
            );
            eval.add_constraint(
                r2_only.clone() * (columns.x3.limbs()[i].clone() - columns.r1.x.limbs()[i].clone()),
            );
        }

        // On non-finite-finite rows, the carries must be zero so the
        // signed-carry lookups are well-defined and padding leaks nothing.
        for carry in columns
            .dx_carries
            .iter()
            .chain(columns.dy_carries.iter())
            .chain(columns.x3_carries.iter())
        {
            eval.add_constraint((one.clone() - finite_finite.clone()) * carry.clone());
        }

        // signed-carry range lookups for all 3·N_LIMBS carries (gated active so
        // the count is fixed; on infinity/padding rows the carry value is 0).
        for carry in columns
            .dx_carries
            .iter()
            .chain(columns.dy_carries.iter())
            .chain(columns.x3_carries.iter())
        {
            crate::range_checks::add_range_check(&mut eval, &self.signed_carry, active.clone(), carry.clone());
        }

        eval.finalize_logup();
        eval
    }
}

fn consume_hint<E: EvalAtRow>(
    eval: &mut E,
    relation: &FinalCheckHintRelation,
    active: &E::F,
    sig_id: &E::F,
    cert_id: u32,
    point: &EvalPoint<E>,
) {
    let mut values = Vec::with_capacity(FINAL_CHECK_HINT_RELATION_ARITY);
    values.push(sig_id.clone());
    values.push(E::F::from(M31::from_u32_unchecked(cert_id)));
    values.extend(point.relation_values());
    eval.add_to_relation(RelationEntry::new(relation, E::EF::from(active.clone()), &values));
}

fn consume_mul<E: EvalAtRow>(
    eval: &mut E,
    relation: &FinalAddMulResultRelation,
    active: &E::F,
    mul_index: u32,
    role: u32,
    limbs: &[E::F; N_LIMBS],
) {
    for (limb_index, limb) in limbs.iter().enumerate() {
        eval.add_to_relation(RelationEntry::new(
            relation,
            E::EF::from(active.clone()),
            &[
                E::F::from(M31::from_u32_unchecked(mul_index)),
                E::F::from(M31::from_u32_unchecked(role)),
                E::F::from(M31::from_u32_unchecked(limb_index as u32)),
                limb.clone(),
            ],
        ));
    }
}

/// `value + lo - hi - q·p = 0` over 13-bit limbs with signed carries, final 0.
/// (`value = (hi - lo) mod p`, so `value + lo = hi + q·p`, `q ∈ {0, 1}`.)
#[allow(clippy::too_many_arguments)]
fn add_sub_reduction<E: EvalAtRow>(
    eval: &mut E,
    signed_carry: &RangeCheckRelation,
    gate: &E::F,
    value: &P256EvalBigInt<E>,
    lo: &P256EvalBigInt<E>,
    hi: &P256EvalBigInt<E>,
    q: &E::F,
    carries: &[E::F; N_LIMBS],
) {
    let _ = signed_carry;
    let zero = E::F::from(M31::from_u32_unchecked(0));
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    let modulus = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS));
    for i in 0..N_LIMBS {
        let prev = if i == 0 { zero.clone() } else { carries[i - 1].clone() };
        let recurrence = value.limbs()[i].clone() + lo.limbs()[i].clone() - hi.limbs()[i].clone()
            - q.clone() * fixed_limb::<E>(&modulus, i)
            + prev
            - limb_base.clone() * carries[i].clone();
        eval.add_constraint(gate.clone() * recurrence);
    }
    eval.add_constraint(gate.clone() * carries[N_LIMBS - 1].clone());
}

/// `x3 + x1 + x2 - lamsq - q·p = 0` over 13-bit limbs with signed carries.
#[allow(clippy::too_many_arguments)]
fn add_x3_reduction<E: EvalAtRow>(
    eval: &mut E,
    signed_carry: &RangeCheckRelation,
    gate: &E::F,
    x3: &P256EvalBigInt<E>,
    x1: &P256EvalBigInt<E>,
    x2: &P256EvalBigInt<E>,
    lamsq: &P256EvalBigInt<E>,
    q: &E::F,
    carries: &[E::F; N_LIMBS],
) {
    let _ = signed_carry;
    let zero = E::F::from(M31::from_u32_unchecked(0));
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    let modulus = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS));
    for i in 0..N_LIMBS {
        let prev = if i == 0 { zero.clone() } else { carries[i - 1].clone() };
        let recurrence = x3.limbs()[i].clone() + x1.limbs()[i].clone() + x2.limbs()[i].clone()
            - lamsq.limbs()[i].clone()
            - q.clone() * fixed_limb::<E>(&modulus, i)
            + prev
            - limb_base.clone() * carries[i].clone();
        eval.add_constraint(gate.clone() * recurrence);
    }
    eval.add_constraint(gate.clone() * carries[N_LIMBS - 1].clone());
}

/// `dx + q·p - 2·y1 = 0` over 13-bit limbs with signed carries.
/// Doubling-branch: `dx ≡ 2·y1 (mod p)` so the slope denominator is `2·y1`.
fn add_two_y1_reduction<E: EvalAtRow>(
    eval: &mut E,
    gate: &E::F,
    dx: &P256EvalBigInt<E>,
    y1: &P256EvalBigInt<E>,
    q: &E::F,
    carries: &[E::F; N_LIMBS],
) {
    let zero = E::F::from(M31::from_u32_unchecked(0));
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    let two = E::F::from(M31::from_u32_unchecked(2));
    let modulus = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS));
    for i in 0..N_LIMBS {
        let prev = if i == 0 { zero.clone() } else { carries[i - 1].clone() };
        let recurrence = dx.limbs()[i].clone() + q.clone() * fixed_limb::<E>(&modulus, i)
            - two.clone() * y1.limbs()[i].clone()
            + prev
            - limb_base.clone() * carries[i].clone();
        eval.add_constraint(gate.clone() * recurrence);
    }
    eval.add_constraint(gate.clone() * carries[N_LIMBS - 1].clone());
}

/// `dy + 3 + q·p - 3·x1_sq = 0` over 13-bit limbs with signed carries.
/// Doubling-branch: `dy + 3 ≡ 3·x1² (mod p)`, i.e. `dy ≡ 3·x1² - 3 (mod p)`.
/// The constant 3 is a single field element added to limb 0 only (its
/// limb decomposition is `[3, 0, 0, …, 0]`).
#[allow(clippy::too_many_arguments)]
fn add_slope_numer_reduction<E: EvalAtRow>(
    eval: &mut E,
    gate: &E::F,
    dy: &P256EvalBigInt<E>,
    x1_sq: &P256EvalBigInt<E>,
    three: &E::F,
    q: &E::F,
    carries: &[E::F; N_LIMBS],
) {
    let zero = E::F::from(M31::from_u32_unchecked(0));
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    let three_coeff = E::F::from(M31::from_u32_unchecked(3));
    let modulus = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS));
    for i in 0..N_LIMBS {
        let prev = if i == 0 { zero.clone() } else { carries[i - 1].clone() };
        let three_term = if i == 0 { three.clone() } else { zero.clone() };
        let recurrence = dy.limbs()[i].clone()
            + three_term
            + q.clone() * fixed_limb::<E>(&modulus, i)
            - three_coeff.clone() * x1_sq.limbs()[i].clone()
            + prev
            - limb_base.clone() * carries[i].clone();
        eval.add_constraint(gate.clone() * recurrence);
    }
    eval.add_constraint(gate.clone() * carries[N_LIMBS - 1].clone());
}

fn fixed_limb<E: EvalAtRow>(value: &P256M31BigInt, index: usize) -> E::F {
    E::F::from(value.limbs()[index])
}
