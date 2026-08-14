//! AIR constraint evaluation for the FinalAdd component: the mul-provider and
//! check `FrameworkEval` impls, their column reader structs, the per-branch
//! reduction constraint builders, and AIR-shape constants.
//!
//! Split out of `mod.rs` (pure relocation, no behavioral change).

use stwo::core::fields::m31::M31;
use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry};
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};

use crate::constants::P256_MODULUS;
use crate::limbs::{EvalP256BigIntExt, P256EvalBigInt, P256M31BigInt};
use crate::prepared_table::{FinalCheckHintRelation, PREPARED_TABLE_EC_POINT_COLUMNS};
use crate::projective_air::ProjectiveRcbMulResultRelation;
use crate::types::U256;

use super::*;

// ---------------------------------------------------------------------------
// Check evaluator (the four muls are proven by hinted-mul rows)
// ---------------------------------------------------------------------------

pub type FinalAddCheckComponent = FrameworkComponent<FinalAddCheckEval>;

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
    /// Witnessed degree-1 gate `both_finite = (1 − r1.inf)·(1 − r2.inf)`.
    ///
    /// An inline product would make dependent gates degree 3.
    /// The ungated definition sets this value to one on padding rows.
    both_finite: E::F,
    /// Witnessed bit splits for ternary reduction quotients.
    ///
    /// `q = b0 + 2·b1` and `b0·b1 = 0` give `q ∈ {0, 1, 2}`.
    /// The ungated constraints use zero values on inactive rows.
    dy_q_b0: E::F,
    dy_q_b1: E::F,
    x3_q_b0: E::F,
    x3_q_b1: E::F,
    /// Per-cert PROVEN fake-GLV sign bits, consumed from `FinalAddSignRelation`
    /// (bound to `fake_glv_scalar`'s `s2_sign_bit`). On an inactive cert the
    /// consume gate is 0, leaving the bit free — harmless, because that cert's
    /// `R` is ∞ and orientation is x-invariant-moot.
    b1: E::F,
    b2: E::F,
    /// `d = b1 ⊕ b2` (witnessed boolean, defining constraint `d = b1+b2−2·b1·b2`).
    sign_d: E::F,
    /// `R_2` oriented by `d`: `r2p_y ≡ (−1)^d · r2.y (mod p)`. The add runs on
    /// `(R_1, (r2.x, r2p_y))`, binding `x(R_1 + (−1)^d R_2) = x(h_1 + h_2)`.
    r2p_y: P256EvalBigInt<E>,
    /// Modular-negation quotient (`∈ {0,1}`) and carries for the `d = 1` branch.
    neg_q: E::F,
    neg_carries: [E::F; N_LIMBS],
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
            b1: eval.next_trace_mask(),
            b2: eval.next_trace_mask(),
            sign_d: eval.next_trace_mask(),
            r2p_y: eval.next_p256_bigint(),
            neg_q: eval.next_trace_mask(),
            neg_carries: core::array::from_fn(|_| eval.next_trace_mask()),
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
    + 4 // dy_q/x3_q bit splits (b0, b1 each)
    + 3 // b1, b2, sign_d (per-cert sign bits + their XOR)
    + N_LIMBS // r2p_y (oriented R_2 y-coordinate)
    + 1 // neg_q (modular-negation quotient)
    + N_LIMBS; // neg_carries

#[derive(Clone)]
pub struct FinalAddCheckEval {
    pub(crate) log_size: u32,
    pub(crate) mul_result: ProjectiveRcbMulResultRelation,
    /// First hinted-mul `source_index` reserved for final-add muls (the row's
    /// source is `hinted_source_offset + sig_id`).
    pub(crate) hinted_source_offset: u32,
    pub(crate) hint_relation: FinalCheckHintRelation,
    pub(crate) sign_relation: FinalAddSignRelation,
    pub(crate) output_relation: FinalAddOutputRelation,
    pub(crate) gamma_digest: crate::components::gamma_digest::GammaDigestRelation,
    pub(crate) gamma_challenge: crate::components::gamma_digest::GammaChallenge,
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
            .chain(columns.r2p_y.limbs())
            .chain(columns.neg_carries.iter())
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
            columns.b1.clone(),
            columns.b2.clone(),
            columns.sign_d.clone(),
            columns.neg_q.clone(),
        ] {
            eval.add_constraint((one.clone() - active.clone()) * value);
        }

        // inf flags boolean.
        eval.add_constraint(columns.r1.inf.clone() * (one.clone() - columns.r1.inf.clone()));
        eval.add_constraint(columns.r2.inf.clone() * (one.clone() - columns.r2.inf.clone()));
        // Witnessed `both_finite = (1 − r1.inf)·(1 − r2.inf)` (ungated degree-2
        // definition. Padding rows hold 1 since their inf flags are 0). All
        // gates below use the degree-1 column so every constraint stays within
        // the log_size + 1 (degree-2) composition budget.
        eval.add_constraint(
            columns.both_finite.clone()
                - (one.clone() - columns.r1.inf.clone()) * (one.clone() - columns.r2.inf.clone()),
        );
        // Reject R_1 = R_2 = ∞ (=> R_final = ∞). With both inf flags boolean,
        // inf1·inf2 = both_finite − 1 + inf1 + inf2 (degree 1 via the column).
        eval.add_constraint(
            active.clone()
                * (columns.both_finite.clone() + columns.r1.inf.clone() + columns.r2.inf.clone()
                    - one.clone()),
        );

        // -------- Branch selectors --------
        //
        // Witnessed: double_add, inverse_add (both bool).
        // Derived: both_finite, r1_only, r2_only, distinct_add (degree 2).
        // Sum constraint: distinct_add + double_add + inverse_add + r1_only +
        // r2_only = active. Boolean constraints pin every flag to {0,1}.
        // Infinity-derived selectors are mutually exclusive with both_finite.
        // Therefore, exactly one selector is 1 on an active row.
        //
        // `active · inverse_add = 0` rejects the additive-inverse branch.
        // The other branch constraints reject alternate selectors for these points.
        eval.add_constraint(
            columns.double_add.clone() * (one.clone() - columns.double_add.clone()),
        );
        eval.add_constraint(
            columns.inverse_add.clone() * (one.clone() - columns.inverse_add.clone()),
        );
        // `active · inverse_add = 0` already excludes both branch flags together.
        // Reject R_final = ∞ (additive-inverse case).
        eval.add_constraint(active.clone() * columns.inverse_add.clone());

        // Degree-1 witnessed gate (defined above next to the inf booleans).
        let both_finite = columns.both_finite.clone();
        // Use the witnessed gate to keep the pass-through bindings at degree 2.
        // Here, `bf = (1 − inf1)(1 − inf2)`.
        let r1_only = one.clone() - both_finite.clone() - columns.r2.inf.clone();
        let r2_only = one.clone() - both_finite.clone() - columns.r1.inf.clone();
        // distinct_add = both_finite - double_add - inverse_add (degree 2).
        let distinct_add =
            both_finite.clone() - columns.double_add.clone() - columns.inverse_add.clone();
        // distinct_add must itself be bool — distinct_add * (1 - distinct_add) = 0.
        eval.add_constraint(distinct_add.clone() * (one.clone() - distinct_add.clone()));
        // double_add only makes sense when both finite (rejects double_add on
        // infinity branches): double_add * (1 - both_finite) = 0.
        eval.add_constraint(columns.double_add.clone() * (one.clone() - both_finite.clone()));
        eval.add_constraint(columns.inverse_add.clone() * (one.clone() - both_finite.clone()));

        // `double_add` requires equal first and oriented second points.
        for i in 0..N_LIMBS {
            eval.add_constraint(
                columns.double_add.clone()
                    * (columns.r2.x.limbs()[i].clone() - columns.r1.x.limbs()[i].clone()),
            );
            eval.add_constraint(
                columns.double_add.clone()
                    * (columns.r2p_y.limbs()[i].clone() - columns.r1.y.limbs()[i].clone()),
            );
        }

        // -------- Hint consumes (unchanged) --------
        let r1_gate = active.clone() * (one.clone() - columns.r1.inf.clone());
        let r2_gate = active.clone() * (one.clone() - columns.r2.inf.clone());
        consume_hint(
            &mut eval,
            &self.hint_relation,
            &r1_gate,
            &columns.sig_id,
            0,
            &columns.r1,
        );
        consume_hint(
            &mut eval,
            &self.hint_relation,
            &r2_gate,
            &columns.sig_id,
            1,
            &columns.r2,
        );

        // -------- Sign-bit consumes + R_2 orientation --------
        // Bind b1,b2 to the proven per-cert s2_sign_bit (provider:
        // fake_glv_scalar). SAME gate as the hint consume, so the bit is bound
        // exactly for active finite certs. Free (harmless) on inactive certs.
        consume_sign(
            &mut eval,
            &self.sign_relation,
            &r1_gate,
            &columns.sig_id,
            0,
            &columns.b1,
        );
        consume_sign(
            &mut eval,
            &self.sign_relation,
            &r2_gate,
            &columns.sig_id,
            1,
            &columns.b2,
        );
        eval.add_constraint(columns.b1.clone() * (one.clone() - columns.b1.clone()));
        eval.add_constraint(columns.b2.clone() * (one.clone() - columns.b2.clone()));
        eval.add_constraint(columns.sign_d.clone() * (one.clone() - columns.sign_d.clone()));
        // d = b1 ⊕ b2 = b1 + b2 − 2·b1·b2 (degree 2).
        eval.add_constraint(
            columns.sign_d.clone()
                - (columns.b1.clone() + columns.b2.clone()
                    - (columns.b1.clone() + columns.b1.clone()) * columns.b2.clone()),
        );
        // `r2p_y ≡ (−1)^d · r2.y (mod p)`.
        // The x-coordinate and infinity flag do not change under orientation.
        // The addition binds `x(R_1 + (−1)^d R_2) = x(h_1 + h_2)`.
        let neg_d = one.clone() - columns.sign_d.clone();
        for i in 0..N_LIMBS {
            eval.add_constraint(
                neg_d.clone()
                    * (columns.r2p_y.limbs()[i].clone() - columns.r2.y.limbs()[i].clone()),
            );
        }
        add_negation_reduction(
            &mut eval,
            &columns.sign_d,
            &columns.r2p_y,
            &columns.r2.y,
            &columns.neg_q,
            &columns.neg_carries,
        );
        eval.add_constraint(columns.neg_q.clone() * (one.clone() - columns.neg_q.clone()));
        // neg_q = 0 on the passthrough (d=0) branch (and on padding via the
        // (1−active) gate above). The negation carries are likewise zero unless
        // the d=1 reduction constrains them, so they are not free witnesses.
        eval.add_constraint(neg_d.clone() * columns.neg_q.clone());
        for carry in columns.neg_carries.iter() {
            eval.add_constraint(neg_d.clone() * carry.clone());
        }
        // The ORIENTED second point fed to the add (x, inf reused from R_2).
        let r2p: EvalPoint<E> = EvalPoint {
            x: columns.r2.x.clone(),
            y: columns.r2p_y.clone(),
            inf: columns.r2.inf.clone(),
        };

        // -------- Mul consumes (wide tuples, hinted provider) --------
        let mul_source =
            E::F::from(M31::from_u32_unchecked(self.hinted_source_offset)) + columns.sig_id.clone();
        // lambda · dx = dy (semantically `lambda · denom = numer` per branch).
        consume_mul(
            &mut eval,
            &self.mul_result,
            &active,
            &mul_source,
            MUL_LAMBDA_DX,
            ROLE_LHS,
            columns.lambda.limbs(),
        );
        consume_mul(
            &mut eval,
            &self.mul_result,
            &active,
            &mul_source,
            MUL_LAMBDA_DX,
            ROLE_RHS,
            columns.dx.limbs(),
        );
        consume_mul(
            &mut eval,
            &self.mul_result,
            &active,
            &mul_source,
            MUL_LAMBDA_DX,
            ROLE_RESULT,
            columns.dy.limbs(),
        );
        consume_mul(
            &mut eval,
            &self.mul_result,
            &active,
            &mul_source,
            MUL_LAMBDA_SQUARED,
            ROLE_LHS,
            columns.lambda.limbs(),
        );
        consume_mul(
            &mut eval,
            &self.mul_result,
            &active,
            &mul_source,
            MUL_LAMBDA_SQUARED,
            ROLE_RHS,
            columns.lambda.limbs(),
        );
        consume_mul(
            &mut eval,
            &self.mul_result,
            &active,
            &mul_source,
            MUL_LAMBDA_SQUARED,
            ROLE_RESULT,
            columns.lamsq.limbs(),
        );
        // dx · dx_inv = dx_inv_result, with dx_inv_result pinned to
        // (distinct_add + double_add). Forces dx invertible on either finite
        // branch (⟹ x1 != x2 for distinct, ⟹ y1 != 0 for doubling).
        consume_mul(
            &mut eval,
            &self.mul_result,
            &active,
            &mul_source,
            MUL_DX_INV,
            ROLE_LHS,
            columns.dx.limbs(),
        );
        consume_mul(
            &mut eval,
            &self.mul_result,
            &active,
            &mul_source,
            MUL_DX_INV,
            ROLE_RHS,
            columns.dx_inv.limbs(),
        );
        consume_mul(
            &mut eval,
            &self.mul_result,
            &active,
            &mul_source,
            MUL_DX_INV,
            ROLE_RESULT,
            columns.dx_inv_result.limbs(),
        );
        // x1 · x1 = x1_sq.
        consume_mul(
            &mut eval,
            &self.mul_result,
            &active,
            &mul_source,
            MUL_X1_SQUARED,
            ROLE_LHS,
            columns.r1.x.limbs(),
        );
        consume_mul(
            &mut eval,
            &self.mul_result,
            &active,
            &mul_source,
            MUL_X1_SQUARED,
            ROLE_RHS,
            columns.r1.x.limbs(),
        );
        consume_mul(
            &mut eval,
            &self.mul_result,
            &active,
            &mul_source,
            MUL_X1_SQUARED,
            ROLE_RESULT,
            columns.x1_sq.limbs(),
        );

        // Provide x3 to the final check (yield, -active).
        let mut out_values = Vec::with_capacity(FINAL_ADD_OUTPUT_RELATION_ARITY);
        out_values.push(columns.sig_id.clone());
        out_values.extend(columns.x3.limbs().iter().cloned());
        eval.add_to_relation(RelationEntry::base(
            &self.output_relation,
            -active.clone(),
            &out_values,
        ));

        // Collect every witnessed limb for the range13 γ-digest (same order
        // as `final_add_range13_uses`).
        let range13_values: Vec<E::F> = columns
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
            .chain(columns.r2p_y.limbs())
            .cloned()
            .collect();

        // -------- dx_inv_result pinning --------
        // Pin limb0 = (distinct_add + double_add), higher limbs 0.
        let denom_inv_target = distinct_add.clone() + columns.double_add.clone();
        eval.add_constraint(
            active.clone() * (columns.dx_inv_result.limbs()[0].clone() - denom_inv_target.clone()),
        );
        for limb in columns.dx_inv_result.limbs().iter().skip(1) {
            eval.add_constraint(active.clone() * limb.clone());
        }

        // Quotient bounds with degree at most two.
        // The former gated ternary checks `gate·q·(q−1)·(q−2)` were degree 4,
        // over the log_size + 1 (degree-2) composition budget. Replace them
        // with ungated witnessed bit splits: `q = b0 + 2·b1`, `b0, b1` bool,
        // `b0·b1 = 0` ⟺ `q ∈ {0, 1, 2}` on EVERY row (strictly stronger than
        // the former gated checks. Padding/off-branch rows hold q = bits = 0).
        let finite_finite = distinct_add.clone() + columns.double_add.clone();
        // dx_q ∈ {0, 1} everywhere (ungated boolean, off-branch zero below).
        eval.add_constraint(columns.dx_q.clone() * (columns.dx_q.clone() - one.clone()));
        // dy_q ∈ {0, 1, 2} everywhere. It is in {0, 1} on the distinct branch.
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
            &distinct_add,
            &columns.dx,
            &columns.r1.x,
            &columns.r2.x,
            &columns.dx_q,
            &columns.dx_carries,
        );
        add_sub_reduction(
            &mut eval,
            &distinct_add,
            &columns.dy,
            &columns.r1.y,
            &r2p.y,
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

        // Collect all 4·N_LIMBS carries for the signed γ-digest (dx, dy, x3,
        // neg order, matching `final_add_signed_values_list`).
        let signed_carry_values: Vec<E::F> = columns
            .dx_carries
            .iter()
            .chain(columns.dy_carries.iter())
            .chain(columns.x3_carries.iter())
            .chain(columns.neg_carries.iter())
            .cloned()
            .collect();

        // γ-digest yields: ONE signature ⇒ the constant group row 0.
        let row_zero = E::F::from(M31::from_u32_unchecked(0));
        crate::components::gamma_digest::yield_gamma_digest(
            &mut eval,
            &self.gamma_digest,
            &self.gamma_challenge,
            crate::components::gamma_digest::GAMMA_TAG_FINAL_ADD_RANGE13,
            row_zero.clone(),
            active.clone(),
            M31::from_u32_unchecked(0),
            &range13_values,
        );
        crate::components::gamma_digest::yield_gamma_digest(
            &mut eval,
            &self.gamma_digest,
            &self.gamma_challenge,
            crate::components::gamma_digest::GAMMA_TAG_FINAL_ADD_SIGNED,
            row_zero,
            active.clone(),
            crate::range_checks::encode_signed_carry(0),
            &signed_carry_values,
        );

        eval.finalize_logup_in_pairs();
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
    eval.add_to_relation(RelationEntry::base(relation, active.clone(), &values));
}

/// Consume a cert's proven `s2_sign_bit` (use, `+gate`). Bound to the
/// `fake_glv_scalar` provider. The gate matches the hint consume.
fn consume_sign<E: EvalAtRow>(
    eval: &mut E,
    relation: &FinalAddSignRelation,
    gate: &E::F,
    sig_id: &E::F,
    cert_id: u32,
    bit: &E::F,
) {
    let values = [
        sig_id.clone(),
        E::F::from(M31::from_u32_unchecked(cert_id)),
        bit.clone(),
    ];
    eval.add_to_relation(RelationEntry::base(relation, gate.clone(), &values));
}

/// `r2p_y + r2_y − q·p = 0` over 13-bit limbs with signed carries, final 0.
/// Gated by `d` (the negation branch). `q ∈ {0,1}`. Establishes
/// `r2p_y ≡ −r2_y (mod p)`, i.e. the y-coordinate of `−R_2`.
fn add_negation_reduction<E: EvalAtRow>(
    eval: &mut E,
    gate: &E::F,
    r2p_y: &P256EvalBigInt<E>,
    r2_y: &P256EvalBigInt<E>,
    q: &E::F,
    carries: &[E::F; N_LIMBS],
) {
    let zero = E::F::from(M31::from_u32_unchecked(0));
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    let modulus = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS));
    for i in 0..N_LIMBS {
        let prev = if i == 0 {
            zero.clone()
        } else {
            carries[i - 1].clone()
        };
        let recurrence = r2p_y.limbs()[i].clone() + r2_y.limbs()[i].clone()
            - q.clone() * fixed_limb::<E>(&modulus, i)
            + prev
            - limb_base.clone() * carries[i].clone();
        eval.add_constraint(gate.clone() * recurrence);
    }
    eval.add_constraint(gate.clone() * carries[N_LIMBS - 1].clone());
}

fn consume_mul<E: EvalAtRow>(
    eval: &mut E,
    relation: &ProjectiveRcbMulResultRelation,
    active: &E::F,
    source_index: &E::F,
    mul_index: u32,
    role: u32,
    limbs: &[E::F; N_LIMBS],
) {
    let mut values = Vec::with_capacity(3 + N_LIMBS);
    values.push(source_index.clone());
    values.push(E::F::from(M31::from_u32_unchecked(mul_index)));
    values.push(E::F::from(M31::from_u32_unchecked(role)));
    values.extend(limbs.iter().cloned());
    eval.add_to_relation(RelationEntry::base(relation, active.clone(), &values));
}

/// `value + lo - hi - q·p = 0` over 13-bit limbs with signed carries, final 0.
/// (`value = (hi - lo) mod p`, so `value + lo = hi + q·p`, `q ∈ {0, 1}`.)
#[allow(clippy::too_many_arguments)]
fn add_sub_reduction<E: EvalAtRow>(
    eval: &mut E,
    gate: &E::F,
    value: &P256EvalBigInt<E>,
    lo: &P256EvalBigInt<E>,
    hi: &P256EvalBigInt<E>,
    q: &E::F,
    carries: &[E::F; N_LIMBS],
) {
    let zero = E::F::from(M31::from_u32_unchecked(0));
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    let modulus = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS));
    for i in 0..N_LIMBS {
        let prev = if i == 0 {
            zero.clone()
        } else {
            carries[i - 1].clone()
        };
        let recurrence = value.limbs()[i].clone() + lo.limbs()[i].clone()
            - hi.limbs()[i].clone()
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
    gate: &E::F,
    x3: &P256EvalBigInt<E>,
    x1: &P256EvalBigInt<E>,
    x2: &P256EvalBigInt<E>,
    lamsq: &P256EvalBigInt<E>,
    q: &E::F,
    carries: &[E::F; N_LIMBS],
) {
    let zero = E::F::from(M31::from_u32_unchecked(0));
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    let modulus = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS));
    for i in 0..N_LIMBS {
        let prev = if i == 0 {
            zero.clone()
        } else {
            carries[i - 1].clone()
        };
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
        let prev = if i == 0 {
            zero.clone()
        } else {
            carries[i - 1].clone()
        };
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
        let prev = if i == 0 {
            zero.clone()
        } else {
            carries[i - 1].clone()
        };
        let three_term = if i == 0 { three.clone() } else { zero.clone() };
        let recurrence =
            dy.limbs()[i].clone() + three_term + q.clone() * fixed_limb::<E>(&modulus, i)
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
