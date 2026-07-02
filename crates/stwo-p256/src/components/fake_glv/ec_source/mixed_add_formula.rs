//! C5-2b: in-AIR constraint of the projective **MixedAdd** EC-op coordinate
//! formula on the fake-GLV projective-source consumer.
//!
//! ## What this closes
//!
//! Sibling to [`super::double_formula`]. The silo ([`projective_rcb_mul`])
//! proves, per source op, the **15** field products `result_k = lhs_k · rhs_k
//! (mod p)` (`k = 0..14`); C5-1 plumbing makes the consumer's committed mul-limb
//! columns ([`ConsumedMulLimbs`]) equal the silo's proven values. C5-2a-ii bound
//! the Double half. This module binds every operand and the output of the
//! **MixedAdd** half, closing the other side of the "C5" EC-ladder hole.
//!
//! ## The MixedAdd formula (15 muls; verified by symbolic replay of
//! `rcb_mixed_add_with_mul_rows`, `projective_rcb_mul/trace.rs`)
//!
//! The consumer's `lhs`/`rhs` are AFFINE points; the accumulator (`lhs`) is
//! lifted to projective with `z1 = 1` (see `ProjectivePoint::from_prepared` —
//! every primitive MixedAdd row has a finite accumulator, so `z1 = 1`; the
//! `lhs = ∞` accumulator state is a `MsbInit` row that produces NO primitive
//! op, so it never reaches this consumer). With `x1 = lhs.x`, `y1 = lhs.y`,
//! `z1 = 1`, `x2 = rhs.x`, `y2 = rhs.y`, `b` = P-256 curve constant, `R_k` =
//! result of mul `k`:
//!
//! ```text
//! M0  x1·x2                       M1  y1·y2
//! M2  (x2+y2)·(x1+y1)             M3  y2·z1 (=y2·1)
//! M4  x2·z1 (=x2·1)              M5  b·z1 (=b·1)
//! M6  b·(R4+x1)
//! M7  (R3+y1)·(3R6−3R0−9z1)       M8  (3R0−3z1)·(3R6−3R0−9z1)
//! M9  (R1+3R4−3R5+3x1)·(R1−3R4+3R5−3x1)
//! M10 (R2−R0−R1)·(R1+3R4−3R5+3x1) M11 (R3+y1)·(R1−3R4+3R5−3x1)
//! M12 (R2−R0−R1)·(3R0−3z1)
//! output (projective): x3 = R10−R7,  y3 = R8+R9,  z3 = R11+R12
//! M13 output_affine.x · z3 = R13      M14 output_affine.y · z3 = R14
//! ```
//!
//! (the `3z1`/`9z1` constant terms above use `z1 = 1`, materialized as the
//! reduced constant `1` source so the signed-carry reductions see them as a
//! coefficient times a committed limb vector, like every other combo term.)
//!
//! ## Constraints added (all gated by `mixed_active = active · (1 − op)`)
//!
//! 1. **Operand binding** — each consumed mul's `lhs`/`rhs` committed limbs are
//!    pinned to the correct quantity. 11 are single reduced sources with
//!    coefficient `+1` (`operand == src` limb-wise, degree 1); the other 18 are
//!    multi-term/coefficient combos pinned via the signed-carry reduction idiom
//!    ([`add_combo_reduction`]). This is the soundness crux: binding only the
//!    *result* would let a prover pair a correct product with wrong operands.
//! 2. **Output projective** — committed working values `x3,y3,z3` pinned via
//!    reductions to `R10−R7`, `R8+R9`, `R11+R12`.
//! 3. **Affine-normalization (z3≠0 gated)** — `R13 == x3` and `R14 == y3`
//!    (limb-wise), gated by `out_finite = 1 − output.inf`. Since the silo proved
//!    `R13 = affine.x·z3`, `R14 = affine.y·z3`, on a finite output (z3≠0) this
//!    forces `output = (x3/z3, y3/z3)` = the unique correct affine point.
//! 4. **Infinity / non-degeneracy** — `output.inf · z3.limb[i] == 0` forbids
//!    claiming `inf=1` while `z3≠0` (escaping the affine binding on a finite
//!    output). P-256 has prime order; the only finite-input output-infinity
//!    MixedAdd is `P + (−P) = ∞`, whose RCB projective output is `z3 = 0`
//!    (verified numerically), so the gate is complete there (`inf=1`,
//!    affine binding released) and `inf=0` is infeasible (it would force the
//!    released affine binding to hold against a `z3 = 0` that makes `R13 = R14 =
//!    0`, contradicting a finite `output`).
//! 5. **Infinity-operand no-op** — a MixedAdd whose affine operand (`rhs`) is
//!    `∞` (`rhs.inf = 1`) emits ZERO silo muls and returns the accumulator
//!    unchanged: `lhs + ∞ = lhs`. The formula constraints (1–4) are gated off on
//!    these rows by `formula_gate = mixed_active · (1 − rhs.inf) = 0`, so the
//!    output is pinned directly: `output = lhs` (`output.x == lhs.x`,
//!    `output.y == lhs.y`, `output.inf == lhs.inf`), gated by
//!    `mixed_active · rhs.inf`. Since the accumulator is finite, this correctly
//!    copies it through. (Soundness: the EC-row relation already binds `output`
//!    to the producer; this adds the in-AIR coordinate identity for the no-op so
//!    a forged no-op output is also caught locally. The gate uses the affine
//!    operand's own `rhs.inf` flag, which on an active MixedAdd row equals
//!    `1 − has_muls` since `has_muls` is constrained to `1 − (1−op)·rhs.inf`.)
//!
//! Soundness of the reduction idiom with only 13-bit-limb (not canonical `< p`)
//! operands is identical to [`super::double_formula`]: the per-limb signed-carry
//! recurrence with final carry 0 proves the integer identity `combo = operand +
//! q·p`, i.e. `operand ≡ combo (mod p)`; the operand's only downstream use is as
//! a silo-product factor (depends only on the value mod p). `q` is pinned only
//! transitively by the carry range check + 13-bit operands.

use stwo::core::fields::m31::M31;
use stwo_constraint_framework::EvalAtRow;
use stwo_p256_utils::constants::N_LIMBS;

use super::double_formula::{
    add_combo_reduction, bind_equal, constant_bigint, curve_b_bigint, modulus_bigint, one_bigint,
    read_bigint, solve_combo_reduction, term, DoubleFormulaColumns, M31Term, ReductionWitness,
};
use crate::limbs::{P256EvalBigInt, P256M31BigInt};
use crate::projective_air::ConsumedMulLimbsView;

/// Number of silo muls whose operands the MixedAdd formula binds via the
/// signed-carry reduction idiom (multi-term / coefficient ≠ 1 combos).
pub(crate) const MIXED_ADD_OPERAND_REDUCTIONS: usize = 15;
/// Number of output working-value reductions (`x3`, `y3`, `z3`).
pub(crate) const MIXED_ADD_OUTPUT_REDUCTIONS: usize = 3;
/// Total signed-carry reductions the MixedAdd formula performs per active row.
pub(crate) const MIXED_ADD_TOTAL_REDUCTIONS: usize =
    MIXED_ADD_OPERAND_REDUCTIONS + MIXED_ADD_OUTPUT_REDUCTIONS;

/// Number of witnessed degree-1 gate columns (`mixed_active`, `formula_gate`)
/// the MixedAdd formula commits so its operand/reduction/output bindings stay at
/// degree 2 (the effective ceiling of stwo's SubDomain composition; binding by
/// the inline degree-3 product `active·(1−op)·(1−rhs.inf)` pushes the limb
/// bindings to degree 4, which aliases in the composition quotient even though
/// the constraint is 0 on every trace row).
pub(crate) const MIXED_ADD_GATE_COLUMNS: usize = 2;

/// Committed working values + reduction witnesses + witnessed gate columns for
/// the MixedAdd formula.
///
/// Read order (must match the base-trace writer in `air.rs`):
/// `x3, y3, z3` bigints, then the [`MIXED_ADD_TOTAL_REDUCTIONS`] reduction
/// witnesses in canonical order (the 15 operand reductions, then `x3`,`y3`,`z3`
/// output reductions), then the two witnessed gate columns `mixed_active_col`,
/// `formula_gate_col` (appended LAST so the x3/y3/z3 + reduction column offsets
/// the Range13 / signed-carry USE lists reference are unchanged).
pub(crate) struct MixedAddFormulaColumns<E: EvalAtRow> {
    pub x3: P256EvalBigInt<E>,
    pub y3: P256EvalBigInt<E>,
    pub z3: P256EvalBigInt<E>,
    pub reductions: [ReductionWitness<E>; MIXED_ADD_TOTAL_REDUCTIONS],
    /// Witnessed `mixed_active = active · (1 − op)` (degree-1 column).
    pub mixed_active_col: E::F,
    /// Witnessed `formula_gate = mixed_active · (1 − rhs.inf)` (degree-1 column).
    pub formula_gate_col: E::F,
}

impl<E: EvalAtRow> MixedAddFormulaColumns<E> {
    pub(crate) fn read(eval: &mut E) -> Self {
        let x3 = read_bigint(eval);
        let y3 = read_bigint(eval);
        let z3 = read_bigint(eval);
        let reductions = core::array::from_fn(|_| ReductionWitness::read(eval));
        let mixed_active_col = eval.next_trace_mask();
        let formula_gate_col = eval.next_trace_mask();
        Self {
            x3,
            y3,
            z3,
            reductions,
            mixed_active_col,
            formula_gate_col,
        }
    }

    /// The Double formula's view of this (shared) formula block.
    ///
    /// The Double block's shape — `x3, y3, z3` working values followed by
    /// [`DOUBLE_TOTAL_REDUCTIONS`] reduction witnesses — is a strict prefix
    /// of the MixedAdd block's, and the two formulas' gates
    /// (`active · op` vs `active · (1 − op)`) are mutually exclusive per
    /// row, so both formulas constrain the SAME committed cells: on a
    /// Double row they hold the Double witness (with the MixedAdd-only
    /// reduction suffix forced to zero), on a MixedAdd row the MixedAdd
    /// witness.
    pub(crate) fn double_view(&self) -> DoubleFormulaColumns<E> {
        DoubleFormulaColumns {
            x3: self.x3.clone(),
            y3: self.y3.clone(),
            z3: self.z3.clone(),
            reductions: core::array::from_fn(|slot| ReductionWitness {
                q: self.reductions[slot].q.clone(),
                carries: self.reductions[slot].carries.clone(),
            }),
        }
    }
}

/// Base-trace column count of the MixedAdd-formula block: three bigints plus the
/// per-reduction `(q + N_LIMBS carries)` columns plus the two witnessed gate
/// columns.
pub(crate) const MIXED_ADD_FORMULA_COLUMNS: usize = SHARED_FORMULA_COLUMNS;

/// Bind the full MixedAdd-op coordinate formula on this consumer row.
///
/// `gate = mixed_active = active · (1 − op)` (1 only on active MixedAdd rows).
/// `rhs_inf` is the affine operand's infinity flag: `rhs_inf = 1` marks the
/// 0-mul no-op (`lhs + ∞ = lhs`), so the silo-mul formula is gated by
/// `mixed_active · (1 − rhs_inf)` and the no-op copy by `mixed_active · rhs_inf`.
/// `x1`/`y1` are the affine input (accumulator) coordinates (lifted with
/// `z1 = 1`); `x2`/`y2` are the affine operand (`rhs`) coordinates;
/// `output_x`/`output_y` are the committed affine output coordinates;
/// `output_inf` is the output infinity flag; `lhs_inf` is the accumulator's
/// infinity flag (drives the no-op `output.inf == lhs.inf` copy).
/// `muls` exposes the consumed silo mul `(lhs, rhs, result)` limbs for M0..M14.
/// `range13` is the consumer-local Range13 relation.
#[allow(clippy::too_many_arguments)]
pub(crate) fn bind_mixed_add_formula<E: EvalAtRow>(
    eval: &mut E,
    gate: &E::F,
    rhs_inf: &E::F,
    x1: &P256EvalBigInt<E>,
    y1: &P256EvalBigInt<E>,
    x2: &P256EvalBigInt<E>,
    y2: &P256EvalBigInt<E>,
    lhs_inf: &E::F,
    output_x: &P256EvalBigInt<E>,
    output_y: &P256EvalBigInt<E>,
    output_inf: &E::F,
    muls: &ConsumedMulLimbsView<E>,
    columns: &MixedAddFormulaColumns<E>,
    range13_values: &mut Vec<E::F>,
) {
    let one = E::F::from(M31::from_u32_unchecked(1));
    let one_const = constant_bigint::<E>(&one_bigint());
    let b_const = constant_bigint::<E>(&curve_b_bigint());

    // Result accessor (R_k = result limbs of mul k).
    let r = |k: usize| muls.result(k);

    // ---- Witnessed degree-1 gate columns (the degree-control crux) ----
    // The silo-mul bindings below pin a committed limb (degree 1) to a target.
    // The natural gate is `mixed_active · (1 − rhs.inf) = active·(1−op)·(1−rhs.inf)`
    // (degree 3); multiplied by the degree-1 limb difference that is a degree-4
    // constraint. stwo evaluates the composition quotient on a domain of only
    // `2^(log_size+1)` points (its SubDomain mode), which represents quotients of
    // constraints up to degree 2 ONLY — a degree-3+ binding aliases there and
    // fails OODS even though it is identically 0 on every trace row (so
    // `assert_constraints_on_trace`, which samples only trace rows, still passes).
    // The fix mirrors the proven `scalar_mod_mul` pattern: witness the gate as a
    // degree-1 committed column and constrain it with a degree-2 identity, so each
    // binding is `gate_col(deg 1)·(limb − target)(deg 1)` = degree 2.
    //
    //   mixed_active_col == mixed_active  (= active·(1−op), the degree-2 `gate`)
    //   formula_gate_col == mixed_active_col · (1 − rhs.inf)  (degree-2 identity)
    //
    // Both definitions are degree ≤ 2, and both columns are forced to 0 off
    // MixedAdd rows by the `mixed_active` definition (op=1 ⇒ 0; padding active=0 ⇒
    // 0), so they leak nothing and need no extra boolean/zero gate.
    let mixed_active_col = columns.mixed_active_col.clone();
    let formula_gate = columns.formula_gate_col.clone();
    // mixed_active_col == active·(1−op) (the `gate` passed in is exactly that).
    eval.add_constraint(mixed_active_col.clone() - gate.clone());
    // formula_gate_col == mixed_active_col · (1 − rhs.inf).
    eval.add_constraint(
        formula_gate.clone() - mixed_active_col.clone() * (one.clone() - rhs_inf.clone()),
    );

    // ----- (1a) Operand bindings: single reduced source, coefficient +1 -----
    // Operand dedup: M0/M1/M3/M4/M5 lhs+rhs are dropped consumed-mul slots
    // whose consume-tuple values are the bound expressions already
    // (`ConsumedMulLimbs::fill_dropped`); only M6.lhs (a kept column, combo-
    // reduced in the Double kind) still needs its pin: M6.lhs b.
    bind_equal(eval, &formula_gate, muls.lhs(6), &b_const);

    // ----- (1b) Operand bindings: multi-term / coefficient ≠ 1 reductions -----
    // Reduction-witness slot order (must match the trace writer):
    //   0: M2.lhs  x2+y2
    //   1: M2.rhs  x1+y1
    //   2: M6.rhs  R4+x1
    //   3: M7.lhs  R3+y1
    //   4: M7.rhs  3R6−3R0−9z1
    //   5: M8.lhs  3R0−3z1
    //   6: M8.rhs  3R6−3R0−9z1
    //   7: M9.lhs  R1+3R4−3R5+3x1
    //   8: M9.rhs  R1−3R4+3R5−3x1
    //   9: M10.lhs R2−R0−R1
    //  10: M10.rhs R1+3R4−3R5+3x1
    //  11: M11.lhs R3+y1
    //  12: M11.rhs R1−3R4+3R5−3x1
    //  13: M12.lhs R2−R0−R1
    //  14: M12.rhs 3R0−3z1
    let combo_x2y2 = [term(1, x2), term(1, y2)];
    let combo_x1y1 = [term(1, x1), term(1, y1)];
    let combo_r4x1 = [term(1, r(4)), term(1, x1)];
    let combo_r3y1 = [term(1, r(3)), term(1, y1)];
    let combo_yy = [term(3, r(6)), term(-3, r(0)), term(-9, &one_const)];
    let combo_3r0 = [term(3, r(0)), term(-3, &one_const)];
    let combo_x3p = [term(1, r(1)), term(3, r(4)), term(-3, r(5)), term(3, x1)];
    let combo_z3p = [term(1, r(1)), term(-3, r(4)), term(3, r(5)), term(-3, x1)];
    let combo_t3 = [term(-1, r(0)), term(-1, r(1)), term(1, r(2))];

    add_combo_reduction(
        eval,
        &formula_gate,
        muls.lhs(2),
        &combo_x2y2,
        &columns.reductions[0],
    );
    add_combo_reduction(
        eval,
        &formula_gate,
        muls.rhs(2),
        &combo_x1y1,
        &columns.reductions[1],
    );
    add_combo_reduction(
        eval,
        &formula_gate,
        muls.rhs(6),
        &combo_r4x1,
        &columns.reductions[2],
    );
    add_combo_reduction(
        eval,
        &formula_gate,
        muls.lhs(7),
        &combo_r3y1,
        &columns.reductions[3],
    );
    add_combo_reduction(
        eval,
        &formula_gate,
        muls.rhs(7),
        &combo_yy,
        &columns.reductions[4],
    );
    add_combo_reduction(
        eval,
        &formula_gate,
        muls.lhs(8),
        &combo_3r0,
        &columns.reductions[5],
    );
    add_combo_reduction(
        eval,
        &formula_gate,
        muls.rhs(8),
        &combo_yy,
        &columns.reductions[6],
    );
    add_combo_reduction(
        eval,
        &formula_gate,
        muls.lhs(9),
        &combo_x3p,
        &columns.reductions[7],
    );
    add_combo_reduction(
        eval,
        &formula_gate,
        muls.rhs(9),
        &combo_z3p,
        &columns.reductions[8],
    );
    add_combo_reduction(
        eval,
        &formula_gate,
        muls.lhs(10),
        &combo_t3,
        &columns.reductions[9],
    );
    add_combo_reduction(
        eval,
        &formula_gate,
        muls.rhs(10),
        &combo_x3p,
        &columns.reductions[10],
    );
    add_combo_reduction(
        eval,
        &formula_gate,
        muls.lhs(11),
        &combo_r3y1,
        &columns.reductions[11],
    );
    add_combo_reduction(
        eval,
        &formula_gate,
        muls.rhs(11),
        &combo_z3p,
        &columns.reductions[12],
    );
    add_combo_reduction(
        eval,
        &formula_gate,
        muls.lhs(12),
        &combo_t3,
        &columns.reductions[13],
    );
    add_combo_reduction(
        eval,
        &formula_gate,
        muls.rhs(12),
        &combo_3r0,
        &columns.reductions[14],
    );

    // ----- (2) Output projective working values -----
    // x3 ≡ R10 − R7,  y3 ≡ R8 + R9,  z3 ≡ R11 + R12.
    let combo_x3 = [term(1, r(10)), term(-1, r(7))];
    let combo_y3 = [term(1, r(8)), term(1, r(9))];
    let combo_z3 = [term(1, r(11)), term(1, r(12))];
    add_combo_reduction(
        eval,
        &formula_gate,
        &columns.x3,
        &combo_x3,
        &columns.reductions[15],
    );
    add_combo_reduction(
        eval,
        &formula_gate,
        &columns.y3,
        &combo_y3,
        &columns.reductions[16],
    );
    add_combo_reduction(
        eval,
        &formula_gate,
        &columns.z3,
        &combo_z3,
        &columns.reductions[17],
    );

    // ----- (3a) Affine-normalization OPERAND binding (the link to `output`) ----
    // Operand dedup: M13/M14's operands are dropped consumed-mul slots whose
    // consume-tuple values are `output.x`/`output.y` and
    // `z3_double + z3_mixed`; the consume↔provider balance pins the silo
    // operands to those columns on every `has_muls` row (see the Double
    // binder's (3a) note).

    // ----- (3b) Affine-normalization RESULT binding, gated by out_finite -------
    // R13 == x3,  R14 == y3 (limb-wise). Combined with (3a)'s R13 = output.x·z3,
    // R14 = output.y·z3, on a finite output (z3≠0) these force
    // output = (x3/z3, y3/z3) — the unique correct affine point.
    //
    // Gated by `mixed_active_col · out_finite` (degree 2 using the witnessed
    // degree-1 `mixed_active_col`), NOT `formula_gate · out_finite`. Dropping
    // `has_muls` here is SOUND+COMPLETE: on an infinity-operand no-op row
    // (`has_muls = 0`) the silo proves no muls, so the committed `R13 =
    // result(13)` and `x3` are BOTH zero, and `out_finite = 1` (the no-op output
    // = the finite accumulator), so the binding is the vacuous `0 == 0`. On a
    // finite-mul row `mixed_active = formula_gate` (since `has_muls = 1`), so the
    // binding is identical to gating by `formula_gate`. The result limb (degree 1)
    // and `x3` are both zeroed off-MixedAdd (x3 by `not_mixed`), so the binding
    // has the same degree-≤2 effective composition profile as the Double formula's
    // affine-result binding (which proves under the same SubDomain mode).
    let out_finite = one.clone() - output_inf.clone();
    let affine_gate = mixed_active_col.clone() * out_finite;
    bind_equal(eval, &affine_gate, muls.result(13), &columns.x3);
    bind_equal(eval, &affine_gate, muls.result(14), &columns.y3);

    // ----- (4) Non-degeneracy / infinity: output.inf · z3.limb[i] == 0 -----
    // Forbids claiming inf=1 while z3≠0 (escaping the affine binding on a finite
    // output). Complete: honest P+(−P)=∞ has RCB projective z3 = 0. Gated by
    // `mixed_active_col · output_inf` (using the witnessed degree-1
    // `mixed_active_col`, so the limb constraint is degree 3 like the Double
    // formula's `inf · z3` binding; dropping `has_muls` is sound — a no-op row has
    // `output_inf = lhs_inf = 0`, so the gate vanishes).
    let inf_gate = mixed_active_col.clone() * output_inf.clone();
    for i in 0..N_LIMBS {
        eval.add_constraint(inf_gate.clone() * columns.z3.limbs()[i].clone());
    }

    // ----- (5) Infinity-operand no-op: lhs + ∞ = lhs -----
    // An infinity-operand MixedAdd (`rhs.inf = 1`) emits no silo muls and returns
    // the accumulator unchanged: `output = lhs`. The formula above is gated off
    // (`formula_gate = mixed_active·(1−rhs.inf) = 0`), so pin the output to the
    // accumulator directly: x/y limb-wise and the infinity flag. The accumulator
    // is finite, so `output.inf == lhs.inf == 0`, but constraining the flag too
    // leaves no freedom. Gated by `noop_gate = mixed_active · rhs.inf` (1 exactly
    // on no-op MixedAdd rows; `rhs.inf` is used instead of `1 − has_muls` for the
    // same low-degree-extension reason as `formula_gate`).
    let noop_gate = mixed_active_col.clone() * rhs_inf.clone();
    bind_equal(eval, &noop_gate, output_x, x1);
    bind_equal(eval, &noop_gate, output_y, y1);
    eval.add_constraint(noop_gate.clone() * (output_inf.clone() - lhs_inf.clone()));

    // ----- Range-checked values (fixed count, γ-digest) -----
    // Cover the affine input/operand/output coords and the x3/y3/z3 working
    // values so the reduction headroom (no M31 wraparound) holds and padding
    // leaks nothing. The consumed mul limbs are already Range13-checked by the
    // silo. The values are COLLECTED (in the fixed
    // `mixed_add_formula_range13_use_columns` order) into the caller's
    // γ-digest; the tall expander emits the actual range uses.
    for limb in x1
        .limbs()
        .iter()
        .chain(y1.limbs())
        .chain(x2.limbs())
        .chain(y2.limbs())
        .chain(output_x.limbs())
        .chain(output_y.limbs())
        .chain(columns.x3.limbs())
        .chain(columns.y3.limbs())
        .chain(columns.z3.limbs())
    {
        range13_values.push(limb.clone());
    }
}

// ===========================================================================
// Prover-side witness generation
// ===========================================================================

use crate::projective::ProjectivePoint;

/// Concrete (M31) MixedAdd-formula witness: the `x3,y3,z3` working-value limbs
/// and the `(q, carries)` of each of the [`MIXED_ADD_TOTAL_REDUCTIONS`]
/// reductions, in the SAME order the AIR reads them.
pub(crate) struct MixedAddFormulaWitness {
    pub x3: P256M31BigInt,
    pub y3: P256M31BigInt,
    pub z3: P256M31BigInt,
    pub reductions: [(i64, [i64; N_LIMBS]); MIXED_ADD_TOTAL_REDUCTIONS],
}

/// Extract the M31 limbs of mul `k`'s result `R_k` from the flat consumed-mul
/// limb array (`[lhs|rhs|result] × 15`, each `N_LIMBS`).
fn result_limbs(mul_limbs: &[M31], k: usize) -> P256M31BigInt {
    let base = k * 3 * N_LIMBS + 2 * N_LIMBS;
    P256M31BigInt::from_limbs(core::array::from_fn(|i| mul_limbs[base + i]))
}

/// Compute the concrete MixedAdd-formula witness from the silo's flat mul-limb
/// array and the projective output coordinates. Mirrors
/// [`bind_mixed_add_formula`]'s reduction list exactly (operand reductions
/// 0..14, then x3/y3/z3 outputs).
pub(crate) fn solve_mixed_add_formula_witness(
    mul_limbs: &[M31],
    output_projective: &ProjectivePoint,
) -> Option<MixedAddFormulaWitness> {
    let modulus = modulus_bigint();
    let one = one_bigint();
    let r = |k: usize| result_limbs(mul_limbs, k);

    // Operand targets (the silo's committed lhs/rhs limbs of the reduced muls).
    let operand = |k: usize, role: usize| -> P256M31BigInt {
        let base = k * 3 * N_LIMBS + role * N_LIMBS;
        P256M31BigInt::from_limbs(core::array::from_fn(|i| mul_limbs[base + i]))
    };
    // x1 = M0.lhs, y1 = M1.lhs, x2 = M0.rhs, y2 = M1.rhs (bound to those above).
    let x1 = operand(0, 0);
    let y1 = operand(1, 0);
    let x2 = operand(0, 1);
    let y2 = operand(1, 1);
    let (r0, r1, r2, r3, r4, r5, r6) = (r(0), r(1), r(2), r(3), r(4), r(5), r(6));
    let (r7, r8, r9, r10, r11, r12) = (r(7), r(8), r(9), r(10), r(11), r(12));

    let x3 = P256M31BigInt::from_u256(&output_projective.x.to_u256());
    let y3 = P256M31BigInt::from_u256(&output_projective.y.to_u256());
    let z3 = P256M31BigInt::from_u256(&output_projective.z.to_u256());

    // Reduction targets + combos (same slot order as the AIR):
    //  0 M2.lhs x2+y2          1 M2.rhs x1+y1          2 M6.rhs R4+x1
    //  3 M7.lhs R3+y1          4 M7.rhs 3R6−3R0−9z1    5 M8.lhs 3R0−3z1
    //  6 M8.rhs 3R6−3R0−9z1    7 M9.lhs R1+3R4−3R5+3x1 8 M9.rhs R1−3R4+3R5−3x1
    //  9 M10.lhs R2−R0−R1     10 M10.rhs R1+3R4−3R5+3x1 11 M11.lhs R3+y1
    // 12 M11.rhs R1−3R4+3R5−3x1 13 M12.lhs R2−R0−R1    14 M12.rhs 3R0−3z1
    // 15 x3=R10−R7           16 y3=R8+R9             17 z3=R11+R12
    let specs: [(P256M31BigInt, Vec<M31Term>); MIXED_ADD_TOTAL_REDUCTIONS] = [
        (operand(2, 0), vec![tt(1, &x2), tt(1, &y2)]),
        (operand(2, 1), vec![tt(1, &x1), tt(1, &y1)]),
        (operand(6, 1), vec![tt(1, &r4), tt(1, &x1)]),
        (operand(7, 0), vec![tt(1, &r3), tt(1, &y1)]),
        (operand(7, 1), vec![tt(3, &r6), tt(-3, &r0), tt(-9, &one)]),
        (operand(8, 0), vec![tt(3, &r0), tt(-3, &one)]),
        (operand(8, 1), vec![tt(3, &r6), tt(-3, &r0), tt(-9, &one)]),
        (
            operand(9, 0),
            vec![tt(1, &r1), tt(3, &r4), tt(-3, &r5), tt(3, &x1)],
        ),
        (
            operand(9, 1),
            vec![tt(1, &r1), tt(-3, &r4), tt(3, &r5), tt(-3, &x1)],
        ),
        (operand(10, 0), vec![tt(-1, &r0), tt(-1, &r1), tt(1, &r2)]),
        (
            operand(10, 1),
            vec![tt(1, &r1), tt(3, &r4), tt(-3, &r5), tt(3, &x1)],
        ),
        (operand(11, 0), vec![tt(1, &r3), tt(1, &y1)]),
        (
            operand(11, 1),
            vec![tt(1, &r1), tt(-3, &r4), tt(3, &r5), tt(-3, &x1)],
        ),
        (operand(12, 0), vec![tt(-1, &r0), tt(-1, &r1), tt(1, &r2)]),
        (operand(12, 1), vec![tt(3, &r0), tt(-3, &one)]),
        (x3.clone(), vec![tt(1, &r10), tt(-1, &r7)]),
        (y3.clone(), vec![tt(1, &r8), tt(1, &r9)]),
        (z3.clone(), vec![tt(1, &r11), tt(1, &r12)]),
    ];

    let mut reductions = [(0i64, [0i64; N_LIMBS]); MIXED_ADD_TOTAL_REDUCTIONS];
    for (slot, (target, terms)) in specs.iter().enumerate() {
        reductions[slot] = solve_combo_reduction(target, terms, &modulus)?;
    }
    Some(MixedAddFormulaWitness {
        x3,
        y3,
        z3,
        reductions,
    })
}

fn tt<'a>(coeff: i64, src: &'a P256M31BigInt) -> M31Term<'a> {
    M31Term { coeff, src }
}

/// Flatten a [`MixedAddFormulaWitness`] into the [`MIXED_ADD_FORMULA_COLUMNS`]
/// M31 trace cells in AIR read order: `x3,y3,z3` limbs, then per reduction the
/// `(q, carries)` (signed values centered-encoded), then the two witnessed gate
/// columns `mixed_active`, `formula_gate`. This is only called for a
/// finite-operand MixedAdd row, where both gates are `1`; the caller writes the
/// gate columns directly for the other row kinds (see
/// [`mixed_add_gate_trace_values`]).
pub(crate) fn mixed_add_formula_trace_values(
    witness: &MixedAddFormulaWitness,
) -> [M31; MIXED_ADD_FORMULA_COLUMNS] {
    let mut values = [M31::from_u32_unchecked(0); MIXED_ADD_FORMULA_COLUMNS];
    let mut col = 0;
    for limb in witness
        .x3
        .limbs()
        .iter()
        .chain(witness.y3.limbs())
        .chain(witness.z3.limbs())
    {
        values[col] = *limb;
        col += 1;
    }
    for (q, carries) in &witness.reductions {
        values[col] = crate::range_checks::encode_signed_carry(*q);
        col += 1;
        for carry in carries {
            values[col] = crate::range_checks::encode_signed_carry(*carry);
            col += 1;
        }
    }
    // Witnessed gate columns: a finite-operand MixedAdd row has
    // `mixed_active = formula_gate = 1`.
    let [mixed_active, formula_gate] = mixed_add_gate_trace_values(true, true);
    values[col] = mixed_active;
    col += 1;
    values[col] = formula_gate;
    col += 1;
    debug_assert_eq!(col, MIXED_ADD_FORMULA_COLUMNS);
    values
}

/// The two witnessed gate-column M31 values for ANY consumer row, in block
/// order `[mixed_active, formula_gate]`. `is_mixed_active` = `active·(1−op)` (1
/// iff this is an active MixedAdd row, incl. the infinity-operand no-op);
/// `is_finite_mixed` = `mixed_active·(1−rhs.inf)` (1 iff a finite-operand
/// MixedAdd, i.e. `has_muls`). For Double / padding both are `0`; for a no-op
/// MixedAdd `mixed_active = 1`, `formula_gate = 0`. The AIR constrains these
/// columns to exactly these definitions, so they must be written for EVERY row
/// (not only the finite-MixedAdd rows whose witness block is otherwise nonzero).
pub(crate) fn mixed_add_gate_trace_values(
    is_mixed_active: bool,
    is_finite_mixed: bool,
) -> [M31; 2] {
    [
        M31::from_u32_unchecked(is_mixed_active as u32),
        M31::from_u32_unchecked(is_finite_mixed as u32),
    ]
}

/// Block-relative column offset of the first witnessed gate column
/// (`mixed_active`) in the shared formula block.
pub(crate) const MIXED_ADD_GATE_OFFSET_IN_BLOCK: usize = SHARED_FORMULA_GATE_OFFSET_IN_BLOCK;
