//! C5-2a-ii: in-AIR constraint of the projective **Double** EC-op coordinate
//! formula on the fake-GLV projective-source consumer.
//!
//! ## What this closes
//!
//! The silo ([`projective_rcb_mul`]) proves, per source op, the **15** field
//! products `result_k = lhs_k · rhs_k (mod p)` (`k = 0..14`), and the C5-1
//! plumbing makes the consumer's committed mul-limb columns
//! ([`ConsumedMulLimbs`]) equal the silo's proven values. But nothing yet tied
//! those products' *operands* to the input point's coordinates / prior results,
//! nor the *result combination* to the committed affine `output`. So a forged
//! `output` survived. This module binds every operand and the output, closing
//! the Double half of the "C5" EC-ladder hole. (MixedAdd is a separate task.)
//!
//! ## The Double formula (15 muls; verified by symbolic replay of
//! `rcb_double_with_mul_rows`, `projective_rcb_mul/trace.rs`)
//!
//! Inputs are affine ⇒ `z1 = 1`. `b` = P-256 curve constant. `x1 = lhs.x`,
//! `y1 = lhs.y`. `R_k` = result of mul `k`:
//!
//! ```text
//! M0  x1·x1            M1  y1·y1             M2  z1·z1 (=1·1)
//! M3  x1·y1            M4  x1·z1 (=x1·1)     M5  b·R2
//! M6  (R1−3R5+6R4)·(R1+3R5−6R4)             M7  (R1−3R5+6R4)·(2R3)
//! M8  b·(2R4)          M9  (3R0−3R2)·(3R8−9R2−3R0)
//! M10 y1·z1 (=y1·1)    M11 (2R10)·(3R8−9R2−3R0)   M12 (2R10)·R1
//! output (projective): x3 = R7−R11,  y3 = R6+R9,  z3 = 4·R12
//! M13 output_affine.x · z3 = R13      M14 output_affine.y · z3 = R14
//! ```
//!
//! ## Constraints added (all gated by `double_active = active · op`)
//!
//! 1. **Operand binding** — each consumed mul's `lhs`/`rhs` committed limbs are
//!    pinned to the correct quantity. 16 are single reduced sources with
//!    coefficient `+1` (`operand == src` limb-wise, degree 1); the other 10 are
//!    multi-term/coefficient combos pinned via the signed-carry reduction idiom
//!    ([`add_combo_reduction`]). This is the soundness crux: binding only the
//!    *result* would let a prover pair a correct product with wrong operands.
//! 2. **Output projective** — committed working values `x3,y3,z3` pinned via
//!    reductions to `R7−R11`, `R6+R9`, `4·R12`.
//! 3. **Affine-normalization (z3≠0 gated)** — `R13 == x3` and `R14 == y3`
//!    (limb-wise), gated by `out_finite = 1 − output.inf`. Since the silo proved
//!    `R13 = affine.x·z3`, `R14 = affine.y·z3`, on a finite output (z3≠0) this
//!    forces `output = (x3/z3, y3/z3)` = the unique correct affine point.
//! 4. **Infinity / non-degeneracy** — `output.inf · z3.limb[i] == 0` forbids
//!    claiming `inf=1` while `z3≠0` (which would escape the affine binding on a
//!    finite output). P-256 has prime order, so the only infinity-output Double
//!    is `double(∞) = ∞`, whose projective output is canonically `(0,1,0)`
//!    (z3 limbs all 0, y3=1); the gate is complete there and `inf=0` is
//!    infeasible (it would force `y3 == 0` against the pinned `y3 = R6+R9 = 1`).
//!    This replaces the `z3·z3_inv` non-degeneracy witness from the task brief,
//!    which would require a multi-limb field multiplication with no backing silo
//!    mul; the limb constraint is sound, complete, and field-mul-free.
//!
//! Soundness of the reduction idiom with only 13-bit-limb (not canonical `< p`)
//! operands: the per-limb signed-carry recurrence with final carry 0 proves the
//! integer identity `combo = operand + q·p`, i.e. `operand ≡ combo (mod p)`.
//! The operand's only downstream use is as a factor in the silo product
//! `result = lhs·rhs (mod p)`, which depends only on the operand's value mod p,
//! so a non-canonical representative is harmless — exactly the basis on which
//! `final_add` binds its (also non-canonical) operands. `q` is pinned only
//! TRANSITIVELY, not directly: the per-limb recurrence has the shape
//! `… − q·p_i + prev_carry − 2^13·carry_i = 0` with the carries range-checked
//! and the operands 13-bit-bounded, so a `q` outside its small honest window
//! cannot close the carry chain (it would force an out-of-range carry). Hence
//! no explicit `q`-range product constraint is needed — the carry range check
//! plus 13-bit operands already constrain `q`.

use stwo::core::fields::m31::M31;
use stwo_constraint_framework::EvalAtRow;
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};

use crate::constants::{P256_B, P256_MODULUS};
use crate::limbs::{P256EvalBigInt, P256M31BigInt};
use crate::projective_air::ConsumedMulLimbsView;
use crate::range_checks::{add_range_check, RangeCheckRelation};
use crate::types::U256;

/// Number of silo muls whose operands the Double formula binds via the
/// signed-carry reduction idiom (multi-term / coefficient ≠ 1 combos).
pub(crate) const DOUBLE_OPERAND_REDUCTIONS: usize = 10;
/// Number of output working-value reductions (`x3`, `y3`, `z3`).
pub(crate) const DOUBLE_OUTPUT_REDUCTIONS: usize = 3;
/// Total signed-carry reductions the Double formula performs per active row.
pub(crate) const DOUBLE_TOTAL_REDUCTIONS: usize =
    DOUBLE_OPERAND_REDUCTIONS + DOUBLE_OUTPUT_REDUCTIONS;

/// One signed-carry reduction's witness columns: the integer quotient `q`
/// (signed, centered-encoded) and the `N_LIMBS` signed carries.
pub(crate) struct ReductionWitness<E: EvalAtRow> {
    pub q: E::F,
    pub carries: [E::F; N_LIMBS],
}

impl<E: EvalAtRow> ReductionWitness<E> {
    pub(crate) fn read(eval: &mut E) -> Self {
        Self {
            q: eval.next_trace_mask(),
            carries: core::array::from_fn(|_| eval.next_trace_mask()),
        }
    }
}

/// Committed working values + reduction witnesses for the Double formula.
///
/// Read order (must match the base-trace writer in `trace.rs`):
/// `x3, y3, z3` bigints, then the [`DOUBLE_TOTAL_REDUCTIONS`] reduction
/// witnesses in canonical order (the 10 operand reductions, then `x3`,`y3`,`z3`
/// output reductions).
pub(crate) struct DoubleFormulaColumns<E: EvalAtRow> {
    pub x3: P256EvalBigInt<E>,
    pub y3: P256EvalBigInt<E>,
    pub z3: P256EvalBigInt<E>,
    pub reductions: [ReductionWitness<E>; DOUBLE_TOTAL_REDUCTIONS],
}

impl<E: EvalAtRow> DoubleFormulaColumns<E> {
    pub(crate) fn read(eval: &mut E) -> Self {
        let x3 = read_bigint(eval);
        let y3 = read_bigint(eval);
        let z3 = read_bigint(eval);
        Self {
            x3,
            y3,
            z3,
            reductions: core::array::from_fn(|_| ReductionWitness::read(eval)),
        }
    }
}

/// Base-trace column count of the Double-formula block: three bigints plus the
/// per-reduction `(q + N_LIMBS carries)` columns.
pub(crate) const DOUBLE_FORMULA_COLUMNS: usize =
    3 * N_LIMBS + DOUBLE_TOTAL_REDUCTIONS * (1 + N_LIMBS);

pub(crate) fn read_bigint<E: EvalAtRow>(eval: &mut E) -> P256EvalBigInt<E> {
    P256EvalBigInt::<E>::from_limbs(core::array::from_fn(|_| eval.next_trace_mask()))
}

pub(crate) fn modulus_bigint() -> P256M31BigInt {
    P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS))
}

pub(crate) fn curve_b_bigint() -> P256M31BigInt {
    P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_B))
}

/// The reduced field constant `1` as a [`P256M31BigInt`] (= the projective `z`
/// coordinate of any affine accumulator, since the consumer's `lhs`/`rhs` are
/// affine points lifted with `z = 1`).
pub(crate) fn one_bigint() -> P256M31BigInt {
    P256M31BigInt::from_u256(&U256::from_le_u64s(&[1, 0, 0, 0]))
}

fn fixed_limb<E: EvalAtRow>(value: &P256M31BigInt, index: usize) -> E::F {
    E::F::from(value.limbs()[index])
}

/// A signed-integer-coefficient term `coeff · src` of a reduction's right-hand
/// linear combination. `src` limbs are committed field values.
pub(crate) struct ComboTerm<'a, E: EvalAtRow> {
    pub coeff: i64,
    pub src: &'a P256EvalBigInt<E>,
}

/// Constrain `target ≡ Σ_j coeff_j · src_j (mod p)` over 13-bit limbs with the
/// signed-carry reduction idiom (mirrors `final_add`'s `add_sub_reduction`,
/// generalized to arbitrary signed integer coefficients).
///
/// Per limb `i` (gated):
/// `Σ_j coeff_j·src_j.limb[i] − target.limb[i] − q·p_i + prev_carry − 2^13·carry_i = 0`,
/// with `prev_carry_0 = 0` and `carry_{N−1} = 0`. Summed with limb weights this
/// telescopes to the exact integer identity `Σ coeff·src = target + q·p`, hence
/// `target ≡ combo (mod p)`. Degree 2 (`gate · recurrence`, `recurrence` linear
/// in the witnesses since `q·p_i` has a constant `p_i`).
///
/// The caller is responsible for range-checking `target`'s limbs and `q`/`carry`
/// columns; this routine only emits the recurrence + final-carry-zero constraint.
pub(crate) fn add_combo_reduction<E: EvalAtRow>(
    eval: &mut E,
    gate: &E::F,
    target: &P256EvalBigInt<E>,
    terms: &[ComboTerm<'_, E>],
    witness: &ReductionWitness<E>,
) {
    let zero = E::F::from(M31::from_u32_unchecked(0));
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    let modulus = modulus_bigint();
    for i in 0..N_LIMBS {
        let prev = if i == 0 {
            zero.clone()
        } else {
            witness.carries[i - 1].clone()
        };
        // Σ_j coeff_j · src_j.limb[i]
        let mut combo = zero.clone();
        for term in terms {
            let limb = term.src.limbs()[i].clone();
            combo = combo + signed_coeff_mul::<E>(term.coeff, limb);
        }
        let recurrence = combo - target.limbs()[i].clone()
            - witness.q.clone() * fixed_limb::<E>(&modulus, i)
            + prev
            - limb_base.clone() * witness.carries[i].clone();
        eval.add_constraint(gate.clone() * recurrence);
    }
    eval.add_constraint(gate.clone() * witness.carries[N_LIMBS - 1].clone());
}

/// `coeff · limb` for a signed integer `coeff`, expressed in `E::F`
/// (`coeff < 0` ⟹ subtract `|coeff| · limb`).
fn signed_coeff_mul<E: EvalAtRow>(coeff: i64, limb: E::F) -> E::F {
    let magnitude = E::F::from(M31::from_u32_unchecked(coeff.unsigned_abs() as u32));
    let scaled = magnitude * limb;
    if coeff < 0 {
        E::F::from(M31::from_u32_unchecked(0)) - scaled
    } else {
        scaled
    }
}

/// Limb-wise equality `target == src` over all `N_LIMBS` limbs, gated. Used for
/// the operand bindings whose combo is a single reduced source with coefficient
/// `+1` (the silo and the source are then equal as integers, degree 1).
pub(crate) fn bind_equal<E: EvalAtRow>(
    eval: &mut E,
    gate: &E::F,
    target: &P256EvalBigInt<E>,
    src: &P256EvalBigInt<E>,
) {
    for i in 0..N_LIMBS {
        eval.add_constraint(gate.clone() * (target.limbs()[i].clone() - src.limbs()[i].clone()));
    }
}

/// A reduced field constant (`1`, `b`) materialized as a [`P256EvalBigInt`] so
/// it can be a [`bind_equal`] source.
pub(crate) fn constant_bigint<E: EvalAtRow>(value: &P256M31BigInt) -> P256EvalBigInt<E> {
    P256EvalBigInt::<E>::from_limbs(core::array::from_fn(|i| E::F::from(value.limbs()[i])))
}

/// Bind the full Double-op coordinate formula on this consumer row.
///
/// `gate = double_active = active · op` (1 only on active Double rows). `x1`/`y1`
/// are the affine input (accumulator) coordinates; `output_x`/`output_y` are the
/// committed affine output coordinates; `output_inf` is the output infinity flag.
/// `muls` exposes the consumed silo mul `(lhs, rhs, result)` limbs for M0..M14.
/// `range13` is the consumer-local Range13 relation (its limbs of `x1,y1,
/// output_*,x3,y3,z3` are range-checked here so the reduction headroom holds).
#[allow(clippy::too_many_arguments)]
pub(crate) fn bind_double_formula<E: EvalAtRow>(
    eval: &mut E,
    gate: &E::F,
    active: &E::F,
    x1: &P256EvalBigInt<E>,
    y1: &P256EvalBigInt<E>,
    output_x: &P256EvalBigInt<E>,
    output_y: &P256EvalBigInt<E>,
    output_inf: &E::F,
    muls: &ConsumedMulLimbsView<E>,
    columns: &DoubleFormulaColumns<E>,
    range13: &RangeCheckRelation,
) {
    let one = E::F::from(M31::from_u32_unchecked(1));
    let one_const = constant_bigint::<E>(&P256M31BigInt::from_u256(&U256::from_le_u64s(&[
        1, 0, 0, 0,
    ])));
    let b_const = constant_bigint::<E>(&curve_b_bigint());

    // Convenient result/operand accessors (R_k = result limbs of mul k).
    let r = |k: usize| muls.result(k);

    // ----- (1a) Operand bindings: single reduced source, coefficient +1 -----
    // M0 x1·x1, M1 y1·y1, M2 z1·z1 (z1=1), M3 x1·y1, M4 x1·z1, M5 b·R2,
    // M8.lhs b, M10 y1·z1, M12.rhs R1.
    bind_equal(eval, gate, muls.lhs(0), x1);
    bind_equal(eval, gate, muls.rhs(0), x1);
    bind_equal(eval, gate, muls.lhs(1), y1);
    bind_equal(eval, gate, muls.rhs(1), y1);
    bind_equal(eval, gate, muls.lhs(2), &one_const);
    bind_equal(eval, gate, muls.rhs(2), &one_const);
    bind_equal(eval, gate, muls.lhs(3), x1);
    bind_equal(eval, gate, muls.rhs(3), y1);
    bind_equal(eval, gate, muls.lhs(4), x1);
    bind_equal(eval, gate, muls.rhs(4), &one_const);
    bind_equal(eval, gate, muls.lhs(5), &b_const);
    bind_equal(eval, gate, muls.rhs(5), r(2));
    bind_equal(eval, gate, muls.lhs(8), &b_const);
    bind_equal(eval, gate, muls.lhs(10), y1);
    bind_equal(eval, gate, muls.rhs(10), &one_const);
    bind_equal(eval, gate, muls.rhs(12), r(1));

    // ----- (1b) Operand bindings: multi-term / coefficient ≠ 1 reductions -----
    // Reduction-witness slot order (must match trace.rs):
    //   0: M6.lhs  R1−3R5+6R4
    //   1: M6.rhs  R1+3R5−6R4
    //   2: M7.lhs  R1−3R5+6R4
    //   3: M7.rhs  2R3
    //   4: M8.rhs  2R4
    //   5: M9.lhs  3R0−3R2
    //   6: M9.rhs  3R8−9R2−3R0
    //   7: M11.lhs 2R10
    //   8: M11.rhs 3R8−9R2−3R0
    //   9: M12.lhs 2R10
    let combo_m6lhs = [term(1, r(1)), term(-3, r(5)), term(6, r(4))];
    let combo_m6rhs = [term(1, r(1)), term(3, r(5)), term(-6, r(4))];
    let combo_2r3 = [term(2, r(3))];
    let combo_2r4 = [term(2, r(4))];
    let combo_m9lhs = [term(3, r(0)), term(-3, r(2))];
    let combo_t = [term(3, r(8)), term(-9, r(2)), term(-3, r(0))];
    let combo_2r10 = [term(2, r(10))];

    add_combo_reduction(eval, gate, muls.lhs(6), &combo_m6lhs, &columns.reductions[0]);
    add_combo_reduction(eval, gate, muls.rhs(6), &combo_m6rhs, &columns.reductions[1]);
    add_combo_reduction(eval, gate, muls.lhs(7), &combo_m6lhs, &columns.reductions[2]);
    add_combo_reduction(eval, gate, muls.rhs(7), &combo_2r3, &columns.reductions[3]);
    add_combo_reduction(eval, gate, muls.rhs(8), &combo_2r4, &columns.reductions[4]);
    add_combo_reduction(eval, gate, muls.lhs(9), &combo_m9lhs, &columns.reductions[5]);
    add_combo_reduction(eval, gate, muls.rhs(9), &combo_t, &columns.reductions[6]);
    add_combo_reduction(eval, gate, muls.lhs(11), &combo_2r10, &columns.reductions[7]);
    add_combo_reduction(eval, gate, muls.rhs(11), &combo_t, &columns.reductions[8]);
    add_combo_reduction(eval, gate, muls.lhs(12), &combo_2r10, &columns.reductions[9]);

    // ----- (2) Output projective working values -----
    // x3 ≡ R7 − R11,  y3 ≡ R6 + R9,  z3 ≡ 4·R12.
    let combo_x3 = [term(1, r(7)), term(-1, r(11))];
    let combo_y3 = [term(1, r(6)), term(1, r(9))];
    let combo_z3 = [term(4, r(12))];
    add_combo_reduction(eval, gate, &columns.x3, &combo_x3, &columns.reductions[10]);
    add_combo_reduction(eval, gate, &columns.y3, &combo_y3, &columns.reductions[11]);
    add_combo_reduction(eval, gate, &columns.z3, &combo_z3, &columns.reductions[12]);

    // ----- (3a) Affine-normalization OPERAND binding (the link to `output`) ----
    // The silo proves R13 = M13.lhs · M13.rhs and R14 = M14.lhs · M14.rhs, but
    // those operands are free witnesses in the silo. Bind them to the committed
    // affine output coords and `z3` so R13 = output.x·z3, R14 = output.y·z3 hold
    // for THIS row's committed `output`. Without this, a prover could feed the
    // silo a different `output.x` than the one the EC-row relation carries (the
    // forged-output hole). Unconditional on Double rows (the silo computes these
    // for every Double, finite or infinity).
    bind_equal(eval, gate, muls.lhs(13), output_x);
    bind_equal(eval, gate, muls.rhs(13), &columns.z3);
    bind_equal(eval, gate, muls.lhs(14), output_y);
    bind_equal(eval, gate, muls.rhs(14), &columns.z3);

    // ----- (3b) Affine-normalization RESULT binding, gated by out_finite -------
    // R13 == x3,  R14 == y3 (limb-wise). Combined with (3a)'s R13 = output.x·z3,
    // R14 = output.y·z3, on a finite output (z3≠0) these force
    // output = (x3/z3, y3/z3) — the unique correct affine point.
    let out_finite = one.clone() - output_inf.clone();
    let affine_gate = gate.clone() * out_finite;
    bind_equal(eval, &affine_gate, muls.result(13), &columns.x3);
    bind_equal(eval, &affine_gate, muls.result(14), &columns.y3);

    // ----- (4) Non-degeneracy / infinity: output.inf · z3.limb[i] == 0 -----
    // Forbids claiming inf=1 while z3≠0 (escaping the affine binding on a finite
    // output). Complete: honest double(∞)=∞ has canonical z3 limbs all 0.
    let inf_gate = gate.clone() * output_inf.clone();
    for i in 0..N_LIMBS {
        eval.add_constraint(inf_gate.clone() * columns.z3.limbs()[i].clone());
    }

    // ----- Range checks (gated `active`, fixed count): every witnessed limb the
    // reductions read on the combo side or pin on the target side. The consumed
    // mul limbs are already Range13-checked by the silo; here we cover the
    // affine input/output coords and the x3/y3/z3 working values so the reduction
    // headroom (no M31 wraparound) holds and padding leaks nothing. The signed
    // carries + quotients are range-checked separately by the caller against the
    // consumer-local signed-carry table.
    for limb in x1
        .limbs()
        .iter()
        .chain(y1.limbs())
        .chain(output_x.limbs())
        .chain(output_y.limbs())
        .chain(columns.x3.limbs())
        .chain(columns.y3.limbs())
        .chain(columns.z3.limbs())
    {
        add_range_check(eval, range13, active.clone(), limb.clone());
    }
}

pub(crate) fn term<'a, E: EvalAtRow>(coeff: i64, src: &'a P256EvalBigInt<E>) -> ComboTerm<'a, E> {
    ComboTerm { coeff, src }
}

// ===========================================================================
// Prover-side witness generation
// ===========================================================================

use crate::projective::ProjectivePoint;

/// Concrete (M31) Double-formula witness: the `x3,y3,z3` working-value limbs and
/// the `(q, carries)` of each of the [`DOUBLE_TOTAL_REDUCTIONS`] reductions, in
/// the SAME order the AIR reads them. `q` and `carries` are signed integers
/// (centered-encoded into M31 when written to the trace).
pub(crate) struct DoubleFormulaWitness {
    pub x3: P256M31BigInt,
    pub y3: P256M31BigInt,
    pub z3: P256M31BigInt,
    pub reductions: [(i64, [i64; N_LIMBS]); DOUBLE_TOTAL_REDUCTIONS],
}

/// One M31 reduction source term `coeff · src`.
pub(crate) struct M31Term<'a> {
    pub coeff: i64,
    pub src: &'a P256M31BigInt,
}

/// Solve `Σ coeff_j·src_j ≡ target (mod p)` for the signed quotient `q` and the
/// signed carries: per limb `Σ coeff_j·src_j.limb[i] − target.limb[i] − q·p_i +
/// prev − 2^13·carry_i = 0`, final carry 0. `q` is determined as
/// `(Σcoeff·src_value − target_value) / p`; we then verify the carry chain
/// closes. Returns `None` if no valid `(q, carries)` exists (a prover bug).
pub(crate) fn solve_combo_reduction(
    target: &P256M31BigInt,
    terms: &[M31Term<'_>],
    modulus: &P256M31BigInt,
) -> Option<(i64, [i64; N_LIMBS])> {
    let base = 1i64 << LIMB_BITS;
    // q = (combo_value - target_value) / p over the integers. Compute the combo
    // and target as big integers via limb weights in i128 (260-bit fits i128? no
    // — 2^260 > i128). Instead derive q from the limb recurrence directly: run
    // the carry chain symbolically with q unknown is awkward, so we search a
    // small signed window for q (the combos' value/p ratio is bounded by the
    // coefficient magnitudes, |q| ≤ ~16).
    let coeff_sum: i64 = terms.iter().map(|t| t.coeff.abs()).sum();
    let q_bound = coeff_sum + 2;
    for q in -q_bound..=q_bound {
        if let Some(carries) = try_combo_carries(target, terms, modulus, q, base) {
            return Some((q, carries));
        }
    }
    None
}

fn try_combo_carries(
    target: &P256M31BigInt,
    terms: &[M31Term<'_>],
    modulus: &P256M31BigInt,
    q: i64,
    base: i64,
) -> Option<[i64; N_LIMBS]> {
    let mut carries = [0i64; N_LIMBS];
    let mut prev = 0i64;
    for (i, carry) in carries.iter_mut().enumerate() {
        let mut combo = 0i64;
        for t in terms {
            combo += t.coeff * i64::from(t.src.limbs()[i].0);
        }
        let total = combo - i64::from(target.limbs()[i].0) - q * i64::from(modulus.limbs()[i].0)
            + prev;
        if total % base != 0 {
            return None;
        }
        *carry = total / base;
        prev = *carry;
    }
    if carries[N_LIMBS - 1] == 0 {
        Some(carries)
    } else {
        None
    }
}

/// Extract the M31 limbs of mul `k`'s result `R_k` from the flat consumed-mul
/// limb array (`[lhs|rhs|result] × 15`, each `N_LIMBS`).
fn result_limbs(mul_limbs: &[M31], k: usize) -> P256M31BigInt {
    let base = k * 3 * N_LIMBS + 2 * N_LIMBS;
    P256M31BigInt::from_limbs(core::array::from_fn(|i| mul_limbs[base + i]))
}

/// Compute the concrete Double-formula witness from the silo's flat mul-limb
/// array and the projective output coordinates. Mirrors [`bind_double_formula`]'s
/// reduction list exactly (operand reductions 0..9, then x3/y3/z3 outputs).
pub(crate) fn solve_double_formula_witness(
    mul_limbs: &[M31],
    output_projective: &ProjectivePoint,
) -> Option<DoubleFormulaWitness> {
    let modulus = modulus_bigint();
    let r = |k: usize| result_limbs(mul_limbs, k);

    // Operand targets (the silo's committed lhs/rhs limbs of the reduced muls).
    let operand = |k: usize, role: usize| -> P256M31BigInt {
        let base = k * 3 * N_LIMBS + role * N_LIMBS;
        P256M31BigInt::from_limbs(core::array::from_fn(|i| mul_limbs[base + i]))
    };
    let (r0, r1, r2, r3, r4, r5) = (r(0), r(1), r(2), r(3), r(4), r(5));
    let (r6, r7, r8, r9, r10, r11, r12) = (r(6), r(7), r(8), r(9), r(10), r(11), r(12));

    let x3 = P256M31BigInt::from_u256(&output_projective.x.to_u256());
    let y3 = P256M31BigInt::from_u256(&output_projective.y.to_u256());
    let z3 = P256M31BigInt::from_u256(&output_projective.z.to_u256());

    // Reduction targets + combos (same slot order as the AIR):
    //  0 M6.lhs  R1−3R5+6R4   1 M6.rhs R1+3R5−6R4   2 M7.lhs R1−3R5+6R4
    //  3 M7.rhs  2R3          4 M8.rhs 2R4           5 M9.lhs 3R0−3R2
    //  6 M9.rhs  3R8−9R2−3R0  7 M11.lhs 2R10         8 M11.rhs 3R8−9R2−3R0
    //  9 M12.lhs 2R10        10 x3=R7−R11           11 y3=R6+R9   12 z3=4R12
    let specs: [(P256M31BigInt, Vec<M31Term>); DOUBLE_TOTAL_REDUCTIONS] = [
        (operand(6, 0), vec![tt(1, &r1), tt(-3, &r5), tt(6, &r4)]),
        (operand(6, 1), vec![tt(1, &r1), tt(3, &r5), tt(-6, &r4)]),
        (operand(7, 0), vec![tt(1, &r1), tt(-3, &r5), tt(6, &r4)]),
        (operand(7, 1), vec![tt(2, &r3)]),
        (operand(8, 1), vec![tt(2, &r4)]),
        (operand(9, 0), vec![tt(3, &r0), tt(-3, &r2)]),
        (operand(9, 1), vec![tt(3, &r8), tt(-9, &r2), tt(-3, &r0)]),
        (operand(11, 0), vec![tt(2, &r10)]),
        (operand(11, 1), vec![tt(3, &r8), tt(-9, &r2), tt(-3, &r0)]),
        (operand(12, 0), vec![tt(2, &r10)]),
        (x3.clone(), vec![tt(1, &r7), tt(-1, &r11)]),
        (y3.clone(), vec![tt(1, &r6), tt(1, &r9)]),
        (z3.clone(), vec![tt(4, &r12)]),
    ];

    let mut reductions = [(0i64, [0i64; N_LIMBS]); DOUBLE_TOTAL_REDUCTIONS];
    for (slot, (target, terms)) in specs.iter().enumerate() {
        reductions[slot] = solve_combo_reduction(target, terms, &modulus)?;
    }
    Some(DoubleFormulaWitness {
        x3,
        y3,
        z3,
        reductions,
    })
}

fn tt<'a>(coeff: i64, src: &'a P256M31BigInt) -> M31Term<'a> {
    M31Term { coeff, src }
}

/// Flatten a [`DoubleFormulaWitness`] into the [`DOUBLE_FORMULA_COLUMNS`] M31
/// trace cells in AIR read order: `x3,y3,z3` limbs, then per reduction the
/// `(q, carries)` (signed values centered-encoded).
pub(crate) fn double_formula_trace_values(
    witness: &DoubleFormulaWitness,
) -> [M31; DOUBLE_FORMULA_COLUMNS] {
    let mut values = [M31::from_u32_unchecked(0); DOUBLE_FORMULA_COLUMNS];
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
    debug_assert_eq!(col, DOUBLE_FORMULA_COLUMNS);
    values
}

// (The Range13 / signed-carry USE values are collected directly from the
// consumer base trace in `air.rs` via the `*_uses_from_base` helpers, so the
// provider multiplicities tally exactly the columns the AIR range-checks.)
