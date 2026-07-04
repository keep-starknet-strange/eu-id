//! Phase 2: per-field-mul EC-formula binding for the hinted-mul silo.
//!
//! The silo proves the 15 field products `R_k = lhs_k · rhs_k (mod p)` of each
//! projective EC op (`k = 0..14`), but the products' *operands* and the output
//! combination were bound OUTSIDE the silo (on the two projective-source
//! consumers, via `double_formula` / `mixed_add_formula`). Phase 2 moves that
//! binding INTO the silo so a single per-`mul_index` spec table — interpreted
//! both symbolically (AIR) and concretely (witness solver) — pins every operand
//! and the projective output on the silo rows themselves.
//!
//! # Spec table (single source of truth)
//!
//! [`FORMULA_SPEC`] transcribes the authoritative "Normalized per-k table" from
//! `tasks/rotation-impl-plan.md`. Each entry describes silo row `k` of a proj
//! group (15 contiguous rows, `mul_index` ascending). The AIR reads operand /
//! result / constant sources at the row-relative offsets the table implies (a
//! source referencing group mul `j` lives on the row `j`, i.e. offset `j − k`);
//! the solver reads group mul `j`'s concrete limbs. Slot assignment is FIXED:
//! `slot 0` targets the row's `a` operand (or `out_val` on `k = 13/14`), `slot 1`
//! targets the row's `b` operand. Where one EC-op kind combo-reduces a side and
//! the other only needs equality, the equality is expressed as a DEGENERATE
//! reduction (combo `= [(1, src)]`, carries solve to ~0) through the same slot —
//! sound because operands only matter mod p as silo product factors.
//!
//! The reduction machinery ([`add_combo_reduction`], [`solve_combo_reduction`],
//! …) lives here (moved from `fake_glv/ec_source/double_formula.rs`, which now
//! re-exports it so the Phase-3-doomed consumers keep compiling).

use stwo::core::fields::m31::M31;
use stwo_constraint_framework::EvalAtRow;
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};

use crate::constants::{P256_B, P256_MODULUS};
use crate::limbs::{P256EvalBigInt, P256M31BigInt};
use crate::types::U256;

// ===========================================================================
// Generic signed-carry reduction machinery (moved from double_formula.rs).
// ===========================================================================

/// One signed-carry reduction's witness columns: the integer quotient `q`
/// (signed, centered-encoded) and the `N_LIMBS` signed carries.
pub(crate) struct ReductionWitness<E: EvalAtRow> {
    pub q: E::F,
    pub carries: [E::F; N_LIMBS],
}

pub(crate) fn modulus_bigint() -> P256M31BigInt {
    P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS))
}

pub(crate) fn curve_b_bigint() -> P256M31BigInt {
    P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_B))
}

/// The reduced field constant `1`.
pub(crate) fn one_bigint() -> P256M31BigInt {
    P256M31BigInt::from_u256(&U256::from_le_u64s(&[1, 0, 0, 0]))
}

pub(crate) fn fixed_limb<E: EvalAtRow>(value: &P256M31BigInt, index: usize) -> E::F {
    E::F::from(value.limbs()[index])
}

/// A signed-integer-coefficient term `coeff · src` of a reduction's right-hand
/// linear combination. `src` limbs are committed field values.
pub(crate) struct ComboTerm<'a, E: EvalAtRow> {
    pub coeff: i64,
    pub src: &'a P256EvalBigInt<E>,
}

pub(crate) fn term<'a, E: EvalAtRow>(coeff: i64, src: &'a P256EvalBigInt<E>) -> ComboTerm<'a, E> {
    ComboTerm { coeff, src }
}

/// `coeff · limb` for a signed integer `coeff`, expressed in `E::F`.
pub(crate) fn signed_coeff_mul<E: EvalAtRow>(coeff: i64, limb: E::F) -> E::F {
    let magnitude = E::F::from(M31::from_u32_unchecked(coeff.unsigned_abs() as u32));
    let scaled = magnitude * limb;
    if coeff < 0 {
        E::F::from(M31::from_u32_unchecked(0)) - scaled
    } else {
        scaled
    }
}

/// Muxed signed-carry reduction: constrain
/// `target ≡ op·Σ double + (1−op)·Σ mixed (mod p)`, gated by `gate` (the
/// `is_proj_k` preprocessed one-hot). Per limb `i`:
/// `gate·(op·comboD_i + (1−op)·comboM_i − target_i − q·p_i + prev − 2^13·carry_i)`
/// plus `gate·last_carry`. Degree ≤ 3 (`gate(1)·[op(1)·linear(1)]`).
///
/// `op_expr` is the group header's `op` flag read at offset `−k` (1 = Double).
/// Either term list may be empty (that kind imposes no reduction here); the mux
/// still zeroes the absent side.
pub(crate) fn add_muxed_combo_reduction<E: EvalAtRow>(
    eval: &mut E,
    gate: &E::F,
    op_expr: &E::F,
    target: &[E::F; N_LIMBS],
    double: &[ComboTerm<'_, E>],
    mixed: &[ComboTerm<'_, E>],
    witness: &ReductionWitness<E>,
) {
    let zero = E::F::from(M31::from_u32_unchecked(0));
    let one = E::F::from(M31::from_u32_unchecked(1));
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    let modulus = modulus_bigint();
    let not_op = one - op_expr.clone();
    for i in 0..N_LIMBS {
        let prev = if i == 0 {
            zero.clone()
        } else {
            witness.carries[i - 1].clone()
        };
        let mut combo_d = zero.clone();
        for t in double {
            combo_d += signed_coeff_mul::<E>(t.coeff, t.src.limbs()[i].clone());
        }
        let mut combo_m = zero.clone();
        for t in mixed {
            combo_m += signed_coeff_mul::<E>(t.coeff, t.src.limbs()[i].clone());
        }
        let muxed = op_expr.clone() * combo_d + not_op.clone() * combo_m;
        let recurrence =
            muxed - target[i].clone() - witness.q.clone() * fixed_limb::<E>(&modulus, i) + prev
                - limb_base.clone() * witness.carries[i].clone();
        eval.add_constraint(gate.clone() * recurrence);
    }
    eval.add_constraint(gate.clone() * witness.carries[N_LIMBS - 1].clone());
}

/// Muxed pure equality: `gate·(op·(x − srcD) + (1−op)·(x − srcM))` per limb,
/// where `srcD`/`srcM` are optional (a kind that imposes no equality here passes
/// `None`, and its half of the mux is dropped — gate by that kind only). Degree
/// ≤ 3 (`gate(1)·op(1)·linear(1)`).
pub(crate) fn add_muxed_equality<E: EvalAtRow>(
    eval: &mut E,
    gate: &E::F,
    op_expr: &E::F,
    x: &[E::F; N_LIMBS],
    double: Option<&[E::F; N_LIMBS]>,
    mixed: Option<&[E::F; N_LIMBS]>,
) {
    let one = E::F::from(M31::from_u32_unchecked(1));
    let not_op = one - op_expr.clone();
    for i in 0..N_LIMBS {
        let mut term = E::F::from(M31::from_u32_unchecked(0));
        if let Some(d) = double {
            term += op_expr.clone() * (x[i].clone() - d[i].clone());
        }
        if let Some(m) = mixed {
            term += not_op.clone() * (x[i].clone() - m[i].clone());
        }
        eval.add_constraint(gate.clone() * term);
    }
}

/// A reduced field constant materialized as a [`P256EvalBigInt`].
pub(crate) fn constant_bigint<E: EvalAtRow>(value: &P256M31BigInt) -> P256EvalBigInt<E> {
    P256EvalBigInt::<E>::from_limbs(core::array::from_fn(|i| E::F::from(value.limbs()[i])))
}

/// One M31 reduction source term `coeff · src`.
pub(crate) struct M31Term<'a> {
    pub coeff: i64,
    pub src: &'a P256M31BigInt,
}

/// Solve `Σ coeff_j·src_j ≡ target (mod p)` for the signed quotient `q` and the
/// signed carries. See `double_formula.rs` docs (unchanged).
pub(crate) fn solve_combo_reduction(
    target: &P256M31BigInt,
    terms: &[M31Term<'_>],
    modulus: &P256M31BigInt,
) -> Option<(i64, [i64; N_LIMBS])> {
    let base = 1i64 << LIMB_BITS;
    let coeff_sum: i64 = terms.iter().map(|t| t.coeff.abs()).sum();
    let q_bound = coeff_sum + 2;
    for q in -q_bound..=q_bound {
        if let Some(carries) = try_combo_carries(target, terms, modulus, q, base) {
            return Some((q, carries));
        }
    }
    None
}

pub(crate) fn try_combo_carries(
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
        let total =
            combo - i64::from(target.limbs()[i].0) - q * i64::from(modulus.limbs()[i].0) + prev;
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

// ===========================================================================
// Shared per-mul_index spec table (single source of truth: AIR + solver).
// ===========================================================================

/// A source of limbs referenced by the formula spec. `A/B/R(j)` name group mul
/// `j`'s lhs/rhs/result columns; the AIR reads them at offset `j − k`, the
/// solver reads mul `j`'s concrete limbs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Src {
    /// This row's own `a` operand (offset 0).
    OwnA,
    /// lhs limbs of group mul `j`.
    A(usize),
    /// rhs limbs of group mul `j`.
    B(usize),
    /// result limbs of group mul `j`.
    R(usize),
    /// The reduced field constant `1`.
    One,
    /// The P-256 curve constant `b`.
    CurveB,
}

/// One signed term `coeff · src` of a combo.
#[derive(Clone, Copy, Debug)]
pub(crate) struct SpecTerm {
    pub coeff: i64,
    pub src: Src,
}

const fn t(coeff: i64, src: Src) -> SpecTerm {
    SpecTerm { coeff, src }
}

/// Reduction target side within a row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RedTarget {
    /// Slot 0 targets the row's own `a` operand.
    OwnA,
    /// Slot 0 targets the row's `out_val` cells (k = 13/14).
    OutVal,
    /// Slot 1 targets the row's own `b` operand.
    OwnB,
}

/// A muxed reduction: `target ≡ op·Σ double + (1−op)·Σ mixed (mod p)`. Empty
/// `double`/`mixed` means that kind has no reduction here (handled by gating).
#[derive(Clone, Copy, Debug)]
pub(crate) struct Reduction {
    pub target: RedTarget,
    pub double: &'static [SpecTerm],
    pub mixed: &'static [SpecTerm],
}

/// A pure muxed equality on one side (no witness): `target_side ≡ op·double_src
/// + (1−op)·mixed_src`. `None` for a kind means it imposes no constraint there
/// (gate by the present kind only).
#[derive(Clone, Copy, Debug)]
pub(crate) struct Equality {
    /// `true` ⇒ constrain the row's `a` operand; `false` ⇒ the `b` operand.
    pub is_a: bool,
    pub double: Option<Src>,
    pub mixed: Option<Src>,
}

/// Full formula spec for one silo `mul_index`.
#[derive(Clone, Copy, Debug)]
pub(crate) struct FormulaSpec {
    pub slot0: Option<Reduction>,
    pub slot1: Option<Reduction>,
    pub eqs: &'static [Equality],
}

// --- Reduction combo term lists (static; referenced by the spec below) ---
// Double combos.
const D_ONE: [SpecTerm; 1] = [t(1, Src::One)];
const D_M6L: [SpecTerm; 3] = [t(1, Src::R(1)), t(-3, Src::R(5)), t(6, Src::R(4))];
const D_M6R: [SpecTerm; 3] = [t(1, Src::R(1)), t(3, Src::R(5)), t(-6, Src::R(4))];
const D_2R3: [SpecTerm; 1] = [t(2, Src::R(3))];
const D_BC: [SpecTerm; 1] = [t(1, Src::CurveB)];
const D_2R4: [SpecTerm; 1] = [t(2, Src::R(4))];
const D_3R0M3R2: [SpecTerm; 2] = [t(3, Src::R(0)), t(-3, Src::R(2))];
const D_TT: [SpecTerm; 3] = [t(3, Src::R(8)), t(-9, Src::R(2)), t(-3, Src::R(0))];
const D_A1: [SpecTerm; 1] = [t(1, Src::A(1))];
const D_2R10: [SpecTerm; 1] = [t(2, Src::R(10))];
const D_R1: [SpecTerm; 1] = [t(1, Src::R(1))];
const D_X3: [SpecTerm; 2] = [t(1, Src::R(7)), t(-1, Src::R(11))];
const D_Z3: [SpecTerm; 1] = [t(4, Src::R(12))];
const D_Y3: [SpecTerm; 2] = [t(1, Src::R(6)), t(1, Src::R(9))];
// MixedAdd combos.
const M_B0B1: [SpecTerm; 2] = [t(1, Src::B(0)), t(1, Src::B(1))];
const M_A0A1: [SpecTerm; 2] = [t(1, Src::A(0)), t(1, Src::A(1))];
const M_BC: [SpecTerm; 1] = [t(1, Src::CurveB)];
const M_R4A0: [SpecTerm; 2] = [t(1, Src::R(4)), t(1, Src::A(0))];
const M_R3A1: [SpecTerm; 2] = [t(1, Src::R(3)), t(1, Src::A(1))];
const M_YY: [SpecTerm; 3] = [t(3, Src::R(6)), t(-3, Src::R(0)), t(-9, Src::One)];
const M_3R0: [SpecTerm; 2] = [t(3, Src::R(0)), t(-3, Src::One)];
const M_X3P: [SpecTerm; 4] = [
    t(1, Src::R(1)),
    t(3, Src::R(4)),
    t(-3, Src::R(5)),
    t(3, Src::A(0)),
];
const M_Z3P: [SpecTerm; 4] = [
    t(1, Src::R(1)),
    t(-3, Src::R(4)),
    t(3, Src::R(5)),
    t(-3, Src::A(0)),
];
const M_T3: [SpecTerm; 3] = [t(1, Src::R(2)), t(-1, Src::R(0)), t(-1, Src::R(1))];
const M_X3: [SpecTerm; 2] = [t(1, Src::R(10)), t(-1, Src::R(7))];
const M_Y3: [SpecTerm; 2] = [t(1, Src::R(8)), t(1, Src::R(9))];
const M_Z3M: [SpecTerm; 2] = [t(1, Src::R(11)), t(1, Src::R(12))];

/// Silo mul count per proj group.
pub(crate) const FORMULA_ROWS: usize = crate::projective_air::PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP;

/// The per-`mul_index` formula spec (authoritative "Normalized per-k table").
pub(crate) const FORMULA_SPEC: [FormulaSpec; FORMULA_ROWS] = [
    // k=0: D: b eq a(own) | M: none.
    FormulaSpec {
        slot0: None,
        slot1: None,
        eqs: &[Equality {
            is_a: false,
            double: Some(Src::OwnA),
            mixed: None,
        }],
    },
    // k=1: D: b eq a(own) | M: none.
    FormulaSpec {
        slot0: None,
        slot1: None,
        eqs: &[Equality {
            is_a: false,
            double: Some(Src::OwnA),
            mixed: None,
        }],
    },
    // k=2: aR: D=[1·one] M=[B(0)+B(1)]; bR: D=[1·one] M=[A(0)+A(1)].
    FormulaSpec {
        slot0: Some(Reduction {
            target: RedTarget::OwnA,
            double: &D_ONE,
            mixed: &M_B0B1,
        }),
        slot1: Some(Reduction {
            target: RedTarget::OwnB,
            double: &D_ONE,
            mixed: &M_A0A1,
        }),
        eqs: &[],
    },
    // k=3: a eq (D: A(0) | M: B(1)); b eq (D: A(1) | M: one).
    FormulaSpec {
        slot0: None,
        slot1: None,
        eqs: &[
            Equality {
                is_a: true,
                double: Some(Src::A(0)),
                mixed: Some(Src::B(1)),
            },
            Equality {
                is_a: false,
                double: Some(Src::A(1)),
                mixed: Some(Src::One),
            },
        ],
    },
    // k=4: a eq (D: A(0) | M: B(0)); b eq one (both).
    FormulaSpec {
        slot0: None,
        slot1: None,
        eqs: &[
            Equality {
                is_a: true,
                double: Some(Src::A(0)),
                mixed: Some(Src::B(0)),
            },
            Equality {
                is_a: false,
                double: Some(Src::One),
                mixed: Some(Src::One),
            },
        ],
    },
    // k=5: a eq bC (both); b eq (D: R(2) | M: one).
    FormulaSpec {
        slot0: None,
        slot1: None,
        eqs: &[
            Equality {
                is_a: true,
                double: Some(Src::CurveB),
                mixed: Some(Src::CurveB),
            },
            Equality {
                is_a: false,
                double: Some(Src::R(2)),
                mixed: Some(Src::One),
            },
        ],
    },
    // k=6: aR: D=[R1−3R5+6R4] M=[bC]; bR: D=[R1+3R5−6R4] M=[R4+A0].
    FormulaSpec {
        slot0: Some(Reduction {
            target: RedTarget::OwnA,
            double: &D_M6L,
            mixed: &M_BC,
        }),
        slot1: Some(Reduction {
            target: RedTarget::OwnB,
            double: &D_M6R,
            mixed: &M_R4A0,
        }),
        eqs: &[],
    },
    // k=7: aR: D=[R1−3R5+6R4] M=[R3+A1]; bR: D=[2R3] M=[3R6−3R0−9·one].
    FormulaSpec {
        slot0: Some(Reduction {
            target: RedTarget::OwnA,
            double: &D_M6L,
            mixed: &M_R3A1,
        }),
        slot1: Some(Reduction {
            target: RedTarget::OwnB,
            double: &D_2R3,
            mixed: &M_YY,
        }),
        eqs: &[],
    },
    // k=8: aR: D=[bC] M=[3R0−3·one]; bR: D=[2R4] M=[3R6−3R0−9·one].
    FormulaSpec {
        slot0: Some(Reduction {
            target: RedTarget::OwnA,
            double: &D_BC,
            mixed: &M_3R0,
        }),
        slot1: Some(Reduction {
            target: RedTarget::OwnB,
            double: &D_2R4,
            mixed: &M_YY,
        }),
        eqs: &[],
    },
    // k=9: aR: D=[3R0−3R2] M=[R1+3R4−3R5+3A0]; bR: D=[3R8−9R2−3R0] M=[R1−3R4+3R5−3A0].
    FormulaSpec {
        slot0: Some(Reduction {
            target: RedTarget::OwnA,
            double: &D_3R0M3R2,
            mixed: &M_X3P,
        }),
        slot1: Some(Reduction {
            target: RedTarget::OwnB,
            double: &D_TT,
            mixed: &M_Z3P,
        }),
        eqs: &[],
    },
    // k=10: aR: D=[A1] M=[R2−R0−R1]; bR: D=[one] M=[R1+3R4−3R5+3A0].
    FormulaSpec {
        slot0: Some(Reduction {
            target: RedTarget::OwnA,
            double: &D_A1,
            mixed: &M_T3,
        }),
        slot1: Some(Reduction {
            target: RedTarget::OwnB,
            double: &D_ONE,
            mixed: &M_X3P,
        }),
        eqs: &[],
    },
    // k=11: aR: D=[2R10] M=[R3+A1]; bR: D=[3R8−9R2−3R0] M=[R1−3R4+3R5−3A0].
    FormulaSpec {
        slot0: Some(Reduction {
            target: RedTarget::OwnA,
            double: &D_2R10,
            mixed: &M_R3A1,
        }),
        slot1: Some(Reduction {
            target: RedTarget::OwnB,
            double: &D_TT,
            mixed: &M_Z3P,
        }),
        eqs: &[],
    },
    // k=12: aR: D=[2R10] M=[R2−R0−R1]; bR: D=[R1] M=[3R0−3·one].
    FormulaSpec {
        slot0: Some(Reduction {
            target: RedTarget::OwnA,
            double: &D_2R10,
            mixed: &M_T3,
        }),
        slot1: Some(Reduction {
            target: RedTarget::OwnB,
            double: &D_R1,
            mixed: &M_3R0,
        }),
        eqs: &[],
    },
    // k=13: slot0→out_val: D=[R7−R11] M=[R10−R7]; bR (z3): D=[4R12] M=[R11+R12].
    FormulaSpec {
        slot0: Some(Reduction {
            target: RedTarget::OutVal,
            double: &D_X3,
            mixed: &M_X3,
        }),
        slot1: Some(Reduction {
            target: RedTarget::OwnB,
            double: &D_Z3,
            mixed: &M_Z3M,
        }),
        eqs: &[],
    },
    // k=14: slot0→out_val: D=[R6+R9] M=[R8+R9]; shared: b eq b@−1 (= B(13)).
    FormulaSpec {
        slot0: Some(Reduction {
            target: RedTarget::OutVal,
            double: &D_Y3,
            mixed: &M_Y3,
        }),
        slot1: None,
        eqs: &[Equality {
            is_a: false,
            double: Some(Src::B(13)),
            mixed: Some(Src::B(13)),
        }],
    },
];

/// Number of reduction slots per proj group that carry a witness (slot0 at
/// {2,6,7,8,9,10,11,12,13,14}, slot1 at {2,6,7,8,9,10,11,12,13}).
#[cfg(test)]
pub(crate) fn spec_slot_count() -> (usize, usize) {
    let s0 = FORMULA_SPEC.iter().filter(|s| s.slot0.is_some()).count();
    let s1 = FORMULA_SPEC.iter().filter(|s| s.slot1.is_some()).count();
    (s0, s1)
}

// ===========================================================================
// Witness solver: interpret the spec table concretely per group.
// ===========================================================================

/// Per-silo-row formula witness cells: the two reduction slots' `(q, carries)`
/// and the `out_val` limbs (nonzero only on rows 13/14). Every active proj row
/// carries this; unused slots hold `(0, [0; N])` (encoded as zero on write) so
/// the signed-table lookup passes.
#[derive(Clone, Debug)]
pub struct FormulaRowCells {
    pub out_val: [M31; N_LIMBS],
    pub slot0: (i64, [i64; N_LIMBS]),
    pub slot1: (i64, [i64; N_LIMBS]),
}

impl Default for FormulaRowCells {
    fn default() -> Self {
        Self {
            out_val: [M31::from_u32_unchecked(0); N_LIMBS],
            slot0: (0, [0; N_LIMBS]),
            slot1: (0, [0; N_LIMBS]),
        }
    }
}

/// Resolve a spec [`Src`] to concrete M31 limbs for group mul `k`'s row.
/// `muls[j]` = `(a, b, r)` limbs of group mul `j`. `own_a`/`own_b` = this row's
/// operands.
fn src_limbs(
    src: Src,
    muls: &[([M31; N_LIMBS], [M31; N_LIMBS], [M31; N_LIMBS])],
    own_a: &[M31; N_LIMBS],
    _own_b: &[M31; N_LIMBS],
    one: &P256M31BigInt,
    curve_b: &P256M31BigInt,
) -> P256M31BigInt {
    match src {
        Src::OwnA => P256M31BigInt::from_limbs(*own_a),
        Src::A(j) => P256M31BigInt::from_limbs(muls[j].0),
        Src::B(j) => P256M31BigInt::from_limbs(muls[j].1),
        Src::R(j) => P256M31BigInt::from_limbs(muls[j].2),
        Src::One => one.clone(),
        Src::CurveB => curve_b.clone(),
    }
}

/// Solve one reduction slot for group mul `k`, kind `op_double`. `target` is the
/// concrete target bigint (own operand or out_val). Returns `(q, carries)`.
fn solve_slot(
    red: &Reduction,
    op_double: bool,
    target: &P256M31BigInt,
    muls: &[([M31; N_LIMBS], [M31; N_LIMBS], [M31; N_LIMBS])],
    own_a: &[M31; N_LIMBS],
    own_b: &[M31; N_LIMBS],
    one: &P256M31BigInt,
    curve_b: &P256M31BigInt,
    modulus: &P256M31BigInt,
) -> Option<(i64, [i64; N_LIMBS])> {
    let combo = if op_double { red.double } else { red.mixed };
    // Materialize term sources (owned bigints so references outlive the call).
    let srcs: Vec<P256M31BigInt> = combo
        .iter()
        .map(|st| src_limbs(st.src, muls, own_a, own_b, one, curve_b))
        .collect();
    let terms: Vec<M31Term> = combo
        .iter()
        .zip(&srcs)
        .map(|(st, s)| M31Term {
            coeff: st.coeff,
            src: s,
        })
        .collect();
    solve_combo_reduction(target, &terms, modulus)
}

/// Compute the per-row formula cells for a whole proj group.
///
/// `muls`: the group's 15 muls' `(a, b, r)` M31 limbs (in `mul_index` order).
/// `op_double`: `true` for a Double op. `out_x`/`out_y`: the projective output
/// coordinate limbs (canonical `< p`), used as the `out_val` targets on rows
/// 13/14. Returns 15 [`FormulaRowCells`], or `None` if any reduction is
/// unsolvable (a prover bug).
pub fn solve_group_formula(
    muls: &[([M31; N_LIMBS], [M31; N_LIMBS], [M31; N_LIMBS])],
    op_double: bool,
    out_x: &[M31; N_LIMBS],
    out_y: &[M31; N_LIMBS],
) -> Option<Vec<FormulaRowCells>> {
    debug_assert_eq!(muls.len(), FORMULA_ROWS);
    let one = one_bigint();
    let curve_b = curve_b_bigint();
    let modulus = modulus_bigint();
    let mut cells = Vec::with_capacity(FORMULA_ROWS);
    for (k, spec) in FORMULA_SPEC.iter().enumerate() {
        let own_a = &muls[k].0;
        let own_b = &muls[k].1;
        let mut row = FormulaRowCells::default();
        if k == 13 || k == 14 {
            row.out_val = if k == 13 { *out_x } else { *out_y };
        }
        if let Some(red) = &spec.slot0 {
            let target = match red.target {
                RedTarget::OwnA => P256M31BigInt::from_limbs(*own_a),
                RedTarget::OutVal => P256M31BigInt::from_limbs(row.out_val),
                RedTarget::OwnB => unreachable!("slot0 never targets b"),
            };
            row.slot0 = solve_slot(
                red, op_double, &target, muls, own_a, own_b, &one, &curve_b, &modulus,
            )?;
        }
        if let Some(red) = &spec.slot1 {
            let target = P256M31BigInt::from_limbs(*own_b);
            row.slot1 = solve_slot(
                red, op_double, &target, muls, own_a, own_b, &one, &curve_b, &modulus,
            )?;
        }
        cells.push(row);
    }
    Some(cells)
}

/// A tiny projective EC trace exercising one Double, one finite MixedAdd, and
/// one infinity-operand MixedAdd no-op. Shared by the completeness/adversarial
/// tests and the spec-table cross-check. Not `#[cfg(test)]` on its own module so
/// the sibling `air.rs`/`trace.rs` tests can reuse it.
#[cfg(test)]
pub(crate) fn sample_projective_trace() -> crate::projective::ProjectiveEcTraceClaim {
    use crate::curve::{point_add, point_double};
    use crate::prepared_table::PreparedAffinePoint;
    use crate::projective::{ProjectiveEcOp, ProjectiveEcRow, ProjectiveEcTraceClaim};
    use crate::types::AffinePoint;

    let g = PreparedAffinePoint::from_affine(AffinePoint {
        x: U256::from_le_u64s(&crate::constants::P256_GX),
        y: U256::from_le_u64s(&crate::constants::P256_GY),
    });
    let g_affine = g.to_option().unwrap();
    let two_g = point_double(&g_affine).output;
    let two_g_prepared = PreparedAffinePoint::from_affine(two_g.clone());
    // Double: [2]G.
    let double_row = ProjectiveEcRow::new(
        M31::from_u32_unchecked(0),
        M31::from_u32_unchecked(0),
        ProjectiveEcOp::Double,
        &g,
        &PreparedAffinePoint::infinity(),
        &two_g_prepared,
    );
    // Finite MixedAdd: G + [2]G = [3]G.
    let three_g = point_add(&g_affine, &two_g).output;
    let mixed_row = ProjectiveEcRow::new(
        M31::from_u32_unchecked(0),
        M31::from_u32_unchecked(0),
        ProjectiveEcOp::MixedAdd,
        &g,
        &two_g_prepared,
        &PreparedAffinePoint::from_affine(three_g),
    );
    // Infinity-operand MixedAdd no-op: G + ∞ = G.
    let noop_row = ProjectiveEcRow::new(
        M31::from_u32_unchecked(0),
        M31::from_u32_unchecked(0),
        ProjectiveEcOp::MixedAdd,
        &g,
        &PreparedAffinePoint::infinity(),
        &g,
    );
    ProjectiveEcTraceClaim {
        rows: vec![double_row, mixed_row, noop_row],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::projective::ProjectiveEcOp;

    /// Cross-check the spec table against honestly generated Double and MixedAdd
    /// group witnesses: every reduction solves, and every pure equality holds
    /// limb-exact for the honest witness (honest operands are canonical, so the
    /// pinned side equals its source limb-for-limb).
    #[test]
    fn spec_table_matches_honest_group_witness() {
        let trace = sample_projective_trace();
        let claim =
            crate::projective_air::ProjectiveRcbAirTraceClaim::from_projective_trace_lite(&trace)
                .expect("proj rcb claim builds");

        let mut saw_double = false;
        let mut saw_mixed = false;
        for row in &claim.rows {
            if row.muls.is_empty() {
                continue; // infinity-operand no-op: no silo group.
            }
            let op_double = matches!(row.op, ProjectiveEcOp::Double);
            saw_double |= op_double;
            saw_mixed |= !op_double;
            let muls: Vec<_> = row
                .muls
                .iter()
                .map(|m| {
                    (
                        *m.trace.lhs.limbs(),
                        *m.trace.rhs.limbs(),
                        *m.trace.result.limbs(),
                    )
                })
                .collect();
            let out_x = *P256M31BigInt::from_u256(&row.output_projective.x.to_u256()).limbs();
            let out_y = *P256M31BigInt::from_u256(&row.output_projective.y.to_u256()).limbs();
            let cells = solve_group_formula(&muls, op_double, &out_x, &out_y)
                .expect("every reduction solves for an honest group");
            assert_eq!(cells.len(), FORMULA_ROWS);

            // Pure-equality cross-check: the pinned side equals its source limb-
            // wise (honest operands are canonical field elements).
            let one = one_bigint();
            let curve_b = curve_b_bigint();
            for (k, spec) in FORMULA_SPEC.iter().enumerate() {
                for eq in spec.eqs {
                    let src = if op_double { eq.double } else { eq.mixed };
                    let Some(src) = src else { continue };
                    let expected = src_limbs(src, &muls, &muls[k].0, &muls[k].1, &one, &curve_b);
                    let actual = if eq.is_a { muls[k].0 } else { muls[k].1 };
                    assert_eq!(
                        &actual,
                        expected.limbs(),
                        "eq mismatch at k={k} is_a={} op_double={op_double}",
                        eq.is_a
                    );
                }
            }
        }
        assert!(saw_double, "sample trace exercises a Double op");
        assert!(saw_mixed, "sample trace exercises a MixedAdd op");
    }

    /// Slot usage matches the plan (slot0 ×10, slot1 ×9).
    #[test]
    fn spec_slot_usage_matches_plan() {
        assert_eq!(spec_slot_count(), (10, 9));
    }
}
