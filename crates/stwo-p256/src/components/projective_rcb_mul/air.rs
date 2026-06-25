//! AIR constraint evaluation (FrameworkEval impls, column readers, constraint builders) for the
//! projective RCB multiplication AIR family.
//!
//! Split out of `mod.rs` (pure relocation, no behavioral change).

use stwo::core::fields::m31::M31;
use stwo_constraint_framework::{EvalAtRow, RelationEntry};
use stwo_p256_utils::constants::N_LIMBS;

use super::*;
use crate::limbs::P256EvalBigInt;

pub const PROJECTIVE_RCB_SIGNED_CARRY_EQUATION: &str = "projective_rcb_reduction";

pub const PROJECTIVE_RCB_SIGNED_CARRY_BOUND: i64 = projective_rcb_signed_carry_bound();

pub const PROJECTIVE_RCB_MUL_ROLE_LHS: u32 = 0;

pub const PROJECTIVE_RCB_MUL_ROLE_RHS: u32 = 1;

pub const PROJECTIVE_RCB_MUL_ROLE_RESULT: u32 = 2;

const PROJECTIVE_RCB_MUL_RESULT_ROLES: [u32; 3] = [
    PROJECTIVE_RCB_MUL_ROLE_LHS,
    PROJECTIVE_RCB_MUL_ROLE_RHS,
    PROJECTIVE_RCB_MUL_ROLE_RESULT,
];

/// An EC op's consumed silo mul limbs, committed as base-trace columns on a
/// projective-source consumer. Indexed `[mul_index][role][limb_index]` in the
/// SAME canonical order as `projective_rcb_op_mul_limbs` so the LogUp keys line
/// up with the silo's provided yields. C5-2 will constrain the coordinate
/// formula on these columns; C5-1 only pins them equal to the silo via balance.
///
/// `has_muls` is a committed boolean gate: `1` iff the op emitted the full
/// `PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP` muls (Double, or MixedAdd with a finite
/// operand), `0` for an infinity-operand MixedAdd no-op (which the silo proves
/// with ZERO muls). The consume is gated by `has_muls` so a 0-mul op consumes
/// nothing, matching the silo provider and keeping the 3-way balance closed.
pub struct ConsumedMulLimbs<E: EvalAtRow> {
    /// Committed `has_muls` flag (column 0 of the consumed-mul block).
    pub has_muls: E::F,
    pub limbs: [[[E::F; N_LIMBS]; 3]; PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP],
}

/// Operand dedup: which consumed-mul slots remain committed columns.
///
/// Both coordinate-formula binders bind these operand slots to EXISTING row
/// columns / constants with `bind_equal` (Double and MixedAdd alike):
/// M0/M1/M3/M4/M5/M13/M14 lhs+rhs. Their consume-tuple values are therefore
/// built as expressions of those columns ([`ConsumedMulLimbs::fill_dropped`])
/// instead of committing a verbatim copy — the consume↔provider LogUp balance
/// pins the silo operands directly to the expressions, which is the same
/// binding the old column+`bind_equal` pair provided, one hop shorter.
/// Results are always committed (consumed AND used as combo sources), and
/// operand slots that are combo-reduced in EITHER kind keep their columns.
pub const fn consumed_mul_slot_kept(mul: usize, role: usize) -> bool {
    if role == 2 {
        return !matches!(mul, 13 | 14);
    }
    !matches!(mul, 0 | 1 | 3 | 4 | 5 | 13 | 14)
}

/// Dropped slots whose unified expression is degree 2 (a genuine
/// `op·a + (1−op)·b` mix of distinct columns): their LogUp entries must sit in
/// solo batches (denominator degree 2 + cumulative term = 3, the `log_size+1`
/// ceiling). The other dropped slots are constants, shared columns, or the
/// degree-1 `z3_double + z3_mixed` sum (inactive block zero-forced).
pub const fn consumed_mul_slot_degree2(mul: usize, role: usize) -> bool {
    matches!(
        (mul, role),
        (0, 1) | (1, 1) | (3, 0) | (3, 1) | (4, 0) | (5, 1) | (13, 2) | (14, 2)
    )
}

/// Number of committed consumed-mul slots (31 of 45).
pub const CONSUMED_MUL_KEPT_SLOTS: usize = {
    let mut count = 0;
    let mut mul = 0;
    while mul < PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP {
        let mut role = 0;
        while role < 3 {
            if consumed_mul_slot_kept(mul, role) {
                count += 1;
            }
            role += 1;
        }
        mul += 1;
    }
    count
};

/// Committed column offset (within the consumed-mul block, after `has_muls`)
/// of a kept slot's first limb. `None` for dropped slots.
pub const fn consumed_mul_kept_column(mul: usize, role: usize) -> Option<usize> {
    if !consumed_mul_slot_kept(mul, role) {
        return None;
    }
    let mut offset = 0;
    let mut m = 0;
    while m < PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP {
        let mut r = 0;
        while r < 3 {
            if m == mul && r == role {
                return Some(offset);
            }
            if consumed_mul_slot_kept(m, r) {
                offset += N_LIMBS;
            }
            r += 1;
        }
        m += 1;
    }
    None
}

/// Base-trace column count of the consumed-mul block: the `has_muls` flag plus
/// the KEPT slots' limb columns (operand dedup — see
/// [`consumed_mul_slot_kept`]).
pub const CONSUMED_MUL_LIMBS_COLUMNS: usize = 1 + CONSUMED_MUL_KEPT_SLOTS * N_LIMBS;

/// The row columns the dropped operand slots' consume expressions read.
/// `op` selects the formula kind (1 = Double, 0 = MixedAdd); the points are
/// the EC row's committed coordinates; `z3_double`/`z3_mixed` are the two
/// formula blocks' working `z3` values (the inactive block is zero-forced, so
/// their SUM is the active kind's `z3` — degree 1).
pub struct ConsumedMulWiring<E: EvalAtRow> {
    pub op: E::F,
    pub x1: P256EvalBigInt<E>,
    pub y1: P256EvalBigInt<E>,
    pub x2: P256EvalBigInt<E>,
    pub y2: P256EvalBigInt<E>,
    pub output_x: P256EvalBigInt<E>,
    pub output_y: P256EvalBigInt<E>,
    pub output_inf: E::F,
    pub x3: P256EvalBigInt<E>,
    pub y3: P256EvalBigInt<E>,
    pub z3_double: P256EvalBigInt<E>,
    pub z3_mixed: P256EvalBigInt<E>,
}

impl<E: EvalAtRow> ConsumedMulLimbs<E> {
    /// Read the consumed-mul columns: `has_muls` first, then the
    /// `PROJECTIVE_RCB_OP_MUL_LIMB_COLUMNS` limbs in canonical order (mul_index
    /// outer, role `[LHS, RHS, RESULT]`, limb_index). Must match
    /// `projective_rcb_op_mul_limbs` + the leading flag.
    pub fn read(eval: &mut E) -> Self {
        let has_muls = eval.next_trace_mask();
        Self {
            has_muls,
            limbs: core::array::from_fn(|mul| {
                core::array::from_fn(|role| {
                    core::array::from_fn(|_limb| {
                        if consumed_mul_slot_kept(mul, role) {
                            eval.next_trace_mask()
                        } else {
                            // Placeholder until `fill_dropped` installs the
                            // operand expression.
                            E::F::from(M31::from_u32_unchecked(0))
                        }
                    })
                })
            }),
        }
    }

    /// Install the dropped operand slots' consume expressions (operand dedup).
    /// MUST be called before [`Self::consume`] / [`Self::view`]. The unified
    /// per-kind wiring (Double | MixedAdd):
    ///   M0  x1·x1   | x1·x2,   M1  y1·y1 | y1·y2,
    ///   M3  x1·y1   | y2·1,    M4  x1·1  | x2·1,
    ///   M5  b·R2    | b·1,     M13 out_x·z3,   M14 out_y·z3.
    pub fn fill_dropped(&mut self, wiring: &ConsumedMulWiring<E>) {
        let one = E::F::from(M31::from_u32_unchecked(1));
        let mixed = one.clone() - wiring.op.clone();
        let one_limbs: [M31; N_LIMBS] = core::array::from_fn(|i| {
            if i == 0 {
                M31::from_u32_unchecked(1)
            } else {
                M31::from_u32_unchecked(0)
            }
        });
        let b: [M31; N_LIMBS] = core::array::from_fn(|i| {
            crate::limbs::P256M31BigInt::from_u256(&crate::types::U256::from_le_u64s(
                &crate::constants::P256_B,
            ))
            .limbs()[i]
        });
        let pick = |a: &P256EvalBigInt<E>, b_src: &P256EvalBigInt<E>| -> [E::F; N_LIMBS] {
            core::array::from_fn(|i| {
                wiring.op.clone() * a.limbs()[i].clone() + mixed.clone() * b_src.limbs()[i].clone()
            })
        };
        let pick_const = |a: &P256EvalBigInt<E>, c: &[M31; N_LIMBS]| -> [E::F; N_LIMBS] {
            core::array::from_fn(|i| {
                wiring.op.clone() * a.limbs()[i].clone() + mixed.clone() * E::F::from(c[i])
            })
        };
        let shared = |a: &P256EvalBigInt<E>| -> [E::F; N_LIMBS] {
            core::array::from_fn(|i| a.limbs()[i].clone())
        };
        let consts =
            |c: &[M31; N_LIMBS]| -> [E::F; N_LIMBS] { core::array::from_fn(|i| E::F::from(c[i])) };
        let z3_sum: [E::F; N_LIMBS] = core::array::from_fn(|i| {
            wiring.z3_double.limbs()[i].clone() + wiring.z3_mixed.limbs()[i].clone()
        });
        let r2 = P256EvalBigInt::<E>::from_limbs(self.limbs[2][2].clone());

        self.limbs[0][0] = shared(&wiring.x1);
        self.limbs[0][1] = pick(&wiring.x1, &wiring.x2);
        self.limbs[1][0] = shared(&wiring.y1);
        self.limbs[1][1] = pick(&wiring.y1, &wiring.y2);
        self.limbs[3][0] = pick(&wiring.x1, &wiring.y2);
        self.limbs[3][1] = pick_const(&wiring.y1, &one_limbs);
        self.limbs[4][0] = pick(&wiring.x1, &wiring.x2);
        self.limbs[4][1] = consts(&one_limbs);
        self.limbs[5][0] = consts(&b);
        self.limbs[5][1] = pick_const(&r2, &one_limbs);
        self.limbs[13][0] = shared(&wiring.output_x);
        self.limbs[13][1] = z3_sum.clone();
        let out_finite = one - wiring.output_inf.clone();
        self.limbs[13][2] =
            core::array::from_fn(|i| out_finite.clone() * wiring.x3.limbs()[i].clone());
        self.limbs[14][0] = shared(&wiring.output_y);
        self.limbs[14][1] = z3_sum;
        self.limbs[14][2] =
            core::array::from_fn(|i| out_finite.clone() * wiring.y3.limbs()[i].clone());
    }

    /// Constrain the committed `has_muls` flag: boolean, zero on padding, and
    /// equal to `expected_has_muls` on active rows. `expected_has_muls` is the
    /// consumer-computed predicate `1 - (1 - op)·operand_inf` (1 for Double and
    /// finite-operand MixedAdd, 0 for an infinity-operand MixedAdd), which is
    /// exactly when the silo emits muls.
    pub fn constrain_has_muls(&self, eval: &mut E, active: &E::F, expected_has_muls: &E::F) {
        let one = one::<E>();
        eval.add_constraint(self.has_muls.clone() * (one.clone() - self.has_muls.clone()));
        eval.add_constraint((one - active.clone()) * self.has_muls.clone());
        eval.add_constraint(active.clone() * (self.has_muls.clone() - expected_has_muls.clone()));
    }

    /// CONSUME (use, `+has_muls`) every committed limb from
    /// `ProjectiveRcbMulResultRelation`, keyed `(source_index, mul_index, role,
    /// limb_index, limb)`. Gated by `has_muls` so a 0-mul op (infinity-operand
    /// MixedAdd) consumes nothing — matching the silo, which provides nothing
    /// for it. The silo provided these with `-active` over the same keys, so the
    /// LogUp balance pins each committed column equal to the silo's proven value.
    pub fn consume(
        &self,
        eval: &mut E,
        relation: &ProjectiveRcbMulResultRelation,
        source_index: &E::F,
    ) {
        for (mul_index, roles) in self.limbs.iter().enumerate() {
            for (role_index, limbs) in roles.iter().enumerate() {
                let mut values = Vec::with_capacity(3 + N_LIMBS);
                values.push(source_index.clone());
                values.push(constant(mul_index as u32));
                values.push(constant(PROJECTIVE_RCB_MUL_RESULT_ROLES[role_index]));
                values.extend(limbs.iter().cloned());
                eval.add_to_relation(RelationEntry::new(
                    relation,
                    E::EF::from(self.has_muls.clone()),
                    &values,
                ));
            }
        }
    }

    /// Materialize a [`ConsumedMulLimbsView`]: the committed `lhs`/`rhs`/`result`
    /// limbs of every mul wrapped as [`P256EvalBigInt`]s so a coordinate-formula
    /// consumer (C5-2) can bind them with the limb-reduction helpers. The view
    /// holds owned bigints (the underlying limb cells are `Clone`).
    pub fn view(&self) -> ConsumedMulLimbsView<E> {
        ConsumedMulLimbsView {
            muls: core::array::from_fn(|mul| {
                core::array::from_fn(|role| {
                    P256EvalBigInt::<E>::from_limbs(self.limbs[mul][role].clone())
                })
            }),
        }
    }
}

/// A [`ConsumedMulLimbs`] reshaped so each mul's `lhs`/`rhs`/`result` limbs are a
/// borrowable [`P256EvalBigInt`]. Indexed `[mul_index][role]` with
/// `role ∈ {0=LHS, 1=RHS, 2=RESULT}` (canonical order). Built by
/// [`ConsumedMulLimbs::view`]; consumed by the Double/MixedAdd coordinate-formula
/// constraints to bind silo mul operands/results to input coords and prior
/// results.
pub struct ConsumedMulLimbsView<E: EvalAtRow> {
    muls: [[P256EvalBigInt<E>; 3]; PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP],
}

impl<E: EvalAtRow> ConsumedMulLimbsView<E> {
    /// The `lhs` operand limbs of mul `k` (`R_k`'s left factor).
    pub fn lhs(&self, k: usize) -> &P256EvalBigInt<E> {
        &self.muls[k][0]
    }

    /// The `rhs` operand limbs of mul `k`.
    pub fn rhs(&self, k: usize) -> &P256EvalBigInt<E> {
        &self.muls[k][1]
    }

    /// The `result` limbs `R_k` of mul `k`.
    pub fn result(&self, k: usize) -> &P256EvalBigInt<E> {
        &self.muls[k][2]
    }
}

pub const fn projective_rcb_signed_carry_bound() -> i64 {
    max_i64(
        folded_digit_carry_bound(),
        fp_solinas_reduction_digit_carry_bound(),
    )
}

pub const fn projective_rcb_signed_carry_log_size() -> u32 {
    (2 * PROJECTIVE_RCB_SIGNED_CARRY_BOUND as u64 + 1)
        .next_power_of_two()
        .ilog2()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn consumed_mul_layout_drops_affine_normalization_results() {
        assert!(!consumed_mul_slot_kept(
            13,
            PROJECTIVE_RCB_MUL_ROLE_RESULT as usize
        ));
        assert!(!consumed_mul_slot_kept(
            14,
            PROJECTIVE_RCB_MUL_ROLE_RESULT as usize
        ));
        assert!(consumed_mul_slot_degree2(
            13,
            PROJECTIVE_RCB_MUL_ROLE_RESULT as usize
        ));
        assert!(consumed_mul_slot_degree2(
            14,
            PROJECTIVE_RCB_MUL_ROLE_RESULT as usize
        ));
        assert_eq!(CONSUMED_MUL_KEPT_SLOTS, 29);
        assert_eq!(CONSUMED_MUL_LIMBS_COLUMNS, 1 + 29 * N_LIMBS);
    }
}
