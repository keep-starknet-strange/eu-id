//! Native witness construction and base/preprocessed trace generation for the
//! FinalAdd component: the fully-checked native claim/branch/error types, the
//! per-branch reduction solvers and checkers, and the base-trace writers.
//!
//! Split out of `mod.rs` (pure relocation, no behavioral change).

use stwo::core::fields::m31::M31;

use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};

use crate::constants::P256_MODULUS;
use crate::limbs::P256M31BigInt;
use crate::prepared_table::PreparedAffinePoint;
use crate::projective::{ProjectiveEcOp, ProjectivePoint};
use crate::projective_air::{
    gen_projective_rcb_folded_contribution_base_trace,
    gen_projective_rcb_folded_digit_base_trace, gen_projective_rcb_mul_base_trace,
    gen_projective_rcb_raw_product_chunk_base_trace, projective_rcb_signed_carry_bound,
    projective_rcb_signed_carry_log_size, ProjectiveRcbAirError, ProjectiveRcbAirRow,
    ProjectiveRcbAirTraceClaim, ProjectiveRcbMulRow, ProjectiveRcbMulStep,
    PROJECTIVE_RCB_SCHEDULE_NAMESPACE_FINAL_ADD, PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
};
use crate::range_checks::{
    encode_signed_carry, range_check_value_column_id, signed_carry_active_column_id,
    signed_carry_value_column_id, RangeCheckClaim, SignedCarryRangeClaim, RANGE13_BITS,
};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, M31ColumnEval};
use crate::types::{AffinePoint, U256};

use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

use super::*;

// ---------------------------------------------------------------------------
// Native claim
// ---------------------------------------------------------------------------

/// Active branch selector for the final-add row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FinalAddBranch {
    /// `r1`, `r2` finite, `r1.x != r2.x` (chord addition).
    DistinctAdd,
    /// `r1 == r2` finite (tangent doubling).
    DoubleAdd,
    /// `r1 = ∞`, `r2` finite (output `S = r2`).
    R2Only,
    /// `r2 = ∞`, `r1` finite (output `S = r1`).
    R1Only,
}

impl FinalAddBranch {
    fn double_add(self) -> M31 {
        match self {
            FinalAddBranch::DoubleAdd => M31::from_u32_unchecked(1),
            _ => M31::from_u32_unchecked(0),
        }
    }
}

/// Fully checked native witness for one final EC addition `S = R_1 + R_2`.
///
/// The `dx`/`dy`/`dx_inv` columns carry semantic `denom`/`numer`/`denom_inv`
/// values that differ per branch:
/// - `DistinctAdd`: `dx = x2 − x1`, `dy = y2 − y1`, `dx_inv = dx^{-1}`.
/// - `DoubleAdd`:   `dx = 2·y1`,  `dy = 3·x1^2 − 3`, `dx_inv = dx^{-1}`.
/// - Infinity branches: all three zeroed.
#[derive(Clone, Debug)]
pub struct FinalAddClaim {
    /// All mod-`p` multiplications consumed by the check row, through the
    /// shared `projective_air` mul machinery (one source row,
    /// [`FINAL_ADD_MUL_COUNT`] mul rows).
    pub mul_trace: ProjectiveRcbAirTraceClaim,
    pub sig_id: M31,
    /// Active row branch.
    pub branch: FinalAddBranch,
    /// Consumed hint `R_1` (cert0 = `u1·G`).
    pub r1: PreparedAffinePoint,
    /// Consumed hint `R_2` (cert1 = `u2·Q`).
    pub r2: PreparedAffinePoint,
    /// Slope denominator (see [`FinalAddBranch`] doc on the struct).
    pub dx: P256M31BigInt,
    pub dx_q: i64,
    pub dx_carries: [i64; N_LIMBS],
    /// Slope-denominator inverse — witnesses `dx != 0` on both finite
    /// branches (rejects `x1 == x2` for distinct and `y1 == 0` for doubling).
    pub dx_inv: P256M31BigInt,
    /// Slope numerator (see [`FinalAddBranch`] doc on the struct).
    pub dy: P256M31BigInt,
    pub dy_q: i64,
    pub dy_carries: [i64; N_LIMBS],
    /// Slope `lambda = numer / denom (mod p)` and `lamsq = lambda² mod p`.
    pub lambda: P256M31BigInt,
    pub lamsq: P256M31BigInt,
    /// Proven x-coordinate `x3 = x(S)`.
    pub x3: P256M31BigInt,
    /// `x3 + x1 + x2 ≡ lamsq (mod p)` quotient/carries. (`x2 = x1` for the
    /// doubling branch, enforced by `double_add · (r2 − r1) = 0`.)
    pub x3_q: i64,
    pub x3_carries: [i64; N_LIMBS],
    /// `x1_sq = x1·x1 mod p`. Proven by [`MUL_X1_SQUARED`] on every active
    /// row; consumed by the doubling slope-numer reduction
    /// `dy + 3 ≡ 3·x1_sq (mod p)`.
    pub x1_sq: P256M31BigInt,
}

impl FinalAddClaim {
    /// Build a final-add claim from the two pinned hint points `R_1`, `R_2`.
    ///
    /// Supports: `DistinctAdd` (`x1 != x2`), `DoubleAdd` (`r1 == r2`),
    /// `R1Only`/`R2Only` (one infinity branch).
    ///
    /// Rejects: the additive-inverse case `R_1 == -R_2` (yields `S = ∞`, an
    /// invalid ECDSA result — the AIR also makes this branch unprovable via
    /// `active · inverse_add = 0`) and both-infinity.
    pub fn from_hints(
        sig_id: M31,
        r1: &AffinePoint,
        r1_inf: bool,
        r2: &AffinePoint,
        r2_inf: bool,
    ) -> Result<Self, FinalAddError> {
        let r1_values = point_values(r1, r1_inf);
        let r2_values = point_values(r2, r2_inf);
        let modulus = U256::from_le_u64s(&P256_MODULUS);
        let zero = U256::ZERO;
        let three = U256::from_le_u64s(&[3, 0, 0, 0]);

        // Pick the branch up front so every sub-witness can route on it.
        let branch = match (r1_inf, r2_inf) {
            (true, true) => return Err(FinalAddError::BothInfinity { sig_id: sig_id.0 }),
            (true, false) => FinalAddBranch::R2Only,
            (false, true) => FinalAddBranch::R1Only,
            (false, false) => {
                if r1.x == r2.x {
                    if r1.y == r2.y {
                        FinalAddBranch::DoubleAdd
                    } else {
                        // The only other equal-x case on the curve is y2 = p − y1,
                        // i.e. R_1 = -R_2. The AIR forbids this branch (output ∞).
                        return Err(FinalAddError::InverseAdd { sig_id: sig_id.0 });
                    }
                } else {
                    FinalAddBranch::DistinctAdd
                }
            }
        };

        // ----- Per-branch denom/numer/lambda derivation -----
        let (lambda_u, dx_u, dy_u, dx_inv_u) = match branch {
            FinalAddBranch::DistinctAdd => {
                let dx = fp_sub(&r2.x, &r1.x, &modulus);
                let dy = fp_sub(&r2.y, &r1.y, &modulus);
                let dx_inv = mod_inverse(&dx, &modulus);
                let lambda = fp_mul(&dy, &dx_inv, &modulus);
                (lambda, dx, dy, dx_inv)
            }
            FinalAddBranch::DoubleAdd => {
                let two_y1 = fp_add(&r1.y, &r1.y, &modulus);
                let two_y1_inv = mod_inverse(&two_y1, &modulus);
                let x1_sq = fp_mul(&r1.x, &r1.x, &modulus);
                let three_x1_sq = fp_mul(&three, &x1_sq, &modulus);
                let slope_numer = fp_sub(&three_x1_sq, &three, &modulus);
                let lambda = fp_mul(&slope_numer, &two_y1_inv, &modulus);
                (lambda, two_y1, slope_numer, two_y1_inv)
            }
            _ => (zero.clone(), zero.clone(), zero.clone(), zero.clone()),
        };

        // ----- Mul rows (always 4) -----
        //
        // MUL_X1_SQUARED must use the *column* x1 value (`r1_values.x`), which is
        // 0 on an infinity row — NOT the raw hint `r1.x`. The AIR binds this mul's
        // operands to the r1.x column, so on an inf row the operands must be 0
        // (the mul is idle: 0·0 = 0). Using the raw `r1.x` made the witnessed mul
        // disagree with the r1.x column and broke the AIR constraint on inf rows.
        let x1_col_u = if r1_inf { zero.clone() } else { r1.x.clone() };
        let x1_sq_u = fp_mul(&x1_col_u, &x1_col_u, &modulus);
        let mut muls = Vec::with_capacity(FINAL_ADD_MUL_COUNT);
        let p1_u = push_mul(&mut muls, MUL_LAMBDA_DX as usize, &lambda_u, &dx_u)?;
        let lamsq_u = push_mul(&mut muls, MUL_LAMBDA_SQUARED as usize, &lambda_u, &lambda_u)?;
        let dx_inv_check = push_mul(&mut muls, MUL_DX_INV as usize, &dx_u, &dx_inv_u)?;
        let x1_sq_check = push_mul(&mut muls, MUL_X1_SQUARED as usize, &x1_col_u, &x1_col_u)?;
        debug_assert!(
            matches!(branch, FinalAddBranch::R1Only | FinalAddBranch::R2Only)
                || dx_inv_check == U256::from_le_u64s(&[1, 0, 0, 0]),
            "denom · denom_inv must be 1 on either finite branch"
        );
        debug_assert!(x1_sq_check == x1_sq_u, "MUL_X1_SQUARED result mismatch");

        let air_row = ProjectiveRcbAirRow {
            source_index: 0,
            sig_id: M31::from_u32_unchecked(0),
            cert_id: M31::from_u32_unchecked(0),
            op: ProjectiveEcOp::Double,
            output_projective: ProjectivePoint::infinity(),
            muls,
        };
        let mul_trace = ProjectiveRcbAirTraceClaim {
            rows: vec![air_row],
        };

        // ----- x3 + the three column-bound reductions per branch -----
        let (x3_u, dx_red, dy_red, x3_red) = match branch {
            FinalAddBranch::DistinctAdd => {
                if p1_u != dy_u {
                    return Err(FinalAddError::SlopeMismatch { sig_id: sig_id.0 });
                }
                let x3 = fp_sub(&fp_sub(&lamsq_u, &r1.x, &modulus), &r2.x, &modulus);
                let dx_red = solve_sub_reduction(&dx_u, &r1.x, &r2.x, &modulus).ok_or(
                    FinalAddError::ReductionFailed { which: "dx", sig_id: sig_id.0 },
                )?;
                let dy_red = solve_sub_reduction(&dy_u, &r1.y, &r2.y, &modulus).ok_or(
                    FinalAddError::ReductionFailed { which: "dy", sig_id: sig_id.0 },
                )?;
                let x3_red = solve_x3_reduction(&x3, &r1.x, &r2.x, &lamsq_u, &modulus).ok_or(
                    FinalAddError::ReductionFailed { which: "x3", sig_id: sig_id.0 },
                )?;
                (x3, dx_red, dy_red, x3_red)
            }
            FinalAddBranch::DoubleAdd => {
                if p1_u != dy_u {
                    return Err(FinalAddError::SlopeMismatch { sig_id: sig_id.0 });
                }
                // x3 = lamsq − 2·x1 (mod p).
                let two_x1 = fp_add(&r1.x, &r1.x, &modulus);
                let x3 = fp_sub(&lamsq_u, &two_x1, &modulus);
                // dx = 2·y1  ⟺  dx + 0 ≡ 2·y1 (mod p) i.e. solve via the
                // "sub" form `dx + lo ≡ hi`, with `lo = 0` and `hi = 2·y1`.
                // We pose this as `dx + r1.y ≡ 2·y1 − r1.y + r1.y = 2·y1`,
                // but the cleanest is a new dedicated reduction. We use a
                // tiny helper: `dx + r1.y ≡ 2·y1` is the same as `dx ≡ 2·y1 − r1.y`.
                // Equivalently `dx = (2·y1 − r1.y) mod p = r1.y mod p`. That
                // would fold to `dx == r1.y`, which is wrong because dx is
                // `2·y1 mod p`. We just use a dedicated double-add reduction
                // `dx + q·p ≡ 2·y1 (mod 2^256)`.
                let dx_red = solve_two_y1_reduction(&dx_u, &r1.y, &modulus).ok_or(
                    FinalAddError::ReductionFailed { which: "dx_double", sig_id: sig_id.0 },
                )?;
                // dy = 3·x1_sq − 3 (mod p). `dy + 3 + q·p ≡ 3·x1_sq (mod 2^256)`.
                let dy_red = solve_slope_numer_reduction(&dy_u, &x1_sq_u, &modulus).ok_or(
                    FinalAddError::ReductionFailed { which: "dy_double", sig_id: sig_id.0 },
                )?;
                // x3 reduction uses x2 = x1 (enforced in-AIR by double_add gate).
                let x3_red = solve_x3_reduction(&x3, &r1.x, &r1.x, &lamsq_u, &modulus).ok_or(
                    FinalAddError::ReductionFailed { which: "x3_double", sig_id: sig_id.0 },
                )?;
                (x3, dx_red, dy_red, x3_red)
            }
            FinalAddBranch::R2Only => {
                (r2.x.clone(), zero_reduction(), zero_reduction(), zero_reduction())
            }
            FinalAddBranch::R1Only => {
                (r1.x.clone(), zero_reduction(), zero_reduction(), zero_reduction())
            }
        };

        let claim = Self {
            mul_trace,
            sig_id,
            branch,
            r1: r1_values,
            r2: r2_values,
            dx: P256M31BigInt::from_u256(&dx_u),
            dx_q: dx_red.0,
            dx_carries: dx_red.1,
            dx_inv: P256M31BigInt::from_u256(&dx_inv_u),
            dy: P256M31BigInt::from_u256(&dy_u),
            dy_q: dy_red.0,
            dy_carries: dy_red.1,
            lambda: P256M31BigInt::from_u256(&lambda_u),
            lamsq: P256M31BigInt::from_u256(&lamsq_u),
            x3: P256M31BigInt::from_u256(&x3_u),
            x3_q: x3_red.0,
            x3_carries: x3_red.1,
            x1_sq: P256M31BigInt::from_u256(&x1_sq_u),
        };
        claim.verify()?;
        Ok(claim)
    }

    /// Re-check the native witness end to end.
    pub fn verify(&self) -> Result<(), FinalAddError> {
        if self.mul_trace.rows.len() != 1
            || self.mul_trace.rows[0].muls.len() != FINAL_ADD_MUL_COUNT
        {
            return Err(FinalAddError::MulTraceShape);
        }
        for row in &self.mul_trace.rows {
            row.verify().map_err(FinalAddError::MulTrace)?;
        }
        let muls = &self.mul_trace.rows[0].muls;
        // Mul operands/results match the witnessed copies.
        require_eq("lambda(dx).lhs", &muls[MUL_LAMBDA_DX as usize].trace.lhs, &self.lambda)?;
        require_eq("lambda(dx).rhs", &muls[MUL_LAMBDA_DX as usize].trace.rhs, &self.dx)?;
        require_eq("lambda^2.lhs", &muls[MUL_LAMBDA_SQUARED as usize].trace.lhs, &self.lambda)?;
        require_eq("lambda^2.rhs", &muls[MUL_LAMBDA_SQUARED as usize].trace.rhs, &self.lambda)?;
        require_eq("lambda^2.result", &muls[MUL_LAMBDA_SQUARED as usize].trace.result, &self.lamsq)?;
        require_eq("dx_inv.lhs", &muls[MUL_DX_INV as usize].trace.lhs, &self.dx)?;
        require_eq("dx_inv.rhs", &muls[MUL_DX_INV as usize].trace.rhs, &self.dx_inv)?;
        require_eq("x1_sq.lhs", &muls[MUL_X1_SQUARED as usize].trace.lhs, &self.r1.x)?;
        require_eq("x1_sq.rhs", &muls[MUL_X1_SQUARED as usize].trace.rhs, &self.r1.x)?;
        require_eq("x1_sq.result", &muls[MUL_X1_SQUARED as usize].trace.result, &self.x1_sq)?;

        let r1_inf = self.r1.inf.0 == 1;
        let r2_inf = self.r2.inf.0 == 1;
        if r1_inf && r2_inf {
            return Err(FinalAddError::BothInfinity { sig_id: self.sig_id.0 });
        }

        let modulus = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS));
        let three = P256M31BigInt::from_u256(&U256::from_le_u64s(&[3, 0, 0, 0]));

        match self.branch {
            FinalAddBranch::DistinctAdd => {
                require_eq(
                    "dx*dx_inv==1",
                    &muls[MUL_DX_INV as usize].trace.result,
                    &P256M31BigInt::from_u256(&U256::from_le_u64s(&[1, 0, 0, 0])),
                )?;
                require_eq("p1==dy", &muls[MUL_LAMBDA_DX as usize].trace.result, &self.dy)?;
                check_sub_reduction("dx", &self.dx, &self.r1.x, &self.r2.x, &modulus, self.dx_q, &self.dx_carries, self.sig_id.0)?;
                check_sub_reduction("dy", &self.dy, &self.r1.y, &self.r2.y, &modulus, self.dy_q, &self.dy_carries, self.sig_id.0)?;
                check_x3_reduction(&self.x3, &self.r1.x, &self.r2.x, &self.lamsq, &modulus, self.x3_q, &self.x3_carries, self.sig_id.0)?;
            }
            FinalAddBranch::DoubleAdd => {
                require_eq(
                    "denom*denom_inv==1",
                    &muls[MUL_DX_INV as usize].trace.result,
                    &P256M31BigInt::from_u256(&U256::from_le_u64s(&[1, 0, 0, 0])),
                )?;
                require_eq("p1==numer", &muls[MUL_LAMBDA_DX as usize].trace.result, &self.dy)?;
                require_eq("x1==x2 (double)", &self.r1.x, &self.r2.x)?;
                require_eq("y1==y2 (double)", &self.r1.y, &self.r2.y)?;
                check_two_y1_reduction(&self.dx, &self.r1.y, &modulus, self.dx_q, &self.dx_carries, self.sig_id.0)?;
                check_slope_numer_reduction(&self.dy, &self.x1_sq, &three, &modulus, self.dy_q, &self.dy_carries, self.sig_id.0)?;
                // x2 = x1 here; reuse the x3 + x1 + x2 ≡ lamsq reduction.
                check_x3_reduction(&self.x3, &self.r1.x, &self.r1.x, &self.lamsq, &modulus, self.x3_q, &self.x3_carries, self.sig_id.0)?;
            }
            FinalAddBranch::R1Only => {
                // r2 = ∞, r1 finite ⇒ output S = r1, so x3 ≡ r1.x.
                require_eq("x3==x1", &self.x3, &self.r1.x)?;
            }
            FinalAddBranch::R2Only => {
                // r1 = ∞, r2 finite ⇒ output S = r2, so x3 ≡ r2.x.
                require_eq("x3==x2", &self.x3, &self.r2.x)?;
            }
        }
        Ok(())
    }

    pub fn output_x(&self) -> P256M31BigInt {
        self.x3.clone()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FinalAddError {
    MulTraceShape,
    MulTrace(ProjectiveRcbAirError),
    WitnessMismatch { field: &'static str },
    /// `R_1 = -R_2`: native sum is the point at infinity, an invalid ECDSA
    /// result. The AIR likewise rejects this branch.
    InverseAdd { sig_id: u32 },
    SlopeMismatch { sig_id: u32 },
    ReductionFailed { which: &'static str, sig_id: u32 },
    BothInfinity { sig_id: u32 },
    QuotientOutOfRange { which: &'static str, q: i64 },
    CarryOutOfRange { which: &'static str, limb: usize, carry: i64 },
    ReductionMismatch { which: &'static str, limb: usize, value: i64 },
    FinalCarryNonZero { which: &'static str, carry: i64 },
}

// ---------------------------------------------------------------------------
// Native helpers
// ---------------------------------------------------------------------------

fn point_values(point: &AffinePoint, inf: bool) -> PreparedAffinePoint {
    if inf {
        PreparedAffinePoint::infinity()
    } else {
        PreparedAffinePoint::from_affine(point.clone())
    }
}

fn push_mul(
    muls: &mut Vec<ProjectiveRcbMulRow>,
    mul_index: usize,
    lhs: &U256,
    rhs: &U256,
) -> Result<U256, FinalAddError> {
    let row = ProjectiveRcbMulRow::new(0, mul_index, ProjectiveRcbMulStep::DoubleX1Squared, lhs, rhs)
        .map_err(FinalAddError::MulTrace)?;
    let result = row.trace.result.to_u256();
    muls.push(row);
    Ok(result)
}

fn require_eq(
    field: &'static str,
    actual: &P256M31BigInt,
    expected: &P256M31BigInt,
) -> Result<(), FinalAddError> {
    if actual == expected {
        Ok(())
    } else {
        Err(FinalAddError::WitnessMismatch { field })
    }
}

fn fp_sub(a: &U256, b: &U256, m: &U256) -> U256 {
    crate::field_ops::sub_mod_witness(a, b, m).result.to_u256()
}
fn fp_mul(a: &U256, b: &U256, m: &U256) -> U256 {
    crate::field_ops::mul_mod_witness(a, b, m).result.to_u256()
}
fn fp_add(a: &U256, b: &U256, m: &U256) -> U256 {
    crate::field_ops::add_mod_witness(a, b, m).result.to_u256()
}
fn mod_inverse(a: &U256, m: &U256) -> U256 {
    crate::curve::mod_inverse(a, m)
}

fn zero_reduction() -> (i64, [i64; N_LIMBS]) {
    (0, [0i64; N_LIMBS])
}

/// Solve `value + lo ≡ hi (mod p)`: `value + lo - hi - q·p = 0` over 13-bit
/// limbs with `q ∈ {0, 1}` and final carry 0. (`value = (hi - lo) mod p`.)
fn solve_sub_reduction(
    value: &U256,
    lo: &U256,
    hi: &U256,
    modulus: &U256,
) -> Option<(i64, [i64; N_LIMBS])> {
    let v = P256M31BigInt::from_u256(value);
    let l = P256M31BigInt::from_u256(lo);
    let h = P256M31BigInt::from_u256(hi);
    let m = P256M31BigInt::from_u256(modulus);
    for q in [0i64, 1] {
        if let Some(carries) = try_sub_carries(&v, &l, &h, &m, q) {
            return Some((q, carries));
        }
    }
    None
}

fn try_sub_carries(
    v: &P256M31BigInt,
    l: &P256M31BigInt,
    h: &P256M31BigInt,
    m: &P256M31BigInt,
    q: i64,
) -> Option<[i64; N_LIMBS]> {
    let base = 1i64 << LIMB_BITS;
    let mut carries = [0i64; N_LIMBS];
    let mut prev = 0i64;
    for (i, carry) in carries.iter_mut().enumerate() {
        let combined = i64::from(v.limbs()[i].0) + i64::from(l.limbs()[i].0)
            - i64::from(h.limbs()[i].0)
            - q * i64::from(m.limbs()[i].0);
        let total = combined + prev;
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

/// Solve `x3 + x1 + x2 ≡ lamsq (mod p)`: `x3 + x1 + x2 - lamsq - q·p = 0` with
/// `q ∈ {0, 1, 2}` and final carry 0.
fn solve_x3_reduction(
    x3: &U256,
    x1: &U256,
    x2: &U256,
    lamsq: &U256,
    modulus: &U256,
) -> Option<(i64, [i64; N_LIMBS])> {
    let x3 = P256M31BigInt::from_u256(x3);
    let x1 = P256M31BigInt::from_u256(x1);
    let x2 = P256M31BigInt::from_u256(x2);
    let lamsq = P256M31BigInt::from_u256(lamsq);
    let m = P256M31BigInt::from_u256(modulus);
    for q in [0i64, 1, 2] {
        if let Some(carries) = try_x3_carries(&x3, &x1, &x2, &lamsq, &m, q) {
            return Some((q, carries));
        }
    }
    None
}

fn try_x3_carries(
    x3: &P256M31BigInt,
    x1: &P256M31BigInt,
    x2: &P256M31BigInt,
    lamsq: &P256M31BigInt,
    m: &P256M31BigInt,
    q: i64,
) -> Option<[i64; N_LIMBS]> {
    let base = 1i64 << LIMB_BITS;
    let mut carries = [0i64; N_LIMBS];
    let mut prev = 0i64;
    for (i, carry) in carries.iter_mut().enumerate() {
        let combined = i64::from(x3.limbs()[i].0) + i64::from(x1.limbs()[i].0)
            + i64::from(x2.limbs()[i].0)
            - i64::from(lamsq.limbs()[i].0)
            - q * i64::from(m.limbs()[i].0);
        let total = combined + prev;
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

/// Doubling-branch: `dx + q·p ≡ 2·y1 (mod 2^256)` with `q ∈ {0, 1}` and final
/// carry 0. (`dx = (2·y1) mod p`, with `2·y1 < 2p` so `q ∈ {0, 1}`.)
fn solve_two_y1_reduction(
    dx: &U256,
    y1: &U256,
    modulus: &U256,
) -> Option<(i64, [i64; N_LIMBS])> {
    let dx = P256M31BigInt::from_u256(dx);
    let y1 = P256M31BigInt::from_u256(y1);
    let m = P256M31BigInt::from_u256(modulus);
    for q in [0i64, 1] {
        if let Some(carries) = try_two_y1_carries(&dx, &y1, &m, q) {
            return Some((q, carries));
        }
    }
    None
}

fn try_two_y1_carries(
    dx: &P256M31BigInt,
    y1: &P256M31BigInt,
    m: &P256M31BigInt,
    q: i64,
) -> Option<[i64; N_LIMBS]> {
    let base = 1i64 << LIMB_BITS;
    let mut carries = [0i64; N_LIMBS];
    let mut prev = 0i64;
    for (i, carry) in carries.iter_mut().enumerate() {
        // dx[i] + q·m[i] - 2·y1[i] + prev = base·c[i]
        let combined = i64::from(dx.limbs()[i].0) + q * i64::from(m.limbs()[i].0)
            - 2 * i64::from(y1.limbs()[i].0);
        let total = combined + prev;
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

/// Doubling-branch slope numerator: `dy + 3 + q·p ≡ 3·x1_sq (mod 2^256)` with
/// `q ∈ {0, 1, 2}` and final carry 0. (`dy = (3·x1_sq − 3) mod p`; since
/// `3·x1_sq < 3p` and `dy < p`, the quotient `q ∈ {0, 1, 2}`.)
fn solve_slope_numer_reduction(
    dy: &U256,
    x1_sq: &U256,
    modulus: &U256,
) -> Option<(i64, [i64; N_LIMBS])> {
    let dy = P256M31BigInt::from_u256(dy);
    let x1_sq = P256M31BigInt::from_u256(x1_sq);
    let m = P256M31BigInt::from_u256(modulus);
    for q in [0i64, 1, 2] {
        if let Some(carries) = try_slope_numer_carries(&dy, &x1_sq, &m, q) {
            return Some((q, carries));
        }
    }
    None
}

fn try_slope_numer_carries(
    dy: &P256M31BigInt,
    x1_sq: &P256M31BigInt,
    m: &P256M31BigInt,
    q: i64,
) -> Option<[i64; N_LIMBS]> {
    let base = 1i64 << LIMB_BITS;
    let mut carries = [0i64; N_LIMBS];
    let mut prev = 0i64;
    for (i, carry) in carries.iter_mut().enumerate() {
        // dy[i] + 3·(i==0) + q·m[i] - 3·x1_sq[i] + prev = base·c[i]
        let three_at_zero = if i == 0 { 3i64 } else { 0i64 };
        let combined = i64::from(dy.limbs()[i].0) + three_at_zero
            + q * i64::from(m.limbs()[i].0)
            - 3 * i64::from(x1_sq.limbs()[i].0);
        let total = combined + prev;
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

#[allow(clippy::too_many_arguments)]
fn check_sub_reduction(
    which: &'static str,
    value: &P256M31BigInt,
    lo: &P256M31BigInt,
    hi: &P256M31BigInt,
    modulus: &P256M31BigInt,
    q: i64,
    carries: &[i64; N_LIMBS],
    sig_id: u32,
) -> Result<(), FinalAddError> {
    let _ = sig_id;
    if !(0..=1).contains(&q) {
        return Err(FinalAddError::QuotientOutOfRange { which, q });
    }
    let base = 1i64 << LIMB_BITS;
    let mut prev = 0i64;
    for i in 0..N_LIMBS {
        let combined = i64::from(value.limbs()[i].0) + i64::from(lo.limbs()[i].0)
            - i64::from(hi.limbs()[i].0)
            - q * i64::from(modulus.limbs()[i].0);
        let total = combined + prev - base * carries[i];
        if total != 0 {
            return Err(FinalAddError::ReductionMismatch { which, limb: i, value: total });
        }
        if carries[i].abs() > projective_rcb_signed_carry_bound() {
            return Err(FinalAddError::CarryOutOfRange { which, limb: i, carry: carries[i] });
        }
        prev = carries[i];
    }
    if carries[N_LIMBS - 1] != 0 {
        return Err(FinalAddError::FinalCarryNonZero { which, carry: carries[N_LIMBS - 1] });
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn check_x3_reduction(
    x3: &P256M31BigInt,
    x1: &P256M31BigInt,
    x2: &P256M31BigInt,
    lamsq: &P256M31BigInt,
    modulus: &P256M31BigInt,
    q: i64,
    carries: &[i64; N_LIMBS],
    sig_id: u32,
) -> Result<(), FinalAddError> {
    let _ = sig_id;
    if !(0..=FINAL_ADD_QUOTIENT_BOUND).contains(&q) {
        return Err(FinalAddError::QuotientOutOfRange { which: "x3", q });
    }
    let base = 1i64 << LIMB_BITS;
    let mut prev = 0i64;
    for i in 0..N_LIMBS {
        let combined = i64::from(x3.limbs()[i].0) + i64::from(x1.limbs()[i].0)
            + i64::from(x2.limbs()[i].0)
            - i64::from(lamsq.limbs()[i].0)
            - q * i64::from(modulus.limbs()[i].0);
        let total = combined + prev - base * carries[i];
        if total != 0 {
            return Err(FinalAddError::ReductionMismatch { which: "x3", limb: i, value: total });
        }
        if carries[i].abs() > projective_rcb_signed_carry_bound() {
            return Err(FinalAddError::CarryOutOfRange { which: "x3", limb: i, carry: carries[i] });
        }
        prev = carries[i];
    }
    if carries[N_LIMBS - 1] != 0 {
        return Err(FinalAddError::FinalCarryNonZero { which: "x3", carry: carries[N_LIMBS - 1] });
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn check_two_y1_reduction(
    dx: &P256M31BigInt,
    y1: &P256M31BigInt,
    modulus: &P256M31BigInt,
    q: i64,
    carries: &[i64; N_LIMBS],
    sig_id: u32,
) -> Result<(), FinalAddError> {
    let _ = sig_id;
    if !(0..=1).contains(&q) {
        return Err(FinalAddError::QuotientOutOfRange { which: "dx_double", q });
    }
    let base = 1i64 << LIMB_BITS;
    let mut prev = 0i64;
    for i in 0..N_LIMBS {
        let combined = i64::from(dx.limbs()[i].0) + q * i64::from(modulus.limbs()[i].0)
            - 2 * i64::from(y1.limbs()[i].0);
        let total = combined + prev - base * carries[i];
        if total != 0 {
            return Err(FinalAddError::ReductionMismatch { which: "dx_double", limb: i, value: total });
        }
        if carries[i].abs() > projective_rcb_signed_carry_bound() {
            return Err(FinalAddError::CarryOutOfRange { which: "dx_double", limb: i, carry: carries[i] });
        }
        prev = carries[i];
    }
    if carries[N_LIMBS - 1] != 0 {
        return Err(FinalAddError::FinalCarryNonZero { which: "dx_double", carry: carries[N_LIMBS - 1] });
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn check_slope_numer_reduction(
    dy: &P256M31BigInt,
    x1_sq: &P256M31BigInt,
    three: &P256M31BigInt,
    modulus: &P256M31BigInt,
    q: i64,
    carries: &[i64; N_LIMBS],
    sig_id: u32,
) -> Result<(), FinalAddError> {
    let _ = sig_id;
    if !(0..=FINAL_ADD_QUOTIENT_BOUND).contains(&q) {
        return Err(FinalAddError::QuotientOutOfRange { which: "dy_double", q });
    }
    let base = 1i64 << LIMB_BITS;
    let mut prev = 0i64;
    for i in 0..N_LIMBS {
        let combined = i64::from(dy.limbs()[i].0) + i64::from(three.limbs()[i].0)
            + q * i64::from(modulus.limbs()[i].0)
            - 3 * i64::from(x1_sq.limbs()[i].0);
        let total = combined + prev - base * carries[i];
        if total != 0 {
            return Err(FinalAddError::ReductionMismatch { which: "dy_double", limb: i, value: total });
        }
        if carries[i].abs() > projective_rcb_signed_carry_bound() {
            return Err(FinalAddError::CarryOutOfRange { which: "dy_double", limb: i, carry: carries[i] });
        }
        prev = carries[i];
    }
    if carries[N_LIMBS - 1] != 0 {
        return Err(FinalAddError::FinalCarryNonZero { which: "dy_double", carry: carries[N_LIMBS - 1] });
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Trace generation
// ---------------------------------------------------------------------------

/// Preprocessed schedule + range/signed-carry value columns for this sub-graph,
/// mirroring `public_key_curve_air::gen_slice_preprocessed_trace` but under the
/// FINAL_ADD namespace.
pub fn final_add_preprocessed_columns(
    claim: &FinalAddClaim,
) -> Result<Vec<(PreProcessedColumnId, M31ColumnEval)>, FinalAddError> {
    let projective_ids = claim
        .mul_trace
        .preprocessed_column_ids_with_namespace(PROJECTIVE_RCB_SCHEDULE_NAMESPACE_FINAL_ADD);
    let mut columns: Vec<(PreProcessedColumnId, M31ColumnEval)> = claim
        .mul_trace
        .gen_preprocessed_trace_with_namespace(
            &projective_ids,
            PROJECTIVE_RCB_SCHEDULE_NAMESPACE_FINAL_ADD,
        )
        .map_err(FinalAddError::MulTrace)?
        .into_iter()
        .zip(projective_ids)
        .map(|(eval, id)| (id, eval))
        .collect();

    let range13 = RangeCheckClaim::new(RANGE13_BITS);
    columns.push((
        range_check_value_column_id(RANGE13_BITS),
        range13.gen_preprocessed_column(),
    ));
    let signed_carry = final_add_signed_carry_claim();
    columns.push((
        signed_carry_value_column_id(PROJECTIVE_RCB_SIGNED_CARRY_EQUATION),
        signed_carry.gen_value_column(),
    ));
    columns.push((
        signed_carry_active_column_id(PROJECTIVE_RCB_SIGNED_CARRY_EQUATION),
        signed_carry.gen_active_column(),
    ));
    Ok(columns)
}

/// Preprocessed column ids this sub-graph reads (schedule + range/signed-carry).
pub fn final_add_preprocessed_column_ids(claim: &FinalAddClaim) -> Vec<PreProcessedColumnId> {
    let mut ids = claim
        .mul_trace
        .preprocessed_column_ids_with_namespace(PROJECTIVE_RCB_SCHEDULE_NAMESPACE_FINAL_ADD);
    ids.push(range_check_value_column_id(RANGE13_BITS));
    ids.push(signed_carry_value_column_id(PROJECTIVE_RCB_SIGNED_CARRY_EQUATION));
    ids.push(signed_carry_active_column_id(PROJECTIVE_RCB_SIGNED_CARRY_EQUATION));
    ids
}

/// The witnessed `dx · dx_inv` result column: `[both_finite, 0, …, 0]`.
pub(crate) fn dx_inv_result_value(claim: &FinalAddClaim) -> P256M31BigInt {
    let both_finite = claim.r1.inf.0 == 0 && claim.r2.inf.0 == 0;
    if both_finite {
        P256M31BigInt::from_u256(&U256::from_le_u64s(&[1, 0, 0, 0]))
    } else {
        P256M31BigInt::zero()
    }
}

pub(crate) fn final_add_signed_carry_claim() -> SignedCarryRangeClaim {
    SignedCarryRangeClaim::new(
        projective_rcb_signed_carry_log_size(),
        projective_rcb_signed_carry_bound(),
        PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
    )
}

/// All range13 uses: mul-family uses + the check-row witnessed limbs.
pub(crate) fn final_add_range13_uses(claim: &FinalAddClaim) -> Vec<M31> {
    let mut uses = claim.mul_trace.range13_lookup_values();
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
        // Task 6: the doubling-branch slope-numerator intermediate
        // `x1_sq = x1 · x1 mod p` is a witnessed big-int field; every
        // limb needs the standard 13-bit range lookup to balance the
        // FinalAddInternal relation.
        &claim.x1_sq,
    ] {
        uses.extend(value.limbs().iter().copied());
    }
    uses
}

/// All signed-carry uses: mul-family uses + the check-row carries.
pub(crate) fn final_add_signed_carry_uses(claim: &FinalAddClaim) -> Result<Vec<i64>, FinalAddError> {
    let mut uses = claim
        .mul_trace
        .signed_carry_lookup_values()
        .map_err(FinalAddError::MulTrace)?;
    uses.extend(claim.dx_carries.iter().copied());
    uses.extend(claim.dy_carries.iter().copied());
    uses.extend(claim.x3_carries.iter().copied());
    Ok(uses)
}

pub fn gen_final_add_base_trace(
    claim: &FinalAddClaim,
    log_sizes: FinalAddLogSizes,
) -> Result<Vec<M31ColumnEval>, FinalAddError> {
    let mut columns = Vec::new();
    columns.extend(
        gen_projective_rcb_mul_base_trace(&claim.mul_trace, log_sizes.mul)
            .map_err(FinalAddError::MulTrace)?,
    );
    columns.extend(
        gen_projective_rcb_raw_product_chunk_base_trace(&claim.mul_trace, log_sizes.raw_product_chunk)
            .map_err(FinalAddError::MulTrace)?,
    );
    columns.extend(
        gen_projective_rcb_folded_contribution_base_trace(
            &claim.mul_trace,
            log_sizes.folded_contribution,
        )
        .map_err(FinalAddError::MulTrace)?,
    );
    columns.extend(
        gen_projective_rcb_folded_digit_base_trace(&claim.mul_trace, log_sizes.folded_digit)
            .map_err(FinalAddError::MulTrace)?,
    );
    columns.extend(gen_check_base_trace(claim, log_sizes.check));

    // Shared range providers' multiplicity columns (over ALL uses in the sub-graph).
    let range13 = RangeCheckClaim::new(RANGE13_BITS);
    columns.push(range13.gen_multiplicity_trace(final_add_range13_uses(claim)));
    let signed_carry = final_add_signed_carry_claim();
    columns.push(signed_carry.gen_multiplicity_trace(final_add_signed_carry_uses(claim)?));
    Ok(columns)
}

fn gen_check_base_trace(claim: &FinalAddClaim, log_size: u32) -> Vec<M31ColumnEval> {
    let row_count = 1usize << log_size;
    let mut cols = vec![vec![M31::from_u32_unchecked(0); row_count]; CHECK_TRACE_COLUMNS];
    let row = 0usize; // single active row at coset index 0
    let mut offset = 0usize;
    cols[offset][row] = M31::from_u32_unchecked(1); // active
    offset += 1;
    cols[offset][row] = claim.sig_id;
    offset += 1;
    write_point(&mut cols, &mut offset, &claim.r1, row);
    write_point(&mut cols, &mut offset, &claim.r2, row);
    // Task 6 branch selectors. Valid claims never carry `InverseAdd` (the
    // builder rejects `R_1 = -R_2`), so `inverse_add` is always 0 in the
    // written trace; the AIR independently enforces
    // `active · inverse_add = 0`.
    cols[offset][row] = M31::from_u32_unchecked(if claim.branch == FinalAddBranch::DoubleAdd {
        1
    } else {
        0
    });
    offset += 1;
    cols[offset][row] = M31::from_u32_unchecked(0); // inverse_add: always 0 for valid claims
    offset += 1;
    write_limbs(&mut cols, &mut offset, &claim.dx, row);
    write_limbs(&mut cols, &mut offset, &claim.dy, row);
    write_limbs(&mut cols, &mut offset, &claim.lambda, row);
    write_limbs(&mut cols, &mut offset, &claim.lamsq, row);
    write_limbs(&mut cols, &mut offset, &claim.x3, row);
    write_limbs(&mut cols, &mut offset, &claim.dx_inv, row);
    let dx_inv_result = dx_inv_result_value(claim);
    write_limbs(&mut cols, &mut offset, &dx_inv_result, row);
    // Task 6 doubling: `x1_sq = r1.x² mod p` is read at this position by the
    // AIR (see `Columns::read`) and consumed via `MUL_X1_SQUARED`'s Result
    // role. Without writing it the column stays zero, breaking the mul
    // provider/consumer balance.
    write_limbs(&mut cols, &mut offset, &claim.x1_sq, row);
    cols[offset][row] = M31::from_u32_unchecked(claim.dx_q as u32);
    offset += 1;
    write_signed_carries(&mut cols, &mut offset, &claim.dx_carries, row);
    cols[offset][row] = M31::from_u32_unchecked(claim.dy_q as u32);
    offset += 1;
    write_signed_carries(&mut cols, &mut offset, &claim.dy_carries, row);
    cols[offset][row] = M31::from_u32_unchecked(claim.x3_q as u32);
    offset += 1;
    write_signed_carries(&mut cols, &mut offset, &claim.x3_carries, row);
    debug_assert_eq!(offset, CHECK_TRACE_COLUMNS);

    cols.into_iter()
        .map(|values| m31_column_eval(log_size, values))
        .collect()
}

fn write_point(
    cols: &mut [Vec<M31>],
    offset: &mut usize,
    point: &PreparedAffinePoint,
    row: usize,
) {
    for limb in point.x.limbs() {
        cols[*offset][row] = *limb;
        *offset += 1;
    }
    for limb in point.y.limbs() {
        cols[*offset][row] = *limb;
        *offset += 1;
    }
    cols[*offset][row] = point.inf;
    *offset += 1;
}

fn write_limbs(cols: &mut [Vec<M31>], offset: &mut usize, value: &P256M31BigInt, row: usize) {
    for limb in value.limbs() {
        cols[*offset][row] = *limb;
        *offset += 1;
    }
}

fn write_signed_carries(
    cols: &mut [Vec<M31>],
    offset: &mut usize,
    carries: &[i64; N_LIMBS],
    row: usize,
) {
    for carry in carries {
        cols[*offset][row] = encode_signed_carry(*carry);
        *offset += 1;
    }
}
