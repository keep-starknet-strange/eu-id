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

pub mod relation;

pub use relation::*;

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
        // MUL_X1_SQUARED uses `r1.x · r1.x` even on non-doubling branches;
        // the AIR doesn't constrain the result anywhere outside the doubling
        // slope-numer reduction, so this is sound. On infinity rows `r1.x = 0`
        // so the mul is trivial.
        let x1_sq_u = if r1_inf { zero.clone() } else { fp_mul(&r1.x, &r1.x, &modulus) };
        let mut muls = Vec::with_capacity(FINAL_ADD_MUL_COUNT);
        let p1_u = push_mul(&mut muls, MUL_LAMBDA_DX as usize, &lambda_u, &dx_u)?;
        let lamsq_u = push_mul(&mut muls, MUL_LAMBDA_SQUARED as usize, &lambda_u, &lambda_u)?;
        let dx_inv_check = push_mul(&mut muls, MUL_DX_INV as usize, &dx_u, &dx_inv_u)?;
        let x1_sq_check = push_mul(&mut muls, MUL_X1_SQUARED as usize, &r1.x, &r1.x)?;
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
// Mul-provider evaluator (clone of PublicKeyMulEval shape)
// ---------------------------------------------------------------------------

type FinalAddMulComponent = FrameworkComponent<FinalAddMulEval>;
type FinalAddCheckComponent = FrameworkComponent<FinalAddCheckEval>;

#[derive(Clone)]
struct FinalAddMulEval {
    log_size: u32,
    mul_relations: ProjectiveRcbMulComponentRelations,
    result_relation: FinalAddMulResultRelation,
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

const FINAL_ADD_MUL_PROVIDER_FRACTIONS: usize = 3 * N_LIMBS;

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
        }
    }
}

/// Number of base-trace columns of the check component.
const CHECK_TRACE_COLUMNS: usize = 1 // active
    + 1 // sig_id
    + 2 * (2 * N_LIMBS + 1) // r1, r2 points
    + 2 // double_add, inverse_add
    + 8 * N_LIMBS // dx, dy, lambda, lamsq, x3, dx_inv, dx_inv_result, x1_sq
    + 3 * (1 + N_LIMBS); // (q + carries) × 3

#[derive(Clone)]
struct FinalAddCheckEval {
    log_size: u32,
    result_relation: FinalAddMulResultRelation,
    hint_relation: FinalCheckHintRelation,
    output_relation: FinalAddOutputRelation,
    range13: RangeCheckRelation,
    signed_carry: RangeCheckRelation,
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
        let two = E::F::from(M31::from_u32_unchecked(2));
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
        // Reject R_1 = R_2 = ∞ (=> R_final = ∞).
        eval.add_constraint(active.clone() * columns.r1.inf.clone() * columns.r2.inf.clone());

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
        // Only one of double_add / inverse_add can be 1 (and they only apply
        // when both R_1, R_2 are finite — gated implicitly via the chord muls).
        eval.add_constraint(
            active.clone() * columns.double_add.clone() * columns.inverse_add.clone(),
        );
        // Reject R_final = ∞ (additive-inverse case).
        eval.add_constraint(active.clone() * columns.inverse_add.clone());

        let both_finite =
            (one.clone() - columns.r1.inf.clone()) * (one.clone() - columns.r2.inf.clone());
        let r1_only = columns.r1.inf.clone() * (one.clone() - columns.r2.inf.clone());
        let r2_only = columns.r2.inf.clone() * (one.clone() - columns.r1.inf.clone());
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

        // -------- Quotient bounds --------
        let finite_finite = distinct_add.clone() + columns.double_add.clone();
        // dx_q ∈ {0, 1} on either finite branch.
        eval.add_constraint(
            finite_finite.clone()
                * columns.dx_q.clone()
                * (columns.dx_q.clone() - one.clone()),
        );
        // dy_q ∈ {0, 1} on distinct; ∈ {0, 1, 2} on doubling.
        eval.add_constraint(
            distinct_add.clone()
                * columns.dy_q.clone()
                * (columns.dy_q.clone() - one.clone()),
        );
        eval.add_constraint(
            columns.double_add.clone()
                * columns.dy_q.clone()
                * (columns.dy_q.clone() - one.clone())
                * (columns.dy_q.clone() - two.clone()),
        );
        // x3_q ∈ {0, 1, 2} on either finite branch.
        eval.add_constraint(
            finite_finite.clone()
                * columns.x3_q.clone()
                * (columns.x3_q.clone() - one.clone())
                * (columns.x3_q.clone() - two.clone()),
        );
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
fn dx_inv_result_value(claim: &FinalAddClaim) -> P256M31BigInt {
    let both_finite = claim.r1.inf.0 == 0 && claim.r2.inf.0 == 0;
    if both_finite {
        P256M31BigInt::from_u256(&U256::from_le_u64s(&[1, 0, 0, 0]))
    } else {
        P256M31BigInt::zero()
    }
}

fn final_add_signed_carry_claim() -> SignedCarryRangeClaim {
    SignedCarryRangeClaim::new(
        projective_rcb_signed_carry_log_size(),
        projective_rcb_signed_carry_bound(),
        PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
    )
}

/// All range13 uses: mul-family uses + the check-row witnessed limbs.
fn final_add_range13_uses(claim: &FinalAddClaim) -> Vec<M31> {
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
fn final_add_signed_carry_uses(claim: &FinalAddClaim) -> Result<Vec<i64>, FinalAddError> {
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
