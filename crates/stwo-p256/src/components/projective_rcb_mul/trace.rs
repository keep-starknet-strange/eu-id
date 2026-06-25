//! Native witness, claim, and base/preprocessed-trace generation for the projective RCB
//! multiplication AIR family.
//!
//! Split out of `mod.rs` (pure relocation, no behavioral change).

use stwo::core::fields::m31::M31;
use stwo_p256_utils::constants::N_LIMBS;

use super::*;
use crate::constants::{P256_B, P256_MODULUS};
use crate::field_ops::{add_mod_witness, sub_mod_witness};
use crate::fp_solinas::{FpSolinasError, FpSolinasMulTrace, FP_SOLINAS_RAW_LIMBS};
use crate::fp_solinas_air::FpSolinasReductionTraceError;
use crate::limbs::P256M31BigInt;
use crate::prepared_table::PreparedAffinePoint;
use crate::projective::{
    ProjectiveEcError, ProjectiveEcOp, ProjectiveEcRow, ProjectiveEcTraceClaim, ProjectivePoint,
};
use crate::range_checks::SignedCarryRangeClaim;
use crate::scalar::scalar_mod_mul::columns::M31ColumnEval;
use crate::types::U256;

/// Schedule-column id namespace for the canonical EC projective-RCB mul trace.
/// Empty so existing preprocessed-column ids are unchanged.
pub(crate) fn projective_rcb_signed_carry_claim() -> SignedCarryRangeClaim {
    SignedCarryRangeClaim::new(
        projective_rcb_signed_carry_log_size(),
        PROJECTIVE_RCB_SIGNED_CARRY_BOUND,
        PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
    )
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbAirTraceClaim {
    pub rows: Vec<ProjectiveRcbAirRow>,
}

impl ProjectiveRcbAirTraceClaim {
    /// Build the claim from the projective EC trace: every mul row carries
    /// real lhs/rhs/result, natively verified; the muls themselves are proven
    /// by the hinted-mul component.
    pub fn from_projective_trace_lite(
        trace: &ProjectiveEcTraceClaim,
    ) -> Result<Self, ProjectiveRcbAirError> {
        use rayon::prelude::*;
        let rows = trace
            .rows
            .par_iter()
            .enumerate()
            .map(|(source_index, row)| ProjectiveRcbAirRow::from_projective_row(source_index, row))
            .collect::<Result<Vec<_>, _>>()?;
        let claim = Self { rows };
        claim.verify_against_projective_trace(trace)?;
        Ok(claim)
    }

    pub fn verify_against_projective_trace(
        &self,
        trace: &ProjectiveEcTraceClaim,
    ) -> Result<(), ProjectiveRcbAirError> {
        if self.rows.len() != trace.rows.len() {
            return Err(ProjectiveRcbAirError::RowCountMismatch {
                expected: trace.rows.len(),
                actual: self.rows.len(),
            });
        }
        for (source_index, (air_row, projective_row)) in
            self.rows.iter().zip(&trace.rows).enumerate()
        {
            air_row.verify_against_projective_row(source_index, projective_row)?;
        }
        Ok(())
    }

    pub fn active_row_count(&self) -> usize {
        self.rows.len()
    }

    pub fn mul_row_count(&self) -> usize {
        self.rows.iter().map(|row| row.muls.len()).sum()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbAirRow {
    pub source_index: usize,
    pub sig_id: M31,
    pub cert_id: M31,
    pub op: ProjectiveEcOp,
    pub output_projective: ProjectivePoint,
    pub muls: Vec<ProjectiveRcbMulRow>,
}

/// Number of mul-result limb values one EC op contributes to a projective-source
/// consumer (C5 plumbing): `PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP` muls ×
/// `{LHS, RHS, RESULT}` × `N_LIMBS`. The consumer commits this many columns and
/// CONSUMES them from the silo keyed `(source_index, mul_index, role,
/// limb_index, limb)`.
pub const PROJECTIVE_RCB_OP_MUL_LIMB_COLUMNS: usize =
    PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP * 3 * N_LIMBS;

/// Flatten an EC op's proven mul `lhs`/`rhs`/`result` limbs into the canonical
/// consumer layout: for `mul_index` in `0..PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP`,
/// then role in `[LHS, RHS, RESULT]`, then `limb_index` in `0..N_LIMBS`. This is
/// the SINGLE source of truth for the silo→source mul-limb column order; the
/// consumer AIR reads and keys columns in exactly this order.
///
/// Returns `(limbs, has_muls)`. `has_muls` is `true` iff the op emitted the full
/// `PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP` muls — `Double` (always) and `MixedAdd`
/// with a FINITE operand. A `MixedAdd` with an infinity operand is a no-op that
/// emits ZERO muls (`rcb_mixed_add_with_mul_rows` early-returns); for it
/// `has_muls = false` and `limbs` are all zero, so the consumer must gate its
/// `ProjectiveRcbMulResultRelation` consumes by `has_muls` to match the silo
/// (which provides nothing for a 0-mul op). This keeps the 3-way balance closed.
pub(crate) fn projective_rcb_op_mul_limbs(
    source_index: usize,
    row: &ProjectiveEcRow,
) -> Result<([M31; PROJECTIVE_RCB_OP_MUL_LIMB_COLUMNS], bool), ProjectiveRcbAirError> {
    let air_row = ProjectiveRcbAirRow::from_projective_row(source_index, row)?;
    let mut values = [M31::from_u32_unchecked(0); PROJECTIVE_RCB_OP_MUL_LIMB_COLUMNS];
    if air_row.muls.is_empty() {
        // Infinity-operand MixedAdd no-op: zero muls, zero limbs, not gated in.
        return Ok((values, false));
    }
    debug_assert_eq!(air_row.muls.len(), PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP);
    let mut column = 0;
    for mul in &air_row.muls {
        for limbs in [
            mul.trace.lhs.limbs(),
            mul.trace.rhs.limbs(),
            mul.trace.result.limbs(),
        ] {
            for limb in limbs {
                values[column] = *limb;
                column += 1;
            }
        }
    }
    debug_assert_eq!(column, PROJECTIVE_RCB_OP_MUL_LIMB_COLUMNS);
    Ok((values, true))
}

/// Project the canonical full limb array onto the KEPT consumed-mul slots
/// (the committed block layout after operand dedup), in canonical order.
pub(crate) fn projective_rcb_kept_mul_limbs(
    full: &[M31; PROJECTIVE_RCB_OP_MUL_LIMB_COLUMNS],
) -> Vec<M31> {
    let mut kept = Vec::with_capacity(crate::projective_air::CONSUMED_MUL_KEPT_SLOTS * N_LIMBS);
    for mul in 0..PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP {
        for role in 0..3 {
            if crate::projective_air::consumed_mul_slot_kept(mul, role) {
                let start = (mul * 3 + role) * N_LIMBS;
                kept.extend_from_slice(&full[start..start + N_LIMBS]);
            }
        }
    }
    kept
}

/// Gen-side column layout a projective-source consumer hands to
/// [`consumed_mul_slot_packed_limbs`] so dropped-slot consume values can be
/// computed from the SAME base columns the eval's expressions read.
pub(crate) struct ConsumedMulGenLayout {
    pub op_col: usize,
    pub x1_col: usize,
    pub y1_col: usize,
    pub x2_col: usize,
    pub y2_col: usize,
    pub output_x_col: usize,
    pub output_y_col: usize,
    pub z3_double_col: usize,
    pub z3_mixed_col: Option<usize>,
    /// First kept-limb column (right after the `has_muls` flag).
    pub mul_limb_offset: usize,
}

/// The packed limb values of consumed-mul slot `(mul, role)` at `vec_row`:
/// kept slots read their committed columns; dropped slots evaluate the
/// operand-dedup expressions (mirroring `ConsumedMulLimbs::fill_dropped`).
pub(crate) fn consumed_mul_slot_packed_limbs(
    base: &[M31ColumnEval],
    vec_row: usize,
    layout: &ConsumedMulGenLayout,
    mul: usize,
    role: usize,
) -> Vec<stwo::prover::backend::simd::m31::PackedM31> {
    use stwo::prover::backend::simd::m31::PackedM31;
    if let Some(offset) = crate::projective_air::consumed_mul_kept_column(mul, role) {
        return (0..N_LIMBS)
            .map(|limb| base[layout.mul_limb_offset + offset + limb].data[vec_row])
            .collect();
    }
    let op = base[layout.op_col].data[vec_row];
    let one_minus_op = PackedM31::broadcast(M31::from_u32_unchecked(1)) - op;
    let column = |col: usize, limb: usize| base[col + limb].data[vec_row];
    let one_limb =
        |limb: usize| PackedM31::broadcast(M31::from_u32_unchecked(u32::from(limb == 0)));
    let b = crate::limbs::P256M31BigInt::from_u256(&crate::types::U256::from_le_u64s(
        &crate::constants::P256_B,
    ));
    let r2_offset =
        crate::projective_air::consumed_mul_kept_column(2, 2).expect("R2 is a kept slot");
    (0..N_LIMBS)
        .map(|limb| match (mul, role) {
            (0, 0) => column(layout.x1_col, limb),
            (0, 1) => op * column(layout.x1_col, limb) + one_minus_op * column(layout.x2_col, limb),
            (1, 0) => column(layout.y1_col, limb),
            (1, 1) => op * column(layout.y1_col, limb) + one_minus_op * column(layout.y2_col, limb),
            (3, 0) => op * column(layout.x1_col, limb) + one_minus_op * column(layout.y2_col, limb),
            (3, 1) => op * column(layout.y1_col, limb) + one_minus_op * one_limb(limb),
            (4, 0) => op * column(layout.x1_col, limb) + one_minus_op * column(layout.x2_col, limb),
            (4, 1) => one_limb(limb),
            (5, 0) => PackedM31::broadcast(b.limbs()[limb]),
            (5, 1) => {
                op * base[layout.mul_limb_offset + r2_offset + limb].data[vec_row]
                    + one_minus_op * one_limb(limb)
            }
            (13, 0) => column(layout.output_x_col, limb),
            (13, 1) | (14, 1) => match layout.z3_mixed_col {
                Some(z3_mixed_col) => {
                    column(layout.z3_double_col, limb) + column(z3_mixed_col, limb)
                }
                None => column(layout.z3_double_col, limb),
            },
            (14, 0) => column(layout.output_y_col, limb),
            _ => unreachable!("dropped-slot table covers exactly the dedup slots"),
        })
        .collect()
}

impl ProjectiveRcbAirRow {
    fn from_projective_row(
        source_index: usize,
        row: &ProjectiveEcRow,
    ) -> Result<Self, ProjectiveRcbAirError> {
        row.verify()?;
        let lhs = ProjectivePoint::from_prepared(&row.lhs_affine);
        let mut muls = Vec::with_capacity(PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP);
        let output_projective = match row.op {
            ProjectiveEcOp::Double => {
                rcb_double_with_mul_rows(&lhs, &row.output_affine, &mut muls)?
            }
            ProjectiveEcOp::MixedAdd => {
                rcb_mixed_add_with_mul_rows(&lhs, &row.rhs_affine, &row.output_affine, &mut muls)?
            }
        };
        if output_projective != row.output_projective {
            return Err(ProjectiveRcbAirError::ProjectiveOutputMismatch { source_index });
        }
        Ok(Self {
            source_index,
            sig_id: row.sig_id,
            cert_id: row.cert_id,
            op: row.op,
            output_projective,
            muls,
        })
    }

    fn verify_against_projective_row(
        &self,
        source_index: usize,
        row: &ProjectiveEcRow,
    ) -> Result<(), ProjectiveRcbAirError> {
        self.verify()?;
        let expected = Self::from_projective_row(source_index, row)?;
        if self == &expected {
            Ok(())
        } else {
            Err(ProjectiveRcbAirError::TraceRowsMismatch { source_index })
        }
    }

    pub fn verify(&self) -> Result<(), ProjectiveRcbAirError> {
        self.output_projective.verify()?;
        for mul in &self.muls {
            mul.verify()?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbMulRow {
    pub step: ProjectiveRcbMulStep,
    pub trace: FpSolinasMulTrace,
    /// Identity fast-path: `true` iff this is a `lhs · 1` mul (ladder affine
    /// `z = 1`). Identity rows carry `rhs = 1`, `result = lhs` (RAW — `lhs`
    /// may be non-canonical, which is harmless mod p) with zeroed schoolbook
    /// internals, so `trace.verify()` is skipped; the hinted-mul component
    /// recomputes and proves the mul like any other.
    pub is_identity: bool,
}

impl ProjectiveRcbMulRow {
    /// Build a mul row: real `FpSolinasMulTrace` (the native
    /// `lhs·rhs = result` check runs and consumers read the same limbs); the
    /// mul is proven by the hinted-mul component.
    pub(crate) fn new_lite(
        step: ProjectiveRcbMulStep,
        lhs: &U256,
        rhs: &U256,
    ) -> Result<Self, ProjectiveRcbAirError> {
        let trace = FpSolinasMulTrace::new(lhs, rhs)?;
        Ok(Self {
            step,
            trace,
            is_identity: false,
        })
    }

    pub(crate) fn identity(step: ProjectiveRcbMulStep, lhs: &U256) -> Self {
        let lhs_big = P256M31BigInt::from_u256(lhs);
        let one_big = P256M31BigInt::from_u256(&U256::from_le_u64s(&[1, 0, 0, 0]));
        let trace = FpSolinasMulTrace {
            lhs: lhs_big.clone(),
            rhs: one_big,
            result: lhs_big,
            raw_product: [0i128; FP_SOLINAS_RAW_LIMBS],
            folded_coefficients: [0i128; N_LIMBS],
            correction: 0,
            carries: [0i128; N_LIMBS],
        };
        Self {
            step,
            trace,
            is_identity: true,
        }
    }

    pub fn verify(&self) -> Result<(), ProjectiveRcbAirError> {
        if self.is_identity {
            // Identity row: `result = lhs · 1` by construction; the zeroed
            // schoolbook internals would fail `trace.verify()`, and the
            // hinted-mul component proves the mul anyway.
            return Ok(());
        }
        self.trace.verify()?;
        Ok(())
    }
}

/// Field-muls one EC op contributes to the silo. The first 13 are the
/// renes-costello-batina (RCB) formula muls (`Double`: 13 always; `MixedAdd`:
/// 13 for a finite operand, 0 for an infinity operand — the no-op early-returns
/// before any mul). The last 2 (`M13`, `M14`) are the affine-normalization muls
/// `output_affine.{x,y} · output_projective.z`; C5-2a-ii will bind their
/// operands/result to prove `output_affine = to_affine(output_projective)`. The
/// silo proves all 15 products via its Solinas reduction; this constant is the
/// SINGLE source of truth for the per-op mul count (consumer column widths and
/// every count test scale from it).
pub const PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP: usize = 15;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProjectiveRcbMulStep {
    DoubleX1Squared,
    DoubleY1Squared,
    DoubleZ1Squared,
    DoubleX1Y1,
    DoubleX1Z1,
    DoubleBT2,
    DoubleX3Y3,
    DoubleX3T3,
    DoubleBZ3,
    DoubleT0Z3,
    DoubleY1Z1,
    DoubleT0Z3Final,
    DoubleT0T1,
    /// M13: `output_affine.x · output_projective.z` (affine-norm, → x3).
    DoubleAffineNormX,
    /// M14: `output_affine.y · output_projective.z` (affine-norm, → y3).
    DoubleAffineNormY,
    MixedX1X2,
    MixedY1Y2,
    MixedX2Y2X1Y1,
    MixedY2Z1,
    MixedX2Z1,
    MixedBZ1,
    MixedBY3,
    MixedT4Y3,
    MixedT0Y3,
    MixedX3Z3,
    MixedT3X3,
    MixedT4Z3,
    MixedT3T0,
    /// M13: `output_affine.x · output_projective.z` (affine-norm, → x3).
    MixedAffineNormX,
    /// M14: `output_affine.y · output_projective.z` (affine-norm, → y3).
    MixedAffineNormY,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProjectiveRcbAirError {
    Projective(ProjectiveEcError),
    FpSolinas(FpSolinasError),
    FpSolinasReduction(FpSolinasReductionTraceError),
    RowCountMismatch {
        expected: usize,
        actual: usize,
    },
    RawProductChunkCountMismatch {
        expected: usize,
        actual: usize,
    },
    RawProductCoeffOutOfRange {
        coeff: usize,
    },
    RawProductChunkOutOfRange {
        coeff: usize,
        chunk: usize,
    },
    RawProductTermMismatch {
        coeff: usize,
        chunk: usize,
    },
    RawProductChunkDigitMismatch {
        coeff: usize,
        chunk: usize,
    },
    RawProductChunkUseCountMismatch {
        coeff: usize,
        chunk: usize,
    },
    RawProductChunkMismatch {
        coeff: usize,
        chunk: usize,
    },
    RawProductCoefficientMismatch,
    RawProductChunkOverflow {
        value: i128,
    },
    FoldedContributionDigitOutOfRange {
        digit_index: usize,
    },
    FoldedContributionMismatch,
    FoldedContributionSumMismatch {
        digit_index: usize,
        group_index: usize,
    },
    FoldedDigitRowCountMismatch {
        expected: usize,
        actual: usize,
    },
    FoldedDigitIndexMismatch {
        expected: usize,
        actual: usize,
    },
    FoldedCarryLinkMismatch {
        digit_index: usize,
    },
    FoldedDigitEquationMismatch {
        digit_index: usize,
        value: i128,
    },
    FoldedDigitContributionGroupOverflow {
        digit_index: usize,
    },
    FoldedDigitContributionSumMismatch {
        digit_index: usize,
    },
    FoldedCoefficientMismatch,
    FoldedDigitMismatch,
    FoldedFinalCarryOutOfRange {
        carry: i128,
    },
    FoldedFinalCarryMismatch {
        folded: i128,
        reduction: i128,
    },
    FoldedReductionDigitMismatch {
        digit_index: usize,
    },
    RelationImbalance {
        relation: &'static str,
    },
    PreprocessedColumnMissing {
        id: String,
    },
    PreprocessedColumnCountMismatch {
        expected: usize,
        actual: usize,
    },
    BaseTraceColumnCountMismatch {
        expected: usize,
        actual: usize,
    },
    BaseTraceRowWidthMismatch {
        expected: usize,
        actual: usize,
    },
    BaseTraceRowCountMismatch {
        max: usize,
        actual: usize,
    },
    InteractionTraceColumnCountMismatch {
        expected: usize,
        actual: usize,
    },
    ProofLayer(String),
    SignedCarryLookupOutOfRange {
        value: i128,
        bound: i64,
    },
    ProjectiveOutputMismatch {
        source_index: usize,
    },
    TraceRowsMismatch {
        source_index: usize,
    },
}

impl From<ProjectiveEcError> for ProjectiveRcbAirError {
    fn from(value: ProjectiveEcError) -> Self {
        Self::Projective(value)
    }
}

impl From<FpSolinasError> for ProjectiveRcbAirError {
    fn from(value: FpSolinasError) -> Self {
        Self::FpSolinas(value)
    }
}

impl From<FpSolinasReductionTraceError> for ProjectiveRcbAirError {
    fn from(value: FpSolinasReductionTraceError) -> Self {
        Self::FpSolinasReduction(value)
    }
}

fn rcb_double_with_mul_rows(
    input: &ProjectivePoint,
    output_affine: &PreparedAffinePoint,
    muls: &mut Vec<ProjectiveRcbMulRow>,
) -> Result<ProjectivePoint, ProjectiveRcbAirError> {
    let x1 = input.x.to_u256();
    let y1 = input.y.to_u256();
    let z1 = input.z.to_u256();

    let t0 = fp_mul(ProjectiveRcbMulStep::DoubleX1Squared, &x1, &x1, muls)?;
    let t1 = fp_mul(ProjectiveRcbMulStep::DoubleY1Squared, &y1, &y1, muls)?;
    // M2 z1·z1 (z1 = 1) → identity, value = z1.
    let mut t2 = fp_mul_identity(ProjectiveRcbMulStep::DoubleZ1Squared, &z1, muls);
    let mut t3 = fp_mul(ProjectiveRcbMulStep::DoubleX1Y1, &x1, &y1, muls)?;
    t3 = fp_add(&t3, &t3);
    // M4 x1·z1 (z1 = 1) → identity, value = x1.
    let mut z3 = fp_mul_identity(ProjectiveRcbMulStep::DoubleX1Z1, &x1, muls);
    z3 = fp_add(&z3, &z3);
    // M5 b·t2 (t2 = z1² = 1) → identity, value = b.
    let mut y3 = fp_mul_identity(ProjectiveRcbMulStep::DoubleBT2, &curve_b(), muls);
    y3 = fp_sub(&y3, &z3);
    let mut x3 = fp_add(&y3, &y3);
    y3 = fp_add(&x3, &y3);
    x3 = fp_sub(&t1, &y3);
    y3 = fp_add(&t1, &y3);
    y3 = fp_mul(ProjectiveRcbMulStep::DoubleX3Y3, &x3, &y3, muls)?;
    x3 = fp_mul(ProjectiveRcbMulStep::DoubleX3T3, &x3, &t3, muls)?;
    t3 = fp_add(&t2, &t2);
    t2 = fp_add(&t2, &t3);
    z3 = fp_mul(ProjectiveRcbMulStep::DoubleBZ3, &curve_b(), &z3, muls)?;
    z3 = fp_sub(&z3, &t2);
    z3 = fp_sub(&z3, &t0);
    t3 = fp_add(&z3, &z3);
    z3 = fp_add(&z3, &t3);
    t3 = fp_add(&t0, &t0);
    let mut t0 = fp_add(&t3, &t0);
    t0 = fp_sub(&t0, &t2);
    t0 = fp_mul(ProjectiveRcbMulStep::DoubleT0Z3, &t0, &z3, muls)?;
    y3 = fp_add(&y3, &t0);
    // M10 y1·z1 (z1 = 1) → identity, value = y1.
    t0 = fp_mul_identity(ProjectiveRcbMulStep::DoubleY1Z1, &y1, muls);
    t0 = fp_add(&t0, &t0);
    z3 = fp_mul(ProjectiveRcbMulStep::DoubleT0Z3Final, &t0, &z3, muls)?;
    x3 = fp_sub(&x3, &z3);
    z3 = fp_mul(ProjectiveRcbMulStep::DoubleT0T1, &t0, &t1, muls)?;
    z3 = fp_add(&z3, &z3);
    z3 = fp_add(&z3, &z3);

    let output = projective_from_u256(x3, y3, z3);
    append_affine_norm_muls(
        ProjectiveRcbMulStep::DoubleAffineNormX,
        ProjectiveRcbMulStep::DoubleAffineNormY,
        output_affine,
        &output,
        muls,
    )?;
    Ok(output)
}

fn rcb_mixed_add_with_mul_rows(
    state: &ProjectivePoint,
    operand: &PreparedAffinePoint,
    output_affine: &PreparedAffinePoint,
    muls: &mut Vec<ProjectiveRcbMulRow>,
) -> Result<ProjectivePoint, ProjectiveRcbAirError> {
    let Some(operand) = operand.to_option() else {
        // Infinity-operand no-op: the silo emits ZERO muls for this op (including
        // no affine-norm muls), so the consumer gates its consumes off via
        // `has_muls = false` and the 3-way balance stays closed.
        return Ok(state.clone());
    };

    let x1 = state.x.to_u256();
    let y1 = state.y.to_u256();
    let z1 = state.z.to_u256();
    let x2 = operand.x;
    let y2 = operand.y;

    let mut t0 = fp_mul(ProjectiveRcbMulStep::MixedX1X2, &x1, &x2, muls)?;
    let mut t1 = fp_mul(ProjectiveRcbMulStep::MixedY1Y2, &y1, &y2, muls)?;
    let mut t3 = fp_add(&x2, &y2);
    let mut t4 = fp_add(&x1, &y1);
    t3 = fp_mul(ProjectiveRcbMulStep::MixedX2Y2X1Y1, &t3, &t4, muls)?;
    t4 = fp_add(&t0, &t1);
    t3 = fp_sub(&t3, &t4);
    // M3 y2·z1 (z1 = 1) → identity, value = y2.
    t4 = fp_mul_identity(ProjectiveRcbMulStep::MixedY2Z1, &y2, muls);
    t4 = fp_add(&t4, &y1);
    // M4 x2·z1 (z1 = 1) → identity, value = x2.
    let mut y3 = fp_mul_identity(ProjectiveRcbMulStep::MixedX2Z1, &x2, muls);
    y3 = fp_add(&y3, &x1);
    // M5 b·z1 (z1 = 1) → identity, value = b.
    let mut z3 = fp_mul_identity(ProjectiveRcbMulStep::MixedBZ1, &curve_b(), muls);
    let mut x3 = fp_sub(&y3, &z3);
    z3 = fp_add(&x3, &x3);
    x3 = fp_add(&x3, &z3);
    z3 = fp_sub(&t1, &x3);
    x3 = fp_add(&t1, &x3);
    y3 = fp_mul(ProjectiveRcbMulStep::MixedBY3, &curve_b(), &y3, muls)?;
    t1 = fp_add(&z1, &z1);
    let t2 = fp_add(&t1, &z1);
    y3 = fp_sub(&y3, &t2);
    y3 = fp_sub(&y3, &t0);
    t1 = fp_add(&y3, &y3);
    y3 = fp_add(&t1, &y3);
    t1 = fp_add(&t0, &t0);
    t0 = fp_add(&t1, &t0);
    t0 = fp_sub(&t0, &t2);
    t1 = fp_mul(ProjectiveRcbMulStep::MixedT4Y3, &t4, &y3, muls)?;
    let t2 = fp_mul(ProjectiveRcbMulStep::MixedT0Y3, &t0, &y3, muls)?;
    y3 = fp_mul(ProjectiveRcbMulStep::MixedX3Z3, &x3, &z3, muls)?;
    y3 = fp_add(&y3, &t2);
    x3 = fp_mul(ProjectiveRcbMulStep::MixedT3X3, &t3, &x3, muls)?;
    x3 = fp_sub(&x3, &t1);
    z3 = fp_mul(ProjectiveRcbMulStep::MixedT4Z3, &t4, &z3, muls)?;
    t1 = fp_mul(ProjectiveRcbMulStep::MixedT3T0, &t3, &t0, muls)?;
    z3 = fp_add(&z3, &t1);

    let output = projective_from_u256(x3, y3, z3);
    append_affine_norm_muls(
        ProjectiveRcbMulStep::MixedAffineNormX,
        ProjectiveRcbMulStep::MixedAffineNormY,
        output_affine,
        &output,
        muls,
    )?;
    Ok(output)
}

/// Append the 2 affine-normalization muls (M13, M14) for an EC op that emitted
/// the full RCB formula muls: `M13 = output_affine.x · output_projective.z` and
/// `M14 = output_affine.y · output_projective.z`. For a finite output these
/// equal `output_projective.{x,y}` (the to-affine identity); for the canonical
/// infinity output (`z = 0`) both products are `0`. Either way the silo proves
/// the honest product via [`ProjectiveRcbMulRow::new`]'s Solinas reduction. The
/// downstream C5-2a-ii constraint binds these operands/result to the consumer's
/// committed affine + projective output, completing the soundness argument.
fn append_affine_norm_muls(
    step_x: ProjectiveRcbMulStep,
    step_y: ProjectiveRcbMulStep,
    output_affine: &PreparedAffinePoint,
    output_projective: &ProjectivePoint,
    muls: &mut Vec<ProjectiveRcbMulRow>,
) -> Result<(), ProjectiveRcbAirError> {
    let affine_x = output_affine.x.to_u256();
    let affine_y = output_affine.y.to_u256();
    let projective_z = output_projective.z.to_u256();
    fp_mul(step_x, &affine_x, &projective_z, muls)?;
    fp_mul(step_y, &affine_y, &projective_z, muls)?;
    Ok(())
}

fn fp_mul(
    step: ProjectiveRcbMulStep,
    lhs: &U256,
    rhs: &U256,
    muls: &mut Vec<ProjectiveRcbMulRow>,
) -> Result<U256, ProjectiveRcbAirError> {
    let row = ProjectiveRcbMulRow::new_lite(step, lhs, rhs)?;
    let result = row.trace.result.to_u256();
    muls.push(row);
    Ok(result)
}

/// `value · 1 = value` identity mul (ladder affine `z = 1`): pushes an identity
/// row (empty sub-families, `rhs = 1`, `result = value`) and returns `value`.
/// The silo AIR proves it via `rhs = 1 ∧ result = lhs` instead of a full Solinas
/// reduction. Caller must pass the genuine non-one operand as `value`.
fn fp_mul_identity(
    step: ProjectiveRcbMulStep,
    value: &U256,
    muls: &mut Vec<ProjectiveRcbMulRow>,
) -> U256 {
    let row = ProjectiveRcbMulRow::identity(step, value);
    let result = row.trace.result.to_u256();
    muls.push(row);
    result
}

fn projective_from_u256(x: U256, y: U256, z: U256) -> ProjectivePoint {
    ProjectivePoint {
        x: crate::limbs::P256M31BigInt::from_u256(&x),
        y: crate::limbs::P256M31BigInt::from_u256(&y),
        z: crate::limbs::P256M31BigInt::from_u256(&z),
    }
}

fn fp_add(lhs: &U256, rhs: &U256) -> U256 {
    add_mod_witness(lhs, rhs, &modulus()).result.to_u256()
}

fn fp_sub(lhs: &U256, rhs: &U256) -> U256 {
    sub_mod_witness(lhs, rhs, &modulus()).result.to_u256()
}

fn modulus() -> U256 {
    U256::from_le_u64s(&P256_MODULUS)
}

fn curve_b() -> U256 {
    U256::from_le_u64s(&P256_B)
}
