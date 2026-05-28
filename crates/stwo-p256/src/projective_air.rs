use stwo::core::fields::m31::M31;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry,
};
use stwo_p256_utils::constants::N_LIMBS;

use crate::constants::{P256_B, P256_MODULUS};
use crate::field_ops::{add_mod_witness, sub_mod_witness};
use crate::fp_solinas::{FpSolinasError, FpSolinasMulTrace};
use crate::fp_solinas_air::{
    add_fp_solinas_reduction_digit, FpSolinasReductionDigitColumns, FpSolinasReductionRelations,
    FpSolinasReductionTraceClaim, FpSolinasReductionTraceError, FP_SOLINAS_REDUCTION_DIGITS,
    FP_SOLINAS_REDUCTION_DIGIT_TRACE_COLUMNS,
};
use crate::limbs::{EvalP256BigIntExt, P256EvalBigInt};
use crate::prepared_table::PreparedAffinePoint;
use crate::projective::{
    ProjectiveEcError, ProjectiveEcOp, ProjectiveEcRow, ProjectiveEcTraceClaim, ProjectivePoint,
};
use crate::range_checks::{add_range_check, RangeCheckRelation};
use crate::types::U256;

pub type ProjectiveRcbMulComponent = FrameworkComponent<ProjectiveRcbMulEval>;

pub const PROJECTIVE_RCB_MUL_LIMB_RELATION_ARITY: usize = 5;
pub const PROJECTIVE_RCB_MUL_ROLE_LHS: u32 = 0;
pub const PROJECTIVE_RCB_MUL_ROLE_RHS: u32 = 1;
pub const PROJECTIVE_RCB_MUL_ROLE_RESULT: u32 = 2;
pub const PROJECTIVE_RCB_MUL_ID_TRACE_COLUMNS: usize = 2;
pub const PROJECTIVE_RCB_MUL_ACTIVE_TRACE_COLUMNS: usize = 1;
pub const PROJECTIVE_RCB_MUL_LIMB_TRACE_COLUMNS: usize = 3 * N_LIMBS;
pub const PROJECTIVE_RCB_MUL_REDUCTION_TRACE_COLUMNS: usize =
    FP_SOLINAS_REDUCTION_DIGITS * FP_SOLINAS_REDUCTION_DIGIT_TRACE_COLUMNS + 1;
pub const PROJECTIVE_RCB_MUL_TRACE_COLUMNS: usize = PROJECTIVE_RCB_MUL_ACTIVE_TRACE_COLUMNS
    + PROJECTIVE_RCB_MUL_ID_TRACE_COLUMNS
    + PROJECTIVE_RCB_MUL_LIMB_TRACE_COLUMNS
    + PROJECTIVE_RCB_MUL_REDUCTION_TRACE_COLUMNS;

relation!(
    ProjectiveRcbMulLimbRelation,
    PROJECTIVE_RCB_MUL_LIMB_RELATION_ARITY
);

#[derive(Clone)]
pub struct ProjectiveRcbMulEval {
    pub log_size: u32,
    pub relations: ProjectiveRcbMulComponentRelations,
}

impl FrameworkEval for ProjectiveRcbMulEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.next_trace_mask();
        let source_index = eval.next_trace_mask();
        let mul_index = eval.next_trace_mask();
        let columns = ProjectiveRcbMulColumns::read(&mut eval);

        eval.add_constraint(active.clone() * (one::<E>() - active.clone()));
        add_projective_rcb_mul_row(
            &mut eval,
            self.relations.as_refs(),
            active,
            source_index,
            mul_index,
            &columns,
        );
        eval.finalize_logup_in_pairs();
        eval
    }
}

#[derive(Clone)]
pub struct ProjectiveRcbMulComponentRelations {
    pub range13: RangeCheckRelation,
    pub signed_carry: RangeCheckRelation,
    pub mul_limb: ProjectiveRcbMulLimbRelation,
}

impl ProjectiveRcbMulComponentRelations {
    pub fn dummy() -> Self {
        Self {
            range13: RangeCheckRelation::dummy(),
            signed_carry: RangeCheckRelation::dummy(),
            mul_limb: ProjectiveRcbMulLimbRelation::dummy(),
        }
    }

    pub fn as_refs(&self) -> ProjectiveRcbMulRelations<'_> {
        ProjectiveRcbMulRelations {
            range13: &self.range13,
            signed_carry: &self.signed_carry,
            mul_limb: &self.mul_limb,
        }
    }
}

#[derive(Clone, Copy)]
pub struct ProjectiveRcbMulRelations<'a> {
    pub range13: &'a RangeCheckRelation,
    pub signed_carry: &'a RangeCheckRelation,
    pub mul_limb: &'a ProjectiveRcbMulLimbRelation,
}

pub struct ProjectiveRcbMulColumns<E: EvalAtRow> {
    pub lhs: P256EvalBigInt<E>,
    pub rhs: P256EvalBigInt<E>,
    pub result: P256EvalBigInt<E>,
    pub folded_final_carry: E::F,
    pub reduction: [FpSolinasReductionDigitColumns<E>; FP_SOLINAS_REDUCTION_DIGITS],
}

impl<E: EvalAtRow> ProjectiveRcbMulColumns<E> {
    fn read(eval: &mut E) -> Self {
        Self {
            lhs: eval.next_p256_bigint(),
            rhs: eval.next_p256_bigint(),
            result: eval.next_p256_bigint(),
            folded_final_carry: eval.next_trace_mask(),
            reduction: core::array::from_fn(|_| FpSolinasReductionDigitColumns {
                folded_digit: eval.next_trace_mask(),
                correction_product_digit: eval.next_trace_mask(),
                result_limb: eval.next_trace_mask(),
                prev_carry: eval.next_trace_mask(),
                carry: eval.next_trace_mask(),
            }),
        }
    }
}

pub fn add_projective_rcb_mul_row<E: EvalAtRow>(
    eval: &mut E,
    relations: ProjectiveRcbMulRelations<'_>,
    gate: E::F,
    source_index: E::F,
    mul_index: E::F,
    columns: &ProjectiveRcbMulColumns<E>,
) {
    add_mul_limb_group(
        eval,
        relations,
        gate.clone(),
        source_index.clone(),
        mul_index.clone(),
        PROJECTIVE_RCB_MUL_ROLE_LHS,
        &columns.lhs,
    );
    add_mul_limb_group(
        eval,
        relations,
        gate.clone(),
        source_index.clone(),
        mul_index.clone(),
        PROJECTIVE_RCB_MUL_ROLE_RHS,
        &columns.rhs,
    );
    add_mul_limb_group(
        eval,
        relations,
        gate.clone(),
        source_index,
        mul_index,
        PROJECTIVE_RCB_MUL_ROLE_RESULT,
        &columns.result,
    );

    let reduction_relations = FpSolinasReductionRelations {
        range13: relations.range13,
        signed_carry: relations.signed_carry,
    };
    for row in &columns.reduction {
        add_fp_solinas_reduction_digit(eval, reduction_relations, gate.clone(), row);
    }

    eval.add_constraint(gate.clone() * columns.reduction[0].prev_carry.clone());
    for digit_index in 1..FP_SOLINAS_REDUCTION_DIGITS {
        eval.add_constraint(
            gate.clone()
                * (columns.reduction[digit_index].prev_carry.clone()
                    - columns.reduction[digit_index - 1].carry.clone()),
        );
    }
    eval.add_constraint(
        gate.clone()
            * columns.folded_final_carry.clone()
            * (columns.folded_final_carry.clone() + one::<E>()),
    );
    eval.add_constraint(
        gate * (columns.reduction[FP_SOLINAS_REDUCTION_DIGITS - 1]
            .carry
            .clone()
            + columns.folded_final_carry.clone()),
    );
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbAirTraceClaim {
    pub rows: Vec<ProjectiveRcbAirRow>,
}

impl ProjectiveRcbAirTraceClaim {
    pub fn from_projective_trace(
        trace: &ProjectiveEcTraceClaim,
    ) -> Result<Self, ProjectiveRcbAirError> {
        let rows = trace
            .rows
            .iter()
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

    pub fn reduction_row_count(&self) -> usize {
        self.rows
            .iter()
            .flat_map(|row| &row.muls)
            .map(|mul| mul.reduction.rows.len())
            .sum()
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

impl ProjectiveRcbAirRow {
    fn from_projective_row(
        source_index: usize,
        row: &ProjectiveEcRow,
    ) -> Result<Self, ProjectiveRcbAirError> {
        row.verify()?;
        let lhs = ProjectivePoint::from_prepared(&row.lhs_affine);
        let mut muls = Vec::with_capacity(PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP);
        let output_projective = match row.op {
            ProjectiveEcOp::Double => rcb_double_with_mul_rows(&lhs, &mut muls)?,
            ProjectiveEcOp::MixedAdd => {
                rcb_mixed_add_with_mul_rows(&lhs, &row.rhs_affine, &mut muls)?
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
    pub reduction: FpSolinasReductionTraceClaim,
}

impl ProjectiveRcbMulRow {
    fn new(
        step: ProjectiveRcbMulStep,
        lhs: &U256,
        rhs: &U256,
    ) -> Result<Self, ProjectiveRcbAirError> {
        let trace = FpSolinasMulTrace::new(lhs, rhs)?;
        let reduction = FpSolinasReductionTraceClaim::from_mul_trace(&trace)?;
        Ok(Self {
            step,
            trace,
            reduction,
        })
    }

    pub fn verify(&self) -> Result<(), ProjectiveRcbAirError> {
        self.trace.verify()?;
        self.reduction.verify_against_mul_trace(&self.trace)?;
        Ok(())
    }
}

pub const PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP: usize = 13;

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
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProjectiveRcbAirError {
    Projective(ProjectiveEcError),
    FpSolinas(FpSolinasError),
    FpSolinasReduction(FpSolinasReductionTraceError),
    RowCountMismatch { expected: usize, actual: usize },
    ProjectiveOutputMismatch { source_index: usize },
    TraceRowsMismatch { source_index: usize },
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

fn add_mul_limb_group<E: EvalAtRow>(
    eval: &mut E,
    relations: ProjectiveRcbMulRelations<'_>,
    gate: E::F,
    source_index: E::F,
    mul_index: E::F,
    role: u32,
    value: &P256EvalBigInt<E>,
) {
    for (limb_index, limb) in value.limbs().iter().enumerate() {
        add_range_check(eval, relations.range13, gate.clone(), limb.clone());
        eval.add_to_relation(RelationEntry::new(
            relations.mul_limb,
            -E::EF::from(gate.clone()),
            &[
                source_index.clone(),
                mul_index.clone(),
                constant(role),
                constant(limb_index as u32),
                limb.clone(),
            ],
        ));
    }
}

fn constant<F: From<M31>>(value: u32) -> F {
    F::from(M31::from_u32_unchecked(value))
}

fn one<E: EvalAtRow>() -> E::F {
    constant(1)
}

fn rcb_double_with_mul_rows(
    input: &ProjectivePoint,
    muls: &mut Vec<ProjectiveRcbMulRow>,
) -> Result<ProjectivePoint, ProjectiveRcbAirError> {
    let x1 = input.x.to_u256();
    let y1 = input.y.to_u256();
    let z1 = input.z.to_u256();

    let t0 = fp_mul(ProjectiveRcbMulStep::DoubleX1Squared, &x1, &x1, muls)?;
    let t1 = fp_mul(ProjectiveRcbMulStep::DoubleY1Squared, &y1, &y1, muls)?;
    let mut t2 = fp_mul(ProjectiveRcbMulStep::DoubleZ1Squared, &z1, &z1, muls)?;
    let mut t3 = fp_mul(ProjectiveRcbMulStep::DoubleX1Y1, &x1, &y1, muls)?;
    t3 = fp_add(&t3, &t3);
    let mut z3 = fp_mul(ProjectiveRcbMulStep::DoubleX1Z1, &x1, &z1, muls)?;
    z3 = fp_add(&z3, &z3);
    let mut y3 = fp_mul(ProjectiveRcbMulStep::DoubleBT2, &curve_b(), &t2, muls)?;
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
    t0 = fp_mul(ProjectiveRcbMulStep::DoubleY1Z1, &y1, &z1, muls)?;
    t0 = fp_add(&t0, &t0);
    z3 = fp_mul(ProjectiveRcbMulStep::DoubleT0Z3Final, &t0, &z3, muls)?;
    x3 = fp_sub(&x3, &z3);
    z3 = fp_mul(ProjectiveRcbMulStep::DoubleT0T1, &t0, &t1, muls)?;
    z3 = fp_add(&z3, &z3);
    z3 = fp_add(&z3, &z3);

    Ok(projective_from_u256(x3, y3, z3))
}

fn rcb_mixed_add_with_mul_rows(
    state: &ProjectivePoint,
    operand: &PreparedAffinePoint,
    muls: &mut Vec<ProjectiveRcbMulRow>,
) -> Result<ProjectivePoint, ProjectiveRcbAirError> {
    let Some(operand) = operand.to_option() else {
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
    t4 = fp_mul(ProjectiveRcbMulStep::MixedY2Z1, &y2, &z1, muls)?;
    t4 = fp_add(&t4, &y1);
    let mut y3 = fp_mul(ProjectiveRcbMulStep::MixedX2Z1, &x2, &z1, muls)?;
    y3 = fp_add(&y3, &x1);
    let mut z3 = fp_mul(ProjectiveRcbMulStep::MixedBZ1, &curve_b(), &z1, muls)?;
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

    Ok(projective_from_u256(x3, y3, z3))
}

fn fp_mul(
    step: ProjectiveRcbMulStep,
    lhs: &U256,
    rhs: &U256,
    muls: &mut Vec<ProjectiveRcbMulRow>,
) -> Result<U256, ProjectiveRcbAirError> {
    let row = ProjectiveRcbMulRow::new(step, lhs, rhs)?;
    let result = row.trace.result.to_u256();
    muls.push(row);
    Ok(result)
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY};
    use crate::curve::point_double;
    use crate::types::AffinePoint;
    use num_traits::Zero;
    use stwo::core::air::Component;
    use stwo::core::fields::qm31::SecureField;
    use stwo_constraint_framework::TraceLocationAllocator;

    fn generator() -> PreparedAffinePoint {
        PreparedAffinePoint::from_affine(AffinePoint {
            x: U256::from_le_u64s(&P256_GX),
            y: U256::from_le_u64s(&P256_GY),
        })
    }

    fn one_row_trace(op: ProjectiveEcOp, rhs: PreparedAffinePoint) -> ProjectiveEcTraceClaim {
        let lhs = generator();
        let output = match op {
            ProjectiveEcOp::Double => {
                PreparedAffinePoint::from_affine(point_double(&lhs.to_option().unwrap()).output)
            }
            ProjectiveEcOp::MixedAdd => {
                let output =
                    crate::curve::point_add(&lhs.to_option().unwrap(), &rhs.to_option().unwrap())
                        .output;
                PreparedAffinePoint::from_affine(output)
            }
        };
        ProjectiveEcTraceClaim {
            rows: vec![ProjectiveEcRow::new(
                M31::from_u32_unchecked(0),
                M31::from_u32_unchecked(0),
                op,
                &lhs,
                &rhs,
                &output,
            )],
        }
    }

    #[test]
    fn projective_rcb_air_rows_verify_double() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");

        claim
            .verify_against_projective_trace(&trace)
            .expect("claim verifies");
        assert_eq!(claim.active_row_count(), 1);
        assert_eq!(claim.mul_row_count(), PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP);
        assert_eq!(
            claim.reduction_row_count(),
            PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP * FP_SOLINAS_REDUCTION_DIGITS
        );
    }

    #[test]
    fn projective_rcb_air_rows_verify_mixed_add() {
        let g = generator();
        let rhs = PreparedAffinePoint::from_affine(point_double(&g.to_option().unwrap()).output);
        let trace = one_row_trace(ProjectiveEcOp::MixedAdd, rhs);
        let claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");

        claim
            .verify_against_projective_trace(&trace)
            .expect("claim verifies");
        assert_eq!(claim.active_row_count(), 1);
        assert_eq!(claim.mul_row_count(), PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP);
    }

    #[test]
    fn projective_rcb_air_rows_skip_operand_infinity_mixed_add() {
        let lhs = generator();
        let output = lhs.clone();
        let trace = ProjectiveEcTraceClaim {
            rows: vec![ProjectiveEcRow::new(
                M31::from_u32_unchecked(0),
                M31::from_u32_unchecked(0),
                ProjectiveEcOp::MixedAdd,
                &lhs,
                &PreparedAffinePoint::infinity(),
                &output,
            )],
        };
        let claim = ProjectiveRcbAirTraceClaim::from_projective_trace(&trace)
            .expect("valid infinity-add RCB AIR trace");

        claim
            .verify_against_projective_trace(&trace)
            .expect("claim verifies");
        assert_eq!(claim.mul_row_count(), 0);
    }

    #[test]
    fn projective_rcb_air_rows_detect_mutated_reduction_digit() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let mut claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        claim.rows[0].muls[0].reduction.rows[0].folded_digit ^= 1;

        let err = claim
            .verify_against_projective_trace(&trace)
            .expect_err("mutated reduction row must fail");

        assert!(matches!(
            err,
            ProjectiveRcbAirError::FpSolinasReduction(
                FpSolinasReductionTraceError::TraceRowsMismatch
                    | FpSolinasReductionTraceError::ReductionEquationMismatch { .. }
            )
        ));
    }

    #[test]
    fn projective_rcb_air_rows_detect_mutated_projective_output() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let mut claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        claim.rows[0].output_projective.x = crate::limbs::P256M31BigInt::zero();

        let err = claim
            .verify_against_projective_trace(&trace)
            .expect_err("mutated output must fail");

        assert!(matches!(
            err,
            ProjectiveRcbAirError::TraceRowsMismatch { .. }
                | ProjectiveRcbAirError::Projective(ProjectiveEcError::InvalidProjectiveInfinity)
        ));
    }

    #[test]
    fn projective_rcb_mul_eval_allocates_expected_width() {
        let mut allocator = TraceLocationAllocator::default();
        let component = ProjectiveRcbMulComponent::new(
            &mut allocator,
            ProjectiveRcbMulEval {
                log_size: 6,
                relations: ProjectiveRcbMulComponentRelations::dummy(),
            },
            SecureField::zero(),
        );

        assert_eq!(
            PROJECTIVE_RCB_MUL_TRACE_COLUMNS,
            1 + 2 + 3 * N_LIMBS + 1 + 5 * FP_SOLINAS_REDUCTION_DIGITS
        );
        assert_eq!(
            component.trace_log_degree_bounds()[1].len(),
            PROJECTIVE_RCB_MUL_TRACE_COLUMNS
        );
        assert_eq!(PROJECTIVE_RCB_MUL_LIMB_RELATION_ARITY, 5);
        assert_eq!(
            ProjectiveRcbMulEval {
                log_size: 6,
                relations: ProjectiveRcbMulComponentRelations::dummy(),
            }
            .max_constraint_log_degree_bound(),
            8
        );
    }
}
