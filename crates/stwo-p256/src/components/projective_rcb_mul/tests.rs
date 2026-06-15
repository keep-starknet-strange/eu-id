//! Native-claim tests for the projective RCB mul rows (the lite/hinted-era
//! surface: row building, native verification, mutation detection).

use super::*;
use crate::constants::{P256_GX, P256_GY};
use crate::curve::point_double;
use crate::prepared_table::PreparedAffinePoint;
use crate::projective::{
    ProjectiveEcError, ProjectiveEcOp, ProjectiveEcRow, ProjectiveEcTraceClaim,
};
use crate::types::{AffinePoint, U256};
use stwo::core::fields::m31::M31;

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
        ProjectiveRcbAirTraceClaim::from_projective_trace_lite(&trace).expect("valid trace");

    claim
        .verify_against_projective_trace(&trace)
        .expect("claim verifies");
    assert_eq!(claim.active_row_count(), 1);
    assert_eq!(claim.mul_row_count(), PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP);
}

#[test]
fn projective_rcb_air_rows_verify_mixed_add() {
    let g = generator();
    let rhs = PreparedAffinePoint::from_affine(point_double(&g.to_option().unwrap()).output);
    let trace = one_row_trace(ProjectiveEcOp::MixedAdd, rhs);
    let claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace_lite(&trace).expect("valid trace");

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
    let claim = ProjectiveRcbAirTraceClaim::from_projective_trace_lite(&trace)
        .expect("valid infinity-add trace");

    claim
        .verify_against_projective_trace(&trace)
        .expect("claim verifies");
    assert_eq!(claim.mul_row_count(), 0);
}

#[test]
fn projective_rcb_air_rows_detect_mutated_projective_output() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let mut claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace_lite(&trace).expect("valid trace");
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
fn projective_rcb_air_rows_detect_mutated_mul_result() {
    let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
    let mut claim =
        ProjectiveRcbAirTraceClaim::from_projective_trace_lite(&trace).expect("valid trace");
    let limbs = claim.rows[0].muls[0].trace.result.limbs_mut();
    limbs[0] = M31::from_u32_unchecked(limbs[0].0 ^ 1);

    claim
        .verify_against_projective_trace(&trace)
        .expect_err("mutated mul result must fail native verification");
}
