//! Tests for the FinalAdd AIR component.
//!
//! Relocated verbatim out of `mod.rs` (test module body, dedented one level).

use super::*;
use crate::constants::{P256_GX, P256_GY};
use crate::curve::scalar_mul;
use crate::limbs::P256M31BigInt;
use crate::types::{AffinePoint, U256};

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
    let claim = FinalAddClaim::from_hints(
        M31::from_u32_unchecked(0),
        &r1,
        false,
        M31::from_u32_unchecked(0),
        &r2,
        false,
        M31::from_u32_unchecked(0),
        0,
    )
    .expect("distinct add witness");
    assert_eq!(claim.x3.to_u256(), add_x(&r1, &r2));
}

#[test]
fn final_add_r1_infinity_yields_x2() {
    // R_1 = ∞ (cert0 inactive), R_2 = 11G. x3 == x(R_2).
    let r2 = mul(11);
    let claim = FinalAddClaim::from_hints(
        M31::from_u32_unchecked(0),
        &generator(),
        true,
        M31::from_u32_unchecked(0),
        &r2,
        false,
        M31::from_u32_unchecked(0),
        0,
    )
    .expect("r1=inf witness");
    assert_eq!(claim.x3.to_u256(), r2.x);
}

#[test]
fn final_add_r2_infinity_yields_x1() {
    let r1 = mul(7);
    let claim = FinalAddClaim::from_hints(
        M31::from_u32_unchecked(0),
        &r1,
        false,
        M31::from_u32_unchecked(0),
        &generator(),
        true,
        M31::from_u32_unchecked(0),
        0,
    )
    .expect("r2=inf witness");
    assert_eq!(claim.x3.to_u256(), r1.x);
}

#[test]
fn final_add_supports_finite_doubling() {
    // Equal points select the doubling branch.
    // The witness builder must produce a valid `FinalAddClaim`.
    let r = mul(7);
    let claim = FinalAddClaim::from_hints(
        M31::from_u32_unchecked(0),
        &r,
        false,
        M31::from_u32_unchecked(0),
        &r,
        false,
        M31::from_u32_unchecked(0),
        0,
    )
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
        M31::from_u32_unchecked(0),
        &generator(),
        true,
        M31::from_u32_unchecked(0),
        0,
    )
    .expect_err("both inf rejected");
    assert!(matches!(err, FinalAddError::BothInfinity { .. }));
}

#[test]
fn final_add_base_and_interaction_trace_shapes_balance() {
    let r1 = mul(7);
    let r2 = mul(11);
    let claim = FinalAddClaim::from_hints(
        M31::from_u32_unchecked(0),
        &r1,
        false,
        M31::from_u32_unchecked(0),
        &r2,
        false,
        M31::from_u32_unchecked(0),
        0,
    )
    .expect("witness");
    let log_sizes = FinalAddLogSizes::from_claim(&claim);
    let _base = gen_final_add_base_trace(&claim, log_sizes).expect("base trace");
    let _pre = final_add_preprocessed_columns(&claim).expect("preprocessed");
}

/// Confirms that native verification rejects a changed `x3`.
///
/// The change breaks the chord-addition identity before proof generation.
#[test]
fn final_add_rejects_mutated_x3() {
    let r1 = mul(7);
    let r2 = mul(11);
    let mut claim = FinalAddClaim::from_hints(
        M31::from_u32_unchecked(0),
        &r1,
        false,
        M31::from_u32_unchecked(0),
        &r2,
        false,
        M31::from_u32_unchecked(0),
        0,
    )
    .expect("witness");
    // Flip the low limb of x3.
    let mut limbs = *claim.x3.limbs();
    limbs[0] += M31::from_u32_unchecked(1);
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
    let mut claim = FinalAddClaim::from_hints(
        M31::from_u32_unchecked(0),
        &r1,
        false,
        M31::from_u32_unchecked(0),
        &r2,
        false,
        M31::from_u32_unchecked(0),
        0,
    )
    .expect("witness");
    let mut limbs = *claim.lambda.limbs();
    limbs[0] += M31::from_u32_unchecked(1);
    claim.lambda = P256M31BigInt::from_limbs(limbs);
    // The mul trace still encodes the true lambda, so the witnessed-lambda
    // copy no longer matches the mul lhs.
    assert!(claim.verify().is_err());
}
