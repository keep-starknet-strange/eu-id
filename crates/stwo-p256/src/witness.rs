use crypto_bigint::U256;
use crate::limbs::LimbsM31;
use crate::ops::affine_point::AffinePoint;

/// Result of a modular multiplication, with all intermediate witness values
/// needed for trace generation and constraint verification.
#[derive(Clone, Debug)]
pub struct MulModWitness {
    pub a: LimbsM31,
    pub b: LimbsM31,
    pub modulus: LimbsM31,
    pub result: LimbsM31,
    pub quotient: LimbsM31,
    /// Carries from the verification equation: a*b - q*p - r = 0 (limb by limb with carries)
    pub carries: Vec<i64>,
}

/// Result of a modular addition.
#[derive(Clone, Debug)]
pub struct AddModWitness {
    pub a: LimbsM31,
    pub b: LimbsM31,
    pub modulus: LimbsM31,
    pub result: LimbsM31,
    /// Whether a borrow/reduction was needed (0 or 1).
    pub reduced: u32,
    pub carries: Vec<i64>,
}

/// Result of a modular subtraction.
#[derive(Clone, Debug)]
pub struct SubModWitness {
    pub a: LimbsM31,
    pub b: LimbsM31,
    pub modulus: LimbsM31,
    pub result: LimbsM31,
    /// Whether a borrow was needed (0 or 1).
    pub borrowed: u32,
    pub carries: Vec<i64>,
}

/// Witness data for a point doubling operation on P-256.
/// 2P = R where P = (x1, y1), R = (x3, y3)
///
/// Formulas (short Weierstrass y^2 = x^3 + ax + b, a = -3 for P-256):
///   lambda = (3*x1^2 + a) / (2*y1)
///   x3 = lambda^2 - 2*x1
///   y3 = lambda*(x1 - x3) - y1
#[derive(Clone, Debug)]
pub struct PointDoubleWitness {
    pub input: AffinePoint,
    pub output: AffinePoint,
    pub lambda: U256,
    pub lambda_num: U256,   // 3*x1^2 + a
    pub lambda_denom: U256, // 2*y1
}

/// Witness data for a point addition on P-256.
/// P + Q = R where P = (x1, y1), Q = (x2, y2), R = (x3, y3)
///
/// Formulas:
///   lambda = (y2 - y1) / (x2 - x1)
///   x3 = lambda^2 - x1 - x2
///   y3 = lambda*(x1 - x3) - y1
#[derive(Clone, Debug)]
pub struct PointAddWitness {
    pub p: AffinePoint,
    pub q: AffinePoint,
    pub output: AffinePoint,
    pub lambda: U256,
}