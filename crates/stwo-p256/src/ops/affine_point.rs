use crypto_bigint::{NonZero, U256};
use serde::{Deserialize, Serialize};

use crate::ops::consts::{A_COEFF, GX, GY, MODULUS};
use crate::ops::{add_mod, mod_inverse, mul_mod, sub_mod};

/// An affine point on P-256.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AffinePoint {
    pub x: U256,
    pub y: U256,
}

impl AffinePoint {
    pub fn generator() -> Self {
        Self { x: GX, y: GY }
    }

    pub fn new(x: impl Into<U256>, y: impl Into<U256>) -> Self {
        Self { x: x.into(), y: y.into() }
    }

    /// Returns `[2]self`.
    pub fn double(&self) -> Self {
        let modp = NonZero::new(MODULUS).unwrap();
        let two = U256::from(2u32);
        let three = U256::from(3u32);

        // lambda = (3*x1^2 + a) / (2*y1)
        let x1_sq = mul_mod(&self.x, &self.x, &modp);
        let lambda_num = add_mod(&mul_mod(&three, &x1_sq, &modp), &A_COEFF, &modp);
        let lambda_denom = mul_mod(&two, &self.y, &modp);
        let lambda = mul_mod(&lambda_num, &mod_inverse(&lambda_denom, &modp), &modp);

        // x3 = lambda^2 - 2*x1
        let x3 = sub_mod(&mul_mod(&lambda, &lambda, &modp), &mul_mod(&two, &self.x, &modp), &modp);

        // y3 = lambda*(x1 - x3) - y1
        let y3 = sub_mod(&mul_mod(&lambda, &sub_mod(&self.x, &x3, &modp), &modp), &self.y, &modp);

        Self { x: x3, y: y3 }
    }

    /// Returns `self + other`. Caller must ensure the points are distinct and neither is infinity.
    pub fn add(&self, other: &Self) -> Self {
        let modp = NonZero::new(MODULUS).unwrap();

        // lambda = (y2 - y1) / (x2 - x1)
        let lambda = mul_mod(
            &sub_mod(&other.y, &self.y, &modp),
            &mod_inverse(&sub_mod(&other.x, &self.x, &modp), &modp),
            &modp,
        );

        // x3 = lambda^2 - x1 - x2
        let x3 = sub_mod(
            &mul_mod(&lambda, &lambda, &modp),
            &add_mod(&self.x, &other.x, &modp),
            &modp,
        );

        // y3 = lambda*(x1 - x3) - y1
        let y3 = sub_mod(&mul_mod(&lambda, &sub_mod(&self.x, &x3, &modp), &modp), &self.y, &modp);

        Self { x: x3, y: y3 }
    }

    /// Returns `[k]self`. Panics if `k` is zero.
    pub fn scalar_mul(&self, k: &U256) -> Self {
        let bit_len = k.bits_vartime();
        assert!(bit_len > 0, "scalar must be nonzero");

        let mut acc = self.clone();
        for i in (0..bit_len - 1).rev() {
            acc = acc.double();
            if k.bit_vartime(i) {
                acc = acc.add(self);
            }
        }
        acc
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ops::consts::{MODULUS, ORDER};

    fn modp() -> NonZero<U256> {
        NonZero::new(MODULUS).unwrap()
    }

    const B_COEFF: U256 = U256::from_be_hex(
        "5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b",
    );

    fn on_curve(p: &AffinePoint) -> bool {
        let modp = modp();
        let y2 = mul_mod(&p.y, &p.y, &modp);
        let x3 = mul_mod(&mul_mod(&p.x, &p.x, &modp), &p.x, &modp);
        let ax = mul_mod(&A_COEFF, &p.x, &modp);
        let rhs = add_mod(&add_mod(&x3, &ax, &modp), &B_COEFF, &modp);
        y2 == rhs
    }

    #[test]
    fn test_generator_on_curve() {
        assert!(on_curve(&AffinePoint::generator()));
    }

    #[test]
    fn test_double_on_curve() {
        assert!(on_curve(&AffinePoint::generator().double()));
    }

    #[test]
    fn test_add_on_curve() {
        let g = AffinePoint::generator();
        assert!(on_curve(&g.add(&g.double())));
    }

    #[test]
    fn test_add_commutativity() {
        let g = AffinePoint::generator();
        let g3 = g.double().add(&g);
        let g3b = g.add(&g.double());
        assert_eq!(g3, g3b);
    }

    #[test]
    fn test_scalar_mul_one() {
        let g = AffinePoint::generator();
        assert_eq!(g.scalar_mul(&U256::from(1u32)), g);
    }

    #[test]
    fn test_scalar_mul_two() {
        let g = AffinePoint::generator();
        assert_eq!(g.scalar_mul(&U256::from(2u32)), g.double());
    }

    #[test]
    fn test_scalar_mul_three() {
        let g = AffinePoint::generator();
        assert_eq!(g.scalar_mul(&U256::from(3u32)), g.add(&g.double()));
    }

    #[test]
    fn test_scalar_mul_order_minus_one() {
        // [n-1]G = -G  =>  same x, y = p - G.y
        let g = AffinePoint::generator();
        let result = g.scalar_mul(&ORDER.wrapping_sub(&U256::from(1u32)));
        assert_eq!(result.x, GX);
        assert_eq!(result.y, sub_mod(&MODULUS, &GY, &modp()));
    }
}
