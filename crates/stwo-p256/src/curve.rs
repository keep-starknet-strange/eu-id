use crate::constants::P256_MODULUS;

use crate::field_ops::{add_mod_witness, mul_mod_witness, sub_mod_witness};
use crate::types::{AffinePoint, U256};

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

fn modulus() -> U256 {
    U256::from_le_u64s(&P256_MODULUS)
}

/// Compute modular inverse: a^(-1) mod p using extended Euclidean algorithm.
/// Panics if a is zero.
pub fn mod_inverse(a: &U256, p: &U256) -> U256 {
    assert_ne!(*a, U256::ZERO, "cannot invert zero modulo modulus");

    let a_big = a.to_le_u64s();
    let p_big = p.to_le_u64s();

    // Extended GCD over 256-bit integers using signed arithmetic.
    // We use i512 representation via (sign, magnitude).
    let mut old_r = to_i512(&p_big);
    let mut r = to_i512(&a_big);
    let mut old_s = (false, [0u64; 8]); // 0
    let mut s = (false, [1, 0, 0, 0, 0, 0, 0, 0]); // 1

    while !is_zero_i512(&r) {
        let (q, _rem) = divmod_abs(&old_r.1, &r.1);
        let qr = mul_i512_abs(&q, &r.1);

        let new_r = sub_i512(&old_r, &(r.0, qr));
        old_r = r;
        r = new_r;

        let qs = mul_i512_abs(&q, &s.1);
        let new_s = sub_i512(&old_s, &(s.0 ^ false, qs));
        old_s = s;
        s = new_s;
    }

    // old_s is the inverse (mod p). Normalize to [0, p).
    if old_s.0 {
        // Negative: add p
        let neg_val = U256::from_le_u64s(&[old_s.1[0], old_s.1[1], old_s.1[2], old_s.1[3]]);
        sub_512_u256(p, &neg_val)
    } else {
        U256::from_le_u64s(&[old_s.1[0], old_s.1[1], old_s.1[2], old_s.1[3]])
    }
}

/// Double a point on P-256.
pub fn point_double(p: &AffinePoint) -> PointDoubleWitness {
    let modp = modulus();

    // lambda_num = 3*x1^2 + a, where a = p - 3
    let a_coeff = sub_512_u256(&modp, &U256::from_le_u64s(&[3, 0, 0, 0]));
    let x1_sq_w = mul_mod_witness(&p.x, &p.x, &modp);
    let x1_sq = x1_sq_w.result.to_u256();

    let three = U256::from_le_u64s(&[3, 0, 0, 0]);
    let three_x1_sq_w = mul_mod_witness(&three, &x1_sq, &modp);
    let three_x1_sq = three_x1_sq_w.result.to_u256();

    let lambda_num_w = add_mod_witness(&three_x1_sq, &a_coeff, &modp);
    let lambda_num = lambda_num_w.result.to_u256();

    // lambda_denom = 2*y1
    let two = U256::from_le_u64s(&[2, 0, 0, 0]);
    let lambda_denom_w = mul_mod_witness(&two, &p.y, &modp);
    let lambda_denom = lambda_denom_w.result.to_u256();

    // lambda = lambda_num / lambda_denom
    let denom_inv = mod_inverse(&lambda_denom, &modp);
    let lambda_w = mul_mod_witness(&lambda_num, &denom_inv, &modp);
    let lambda = lambda_w.result.to_u256();

    // x3 = lambda^2 - 2*x1
    let lam_sq_w = mul_mod_witness(&lambda, &lambda, &modp);
    let lam_sq = lam_sq_w.result.to_u256();
    let two_x1_w = mul_mod_witness(&two, &p.x, &modp);
    let two_x1 = two_x1_w.result.to_u256();
    let x3_w = sub_mod_witness(&lam_sq, &two_x1, &modp);
    let x3 = x3_w.result.to_u256();

    // y3 = lambda*(x1 - x3) - y1
    let x1_minus_x3_w = sub_mod_witness(&p.x, &x3, &modp);
    let x1_minus_x3 = x1_minus_x3_w.result.to_u256();
    let lam_diff_w = mul_mod_witness(&lambda, &x1_minus_x3, &modp);
    let lam_diff = lam_diff_w.result.to_u256();
    let y3_w = sub_mod_witness(&lam_diff, &p.y, &modp);
    let y3 = y3_w.result.to_u256();

    PointDoubleWitness {
        input: p.clone(),
        output: AffinePoint { x: x3, y: y3 },
        lambda,
        lambda_num,
        lambda_denom,
    }
}

/// Add two distinct points on P-256.
pub fn point_add(p: &AffinePoint, q: &AffinePoint) -> PointAddWitness {
    let modp = modulus();

    // lambda = (y2 - y1) / (x2 - x1)
    let dy_w = sub_mod_witness(&q.y, &p.y, &modp);
    let dy = dy_w.result.to_u256();
    let dx_w = sub_mod_witness(&q.x, &p.x, &modp);
    let dx = dx_w.result.to_u256();
    let dx_inv = mod_inverse(&dx, &modp);
    let lambda_w = mul_mod_witness(&dy, &dx_inv, &modp);
    let lambda = lambda_w.result.to_u256();

    // x3 = lambda^2 - x1 - x2
    let lam_sq_w = mul_mod_witness(&lambda, &lambda, &modp);
    let lam_sq = lam_sq_w.result.to_u256();
    let x_sum_w = add_mod_witness(&p.x, &q.x, &modp);
    let x_sum = x_sum_w.result.to_u256();
    let x3_w = sub_mod_witness(&lam_sq, &x_sum, &modp);
    let x3 = x3_w.result.to_u256();

    // y3 = lambda*(x1 - x3) - y1
    let x1_minus_x3_w = sub_mod_witness(&p.x, &x3, &modp);
    let x1_minus_x3 = x1_minus_x3_w.result.to_u256();
    let lam_diff_w = mul_mod_witness(&lambda, &x1_minus_x3, &modp);
    let lam_diff = lam_diff_w.result.to_u256();
    let y3_w = sub_mod_witness(&lam_diff, &p.y, &modp);
    let y3 = y3_w.result.to_u256();

    PointAddWitness {
        p: p.clone(),
        q: q.clone(),
        output: AffinePoint { x: x3, y: y3 },
        lambda,
    }
}

/// Scalar multiplication: k * P using double-and-add.
///
/// Returns `None` for the point at infinity, which occurs when `k = 0`.
pub fn scalar_mul(k: &U256, p: &AffinePoint) -> Option<AffinePoint> {
    let k_bits = u256_to_bits(k);

    let first_one = k_bits.iter().rposition(|&b| b)?;

    let mut acc = p.clone();
    for i in (0..first_one).rev() {
        let dbl = point_double(&acc);
        acc = dbl.output;
        if k_bits[i] {
            let add = point_add(&acc, p);
            acc = add.output;
        }
    }

    Some(acc)
}

fn u256_to_bits(val: &U256) -> Vec<bool> {
    let le = val.to_le_u64s();
    let mut bits = Vec::with_capacity(256);
    for limb in &le {
        for bit in 0..64 {
            bits.push((limb >> bit) & 1 == 1);
        }
    }
    bits
}

// --- Internal helpers ---

type I512 = (bool, [u64; 8]); // (negative, magnitude)

fn to_i512(a: &[u64; 4]) -> I512 {
    (false, [a[0], a[1], a[2], a[3], 0, 0, 0, 0])
}

fn is_zero_i512(a: &I512) -> bool {
    a.1.iter().all(|&x| x == 0)
}

fn sub_i512(a: &I512, b: &I512) -> I512 {
    if a.0 == b.0 {
        let cmp = cmp_abs(&a.1, &b.1);
        if cmp >= 0 {
            (a.0, sub_abs(&a.1, &b.1))
        } else {
            (!a.0, sub_abs(&b.1, &a.1))
        }
    } else {
        (a.0, add_abs(&a.1, &b.1))
    }
}

fn cmp_abs(a: &[u64; 8], b: &[u64; 8]) -> i32 {
    for i in (0..8).rev() {
        if a[i] > b[i] {
            return 1;
        }
        if a[i] < b[i] {
            return -1;
        }
    }
    0
}

fn add_abs(a: &[u64; 8], b: &[u64; 8]) -> [u64; 8] {
    let mut result = [0u64; 8];
    let mut carry = 0u64;
    for i in 0..8 {
        let (s1, c1) = a[i].overflowing_add(b[i]);
        let (s2, c2) = s1.overflowing_add(carry);
        result[i] = s2;
        carry = (c1 as u64) + (c2 as u64);
    }
    result
}

fn sub_abs(a: &[u64; 8], b: &[u64; 8]) -> [u64; 8] {
    let mut result = [0u64; 8];
    let mut borrow = 0u64;
    for i in 0..8 {
        let (s1, c1) = a[i].overflowing_sub(b[i]);
        let (s2, c2) = s1.overflowing_sub(borrow);
        result[i] = s2;
        borrow = (c1 as u64) + (c2 as u64);
    }
    result
}

fn mul_i512_abs(a: &[u64; 8], b: &[u64; 8]) -> [u64; 8] {
    let mut result = [0u128; 8];
    for i in 0..8 {
        if a[i] == 0 {
            continue;
        }
        for j in 0..8 {
            if i + j >= 8 {
                break;
            }
            result[i + j] += (a[i] as u128) * (b[j] as u128);
        }
    }
    let mut out = [0u64; 8];
    let mut carry = 0u128;
    for i in 0..8 {
        let val = result[i] + carry;
        out[i] = val as u64;
        carry = val >> 64;
    }
    out
}

fn divmod_abs(a: &[u64; 8], b: &[u64; 8]) -> ([u64; 8], [u64; 8]) {
    if b.iter().all(|&x| x == 0) {
        panic!("division by zero");
    }
    if cmp_abs(a, b) < 0 {
        return ([0; 8], *a);
    }

    let a_bits = 512 - leading_zeros(a);
    let b_bits = 512 - leading_zeros(b);

    let mut quotient = [0u64; 8];
    let mut remainder = *a;

    for shift in (0..=(a_bits.saturating_sub(b_bits))).rev() {
        let shifted = shl(b, shift);
        if cmp_abs(&remainder, &shifted) >= 0 {
            remainder = sub_abs(&remainder, &shifted);
            let word = shift / 64;
            let bit = shift % 64;
            quotient[word] |= 1u64 << bit;
        }
    }

    (quotient, remainder)
}

fn leading_zeros(a: &[u64; 8]) -> usize {
    for i in (0..8).rev() {
        if a[i] != 0 {
            return (7 - i) * 64 + a[i].leading_zeros() as usize;
        }
    }
    512
}

fn shl(a: &[u64; 8], shift: usize) -> [u64; 8] {
    if shift >= 512 {
        return [0; 8];
    }
    let word_shift = shift / 64;
    let bit_shift = shift % 64;
    let mut result = [0u64; 8];
    for i in word_shift..8 {
        result[i] = a[i - word_shift] << bit_shift;
        if bit_shift > 0 && i > word_shift {
            result[i] |= a[i - word_shift - 1] >> (64 - bit_shift);
        }
    }
    result
}

fn sub_512_u256(a: &U256, b: &U256) -> U256 {
    let a_le = a.to_le_u64s();
    let b_le = b.to_le_u64s();
    let mut result = [0u64; 4];
    let mut borrow = 0u64;
    for i in 0..4 {
        let (s1, c1) = a_le[i].overflowing_sub(b_le[i]);
        let (s2, c2) = s1.overflowing_sub(borrow);
        result[i] = s2;
        borrow = (c1 as u64) + (c2 as u64);
    }
    U256::from_le_u64s(&result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY};

    fn gen_point() -> AffinePoint {
        AffinePoint {
            x: U256::from_le_u64s(&P256_GX),
            y: U256::from_le_u64s(&P256_GY),
        }
    }

    #[test]
    fn test_point_on_curve() {
        let g = gen_point();
        let p = modulus();
        // Check y^2 = x^3 + ax + b mod p
        let y2 = mul_mod_witness(&g.y, &g.y, &p).result.to_u256();
        let x2 = mul_mod_witness(&g.x, &g.x, &p).result.to_u256();
        let x3 = mul_mod_witness(&x2, &g.x, &p).result.to_u256();
        let a = sub_512_u256(&p, &U256::from_le_u64s(&[3, 0, 0, 0]));
        let ax = mul_mod_witness(&a, &g.x, &p).result.to_u256();
        let b = U256::from_le_u64s(&[
            0x3BCE_3C3E_27D2_604B,
            0x651D_06B0_CC53_B0F6,
            0xB3EB_BD55_7698_86BC,
            0x5AC6_35D8_AA3A_93E7,
        ]);
        let rhs1 = add_mod_witness(&x3, &ax, &p).result.to_u256();
        let rhs = add_mod_witness(&rhs1, &b, &p).result.to_u256();
        assert_eq!(y2, rhs, "Generator point must satisfy curve equation");
    }

    #[test]
    fn test_point_double() {
        let g = gen_point();
        let w = point_double(&g);
        let p = modulus();

        // Verify 2G is on the curve
        let y2 = mul_mod_witness(&w.output.y, &w.output.y, &p)
            .result
            .to_u256();
        let x2 = mul_mod_witness(&w.output.x, &w.output.x, &p)
            .result
            .to_u256();
        let x3 = mul_mod_witness(&x2, &w.output.x, &p).result.to_u256();
        let a = sub_512_u256(&p, &U256::from_le_u64s(&[3, 0, 0, 0]));
        let ax = mul_mod_witness(&a, &w.output.x, &p).result.to_u256();
        let b = U256::from_le_u64s(&[
            0x3BCE_3C3E_27D2_604B,
            0x651D_06B0_CC53_B0F6,
            0xB3EB_BD55_7698_86BC,
            0x5AC6_35D8_AA3A_93E7,
        ]);
        let rhs1 = add_mod_witness(&x3, &ax, &p).result.to_u256();
        let rhs = add_mod_witness(&rhs1, &b, &p).result.to_u256();
        assert_eq!(y2, rhs, "2G must satisfy curve equation");
    }

    #[test]
    fn test_point_add() {
        let g = gen_point();
        let g2 = point_double(&g).output;
        let w = point_add(&g, &g2);
        let p = modulus();

        // Verify 3G is on the curve
        let y2 = mul_mod_witness(&w.output.y, &w.output.y, &p)
            .result
            .to_u256();
        let x2 = mul_mod_witness(&w.output.x, &w.output.x, &p)
            .result
            .to_u256();
        let x3 = mul_mod_witness(&x2, &w.output.x, &p).result.to_u256();
        let a = sub_512_u256(&p, &U256::from_le_u64s(&[3, 0, 0, 0]));
        let ax = mul_mod_witness(&a, &w.output.x, &p).result.to_u256();
        let b = U256::from_le_u64s(&[
            0x3BCE_3C3E_27D2_604B,
            0x651D_06B0_CC53_B0F6,
            0xB3EB_BD55_7698_86BC,
            0x5AC6_35D8_AA3A_93E7,
        ]);
        let rhs1 = add_mod_witness(&x3, &ax, &p).result.to_u256();
        let rhs = add_mod_witness(&rhs1, &b, &p).result.to_u256();
        assert_eq!(y2, rhs, "3G must satisfy curve equation");
    }

    #[test]
    fn test_mod_inverse() {
        let a = U256::from_le_u64s(&[7, 0, 0, 0]);
        let p = U256::from_le_u64s(&[101, 0, 0, 0]);
        let inv = mod_inverse(&a, &p);
        let product = mul_mod_witness(&a, &inv, &p).result.to_u256();
        assert_eq!(product, U256::from_le_u64s(&[1, 0, 0, 0]));
    }
}
