use crypto_bigint::{NonZero, U256};

/// 2^128
const TWO_POW_128: U256 =
    U256::from_be_hex("0000000000000000000000000000000100000000000000000000000000000000");

/// Result of fake-GLV scalar decomposition.
///
/// Guarantees: `s1 + u * s2_signed ≡ 0 mod n`, `0 < s1, s2_abs < 2^128`.
/// `s2_signed = s2_abs` when `s2_sign_bit = false`, `s2_signed = -s2_abs` when `s2_sign_bit = true`.
#[derive(Clone, Debug)]
pub struct FakeGlvDecomposition {
    pub s1: U256,
    pub s2_abs: U256,
    pub s2_sign_bit: bool,
}

/// Decompose scalar `u` into a short pair `(s1, s2)` satisfying
/// `s1 + u * s2_signed ≡ 0 mod n`, with `s1, s2_abs < 2^128`.
///
/// Uses the extended Euclidean algorithm on `(n, u)`, stopping when the
/// remainder first drops below 2^128. At that point the remainder and its
/// Bezout coefficient are both < 2^128, giving the required short pair.
pub fn fake_glv_decompose(u: &U256, n: &NonZero<U256>) -> FakeGlvDecomposition {
    // Extended GCD: maintain (r, t) with u * t ≡ r (mod n).
    // r_0 = n, t_0 = 0
    // r_1 = u, t_1 = 1
    let mut r_prev = *n.as_ref();
    let mut r_curr = *u;
    let mut t_prev_abs = U256::ZERO;
    let mut t_prev_neg = false;
    let mut t_curr_abs = U256::ONE;
    let mut t_curr_neg = false;

    while r_curr >= TWO_POW_128 {
        let (q, r_next) = r_prev.div_rem_vartime::<4>(&NonZero::new(r_curr).unwrap());

        // t_next = t_prev - q * t_curr
        //
        // Overflow safety: while r_curr >= 2^128, both q and |t_curr| are < 2^128
        // (from the invariant |t_i| <= n / r_i and q = r_prev / r_curr <= n / 2^128),
        // so their product fits in U256.
        let (qt, hi) = q.widening_mul(&t_curr_abs);
        debug_assert!(bool::from(hi.is_zero()), "fake-GLV GCD: q * t overflow");

        let (t_next_abs, t_next_neg) = signed_sub(t_prev_abs, t_prev_neg, qt, t_curr_neg);

        r_prev = r_curr;
        r_curr = r_next;
        t_prev_abs = t_curr_abs;
        t_prev_neg = t_curr_neg;
        t_curr_abs = t_next_abs;
        t_curr_neg = t_next_neg;
    }

    // u * t_curr ≡ r_curr (mod n), so r_curr + u * (-t_curr) ≡ 0 (mod n).
    // s1 = r_curr, s2_signed = -t_curr.
    FakeGlvDecomposition {
        s1: r_curr,
        s2_abs: t_curr_abs,
        s2_sign_bit: !t_curr_neg, // negate t_curr to get s2_signed
    }
}

/// Compute `(a, a_neg) - (b, b_neg)` as a signed magnitude pair.
fn signed_sub(a_abs: U256, a_neg: bool, b_abs: U256, b_neg: bool) -> (U256, bool) {
    if a_neg == b_neg {
        // Same sign: subtract magnitudes.
        if a_abs >= b_abs {
            (a_abs.wrapping_sub(&b_abs), a_neg)
        } else {
            (b_abs.wrapping_sub(&a_abs), !a_neg)
        }
    } else {
        // Opposite signs: add magnitudes, keep sign of a.
        (a_abs.wrapping_add(&b_abs), a_neg)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ops::consts::ORDER;
    use crate::ops::{add_mod, mul_mod};

    fn n() -> NonZero<U256> {
        NonZero::new(ORDER).unwrap()
    }

    fn verify(u: &U256) {
        let n = n();
        let d = fake_glv_decompose(u, &n);

        assert!(d.s1 > U256::ZERO, "s1 must be positive");
        assert!(d.s1 < TWO_POW_128, "s1 must be < 2^128");
        assert!(d.s2_abs > U256::ZERO, "s2_abs must be positive");
        assert!(d.s2_abs < TWO_POW_128, "s2_abs must be < 2^128");

        // Verify s1 + u * s2_signed ≡ 0 mod n
        let s2_signed = if d.s2_sign_bit {
            // s2_signed = -s2_abs mod n
            ORDER.wrapping_sub(&d.s2_abs)
        } else {
            d.s2_abs
        };
        let result = add_mod(&d.s1, &mul_mod(u, &s2_signed, &n), &n);
        assert!(bool::from(result.is_zero()), "s1 + u * s2_signed must be 0 mod n");
    }

    #[test]
    fn test_decompose_one() {
        verify(&U256::ONE);
    }

    #[test]
    fn test_decompose_two() {
        verify(&U256::from(2u32));
    }

    #[test]
    fn test_decompose_large() {
        // Use a large scalar close to n
        verify(&ORDER.wrapping_sub(&U256::ONE));
    }

    #[test]
    fn test_decompose_random_looking() {
        // A fixed "random-looking" scalar
        let u = U256::from_be_hex(
            "a9fb57dba1eea9bc3e660a909d838d718c397aa3b561a6f7901e0e82974856a7",
        );
        verify(&u);
    }
}
