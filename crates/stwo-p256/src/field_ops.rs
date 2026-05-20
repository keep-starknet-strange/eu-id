use stwo::core::fields::m31::M31;
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};
use stwo_p256_utils::scalar_arithmetic::{BigIntLimbs, FnMulTrace};

use crate::limbs::P256M31BigInt;
use crate::types::U256;

/// Result of a modular multiplication, with all intermediate witness values
/// needed for trace generation and constraint verification.
#[derive(Clone, Debug)]
pub struct MulModWitness {
    pub a: P256M31BigInt,
    pub b: P256M31BigInt,
    pub modulus: P256M31BigInt,
    pub result: P256M31BigInt,
    pub quotient: P256M31BigInt,
    /// Carries from the verification equation: a*b - q*p - r = 0 (limb by limb with carries)
    pub carries: Vec<i64>,
}

/// Result of a modular addition.
#[derive(Clone, Debug)]
pub struct AddModWitness {
    pub a: P256M31BigInt,
    pub b: P256M31BigInt,
    pub modulus: P256M31BigInt,
    pub result: P256M31BigInt,
    /// Whether a borrow/reduction was needed (0 or 1).
    pub reduced: u32,
    pub carries: Vec<i64>,
}

/// Result of a modular subtraction.
#[derive(Clone, Debug)]
pub struct SubModWitness {
    pub a: P256M31BigInt,
    pub b: P256M31BigInt,
    pub modulus: P256M31BigInt,
    pub result: P256M31BigInt,
    /// Whether a borrow was needed (0 or 1).
    pub borrowed: u32,
    pub carries: Vec<i64>,
}

/// Compute a * b mod modulus, producing all witness data.
pub fn mul_mod_witness(a: &U256, b: &U256, modulus: &U256) -> MulModWitness {
    let trace = FnMulTrace::new(&a.to_le_u64s(), &b.to_le_u64s(), &modulus.to_le_u64s())
        .expect("modular multiplication modulus must be nonzero");

    MulModWitness {
        a: m31_limbs(&trace.a),
        b: m31_limbs(&trace.b),
        modulus: m31_limbs(&trace.modulus),
        result: m31_limbs(&trace.result),
        quotient: m31_limbs(&trace.quotient),
        carries: trace.carries.to_vec(),
    }
}

fn m31_limbs(limbs: &BigIntLimbs) -> P256M31BigInt {
    P256M31BigInt::from_limbs(limbs.map(M31::from_u32_unchecked))
}

/// Compute (a + b) mod modulus, producing witness data.
pub fn add_mod_witness(a: &U256, b: &U256, modulus: &U256) -> AddModWitness {
    let a_big = u256_to_u512(a);
    let b_big = u256_to_u512(b);
    let p_big = u256_to_u512(modulus);

    let sum = add_512(&a_big, &b_big);
    let reduced = cmp_512(&sum, &p_big) >= 0;
    let result_big = if reduced { sub_512(&sum, &p_big) } else { sum };

    let a_limbs = P256M31BigInt::from_u256(a);
    let b_limbs = P256M31BigInt::from_u256(b);
    let p_limbs = P256M31BigInt::from_u256(modulus);
    let result = u512_to_u256_low(&result_big);
    let r_limbs = P256M31BigInt::from_u256(&result);

    // Carry computation for: a + b - reduced*p - r = 0
    let mut carries = vec![0i64; N_LIMBS + 1];
    let mut carry: i64 = 0;
    for i in 0..=N_LIMBS {
        let a_val = if i < N_LIMBS {
            a_limbs.0[i].0 as i64
        } else {
            0
        };
        let b_val = if i < N_LIMBS {
            b_limbs.0[i].0 as i64
        } else {
            0
        };
        let p_val = if i < N_LIMBS {
            p_limbs.0[i].0 as i64
        } else {
            0
        };
        let r_val = if i < N_LIMBS {
            r_limbs.0[i].0 as i64
        } else {
            0
        };

        let diff = a_val + b_val - (reduced as i64) * p_val - r_val + carry;
        let limb_modulus = 1i64 << LIMB_BITS;
        carry = diff / limb_modulus;
        *carry_slot = carry;
    }

    AddModWitness {
        a: a_limbs,
        b: b_limbs,
        modulus: p_limbs,
        result: r_limbs,
        reduced: reduced as u32,
        carries,
    }
}

/// Compute (a - b) mod modulus, producing witness data.
pub fn sub_mod_witness(a: &U256, b: &U256, modulus: &U256) -> SubModWitness {
    let a_big = u256_to_u512(a);
    let b_big = u256_to_u512(b);
    let p_big = u256_to_u512(modulus);

    let borrowed = cmp_512(&a_big, &b_big) < 0;
    let result_big = if borrowed {
        let a_plus_p = add_512(&a_big, &p_big);
        sub_512(&a_plus_p, &b_big)
    } else {
        sub_512(&a_big, &b_big)
    };

    let a_limbs = P256M31BigInt::from_u256(a);
    let b_limbs = P256M31BigInt::from_u256(b);
    let p_limbs = P256M31BigInt::from_u256(modulus);
    let result = u512_to_u256_low(&result_big);
    let r_limbs = P256M31BigInt::from_u256(&result);

    let mut carries = vec![0i64; N_LIMBS + 1];
    let mut carry: i64 = 0;
    for i in 0..=N_LIMBS {
        let a_val = if i < N_LIMBS {
            a_limbs.0[i].0 as i64
        } else {
            0
        };
        let b_val = if i < N_LIMBS {
            b_limbs.0[i].0 as i64
        } else {
            0
        };
        let p_val = if i < N_LIMBS {
            p_limbs.0[i].0 as i64
        } else {
            0
        };
        let r_val = if i < N_LIMBS {
            r_limbs.0[i].0 as i64
        } else {
            0
        };

        let diff = a_val - b_val + (borrowed as i64) * p_val - r_val + carry;
        let limb_modulus = 1i64 << LIMB_BITS;
        carry = diff / limb_modulus;
        *carry_slot = carry;
    }

    SubModWitness {
        a: a_limbs,
        b: b_limbs,
        modulus: p_limbs,
        result: r_limbs,
        borrowed: borrowed as u32,
        carries,
    }
}

// --- 512-bit big integer helpers (internal) ---

type U512 = [u64; 8];

fn u256_to_u512(a: &U256) -> U512 {
    let le = a.to_le_u64s();
    [le[0], le[1], le[2], le[3], 0, 0, 0, 0]
}

fn u512_to_u256_low(a: &U512) -> U256 {
    U256::from_le_u64s(&[a[0], a[1], a[2], a[3]])
}

fn add_512(a: &U512, b: &U512) -> U512 {
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

fn sub_512(a: &U512, b: &U512) -> U512 {
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

fn cmp_512(a: &U512, b: &U512) -> i32 {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::P256_MODULUS;

    #[test]
    fn test_mul_mod_small() {
        let a = U256::from_le_u64s(&[7, 0, 0, 0]);
        let b = U256::from_le_u64s(&[11, 0, 0, 0]);
        let p = U256::from_le_u64s(&[100, 0, 0, 0]);
        let w = mul_mod_witness(&a, &b, &p);
        let result = w.result.to_u256();
        // 7 * 11 = 77, 77 mod 100 = 77
        assert_eq!(result, U256::from_le_u64s(&[77, 0, 0, 0]));
    }

    #[test]
    fn test_mul_mod_with_reduction() {
        let a = U256::from_le_u64s(&[13, 0, 0, 0]);
        let b = U256::from_le_u64s(&[11, 0, 0, 0]);
        let p = U256::from_le_u64s(&[100, 0, 0, 0]);
        let w = mul_mod_witness(&a, &b, &p);
        let result = w.result.to_u256();
        // 13 * 11 = 143, 143 mod 100 = 43
        assert_eq!(result, U256::from_le_u64s(&[43, 0, 0, 0]));
    }

    #[test]
    fn test_mul_mod_p256() {
        let a = U256::from_le_u64s(&[0xDEAD_BEEF, 0, 0, 0]);
        let b = U256::from_le_u64s(&[0xCAFE_BABE, 0, 0, 0]);
        let p = U256::from_le_u64s(&P256_MODULUS);
        let w = mul_mod_witness(&a, &b, &p);
        // Result should be (0xDEADBEEF * 0xCAFEBABE) mod p
        let expected = (0xDEAD_BEEFu128 * 0xCAFE_BABEu128) % P256_MODULUS[0] as u128;
        let result = w.result.to_u256().to_le_u64s();
        assert_eq!(result[0], expected as u64);
    }

    #[test]
    fn test_add_mod() {
        let a = U256::from_le_u64s(&[70, 0, 0, 0]);
        let b = U256::from_le_u64s(&[50, 0, 0, 0]);
        let p = U256::from_le_u64s(&[100, 0, 0, 0]);
        let w = add_mod_witness(&a, &b, &p);
        let result = w.result.to_u256();
        assert_eq!(result, U256::from_le_u64s(&[20, 0, 0, 0]));
        assert_eq!(w.reduced, 1);
    }

    #[test]
    fn test_sub_mod() {
        let a = U256::from_le_u64s(&[30, 0, 0, 0]);
        let b = U256::from_le_u64s(&[50, 0, 0, 0]);
        let p = U256::from_le_u64s(&[100, 0, 0, 0]);
        let w = sub_mod_witness(&a, &b, &p);
        let result = w.result.to_u256();
        // 30 - 50 mod 100 = 80
        assert_eq!(result, U256::from_le_u64s(&[80, 0, 0, 0]));
        assert_eq!(w.borrowed, 1);
    }
}
