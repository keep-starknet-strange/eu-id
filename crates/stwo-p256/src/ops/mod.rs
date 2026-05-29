use crate::limbs::{schoolbook_mul_raw, LimbsM31};
use crate::ops::consts::{LIMB_BITS, N_LIMBS};
use crate::witness::{AddModWitness, MulModWitness, SubModWitness};
use crypto_bigint::{CtEq, CtLt, Limb, NonZero, U256, U512, CtSelect};
use subtle::ConditionallySelectable;

pub mod affine_point;
pub mod consts;
pub mod glv;

/// Compute modular inverse: a^(-1) mod p.
pub fn mod_inverse(a: &U256, p: &NonZero<U256>) -> U256 {
    a.invert_mod(p).expect("No inverse exists")
}

/// Compute a * b mod modulus.
pub fn mul_mod(a: &U256, b: &U256, modulus: &NonZero<U256>) -> U256 {
    let modulus_512: NonZero<U512> = NonZero::new(modulus.as_ref().into()).unwrap();
    let (lo, hi) = a.widening_mul(b);
    let product: U512 = lo.concat(&hi);
    let (_, remainder) = product.div_rem(&modulus_512);
    let (r, _) = remainder.split();
    r
}

/// Compute (a + b) mod modulus.
pub fn add_mod(a: &U256, b: &U256, modulus: &NonZero<U256>) -> U256 {
    let (sum, overflow) = a.carrying_add(b, Limb::ZERO);
    let no_overflow = overflow.ct_eq(&Limb::ZERO);
    let sum_lt_modulus = sum.ct_lt(modulus.as_ref());
    let reduced = !(no_overflow & sum_lt_modulus.into());
    U256::conditional_select(&sum, &sum.wrapping_sub(modulus.as_ref()), reduced.into())
}

/// Compute (a - b) mod modulus.
pub fn sub_mod(a: &U256, b: &U256, modulus: &NonZero<U256>) -> U256 {
    let borrowed = a.ct_lt(b);
    U256::conditional_select(
        &a.wrapping_sub(b),
        &a.wrapping_add(modulus.as_ref()).wrapping_sub(b),
        borrowed.into(),
    )
}

/// Compute a * b mod modulus, producing all witness data.
pub fn mul_mod_witness(a: &U256, b: &U256, modulus: &NonZero<U256>) -> MulModWitness {
    let modulus_512: NonZero<U512> = NonZero::new(modulus.as_ref().into()).unwrap();

    let (product_low, product_high) = a.widening_mul(b);
    let product: U512 = product_low.concat(&product_high);
    let (quotient, remainder) = product.div_rem(&modulus_512);
    let (q, _) = quotient.split();
    let (r, _) = remainder.split();

    let a_limbs = LimbsM31::from_u256(a);
    let b_limbs = LimbsM31::from_u256(b);
    let m_limbs = LimbsM31::from_u256(modulus.as_ref());
    let r_limbs = LimbsM31::from_u256(&r);
    let q_limbs = LimbsM31::from_u256(&q);

    // Compute carries for the relation: a*b = q*m + r
    // Limb-by-limb: sum(a[j]*b[i-j]) = sum(q[j]*p[i-j]) + r[i] + carry[i]*2^LIMB_BITS - carry[i-1]
    let ab_raw = schoolbook_mul_raw(&a_limbs, &b_limbs);
    let qm_raw = schoolbook_mul_raw(&q_limbs, &m_limbs);

    let n_out = 2 * N_LIMBS;
    let mut carries = vec![0i64; n_out];
    let mut carry: i64 = 0;

    for i in 0..n_out {
        let ab_val = if i < ab_raw.len() {
            ab_raw[i] as i64
        } else {
            0
        };
        let qm_val = if i < qm_raw.len() {
            qm_raw[i] as i64
        } else {
            0
        };
        let r_val = if i < N_LIMBS {
            r_limbs.0[i].0 as i64
        } else {
            0
        };

        // ab = qp + r, so ab - qm - r should be 0 with carries
        let diff = ab_val - qm_val - r_val + carry;
        let limb_modulus = 1i64 << LIMB_BITS;
        carry = diff / limb_modulus;
        carries[i] = carry;
    }

    MulModWitness {
        a: a_limbs,
        b: b_limbs,
        modulus: m_limbs,
        result: r_limbs,
        quotient: q_limbs,
        carries,
    }
}

/// Compute (a + b) mod modulus, producing witness data.
pub fn add_mod_witness(a: &U256, b: &U256, modulus: &NonZero<U256>) -> AddModWitness {
    let (sum, overflow): (U256, Limb) = a.carrying_add(b, Limb::ZERO);
    let no_overflow = overflow.ct_eq(&Limb::ZERO);
    let sum_lt_modulus = sum.ct_lt(modulus.as_ref());
    let reduced = !(no_overflow & sum_lt_modulus.into());
    let result: U256 = U256::conditional_select(&sum, &sum.wrapping_sub(modulus.as_ref()), reduced.into());
    let reduced = u8::from(reduced) as u32;

    let a_limbs = LimbsM31::from_u256(a);
    let b_limbs = LimbsM31::from_u256(b);
    let m_limbs = LimbsM31::from_u256(modulus.as_ref());
    let r_limbs = LimbsM31::from_u256(&result);

    // Carry computation for: a + b - reduced*m - r = 0
    let mut carries = vec![0i64; N_LIMBS + 1];
    let mut carry: i64 = 0;
    for (i, carry_slot) in carries.iter_mut().enumerate() {
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
        let m_val = if i < N_LIMBS {
            m_limbs.0[i].0 as i64
        } else {
            0
        };
        let r_val = if i < N_LIMBS {
            r_limbs.0[i].0 as i64
        } else {
            0
        };

        let diff = a_val + b_val - (reduced as i64) * m_val - r_val + carry;
        let limb_modulus = 1i64 << LIMB_BITS;
        carry = diff / limb_modulus;
        *carry_slot = carry;
    }

    AddModWitness {
        a: a_limbs,
        b: b_limbs,
        modulus: m_limbs,
        result: r_limbs,
        reduced: reduced as u32,
        carries,
    }
}

/// Compute (a - b) mod modulus, producing witness data.
pub fn sub_mod_witness(a: &U256, b: &U256, modulus: &NonZero<U256>) -> SubModWitness {
    let borrowed = a.ct_lt(b);
    let result: U256 = U256::conditional_select(
        &a.wrapping_sub(b), // if a >= b => a - b
        &a.wrapping_add(modulus.as_ref()).wrapping_sub(b), // if a < b => a + modulus - b
        borrowed.into() // a < b
    );
    let borrowed = u8::from(borrowed) as u32;

    let a_limbs = LimbsM31::from_u256(a);
    let b_limbs = LimbsM31::from_u256(b);
    let m_limbs = LimbsM31::from_u256(modulus.as_ref());
    let r_limbs = LimbsM31::from_u256(&result);

    let mut carries = vec![0i64; N_LIMBS + 1];
    let mut carry: i64 = 0;
    for (i, carry_slot) in carries.iter_mut().enumerate() {
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
        let m_val = if i < N_LIMBS {
            m_limbs.0[i].0 as i64
        } else {
            0
        };
        let r_val = if i < N_LIMBS {
            r_limbs.0[i].0 as i64
        } else {
            0
        };

        let diff = a_val - b_val + (borrowed as i64) * m_val - r_val + carry;
        let limb_modulus = 1i64 << LIMB_BITS;
        carry = diff / limb_modulus;
        *carry_slot = carry;
    }

    SubModWitness {
        a: a_limbs,
        b: b_limbs,
        modulus: m_limbs,
        result: r_limbs,
        borrowed,
        carries,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::limbs::schoolbook_mul_raw;
    use crate::witness::{AddModWitness, MulModWitness, SubModWitness};

    fn u(n: u64) -> U256 {
        U256::from_u64(n)
    }

    fn nz(n: u64) -> NonZero<U256> {
        NonZero::new(u(n)).unwrap()
    }

    fn p256() -> NonZero<U256> {
        NonZero::new(consts::MODULUS).unwrap()
    }

    fn verify_mul_carries(w: &MulModWitness) {
        let ab_raw = schoolbook_mul_raw(&w.a, &w.b);
        let qm_raw = schoolbook_mul_raw(&w.quotient, &w.modulus);
        let limb_mod = 1i64 << LIMB_BITS;
        let mut carry: i64 = 0;
        for i in 0..2 * N_LIMBS {
            let ab_val = if i < ab_raw.len() { ab_raw[i] as i64 } else { 0 };
            let qm_val = if i < qm_raw.len() { qm_raw[i] as i64 } else { 0 };
            let r_val = if i < N_LIMBS { w.result.0[i].0 as i64 } else { 0 };
            let diff = ab_val - qm_val - r_val + carry;
            assert_eq!(diff % limb_mod, 0, "mul constraint not satisfied at limb {i}");
            carry = diff / limb_mod;
            assert_eq!(carry, w.carries[i], "mul carry mismatch at {i}");
        }
        assert_eq!(carry, 0, "mul final carry non-zero");
    }

    fn verify_add_carries(w: &AddModWitness) {
        let limb_mod = 1i64 << LIMB_BITS;
        let mut carry: i64 = 0;
        for i in 0..=N_LIMBS {
            let a_val = if i < N_LIMBS { w.a.0[i].0 as i64 } else { 0 };
            let b_val = if i < N_LIMBS { w.b.0[i].0 as i64 } else { 0 };
            let m_val = if i < N_LIMBS { w.modulus.0[i].0 as i64 } else { 0 };
            let r_val = if i < N_LIMBS { w.result.0[i].0 as i64 } else { 0 };
            let diff = a_val + b_val - (w.reduced as i64) * m_val - r_val + carry;
            assert_eq!(diff % limb_mod, 0, "add constraint not satisfied at limb {i}");
            carry = diff / limb_mod;
            assert_eq!(carry, w.carries[i], "add carry mismatch at {i}");
        }
        assert_eq!(carry, 0, "add final carry non-zero");
    }

    fn verify_sub_carries(w: &SubModWitness) {
        let limb_mod = 1i64 << LIMB_BITS;
        let mut carry: i64 = 0;
        for i in 0..=N_LIMBS {
            let a_val = if i < N_LIMBS { w.a.0[i].0 as i64 } else { 0 };
            let b_val = if i < N_LIMBS { w.b.0[i].0 as i64 } else { 0 };
            let m_val = if i < N_LIMBS { w.modulus.0[i].0 as i64 } else { 0 };
            let r_val = if i < N_LIMBS { w.result.0[i].0 as i64 } else { 0 };
            let diff = a_val - b_val + (w.borrowed as i64) * m_val - r_val + carry;
            assert_eq!(diff % limb_mod, 0, "sub constraint not satisfied at limb {i}");
            carry = diff / limb_mod;
            assert_eq!(carry, w.carries[i], "sub carry mismatch at {i}");
        }
        assert_eq!(carry, 0, "sub final carry non-zero");
    }

    // --- mul ---

    #[test]
    fn test_mul_no_reduction() {
        let w = mul_mod_witness(&u(7), &u(11), &nz(100));
        assert_eq!(w.result.to_u256(), u(77));
        verify_mul_carries(&w);
    }

    #[test]
    fn test_mul_with_reduction() {
        let w = mul_mod_witness(&u(13), &u(11), &nz(100));
        assert_eq!(w.result.to_u256(), u(43)); // 143 mod 100
        verify_mul_carries(&w);
    }

    #[test]
    fn test_mul_p256() {
        let w = mul_mod_witness(&u(0xDEAD_BEEF), &u(0xCAFE_BABE), &p256());
        let expected = (0xDEAD_BEEFu128 * 0xCAFE_BABEu128) as u64;
        assert_eq!(w.result.to_u256(), u(expected));
        verify_mul_carries(&w);
    }

    // --- add ---

    #[test]
    fn test_add_no_reduction() {
        let w = add_mod_witness(&u(30), &u(40), &nz(100));
        assert_eq!(w.result.to_u256(), u(70));
        assert_eq!(w.reduced, 0);
        verify_add_carries(&w);
    }

    #[test]
    fn test_add_sum_ge_modulus() {
        let w = add_mod_witness(&u(70), &u(50), &nz(100));
        assert_eq!(w.result.to_u256(), u(20)); // 120 mod 100
        assert_eq!(w.reduced, 1);
        verify_add_carries(&w);
    }

    #[test]
    fn test_add_overflow_carry() {
        // a + b overflows 256 bits, forcing reduction
        let p = p256();
        let a = consts::MODULUS.wrapping_sub(&u(1)); // p - 1
        let b = consts::MODULUS.wrapping_sub(&u(1)); // p - 1
        let w = add_mod_witness(&a, &b, &p);
        assert_eq!(w.result.to_u256(), consts::MODULUS.wrapping_sub(&u(2)));
        assert_eq!(w.reduced, 1);
        verify_add_carries(&w);
    }

    // --- plain mul ---

    #[test]
    fn test_plain_mul_no_reduction() {
        assert_eq!(mul_mod(&u(7), &u(11), &nz(100)), u(77));
    }

    #[test]
    fn test_plain_mul_with_reduction() {
        assert_eq!(mul_mod(&u(13), &u(11), &nz(100)), u(43)); // 143 mod 100
    }

    #[test]
    fn test_plain_mul_p256() {
        let expected = (0xDEAD_BEEFu128 * 0xCAFE_BABEu128) as u64;
        assert_eq!(mul_mod(&u(0xDEAD_BEEF), &u(0xCAFE_BABE), &p256()), u(expected));
    }

    // --- plain add ---

    #[test]
    fn test_plain_add_no_reduction() {
        assert_eq!(add_mod(&u(30), &u(40), &nz(100)), u(70));
    }

    #[test]
    fn test_plain_add_sum_ge_modulus() {
        assert_eq!(add_mod(&u(70), &u(50), &nz(100)), u(20)); // 120 mod 100
    }

    #[test]
    fn test_plain_add_overflow_carry() {
        let p = p256();
        let a = consts::MODULUS.wrapping_sub(&u(1)); // p - 1
        let b = consts::MODULUS.wrapping_sub(&u(1)); // p - 1
        assert_eq!(add_mod(&a, &b, &p), consts::MODULUS.wrapping_sub(&u(2)));
    }

    // --- plain sub ---

    #[test]
    fn test_plain_sub_no_borrow() {
        assert_eq!(sub_mod(&u(70), &u(40), &nz(100)), u(30));
    }

    #[test]
    fn test_plain_sub_with_borrow() {
        assert_eq!(sub_mod(&u(30), &u(50), &nz(100)), u(80)); // 30 - 50 + 100 = 80
    }

    #[test]
    fn test_plain_sub_p256_with_borrow() {
        assert_eq!(sub_mod(&u(5), &u(10), &p256()), consts::MODULUS.wrapping_sub(&u(5))); // p - 5
    }

    // --- sub ---

    #[test]
    fn test_sub_no_borrow() {
        let w = sub_mod_witness(&u(70), &u(40), &nz(100));
        assert_eq!(w.result.to_u256(), u(30));
        assert_eq!(w.borrowed, 0);
        verify_sub_carries(&w);
    }

    #[test]
    fn test_sub_with_borrow() {
        let w = sub_mod_witness(&u(30), &u(50), &nz(100));
        assert_eq!(w.result.to_u256(), u(80)); // 30 - 50 + 100 = 80
        assert_eq!(w.borrowed, 1);
        verify_sub_carries(&w);
    }

    #[test]
    fn test_sub_p256_with_borrow() {
        let w = sub_mod_witness(&u(5), &u(10), &p256());
        assert_eq!(w.result.to_u256(), consts::MODULUS.wrapping_sub(&u(5))); // p - 5
        assert_eq!(w.borrowed, 1);
        verify_sub_carries(&w);
    }
}
