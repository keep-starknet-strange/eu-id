//! Minimal fixed-width 512-bit unsigned integer helpers for the hinted-mul
//! witness builder (`a·b_half` reaches 2^390, beyond `U256`). Little-endian
//! `[u64; 8]` words; every operation asserts it cannot silently overflow.

/// Little-endian 512-bit unsigned integer.
pub type U512 = [u64; 8];

pub const U512_ZERO: U512 = [0u64; 8];

/// Builds a `U512` as `Σ limbs[i] · 2^(13·i)`. Limb values may exceed 13 bits
/// (used for un-normalized limb sums like `m1 + X^10·m2`); the accumulation is
/// exact. Panics if the value would exceed 512 bits.
pub fn u512_from_limbs13(limbs: &[u32]) -> U512 {
    let mut out = U512_ZERO;
    for (i, &limb) in limbs.iter().enumerate() {
        if limb == 0 {
            continue;
        }
        let bit_offset = 13 * i;
        let word = bit_offset / 64;
        let shift = bit_offset % 64;
        let wide = (limb as u128) << shift;
        add_word_at(&mut out, word, wide as u64);
        let high = (wide >> 64) as u64;
        if high != 0 {
            add_word_at(&mut out, word + 1, high);
        }
    }
    out
}

/// Decomposes into exactly `n` 13-bit limbs. Panics if the value needs more.
pub fn u512_to_limbs13(value: &U512, n: usize) -> Vec<u32> {
    let mut limbs = Vec::with_capacity(n);
    for i in 0..n {
        limbs.push((extract_bits(value, 13 * i) & 0x1FFF) as u32);
    }
    // Everything above the requested limbs must be zero.
    let used_bits = 13 * n;
    for bit in (used_bits..512).step_by(64) {
        let chunk_bits = (512 - bit).min(64);
        if extract_bits(value, bit) & mask(chunk_bits) != 0 {
            panic!("u512_to_limbs13: value does not fit in {n} limbs");
        }
    }
    limbs
}

/// Schoolbook 512-bit multiplication. Panics if the product exceeds 512 bits.
pub fn u512_mul(a: &U512, b: &U512) -> U512 {
    let mut acc = [0u128; 9];
    for i in 0..8 {
        if a[i] == 0 {
            continue;
        }
        for j in 0..8 {
            if b[j] == 0 {
                continue;
            }
            let k = i + j;
            assert!(k < 8, "u512_mul overflow: term at word {k}");
            let prod = (a[i] as u128) * (b[j] as u128);
            // Split the 128-bit product to keep the accumulator below 2^128.
            acc[k] += prod & u128::from(u64::MAX);
            acc[k + 1] += prod >> 64;
        }
    }
    let mut out = U512_ZERO;
    let mut carry: u128 = 0;
    for k in 0..8 {
        let total = acc[k] + carry;
        out[k] = total as u64;
        carry = total >> 64;
    }
    assert_eq!(carry + acc[8], 0, "u512_mul overflow past 512 bits");
    out
}

/// `a + b`, panicking on overflow past 512 bits.
pub fn u512_add(a: &U512, b: &U512) -> U512 {
    let mut out = U512_ZERO;
    let mut carry: u128 = 0;
    for i in 0..8 {
        let total = a[i] as u128 + b[i] as u128 + carry;
        out[i] = total as u64;
        carry = total >> 64;
    }
    assert_eq!(carry, 0, "u512_add overflow");
    out
}

/// `a - b`, panicking on underflow.
pub fn u512_sub(a: &U512, b: &U512) -> U512 {
    let mut out = U512_ZERO;
    let mut borrow: i128 = 0;
    for i in 0..8 {
        let diff = a[i] as i128 - b[i] as i128 - borrow;
        if diff < 0 {
            out[i] = (diff + (1i128 << 64)) as u64;
            borrow = 1;
        } else {
            out[i] = diff as u64;
            borrow = 0;
        }
    }
    assert_eq!(borrow, 0, "u512_sub underflow");
    out
}

pub fn u512_cmp(a: &U512, b: &U512) -> core::cmp::Ordering {
    for i in (0..8).rev() {
        match a[i].cmp(&b[i]) {
            core::cmp::Ordering::Equal => continue,
            other => return other,
        }
    }
    core::cmp::Ordering::Equal
}

pub fn u512_is_zero(a: &U512) -> bool {
    a.iter().all(|&w| w == 0)
}

/// Shift-subtract long division: `(n / d, n % d)`. Panics if `d == 0`.
pub fn u512_divmod(n: &U512, d: &U512) -> (U512, U512) {
    assert!(!u512_is_zero(d), "u512_divmod by zero");
    let mut quotient = U512_ZERO;
    let mut remainder = U512_ZERO;
    for bit in (0..512).rev() {
        // remainder = (remainder << 1) | n.bit(bit)
        let mut carry = (n[bit / 64] >> (bit % 64)) & 1;
        for word in remainder.iter_mut() {
            let new_carry = *word >> 63;
            *word = (*word << 1) | carry;
            carry = new_carry;
        }
        debug_assert_eq!(carry, 0, "remainder overflow during division");
        if u512_cmp(&remainder, d) != core::cmp::Ordering::Less {
            remainder = u512_sub(&remainder, d);
            quotient[bit / 64] |= 1 << (bit % 64);
        }
    }
    (quotient, remainder)
}

fn add_word_at(value: &mut U512, word: usize, addend: u64) {
    assert!(word < 8, "u512 accumulation overflow");
    let mut carry = addend as u128;
    let mut index = word;
    while carry != 0 {
        assert!(index < 8, "u512 accumulation overflow");
        let total = value[index] as u128 + carry;
        value[index] = total as u64;
        carry = total >> 64;
        index += 1;
    }
}

/// Extracts up to 64 bits starting at `bit_offset`.
fn extract_bits(value: &U512, bit_offset: usize) -> u64 {
    if bit_offset >= 512 {
        return 0;
    }
    let word = bit_offset / 64;
    let shift = bit_offset % 64;
    let mut out = value[word] >> shift;
    if shift != 0 && word + 1 < 8 {
        out |= value[word + 1] << (64 - shift);
    }
    out
}

fn mask(bits: usize) -> u64 {
    if bits >= 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn u512_from_u64(v: u64) -> U512 {
        let mut out = U512_ZERO;
        out[0] = v;
        out
    }

    #[test]
    fn limbs13_roundtrip() {
        let limbs: Vec<u32> = (0..20).map(|i| (i * 137 + 5) % 8192).collect();
        let value = u512_from_limbs13(&limbs);
        assert_eq!(u512_to_limbs13(&value, 20), limbs);
    }

    #[test]
    fn from_limbs13_accepts_unnormalized_limbs() {
        // 2 limbs worth of value expressed with one oversized limb:
        // [β + 3] == [3, 1] as normalized limbs.
        let value = u512_from_limbs13(&[8192 + 3]);
        assert_eq!(u512_to_limbs13(&value, 2), vec![3, 1]);
    }

    #[test]
    fn mul_and_divmod_agree_with_small_values() {
        let a = u512_from_u64(0xDEAD_BEEF_1234_5678);
        let b = u512_from_u64(0x1_0000_0001);
        let product = u512_mul(&a, &b);
        let (q, r) = u512_divmod(&product, &b);
        assert_eq!(q, a);
        assert!(u512_is_zero(&r));
    }

    #[test]
    fn divmod_returns_remainder() {
        let n = u512_from_u64(1000);
        let d = u512_from_u64(7);
        let (q, r) = u512_divmod(&n, &d);
        assert_eq!(q[0], 142);
        assert_eq!(r[0], 6);
        assert_eq!(
            u512_add(&u512_mul(&q, &d), &r),
            n,
            "q*d + r must reconstruct n"
        );
    }

    #[test]
    fn add_sub_roundtrip() {
        let a = u512_from_limbs13(&[5; 30]);
        let b = u512_from_limbs13(&[3; 25]);
        assert_eq!(u512_sub(&u512_add(&a, &b), &b), a);
    }

    #[test]
    #[should_panic(expected = "u512_to_limbs13")]
    fn to_limbs13_rejects_oversized_values() {
        let value = u512_from_limbs13(&[1; 25]);
        let _ = u512_to_limbs13(&value, 20);
    }
}
