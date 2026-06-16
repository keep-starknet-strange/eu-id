use core::cmp::Ordering;

use super::types::U256Words;

pub(super) type U512 = [u64; 8];

pub(super) fn is_zero_words(value: &U256Words) -> bool {
    value.iter().all(|&word| word == 0)
}

pub(super) fn checked_sub_words(a: &U256Words, b: &U256Words) -> Option<U256Words> {
    if cmp_words(a, b) == Ordering::Less {
        return None;
    }

    let mut result = [0u64; 4];
    let mut borrow = 0u64;
    for (i, result_word) in result.iter_mut().enumerate() {
        let (first, first_borrow) = a[i].overflowing_sub(b[i]);
        let (second, second_borrow) = first.overflowing_sub(borrow);
        *result_word = second;
        borrow = u64::from(first_borrow) + u64::from(second_borrow);
    }
    debug_assert_eq!(borrow, 0);
    Some(result)
}

pub(super) fn sub_one_words(value: &U256Words) -> Option<U256Words> {
    checked_sub_words(value, &[1, 0, 0, 0])
}

pub(super) fn cmp_words(a: &U256Words, b: &U256Words) -> Ordering {
    for (&a_word, &b_word) in a.iter().zip(b).rev() {
        match a_word.cmp(&b_word) {
            Ordering::Equal => {}
            ordering => return ordering,
        }
    }
    Ordering::Equal
}

pub(super) fn words_to_512(value: &U256Words) -> U512 {
    [value[0], value[1], value[2], value[3], 0, 0, 0, 0]
}

pub(super) fn words_from_512_low(value: &U512) -> U256Words {
    [value[0], value[1], value[2], value[3]]
}

pub(super) fn sub_512(a: &U512, b: &U512) -> U512 {
    let mut result = [0u64; 8];
    let mut borrow = 0u64;
    for (i, result_word) in result.iter_mut().enumerate() {
        let (first, first_borrow) = a[i].overflowing_sub(b[i]);
        let (second, second_borrow) = first.overflowing_sub(borrow);
        *result_word = second;
        borrow = u64::from(first_borrow) + u64::from(second_borrow);
    }
    result
}

pub(super) fn cmp_512(a: &U512, b: &U512) -> Ordering {
    for (&a_word, &b_word) in a.iter().zip(b).rev() {
        match a_word.cmp(&b_word) {
            Ordering::Equal => {}
            ordering => return ordering,
        }
    }
    Ordering::Equal
}

pub(super) fn mul_512(a: &U512, b: &U512) -> U512 {
    let mut out = [0u64; 8];
    let mut carry = 0u128;
    for (k, out_limb) in out.iter_mut().enumerate() {
        let mut acc = carry;
        carry = 0;
        let j_start = k.saturating_sub(3);
        let j_end = if k < 4 { k + 1 } else { 4 };
        for (j, &b_limb) in b.iter().enumerate().take(j_end).skip(j_start) {
            let i = k - j;
            let product = u128::from(a[i]) * u128::from(b_limb);
            acc += product & 0xffff_ffff_ffff_ffff;
            carry += product >> 64;
        }
        carry += acc >> 64;
        *out_limb = acc as u64;
    }
    out
}

pub(super) fn divmod_512(a: &U512, b: &U512) -> (U512, U512) {
    debug_assert_ne!(cmp_512(b, &[0; 8]), Ordering::Equal);
    if cmp_512(a, b) == Ordering::Less {
        return ([0; 8], *a);
    }

    let a_bits = 512 - leading_zeros_512(a);
    let b_bits = 512 - leading_zeros_512(b);
    let mut quotient = [0u64; 8];
    let mut remainder = *a;

    for shift in (0..=(a_bits - b_bits)).rev() {
        let shifted = shl_512(b, shift);
        if cmp_512(&remainder, &shifted) != Ordering::Less {
            remainder = sub_512(&remainder, &shifted);
            quotient[shift / 64] |= 1u64 << (shift % 64);
        }
    }

    (quotient, remainder)
}

fn leading_zeros_512(value: &U512) -> usize {
    for (i, &word) in value.iter().enumerate().rev() {
        if word != 0 {
            return (7 - i) * 64 + word.leading_zeros() as usize;
        }
    }
    512
}

fn shl_512(value: &U512, shift: usize) -> U512 {
    if shift >= 512 {
        return [0; 8];
    }

    let word_shift = shift / 64;
    let bit_shift = shift % 64;
    let mut result = [0u64; 8];
    for i in word_shift..8 {
        result[i] = value[i - word_shift] << bit_shift;
        if bit_shift > 0 && i > word_shift {
            result[i] |= value[i - word_shift - 1] >> (64 - bit_shift);
        }
    }
    result
}
