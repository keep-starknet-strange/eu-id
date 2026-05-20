use crate::constants::{LIMB_BITS, N_LIMBS};

use super::error::ScalarArithmeticError;
use super::types::{BigIntLimbs, U256Words};

const LIMB_BOUND: u32 = 1u32 << LIMB_BITS;

#[must_use]
pub fn words_to_limbs(value: &U256Words) -> BigIntLimbs {
    let mut limbs = [0u32; N_LIMBS];
    let mut bit_pos = 0usize;

    for limb in &mut limbs {
        let mut limb_value = 0u32;
        for bit in 0..LIMB_BITS {
            if bit_pos + bit >= 256 {
                break;
            }
            let global_bit = bit_pos + bit;
            let word_idx = global_bit / 64;
            let bit_in_word = global_bit % 64;
            if (value[word_idx] >> bit_in_word) & 1 == 1 {
                limb_value |= 1 << bit;
            }
        }
        *limb = limb_value;
        bit_pos += LIMB_BITS;
    }

    limbs
}

#[must_use]
pub fn limbs_to_words(limbs: &BigIntLimbs) -> U256Words {
    let mut words = [0u64; 4];
    let mut bit_pos = 0usize;

    for limb_value in limbs {
        for bit in 0..LIMB_BITS {
            if bit_pos + bit >= 256 {
                break;
            }
            if (limb_value >> bit) & 1 == 1 {
                let global_bit = bit_pos + bit;
                let word_idx = global_bit / 64;
                let bit_in_word = global_bit % 64;
                words[word_idx] |= 1u64 << bit_in_word;
            }
        }
        bit_pos += LIMB_BITS;
    }

    words
}

pub(super) fn check_limbs_range(
    value_name: &'static str,
    value: &BigIntLimbs,
) -> Result<(), ScalarArithmeticError> {
    for (limb, &value) in value.iter().enumerate() {
        if value >= LIMB_BOUND {
            return Err(ScalarArithmeticError::LimbOutOfRange {
                value_name,
                limb,
                value,
            });
        }
    }
    Ok(())
}

pub(super) fn limb_i64(value: &BigIntLimbs, limb: usize) -> i64 {
    i64::from(value[limb])
}

pub(super) fn result_limb_i64(result: &BigIntLimbs, limb: usize) -> i64 {
    result.get(limb).copied().map(i64::from).unwrap_or(0)
}

pub(super) fn is_zero_limbs(value: &BigIntLimbs) -> bool {
    value.iter().all(|&limb| limb == 0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn limbs_roundtrip_words() {
        let value = [
            0xdead_beef_cafe_babe,
            0x1234_5678_9abc_def0,
            0xffff_ffff_0000_0001,
            0x0000_0001_ffff_fffe,
        ];

        assert_eq!(limbs_to_words(&words_to_limbs(&value)), value);
    }
}
