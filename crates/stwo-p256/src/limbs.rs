use crate::ops::consts::{LIMB_BITS, N_LIMBS};
use crypto_bigint::{Encoding, U256};
use stwo::core::fields::m31::M31;

pub const LIMB_MAX: u32 = (1 << LIMB_BITS) - 1; // 8191

/// A 256-bit integer decomposed into N_LIMBS limbs of LIMB_BITS each, stored as M31 values.
/// Limb 0 is the least significant.
#[derive(Clone, Debug)]
pub struct LimbsM31(pub [M31; N_LIMBS]);

impl LimbsM31 {
    pub const fn zero() -> Self {
        Self([M31::from_u32_unchecked(0); N_LIMBS])
    }

    /// Convert a U256 into limbs of LIMB_BITS each (little-endian limb order).
    pub fn from_u256(val: &U256) -> Self {
        let bytes = val.to_le_bytes();
        let mut limbs = [M31::from_u32_unchecked(0); N_LIMBS];
        for (i, limb) in limbs.iter_mut().enumerate() {
            let bit_pos = i * LIMB_BITS;
            let mut limb_val = 0u32;
            for bit in 0..LIMB_BITS {
                let global_bit = bit_pos + bit;
                if global_bit >= 256 {
                    break;
                }
                if (bytes[global_bit / 8] >> (global_bit % 8)) & 1 == 1 {
                    limb_val |= 1 << bit;
                }
            }
            *limb = M31::from_u32_unchecked(limb_val);
        }
        Self(limbs)
    }

    /// Convert limbs back to a U256.
    pub fn to_u256(&self) -> U256 {
        let mut bytes = [0u8; 32];
        for (i, limb) in self.0.iter().enumerate() {
            let bit_pos = i * LIMB_BITS;
            for bit in 0..LIMB_BITS {
                let global_bit = bit_pos + bit;
                if global_bit >= 256 {
                    break;
                }
                if (limb.0 >> bit) & 1 == 1 {
                    bytes[global_bit / 8] |= 1 << (global_bit % 8);
                }
            }
        }
        U256::from_le_slice(&bytes)
    }
}

/// Schoolbook multiplication of two limbed numbers.
/// Returns the raw convolution (2*N_LIMBS - 1 limbs) as u64 values before reduction.
pub fn schoolbook_mul_raw(a: &LimbsM31, b: &LimbsM31) -> Vec<u64> {
    let n = N_LIMBS;
    let mut result = vec![0u64; 2 * n - 1];

    for i in 0..n {
        for j in 0..n {
            result[i + j] += (a.0[i].0 as u64) * (b.0[j].0 as u64);
        }
    }

    result
}

/// Propagate carries through a raw convolution, producing limbs with values in [0, LIMB_MAX].
/// Returns (output_limbs, carries) for constraint generation.
pub fn propagate_carries(raw: &[u64], n_output: usize) -> (Vec<u32>, Vec<u64>) {
    let mut output = vec![0u32; n_output];
    let mut carries = vec![0u64; n_output];
    let mut carry: u64 = 0;

    for i in 0..n_output {
        let val = if i < raw.len() { raw[i] } else { 0 } + carry;
        output[i] = (val & LIMB_MAX as u64) as u32;
        carry = val >> LIMB_BITS;
        carries[i] = carry;
    }

    (output, carries)
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//
//     #[test]
//     fn test_u256_roundtrip() {
//         let val = U256::from_le_u64s(&[
//             0xDEAD_BEEF_CAFE_BABE,
//             0x1234_5678_9ABC_DEF0,
//             0xFFFF_FFFF_0000_0001,
//             0x0000_0001_FFFF_FFFE,
//         ]);
//         let limbs = LimbsM31::from_u256(&val);
//         let recovered = limbs.to_u256();
//         assert_eq!(val, recovered);
//     }
//
//     #[test]
//     fn test_zero_roundtrip() {
//         let val = U256::ZERO;
//         let limbs = LimbsM31::from_u256(&val);
//         let recovered = limbs.to_u256();
//         assert_eq!(val, recovered);
//     }
//
//     #[test]
//     fn test_max_roundtrip() {
//         let val = U256::from_le_u64s(&[u64::MAX, u64::MAX, u64::MAX, u64::MAX]);
//         let limbs = LimbsM31::from_u256(&val);
//         let recovered = limbs.to_u256();
//         assert_eq!(val, recovered);
//     }
//
//     #[test]
//     fn test_schoolbook_mul_small() {
//         let a = U256::from_le_u64s(&[3, 0, 0, 0]);
//         let b = U256::from_le_u64s(&[7, 0, 0, 0]);
//         let la = LimbsM31::from_u256(&a);
//         let lb = LimbsM31::from_u256(&b);
//         let raw = schoolbook_mul_raw(&la, &lb);
//         let (output, _carries) = propagate_carries(&raw, 2 * N_LIMBS);
//         assert_eq!(output[0], 21);
//         for i in 1..output.len() {
//             assert_eq!(output[i], 0);
//         }
//     }
//
//     #[test]
//     fn test_limb_values_in_range() {
//         let val = U256::from_le_u64s(&[u64::MAX, u64::MAX, u64::MAX, u64::MAX]);
//         let limbs = LimbsM31::from_u256(&val);
//         for limb in &limbs.0 {
//             assert!(
//                 limb.0 <= LIMB_MAX,
//                 "Limb {} exceeds max {}",
//                 limb.0,
//                 LIMB_MAX
//             );
//         }
//     }
// }
