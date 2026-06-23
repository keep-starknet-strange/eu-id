use serde::{Deserialize, Serialize};
use stwo::core::fields::m31::M31;
use stwo_constraint_framework::EvalAtRow;
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};

#[cfg(test)]
use crate::constants::LIMB_MAX;
use crate::types::U256;

/// A P-256-sized integer decomposed into N_LIMBS limbs of LIMB_BITS each.
///
/// Limb 0 is the least significant.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct P256BigInt<F>(pub [F; N_LIMBS]);

/// A P-256 bigint whose limbs are values read by an AIR evaluator.
pub type P256EvalBigInt<E> = P256BigInt<<E as EvalAtRow>::F>;

/// A P-256 bigint whose limbs are concrete M31 values.
pub type P256M31BigInt = P256BigInt<M31>;

impl<F> P256BigInt<F> {
    pub const fn from_limbs(limbs: [F; N_LIMBS]) -> Self {
        Self(limbs)
    }

    pub fn into_limbs(self) -> [F; N_LIMBS] {
        self.0
    }

    pub const fn limbs(&self) -> &[F; N_LIMBS] {
        &self.0
    }

    pub fn limbs_mut(&mut self) -> &mut [F; N_LIMBS] {
        &mut self.0
    }

    pub fn map<G>(self, mut f: impl FnMut(F) -> G) -> P256BigInt<G> {
        P256BigInt(self.0.map(&mut f))
    }
}

pub trait EvalP256BigIntExt: EvalAtRow {
    fn next_p256_bigint(&mut self) -> P256EvalBigInt<Self> {
        P256BigInt(core::array::from_fn(|_| self.next_trace_mask()))
    }
}

impl<E: EvalAtRow> EvalP256BigIntExt for E {}

impl P256M31BigInt {
    pub const fn zero() -> Self {
        Self([M31::from_u32_unchecked(0); N_LIMBS])
    }

    /// Convert a U256 (big-endian bytes) into limbs of LIMB_BITS each (little-endian limb order).
    pub fn from_u256(val: &U256) -> Self {
        let mut limbs = [M31::from_u32_unchecked(0); N_LIMBS];
        let mut bit_pos = 0usize;

        for limb in &mut limbs {
            let mut limb_val = 0u32;
            for bit in 0..LIMB_BITS {
                if bit_pos + bit >= 256 {
                    break;
                }
                let global_bit = bit_pos + bit;
                let byte_idx = 31 - (global_bit / 8);
                let bit_in_byte = global_bit % 8;
                if (val.0[byte_idx] >> bit_in_byte) & 1 == 1 {
                    limb_val |= 1 << bit;
                }
            }
            *limb = M31::from_u32_unchecked(limb_val);
            bit_pos += LIMB_BITS;
        }

        Self(limbs)
    }

    /// Convert limbs back to a U256.
    pub fn to_u256(&self) -> U256 {
        let mut bytes = [0u8; 32];
        let mut bit_pos = 0usize;

        for limb in &self.0 {
            let limb_val = limb.0;
            for bit in 0..LIMB_BITS {
                if bit_pos + bit >= 256 {
                    break;
                }
                let global_bit = bit_pos + bit;
                let byte_idx = 31 - (global_bit / 8);
                let bit_in_byte = global_bit % 8;
                if (limb_val >> bit) & 1 == 1 {
                    bytes[byte_idx] |= 1 << bit_in_byte;
                }
            }
            bit_pos += LIMB_BITS;
        }

        U256(bytes)
    }
}

/// Schoolbook multiplication of two limbed numbers.
/// Returns the raw convolution (2*N_LIMBS - 1 limbs) as u64 values before reduction.
#[cfg(test)]
pub fn schoolbook_mul_raw(a: &P256M31BigInt, b: &P256M31BigInt) -> Vec<u64> {
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
#[cfg(test)]
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_u256_roundtrip() {
        let val = U256::from_le_u64s(&[
            0xDEAD_BEEF_CAFE_BABE,
            0x1234_5678_9ABC_DEF0,
            0xFFFF_FFFF_0000_0001,
            0x0000_0001_FFFF_FFFE,
        ]);
        let limbs = P256M31BigInt::from_u256(&val);
        let recovered = limbs.to_u256();
        assert_eq!(val, recovered);
    }

    #[test]
    fn test_zero_roundtrip() {
        let val = U256::ZERO;
        let limbs = P256M31BigInt::from_u256(&val);
        let recovered = limbs.to_u256();
        assert_eq!(val, recovered);
    }

    #[test]
    fn test_max_roundtrip() {
        let val = U256::from_le_u64s(&[u64::MAX, u64::MAX, u64::MAX, u64::MAX]);
        let limbs = P256M31BigInt::from_u256(&val);
        let recovered = limbs.to_u256();
        assert_eq!(val, recovered);
    }

    #[test]
    fn test_schoolbook_mul_small() {
        let a = U256::from_le_u64s(&[3, 0, 0, 0]);
        let b = U256::from_le_u64s(&[7, 0, 0, 0]);
        let la = P256M31BigInt::from_u256(&a);
        let lb = P256M31BigInt::from_u256(&b);
        let raw = schoolbook_mul_raw(&la, &lb);
        let (output, _carries) = propagate_carries(&raw, 2 * N_LIMBS);
        assert_eq!(output[0], 21);
        for value in output.iter().skip(1) {
            assert_eq!(*value, 0);
        }
    }

    #[test]
    fn test_limb_values_in_range() {
        let val = U256::from_le_u64s(&[u64::MAX, u64::MAX, u64::MAX, u64::MAX]);
        let limbs = P256M31BigInt::from_u256(&val);
        for limb in &limbs.0 {
            assert!(
                limb.0 <= LIMB_MAX,
                "Limb {} exceeds max {}",
                limb.0,
                LIMB_MAX
            );
        }
    }

    #[test]
    fn p256_bigint_helpers_preserve_limb_order() {
        let raw = core::array::from_fn(|i| M31::from_u32_unchecked(i as u32));
        let bigint = P256M31BigInt::from_limbs(raw);

        assert_eq!(bigint.limbs()[0], M31::from_u32_unchecked(0));
        assert_eq!(
            bigint.limbs()[N_LIMBS - 1],
            M31::from_u32_unchecked((N_LIMBS - 1) as u32)
        );
        assert_eq!(bigint.into_limbs(), raw);
    }

    #[test]
    fn p256_bigint_mutation_is_explicit() {
        let mut bigint = P256M31BigInt::zero();

        bigint.limbs_mut()[3] = M31::from_u32_unchecked(17);

        assert_eq!(bigint.limbs()[3], M31::from_u32_unchecked(17));
        assert_eq!(bigint.limbs()[2], M31::from_u32_unchecked(0));
    }

    #[test]
    fn p256_bigint_map_transforms_each_limb() {
        let raw = core::array::from_fn(|i| M31::from_u32_unchecked(i as u32));
        let mapped = P256M31BigInt::from_limbs(raw).map(|limb| limb.0 as u64);

        assert_eq!(mapped.limbs()[0], 0);
        assert_eq!(mapped.limbs()[7], 7);
        assert_eq!(mapped.limbs()[N_LIMBS - 1], (N_LIMBS - 1) as u64);
    }
}
