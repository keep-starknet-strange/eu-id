use crate::constants::{LIMB_BITS, N_LIMBS};

use super::carries::verify_product_equation;
use super::error::ScalarArithmeticError;
use super::limbs::{check_limbs_range, result_limb_i64};
use super::mul::FnMulTrace;
use super::types::{BigIntLimbs, ProductCarries};

pub const FNMUL_CHUNK_TERMS: usize = 2;
pub const PRODUCT_COEFFICIENTS: usize = 2 * N_LIMBS - 1;
pub const PRODUCT_CHUNKS: usize = N_LIMBS * (N_LIMBS + 1) / 2;
pub const CHUNK_DIGITS: usize = 3;
pub const CHUNK_TOP_DIGIT_MAX: u32 = 1;

const LIMB_RADIX: u64 = 1u64 << LIMB_BITS;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProductChunk {
    pub coeff: usize,
    pub chunk: usize,
    pub terms: usize,
    pub digits: [u32; CHUNK_DIGITS],
}

impl ProductChunk {
    fn new(coeff: usize, chunk: usize, terms: &[u64]) -> Self {
        debug_assert!(!terms.is_empty());
        debug_assert!(terms.len() <= FNMUL_CHUNK_TERMS);

        let value = terms.iter().sum::<u64>();
        let d0 = value % LIMB_RADIX;
        let d1 = (value / LIMB_RADIX) % LIMB_RADIX;
        let d2 = value / (LIMB_RADIX * LIMB_RADIX);
        debug_assert!(d2 <= u64::from(CHUNK_TOP_DIGIT_MAX));

        Self {
            coeff,
            chunk,
            terms: terms.len(),
            digits: [d0 as u32, d1 as u32, d2 as u32],
        }
    }

    pub fn value(&self) -> u64 {
        u64::from(self.digits[0])
            + LIMB_RADIX * u64::from(self.digits[1])
            + LIMB_RADIX * LIMB_RADIX * u64::from(self.digits[2])
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SplitProductTrace {
    pub ab_chunks: Vec<ProductChunk>,
    pub qn_chunks: Vec<ProductChunk>,
    pub carries: ProductCarries,
}

impl SplitProductTrace {
    pub fn new(mul: &FnMulTrace) -> Self {
        Self {
            ab_chunks: split_product_chunks(&mul.a, &mul.b),
            qn_chunks: split_product_chunks(&mul.quotient, &mul.modulus),
            carries: mul.carries,
        }
    }

    pub fn verify(
        &self,
        equation: &'static str,
        mul: &FnMulTrace,
    ) -> Result<(), ScalarArithmeticError> {
        check_limbs_range("split_mul_a", &mul.a)?;
        check_limbs_range("split_mul_b", &mul.b)?;
        check_limbs_range("split_mul_modulus", &mul.modulus)?;
        check_limbs_range("split_mul_result", &mul.result)?;
        check_limbs_range("split_mul_quotient", &mul.quotient)?;

        verify_chunks(equation, "ab", &self.ab_chunks, &mul.a, &mul.b)?;
        verify_chunks(equation, "qn", &self.qn_chunks, &mul.quotient, &mul.modulus)?;

        verify_product_equation(equation, &self.carries, |limb, carry_in| {
            split_digit_i64(&self.ab_chunks, limb)
                - split_digit_i64(&self.qn_chunks, limb)
                - result_limb_i64(&mul.result, limb)
                + carry_in
        })
    }
}

fn split_product_chunks(a: &BigIntLimbs, b: &BigIntLimbs) -> Vec<ProductChunk> {
    let mut chunks = Vec::with_capacity(PRODUCT_CHUNKS);
    for coeff in 0..PRODUCT_COEFFICIENTS {
        let mut terms = Vec::with_capacity(FNMUL_CHUNK_TERMS);
        let mut chunk = 0usize;
        for (i, j) in coefficient_pairs(coeff) {
            terms.push(u64::from(a[i]) * u64::from(b[j]));
            if terms.len() == FNMUL_CHUNK_TERMS {
                chunks.push(ProductChunk::new(coeff, chunk, &terms));
                terms.clear();
                chunk += 1;
            }
        }
        if !terms.is_empty() {
            chunks.push(ProductChunk::new(coeff, chunk, &terms));
        }
    }
    debug_assert_eq!(chunks.len(), PRODUCT_CHUNKS);
    chunks
}

fn verify_chunks(
    equation: &'static str,
    label: &'static str,
    chunks: &[ProductChunk],
    a: &BigIntLimbs,
    b: &BigIntLimbs,
) -> Result<(), ScalarArithmeticError> {
    if chunks.len() != PRODUCT_CHUNKS {
        return Err(ScalarArithmeticError::TraceMismatch { value_name: label });
    }

    let expected = split_product_chunks(a, b);
    for (actual, expected) in chunks.iter().zip(expected) {
        if actual != &expected {
            return Err(ScalarArithmeticError::ProductChunkMismatch {
                equation,
                coeff: expected.coeff,
                chunk: expected.chunk,
                expected: expected.value(),
                actual: actual.value(),
            });
        }
    }
    Ok(())
}

fn split_digit_i64(chunks: &[ProductChunk], digit: usize) -> i64 {
    chunks
        .iter()
        .map(|chunk| chunk_digit_contribution(chunk, digit))
        .sum::<u64>() as i64
}

fn chunk_digit_contribution(chunk: &ProductChunk, digit: usize) -> u64 {
    let Some(offset) = digit.checked_sub(chunk.coeff) else {
        return 0;
    };
    chunk
        .digits
        .get(offset)
        .copied()
        .map(u64::from)
        .unwrap_or(0)
}

fn coefficient_pairs(coeff: usize) -> impl Iterator<Item = (usize, usize)> {
    let start = coeff.saturating_sub(N_LIMBS - 1);
    let end = coeff.min(N_LIMBS - 1);
    (start..=end).map(move |i| (i, coeff - i))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar_arithmetic::{FnMulTrace, P256_ORDER};

    fn scalar(value: u64) -> [u64; 4] {
        [value, 0, 0, 0]
    }

    #[test]
    fn split_trace_verifies_modular_product() {
        let mul = FnMulTrace::new(&scalar(7), &scalar(11), &P256_ORDER)
            .expect("valid multiplication trace");
        let split = SplitProductTrace::new(&mul);

        split
            .verify("split_mul", &mul)
            .expect("split trace verifies");
        assert_eq!(split.ab_chunks.len(), PRODUCT_CHUNKS);
        assert_eq!(split.qn_chunks.len(), PRODUCT_CHUNKS);
    }

    #[test]
    fn split_trace_detects_mutated_chunk_digit() {
        let mul = FnMulTrace::new(&scalar(7), &scalar(11), &P256_ORDER)
            .expect("valid multiplication trace");
        let mut split = SplitProductTrace::new(&mul);
        split.ab_chunks[0].digits[0] += 1;

        let err = split
            .verify("split_mul", &mul)
            .expect_err("mutated chunk must fail");
        assert!(matches!(
            err,
            ScalarArithmeticError::ProductChunkMismatch { .. }
        ));
    }

    #[test]
    fn split_trace_top_chunk_digit_is_boolean() {
        let mut max_scalar = P256_ORDER;
        max_scalar[0] -= 1;
        let mul = FnMulTrace::new(&max_scalar, &max_scalar, &P256_ORDER)
            .expect("valid multiplication trace");
        let split = SplitProductTrace::new(&mul);

        assert!(split
            .ab_chunks
            .iter()
            .chain(&split.qn_chunks)
            .all(|chunk| chunk.digits[2] <= CHUNK_TOP_DIGIT_MAX));
    }

    #[test]
    fn split_trace_carries_match_unsplit_trace() {
        let mul = FnMulTrace::new(&P256_ORDER, &scalar(17), &P256_ORDER)
            .expect("valid multiplication trace");
        let split = SplitProductTrace::new(&mul);

        assert_eq!(split.carries, mul.carries);
        split
            .verify("split_mul", &mul)
            .expect("split trace verifies");
    }
}
