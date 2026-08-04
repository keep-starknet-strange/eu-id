use core::array;
use core::fmt;

use stwo::core::fields::m31::M31;
use stwo_p256_utils::constants::N_LIMBS;
use stwo_p256_utils::scalar_arithmetic::{
    words_to_limbs, CanonicalLtTrace, ProductChunk, ScalarArithmeticError, ScalarFieldMulTrace,
    SplitProductTrace, P256_ORDER, PRODUCT_EQUATION_LIMBS,
};

use crate::range_checks::encode_signed_carry;

use super::accumulator::for_each_digit_contribution;
use super::{
    product_chunk_pairs, ProductSide, ScalarModMulLimbRole, PRODUCT_DIGIT_ACCUMULATOR_TERMS,
    PRODUCT_SCALAR_LIMB_USE_COUNT, SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS,
    SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS, SCALAR_MOD_MUL_SPLIT_PRODUCT_CHUNKS,
};

const SCALAR_MOD_MUL_CANONICAL_ROWS: usize = 4;
const SCALAR_MOD_MUL_ACCUMULATOR_ROWS: usize = 2 * PRODUCT_EQUATION_LIMBS;
const SCALAR_MOD_MUL_REDUCTION_ROWS: usize = PRODUCT_EQUATION_LIMBS;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ScalarModMulTraceError {
    NonP256OrderModulus,
    ScalarArithmetic(ScalarArithmeticError),
    ProductChunkMetadataMismatch {
        side: ProductSide,
        row: usize,
        expected_coeff: usize,
        expected_chunk: usize,
        actual_coeff: usize,
        actual_chunk: usize,
    },
}

impl fmt::Display for ScalarModMulTraceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NonP256OrderModulus => {
                write!(f, "scalar mod-mul trace must use the fixed P-256 order")
            }
            Self::ScalarArithmetic(err) => err.fmt(f),
            Self::ProductChunkMetadataMismatch {
                side,
                row,
                expected_coeff,
                expected_chunk,
                actual_coeff,
                actual_chunk,
            } => write!(
                f,
                "{side:?} chunk row {row} metadata mismatch: expected ({expected_coeff}, \
                 {expected_chunk}), got ({actual_coeff}, {actual_chunk})"
            ),
        }
    }
}

impl std::error::Error for ScalarModMulTraceError {}

impl From<ScalarArithmeticError> for ScalarModMulTraceError {
    fn from(error: ScalarArithmeticError) -> Self {
        Self::ScalarArithmetic(error)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanonicalScalarTraceRow {
    pub role: ScalarModMulLimbRole,
    pub value: [M31; N_LIMBS],
    pub slack: [M31; N_LIMBS],
    pub carries: [M31; N_LIMBS],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProductTermTrace {
    pub lhs: M31,
    pub rhs: M31,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VariableProductChunkTraceRow {
    pub side: ProductSide,
    pub coeff: usize,
    pub chunk: usize,
    pub terms: [ProductTermTrace; SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS],
    pub digits: [M31; SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QnProductChunkTraceRow {
    pub side: ProductSide,
    pub coeff: usize,
    pub chunk: usize,
    pub quotient_limbs: [M31; SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS],
    pub digits: [M31; SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProductDigitAccumulatorTraceRow {
    pub side: ProductSide,
    pub digit_index: usize,
    pub terms: [M31; PRODUCT_DIGIT_ACCUMULATOR_TERMS],
    pub term_count: usize,
    pub product_digit: M31,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarReductionDigitTraceRow {
    pub digit_index: usize,
    pub ab_digit: M31,
    pub qn_digit: M31,
    pub result_limb: M31,
    pub prev_carry: M31,
    pub carry: M31,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarModMulTraceRows {
    pub mul_id: u32,
    pub canonical_scalars: [CanonicalScalarTraceRow; SCALAR_MOD_MUL_CANONICAL_ROWS],
    pub ab_chunks: Vec<VariableProductChunkTraceRow>,
    pub qn_chunks: Vec<QnProductChunkTraceRow>,
    pub accumulators: Vec<ProductDigitAccumulatorTraceRow>,
    pub reduction_digits: Vec<ScalarReductionDigitTraceRow>,
}

/// Vertical concatenation of several `ScalarModMulTraceRows` instances into a
/// single merged component set. Each sub-family's rows are laid out block-major
/// (instance 0's rows, then instance 1's, ...). Every row carries the `mul_id`
/// of its originating instance so the merged LogUp tuples stay keyed per
/// instance. Per-instance row counts are input-independent, so the merged
/// schedule remains a valid preprocessed (circuit-fixed) trace.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarModMulMergedRows {
    pub instances: Vec<ScalarModMulTraceRows>,
}

impl ScalarModMulMergedRows {
    pub fn new(instances: Vec<ScalarModMulTraceRows>) -> Self {
        Self { instances }
    }

    pub fn canonical_scalars(&self) -> impl Iterator<Item = (u32, &CanonicalScalarTraceRow)> {
        self.instances.iter().flat_map(|inst| {
            inst.canonical_scalars
                .iter()
                .map(move |row| (inst.mul_id, row))
        })
    }

    pub fn ab_chunks(&self) -> impl Iterator<Item = (u32, &VariableProductChunkTraceRow)> {
        self.instances
            .iter()
            .flat_map(|inst| inst.ab_chunks.iter().map(move |row| (inst.mul_id, row)))
    }

    pub fn qn_chunks(&self) -> impl Iterator<Item = (u32, &QnProductChunkTraceRow)> {
        self.instances
            .iter()
            .flat_map(|inst| inst.qn_chunks.iter().map(move |row| (inst.mul_id, row)))
    }

    pub fn accumulators(&self) -> impl Iterator<Item = (u32, &ProductDigitAccumulatorTraceRow)> {
        self.instances
            .iter()
            .flat_map(|inst| inst.accumulators.iter().map(move |row| (inst.mul_id, row)))
    }

    pub fn reduction_digits(&self) -> impl Iterator<Item = (u32, &ScalarReductionDigitTraceRow)> {
        self.instances.iter().flat_map(|inst| {
            inst.reduction_digits
                .iter()
                .map(move |row| (inst.mul_id, row))
        })
    }

    pub fn canonical_len(&self) -> usize {
        self.instances
            .iter()
            .map(|inst| inst.canonical_scalars.len())
            .sum()
    }

    pub fn ab_chunks_len(&self) -> usize {
        self.instances.iter().map(|inst| inst.ab_chunks.len()).sum()
    }

    pub fn qn_chunks_len(&self) -> usize {
        self.instances.iter().map(|inst| inst.qn_chunks.len()).sum()
    }

    pub fn accumulators_len(&self) -> usize {
        self.instances
            .iter()
            .map(|inst| inst.accumulators.len())
            .sum()
    }

    pub fn reduction_len(&self) -> usize {
        self.instances
            .iter()
            .map(|inst| inst.reduction_digits.len())
            .sum()
    }
}

impl ScalarModMulTraceRows {
    pub fn new(mul_id: u32, trace: &ScalarFieldMulTrace) -> Result<Self, ScalarModMulTraceError> {
        trace.verify()?;
        if trace.mul.modulus != words_to_limbs(&P256_ORDER) {
            return Err(ScalarModMulTraceError::NonP256OrderModulus);
        }

        let split = SplitProductTrace::new(&trace.mul);
        split.verify(trace.equation, &trace.mul)?;

        let canonical_scalars = [
            canonical_row(ScalarModMulLimbRole::A, &trace.a_lt_modulus),
            canonical_row(ScalarModMulLimbRole::B, &trace.b_lt_modulus),
            canonical_row(ScalarModMulLimbRole::Quotient, &trace.quotient_lt_modulus),
            canonical_row(ScalarModMulLimbRole::Result, &trace.result_lt_modulus),
        ];
        let ab_chunks = variable_product_rows(&trace.mul.a, &trace.mul.b, &split.ab_chunks)?;
        let qn_chunks = qn_product_rows(&trace.mul.quotient, &split.qn_chunks)?;
        let accumulators = product_digit_accumulator_rows(&split);
        let reduction_digits = reduction_digit_rows(trace, &split);

        Ok(Self {
            mul_id,
            canonical_scalars,
            ab_chunks,
            qn_chunks,
            accumulators,
            reduction_digits,
        })
    }

    pub const fn active_row_count() -> usize {
        SCALAR_MOD_MUL_CANONICAL_ROWS
            + 2 * SCALAR_MOD_MUL_SPLIT_PRODUCT_CHUNKS
            + SCALAR_MOD_MUL_ACCUMULATOR_ROWS
            + SCALAR_MOD_MUL_REDUCTION_ROWS
    }

    pub const fn padded_log_size() -> u32 {
        Self::active_row_count()
            .next_power_of_two()
            .trailing_zeros()
    }

    pub const fn padded_row_count() -> usize {
        1usize << Self::padded_log_size()
    }

    pub fn relation_counts(&self) -> ScalarModMulRelationCounts {
        ScalarModMulRelationCounts {
            scalar_limb_provides: PRODUCT_SCALAR_LIMB_USE_COUNT as usize * N_LIMBS * 3 + N_LIMBS,
            scalar_limb_uses: 3 * N_LIMBS * N_LIMBS + N_LIMBS,
            product_chunk_digit_provides: self.provided_product_chunk_digits(),
            product_chunk_digit_uses: self.accumulators.iter().map(|row| row.term_count).sum(),
            product_digit_provides: self.accumulators.len(),
            product_digit_uses: 2 * self.reduction_digits.len(),
            reduction_carry_provides: PRODUCT_EQUATION_LIMBS - 1,
            reduction_carry_uses: PRODUCT_EQUATION_LIMBS - 1,
        }
    }

    fn provided_product_chunk_digits(&self) -> usize {
        self.ab_chunks
            .iter()
            .map(|row| provided_chunk_digits(row.coeff))
            .sum::<usize>()
            + self
                .qn_chunks
                .iter()
                .map(|row| provided_chunk_digits(row.coeff))
                .sum::<usize>()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ScalarModMulRelationCounts {
    pub scalar_limb_provides: usize,
    pub scalar_limb_uses: usize,
    pub product_chunk_digit_provides: usize,
    pub product_chunk_digit_uses: usize,
    pub product_digit_provides: usize,
    pub product_digit_uses: usize,
    pub reduction_carry_provides: usize,
    pub reduction_carry_uses: usize,
}

impl ScalarModMulRelationCounts {
    pub const fn is_balanced(self) -> bool {
        self.scalar_limb_provides == self.scalar_limb_uses
            && self.product_chunk_digit_provides == self.product_chunk_digit_uses
            && self.product_digit_provides == self.product_digit_uses
            && self.reduction_carry_provides == self.reduction_carry_uses
    }
}

fn canonical_row(role: ScalarModMulLimbRole, trace: &CanonicalLtTrace) -> CanonicalScalarTraceRow {
    CanonicalScalarTraceRow {
        role,
        value: trace.value.map(m31_from_u32),
        slack: trace.slack.map(m31_from_u32),
        carries: trace.carries.map(m31_from_bool_carry),
    }
}

fn variable_product_rows(
    a: &[u32; N_LIMBS],
    b: &[u32; N_LIMBS],
    chunks: &[ProductChunk],
) -> Result<Vec<VariableProductChunkTraceRow>, ScalarModMulTraceError> {
    chunks
        .iter()
        .enumerate()
        .map(|(row, chunk)| {
            assert_chunk_metadata(ProductSide::Ab, row, chunk)?;
            let (pairs, term_count) = product_chunk_pairs(chunk.coeff, chunk.chunk);
            let terms = array::from_fn(|i| {
                if i < term_count {
                    let (lhs, rhs) = pairs[i];
                    ProductTermTrace {
                        lhs: m31_from_u32(a[lhs]),
                        rhs: m31_from_u32(b[rhs]),
                    }
                } else {
                    ProductTermTrace::zero()
                }
            });

            Ok(VariableProductChunkTraceRow {
                side: ProductSide::Ab,
                coeff: chunk.coeff,
                chunk: chunk.chunk,
                terms,
                digits: chunk.digits.map(m31_from_u32),
            })
        })
        .collect()
}

fn qn_product_rows(
    quotient: &[u32; N_LIMBS],
    chunks: &[ProductChunk],
) -> Result<Vec<QnProductChunkTraceRow>, ScalarModMulTraceError> {
    chunks
        .iter()
        .enumerate()
        .map(|(row, chunk)| {
            assert_chunk_metadata(ProductSide::Qn, row, chunk)?;
            let (pairs, term_count) = product_chunk_pairs(chunk.coeff, chunk.chunk);
            let quotient_limbs = array::from_fn(|i| {
                if i < term_count {
                    m31_from_u32(quotient[pairs[i].0])
                } else {
                    M31::from_u32_unchecked(0)
                }
            });

            Ok(QnProductChunkTraceRow {
                side: ProductSide::Qn,
                coeff: chunk.coeff,
                chunk: chunk.chunk,
                quotient_limbs,
                digits: chunk.digits.map(m31_from_u32),
            })
        })
        .collect()
}

fn product_digit_accumulator_rows(
    split: &SplitProductTrace,
) -> Vec<ProductDigitAccumulatorTraceRow> {
    let mut rows = Vec::with_capacity(SCALAR_MOD_MUL_ACCUMULATOR_ROWS);
    for side in [ProductSide::Ab, ProductSide::Qn] {
        let chunks = match side {
            ProductSide::Ab => &split.ab_chunks,
            ProductSide::Qn => &split.qn_chunks,
        };
        for digit_index in 0..PRODUCT_EQUATION_LIMBS {
            rows.push(product_digit_accumulator_row(side, digit_index, chunks));
        }
    }
    rows
}

fn product_digit_accumulator_row(
    side: ProductSide,
    digit_index: usize,
    chunks: &[ProductChunk],
) -> ProductDigitAccumulatorTraceRow {
    let mut terms = [M31::from_u32_unchecked(0); PRODUCT_DIGIT_ACCUMULATOR_TERMS];
    let term_count =
        for_each_digit_contribution(digit_index, |term_index, coeff, chunk, offset| {
            let digit = find_chunk(chunks, coeff, chunk).digits[offset];
            terms[term_index] = m31_from_u32(digit);
        });
    let product_digit = terms[..term_count]
        .iter()
        .fold(0u64, |acc, term| acc + u64::from(term.0));

    ProductDigitAccumulatorTraceRow {
        side,
        digit_index,
        terms,
        term_count,
        product_digit: m31_from_u64(product_digit),
    }
}

fn reduction_digit_rows(
    trace: &ScalarFieldMulTrace,
    split: &SplitProductTrace,
) -> Vec<ScalarReductionDigitTraceRow> {
    (0..PRODUCT_EQUATION_LIMBS)
        .map(|digit_index| {
            let result_limb = trace
                .mul
                .result
                .get(digit_index)
                .copied()
                .map(m31_from_u32)
                .unwrap_or_else(|| M31::from_u32_unchecked(0));
            let prev_carry = if digit_index == 0 {
                0
            } else {
                split.carries[digit_index - 1]
            };

            ScalarReductionDigitTraceRow {
                digit_index,
                ab_digit: split_product_digit(&split.ab_chunks, digit_index),
                qn_digit: split_product_digit(&split.qn_chunks, digit_index),
                result_limb,
                prev_carry: encode_signed_carry(prev_carry),
                carry: encode_signed_carry(split.carries[digit_index]),
            }
        })
        .collect()
}

fn assert_chunk_metadata(
    side: ProductSide,
    row: usize,
    chunk: &ProductChunk,
) -> Result<(), ScalarModMulTraceError> {
    let expected = expected_chunk_metadata(row);
    if (chunk.coeff, chunk.chunk) == expected {
        Ok(())
    } else {
        Err(ScalarModMulTraceError::ProductChunkMetadataMismatch {
            side,
            row,
            expected_coeff: expected.0,
            expected_chunk: expected.1,
            actual_coeff: chunk.coeff,
            actual_chunk: chunk.chunk,
        })
    }
}

fn expected_chunk_metadata(row: usize) -> (usize, usize) {
    let mut seen = 0usize;
    for coeff in 0..(PRODUCT_EQUATION_LIMBS - 1) {
        let mut chunk = 0usize;
        loop {
            let (_, term_count) = product_chunk_pairs(coeff, chunk);
            if term_count == 0 {
                break;
            }
            if seen == row {
                return (coeff, chunk);
            }
            seen += 1;
            chunk += 1;
        }
    }
    panic!("product chunk row {row} outside 0..{SCALAR_MOD_MUL_SPLIT_PRODUCT_CHUNKS}");
}

fn find_chunk(chunks: &[ProductChunk], coeff: usize, chunk: usize) -> &ProductChunk {
    chunks
        .iter()
        .find(|candidate| candidate.coeff == coeff && candidate.chunk == chunk)
        .expect("split product trace contains every chunk")
}

fn split_product_digit(chunks: &[ProductChunk], digit_index: usize) -> M31 {
    let value = chunks
        .iter()
        .filter_map(|chunk| {
            digit_index
                .checked_sub(chunk.coeff)
                .and_then(|offset| chunk.digits.get(offset))
                .copied()
        })
        .map(u64::from)
        .sum();
    m31_from_u64(value)
}

fn provided_chunk_digits(coeff: usize) -> usize {
    SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS.min(PRODUCT_EQUATION_LIMBS - coeff)
}

impl ProductTermTrace {
    const fn zero() -> Self {
        Self {
            lhs: M31::from_u32_unchecked(0),
            rhs: M31::from_u32_unchecked(0),
        }
    }
}

fn m31_from_u32(value: u32) -> M31 {
    M31::from_u32_unchecked(value)
}

fn m31_from_u64(value: u64) -> M31 {
    assert!(
        value < (1u64 << 31) - 1,
        "value {value} does not fit in M31"
    );
    M31::from_u32_unchecked(value as u32)
}

fn m31_from_bool_carry(carry: i64) -> M31 {
    assert!(
        carry == 0 || carry == 1,
        "canonical comparison carry must be 0 or 1, got {carry}"
    );
    M31::from_u32_unchecked(carry as u32)
}

#[cfg(test)]
mod tests {
    use super::*;
    use stwo_p256_utils::constants::LIMB_BITS;

    use super::super::chunk_product::PRODUCT_CHUNK_DIGIT_ENTRIES_PER_SIDE;

    fn scalar(value: u64) -> [u64; 4] {
        [value, 0, 0, 0]
    }

    fn test_rows() -> ScalarModMulTraceRows {
        let trace = ScalarFieldMulTrace::new("test_mul", &scalar(7), &scalar(11), &P256_ORDER)
            .expect("valid scalar mod-mul trace");
        ScalarModMulTraceRows::new(3, &trace).expect("trace rows generate")
    }

    #[test]
    fn scalar_mod_mul_trace_row_counts_match_layout() {
        let rows = test_rows();

        assert_eq!(rows.canonical_scalars.len(), 4);
        assert_eq!(rows.ab_chunks.len(), SCALAR_MOD_MUL_SPLIT_PRODUCT_CHUNKS);
        assert_eq!(rows.qn_chunks.len(), SCALAR_MOD_MUL_SPLIT_PRODUCT_CHUNKS);
        assert_eq!(rows.accumulators.len(), 2 * PRODUCT_EQUATION_LIMBS);
        assert_eq!(rows.reduction_digits.len(), PRODUCT_EQUATION_LIMBS);
        assert_eq!(ScalarModMulTraceRows::active_row_count(), 544);
        assert_eq!(ScalarModMulTraceRows::padded_log_size(), 10);
        assert_eq!(ScalarModMulTraceRows::padded_row_count(), 1024);
    }

    #[test]
    fn scalar_mod_mul_trace_relation_counts_are_balanced() {
        let counts = test_rows().relation_counts();

        assert!(counts.is_balanced());
        assert_eq!(counts.scalar_limb_provides, 1220);
        assert_eq!(
            counts.product_chunk_digit_provides,
            2 * PRODUCT_CHUNK_DIGIT_ENTRIES_PER_SIDE
        );
        assert_eq!(counts.product_digit_provides, 2 * PRODUCT_EQUATION_LIMBS);
        assert_eq!(counts.reduction_carry_provides, PRODUCT_EQUATION_LIMBS - 1);
    }

    #[test]
    fn scalar_mod_mul_trace_metadata_is_row_deterministic() {
        let rows = test_rows();

        for (row, chunk) in rows.ab_chunks.iter().enumerate() {
            let expected = expected_chunk_metadata(row);
            assert_eq!((chunk.coeff, chunk.chunk), expected);
            assert_eq!(chunk.side, ProductSide::Ab);
        }
        for (row, chunk) in rows.qn_chunks.iter().enumerate() {
            let expected = expected_chunk_metadata(row);
            assert_eq!((chunk.coeff, chunk.chunk), expected);
            assert_eq!(chunk.side, ProductSide::Qn);
        }
    }

    #[test]
    fn scalar_mod_mul_trace_uses_fixed_p256_order() {
        let wrong_modulus = [101, 0, 0, 0];
        let trace =
            ScalarFieldMulTrace::new("wrong_modulus", &scalar(7), &scalar(11), &wrong_modulus)
                .expect("valid trace over small modulus");

        let err = ScalarModMulTraceRows::new(0, &trace).expect_err("non-P256 modulus rejected");
        assert!(matches!(err, ScalarModMulTraceError::NonP256OrderModulus));
    }

    #[test]
    fn scalar_mod_mul_trace_carries_are_centered_encoded() {
        let mut max_scalar = P256_ORDER;
        max_scalar[0] -= 1;
        let trace = ScalarFieldMulTrace::new("max_mul", &max_scalar, &max_scalar, &P256_ORDER)
            .expect("valid max scalar trace");
        let split = SplitProductTrace::new(&trace.mul);
        let rows = ScalarModMulTraceRows::new(9, &trace).expect("trace rows generate");

        for (digit, row) in rows.reduction_digits.iter().enumerate() {
            let expected_prev = if digit == 0 {
                0
            } else {
                split.carries[digit - 1]
            };
            assert_eq!(row.prev_carry, encode_signed_carry(expected_prev));
            assert_eq!(row.carry, encode_signed_carry(split.carries[digit]));
        }
    }

    #[test]
    fn scalar_mod_mul_trace_detects_chunk_order_mutation() {
        let trace = ScalarFieldMulTrace::new("test_mul", &scalar(7), &scalar(11), &P256_ORDER)
            .expect("valid scalar mod-mul trace");
        let mut split = SplitProductTrace::new(&trace.mul);
        split.ab_chunks.swap(0, 1);

        let err = variable_product_rows(&trace.mul.a, &trace.mul.b, &split.ab_chunks)
            .expect_err("mutated chunk order rejected");
        assert!(matches!(
            err,
            ScalarModMulTraceError::ProductChunkMetadataMismatch { .. }
        ));
    }

    #[test]
    fn scalar_mod_mul_trace_bitwidth_constants_match_limbs() {
        assert_eq!(1u32 << LIMB_BITS, 8192);
        assert_eq!(PRODUCT_EQUATION_LIMBS, 2 * N_LIMBS);
    }
}
