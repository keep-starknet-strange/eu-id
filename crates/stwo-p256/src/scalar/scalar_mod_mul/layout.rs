use std::collections::BTreeMap;

use stwo::core::fields::m31::M31;
use stwo_p256_utils::constants::N_LIMBS;
use stwo_p256_utils::scalar_arithmetic::PRODUCT_EQUATION_LIMBS;

use crate::range_checks::decode_signed_carry;

use super::accumulator::for_each_digit_contribution;
use super::columns::{m31_column_eval, padded_log_size, M31ColumnEval};
use super::{
    product_chunk_pairs, ProductSide, ScalarModMulTraceRows, PRODUCT_DIGIT_ACCUMULATOR_TERMS,
    ROLE_RESULT, SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS, SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS,
};

pub const CANONICAL_SCALAR_TRACE_COLUMNS: usize = 3 * N_LIMBS;
pub const AB_PRODUCT_CHUNK_TRACE_COLUMNS: usize =
    2 * SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS + SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS;
pub const QN_PRODUCT_CHUNK_TRACE_COLUMNS: usize =
    SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS + SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS;
pub const PRODUCT_DIGIT_ACCUMULATOR_TRACE_COLUMNS: usize = PRODUCT_DIGIT_ACCUMULATOR_TERMS + 1;
pub const SCALAR_REDUCTION_DIGIT_TRACE_COLUMNS: usize = 5;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarModMulColumnTrace<const W: usize> {
    pub log_size: u32,
    pub active_rows: usize,
    pub columns: [Vec<M31>; W],
}

impl<const W: usize> ScalarModMulColumnTrace<W> {
    fn from_rows<R>(rows: &[R], mut encode: impl FnMut(&R) -> [M31; W]) -> Self {
        let active_rows = rows.len();
        let log_size = padded_log_size(active_rows);
        let padded_rows = 1usize << log_size;
        let mut columns = std::array::from_fn(|_| vec![M31::from_u32_unchecked(0); padded_rows]);

        for (row_index, row) in rows.iter().enumerate() {
            for (col_index, value) in encode(row).into_iter().enumerate() {
                columns[col_index][row_index] = value;
            }
        }

        Self {
            log_size,
            active_rows,
            columns,
        }
    }

    pub fn padded_rows(&self) -> usize {
        self.columns.first().map(Vec::len).unwrap_or(0)
    }

    pub fn to_circle_evaluations(&self) -> [M31ColumnEval; W] {
        self.columns
            .clone()
            .map(|column| m31_column_eval(self.log_size, column))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarModMulFamilyTraces {
    pub canonical_scalars: ScalarModMulColumnTrace<CANONICAL_SCALAR_TRACE_COLUMNS>,
    pub ab_chunks: ScalarModMulColumnTrace<AB_PRODUCT_CHUNK_TRACE_COLUMNS>,
    pub qn_chunks: ScalarModMulColumnTrace<QN_PRODUCT_CHUNK_TRACE_COLUMNS>,
    pub accumulators: ScalarModMulColumnTrace<PRODUCT_DIGIT_ACCUMULATOR_TRACE_COLUMNS>,
    pub reduction_digits: ScalarModMulColumnTrace<SCALAR_REDUCTION_DIGIT_TRACE_COLUMNS>,
}

pub struct ScalarModMulFamilyColumnEvals {
    pub canonical_scalars: [M31ColumnEval; CANONICAL_SCALAR_TRACE_COLUMNS],
    pub ab_chunks: [M31ColumnEval; AB_PRODUCT_CHUNK_TRACE_COLUMNS],
    pub qn_chunks: [M31ColumnEval; QN_PRODUCT_CHUNK_TRACE_COLUMNS],
    pub accumulators: [M31ColumnEval; PRODUCT_DIGIT_ACCUMULATOR_TRACE_COLUMNS],
    pub reduction_digits: [M31ColumnEval; SCALAR_REDUCTION_DIGIT_TRACE_COLUMNS],
}

impl ScalarModMulFamilyTraces {
    pub fn from_rows(rows: &ScalarModMulTraceRows) -> Self {
        Self {
            canonical_scalars: ScalarModMulColumnTrace::from_rows(
                &rows.canonical_scalars,
                canonical_columns,
            ),
            ab_chunks: ScalarModMulColumnTrace::from_rows(&rows.ab_chunks, ab_chunk_columns),
            qn_chunks: ScalarModMulColumnTrace::from_rows(&rows.qn_chunks, qn_chunk_columns),
            accumulators: ScalarModMulColumnTrace::from_rows(
                &rows.accumulators,
                accumulator_columns,
            ),
            reduction_digits: ScalarModMulColumnTrace::from_rows(
                &rows.reduction_digits,
                reduction_columns,
            ),
        }
    }

    pub fn to_circle_evaluations(&self) -> ScalarModMulFamilyColumnEvals {
        ScalarModMulFamilyColumnEvals {
            canonical_scalars: self.canonical_scalars.to_circle_evaluations(),
            ab_chunks: self.ab_chunks.to_circle_evaluations(),
            qn_chunks: self.qn_chunks.to_circle_evaluations(),
            accumulators: self.accumulators.to_circle_evaluations(),
            reduction_digits: self.reduction_digits.to_circle_evaluations(),
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ScalarModMulLookupUses {
    pub range13: Vec<M31>,
    pub signed_carry: Vec<i64>,
}

impl ScalarModMulLookupUses {
    pub fn from_rows(rows: &ScalarModMulTraceRows) -> Self {
        let mut uses = Self::default();

        for row in &rows.canonical_scalars {
            uses.range13.extend(row.value);
            uses.range13.extend(row.slack);
        }
        for row in &rows.ab_chunks {
            uses.range13.extend([row.digits[0], row.digits[1]]);
        }
        for row in &rows.qn_chunks {
            uses.range13.extend([row.digits[0], row.digits[1]]);
        }
        for row in &rows.reduction_digits {
            uses.signed_carry.push(decode_signed_carry(row.carry));
        }

        uses
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ScalarModMulRelationAudit {
    pub scalar_limb: RelationBalance,
    pub product_chunk_digit: RelationBalance,
    pub product_digit: RelationBalance,
    pub reduction_carry: RelationBalance,
}

impl ScalarModMulRelationAudit {
    pub fn from_rows(rows: &ScalarModMulTraceRows) -> Self {
        let mut audit = Self::default();
        audit.add_scalar_limb_terms(rows);
        audit.add_product_chunk_digit_terms(rows);
        audit.add_product_digit_terms(rows);
        audit.add_reduction_carry_terms(rows);
        audit
    }

    pub fn is_balanced(&self) -> bool {
        self.scalar_limb.is_balanced()
            && self.product_chunk_digit.is_balanced()
            && self.product_digit.is_balanced()
            && self.reduction_carry.is_balanced()
    }

    fn add_scalar_limb_terms(&mut self, rows: &ScalarModMulTraceRows) {
        for row in &rows.canonical_scalars {
            let multiplicity = match row.role {
                super::ScalarModMulLimbRole::A
                | super::ScalarModMulLimbRole::B
                | super::ScalarModMulLimbRole::Quotient => N_LIMBS as i64,
                super::ScalarModMulLimbRole::Result => 1,
            };
            for (limb_index, limb) in row.value.iter().enumerate() {
                self.scalar_limb.add(
                    scalar_limb_key(rows.mul_id, row.role.relation_role(), limb_index, limb.0),
                    -multiplicity,
                );
            }
        }

        for row in &rows.ab_chunks {
            let (_, term_count) = product_chunk_pairs(row.coeff, row.chunk);
            for (term_index, term) in row.terms.iter().take(term_count).enumerate() {
                let (lhs_index, rhs_index) =
                    product_chunk_pairs(row.coeff, row.chunk).0[term_index];
                self.scalar_limb.add(
                    scalar_limb_key(rows.mul_id, super::ROLE_A, lhs_index, term.lhs.0),
                    1,
                );
                self.scalar_limb.add(
                    scalar_limb_key(rows.mul_id, super::ROLE_B, rhs_index, term.rhs.0),
                    1,
                );
            }
        }

        for row in &rows.qn_chunks {
            let (pairs, term_count) = product_chunk_pairs(row.coeff, row.chunk);
            for (term_index, quotient_limb) in
                row.quotient_limbs.iter().take(term_count).enumerate()
            {
                self.scalar_limb.add(
                    scalar_limb_key(
                        rows.mul_id,
                        super::ROLE_QUOTIENT,
                        pairs[term_index].0,
                        quotient_limb.0,
                    ),
                    1,
                );
            }
        }

        for row in rows.reduction_digits.iter().take(N_LIMBS) {
            self.scalar_limb.add(
                scalar_limb_key(rows.mul_id, ROLE_RESULT, row.digit_index, row.result_limb.0),
                1,
            );
        }
    }

    fn add_product_chunk_digit_terms(&mut self, rows: &ScalarModMulTraceRows) {
        for row in &rows.ab_chunks {
            self.add_product_chunk_digit_provides(
                rows.mul_id,
                row.side,
                row.coeff,
                row.chunk,
                row.digits,
            );
        }
        for row in &rows.qn_chunks {
            self.add_product_chunk_digit_provides(
                rows.mul_id,
                row.side,
                row.coeff,
                row.chunk,
                row.digits,
            );
        }

        for row in &rows.accumulators {
            let side = row.side.relation_side();
            for_each_digit_contribution(row.digit_index, |term_index, coeff, chunk, offset| {
                self.product_chunk_digit.add(
                    vec![
                        rows.mul_id,
                        side,
                        coeff as u32,
                        chunk as u32,
                        offset as u32,
                        row.terms[term_index].0,
                    ],
                    1,
                );
            });
        }
    }

    fn add_product_chunk_digit_provides(
        &mut self,
        mul_id: u32,
        side: ProductSide,
        coeff: usize,
        chunk: usize,
        digits: [M31; SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS],
    ) {
        for (offset, digit) in digits.iter().enumerate() {
            if coeff + offset >= PRODUCT_EQUATION_LIMBS {
                continue;
            }
            self.product_chunk_digit.add(
                vec![
                    mul_id,
                    side.relation_side(),
                    coeff as u32,
                    chunk as u32,
                    offset as u32,
                    digit.0,
                ],
                -1,
            );
        }
    }

    fn add_product_digit_terms(&mut self, rows: &ScalarModMulTraceRows) {
        for row in &rows.accumulators {
            self.product_digit.add(
                product_digit_key(
                    rows.mul_id,
                    row.side.relation_side(),
                    row.digit_index,
                    row.product_digit.0,
                ),
                -1,
            );
        }

        for row in &rows.reduction_digits {
            self.product_digit.add(
                product_digit_key(rows.mul_id, super::SIDE_AB, row.digit_index, row.ab_digit.0),
                1,
            );
            self.product_digit.add(
                product_digit_key(rows.mul_id, super::SIDE_QN, row.digit_index, row.qn_digit.0),
                1,
            );
        }
    }

    fn add_reduction_carry_terms(&mut self, rows: &ScalarModMulTraceRows) {
        for row in &rows.reduction_digits {
            if row.digit_index > 0 {
                self.reduction_carry.add(
                    reduction_carry_key(rows.mul_id, row.digit_index - 1, row.prev_carry.0),
                    1,
                );
            }
            if row.digit_index + 1 < PRODUCT_EQUATION_LIMBS {
                self.reduction_carry.add(
                    reduction_carry_key(rows.mul_id, row.digit_index, row.carry.0),
                    -1,
                );
            }
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RelationBalance {
    entries: BTreeMap<Vec<u32>, i64>,
}

impl RelationBalance {
    fn add(&mut self, key: Vec<u32>, multiplicity: i64) {
        *self.entries.entry(key).or_default() += multiplicity;
    }

    pub fn is_balanced(&self) -> bool {
        self.entries.values().all(|&multiplicity| multiplicity == 0)
    }

    pub fn nonzero_entries(&self) -> usize {
        self.entries
            .values()
            .filter(|&&multiplicity| multiplicity != 0)
            .count()
    }
}

fn canonical_columns(
    row: &super::CanonicalScalarTraceRow,
) -> [M31; CANONICAL_SCALAR_TRACE_COLUMNS] {
    let mut columns = [M31::from_u32_unchecked(0); CANONICAL_SCALAR_TRACE_COLUMNS];
    columns[..N_LIMBS].copy_from_slice(&row.value);
    columns[N_LIMBS..2 * N_LIMBS].copy_from_slice(&row.slack);
    columns[2 * N_LIMBS..].copy_from_slice(&row.carries);
    columns
}

fn ab_chunk_columns(
    row: &super::VariableProductChunkTraceRow,
) -> [M31; AB_PRODUCT_CHUNK_TRACE_COLUMNS] {
    [
        row.terms[0].lhs,
        row.terms[0].rhs,
        row.terms[1].lhs,
        row.terms[1].rhs,
        row.digits[0],
        row.digits[1],
        row.digits[2],
    ]
}

fn qn_chunk_columns(row: &super::QnProductChunkTraceRow) -> [M31; QN_PRODUCT_CHUNK_TRACE_COLUMNS] {
    [
        row.quotient_limbs[0],
        row.quotient_limbs[1],
        row.digits[0],
        row.digits[1],
        row.digits[2],
    ]
}

fn accumulator_columns(
    row: &super::ProductDigitAccumulatorTraceRow,
) -> [M31; PRODUCT_DIGIT_ACCUMULATOR_TRACE_COLUMNS] {
    let mut columns = [M31::from_u32_unchecked(0); PRODUCT_DIGIT_ACCUMULATOR_TRACE_COLUMNS];
    columns[..PRODUCT_DIGIT_ACCUMULATOR_TERMS].copy_from_slice(&row.terms);
    columns[PRODUCT_DIGIT_ACCUMULATOR_TERMS] = row.product_digit;
    columns
}

fn reduction_columns(
    row: &super::ScalarReductionDigitTraceRow,
) -> [M31; SCALAR_REDUCTION_DIGIT_TRACE_COLUMNS] {
    [
        row.ab_digit,
        row.qn_digit,
        row.result_limb,
        row.prev_carry,
        row.carry,
    ]
}

fn scalar_limb_key(mul_id: u32, role: u32, limb_index: usize, limb_value: u32) -> Vec<u32> {
    vec![mul_id, role, limb_index as u32, limb_value]
}

fn product_digit_key(mul_id: u32, side: u32, digit_index: usize, digit_value: u32) -> Vec<u32> {
    vec![mul_id, side, digit_index as u32, digit_value]
}

fn reduction_carry_key(mul_id: u32, digit_index: usize, carry_value: u32) -> Vec<u32> {
    vec![mul_id, digit_index as u32, carry_value]
}

#[cfg(test)]
mod tests {
    use stwo_p256_utils::scalar_arithmetic::{ScalarFieldMulTrace, P256_ORDER};

    use super::*;

    fn scalar(value: u64) -> [u64; 4] {
        [value, 0, 0, 0]
    }

    fn test_rows() -> ScalarModMulTraceRows {
        let trace = ScalarFieldMulTrace::new("test_mul", &scalar(7), &scalar(11), &P256_ORDER)
            .expect("valid scalar mod-mul trace");
        ScalarModMulTraceRows::new(3, &trace).expect("trace rows generate")
    }

    #[test]
    fn scalar_mod_mul_family_traces_have_expected_widths_and_padding() {
        let rows = test_rows();
        let traces = ScalarModMulFamilyTraces::from_rows(&rows);

        assert_eq!(traces.canonical_scalars.columns.len(), 60);
        assert_eq!(traces.canonical_scalars.active_rows, 4);
        assert_eq!(
            traces.canonical_scalars.padded_rows(),
            1 << padded_log_size(4)
        );
        assert_eq!(traces.ab_chunks.columns.len(), 7);
        assert_eq!(traces.ab_chunks.active_rows, 210);
        assert_eq!(traces.ab_chunks.padded_rows(), 256);
        assert_eq!(traces.qn_chunks.columns.len(), 5);
        assert_eq!(traces.qn_chunks.padded_rows(), 256);
        assert_eq!(traces.accumulators.columns.len(), 31);
        assert_eq!(traces.accumulators.active_rows, 80);
        assert_eq!(traces.accumulators.padded_rows(), 128);
        assert_eq!(traces.reduction_digits.columns.len(), 5);
        assert_eq!(traces.reduction_digits.active_rows, 40);
        assert_eq!(traces.reduction_digits.padded_rows(), 64);
    }

    #[test]
    fn scalar_mod_mul_lookup_uses_match_air_helpers() {
        let rows = test_rows();
        let uses = ScalarModMulLookupUses::from_rows(&rows);

        assert_eq!(uses.range13.len(), 4 * 2 * N_LIMBS + 2 * 210 * 2);
        assert_eq!(uses.signed_carry.len(), PRODUCT_EQUATION_LIMBS);
        assert!(uses
            .range13
            .iter()
            .all(|value| value.0 < (1u32 << stwo_p256_utils::constants::LIMB_BITS)));
    }

    #[test]
    fn scalar_mod_mul_relation_audit_is_tuple_balanced() {
        let rows = test_rows();
        let audit = ScalarModMulRelationAudit::from_rows(&rows);

        assert!(audit.is_balanced());
        assert_eq!(audit.scalar_limb.nonzero_entries(), 0);
        assert_eq!(audit.product_chunk_digit.nonzero_entries(), 0);
        assert_eq!(audit.product_digit.nonzero_entries(), 0);
        assert_eq!(audit.reduction_carry.nonzero_entries(), 0);
    }

    #[test]
    fn scalar_mod_mul_relation_audit_detects_mutated_tuple_value() {
        let mut rows = test_rows();
        rows.accumulators[0].terms[0] += M31::from_u32_unchecked(1);
        let audit = ScalarModMulRelationAudit::from_rows(&rows);

        assert!(!audit.is_balanced());
        assert!(audit.product_chunk_digit.nonzero_entries() > 0);
    }

    #[test]
    fn scalar_mod_mul_column_trace_keeps_padding_zero() {
        let rows = test_rows();
        let traces = ScalarModMulFamilyTraces::from_rows(&rows);

        for column in &traces.ab_chunks.columns {
            assert!(column[traces.ab_chunks.active_rows..]
                .iter()
                .all(|&value| value == M31::from_u32_unchecked(0)));
        }
    }

    #[test]
    fn scalar_mod_mul_family_traces_materialize_circle_evaluations() {
        let rows = test_rows();
        let traces = ScalarModMulFamilyTraces::from_rows(&rows);
        let evals = traces.to_circle_evaluations();

        assert_eq!(
            evals.canonical_scalars.len(),
            CANONICAL_SCALAR_TRACE_COLUMNS
        );
        assert_eq!(evals.ab_chunks.len(), AB_PRODUCT_CHUNK_TRACE_COLUMNS);
        assert_eq!(evals.qn_chunks.len(), QN_PRODUCT_CHUNK_TRACE_COLUMNS);
        assert_eq!(
            evals.accumulators.len(),
            PRODUCT_DIGIT_ACCUMULATOR_TRACE_COLUMNS
        );
        assert_eq!(
            evals.reduction_digits.len(),
            SCALAR_REDUCTION_DIGIT_TRACE_COLUMNS
        );
        assert_eq!(
            evals.canonical_scalars[0].domain.log_size(),
            padded_log_size(4)
        );
        assert_eq!(evals.ab_chunks[0].domain.log_size(), 8);
        assert_eq!(evals.accumulators[0].domain.size(), 128);
        assert_eq!(evals.reduction_digits[0].domain.size(), 64);
    }
}
