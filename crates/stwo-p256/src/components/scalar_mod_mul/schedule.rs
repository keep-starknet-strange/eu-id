use stwo::core::fields::m31::M31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_p256_utils::constants::N_LIMBS;
use stwo_p256_utils::scalar_arithmetic::{words_to_limbs, P256_ORDER};

use super::accumulator::for_each_digit_contribution;
use super::columns::{log_size_from_padded_len, m31_column_eval, padded_log_size, M31ColumnEval};
use super::{
    product_chunk_pairs, ScalarModMulLimbRole, ScalarModMulMergedRows,
    PRODUCT_DIGIT_ACCUMULATOR_TERMS, PRODUCT_SCALAR_LIMB_USE_COUNT,
    SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS, SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProductFamily {
    Ab,
    Qn,
}

impl ProductFamily {
    fn prefix(self) -> &'static str {
        match self {
            Self::Ab => "ab",
            Self::Qn => "qn",
        }
    }

    fn prefixed(self, name: &str) -> String {
        format!("{}_{}", self.prefix(), name)
    }

    fn prefixed_indexed(self, name: &str, index: usize) -> String {
        format!("{}_{}_{}", self.prefix(), name, index)
    }
}

pub struct ScalarModMulScheduleColumnIds;

impl ScalarModMulScheduleColumnIds {
    pub fn canonical_active() -> PreProcessedColumnId {
        schedule_id("canonical_active")
    }

    pub fn canonical_role() -> PreProcessedColumnId {
        schedule_id("canonical_role")
    }

    pub fn canonical_multiplicity() -> PreProcessedColumnId {
        schedule_id("canonical_multiplicity")
    }

    pub fn product_active(family: ProductFamily) -> PreProcessedColumnId {
        schedule_id(family.prefixed("active"))
    }

    pub fn product_coeff(family: ProductFamily) -> PreProcessedColumnId {
        schedule_id(family.prefixed("coeff"))
    }

    pub fn product_chunk(family: ProductFamily) -> PreProcessedColumnId {
        schedule_id(family.prefixed("chunk"))
    }

    pub fn product_term_active(family: ProductFamily, term: usize) -> PreProcessedColumnId {
        schedule_id(family.prefixed_indexed("term_active", term))
    }

    pub fn product_lhs_index(family: ProductFamily, term: usize) -> PreProcessedColumnId {
        schedule_id(family.prefixed_indexed("lhs_index", term))
    }

    pub fn product_rhs_index(family: ProductFamily, term: usize) -> PreProcessedColumnId {
        schedule_id(family.prefixed_indexed("rhs_index", term))
    }

    pub fn product_digit_active(family: ProductFamily, offset: usize) -> PreProcessedColumnId {
        schedule_id(family.prefixed_indexed("digit_active", offset))
    }

    pub fn qn_modulus_limb(term: usize) -> PreProcessedColumnId {
        schedule_id(format!("qn_modulus_limb_{term}"))
    }

    pub fn accumulator_active() -> PreProcessedColumnId {
        schedule_id("accumulator_active")
    }

    pub fn accumulator_side() -> PreProcessedColumnId {
        schedule_id("accumulator_side")
    }

    pub fn accumulator_digit() -> PreProcessedColumnId {
        schedule_id("accumulator_digit")
    }

    pub fn accumulator_term_active(term: usize) -> PreProcessedColumnId {
        schedule_id(format!("accumulator_term_active_{term}"))
    }

    pub fn accumulator_coeff(term: usize) -> PreProcessedColumnId {
        schedule_id(format!("accumulator_coeff_{term}"))
    }

    pub fn accumulator_chunk(term: usize) -> PreProcessedColumnId {
        schedule_id(format!("accumulator_chunk_{term}"))
    }

    pub fn accumulator_offset(term: usize) -> PreProcessedColumnId {
        schedule_id(format!("accumulator_offset_{term}"))
    }

    pub fn reduction_active() -> PreProcessedColumnId {
        schedule_id("reduction_active")
    }

    pub fn reduction_digit() -> PreProcessedColumnId {
        schedule_id("reduction_digit")
    }

    pub fn reduction_has_result_limb() -> PreProcessedColumnId {
        schedule_id("reduction_has_result_limb")
    }

    pub fn reduction_has_prev_carry() -> PreProcessedColumnId {
        schedule_id("reduction_has_prev_carry")
    }

    pub fn reduction_has_next_carry() -> PreProcessedColumnId {
        schedule_id("reduction_has_next_carry")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarModMulScheduleColumn {
    pub id: PreProcessedColumnId,
    pub values: Vec<M31>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarModMulFixedSchedule {
    pub canonical: Vec<ScalarModMulScheduleColumn>,
    pub ab_chunks: Vec<ScalarModMulScheduleColumn>,
    pub qn_chunks: Vec<ScalarModMulScheduleColumn>,
    pub accumulators: Vec<ScalarModMulScheduleColumn>,
    pub reduction_digits: Vec<ScalarModMulScheduleColumn>,
}

pub struct ScalarModMulFixedScheduleEvals {
    pub canonical: Vec<M31ColumnEval>,
    pub ab_chunks: Vec<M31ColumnEval>,
    pub qn_chunks: Vec<M31ColumnEval>,
    pub accumulators: Vec<M31ColumnEval>,
    pub reduction_digits: Vec<M31ColumnEval>,
}

impl ScalarModMulFixedSchedule {
    pub fn from_rows(rows: &ScalarModMulMergedRows) -> Self {
        debug_assert!(rows
            .ab_chunks()
            .all(|(_, row)| row.side == super::ProductSide::Ab));
        debug_assert!(rows
            .qn_chunks()
            .all(|(_, row)| row.side == super::ProductSide::Qn));
        Self {
            canonical: canonical_schedule(rows),
            ab_chunks: product_schedule(
                ProductFamily::Ab,
                rows.ab_chunks_len(),
                rows.ab_chunks().map(|(_, row)| (row.coeff, row.chunk)),
            ),
            qn_chunks: qn_product_schedule(rows),
            accumulators: accumulator_schedule(rows),
            reduction_digits: reduction_schedule(rows),
        }
    }

    pub fn to_circle_evaluations(&self) -> ScalarModMulFixedScheduleEvals {
        ScalarModMulFixedScheduleEvals {
            canonical: schedule_columns_to_evals(&self.canonical),
            ab_chunks: schedule_columns_to_evals(&self.ab_chunks),
            qn_chunks: schedule_columns_to_evals(&self.qn_chunks),
            accumulators: schedule_columns_to_evals(&self.accumulators),
            reduction_digits: schedule_columns_to_evals(&self.reduction_digits),
        }
    }
}

fn schedule_columns_to_evals(columns: &[ScalarModMulScheduleColumn]) -> Vec<M31ColumnEval> {
    columns
        .iter()
        .map(|column| {
            let log_size = log_size_from_padded_len(column.values.len());
            m31_column_eval(log_size, column.values.clone())
        })
        .collect()
}

fn canonical_schedule(rows: &ScalarModMulMergedRows) -> Vec<ScalarModMulScheduleColumn> {
    let padded_rows = 1usize << padded_log_size(rows.canonical_len());
    let mut active = zeros(padded_rows);
    let mut role = zeros(padded_rows);
    let mut multiplicity = zeros(padded_rows);

    for (row_index, (_, row)) in rows.canonical_scalars().enumerate() {
        active[row_index] = one();
        role[row_index] = m31(row.role.relation_role());
        multiplicity[row_index] = m31(canonical_limb_multiplicity(row.role));
    }

    vec![
        column(ScalarModMulScheduleColumnIds::canonical_active(), active),
        column(ScalarModMulScheduleColumnIds::canonical_role(), role),
        column(
            ScalarModMulScheduleColumnIds::canonical_multiplicity(),
            multiplicity,
        ),
    ]
}

fn product_schedule(
    family: ProductFamily,
    active_rows: usize,
    coordinates: impl IntoIterator<Item = (usize, usize)>,
) -> Vec<ScalarModMulScheduleColumn> {
    let log_size = padded_log_size(active_rows);
    let padded_rows = 1usize << log_size;
    let mut active = zeros(padded_rows);
    let mut coeff = zeros(padded_rows);
    let mut chunk = zeros(padded_rows);
    let mut term_active = term_columns(padded_rows);
    let mut lhs_index = term_columns(padded_rows);
    let mut rhs_index = term_columns(padded_rows);
    let mut digit_active = digit_columns(padded_rows);

    for (row, (row_coeff, row_chunk)) in coordinates.into_iter().enumerate() {
        let (pairs, term_count) = product_chunk_pairs(row_coeff, row_chunk);
        active[row] = one();
        coeff[row] = m31(row_coeff as u32);
        chunk[row] = m31(row_chunk as u32);
        for term in 0..term_count {
            term_active[term][row] = one();
            lhs_index[term][row] = m31(pairs[term].0 as u32);
            rhs_index[term][row] = m31(pairs[term].1 as u32);
        }
        for (offset, column) in digit_active.iter_mut().enumerate() {
            if row_coeff + offset < 2 * N_LIMBS {
                column[row] = one();
            }
        }
    }

    let mut columns = vec![
        column(
            ScalarModMulScheduleColumnIds::product_active(family),
            active,
        ),
        column(ScalarModMulScheduleColumnIds::product_coeff(family), coeff),
        column(ScalarModMulScheduleColumnIds::product_chunk(family), chunk),
    ];
    for term in 0..SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS {
        columns.push(column(
            ScalarModMulScheduleColumnIds::product_term_active(family, term),
            term_active[term].clone(),
        ));
        columns.push(column(
            ScalarModMulScheduleColumnIds::product_lhs_index(family, term),
            lhs_index[term].clone(),
        ));
        columns.push(column(
            ScalarModMulScheduleColumnIds::product_rhs_index(family, term),
            rhs_index[term].clone(),
        ));
    }
    for (offset, values) in digit_active.iter().enumerate() {
        columns.push(column(
            ScalarModMulScheduleColumnIds::product_digit_active(family, offset),
            values.clone(),
        ));
    }

    columns
}

fn qn_product_schedule(rows: &ScalarModMulMergedRows) -> Vec<ScalarModMulScheduleColumn> {
    let mut columns = product_schedule(
        ProductFamily::Qn,
        rows.qn_chunks_len(),
        rows.qn_chunks().map(|(_, row)| (row.coeff, row.chunk)),
    );
    let padded_rows = columns[0].values.len();
    let n_limbs = words_to_limbs(&P256_ORDER);
    let mut modulus_limb = term_columns(padded_rows);

    for (row, (_, chunk)) in rows.qn_chunks().enumerate() {
        let (pairs, term_count) = product_chunk_pairs(chunk.coeff, chunk.chunk);
        for (term, column) in modulus_limb.iter_mut().take(term_count).enumerate() {
            column[row] = m31(n_limbs[pairs[term].1]);
        }
    }

    for (term, values) in modulus_limb.iter().enumerate() {
        columns.push(column(
            ScalarModMulScheduleColumnIds::qn_modulus_limb(term),
            values.clone(),
        ));
    }
    columns
}

fn accumulator_schedule(rows: &ScalarModMulMergedRows) -> Vec<ScalarModMulScheduleColumn> {
    let log_size = padded_log_size(rows.accumulators_len());
    let padded_rows = 1usize << log_size;
    let mut active = zeros(padded_rows);
    let mut side = zeros(padded_rows);
    let mut digit = zeros(padded_rows);
    let mut term_active = accumulator_term_columns(padded_rows);
    let mut coeff = accumulator_term_columns(padded_rows);
    let mut chunk = accumulator_term_columns(padded_rows);
    let mut offset = accumulator_term_columns(padded_rows);

    for (row_index, (_, row)) in rows.accumulators().enumerate() {
        active[row_index] = one();
        side[row_index] = m31(row.side.relation_side());
        digit[row_index] = m31(row.digit_index as u32);
        for_each_digit_contribution(
            row.digit_index,
            |term, term_coeff, term_chunk, term_offset| {
                term_active[term][row_index] = one();
                coeff[term][row_index] = m31(term_coeff as u32);
                chunk[term][row_index] = m31(term_chunk as u32);
                offset[term][row_index] = m31(term_offset as u32);
            },
        );
    }

    let mut columns = vec![
        column(ScalarModMulScheduleColumnIds::accumulator_active(), active),
        column(ScalarModMulScheduleColumnIds::accumulator_side(), side),
        column(ScalarModMulScheduleColumnIds::accumulator_digit(), digit),
    ];
    for term in 0..PRODUCT_DIGIT_ACCUMULATOR_TERMS {
        columns.push(column(
            ScalarModMulScheduleColumnIds::accumulator_term_active(term),
            term_active[term].clone(),
        ));
        columns.push(column(
            ScalarModMulScheduleColumnIds::accumulator_coeff(term),
            coeff[term].clone(),
        ));
        columns.push(column(
            ScalarModMulScheduleColumnIds::accumulator_chunk(term),
            chunk[term].clone(),
        ));
        columns.push(column(
            ScalarModMulScheduleColumnIds::accumulator_offset(term),
            offset[term].clone(),
        ));
    }
    columns
}

fn reduction_schedule(rows: &ScalarModMulMergedRows) -> Vec<ScalarModMulScheduleColumn> {
    let log_size = padded_log_size(rows.reduction_len());
    let padded_rows = 1usize << log_size;
    let mut active = zeros(padded_rows);
    let mut digit = zeros(padded_rows);
    let mut has_result_limb = zeros(padded_rows);
    let mut has_prev_carry = zeros(padded_rows);
    let mut has_next_carry = zeros(padded_rows);

    for (row_index, (_, row)) in rows.reduction_digits().enumerate() {
        active[row_index] = one();
        digit[row_index] = m31(row.digit_index as u32);
        if row.digit_index < N_LIMBS {
            has_result_limb[row_index] = one();
        }
        if row.digit_index > 0 {
            has_prev_carry[row_index] = one();
        }
        if row.digit_index + 1 < 2 * N_LIMBS {
            has_next_carry[row_index] = one();
        }
    }

    vec![
        column(ScalarModMulScheduleColumnIds::reduction_active(), active),
        column(ScalarModMulScheduleColumnIds::reduction_digit(), digit),
        column(
            ScalarModMulScheduleColumnIds::reduction_has_result_limb(),
            has_result_limb,
        ),
        column(
            ScalarModMulScheduleColumnIds::reduction_has_prev_carry(),
            has_prev_carry,
        ),
        column(
            ScalarModMulScheduleColumnIds::reduction_has_next_carry(),
            has_next_carry,
        ),
    ]
}

fn canonical_limb_multiplicity(role: ScalarModMulLimbRole) -> u32 {
    match role {
        ScalarModMulLimbRole::A | ScalarModMulLimbRole::B | ScalarModMulLimbRole::Quotient => {
            PRODUCT_SCALAR_LIMB_USE_COUNT
        }
        ScalarModMulLimbRole::Result => 1,
    }
}

fn schedule_id(name: impl Into<String>) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("p256_scalar_mod_mul_schedule_{}", name.into()),
    }
}

fn column(id: PreProcessedColumnId, values: Vec<M31>) -> ScalarModMulScheduleColumn {
    ScalarModMulScheduleColumn { id, values }
}

fn zeros(len: usize) -> Vec<M31> {
    vec![M31::from_u32_unchecked(0); len]
}

fn term_columns(len: usize) -> [Vec<M31>; SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS] {
    core::array::from_fn(|_| zeros(len))
}

fn digit_columns(len: usize) -> [Vec<M31>; SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS] {
    core::array::from_fn(|_| zeros(len))
}

fn accumulator_term_columns(len: usize) -> [Vec<M31>; PRODUCT_DIGIT_ACCUMULATOR_TERMS] {
    core::array::from_fn(|_| zeros(len))
}

fn one() -> M31 {
    M31::from_u32_unchecked(1)
}

fn m31(value: u32) -> M31 {
    M31::from_u32_unchecked(value)
}

#[cfg(test)]
mod tests {
    use stwo_p256_utils::scalar_arithmetic::{ScalarFieldMulTrace, P256_ORDER};

    use super::super::{
        ScalarModMulTraceRows, ROLE_A, ROLE_B, ROLE_QUOTIENT, ROLE_RESULT,
    };
    use super::*;

    fn scalar(value: u64) -> [u64; 4] {
        [value, 0, 0, 0]
    }

    fn test_rows() -> ScalarModMulMergedRows {
        let trace = ScalarFieldMulTrace::new("test_mul", &scalar(7), &scalar(11), &P256_ORDER)
            .expect("valid scalar mod-mul trace");
        ScalarModMulMergedRows::new(vec![
            ScalarModMulTraceRows::new(3, &trace).expect("trace rows generate"),
        ])
    }

    #[test]
    fn fixed_schedule_columns_are_padded_per_family() {
        let schedule = ScalarModMulFixedSchedule::from_rows(&test_rows());

        assert_eq!(schedule.canonical[0].values.len(), 1 << padded_log_size(4));
        assert_eq!(schedule.ab_chunks[0].values.len(), 256);
        assert_eq!(schedule.qn_chunks[0].values.len(), 256);
        assert_eq!(schedule.accumulators[0].values.len(), 128);
        assert_eq!(schedule.reduction_digits[0].values.len(), 64);
    }

    #[test]
    fn fixed_schedule_qn_modulus_limb_depends_on_row_pair() {
        let rows = test_rows();
        let schedule = ScalarModMulFixedSchedule::from_rows(&rows);
        let n_limbs = words_to_limbs(&P256_ORDER);
        let first_modulus_column = schedule
            .qn_chunks
            .iter()
            .find(|column| column.id == ScalarModMulScheduleColumnIds::qn_modulus_limb(0))
            .expect("qn modulus limb column exists");

        assert_eq!(first_modulus_column.values[0], m31(n_limbs[0]));
        let row_with_shifted_modulus = rows
            .qn_chunks()
            .position(|(_, row)| product_chunk_pairs(row.coeff, row.chunk).0[0].1 == 1)
            .expect("schedule eventually uses n limb 1");
        assert_eq!(
            first_modulus_column.values[row_with_shifted_modulus],
            m31(n_limbs[1])
        );
    }

    #[test]
    fn fixed_schedule_uses_distinct_relation_roles() {
        let schedule = ScalarModMulFixedSchedule::from_rows(&test_rows());
        let role_column = schedule
            .canonical
            .iter()
            .find(|column| column.id == ScalarModMulScheduleColumnIds::canonical_role())
            .expect("role column exists");

        assert_eq!(
            role_column.values[..4],
            [ROLE_A, ROLE_B, ROLE_QUOTIENT, ROLE_RESULT].map(m31)
        );
    }

    #[test]
    fn fixed_schedule_materializes_circle_evaluations() {
        let schedule = ScalarModMulFixedSchedule::from_rows(&test_rows());
        let evals = schedule.to_circle_evaluations();

        assert_eq!(evals.canonical.len(), schedule.canonical.len());
        assert_eq!(evals.ab_chunks.len(), schedule.ab_chunks.len());
        assert_eq!(evals.qn_chunks.len(), schedule.qn_chunks.len());
        assert_eq!(evals.accumulators.len(), schedule.accumulators.len());
        assert_eq!(
            evals.reduction_digits.len(),
            schedule.reduction_digits.len()
        );
        assert_eq!(evals.canonical[0].domain.size(), 1 << padded_log_size(4));
        assert_eq!(evals.ab_chunks[0].domain.size(), 256);
        assert_eq!(evals.qn_chunks[0].domain.size(), 256);
        assert_eq!(evals.accumulators[0].domain.size(), 128);
        assert_eq!(evals.reduction_digits[0].domain.size(), 64);
    }
}
