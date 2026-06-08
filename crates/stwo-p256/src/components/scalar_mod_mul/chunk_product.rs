use stwo::core::fields::m31::M31;
use stwo_constraint_framework::EvalAtRow;
use stwo_p256_utils::scalar_arithmetic::{words_to_limbs, P256_ORDER, PRODUCT_EQUATION_LIMBS};

use crate::range_checks::RangeCheckRelation;

use super::{
    add_chunk_decomposition, add_chunk_digit_constraints, consume_scalar_limb, product_chunk_pairs,
    provide_product_chunk_digit, ProductChunkCoordinate, ScalarModMulChunkLinkRelations,
    SplitChunkColumns, ROLE_A, ROLE_B, ROLE_QUOTIENT, SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS,
    SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS, SCALAR_MOD_MUL_SPLIT_PRODUCT_CHUNKS, SIDE_AB, SIDE_QN,
};

pub const AB_PRODUCT_CHUNK_TRACE_COLUMNS: usize =
    2 * SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS + SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS;
pub const QN_PRODUCT_CHUNK_TRACE_COLUMNS: usize =
    SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS + SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS;
pub const PRODUCT_CHUNK_DIGIT_ENTRIES_PER_SIDE: usize =
    SCALAR_MOD_MUL_SPLIT_PRODUCT_CHUNKS * SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS - 1;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProductSide {
    Ab,
    Qn,
}

impl ProductSide {
    pub const fn relation_side(self) -> u32 {
        match self {
            Self::Ab => SIDE_AB,
            Self::Qn => SIDE_QN,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProductChunkMeta {
    pub side: ProductSide,
    pub coeff: usize,
    pub chunk: usize,
}

impl ProductChunkMeta {
    pub fn new(side: ProductSide, coeff: usize, chunk: usize) -> Self {
        let (_, term_count) = product_chunk_pairs(coeff, chunk);
        assert!(
            term_count > 0,
            "invalid product chunk coeff={coeff} chunk={chunk}",
        );
        Self { side, coeff, chunk }
    }

    fn coordinate(self) -> ProductChunkCoordinate {
        ProductChunkCoordinate {
            side: self.side.relation_side(),
            coeff: self.coeff,
            chunk: self.chunk,
        }
    }

    fn term_pairs(self) -> ([(usize, usize); SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS], usize) {
        product_chunk_pairs(self.coeff, self.chunk)
    }
}

pub struct ProductTermColumns<E: EvalAtRow> {
    pub lhs: E::F,
    pub rhs: E::F,
}

/// Narrow row for one split `A * B` product chunk.
pub struct VariableProductChunkColumns<E: EvalAtRow> {
    pub terms: [ProductTermColumns<E>; SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS],
    pub chunk: SplitChunkColumns<E>,
}

/// Narrow row for one split `Q * n` product chunk.
pub struct QnProductChunkColumns<E: EvalAtRow> {
    pub quotient_limbs: [E::F; SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS],
    pub chunk: SplitChunkColumns<E>,
}

#[derive(Clone, Copy)]
pub struct ProductChunkLinkRelations<'a> {
    pub range13: &'a RangeCheckRelation,
    pub links: ScalarModMulChunkLinkRelations<'a>,
}

/// Prove one chunk of `A * B` and provide its three chunk digits.
///
/// The term limb columns are not range-checked locally. They are consumed from
/// canonical scalar limb providers using `(mul_id, role, limb_index, value)`.
pub fn add_ab_product_chunk_provider<E: EvalAtRow>(
    eval: &mut E,
    relations: ProductChunkLinkRelations<'_>,
    gate: E::F,
    mul_id: E::F,
    meta: ProductChunkMeta,
    columns: &VariableProductChunkColumns<E>,
) {
    assert_eq!(
        meta.side,
        ProductSide::Ab,
        "AB product chunk requires AB side"
    );
    let (pairs, term_count) = meta.term_pairs();

    let mut product_sum = E::F::from(M31::from_u32_unchecked(0));
    for (term, &(lhs_index, rhs_index)) in columns.terms.iter().zip(&pairs).take(term_count) {
        consume_scalar_limb(
            eval,
            relations.links.scalar_limb,
            gate.clone(),
            mul_id.clone(),
            ROLE_A,
            lhs_index,
            term.lhs.clone(),
        );
        consume_scalar_limb(
            eval,
            relations.links.scalar_limb,
            gate.clone(),
            mul_id.clone(),
            ROLE_B,
            rhs_index,
            term.rhs.clone(),
        );
        product_sum += term.lhs.clone() * term.rhs.clone();
    }
    constrain_unused_variable_terms(eval, gate.clone(), columns, term_count);
    finish_product_chunk(
        eval,
        relations,
        gate,
        mul_id,
        meta,
        product_sum,
        &columns.chunk,
    );
}

/// Prove one chunk of `Q * n` and provide its three chunk digits.
pub fn add_qn_product_chunk_provider<E: EvalAtRow>(
    eval: &mut E,
    relations: ProductChunkLinkRelations<'_>,
    gate: E::F,
    mul_id: E::F,
    meta: ProductChunkMeta,
    columns: &QnProductChunkColumns<E>,
) {
    assert_eq!(
        meta.side,
        ProductSide::Qn,
        "QN product chunk requires QN side"
    );
    let (pairs, term_count) = meta.term_pairs();
    let n_limbs = words_to_limbs(&P256_ORDER);

    let mut product_sum = E::F::from(M31::from_u32_unchecked(0));
    for (quotient_limb, &(lhs_index, rhs_index)) in
        columns.quotient_limbs.iter().zip(&pairs).take(term_count)
    {
        consume_scalar_limb(
            eval,
            relations.links.scalar_limb,
            gate.clone(),
            mul_id.clone(),
            ROLE_QUOTIENT,
            lhs_index,
            quotient_limb.clone(),
        );
        product_sum +=
            quotient_limb.clone() * E::F::from(M31::from_u32_unchecked(n_limbs[rhs_index]));
    }
    constrain_unused_qn_terms(eval, gate.clone(), columns, term_count);
    finish_product_chunk(
        eval,
        relations,
        gate,
        mul_id,
        meta,
        product_sum,
        &columns.chunk,
    );
}

fn finish_product_chunk<E: EvalAtRow>(
    eval: &mut E,
    relations: ProductChunkLinkRelations<'_>,
    gate: E::F,
    mul_id: E::F,
    meta: ProductChunkMeta,
    product_sum: E::F,
    chunk: &SplitChunkColumns<E>,
) {
    add_chunk_digit_constraints(eval, relations.range13, gate.clone(), chunk);
    add_chunk_decomposition(eval, gate.clone(), product_sum, chunk);
    provide_chunk_digits(eval, relations.links, gate, mul_id, meta, chunk);
}

fn provide_chunk_digits<E: EvalAtRow>(
    eval: &mut E,
    links: ScalarModMulChunkLinkRelations<'_>,
    gate: E::F,
    mul_id: E::F,
    meta: ProductChunkMeta,
    chunk: &SplitChunkColumns<E>,
) {
    for (offset, digit) in chunk.digits.iter().enumerate() {
        if meta.coeff + offset >= PRODUCT_EQUATION_LIMBS {
            continue;
        }
        provide_product_chunk_digit(
            eval,
            links.product_chunk_digit,
            gate.clone(),
            mul_id.clone(),
            meta.coordinate(),
            offset,
            digit.clone(),
        );
    }
}

fn constrain_unused_variable_terms<E: EvalAtRow>(
    eval: &mut E,
    gate: E::F,
    columns: &VariableProductChunkColumns<E>,
    term_count: usize,
) {
    for term in columns.terms.iter().skip(term_count) {
        eval.add_constraint(gate.clone() * term.lhs.clone());
        eval.add_constraint(gate.clone() * term.rhs.clone());
    }
}

fn constrain_unused_qn_terms<E: EvalAtRow>(
    eval: &mut E,
    gate: E::F,
    columns: &QnProductChunkColumns<E>,
    term_count: usize,
) {
    for quotient_limb in columns.quotient_limbs.iter().skip(term_count) {
        eval.add_constraint(gate.clone() * quotient_limb.clone());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use stwo_p256_utils::constants::N_LIMBS;
    use stwo_p256_utils::scalar_arithmetic::{FnMulTrace, SplitProductTrace};

    #[test]
    fn narrow_product_chunk_rows_are_small() {
        let aggregate_product_columns = 3 * N_LIMBS
            + 2 * SCALAR_MOD_MUL_SPLIT_PRODUCT_CHUNKS * SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS;

        assert_eq!(AB_PRODUCT_CHUNK_TRACE_COLUMNS, 7);
        assert_eq!(QN_PRODUCT_CHUNK_TRACE_COLUMNS, 5);
        assert_eq!(aggregate_product_columns, 1320);
        assert_eq!(
            aggregate_product_columns / AB_PRODUCT_CHUNK_TRACE_COLUMNS,
            188
        );
    }

    #[test]
    fn product_chunk_metadata_matches_split_trace() {
        let scalar = [7, 0, 0, 0];
        let mul =
            FnMulTrace::new(&scalar, &scalar, &P256_ORDER).expect("valid multiplication trace");
        let split = SplitProductTrace::new(&mul);

        for chunk in &split.ab_chunks {
            let meta = ProductChunkMeta::new(ProductSide::Ab, chunk.coeff, chunk.chunk);
            let (_, term_count) = meta.term_pairs();
            assert_eq!(term_count, chunk.terms);
        }

        for chunk in &split.qn_chunks {
            let meta = ProductChunkMeta::new(ProductSide::Qn, chunk.coeff, chunk.chunk);
            let (_, term_count) = meta.term_pairs();
            assert_eq!(term_count, chunk.terms);
        }
    }

    #[test]
    fn product_chunk_digit_entries_are_not_aggregate_digits() {
        let aggregate_digits = 2 * N_LIMBS - 1;

        assert_eq!(aggregate_digits, 39);
        assert_eq!(PRODUCT_CHUNK_DIGIT_ENTRIES_PER_SIDE, 629);
    }
}
