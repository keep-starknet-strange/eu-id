use stwo::core::fields::m31::M31;
use stwo_constraint_framework::EvalAtRow;
use stwo_p256_utils::scalar_arithmetic::{words_to_limbs, BigIntLimbs, P256_ORDER};

use crate::limbs::P256EvalBigInt;
use crate::range_checks::RangeCheckRelation;

use super::{
    add_chunk_decomposition, add_chunk_digit_constraints, consume_scalar_value,
    for_each_product_chunk, provide_product_digit, split_digit_expr, FnMulLinkRelations,
    SplitChunkColumns, FNMUL_SPLIT_PRODUCT_CHUNKS, PRODUCT_EQUATION_LIMBS, ROLE_A, ROLE_B,
    ROLE_QUOTIENT, SIDE_AB, SIDE_QN,
};

/// Aggregate split-product row.
///
/// This is intentionally separated from canonicality and reduction rows, but
/// it is still a wide aggregate helper: it proves all `A*B` and `Q*n` chunks
/// for one multiplication instance. A narrower physical component can later
/// split this shape by coefficient/chunk while preserving the same relation
/// contract.
pub struct ScalarProductColumns<E: EvalAtRow> {
    /// Multiplicand consumed from the canonical scalar relation as role `A`.
    pub a: P256EvalBigInt<E>,
    /// Multiplier consumed from the canonical scalar relation as role `B`.
    pub b: P256EvalBigInt<E>,
    /// Quotient consumed from the canonical scalar relation as role `QUOTIENT`.
    pub quotient: P256EvalBigInt<E>,
    /// Split chunks for `A * B`.
    pub ab_chunks: [SplitChunkColumns<E>; FNMUL_SPLIT_PRODUCT_CHUNKS],
    /// Split chunks for `quotient * n`.
    pub qn_chunks: [SplitChunkColumns<E>; FNMUL_SPLIT_PRODUCT_CHUNKS],
}

#[derive(Clone, Copy)]
pub struct ScalarProductRelations<'a> {
    /// 13-bit range table for low and middle split-chunk digits.
    pub range13: &'a RangeCheckRelation,
    /// LogUp links to canonical scalar providers and reduction consumers.
    pub links: FnMulLinkRelations<'a>,
}

/// Prove split product chunks for `A*B` and `Q*n`, then provide normalized
/// product digits keyed by `(mul_id, side, digit_index)`.
///
/// The helper consumes canonical `A`, `B`, and `quotient` values under the
/// same `mul_id`. It does not range-check those columns locally; their range
/// and canonicality come from matching scalar providers.
pub fn add_scalar_product_provider<E: EvalAtRow>(
    eval: &mut E,
    relations: ScalarProductRelations<'_>,
    gate: E::F,
    mul_id: E::F,
    columns: &ScalarProductColumns<E>,
) {
    consume_scalar_value(
        eval,
        relations.links.scalar_value,
        gate.clone(),
        mul_id.clone(),
        ROLE_A,
        &columns.a,
    );
    consume_scalar_value(
        eval,
        relations.links.scalar_value,
        gate.clone(),
        mul_id.clone(),
        ROLE_B,
        &columns.b,
    );
    consume_scalar_value(
        eval,
        relations.links.scalar_value,
        gate.clone(),
        mul_id.clone(),
        ROLE_QUOTIENT,
        &columns.quotient,
    );

    add_eval_product_chunks(
        eval,
        relations.range13,
        gate.clone(),
        &columns.a,
        &columns.b,
        &columns.ab_chunks,
    );

    let n_limbs = words_to_limbs(&P256_ORDER);
    add_fixed_rhs_product_chunks(
        eval,
        relations.range13,
        gate.clone(),
        &columns.quotient,
        &n_limbs,
        &columns.qn_chunks,
    );

    for digit in 0..PRODUCT_EQUATION_LIMBS {
        provide_product_digit(
            eval,
            relations.links.product_digit,
            gate.clone(),
            mul_id.clone(),
            SIDE_AB,
            digit,
            split_digit_expr(&columns.ab_chunks, digit),
        );
        provide_product_digit(
            eval,
            relations.links.product_digit,
            gate.clone(),
            mul_id.clone(),
            SIDE_QN,
            digit,
            split_digit_expr(&columns.qn_chunks, digit),
        );
    }
}

fn add_eval_product_chunks<E: EvalAtRow>(
    eval: &mut E,
    range13: &RangeCheckRelation,
    gate: E::F,
    lhs: &P256EvalBigInt<E>,
    rhs: &P256EvalBigInt<E>,
    chunks: &[SplitChunkColumns<E>; FNMUL_SPLIT_PRODUCT_CHUNKS],
) {
    for_each_product_chunk(|chunk_index, _coeff, pairs| {
        add_chunk_digit_constraints(eval, range13, gate.clone(), &chunks[chunk_index]);
        let product_sum = pairs
            .iter()
            .fold(E::F::from(M31::from_u32_unchecked(0)), |acc, &(i, j)| {
                acc + lhs.limbs()[i].clone() * rhs.limbs()[j].clone()
            });
        add_chunk_decomposition(eval, gate.clone(), product_sum, &chunks[chunk_index]);
    });
}

fn add_fixed_rhs_product_chunks<E: EvalAtRow>(
    eval: &mut E,
    range13: &RangeCheckRelation,
    gate: E::F,
    lhs: &P256EvalBigInt<E>,
    rhs: &BigIntLimbs,
    chunks: &[SplitChunkColumns<E>; FNMUL_SPLIT_PRODUCT_CHUNKS],
) {
    for_each_product_chunk(|chunk_index, _coeff, pairs| {
        add_chunk_digit_constraints(eval, range13, gate.clone(), &chunks[chunk_index]);
        let product_sum =
            pairs
                .iter()
                .fold(E::F::from(M31::from_u32_unchecked(0)), |acc, &(i, j)| {
                    acc + lhs.limbs()[i].clone() * E::F::from(M31::from_u32_unchecked(rhs[j]))
                });
        add_chunk_decomposition(eval, gate.clone(), product_sum, &chunks[chunk_index]);
    });
}
