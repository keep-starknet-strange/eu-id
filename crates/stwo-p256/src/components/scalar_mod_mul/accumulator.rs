use stwo::core::fields::m31::M31;
use stwo_constraint_framework::EvalAtRow;
use stwo_p256_utils::constants::N_LIMBS;
use stwo_p256_utils::scalar_arithmetic::PRODUCT_EQUATION_LIMBS;

use super::{
    consume_product_chunk_digit, provide_product_digit, ProductChunkCoordinate, ProductSide,
    ScalarProductChunkDigitRelation, ScalarProductDigitRelation,
    PRODUCT_DIGIT_ACCUMULATOR_MAX_TERMS, SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS,
    SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS,
};

pub const PRODUCT_DIGIT_ACCUMULATOR_TERMS: usize = PRODUCT_DIGIT_ACCUMULATOR_MAX_TERMS;

pub struct ProductDigitAccumulatorColumns<E: EvalAtRow> {
    pub terms: [E::F; PRODUCT_DIGIT_ACCUMULATOR_TERMS],
    pub product_digit: E::F,
}

#[derive(Clone, Copy)]
pub struct ProductDigitAccumulatorRelations<'a> {
    pub product_chunk_digit: &'a ScalarProductChunkDigitRelation,
    pub product_digit: &'a ScalarProductDigitRelation,
}

/// Accumulate chunk digits into one normalized product digit.
///
/// For fixed `(mul_id, side, digit_index)`, this consumes every chunk digit
/// whose `(coeff + digit_offset)` contributes to that product digit and
/// provides the existing product-digit relation consumed by reduction.
pub fn add_product_digit_accumulator<E: EvalAtRow>(
    eval: &mut E,
    relations: ProductDigitAccumulatorRelations<'_>,
    gate: E::F,
    mul_id: E::F,
    side: ProductSide,
    digit_index: usize,
    columns: &ProductDigitAccumulatorColumns<E>,
) {
    assert!(
        digit_index < PRODUCT_EQUATION_LIMBS,
        "product digit index {digit_index} outside 0..{PRODUCT_EQUATION_LIMBS}",
    );

    let relation_side = side.relation_side();
    let mut acc = E::F::from(M31::from_u32_unchecked(0));
    let term_count =
        for_each_digit_contribution(digit_index, |term_index, coeff, chunk, offset| {
            let term = columns.terms[term_index].clone();
            consume_product_chunk_digit(
                eval,
                relations.product_chunk_digit,
                gate.clone(),
                mul_id.clone(),
                ProductChunkCoordinate {
                    side: relation_side,
                    coeff,
                    chunk,
                },
                offset,
                term.clone(),
            );
            acc += term;
        });

    for term in columns.terms.iter().skip(term_count) {
        eval.add_constraint(gate.clone() * term.clone());
    }
    eval.add_constraint(gate.clone() * (acc - columns.product_digit.clone()));
    provide_product_digit(
        eval,
        relations.product_digit,
        gate,
        mul_id,
        relation_side,
        digit_index,
        columns.product_digit.clone(),
    );
}

pub(super) fn for_each_digit_contribution(
    digit_index: usize,
    mut f: impl FnMut(usize, usize, usize, usize),
) -> usize {
    let mut term_index = 0usize;
    let start_coeff = digit_index.saturating_sub(SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS - 1);
    let end_coeff = digit_index.min(PRODUCT_EQUATION_LIMBS - 2);
    for coeff in start_coeff..=end_coeff {
        let offset = digit_index - coeff;
        let chunk_count = coefficient_chunk_count(coeff);
        for chunk in 0..chunk_count {
            f(term_index, coeff, chunk, offset);
            term_index += 1;
        }
    }
    debug_assert!(term_index <= PRODUCT_DIGIT_ACCUMULATOR_TERMS);
    term_index
}

const fn coefficient_chunk_count(coeff: usize) -> usize {
    coefficient_term_count(coeff).div_ceil(SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS)
}

const fn coefficient_term_count(coeff: usize) -> usize {
    if coeff < N_LIMBS {
        coeff + 1
    } else {
        PRODUCT_EQUATION_LIMBS - 1 - coeff
    }
}

#[cfg(test)]
mod tests {
    use super::super::chunk_product::PRODUCT_CHUNK_DIGIT_ENTRIES_PER_SIDE;
    use super::super::PRODUCT_CHUNKS_PER_COEFFICIENT;
    use super::*;

    #[test]
    fn accumulator_term_bound_covers_every_product_digit() {
        let mut max_terms = 0usize;
        for digit in 0..PRODUCT_EQUATION_LIMBS {
            let term_count = for_each_digit_contribution(digit, |_, _, _, _| {});
            max_terms = max_terms.max(term_count);
            assert!(term_count <= PRODUCT_DIGIT_ACCUMULATOR_TERMS);
        }

        assert_eq!(PRODUCT_DIGIT_ACCUMULATOR_TERMS, 30);
        assert_eq!(max_terms, PRODUCT_DIGIT_ACCUMULATOR_TERMS);
    }

    #[test]
    fn accumulator_consumes_all_chunk_digit_entries_per_side() {
        let mut uses = 0usize;
        for digit in 0..PRODUCT_EQUATION_LIMBS {
            uses += for_each_digit_contribution(digit, |_, _, _, _| {});
        }

        assert_eq!(uses, PRODUCT_CHUNK_DIGIT_ENTRIES_PER_SIDE);
    }

    #[test]
    fn accumulator_metadata_stays_inside_chunk_shape() {
        for digit in 0..PRODUCT_EQUATION_LIMBS {
            for_each_digit_contribution(digit, |_, coeff, chunk, offset| {
                assert!(coeff < PRODUCT_EQUATION_LIMBS - 1);
                assert!(chunk < PRODUCT_CHUNKS_PER_COEFFICIENT);
                assert!(offset < SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS);
            });
        }
        assert_eq!(PRODUCT_CHUNKS_PER_COEFFICIENT, N_LIMBS / 2);
    }
}
