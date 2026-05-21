pub mod canonical;
pub mod product;
pub mod reduction;

use stwo::core::fields::m31::M31;
use stwo_constraint_framework::{relation, EvalAtRow, RelationEntry};
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};
use stwo_p256_utils::scalar_arithmetic::{
    FNMUL_CHUNK_TERMS, PRODUCT_CHUNKS, PRODUCT_COEFFICIENTS, PRODUCT_EQUATION_LIMBS,
};

use crate::limbs::P256EvalBigInt;

pub use canonical::{add_canonical_lt_n_provider, CanonicalLtNColumns, CanonicalLtNRelations};
pub use product::{add_scalar_product_provider, ScalarProductColumns, ScalarProductRelations};
pub use reduction::{
    add_scalar_reduction_consumer, ScalarReductionColumns, ScalarReductionRelations,
};

relation!(ScalarValueRelation, 22);
relation!(ScalarProductDigitRelation, 4);

pub const FNMUL_SPLIT_CHUNK_TERMS: usize = FNMUL_CHUNK_TERMS;
pub const FNMUL_SPLIT_PRODUCT_CHUNKS: usize = PRODUCT_CHUNKS;
pub const FNMUL_SPLIT_CHUNK_DIGITS: usize = 3;
pub const FNMUL_SPLIT_CHUNK_TOP_DIGIT_BOUND: i64 = 1;
pub const FNMUL_SPLIT_CARRY_BOUND: i64 = split_digit_carry_bound();
pub const M31_CENTERED_BOUND: i64 = (1i64 << 30) - 1;

pub const ROLE_A: u32 = 0;
pub const ROLE_B: u32 = 1;
pub const ROLE_RESULT: u32 = 2;
pub const ROLE_QUOTIENT: u32 = 3;

pub const SIDE_AB: u32 = 0;
pub const SIDE_QN: u32 = 1;

const LIMB_BOUND: i64 = 1i64 << LIMB_BITS;

pub struct SplitChunkColumns<E: EvalAtRow> {
    pub digits: [E::F; FNMUL_SPLIT_CHUNK_DIGITS],
}

#[derive(Clone, Copy)]
pub struct FnMulRelationIds<'a> {
    pub scalar_value: &'a ScalarValueRelation,
    pub product_digit: &'a ScalarProductDigitRelation,
}

/// Worst-case absolute value of a split product chunk decomposition:
///
/// ```text
/// sum(a_i*b_i for up to 2 terms) - d0 - B*d1 - B^2*d2 = 0
/// ```
///
/// with `d0,d1 < B` and `d2 in {0,1}`.
pub const fn split_chunk_max_abs_expr() -> i64 {
    let product = (LIMB_BOUND - 1) * (LIMB_BOUND - 1);
    FNMUL_SPLIT_CHUNK_TERMS as i64 * product
        + (LIMB_BOUND - 1)
        + LIMB_BOUND * (LIMB_BOUND - 1)
        + LIMB_BOUND * LIMB_BOUND * FNMUL_SPLIT_CHUNK_TOP_DIGIT_BOUND
}

/// Conservative worst-case absolute value of the normalized split digit
/// equation:
///
/// ```text
/// ab_digit - qn_digit - result_digit + carry_in - B*carry_out = 0
/// ```
pub const fn split_digit_max_abs_expr() -> i64 {
    let diff_bound = split_digit_diff_bound();
    let carry_bound = split_digit_carry_bound();
    diff_bound + carry_bound + LIMB_BOUND * carry_bound
}

pub const fn split_digit_carry_bound() -> i64 {
    let diff_bound = split_digit_diff_bound();
    (diff_bound + LIMB_BOUND - 1) / LIMB_BOUND
}

const fn split_digit_diff_bound() -> i64 {
    let product_digit_bound = split_product_digit_bound();
    2 * product_digit_bound + (LIMB_BOUND - 1)
}

const fn split_product_digit_bound() -> i64 {
    let chunks_per_coeff =
        (N_LIMBS as i64 + FNMUL_SPLIT_CHUNK_TERMS as i64 - 1) / FNMUL_SPLIT_CHUNK_TERMS as i64;
    3 * chunks_per_coeff * (LIMB_BOUND - 1) + chunks_per_coeff
}

pub fn split_fnmul_fits_m31_centered() -> bool {
    split_chunk_max_abs_expr() < M31_CENTERED_BOUND
        && split_digit_max_abs_expr() < M31_CENTERED_BOUND
}

fn provide_scalar_value<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarValueRelation,
    gate: E::F,
    mul_id: E::F,
    role: u32,
    value: &P256EvalBigInt<E>,
) {
    add_scalar_value_relation(eval, relation, -E::EF::from(gate), mul_id, role, value);
}

fn consume_scalar_value<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarValueRelation,
    gate: E::F,
    mul_id: E::F,
    role: u32,
    value: &P256EvalBigInt<E>,
) {
    add_scalar_value_relation(eval, relation, E::EF::from(gate), mul_id, role, value);
}

fn provide_product_digit<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarProductDigitRelation,
    gate: E::F,
    mul_id: E::F,
    side: u32,
    digit_index: usize,
    digit_value: E::F,
) {
    add_product_digit_relation(
        eval,
        relation,
        -E::EF::from(gate),
        mul_id,
        side,
        digit_index,
        digit_value,
    );
}

fn consume_product_digit<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarProductDigitRelation,
    gate: E::F,
    mul_id: E::F,
    side: u32,
    digit_index: usize,
    digit_value: E::F,
) {
    add_product_digit_relation(
        eval,
        relation,
        E::EF::from(gate),
        mul_id,
        side,
        digit_index,
        digit_value,
    );
}

fn add_scalar_value_relation<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarValueRelation,
    numerator: E::EF,
    mul_id: E::F,
    role: u32,
    value: &P256EvalBigInt<E>,
) {
    let values: [E::F; 2 + N_LIMBS] = core::array::from_fn(|i| match i {
        0 => mul_id.clone(),
        1 => E::F::from(M31::from_u32_unchecked(role)),
        _ => value.limbs()[i - 2].clone(),
    });
    eval.add_to_relation(RelationEntry::new(relation, numerator, &values));
}

fn add_product_digit_relation<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarProductDigitRelation,
    numerator: E::EF,
    mul_id: E::F,
    side: u32,
    digit_index: usize,
    digit_value: E::F,
) {
    let values = [
        mul_id,
        E::F::from(M31::from_u32_unchecked(side)),
        E::F::from(M31::from_u32_unchecked(digit_index as u32)),
        digit_value,
    ];
    eval.add_to_relation(RelationEntry::new(relation, numerator, &values));
}

fn add_chunk_digit_constraints<E: EvalAtRow>(
    eval: &mut E,
    range13: &crate::range_checks::RangeCheckRelation,
    gate: E::F,
    chunk: &SplitChunkColumns<E>,
) {
    let one = E::F::from(M31::from_u32_unchecked(1));
    crate::range_checks::add_range_check(eval, range13, gate.clone(), chunk.digits[0].clone());
    crate::range_checks::add_range_check(eval, range13, gate.clone(), chunk.digits[1].clone());
    eval.add_constraint(gate * chunk.digits[2].clone() * (chunk.digits[2].clone() - one));
}

fn add_chunk_decomposition<E: EvalAtRow>(
    eval: &mut E,
    gate: E::F,
    product_sum: E::F,
    chunk: &SplitChunkColumns<E>,
) {
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    let decomposition = product_sum
        - chunk.digits[0].clone()
        - limb_base.clone() * chunk.digits[1].clone()
        - limb_base.clone() * limb_base * chunk.digits[2].clone();
    eval.add_constraint(gate * decomposition);
}

fn split_digit_expr<E: EvalAtRow>(
    chunks: &[SplitChunkColumns<E>; FNMUL_SPLIT_PRODUCT_CHUNKS],
    digit: usize,
) -> E::F {
    let mut acc = E::F::from(M31::from_u32_unchecked(0));
    let start_coeff = digit.saturating_sub(FNMUL_SPLIT_CHUNK_DIGITS - 1);
    let end_coeff = digit.min(PRODUCT_COEFFICIENTS - 1);
    for coeff in start_coeff..=end_coeff {
        let offset = digit - coeff;
        let first_chunk = first_chunk_index(coeff);
        let chunk_count = coefficient_chunk_count(coeff);
        for chunk in chunks.iter().skip(first_chunk).take(chunk_count) {
            acc += chunk.digits[offset].clone();
        }
    }
    acc
}

fn for_each_product_chunk(mut f: impl FnMut(usize, usize, &[(usize, usize)])) {
    let mut chunk_index = 0usize;
    for coeff in 0..PRODUCT_COEFFICIENTS {
        let mut pairs = [(0usize, 0usize); FNMUL_SPLIT_CHUNK_TERMS];
        let mut pair_count = 0usize;
        for pair in coefficient_pairs(coeff) {
            pairs[pair_count] = pair;
            pair_count += 1;
            if pair_count == FNMUL_SPLIT_CHUNK_TERMS {
                f(chunk_index, coeff, &pairs[..pair_count]);
                chunk_index += 1;
                pair_count = 0;
            }
        }
        if pair_count > 0 {
            f(chunk_index, coeff, &pairs[..pair_count]);
            chunk_index += 1;
        }
    }
    debug_assert_eq!(chunk_index, FNMUL_SPLIT_PRODUCT_CHUNKS);
}

fn coefficient_pairs(coeff: usize) -> impl Iterator<Item = (usize, usize)> {
    let start = coeff.saturating_sub(N_LIMBS - 1);
    let end = coeff.min(N_LIMBS - 1);
    (start..=end).map(move |i| (i, coeff - i))
}

fn first_chunk_index(coeff: usize) -> usize {
    (0..coeff).map(coefficient_chunk_count).sum()
}

fn coefficient_chunk_count(coeff: usize) -> usize {
    coefficient_term_count(coeff).div_ceil(FNMUL_SPLIT_CHUNK_TERMS)
}

fn coefficient_term_count(coeff: usize) -> usize {
    if coeff < N_LIMBS {
        coeff + 1
    } else {
        PRODUCT_COEFFICIENTS - coeff
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use stwo_p256_utils::scalar_arithmetic::{FnMulTrace, SplitProductTrace, P256_ORDER};

    #[test]
    fn split_fnmul_chunk_constraints_fit_m31_centered() {
        assert!(split_chunk_max_abs_expr() < M31_CENTERED_BOUND);
    }

    #[test]
    fn split_fnmul_digit_constraints_fit_m31_centered() {
        assert!(split_digit_max_abs_expr() < M31_CENTERED_BOUND);
    }

    #[test]
    fn split_fnmul_carry_bound_is_tight_for_headroom_formula() {
        assert_eq!(FNMUL_SPLIT_CARRY_BOUND, 61);
        assert_eq!(
            split_digit_max_abs_expr(),
            split_digit_diff_bound()
                + FNMUL_SPLIT_CARRY_BOUND
                + LIMB_BOUND * FNMUL_SPLIT_CARRY_BOUND
        );
    }

    #[test]
    fn split_fnmul_uses_expected_chunk_count() {
        assert_eq!(FNMUL_SPLIT_PRODUCT_CHUNKS, 210);
        assert_eq!(FNMUL_SPLIT_CHUNK_TERMS, 2);
        assert!(split_fnmul_fits_m31_centered());
    }

    #[test]
    fn split_fnmul_trace_carries_fit_audited_bound() {
        let mut max_scalar = P256_ORDER;
        max_scalar[0] -= 1;
        let mul = FnMulTrace::new(&max_scalar, &max_scalar, &P256_ORDER)
            .expect("valid multiplication trace");
        let split = SplitProductTrace::new(&mul);

        assert!(split
            .carries
            .iter()
            .all(|&carry| (-FNMUL_SPLIT_CARRY_BOUND..=FNMUL_SPLIT_CARRY_BOUND).contains(&carry)));
    }

    #[test]
    fn product_chunk_metadata_matches_shape() {
        let mut chunks = 0usize;
        for_each_product_chunk(|chunk_index, coeff, pairs| {
            assert_eq!(chunk_index, chunks);
            assert!(!pairs.is_empty());
            assert!(pairs.len() <= FNMUL_SPLIT_CHUNK_TERMS);
            assert_eq!(
                pairs.len(),
                coefficient_chunk_term_count(coeff, chunk_index)
            );
            chunks += 1;
        });
        assert_eq!(chunks, FNMUL_SPLIT_PRODUCT_CHUNKS);
    }

    fn coefficient_chunk_term_count(coeff: usize, global_chunk: usize) -> usize {
        let first = first_chunk_index(coeff);
        let local = global_chunk - first;
        let term_count = coefficient_term_count(coeff);
        let consumed = local * FNMUL_SPLIT_CHUNK_TERMS;
        (term_count - consumed).min(FNMUL_SPLIT_CHUNK_TERMS)
    }
}
