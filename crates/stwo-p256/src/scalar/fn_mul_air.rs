use stwo::core::fields::m31::M31;
use stwo_constraint_framework::EvalAtRow;
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};
use stwo_p256_utils::scalar_arithmetic::{
    words_to_limbs, BigIntLimbs, FNMUL_CHUNK_TERMS, P256_ORDER, PRODUCT_CHUNKS,
    PRODUCT_COEFFICIENTS, PRODUCT_EQUATION_LIMBS,
};

use crate::limbs::P256EvalBigInt;
use crate::range_checks::{add_range_check, RangeCheckRelation};

use super::canonical_lt::{add_canonical_lt_fixed_bound, CanonicalLtRelations};

pub const FNMUL_SPLIT_CHUNK_TERMS: usize = FNMUL_CHUNK_TERMS;
pub const FNMUL_SPLIT_PRODUCT_CHUNKS: usize = PRODUCT_CHUNKS;
pub const FNMUL_SPLIT_CHUNK_DIGITS: usize = 3;
pub const FNMUL_SPLIT_CHUNK_TOP_DIGIT_BOUND: i64 = 1;
pub const M31_CENTERED_BOUND: i64 = (1i64 << 30) - 1;
pub const FNMUL_SPLIT_CARRY_BOUND: i64 = split_digit_carry_bound();

const LIMB_BOUND: i64 = 1i64 << LIMB_BITS;

#[derive(Clone, Copy)]
pub struct SplitFnMulRelations<'a> {
    /// 13-bit range table for scalar limbs and low/mid chunk digits.
    pub range13: &'a RangeCheckRelation,
    /// Signed carry table for the normalized split carry recurrence.
    ///
    /// Must be configured with [`FNMUL_SPLIT_CARRY_BOUND`].
    pub signed_carry: &'a RangeCheckRelation,
}

pub struct SplitChunkColumns<E: EvalAtRow> {
    pub digits: [E::F; FNMUL_SPLIT_CHUNK_DIGITS],
}

pub struct CanonicalLtColumns<E: EvalAtRow> {
    pub slack: P256EvalBigInt<E>,
    pub carries: [E::F; N_LIMBS],
}

pub struct SplitFnMulColumns<E: EvalAtRow> {
    pub a: P256EvalBigInt<E>,
    pub b: P256EvalBigInt<E>,
    pub result: P256EvalBigInt<E>,
    pub quotient: P256EvalBigInt<E>,
    pub ab_chunks: [SplitChunkColumns<E>; FNMUL_SPLIT_PRODUCT_CHUNKS],
    pub qn_chunks: [SplitChunkColumns<E>; FNMUL_SPLIT_PRODUCT_CHUNKS],
    pub carries: [E::F; PRODUCT_EQUATION_LIMBS],
    pub a_lt_n: CanonicalLtColumns<E>,
    pub b_lt_n: CanonicalLtColumns<E>,
    pub result_lt_n: CanonicalLtColumns<E>,
    pub quotient_lt_n: CanonicalLtColumns<E>,
}

/// Enforce `a * b = quotient * n + result` over the P-256 scalar field.
///
/// The product coefficients are split into chunks of at most two 13-bit
/// products. Each chunk is decomposed as `d0 + B*d1 + B^2*d2`, with
/// `d0,d1 < B` and `d2` boolean. The normalized digit equation then carries
/// over these decomposed digits.
///
/// `gate` must be the same 0/1 selector used by consumers of the multiplication
/// result and by the trace generator's range-check multiplicities.
pub fn add_split_fn_mul<E: EvalAtRow>(
    eval: &mut E,
    relations: SplitFnMulRelations<'_>,
    gate: E::F,
    columns: &SplitFnMulColumns<E>,
) {
    let n_limbs = words_to_limbs(&P256_ORDER);
    let zero = E::F::from(M31::from_u32_unchecked(0));
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));

    add_scalar_canonicality(
        eval,
        relations.range13,
        gate.clone(),
        &columns.a,
        &n_limbs,
        &columns.a_lt_n,
    );
    add_scalar_canonicality(
        eval,
        relations.range13,
        gate.clone(),
        &columns.b,
        &n_limbs,
        &columns.b_lt_n,
    );
    add_scalar_canonicality(
        eval,
        relations.range13,
        gate.clone(),
        &columns.result,
        &n_limbs,
        &columns.result_lt_n,
    );
    add_scalar_canonicality(
        eval,
        relations.range13,
        gate.clone(),
        &columns.quotient,
        &n_limbs,
        &columns.quotient_lt_n,
    );

    add_eval_product_chunks(
        eval,
        relations.range13,
        gate.clone(),
        &columns.a,
        &columns.b,
        &columns.ab_chunks,
    );
    add_fixed_rhs_product_chunks(
        eval,
        relations.range13,
        gate.clone(),
        &columns.quotient,
        &n_limbs,
        &columns.qn_chunks,
    );

    for i in 0..PRODUCT_EQUATION_LIMBS {
        add_range_check(
            eval,
            relations.signed_carry,
            gate.clone(),
            columns.carries[i].clone(),
        );

        let prev_carry = if i == 0 {
            zero.clone()
        } else {
            columns.carries[i - 1].clone()
        };
        let recurrence = split_digit_expr(&columns.ab_chunks, i)
            - split_digit_expr(&columns.qn_chunks, i)
            - result_limb::<E>(&columns.result, i)
            + prev_carry
            - limb_base.clone() * columns.carries[i].clone();
        eval.add_constraint(gate.clone() * recurrence);
    }
    eval.add_constraint(gate * columns.carries[PRODUCT_EQUATION_LIMBS - 1].clone());
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
///
/// A digit can receive at most `ceil(N_LIMBS / 2)` chunk digits from a
/// coefficient, and at most three adjacent coefficient digit layers
/// (`d0`, previous `d1`, previous-previous `d2`).
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

fn add_scalar_canonicality<E: EvalAtRow>(
    eval: &mut E,
    range13: &RangeCheckRelation,
    gate: E::F,
    value: &P256EvalBigInt<E>,
    n_limbs: &BigIntLimbs,
    columns: &CanonicalLtColumns<E>,
) {
    add_canonical_lt_fixed_bound(
        eval,
        CanonicalLtRelations {
            limb_range: range13,
        },
        gate,
        value,
        n_limbs,
        &columns.slack,
        &columns.carries,
    );
}

fn add_eval_product_chunks<E: EvalAtRow>(
    eval: &mut E,
    range13: &RangeCheckRelation,
    gate: E::F,
    lhs: &P256EvalBigInt<E>,
    rhs: &P256EvalBigInt<E>,
    chunks: &[SplitChunkColumns<E>; FNMUL_SPLIT_PRODUCT_CHUNKS],
) {
    let one = E::F::from(M31::from_u32_unchecked(1));
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));

    for_each_product_chunk(|chunk_index, _coeff, pairs| {
        add_chunk_digit_constraints(
            eval,
            range13,
            gate.clone(),
            &chunks[chunk_index],
            one.clone(),
        );
        let product_sum = pairs
            .iter()
            .fold(E::F::from(M31::from_u32_unchecked(0)), |acc, &(i, j)| {
                acc + lhs.limbs()[i].clone() * rhs.limbs()[j].clone()
            });
        add_chunk_decomposition(
            eval,
            gate.clone(),
            product_sum,
            &chunks[chunk_index],
            limb_base.clone(),
        );
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
    let one = E::F::from(M31::from_u32_unchecked(1));
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));

    for_each_product_chunk(|chunk_index, _coeff, pairs| {
        add_chunk_digit_constraints(
            eval,
            range13,
            gate.clone(),
            &chunks[chunk_index],
            one.clone(),
        );
        let product_sum = pairs
            .iter()
            .fold(E::F::from(M31::from_u32_unchecked(0)), |acc, &(i, j)| {
                acc + lhs.limbs()[i].clone() * fixed_limb::<E>(rhs, j)
            });
        add_chunk_decomposition(
            eval,
            gate.clone(),
            product_sum,
            &chunks[chunk_index],
            limb_base.clone(),
        );
    });
}

fn add_chunk_digit_constraints<E: EvalAtRow>(
    eval: &mut E,
    range13: &RangeCheckRelation,
    gate: E::F,
    chunk: &SplitChunkColumns<E>,
    one: E::F,
) {
    add_range_check(eval, range13, gate.clone(), chunk.digits[0].clone());
    add_range_check(eval, range13, gate.clone(), chunk.digits[1].clone());
    eval.add_constraint(gate * chunk.digits[2].clone() * (chunk.digits[2].clone() - one));
}

fn add_chunk_decomposition<E: EvalAtRow>(
    eval: &mut E,
    gate: E::F,
    product_sum: E::F,
    chunk: &SplitChunkColumns<E>,
    limb_base: E::F,
) {
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
    let zero = E::F::from(M31::from_u32_unchecked(0));
    let mut acc = zero;
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

fn result_limb<E: EvalAtRow>(result: &P256EvalBigInt<E>, index: usize) -> E::F {
    result
        .limbs()
        .get(index)
        .cloned()
        .unwrap_or_else(|| E::F::from(M31::from_u32_unchecked(0)))
}

fn fixed_limb<E: EvalAtRow>(limbs: &BigIntLimbs, index: usize) -> E::F {
    E::F::from(M31::from_u32_unchecked(limbs[index]))
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
    use stwo_p256_utils::scalar_arithmetic::{FnMulTrace, SplitProductTrace};

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
