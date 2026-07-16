pub mod accumulator;
pub mod canonical;
pub mod chunk_product;
pub mod claim;
pub mod columns;
pub mod component;
pub mod interaction;
pub(crate) mod interaction_claim;
pub mod layout;
pub(crate) mod providers;
pub mod reduction;
pub(crate) mod relation;
pub mod schedule;
pub mod trace;

use stwo::core::fields::m31::M31;
use stwo_constraint_framework::{EvalAtRow, RelationEntry};
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};
#[cfg(test)]
use stwo_p256_utils::scalar_arithmetic::PRODUCT_COEFFICIENTS;
use stwo_p256_utils::scalar_arithmetic::{FNMUL_CHUNK_TERMS, PRODUCT_CHUNKS};

pub use accumulator::{
    add_product_digit_accumulator, ProductDigitAccumulatorColumns,
    ProductDigitAccumulatorRelations, PRODUCT_DIGIT_ACCUMULATOR_TERMS,
};
pub use canonical::{
    add_canonical_lt_n, add_canonical_scalar_limb_provider, CanonicalLtNColumns,
    CanonicalLtNRelations, CanonicalScalarLimbRelations, ScalarModMulLimbRole,
};
pub use chunk_product::{
    add_ab_product_chunk_provider, add_qn_product_chunk_provider, ProductChunkLinkRelations,
    ProductChunkMeta, ProductSide, ProductTermColumns, QnProductChunkColumns,
    VariableProductChunkColumns,
};
pub use claim::ScalarModMulClaim;
pub use component::{
    AbProductChunkEval, CanonicalScalarEval, ProductDigitAccumulatorEval, QnProductChunkEval,
    ScalarReductionDigitEval,
};
pub use interaction::ScalarModMulInteractionTraces;
pub use interaction_claim::ScalarModMulInteractionClaim;
pub use layout::{
    ScalarModMulColumnTrace, ScalarModMulFamilyColumnEvals, ScalarModMulFamilyTraces,
    ScalarModMulLookupUses, ScalarModMulRelationAudit,
};
pub use reduction::{
    add_scalar_reduction_digit, ScalarReductionDigitColumns, ScalarReductionDigitRelations,
    SCALAR_REDUCTION_DIGIT_TRACE_COLUMNS,
};
pub use relation::{
    ScalarLimbRelation, ScalarModMulComponentRelations, ScalarProductChunkDigitRelation,
    ScalarProductDigitRelation, ScalarReductionCarryRelation, PRODUCT_CHUNK_DIGIT_RELATION_ARITY,
    PRODUCT_DIGIT_RELATION_ARITY, REDUCTION_CARRY_RELATION_ARITY, SCALAR_LIMB_RELATION_ARITY,
};
pub use schedule::{
    ProductFamily, ScalarModMulFixedSchedule, ScalarModMulFixedScheduleEvals,
    ScalarModMulScheduleColumn, ScalarModMulScheduleColumnIds,
};
pub use trace::{
    CanonicalScalarTraceRow, ProductDigitAccumulatorTraceRow, QnProductChunkTraceRow,
    ScalarModMulMergedRows, ScalarModMulRelationCounts, ScalarModMulTraceError,
    ScalarModMulTraceRows, ScalarReductionDigitTraceRow, VariableProductChunkTraceRow,
};

pub const SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS: usize = FNMUL_CHUNK_TERMS;
pub const SCALAR_MOD_MUL_SPLIT_PRODUCT_CHUNKS: usize = PRODUCT_CHUNKS;
pub const SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS: usize = 3;
pub const SCALAR_MOD_MUL_SPLIT_CHUNK_TOP_DIGIT_BOUND: i64 = 1;
pub const SCALAR_MOD_MUL_SPLIT_CARRY_BOUND: i64 = split_digit_carry_bound();
pub const M31_CENTERED_BOUND: i64 = (1i64 << 30) - 1;
pub const PRODUCT_SCALAR_LIMB_USE_COUNT: u32 = N_LIMBS as u32;
pub const PRODUCT_CHUNKS_PER_COEFFICIENT: usize =
    N_LIMBS.div_ceil(SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS);
pub const PRODUCT_DIGIT_ACCUMULATOR_MAX_TERMS: usize =
    SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS * PRODUCT_CHUNKS_PER_COEFFICIENT;

pub const ROLE_A: u32 = 0;
pub const ROLE_B: u32 = 1;
pub const ROLE_RESULT: u32 = 2;
pub const ROLE_QUOTIENT: u32 = 3;

pub const SIDE_AB: u32 = 0;
pub const SIDE_QN: u32 = 1;

pub(crate) const SCALAR_MOD_MUL_ENABLE_AB_A_LIMB_RELATIONS: bool = true;
pub(crate) const SCALAR_MOD_MUL_ENABLE_AB_B_LIMB_RELATIONS: bool = true;
pub(crate) const SCALAR_MOD_MUL_ENABLE_AB_SCALAR_LIMB_RELATIONS: bool =
    SCALAR_MOD_MUL_ENABLE_AB_A_LIMB_RELATIONS || SCALAR_MOD_MUL_ENABLE_AB_B_LIMB_RELATIONS;
pub(crate) const SCALAR_MOD_MUL_ENABLE_AB_RANGE_RELATIONS: bool = true;
pub(crate) const SCALAR_MOD_MUL_ENABLE_AB_PRODUCT_CHUNK_DIGIT_RELATIONS: bool = true;
pub(crate) const SCALAR_MOD_MUL_ENABLE_AB_RELATIONS: bool =
    SCALAR_MOD_MUL_ENABLE_AB_SCALAR_LIMB_RELATIONS
        || SCALAR_MOD_MUL_ENABLE_AB_RANGE_RELATIONS
        || SCALAR_MOD_MUL_ENABLE_AB_PRODUCT_CHUNK_DIGIT_RELATIONS;
pub(crate) const SCALAR_MOD_MUL_ENABLE_QN_RELATIONS: bool = true;
pub(crate) const SCALAR_MOD_MUL_ENABLE_ACCUMULATOR_RELATIONS: bool = true;
pub(crate) const SCALAR_MOD_MUL_ENABLE_REDUCTION_RELATIONS: bool = true;

const LIMB_BOUND: i64 = 1i64 << LIMB_BITS;

pub struct SplitChunkColumns<E: EvalAtRow> {
    /// Little-endian base-`B` decomposition of one split product chunk:
    /// `digits[0] + B * digits[1] + B^2 * digits[2]`.
    pub digits: [E::F; SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS],
}

#[derive(Clone, Copy)]
pub struct ScalarModMulChunkLinkRelations<'a> {
    /// Links canonical scalar limb providers to narrow product chunk rows.
    pub scalar_limb: &'a ScalarLimbRelation,
    /// Links product chunk rows to a future product-digit accumulator.
    pub product_chunk_digit: &'a ScalarProductChunkDigitRelation,
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
    SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS as i64 * product
        + (LIMB_BOUND - 1)
        + LIMB_BOUND * (LIMB_BOUND - 1)
        + LIMB_BOUND * LIMB_BOUND * SCALAR_MOD_MUL_SPLIT_CHUNK_TOP_DIGIT_BOUND
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
    let chunks_per_coeff = (N_LIMBS as i64 + SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS as i64 - 1)
        / SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS as i64;
    3 * chunks_per_coeff * (LIMB_BOUND - 1) + chunks_per_coeff
}

pub fn scalar_mod_mul_fits_m31_centered() -> bool {
    split_chunk_max_abs_expr() < M31_CENTERED_BOUND
        && split_digit_max_abs_expr() < M31_CENTERED_BOUND
}

fn provide_scalar_limb<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarLimbRelation,
    gate: E::F,
    mul_id: E::F,
    limb: (u32, usize),
    limb_value: E::F,
    multiplicity: u32,
) {
    if multiplicity == 0 {
        return;
    }
    let scaled_gate = gate * E::F::from(M31::from_u32_unchecked(multiplicity));
    add_scalar_limb_relation(eval, relation, -scaled_gate, mul_id, limb, limb_value);
}

fn consume_scalar_limb<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarLimbRelation,
    gate: E::F,
    mul_id: E::F,
    role: u32,
    limb_index: usize,
    limb_value: E::F,
) {
    add_scalar_limb_relation(eval, relation, gate, mul_id, (role, limb_index), limb_value);
}

fn provide_product_chunk_digit<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarProductChunkDigitRelation,
    gate: E::F,
    mul_id: E::F,
    meta: ProductChunkCoordinate,
    digit_offset: usize,
    digit_value: E::F,
) {
    add_product_chunk_digit_relation(
        eval,
        relation,
        -gate,
        mul_id,
        meta,
        digit_offset,
        digit_value,
    );
}

fn consume_product_chunk_digit<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarProductChunkDigitRelation,
    gate: E::F,
    mul_id: E::F,
    meta: ProductChunkCoordinate,
    digit_offset: usize,
    digit_value: E::F,
) {
    add_product_chunk_digit_relation(
        eval,
        relation,
        gate,
        mul_id,
        meta,
        digit_offset,
        digit_value,
    );
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
        -gate,
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
    add_product_digit_relation(eval, relation, gate, mul_id, side, digit_index, digit_value);
}

fn provide_reduction_carry<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarReductionCarryRelation,
    gate: E::F,
    mul_id: E::F,
    digit_index: usize,
    carry_value: E::F,
) {
    add_reduction_carry_relation(eval, relation, -gate, mul_id, digit_index, carry_value);
}

fn consume_reduction_carry<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarReductionCarryRelation,
    gate: E::F,
    mul_id: E::F,
    digit_index: usize,
    carry_value: E::F,
) {
    add_reduction_carry_relation(eval, relation, gate, mul_id, digit_index, carry_value);
}

fn add_scalar_limb_relation<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarLimbRelation,
    numerator: E::F,
    mul_id: E::F,
    limb: (u32, usize),
    limb_value: E::F,
) {
    let values: [E::F; SCALAR_LIMB_RELATION_ARITY] = [
        mul_id,
        E::F::from(M31::from_u32_unchecked(limb.0)),
        E::F::from(M31::from_u32_unchecked(limb.1 as u32)),
        limb_value,
    ];
    eval.add_to_relation(RelationEntry::base(relation, numerator, &values));
}

#[derive(Clone, Copy)]
struct ProductChunkCoordinate {
    side: u32,
    coeff: usize,
    chunk: usize,
}

fn add_product_chunk_digit_relation<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarProductChunkDigitRelation,
    numerator: E::F,
    mul_id: E::F,
    meta: ProductChunkCoordinate,
    digit_offset: usize,
    digit_value: E::F,
) {
    let values: [E::F; PRODUCT_CHUNK_DIGIT_RELATION_ARITY] = [
        mul_id,
        E::F::from(M31::from_u32_unchecked(meta.side)),
        E::F::from(M31::from_u32_unchecked(meta.coeff as u32)),
        E::F::from(M31::from_u32_unchecked(meta.chunk as u32)),
        E::F::from(M31::from_u32_unchecked(digit_offset as u32)),
        digit_value,
    ];
    eval.add_to_relation(RelationEntry::base(relation, numerator, &values));
}

fn add_product_digit_relation<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarProductDigitRelation,
    numerator: E::F,
    mul_id: E::F,
    side: u32,
    digit_index: usize,
    digit_value: E::F,
) {
    let values: [E::F; PRODUCT_DIGIT_RELATION_ARITY] = [
        mul_id,
        E::F::from(M31::from_u32_unchecked(side)),
        E::F::from(M31::from_u32_unchecked(digit_index as u32)),
        digit_value,
    ];
    eval.add_to_relation(RelationEntry::base(relation, numerator, &values));
}

fn add_reduction_carry_relation<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarReductionCarryRelation,
    numerator: E::F,
    mul_id: E::F,
    digit_index: usize,
    carry_value: E::F,
) {
    let values: [E::F; REDUCTION_CARRY_RELATION_ARITY] = [
        mul_id,
        E::F::from(M31::from_u32_unchecked(digit_index as u32)),
        carry_value,
    ];
    eval.add_to_relation(RelationEntry::base(relation, numerator, &values));
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

#[cfg(test)]
fn for_each_product_chunk(mut f: impl FnMut(usize, usize, &[(usize, usize)])) {
    let mut chunk_index = 0usize;
    for coeff in 0..PRODUCT_COEFFICIENTS {
        let mut pairs = [(0usize, 0usize); SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS];
        let mut pair_count = 0usize;
        for pair in coefficient_pairs(coeff) {
            pairs[pair_count] = pair;
            pair_count += 1;
            if pair_count == SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS {
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
    debug_assert_eq!(chunk_index, SCALAR_MOD_MUL_SPLIT_PRODUCT_CHUNKS);
}

fn coefficient_pairs(coeff: usize) -> impl Iterator<Item = (usize, usize)> {
    let start = coeff.saturating_sub(N_LIMBS - 1);
    let end = coeff.min(N_LIMBS - 1);
    (start..=end).map(move |i| (i, coeff - i))
}

fn product_chunk_pairs(
    coeff: usize,
    chunk: usize,
) -> ([(usize, usize); SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS], usize) {
    let mut pairs = [(0usize, 0usize); SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS];
    let mut pair_count = 0usize;
    let skipped = chunk * SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS;
    for pair in coefficient_pairs(coeff)
        .skip(skipped)
        .take(SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS)
    {
        pairs[pair_count] = pair;
        pair_count += 1;
    }
    (pairs, pair_count)
}

#[cfg(test)]
fn first_chunk_index(coeff: usize) -> usize {
    (0..coeff).map(coefficient_chunk_count).sum()
}

#[cfg(test)]
fn coefficient_chunk_count(coeff: usize) -> usize {
    coefficient_term_count(coeff).div_ceil(SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS)
}

#[cfg(test)]
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
    fn scalar_mod_mul_chunk_constraints_fit_m31_centered() {
        assert!(split_chunk_max_abs_expr() < M31_CENTERED_BOUND);
    }

    #[test]
    fn scalar_mod_mul_digit_constraints_fit_m31_centered() {
        assert!(split_digit_max_abs_expr() < M31_CENTERED_BOUND);
    }

    #[test]
    fn scalar_mod_mul_carry_bound_is_tight_for_headroom_formula() {
        assert_eq!(SCALAR_MOD_MUL_SPLIT_CARRY_BOUND, 61);
        assert_eq!(
            split_digit_max_abs_expr(),
            split_digit_diff_bound()
                + SCALAR_MOD_MUL_SPLIT_CARRY_BOUND
                + LIMB_BOUND * SCALAR_MOD_MUL_SPLIT_CARRY_BOUND
        );
    }

    #[test]
    fn scalar_mod_mul_uses_expected_chunk_count() {
        assert_eq!(SCALAR_MOD_MUL_SPLIT_PRODUCT_CHUNKS, 210);
        assert_eq!(SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS, 2);
        assert!(scalar_mod_mul_fits_m31_centered());
    }

    #[test]
    fn scalar_mod_mul_trace_carries_fit_audited_bound() {
        let mut max_scalar = P256_ORDER;
        max_scalar[0] -= 1;
        let mul = FnMulTrace::new(&max_scalar, &max_scalar, &P256_ORDER)
            .expect("valid multiplication trace");
        let split = SplitProductTrace::new(&mul);

        assert!(split
            .carries
            .iter()
            .all(
                |&carry| (-SCALAR_MOD_MUL_SPLIT_CARRY_BOUND..=SCALAR_MOD_MUL_SPLIT_CARRY_BOUND)
                    .contains(&carry)
            ));
    }

    #[test]
    fn product_chunk_metadata_matches_shape() {
        let mut chunks = 0usize;
        for_each_product_chunk(|chunk_index, coeff, pairs| {
            assert_eq!(chunk_index, chunks);
            assert!(!pairs.is_empty());
            assert!(pairs.len() <= SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS);
            assert_eq!(
                pairs.len(),
                coefficient_chunk_term_count(coeff, chunk_index)
            );
            chunks += 1;
        });
        assert_eq!(chunks, SCALAR_MOD_MUL_SPLIT_PRODUCT_CHUNKS);
    }

    fn coefficient_chunk_term_count(coeff: usize, global_chunk: usize) -> usize {
        let first = first_chunk_index(coeff);
        let local = global_chunk - first;
        let term_count = coefficient_term_count(coeff);
        let consumed = local * SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS;
        (term_count - consumed).min(SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS)
    }
}
