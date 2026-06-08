use stwo::{
    core::{
        fields::{m31::M31, qm31::SecureField},
        utils::{bit_reverse_index, coset_index_to_circle_domain_index},
        ColumnVec,
    },
    prover::backend::simd::{
        m31::{LOG_N_LANES, N_LANES},
        qm31::PackedQM31,
    },
};
use stwo_constraint_framework::{LogupTraceGenerator, Relation};
use stwo_p256_utils::constants::N_LIMBS;
use stwo_p256_utils::scalar_arithmetic::PRODUCT_EQUATION_LIMBS;

use super::accumulator::for_each_digit_contribution;
use super::columns::M31ColumnEval;
use super::ScalarModMulInteractionClaim;
use super::{
    product_chunk_pairs, ScalarModMulComponentRelations, ScalarModMulTraceRows,
    PRODUCT_DIGIT_ACCUMULATOR_TERMS, ROLE_A, ROLE_B, ROLE_QUOTIENT, ROLE_RESULT,
    SCALAR_MOD_MUL_ENABLE_AB_A_LIMB_RELATIONS, SCALAR_MOD_MUL_ENABLE_AB_B_LIMB_RELATIONS,
    SCALAR_MOD_MUL_ENABLE_AB_PRODUCT_CHUNK_DIGIT_RELATIONS,
    SCALAR_MOD_MUL_ENABLE_AB_RANGE_RELATIONS, SCALAR_MOD_MUL_ENABLE_AB_RELATIONS,
    SCALAR_MOD_MUL_ENABLE_AB_SCALAR_LIMB_RELATIONS, SCALAR_MOD_MUL_ENABLE_ACCUMULATOR_RELATIONS,
    SCALAR_MOD_MUL_ENABLE_QN_RELATIONS, SCALAR_MOD_MUL_ENABLE_REDUCTION_RELATIONS,
    SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS, SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS, SIDE_AB, SIDE_QN,
};

pub struct ScalarModMulInteractionTraces {
    pub canonical_scalars: ColumnVec<M31ColumnEval>,
    pub ab_chunks: ColumnVec<M31ColumnEval>,
    pub qn_chunks: ColumnVec<M31ColumnEval>,
    pub accumulators: ColumnVec<M31ColumnEval>,
    pub reduction_digits: ColumnVec<M31ColumnEval>,
}

impl ScalarModMulInteractionTraces {
    pub fn from_rows(
        rows: &ScalarModMulTraceRows,
        external_limb_links: bool,
        relations: &ScalarModMulComponentRelations,
    ) -> (Self, ScalarModMulInteractionClaim) {
        let (canonical_scalars, canonical_claim) = gen_family_interaction_trace(
            super::columns::padded_log_size(rows.canonical_scalars.len()),
            rows.canonical_scalars
                .iter()
                .map(|row| canonical_fractions(rows.mul_id, row, external_limb_links)),
            canonical_padding_fractions(rows.mul_id),
            relations,
            false,
        );
        let (ab_chunks, ab_claim) = gen_family_interaction_trace(
            super::columns::padded_log_size(rows.ab_chunks.len()),
            rows.ab_chunks
                .iter()
                .map(|row| ab_chunk_fractions(rows.mul_id, row)),
            product_chunk_padding_fractions(rows.mul_id, SIDE_AB),
            relations,
            false,
        );
        let (qn_chunks, qn_claim) = gen_family_interaction_trace(
            super::columns::padded_log_size(rows.qn_chunks.len()),
            rows.qn_chunks
                .iter()
                .map(|row| qn_chunk_fractions(rows.mul_id, row)),
            qn_product_chunk_padding_fractions(rows.mul_id),
            relations,
            false,
        );
        let (accumulators, accumulator_claim) = gen_family_interaction_trace(
            super::columns::padded_log_size(rows.accumulators.len()),
            rows.accumulators
                .iter()
                .map(|row| accumulator_fractions(rows.mul_id, row)),
            accumulator_padding_fractions(rows.mul_id),
            relations,
            false,
        );
        let (reduction_digits, reduction_claim) = gen_family_interaction_trace(
            super::columns::padded_log_size(rows.reduction_digits.len()),
            rows.reduction_digits
                .iter()
                .map(|row| reduction_fractions(rows.mul_id, row)),
            reduction_padding_fractions(rows.mul_id),
            relations,
            false,
        );

        (
            Self {
                canonical_scalars,
                ab_chunks,
                qn_chunks,
                accumulators,
                reduction_digits,
            },
            ScalarModMulInteractionClaim {
                canonical_scalars: canonical_claim,
                ab_chunks: ab_claim,
                qn_chunks: qn_claim,
                accumulators: accumulator_claim,
                reduction_digits: reduction_claim,
            },
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct FractionSpec {
    relation: RelationKind,
    numerator: i64,
    values: Vec<M31>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RelationKind {
    Range13,
    SignedCarry,
    ScalarLimb,
    ProductChunkDigit,
    ProductDigit,
    ReductionCarry,
}

fn gen_family_interaction_trace(
    log_size: u32,
    rows: impl IntoIterator<Item = Vec<FractionSpec>>,
    padding_fractions: Vec<FractionSpec>,
    relations: &ScalarModMulComponentRelations,
    pair_fractions: bool,
) -> (ColumnVec<M31ColumnEval>, SecureField) {
    let row_fractions = rows.into_iter().collect::<Vec<_>>();
    let padded_rows = 1usize << log_size;
    assert!(
        row_fractions.len() <= padded_rows,
        "active rows exceed interaction domain"
    );
    let mut storage_fractions = vec![padding_fractions; padded_rows];
    for (coset_index, fractions) in row_fractions.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        );
        storage_fractions[row] = fractions;
    }
    let max_fractions = storage_fractions.iter().map(Vec::len).max().unwrap_or(0);
    if max_fractions == 0 {
        return (Vec::new(), SecureField::from(M31::from_u32_unchecked(0)));
    }
    let batch_count = if pair_fractions {
        max_fractions.div_ceil(2)
    } else {
        max_fractions
    };

    let mut logup = LogupTraceGenerator::new(log_size);
    for batch in 0..batch_count {
        let mut col = logup.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let mut numerators = [SecureField::from(M31::from_u32_unchecked(0)); N_LANES];
            let mut denominators = [SecureField::from(M31::from_u32_unchecked(1)); N_LANES];
            for lane in 0..N_LANES {
                let row = vec_row * N_LANES + lane;
                let fractions = &storage_fractions[row];
                let (numerator, denominator) = if pair_fractions {
                    batch_fraction(fractions, batch, relations)
                } else {
                    fractions
                        .get(batch)
                        .map(|fraction| scalar_fraction(fraction, relations))
                        .unwrap_or_else(zero_fraction)
                };
                numerators[lane] = numerator;
                denominators[lane] = denominator;
            }
            col.write_frac(
                vec_row,
                PackedQM31::from_array(numerators),
                PackedQM31::from_array(denominators),
            );
        }
        col.finalize_col();
    }

    logup.finalize_last()
}

fn batch_fraction(
    fractions: &[FractionSpec],
    batch: usize,
    relations: &ScalarModMulComponentRelations,
) -> (SecureField, SecureField) {
    let first = fractions
        .get(2 * batch)
        .map(|fraction| scalar_fraction(fraction, relations));
    let second = fractions
        .get(2 * batch + 1)
        .map(|fraction| scalar_fraction(fraction, relations));

    match (first, second) {
        (Some((n0, d0)), Some((n1, d1))) => (n0 * d1 + n1 * d0, d0 * d1),
        (Some(fraction), None) | (None, Some(fraction)) => fraction,
        (None, None) => zero_fraction(),
    }
}

fn scalar_fraction(
    fraction: &FractionSpec,
    relations: &ScalarModMulComponentRelations,
) -> (SecureField, SecureField) {
    let denominator = match fraction.relation {
        RelationKind::Range13 => relations.range13.combine(&fraction.values),
        RelationKind::SignedCarry => relations.signed_carry.combine(&fraction.values),
        RelationKind::ScalarLimb => relations.scalar_limb.combine(&fraction.values),
        RelationKind::ProductChunkDigit => relations.product_chunk_digit.combine(&fraction.values),
        RelationKind::ProductDigit => relations.product_digit.combine(&fraction.values),
        RelationKind::ReductionCarry => relations.reduction_carry.combine(&fraction.values),
    };
    (secure_from_i64(fraction.numerator), denominator)
}

fn zero_fraction() -> (SecureField, SecureField) {
    (
        SecureField::from(M31::from_u32_unchecked(0)),
        SecureField::from(M31::from_u32_unchecked(1)),
    )
}

fn canonical_fractions(
    mul_id: u32,
    row: &super::CanonicalScalarTraceRow,
    external_limb_links: bool,
) -> Vec<FractionSpec> {
    let internal_multiplicity = match row.role {
        super::ScalarModMulLimbRole::A
        | super::ScalarModMulLimbRole::B
        | super::ScalarModMulLimbRole::Quotient => N_LIMBS as i64,
        super::ScalarModMulLimbRole::Result => 1,
    };
    let multiplicity = internal_multiplicity + i64::from(external_limb_links);
    let mut fractions = Vec::with_capacity(3 * N_LIMBS);
    for i in 0..N_LIMBS {
        fractions.push(range13_use(row.value[i]));
        fractions.push(range13_use(row.slack[i]));
    }
    for (limb_index, limb) in row.value.iter().enumerate() {
        fractions.push(FractionSpec {
            relation: RelationKind::ScalarLimb,
            numerator: -multiplicity,
            values: vec![
                m31(mul_id),
                m31(row.role.relation_role()),
                m31(limb_index as u32),
                *limb,
            ],
        });
    }
    fractions
}

fn canonical_padding_fractions(mul_id: u32) -> Vec<FractionSpec> {
    let zero = m31(0);
    let mut fractions = Vec::with_capacity(3 * N_LIMBS);
    for _ in 0..N_LIMBS {
        fractions.push(FractionSpec {
            relation: RelationKind::Range13,
            numerator: 0,
            values: vec![zero],
        });
        fractions.push(FractionSpec {
            relation: RelationKind::Range13,
            numerator: 0,
            values: vec![zero],
        });
    }
    for limb_index in 0..N_LIMBS {
        fractions.push(FractionSpec {
            relation: RelationKind::ScalarLimb,
            numerator: 0,
            values: vec![m31(mul_id), m31(0), m31(limb_index as u32), zero],
        });
    }
    fractions
}

fn ab_chunk_fractions(mul_id: u32, row: &super::VariableProductChunkTraceRow) -> Vec<FractionSpec> {
    if !SCALAR_MOD_MUL_ENABLE_AB_RELATIONS {
        return Vec::new();
    }
    let (pairs, term_count) = product_chunk_pairs(row.coeff, row.chunk);
    let mut fractions = Vec::with_capacity(9);
    if SCALAR_MOD_MUL_ENABLE_AB_SCALAR_LIMB_RELATIONS {
        for (term_index, term) in row
            .terms
            .iter()
            .enumerate()
            .take(SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS)
        {
            let term_active = (term_index < term_count) as i64;
            if SCALAR_MOD_MUL_ENABLE_AB_A_LIMB_RELATIONS {
                fractions.push(scalar_limb_use(
                    mul_id,
                    ROLE_A,
                    pairs[term_index].0,
                    term.lhs,
                    term_active,
                ));
            }
            if SCALAR_MOD_MUL_ENABLE_AB_B_LIMB_RELATIONS {
                fractions.push(scalar_limb_use(
                    mul_id,
                    ROLE_B,
                    pairs[term_index].1,
                    term.rhs,
                    term_active,
                ));
            }
        }
    }
    if SCALAR_MOD_MUL_ENABLE_AB_RANGE_RELATIONS
        || SCALAR_MOD_MUL_ENABLE_AB_PRODUCT_CHUNK_DIGIT_RELATIONS
    {
        fractions.extend(product_chunk_finish_fractions(
            mul_id, SIDE_AB, row.coeff, row.chunk, row.digits,
        ));
    }
    fractions
}

fn qn_chunk_fractions(mul_id: u32, row: &super::QnProductChunkTraceRow) -> Vec<FractionSpec> {
    if !SCALAR_MOD_MUL_ENABLE_QN_RELATIONS {
        return Vec::new();
    }
    let (pairs, term_count) = product_chunk_pairs(row.coeff, row.chunk);
    let mut fractions = Vec::with_capacity(7);
    for (term_index, quotient_limb) in row
        .quotient_limbs
        .iter()
        .enumerate()
        .take(SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS)
    {
        let term_active = (term_index < term_count) as i64;
        fractions.push(scalar_limb_use(
            mul_id,
            ROLE_QUOTIENT,
            pairs[term_index].0,
            *quotient_limb,
            term_active,
        ));
    }
    fractions.extend(product_chunk_finish_fractions(
        mul_id, SIDE_QN, row.coeff, row.chunk, row.digits,
    ));
    fractions
}

fn product_chunk_finish_fractions(
    mul_id: u32,
    side: u32,
    coeff: usize,
    chunk: usize,
    digits: [M31; SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS],
) -> Vec<FractionSpec> {
    let mut fractions = Vec::with_capacity(5);
    if side != SIDE_AB || SCALAR_MOD_MUL_ENABLE_AB_RANGE_RELATIONS {
        fractions.push(range13_use(digits[0]));
        fractions.push(range13_use(digits[1]));
    }
    if side != SIDE_AB || SCALAR_MOD_MUL_ENABLE_AB_PRODUCT_CHUNK_DIGIT_RELATIONS {
        for (offset, digit) in digits.iter().enumerate() {
            let active = (coeff + offset < PRODUCT_EQUATION_LIMBS) as i64;
            fractions.push(FractionSpec {
                relation: RelationKind::ProductChunkDigit,
                numerator: -active,
                values: vec![
                    m31(mul_id),
                    m31(side),
                    m31(coeff as u32),
                    m31(chunk as u32),
                    m31(offset as u32),
                    *digit,
                ],
            });
        }
    }
    fractions
}

fn product_chunk_padding_fractions(mul_id: u32, side: u32) -> Vec<FractionSpec> {
    if !SCALAR_MOD_MUL_ENABLE_AB_RELATIONS {
        return Vec::new();
    }
    let mut fractions = Vec::with_capacity(2 * SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS + 5);
    for _ in 0..SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS {
        if side != SIDE_AB || SCALAR_MOD_MUL_ENABLE_AB_A_LIMB_RELATIONS {
            fractions.push(scalar_limb_use(mul_id, ROLE_A, 0, m31(0), 0));
        }
        if side != SIDE_AB || SCALAR_MOD_MUL_ENABLE_AB_B_LIMB_RELATIONS {
            fractions.push(scalar_limb_use(mul_id, ROLE_B, 0, m31(0), 0));
        }
    }
    fractions.extend(
        product_chunk_finish_fractions(
            mul_id,
            side,
            0,
            0,
            [m31(0); SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS],
        )
        .into_iter()
        .map(|mut fraction| {
            fraction.numerator = 0;
            fraction
        }),
    );
    fractions
}

fn qn_product_chunk_padding_fractions(mul_id: u32) -> Vec<FractionSpec> {
    if !SCALAR_MOD_MUL_ENABLE_QN_RELATIONS {
        return Vec::new();
    }
    let mut fractions = Vec::with_capacity(SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS + 5);
    for _ in 0..SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS {
        fractions.push(scalar_limb_use(mul_id, ROLE_QUOTIENT, 0, m31(0), 0));
    }
    fractions.extend(
        product_chunk_finish_fractions(
            mul_id,
            SIDE_QN,
            0,
            0,
            [m31(0); SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS],
        )
        .into_iter()
        .map(|mut fraction| {
            fraction.numerator = 0;
            fraction
        }),
    );
    fractions
}

fn accumulator_fractions(
    mul_id: u32,
    row: &super::ProductDigitAccumulatorTraceRow,
) -> Vec<FractionSpec> {
    if !SCALAR_MOD_MUL_ENABLE_ACCUMULATOR_RELATIONS {
        return Vec::new();
    }
    let mut fractions = Vec::with_capacity(PRODUCT_DIGIT_ACCUMULATOR_TERMS + 1);
    let side = row.side.relation_side();
    for_each_digit_contribution(row.digit_index, |term_index, coeff, chunk, offset| {
        fractions.push(FractionSpec {
            relation: RelationKind::ProductChunkDigit,
            numerator: 1,
            values: vec![
                m31(mul_id),
                m31(side),
                m31(coeff as u32),
                m31(chunk as u32),
                m31(offset as u32),
                row.terms[term_index],
            ],
        });
    });
    for term_index in row.term_count..PRODUCT_DIGIT_ACCUMULATOR_TERMS {
        fractions.push(FractionSpec {
            relation: RelationKind::ProductChunkDigit,
            numerator: 0,
            values: vec![
                m31(mul_id),
                m31(side),
                m31(0),
                m31(0),
                m31(0),
                row.terms[term_index],
            ],
        });
    }
    fractions.push(FractionSpec {
        relation: RelationKind::ProductDigit,
        numerator: -1,
        values: vec![
            m31(mul_id),
            m31(side),
            m31(row.digit_index as u32),
            row.product_digit,
        ],
    });
    fractions
}

fn accumulator_padding_fractions(mul_id: u32) -> Vec<FractionSpec> {
    if !SCALAR_MOD_MUL_ENABLE_ACCUMULATOR_RELATIONS {
        return Vec::new();
    }
    let mut fractions = Vec::with_capacity(PRODUCT_DIGIT_ACCUMULATOR_TERMS + 1);
    for _ in 0..PRODUCT_DIGIT_ACCUMULATOR_TERMS {
        fractions.push(FractionSpec {
            relation: RelationKind::ProductChunkDigit,
            numerator: 0,
            values: vec![m31(mul_id), m31(0), m31(0), m31(0), m31(0), m31(0)],
        });
    }
    fractions.push(FractionSpec {
        relation: RelationKind::ProductDigit,
        numerator: 0,
        values: vec![m31(mul_id), m31(0), m31(0), m31(0)],
    });
    fractions
}

fn reduction_fractions(
    mul_id: u32,
    row: &super::ScalarReductionDigitTraceRow,
) -> Vec<FractionSpec> {
    if !SCALAR_MOD_MUL_ENABLE_REDUCTION_RELATIONS {
        return Vec::new();
    }
    let has_result_limb = (row.digit_index < N_LIMBS) as i64;
    let has_prev_carry = (row.digit_index > 0) as i64;
    let has_next_carry = (row.digit_index + 1 < PRODUCT_EQUATION_LIMBS) as i64;
    vec![
        product_digit_use(mul_id, SIDE_AB, row.digit_index, row.ab_digit),
        product_digit_use(mul_id, SIDE_QN, row.digit_index, row.qn_digit),
        FractionSpec {
            relation: RelationKind::ScalarLimb,
            numerator: has_result_limb,
            values: vec![
                m31(mul_id),
                m31(ROLE_RESULT),
                m31(row.digit_index as u32),
                row.result_limb,
            ],
        },
        FractionSpec {
            relation: RelationKind::ReductionCarry,
            numerator: has_prev_carry,
            values: vec![
                m31(mul_id),
                m31_from_i64(row.digit_index as i64 - 1),
                row.prev_carry,
            ],
        },
        FractionSpec {
            relation: RelationKind::SignedCarry,
            numerator: 1,
            values: vec![row.carry],
        },
        FractionSpec {
            relation: RelationKind::ReductionCarry,
            numerator: -has_next_carry,
            values: vec![m31(mul_id), m31(row.digit_index as u32), row.carry],
        },
    ]
}

fn reduction_padding_fractions(mul_id: u32) -> Vec<FractionSpec> {
    if !SCALAR_MOD_MUL_ENABLE_REDUCTION_RELATIONS {
        return Vec::new();
    }
    vec![
        product_digit_use(mul_id, SIDE_AB, 0, m31(0)).with_numerator(0),
        product_digit_use(mul_id, SIDE_QN, 0, m31(0)).with_numerator(0),
        FractionSpec {
            relation: RelationKind::ScalarLimb,
            numerator: 0,
            values: vec![m31(mul_id), m31(ROLE_RESULT), m31(0), m31(0)],
        },
        FractionSpec {
            relation: RelationKind::ReductionCarry,
            numerator: 0,
            values: vec![m31(mul_id), m31_from_i64(-1), m31(0)],
        },
        FractionSpec {
            relation: RelationKind::SignedCarry,
            numerator: 0,
            values: vec![m31(0)],
        },
        FractionSpec {
            relation: RelationKind::ReductionCarry,
            numerator: 0,
            values: vec![m31(mul_id), m31(0), m31(0)],
        },
    ]
}

impl FractionSpec {
    fn with_numerator(mut self, numerator: i64) -> Self {
        self.numerator = numerator;
        self
    }
}

fn range13_use(value: M31) -> FractionSpec {
    FractionSpec {
        relation: RelationKind::Range13,
        numerator: 1,
        values: vec![value],
    }
}

fn scalar_limb_use(
    mul_id: u32,
    role: u32,
    limb_index: usize,
    limb: M31,
    numerator: i64,
) -> FractionSpec {
    FractionSpec {
        relation: RelationKind::ScalarLimb,
        numerator,
        values: vec![m31(mul_id), m31(role), m31(limb_index as u32), limb],
    }
}

fn product_digit_use(mul_id: u32, side: u32, digit_index: usize, digit: M31) -> FractionSpec {
    FractionSpec {
        relation: RelationKind::ProductDigit,
        numerator: 1,
        values: vec![m31(mul_id), m31(side), m31(digit_index as u32), digit],
    }
}

fn secure_from_i64(value: i64) -> SecureField {
    SecureField::from(m31_from_i64(value))
}

fn m31_from_i64(value: i64) -> M31 {
    const MODULUS: i64 = (1i64 << 31) - 1;
    let reduced = value.rem_euclid(MODULUS);
    M31::from_u32_unchecked(reduced as u32)
}

fn m31(value: u32) -> M31 {
    M31::from_u32_unchecked(value)
}

#[cfg(test)]
mod tests {
    use stwo::core::fields::qm31::SecureField;
    use stwo_p256_utils::scalar_arithmetic::{ScalarFieldMulTrace, P256_ORDER};

    use crate::range_checks::RangeCheckRelation;

    use super::super::{
        layout::ScalarModMulRelationAudit, ScalarLimbRelation, ScalarProductChunkDigitRelation,
        ScalarProductDigitRelation, ScalarReductionCarryRelation,
    };
    use super::*;

    fn scalar(value: u64) -> [u64; 4] {
        [value, 0, 0, 0]
    }

    fn test_rows() -> ScalarModMulTraceRows {
        let trace = ScalarFieldMulTrace::new("test_mul", &scalar(7), &scalar(11), &P256_ORDER)
            .expect("valid scalar mod-mul trace");
        ScalarModMulTraceRows::new(3, &trace).expect("trace rows generate")
    }

    fn relations() -> ScalarModMulComponentRelations {
        ScalarModMulComponentRelations {
            range13: RangeCheckRelation::dummy(),
            signed_carry: RangeCheckRelation::dummy(),
            scalar_limb: ScalarLimbRelation::dummy(),
            product_chunk_digit: ScalarProductChunkDigitRelation::dummy(),
            product_digit: ScalarProductDigitRelation::dummy(),
            reduction_carry: ScalarReductionCarryRelation::dummy(),
        }
    }

    #[test]
    fn scalar_mod_mul_interaction_traces_have_expected_domains_and_widths() {
        let rows = test_rows();
        let (traces, claim) = ScalarModMulInteractionTraces::from_rows(&rows, false, &relations());

        assert_eq!(traces.canonical_scalars[0].domain.size(), 16);
        assert_eq!(traces.ab_chunks[0].domain.size(), 256);
        assert_eq!(traces.qn_chunks[0].domain.size(), 256);
        assert_eq!(traces.accumulators[0].domain.size(), 128);
        assert_eq!(traces.reduction_digits[0].domain.size(), 64);

        assert_eq!(traces.canonical_scalars.len(), 60 * 4);
        assert_eq!(traces.ab_chunks.len(), 9 * 4);
        assert_eq!(traces.qn_chunks.len(), 7 * 4);
        assert_eq!(traces.accumulators.len(), 31 * 4);
        assert_eq!(traces.reduction_digits.len(), 6 * 4);

        assert_ne!(
            claim.canonical_scalars,
            SecureField::from(M31::from_u32_unchecked(0))
        );
    }

    #[test]
    fn scalar_mod_mul_interaction_claim_changes_after_tuple_mutation() {
        let rows = test_rows();
        let (_, honest_claim) =
            ScalarModMulInteractionTraces::from_rows(&rows, false, &relations());

        let mut mutated = rows.clone();
        mutated.accumulators[0].terms[0] += M31::from_u32_unchecked(1);
        let (_, mutated_claim) =
            ScalarModMulInteractionTraces::from_rows(&mutated, false, &relations());

        assert_ne!(honest_claim.accumulators, mutated_claim.accumulators);
        assert!(!ScalarModMulRelationAudit::from_rows(&mutated).is_balanced());
    }

    #[test]
    fn batched_fraction_matches_sum_of_two_fractions() {
        let relations = relations();
        let fractions = [
            FractionSpec {
                relation: RelationKind::ScalarLimb,
                numerator: 3,
                values: vec![m31(1), m31(2), m31(3), m31(4)],
            },
            FractionSpec {
                relation: RelationKind::ScalarLimb,
                numerator: -5,
                values: vec![m31(6), m31(7), m31(8), m31(9)],
            },
        ];
        let (n, d) = batch_fraction(&fractions, 0, &relations);
        let (n0, d0) = scalar_fraction(&fractions[0], &relations);
        let (n1, d1) = scalar_fraction(&fractions[1], &relations);

        assert_eq!(n, n0 * d1 + n1 * d0);
        assert_eq!(d, d0 * d1);
    }
}
