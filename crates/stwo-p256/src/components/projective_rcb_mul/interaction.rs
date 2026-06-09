//! Interaction-trace (LogUp) generation for the projective RCB multiplication AIR family.
//!
//! Split out of `mod.rs` (pure relocation, no behavioral change).

use stwo::core::{
    channel::Channel,
    fields::{m31::M31, qm31::SecureField},
    utils::{bit_reverse_index, coset_index_to_circle_domain_index},
    ColumnVec,
};
use stwo::prover::backend::simd::{
    m31::{LOG_N_LANES, N_LANES},
    qm31::PackedQM31,
};
use stwo_constraint_framework::{LogupTraceGenerator, Relation};
use stwo_p256_utils::constants::N_LIMBS;

use super::*;
use crate::fp_solinas::FP_SOLINAS_SIGNED_CORRECTION_LIMBS;
use crate::fp_solinas_air::{fp_solinas_correction_digit_columns, FP_SOLINAS_REDUCTION_DIGITS};
use crate::range_checks::RangeCheckInteractionClaim;
use crate::scalar::scalar_mod_mul::columns::M31ColumnEval;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbAirComponentInteractionClaim {
    pub mul: SecureField,
    pub raw_product_chunk: SecureField,
    pub folded_contribution: SecureField,
    pub folded_digit: SecureField,
}

impl ProjectiveRcbAirComponentInteractionClaim {
    pub fn total(&self) -> SecureField {
        self.mul + self.raw_product_chunk + self.folded_contribution + self.folded_digit
    }
}

#[derive(Clone, Debug)]
pub struct ProjectiveRcbAirInteractionTraces {
    pub mul: ColumnVec<M31ColumnEval>,
    pub raw_product_chunk: ColumnVec<M31ColumnEval>,
    pub folded_contribution: ColumnVec<M31ColumnEval>,
    pub folded_digit: ColumnVec<M31ColumnEval>,
}

impl ProjectiveRcbAirInteractionTraces {
    pub fn into_columns(self) -> Vec<M31ColumnEval> {
        let mut columns = Vec::new();
        columns.extend(self.mul);
        columns.extend(self.raw_product_chunk);
        columns.extend(self.folded_contribution);
        columns.extend(self.folded_digit);
        columns
    }
}

#[derive(Clone, Debug)]
pub struct ProjectiveRcbAirProofInteractionClaim {
    pub components: ProjectiveRcbAirComponentInteractionClaim,
    pub range13: RangeCheckInteractionClaim,
    pub raw_product_carry16: RangeCheckInteractionClaim,
    pub signed_carry: RangeCheckInteractionClaim,
    /// C5 plumbing: the `ProjectiveRcbMulResultRelation` provider sum (yield,
    /// `-active`). Part of `components.mul`, surfaced separately so the proof's
    /// `relation_balances()` can net it against the projective-source consumers
    /// and `liveness_witnesses()` can require it nonzero.
    pub mul_result_provider_claimed_sum: SecureField,
}

impl ProjectiveRcbAirProofInteractionClaim {
    pub fn zero() -> Self {
        Self {
            components: ProjectiveRcbAirComponentInteractionClaim {
                mul: secure_zero(),
                raw_product_chunk: secure_zero(),
                folded_contribution: secure_zero(),
                folded_digit: secure_zero(),
            },
            range13: RangeCheckInteractionClaim {
                claimed_sum: secure_zero(),
            },
            raw_product_carry16: RangeCheckInteractionClaim {
                claimed_sum: secure_zero(),
            },
            signed_carry: RangeCheckInteractionClaim {
                claimed_sum: secure_zero(),
            },
            mul_result_provider_claimed_sum: secure_zero(),
        }
    }

    pub fn total(&self) -> SecureField {
        self.components.total()
            + self.range13.claimed_sum
            + self.raw_product_carry16.claimed_sum
            + self.signed_carry.claimed_sum
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[
            self.components.mul,
            self.components.raw_product_chunk,
            self.components.folded_contribution,
            self.components.folded_digit,
            self.range13.claimed_sum,
            self.raw_product_carry16.claimed_sum,
            self.signed_carry.claimed_sum,
            // C5 plumbing: bind the provider breakdown sum into Fiat-Shamir so
            // the verifier-side `relation_balances()` term is sound.
            self.mul_result_provider_claimed_sum,
        ]);
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ProjectiveRcbFractionSpec {
    relation: ProjectiveRcbRelationKind,
    numerator: i64,
    values: Vec<M31>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ProjectiveRcbRelationKind {
    Range13,
    RawProductCarry16,
    SignedCarry,
    MulLimb,
    MulResult,
    RawProductChunkDigit,
    FoldedContribution,
    FoldedDigit,
    FoldedCarry,
}

pub(crate) fn gen_projective_rcb_family_interaction_trace(
    log_size: u32,
    rows: impl IntoIterator<Item = Vec<ProjectiveRcbFractionSpec>>,
    padding_fractions: Vec<ProjectiveRcbFractionSpec>,
    relations: &ProjectiveRcbMulComponentRelations,
    batch_in_pairs: bool,
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
        return (Vec::new(), secure_zero());
    }

    let mut logup = LogupTraceGenerator::new(log_size);
    let batch_count = if batch_in_pairs {
        max_fractions.div_ceil(2)
    } else {
        max_fractions
    };
    for batch in 0..batch_count {
        let mut col = logup.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let mut numerators = [secure_zero(); N_LANES];
            let mut denominators = [secure_one(); N_LANES];
            for lane in 0..N_LANES {
                let row = vec_row * N_LANES + lane;
                let (numerator, denominator) = projective_rcb_batch_fraction(
                    &storage_fractions[row],
                    batch,
                    relations,
                    batch_in_pairs,
                );
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

fn projective_rcb_batch_fraction(
    fractions: &[ProjectiveRcbFractionSpec],
    batch: usize,
    relations: &ProjectiveRcbMulComponentRelations,
    batch_in_pairs: bool,
) -> (SecureField, SecureField) {
    if !batch_in_pairs {
        return fractions
            .get(batch)
            .map(|fraction| projective_rcb_fraction(fraction, relations))
            .unwrap_or_else(zero_fraction);
    }
    let first = fractions
        .get(2 * batch)
        .map(|fraction| projective_rcb_fraction(fraction, relations));
    let second = fractions
        .get(2 * batch + 1)
        .map(|fraction| projective_rcb_fraction(fraction, relations));
    match (first, second) {
        (Some((n0, d0)), Some((n1, d1))) => (n0 * d1 + n1 * d0, d0 * d1),
        (Some(fraction), None) | (None, Some(fraction)) => fraction,
        (None, None) => zero_fraction(),
    }
}

fn projective_rcb_fraction(
    fraction: &ProjectiveRcbFractionSpec,
    relations: &ProjectiveRcbMulComponentRelations,
) -> (SecureField, SecureField) {
    let denominator = match fraction.relation {
        ProjectiveRcbRelationKind::Range13 => relations.range13.combine(&fraction.values),
        ProjectiveRcbRelationKind::RawProductCarry16 => {
            relations.raw_product_carry16.combine(&fraction.values)
        }
        ProjectiveRcbRelationKind::SignedCarry => relations.signed_carry.combine(&fraction.values),
        ProjectiveRcbRelationKind::MulLimb => relations.mul_limb.combine(&fraction.values),
        ProjectiveRcbRelationKind::MulResult => relations.mul_result.combine(&fraction.values),
        ProjectiveRcbRelationKind::RawProductChunkDigit => {
            relations.raw_product_chunk_digit.combine(&fraction.values)
        }
        ProjectiveRcbRelationKind::FoldedContribution => {
            relations.folded_contribution.combine(&fraction.values)
        }
        ProjectiveRcbRelationKind::FoldedDigit => relations.folded_digit.combine(&fraction.values),
        ProjectiveRcbRelationKind::FoldedCarry => relations.folded_carry.combine(&fraction.values),
    };
    (secure_from_i64(fraction.numerator), denominator)
}

fn zero_fraction() -> (SecureField, SecureField) {
    (secure_zero(), secure_one())
}

pub(crate) fn projective_rcb_mul_row_fractions(
    source_index: usize,
    mul_index: usize,
    mul: &ProjectiveRcbMulRow,
) -> Vec<ProjectiveRcbFractionSpec> {
    let mut fractions = Vec::with_capacity(projective_rcb_mul_fraction_count());
    for (role, limbs, multiplicity) in [
        (
            PROJECTIVE_RCB_MUL_ROLE_LHS,
            mul.trace.lhs.limbs(),
            -(N_LIMBS as i64),
        ),
        (
            PROJECTIVE_RCB_MUL_ROLE_RHS,
            mul.trace.rhs.limbs(),
            -(N_LIMBS as i64),
        ),
    ] {
        for (limb_index, limb) in limbs.iter().enumerate() {
            fractions.push(range13_fraction(1, *limb));
            fractions.push(mul_limb_fraction(
                multiplicity,
                source_index,
                mul_index,
                role,
                limb_index,
                *limb,
            ));
        }
    }
    for limb in mul.trace.result.limbs() {
        fractions.push(range13_fraction(1, *limb));
    }
    for row in &mul.reduction.rows {
        fractions.push(range13_fraction(1, m31(row.folded_digit)));
        fractions.push(range13_fraction(1, m31(row.result_limb)));
        fractions.push(signed_carry_fraction(1, m31_i128(row.prev_carry)));
        fractions.push(signed_carry_fraction(1, m31_i128(row.carry)));
    }
    // C1: Range13 consumers for the nine 13-bit correction digits, emitted by
    // `add_fp_solinas_correction_digit_binding` immediately after the per-digit
    // reduction fractions and before the folded-digit relation fractions.
    let (_, correction_digits) = fp_solinas_correction_digit_columns(mul.trace.correction)
        .expect("mul trace correction fits the signed window");
    for digit in correction_digits {
        fractions.push(range13_fraction(1, m31(digit)));
    }
    for row in &mul.reduction.rows {
        fractions.push(folded_digit_fraction(
            1,
            source_index,
            mul_index,
            row.digit_index,
            m31(row.folded_digit),
        ));
    }
    fractions.push(folded_carry_fraction(
        -1,
        source_index,
        mul_index,
        0,
        m31(0),
    ));
    fractions.push(folded_carry_fraction(
        1,
        source_index,
        mul_index,
        FP_SOLINAS_REDUCTION_DIGITS,
        m31_i128(mul.folded_digits.final_carry),
    ));
    debug_assert_eq!(fractions.len(), projective_rcb_mul_fraction_count());
    fractions
}

/// C5 plumbing: the SILO's per-mul fractions = the shared mul-family fractions
/// PLUS the `ProjectiveRcbMulResultRelation` provider yields (one `-1` per limb
/// of `lhs`/`rhs`/`result`). Appended LAST so the order matches the silo AIR
/// (`add_projective_rcb_mul_row` then the three `provide_mul_result_limbs`
/// calls) under one `finalize_logup`. NOT used by `final_add`/`public_key_curve`
/// — they reuse `projective_rcb_mul_row_fractions` (without the provider) and
/// have their own result relations.
pub(crate) fn projective_rcb_silo_mul_row_fractions(
    source_index: usize,
    mul_index: usize,
    mul: &ProjectiveRcbMulRow,
) -> Vec<ProjectiveRcbFractionSpec> {
    let mut fractions = projective_rcb_mul_row_fractions(source_index, mul_index, mul);
    for (role, limbs) in [
        (PROJECTIVE_RCB_MUL_ROLE_LHS, mul.trace.lhs.limbs()),
        (PROJECTIVE_RCB_MUL_ROLE_RHS, mul.trace.rhs.limbs()),
        (PROJECTIVE_RCB_MUL_ROLE_RESULT, mul.trace.result.limbs()),
    ] {
        for (limb_index, limb) in limbs.iter().enumerate() {
            fractions.push(mul_result_fraction(
                -1,
                source_index,
                mul_index,
                role,
                limb_index,
                *limb,
            ));
        }
    }
    debug_assert_eq!(fractions.len(), projective_rcb_silo_mul_fraction_count());
    fractions
}

/// SILO per-mul fraction count: shared mul-family + the `3 * N_LIMBS`
/// `ProjectiveRcbMulResultRelation` provider yields.
pub(crate) fn projective_rcb_silo_mul_fraction_count() -> usize {
    projective_rcb_mul_fraction_count() + 3 * N_LIMBS
}

/// SILO mul-family padding fractions (one zero per silo mul fraction).
pub(crate) fn projective_rcb_silo_mul_padding_fractions() -> Vec<ProjectiveRcbFractionSpec> {
    zeroed_projective_rcb_fractions(projective_rcb_silo_mul_fraction_count())
}

/// Number of LogUp fractions a single mul row emits inside the mul family.
///
/// Exposed so adapters that swap a custom evaluator in for
/// [`ProjectiveRcbMulEval`] (see `public_key_curve_air`) can pad and size
/// their interaction traces to match the shared mul family.
pub(crate) fn projective_rcb_mul_row_fraction_count() -> usize {
    projective_rcb_mul_fraction_count()
}

/// Evaluated `(numerator, denominator)` LogUp pairs for one mul row, in the
/// exact order [`add_projective_rcb_mul_row`] emits them with a single
/// `finalize_logup`.
///
/// This hides [`ProjectiveRcbFractionSpec`] internals so an adapter component
/// can build a combined interaction trace (these standard pairs followed by
/// its own provider pairs) inside one [`LogupTraceGenerator`].
pub(crate) fn projective_rcb_mul_row_fraction_pairs(
    source_index: usize,
    mul_index: usize,
    mul: &ProjectiveRcbMulRow,
    relations: &ProjectiveRcbMulComponentRelations,
) -> Vec<(SecureField, SecureField)> {
    projective_rcb_mul_row_fractions(source_index, mul_index, mul)
        .iter()
        .map(|fraction| projective_rcb_fraction(fraction, relations))
        .collect()
}

/// Padding `(numerator, denominator)` pairs for an inactive mul row: a
/// zero numerator over a unit denominator, repeated for every standard mul
/// fraction.
pub(crate) fn projective_rcb_mul_padding_fraction_pairs() -> Vec<(SecureField, SecureField)> {
    (0..projective_rcb_mul_fraction_count())
        .map(|_| zero_fraction())
        .collect()
}

pub(crate) fn projective_rcb_raw_product_chunk_fractions(
    row: &ProjectiveRcbRawProductChunkRow,
) -> Vec<ProjectiveRcbFractionSpec> {
    let mut fractions = Vec::with_capacity(projective_rcb_raw_product_chunk_fraction_count());
    for term in &row.terms {
        let active = i64::from(term.active);
        fractions.push(mul_limb_fraction(
            active,
            row.source_index,
            row.mul_index,
            PROJECTIVE_RCB_MUL_ROLE_LHS,
            term.lhs_index,
            m31(term.lhs_limb),
        ));
        fractions.push(mul_limb_fraction(
            active,
            row.source_index,
            row.mul_index,
            PROJECTIVE_RCB_MUL_ROLE_RHS,
            term.rhs_index,
            m31(term.rhs_limb),
        ));
    }
    for digit in row.digits {
        fractions.push(range13_fraction(1, m31(digit)));
    }
    fractions.push(raw_product_carry16_fraction(1, m31(row.carry1)));
    for (offset, digit) in row.digits.iter().enumerate() {
        fractions.push(raw_product_chunk_digit_fraction(
            -(row.digit_use_counts[offset] as i64),
            row.source_index,
            row.mul_index,
            row.coeff,
            row.chunk,
            offset,
            m31(*digit),
        ));
    }
    debug_assert_eq!(
        fractions.len(),
        projective_rcb_raw_product_chunk_fraction_count()
    );
    fractions
}

pub(crate) fn projective_rcb_folded_contribution_fractions(
    row: &ProjectiveRcbFoldedContributionRow,
) -> Vec<ProjectiveRcbFractionSpec> {
    let mut fractions = Vec::with_capacity(projective_rcb_folded_contribution_fraction_count());
    for term in &row.terms {
        fractions.push(raw_product_chunk_digit_fraction(
            i64::from(term.active),
            row.source_index,
            row.mul_index,
            term.raw_coeff,
            term.raw_chunk,
            term.raw_offset,
            m31(term.raw_digit),
        ));
    }
    fractions.push(folded_contribution_fraction(
        -1,
        row.source_index,
        row.mul_index,
        row.digit_index,
        row.group_index,
        m31_i128(row.contribution_sum),
    ));
    debug_assert_eq!(
        fractions.len(),
        projective_rcb_folded_contribution_fraction_count()
    );
    fractions
}

pub(crate) fn projective_rcb_folded_digit_fractions(
    row: &ProjectiveRcbFoldedDigitRow,
) -> Vec<ProjectiveRcbFractionSpec> {
    let mut fractions = Vec::with_capacity(projective_rcb_folded_digit_fraction_count());
    for group in &row.contribution_groups {
        fractions.push(folded_contribution_fraction(
            i64::from(group.active),
            row.source_index,
            row.mul_index,
            row.digit_index,
            group.group_index,
            m31_i128(group.contribution_sum),
        ));
    }
    fractions.push(range13_fraction(1, m31(row.folded_digit)));
    fractions.push(signed_carry_fraction(1, m31_i128(row.prev_carry)));
    fractions.push(signed_carry_fraction(1, m31_i128(row.carry)));
    fractions.push(folded_carry_fraction(
        1,
        row.source_index,
        row.mul_index,
        row.digit_index,
        m31_i128(row.prev_carry),
    ));
    fractions.push(folded_carry_fraction(
        -1,
        row.source_index,
        row.mul_index,
        row.digit_index + 1,
        m31_i128(row.carry),
    ));
    fractions.push(folded_digit_fraction(
        -1,
        row.source_index,
        row.mul_index,
        row.digit_index,
        m31(row.folded_digit),
    ));
    debug_assert_eq!(
        fractions.len(),
        projective_rcb_folded_digit_fraction_count()
    );
    fractions
}

pub(crate) fn projective_rcb_raw_product_chunk_padding_fractions() -> Vec<ProjectiveRcbFractionSpec>
{
    zeroed_projective_rcb_fractions(projective_rcb_raw_product_chunk_fraction_count())
}

pub(crate) fn projective_rcb_folded_contribution_padding_fractions(
) -> Vec<ProjectiveRcbFractionSpec> {
    zeroed_projective_rcb_fractions(projective_rcb_folded_contribution_fraction_count())
}

pub(crate) fn projective_rcb_folded_digit_padding_fractions() -> Vec<ProjectiveRcbFractionSpec> {
    zeroed_projective_rcb_fractions(projective_rcb_folded_digit_fraction_count())
}

fn zeroed_projective_rcb_fractions(count: usize) -> Vec<ProjectiveRcbFractionSpec> {
    (0..count).map(|_| range13_fraction(0, m31(0))).collect()
}

fn projective_rcb_mul_fraction_count() -> usize {
    2 * N_LIMBS * 2
        + N_LIMBS
        + 4 * FP_SOLINAS_REDUCTION_DIGITS
        + FP_SOLINAS_SIGNED_CORRECTION_LIMBS
        + FP_SOLINAS_REDUCTION_DIGITS
        + 2
}

fn projective_rcb_raw_product_chunk_fraction_count() -> usize {
    2 * PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS + 2 * PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS + 1
}

fn projective_rcb_folded_contribution_fraction_count() -> usize {
    PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS + 1
}

fn projective_rcb_folded_digit_fraction_count() -> usize {
    PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS + 6
}

pub(crate) fn projective_rcb_mul_interaction_columns() -> usize {
    // The SILO mul family emits the shared mul fractions PLUS the C5
    // `ProjectiveRcbMulResultRelation` provider yields, so its interaction width
    // uses the silo count. (`final_add`/`public_key_curve` size their own mul
    // families with `projective_rcb_mul_row_fraction_count`.)
    QM31_TRACE_COLUMNS * projective_rcb_silo_mul_fraction_count()
}

pub(crate) fn projective_rcb_raw_product_chunk_interaction_columns() -> usize {
    QM31_TRACE_COLUMNS * projective_rcb_raw_product_chunk_fraction_count().div_ceil(2)
}

pub(crate) fn projective_rcb_folded_contribution_interaction_columns() -> usize {
    QM31_TRACE_COLUMNS * projective_rcb_folded_contribution_fraction_count()
}

pub(crate) fn projective_rcb_folded_digit_interaction_columns() -> usize {
    QM31_TRACE_COLUMNS * projective_rcb_folded_digit_fraction_count()
}

fn range13_fraction(numerator: i64, value: M31) -> ProjectiveRcbFractionSpec {
    ProjectiveRcbFractionSpec {
        relation: ProjectiveRcbRelationKind::Range13,
        numerator,
        values: vec![value],
    }
}

fn raw_product_carry16_fraction(numerator: i64, value: M31) -> ProjectiveRcbFractionSpec {
    ProjectiveRcbFractionSpec {
        relation: ProjectiveRcbRelationKind::RawProductCarry16,
        numerator,
        values: vec![value],
    }
}

fn signed_carry_fraction(numerator: i64, value: M31) -> ProjectiveRcbFractionSpec {
    ProjectiveRcbFractionSpec {
        relation: ProjectiveRcbRelationKind::SignedCarry,
        numerator,
        values: vec![value],
    }
}

fn mul_limb_fraction(
    numerator: i64,
    source_index: usize,
    mul_index: usize,
    role: u32,
    limb_index: usize,
    limb: M31,
) -> ProjectiveRcbFractionSpec {
    ProjectiveRcbFractionSpec {
        relation: ProjectiveRcbRelationKind::MulLimb,
        numerator,
        values: vec![
            m31_usize(source_index),
            m31_usize(mul_index),
            m31(role),
            m31_usize(limb_index),
            limb,
        ],
    }
}

fn mul_result_fraction(
    numerator: i64,
    source_index: usize,
    mul_index: usize,
    role: u32,
    limb_index: usize,
    limb: M31,
) -> ProjectiveRcbFractionSpec {
    ProjectiveRcbFractionSpec {
        relation: ProjectiveRcbRelationKind::MulResult,
        numerator,
        values: vec![
            m31_usize(source_index),
            m31_usize(mul_index),
            m31(role),
            m31_usize(limb_index),
            limb,
        ],
    }
}

fn raw_product_chunk_digit_fraction(
    numerator: i64,
    source_index: usize,
    mul_index: usize,
    coeff: usize,
    chunk: usize,
    offset: usize,
    digit: M31,
) -> ProjectiveRcbFractionSpec {
    ProjectiveRcbFractionSpec {
        relation: ProjectiveRcbRelationKind::RawProductChunkDigit,
        numerator,
        values: vec![
            m31_usize(source_index),
            m31_usize(mul_index),
            m31_usize(coeff),
            m31_usize(chunk),
            m31_usize(offset),
            digit,
        ],
    }
}

fn folded_contribution_fraction(
    numerator: i64,
    source_index: usize,
    mul_index: usize,
    digit_index: usize,
    group_index: usize,
    contribution_sum: M31,
) -> ProjectiveRcbFractionSpec {
    ProjectiveRcbFractionSpec {
        relation: ProjectiveRcbRelationKind::FoldedContribution,
        numerator,
        values: vec![
            m31_usize(source_index),
            m31_usize(mul_index),
            m31_usize(digit_index),
            m31_usize(group_index),
            contribution_sum,
        ],
    }
}

fn folded_digit_fraction(
    numerator: i64,
    source_index: usize,
    mul_index: usize,
    digit_index: usize,
    folded_digit: M31,
) -> ProjectiveRcbFractionSpec {
    ProjectiveRcbFractionSpec {
        relation: ProjectiveRcbRelationKind::FoldedDigit,
        numerator,
        values: vec![
            m31_usize(source_index),
            m31_usize(mul_index),
            m31_usize(digit_index),
            folded_digit,
        ],
    }
}

fn folded_carry_fraction(
    numerator: i64,
    source_index: usize,
    mul_index: usize,
    digit_index: usize,
    carry: M31,
) -> ProjectiveRcbFractionSpec {
    ProjectiveRcbFractionSpec {
        relation: ProjectiveRcbRelationKind::FoldedCarry,
        numerator,
        values: vec![
            m31_usize(source_index),
            m31_usize(mul_index),
            m31_usize(digit_index),
            carry,
        ],
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbAirInteractionClaim {
    pub mul_limb: SecureField,
    pub raw_product_chunk_digit: SecureField,
    pub folded_contribution: SecureField,
    pub folded_digit: SecureField,
    pub folded_carry: SecureField,
}

impl ProjectiveRcbAirInteractionClaim {
    pub fn from_trace(
        trace: &ProjectiveRcbAirTraceClaim,
        relations: &ProjectiveRcbMulComponentRelations,
    ) -> Self {
        let mut claim = Self::zero();
        for row in &trace.rows {
            for (mul_index, mul) in row.muls.iter().enumerate() {
                claim.add_mul_limb_fractions(row.source_index, mul_index, mul, relations);
                claim.add_raw_product_fractions(mul, relations);
                claim.add_folded_contribution_fractions(mul, relations);
                claim.add_folded_digit_fractions(row.source_index, mul_index, mul, relations);
                claim.add_folded_carry_fractions(row.source_index, mul_index, mul, relations);
            }
        }
        claim
    }

    pub fn zero() -> Self {
        let zero = secure_zero();
        Self {
            mul_limb: zero,
            raw_product_chunk_digit: zero,
            folded_contribution: zero,
            folded_digit: zero,
            folded_carry: zero,
        }
    }

    pub fn verify_balanced(&self) -> Result<(), ProjectiveRcbAirError> {
        verify_relation_zero("ProjectiveRcbMulLimb", self.mul_limb)?;
        verify_relation_zero(
            "ProjectiveRcbRawProductChunkDigit",
            self.raw_product_chunk_digit,
        )?;
        verify_relation_zero("ProjectiveRcbFoldedContribution", self.folded_contribution)?;
        verify_relation_zero("ProjectiveRcbFoldedDigit", self.folded_digit)?;
        verify_relation_zero("ProjectiveRcbFoldedCarry", self.folded_carry)
    }

    fn add_mul_limb_fractions(
        &mut self,
        source_index: usize,
        mul_index: usize,
        mul: &ProjectiveRcbMulRow,
        relations: &ProjectiveRcbMulComponentRelations,
    ) {
        for (role, limbs) in [
            (PROJECTIVE_RCB_MUL_ROLE_LHS, mul.trace.lhs.limbs()),
            (PROJECTIVE_RCB_MUL_ROLE_RHS, mul.trace.rhs.limbs()),
        ] {
            for (limb_index, limb) in limbs.iter().enumerate() {
                self.mul_limb += relation_fraction(
                    &relations.mul_limb,
                    -(N_LIMBS as i64),
                    &[
                        m31_usize(source_index),
                        m31_usize(mul_index),
                        m31(role),
                        m31_usize(limb_index),
                        *limb,
                    ],
                );
            }
        }
        for chunk in &mul.raw_product_chunks {
            for term in &chunk.terms {
                if term.active {
                    self.mul_limb += relation_fraction(
                        &relations.mul_limb,
                        1,
                        &[
                            m31_usize(chunk.source_index),
                            m31_usize(chunk.mul_index),
                            m31(PROJECTIVE_RCB_MUL_ROLE_LHS),
                            m31_usize(term.lhs_index),
                            m31(term.lhs_limb),
                        ],
                    );
                    self.mul_limb += relation_fraction(
                        &relations.mul_limb,
                        1,
                        &[
                            m31_usize(chunk.source_index),
                            m31_usize(chunk.mul_index),
                            m31(PROJECTIVE_RCB_MUL_ROLE_RHS),
                            m31_usize(term.rhs_index),
                            m31(term.rhs_limb),
                        ],
                    );
                }
            }
        }
    }

    fn add_raw_product_fractions(
        &mut self,
        mul: &ProjectiveRcbMulRow,
        relations: &ProjectiveRcbMulComponentRelations,
    ) {
        for chunk in &mul.raw_product_chunks {
            for (offset, digit) in chunk.digits.iter().enumerate() {
                let use_count = chunk.digit_use_counts[offset] as i64;
                if use_count != 0 {
                    self.raw_product_chunk_digit += relation_fraction(
                        &relations.raw_product_chunk_digit,
                        -use_count,
                        &[
                            m31_usize(chunk.source_index),
                            m31_usize(chunk.mul_index),
                            m31_usize(chunk.coeff),
                            m31_usize(chunk.chunk),
                            m31_usize(offset),
                            m31(*digit),
                        ],
                    );
                }
            }
        }
        for row in &mul.folded_contributions.rows {
            for term in &row.terms {
                if term.active {
                    self.raw_product_chunk_digit += relation_fraction(
                        &relations.raw_product_chunk_digit,
                        1,
                        &[
                            m31_usize(row.source_index),
                            m31_usize(row.mul_index),
                            m31_usize(term.raw_coeff),
                            m31_usize(term.raw_chunk),
                            m31_usize(term.raw_offset),
                            m31(term.raw_digit),
                        ],
                    );
                }
            }
        }
    }

    fn add_folded_contribution_fractions(
        &mut self,
        mul: &ProjectiveRcbMulRow,
        relations: &ProjectiveRcbMulComponentRelations,
    ) {
        for row in &mul.folded_contributions.rows {
            self.folded_contribution += relation_fraction(
                &relations.folded_contribution,
                -1,
                &[
                    m31_usize(row.source_index),
                    m31_usize(row.mul_index),
                    m31_usize(row.digit_index),
                    m31_usize(row.group_index),
                    m31_i128(row.contribution_sum),
                ],
            );
        }
        for row in &mul.folded_digits.rows {
            for group in &row.contribution_groups {
                if group.active {
                    self.folded_contribution += relation_fraction(
                        &relations.folded_contribution,
                        1,
                        &[
                            m31_usize(row.source_index),
                            m31_usize(row.mul_index),
                            m31_usize(row.digit_index),
                            m31_usize(group.group_index),
                            m31_i128(group.contribution_sum),
                        ],
                    );
                }
            }
        }
    }

    fn add_folded_digit_fractions(
        &mut self,
        source_index: usize,
        mul_index: usize,
        mul: &ProjectiveRcbMulRow,
        relations: &ProjectiveRcbMulComponentRelations,
    ) {
        for row in &mul.folded_digits.rows {
            self.folded_digit += relation_fraction(
                &relations.folded_digit,
                -1,
                &[
                    m31_usize(row.source_index),
                    m31_usize(row.mul_index),
                    m31_usize(row.digit_index),
                    m31(row.folded_digit),
                ],
            );
        }
        for row in &mul.reduction.rows {
            self.folded_digit += relation_fraction(
                &relations.folded_digit,
                1,
                &[
                    m31_usize(source_index),
                    m31_usize(mul_index),
                    m31_usize(row.digit_index),
                    m31(row.folded_digit),
                ],
            );
        }
    }

    fn add_folded_carry_fractions(
        &mut self,
        source_index: usize,
        mul_index: usize,
        mul: &ProjectiveRcbMulRow,
        relations: &ProjectiveRcbMulComponentRelations,
    ) {
        self.folded_carry += relation_fraction(
            &relations.folded_carry,
            -1,
            &[
                m31_usize(source_index),
                m31_usize(mul_index),
                m31(0),
                m31(0),
            ],
        );
        self.folded_carry += relation_fraction(
            &relations.folded_carry,
            1,
            &[
                m31_usize(source_index),
                m31_usize(mul_index),
                m31_usize(FP_SOLINAS_REDUCTION_DIGITS),
                m31_i128(mul.folded_digits.final_carry),
            ],
        );
        for row in &mul.folded_digits.rows {
            self.folded_carry += relation_fraction(
                &relations.folded_carry,
                1,
                &[
                    m31_usize(row.source_index),
                    m31_usize(row.mul_index),
                    m31_usize(row.digit_index),
                    m31_i128(row.prev_carry),
                ],
            );
            self.folded_carry += relation_fraction(
                &relations.folded_carry,
                -1,
                &[
                    m31_usize(row.source_index),
                    m31_usize(row.mul_index),
                    m31_usize(row.digit_index + 1),
                    m31_i128(row.carry),
                ],
            );
        }
    }
}

pub(crate) fn relation_fraction<R: Relation<M31, SecureField>>(
    relation: &R,
    numerator: i64,
    values: &[M31],
) -> SecureField {
    secure_from_i64(numerator) / relation.combine(values)
}

/// C5 plumbing: the silo's `ProjectiveRcbMulResultRelation` provider claimed sum
/// (yield, `-1` per limb of `lhs`/`rhs`/`result` of every mul). Computed
/// analytically over the trace so the proof balance can net it against the two
/// projective-source consumers. This sum is ALSO part of `components.mul` (the
/// mul-family interaction column), but is exposed separately because it crosses
/// the silo boundary and must NOT net to zero internally.
pub(crate) fn projective_rcb_mul_result_provider_sum(
    trace: &ProjectiveRcbAirTraceClaim,
    relations: &ProjectiveRcbMulComponentRelations,
) -> SecureField {
    let mut sum = secure_zero();
    for row in &trace.rows {
        for (mul_index, mul) in row.muls.iter().enumerate() {
            for (role, limbs) in [
                (PROJECTIVE_RCB_MUL_ROLE_LHS, mul.trace.lhs.limbs()),
                (PROJECTIVE_RCB_MUL_ROLE_RHS, mul.trace.rhs.limbs()),
                (PROJECTIVE_RCB_MUL_ROLE_RESULT, mul.trace.result.limbs()),
            ] {
                for (limb_index, limb) in limbs.iter().enumerate() {
                    sum += relation_fraction(
                        &relations.mul_result,
                        -1,
                        &[
                            m31_usize(row.source_index),
                            m31_usize(mul_index),
                            m31(role),
                            m31_usize(limb_index),
                            *limb,
                        ],
                    );
                }
            }
        }
    }
    sum
}
