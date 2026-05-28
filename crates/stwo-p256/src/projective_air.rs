use stwo::core::fields::m31::M31;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry,
};
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};

use crate::constants::{P256_B, P256_MODULUS};
use crate::field_ops::{add_mod_witness, sub_mod_witness};
use crate::fp_solinas::{
    FpSolinasError, FpSolinasMulTrace, FP_SOLINAS_LIMB_BASE, FP_SOLINAS_RAW_LIMBS,
    M31_CENTERED_BOUND,
};
use crate::fp_solinas_air::{
    add_fp_solinas_reduction_digit, FpSolinasReductionDigitColumns, FpSolinasReductionRelations,
    FpSolinasReductionTraceClaim, FpSolinasReductionTraceError, FP_SOLINAS_REDUCTION_DIGITS,
    FP_SOLINAS_REDUCTION_DIGIT_TRACE_COLUMNS,
};
use crate::limbs::{EvalP256BigIntExt, P256EvalBigInt};
use crate::prepared_table::PreparedAffinePoint;
use crate::projective::{
    ProjectiveEcError, ProjectiveEcOp, ProjectiveEcRow, ProjectiveEcTraceClaim, ProjectivePoint,
};
use crate::range_checks::{add_range_check, RangeCheckRelation};
use crate::types::U256;

pub type ProjectiveRcbMulComponent = FrameworkComponent<ProjectiveRcbMulEval>;
pub type ProjectiveRcbRawProductChunkComponent =
    FrameworkComponent<ProjectiveRcbRawProductChunkEval>;

pub const PROJECTIVE_RCB_MUL_LIMB_RELATION_ARITY: usize = 5;
pub const PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGIT_RELATION_ARITY: usize = 6;
pub const PROJECTIVE_RCB_MUL_ROLE_LHS: u32 = 0;
pub const PROJECTIVE_RCB_MUL_ROLE_RHS: u32 = 1;
pub const PROJECTIVE_RCB_MUL_ROLE_RESULT: u32 = 2;
pub const PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS: usize = 2;
pub const PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS: usize = 3;
pub const PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS: usize = raw_product_chunk_count();
pub const PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERM_TRACE_COLUMNS: usize = 5;
pub const PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS: usize = 1
    + 2
    + 2
    + PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS * PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERM_TRACE_COLUMNS
    + PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS;
pub const PROJECTIVE_RCB_MUL_ID_TRACE_COLUMNS: usize = 2;
pub const PROJECTIVE_RCB_MUL_ACTIVE_TRACE_COLUMNS: usize = 1;
pub const PROJECTIVE_RCB_MUL_LIMB_TRACE_COLUMNS: usize = 3 * N_LIMBS;
pub const PROJECTIVE_RCB_MUL_REDUCTION_TRACE_COLUMNS: usize =
    FP_SOLINAS_REDUCTION_DIGITS * FP_SOLINAS_REDUCTION_DIGIT_TRACE_COLUMNS + 1;
pub const PROJECTIVE_RCB_MUL_TRACE_COLUMNS: usize = PROJECTIVE_RCB_MUL_ACTIVE_TRACE_COLUMNS
    + PROJECTIVE_RCB_MUL_ID_TRACE_COLUMNS
    + PROJECTIVE_RCB_MUL_LIMB_TRACE_COLUMNS
    + PROJECTIVE_RCB_MUL_REDUCTION_TRACE_COLUMNS;

relation!(
    ProjectiveRcbMulLimbRelation,
    PROJECTIVE_RCB_MUL_LIMB_RELATION_ARITY
);
relation!(
    ProjectiveRcbRawProductChunkDigitRelation,
    PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGIT_RELATION_ARITY
);

#[derive(Clone)]
pub struct ProjectiveRcbMulEval {
    pub log_size: u32,
    pub relations: ProjectiveRcbMulComponentRelations,
}

impl FrameworkEval for ProjectiveRcbMulEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.next_trace_mask();
        let source_index = eval.next_trace_mask();
        let mul_index = eval.next_trace_mask();
        let columns = ProjectiveRcbMulColumns::read(&mut eval);

        eval.add_constraint(active.clone() * (one::<E>() - active.clone()));
        add_projective_rcb_mul_row(
            &mut eval,
            self.relations.as_refs(),
            active,
            source_index,
            mul_index,
            &columns,
        );
        eval.finalize_logup_in_pairs();
        eval
    }
}

#[derive(Clone)]
pub struct ProjectiveRcbRawProductChunkEval {
    pub log_size: u32,
    pub relations: ProjectiveRcbMulComponentRelations,
}

impl FrameworkEval for ProjectiveRcbRawProductChunkEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let columns = ProjectiveRcbRawProductChunkColumns::read(&mut eval);

        eval.add_constraint(columns.active.clone() * (one::<E>() - columns.active.clone()));
        add_projective_rcb_raw_product_chunk(&mut eval, self.relations.as_refs(), &columns);
        eval.finalize_logup_in_pairs();
        eval
    }
}

#[derive(Clone)]
pub struct ProjectiveRcbMulComponentRelations {
    pub range13: RangeCheckRelation,
    pub signed_carry: RangeCheckRelation,
    pub mul_limb: ProjectiveRcbMulLimbRelation,
    pub raw_product_chunk_digit: ProjectiveRcbRawProductChunkDigitRelation,
}

impl ProjectiveRcbMulComponentRelations {
    pub fn dummy() -> Self {
        Self {
            range13: RangeCheckRelation::dummy(),
            signed_carry: RangeCheckRelation::dummy(),
            mul_limb: ProjectiveRcbMulLimbRelation::dummy(),
            raw_product_chunk_digit: ProjectiveRcbRawProductChunkDigitRelation::dummy(),
        }
    }

    pub fn as_refs(&self) -> ProjectiveRcbMulRelations<'_> {
        ProjectiveRcbMulRelations {
            range13: &self.range13,
            signed_carry: &self.signed_carry,
            mul_limb: &self.mul_limb,
            raw_product_chunk_digit: &self.raw_product_chunk_digit,
        }
    }
}

#[derive(Clone, Copy)]
pub struct ProjectiveRcbMulRelations<'a> {
    pub range13: &'a RangeCheckRelation,
    pub signed_carry: &'a RangeCheckRelation,
    pub mul_limb: &'a ProjectiveRcbMulLimbRelation,
    pub raw_product_chunk_digit: &'a ProjectiveRcbRawProductChunkDigitRelation,
}

pub struct ProjectiveRcbMulColumns<E: EvalAtRow> {
    pub lhs: P256EvalBigInt<E>,
    pub rhs: P256EvalBigInt<E>,
    pub result: P256EvalBigInt<E>,
    pub folded_final_carry: E::F,
    pub reduction: [FpSolinasReductionDigitColumns<E>; FP_SOLINAS_REDUCTION_DIGITS],
}

impl<E: EvalAtRow> ProjectiveRcbMulColumns<E> {
    fn read(eval: &mut E) -> Self {
        Self {
            lhs: eval.next_p256_bigint(),
            rhs: eval.next_p256_bigint(),
            result: eval.next_p256_bigint(),
            folded_final_carry: eval.next_trace_mask(),
            reduction: core::array::from_fn(|_| FpSolinasReductionDigitColumns {
                folded_digit: eval.next_trace_mask(),
                correction_product_digit: eval.next_trace_mask(),
                result_limb: eval.next_trace_mask(),
                prev_carry: eval.next_trace_mask(),
                carry: eval.next_trace_mask(),
            }),
        }
    }
}

pub fn add_projective_rcb_mul_row<E: EvalAtRow>(
    eval: &mut E,
    relations: ProjectiveRcbMulRelations<'_>,
    gate: E::F,
    source_index: E::F,
    mul_index: E::F,
    columns: &ProjectiveRcbMulColumns<E>,
) {
    add_mul_limb_group(
        eval,
        relations,
        gate.clone(),
        source_index.clone(),
        mul_index.clone(),
        PROJECTIVE_RCB_MUL_ROLE_LHS,
        &columns.lhs,
    );
    add_mul_limb_group(
        eval,
        relations,
        gate.clone(),
        source_index.clone(),
        mul_index.clone(),
        PROJECTIVE_RCB_MUL_ROLE_RHS,
        &columns.rhs,
    );
    add_mul_limb_group(
        eval,
        relations,
        gate.clone(),
        source_index,
        mul_index,
        PROJECTIVE_RCB_MUL_ROLE_RESULT,
        &columns.result,
    );

    let reduction_relations = FpSolinasReductionRelations {
        range13: relations.range13,
        signed_carry: relations.signed_carry,
    };
    for row in &columns.reduction {
        add_fp_solinas_reduction_digit(eval, reduction_relations, gate.clone(), row);
    }

    eval.add_constraint(gate.clone() * columns.reduction[0].prev_carry.clone());
    for digit_index in 1..FP_SOLINAS_REDUCTION_DIGITS {
        eval.add_constraint(
            gate.clone()
                * (columns.reduction[digit_index].prev_carry.clone()
                    - columns.reduction[digit_index - 1].carry.clone()),
        );
    }
    eval.add_constraint(
        gate.clone()
            * columns.folded_final_carry.clone()
            * (columns.folded_final_carry.clone() + one::<E>()),
    );
    eval.add_constraint(
        gate * (columns.reduction[FP_SOLINAS_REDUCTION_DIGITS - 1]
            .carry
            .clone()
            + columns.folded_final_carry.clone()),
    );
}

pub struct ProjectiveRcbRawProductChunkColumns<E: EvalAtRow> {
    pub active: E::F,
    pub source_index: E::F,
    pub mul_index: E::F,
    pub coeff: E::F,
    pub chunk: E::F,
    pub terms: [ProjectiveRcbRawProductTermColumns<E>; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS],
    pub digits: [E::F; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS],
}

impl<E: EvalAtRow> ProjectiveRcbRawProductChunkColumns<E> {
    fn read(eval: &mut E) -> Self {
        Self {
            active: eval.next_trace_mask(),
            source_index: eval.next_trace_mask(),
            mul_index: eval.next_trace_mask(),
            coeff: eval.next_trace_mask(),
            chunk: eval.next_trace_mask(),
            terms: core::array::from_fn(|_| ProjectiveRcbRawProductTermColumns {
                term_active: eval.next_trace_mask(),
                lhs_index: eval.next_trace_mask(),
                rhs_index: eval.next_trace_mask(),
                lhs_limb: eval.next_trace_mask(),
                rhs_limb: eval.next_trace_mask(),
            }),
            digits: core::array::from_fn(|_| eval.next_trace_mask()),
        }
    }
}

pub struct ProjectiveRcbRawProductTermColumns<E: EvalAtRow> {
    pub term_active: E::F,
    pub lhs_index: E::F,
    pub rhs_index: E::F,
    pub lhs_limb: E::F,
    pub rhs_limb: E::F,
}

pub fn add_projective_rcb_raw_product_chunk<E: EvalAtRow>(
    eval: &mut E,
    relations: ProjectiveRcbMulRelations<'_>,
    columns: &ProjectiveRcbRawProductChunkColumns<E>,
) {
    let mut product_sum = zero::<E>();
    for term in &columns.terms {
        eval.add_constraint(
            columns.active.clone()
                * term.term_active.clone()
                * (one::<E>() - term.term_active.clone()),
        );
        product_sum += term.term_active.clone() * term.lhs_limb.clone() * term.rhs_limb.clone();
        constrain_unused(
            eval,
            columns.active.clone(),
            term.term_active.clone(),
            term.lhs_limb.clone(),
        );
        constrain_unused(
            eval,
            columns.active.clone(),
            term.term_active.clone(),
            term.rhs_limb.clone(),
        );
        add_projective_rcb_mul_limb_relation(
            eval,
            relations.mul_limb,
            E::EF::from(columns.active.clone() * term.term_active.clone()),
            columns.source_index.clone(),
            columns.mul_index.clone(),
            constant(PROJECTIVE_RCB_MUL_ROLE_LHS),
            term.lhs_index.clone(),
            term.lhs_limb.clone(),
        );
        add_projective_rcb_mul_limb_relation(
            eval,
            relations.mul_limb,
            E::EF::from(columns.active.clone() * term.term_active.clone()),
            columns.source_index.clone(),
            columns.mul_index.clone(),
            constant(PROJECTIVE_RCB_MUL_ROLE_RHS),
            term.rhs_index.clone(),
            term.rhs_limb.clone(),
        );
    }

    add_range_check(
        eval,
        relations.range13,
        columns.active.clone(),
        columns.digits[0].clone(),
    );
    add_range_check(
        eval,
        relations.range13,
        columns.active.clone(),
        columns.digits[1].clone(),
    );
    eval.add_constraint(
        columns.active.clone()
            * columns.digits[2].clone()
            * (columns.digits[2].clone() - one::<E>()),
    );
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    eval.add_constraint(
        columns.active.clone()
            * (product_sum
                - columns.digits[0].clone()
                - limb_base.clone() * columns.digits[1].clone()
                - limb_base.clone() * limb_base * columns.digits[2].clone()),
    );

    for (offset, digit) in columns.digits.iter().enumerate() {
        eval.add_to_relation(RelationEntry::new(
            relations.raw_product_chunk_digit,
            -E::EF::from(columns.active.clone()),
            &[
                columns.source_index.clone(),
                columns.mul_index.clone(),
                columns.coeff.clone(),
                columns.chunk.clone(),
                constant(offset as u32),
                digit.clone(),
            ],
        ));
    }
}

pub const fn projective_rcb_raw_product_chunk_max_abs_expr() -> i128 {
    let product_sum =
        PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS as i128 * (FP_SOLINAS_LIMB_BASE - 1).pow(2);
    product_sum
        + (FP_SOLINAS_LIMB_BASE - 1)
        + FP_SOLINAS_LIMB_BASE * (FP_SOLINAS_LIMB_BASE - 1)
        + FP_SOLINAS_LIMB_BASE * FP_SOLINAS_LIMB_BASE
}

pub fn projective_rcb_raw_product_chunk_fits_m31() -> bool {
    projective_rcb_raw_product_chunk_max_abs_expr() < M31_CENTERED_BOUND
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbAirTraceClaim {
    pub rows: Vec<ProjectiveRcbAirRow>,
}

impl ProjectiveRcbAirTraceClaim {
    pub fn from_projective_trace(
        trace: &ProjectiveEcTraceClaim,
    ) -> Result<Self, ProjectiveRcbAirError> {
        let rows = trace
            .rows
            .iter()
            .enumerate()
            .map(|(source_index, row)| ProjectiveRcbAirRow::from_projective_row(source_index, row))
            .collect::<Result<Vec<_>, _>>()?;
        let claim = Self { rows };
        claim.verify_against_projective_trace(trace)?;
        Ok(claim)
    }

    pub fn verify_against_projective_trace(
        &self,
        trace: &ProjectiveEcTraceClaim,
    ) -> Result<(), ProjectiveRcbAirError> {
        if self.rows.len() != trace.rows.len() {
            return Err(ProjectiveRcbAirError::RowCountMismatch {
                expected: trace.rows.len(),
                actual: self.rows.len(),
            });
        }
        for (source_index, (air_row, projective_row)) in
            self.rows.iter().zip(&trace.rows).enumerate()
        {
            air_row.verify_against_projective_row(source_index, projective_row)?;
        }
        Ok(())
    }

    pub fn active_row_count(&self) -> usize {
        self.rows.len()
    }

    pub fn mul_row_count(&self) -> usize {
        self.rows.iter().map(|row| row.muls.len()).sum()
    }

    pub fn reduction_row_count(&self) -> usize {
        self.rows
            .iter()
            .flat_map(|row| &row.muls)
            .map(|mul| mul.reduction.rows.len())
            .sum()
    }

    pub fn raw_product_chunk_count(&self) -> usize {
        self.rows
            .iter()
            .flat_map(|row| &row.muls)
            .map(|mul| mul.raw_product_chunks.len())
            .sum()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbAirRow {
    pub source_index: usize,
    pub sig_id: M31,
    pub cert_id: M31,
    pub op: ProjectiveEcOp,
    pub output_projective: ProjectivePoint,
    pub muls: Vec<ProjectiveRcbMulRow>,
}

impl ProjectiveRcbAirRow {
    fn from_projective_row(
        source_index: usize,
        row: &ProjectiveEcRow,
    ) -> Result<Self, ProjectiveRcbAirError> {
        row.verify()?;
        let lhs = ProjectivePoint::from_prepared(&row.lhs_affine);
        let mut muls = Vec::with_capacity(PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP);
        let output_projective = match row.op {
            ProjectiveEcOp::Double => rcb_double_with_mul_rows(source_index, &lhs, &mut muls)?,
            ProjectiveEcOp::MixedAdd => {
                rcb_mixed_add_with_mul_rows(source_index, &lhs, &row.rhs_affine, &mut muls)?
            }
        };
        if output_projective != row.output_projective {
            return Err(ProjectiveRcbAirError::ProjectiveOutputMismatch { source_index });
        }
        Ok(Self {
            source_index,
            sig_id: row.sig_id,
            cert_id: row.cert_id,
            op: row.op,
            output_projective,
            muls,
        })
    }

    fn verify_against_projective_row(
        &self,
        source_index: usize,
        row: &ProjectiveEcRow,
    ) -> Result<(), ProjectiveRcbAirError> {
        self.verify()?;
        let expected = Self::from_projective_row(source_index, row)?;
        if self == &expected {
            Ok(())
        } else {
            Err(ProjectiveRcbAirError::TraceRowsMismatch { source_index })
        }
    }

    pub fn verify(&self) -> Result<(), ProjectiveRcbAirError> {
        self.output_projective.verify()?;
        for mul in &self.muls {
            mul.verify()?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbMulRow {
    pub step: ProjectiveRcbMulStep,
    pub trace: FpSolinasMulTrace,
    pub raw_product_chunks: Vec<ProjectiveRcbRawProductChunkRow>,
    pub reduction: FpSolinasReductionTraceClaim,
}

impl ProjectiveRcbMulRow {
    fn new(
        source_index: usize,
        mul_index: usize,
        step: ProjectiveRcbMulStep,
        lhs: &U256,
        rhs: &U256,
    ) -> Result<Self, ProjectiveRcbAirError> {
        let trace = FpSolinasMulTrace::new(lhs, rhs)?;
        let raw_product_chunks =
            ProjectiveRcbRawProductTraceClaim::from_mul_trace(source_index, mul_index, &trace)?
                .rows;
        let reduction = FpSolinasReductionTraceClaim::from_mul_trace(&trace)?;
        Ok(Self {
            step,
            trace,
            raw_product_chunks,
            reduction,
        })
    }

    pub fn verify(&self) -> Result<(), ProjectiveRcbAirError> {
        self.trace.verify()?;
        ProjectiveRcbRawProductTraceClaim {
            rows: self.raw_product_chunks.clone(),
        }
        .verify_against_mul_trace(&self.trace)?;
        self.reduction.verify_against_mul_trace(&self.trace)?;
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbRawProductTraceClaim {
    pub rows: Vec<ProjectiveRcbRawProductChunkRow>,
}

impl ProjectiveRcbRawProductTraceClaim {
    pub fn from_mul_trace(
        source_index: usize,
        mul_index: usize,
        trace: &FpSolinasMulTrace,
    ) -> Result<Self, ProjectiveRcbAirError> {
        let mut rows = Vec::with_capacity(PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS);
        for coeff in 0..FP_SOLINAS_RAW_LIMBS {
            for chunk in 0..coefficient_chunk_count(coeff) {
                rows.push(ProjectiveRcbRawProductChunkRow::from_mul_trace(
                    source_index,
                    mul_index,
                    coeff,
                    chunk,
                    trace,
                )?);
            }
        }
        let claim = Self { rows };
        claim.verify_against_mul_trace(trace)?;
        Ok(claim)
    }

    pub fn verify_against_mul_trace(
        &self,
        trace: &FpSolinasMulTrace,
    ) -> Result<(), ProjectiveRcbAirError> {
        if self.rows.len() != PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS {
            return Err(ProjectiveRcbAirError::RawProductChunkCountMismatch {
                expected: PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS,
                actual: self.rows.len(),
            });
        }
        let mut coeff_sums = [0i128; FP_SOLINAS_RAW_LIMBS];
        for row in &self.rows {
            row.verify()?;
            coeff_sums[row.coeff] += row.product_sum();
            let expected = ProjectiveRcbRawProductChunkRow::from_mul_trace(
                row.source_index,
                row.mul_index,
                row.coeff,
                row.chunk,
                trace,
            )?;
            if row != &expected {
                return Err(ProjectiveRcbAirError::RawProductChunkMismatch {
                    coeff: row.coeff,
                    chunk: row.chunk,
                });
            }
        }
        if coeff_sums == trace.raw_product {
            Ok(())
        } else {
            Err(ProjectiveRcbAirError::RawProductCoefficientMismatch)
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbRawProductChunkRow {
    pub source_index: usize,
    pub mul_index: usize,
    pub coeff: usize,
    pub chunk: usize,
    pub terms: [ProjectiveRcbRawProductTermRow; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS],
    pub digits: [u32; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS],
}

impl ProjectiveRcbRawProductChunkRow {
    fn from_mul_trace(
        source_index: usize,
        mul_index: usize,
        coeff: usize,
        chunk: usize,
        trace: &FpSolinasMulTrace,
    ) -> Result<Self, ProjectiveRcbAirError> {
        let pairs = product_chunk_pairs(coeff, chunk)?;
        let mut terms =
            [ProjectiveRcbRawProductTermRow::inactive(); PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS];
        let mut product_sum = 0i128;
        for (term_index, maybe_pair) in pairs.into_iter().enumerate() {
            if let Some((lhs_index, rhs_index)) = maybe_pair {
                let lhs_limb = trace.lhs.limbs()[lhs_index].0;
                let rhs_limb = trace.rhs.limbs()[rhs_index].0;
                product_sum += i128::from(lhs_limb) * i128::from(rhs_limb);
                terms[term_index] = ProjectiveRcbRawProductTermRow {
                    active: true,
                    lhs_index,
                    rhs_index,
                    lhs_limb,
                    rhs_limb,
                };
            }
        }
        Ok(Self {
            source_index,
            mul_index,
            coeff,
            chunk,
            terms,
            digits: split_raw_product_chunk(product_sum)?,
        })
    }

    pub fn verify(&self) -> Result<(), ProjectiveRcbAirError> {
        if self.coeff >= FP_SOLINAS_RAW_LIMBS {
            return Err(ProjectiveRcbAirError::RawProductCoeffOutOfRange { coeff: self.coeff });
        }
        if self.chunk >= coefficient_chunk_count(self.coeff) {
            return Err(ProjectiveRcbAirError::RawProductChunkOutOfRange {
                coeff: self.coeff,
                chunk: self.chunk,
            });
        }
        let expected_pairs = product_chunk_pairs(self.coeff, self.chunk)?;
        for (term, expected_pair) in self.terms.iter().zip(expected_pairs) {
            match expected_pair {
                Some((lhs_index, rhs_index)) => {
                    if !term.active || term.lhs_index != lhs_index || term.rhs_index != rhs_index {
                        return Err(ProjectiveRcbAirError::RawProductTermMismatch {
                            coeff: self.coeff,
                            chunk: self.chunk,
                        });
                    }
                }
                None => {
                    if *term != ProjectiveRcbRawProductTermRow::inactive() {
                        return Err(ProjectiveRcbAirError::RawProductTermMismatch {
                            coeff: self.coeff,
                            chunk: self.chunk,
                        });
                    }
                }
            }
        }
        let digits = split_raw_product_chunk(self.product_sum())?;
        if self.digits == digits {
            Ok(())
        } else {
            Err(ProjectiveRcbAirError::RawProductChunkDigitMismatch {
                coeff: self.coeff,
                chunk: self.chunk,
            })
        }
    }

    fn product_sum(&self) -> i128 {
        self.terms
            .iter()
            .filter(|term| term.active)
            .map(|term| i128::from(term.lhs_limb) * i128::from(term.rhs_limb))
            .sum()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbRawProductTermRow {
    pub active: bool,
    pub lhs_index: usize,
    pub rhs_index: usize,
    pub lhs_limb: u32,
    pub rhs_limb: u32,
}

impl ProjectiveRcbRawProductTermRow {
    const fn inactive() -> Self {
        Self {
            active: false,
            lhs_index: 0,
            rhs_index: 0,
            lhs_limb: 0,
            rhs_limb: 0,
        }
    }
}

pub const PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP: usize = 13;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProjectiveRcbMulStep {
    DoubleX1Squared,
    DoubleY1Squared,
    DoubleZ1Squared,
    DoubleX1Y1,
    DoubleX1Z1,
    DoubleBT2,
    DoubleX3Y3,
    DoubleX3T3,
    DoubleBZ3,
    DoubleT0Z3,
    DoubleY1Z1,
    DoubleT0Z3Final,
    DoubleT0T1,
    MixedX1X2,
    MixedY1Y2,
    MixedX2Y2X1Y1,
    MixedY2Z1,
    MixedX2Z1,
    MixedBZ1,
    MixedBY3,
    MixedT4Y3,
    MixedT0Y3,
    MixedX3Z3,
    MixedT3X3,
    MixedT4Z3,
    MixedT3T0,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProjectiveRcbAirError {
    Projective(ProjectiveEcError),
    FpSolinas(FpSolinasError),
    FpSolinasReduction(FpSolinasReductionTraceError),
    RowCountMismatch { expected: usize, actual: usize },
    RawProductChunkCountMismatch { expected: usize, actual: usize },
    RawProductCoeffOutOfRange { coeff: usize },
    RawProductChunkOutOfRange { coeff: usize, chunk: usize },
    RawProductTermMismatch { coeff: usize, chunk: usize },
    RawProductChunkDigitMismatch { coeff: usize, chunk: usize },
    RawProductChunkMismatch { coeff: usize, chunk: usize },
    RawProductCoefficientMismatch,
    RawProductChunkOverflow { value: i128 },
    ProjectiveOutputMismatch { source_index: usize },
    TraceRowsMismatch { source_index: usize },
}

impl From<ProjectiveEcError> for ProjectiveRcbAirError {
    fn from(value: ProjectiveEcError) -> Self {
        Self::Projective(value)
    }
}

impl From<FpSolinasError> for ProjectiveRcbAirError {
    fn from(value: FpSolinasError) -> Self {
        Self::FpSolinas(value)
    }
}

impl From<FpSolinasReductionTraceError> for ProjectiveRcbAirError {
    fn from(value: FpSolinasReductionTraceError) -> Self {
        Self::FpSolinasReduction(value)
    }
}

fn add_mul_limb_group<E: EvalAtRow>(
    eval: &mut E,
    relations: ProjectiveRcbMulRelations<'_>,
    gate: E::F,
    source_index: E::F,
    mul_index: E::F,
    role: u32,
    value: &P256EvalBigInt<E>,
) {
    for (limb_index, limb) in value.limbs().iter().enumerate() {
        add_range_check(eval, relations.range13, gate.clone(), limb.clone());
        add_projective_rcb_mul_limb_relation(
            eval,
            relations.mul_limb,
            -E::EF::from(gate.clone()),
            source_index.clone(),
            mul_index.clone(),
            constant(role),
            constant(limb_index as u32),
            limb.clone(),
        );
    }
}

#[allow(clippy::too_many_arguments)]
fn add_projective_rcb_mul_limb_relation<E: EvalAtRow>(
    eval: &mut E,
    relation: &ProjectiveRcbMulLimbRelation,
    numerator: E::EF,
    source_index: E::F,
    mul_index: E::F,
    role: E::F,
    limb_index: E::F,
    limb: E::F,
) {
    eval.add_to_relation(RelationEntry::new(
        relation,
        numerator,
        &[source_index, mul_index, role, limb_index, limb],
    ));
}

fn constrain_unused<E: EvalAtRow>(eval: &mut E, active: E::F, term_active: E::F, value: E::F) {
    eval.add_constraint(active * (one::<E>() - term_active) * value);
}

fn constant<F: From<M31>>(value: u32) -> F {
    F::from(M31::from_u32_unchecked(value))
}

fn zero<E: EvalAtRow>() -> E::F {
    constant(0)
}

fn one<E: EvalAtRow>() -> E::F {
    constant(1)
}

const fn raw_product_chunk_count() -> usize {
    let mut coeff = 0usize;
    let mut count = 0usize;
    while coeff < FP_SOLINAS_RAW_LIMBS {
        count += coefficient_chunk_count_const(coeff);
        coeff += 1;
    }
    count
}

const fn coefficient_chunk_count_const(coeff: usize) -> usize {
    coefficient_term_count_const(coeff).div_ceil(PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS)
}

fn coefficient_chunk_count(coeff: usize) -> usize {
    coefficient_term_count(coeff).div_ceil(PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS)
}

const fn coefficient_term_count_const(coeff: usize) -> usize {
    if coeff < N_LIMBS {
        coeff + 1
    } else {
        FP_SOLINAS_RAW_LIMBS - coeff
    }
}

fn coefficient_term_count(coeff: usize) -> usize {
    if coeff < N_LIMBS {
        coeff + 1
    } else {
        FP_SOLINAS_RAW_LIMBS - coeff
    }
}

fn coefficient_pairs(coeff: usize) -> impl Iterator<Item = (usize, usize)> {
    let start = coeff.saturating_sub(N_LIMBS - 1);
    let end = coeff.min(N_LIMBS - 1);
    (start..=end).map(move |lhs_index| (lhs_index, coeff - lhs_index))
}

fn product_chunk_pairs(
    coeff: usize,
    chunk: usize,
) -> Result<[Option<(usize, usize)>; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS], ProjectiveRcbAirError>
{
    if coeff >= FP_SOLINAS_RAW_LIMBS {
        return Err(ProjectiveRcbAirError::RawProductCoeffOutOfRange { coeff });
    }
    if chunk >= coefficient_chunk_count(coeff) {
        return Err(ProjectiveRcbAirError::RawProductChunkOutOfRange { coeff, chunk });
    }
    let mut pairs = [None; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS];
    let skipped = chunk * PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS;
    for (index, pair) in coefficient_pairs(coeff)
        .skip(skipped)
        .take(PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS)
        .enumerate()
    {
        pairs[index] = Some(pair);
    }
    Ok(pairs)
}

fn split_raw_product_chunk(
    mut value: i128,
) -> Result<[u32; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS], ProjectiveRcbAirError> {
    if !(0..=(2 * (FP_SOLINAS_LIMB_BASE - 1).pow(2))).contains(&value) {
        return Err(ProjectiveRcbAirError::RawProductChunkOverflow { value });
    }
    let mut digits = [0u32; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS];
    for digit in &mut digits {
        *digit = value.rem_euclid(FP_SOLINAS_LIMB_BASE) as u32;
        value = value.div_euclid(FP_SOLINAS_LIMB_BASE);
    }
    if value == 0 {
        Ok(digits)
    } else {
        Err(ProjectiveRcbAirError::RawProductChunkOverflow { value })
    }
}

fn rcb_double_with_mul_rows(
    source_index: usize,
    input: &ProjectivePoint,
    muls: &mut Vec<ProjectiveRcbMulRow>,
) -> Result<ProjectivePoint, ProjectiveRcbAirError> {
    let x1 = input.x.to_u256();
    let y1 = input.y.to_u256();
    let z1 = input.z.to_u256();

    let t0 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleX1Squared,
        &x1,
        &x1,
        muls,
    )?;
    let t1 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleY1Squared,
        &y1,
        &y1,
        muls,
    )?;
    let mut t2 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleZ1Squared,
        &z1,
        &z1,
        muls,
    )?;
    let mut t3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleX1Y1,
        &x1,
        &y1,
        muls,
    )?;
    t3 = fp_add(&t3, &t3);
    let mut z3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleX1Z1,
        &x1,
        &z1,
        muls,
    )?;
    z3 = fp_add(&z3, &z3);
    let mut y3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleBT2,
        &curve_b(),
        &t2,
        muls,
    )?;
    y3 = fp_sub(&y3, &z3);
    let mut x3 = fp_add(&y3, &y3);
    y3 = fp_add(&x3, &y3);
    x3 = fp_sub(&t1, &y3);
    y3 = fp_add(&t1, &y3);
    y3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleX3Y3,
        &x3,
        &y3,
        muls,
    )?;
    x3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleX3T3,
        &x3,
        &t3,
        muls,
    )?;
    t3 = fp_add(&t2, &t2);
    t2 = fp_add(&t2, &t3);
    z3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleBZ3,
        &curve_b(),
        &z3,
        muls,
    )?;
    z3 = fp_sub(&z3, &t2);
    z3 = fp_sub(&z3, &t0);
    t3 = fp_add(&z3, &z3);
    z3 = fp_add(&z3, &t3);
    t3 = fp_add(&t0, &t0);
    let mut t0 = fp_add(&t3, &t0);
    t0 = fp_sub(&t0, &t2);
    t0 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleT0Z3,
        &t0,
        &z3,
        muls,
    )?;
    y3 = fp_add(&y3, &t0);
    t0 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleY1Z1,
        &y1,
        &z1,
        muls,
    )?;
    t0 = fp_add(&t0, &t0);
    z3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleT0Z3Final,
        &t0,
        &z3,
        muls,
    )?;
    x3 = fp_sub(&x3, &z3);
    z3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleT0T1,
        &t0,
        &t1,
        muls,
    )?;
    z3 = fp_add(&z3, &z3);
    z3 = fp_add(&z3, &z3);

    Ok(projective_from_u256(x3, y3, z3))
}

fn rcb_mixed_add_with_mul_rows(
    source_index: usize,
    state: &ProjectivePoint,
    operand: &PreparedAffinePoint,
    muls: &mut Vec<ProjectiveRcbMulRow>,
) -> Result<ProjectivePoint, ProjectiveRcbAirError> {
    let Some(operand) = operand.to_option() else {
        return Ok(state.clone());
    };

    let x1 = state.x.to_u256();
    let y1 = state.y.to_u256();
    let z1 = state.z.to_u256();
    let x2 = operand.x;
    let y2 = operand.y;

    let mut t0 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedX1X2,
        &x1,
        &x2,
        muls,
    )?;
    let mut t1 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedY1Y2,
        &y1,
        &y2,
        muls,
    )?;
    let mut t3 = fp_add(&x2, &y2);
    let mut t4 = fp_add(&x1, &y1);
    t3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedX2Y2X1Y1,
        &t3,
        &t4,
        muls,
    )?;
    t4 = fp_add(&t0, &t1);
    t3 = fp_sub(&t3, &t4);
    t4 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedY2Z1,
        &y2,
        &z1,
        muls,
    )?;
    t4 = fp_add(&t4, &y1);
    let mut y3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedX2Z1,
        &x2,
        &z1,
        muls,
    )?;
    y3 = fp_add(&y3, &x1);
    let mut z3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedBZ1,
        &curve_b(),
        &z1,
        muls,
    )?;
    let mut x3 = fp_sub(&y3, &z3);
    z3 = fp_add(&x3, &x3);
    x3 = fp_add(&x3, &z3);
    z3 = fp_sub(&t1, &x3);
    x3 = fp_add(&t1, &x3);
    y3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedBY3,
        &curve_b(),
        &y3,
        muls,
    )?;
    t1 = fp_add(&z1, &z1);
    let t2 = fp_add(&t1, &z1);
    y3 = fp_sub(&y3, &t2);
    y3 = fp_sub(&y3, &t0);
    t1 = fp_add(&y3, &y3);
    y3 = fp_add(&t1, &y3);
    t1 = fp_add(&t0, &t0);
    t0 = fp_add(&t1, &t0);
    t0 = fp_sub(&t0, &t2);
    t1 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedT4Y3,
        &t4,
        &y3,
        muls,
    )?;
    let t2 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedT0Y3,
        &t0,
        &y3,
        muls,
    )?;
    y3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedX3Z3,
        &x3,
        &z3,
        muls,
    )?;
    y3 = fp_add(&y3, &t2);
    x3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedT3X3,
        &t3,
        &x3,
        muls,
    )?;
    x3 = fp_sub(&x3, &t1);
    z3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedT4Z3,
        &t4,
        &z3,
        muls,
    )?;
    t1 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedT3T0,
        &t3,
        &t0,
        muls,
    )?;
    z3 = fp_add(&z3, &t1);

    Ok(projective_from_u256(x3, y3, z3))
}

fn fp_mul(
    source_index: usize,
    step: ProjectiveRcbMulStep,
    lhs: &U256,
    rhs: &U256,
    muls: &mut Vec<ProjectiveRcbMulRow>,
) -> Result<U256, ProjectiveRcbAirError> {
    let row = ProjectiveRcbMulRow::new(source_index, muls.len(), step, lhs, rhs)?;
    let result = row.trace.result.to_u256();
    muls.push(row);
    Ok(result)
}

fn projective_from_u256(x: U256, y: U256, z: U256) -> ProjectivePoint {
    ProjectivePoint {
        x: crate::limbs::P256M31BigInt::from_u256(&x),
        y: crate::limbs::P256M31BigInt::from_u256(&y),
        z: crate::limbs::P256M31BigInt::from_u256(&z),
    }
}

fn fp_add(lhs: &U256, rhs: &U256) -> U256 {
    add_mod_witness(lhs, rhs, &modulus()).result.to_u256()
}

fn fp_sub(lhs: &U256, rhs: &U256) -> U256 {
    sub_mod_witness(lhs, rhs, &modulus()).result.to_u256()
}

fn modulus() -> U256 {
    U256::from_le_u64s(&P256_MODULUS)
}

fn curve_b() -> U256 {
    U256::from_le_u64s(&P256_B)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY};
    use crate::curve::point_double;
    use crate::types::AffinePoint;
    use num_traits::Zero;
    use stwo::core::air::Component;
    use stwo::core::fields::qm31::SecureField;
    use stwo_constraint_framework::TraceLocationAllocator;

    fn generator() -> PreparedAffinePoint {
        PreparedAffinePoint::from_affine(AffinePoint {
            x: U256::from_le_u64s(&P256_GX),
            y: U256::from_le_u64s(&P256_GY),
        })
    }

    fn one_row_trace(op: ProjectiveEcOp, rhs: PreparedAffinePoint) -> ProjectiveEcTraceClaim {
        let lhs = generator();
        let output = match op {
            ProjectiveEcOp::Double => {
                PreparedAffinePoint::from_affine(point_double(&lhs.to_option().unwrap()).output)
            }
            ProjectiveEcOp::MixedAdd => {
                let output =
                    crate::curve::point_add(&lhs.to_option().unwrap(), &rhs.to_option().unwrap())
                        .output;
                PreparedAffinePoint::from_affine(output)
            }
        };
        ProjectiveEcTraceClaim {
            rows: vec![ProjectiveEcRow::new(
                M31::from_u32_unchecked(0),
                M31::from_u32_unchecked(0),
                op,
                &lhs,
                &rhs,
                &output,
            )],
        }
    }

    #[test]
    fn projective_rcb_air_rows_verify_double() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");

        claim
            .verify_against_projective_trace(&trace)
            .expect("claim verifies");
        assert_eq!(claim.active_row_count(), 1);
        assert_eq!(claim.mul_row_count(), PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP);
        assert_eq!(
            claim.raw_product_chunk_count(),
            PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP * PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS
        );
        assert_eq!(
            claim.reduction_row_count(),
            PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP * FP_SOLINAS_REDUCTION_DIGITS
        );
    }

    #[test]
    fn projective_rcb_air_rows_verify_mixed_add() {
        let g = generator();
        let rhs = PreparedAffinePoint::from_affine(point_double(&g.to_option().unwrap()).output);
        let trace = one_row_trace(ProjectiveEcOp::MixedAdd, rhs);
        let claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");

        claim
            .verify_against_projective_trace(&trace)
            .expect("claim verifies");
        assert_eq!(claim.active_row_count(), 1);
        assert_eq!(claim.mul_row_count(), PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP);
    }

    #[test]
    fn projective_rcb_air_rows_skip_operand_infinity_mixed_add() {
        let lhs = generator();
        let output = lhs.clone();
        let trace = ProjectiveEcTraceClaim {
            rows: vec![ProjectiveEcRow::new(
                M31::from_u32_unchecked(0),
                M31::from_u32_unchecked(0),
                ProjectiveEcOp::MixedAdd,
                &lhs,
                &PreparedAffinePoint::infinity(),
                &output,
            )],
        };
        let claim = ProjectiveRcbAirTraceClaim::from_projective_trace(&trace)
            .expect("valid infinity-add RCB AIR trace");

        claim
            .verify_against_projective_trace(&trace)
            .expect("claim verifies");
        assert_eq!(claim.mul_row_count(), 0);
    }

    #[test]
    fn projective_rcb_air_rows_detect_mutated_reduction_digit() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let mut claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        claim.rows[0].muls[0].reduction.rows[0].folded_digit ^= 1;

        let err = claim
            .verify_against_projective_trace(&trace)
            .expect_err("mutated reduction row must fail");

        assert!(matches!(
            err,
            ProjectiveRcbAirError::FpSolinasReduction(
                FpSolinasReductionTraceError::TraceRowsMismatch
                    | FpSolinasReductionTraceError::ReductionEquationMismatch { .. }
            )
        ));
    }

    #[test]
    fn projective_rcb_air_rows_detect_mutated_raw_product_digit() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let mut claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        claim.rows[0].muls[0].raw_product_chunks[0].digits[0] ^= 1;

        let err = claim
            .verify_against_projective_trace(&trace)
            .expect_err("mutated raw product chunk must fail");

        assert!(matches!(
            err,
            ProjectiveRcbAirError::RawProductChunkDigitMismatch { .. }
                | ProjectiveRcbAirError::RawProductChunkMismatch { .. }
        ));
    }

    #[test]
    fn projective_rcb_air_rows_detect_mutated_projective_output() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let mut claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        claim.rows[0].output_projective.x = crate::limbs::P256M31BigInt::zero();

        let err = claim
            .verify_against_projective_trace(&trace)
            .expect_err("mutated output must fail");

        assert!(matches!(
            err,
            ProjectiveRcbAirError::TraceRowsMismatch { .. }
                | ProjectiveRcbAirError::Projective(ProjectiveEcError::InvalidProjectiveInfinity)
        ));
    }

    #[test]
    fn projective_rcb_mul_eval_allocates_expected_width() {
        let mut allocator = TraceLocationAllocator::default();
        let component = ProjectiveRcbMulComponent::new(
            &mut allocator,
            ProjectiveRcbMulEval {
                log_size: 6,
                relations: ProjectiveRcbMulComponentRelations::dummy(),
            },
            SecureField::zero(),
        );

        assert_eq!(
            PROJECTIVE_RCB_MUL_TRACE_COLUMNS,
            1 + 2 + 3 * N_LIMBS + 1 + 5 * FP_SOLINAS_REDUCTION_DIGITS
        );
        assert_eq!(
            component.trace_log_degree_bounds()[1].len(),
            PROJECTIVE_RCB_MUL_TRACE_COLUMNS
        );
        assert_eq!(PROJECTIVE_RCB_MUL_LIMB_RELATION_ARITY, 5);
        assert_eq!(
            ProjectiveRcbMulEval {
                log_size: 6,
                relations: ProjectiveRcbMulComponentRelations::dummy(),
            }
            .max_constraint_log_degree_bound(),
            8
        );
    }

    #[test]
    fn projective_rcb_raw_product_chunk_eval_allocates_expected_width() {
        let mut allocator = TraceLocationAllocator::default();
        let component = ProjectiveRcbRawProductChunkComponent::new(
            &mut allocator,
            ProjectiveRcbRawProductChunkEval {
                log_size: 8,
                relations: ProjectiveRcbMulComponentRelations::dummy(),
            },
            SecureField::zero(),
        );

        assert_eq!(PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS, 210);
        assert_eq!(
            PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS,
            1 + 2 + 2 + 2 * 5 + 3
        );
        assert_eq!(
            component.trace_log_degree_bounds()[1].len(),
            PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS
        );
        assert_eq!(PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGIT_RELATION_ARITY, 6);
        assert!(projective_rcb_raw_product_chunk_fits_m31());
    }
}
