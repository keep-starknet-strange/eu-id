//! Native witness construction, claim types, and base/preprocessed/value
//! trace generation for the prepared-table family.
//!
//! Split out of `mod.rs` (pure relocation, no behavioral change).

use serde::{Deserialize, Serialize};
use stwo::core::{air::Component, channel::Channel, fields::m31::M31, pcs::TreeVec, ColumnVec};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::TraceLocationAllocator;
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};

use crate::constants::P256_MODULUS;
use crate::curve::{point_add, point_double, scalar_mul};
use crate::field_ops::{add_mod_witness, sub_mod_witness};
use crate::limbs::P256M31BigInt;
use crate::prepared_point::{
    PreparedPointInstance, PreparedPointTraceClaim, PreparedPointUseCountClaim,
    PREPARED_BASE_COUNT, TABLE16_INDEX,
};
use crate::projective::ProjectiveEcTraceClaim;
use crate::projective_air::projective_rcb_op_mul_limbs;
use crate::types::{AffinePoint, U256};

use crate::scalar::cert_bind::{CertScalarInputClaim, CertScalarInputRow, CERT_ID_U1_GENERATOR};
use crate::scalar::fake_glv_scalar::{FakeGlvScalarHintClaim, FakeGlvScalarHintRow};
use crate::scalar::fake_glv_selector::{FakeGlvSelectorClaim, FakeGlvSelectorRow};
use crate::scalar::fake_glv_selector_lookup::Selector16DecodeEntry;
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};

use super::super::ec_source::{double_formula, mixed_add_formula};
use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedTableClaim {
    pub certs: Vec<PreparedTableCert>,
}

impl PreparedTableClaim {
    pub fn from_claims(
        cert_inputs: &CertScalarInputClaim,
        fake_glv_scalars: &FakeGlvScalarHintClaim,
        selectors: &FakeGlvSelectorClaim,
    ) -> Result<Self, PreparedTableError> {
        if cert_inputs.rows.len() != fake_glv_scalars.rows.len()
            || cert_inputs.rows.len() != selectors.rows.len()
        {
            return Err(PreparedTableError::RowCountMismatch {
                certs: cert_inputs.rows.len(),
                fake_glv: fake_glv_scalars.rows.len(),
                selectors: selectors.rows.len(),
            });
        }

        let certs = cert_inputs
            .rows
            .iter()
            .zip(&fake_glv_scalars.rows)
            .zip(&selectors.rows)
            .map(|((cert, fake_glv), selector)| PreparedTableCert::new(cert, fake_glv, selector))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self { certs })
    }

    pub fn verify(&self) -> Result<(), PreparedTableError> {
        for cert in &self.certs {
            cert.verify()?;
        }
        Ok(())
    }

    pub fn prepared_point_trace(
        &self,
        use_counts: &PreparedPointUseCountClaim,
    ) -> Result<PreparedPointTraceClaim, PreparedTableError> {
        if self.certs.len() != use_counts.certs.len() {
            return Err(PreparedTableError::UseCountCountMismatch {
                tables: self.certs.len(),
                use_counts: use_counts.certs.len(),
            });
        }

        Ok(PreparedPointTraceClaim::from_use_counts(
            use_counts,
            |sig_id, cert_id, table_index| {
                self.instance(sig_id, cert_id, table_index)
                    .unwrap_or_else(|| PreparedPointInstance::dummy(sig_id, cert_id, table_index))
            },
        ))
    }

    pub fn verify_prepared_point_trace(
        &self,
        use_counts: &PreparedPointUseCountClaim,
        trace: &PreparedPointTraceClaim,
    ) -> Result<(), PreparedTableError> {
        let expected = self.prepared_point_trace(use_counts)?;
        if &expected == trace {
            Ok(())
        } else {
            Err(PreparedTableError::PreparedPointTraceMismatch)
        }
    }

    pub fn instance(
        &self,
        sig_id: M31,
        cert_id: M31,
        table_index: u32,
    ) -> Option<PreparedPointInstance<M31>> {
        self.certs
            .iter()
            .find(|cert| cert.sig_id == sig_id && cert.cert_id == cert_id)
            .and_then(|cert| cert.instance(table_index))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedTableEcTraceClaim {
    pub rows: Vec<PreparedTableEcRow>,
}

impl PreparedTableEcTraceClaim {
    pub fn from_claims(
        cert_inputs: &CertScalarInputClaim,
        fake_glv_scalars: &FakeGlvScalarHintClaim,
        selectors: &FakeGlvSelectorClaim,
        table: &PreparedTableClaim,
    ) -> Result<Self, PreparedTableError> {
        if cert_inputs.rows.len() != fake_glv_scalars.rows.len()
            || cert_inputs.rows.len() != selectors.rows.len()
            || cert_inputs.rows.len() != table.certs.len()
        {
            return Err(PreparedTableError::EcTraceCountMismatch {
                certs: cert_inputs.rows.len(),
                fake_glv: fake_glv_scalars.rows.len(),
                selectors: selectors.rows.len(),
                tables: table.certs.len(),
            });
        }

        let mut rows = Vec::new();
        for (((cert, fake_glv), selector), table_cert) in cert_inputs
            .rows
            .iter()
            .zip(&fake_glv_scalars.rows)
            .zip(&selectors.rows)
            .zip(&table.certs)
        {
            rows.extend(prepared_table_ec_rows_for_cert(
                cert, fake_glv, selector, table_cert,
            )?);
        }
        let claim = Self { rows };
        claim.verify()?;
        Ok(claim)
    }

    pub fn verify(&self) -> Result<(), PreparedTableError> {
        for row in &self.rows {
            row.verify()?;
        }
        Ok(())
    }

    pub fn active_row_count(&self) -> usize {
        self.rows.len()
    }

    pub fn verify_against_table(
        &self,
        table: &PreparedTableClaim,
    ) -> Result<(), PreparedTableError> {
        for cert in &table.certs {
            let cert_rows = self
                .rows
                .iter()
                .filter(|row| row.sig_id == cert.sig_id && row.cert_id == cert.cert_id)
                .collect::<Vec<_>>();
            if cert.cert_active.0 == 0 {
                if cert_rows.is_empty() {
                    continue;
                }
                return Err(PreparedTableError::InactiveEcTraceRows {
                    sig_id: cert.sig_id.0,
                    cert_id: cert.cert_id.0,
                });
            }

            let expected_rows = if cert.cert_id.0 == CERT_ID_U1_GENERATOR {
                PREPARED_BASE_COUNT + 3
            } else {
                PREPARED_BASE_COUNT + 5
            };
            if cert_rows.len() != expected_rows {
                return Err(PreparedTableError::EcTraceCertRowCountMismatch {
                    sig_id: cert.sig_id.0,
                    cert_id: cert.cert_id.0,
                    expected: expected_rows,
                    actual: cert_rows.len(),
                });
            }

            require_unique_output(
                &cert_rows,
                cert.sig_id,
                cert.cert_id,
                PreparedTableEcRowKind::AddR2R,
                "R3",
                &cert.r3,
            )?;
            for (index, point) in cert.base.iter().enumerate() {
                require_unique_output(
                    &cert_rows,
                    cert.sig_id,
                    cert.cert_id,
                    PreparedTableEcRowKind::Base(index as u32),
                    "Base",
                    point,
                )?;
            }
            require_unique_output(
                &cert_rows,
                cert.sig_id,
                cert.cert_id,
                PreparedTableEcRowKind::Table16,
                "Table16",
                &cert.table16,
            )?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PreparedTableEcRowProofClaim {
    pub log_size: u32,
}

impl PreparedTableEcRowProofClaim {
    pub fn from_trace(trace: &PreparedTableEcTraceClaim) -> Self {
        Self {
            log_size: padded_log_size(trace.rows.len()),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    pub fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut allocator = TraceLocationAllocator::default();
        let _ = PreparedTableEcRowComponent::new(
            &mut allocator,
            PreparedTableEcRowEval {
                log_size: self.log_size,
                relation: PreparedTableEcRowRelation::dummy(),
                pinning: None,
            },
            secure_zero(),
        );
        allocator.preprocessed_columns().clone()
    }

    pub fn trace_log_degree_bounds(&self, ids: &[PreProcessedColumnId]) -> TreeVec<ColumnVec<u32>> {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let component = PreparedTableEcRowComponent::new(
            &mut allocator,
            PreparedTableEcRowEval {
                log_size: self.log_size,
                relation: PreparedTableEcRowRelation::dummy(),
                pinning: None,
            },
            secure_zero(),
        );
        component.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self, ids: &[PreProcessedColumnId]) -> u32 {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let component = PreparedTableEcRowComponent::new(
            &mut allocator,
            PreparedTableEcRowEval {
                log_size: self.log_size,
                relation: PreparedTableEcRowRelation::dummy(),
                pinning: None,
            },
            secure_zero(),
        );
        component.max_constraint_log_degree_bound()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PreparedTableProjectiveSourceProofClaim {
    pub log_size: u32,
    /// Active prepared-table rows (= γ-digest groups / tall schedule).
    pub rows: u32,
}

impl PreparedTableProjectiveSourceProofClaim {
    pub fn from_prepared_trace(trace: &PreparedTableEcTraceClaim) -> Self {
        Self {
            log_size: padded_log_size(trace.rows.len()),
            rows: trace.rows.len() as u32,
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
        channel.mix_u64(self.rows as u64);
    }

    pub fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut allocator = TraceLocationAllocator::default();
        let _ = PreparedTableProjectiveSourceComponents::new(
            &mut allocator,
            self.log_size,
            self.rows,
            &PreparedTableProjectiveSourceInteractionClaim::zero(),
            &PreparedTableEcRowRelation::dummy(),
            &crate::projective_air::ProjectiveRcbMulComponentRelations::dummy(),
            &crate::range_checks::RangeCheckRelation::dummy(),
            &crate::range_checks::RangeCheckRelation::dummy(),
            &crate::components::gamma_digest::GammaDigestRelation::dummy(),
            &prepared_dummy_gamma_challenge(),
        );
        allocator.preprocessed_columns().clone()
    }

    pub fn trace_log_degree_bounds(&self, ids: &[PreProcessedColumnId]) -> TreeVec<ColumnVec<u32>> {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = PreparedTableProjectiveSourceComponents::new(
            &mut allocator,
            self.log_size,
            self.rows,
            &PreparedTableProjectiveSourceInteractionClaim::zero(),
            &PreparedTableEcRowRelation::dummy(),
            &crate::projective_air::ProjectiveRcbMulComponentRelations::dummy(),
            &crate::range_checks::RangeCheckRelation::dummy(),
            &crate::range_checks::RangeCheckRelation::dummy(),
            &crate::components::gamma_digest::GammaDigestRelation::dummy(),
            &prepared_dummy_gamma_challenge(),
        );
        components.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self, ids: &[PreProcessedColumnId]) -> u32 {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = PreparedTableProjectiveSourceComponents::new(
            &mut allocator,
            self.log_size,
            self.rows,
            &PreparedTableProjectiveSourceInteractionClaim::zero(),
            &PreparedTableEcRowRelation::dummy(),
            &crate::projective_air::ProjectiveRcbMulComponentRelations::dummy(),
            &crate::range_checks::RangeCheckRelation::dummy(),
            &crate::range_checks::RangeCheckRelation::dummy(),
            &crate::components::gamma_digest::GammaDigestRelation::dummy(),
            &prepared_dummy_gamma_challenge(),
        );
        components.max_constraint_log_degree_bound()
    }
}

/// Dummy γ challenge for preprocessed-id / degree-bound queries.
pub(crate) fn prepared_dummy_gamma_challenge() -> crate::components::gamma_digest::GammaChallenge {
    crate::components::gamma_digest::GammaChallenge::from_gamma(
        stwo::core::fields::qm31::SecureField::from(M31::from_u32_unchecked(2)),
        crate::components::gamma_digest::gamma_padded_values(
            super::interaction::prepared_gamma_range13_columns().len(),
        )
        .max(crate::components::gamma_digest::gamma_padded_values(
            super::interaction::prepared_gamma_signed_carry_columns().len(),
        )),
    )
}

pub(crate) fn gen_prepared_table_ec_row_preprocessed_trace(
    log_size: u32,
    rows: u32,
    ids: &[PreProcessedColumnId],
) -> Result<ColumnVec<M31ColumnEval>, PreparedTableError> {
    let gamma_layouts = super::interaction::prepared_gamma_layouts(rows as usize);
    // C5-2 preprocessed columns the self-contained Range13 / signed-carry
    // providers declare (shared by id with the silo's, deduplicated globally).
    let range13_value_id =
        crate::range_checks::range_check_value_column_id(crate::range_checks::RANGE13_BITS);
    let signed_carry_value_id = crate::range_checks::signed_carry_value_column_id(
        crate::projective_air::PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
    );
    let signed_carry_active_id = crate::range_checks::signed_carry_active_column_id(
        crate::projective_air::PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
    );
    let signed_carry_claim = crate::projective_air::projective_rcb_signed_carry_claim();
    ids.iter()
        .map(|id| {
            if id == &prepared_table_ec_row_index_column_id() {
                Ok(m31_column_eval(
                    log_size,
                    (0..(1usize << log_size))
                        .map(|index| M31::from_u32_unchecked(index as u32))
                        .collect(),
                ))
            } else if id == &range13_value_id {
                Ok(
                    crate::range_checks::RangeCheckClaim::new(crate::range_checks::RANGE13_BITS)
                        .gen_preprocessed_column(),
                )
            } else if id == &signed_carry_value_id {
                Ok(signed_carry_claim.gen_value_column())
            } else if id == &signed_carry_active_id {
                Ok(signed_carry_claim.gen_active_column())
            } else if let Some(column) = gamma_layouts.iter().find_map(|layout| {
                crate::components::gamma_digest::gamma_tall_preprocessed_column(layout, id)
            }) {
                Ok(column)
            } else {
                Err(PreparedTableError::PreprocessedColumnMissing)
            }
        })
        .collect()
}

pub(crate) fn gen_prepared_table_ec_row_base_trace(
    trace: &PreparedTableEcTraceClaim,
    log_size: u32,
) -> Result<ColumnVec<M31ColumnEval>, PreparedTableError> {
    let padded_rows = 1usize << log_size;
    if trace.rows.len() > padded_rows {
        return Err(PreparedTableError::EcTraceRowsExceedDomain {
            rows: trace.rows.len(),
            domain: padded_rows,
        });
    }
    let mut rows = trace
        .rows
        .iter()
        .enumerate()
        .map(|(source_index, row)| prepared_table_ec_row_trace_values(source_index, row))
        .collect::<Vec<_>>();
    rows.resize(
        padded_rows,
        [M31::from_u32_unchecked(0); PREPARED_TABLE_EC_ROW_TRACE_COLUMNS],
    );
    Ok(columns_from_rows(log_size, rows))
}

pub(crate) fn gen_prepared_table_projective_source_base_trace(
    prepared: &PreparedTableEcTraceClaim,
    projective: &ProjectiveEcTraceClaim,
    log_size: u32,
) -> Result<ColumnVec<M31ColumnEval>, PreparedTableError> {
    let padded_rows = 1usize << log_size;
    if prepared.rows.len() > padded_rows {
        return Err(PreparedTableError::EcTraceRowsExceedDomain {
            rows: prepared.rows.len(),
            domain: padded_rows,
        });
    }
    if projective.rows.len() < prepared.rows.len() {
        return Err(PreparedTableError::ProjectiveSourcePrefixTooShort {
            prepared: prepared.rows.len(),
            projective: projective.rows.len(),
        });
    }
    let mut rows = prepared
        .rows
        .iter()
        .zip(projective.rows.iter())
        .enumerate()
        .map(|(source_index, (prepared_row, projective_row))| {
            prepared_table_projective_source_trace_values(
                source_index,
                prepared_row,
                projective_row,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    rows.resize(
        padded_rows,
        [M31::from_u32_unchecked(0); PREPARED_TABLE_PROJECTIVE_SOURCE_TRACE_COLUMNS],
    );
    Ok(columns_from_rows(log_size, rows))
}

fn prepared_table_ec_row_trace_values(
    source_index: usize,
    row: &PreparedTableEcRow,
) -> [M31; PREPARED_TABLE_EC_ROW_TRACE_COLUMNS] {
    let mut values = [M31::from_u32_unchecked(0); PREPARED_TABLE_EC_ROW_TRACE_COLUMNS];
    let mut column = 0;
    values[column] = M31::from_u32_unchecked(1);
    column += 1;
    values[column] = M31::from_u32_unchecked(source_index as u32);
    column += 1;
    values[column] = row.sig_id;
    column += 1;
    values[column] = row.cert_id;
    column += 1;
    for flag in kind_flags(row.kind) {
        values[column] = flag;
        column += 1;
    }
    values[column] = prepared_table_ec_op_code(row.kind);
    column += 1;
    values[column] = prepared_table_ec_table_index(row.kind);
    column += 1;
    for value in prepared_table_ec_point_values(&row.lhs) {
        values[column] = value;
        column += 1;
    }
    for value in prepared_table_ec_point_values(&row.rhs) {
        values[column] = value;
        column += 1;
    }
    for value in prepared_table_ec_point_values(&row.output) {
        values[column] = value;
        column += 1;
    }
    // Negation aux block: `neg = -src` plus `neg.y + src.y = p` carries.
    //   DoubleR: src = lhs (= R)   -> neg = -R
    //   AddR2R:  src = output (= R3) -> neg = -R3
    //   otherwise: neg = 0, carries = 0 (padding-gated in the AIR).
    let neg_source = match row.kind {
        PreparedTableEcRowKind::DoubleR => Some(&row.lhs),
        PreparedTableEcRowKind::AddR2R => Some(&row.output),
        _ => None,
    };
    let (neg_point, neg_carries) = match neg_source {
        Some(src) => prepared_table_ec_negation_witness(src),
        None => (
            PreparedAffinePoint::from_zero_limbs(),
            [M31::from_u32_unchecked(0); PREPARED_TABLE_EC_NEG_CARRY_COLUMNS],
        ),
    };
    for value in prepared_table_ec_point_values(&neg_point) {
        values[column] = value;
        column += 1;
    }
    for carry in neg_carries {
        values[column] = carry;
        column += 1;
    }
    debug_assert_eq!(column, PREPARED_TABLE_EC_ROW_TRACE_COLUMNS);
    values
}

/// Witness the negation `neg = -src` (canonical limbs) together with the boolean
/// carries of the limb addition `neg.y + src.y = p`. Because `neg.y, src.y < p`
/// and (for a finite `src`) `neg.y + src.y = p` exactly, every carry is in
/// `{0, 1}` and the top carry vanishes.
fn prepared_table_ec_negation_witness(
    src: &PreparedAffinePoint,
) -> (
    PreparedAffinePoint,
    [M31; PREPARED_TABLE_EC_NEG_CARRY_COLUMNS],
) {
    let neg = prepared(negate_optional(src.to_option()));
    let p_limbs = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS));
    let mut carries = [M31::from_u32_unchecked(0); PREPARED_TABLE_EC_NEG_CARRY_COLUMNS];
    let mut carry: u32 = 0;
    let limb_modulus = 1u32 << LIMB_BITS;
    for (i, carry_slot) in carries.iter_mut().enumerate().take(N_LIMBS) {
        let sum = neg.y.limbs()[i].0 + src.y.limbs()[i].0 + carry;
        carry = sum / limb_modulus;
        debug_assert!(carry <= 1, "negation carry must be boolean");
        debug_assert_eq!(
            sum % limb_modulus,
            p_limbs.limbs()[i].0,
            "negation limb addition must reconstruct the modulus"
        );
        *carry_slot = M31::from_u32_unchecked(carry);
    }
    debug_assert_eq!(carry, 0, "negation top carry must vanish");
    (neg, carries)
}

fn prepared_table_projective_source_trace_values(
    source_index: usize,
    prepared_row: &PreparedTableEcRow,
    projective_row: &crate::projective::ProjectiveEcRow,
) -> Result<[M31; PREPARED_TABLE_PROJECTIVE_SOURCE_TRACE_COLUMNS], PreparedTableError> {
    let mut values = [M31::from_u32_unchecked(0); PREPARED_TABLE_PROJECTIVE_SOURCE_TRACE_COLUMNS];
    let mut column = 0;
    values[column] = M31::from_u32_unchecked(1);
    column += 1;
    values[column] = M31::from_u32_unchecked(source_index as u32);
    column += 1;
    values[column] = projective_row.sig_id;
    column += 1;
    values[column] = projective_row.cert_id;
    column += 1;
    values[column] = projective_ec_op_code(projective_row.op);
    column += 1;
    values[column] = prepared_table_ec_table_index(prepared_row.kind);
    column += 1;
    for value in prepared_table_ec_point_values(&projective_row.lhs_affine) {
        values[column] = value;
        column += 1;
    }
    for value in prepared_table_ec_point_values(&projective_row.rhs_affine) {
        values[column] = value;
        column += 1;
    }
    for value in prepared_table_ec_point_values(&projective_row.output_affine) {
        values[column] = value;
        column += 1;
    }
    debug_assert_eq!(column, PREPARED_TABLE_PROJECTIVE_SOURCE_HAS_MULS_COL);
    // C5 plumbing: the `has_muls` flag, then the silo's proven mul limbs for this
    // prepared-table op in canonical order. (Prepared-table ops use finite base
    // operands, so `has_muls` is 1, but the flag keeps the consumer robust.)
    let (mul_limbs, has_muls) = projective_rcb_op_mul_limbs(source_index, projective_row)
        .map_err(|_| PreparedTableError::ProjectiveSourceInvalid)?;
    values[column] = M31::from_u32_unchecked(has_muls as u32);
    column += 1;
    // Operand dedup: only the KEPT slots are committed.
    for value in crate::projective_air::projective_rcb_kept_mul_limbs(&mul_limbs) {
        values[column] = value;
        column += 1;
    }
    debug_assert_eq!(column, PREPARED_TABLE_PROJECTIVE_SOURCE_FORMULA_OFFSET);
    // The SHARED formula block: the Double witness (a strict prefix of the
    // block) on Double rows, the MixedAdd witness on finite-operand MixedAdd
    // rows; the two witnessed gate columns at the block's tail are
    // constrained on EVERY row, so the no-witness branch still writes them
    // ((0, 0) on Double rows is the zero default).
    let is_mixed = projective_row.op == crate::projective::ProjectiveEcOp::MixedAdd;
    if projective_row.op == crate::projective::ProjectiveEcOp::Double {
        let witness = double_formula::solve_double_formula_witness(
            &mul_limbs,
            &projective_row.output_projective,
        )
        .ok_or(PreparedTableError::ProjectiveSourceInvalid)?;
        for (offset, value) in double_formula::double_formula_trace_values(&witness)
            .into_iter()
            .enumerate()
        {
            values[column + offset] = value;
        }
        column += mixed_add_formula::MIXED_ADD_FORMULA_COLUMNS;
    } else if is_mixed && has_muls {
        let witness = mixed_add_formula::solve_mixed_add_formula_witness(
            &mul_limbs,
            &projective_row.output_projective,
        )
        .ok_or(PreparedTableError::ProjectiveSourceInvalid)?;
        for value in mixed_add_formula::mixed_add_formula_trace_values(&witness) {
            values[column] = value;
            column += 1;
        }
    } else {
        let gate_base = column + mixed_add_formula::MIXED_ADD_GATE_OFFSET_IN_BLOCK;
        let gates = mixed_add_formula::mixed_add_gate_trace_values(is_mixed, false);
        values[gate_base] = gates[0];
        values[gate_base + 1] = gates[1];
        column += mixed_add_formula::MIXED_ADD_FORMULA_COLUMNS;
    }
    debug_assert_eq!(column, PREPARED_TABLE_PROJECTIVE_SOURCE_TRACE_COLUMNS);
    Ok(values)
}

#[derive(Clone, Debug)]
struct PreparedTableEcPointValues {
    x: [M31; N_LIMBS],
    y: [M31; N_LIMBS],
    inf: M31,
}

impl PreparedTableEcPointValues {
    fn from_prepared(point: &PreparedAffinePoint) -> Self {
        Self {
            x: *point.x.limbs(),
            y: *point.y.limbs(),
            inf: point.inf,
        }
    }
}

impl PreparedTableEcPointLike<M31> for PreparedTableEcPointValues {
    fn relation_values(&self) -> [M31; PREPARED_TABLE_EC_POINT_COLUMNS] {
        core::array::from_fn(|index| match index {
            0..=19 => self.x[index],
            20..=39 => self.y[index - N_LIMBS],
            40 => self.inf,
            _ => unreachable!("prepared-table EC point relation index is in range"),
        })
    }
}

pub(crate) fn prepared_table_ec_point_values(
    point: &PreparedAffinePoint,
) -> [M31; PREPARED_TABLE_EC_POINT_COLUMNS] {
    PreparedTableEcPointValues::from_prepared(point).relation_values()
}

fn columns_from_rows<const N: usize>(
    log_size: u32,
    rows: Vec<[M31; N]>,
) -> ColumnVec<M31ColumnEval> {
    (0..N)
        .map(|column| m31_column_eval(log_size, rows.iter().map(|row| row[column]).collect()))
        .collect()
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedTableEcRow {
    pub sig_id: M31,
    pub cert_id: M31,
    pub kind: PreparedTableEcRowKind,
    pub lhs: PreparedAffinePoint,
    pub rhs: PreparedAffinePoint,
    pub output: PreparedAffinePoint,
}

impl PreparedTableEcRow {
    fn double(
        sig_id: M31,
        cert_id: M31,
        kind: PreparedTableEcRowKind,
        input: PreparedAffinePoint,
        output: PreparedAffinePoint,
    ) -> Self {
        Self {
            sig_id,
            cert_id,
            kind,
            lhs: input,
            rhs: PreparedAffinePoint::infinity(),
            output,
        }
    }

    fn add(
        sig_id: M31,
        cert_id: M31,
        kind: PreparedTableEcRowKind,
        lhs: PreparedAffinePoint,
        rhs: PreparedAffinePoint,
        output: PreparedAffinePoint,
    ) -> Self {
        Self {
            sig_id,
            cert_id,
            kind,
            lhs,
            rhs,
            output,
        }
    }

    pub fn verify(&self) -> Result<(), PreparedTableError> {
        self.lhs.verify()?;
        self.rhs.verify()?;
        self.output.verify()?;
        let expected = match self.kind {
            PreparedTableEcRowKind::DoubleP | PreparedTableEcRowKind::DoubleR => {
                double_optional(self.lhs.to_option())
            }
            PreparedTableEcRowKind::AddP2P
            | PreparedTableEcRowKind::AddR2R
            | PreparedTableEcRowKind::Base(_)
            | PreparedTableEcRowKind::Table16 => {
                add_optional_points(self.lhs.to_option(), self.rhs.to_option())
            }
        };
        let expected = prepared(expected);
        if self.output == expected {
            Ok(())
        } else {
            Err(PreparedTableError::EcTraceOutputMismatch {
                sig_id: self.sig_id.0,
                cert_id: self.cert_id.0,
                kind: self.kind,
            })
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreparedTableEcRowKind {
    DoubleP,
    AddP2P,
    DoubleR,
    AddR2R,
    Base(u32),
    Table16,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedTableCert {
    pub sig_id: M31,
    pub cert_id: M31,
    pub cert_active: M31,
    pub base: [PreparedAffinePoint; PREPARED_BASE_COUNT],
    pub r3: PreparedAffinePoint,
    pub table16: PreparedAffinePoint,
}

impl PreparedTableCert {
    fn new(
        cert: &CertScalarInputRow,
        fake_glv: &FakeGlvScalarHintRow,
        selector: &FakeGlvSelectorRow,
    ) -> Result<Self, PreparedTableError> {
        require_same_id("fake_glv", cert, fake_glv.sig_id, fake_glv.cert_id)?;
        require_same_id("selector", cert, selector.sig_id, selector.cert_id)?;

        if cert.cert_active.0 == 0 {
            return Ok(Self {
                sig_id: cert.sig_id,
                cert_id: cert.cert_id,
                cert_active: cert.cert_active,
                base: core::array::from_fn(|_| PreparedAffinePoint::infinity()),
                r3: PreparedAffinePoint::infinity(),
                table16: PreparedAffinePoint::infinity(),
            });
        }

        let p = AffinePoint {
            x: cert.base_x.to_u256(),
            y: cert.base_y.to_u256(),
        };
        let h =
            scalar_mul(&cert.scalar.to_u256(), &p).ok_or(PreparedTableError::MissingHintPoint {
                sig_id: cert.sig_id.0,
                cert_id: cert.cert_id.0,
            })?;
        let r = signed_hint_point(&h, fake_glv.hint.s2_sign_bit)?;
        let p3 = scalar_mul(&U256::from_le_u64s(&[3, 0, 0, 0]), &p).ok_or(
            PreparedTableError::MissingTriplePoint {
                point: "P",
                sig_id: cert.sig_id.0,
                cert_id: cert.cert_id.0,
            },
        )?;
        let r3 = scalar_mul(&U256::from_le_u64s(&[3, 0, 0, 0]), &r).ok_or(
            PreparedTableError::MissingTriplePoint {
                point: "R",
                sig_id: cert.sig_id.0,
                cert_id: cert.cert_id.0,
            },
        )?;

        let base = [
            prepared(add_optional_points(
                Some(p3.clone()),
                negate_optional(Some(r.clone())),
            )),
            prepared(add_optional_points(
                Some(p.clone()),
                negate_optional(Some(r.clone())),
            )),
            prepared(add_optional_points(Some(p.clone()), Some(r.clone()))),
            prepared(add_optional_points(Some(p3.clone()), Some(r.clone()))),
            prepared(add_optional_points(
                Some(p3.clone()),
                negate_optional(Some(r3.clone())),
            )),
            prepared(add_optional_points(
                Some(p.clone()),
                negate_optional(Some(r3.clone())),
            )),
            prepared(add_optional_points(Some(p.clone()), Some(r3.clone()))),
            prepared(add_optional_points(Some(p3.clone()), Some(r3.clone()))),
        ];

        let selector0 =
            Selector16DecodeEntry::from_selector(selector.selectors[0]).map_err(|_| {
                PreparedTableError::InvalidSelector {
                    selector: selector.selectors[0].0,
                }
            })?;
        let selected = apply_selector(&base, selector0)?;
        let table16 = prepared(add_optional_points(selected.to_option(), Some(r3.clone())));

        Ok(Self {
            sig_id: cert.sig_id,
            cert_id: cert.cert_id,
            cert_active: cert.cert_active,
            base,
            r3: prepared(Some(r3)),
            table16,
        })
    }

    /// Test-only variant of [`Self::new`] that substitutes an injected hint
    /// point `R'` for the production `R = signed_hint(scalar_mul(u, base))`.
    /// Every R-derived cell (`R3 = 3R'`, `base[]`, `table16`) is recomputed
    /// from `R'` so the resulting cert is internally consistent for an
    /// arbitrary (possibly wrong) `R'`. Used to probe whether the in-AIR
    /// scalar multiplication binds `R` to `u·base`.
    #[cfg(test)]
    pub(crate) fn new_with_r_override(
        cert: &CertScalarInputRow,
        _fake_glv: &FakeGlvScalarHintRow,
        selector: &FakeGlvSelectorRow,
        r_override: AffinePoint,
    ) -> Result<Self, PreparedTableError> {
        assert_eq!(cert.cert_active.0, 1, "override path requires active cert");
        let p = AffinePoint {
            x: cert.base_x.to_u256(),
            y: cert.base_y.to_u256(),
        };
        let r = r_override;
        let p3 = scalar_mul(&U256::from_le_u64s(&[3, 0, 0, 0]), &p).ok_or(
            PreparedTableError::MissingTriplePoint {
                point: "P",
                sig_id: cert.sig_id.0,
                cert_id: cert.cert_id.0,
            },
        )?;
        let r3 = scalar_mul(&U256::from_le_u64s(&[3, 0, 0, 0]), &r).ok_or(
            PreparedTableError::MissingTriplePoint {
                point: "R",
                sig_id: cert.sig_id.0,
                cert_id: cert.cert_id.0,
            },
        )?;

        let base = [
            prepared(add_optional_points(
                Some(p3.clone()),
                negate_optional(Some(r.clone())),
            )),
            prepared(add_optional_points(
                Some(p.clone()),
                negate_optional(Some(r.clone())),
            )),
            prepared(add_optional_points(Some(p.clone()), Some(r.clone()))),
            prepared(add_optional_points(Some(p3.clone()), Some(r.clone()))),
            prepared(add_optional_points(
                Some(p3.clone()),
                negate_optional(Some(r3.clone())),
            )),
            prepared(add_optional_points(
                Some(p.clone()),
                negate_optional(Some(r3.clone())),
            )),
            prepared(add_optional_points(Some(p.clone()), Some(r3.clone()))),
            prepared(add_optional_points(Some(p3.clone()), Some(r3.clone()))),
        ];

        let selector0 =
            Selector16DecodeEntry::from_selector(selector.selectors[0]).map_err(|_| {
                PreparedTableError::InvalidSelector {
                    selector: selector.selectors[0].0,
                }
            })?;
        let selected = apply_selector(&base, selector0)?;
        let table16 = prepared(add_optional_points(selected.to_option(), Some(r3.clone())));

        Ok(Self {
            sig_id: cert.sig_id,
            cert_id: cert.cert_id,
            cert_active: cert.cert_active,
            base,
            r3: prepared(Some(r3)),
            table16,
        })
    }

    pub fn verify(&self) -> Result<(), PreparedTableError> {
        if self.cert_active.0 > 1 {
            return Err(PreparedTableError::NonBooleanFlag {
                field: "cert_active",
                actual: self.cert_active.0,
            });
        }
        for point in &self.base {
            point.verify()?;
        }
        self.r3.verify()?;
        self.table16.verify()?;
        Ok(())
    }

    pub fn instance(&self, table_index: u32) -> Option<PreparedPointInstance<M31>> {
        let point = match table_index {
            0..=7 => self.base[table_index as usize].clone(),
            TABLE16_INDEX => self.table16.clone(),
            _ => return None,
        };
        Some(point.instance(self.sig_id, self.cert_id, table_index))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedAffinePoint {
    pub x: P256M31BigInt,
    pub y: P256M31BigInt,
    pub inf: M31,
}

impl PreparedAffinePoint {
    pub const fn infinity() -> Self {
        Self {
            x: P256M31BigInt::zero(),
            y: P256M31BigInt::zero(),
            inf: M31::from_u32_unchecked(1),
        }
    }

    pub fn from_affine(point: AffinePoint) -> Self {
        Self {
            x: P256M31BigInt::from_u256(&point.x),
            y: P256M31BigInt::from_u256(&point.y),
            inf: M31::from_u32_unchecked(0),
        }
    }

    /// All-zero point (`x = y = 0`, `inf = 0`). Used as the inert filler for the
    /// negation aux block on rows that do not witness a negation; distinct from
    /// [`Self::infinity`] (which sets `inf = 1`).
    pub const fn from_zero_limbs() -> Self {
        Self {
            x: P256M31BigInt::zero(),
            y: P256M31BigInt::zero(),
            inf: M31::from_u32_unchecked(0),
        }
    }

    pub fn verify(&self) -> Result<(), PreparedTableError> {
        if self.inf.0 > 1 {
            return Err(PreparedTableError::NonBooleanFlag {
                field: "inf",
                actual: self.inf.0,
            });
        }
        if self.inf.0 == 1 && (self.x != P256M31BigInt::zero() || self.y != P256M31BigInt::zero()) {
            return Err(PreparedTableError::NonCanonicalInfinity);
        }
        Ok(())
    }

    pub fn to_option(&self) -> Option<AffinePoint> {
        (self.inf.0 == 0).then(|| AffinePoint {
            x: self.x.to_u256(),
            y: self.y.to_u256(),
        })
    }

    pub fn instance(
        &self,
        sig_id: M31,
        cert_id: M31,
        table_index: u32,
    ) -> PreparedPointInstance<M31> {
        PreparedPointInstance {
            sig_id,
            cert_id,
            table_index: M31::from_u32_unchecked(table_index),
            x: self.x.clone(),
            y: self.y.clone(),
            inf: self.inf,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreparedTableError {
    RowCountMismatch {
        certs: usize,
        fake_glv: usize,
        selectors: usize,
    },
    UseCountCountMismatch {
        tables: usize,
        use_counts: usize,
    },
    EcTraceCountMismatch {
        certs: usize,
        fake_glv: usize,
        selectors: usize,
        tables: usize,
    },
    IdMismatch {
        source: &'static str,
        cert_sig_id: u32,
        cert_cert_id: u32,
        other_sig_id: u32,
        other_cert_id: u32,
    },
    InvalidSelector {
        selector: u32,
    },
    NonBooleanFlag {
        field: &'static str,
        actual: u32,
    },
    MissingHintPoint {
        sig_id: u32,
        cert_id: u32,
    },
    MissingTriplePoint {
        point: &'static str,
        sig_id: u32,
        cert_id: u32,
    },
    EcTraceOutputMismatch {
        sig_id: u32,
        cert_id: u32,
        kind: PreparedTableEcRowKind,
    },
    PreparedTableOutputMismatch {
        sig_id: u32,
        cert_id: u32,
        table_index: u32,
    },
    PreparedPointTraceMismatch,
    InactiveEcTraceRows {
        sig_id: u32,
        cert_id: u32,
    },
    EcTraceCertRowCountMismatch {
        sig_id: u32,
        cert_id: u32,
        expected: usize,
        actual: usize,
    },
    EcTraceExpectedOutputMissing {
        sig_id: u32,
        cert_id: u32,
        label: &'static str,
    },
    EcTraceExpectedOutputDuplicate {
        sig_id: u32,
        cert_id: u32,
        label: &'static str,
    },
    EcTraceExpectedOutputMismatch {
        sig_id: u32,
        cert_id: u32,
        label: &'static str,
    },
    EcTraceRowsExceedDomain {
        rows: usize,
        domain: usize,
    },
    ProjectiveSourcePrefixTooShort {
        prepared: usize,
        projective: usize,
    },
    ProjectiveSourceInvalid,
    RelationImbalance {
        relation: &'static str,
    },
    PreprocessedColumnMissing,
    NonCanonicalInfinity,
    ProofLayer,
}

fn require_unique_output(
    rows: &[&PreparedTableEcRow],
    sig_id: M31,
    cert_id: M31,
    kind: PreparedTableEcRowKind,
    label: &'static str,
    expected: &PreparedAffinePoint,
) -> Result<(), PreparedTableError> {
    let matches = rows
        .iter()
        .copied()
        .filter(|row| row.kind == kind)
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [] => Err(PreparedTableError::EcTraceExpectedOutputMissing {
            sig_id: sig_id.0,
            cert_id: cert_id.0,
            label,
        }),
        [row] if &row.output == expected => Ok(()),
        [_row] => Err(PreparedTableError::EcTraceExpectedOutputMismatch {
            sig_id: sig_id.0,
            cert_id: cert_id.0,
            label,
        }),
        _ => Err(PreparedTableError::EcTraceExpectedOutputDuplicate {
            sig_id: sig_id.0,
            cert_id: cert_id.0,
            label,
        }),
    }
}

fn prepared_table_ec_rows_for_cert(
    cert: &CertScalarInputRow,
    fake_glv: &FakeGlvScalarHintRow,
    selector: &FakeGlvSelectorRow,
    table: &PreparedTableCert,
) -> Result<Vec<PreparedTableEcRow>, PreparedTableError> {
    require_same_id("fake_glv", cert, fake_glv.sig_id, fake_glv.cert_id)?;
    require_same_id("selector", cert, selector.sig_id, selector.cert_id)?;
    if cert.sig_id != table.sig_id || cert.cert_id != table.cert_id {
        return Err(PreparedTableError::IdMismatch {
            source: "prepared_table",
            cert_sig_id: cert.sig_id.0,
            cert_cert_id: cert.cert_id.0,
            other_sig_id: table.sig_id.0,
            other_cert_id: table.cert_id.0,
        });
    }
    if cert.cert_active.0 == 0 {
        return Ok(Vec::new());
    }

    let sig_id = cert.sig_id;
    let cert_id = cert.cert_id;
    let p = PreparedAffinePoint::from_affine(AffinePoint {
        x: cert.base_x.to_u256(),
        y: cert.base_y.to_u256(),
    });
    let h = scalar_mul(
        &cert.scalar.to_u256(),
        &p.to_option().expect("base point finite"),
    )
    .ok_or(PreparedTableError::MissingHintPoint {
        sig_id: cert.sig_id.0,
        cert_id: cert.cert_id.0,
    })?;
    let r = PreparedAffinePoint::from_affine(signed_hint_point(&h, fake_glv.hint.s2_sign_bit)?);

    let mut rows = Vec::new();
    let p3 = if cert.cert_id.0 == CERT_ID_U1_GENERATOR {
        PreparedAffinePoint::from_affine(
            scalar_mul(&U256::from_le_u64s(&[3, 0, 0, 0]), &p.to_option().unwrap()).ok_or(
                PreparedTableError::MissingTriplePoint {
                    point: "P",
                    sig_id: cert.sig_id.0,
                    cert_id: cert.cert_id.0,
                },
            )?,
        )
    } else {
        let p2 = prepared(double_optional(p.to_option()));
        rows.push(PreparedTableEcRow::double(
            sig_id,
            cert_id,
            PreparedTableEcRowKind::DoubleP,
            p.clone(),
            p2.clone(),
        ));
        let p3 = prepared(add_optional_points(p2.to_option(), p.to_option()));
        rows.push(PreparedTableEcRow::add(
            sig_id,
            cert_id,
            PreparedTableEcRowKind::AddP2P,
            p2,
            p.clone(),
            p3.clone(),
        ));
        p3
    };

    let r2 = prepared(double_optional(r.to_option()));
    rows.push(PreparedTableEcRow::double(
        sig_id,
        cert_id,
        PreparedTableEcRowKind::DoubleR,
        r.clone(),
        r2.clone(),
    ));
    rows.push(PreparedTableEcRow::add(
        sig_id,
        cert_id,
        PreparedTableEcRowKind::AddR2R,
        r2.clone(),
        r.clone(),
        table.r3.clone(),
    ));

    let base_operands = [
        (p3.clone(), prepared(negate_optional(r.to_option()))),
        (p.clone(), prepared(negate_optional(r.to_option()))),
        (p.clone(), r.clone()),
        (p3.clone(), r.clone()),
        (p3.clone(), prepared(negate_optional(table.r3.to_option()))),
        (p.clone(), prepared(negate_optional(table.r3.to_option()))),
        (p.clone(), table.r3.clone()),
        (p3.clone(), table.r3.clone()),
    ];

    for (index, (lhs, rhs)) in base_operands.into_iter().enumerate() {
        let output = table.base[index].clone();
        rows.push(PreparedTableEcRow::add(
            sig_id,
            cert_id,
            PreparedTableEcRowKind::Base(index as u32),
            lhs.clone(),
            rhs.clone(),
            output.clone(),
        ));
        let expected = prepared(add_optional_points(lhs.to_option(), rhs.to_option()));
        if output != expected {
            return Err(PreparedTableError::PreparedTableOutputMismatch {
                sig_id: sig_id.0,
                cert_id: cert_id.0,
                table_index: index as u32,
            });
        }
    }

    let selector0 = Selector16DecodeEntry::from_selector(selector.selectors[0]).map_err(|_| {
        PreparedTableError::InvalidSelector {
            selector: selector.selectors[0].0,
        }
    })?;
    let selected = apply_selector(&table.base, selector0)?;
    rows.push(PreparedTableEcRow::add(
        sig_id,
        cert_id,
        PreparedTableEcRowKind::Table16,
        selected.clone(),
        table.r3.clone(),
        table.table16.clone(),
    ));
    let expected_table16 = prepared(add_optional_points(
        selected.to_option(),
        table.r3.to_option(),
    ));
    if table.table16 != expected_table16 {
        return Err(PreparedTableError::PreparedTableOutputMismatch {
            sig_id: sig_id.0,
            cert_id: cert_id.0,
            table_index: TABLE16_INDEX,
        });
    }

    Ok(rows)
}

/// Test-only variant of [`prepared_table_ec_rows_for_cert`] that uses an
/// injected `R'` instead of the production `R`. Mirrors the production row
/// shape exactly, sourcing R-derived outputs from `table` (which must itself
/// be built from the same `R'`). The internal `output == expected` checks are
/// kept verbatim so trace fidelity is preserved for an arbitrary `R'`.
#[cfg(test)]
fn prepared_table_ec_rows_for_cert_with_r_override(
    cert: &CertScalarInputRow,
    selector: &FakeGlvSelectorRow,
    table: &PreparedTableCert,
    r_override: AffinePoint,
) -> Result<Vec<PreparedTableEcRow>, PreparedTableError> {
    assert_eq!(cert.cert_active.0, 1, "override path requires active cert");
    let sig_id = cert.sig_id;
    let cert_id = cert.cert_id;
    let p = PreparedAffinePoint::from_affine(AffinePoint {
        x: cert.base_x.to_u256(),
        y: cert.base_y.to_u256(),
    });
    let r = PreparedAffinePoint::from_affine(r_override);

    let mut rows = Vec::new();
    let p3 = if cert.cert_id.0 == CERT_ID_U1_GENERATOR {
        PreparedAffinePoint::from_affine(
            scalar_mul(&U256::from_le_u64s(&[3, 0, 0, 0]), &p.to_option().unwrap()).ok_or(
                PreparedTableError::MissingTriplePoint {
                    point: "P",
                    sig_id: cert.sig_id.0,
                    cert_id: cert.cert_id.0,
                },
            )?,
        )
    } else {
        let p2 = prepared(double_optional(p.to_option()));
        rows.push(PreparedTableEcRow::double(
            sig_id,
            cert_id,
            PreparedTableEcRowKind::DoubleP,
            p.clone(),
            p2.clone(),
        ));
        let p3 = prepared(add_optional_points(p2.to_option(), p.to_option()));
        rows.push(PreparedTableEcRow::add(
            sig_id,
            cert_id,
            PreparedTableEcRowKind::AddP2P,
            p2,
            p.clone(),
            p3.clone(),
        ));
        p3
    };

    let r2 = prepared(double_optional(r.to_option()));
    rows.push(PreparedTableEcRow::double(
        sig_id,
        cert_id,
        PreparedTableEcRowKind::DoubleR,
        r.clone(),
        r2.clone(),
    ));
    rows.push(PreparedTableEcRow::add(
        sig_id,
        cert_id,
        PreparedTableEcRowKind::AddR2R,
        r2.clone(),
        r.clone(),
        table.r3.clone(),
    ));

    let base_operands = [
        (p3.clone(), prepared(negate_optional(r.to_option()))),
        (p.clone(), prepared(negate_optional(r.to_option()))),
        (p.clone(), r.clone()),
        (p3.clone(), r.clone()),
        (p3.clone(), prepared(negate_optional(table.r3.to_option()))),
        (p.clone(), prepared(negate_optional(table.r3.to_option()))),
        (p.clone(), table.r3.clone()),
        (p3.clone(), table.r3.clone()),
    ];

    for (index, (lhs, rhs)) in base_operands.into_iter().enumerate() {
        let output = table.base[index].clone();
        rows.push(PreparedTableEcRow::add(
            sig_id,
            cert_id,
            PreparedTableEcRowKind::Base(index as u32),
            lhs.clone(),
            rhs.clone(),
            output.clone(),
        ));
        let expected = prepared(add_optional_points(lhs.to_option(), rhs.to_option()));
        if output != expected {
            return Err(PreparedTableError::PreparedTableOutputMismatch {
                sig_id: sig_id.0,
                cert_id: cert_id.0,
                table_index: index as u32,
            });
        }
    }

    let selector0 = Selector16DecodeEntry::from_selector(selector.selectors[0]).map_err(|_| {
        PreparedTableError::InvalidSelector {
            selector: selector.selectors[0].0,
        }
    })?;
    let selected = apply_selector(&table.base, selector0)?;
    rows.push(PreparedTableEcRow::add(
        sig_id,
        cert_id,
        PreparedTableEcRowKind::Table16,
        selected.clone(),
        table.r3.clone(),
        table.table16.clone(),
    ));
    let expected_table16 = prepared(add_optional_points(
        selected.to_option(),
        table.r3.to_option(),
    ));
    if table.table16 != expected_table16 {
        return Err(PreparedTableError::PreparedTableOutputMismatch {
            sig_id: sig_id.0,
            cert_id: cert_id.0,
            table_index: TABLE16_INDEX,
        });
    }

    Ok(rows)
}

/// Test-only: build a [`PreparedTableEcTraceClaim`] where the cert at
/// `override_cert_index` uses the injected `R'`; all other certs use the
/// production path. Skips the cross-`verify` against the native (true-R)
/// derivation so a wrong-`R'` trace can be assembled.
#[cfg(test)]
impl PreparedTableEcTraceClaim {
    pub(crate) fn from_claims_with_r_override(
        cert_inputs: &CertScalarInputClaim,
        fake_glv_scalars: &FakeGlvScalarHintClaim,
        selectors: &FakeGlvSelectorClaim,
        table: &PreparedTableClaim,
        override_cert_index: usize,
        r_override: AffinePoint,
    ) -> Result<Self, PreparedTableError> {
        let mut rows = Vec::new();
        for (index, (((cert, fake_glv), selector), table_cert)) in cert_inputs
            .rows
            .iter()
            .zip(&fake_glv_scalars.rows)
            .zip(&selectors.rows)
            .zip(&table.certs)
            .enumerate()
        {
            if index == override_cert_index {
                rows.extend(prepared_table_ec_rows_for_cert_with_r_override(
                    cert,
                    selector,
                    table_cert,
                    r_override.clone(),
                )?);
            } else {
                rows.extend(prepared_table_ec_rows_for_cert(
                    cert, fake_glv, selector, table_cert,
                )?);
            }
        }
        Ok(Self { rows })
    }
}

/// Test-only: build a [`PreparedTableClaim`] where the cert at
/// `override_cert_index` is rebuilt from the injected `R'`.
#[cfg(test)]
impl PreparedTableClaim {
    pub(crate) fn from_claims_with_r_override(
        cert_inputs: &CertScalarInputClaim,
        fake_glv_scalars: &FakeGlvScalarHintClaim,
        selectors: &FakeGlvSelectorClaim,
        override_cert_index: usize,
        r_override: AffinePoint,
    ) -> Result<Self, PreparedTableError> {
        let certs = cert_inputs
            .rows
            .iter()
            .zip(&fake_glv_scalars.rows)
            .zip(&selectors.rows)
            .enumerate()
            .map(|(index, ((cert, fake_glv), selector))| {
                if index == override_cert_index {
                    PreparedTableCert::new_with_r_override(
                        cert,
                        fake_glv,
                        selector,
                        r_override.clone(),
                    )
                } else {
                    PreparedTableCert::new(cert, fake_glv, selector)
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self { certs })
    }
}

fn require_same_id(
    source: &'static str,
    cert: &CertScalarInputRow,
    other_sig_id: M31,
    other_cert_id: M31,
) -> Result<(), PreparedTableError> {
    if cert.sig_id == other_sig_id && cert.cert_id == other_cert_id {
        Ok(())
    } else {
        Err(PreparedTableError::IdMismatch {
            source,
            cert_sig_id: cert.sig_id.0,
            cert_cert_id: cert.cert_id.0,
            other_sig_id: other_sig_id.0,
            other_cert_id: other_cert_id.0,
        })
    }
}

fn signed_hint_point(h: &AffinePoint, s2_sign_bit: M31) -> Result<AffinePoint, PreparedTableError> {
    match s2_sign_bit.0 {
        0 => Ok(h.clone()),
        1 => Ok(negate_point(h)),
        actual => Err(PreparedTableError::NonBooleanFlag {
            field: "s2_sign_bit",
            actual,
        }),
    }
}

pub(crate) fn apply_selector(
    base: &[PreparedAffinePoint; PREPARED_BASE_COUNT],
    selector: Selector16DecodeEntry,
) -> Result<PreparedAffinePoint, PreparedTableError> {
    let base_index = selector.base_index.0 as usize;
    let point = base
        .get(base_index)
        .cloned()
        .ok_or(PreparedTableError::InvalidSelector {
            selector: selector.selector.0,
        })?;
    if selector.neg_bit.0 == 0 {
        Ok(point)
    } else if selector.neg_bit.0 == 1 {
        Ok(prepared(negate_optional(point.to_option())))
    } else {
        Err(PreparedTableError::NonBooleanFlag {
            field: "selector.neg_bit",
            actual: selector.neg_bit.0,
        })
    }
}

pub(crate) fn prepared(point: Option<AffinePoint>) -> PreparedAffinePoint {
    point.map_or_else(
        PreparedAffinePoint::infinity,
        PreparedAffinePoint::from_affine,
    )
}

pub(crate) fn add_optional_points(
    lhs: Option<AffinePoint>,
    rhs: Option<AffinePoint>,
) -> Option<AffinePoint> {
    match (lhs, rhs) {
        (None, None) => None,
        (Some(point), None) | (None, Some(point)) => Some(point),
        (Some(lhs), Some(rhs)) if lhs == rhs => Some(point_double(&lhs).output),
        (Some(lhs), Some(rhs)) if is_additive_inverse(&lhs, &rhs) => None,
        (Some(lhs), Some(rhs)) => Some(point_add(&lhs, &rhs).output),
    }
}

fn double_optional(point: Option<AffinePoint>) -> Option<AffinePoint> {
    point.map(|point| point_double(&point).output)
}

fn negate_optional(point: Option<AffinePoint>) -> Option<AffinePoint> {
    point.map(|point| negate_point(&point))
}

fn negate_point(point: &AffinePoint) -> AffinePoint {
    AffinePoint {
        x: point.x.clone(),
        y: sub_mod_witness(
            &U256::from_le_u64s(&P256_MODULUS),
            &point.y,
            &U256::from_le_u64s(&P256_MODULUS),
        )
        .result
        .to_u256(),
    }
}

fn is_additive_inverse(lhs: &AffinePoint, rhs: &AffinePoint) -> bool {
    lhs.x == rhs.x
        && add_mod_witness(&lhs.y, &rhs.y, &U256::from_le_u64s(&P256_MODULUS))
            .result
            .to_u256()
            == U256::ZERO
}
