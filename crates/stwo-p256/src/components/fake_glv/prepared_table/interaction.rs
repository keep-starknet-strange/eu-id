//! Interaction-trace (LogUp) generation for the prepared-table family: the
//! interaction claim types, the per-row / pinned / projective-source
//! generators, and the packed/unpacked relation-tuple builders.
//!
//! Split out of `mod.rs` (pure relocation, no behavioral change).

use stwo::core::{channel::Channel, fields::m31::M31, fields::qm31::SecureField, ColumnVec};
use stwo::prover::backend::simd::{
    m31::{PackedM31, LOG_N_LANES},
    qm31::PackedQM31,
};
use stwo_constraint_framework::{LogupTraceGenerator, Relation};
use stwo_p256_utils::constants::N_LIMBS;

use crate::constants::{P256_3GX, P256_3GY};
use crate::limbs::P256M31BigInt;
use crate::projective_air::{
    ProjectiveRcbMulResultRelation, PROJECTIVE_RCB_MUL_ROLE_LHS, PROJECTIVE_RCB_MUL_ROLE_RESULT,
    PROJECTIVE_RCB_MUL_ROLE_RHS, PROJECTIVE_RCB_OP_MUL_LIMB_COLUMNS,
};
use crate::types::U256;

use crate::scalar::scalar_mod_mul::columns::M31ColumnEval;

use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PreparedTableEcRowInteractionClaim {
    pub claimed_sum: SecureField,
}


impl PreparedTableEcRowInteractionClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}


#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PreparedTableProjectiveSourceInteractionClaim {
    pub provider_claimed_sum: SecureField,
    /// `PreparedTableEcRowRelation` consumer sum.
    pub consumer_claimed_sum: SecureField,
    /// C5 plumbing: `ProjectiveRcbMulResultRelation` consumer sum (silo mul
    /// limbs consumed on the prepared-table projective-source consumer). Shares
    /// the consumer's interaction trace, balanced separately under
    /// `ProjectiveRcbMulResult`.
    pub mul_result_consumer_claimed_sum: SecureField,
}


impl PreparedTableProjectiveSourceInteractionClaim {
    pub fn zero() -> Self {
        Self {
            provider_claimed_sum: secure_zero(),
            consumer_claimed_sum: secure_zero(),
            mul_result_consumer_claimed_sum: secure_zero(),
        }
    }

    /// `PreparedTableProjectiveSource` balance term: provider + EC-row consume.
    /// EXCLUDES the mul-result consume (balanced under `ProjectiveRcbMulResult`).
    pub fn total(self) -> SecureField {
        self.provider_claimed_sum + self.consumer_claimed_sum
    }

    /// The single claimed sum the consumer FrameworkComponent declares (EC-row
    /// + mul-result consumes share one interaction trace / `finalize_logup`).
    pub fn consumer_component_claimed_sum(self) -> SecureField {
        self.consumer_claimed_sum + self.mul_result_consumer_claimed_sum
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[
            self.provider_claimed_sum,
            self.consumer_claimed_sum,
            self.mul_result_consumer_claimed_sum,
        ]);
    }
}


pub(crate) fn gen_prepared_table_ec_row_interaction_trace(
    base: &[M31ColumnEval],
    relation: &PreparedTableEcRowRelation,
) -> (ColumnVec<M31ColumnEval>, PreparedTableEcRowInteractionClaim) {
    assert_eq!(base.len(), PREPARED_TABLE_EC_ROW_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let values = prepared_table_ec_row_packed_relation_values(base, vec_row);
        let numerator = -PackedQM31::from(base[0].data[vec_row]);
        let denominator: PackedQM31 = relation.combine(&values);
        col.write_frac(vec_row, numerator, denominator);
    }
    col.finalize_col();
    let (trace, claimed_sum) = logup.finalize_last();
    (trace, PreparedTableEcRowInteractionClaim { claimed_sum })
}


// Base-trace column offsets for the EC-row provider (used by the pinned
// interaction trace generator). Layout: active, source_index, sig_id, cert_id,
// kind_flags[13], op, table_index, lhs[41], rhs[41], output[41], neg[41],
// neg_carries[20].
const PREPARED_TABLE_EC_COL_SIG_ID: usize = 2;

const PREPARED_TABLE_EC_COL_CERT_ID: usize = 3;

const PREPARED_TABLE_EC_COL_KIND_FLAGS: usize = 4;

const PREPARED_TABLE_EC_COL_LHS: usize = 4 + PREPARED_TABLE_EC_KIND_FLAGS + 2;

const PREPARED_TABLE_EC_COL_RHS: usize = PREPARED_TABLE_EC_COL_LHS + PREPARED_TABLE_EC_POINT_COLUMNS;

const PREPARED_TABLE_EC_COL_OUTPUT: usize =
    PREPARED_TABLE_EC_COL_RHS + PREPARED_TABLE_EC_POINT_COLUMNS;

const PREPARED_TABLE_EC_COL_NEG: usize =
    PREPARED_TABLE_EC_COL_OUTPUT + PREPARED_TABLE_EC_POINT_COLUMNS;


fn pin_point_column_offset(point: PinPoint) -> Option<usize> {
    match point {
        PinPoint::Lhs => Some(PREPARED_TABLE_EC_COL_LHS),
        PinPoint::Rhs => Some(PREPARED_TABLE_EC_COL_RHS),
        PinPoint::Output => Some(PREPARED_TABLE_EC_COL_OUTPUT),
        PinPoint::Neg => Some(PREPARED_TABLE_EC_COL_NEG),
        PinPoint::ConstThreeG => None,
    }
}


/// Per-relation claimed sums of the pinned EC-row provider's logup trace. `total`
/// is what the provider component declares; the breakdown lets `verify_balanced`
/// check each relation independently.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PreparedTableEcRowPinnedInteractionClaim {
    pub total_claimed_sum: SecureField,
    pub prepared_table_provider_claimed_sum: SecureField,
    pub cert_base_consumer_claimed_sum: SecureField,
    pub canonical_claimed_sum: SecureField,
    /// FinalCheckHint provider sum (yield `-1` per active `DoubleR` row). Zero
    /// when no `final_check_hint` relation is forwarded.
    pub final_check_hint_claimed_sum: SecureField,
}


impl PreparedTableEcRowPinnedInteractionClaim {
    pub fn zero() -> Self {
        Self {
            total_claimed_sum: secure_zero(),
            prepared_table_provider_claimed_sum: secure_zero(),
            cert_base_consumer_claimed_sum: secure_zero(),
            canonical_claimed_sum: secure_zero(),
            final_check_hint_claimed_sum: secure_zero(),
        }
    }
}


/// Interaction trace for the monolithic EC-row provider: the base
/// `PreparedTableEcRowRelation` yield plus the 30 `PIN_SCHEDULE` fractions, in
/// the exact order emitted by `PreparedTableEcRowEval::evaluate`. When
/// `final_check_hint` is `Some`, one more fraction is appended (the `DoubleR`
/// `R_i` yield) to mirror the AIR's FinalCheckHint emission.
pub(crate) fn gen_prepared_table_ec_row_pinned_interaction_trace(
    base: &[M31ColumnEval],
    relation: &PreparedTableEcRowRelation,
    cert_base: &CertBaseRelation,
    canonical: &PreparedTableCanonicalRelation,
    final_check_hint: Option<&FinalCheckHintRelation>,
) -> (ColumnVec<M31ColumnEval>, PreparedTableEcRowPinnedInteractionClaim) {
    assert_eq!(base.len(), PREPARED_TABLE_EC_ROW_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let n_vec_rows = 1 << (log_size - LOG_N_LANES);
    let mut logup = LogupTraceGenerator::new(log_size);

    // Column 0: the existing PreparedTableEcRowRelation yield (-active).
    let mut col = logup.new_col();
    for vec_row in 0..n_vec_rows {
        let values = prepared_table_ec_row_packed_relation_values(base, vec_row);
        col.write_frac(
            vec_row,
            -PackedQM31::from(base[0].data[vec_row]),
            relation.combine(&values),
        );
    }
    col.finalize_col();

    let three_g_x = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_3GX));
    let three_g_y = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_3GY));

    // Columns 1..=30: the pinning schedule, one fraction per entry.
    for entry in PIN_SCHEDULE {
        let mut col = logup.new_col();
        for vec_row in 0..n_vec_rows {
            let sig = base[PREPARED_TABLE_EC_COL_SIG_ID].data[vec_row];
            let cert = base[PREPARED_TABLE_EC_COL_CERT_ID].data[vec_row];
            let active = base[0].data[vec_row];
            // Gate = product of kind flags (× is_cert0 = active - cert_id).
            let mut gate = PackedM31::broadcast(M31::from_u32_unchecked(1));
            for &k in entry.kinds {
                gate *= base[PREPARED_TABLE_EC_COL_KIND_FLAGS + k].data[vec_row];
            }
            if entry.cert0_only {
                gate *= active - cert;
            }
            let magnitude = PackedM31::broadcast(M31::from_u32_unchecked(entry.mult.unsigned_abs()));
            let scaled = PackedQM31::from(gate * magnitude);
            let numerator = if entry.mult < 0 { -scaled } else { scaled };
            let denominator: PackedQM31 = match entry.relation {
                PinRelation::CertBase => {
                    let offset = pin_point_column_offset(entry.point)
                        .expect("CertBase entries use a trace point");
                    cert_base.combine(&cert_base_packed_tuple(base, vec_row, sig, cert, offset))
                }
                PinRelation::Canonical(role) => {
                    let tuple = match pin_point_column_offset(entry.point) {
                        Some(offset) => {
                            canonical_packed_tuple_from_columns(base, vec_row, sig, cert, role, offset)
                        }
                        None => canonical_packed_tuple_const(
                            sig,
                            cert,
                            role,
                            &three_g_x,
                            &three_g_y,
                        ),
                    };
                    canonical.combine(&tuple)
                }
            };
            col.write_frac(vec_row, numerator, denominator);
        }
        col.finalize_col();
    }

    // Optional FinalCheckHint column: yield `R_i` (= `lhs`) gated `active *
    // DoubleR_flag`, multiplicity `-1`. Emitted iff a relation is supplied, in
    // lockstep with the AIR's `if let Some(final_check_hint)` emission.
    if let Some(final_check_hint) = final_check_hint {
        let mut col = logup.new_col();
        for vec_row in 0..n_vec_rows {
            let sig = base[PREPARED_TABLE_EC_COL_SIG_ID].data[vec_row];
            let cert = base[PREPARED_TABLE_EC_COL_CERT_ID].data[vec_row];
            let active = base[0].data[vec_row];
            let double_r = base
                [PREPARED_TABLE_EC_COL_KIND_FLAGS + PREPARED_TABLE_EC_KIND_DOUBLE_R]
                .data[vec_row];
            let gate = active * double_r;
            let numerator = -PackedQM31::from(gate);
            let denominator = final_check_hint.combine(&final_check_hint_packed_tuple(
                base,
                vec_row,
                sig,
                cert,
                PREPARED_TABLE_EC_COL_LHS,
            ));
            col.write_frac(vec_row, numerator, denominator);
        }
        col.finalize_col();
    }

    let (trace, total_claimed_sum) = logup.finalize_last();

    // Per-relation breakdown over storage rows (active rows only).
    let mut prepared_table_provider_claimed_sum = secure_zero();
    let mut cert_base_consumer_claimed_sum = secure_zero();
    let mut canonical_claimed_sum = secure_zero();
    let mut final_check_hint_claimed_sum = secure_zero();
    for row in prepared_table_ec_storage_rows(base) {
        let active = row[0];
        if active == M31::from_u32_unchecked(0) {
            continue;
        }
        let sig = row[PREPARED_TABLE_EC_COL_SIG_ID];
        let cert = row[PREPARED_TABLE_EC_COL_CERT_ID];
        // Existing relation yield (-active).
        let values = prepared_table_ec_row_unpacked_relation_values(&row);
        let existing_denom: SecureField = relation.combine(&values);
        prepared_table_provider_claimed_sum += -SecureField::from(active) / existing_denom;
        // FinalCheckHint yield (-1) on active DoubleR rows.
        if let Some(final_check_hint) = final_check_hint {
            let double_r = row[PREPARED_TABLE_EC_COL_KIND_FLAGS + PREPARED_TABLE_EC_KIND_DOUBLE_R];
            if double_r != M31::from_u32_unchecked(0) {
                let denom: SecureField = final_check_hint.combine(&final_check_hint_unpacked_tuple(
                    &row,
                    sig,
                    cert,
                    PREPARED_TABLE_EC_COL_LHS,
                ));
                final_check_hint_claimed_sum += -SecureField::from(active * double_r) / denom;
            }
        }
        for entry in PIN_SCHEDULE {
            let mut gate = M31::from_u32_unchecked(1);
            for &k in entry.kinds {
                gate *= row[PREPARED_TABLE_EC_COL_KIND_FLAGS + k];
            }
            if entry.cert0_only {
                gate *= active - cert;
            }
            if gate == M31::from_u32_unchecked(0) {
                continue;
            }
            let magnitude = M31::from_u32_unchecked(entry.mult.unsigned_abs());
            let scaled = SecureField::from(gate * magnitude);
            let numerator = if entry.mult < 0 { -scaled } else { scaled };
            match entry.relation {
                PinRelation::CertBase => {
                    let offset = pin_point_column_offset(entry.point).unwrap();
                    let denom: SecureField =
                        cert_base.combine(&cert_base_unpacked_tuple(&row, sig, cert, offset));
                    cert_base_consumer_claimed_sum += numerator / denom;
                }
                PinRelation::Canonical(role) => {
                    let tuple = match pin_point_column_offset(entry.point) {
                        Some(offset) => {
                            canonical_unpacked_tuple_from_columns(&row, sig, cert, role, offset)
                        }
                        None => {
                            canonical_unpacked_tuple_const(sig, cert, role, &three_g_x, &three_g_y)
                        }
                    };
                    let denom: SecureField = canonical.combine(&tuple);
                    canonical_claimed_sum += numerator / denom;
                }
            }
        }
    }

    (
        trace,
        PreparedTableEcRowPinnedInteractionClaim {
            total_claimed_sum,
            prepared_table_provider_claimed_sum,
            cert_base_consumer_claimed_sum,
            canonical_claimed_sum,
            final_check_hint_claimed_sum,
        },
    )
}


fn final_check_hint_packed_tuple(
    base: &[M31ColumnEval],
    vec_row: usize,
    sig: PackedM31,
    cert: PackedM31,
    point_offset: usize,
) -> [PackedM31; FINAL_CHECK_HINT_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0 => sig,
        1 => cert,
        2..=21 => base[point_offset + (index - 2)].data[vec_row],
        22..=41 => base[point_offset + N_LIMBS + (index - 22)].data[vec_row],
        42 => base[point_offset + 2 * N_LIMBS].data[vec_row],
        _ => unreachable!("final check hint tuple index in range"),
    })
}


fn final_check_hint_unpacked_tuple(
    row: &[M31],
    sig: M31,
    cert: M31,
    point_offset: usize,
) -> [M31; FINAL_CHECK_HINT_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0 => sig,
        1 => cert,
        2..=21 => row[point_offset + (index - 2)],
        22..=41 => row[point_offset + N_LIMBS + (index - 22)],
        42 => row[point_offset + 2 * N_LIMBS],
        _ => unreachable!("final check hint tuple index in range"),
    })
}


fn cert_base_packed_tuple(
    base: &[M31ColumnEval],
    vec_row: usize,
    sig: PackedM31,
    cert: PackedM31,
    point_offset: usize,
) -> [PackedM31; CERT_BASE_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0 => sig,
        1 => cert,
        2..=21 => base[point_offset + (index - 2)].data[vec_row],
        22..=41 => base[point_offset + N_LIMBS + (index - 22)].data[vec_row],
        _ => unreachable!("cert base tuple index in range"),
    })
}


fn cert_base_unpacked_tuple(
    row: &[M31],
    sig: M31,
    cert: M31,
    point_offset: usize,
) -> [M31; CERT_BASE_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0 => sig,
        1 => cert,
        2..=21 => row[point_offset + (index - 2)],
        22..=41 => row[point_offset + N_LIMBS + (index - 22)],
        _ => unreachable!("cert base tuple index in range"),
    })
}


fn canonical_packed_tuple_from_columns(
    base: &[M31ColumnEval],
    vec_row: usize,
    sig: PackedM31,
    cert: PackedM31,
    role: u32,
    point_offset: usize,
) -> [PackedM31; PREPARED_TABLE_CANONICAL_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0 => sig,
        1 => cert,
        2 => PackedM31::broadcast(M31::from_u32_unchecked(role)),
        3..=43 => base[point_offset + (index - 3)].data[vec_row],
        _ => unreachable!("canonical tuple index in range"),
    })
}


fn canonical_packed_tuple_const(
    sig: PackedM31,
    cert: PackedM31,
    role: u32,
    x: &P256M31BigInt,
    y: &P256M31BigInt,
) -> [PackedM31; PREPARED_TABLE_CANONICAL_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0 => sig,
        1 => cert,
        2 => PackedM31::broadcast(M31::from_u32_unchecked(role)),
        3..=22 => PackedM31::broadcast(x.limbs()[index - 3]),
        23..=42 => PackedM31::broadcast(y.limbs()[index - 23]),
        43 => PackedM31::broadcast(M31::from_u32_unchecked(0)),
        _ => unreachable!("canonical const tuple index in range"),
    })
}


fn canonical_unpacked_tuple_from_columns(
    row: &[M31],
    sig: M31,
    cert: M31,
    role: u32,
    point_offset: usize,
) -> [M31; PREPARED_TABLE_CANONICAL_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0 => sig,
        1 => cert,
        2 => M31::from_u32_unchecked(role),
        3..=43 => row[point_offset + (index - 3)],
        _ => unreachable!("canonical tuple index in range"),
    })
}


fn canonical_unpacked_tuple_const(
    sig: M31,
    cert: M31,
    role: u32,
    x: &P256M31BigInt,
    y: &P256M31BigInt,
) -> [M31; PREPARED_TABLE_CANONICAL_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0 => sig,
        1 => cert,
        2 => M31::from_u32_unchecked(role),
        3..=22 => x.limbs()[index - 3],
        23..=42 => y.limbs()[index - 23],
        43 => M31::from_u32_unchecked(0),
        _ => unreachable!("canonical const tuple index in range"),
    })
}


fn prepared_table_ec_storage_rows(base: &[M31ColumnEval]) -> impl Iterator<Item = Vec<M31>> + '_ {
    let row_count = base[0].domain.size();
    (0..row_count).map(move |row| {
        let vec_row = row / (1 << LOG_N_LANES);
        let lane = row % (1 << LOG_N_LANES);
        base.iter()
            .map(|column| column.data[vec_row].to_array()[lane])
            .collect::<Vec<_>>()
    })
}


fn prepared_table_ec_row_unpacked_relation_values(
    row: &[M31],
) -> [M31; PREPARED_TABLE_EC_ROW_RELATION_ARITY] {
    core::array::from_fn(|index| {
        let column = match index {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 17,
            4 => 18,
            5..=127 => 19 + (index - 5),
            _ => unreachable!("prepared-table EC relation index is in range"),
        };
        row[column]
    })
}


/// Canonical role order for the consumed mul-limb columns, matching
/// `projective_rcb_op_mul_limbs` and `ConsumedMulLimbs`.
const PROJECTIVE_RCB_MUL_RESULT_ROLES: [u32; 3] = [
    PROJECTIVE_RCB_MUL_ROLE_LHS,
    PROJECTIVE_RCB_MUL_ROLE_RHS,
    PROJECTIVE_RCB_MUL_ROLE_RESULT,
];


/// C5 plumbing: interaction trace for the prepared-table projective-source
/// CONSUMER. Emits, in the order `PreparedTableProjectiveSourceEval::evaluate`
/// does under one `finalize_logup`: the `PreparedTableEcRowRelation` consume
/// (col 0, `+active`), then one `ProjectiveRcbMulResultRelation` consume column
/// per committed mul limb (canonical mul/role/limb order, `+active`). Returns
/// the columns, the EC-row consumer sum, and the mul-result consumer sum.
pub(crate) fn gen_prepared_table_projective_source_consumer_interaction_trace(
    base: &[M31ColumnEval],
    ec_row_relation: &PreparedTableEcRowRelation,
    mul_result_relation: &ProjectiveRcbMulResultRelation,
) -> (ColumnVec<M31ColumnEval>, SecureField, SecureField) {
    assert_eq!(base.len(), PREPARED_TABLE_PROJECTIVE_SOURCE_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);

    // Column 0: the existing EC-row consume (+active).
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let values = prepared_table_projective_source_packed_relation_values(base, vec_row);
        let active = PackedQM31::from(base[0].data[vec_row]);
        col.write_frac(vec_row, active, ec_row_relation.combine(&values));
    }
    col.finalize_col();

    // Mul-result consume columns (one per fraction, gated by the `has_muls`
    // column), canonical order.
    for mul_index in 0..(PROJECTIVE_RCB_OP_MUL_LIMB_COLUMNS / (3 * N_LIMBS)) {
        for (role_index, &role) in PROJECTIVE_RCB_MUL_RESULT_ROLES.iter().enumerate() {
            for limb_index in 0..N_LIMBS {
                let base_col = PREPARED_TABLE_PROJECTIVE_SOURCE_MUL_LIMB_OFFSET
                    + mul_index * (3 * N_LIMBS)
                    + role_index * N_LIMBS
                    + limb_index;
                let mut col = logup.new_col();
                for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                    let source_index = base[1].data[vec_row];
                    let limb = base[base_col].data[vec_row];
                    let has_muls = PackedQM31::from(
                        base[PREPARED_TABLE_PROJECTIVE_SOURCE_HAS_MULS_COL].data[vec_row],
                    );
                    let values = [
                        source_index,
                        PackedM31::broadcast(M31::from_u32_unchecked(mul_index as u32)),
                        PackedM31::broadcast(M31::from_u32_unchecked(role)),
                        PackedM31::broadcast(M31::from_u32_unchecked(limb_index as u32)),
                        limb,
                    ];
                    col.write_frac(vec_row, has_muls, mul_result_relation.combine(&values));
                }
                col.finalize_col();
            }
        }
    }
    let (columns, _total) = logup.finalize_last();

    let (ec_row_sum, mul_result_sum) =
        prepared_table_projective_source_consumer_sums(base, ec_row_relation, mul_result_relation);
    (columns, ec_row_sum, mul_result_sum)
}


/// Analytic `(ec_row_consumer_sum, mul_result_consumer_sum)` over the consumer
/// base trace's active rows, using unpacked `SecureField` combines.
fn prepared_table_projective_source_consumer_sums(
    base: &[M31ColumnEval],
    ec_row_relation: &PreparedTableEcRowRelation,
    mul_result_relation: &ProjectiveRcbMulResultRelation,
) -> (SecureField, SecureField) {
    let log_size = base[0].domain.log_size();
    let mut ec_row_sum = secure_zero();
    let mut mul_result_sum = secure_zero();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        for lane in 0..(1 << LOG_N_LANES) {
            let active = base[0].data[vec_row].to_array()[lane];
            if active != M31::from_u32_unchecked(0) {
                let ec_values =
                    prepared_table_projective_source_unpacked_relation_values(base, vec_row, lane);
                let denom: SecureField = ec_row_relation.combine(&ec_values);
                ec_row_sum += SecureField::from(active) / denom;
            }

            let has_muls =
                base[PREPARED_TABLE_PROJECTIVE_SOURCE_HAS_MULS_COL].data[vec_row].to_array()[lane];
            if has_muls == M31::from_u32_unchecked(0) {
                continue;
            }
            let has_muls_ef = SecureField::from(has_muls);
            let source_index = base[1].data[vec_row].to_array()[lane];
            for mul_index in 0..(PROJECTIVE_RCB_OP_MUL_LIMB_COLUMNS / (3 * N_LIMBS)) {
                for (role_index, &role) in PROJECTIVE_RCB_MUL_RESULT_ROLES.iter().enumerate() {
                    for limb_index in 0..N_LIMBS {
                        let base_col = PREPARED_TABLE_PROJECTIVE_SOURCE_MUL_LIMB_OFFSET
                            + mul_index * (3 * N_LIMBS)
                            + role_index * N_LIMBS
                            + limb_index;
                        let limb = base[base_col].data[vec_row].to_array()[lane];
                        let denom: SecureField = mul_result_relation.combine(&[
                            source_index,
                            M31::from_u32_unchecked(mul_index as u32),
                            M31::from_u32_unchecked(role),
                            M31::from_u32_unchecked(limb_index as u32),
                            limb,
                        ]);
                        mul_result_sum += has_muls_ef / denom;
                    }
                }
            }
        }
    }
    (ec_row_sum, mul_result_sum)
}


fn prepared_table_projective_source_unpacked_relation_values(
    base: &[M31ColumnEval],
    vec_row: usize,
    lane: usize,
) -> [M31; PREPARED_TABLE_EC_ROW_RELATION_ARITY] {
    core::array::from_fn(|index| {
        let column = match index {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 4,
            4 => 5,
            5..=127 => 6 + (index - 5),
            _ => unreachable!("prepared-table projective source relation index is in range"),
        };
        base[column].data[vec_row].to_array()[lane]
    })
}


fn prepared_table_ec_row_packed_relation_values(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; PREPARED_TABLE_EC_ROW_RELATION_ARITY] {
    core::array::from_fn(|index| {
        let column = match index {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 17,
            4 => 18,
            5..=127 => 19 + (index - 5),
            _ => unreachable!("prepared-table EC packed relation index is in range"),
        };
        base[column].data[vec_row]
    })
}


fn prepared_table_projective_source_packed_relation_values(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; PREPARED_TABLE_EC_ROW_RELATION_ARITY] {
    core::array::from_fn(|index| {
        let column = match index {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 4,
            4 => 5,
            5..=127 => 6 + (index - 5),
            _ => unreachable!("prepared-table projective source relation index is in range"),
        };
        base[column].data[vec_row]
    })
}

