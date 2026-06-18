//! Interaction-trace (LogUp) generation for the prepared-table family: the
//! interaction claim types, the per-row / pinned / projective-source
//! generators, and the packed/unpacked relation-tuple builders.
//!
//! Split out of `mod.rs` (pure relocation, no behavioral change).

use serde::{Deserialize, Serialize};
use stwo::core::{channel::Channel, fields::m31::M31, fields::qm31::SecureField, ColumnVec};
use stwo::prover::backend::simd::{
    m31::{PackedM31, LOG_N_LANES, N_LANES},
    qm31::PackedQM31,
};
use stwo_constraint_framework::{LogupTraceGenerator, Relation};
use stwo_p256_utils::constants::N_LIMBS;

use crate::components::gamma_digest::{
    gamma_collect_group_values, gamma_digest_of_values, gamma_digest_tuple, gamma_digest_yield_sum,
    gamma_row_index_of, GammaChallenge, GammaDigestRelation, GammaTallInstance,
    GammaTallInteractionClaim, GammaTallLayout, GAMMA_TAG_PREPARED_RANGE13,
    GAMMA_TAG_PREPARED_SIGNED,
};
use crate::components::ComponentInteractionClaim;
use crate::constants::{P256_3GX, P256_3GY};
use crate::limbs::P256M31BigInt;
use crate::projective_air::{
    ProjectiveRcbMulResultRelation, PROJECTIVE_RCB_MUL_ROLE_LHS, PROJECTIVE_RCB_MUL_ROLE_RESULT,
    PROJECTIVE_RCB_MUL_ROLE_RHS, PROJECTIVE_RCB_OP_MUL_LIMB_COLUMNS,
};
use crate::range_checks::RangeCheckInteractionClaim;
use crate::types::U256;

use crate::scalar::scalar_mod_mul::columns::M31ColumnEval;

use super::super::ec_source::double_formula::DOUBLE_TOTAL_REDUCTIONS;
use super::super::ec_source::mixed_add_formula::MIXED_ADD_TOTAL_REDUCTIONS;
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

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PreparedTableProjectiveSourceInteractionClaim {
    pub provider: ComponentInteractionClaim,
    pub consumer: ComponentInteractionClaim,
    /// γ-digest: the range13-kind tall expander (digest use + range uses).
    pub gamma_range13: GammaTallInteractionClaim,
    /// γ-digest: the signed-kind tall expander.
    pub gamma_signed: GammaTallInteractionClaim,
    /// C5-2: the self-contained Range13 PROVIDER (yield) sum.
    pub range13: RangeCheckInteractionClaim,
    /// C5-2: the self-contained signed-carry PROVIDER (yield) sum.
    pub signed_carry: RangeCheckInteractionClaim,
}

impl PreparedTableProjectiveSourceInteractionClaim {
    pub fn zero() -> Self {
        Self {
            provider: ComponentInteractionClaim::zero(),
            consumer: ComponentInteractionClaim::zero(),
            gamma_range13: GammaTallInteractionClaim::zero(),
            gamma_signed: GammaTallInteractionClaim::zero(),
            range13: RangeCheckInteractionClaim {
                claimed_sum: secure_zero(),
            },
            signed_carry: RangeCheckInteractionClaim {
                claimed_sum: secure_zero(),
            },
        }
    }

    /// `PreparedTableProjectiveSource` balance term: provider + EC-row consume.
    /// EXCLUDES the mul-result consume (balanced under `ProjectiveRcbMulResult`)
    /// and the range13/signed-carry consume+provide (balanced under their own
    /// `PreparedTableProjective{Range13,SignedCarry}` relations).
    pub fn total(&self) -> SecureField {
        self.provider.claimed_sum + self.consumer.claimed_sum
    }

    pub(crate) fn component_claimed_sum(&self) -> SecureField {
        self.provider.claimed_sum
            + self.consumer.claimed_sum
            + self.gamma_range13.claimed_sum
            + self.gamma_signed.claimed_sum
            + self.range13.claimed_sum
            + self.signed_carry.claimed_sum
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.provider.mix_into(channel);
        self.consumer.mix_into(channel);
        self.range13.mix_into(channel);
        self.signed_carry.mix_into(channel);
        self.gamma_range13.mix_into(channel);
        self.gamma_signed.mix_into(channel);
    }
}

/// Unpinned provider trace (test-only; the monolith uses the pinned gen).
#[cfg(test)]
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

const PREPARED_TABLE_EC_COL_RHS: usize =
    PREPARED_TABLE_EC_COL_LHS + PREPARED_TABLE_EC_POINT_COLUMNS;

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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PreparedTableEcRowPinnedInteractionClaim {
    pub claimed_sum: SecureField,
    pub final_check_hint: ComponentInteractionClaim,
}

impl PreparedTableEcRowPinnedInteractionClaim {
    pub fn zero() -> Self {
        Self {
            claimed_sum: secure_zero(),
            final_check_hint: ComponentInteractionClaim::zero(),
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
) -> (
    ColumnVec<M31ColumnEval>,
    PreparedTableEcRowPinnedInteractionClaim,
) {
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
            let magnitude =
                PackedM31::broadcast(M31::from_u32_unchecked(entry.mult.unsigned_abs()));
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
                        Some(offset) => canonical_packed_tuple_from_columns(
                            base, vec_row, sig, cert, role, offset,
                        ),
                        None => {
                            canonical_packed_tuple_const(sig, cert, role, &three_g_x, &three_g_y)
                        }
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
            let double_r = base[PREPARED_TABLE_EC_COL_KIND_FLAGS + PREPARED_TABLE_EC_KIND_DOUBLE_R]
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

    let (trace, claimed_sum) = logup.finalize_last();

    let mut final_check_hint_claimed_sum = secure_zero();
    for row in prepared_table_ec_storage_rows(base) {
        let active = row[0];
        if active == M31::from_u32_unchecked(0) {
            continue;
        }
        let sig = row[PREPARED_TABLE_EC_COL_SIG_ID];
        let cert = row[PREPARED_TABLE_EC_COL_CERT_ID];
        if let Some(final_check_hint) = final_check_hint {
            let double_r = row[PREPARED_TABLE_EC_COL_KIND_FLAGS + PREPARED_TABLE_EC_KIND_DOUBLE_R];
            if double_r != M31::from_u32_unchecked(0) {
                let denom: SecureField = final_check_hint.combine(
                    &final_check_hint_unpacked_tuple(&row, sig, cert, PREPARED_TABLE_EC_COL_LHS),
                );
                final_check_hint_claimed_sum += -SecureField::from(active * double_r) / denom;
            }
        }
    }

    (
        trace,
        PreparedTableEcRowPinnedInteractionClaim {
            claimed_sum,
            final_check_hint: ComponentInteractionClaim {
                claimed_sum: final_check_hint_claimed_sum,
            },
        },
    )
}

#[cfg(test)]
pub(crate) fn debug_prepared_table_pinned_relation_sums(
    base: &[M31ColumnEval],
    relation: &PreparedTableEcRowRelation,
    cert_base: &CertBaseRelation,
    canonical: &PreparedTableCanonicalRelation,
) -> (SecureField, SecureField, SecureField) {
    let three_g_x = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_3GX));
    let three_g_y = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_3GY));
    let mut prepared_table_sum = secure_zero();
    let mut cert_base_sum = secure_zero();
    let mut canonical_sum = secure_zero();
    for row in prepared_table_ec_storage_rows(base) {
        let active = row[0];
        if active == M31::from_u32_unchecked(0) {
            continue;
        }
        let sig = row[PREPARED_TABLE_EC_COL_SIG_ID];
        let cert = row[PREPARED_TABLE_EC_COL_CERT_ID];
        let values = prepared_table_ec_row_unpacked_relation_values(&row);
        let denom: SecureField = relation.combine(&values);
        prepared_table_sum += -SecureField::from(active) / denom;
        for entry in PIN_SCHEDULE {
            let mut gate = M31::from_u32_unchecked(1);
            for &kind in entry.kinds {
                gate *= row[PREPARED_TABLE_EC_COL_KIND_FLAGS + kind];
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
                    cert_base_sum += numerator / denom;
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
                    canonical_sum += numerator / denom;
                }
            }
        }
    }
    (prepared_table_sum, cert_base_sum, canonical_sum)
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

#[cfg(test)]
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

#[cfg(test)]
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

#[cfg(test)]
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

#[cfg(test)]
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

// C5 plumbing: interaction trace for the prepared-table projective-source
// CONSUMER. Emits, in the order `PreparedTableProjectiveSourceEval::evaluate`
// does under one `finalize_logup`: the `PreparedTableEcRowRelation` consume
// (col 0, `+active`), then one `ProjectiveRcbMulResultRelation` consume column
// per committed mul limb (canonical mul/role/limb order, `+active`). Returns
// the columns, the EC-row consumer sum, and the mul-result consumer sum.
//
// LogUp batch size for the prepared-table projective-source consumer: 2
// fractions per interaction column (degree <= 3 at the `log_size + 1` bound;
// bounds past +1 empirically fail OODS in this stwo).
pub(crate) const PREPARED_CONSUMER_LOGUP_BATCH: usize = 2;

/// Total LogUp entries the consumer eval emits (EC-row consume + wide mul
/// consumes + the two γ-digest yields), in emission order.
pub(crate) fn prepared_consumer_logup_entries() -> usize {
    1 + (PROJECTIVE_RCB_OP_MUL_LIMB_COLUMNS / (3 * N_LIMBS)) * 3 + 2
}

/// Consumer logup batching: pairs, except the operand-dedup slots whose
/// consume values are degree-2 op-mixes (solo batches; see the fake-GLV twin).
pub(crate) fn prepared_consumer_logup_batching() -> Vec<usize> {
    let solo: Vec<usize> = (0..PROJECTIVE_RCB_OP_MUL_LIMB_COLUMNS / (3 * N_LIMBS))
        .flat_map(|mul| (0..3usize).map(move |role| (mul, role)))
        .filter(|&(mul, role)| crate::projective_air::consumed_mul_slot_degree2(mul, role))
        .map(|(mul, role)| 1 + mul * 3 + role)
        .collect();
    crate::range_checks::batching_with_solo(
        prepared_consumer_logup_entries(),
        PREPARED_CONSUMER_LOGUP_BATCH,
        &solo,
    )
}

/// Gen-side layout for `consumed_mul_slot_packed_limbs` over the prepared
/// consumer base trace (6 metadata columns — `table_index` follows `op`).
fn prepared_consumed_mul_gen_layout() -> crate::projective_air::ConsumedMulGenLayout {
    crate::projective_air::ConsumedMulGenLayout {
        op_col: 4,
        x1_col: 6,
        y1_col: 6 + N_LIMBS,
        x2_col: 6 + PREPARED_TABLE_EC_POINT_COLUMNS,
        y2_col: 6 + PREPARED_TABLE_EC_POINT_COLUMNS + N_LIMBS,
        output_x_col: 6 + 2 * PREPARED_TABLE_EC_POINT_COLUMNS,
        output_y_col: 6 + 2 * PREPARED_TABLE_EC_POINT_COLUMNS + N_LIMBS,
        z3_double_col: PREPARED_TABLE_PROJECTIVE_SOURCE_DOUBLE_FORMULA_OFFSET + 2 * N_LIMBS,
        z3_mixed_col: PREPARED_TABLE_PROJECTIVE_SOURCE_MIXED_ADD_FORMULA_OFFSET + 2 * N_LIMBS,
        mul_limb_offset: PREPARED_TABLE_PROJECTIVE_SOURCE_MUL_LIMB_OFFSET,
    }
}

/// Range13 digest value order: the Double-formula list then the MixedAdd list.
pub(crate) fn prepared_gamma_range13_columns() -> Vec<usize> {
    let mut columns = prepared_double_formula_range13_use_columns();
    columns.extend(prepared_mixed_add_formula_range13_use_columns());
    columns
}

/// Signed-carry digest value order: Double then MixedAdd reduction carries.
pub(crate) fn prepared_gamma_signed_carry_columns() -> Vec<usize> {
    let mut columns = prepared_double_formula_signed_carry_use_columns();
    columns.extend(prepared_mixed_add_formula_signed_carry_use_columns());
    columns
}

/// The two γ-digest tall layouts for `rows` scheduled prepared-table rows.
pub fn prepared_gamma_layouts(rows: usize) -> [GammaTallLayout; 2] {
    [
        GammaTallLayout {
            tag: GAMMA_TAG_PREPARED_RANGE13,
            group_count: rows,
            values_per_group: prepared_gamma_range13_columns().len(),
        },
        GammaTallLayout {
            tag: GAMMA_TAG_PREPARED_SIGNED,
            group_count: rows,
            values_per_group: prepared_gamma_signed_carry_columns().len(),
        },
    ]
}

/// Build the two γ-digest tall instances from the consumer base trace.
pub(crate) fn prepared_gamma_instances(base: &[M31ColumnEval]) -> [GammaTallInstance; 2] {
    let r13_columns = prepared_gamma_range13_columns();
    let signed_columns = prepared_gamma_signed_carry_columns();
    let r13_groups = gamma_collect_group_values(base, &r13_columns);
    let signed_groups = gamma_collect_group_values(base, &signed_columns);
    [
        GammaTallInstance::new(
            GAMMA_TAG_PREPARED_RANGE13,
            r13_columns.len(),
            M31::from_u32_unchecked(0),
            r13_groups,
        ),
        GammaTallInstance::new(
            GAMMA_TAG_PREPARED_SIGNED,
            signed_columns.len(),
            crate::range_checks::encode_signed_carry(0),
            signed_groups,
        ),
    ]
}

pub(crate) fn gen_prepared_table_projective_source_consumer_interaction_trace(
    base: &[M31ColumnEval],
    ec_row_relation: &PreparedTableEcRowRelation,
    mul_result_relation: &ProjectiveRcbMulResultRelation,
    gamma_digest_relation: &GammaDigestRelation,
    gamma_challenge: &GammaChallenge,
) -> PreparedTableProjectiveSourceConsumerInteraction {
    assert_eq!(base.len(), PREPARED_TABLE_PROJECTIVE_SOURCE_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let vec_rows = 1usize << (log_size - LOG_N_LANES);
    // Collect every fraction in the consumer AIR's emission order, then write
    // them `PREPARED_CONSUMER_LOGUP_BATCH` per interaction column to mirror
    // the eval's `finalize_logup_batched(consecutive_batching(..))` layout.
    let mut entries: Vec<(Vec<PackedQM31>, Vec<PackedQM31>)> = Vec::new();
    let active_numerators: Vec<PackedQM31> = (0..vec_rows)
        .map(|vec_row| PackedQM31::from(base[0].data[vec_row]))
        .collect();

    // Entry 0: the EC-row consume (+active).
    entries.push((
        active_numerators.clone(),
        (0..vec_rows)
            .map(|vec_row| {
                let values = prepared_table_projective_source_packed_relation_values(base, vec_row);
                ec_row_relation.combine(&values)
            })
            .collect(),
    ));

    // Wide mul-result consumes (+has_muls), canonical order.
    let has_muls_numerators: Vec<PackedQM31> = (0..vec_rows)
        .map(|vec_row| {
            PackedQM31::from(base[PREPARED_TABLE_PROJECTIVE_SOURCE_HAS_MULS_COL].data[vec_row])
        })
        .collect();
    let layout = prepared_consumed_mul_gen_layout();
    for mul_index in 0..(PROJECTIVE_RCB_OP_MUL_LIMB_COLUMNS / (3 * N_LIMBS)) {
        for (role_index, &role) in PROJECTIVE_RCB_MUL_RESULT_ROLES.iter().enumerate() {
            entries.push((
                has_muls_numerators.clone(),
                (0..vec_rows)
                    .map(|vec_row| {
                        let mut values = Vec::with_capacity(3 + N_LIMBS);
                        values.push(base[1].data[vec_row]);
                        values.push(PackedM31::broadcast(M31::from_u32_unchecked(
                            mul_index as u32,
                        )));
                        values.push(PackedM31::broadcast(M31::from_u32_unchecked(role)));
                        values.extend(crate::projective_air::consumed_mul_slot_packed_limbs(
                            base, vec_row, &layout, mul_index, role_index,
                        ));
                        mul_result_relation.combine(&values)
                    })
                    .collect(),
            ));
        }
    }
    // γ-digest yields (−active), in eval order: range13 kind then signed
    // kind, mirroring the eval's digest computation per row.
    let instances = prepared_gamma_instances(base);
    for instance in &instances {
        let columns = match instance.layout.tag {
            GAMMA_TAG_PREPARED_RANGE13 => prepared_gamma_range13_columns(),
            _ => prepared_gamma_signed_carry_columns(),
        };
        let mut numerators = Vec::with_capacity(vec_rows);
        let mut denominators = Vec::with_capacity(vec_rows);
        for vec_row in 0..vec_rows {
            let mut numerator = [secure_zero(); N_LANES];
            let mut denominator = [SecureField::from(M31::from_u32_unchecked(1)); N_LANES];
            for lane in 0..N_LANES {
                let active = base[0].data[vec_row].to_array()[lane];
                let row_index = gamma_row_index_of(vec_row, lane, log_size);
                let values: Vec<M31> = columns
                    .iter()
                    .map(|&col| base[col].data[vec_row].to_array()[lane])
                    .collect();
                let digest = gamma_digest_of_values(gamma_challenge, instance.pad_value, &values);
                let tuple = gamma_digest_tuple(
                    instance.layout.tag,
                    M31::from_u32_unchecked(row_index),
                    digest,
                );
                numerator[lane] = -SecureField::from(active);
                denominator[lane] = gamma_digest_relation.combine(&tuple);
            }
            numerators.push(PackedQM31::from_array(numerator));
            denominators.push(PackedQM31::from_array(denominator));
        }
        entries.push((numerators, denominators));
    }

    assert_eq!(entries.len(), prepared_consumer_logup_entries());
    let mut logup = LogupTraceGenerator::new(log_size);
    crate::range_checks::write_logup_columns_with_batching(
        &mut logup,
        &entries,
        &prepared_consumer_logup_batching(),
    );
    let (columns, _total) = logup.finalize_last();

    let (ec_row_sum, mul_result_sum) =
        prepared_table_projective_source_consumer_sums(base, ec_row_relation, mul_result_relation);
    let gamma_yield_sum = instances
        .iter()
        .map(|instance| gamma_digest_yield_sum(instance, gamma_challenge, gamma_digest_relation))
        .sum();
    PreparedTableProjectiveSourceConsumerInteraction {
        columns,
        ec_row_sum,
        mul_result_sum,
        gamma_yield_sum,
    }
}

/// Output of the prepared-table projective-source consumer interaction-trace
/// generator: the interaction columns and the per-relation analytic use sums.
pub(crate) struct PreparedTableProjectiveSourceConsumerInteraction {
    pub columns: ColumnVec<M31ColumnEval>,
    pub ec_row_sum: SecureField,
    pub mul_result_sum: SecureField,
    /// Σ of the two γ-digest yields (−active).
    pub gamma_yield_sum: SecureField,
}

/// Base-trace column indices the Range13 USES read, in `bind_double_formula`
/// emission order: lhs.x, lhs.y, output.x, output.y limbs, then x3, y3, z3.
/// (The prepared-table source has 6 metadata columns — `table_index` follows
/// `op` — so points start at column 6, one later than the fake-GLV source.)
fn prepared_double_formula_range13_use_columns() -> Vec<usize> {
    let lhs_x = 6; // after [active, source_index, sig_id, cert_id, op, table_index]
    let lhs_y = lhs_x + N_LIMBS;
    let output_x = 6 + 2 * PREPARED_TABLE_EC_POINT_COLUMNS;
    let output_y = output_x + N_LIMBS;
    let x3 = PREPARED_TABLE_PROJECTIVE_SOURCE_DOUBLE_FORMULA_OFFSET;
    let mut cols = Vec::with_capacity(7 * N_LIMBS);
    for start in [
        lhs_x,
        lhs_y,
        output_x,
        output_y,
        x3,
        x3 + N_LIMBS,
        x3 + 2 * N_LIMBS,
    ] {
        for limb in 0..N_LIMBS {
            cols.push(start + limb);
        }
    }
    cols
}

/// Base-trace column indices the signed-carry USES read, in consumer-AIR
/// emission order (reduction slot outer, carry limb inner). The Double-formula
/// block layout is `x3,y3,z3` (3·N_LIMBS) then per reduction `(q, carries)`.
fn prepared_double_formula_signed_carry_use_columns() -> Vec<usize> {
    let block = PREPARED_TABLE_PROJECTIVE_SOURCE_DOUBLE_FORMULA_OFFSET;
    let reductions_start = block + 3 * N_LIMBS;
    let mut cols = Vec::with_capacity(DOUBLE_TOTAL_REDUCTIONS * N_LIMBS);
    for slot in 0..DOUBLE_TOTAL_REDUCTIONS {
        let q_col = reductions_start + slot * (1 + N_LIMBS);
        for limb in 0..N_LIMBS {
            cols.push(q_col + 1 + limb); // skip the quotient column
        }
    }
    cols
}

/// Base-trace column indices the Range13 USES read for the MixedAdd formula, in
/// `bind_mixed_add_formula` emission order: lhs.x, lhs.y, rhs.x, rhs.y,
/// output.x, output.y limbs, then x3, y3, z3 working-value limbs.
fn prepared_mixed_add_formula_range13_use_columns() -> Vec<usize> {
    let lhs_x = 6; // after [active, source_index, sig_id, cert_id, op, table_index]
    let lhs_y = lhs_x + N_LIMBS;
    let rhs_x = 6 + PREPARED_TABLE_EC_POINT_COLUMNS;
    let rhs_y = rhs_x + N_LIMBS;
    let output_x = 6 + 2 * PREPARED_TABLE_EC_POINT_COLUMNS;
    let output_y = output_x + N_LIMBS;
    let x3 = PREPARED_TABLE_PROJECTIVE_SOURCE_MIXED_ADD_FORMULA_OFFSET;
    let mut cols = Vec::with_capacity(9 * N_LIMBS);
    for start in [
        lhs_x,
        lhs_y,
        rhs_x,
        rhs_y,
        output_x,
        output_y,
        x3,
        x3 + N_LIMBS,
        x3 + 2 * N_LIMBS,
    ] {
        for limb in 0..N_LIMBS {
            cols.push(start + limb);
        }
    }
    cols
}

/// Base-trace column indices the signed-carry USES read for the MixedAdd
/// formula, in consumer-AIR emission order (reduction slot outer, carry limb
/// inner).
fn prepared_mixed_add_formula_signed_carry_use_columns() -> Vec<usize> {
    let block = PREPARED_TABLE_PROJECTIVE_SOURCE_MIXED_ADD_FORMULA_OFFSET;
    let reductions_start = block + 3 * N_LIMBS;
    let mut cols = Vec::with_capacity(MIXED_ADD_TOTAL_REDUCTIONS * N_LIMBS);
    for slot in 0..MIXED_ADD_TOTAL_REDUCTIONS {
        let q_col = reductions_start + slot * (1 + N_LIMBS);
        for limb in 0..N_LIMBS {
            cols.push(q_col + 1 + limb); // skip the quotient column
        }
    }
    cols
}

/// Range13 USE values consumed by the γ-digest tall expander (per scheduled
/// row: the digest-ordered list, lane-padded with zeros). The tall instance is
/// the single source of truth for the provider multiplicity.
pub(crate) fn prepared_table_projective_source_range13_uses_from_base(
    base: &[M31ColumnEval],
) -> Vec<M31> {
    let [r13, _] = prepared_gamma_instances(base);
    r13.all_scheduled_values()
}

/// signed-carry USE values (decoded `i64`) consumed by the γ-digest tall
/// expander (lane-padded with `encode_signed_carry(0)`).
pub(crate) fn prepared_table_projective_source_signed_carry_uses_from_base(
    base: &[M31ColumnEval],
) -> Vec<i64> {
    let [_, signed] = prepared_gamma_instances(base);
    signed
        .all_scheduled_values()
        .into_iter()
        .map(crate::range_checks::decode_signed_carry)
        .collect()
}

/// Analytic `(ec_row_consumer_sum, mul_result_consumer_sum)` over the consumer
/// base trace's active rows, using unpacked `SecureField` combines.
fn prepared_table_projective_source_consumer_sums(
    base: &[M31ColumnEval],
    ec_row_relation: &PreparedTableEcRowRelation,
    mul_result_relation: &ProjectiveRcbMulResultRelation,
) -> (SecureField, SecureField) {
    let log_size = base[0].domain.log_size();
    let mut ec_row_denominators = Vec::new();
    let mut mul_result_denominators = Vec::new();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        for lane in 0..(1 << LOG_N_LANES) {
            let active = base[0].data[vec_row].to_array()[lane];
            if active != M31::from_u32_unchecked(0) {
                let ec_values =
                    prepared_table_projective_source_unpacked_relation_values(base, vec_row, lane);
                ec_row_denominators.push(ec_row_relation.combine(&ec_values));
            }

            let has_muls =
                base[PREPARED_TABLE_PROJECTIVE_SOURCE_HAS_MULS_COL].data[vec_row].to_array()[lane];
            if has_muls == M31::from_u32_unchecked(0) {
                continue;
            }
            let source_index = base[1].data[vec_row].to_array()[lane];
            let layout = prepared_consumed_mul_gen_layout();
            for mul_index in 0..(PROJECTIVE_RCB_OP_MUL_LIMB_COLUMNS / (3 * N_LIMBS)) {
                for (role_index, &role) in PROJECTIVE_RCB_MUL_RESULT_ROLES.iter().enumerate() {
                    let limbs = crate::projective_air::consumed_mul_slot_packed_limbs(
                        base, vec_row, &layout, mul_index, role_index,
                    );
                    let mut values = Vec::with_capacity(3 + N_LIMBS);
                    values.push(source_index);
                    values.push(M31::from_u32_unchecked(mul_index as u32));
                    values.push(M31::from_u32_unchecked(role));
                    values.extend(limbs.iter().map(|packed| packed.to_array()[lane]));
                    mul_result_denominators.push(mul_result_relation.combine(&values));
                }
            }
        }
    }
    (
        crate::range_checks::batched_inverse_sum(&ec_row_denominators),
        crate::range_checks::batched_inverse_sum(&mul_result_denominators),
    )
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
