//! Interaction-trace (LogUp) generation for the prepared-table family: the
//! interaction claim types, the per-row / pinned / projective-source
//! generators, and the packed/unpacked relation-tuple builders.
//!
//! Split out of `mod.rs` (pure relocation, no behavioral change).

use serde::{Deserialize, Serialize};
use stwo::core::{channel::Channel, fields::m31::M31, fields::qm31::SecureField, ColumnVec};
use stwo::prover::backend::simd::{
    m31::{PackedM31, LOG_N_LANES},
    qm31::PackedQM31,
};
use stwo_constraint_framework::{LogupTraceGenerator, Relation};
use stwo_p256_utils::constants::N_LIMBS;

use crate::components::ComponentInteractionClaim;
use crate::constants::{P256_3GX, P256_3GY};
use crate::limbs::P256M31BigInt;
use crate::projective_air::{
    ProjectiveRcbMulResultRelation, PROJECTIVE_RCB_MUL_ROLE_LHS, PROJECTIVE_RCB_MUL_ROLE_RHS,
};
use crate::range_checks::write_batched_logup_columns;
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

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PreparedTableProjectiveSourceInteractionClaim {
    pub provider: ComponentInteractionClaim,
    pub consumer: ComponentInteractionClaim,
}

impl PreparedTableProjectiveSourceInteractionClaim {
    pub fn zero() -> Self {
        Self {
            provider: ComponentInteractionClaim::zero(),
            consumer: ComponentInteractionClaim::zero(),
        }
    }

    /// `PreparedTableProjectiveSource` balance term: provider + EC-row consume.
    /// EXCLUDES the mul-result consume (balanced under `ProjectiveRcbMulResult`)
    /// and the header yield (balanced under `EcOpHeader`).
    pub fn total(&self) -> SecureField {
        self.provider.claimed_sum + self.consumer.claimed_sum
    }

    pub(crate) fn component_claimed_sum(&self) -> SecureField {
        self.provider.claimed_sum + self.consumer.claimed_sum
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.provider.mix_into(channel);
        self.consumer.mix_into(channel);
    }
}

/// Unpinned provider trace (test-only, the monolith uses the pinned gen).
#[cfg(test)]
pub(crate) fn gen_prepared_table_ec_row_interaction_trace(
    base: &[M31ColumnEval],
    relation: &PreparedTableEcRowRelation,
) -> (ColumnVec<M31ColumnEval>, PreparedTableEcRowInteractionClaim) {
    assert_eq!(base.len(), PREPARED_TABLE_EC_ROW_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    logup.col_from_fn(|vec_row| {
        let values = prepared_table_ec_row_packed_relation_values(base, vec_row);
        let numerator = -PackedQM31::from(base[0].data[vec_row]);
        let denominator: PackedQM31 = relation.combine(&values);
        (numerator, denominator)
    });
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

/// Builds the interaction trace for the monolithic EC-row provider.
///
/// The trace starts with the base relation and 30 pinning fractions.
/// Their order matches `PreparedTableEcRowEval::evaluate`.
/// An optional final-check hint adds one `R_i` fraction.
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
    let mut entries = Vec::new();

    // Entry 0: the existing PreparedTableEcRowRelation yield (-active).
    append_packed_entry(&mut entries, n_vec_rows, |vec_row| {
        let values = prepared_table_ec_row_packed_relation_values(base, vec_row);
        (
            -PackedQM31::from(base[0].data[vec_row]),
            relation.combine(&values),
        )
    });

    let three_g_x = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_3GX));
    let three_g_y = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_3GY));

    // Entries 1..=30: the pinning schedule, one fraction per entry.
    for entry in PIN_SCHEDULE {
        append_packed_entry(&mut entries, n_vec_rows, |vec_row| {
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
            (numerator, denominator)
        });
    }

    // Optional FinalCheckHint entry: yield `R_i` (= `lhs`) gated `active *
    // DoubleR_flag`, multiplicity `-2` (final-add + curve membership). Emitted
    // if and only if a relation exists, in step with the AIR
    // `if let Some(final_check_hint)` emission.
    if let Some(final_check_hint) = final_check_hint {
        append_packed_entry(&mut entries, n_vec_rows, |vec_row| {
            let sig = base[PREPARED_TABLE_EC_COL_SIG_ID].data[vec_row];
            let cert = base[PREPARED_TABLE_EC_COL_CERT_ID].data[vec_row];
            let active = base[0].data[vec_row];
            let double_r = base[PREPARED_TABLE_EC_COL_KIND_FLAGS + PREPARED_TABLE_EC_KIND_DOUBLE_R]
                .data[vec_row];
            let gate = active * double_r;
            let numerator = -PackedQM31::from(gate)
                * PackedQM31::broadcast(SecureField::from(M31::from_u32_unchecked(2)));
            let denominator = final_check_hint.combine(&final_check_hint_packed_tuple(
                base,
                vec_row,
                sig,
                cert,
                PREPARED_TABLE_EC_COL_LHS,
            ));
            (numerator, denominator)
        });
    }

    let mut logup = LogupTraceGenerator::new(log_size);
    write_batched_logup_columns(&mut logup, &entries, 2);
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
                final_check_hint_claimed_sum += -SecureField::from(active * double_r)
                    * SecureField::from(M31::from_u32_unchecked(2))
                    / denom;
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

type LogupEntry = (Vec<PackedQM31>, Vec<PackedQM31>);

fn append_packed_entry(
    entries: &mut Vec<LogupEntry>,
    vec_rows: usize,
    fraction: impl Fn(usize) -> (PackedQM31, PackedQM31),
) {
    let mut numerators = Vec::with_capacity(vec_rows);
    let mut denominators = Vec::with_capacity(vec_rows);
    for vec_row in 0..vec_rows {
        let (numerator, denominator) = fraction(vec_row);
        numerators.push(numerator);
        denominators.push(denominator);
    }
    entries.push((numerators, denominators));
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

// Interaction trace for the narrow prepared-table projective-source consumer.
// It emits entries in evaluator order under one
// `finalize_logup_batched`:
//   0. the `PreparedTableEcRowRelation` consume (+active),
//   1..=6. the 6 narrow `ProjectiveRcbMulResultRelation` consumes (+gate),
//   7. the `EcOpHeaderRelation` yield (−gate),
// where `gate = active − (1−op)·rhs.inf` (the group-existence gate, ≡ the old
// `has_muls`).
//
// LogUp batch size: 1 fraction per interaction column. The op-mux consume
// entries (M0.rhs at index 2, M1.rhs at index 4) have degree-2 tuple values.
// Pairing them with a neighbor pushes the logup constraint past degree 3,
// which overflows the `log_size + 1` bound. `finalize_logup_batched` only
// supports a uniform batch size, so everything goes solo.
pub(crate) const PREPARED_CONSUMER_LOGUP_BATCH: usize = 1;

/// Total LogUp entries the consumer eval emits (EC-row consume + 6 narrow mul
/// consumes + the EC-op header yield), in emission order.
pub(crate) fn prepared_consumer_logup_entries() -> usize {
    1 + NARROW_MUL_CONSUME_SLOTS.len() + 1
}

/// Gen-side point column offsets for the narrow mul consumes.
pub(crate) struct NarrowMulConsumeColumns {
    pub source: usize,
    pub op: usize,
    pub lhs_x: usize,
    pub lhs_y: usize,
    pub rhs_x: usize,
    pub rhs_y: usize,
    pub rhs_inf: usize,
    pub out_x: usize,
    pub out_y: usize,
}

/// The 6 narrow consume slots in eval emission order:
/// `(mul_index, role, own column, Some(mix column) for op-mux slots)`.
pub(crate) const NARROW_MUL_CONSUME_SLOTS: [(u32, u32, NarrowSlotSide); 6] = [
    (0, PROJECTIVE_RCB_MUL_ROLE_LHS, NarrowSlotSide::LhsX),
    (0, PROJECTIVE_RCB_MUL_ROLE_RHS, NarrowSlotSide::MixX),
    (1, PROJECTIVE_RCB_MUL_ROLE_LHS, NarrowSlotSide::LhsY),
    (1, PROJECTIVE_RCB_MUL_ROLE_RHS, NarrowSlotSide::MixY),
    (13, PROJECTIVE_RCB_MUL_ROLE_LHS, NarrowSlotSide::OutX),
    (14, PROJECTIVE_RCB_MUL_ROLE_LHS, NarrowSlotSide::OutY),
];

#[derive(Clone, Copy)]
pub(crate) enum NarrowSlotSide {
    LhsX,
    MixX,
    LhsY,
    MixY,
    OutX,
    OutY,
}

impl NarrowSlotSide {
    /// `(own column, Some(mix column))`: the slot value is `own` for plain
    /// slots and `op·own + (1−op)·mix` for the op-mux slots.
    fn columns(self, cols: &NarrowMulConsumeColumns) -> (usize, Option<usize>) {
        match self {
            NarrowSlotSide::LhsX => (cols.lhs_x, None),
            NarrowSlotSide::MixX => (cols.lhs_x, Some(cols.rhs_x)),
            NarrowSlotSide::LhsY => (cols.lhs_y, None),
            NarrowSlotSide::MixY => (cols.lhs_y, Some(cols.rhs_y)),
            NarrowSlotSide::OutX => (cols.out_x, None),
            NarrowSlotSide::OutY => (cols.out_y, None),
        }
    }
}

/// Group-existence gate lanes: `active − (1−op)·rhs.inf` per packed row.
pub(crate) fn narrow_mul_gate_lanes(
    base: &[M31ColumnEval],
    cols: &NarrowMulConsumeColumns,
    vec_rows: usize,
) -> Vec<PackedM31> {
    let one = PackedM31::broadcast(M31::from_u32_unchecked(1));
    (0..vec_rows)
        .map(|vec_row| {
            base[0].data[vec_row]
                - (one - base[cols.op].data[vec_row]) * base[cols.rhs_inf].data[vec_row]
        })
        .collect()
}

/// Append the 6 narrow mul-result consume entries (numerator `+gate`) in eval
/// emission order.
pub(crate) fn push_narrow_mul_consume_entries(
    entries: &mut Vec<(Vec<PackedQM31>, Vec<PackedQM31>)>,
    base: &[M31ColumnEval],
    cols: &NarrowMulConsumeColumns,
    gate: &[PackedM31],
    relation: &ProjectiveRcbMulResultRelation,
    vec_rows: usize,
) {
    let one = PackedM31::broadcast(M31::from_u32_unchecked(1));
    for (mul, role, side) in NARROW_MUL_CONSUME_SLOTS {
        let (own_col, mix_col) = side.columns(cols);
        entries.push((
            gate.iter().map(|&lanes| PackedQM31::from(lanes)).collect(),
            (0..vec_rows)
                .map(|vec_row| {
                    let op = base[cols.op].data[vec_row];
                    let mut values = Vec::with_capacity(3 + N_LIMBS);
                    values.push(base[cols.source].data[vec_row]);
                    values.push(PackedM31::broadcast(M31::from_u32_unchecked(mul)));
                    values.push(PackedM31::broadcast(M31::from_u32_unchecked(role)));
                    for limb in 0..N_LIMBS {
                        let own = base[own_col + limb].data[vec_row];
                        values.push(match mix_col {
                            Some(mix_col) => {
                                op * own + (one - op) * base[mix_col + limb].data[vec_row]
                            }
                            None => own,
                        });
                    }
                    relation.combine(&values)
                })
                .collect(),
        ));
    }
}

/// Analytic narrow mul-result consume sum (`Σ gate/denom` over the 6 slots of
/// every gated row). `gate` is boolean on honest traces, so rows are skipped
/// when it is zero.
pub(crate) fn narrow_mul_consume_sum(
    base: &[M31ColumnEval],
    cols: &NarrowMulConsumeColumns,
    relation: &ProjectiveRcbMulResultRelation,
) -> SecureField {
    let log_size = base[0].domain.log_size();
    let one = M31::from_u32_unchecked(1);
    let mut denominators = Vec::new();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        for lane in 0..(1 << LOG_N_LANES) {
            let cell = |col: usize| base[col].data[vec_row].to_array()[lane];
            let op = cell(cols.op);
            let gate = cell(0) - (one - op) * cell(cols.rhs_inf);
            if gate == M31::from_u32_unchecked(0) {
                continue;
            }
            for (mul, role, side) in NARROW_MUL_CONSUME_SLOTS {
                let (own_col, mix_col) = side.columns(cols);
                let mut values = Vec::with_capacity(3 + N_LIMBS);
                values.push(cell(cols.source));
                values.push(M31::from_u32_unchecked(mul));
                values.push(M31::from_u32_unchecked(role));
                for limb in 0..N_LIMBS {
                    let own = cell(own_col + limb);
                    values.push(match mix_col {
                        Some(mix_col) => op * own + (one - op) * cell(mix_col + limb),
                        None => own,
                    });
                }
                denominators.push(relation.combine(&values));
            }
        }
    }
    crate::range_checks::batched_inverse_sum(&denominators)
}

/// The prepared-table consumer's narrow-consume column layout (6 metadata
/// columns — `table_index` follows `op`. Points start at column 6).
pub(crate) fn prepared_narrow_mul_columns() -> NarrowMulConsumeColumns {
    NarrowMulConsumeColumns {
        source: 1,
        op: 4,
        lhs_x: 6,
        lhs_y: 6 + N_LIMBS,
        rhs_x: 6 + PREPARED_TABLE_EC_POINT_COLUMNS,
        rhs_y: 6 + PREPARED_TABLE_EC_POINT_COLUMNS + N_LIMBS,
        rhs_inf: 6 + 2 * PREPARED_TABLE_EC_POINT_COLUMNS - 1,
        out_x: 6 + 2 * PREPARED_TABLE_EC_POINT_COLUMNS,
        out_y: 6 + 2 * PREPARED_TABLE_EC_POINT_COLUMNS + N_LIMBS,
    }
}

pub(crate) fn gen_prepared_table_projective_source_consumer_interaction_trace(
    base: &[M31ColumnEval],
    ec_row_relation: &PreparedTableEcRowRelation,
    mul_result_relation: &ProjectiveRcbMulResultRelation,
    header_relation: &crate::components::hinted_mul::EcOpHeaderRelation,
) -> PreparedTableProjectiveSourceConsumerInteraction {
    assert_eq!(base.len(), PREPARED_TABLE_PROJECTIVE_SOURCE_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let vec_rows = 1usize << (log_size - LOG_N_LANES);
    let cols = prepared_narrow_mul_columns();
    let gate = narrow_mul_gate_lanes(base, &cols, vec_rows);
    // Collect every fraction in the consumer AIR's emission order, then write
    // them with the eval's exact batching.
    let mut entries: Vec<(Vec<PackedQM31>, Vec<PackedQM31>)> = Vec::new();
    let active_numerators: Vec<PackedQM31> = (0..vec_rows)
        .map(|vec_row| PackedQM31::from(base[0].data[vec_row]))
        .collect();

    // Entry 0: the EC-row consume (+active).
    entries.push((
        active_numerators,
        (0..vec_rows)
            .map(|vec_row| {
                let values = prepared_table_projective_source_packed_relation_values(base, vec_row);
                ec_row_relation.combine(&values)
            })
            .collect(),
    ));

    // Entries 1..=6: the narrow mul-result consumes (+gate).
    push_narrow_mul_consume_entries(
        &mut entries,
        base,
        &cols,
        &gate,
        mul_result_relation,
        vec_rows,
    );

    // Entry 7: EC-op header YIELD (−gate): tuple
    // (source_index, op, output_inf, lhs_inf, rhs_inf).
    let lhs_inf_col = 6 + PREPARED_TABLE_EC_POINT_COLUMNS - 1;
    let rhs_inf_col = 6 + 2 * PREPARED_TABLE_EC_POINT_COLUMNS - 1;
    let output_inf_col = 6 + 3 * PREPARED_TABLE_EC_POINT_COLUMNS - 1;
    entries.push((
        gate.iter().map(|&lanes| -PackedQM31::from(lanes)).collect(),
        (0..vec_rows)
            .map(|vec_row| {
                header_relation.combine(&[
                    base[1].data[vec_row],
                    base[4].data[vec_row],
                    base[output_inf_col].data[vec_row],
                    base[lhs_inf_col].data[vec_row],
                    base[rhs_inf_col].data[vec_row],
                ])
            })
            .collect(),
    ));

    assert_eq!(entries.len(), prepared_consumer_logup_entries());
    let mut logup = LogupTraceGenerator::new(log_size);
    crate::range_checks::write_batched_logup_columns(
        &mut logup,
        &entries,
        PREPARED_CONSUMER_LOGUP_BATCH,
    );
    let (columns, _total) = logup.finalize_last();

    let ec_row_sum = prepared_table_projective_source_ec_row_sum(base, ec_row_relation);
    let mul_result_sum = narrow_mul_consume_sum(base, &cols, mul_result_relation);
    let header_yield_sum = prepared_table_projective_source_header_yield_sum(
        base,
        header_relation,
        &cols,
        lhs_inf_col,
        output_inf_col,
    );
    PreparedTableProjectiveSourceConsumerInteraction {
        columns,
        ec_row_sum,
        mul_result_sum,
        header_yield_sum,
    }
}

/// Analytic header-yield sum (−gate over rows with a silo group), matching the
/// eval's header yield entry. `gate = active − (1−op)·rhs.inf`.
fn prepared_table_projective_source_header_yield_sum(
    base: &[M31ColumnEval],
    header_relation: &crate::components::hinted_mul::EcOpHeaderRelation,
    cols: &NarrowMulConsumeColumns,
    lhs_inf_col: usize,
    output_inf_col: usize,
) -> SecureField {
    let log_size = base[0].domain.log_size();
    let one = M31::from_u32_unchecked(1);
    let mut denominators = Vec::new();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        for lane in 0..(1 << LOG_N_LANES) {
            let cell = |col: usize| base[col].data[vec_row].to_array()[lane];
            let gate = cell(0) - (one - cell(cols.op)) * cell(cols.rhs_inf);
            if gate == M31::from_u32_unchecked(0) {
                continue;
            }
            denominators.push(header_relation.combine(&[
                cell(cols.source),
                cell(cols.op),
                cell(output_inf_col),
                cell(lhs_inf_col),
                cell(cols.rhs_inf),
            ]));
        }
    }
    -crate::range_checks::batched_inverse_sum(&denominators)
}

/// Output of the prepared-table projective-source consumer interaction-trace
/// generator: the interaction columns and the per-relation analytic use sums.
pub(crate) struct PreparedTableProjectiveSourceConsumerInteraction {
    pub columns: ColumnVec<M31ColumnEval>,
    pub ec_row_sum: SecureField,
    pub mul_result_sum: SecureField,
    /// Σ of the EC-op header yields (−gate). Balances against the silo's
    /// header consume.
    pub header_yield_sum: SecureField,
}

/// Analytic EC-row consume sum over the consumer base trace's active rows.
fn prepared_table_projective_source_ec_row_sum(
    base: &[M31ColumnEval],
    ec_row_relation: &PreparedTableEcRowRelation,
) -> SecureField {
    let log_size = base[0].domain.log_size();
    let mut ec_row_denominators = Vec::new();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        for lane in 0..(1 << LOG_N_LANES) {
            let active = base[0].data[vec_row].to_array()[lane];
            if active != M31::from_u32_unchecked(0) {
                let ec_values =
                    prepared_table_projective_source_unpacked_relation_values(base, vec_row, lane);
                ec_row_denominators.push(ec_row_relation.combine(&ec_values));
            }
        }
    }
    crate::range_checks::batched_inverse_sum(&ec_row_denominators)
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
