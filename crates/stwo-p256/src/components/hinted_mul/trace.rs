//! Trace generation for the hinted-mul component: base columns, preprocessed
//! schedule/table columns, and the interaction trace (paired-logup layout in
//! lockstep with `HintedMulEval::evaluate`).

use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::SecureField;
use stwo::core::fields::FieldExpOps;
use stwo::core::ColumnVec;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{LogupTraceGenerator, Relation};
use stwo_p256_utils::constants::N_LIMBS;

use crate::components::projective_rcb_mul::relation::ProjectiveRcbMulResultRelation;
use crate::range_checks::{encode_signed_carry, RangeCheckRelation};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};

use super::witness::{
    split_carry, HintedMulWitness, HINTED_MUL_H_COEFFS, HINTED_MUL_Q_LIMBS,
};

/// One scheduled mul: the witness plus its `(source_index, mul_index)` key in
/// the `ProjectiveRcbMulResultRelation` namespace.
#[derive(Clone, Debug)]
pub struct HintedMulScheduledRow {
    pub source_index: u32,
    pub mul_index: u32,
    pub witness: HintedMulWitness,
}

/// All scheduled muls of one proof.
#[derive(Clone, Debug)]
pub struct HintedMulTraceClaim {
    pub rows: Vec<HintedMulScheduledRow>,
}

impl HintedMulTraceClaim {
    pub fn log_size(&self) -> u32 {
        padded_log_size(self.rows.len()).max(LOG_N_LANES)
    }

    /// Builds the hinted-mul rows from the silo trace claim, keyed by the
    /// exact `(source_index, mul_index)` pairs the EC-formula consumers use.
    /// The recomputed canonical result must match the silo's stored result
    /// limb-exact (the native silo results are canonical, including the
    /// identity fast-path rows whose result equals the canonical lhs), so the
    /// consumed-limb tuples are unchanged by the swap.
    pub fn from_projective_rcb(
        claim: &crate::projective_air::ProjectiveRcbAirTraceClaim,
    ) -> Result<Self, super::witness::HintedMulWitnessError> {
        let mut rows = Vec::new();
        for row in &claim.rows {
            for (mul_index, mul) in row.muls.iter().enumerate() {
                let a: [u32; N_LIMBS] = core::array::from_fn(|i| mul.trace.lhs.limbs()[i].0);
                let b: [u32; N_LIMBS] = core::array::from_fn(|i| mul.trace.rhs.limbs()[i].0);
                let witness = HintedMulWitness::new(&a, &b)?;
                let stored: [u32; N_LIMBS] =
                    core::array::from_fn(|i| mul.trace.result.limbs()[i].0);
                if witness.r != stored {
                    return Err(super::witness::HintedMulWitnessError::ResultMismatch {
                        source_index: row.source_index,
                        mul_index,
                    });
                }
                rows.push(HintedMulScheduledRow {
                    source_index: row.source_index as u32,
                    mul_index: mul_index as u32,
                    witness,
                });
            }
        }
        Ok(Self { rows })
    }

    /// Native re-verification of every witness (used by the draft's
    /// `verify_current_components`).
    pub fn verify(&self) -> Result<(), super::witness::HintedMulWitnessError> {
        for row in &self.rows {
            row.witness.verify()?;
        }
        Ok(())
    }
}

/// Per-identity column group: `q`, then the 20-limb value (`m1`/`m2`/`r`),
/// then `h_lo`, then `h_hi`.
pub const HINTED_MUL_GROUP_COLUMNS: usize =
    HINTED_MUL_Q_LIMBS + N_LIMBS + 2 * HINTED_MUL_H_COEFFS;

/// Base-trace column count: `a`, `b`, then the three identity groups.
pub const HINTED_MUL_TRACE_COLUMNS: usize = 2 * N_LIMBS + 3 * HINTED_MUL_GROUP_COLUMNS;

pub fn hinted_mul_schedule_active_id(log_size: u32) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("hinted_mul_schedule_active_{log_size}"),
    }
}

pub fn hinted_mul_schedule_source_index_id(log_size: u32) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("hinted_mul_schedule_source_index_{log_size}"),
    }
}

pub fn hinted_mul_schedule_mul_index_id(log_size: u32) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("hinted_mul_schedule_mul_index_{log_size}"),
    }
}

/// Schedule columns (per-circuit constants once the mul list shape is fixed):
/// `active`, `source_index`, `mul_index`.
pub fn gen_hinted_mul_schedule_columns(claim: &HintedMulTraceClaim) -> ColumnVec<M31ColumnEval> {
    let log_size = claim.log_size();
    let rows = 1usize << log_size;
    let mut active = vec![M31::from_u32_unchecked(0); rows];
    let mut source_index = vec![M31::from_u32_unchecked(0); rows];
    let mut mul_index = vec![M31::from_u32_unchecked(0); rows];
    for (row, scheduled) in claim.rows.iter().enumerate() {
        active[row] = M31::from_u32_unchecked(1);
        source_index[row] = M31::from_u32_unchecked(scheduled.source_index);
        mul_index[row] = M31::from_u32_unchecked(scheduled.mul_index);
    }
    vec![
        m31_column_eval(log_size, active),
        m31_column_eval(log_size, source_index),
        m31_column_eval(log_size, mul_index),
    ]
}

/// Base trace in [`HINTED_MUL_TRACE_COLUMNS`] layout. Padding rows are
/// all-zero, which satisfies the (ungated) carry identities trivially.
pub fn gen_hinted_mul_base_trace(claim: &HintedMulTraceClaim) -> ColumnVec<M31ColumnEval> {
    let log_size = claim.log_size();
    let rows = 1usize << log_size;
    let mut columns = vec![vec![M31::from_u32_unchecked(0); rows]; HINTED_MUL_TRACE_COLUMNS];
    for (row, scheduled) in claim.rows.iter().enumerate() {
        let mut values = Vec::with_capacity(HINTED_MUL_TRACE_COLUMNS);
        push_row_values(&scheduled.witness, &mut values);
        debug_assert_eq!(values.len(), HINTED_MUL_TRACE_COLUMNS);
        for (column, value) in columns.iter_mut().zip(values) {
            column[row] = value;
        }
    }
    columns
        .into_iter()
        .map(|values| m31_column_eval(log_size, values))
        .collect()
}

/// The committed M31 values of one witness, in column order. This is the
/// single source of truth for the base layout; `HintedMulEval::evaluate` reads
/// masks in the same order.
fn push_row_values(witness: &HintedMulWitness, out: &mut Vec<M31>) {
    let m = M31::from_u32_unchecked;
    out.extend(witness.a.iter().map(|&v| m(v)));
    out.extend(witness.b.iter().map(|&v| m(v)));
    for (q, value, h) in [
        (&witness.q1, &witness.m1, &witness.h1),
        (&witness.q2, &witness.m2, &witness.h2),
        (&witness.q3, &witness.r, &witness.h3),
    ] {
        out.extend(q.iter().map(|&v| m(v)));
        out.extend(value.iter().map(|&v| m(v)));
        let split: Vec<(u32, i64)> = h.iter().map(|&coeff| split_carry(coeff)).collect();
        out.extend(split.iter().map(|&(lo, _)| m(lo)));
        out.extend(split.iter().map(|&(_, hi)| encode_signed_carry(hi)));
    }
}

/// Relations consumed/provided by the check component.
#[derive(Clone)]
pub struct HintedMulRelations {
    pub range13: RangeCheckRelation,
    pub signed_h: RangeCheckRelation,
    pub mul_result: ProjectiveRcbMulResultRelation,
}

/// Interaction trace + per-relation claimed sums, paired two fractions per
/// interaction column (`finalize_logup_in_pairs` on the AIR side).
pub struct HintedMulInteractionClaim {
    pub claimed_sum: SecureField,
    pub range13_consumer_claimed_sum: SecureField,
    pub signed_h_consumer_claimed_sum: SecureField,
    pub mul_result_provider_claimed_sum: SecureField,
}

pub fn gen_hinted_mul_interaction_trace(
    claim: &HintedMulTraceClaim,
    base: &[M31ColumnEval],
    schedule: &[M31ColumnEval],
    relations: &HintedMulRelations,
) -> (ColumnVec<M31ColumnEval>, HintedMulInteractionClaim) {
    assert_eq!(base.len(), HINTED_MUL_TRACE_COLUMNS);
    assert_eq!(schedule.len(), 3);
    let log_size = claim.log_size();
    let vec_rows = 1usize << (log_size - LOG_N_LANES);
    let active = &schedule[0];
    let source_index = &schedule[1];
    let mul_index = &schedule[2];

    // Materialize the per-row entry stream column-wise: for each entry, a
    // (sign, denominator) per packed row. Entry order mirrors `evaluate`.
    let mut entries: Vec<(i64, Vec<PackedQM31>)> = Vec::new();
    let mut range13_uses: Vec<(usize, usize)> = Vec::new(); // (entry, column)
    let mut signed_uses: Vec<(usize, usize)> = Vec::new();

    let mut column_cursor = 0usize;
    let push_use = |entries: &mut Vec<(i64, Vec<PackedQM31>)>,
                        relation_kind: u8,
                        column: usize| {
        let denominators: Vec<PackedQM31> = (0..vec_rows)
            .map(|vec_row| {
                let value = base[column].data[vec_row];
                match relation_kind {
                    0 => relations.range13.combine(&[value]),
                    _ => relations.signed_h.combine(&[value]),
                }
            })
            .collect();
        entries.push((1, denominators));
    };

    // a, b: Range13.
    for _ in 0..2 * N_LIMBS {
        push_use(&mut entries, 0, column_cursor);
        range13_uses.push((entries.len() - 1, column_cursor));
        column_cursor += 1;
    }
    // Three identity groups: q, value, h_lo (Range13), h_hi (signed table).
    for _ in 0..3 {
        for _ in 0..HINTED_MUL_Q_LIMBS + N_LIMBS + HINTED_MUL_H_COEFFS {
            push_use(&mut entries, 0, column_cursor);
            range13_uses.push((entries.len() - 1, column_cursor));
            column_cursor += 1;
        }
        for _ in 0..HINTED_MUL_H_COEFFS {
            push_use(&mut entries, 1, column_cursor);
            signed_uses.push((entries.len() - 1, column_cursor));
            column_cursor += 1;
        }
    }
    assert_eq!(column_cursor, HINTED_MUL_TRACE_COLUMNS);

    // Provides: (source_index, mul_index, role, limb_index, limb) per role.
    let role_columns: [(u32, usize); 3] = [
        (0, 0),            // LHS → a
        (1, N_LIMBS),      // RHS → b
        (2, role_result_column()),
    ];
    for &(role, base_column) in role_columns.iter() {
        for limb_index in 0..N_LIMBS {
            let denominators: Vec<PackedQM31> = (0..vec_rows)
                .map(|vec_row| {
                    relations.mul_result.combine(&[
                        source_index.data[vec_row],
                        mul_index.data[vec_row],
                        PackedM31::broadcast(M31::from_u32_unchecked(role)),
                        PackedM31::broadcast(M31::from_u32_unchecked(limb_index as u32)),
                        base[base_column + limb_index].data[vec_row],
                    ])
                })
                .collect();
            entries.push((-1, denominators));
        }
    }

    // Write paired columns: fractions (n1/d1 + n2/d2) per interaction column,
    // exactly the layout `finalize_logup_in_pairs` expects.
    let mut logup = LogupTraceGenerator::new(log_size);
    for pair in entries.chunks(2) {
        let mut col = logup.new_col();
        for vec_row in 0..vec_rows {
            let active_value = PackedQM31::from(active.data[vec_row]);
            let (frac_n, frac_d) = match pair {
                [(s1, d1), (s2, d2)] => {
                    let n1 = active_value * signed_secure(*s1);
                    let n2 = active_value * signed_secure(*s2);
                    (
                        n1 * d2[vec_row] + n2 * d1[vec_row],
                        d1[vec_row] * d2[vec_row],
                    )
                }
                [(s1, d1)] => (active_value * signed_secure(*s1), d1[vec_row]),
                _ => unreachable!(),
            };
            col.write_frac(vec_row, frac_n, frac_d);
        }
        col.finalize_col();
    }
    let (trace, claimed_sum) = logup.finalize_last();

    // Per-relation claimed sums from the scalar view (active rows only).
    // Denominators are collected and inverted in one Montgomery batch per
    // relation (`FieldExpOps::batch_inverse`): the naive per-entry division is
    // ~367 QM31 inversions per row (~2.2M per signature) and dominated the
    // whole interaction generation.
    let mut range13_denominators: Vec<SecureField> =
        Vec::with_capacity(claim.rows.len() * range13_uses.len());
    let mut signed_denominators: Vec<SecureField> =
        Vec::with_capacity(claim.rows.len() * signed_uses.len());
    let mut mul_result_denominators: Vec<SecureField> =
        Vec::with_capacity(claim.rows.len() * 3 * N_LIMBS);
    for scheduled in claim.rows.iter() {
        let mut values = Vec::with_capacity(HINTED_MUL_TRACE_COLUMNS);
        push_row_values(&scheduled.witness, &mut values);
        for &(_, column) in range13_uses.iter() {
            range13_denominators.push(relations.range13.combine(&[values[column]]));
        }
        for &(_, column) in signed_uses.iter() {
            signed_denominators.push(relations.signed_h.combine(&[values[column]]));
        }
        for &(role, base_column) in role_columns.iter() {
            for limb_index in 0..N_LIMBS {
                mul_result_denominators.push(relations.mul_result.combine(&[
                    M31::from_u32_unchecked(scheduled.source_index),
                    M31::from_u32_unchecked(scheduled.mul_index),
                    M31::from_u32_unchecked(role),
                    M31::from_u32_unchecked(limb_index as u32),
                    values[base_column + limb_index],
                ]));
            }
        }
    }
    let range13_consumer: SecureField =
        SecureField::batch_inverse(&range13_denominators).into_iter().sum();
    let signed_consumer: SecureField =
        SecureField::batch_inverse(&signed_denominators).into_iter().sum();
    let mul_result_provider: SecureField = -SecureField::batch_inverse(&mul_result_denominators)
        .into_iter()
        .sum::<SecureField>();

    (
        trace,
        HintedMulInteractionClaim {
            claimed_sum,
            range13_consumer_claimed_sum: range13_consumer,
            signed_h_consumer_claimed_sum: signed_consumer,
            mul_result_provider_claimed_sum: mul_result_provider,
        },
    )
}

/// Range13 use values per active row (multiplicity feed for the provider).
pub fn hinted_mul_range13_uses(claim: &HintedMulTraceClaim) -> Vec<M31> {
    let mut uses = Vec::new();
    for scheduled in &claim.rows {
        let mut values = Vec::with_capacity(HINTED_MUL_TRACE_COLUMNS);
        push_row_values(&scheduled.witness, &mut values);
        let mut column = 0usize;
        for _ in 0..2 * N_LIMBS {
            uses.push(values[column]);
            column += 1;
        }
        for _ in 0..3 {
            for _ in 0..HINTED_MUL_Q_LIMBS + N_LIMBS + HINTED_MUL_H_COEFFS {
                uses.push(values[column]);
                column += 1;
            }
            column += HINTED_MUL_H_COEFFS; // skip h_hi (signed table)
        }
    }
    uses
}

/// Signed-table use values (`h_hi`, decoded) per active row.
pub fn hinted_mul_signed_uses(claim: &HintedMulTraceClaim) -> Vec<i64> {
    let mut uses = Vec::new();
    for scheduled in &claim.rows {
        for h in [
            &scheduled.witness.h1,
            &scheduled.witness.h2,
            &scheduled.witness.h3,
        ] {
            for &coeff in h.iter() {
                uses.push(split_carry(coeff).1);
            }
        }
    }
    uses
}

/// Column of the RESULT role (`r`): third group's 20-limb value.
pub const fn role_result_column() -> usize {
    2 * N_LIMBS + 2 * HINTED_MUL_GROUP_COLUMNS + HINTED_MUL_Q_LIMBS
}

fn signed_secure(sign: i64) -> PackedQM31 {
    let value = if sign >= 0 {
        M31::from_u32_unchecked(sign as u32)
    } else {
        M31::from_u32_unchecked((((1i64 << 31) - 1) + sign) as u32)
    };
    PackedQM31::from(PackedM31::broadcast(value))
}
