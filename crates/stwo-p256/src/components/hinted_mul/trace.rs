//! Trace generation for the hinted-mul component: base columns, preprocessed
//! schedule/table columns, and the interaction trace (paired-logup layout in
//! lockstep with `HintedMulEval::evaluate`).

use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::core::ColumnVec;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{LogupTraceGenerator, Relation};
use stwo_p256_utils::constants::N_LIMBS;

use crate::components::gamma_digest::{
    gamma_padded_values, GammaChallenge, GammaDigestRelation, GammaTallInstance, GammaTallLayout,
    GAMMA_TAG_HINTED_MUL_RANGE13, GAMMA_TAG_HINTED_MUL_SIGNED,
};
use crate::components::projective_rcb_mul::relation::ProjectiveRcbMulResultRelation;
use crate::range_checks::{encode_signed_carry, RangeCheckRelation};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};

use super::witness::{split_carry, HintedMulWitness, HINTED_MUL_H_COEFFS, HINTED_MUL_Q_LIMBS};

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
        let mut rows = Self { rows: Vec::new() };
        rows.extend_from_projective_rcb(claim, 0)?;
        Ok(rows)
    }

    /// Appends every mul of `claim` keyed at
    /// `(source_offset + row.source_index, mul_index)` — used to fold other
    /// sub-graphs' muls (final-add, public-key curve check) into the single
    /// hinted provider with disjoint source ranges.
    pub fn extend_from_projective_rcb(
        &mut self,
        claim: &crate::projective_air::ProjectiveRcbAirTraceClaim,
        source_offset: u32,
    ) -> Result<(), super::witness::HintedMulWitnessError> {
        use rayon::prelude::*;
        let new_rows = claim
            .rows
            .par_iter()
            .flat_map_iter(|row| {
                row.muls.iter().enumerate().map(move |(mul_index, mul)| {
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
                    Ok(HintedMulScheduledRow {
                        source_index: source_offset + row.source_index as u32,
                        mul_index: mul_index as u32,
                        witness,
                    })
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        self.rows.extend(new_rows);
        Ok(())
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
pub const HINTED_MUL_GROUP_COLUMNS: usize = HINTED_MUL_Q_LIMBS + N_LIMBS + 2 * HINTED_MUL_H_COEFFS;

/// Base-trace column count: `a`, `b`, then the three identity groups.
pub const HINTED_MUL_TRACE_COLUMNS: usize = 2 * N_LIMBS + 3 * HINTED_MUL_GROUP_COLUMNS;
pub const HINTED_MUL_RANGE13_VALUES_PER_ROW: usize =
    2 * N_LIMBS + 3 * (HINTED_MUL_Q_LIMBS + N_LIMBS + HINTED_MUL_H_COEFFS);
pub const HINTED_MUL_SIGNED_VALUES_PER_ROW: usize = 3 * HINTED_MUL_H_COEFFS;

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

pub fn hinted_mul_schedule_row_index_id(log_size: u32) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("hinted_mul_schedule_row_index_{log_size}"),
    }
}

/// Schedule columns (per-circuit constants once the mul list shape is fixed):
/// `active`, `source_index`, `mul_index`, `row_index`.
pub fn gen_hinted_mul_schedule_columns(claim: &HintedMulTraceClaim) -> ColumnVec<M31ColumnEval> {
    let log_size = claim.log_size();
    let rows = 1usize << log_size;
    let mut active = vec![M31::from_u32_unchecked(0); rows];
    let mut source_index = vec![M31::from_u32_unchecked(0); rows];
    let mut mul_index = vec![M31::from_u32_unchecked(0); rows];
    let mut row_index = vec![M31::from_u32_unchecked(0); rows];
    for (row, scheduled) in claim.rows.iter().enumerate() {
        active[row] = M31::from_u32_unchecked(1);
        source_index[row] = M31::from_u32_unchecked(scheduled.source_index);
        mul_index[row] = M31::from_u32_unchecked(scheduled.mul_index);
        row_index[row] = M31::from_u32_unchecked(row as u32);
    }
    vec![
        m31_column_eval(log_size, active),
        m31_column_eval(log_size, source_index),
        m31_column_eval(log_size, mul_index),
        m31_column_eval(log_size, row_index),
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

pub fn hinted_mul_gamma_range13_columns() -> Vec<usize> {
    let mut columns = Vec::with_capacity(HINTED_MUL_RANGE13_VALUES_PER_ROW);
    let mut cursor = 0usize;
    for _ in 0..2 * N_LIMBS {
        columns.push(cursor);
        cursor += 1;
    }
    for _ in 0..3 {
        for _ in 0..HINTED_MUL_Q_LIMBS + N_LIMBS + HINTED_MUL_H_COEFFS {
            columns.push(cursor);
            cursor += 1;
        }
        cursor += HINTED_MUL_H_COEFFS;
    }
    debug_assert_eq!(columns.len(), HINTED_MUL_RANGE13_VALUES_PER_ROW);
    columns
}

pub fn hinted_mul_gamma_signed_columns() -> Vec<usize> {
    let mut columns = Vec::with_capacity(HINTED_MUL_SIGNED_VALUES_PER_ROW);
    let mut cursor = 2 * N_LIMBS;
    for _ in 0..3 {
        cursor += HINTED_MUL_Q_LIMBS + N_LIMBS + HINTED_MUL_H_COEFFS;
        for _ in 0..HINTED_MUL_H_COEFFS {
            columns.push(cursor);
            cursor += 1;
        }
    }
    debug_assert_eq!(columns.len(), HINTED_MUL_SIGNED_VALUES_PER_ROW);
    columns
}

pub fn hinted_mul_gamma_max_padded_values() -> usize {
    gamma_padded_values(HINTED_MUL_RANGE13_VALUES_PER_ROW)
        .max(gamma_padded_values(HINTED_MUL_SIGNED_VALUES_PER_ROW))
}

pub fn hinted_mul_gamma_layouts(rows: usize) -> [GammaTallLayout; 2] {
    [
        GammaTallLayout {
            tag: GAMMA_TAG_HINTED_MUL_RANGE13,
            group_count: rows,
            values_per_group: HINTED_MUL_RANGE13_VALUES_PER_ROW,
        },
        GammaTallLayout {
            tag: GAMMA_TAG_HINTED_MUL_SIGNED,
            group_count: rows,
            values_per_group: HINTED_MUL_SIGNED_VALUES_PER_ROW,
        },
    ]
}

pub fn hinted_mul_gamma_instances(claim: &HintedMulTraceClaim) -> [GammaTallInstance; 2] {
    let range13_columns = hinted_mul_gamma_range13_columns();
    let signed_columns = hinted_mul_gamma_signed_columns();
    let mut range13_groups = Vec::with_capacity(claim.rows.len());
    let mut signed_groups = Vec::with_capacity(claim.rows.len());
    for scheduled in &claim.rows {
        let mut values = Vec::with_capacity(HINTED_MUL_TRACE_COLUMNS);
        push_row_values(&scheduled.witness, &mut values);
        range13_groups.push(
            range13_columns
                .iter()
                .map(|&column| values[column])
                .collect(),
        );
        signed_groups.push(
            signed_columns
                .iter()
                .map(|&column| values[column])
                .collect(),
        );
    }
    [
        GammaTallInstance::new(
            GAMMA_TAG_HINTED_MUL_RANGE13,
            HINTED_MUL_RANGE13_VALUES_PER_ROW,
            M31::from_u32_unchecked(0),
            range13_groups,
        ),
        GammaTallInstance::new(
            GAMMA_TAG_HINTED_MUL_SIGNED,
            HINTED_MUL_SIGNED_VALUES_PER_ROW,
            encode_signed_carry(0),
            signed_groups,
        ),
    ]
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
    pub gamma_digest: GammaDigestRelation,
    pub gamma_challenge: GammaChallenge,
}

/// Interaction trace + per-relation claimed sums, paired two fractions per
/// interaction column (`finalize_logup_in_pairs` on the AIR side).
pub struct HintedMulInteractionClaim {
    pub claimed_sum: SecureField,
}

pub fn gen_hinted_mul_interaction_trace(
    claim: &HintedMulTraceClaim,
    base: &[M31ColumnEval],
    schedule: &[M31ColumnEval],
    relations: &HintedMulRelations,
) -> (ColumnVec<M31ColumnEval>, HintedMulInteractionClaim) {
    assert_eq!(base.len(), HINTED_MUL_TRACE_COLUMNS);
    assert_eq!(schedule.len(), 4);
    let log_size = claim.log_size();
    let vec_rows = 1usize << (log_size - LOG_N_LANES);
    let active = &schedule[0];
    let source_index = &schedule[1];
    let mul_index = &schedule[2];
    let row_index = &schedule[3];

    // Entry descriptors in the exact `evaluate` emission order: the three
    // mul-result provides, then the two gamma-digest yields that bind all
    // range/signed lookup values to their tall expanders.
    enum EntryKind {
        Provide {
            role: u32,
            column: usize,
        },
        GammaDigest {
            tag: u32,
            pad_value: M31,
            columns: Vec<usize>,
        },
    }
    let mut descriptors: Vec<EntryKind> = Vec::new();
    let role_columns: [(u32, usize); 3] = [
        (0, 0),       // LHS → a
        (1, N_LIMBS), // RHS → b
        (2, role_result_column()),
    ];
    for &(role, base_column) in role_columns.iter() {
        descriptors.push(EntryKind::Provide {
            role,
            column: base_column,
        });
    }
    descriptors.push(EntryKind::GammaDigest {
        tag: GAMMA_TAG_HINTED_MUL_RANGE13,
        pad_value: M31::from_u32_unchecked(0),
        columns: hinted_mul_gamma_range13_columns(),
    });
    descriptors.push(EntryKind::GammaDigest {
        tag: GAMMA_TAG_HINTED_MUL_SIGNED,
        pad_value: encode_signed_carry(0),
        columns: hinted_mul_gamma_signed_columns(),
    });

    // Per-entry packed denominators (independent → rayon).
    use rayon::prelude::*;
    let entries: Vec<(i64, Vec<PackedQM31>)> = descriptors
        .par_iter()
        .map(|kind| match kind {
            EntryKind::Provide { role, column } => (
                -1i64,
                (0..vec_rows)
                    .map(|vec_row| {
                        // Wide tuple: (source_index, mul_index, role, 20 limbs).
                        let mut values = Vec::with_capacity(3 + N_LIMBS);
                        values.push(source_index.data[vec_row]);
                        values.push(mul_index.data[vec_row]);
                        values.push(PackedM31::broadcast(M31::from_u32_unchecked(*role)));
                        for limb in 0..N_LIMBS {
                            values.push(base[*column + limb].data[vec_row]);
                        }
                        relations.mul_result.combine(&values)
                    })
                    .collect(),
            ),
            EntryKind::GammaDigest {
                tag,
                pad_value,
                columns,
            } => (
                -1i64,
                (0..vec_rows)
                    .map(|vec_row| {
                        let padded = gamma_padded_values(columns.len());
                        let pad_sum = {
                            let mut sum = SecureField::from(M31::from_u32_unchecked(0));
                            for power in 0..(padded - columns.len()) {
                                sum += relations.gamma_challenge.power(power);
                            }
                            sum * SecureField::from(*pad_value)
                        };
                        let mut coords: [PackedM31; SECURE_EXTENSION_DEGREE] =
                            pad_sum.to_m31_array().map(PackedM31::broadcast);
                        for (i, column) in columns.iter().enumerate() {
                            let power = relations
                                .gamma_challenge
                                .power(padded - 1 - i)
                                .to_m31_array();
                            for (coord, power_coord) in coords.iter_mut().zip(power) {
                                *coord +=
                                    base[*column].data[vec_row] * PackedM31::broadcast(power_coord);
                            }
                        }
                        let mut values = Vec::with_capacity(2 + SECURE_EXTENSION_DEGREE);
                        values.push(PackedM31::broadcast(M31::from_u32_unchecked(*tag)));
                        values.push(row_index.data[vec_row]);
                        values.extend(coords);
                        relations.gamma_digest.combine(&values)
                    })
                    .collect(),
            ),
        })
        .collect();

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

    // Per-relation analytic sums from the SAME packed denominators (one
    // Montgomery batch inversion over all of them; padding lanes are zeroed by
    // the active mask, so the values are identical to a scalar active-rows
    // walk).
    use stwo::core::fields::FieldExpOps;
    let active_mask: Vec<PackedQM31> = (0..vec_rows)
        .map(|vec_row| PackedQM31::from(active.data[vec_row]))
        .collect();
    let flat: Vec<PackedQM31> = entries
        .iter()
        .flat_map(|(_, denominators)| denominators.iter().copied())
        .collect();
    let inverses = PackedQM31::batch_inverse(&flat);
    let zero = SecureField::from(M31::from_u32_unchecked(0));
    let (mut range13_consumer, mut signed_consumer, mut mul_result_provider) = (zero, zero, zero);
    for (index, kind) in descriptors.iter().enumerate() {
        let segment = &inverses[index * vec_rows..(index + 1) * vec_rows];
        let total: SecureField = segment
            .iter()
            .zip(active_mask.iter())
            .map(|(inverse, mask)| {
                (*inverse * *mask)
                    .to_array()
                    .into_iter()
                    .sum::<SecureField>()
            })
            .sum();
        match kind {
            EntryKind::Provide { .. } => mul_result_provider -= total,
            EntryKind::GammaDigest { tag, .. } if *tag == GAMMA_TAG_HINTED_MUL_RANGE13 => {
                range13_consumer -= total
            }
            EntryKind::GammaDigest { tag, .. } if *tag == GAMMA_TAG_HINTED_MUL_SIGNED => {
                signed_consumer -= total
            }
            EntryKind::GammaDigest { .. } => unreachable!(),
        }
    }

    (trace, HintedMulInteractionClaim { claimed_sum })
}

/// Recompute the hinted-mul check component's `ProjectiveRcbMulResult`
/// provider sum without storing it in the production interaction claim.
#[cfg(test)]
pub(crate) fn hinted_mul_result_provider_sum(
    claim: &HintedMulTraceClaim,
    relations: &HintedMulRelations,
) -> SecureField {
    let mut sum = SecureField::from(M31::from_u32_unchecked(0));
    let roles = [
        (0u32, 0usize),
        (1u32, N_LIMBS),
        (2u32, role_result_column()),
    ];
    for scheduled in &claim.rows {
        let mut values = Vec::new();
        push_row_values(&scheduled.witness, &mut values);
        for (role, base_column) in roles {
            let mut tuple = Vec::with_capacity(3 + N_LIMBS);
            tuple.push(M31::from_u32_unchecked(scheduled.source_index));
            tuple.push(M31::from_u32_unchecked(scheduled.mul_index));
            tuple.push(M31::from_u32_unchecked(role));
            tuple.extend(values[base_column..base_column + N_LIMBS].iter().copied());
            let denom: SecureField = relations.mul_result.combine(&tuple);
            sum -= SecureField::from(M31::from_u32_unchecked(1)) / denom;
        }
    }
    sum
}

/// Range13 use values per active row (multiplicity feed for the provider).
pub fn hinted_mul_range13_uses(claim: &HintedMulTraceClaim) -> Vec<M31> {
    let [range13, _] = hinted_mul_gamma_instances(claim);
    range13.all_scheduled_values()
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
        let pad_count = gamma_padded_values(HINTED_MUL_SIGNED_VALUES_PER_ROW)
            - HINTED_MUL_SIGNED_VALUES_PER_ROW;
        uses.extend(std::iter::repeat_n(0, pad_count));
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
