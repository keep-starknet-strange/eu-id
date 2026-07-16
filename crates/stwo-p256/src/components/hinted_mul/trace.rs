//! Trace generation for the hinted-mul component: base columns, preprocessed
//! schedule/table columns, and the interaction trace (paired-logup layout in
//! lockstep with `HintedMulEval::evaluate`).

use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::SecureField;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::utils::{bit_reverse_index, circle_domain_index_to_coset_index};
use stwo::core::ColumnVec;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES, N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{LogupTraceGenerator, Relation};
use stwo_p256_utils::constants::N_LIMBS;

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
    /// EC-op header metadata, copied from the source `ProjectiveRcbAirRow` onto
    /// EVERY scheduled row of that proj group (Phase 1 threads it; only the
    /// `mul_index == 0` header row's flags are read by the silo). `op_double`
    /// is `true` for `ProjectiveEcOp::Double`. All false for non-proj-scope
    /// rows (final_add / public_key_curve).
    pub op_double: bool,
    pub lhs_inf: bool,
    pub rhs_inf: bool,
    pub output_inf: bool,
    /// `true` iff this row belongs to a projective-source group (fake_glv /
    /// prepared_table). Gates the flag columns and the `is_proj_mul_k`
    /// one-hots on/off.
    pub proj_scope: bool,
    /// Phase-2 per-row formula cells (out_val + the two reduction slots'
    /// `(q, carries)`), computed once per proj group by interpreting the shared
    /// spec table. All-zero (encoded) for non-proj rows.
    pub formula: super::formula_bind::FormulaRowCells,
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
        rows.extend_from_projective_rcb(claim, 0, true)?;
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
        proj_scope: bool,
    ) -> Result<(), super::witness::HintedMulWitnessError> {
        use rayon::prelude::*;
        let new_rows = claim
            .rows
            .par_iter()
            .map(|row| {
                let op_double = matches!(row.op, crate::projective::ProjectiveEcOp::Double);
                let (lhs_inf, rhs_inf, output_inf) = (row.lhs_inf, row.rhs_inf, row.output_inf);
                // Phase-2: solve the whole group's per-row formula cells once,
                // by interpreting the shared spec table. Only proj-scope groups
                // (which carry the full 15 muls) get real cells; every other row
                // holds encoded-zero (default) cells.
                let formula_cells: Option<Vec<super::formula_bind::FormulaRowCells>> = if proj_scope
                    && row.muls.len() == super::formula_bind::FORMULA_ROWS
                {
                    let group_muls: Vec<_> = row
                        .muls
                        .iter()
                        .map(|mul| {
                            let a: [M31; N_LIMBS] =
                                core::array::from_fn(|i| mul.trace.lhs.limbs()[i]);
                            let b: [M31; N_LIMBS] =
                                core::array::from_fn(|i| mul.trace.rhs.limbs()[i]);
                            let r: [M31; N_LIMBS] =
                                core::array::from_fn(|i| mul.trace.result.limbs()[i]);
                            (a, b, r)
                        })
                        .collect();
                    let out_x =
                        *crate::limbs::P256M31BigInt::from_u256(&row.output_projective.x.to_u256())
                            .limbs();
                    let out_y =
                        *crate::limbs::P256M31BigInt::from_u256(&row.output_projective.y.to_u256())
                            .limbs();
                    Some(
                        super::formula_bind::solve_group_formula(
                            &group_muls,
                            op_double,
                            &out_x,
                            &out_y,
                        )
                        .ok_or(
                            super::witness::HintedMulWitnessError::ResultMismatch {
                                source_index: row.source_index,
                                mul_index: 0,
                            },
                        )?,
                    )
                } else {
                    None
                };
                row.muls
                    .iter()
                    .enumerate()
                    .map(|(mul_index, mul)| {
                        let a: [u32; N_LIMBS] =
                            core::array::from_fn(|i| mul.trace.lhs.limbs()[i].0);
                        let b: [u32; N_LIMBS] =
                            core::array::from_fn(|i| mul.trace.rhs.limbs()[i].0);
                        let witness = HintedMulWitness::new(&a, &b)?;
                        let stored: [u32; N_LIMBS] =
                            core::array::from_fn(|i| mul.trace.result.limbs()[i].0);
                        if witness.r != stored {
                            return Err(super::witness::HintedMulWitnessError::ResultMismatch {
                                source_index: row.source_index,
                                mul_index,
                            });
                        }
                        let formula = formula_cells
                            .as_ref()
                            .map(|cells| cells[mul_index].clone())
                            .unwrap_or_default();
                        Ok(HintedMulScheduledRow {
                            source_index: source_offset + row.source_index as u32,
                            mul_index: mul_index as u32,
                            witness,
                            op_double,
                            lhs_inf,
                            rhs_inf,
                            output_inf,
                            proj_scope,
                            formula,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<Vec<_>>, _>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
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

/// Witness-only column count (`a`, `b`, then the three identity groups). This
/// is the layout `push_row_values` / `hinted_mul_range13_uses` walk.
pub const HINTED_MUL_WITNESS_COLUMNS: usize = 2 * N_LIMBS + 3 * HINTED_MUL_GROUP_COLUMNS;

/// Header-flag columns appended after the witness block: `op`, `output_inf`,
/// `lhs_inf`, `rhs_inf` (in this order). Nonzero only on proj-scope header rows
/// (`mul_index == 0`); zero on every other row (including padding and non-proj
/// groups).
pub const HINTED_MUL_FLAG_COLUMNS: usize = 4;

/// Column index of flag `i` (0=op, 1=output_inf, 2=lhs_inf, 3=rhs_inf) in the
/// base trace. The evaluator reads these right after the witness block.
pub const fn hinted_mul_flag_column(i: usize) -> usize {
    HINTED_MUL_WITNESS_COLUMNS + i
}

/// First column of the witness+flag block (offset where the Phase-2 formula
/// columns begin): 307 witness + 4 flags = 311.
pub const HINTED_MUL_FORMULA_BASE: usize = HINTED_MUL_WITNESS_COLUMNS + HINTED_MUL_FLAG_COLUMNS;

/// Phase-2 formula columns appended after the flags, in this fixed order:
/// `out_val[20]`, slot0 (`q`, `carries[20]`), slot1 (`q`, `carries[20]`).
/// `out_val` holds x3 limbs on each proj group's row 13, y3 on row 14, zero
/// elsewhere. Each reduction slot has one un-range-checked quotient `q` and 20
/// signed carries (projective-bound signed table). = 20 + 42 = 62.
pub const HINTED_MUL_OUT_VAL_COLUMNS: usize = N_LIMBS;
pub const HINTED_MUL_SLOT_COLUMNS: usize = 1 + N_LIMBS;
pub const HINTED_MUL_FORMULA_COLUMNS: usize =
    HINTED_MUL_OUT_VAL_COLUMNS + 2 * HINTED_MUL_SLOT_COLUMNS;

/// Column index of `out_val` limb `i`.
pub const fn hinted_mul_out_val_column(i: usize) -> usize {
    HINTED_MUL_FORMULA_BASE + i
}
/// Column index of slot `s` (0/1) quotient `q`.
pub const fn hinted_mul_slot_q_column(s: usize) -> usize {
    HINTED_MUL_FORMULA_BASE + HINTED_MUL_OUT_VAL_COLUMNS + s * HINTED_MUL_SLOT_COLUMNS
}
/// Column index of slot `s` (0/1) carry `i`.
pub const fn hinted_mul_slot_carry_column(s: usize, i: usize) -> usize {
    hinted_mul_slot_q_column(s) + 1 + i
}

/// Base-trace column count: witness + flags + Phase-2 formula columns (373).
pub const HINTED_MUL_TRACE_COLUMNS: usize = HINTED_MUL_FORMULA_BASE + HINTED_MUL_FORMULA_COLUMNS;

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

/// Number of `is_proj_mul_k` one-hot schedule columns (one per silo mul_index of
/// a projective group).
pub const HINTED_MUL_PROJ_MUL_COLUMNS: usize =
    crate::projective_air::PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP;

/// Preprocessed one-hot `is_proj_mul_k`: value 1 exactly on rows with
/// `proj_scope && mul_index == k` (active real rows only), else 0. `k == 0`
/// doubles as the `EcOpHeaderRelation` consume numerator on the silo header row.
pub fn hinted_mul_schedule_proj_mul_id(log_size: u32, k: usize) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("hinted_mul_schedule_proj_mul_{k}_{log_size}"),
    }
}

/// Total schedule columns: `active`, `source_index`, `mul_index`, then the 15
/// `is_proj_mul_k` one-hots.
pub const HINTED_MUL_SCHEDULE_COLUMNS: usize = 3 + HINTED_MUL_PROJ_MUL_COLUMNS;

/// Schedule columns (per-circuit constants once the mul list shape is fixed):
/// `active`, `source_index`, `mul_index`, then `is_proj_mul_0..14`.
pub fn gen_hinted_mul_schedule_columns(claim: &HintedMulTraceClaim) -> ColumnVec<M31ColumnEval> {
    if rayon::current_num_threads() == 1 {
        gen_hinted_mul_schedule_columns_scalar(claim)
    } else {
        gen_hinted_mul_schedule_columns_packed(claim)
    }
}

fn gen_hinted_mul_schedule_columns_scalar(claim: &HintedMulTraceClaim) -> ColumnVec<M31ColumnEval> {
    let log_size = claim.log_size();
    let rows = 1usize << log_size;
    let mut active = vec![M31::from_u32_unchecked(0); rows];
    let mut source_index = vec![M31::from_u32_unchecked(0); rows];
    let mut mul_index = vec![M31::from_u32_unchecked(0); rows];
    let mut proj_mul = vec![vec![M31::from_u32_unchecked(0); rows]; HINTED_MUL_PROJ_MUL_COLUMNS];
    for (row, scheduled) in claim.rows.iter().enumerate() {
        active[row] = M31::from_u32_unchecked(1);
        source_index[row] = M31::from_u32_unchecked(scheduled.source_index);
        mul_index[row] = M31::from_u32_unchecked(scheduled.mul_index);
        if scheduled.proj_scope && (scheduled.mul_index as usize) < HINTED_MUL_PROJ_MUL_COLUMNS {
            proj_mul[scheduled.mul_index as usize][row] = M31::from_u32_unchecked(1);
        }
    }
    let mut columns = vec![
        m31_column_eval(log_size, active),
        m31_column_eval(log_size, source_index),
        m31_column_eval(log_size, mul_index),
    ];
    columns.extend(
        proj_mul
            .into_iter()
            .map(|values| m31_column_eval(log_size, values)),
    );
    columns
}

fn gen_hinted_mul_schedule_columns_packed(claim: &HintedMulTraceClaim) -> ColumnVec<M31ColumnEval> {
    use rayon::prelude::*;

    let log_size = claim.log_size();
    let zero = M31::from_u32_unchecked(0);
    let one = M31::from_u32_unchecked(1);
    let schedule_value = |column: usize, row: usize| -> M31 {
        let Some(scheduled) = claim.rows.get(row) else {
            return zero;
        };
        match column {
            0 => one,
            1 => M31::from_u32_unchecked(scheduled.source_index),
            2 => M31::from_u32_unchecked(scheduled.mul_index),
            column => {
                let mul_index = column - 3;
                if scheduled.proj_scope && scheduled.mul_index as usize == mul_index {
                    one
                } else {
                    zero
                }
            }
        }
    };

    if rayon::current_num_threads() == 1 {
        (0..HINTED_MUL_SCHEDULE_COLUMNS)
            .map(|column| {
                packed_m31_eval_from_coset_rows(log_size, |row| schedule_value(column, row))
            })
            .collect()
    } else {
        (0..HINTED_MUL_SCHEDULE_COLUMNS)
            .into_par_iter()
            .map(|column| {
                packed_m31_eval_from_coset_rows(log_size, |row| schedule_value(column, row))
            })
            .collect()
    }
}

/// Base trace in [`HINTED_MUL_TRACE_COLUMNS`] layout. Padding rows are
/// all-zero, which satisfies the (ungated) carry identities trivially.
pub fn gen_hinted_mul_base_trace(claim: &HintedMulTraceClaim) -> ColumnVec<M31ColumnEval> {
    if rayon::current_num_threads() == 1 {
        gen_hinted_mul_base_trace_scalar(claim)
    } else {
        gen_hinted_mul_base_trace_packed(claim)
    }
}

fn gen_hinted_mul_base_trace_scalar(claim: &HintedMulTraceClaim) -> ColumnVec<M31ColumnEval> {
    let log_size = claim.log_size();
    let rows = 1usize << log_size;
    let mut columns = vec![vec![M31::from_u32_unchecked(0); rows]; HINTED_MUL_TRACE_COLUMNS];
    let bool_m31 = |flag: bool| M31::from_u32_unchecked(u32::from(flag));
    for (row, scheduled) in claim.rows.iter().enumerate() {
        let mut values = Vec::with_capacity(HINTED_MUL_WITNESS_COLUMNS);
        push_row_values(&scheduled.witness, &mut values);
        debug_assert_eq!(values.len(), HINTED_MUL_WITNESS_COLUMNS);
        for (column, value) in columns.iter_mut().zip(values) {
            column[row] = value;
        }
        // Header flags: live only on proj-scope group-header rows; every other
        // row (non-proj groups, non-header proj rows, padding) keeps 0.
        if scheduled.proj_scope && scheduled.mul_index == 0 {
            for (i, flag) in [
                scheduled.op_double,
                scheduled.output_inf,
                scheduled.lhs_inf,
                scheduled.rhs_inf,
            ]
            .into_iter()
            .enumerate()
            {
                columns[hinted_mul_flag_column(i)][row] = bool_m31(flag);
            }
        }
        // Phase-2 formula columns. On EVERY active row (proj AND non-proj) the
        // reduction q/carry cells hold encoded values so the active-gated signed
        // lookup passes; out_val holds x3/y3 on proj rows 13/14, zero elsewhere.
        // (Non-proj rows carry default cells: q=0, carries=0, out_val=0 — all
        // encode to valid table members.) Padding rows keep raw 0.
        let cells = &scheduled.formula;
        for (i, &limb) in cells.out_val.iter().enumerate() {
            columns[hinted_mul_out_val_column(i)][row] = limb;
        }
        for (s, (q, carries)) in [&cells.slot0, &cells.slot1].into_iter().enumerate() {
            columns[hinted_mul_slot_q_column(s)][row] = encode_signed_carry(*q);
            for (i, &carry) in carries.iter().enumerate() {
                columns[hinted_mul_slot_carry_column(s, i)][row] = encode_signed_carry(carry);
            }
        }
    }
    columns
        .into_iter()
        .map(|values| m31_column_eval(log_size, values))
        .collect()
}

fn gen_hinted_mul_base_trace_packed(claim: &HintedMulTraceClaim) -> ColumnVec<M31ColumnEval> {
    use rayon::prelude::*;

    let log_size = claim.log_size();
    let zero = M31::from_u32_unchecked(0);
    let row_values = claim
        .rows
        .par_iter()
        .map(|scheduled| {
            let mut row = vec![zero; HINTED_MUL_TRACE_COLUMNS];
            let mut values = Vec::with_capacity(HINTED_MUL_WITNESS_COLUMNS);
            push_row_values(&scheduled.witness, &mut values);
            debug_assert_eq!(values.len(), HINTED_MUL_WITNESS_COLUMNS);
            row[..HINTED_MUL_WITNESS_COLUMNS].copy_from_slice(&values);
            if scheduled.proj_scope && scheduled.mul_index == 0 {
                for (i, flag) in [
                    scheduled.op_double,
                    scheduled.output_inf,
                    scheduled.lhs_inf,
                    scheduled.rhs_inf,
                ]
                .into_iter()
                .enumerate()
                {
                    row[hinted_mul_flag_column(i)] = M31::from_u32_unchecked(u32::from(flag));
                }
            }
            let cells = &scheduled.formula;
            for (i, &limb) in cells.out_val.iter().enumerate() {
                row[hinted_mul_out_val_column(i)] = limb;
            }
            for (s, (q, carries)) in [&cells.slot0, &cells.slot1].into_iter().enumerate() {
                row[hinted_mul_slot_q_column(s)] = encode_signed_carry(*q);
                for (i, &carry) in carries.iter().enumerate() {
                    row[hinted_mul_slot_carry_column(s, i)] = encode_signed_carry(carry);
                }
            }
            row
        })
        .collect::<Vec<_>>();

    (0..HINTED_MUL_TRACE_COLUMNS)
        .into_par_iter()
        .map(|column| {
            packed_m31_eval_from_coset_rows(log_size, |row| {
                row_values
                    .get(row)
                    .map(|values| values[column])
                    .unwrap_or(zero)
            })
        })
        .collect()
}

fn packed_m31_eval_from_coset_rows(
    log_size: u32,
    value_at_coset_row: impl Fn(usize) -> M31 + Sync,
) -> M31ColumnEval {
    if log_size < LOG_N_LANES {
        let values = (0..(1usize << log_size)).map(value_at_coset_row).collect();
        return m31_column_eval(log_size, values);
    }

    let packed_rows = 1usize << (log_size - LOG_N_LANES);
    let data = (0..packed_rows)
        .map(|packed_row| {
            PackedM31::from_array(core::array::from_fn(|lane| {
                let storage_index = packed_row * N_LANES + lane;
                let circle_index = bit_reverse_index(storage_index, log_size);
                let coset_index = circle_domain_index_to_coset_index(circle_index, log_size);
                value_at_coset_row(coset_index)
            }))
        })
        .collect();
    let domain = CanonicCoset::new(log_size).circle_domain();
    M31ColumnEval::new(domain, BaseColumn::from_simd(data))
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
    /// EC-op header link: the silo CONSUMES `(source_index, op, output_inf,
    /// lhs_inf, rhs_inf)` on each proj group header row (numerator
    /// `is_proj_mul_0`); the projective-source consumers PROVIDE it.
    pub header: super::EcOpHeaderRelation,
    /// Phase-2 signed-carry table for the formula reduction carries, at the
    /// PROJECTIVE bound (`PROJECTIVE_RCB_SIGNED_CARRY_EQUATION`). Dedups by
    /// equation name with the (to-be-deleted) consumer signed-carry providers.
    pub signed_formula: RangeCheckRelation,
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
    assert_eq!(schedule.len(), HINTED_MUL_SCHEDULE_COLUMNS);
    let log_size = claim.log_size();
    let vec_rows = 1usize << (log_size - LOG_N_LANES);
    let active = &schedule[0];
    let source_index = &schedule[1];
    let mul_index = &schedule[2];
    // `is_proj_mul_0` doubles as the header consume numerator (schedule offset 3
    // is `is_proj_mul_0` — see `gen_hinted_mul_schedule_columns`).
    let is_proj_mul_0 = &schedule[3];
    // Per-slot provide-mask numerators (Phase 3), mirroring the eval:
    //   LHS:    active − Σ_{k=2..12} is_proj_k
    //   RHS:    active − Σ_{k=2..14} is_proj_k
    //   RESULT: active − Σ_{k=0..14} is_proj_k
    let masked_numerator = |range: core::ops::RangeInclusive<usize>| -> Vec<PackedM31> {
        (0..vec_rows)
            .map(|vec_row| {
                let mut numerator = active.data[vec_row];
                for k in range.clone() {
                    numerator -= schedule[3 + k].data[vec_row];
                }
                numerator
            })
            .collect()
    };
    let provide_numerators: [Vec<PackedM31>; 3] = [
        masked_numerator(2..=12),
        masked_numerator(2..=14),
        masked_numerator(0..=14),
    ];

    // Entry descriptors in the exact `evaluate` emission order: every committed
    // column in column order (Range13 for limbs, the signed table for h_hi),
    // then the 3 mul-result provides, then the single header consume.
    //
    // Each entry carries its OWN numerator column (not a global `active`
    // multiply): the range/provide entries use `active`, the header consume
    // uses `is_proj_mul_0`. `sign` is +1 for uses/consumes, −1 for provides.
    enum EntryKind {
        Range13(usize),
        SignedH(usize),
        Provide {
            role: u32,
            column: usize,
        },
        Header,
        /// Phase-2 formula reduction carry, signed table at the projective bound.
        SignedFormula(usize),
    }
    let mut descriptors: Vec<EntryKind> = Vec::new();
    let mut column_cursor = 0usize;
    for _ in 0..2 * N_LIMBS {
        descriptors.push(EntryKind::Range13(column_cursor));
        column_cursor += 1;
    }
    for _ in 0..3 {
        for _ in 0..HINTED_MUL_Q_LIMBS + N_LIMBS + HINTED_MUL_H_COEFFS {
            descriptors.push(EntryKind::Range13(column_cursor));
            column_cursor += 1;
        }
        for _ in 0..HINTED_MUL_H_COEFFS {
            descriptors.push(EntryKind::SignedH(column_cursor));
            column_cursor += 1;
        }
    }
    // Descriptors walk the WITNESS columns only; the flag columns carry no
    // range check (the eval reads them without one).
    assert_eq!(column_cursor, HINTED_MUL_WITNESS_COLUMNS);
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
    // Header consume: appended at the END (odd tail; handled solo by the same
    // pairing math the eval's `finalize_logup_in_pairs` applies).
    descriptors.push(EntryKind::Header);
    // Phase-2 formula range/signed uses, in EXACT eval-emission order (after the
    // header consume): out_val (20 Range13), slot0 carries (20 SignedFormula,
    // q skipped), slot1 carries (20 SignedFormula, q skipped).
    for i in 0..N_LIMBS {
        descriptors.push(EntryKind::Range13(hinted_mul_out_val_column(i)));
    }
    for s in 0..2 {
        for i in 0..N_LIMBS {
            descriptors.push(EntryKind::SignedFormula(hinted_mul_slot_carry_column(s, i)));
        }
    }

    // Per-entry (numerator lanes, sign, packed denominators). Independent →
    // rayon.
    use rayon::prelude::*;
    let active_lanes: Vec<PackedM31> = (0..vec_rows).map(|r| active.data[r]).collect();
    let header_lanes: Vec<PackedM31> = (0..vec_rows).map(|r| is_proj_mul_0.data[r]).collect();
    let entries: Vec<(Vec<PackedM31>, i64, Vec<PackedQM31>)> = descriptors
        .par_iter()
        .map(|kind| match kind {
            EntryKind::Range13(column) => (
                active_lanes.clone(),
                1i64,
                (0..vec_rows)
                    .map(|vec_row| relations.range13.combine(&[base[*column].data[vec_row]]))
                    .collect(),
            ),
            EntryKind::SignedH(column) => (
                active_lanes.clone(),
                1i64,
                (0..vec_rows)
                    .map(|vec_row| relations.signed_h.combine(&[base[*column].data[vec_row]]))
                    .collect(),
            ),
            EntryKind::SignedFormula(column) => (
                active_lanes.clone(),
                1i64,
                (0..vec_rows)
                    .map(|vec_row| {
                        relations
                            .signed_formula
                            .combine(&[base[*column].data[vec_row]])
                    })
                    .collect(),
            ),
            EntryKind::Provide { role, column } => (
                provide_numerators[*role as usize].clone(),
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
            // Header consume (+is_proj_mul_0): tuple
            // (source_index, op, output_inf, lhs_inf, rhs_inf) — the flag
            // columns live on the header row itself (offset 0).
            EntryKind::Header => (
                header_lanes.clone(),
                1i64,
                (0..vec_rows)
                    .map(|vec_row| {
                        let values = [
                            source_index.data[vec_row],
                            base[hinted_mul_flag_column(0)].data[vec_row],
                            base[hinted_mul_flag_column(1)].data[vec_row],
                            base[hinted_mul_flag_column(2)].data[vec_row],
                            base[hinted_mul_flag_column(3)].data[vec_row],
                        ];
                        relations.header.combine(&values)
                    })
                    .collect(),
            ),
        })
        .collect();

    // Write paired columns: fractions (n1/d1 + n2/d2) per interaction column,
    // exactly the layout `finalize_logup_in_pairs` expects. Each entry supplies
    // its own numerator column (active-based or is_proj_mul_0), sign-scaled.
    let mut logup = LogupTraceGenerator::new(log_size);
    let numer = |lanes: &[PackedM31], sign: i64, vec_row: usize| {
        PackedQM31::from(lanes[vec_row]) * signed_secure(sign)
    };
    for pair in entries.chunks(2) {
        logup.col_from_fn(|vec_row| match pair {
            [(c1, s1, d1), (c2, s2, d2)] => {
                let n1 = numer(c1, *s1, vec_row);
                let n2 = numer(c2, *s2, vec_row);
                (
                    n1 * d2[vec_row] + n2 * d1[vec_row],
                    d1[vec_row] * d2[vec_row],
                )
            }
            [(c1, s1, d1)] => (numer(c1, *s1, vec_row), d1[vec_row]),
            _ => unreachable!(),
        });
    }
    let (trace, claimed_sum) = logup.finalize_last();

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
            // Per-slot provide masks: proj rows provide only the narrowly
            // consumed slots (LHS at mul 0/1/13/14, RHS at mul 0/1, RESULT
            // never); non-proj rows provide all three roles.
            if scheduled.proj_scope {
                let provided = match role {
                    0 => matches!(scheduled.mul_index, 0 | 1 | 13 | 14),
                    1 => matches!(scheduled.mul_index, 0 | 1),
                    _ => false,
                };
                if !provided {
                    continue;
                }
            }
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

/// Recompute the silo's `EcOpHeaderRelation` consume sum (`+is_proj_0` on each
/// proj group header row) — excluded from the standalone slice balance since the
/// header PROVIDER lives on the (out-of-slice) projective-source consumers.
#[cfg(test)]
pub(crate) fn hinted_mul_header_consume_sum(
    claim: &HintedMulTraceClaim,
    relations: &HintedMulRelations,
) -> SecureField {
    let bool_m31 = |flag: bool| M31::from_u32_unchecked(u32::from(flag));
    let mut sum = SecureField::from(M31::from_u32_unchecked(0));
    for scheduled in &claim.rows {
        if scheduled.proj_scope && scheduled.mul_index == 0 {
            let tuple = [
                M31::from_u32_unchecked(scheduled.source_index),
                bool_m31(scheduled.op_double),
                bool_m31(scheduled.output_inf),
                bool_m31(scheduled.lhs_inf),
                bool_m31(scheduled.rhs_inf),
            ];
            let denom: SecureField = relations.header.combine(&tuple);
            sum += SecureField::from(M31::from_u32_unchecked(1)) / denom;
        }
    }
    sum
}

/// Range13 use values per active row (multiplicity feed for the provider):
/// every 13-bit witness limb, then the Phase-2 `out_val` limbs (also
/// Range13-checked, active-gated; zero on rows ≠ 13/14).
pub fn hinted_mul_range13_uses(claim: &HintedMulTraceClaim) -> Vec<M31> {
    let mut uses = Vec::new();
    for scheduled in &claim.rows {
        let mut values = Vec::with_capacity(HINTED_MUL_WITNESS_COLUMNS);
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
        // Phase-2 out_val limbs (Range13, active-gated). Emitted AFTER the
        // witness limbs to mirror the eval read order exactly.
        for &limb in scheduled.formula.out_val.iter() {
            uses.push(limb);
        }
    }
    uses
}

/// Signed-table use values (Phase-2 reduction carries, decoded) per active row:
/// slot 0's 20 carries then slot 1's 20 carries. The quotient `q` is NOT
/// range-checked (transitively pinned by the carry chain, per the plan). These
/// feed the silo's signed-carry provider at the PROJECTIVE bound.
pub fn hinted_mul_formula_signed_uses(claim: &HintedMulTraceClaim) -> Vec<i64> {
    let mut uses = Vec::new();
    for scheduled in &claim.rows {
        for (_, carries) in [&scheduled.formula.slot0, &scheduled.formula.slot1] {
            for &carry in carries.iter() {
                uses.push(carry);
            }
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

#[cfg(test)]
mod tests {
    use super::super::witness::HintedMulWitness;
    use super::*;

    fn synthetic_claim(muls: usize) -> HintedMulTraceClaim {
        let rows = (0..muls)
            .map(|i| {
                let mut a = [0u32; N_LIMBS];
                let mut b = [0u32; N_LIMBS];
                for k in 0..N_LIMBS {
                    a[k] = ((i as u32 + 1) * 2741 + 97 * k as u32) % 8192;
                    b[k] = ((i as u32 + 3) * 4099 + 53 * k as u32) % 8192;
                }
                HintedMulScheduledRow {
                    source_index: i as u32 / 4,
                    mul_index: i as u32 % 4,
                    witness: HintedMulWitness::new(&a, &b).expect("witness builds"),
                    op_double: false,
                    lhs_inf: false,
                    rhs_inf: false,
                    output_inf: false,
                    proj_scope: false,
                    formula: super::super::formula_bind::FormulaRowCells::default(),
                }
            })
            .collect();
        HintedMulTraceClaim { rows }
    }

    fn projective_claim() -> HintedMulTraceClaim {
        let trace = super::super::formula_bind::sample_projective_trace();
        let rcb =
            crate::projective_air::ProjectiveRcbAirTraceClaim::from_projective_trace_lite(&trace)
                .expect("proj rcb claim");
        HintedMulTraceClaim::from_projective_rcb(&rcb).expect("hinted claim builds")
    }

    fn assert_columns_equal(expected: &[M31ColumnEval], actual: &[M31ColumnEval]) {
        assert_eq!(expected.len(), actual.len(), "column count");
        for (i, (expected, actual)) in expected.iter().zip(actual).enumerate() {
            assert_eq!(
                expected.domain, actual.domain,
                "domain mismatch at column {i}"
            );
            assert_eq!(
                expected.data.len(),
                actual.data.len(),
                "packed rows at column {i}"
            );
            for (row, (expected, actual)) in expected.data.iter().zip(&actual.data).enumerate() {
                assert_eq!(
                    expected.to_array(),
                    actual.to_array(),
                    "data mismatch at column {i}, packed row {row}"
                );
            }
        }
    }

    #[test]
    fn packed_hinted_mul_schedule_matches_scalar_writer() {
        let claim = synthetic_claim(37);
        assert_columns_equal(
            &gen_hinted_mul_schedule_columns_scalar(&claim),
            &gen_hinted_mul_schedule_columns_packed(&claim),
        );
    }

    #[test]
    fn packed_hinted_mul_base_matches_scalar_writer() {
        let claim = projective_claim();
        assert_columns_equal(
            &gen_hinted_mul_base_trace_scalar(&claim),
            &gen_hinted_mul_base_trace_packed(&claim),
        );
    }

    fn best_of(count: usize, mut f: impl FnMut()) -> std::time::Duration {
        (0..count)
            .map(|_| {
                let start = std::time::Instant::now();
                f();
                start.elapsed()
            })
            .min()
            .expect("count > 0")
    }

    #[test]
    #[ignore]
    fn hinted_mul_trace_writer_timing() {
        let claim = synthetic_claim(8192);
        let schedule_scalar = best_of(5, || {
            std::hint::black_box(gen_hinted_mul_schedule_columns_scalar(&claim));
        });
        let schedule_packed = best_of(5, || {
            std::hint::black_box(gen_hinted_mul_schedule_columns_packed(&claim));
        });
        let base_scalar = best_of(5, || {
            std::hint::black_box(gen_hinted_mul_base_trace_scalar(&claim));
        });
        let base_packed = best_of(5, || {
            std::hint::black_box(gen_hinted_mul_base_trace_packed(&claim));
        });
        eprintln!(
            "hinted_mul schedule scalar={schedule_scalar:?} packed={schedule_packed:?}; base scalar={base_scalar:?} packed={base_packed:?}"
        );
    }
}
