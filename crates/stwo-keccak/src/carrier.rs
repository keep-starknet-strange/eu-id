//! The carrier component proves complete Keccak-f[1600] chains.
//!
//! Each permutation uses one input row followed by 24 round-output rows. The
//! round arithmetic reads the previous carrier state and writes the current
//! state. The input and final rows connect to the sponge. A fixed table pins
//! all 25 positions and the Iota constant for each round. The service sends
//! all lookup fractions to the GKR proof.

#![allow(non_snake_case)]

use num_traits::{One, Zero};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use stwo::core::channel::Channel;
use stwo::core::fields::m31::{BaseField, M31};
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::core::pcs::TreeVec;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES, N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    ORIGINAL_TRACE_IDX,
};

use crate::constants::{IOTA_RC, N_BYTES_IN_STATE, N_BYTES_IN_U64, N_ROUNDS};
use crate::keccak;
use crate::keccak_round::{
    self, InteractionClaimData as RoundData, N_ANDNOT_LOOKUPS, N_XOR3_C, N_XOR3_THETA_APPLY,
};
use crate::relations::{direction, KeccakRelations};
use crate::utils::{circle_row_to_coset, col_eval, spread_u32, ColEval};

/// One input boundary row followed by one row for each Keccak round.
pub const ROWS_PER_PERMUTATION: usize = N_ROUNDS + 1;

pub const N_SCHEDULE_COLUMNS: usize = 6 + N_BYTES_IN_U64;
pub const N_CORE_COLUMNS: usize =
    N_BYTES_IN_STATE + keccak_round::ROUND_PRE_CHI_COLUMNS + N_ANDNOT_LOOKUPS;
pub const N_COLUMNS: usize = N_SCHEDULE_COLUMNS + N_CORE_COLUMNS;

pub const N_TOTAL_LOOKUPS: usize = 1 + 1 + keccak_round::N_ARITHMETIC_LOOKUPS + 1;

const HEADER_COLUMN: usize = 0;
const ROUND_COLUMN: usize = 1;
const FINAL_COLUMN: usize = 2;
const PERMUTATION_COLUMN: usize = 3;
const POSITION_COLUMN: usize = 4;
const END_COLUMN: usize = 5;
const ROUND_CONSTANT_START: usize = 6;
const CARRIER_START: usize = N_SCHEDULE_COLUMNS;

pub const ROUND_CONSTANT_COLUMN_START: usize = ROUND_CONSTANT_START;
pub const CARRIER_COLUMN_START: usize = CARRIER_START;

const CHI_CLOSE_LOOKUP_START: usize = N_XOR3_C + N_XOR3_THETA_APPLY;

const _: () = assert!(N_SCHEDULE_COLUMNS == 14);
const _: () = assert!(ROWS_PER_PERMUTATION == 25);
const _: () = assert!(IOTA_RC.len() == ROWS_PER_PERMUTATION);
const _: () = assert!(IOTA_RC[N_ROUNDS] == 0);
const _: () = assert!(N_CORE_COLUMNS == 896);
const _: () = assert!(N_COLUMNS == 910);
const _: () = assert!(N_TOTAL_LOOKUPS == 899);

#[derive(Clone, Copy, Default, Serialize, Deserialize, Debug)]
pub struct Claim {
    pub n_perms: usize,
}

impl Claim {
    pub fn log_size(&self) -> u32 {
        (self.n_perms * ROWS_PER_PERMUTATION)
            .next_power_of_two()
            .ilog2()
            .max(LOG_N_LANES)
    }

    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        TreeVec::new(vec![vec![], vec![self.log_size(); N_COLUMNS], vec![]])
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.n_perms as u64);
    }
}

/// Independent source for the carrier GKR leaves and coefficient replay.
///
/// The columns are an independently mutable deep clone created alongside the
/// committed trace in circle-domain order, before either source is used. The
/// clone lets the MLE tie-back detect changes to either source.
#[derive(Clone)]
pub struct InteractionData {
    pub log_size: u32,
    pub n_perms: usize,
    trace: Vec<ColEval>,
}

impl InteractionData {
    pub(crate) fn trace(&self) -> &[ColEval] {
        &self.trace
    }

    /// Test-only access to the independent GKR source.
    #[doc(hidden)]
    pub fn trace_mut(&mut self) -> &mut [ColEval] {
        &mut self.trace
    }
}

/// The committed carrier trace and its separate GKR source.
pub struct Witness {
    pub claim: Claim,
    pub trace: Vec<ColEval>,
    pub interaction: InteractionData,
    pub round: RoundData,
}

fn set_lane(value: &mut PackedM31, lane: usize, replacement: M31) {
    let mut lanes = value.to_array();
    lanes[lane] = replacement;
    *value = PackedM31::from_array(lanes);
}

fn pack_round_inputs(
    carrier: &[Vec<M31>],
    positions: &[usize],
    permutation_ids: &[M31],
) -> Vec<[PackedM31; N_BYTES_IN_STATE + 2]> {
    let n_rows = positions.len();
    let mut rows = Vec::with_capacity(n_rows / N_LANES);
    for vector_row in 0..n_rows / N_LANES {
        let mut packed = [PackedM31::zero(); N_BYTES_IN_STATE + 2];
        for lane in 0..N_LANES {
            let row = vector_row * N_LANES + lane;
            let previous_row = if row == 0 { n_rows - 1 } else { row - 1 };
            for byte in 0..N_BYTES_IN_STATE {
                set_lane(&mut packed[byte], lane, carrier[byte][previous_row]);
            }
            let round = match positions[row] {
                0 => 0,
                position if position <= N_ROUNDS => position - 1,
                _ => N_ROUNDS,
            };
            set_lane(&mut packed[N_BYTES_IN_STATE], lane, M31::from(round as u32));
            set_lane(
                &mut packed[N_BYTES_IN_STATE + 1],
                lane,
                permutation_ids[row],
            );
        }
        rows.push(packed);
    }
    rows
}

/// Build one carrier witness from scalar permutation boundary rows.
pub fn generate(boundaries: &keccak::BoundaryWitness) -> Witness {
    assert!(boundaries.n_perms > 0, "carrier needs one permutation");
    assert_eq!(
        boundaries.rows.len(),
        boundaries.n_perms * ROWS_PER_PERMUTATION,
        "carrier boundary count"
    );

    let claim = Claim {
        n_perms: boundaries.n_perms,
    };
    let n_active = claim.n_perms * ROWS_PER_PERMUTATION;
    let n_rows = 1usize << claim.log_size();

    let mut columns = vec![vec![M31::zero(); n_rows]; N_COLUMNS];
    let mut positions = vec![N_ROUNDS + 1; n_rows];
    let mut permutation_ids = vec![M31::zero(); n_rows];

    for row in 0..n_active {
        let permutation = row / ROWS_PER_PERMUTATION;
        let position = row % ROWS_PER_PERMUTATION;
        let boundary = &boundaries.rows[permutation * ROWS_PER_PERMUTATION + position];
        positions[row] = position;
        permutation_ids[row] = boundary.perm_id;
        columns[HEADER_COLUMN][row] = M31::from((position == 0) as u32);
        columns[ROUND_COLUMN][row] = M31::from((position > 0) as u32);
        columns[FINAL_COLUMN][row] = M31::from((position == N_ROUNDS) as u32);
        columns[PERMUTATION_COLUMN][row] = boundary.perm_id;
        columns[POSITION_COLUMN][row] = M31::from(position as u32);
        let round = position.saturating_sub(1);
        for byte in 0..N_BYTES_IN_U64 {
            columns[ROUND_CONSTANT_START + byte][row] =
                M31::from(spread_u32(IOTA_RC[round].to_le_bytes()[byte] as u32));
        }
        for byte in 0..N_BYTES_IN_STATE {
            columns[CARRIER_START + byte][row] = boundary.state[byte];
        }
    }
    columns[END_COLUMN][n_active] = M31::one();

    let round_inputs = pack_round_inputs(
        &columns[CARRIER_START..CARRIER_START + N_BYTES_IN_STATE],
        &positions,
        &permutation_ids,
    );
    let (full_trace, mut round_data) =
        keccak_round::generate_arithmetic_trace(round_inputs, n_rows);

    let pre_chi_start = keccak_round::ROUND_INPUT_TRACE_START + N_BYTES_IN_STATE;
    let pre_chi_target = CARRIER_START + N_BYTES_IN_STATE;
    let andnot_target = pre_chi_target + keccak_round::ROUND_PRE_CHI_COLUMNS;
    for row in 0..n_rows {
        let full_row = full_trace.row_at(row);
        for column in 0..keccak_round::ROUND_PRE_CHI_COLUMNS {
            columns[pre_chi_target + column][row] = full_row[pre_chi_start + column];
        }
        for byte in 0..N_ANDNOT_LOOKUPS {
            columns[andnot_target + byte][row] =
                full_row[keccak_round::ROUND_CHI_TRACE_START + 2 * byte];
        }
    }

    // The carrier forces each Chi output to the current carrier. On headers
    // and padding rows, this value can differ from the helper's round output.
    // The numerator is zero on these rows, but the GKR tie-back still binds the
    // denominator. Store the exact committed expression for every row.
    for row in 0..n_rows {
        let vector_row = row / N_LANES;
        let lane = row % N_LANES;
        for byte in 0..N_BYTES_IN_STATE {
            set_lane(
                &mut round_data.lookup_data.xor3[CHI_CLOSE_LOOKUP_START + byte][vector_row][1],
                lane,
                columns[CARRIER_START + byte][row],
            );
        }
    }

    let trace: Vec<ColEval> = columns
        .into_iter()
        .map(|column| col_eval(claim.log_size(), column))
        .collect();
    let gkr_trace = trace.clone();

    Witness {
        claim,
        trace,
        interaction: InteractionData {
            log_size: claim.log_size(),
            n_perms: claim.n_perms,
            trace: gkr_trace,
        },
        round: round_data,
    }
}

// =============================================================================
// Fixed schedule table.
// =============================================================================

pub const SCHEDULE_TABLE_LOG_SIZE: u32 = 5;
pub const N_SCHEDULE_TABLE_PREPROCESSED: usize = 5 + N_BYTES_IN_U64;
pub const N_SCHEDULE_TABLE_TRACE: usize = 1;
pub const N_SCHEDULE_TABLE_INTERACTION: usize = SECURE_EXTENSION_DEGREE;

fn schedule_table_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("keccak_carrier_schedule/{name}"),
    }
}

pub fn schedule_table_ids() -> Vec<PreProcessedColumnId> {
    let mut ids = ["valid", "position", "header", "round", "final"]
        .into_iter()
        .map(schedule_table_id)
        .collect::<Vec<_>>();
    for byte in 0..N_BYTES_IN_U64 {
        ids.push(schedule_table_id(&format!("round_constant_{byte}")));
    }
    ids
}

pub fn generate_schedule_table_preprocessed() -> Vec<ColEval> {
    let n_rows = 1usize << SCHEDULE_TABLE_LOG_SIZE;
    let value = |row: usize, column: usize| -> M31 {
        if row > N_ROUNDS {
            return M31::zero();
        }
        match column {
            0 => M31::one(),
            1 => M31::from(row as u32),
            2 => M31::from((row == 0) as u32),
            3 => M31::from((row > 0) as u32),
            4 => M31::from((row == N_ROUNDS) as u32),
            column => {
                let byte = column - 5;
                let round = row.saturating_sub(1);
                M31::from(spread_u32(IOTA_RC[round].to_le_bytes()[byte] as u32))
            }
        }
    };
    (0..N_SCHEDULE_TABLE_PREPROCESSED)
        .map(|column| {
            col_eval(
                SCHEDULE_TABLE_LOG_SIZE,
                (0..n_rows).map(|row| value(row, column)).collect(),
            )
        })
        .collect()
}

pub fn generate_schedule_multiplicity(n_perms: usize) -> Vec<ColEval> {
    let n_rows = 1usize << SCHEDULE_TABLE_LOG_SIZE;
    vec![col_eval(
        SCHEDULE_TABLE_LOG_SIZE,
        (0..n_rows)
            .map(|row| M31::from(if row <= N_ROUNDS { n_perms as u32 } else { 0 }))
            .collect(),
    )]
}

#[derive(Clone)]
pub struct ScheduleTableEval {
    pub n_perms: usize,
    pub relations: KeccakRelations,
}

pub type ScheduleTableComponent = FrameworkComponent<ScheduleTableEval>;

impl FrameworkEval for ScheduleTableEval {
    fn log_size(&self) -> u32 {
        SCHEDULE_TABLE_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let ids = schedule_table_ids();
        let values: [E::F; N_SCHEDULE_TABLE_PREPROCESSED] =
            std::array::from_fn(|column| eval.get_preprocessed_column(ids[column].clone()));
        let multiplicity = eval.next_trace_mask();
        eval.add_constraint(
            multiplicity.clone() - values[0].clone() * BaseField::from(self.n_perms as u32),
        );
        eval.add_to_relation(RelationEntry::new(
            &self.relations.round_schedule,
            -E::EF::from(multiplicity),
            &values[1..],
        ));
        eval.finalize_logup_in_pairs();
        eval
    }
}

#[derive(Clone, Serialize, Deserialize, Debug)]
pub struct InteractionClaim {
    pub claimed_sum: SecureField,
}

pub fn generate_schedule_interaction(
    relations: &KeccakRelations,
    n_perms: usize,
) -> (InteractionClaim, Vec<ColEval>) {
    let preprocessed = generate_schedule_table_preprocessed();
    let multiplicity = generate_schedule_multiplicity(n_perms);
    let n_vector_rows = 1usize << (SCHEDULE_TABLE_LOG_SIZE - LOG_N_LANES);
    let mut generator = LogupTraceGenerator::new(SCHEDULE_TABLE_LOG_SIZE);
    let mut column = generator.new_col();
    for vector_row in 0..n_vector_rows {
        let tuple = (1..N_SCHEDULE_TABLE_PREPROCESSED)
            .map(|index| preprocessed[index].values.data[vector_row])
            .collect::<Vec<_>>();
        column.write_frac(
            vector_row,
            -PackedQM31::from(multiplicity[0].values.data[vector_row]),
            relations.round_schedule.combine(&tuple),
        );
    }
    column.finalize_col();
    let (trace, claimed_sum) = generator.finalize_last();
    (InteractionClaim { claimed_sum }, trace)
}

// =============================================================================
// Carrier AIR and GKR leaves.
// =============================================================================

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LookupKind {
    Schedule,
    State,
    Xor3,
    Split(usize),
}

pub struct Lookup<E: EvalAtRow> {
    pub kind: LookupKind,
    pub num: E::EF,
    pub tuple: Vec<E::F>,
}

#[derive(Clone)]
pub struct Eval {
    pub claim: Claim,
}

pub type Component = FrameworkComponent<Eval>;

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.claim.log_size()
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let lookups = collect_lookups(&mut eval, self.claim.n_perms);
        debug_assert_eq!(lookups.len(), N_TOTAL_LOOKUPS);
        eval
    }
}

pub fn collect_lookups<E: EvalAtRow>(eval: &mut E, n_perms: usize) -> Vec<Lookup<E>> {
    let header_mask = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [-1, 0]);
    let round_mask = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [-1, 0]);
    let final_mask = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [-1, 0]);
    let permutation_mask = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [-1, 0]);
    let position_mask = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [-1, 0]);
    let end_mask = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [-1, 0]);
    let round_constant_masks: [[E::F; 2]; N_BYTES_IN_U64] =
        std::array::from_fn(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [-1, 0]));

    let header = header_mask[1].clone();
    let round_active = round_mask[1].clone();
    let final_round = final_mask[1].clone();
    let permutation = permutation_mask[1].clone();
    let position = position_mask[1].clone();
    let end = end_mask[1].clone();
    let active = header.clone() + round_active.clone();
    let previous_active = header_mask[0].clone() + round_mask[0].clone();
    let one = E::F::one();

    for flag in [
        header.clone(),
        round_active.clone(),
        final_round.clone(),
        end.clone(),
    ] {
        eval.add_constraint(flag.clone() * (one.clone() - flag));
    }
    eval.add_constraint(
        header.clone()
            - active.clone() * (one.clone() - previous_active.clone() + final_mask[0].clone()),
    );
    eval.add_constraint(
        position.clone() - round_active.clone() * (position_mask[0].clone() + one.clone()),
    );
    eval.add_constraint(
        permutation.clone()
            - round_active.clone() * permutation_mask[0].clone()
            - header.clone() * (permutation_mask[0].clone() + final_mask[0].clone()),
    );
    eval.add_constraint(end.clone() - previous_active * (one.clone() - active.clone()));
    eval.add_constraint(end.clone() * (final_mask[0].clone() - one.clone()));
    eval.add_constraint(
        end.clone()
            * (permutation_mask[0].clone() - E::F::from(BaseField::from((n_perms - 1) as u32))),
    );
    let inactive = one - active.clone();
    eval.add_constraint(inactive.clone() * permutation.clone());
    eval.add_constraint(inactive.clone() * position.clone());
    eval.add_constraint(inactive.clone() * final_round.clone());

    let current_rc: [E::F; N_BYTES_IN_U64] =
        std::array::from_fn(|index| round_constant_masks[index][1].clone());
    for value in &current_rc {
        eval.add_constraint(inactive.clone() * value.clone());
    }

    let mut lookups = Vec::with_capacity(N_TOTAL_LOOKUPS);
    let mut schedule_tuple = vec![
        position,
        header.clone(),
        round_active.clone(),
        final_round.clone(),
    ];
    schedule_tuple.extend(current_rc.iter().cloned());
    lookups.push(Lookup {
        kind: LookupKind::Schedule,
        num: E::EF::from(active),
        tuple: schedule_tuple,
    });

    let carrier_masks: [[E::F; 2]; N_BYTES_IN_STATE] =
        std::array::from_fn(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [-1, 0]));
    let state: [E::F; N_BYTES_IN_STATE] =
        std::array::from_fn(|index| carrier_masks[index][0].clone());
    let carrier: [E::F; N_BYTES_IN_STATE] =
        std::array::from_fn(|index| carrier_masks[index][1].clone());

    let mut input_endpoint = vec![
        permutation.clone(),
        E::F::from(BaseField::from(direction::IN)),
    ];
    input_endpoint.extend(carrier.iter().cloned());
    lookups.push(Lookup {
        kind: LookupKind::State,
        num: -E::EF::from(header),
        tuple: input_endpoint,
    });

    let arithmetic = keccak_round::collect_arithmetic_lookups(
        eval,
        &state,
        &carrier,
        &current_rc,
        E::EF::from(round_active),
    );
    lookups.extend(arithmetic.into_iter().map(|lookup| Lookup {
        kind: match lookup.kind {
            // The andnot lookup retargets onto the xor3 relation/table (see
            // `keccak_round::write_andnot`); no separate `LookupKind` needed.
            keccak_round::ArithmeticLookupKind::Xor3
            | keccak_round::ArithmeticLookupKind::Andnot => LookupKind::Xor3,
            keccak_round::ArithmeticLookupKind::Split(shift) => LookupKind::Split(shift),
        },
        num: lookup.numerator,
        tuple: lookup.tuple,
    }));

    let mut output_endpoint = vec![permutation, E::F::from(BaseField::from(direction::OUT))];
    output_endpoint.extend(carrier);
    lookups.push(Lookup {
        kind: LookupKind::State,
        num: E::EF::from(final_round),
        tuple: output_endpoint,
    });

    debug_assert_eq!(lookups.len(), N_TOTAL_LOOKUPS);
    lookups
}

pub(crate) struct Fractions {
    numerators: Vec<PackedM31>,
    denominators: Vec<PackedQM31>,
    n_vector_rows: usize,
}

impl Fractions {
    fn new(n_vector_rows: usize) -> Self {
        let padded_length = N_TOTAL_LOOKUPS.next_power_of_two() * n_vector_rows;
        Self {
            // These allocations become the padded GKR input columns.
            numerators: Vec::with_capacity(padded_length),
            denominators: Vec::with_capacity(padded_length),
            n_vector_rows,
        }
    }

    pub(crate) fn n_vector_rows(&self) -> usize {
        self.n_vector_rows
    }

    pub(crate) fn n_slots(&self) -> usize {
        self.numerators.len() / self.n_vector_rows
    }

    pub(crate) fn numerators(&self) -> &[PackedM31] {
        &self.numerators
    }

    pub(crate) fn denominators(&self) -> &[PackedQM31] {
        &self.denominators
    }

    #[cfg(test)]
    pub(crate) fn denominator_capacity(&self) -> usize {
        self.denominators.capacity()
    }

    #[cfg(test)]
    pub(crate) fn slot(&self, slot: usize) -> (&[PackedM31], &[PackedQM31]) {
        let start = slot * self.n_vector_rows;
        let end = start + self.n_vector_rows;
        (&self.numerators[start..end], &self.denominators[start..end])
    }

    pub(crate) fn into_parts(self) -> (Vec<PackedM31>, Vec<PackedQM31>) {
        (self.numerators, self.denominators)
    }
}

#[derive(Clone, Copy)]
struct PreviousPackedRow {
    sources: [usize; 2],
    source_count: usize,
    lanes: [(usize, usize); N_LANES],
}

fn previous_packed_rows(log_size: u32) -> Vec<PreviousPackedRow> {
    let n_rows = 1usize << log_size;
    let row_lookup = circle_row_to_coset(log_size);
    let mut coset_to_row = vec![0; n_rows];
    for (row, coset) in row_lookup.iter().copied().enumerate() {
        coset_to_row[coset] = row;
    }

    (0..n_rows / N_LANES)
        .map(|vector_row| {
            let mut sources = [usize::MAX; 2];
            let mut source_count = 0;
            let lanes = std::array::from_fn(|lane| {
                let row = vector_row * N_LANES + lane;
                let previous_coset = (row_lookup[row] + n_rows - 1) % n_rows;
                let previous_row = coset_to_row[previous_coset];
                let packed_row = previous_row / N_LANES;
                let source = sources[..source_count]
                    .iter()
                    .position(|candidate| *candidate == packed_row)
                    .unwrap_or_else(|| {
                        assert!(source_count < sources.len());
                        sources[source_count] = packed_row;
                        source_count += 1;
                        source_count - 1
                    });
                (source, previous_row % N_LANES)
            });
            PreviousPackedRow {
                sources,
                source_count,
                lanes,
            }
        })
        .collect()
}

struct TraceRowEvaluator<'a> {
    trace: &'a [ColEval],
    vector_row: usize,
    previous: PreviousPackedRow,
    column: usize,
}

impl TraceRowEvaluator<'_> {
    fn previous_value(&self, column: &ColEval) -> PackedM31 {
        let sources: [[M31; N_LANES]; 2] = std::array::from_fn(|source| {
            if source < self.previous.source_count {
                column.values.data[self.previous.sources[source]].to_array()
            } else {
                [M31::zero(); N_LANES]
            }
        });
        PackedM31::from_array(std::array::from_fn(|lane| {
            let (source, source_lane) = self.previous.lanes[lane];
            sources[source][source_lane]
        }))
    }
}

impl EvalAtRow for TraceRowEvaluator<'_> {
    type F = PackedM31;
    type EF = PackedQM31;

    fn next_interaction_mask<const N: usize>(
        &mut self,
        interaction: usize,
        offsets: [isize; N],
    ) -> [Self::F; N] {
        assert_eq!(interaction, ORIGINAL_TRACE_IDX);
        let column = &self.trace[self.column];
        self.column += 1;
        offsets.map(|offset| match offset {
            -1 => self.previous_value(column),
            0 => column.values.data[self.vector_row],
            _ => panic!("unsupported carrier mask offset {offset}"),
        })
    }

    fn add_constraint<G>(&mut self, _constraint: G)
    where
        Self::EF: std::ops::Mul<G, Output = Self::EF> + From<G>,
    {
    }

    fn combine_ef(_values: [Self::F; SECURE_EXTENSION_DEGREE]) -> Self::EF {
        unreachable!("the carrier lookup replay reads base-trace masks only")
    }
}

fn replay_row<'a>(
    data: &'a InteractionData,
    previous: PreviousPackedRow,
    vector_row: usize,
) -> Vec<Lookup<TraceRowEvaluator<'a>>> {
    let mut evaluator = TraceRowEvaluator {
        trace: data.trace(),
        vector_row,
        previous,
        column: 0,
    };
    let lookups = collect_lookups(&mut evaluator, data.n_perms);
    assert_eq!(evaluator.column, N_COLUMNS);
    assert_eq!(lookups.len(), N_TOTAL_LOOKUPS);
    lookups
}

fn lookup_denominator(
    relations: &KeccakRelations,
    lookup: &Lookup<TraceRowEvaluator<'_>>,
) -> PackedQM31 {
    let denominator: PackedQM31 = match lookup.kind {
        LookupKind::Schedule => relations.round_schedule.combine(&lookup.tuple),
        LookupKind::State => relations.keccak_state.combine(&lookup.tuple),
        LookupKind::Xor3 => relations.xor3.combine(&lookup.tuple),
        LookupKind::Split(shift) => relations.split[shift - 1].combine(&lookup.tuple),
    };
    normalize_denominator(denominator)
}

fn normalize_denominator(denominator: PackedQM31) -> PackedQM31 {
    PackedQM31::from_array(denominator.to_array())
}

fn base_numerator(numerator: PackedQM31) -> PackedM31 {
    let [base, second, third, fourth] = numerator.into_packed_m31s();
    assert!(
        second.is_zero() && third.is_zero() && fourth.is_zero(),
        "carrier lookup numerator must be in the base field"
    );
    PackedM31::from_array(base.to_array())
}

pub(crate) fn build_fractions(relations: &KeccakRelations, data: &InteractionData) -> Fractions {
    assert_eq!(data.trace().len(), N_COLUMNS);
    let n_vector_rows = 1usize << (data.log_size - LOG_N_LANES);
    let previous = previous_packed_rows(data.log_size);
    let mut fractions = Fractions::new(n_vector_rows);
    let active_length = N_TOTAL_LOOKUPS * n_vector_rows;
    fractions
        .numerators
        .resize(active_length, PackedM31::zero());
    fractions
        .denominators
        .resize(active_length, PackedQM31::zero());
    for vector_row in 0..n_vector_rows {
        for (slot, lookup) in replay_row(data, previous[vector_row], vector_row)
            .into_iter()
            .enumerate()
        {
            let index = slot * n_vector_rows + vector_row;
            fractions.numerators[index] = base_numerator(lookup.num);
            fractions.denominators[index] = lookup_denominator(relations, &lookup);
        }
    }

    assert_eq!(fractions.n_slots(), N_TOTAL_LOOKUPS);
    fractions
}

/// Replay the independent GKR source after GKR and build the folded column.
pub(crate) fn build_folded_coefficients(
    relations: &KeccakRelations,
    data: &InteractionData,
    delta: SecureField,
    eq_ws: &[SecureField],
) -> Vec<PackedQM31> {
    assert_eq!(data.trace().len(), N_COLUMNS);
    assert!(eq_ws.len() >= N_TOTAL_LOOKUPS);
    let n_vector_rows = 1usize << (data.log_size - LOG_N_LANES);
    let previous = previous_packed_rows(data.log_size);
    let weights = eq_ws[..N_TOTAL_LOOKUPS]
        .iter()
        .copied()
        .map(PackedQM31::broadcast)
        .collect::<Vec<_>>();
    let delta = PackedQM31::broadcast(delta);

    (0..n_vector_rows)
        .into_par_iter()
        .map(|vector_row| {
            replay_row(data, previous[vector_row], vector_row)
                .into_iter()
                .enumerate()
                .fold(PackedQM31::zero(), |sum, (slot, lookup)| {
                    let denominator = lookup_denominator(relations, &lookup);
                    let numerator = PackedQM31::from(base_numerator(lookup.num));
                    sum + weights[slot] * (delta * numerator + denominator)
                })
        })
        .collect()
}

#[cfg(test)]
mod replay_tests {
    use stwo::prover::backend::simd::column::BaseColumn;
    use stwo::prover::backend::Column;

    use super::*;

    #[test]
    fn predecessor_map_matches_every_scalar_row() {
        for log_size in LOG_N_LANES..=18 {
            let n_rows = 1usize << log_size;
            let row_to_coset = circle_row_to_coset(log_size);
            let mut coset_to_row = vec![0; n_rows];
            for (row, coset) in row_to_coset.iter().copied().enumerate() {
                coset_to_row[coset] = row;
            }

            let maps = previous_packed_rows(log_size);
            for (vector_row, map) in maps.iter().enumerate() {
                assert!((1..=2).contains(&map.source_count));
                for lane in 0..N_LANES {
                    let row = vector_row * N_LANES + lane;
                    let expected = coset_to_row[(row_to_coset[row] + n_rows - 1) % n_rows];
                    let (source, source_lane) = map.lanes[lane];
                    let actual = map.sources[source] * N_LANES + source_lane;
                    assert_eq!(
                        actual, expected,
                        "predecessor changed at log size {log_size}, domain row {row}"
                    );
                }
            }
        }
    }

    #[test]
    fn gkr_source_is_an_exact_independent_trace_clone() {
        let mut inputs = vec![[PackedM31::zero(); N_BYTES_IN_STATE + 1]; 2];
        for (permutation, input) in inputs.iter_mut().enumerate() {
            input[N_BYTES_IN_STATE] = PackedM31::from(M31::from(permutation as u32));
        }
        let boundaries = keccak::generate_boundary_witness(&inputs);
        let mut witness = generate(&boundaries);
        assert_eq!(witness.trace.len(), N_COLUMNS);
        assert_eq!(witness.interaction.trace().len(), N_COLUMNS);

        for (committed, gkr) in witness.trace.iter().zip(witness.interaction.trace()) {
            assert_ne!(committed.values.data.as_ptr(), gkr.values.data.as_ptr());
            assert_eq!(committed.values.to_cpu(), gkr.values.to_cpu());
        }

        let committed = witness.trace[0].values.at(0);
        witness.interaction.trace_mut()[0]
            .values
            .set(0, committed + M31::one());
        assert_eq!(witness.trace[0].values.at(0), committed);
        assert_ne!(witness.interaction.trace()[0].values.at(0), committed);
    }

    #[test]
    fn replay_normalizes_zero_without_changing_nonzero_values() {
        let raw_zero = -PackedM31::zero();
        let raw_column = BaseColumn::from_simd(vec![raw_zero]);
        assert_eq!(raw_column.as_slice()[0], M31(2_147_483_647));

        let normalized_numerator = base_numerator(PackedQM31::from(raw_zero));
        let normalized_column = BaseColumn::from_simd(vec![normalized_numerator]);
        assert_eq!(normalized_column.as_slice()[0], M31::zero());

        let raw_denominator = PackedQM31::from_packed_m31s([
            raw_zero,
            PackedM31::one(),
            PackedM31::zero(),
            PackedM31::zero(),
        ]);
        let [first, second, third, fourth] =
            normalize_denominator(raw_denominator).into_packed_m31s();
        assert_eq!(
            BaseColumn::from_simd(vec![first]).as_slice()[0],
            M31::zero()
        );
        assert_eq!(
            BaseColumn::from_simd(vec![second]).as_slice()[0],
            M31::one()
        );
        assert_eq!(
            BaseColumn::from_simd(vec![third]).as_slice()[0],
            M31::zero()
        );
        assert_eq!(
            BaseColumn::from_simd(vec![fourth]).as_slice()[0],
            M31::zero()
        );

        let tampered = normalize_denominator(raw_denominator + PackedQM31::one());
        assert_ne!(
            tampered.to_array(),
            normalize_denominator(raw_denominator).to_array(),
            "normalization must not erase a nonzero field change"
        );
    }
}
