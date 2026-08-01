//! The carrier component proves complete Keccak-f[1600] chains.
//!
//! Each permutation uses one input row followed by 24 round-output rows. The
//! round arithmetic reads the previous carrier state and writes the current
//! state. The input and final rows connect to the sponge. A fixed table pins
//! all 25 positions and the Iota constant for each round. The service sends
//! all lookup fractions to the GKR proof.

#![allow(non_snake_case)]

use num_traits::{One, Zero};
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

use crate::constants::{
    IOTA_RC, N_BYTES_IN_STATE, N_BYTES_IN_U64, N_LANES_KECCAK, N_ROUNDS, RHO_OFFSETS, SQRT_N_LANES,
};
use crate::keccak;
use crate::keccak_round::{
    self, InteractionClaimData as RoundData, N_ANDNOT_LOOKUPS, N_SPLIT_C_ROT, N_SPLIT_LOOKUPS,
    N_XOR3_C, N_XOR3_THETA_APPLY,
};
use crate::relations::{direction, KeccakRelations};
use crate::utils::{circle_row_to_coset, col_eval, spread_u32, ColEval};

/// One input boundary row followed by one row for each Keccak round.
pub const ROWS_PER_PERMUTATION: usize = N_ROUNDS + 1;

pub const N_SCHEDULE_COLUMNS: usize = 6 + N_BYTES_IN_U64;
pub const N_CORE_COLUMNS: usize =
    N_BYTES_IN_STATE + keccak_round::ROUND_PRE_CHI_COLUMNS + N_ANDNOT_LOOKUPS;
pub const N_COLUMNS: usize = N_SCHEDULE_COLUMNS + N_CORE_COLUMNS;

pub const N_TOTAL_LOOKUPS: usize = 1 + 1 + (keccak_round::N_TOTAL_LOOKUPS - 2) + 1;

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

/// Data for the GKR leaves. Values use logical coset order.
pub struct InteractionData {
    pub log_size: u32,
    pub n_perms: usize,
    schedule: Vec<Vec<PackedM31>>,
    carrier: Vec<Vec<PackedM31>>,
    pub round: RoundData,
}

impl InteractionData {
    /// Test-only access to the separate GKR schedule source.
    #[doc(hidden)]
    pub fn schedule_mut(&mut self) -> &mut [Vec<PackedM31>] {
        &mut self.schedule
    }

    /// Test-only access to the separate GKR carrier source.
    #[doc(hidden)]
    pub fn carrier_mut(&mut self) -> &mut [Vec<PackedM31>] {
        &mut self.carrier
    }
}

/// The committed carrier trace and its separate GKR source.
pub struct Witness {
    pub claim: Claim,
    pub trace: Vec<ColEval>,
    pub interaction: InteractionData,
}

fn pack_columns(columns: &[Vec<M31>]) -> Vec<Vec<PackedM31>> {
    columns
        .iter()
        .map(|column| {
            column
                .chunks_exact(N_LANES)
                .map(|chunk| PackedM31::from_array(chunk.try_into().unwrap()))
                .collect()
        })
        .collect()
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
pub fn generate(boundaries: &keccak::InteractionClaimData) -> Witness {
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
    let (_, full_trace, mut round_data) = keccak_round::Claim::generate_trace(round_inputs, n_rows);

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

    let schedule = pack_columns(&columns[..N_SCHEDULE_COLUMNS]);
    let carrier = pack_columns(&columns[CARRIER_START..CARRIER_START + N_BYTES_IN_STATE]);
    let trace = columns
        .into_iter()
        .map(|column| col_eval(claim.log_size(), column))
        .collect();

    Witness {
        claim,
        trace,
        interaction: InteractionData {
            log_size: claim.log_size(),
            n_perms: claim.n_perms,
            schedule,
            carrier,
            round: round_data,
        },
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
    Andnot,
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

    let arithmetic_num = E::EF::from(round_active);
    collect_arithmetic(
        eval,
        &mut lookups,
        &state,
        &carrier,
        &current_rc,
        arithmetic_num,
    );

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

fn collect_arithmetic<E: EvalAtRow>(
    eval: &mut E,
    lookups: &mut Vec<Lookup<E>>,
    state: &[E::F; N_BYTES_IN_STATE],
    carrier: &[E::F; N_BYTES_IN_STATE],
    current_rc: &[E::F; N_BYTES_IN_U64],
    numerator: E::EF,
) {
    let S0: [[E::F; N_BYTES_IN_U64]; N_LANES_KECCAK] = std::array::from_fn(|lane| {
        std::array::from_fn(|byte| state[lane * N_BYTES_IN_U64 + byte].clone())
    });

    let mut C: [[E::F; N_BYTES_IN_U64]; SQRT_N_LANES] =
        std::array::from_fn(|_| std::array::from_fn(|_| E::F::zero()));
    for x in 0..SQRT_N_LANES {
        for byte in 0..N_BYTES_IN_U64 {
            let t = eval.next_trace_mask();
            push_xor3(
                lookups,
                &[
                    S0[x][byte].clone(),
                    S0[x + 5][byte].clone(),
                    S0[x + 10][byte].clone(),
                ],
                &t,
                numerator.clone(),
            );
            let c = eval.next_trace_mask();
            push_xor3(
                lookups,
                &[t, S0[x + 15][byte].clone(), S0[x + 20][byte].clone()],
                &c,
                numerator.clone(),
            );
            C[x][byte] = c;
        }
    }

    let Crot: [[E::F; N_BYTES_IN_U64]; SQRT_N_LANES] = std::array::from_fn(|x| {
        collect_rotation(
            eval,
            lookups,
            &C[(x + 1) % SQRT_N_LANES],
            63,
            numerator.clone(),
        )
    });

    let mut S: [[E::F; N_BYTES_IN_U64]; N_LANES_KECCAK] =
        std::array::from_fn(|_| std::array::from_fn(|_| E::F::zero()));
    for y in 0..SQRT_N_LANES {
        for x in 0..SQRT_N_LANES {
            let lane = x + 5 * y;
            let previous_x = (x + 4) % SQRT_N_LANES;
            for byte in 0..N_BYTES_IN_U64 {
                let result = eval.next_trace_mask();
                push_xor3(
                    lookups,
                    &[
                        S0[lane][byte].clone(),
                        C[previous_x][byte].clone(),
                        Crot[x][byte].clone(),
                    ],
                    &result,
                    numerator.clone(),
                );
                S[lane][byte] = result;
            }
        }
    }

    let mut B: [[E::F; N_BYTES_IN_U64]; N_LANES_KECCAK] =
        std::array::from_fn(|_| std::array::from_fn(|_| E::F::zero()));
    for x in 0..SQRT_N_LANES {
        for y in 0..SQRT_N_LANES {
            let offset = RHO_OFFSETS[x][y];
            let rotation = if offset == 0 { 0 } else { 64 - offset };
            let destination = 5 * y + ((2 * x + 3 * y) % SQRT_N_LANES);
            B[destination] =
                collect_rotation(eval, lookups, &S[x + 5 * y], rotation, numerator.clone());
        }
    }

    for y in 0..SQRT_N_LANES {
        for x in 0..SQRT_N_LANES {
            let a = 5 * x + y;
            let b1 = 5 * ((x + 1) % SQRT_N_LANES) + y;
            let b2 = 5 * ((x + 2) % SQRT_N_LANES) + y;
            let output_lane = x + 5 * y;
            for byte in 0..N_BYTES_IN_U64 {
                let andnot = eval.next_trace_mask();
                push_andnot(
                    lookups,
                    &B[b1][byte],
                    &B[b2][byte],
                    &andnot,
                    numerator.clone(),
                );
                let output = carrier[output_lane * N_BYTES_IN_U64 + byte].clone();
                let round_constant = if output_lane == 0 {
                    current_rc[byte].clone()
                } else {
                    E::F::zero()
                };
                push_xor3(
                    lookups,
                    &[B[a][byte].clone(), andnot, round_constant],
                    &output,
                    numerator.clone(),
                );
            }
        }
    }
}

fn push_xor3<E: EvalAtRow>(
    lookups: &mut Vec<Lookup<E>>,
    values: &[E::F; 3],
    output: &E::F,
    numerator: E::EF,
) {
    lookups.push(Lookup {
        kind: LookupKind::Xor3,
        num: numerator,
        tuple: vec![
            values[0].clone() + values[1].clone() + values[2].clone(),
            output.clone(),
        ],
    });
}

fn push_andnot<E: EvalAtRow>(
    lookups: &mut Vec<Lookup<E>>,
    b1: &E::F,
    b2: &E::F,
    output: &E::F,
    numerator: E::EF,
) {
    lookups.push(Lookup {
        kind: LookupKind::Andnot,
        num: numerator,
        tuple: vec![b1.clone() + b2.clone() + b2.clone(), output.clone()],
    });
}

fn collect_rotation<E: EvalAtRow>(
    eval: &mut E,
    lookups: &mut Vec<Lookup<E>>,
    input: &[E::F; N_BYTES_IN_U64],
    rotation: usize,
    numerator: E::EF,
) -> [E::F; N_BYTES_IN_U64] {
    let whole_bytes = rotation / 8;
    let bits = rotation % 8;
    let rotated: [E::F; N_BYTES_IN_U64] =
        std::array::from_fn(|index| input[(index + whole_bytes) % N_BYTES_IN_U64].clone());
    if bits == 0 {
        return rotated;
    }
    let four_pow_bits = M31::from(1u32 << (2 * bits));
    let four_pow_remaining = M31::from(1u32 << (2 * (8 - bits)));
    let high: [E::F; N_BYTES_IN_U64] = std::array::from_fn(|_| eval.next_trace_mask());
    let low: [E::F; N_BYTES_IN_U64] =
        std::array::from_fn(|index| rotated[index].clone() - high[index].clone() * four_pow_bits);
    for index in 0..N_BYTES_IN_U64 {
        lookups.push(Lookup {
            kind: LookupKind::Split(bits),
            num: numerator.clone(),
            tuple: vec![
                rotated[index].clone(),
                high[index].clone(),
                low[index].clone(),
            ],
        });
    }
    std::array::from_fn(|index| {
        high[index].clone() + low[(index + 1) % N_BYTES_IN_U64].clone() * four_pow_remaining
    })
}

pub(crate) struct Fractions {
    numerators: Vec<PackedQM31>,
    denominators: Vec<PackedQM31>,
    n_vector_rows: usize,
}

impl Fractions {
    fn new(n_vector_rows: usize) -> Self {
        let length = N_TOTAL_LOOKUPS * n_vector_rows;
        Self {
            numerators: Vec::with_capacity(length),
            denominators: Vec::with_capacity(length),
            n_vector_rows,
        }
    }

    fn push_slot(&mut self, numerator: Vec<PackedQM31>, denominator: Vec<PackedQM31>) {
        assert_eq!(numerator.len(), self.n_vector_rows);
        assert_eq!(denominator.len(), self.n_vector_rows);
        self.numerators.extend(numerator);
        self.denominators.extend(denominator);
    }

    pub(crate) fn n_vector_rows(&self) -> usize {
        self.n_vector_rows
    }

    pub(crate) fn n_slots(&self) -> usize {
        self.numerators.len() / self.n_vector_rows
    }

    pub(crate) fn numerators(&self) -> &[PackedQM31] {
        &self.numerators
    }

    pub(crate) fn denominators(&self) -> &[PackedQM31] {
        &self.denominators
    }

    pub(crate) fn slot(&self, slot: usize) -> (&[PackedQM31], &[PackedQM31]) {
        let start = slot * self.n_vector_rows;
        let end = start + self.n_vector_rows;
        (&self.numerators[start..end], &self.denominators[start..end])
    }
}

fn circle_order(values: &[PackedQM31], log_size: u32) -> Vec<PackedQM31> {
    let row_lookup = circle_row_to_coset(log_size);
    (0..values.len())
        .map(|vector_row| {
            PackedQM31::from_array(std::array::from_fn(|lane| {
                let coset = row_lookup[vector_row * N_LANES + lane];
                values[coset / N_LANES].to_array()[coset % N_LANES]
            }))
        })
        .collect()
}

fn push_dense_fraction<R: Relation<PackedM31, PackedQM31>>(
    fractions: &mut Fractions,
    relation: &R,
    lookup: &[[PackedM31; 2]],
    gate: &[PackedM31],
    log_size: u32,
) {
    let numerator = gate
        .iter()
        .copied()
        .map(PackedQM31::from)
        .collect::<Vec<_>>();
    let denominator = lookup[..gate.len()]
        .iter()
        .map(|tuple| relation.combine(tuple))
        .collect::<Vec<_>>();
    fractions.push_slot(
        circle_order(&numerator, log_size),
        circle_order(&denominator, log_size),
    );
}

pub(crate) fn build_fractions(relations: &KeccakRelations, data: &InteractionData) -> Fractions {
    let n_vector_rows = 1usize << (data.log_size - LOG_N_LANES);
    let schedule = &data.schedule;
    let carrier = &data.carrier;
    let round = &data.round.lookup_data;
    let mut fractions = Fractions::new(n_vector_rows);

    let header = &schedule[HEADER_COLUMN];
    let round_active = &schedule[ROUND_COLUMN];
    let final_round = &schedule[FINAL_COLUMN];
    let permutation = &schedule[PERMUTATION_COLUMN];
    let position = &schedule[POSITION_COLUMN];
    let round_constants: [&[PackedM31]; N_BYTES_IN_U64] =
        std::array::from_fn(|byte| schedule[ROUND_CONSTANT_START + byte].as_slice());

    let mut schedule_denominator = Vec::with_capacity(n_vector_rows);
    let mut schedule_numerator = Vec::with_capacity(n_vector_rows);
    let mut input_denominator = Vec::with_capacity(n_vector_rows);
    let mut input_numerator = Vec::with_capacity(n_vector_rows);
    for vector_row in 0..n_vector_rows {
        let active = header[vector_row] + round_active[vector_row];
        let mut tuple = vec![
            position[vector_row],
            header[vector_row],
            round_active[vector_row],
            final_round[vector_row],
        ];
        tuple.extend(round_constants.iter().map(|column| column[vector_row]));
        schedule_numerator.push(PackedQM31::from(active));
        schedule_denominator.push(relations.round_schedule.combine(&tuple));

        let mut endpoint = vec![
            permutation[vector_row],
            PackedM31::from(M31::from(direction::IN)),
        ];
        endpoint.extend(carrier.iter().map(|column| column[vector_row]));
        input_numerator.push(-PackedQM31::from(header[vector_row]));
        input_denominator.push(relations.keccak_state.combine(&endpoint));
    }
    fractions.push_slot(
        circle_order(&schedule_numerator, data.log_size),
        circle_order(&schedule_denominator, data.log_size),
    );
    fractions.push_slot(
        circle_order(&input_numerator, data.log_size),
        circle_order(&input_denominator, data.log_size),
    );

    let push_split = |fractions: &mut Fractions, lookup: &[[PackedM31; 4]]| {
        let shift = lookup[0][0].to_array()[0].0 as usize;
        let numerator = round_active
            .iter()
            .copied()
            .map(PackedQM31::from)
            .collect::<Vec<_>>();
        let denominator = lookup[..n_vector_rows]
            .iter()
            .map(|row| relations.split[shift - 1].combine(&[row[1], row[2], row[3]]))
            .collect::<Vec<_>>();
        fractions.push_slot(
            circle_order(&numerator, data.log_size),
            circle_order(&denominator, data.log_size),
        );
    };

    for lookup in &round.xor3[..N_XOR3_C] {
        push_dense_fraction(
            &mut fractions,
            &relations.xor3,
            lookup,
            round_active,
            data.log_size,
        );
    }
    for lookup in &round.split[..N_SPLIT_C_ROT] {
        push_split(&mut fractions, lookup);
    }
    for lookup in &round.xor3[N_XOR3_C..N_XOR3_C + N_XOR3_THETA_APPLY] {
        push_dense_fraction(
            &mut fractions,
            &relations.xor3,
            lookup,
            round_active,
            data.log_size,
        );
    }
    for lookup in &round.split[N_SPLIT_C_ROT..N_SPLIT_LOOKUPS] {
        push_split(&mut fractions, lookup);
    }
    for index in 0..N_ANDNOT_LOOKUPS {
        push_dense_fraction(
            &mut fractions,
            &relations.andnot,
            &round.andnot[index],
            round_active,
            data.log_size,
        );
        push_dense_fraction(
            &mut fractions,
            &relations.xor3,
            &round.xor3[CHI_CLOSE_LOOKUP_START + index],
            round_active,
            data.log_size,
        );
    }

    let mut output_numerator = Vec::with_capacity(n_vector_rows);
    let mut output_denominator = Vec::with_capacity(n_vector_rows);
    for vector_row in 0..n_vector_rows {
        let mut endpoint = vec![
            permutation[vector_row],
            PackedM31::from(M31::from(direction::OUT)),
        ];
        endpoint.extend(carrier.iter().map(|column| column[vector_row]));
        output_numerator.push(PackedQM31::from(final_round[vector_row]));
        output_denominator.push(relations.keccak_state.combine(&endpoint));
    }
    fractions.push_slot(
        circle_order(&output_numerator, data.log_size),
        circle_order(&output_denominator, data.log_size),
    );

    assert_eq!(fractions.n_slots(), N_TOTAL_LOOKUPS);
    fractions
}

/// Build the former columnar LogUp in tests. This is an independent reference
/// for the GKR claimed sum and batching order.
#[cfg(test)]
pub(crate) fn generate_interaction_trace(
    relations: &KeccakRelations,
    data: &InteractionData,
) -> (InteractionClaim, Vec<ColEval>) {
    const BATCH: usize = 4;
    let fractions = build_fractions(relations, data);
    let mut generator = LogupTraceGenerator::new(data.log_size);
    for first in (0..fractions.n_slots()).step_by(BATCH) {
        let last = (first + BATCH).min(fractions.n_slots());
        let mut column = generator.new_col();
        let (first_numerator, first_denominator) = fractions.slot(first);
        for vector_row in 0..fractions.n_vector_rows() {
            let mut numerator = first_numerator[vector_row];
            let mut denominator = first_denominator[vector_row];
            for slot in first + 1..last {
                let (next_numerator, next_denominator) = fractions.slot(slot);
                numerator = next_denominator[vector_row] * numerator
                    + next_numerator[vector_row] * denominator;
                denominator *= next_denominator[vector_row];
            }
            column.write_frac(vector_row, numerator, denominator);
        }
        column.finalize_col();
    }
    let (trace, claimed_sum) = generator.finalize_last();
    (InteractionClaim { claimed_sum }, trace)
}
