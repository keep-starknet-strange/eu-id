//! The vertical `keccak` component uses one trace row for each round boundary.
//! Each Keccak-f[1600] permutation uses 25 rows: the input state and the 24
//! post-round states.
//!
//! The component stacks the 25 state snapshots vertically. It uses `201` trace
//! columns (`perm_id + state[200]`), boundary flags and
//! per-round iota constants preprocessed with shape-encoded identifiers, and 2
//! pair-batched interaction columns. The committed width is 209 columns.
//!
//! ## LogUp wiring
//!
//! Row `25·p + r` holds permutation `p`'s state at boundary `r` (`state_0` is
//! the input; `state_r` for `r ≥ 1` is the post-round-`r−1` state):
//!
//! - `r == 0`: *require* (−) `KeccakStateRelation(perm_id, IN, state_0)`,
//!   served by the sponge's yield.
//! - `r == 24`: *yield* (+) `KeccakStateRelation(perm_id, OUT, state_24)`,
//!   consumed by the sponge's require.
//! - `r < 24`: *yield* (+) the round input link
//!   `KeccakRound(perm_id | IN | r | rc_r | state_r)`.
//! - `r > 0`: *require* (−) the previous round output link
//!   `KeccakRound(perm_id | OUT | r | 0 | state_r)`.
//!
//! The direction tag stops an input tuple from canceling an output tuple. The
//! wrapper therefore pins every round index, Iota constant, and boundary state
//! to its fixed schedule. All gates are preprocessed schedule flags, so padding
//! rows emit nothing and no trace enabler or cross-row mask is needed.

#![allow(non_snake_case)]

use num_traits::Zero;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
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
};

use crate::constants::{IOTA_RC, IOTA_RC_BYTE_INDICES, N_BYTES_IN_STATE, N_ROUNDS};
use crate::relations::{direction, KeccakRelations, KECCAK_ROUND_ARITY, KECCAK_STATE_ARITY};
use crate::utils::{circle_row_to_coset, col_eval, spread_u32, unspread_u32, ColEval};

/// Rows per permutation: the input state plus one row per round output.
pub const ROWS_PER_PERM: usize = N_ROUNDS + 1;

/// Schedule (preprocessed) columns:
/// `is_active | is_first | is_last | round_idx | rc[0,1,3,7]`.
pub const N_SCHEDULE_COLS: usize = 4 + IOTA_RC_BYTE_INDICES.len();

/// Trace columns: `perm_id | state[200]` (state in spread form).
pub const N_COLUMNS: usize = 1 + N_BYTES_IN_STATE;

/// Logup entries per row: round-link yield + round-link require + state IN
/// require + state OUT yield (each preprocessed-gated).
const N_LOGUP_ENTRIES: usize = 4;
const N_INTERACTION_COLUMNS: usize = SECURE_EXTENSION_DEGREE * N_LOGUP_ENTRIES.div_ceil(2);

pub const N_COMMITTED_COLUMNS: usize = N_COLUMNS + N_INTERACTION_COLUMNS;

// =============================================================================
// The preprocessed schedule depends only on the shape.
// =============================================================================

/// Schedule column identifier. It encodes `n_perms`, so two different
/// permutation counts never alias through tree-0 first-writer dedup, and the
/// id fully determines the column content.
fn schedule_id(n_perms: usize, name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("keccak_perm/{n_perms}/{name}"),
    }
}

/// The schedule preprocessed column ids, in commit order.
pub fn schedule_ids(n_perms: usize) -> Vec<PreProcessedColumnId> {
    let mut ids = vec![
        schedule_id(n_perms, "is_active"),
        schedule_id(n_perms, "is_first"),
        schedule_id(n_perms, "is_last"),
        schedule_id(n_perms, "round_idx"),
    ];
    for j in IOTA_RC_BYTE_INDICES {
        ids.push(schedule_id(n_perms, &format!("rc_{j}")));
    }
    ids
}

/// Generate the schedule preprocessed columns (commit order = [`schedule_ids`]).
pub fn gen_schedule_preprocessed(n_perms: usize) -> Vec<ColEval> {
    let claim = Claim { n_perms };
    let log_size = claim.log_size();
    let rows = 1usize << log_size;
    let n_active = n_perms * ROWS_PER_PERM;
    let m = M31::from_u32_unchecked;

    let scalar = |f: &dyn Fn(usize) -> u32| -> Vec<M31> {
        let mut col = vec![M31::zero(); rows];
        for (row, cell) in col.iter_mut().enumerate().take(n_active) {
            *cell = m(f(row % ROWS_PER_PERM));
        }
        col
    };

    let mut cols: Vec<Vec<M31>> = vec![
        scalar(&|_| 1),
        scalar(&|r| (r == 0) as u32),
        scalar(&|r| (r == N_ROUNDS) as u32),
        scalar(&|r| r as u32),
    ];
    for j in IOTA_RC_BYTE_INDICES {
        cols.push(scalar(&move |r| {
            spread_u32(IOTA_RC[r].to_le_bytes()[j] as u32)
        }));
    }
    debug_assert_eq!(cols.len(), N_SCHEDULE_COLS);
    cols.into_iter().map(|c| col_eval(log_size, c)).collect()
}

// =============================================================================
// Claim + trace generation.
// =============================================================================

/// One boundary row's committed values (spread state), kept for the
/// interaction phase.
pub struct RowLook {
    pub perm_id: M31,
    pub state: [M31; N_BYTES_IN_STATE],
}

pub struct InteractionClaimData {
    pub n_perms: usize,
    /// Active rows in coset order (`len == n_perms · ROWS_PER_PERM`).
    pub rows: Vec<RowLook>,
}

#[derive(Copy, Clone, Default, Serialize, Deserialize, Debug)]
pub struct Claim {
    pub n_perms: usize,
}

impl Claim {
    pub fn log_size(&self) -> u32 {
        ((self.n_perms * ROWS_PER_PERM) as u32)
            .next_power_of_two()
            .ilog2()
            .max(LOG_N_LANES)
    }

    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let ls = self.log_size();
        TreeVec::new(vec![
            vec![ls; N_SCHEDULE_COLS],
            vec![ls; N_COLUMNS],
            vec![ls; N_INTERACTION_COLUMNS],
        ])
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.n_perms as u64);
    }

    /// Build the boundary-row trace. `perm_inputs` are splatted per-permutation
    /// rows `[spread_state(200) | perm_id]` with lane 0 real (the sponge's
    /// request order. This matches [`crate::service::build_perm_witness`]).
    pub fn generate_trace(
        perm_inputs: &[[PackedM31; N_BYTES_IN_STATE + 1]],
    ) -> (Self, Vec<ColEval>, InteractionClaimData) {
        let n_perms = perm_inputs.len();
        let claim = Self { n_perms };
        let log_size = claim.log_size();
        let n_rows = 1usize << log_size;

        let per_permutation_rows: Vec<Vec<RowLook>> = perm_inputs
            .par_iter()
            .map(|prow| {
                let perm_id = prow[N_BYTES_IN_STATE].to_array()[0];
                // Lane 0 contains the real spread state. Keep byte and spread
                // forms while this permutation generates its boundary rows.
                let mut bytes = [0u8; N_BYTES_IN_STATE];
                let mut spread = [M31::zero(); N_BYTES_IN_STATE];
                for i in 0..N_BYTES_IN_STATE {
                    spread[i] = prow[i].to_array()[0];
                    bytes[i] = unspread_u32(spread[i].0) as u8;
                }
                let mut rows = Vec::with_capacity(ROWS_PER_PERM);
                rows.push(RowLook {
                    perm_id,
                    state: spread,
                });
                for round in 0..N_ROUNDS {
                    keccak_round_bytes(&mut bytes, round);
                    let state = std::array::from_fn(|i| M31::from(spread_u32(bytes[i] as u32)));
                    rows.push(RowLook { perm_id, state });
                }
                rows
            })
            .collect();
        let rows: Vec<RowLook> = per_permutation_rows.into_iter().flatten().collect();
        debug_assert_eq!(rows.len(), n_perms * ROWS_PER_PERM);

        let mut cols: Vec<Vec<M31>> = vec![vec![M31::zero(); n_rows]; N_COLUMNS];
        for (row_index, row) in rows.iter().enumerate() {
            cols[0][row_index] = row.perm_id;
            for i in 0..N_BYTES_IN_STATE {
                cols[1 + i][row_index] = row.state[i];
            }
        }
        let trace = cols.into_iter().map(|c| col_eval(log_size, c)).collect();

        (claim, trace, InteractionClaimData { n_perms, rows })
    }
}

/// One Keccak-f[1600] round over a byte-form state (scalar).
fn keccak_round_bytes(state: &mut [u8; N_BYTES_IN_STATE], round: usize) {
    let mut packed: [PackedM31; N_BYTES_IN_STATE] =
        std::array::from_fn(|i| PackedM31::from(M31::from(state[i] as u32)));
    crate::utils::keccak_f1600_round(&mut packed, round);
    for i in 0..N_BYTES_IN_STATE {
        state[i] = packed[i].to_array()[0].0 as u8;
    }
}

// ─────────────────────────────── Constraints ───────────────────────────────

#[derive(Clone)]
pub struct Eval {
    pub claim: Claim,
    pub relations: KeccakRelations,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.claim.log_size()
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let rel = &self.relations;
        let n = self.claim.n_perms;

        // The tree-0 root pins the preprocessed schedule.
        let is_active = eval.get_preprocessed_column(schedule_id(n, "is_active"));
        let is_first = eval.get_preprocessed_column(schedule_id(n, "is_first"));
        let is_last = eval.get_preprocessed_column(schedule_id(n, "is_last"));
        let round_idx = eval.get_preprocessed_column(schedule_id(n, "round_idx"));
        let rc: Vec<E::F> = IOTA_RC_BYTE_INDICES
            .iter()
            .map(|j| eval.get_preprocessed_column(schedule_id(n, &format!("rc_{j}"))))
            .collect();

        let perm_id = eval.next_trace_mask();
        let state: Vec<E::F> = (0..N_BYTES_IN_STATE)
            .map(|_| eval.next_trace_mask())
            .collect();

        // Use distinct direction tags so every round input and output must
        // match this fixed schedule. Without the tags, the two entries at an
        // intermediate boundary would cancel and leave its Iota constant free.
        let mut input_link: Vec<E::F> = vec![
            perm_id.clone(),
            E::F::from(BaseField::from(direction::IN)),
            round_idx.clone(),
        ];
        input_link.extend(rc.iter().cloned());
        input_link.extend(state.iter().cloned());
        debug_assert_eq!(input_link.len(), KECCAK_ROUND_ARITY);
        eval.add_to_relation(RelationEntry::base(
            &rel.keccak_round,
            is_active.clone() - is_last.clone(),
            &input_link,
        ));

        let mut output_link: Vec<E::F> = vec![
            perm_id.clone(),
            E::F::from(BaseField::from(direction::OUT)),
            round_idx,
        ];
        output_link.extend((0..IOTA_RC_BYTE_INDICES.len()).map(|_| E::F::zero()));
        output_link.extend(state.iter().cloned());
        debug_assert_eq!(output_link.len(), KECCAK_ROUND_ARITY);
        eval.add_to_relation(RelationEntry::base(
            &rel.keccak_round,
            -is_active + is_first.clone(),
            &output_link,
        ));

        // require (perm_id, IN, state_0) on r == 0.
        let mut in_tuple: Vec<E::F> = vec![perm_id.clone(), E::F::zero()];
        in_tuple.extend(state.iter().cloned());
        debug_assert_eq!(in_tuple.len(), KECCAK_STATE_ARITY);
        eval.add_to_relation(RelationEntry::base(&rel.keccak_state, -is_first, &in_tuple));

        // yield (perm_id, OUT, state_24) on r == 24.
        let mut out_tuple: Vec<E::F> = vec![perm_id, E::F::from(BaseField::from(direction::OUT))];
        out_tuple.extend(state.iter().cloned());
        eval.add_to_relation(RelationEntry::base(&rel.keccak_state, is_last, &out_tuple));

        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type Component = FrameworkComponent<Eval>;

// ─────────────────────────────── Interaction ───────────────────────────────

#[derive(Clone, Serialize, Deserialize, Debug)]
pub struct InteractionClaim {
    pub claimed_sum: SecureField,
}

impl InteractionClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}

/// The 4 per-row fractions in EXACTLY the AIR's emission order, pair-batched
/// (matching `finalize_logup_in_pairs`). Zero-multiplicity entries are
/// `(0, 1)`. This is sound because the pair constraint evaluates the symbolic
/// multiplicity (a preprocessed gate that IS zero there).
fn row_fracs(rel: &KeccakRelations, r: usize, row: &RowLook) -> [(SecureField, SecureField); 4] {
    let zero = SecureField::zero();
    let one = SecureField::from(M31::from(1u32));

    let round_link = |direction_tag: u32| {
        let mut link = [M31::zero(); KECCAK_ROUND_ARITY];
        link[0] = row.perm_id;
        link[1] = M31::from(direction_tag);
        link[2] = M31::from(r as u32);
        if direction_tag == direction::IN {
            for (slot, byte_index) in IOTA_RC_BYTE_INDICES.iter().enumerate() {
                link[3 + slot] =
                    M31::from(spread_u32(IOTA_RC[r].to_le_bytes()[*byte_index] as u32));
            }
        }
        link[3 + IOTA_RC_BYTE_INDICES.len()..].copy_from_slice(&row.state);
        link
    };
    let d_input: SecureField = rel.keccak_round.combine(&round_link(direction::IN));
    let d_output: SecureField = rel.keccak_round.combine(&round_link(direction::OUT));

    let f_input = if r < N_ROUNDS {
        (one, d_input)
    } else {
        (zero, one)
    };
    let f_output = if r > 0 { (-one, d_output) } else { (zero, one) };

    let state_tuple = |dir: u32| {
        let mut t = [M31::zero(); KECCAK_STATE_ARITY];
        t[0] = row.perm_id;
        t[1] = M31::from(dir);
        t[2..].copy_from_slice(&row.state);
        t
    };
    let f_in = if r == 0 {
        (-one, rel.keccak_state.combine(&state_tuple(direction::IN)))
    } else {
        (zero, one)
    };
    let f_out = if r == N_ROUNDS {
        (one, rel.keccak_state.combine(&state_tuple(direction::OUT)))
    } else {
        (zero, one)
    };

    [f_input, f_output, f_in, f_out]
}

/// Build the interaction trace: pair-batched columns matching
/// `finalize_logup_in_pairs` over the AIR's emission order.
pub fn generate_interaction_trace(
    rel: &KeccakRelations,
    data: &InteractionClaimData,
) -> (InteractionClaim, Vec<ColEval>) {
    let claim = Claim {
        n_perms: data.n_perms,
    };
    let log_size = claim.log_size();

    let fracs: Vec<[(SecureField, SecureField); 4]> = data
        .rows
        .iter()
        .enumerate()
        .map(|(coset, row)| row_fracs(rel, coset % ROWS_PER_PERM, row))
        .collect();
    let zero = SecureField::zero();
    let one = SecureField::from(M31::from(1u32));
    let entry = |coset: usize, e: usize| -> (SecureField, SecureField) {
        if coset < fracs.len() {
            fracs[coset][e]
        } else {
            (zero, one)
        }
    };

    let row_lookup = circle_row_to_coset(log_size);
    let n_vec_rows = 1usize << (log_size - LOG_N_LANES);
    let mut gen = LogupTraceGenerator::new(log_size);
    for k in 0..N_LOGUP_ENTRIES / 2 {
        let mut col = gen.new_col();
        for vr in 0..n_vec_rows {
            let mut num = [zero; N_LANES];
            let mut den = [one; N_LANES];
            for lane in 0..N_LANES {
                let coset = row_lookup[vr * N_LANES + lane];
                let (n0, d0) = entry(coset, 2 * k);
                let (n1, d1) = entry(coset, 2 * k + 1);
                num[lane] = n0 * d1 + n1 * d0;
                den[lane] = d0 * d1;
            }
            col.write_frac(vr, PackedQM31::from_array(num), PackedQM31::from_array(den));
        }
        col.finalize_col();
    }
    let (trace, claimed_sum) = gen.finalize_last();
    (InteractionClaim { claimed_sum }, trace)
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::One;

    use crate::relations::{
        KECCAK_ROUND_DIRECTION_INDEX, KECCAK_ROUND_INDEX_INDEX, KECCAK_ROUND_PERM_ID_INDEX,
        KECCAK_ROUND_RC_START, KECCAK_ROUND_STATE_START,
    };

    #[test]
    fn schedule_contains_the_live_round_binding_columns() {
        let ids = schedule_ids(3);
        assert_eq!(ids.len(), N_SCHEDULE_COLS);
        assert_eq!(gen_schedule_preprocessed(3).len(), N_SCHEDULE_COLS);
        assert!(ids.iter().any(|id| id.id.ends_with("/is_active")));
        assert!(ids.iter().any(|id| id.id.ends_with("/is_first")));
        assert!(ids.iter().any(|id| id.id.ends_with("/is_last")));
    }

    #[test]
    fn changed_intermediate_iota_constant_breaks_round_balance() {
        let relations = KeccakRelations::dummy();
        let row = RowLook {
            perm_id: M31::from(7_u32),
            state: [M31::zero(); N_BYTES_IN_STATE],
        };
        let round = 1;
        let [fixed_input, fixed_output, _, _] = row_fracs(&relations, round, &row);
        assert_eq!(fixed_input.0, SecureField::one());
        assert_eq!(fixed_output.0, -SecureField::one());

        let mut official_input = [M31::zero(); KECCAK_ROUND_ARITY];
        official_input[KECCAK_ROUND_PERM_ID_INDEX] = row.perm_id;
        official_input[KECCAK_ROUND_DIRECTION_INDEX] = M31::from(direction::IN);
        official_input[KECCAK_ROUND_INDEX_INDEX] = M31::from(round as u32);
        for (slot, byte_index) in IOTA_RC_BYTE_INDICES.iter().copied().enumerate() {
            official_input[KECCAK_ROUND_RC_START + slot] =
                M31::from(spread_u32(IOTA_RC[round].to_le_bytes()[byte_index] as u32));
        }
        official_input[KECCAK_ROUND_STATE_START..].copy_from_slice(&row.state);
        let official_denominator: SecureField = relations.keccak_round.combine(&official_input);
        assert_eq!(official_denominator, fixed_input.1);

        for slot in 0..IOTA_RC_BYTE_INDICES.len() {
            let mut changed_input = official_input;
            changed_input[KECCAK_ROUND_RC_START + slot] += M31::one();
            let changed_denominator: SecureField = relations.keccak_round.combine(&changed_input);
            let imbalance =
                fixed_input.0 / fixed_input.1 - SecureField::one() / changed_denominator;
            assert_ne!(
                imbalance,
                SecureField::zero(),
                "Iota byte slot {slot} must be bound"
            );
        }
    }

    #[test]
    fn omitted_iota_byte_lanes_are_always_zero() {
        for round_constant in IOTA_RC {
            let bytes = round_constant.to_le_bytes();
            for byte_index in [2, 4, 5, 6] {
                assert_eq!(bytes[byte_index], 0);
            }
        }
    }
}
