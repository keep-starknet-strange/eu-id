//! The `keccak` component: one trace row proves one full Keccak-f[1600]
//! permutation as a chain of 24 `keccak_round` links.
//!
//! Ported from falcon-air `src/{trace,air,interaction}/keccak.rs`, with the
//! bare 200-byte state relation replaced by the interface
//! [`crate::relations::KeccakStateRelation`] keyed on `(perm_id, direction)`
//! so the sponge can request permutations by id in any order.
//!
//! ## LogUp wiring
//!
//! - *require* (−) `KeccakStateRelation(perm_id, IN, state_0)` — served by the
//!   sponge's yield.
//! - *yield* (+) `KeccakStateRelation(perm_id, OUT, state_24)` — consumed by
//!   the sponge's require.
//! - for each round `t`: *yield* (+) the round's input link
//!   `KeccakRound(rc_t | state_t)` and *require* (−) its output link
//!   `KeccakRound(rc_{t+1} | state_{t+1})`. These cancel the `keccak_round`
//!   component, which requires its input link and yields its output link.

#![allow(non_snake_case)]

use num_traits::{One, Zero};
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, ParallelIterator};
use serde::{Deserialize, Serialize};
use stwo::core::channel::Channel;
use stwo::core::fields::m31::{BaseField, M31};
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::core::pcs::TreeVec;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::BackendForChannel;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo_air_utils::trace::component_trace::ComponentTrace;
use stwo_air_utils_derive::{IterMut, ParIterMut, Uninitialized};
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
};

use crate::constants::{IOTA_RC, N_BYTES_IN_STATE, N_BYTES_IN_U64, N_ROUNDS};
use crate::relations::{direction, KeccakRelations};
use crate::utils::{keccak_f1600_round, spread_u32, unspread_u32, Enabler};

const N_STATE_LOOKUPS: usize = 2; // (perm_id,IN,state0) and (perm_id,OUT,state24)
const N_ROUND_LINK_LOOKUPS: usize = 2 * N_ROUNDS;

const ROUND_LINK_ARITY: usize = N_BYTES_IN_STATE + N_BYTES_IN_U64;
const STATE_ARITY: usize = 2 + N_BYTES_IN_STATE;

// enabler + perm_id + 25 state snapshots (initial + 24 post-round states).
const N_COLUMNS: usize = 2 + (N_ROUNDS + 1) * N_BYTES_IN_STATE;
const N_INTERACTION_COLUMNS: usize =
    SECURE_EXTENSION_DEGREE * (N_STATE_LOOKUPS + N_ROUND_LINK_LOOKUPS).div_ceil(2);

pub const N_COMMITTED_COLUMNS: usize = N_COLUMNS + N_INTERACTION_COLUMNS;

pub struct InteractionClaimData {
    pub lookup_data: LookupData,
    pub non_padded_length: usize,
}

#[derive(Uninitialized, IterMut, ParIterMut)]
pub struct LookupData {
    pub state: [Vec<[PackedM31; STATE_ARITY]>; N_STATE_LOOKUPS],
    pub round_link: [Vec<[PackedM31; ROUND_LINK_ARITY]>; N_ROUND_LINK_LOOKUPS],
}

#[derive(Copy, Clone, Default, Serialize, Deserialize, Debug)]
pub struct Claim {
    pub log_size: u32,
}

impl Claim {
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        TreeVec::new(vec![
            vec![],
            vec![self.log_size; N_COLUMNS],
            vec![self.log_size; N_INTERACTION_COLUMNS],
        ])
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    /// Build the permutation trace. Input rows are `[state(200) | perm_id]`.
    pub fn generate_trace(
        mut input: Vec<[PackedM31; N_BYTES_IN_STATE + 1]>,
        invocations: usize,
    ) -> (Self, ComponentTrace<N_COLUMNS>, InteractionClaimData)
    where
        SimdBackend: BackendForChannel<Blake2sMerkleChannel>,
    {
        let log_size = std::cmp::max(invocations.next_power_of_two().ilog2(), LOG_N_LANES);
        input.resize(1 << (log_size - LOG_N_LANES), [PackedM31::zero(); N_BYTES_IN_STATE + 1]);
        let enabler = Enabler::new(invocations);

        let (mut trace, mut lookup_data) = unsafe {
            (
                ComponentTrace::<N_COLUMNS>::uninitialized(log_size),
                LookupData::uninitialized(log_size - LOG_N_LANES),
            )
        };

        (
            trace.par_iter_mut(),
            input.into_par_iter(),
            lookup_data.par_iter_mut(),
        )
            .into_par_iter()
            .enumerate()
            .for_each(|(row_index, (row, input, ld))| {
                let mut col = 0usize;
                *row[col] = enabler.packed_at(row_index);
                col += 1;
                let perm_id = input[N_BYTES_IN_STATE];
                *row[col] = perm_id;
                col += 1;

                // Input state is committed in spread form. Keep a parallel
                // byte-form working copy for the native round; commit/link spread.
                let mut S_spread: [PackedM31; N_BYTES_IN_STATE] =
                    input[..N_BYTES_IN_STATE].try_into().unwrap();
                let mut S_bytes = unspread_state(&S_spread);
                for x in &S_spread {
                    *row[col] = *x;
                    col += 1;
                }

                // require (perm_id, IN, state0)
                *ld.state[0] = state_tuple(perm_id, direction::IN, &S_spread);

                for round in 0..N_ROUNDS {
                    *ld.round_link[2 * round] = round_link_tuple(IOTA_RC[round], &S_spread);
                    keccak_f1600_round(&mut S_bytes, round);
                    S_spread = spread_state(&S_bytes);
                    for x in &S_spread {
                        *row[col] = *x;
                        col += 1;
                    }
                    *ld.round_link[2 * round + 1] = round_link_tuple(IOTA_RC[round + 1], &S_spread);
                    if round == N_ROUNDS - 1 {
                        *ld.state[1] = state_tuple(perm_id, direction::OUT, &S_spread);
                    }
                }
            });

        let claim = Self { log_size };
        (
            claim,
            trace,
            InteractionClaimData {
                lookup_data,
                non_padded_length: invocations,
            },
        )
    }
}

fn state_tuple(
    perm_id: PackedM31,
    dir: u32,
    state: &[PackedM31; N_BYTES_IN_STATE],
) -> [PackedM31; STATE_ARITY] {
    let mut out = [PackedM31::zero(); STATE_ARITY];
    out[0] = perm_id;
    out[1] = PackedM31::from(M31::from(dir));
    out[2..].copy_from_slice(state);
    out
}

/// The round-link tuple: `(spread(rc)[8], spread_state[200])`. Both the rc and
/// the state are carried in spread form to match `keccak_round`.
fn round_link_tuple(rc: u64, state: &[PackedM31; N_BYTES_IN_STATE]) -> [PackedM31; ROUND_LINK_ARITY] {
    let mut out = [PackedM31::zero(); ROUND_LINK_ARITY];
    for (i, b) in rc.to_le_bytes().iter().enumerate() {
        out[i] = PackedM31::from(M31::from(spread_u32(*b as u32)));
    }
    out[N_BYTES_IN_U64..].copy_from_slice(state);
    out
}

/// Unspread a committed spread state into byte form (per SIMD lane).
fn unspread_state(s: &[PackedM31; N_BYTES_IN_STATE]) -> [PackedM31; N_BYTES_IN_STATE] {
    std::array::from_fn(|i| {
        let a = s[i].to_array();
        PackedM31::from_array(std::array::from_fn(|l| M31::from(unspread_u32(a[l].0))))
    })
}

/// Spread a byte-form state into committed spread form (per SIMD lane).
fn spread_state(s: &[PackedM31; N_BYTES_IN_STATE]) -> [PackedM31; N_BYTES_IN_STATE] {
    std::array::from_fn(|i| {
        let a = s[i].to_array();
        PackedM31::from_array(std::array::from_fn(|l| M31::from(spread_u32(a[l].0))))
    })
}

// ─────────────────────────────── Constraints ───────────────────────────────

#[derive(Clone)]
pub struct Eval {
    pub claim: Claim,
    pub relations: KeccakRelations,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let rel = &self.relations;
        let enabler = eval.next_trace_mask();
        eval.add_constraint(enabler.clone() * (E::F::one() - enabler.clone()));
        let en = E::EF::from(enabler);
        let perm_id = eval.next_trace_mask();

        let mut S: [E::F; N_BYTES_IN_STATE] = std::array::from_fn(|_| eval.next_trace_mask());

        // require (perm_id, IN, state0)
        let mut in_tuple: Vec<E::F> = vec![perm_id.clone(), E::F::zero()];
        in_tuple.extend(S.iter().cloned());
        eval.add_to_relation(RelationEntry::new(&rel.keccak_state, -en.clone(), &in_tuple));

        for round in 0..N_ROUNDS {
            // yield input link of this round
            let link_in = round_link_expr::<E>(IOTA_RC[round], &S);
            eval.add_to_relation(RelationEntry::new(&rel.keccak_round, en.clone(), &link_in));

            // next state is witnessed (proven correct by the keccak_round comp)
            let next: [E::F; N_BYTES_IN_STATE] = std::array::from_fn(|_| eval.next_trace_mask());
            let link_out = round_link_expr::<E>(IOTA_RC[round + 1], &next);
            eval.add_to_relation(RelationEntry::new(&rel.keccak_round, -en.clone(), &link_out));
            S = next;
        }

        // yield (perm_id, OUT, state24)
        let mut out_tuple: Vec<E::F> = vec![perm_id, E::F::one()];
        out_tuple.extend(S.iter().cloned());
        eval.add_to_relation(RelationEntry::new(&rel.keccak_state, en, &out_tuple));

        eval.finalize_logup_in_pairs();
        eval
    }
}

fn round_link_expr<E: EvalAtRow>(rc: u64, state: &[E::F; N_BYTES_IN_STATE]) -> Vec<E::F> {
    let mut out: Vec<E::F> = rc
        .to_le_bytes()
        .iter()
        .map(|b| E::F::from(BaseField::from(spread_u32(*b as u32))))
        .collect();
    out.extend(state.iter().cloned());
    out
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

/// Pairing order mirrors the AIR's `add_to_relation` calls:
/// `state[IN]`(−) · round_link[0](+), then per round `round_link[out](−)` ·
/// next-input(+), last pairs with `state[OUT]`(+).
pub fn generate_interaction_trace(
    rel: &KeccakRelations,
    data: &InteractionClaimData,
) -> (
    InteractionClaim,
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
) {
    let log_size = std::cmp::max(
        data.non_padded_length.next_power_of_two().ilog2(),
        LOG_N_LANES,
    );
    let enabler = Enabler::new(data.non_padded_length);
    let mut gen = LogupTraceGenerator::new(log_size);
    let n_vec_rows = 1usize << (log_size - LOG_N_LANES);

    // Column 1: state[IN](−enabler) paired with round_link[0](+enabler).
    pair_col(
        &mut gen,
        n_vec_rows,
        |vr| {
            let e = packed_enabler(&enabler, vr);
            (-e, rel.keccak_state.combine(&data.lookup_data.state[0][vr]))
        },
        |vr| {
            let e = packed_enabler(&enabler, vr);
            (e, rel.keccak_round.combine(&data.lookup_data.round_link[0][vr]))
        },
    );

    // Rounds: (round_link[1+2r] −) paired with (next input +).
    for round in 0..N_ROUNDS {
        let left = 1 + 2 * round;
        if round == N_ROUNDS - 1 {
            pair_col(
                &mut gen,
                n_vec_rows,
                |vr| {
                    let e = packed_enabler(&enabler, vr);
                    (-e, rel.keccak_round.combine(&data.lookup_data.round_link[left][vr]))
                },
                |vr| {
                    let e = packed_enabler(&enabler, vr);
                    (e, rel.keccak_state.combine(&data.lookup_data.state[1][vr]))
                },
            );
        } else {
            let right = left + 1;
            pair_col(
                &mut gen,
                n_vec_rows,
                |vr| {
                    let e = packed_enabler(&enabler, vr);
                    (-e, rel.keccak_round.combine(&data.lookup_data.round_link[left][vr]))
                },
                |vr| {
                    let e = packed_enabler(&enabler, vr);
                    (e, rel.keccak_round.combine(&data.lookup_data.round_link[right][vr]))
                },
            );
        }
    }

    let (trace, claimed_sum) = gen.finalize_last();
    (InteractionClaim { claimed_sum }, trace)
}

fn packed_enabler(enabler: &Enabler, vr: usize) -> PackedQM31 {
    PackedQM31::from(enabler.packed_at(vr))
}

fn pair_col(
    gen: &mut LogupTraceGenerator,
    n_vec_rows: usize,
    f0: impl Fn(usize) -> (PackedQM31, PackedQM31),
    f1: impl Fn(usize) -> (PackedQM31, PackedQM31),
) {
    let mut col = gen.new_col();
    for vr in 0..n_vec_rows {
        let (n0, d0) = f0(vr);
        let (n1, d1) = f1(vr);
        col.write_frac(vr, n0 * d1 + n1 * d0, d0 * d1);
    }
    col.finalize_col();
}
