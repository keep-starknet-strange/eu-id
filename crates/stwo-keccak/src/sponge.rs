//! The `sponge` component: variable-length SHAKE-256 absorb / pad10*1 / squeeze
//! (Improvement B over falcon-air's fixed 72-byte / 10-block wrapper).
//!
//! One trace row proves one hash instance. The block counts and message length
//! are *public* per component instance (fields of [`Claim`]), so every padding
//! position is a compile-time constant of the instance — the per-position
//! "boundary flags" the task describes collapse to constant literals, which is
//! both simpler and strictly sound (a constant cannot be forged).
//!
//! ## Sponge algorithm (FIPS 202 SHAKE-256, rate 136)
//!
//! ```text
//! S = 0^200
//! for a in 0..n_absorb:                 # absorb
//!     S[0..136] ^= block_a              # capacity S[136..200] untouched
//!     S = keccak_f(S)                   # one permutation, requested by id
//! out = S[0..136]                       # first squeeze block
//! for _ in 1..n_squeeze:                # extra squeeze blocks
//!     S = keccak_f(S)
//!     out ||= S[0..136]
//! ```
//!
//! ## pad10*1 (constant positions, `f = L mod 136` in the final absorb block)
//!
//! - real message bytes at positions `0..L` — each *consumed* from
//!   [`HashIoRelation`] `(absorb_stream_id, byte_pos, byte)` (negative), so a
//!   provider's yield of the declared byte cancels; a mismatch breaks balance.
//! - final block position `f` == `0x1F` (delimited suffix), unless `f == 135`,
//!   in which case position 135 == `0x1F | 0x80 == 0x9F`.
//! - final block positions `f+1..135` == 0.
//! - final block position 135 |= `0x80` (so `0x80` when `f < 135`).
//!
//! ## LogUp wiring
//!
//! - each absorb/extra-squeeze permutation: *yield* (+)
//!   `KeccakStateRelation(perm_id, IN, pre)`, *require* (−)
//!   `(perm_id, OUT, post)`. These cancel the `keccak` component, which requires
//!   IN and yields OUT.
//! - multi-block absorb XOR (`a > 0`): one `xor_8_8` use per rate byte.
//! - each squeeze output byte: *yield* (+) `HashIoRelation(squeeze_stream_id,
//!   byte_pos, byte)`.
//!
//! A [`HashIoProvider`] component closes the HashIo balance for a standalone
//! proof and pins the input/output to public values: it *yields* every declared
//! absorb byte and *requires* every expected squeeze byte.

#![allow(non_snake_case)]

use num_traits::{One, Zero};
use serde::{Deserialize, Serialize};
use stwo::core::channel::Channel;
use stwo::core::fields::m31::{BaseField, M31};
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::core::pcs::TreeVec;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES, N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::BackendForChannel;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
};

use crate::constants::{
    DELIMITED_SUFFIX, FINAL_BIT, N_BYTES_IN_RATE, N_BYTES_IN_STATE, N_BYTES_IN_U64,
};
use crate::relations::{direction, KeccakRelations};
use crate::utils::spread_u32;

/// Number of permutations a `(n_absorb, n_squeeze)` sponge performs.
pub const fn n_perms(n_absorb: usize, n_squeeze: usize) -> usize {
    n_absorb + n_squeeze - 1
}

/// Number of absorb blocks needed for a message of `l` bytes (pad10*1 always
/// adds at least one padding byte, so `ceil((l+1)/136)`).
pub const fn n_absorb_blocks(l: usize) -> usize {
    (l + 1).div_ceil(N_BYTES_IN_RATE)
}

/// Static shape of a sponge instance; drives the column layout.
///
/// `perm_id_base` is the PUBLIC global permutation-id offset: this instance's
/// `n_perms` Keccak-f permutations occupy ids `[base, base+n_perms)`. It defaults
/// to 0 (a standalone sponge); a composition assigns disjoint bases across chains
/// so the shared `KeccakStateRelation` never crosses instances. Both the trace
/// data and the `Eval`'s KeccakState tuples honor it.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Shape {
    pub message_len: usize,
    pub n_absorb: usize,
    pub n_squeeze: usize,
    pub absorb_stream_id: u32,
    pub squeeze_stream_id: u32,
    pub perm_id_base: usize,
}

impl Shape {
    pub fn new(
        message_len: usize,
        n_squeeze: usize,
        absorb_stream_id: u32,
        squeeze_stream_id: u32,
    ) -> Self {
        Self::with_perm_id_base(
            message_len,
            n_squeeze,
            absorb_stream_id,
            squeeze_stream_id,
            0,
        )
    }

    /// [`Shape::new`] with an explicit global `perm_id_base` (composition path).
    pub fn with_perm_id_base(
        message_len: usize,
        n_squeeze: usize,
        absorb_stream_id: u32,
        squeeze_stream_id: u32,
        perm_id_base: usize,
    ) -> Self {
        assert!(n_squeeze >= 1, "at least one squeeze block");
        Self {
            message_len,
            n_absorb: n_absorb_blocks(message_len),
            n_squeeze,
            absorb_stream_id,
            squeeze_stream_id,
            perm_id_base,
        }
    }

    pub fn n_perms(&self) -> usize {
        n_perms(self.n_absorb, self.n_squeeze)
    }

    pub fn output_len(&self) -> usize {
        self.n_squeeze * N_BYTES_IN_RATE
    }

    /// `f = L mod 136`: the padding-start position in the final absorb block.
    fn pad_pos(&self) -> usize {
        self.message_len % N_BYTES_IN_RATE
    }

    /// Columns (spread-form state; byte form only at the HashIo boundary):
    /// enabler + block bytes + block-spread + new-rate-spread (a>0) +
    /// post-permutation spread states + squeeze bytes.
    fn n_columns(&self) -> usize {
        1 + N_BYTES_IN_RATE * self.n_absorb                       // block bytes
            + N_BYTES_IN_RATE * self.n_absorb                     // block spread
            + N_BYTES_IN_RATE * self.n_absorb.saturating_sub(1)   // new-rate spread
            + N_BYTES_IN_STATE * self.n_perms()                   // post spread states
            + self.output_len() // squeeze bytes (spread→byte at the HashIo edge)
    }

    /// conv uses: one per block byte (byte↔spread) + one per squeeze byte.
    fn n_conv_lookups(&self) -> usize {
        N_BYTES_IN_RATE * self.n_absorb + self.output_len()
    }

    /// xor3 uses: one per rate byte for every absorb block after the first.
    fn n_xor_lookups(&self) -> usize {
        N_BYTES_IN_RATE * self.n_absorb.saturating_sub(1)
    }

    /// KeccakState requests: 2 (IN,OUT) per permutation.
    fn n_state_lookups(&self) -> usize {
        2 * self.n_perms()
    }

    /// HashIo uses: `L` absorb consumes + `output_len` squeeze yields.
    fn n_io_lookups(&self) -> usize {
        self.message_len + self.output_len()
    }

    fn n_total_lookups(&self) -> usize {
        self.n_state_lookups() + self.n_xor_lookups() + self.n_io_lookups() + self.n_conv_lookups()
    }

    fn n_interaction_columns(&self) -> usize {
        SECURE_EXTENSION_DEGREE * self.n_total_lookups().div_ceil(2)
    }
}

// The sponge is variable-shape, so column counts are runtime. We use a dynamic
// ComponentTrace-free trace: build BaseColumns directly (one instance ⇒ few
// rows, so no SIMD-parallel fill is needed; simplicity over throughput here —
// ponytail: the throughput-critical work is the keccak_round component).

pub struct InteractionClaimData {
    pub shape: Shape,
    pub non_padded_length: usize,
    /// state requests: `[perm_id, dir, spread_state(200)]`.
    pub state: Vec<Vec<[PackedM31; 2 + N_BYTES_IN_STATE]>>,
    /// xor3 uses (a>0 rate): `[key, spread_out]` with `key = a + b + 0`.
    pub xor: Vec<Vec<[PackedM31; 2]>>,
    /// conv uses: `[byte, spread]` — block byte→spread and squeeze spread→byte.
    pub conv: Vec<[PackedM31; 2]>,
    /// io uses with sign: `(is_yield, [stream_id, byte_pos, byte])`.
    pub io: Vec<(bool, Vec<[PackedM31; 3]>)>,
}

#[derive(Clone, Serialize, Deserialize, Debug)]
pub struct Claim {
    pub log_size: u32,
    pub shape: Shape,
}

impl Claim {
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        TreeVec::new(vec![
            vec![],
            vec![self.log_size; self.shape.n_columns()],
            vec![self.log_size; self.shape.n_interaction_columns()],
        ])
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
        channel.mix_u64(self.shape.message_len as u64);
        channel.mix_u64(self.shape.n_squeeze as u64);
        channel.mix_u64(self.shape.absorb_stream_id as u64);
        channel.mix_u64(self.shape.squeeze_stream_id as u64);
        channel.mix_u64(self.shape.perm_id_base as u64);
    }
}

/// Result of running the sponge natively while building the trace.
pub struct SpongeRun {
    pub claim: Claim,
    pub trace: Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    pub data: InteractionClaimData,
    /// Permutation input rows `[state(200)|perm_id]` to feed `keccak`.
    pub perm_inputs: Vec<[PackedM31; N_BYTES_IN_STATE + 1]>,
    /// The squeeze output bytes (length `output_len`).
    pub output: Vec<u8>,
}

/// Build the sponge trace for one message. `perm_id_base` is the global running
/// permutation id offset (so multiple instances get disjoint ids).
pub fn generate_trace(
    message: &[u8],
    n_squeeze: usize,
    absorb_stream_id: u32,
    squeeze_stream_id: u32,
    perm_id_base: usize,
) -> SpongeRun
where
    SimdBackend: BackendForChannel<Blake2sMerkleChannel>,
{
    let shape = Shape::with_perm_id_base(
        message.len(),
        n_squeeze,
        absorb_stream_id,
        squeeze_stream_id,
        perm_id_base,
    );
    let log_size = LOG_N_LANES; // one instance ⇒ a single packed row of 16 lanes
    let f = shape.pad_pos();

    // Build the padded absorb blocks (bytes), lane 0 carries the real data; all
    // 16 SIMD lanes are identical (a single logical instance).
    let mut blocks: Vec<[u8; N_BYTES_IN_RATE]> = vec![[0u8; N_BYTES_IN_RATE]; shape.n_absorb];
    for (i, &b) in message.iter().enumerate() {
        blocks[i / N_BYTES_IN_RATE][i % N_BYTES_IN_RATE] = b;
    }
    // pad10*1 in the final block.
    let last = shape.n_absorb - 1;
    blocks[last][f] ^= DELIMITED_SUFFIX;
    blocks[last][N_BYTES_IN_RATE - 1] ^= FINAL_BIT;

    // Native sponge on a *byte* state; the committed state and links carry
    // spread form. Byte↔spread conversions (conv lookups) happen only at the
    // HashIo boundary (block bytes in, squeeze bytes out).
    let mut state = [0u8; N_BYTES_IN_STATE];
    let mut perm_inputs: Vec<[PackedM31; N_BYTES_IN_STATE + 1]> = Vec::new();
    let mut state_data: Vec<Vec<[PackedM31; 2 + N_BYTES_IN_STATE]>> = Vec::new();
    let mut xor_data: Vec<Vec<[PackedM31; 2]>> = Vec::new();
    let mut conv_data: Vec<[PackedM31; 2]> = Vec::new();
    let mut post_states: Vec<[u8; N_BYTES_IN_STATE]> = Vec::new();
    let mut perm_id = perm_id_base;

    // conv: block bytes → spread (in block order, all positions).
    for a in 0..shape.n_absorb {
        for j in 0..N_BYTES_IN_RATE {
            conv_data.push([splat(blocks[a][j]), spread_byte(blocks[a][j])]);
        }
    }

    let push_perm = |state: &mut [u8; N_BYTES_IN_STATE],
                     perm_id: &mut usize,
                     perm_inputs: &mut Vec<[PackedM31; N_BYTES_IN_STATE + 1]>,
                     state_data: &mut Vec<Vec<[PackedM31; 2 + N_BYTES_IN_STATE]>>,
                     post_states: &mut Vec<[u8; N_BYTES_IN_STATE]>| {
        let pre = *state;
        // request row for keccak (spread state).
        let mut prow = [PackedM31::zero(); N_BYTES_IN_STATE + 1];
        for i in 0..N_BYTES_IN_STATE {
            prow[i] = spread_byte(pre[i]);
        }
        prow[N_BYTES_IN_STATE] = splat_u32(*perm_id as u32);
        perm_inputs.push(prow);

        native_keccak_f_bytes(state);
        let post = *state;
        post_states.push(post);

        state_data.push(vec![state_tuple(*perm_id as u32, direction::IN, &pre)]);
        state_data.push(vec![state_tuple(*perm_id as u32, direction::OUT, &post)]);
        *perm_id += 1;
    };

    // Absorb. Blocks a>0 witness the XORed rate (`new_rate`) as spread columns,
    // via one xor3(prev_rate, block, 0) use per byte.
    let mut new_rates: Vec<[u8; N_BYTES_IN_RATE]> = Vec::new(); // one per absorb block a>0
    for a in 0..shape.n_absorb {
        if a == 0 {
            for j in 0..N_BYTES_IN_RATE {
                state[j] = blocks[a][j];
            }
        } else {
            let mut uses = Vec::with_capacity(N_BYTES_IN_RATE);
            let mut new_rate = [0u8; N_BYTES_IN_RATE];
            for j in 0..N_BYTES_IN_RATE {
                let old = state[j];
                let m = blocks[a][j];
                let newv = old ^ m;
                // xor3 key = spread(old) + spread(m) + 0.
                let key = spread_byte(old) + spread_byte(m);
                uses.push([key, spread_byte(newv)]);
                new_rate[j] = newv;
                state[j] = newv;
            }
            new_rates.push(new_rate);
            xor_data.push(uses);
        }
        push_perm(
            &mut state,
            &mut perm_id,
            &mut perm_inputs,
            &mut state_data,
            &mut post_states,
        );
    }

    // Squeeze.
    let mut output = Vec::with_capacity(shape.output_len());
    output.extend_from_slice(&state[..N_BYTES_IN_RATE]);
    for _ in 1..shape.n_squeeze {
        push_perm(
            &mut state,
            &mut perm_id,
            &mut perm_inputs,
            &mut state_data,
            &mut post_states,
        );
        output.extend_from_slice(&state[..N_BYTES_IN_RATE]);
    }

    // conv: squeeze spread → byte (in output order).
    for &b in &output {
        conv_data.push([splat(b), spread_byte(b)]);
    }

    // HashIo uses: consume L absorb message bytes, yield output_len squeeze bytes.
    let mut io: Vec<(bool, Vec<[PackedM31; 3]>)> = Vec::new();
    let mut absorb_uses = Vec::with_capacity(shape.message_len);
    for (pos, &b) in message.iter().enumerate() {
        absorb_uses.push([splat_u32(absorb_stream_id), splat_u32(pos as u32), splat(b)]);
    }
    io.push((false, absorb_uses)); // require (consume)
    let mut squeeze_uses = Vec::with_capacity(shape.output_len());
    for (pos, &b) in output.iter().enumerate() {
        squeeze_uses.push([
            splat_u32(squeeze_stream_id),
            splat_u32(pos as u32),
            splat(b),
        ]);
    }
    io.push((true, squeeze_uses)); // yield

    // Assemble the base trace columns (packed, single row). Column order MUST
    // match `Eval::evaluate`'s `next_trace_mask` reads:
    //   enabler,
    //   blocks_byte[136·n_absorb],
    //   blocks_spread[136·n_absorb],
    //   per absorb block a: [if a>0: new_rate_spread(136)], post_spread(200),
    //   per extra squeeze: post_spread(200),
    //   squeeze_byte[output_len].
    let mut columns: Vec<PackedM31> = Vec::with_capacity(shape.n_columns());
    columns.push(lane0_enabler());
    for a in 0..shape.n_absorb {
        for j in 0..N_BYTES_IN_RATE {
            columns.push(splat(blocks[a][j]));
        }
    }
    for a in 0..shape.n_absorb {
        for j in 0..N_BYTES_IN_RATE {
            columns.push(spread_byte(blocks[a][j]));
        }
    }
    let mut nr_idx = 0usize;
    for (a, post) in post_states.iter().enumerate().take(shape.n_absorb) {
        if a > 0 {
            for j in 0..N_BYTES_IN_RATE {
                columns.push(spread_byte(new_rates[nr_idx][j]));
            }
            nr_idx += 1;
        }
        for i in 0..N_BYTES_IN_STATE {
            columns.push(spread_byte(post[i]));
        }
    }
    for post in post_states.iter().skip(shape.n_absorb) {
        for i in 0..N_BYTES_IN_STATE {
            columns.push(spread_byte(post[i]));
        }
    }
    for &b in &output {
        columns.push(splat(b));
    }
    debug_assert_eq!(columns.len(), shape.n_columns());

    let domain = stwo::core::poly::circle::CanonicCoset::new(log_size).circle_domain();
    let trace: Vec<_> = columns
        .into_iter()
        .map(|c| {
            let col: stwo::prover::backend::simd::column::BaseColumn =
                c.to_array().into_iter().collect();
            CircleEvaluation::new(domain, col)
        })
        .collect();

    let claim = Claim { log_size, shape };
    SpongeRun {
        claim,
        trace,
        data: InteractionClaimData {
            shape,
            non_padded_length: 1,
            state: state_data,
            xor: xor_data,
            conv: conv_data,
            io,
        },
        perm_inputs,
        output,
    }
}

fn splat(b: u8) -> PackedM31 {
    PackedM31::from(M31::from(b as u32))
}
fn splat_u32(v: u32) -> PackedM31 {
    PackedM31::from(M31::from(v))
}
/// Splat `spread(byte)` across all SIMD lanes.
fn spread_byte(b: u8) -> PackedM31 {
    PackedM31::from(M31::from(spread_u32(b as u32)))
}

/// State tuple with the 200 state limbs carried in spread form.
fn state_tuple(
    perm_id: u32,
    dir: u32,
    state: &[u8; N_BYTES_IN_STATE],
) -> [PackedM31; 2 + N_BYTES_IN_STATE] {
    let mut out = [PackedM31::zero(); 2 + N_BYTES_IN_STATE];
    out[0] = splat_u32(perm_id);
    out[1] = splat_u32(dir);
    for i in 0..N_BYTES_IN_STATE {
        out[2 + i] = spread_byte(state[i]);
    }
    out
}

/// Native Keccak-f on a byte-state (all 16 lanes identical), via the u64 path.
pub(crate) fn native_keccak_f_bytes(state: &mut [u8; N_BYTES_IN_STATE]) {
    let mut words = [0u64; 25];
    for (w, word) in words.iter_mut().enumerate() {
        for b in 0..N_BYTES_IN_U64 {
            *word |= (state[w * N_BYTES_IN_U64 + b] as u64) << (8 * b);
        }
    }
    keccak_f_words(&mut words);
    for (w, &word) in words.iter().enumerate() {
        for b in 0..N_BYTES_IN_U64 {
            state[w * N_BYTES_IN_U64 + b] = ((word >> (8 * b)) & 0xFF) as u8;
        }
    }
}

fn keccak_f_words(state: &mut [u64; 25]) {
    for round in 0..crate::constants::N_ROUNDS {
        keccak_round_words(state, round);
    }
}

fn keccak_round_words(state: &mut [u64; 25], round: usize) {
    const RHO: [u32; 24] = [
        1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
    ];
    const PI: [usize; 24] = [
        10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
    ];
    let rc = crate::constants::iota_rc_rounds();
    let mut c = [0u64; 5];
    for x in 0..5 {
        c[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
    }
    let mut d = [0u64; 5];
    for x in 0..5 {
        d[x] = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
    }
    for y in 0..5 {
        for x in 0..5 {
            state[x + 5 * y] ^= d[x];
        }
    }
    let mut current = state[1];
    for i in 0..24 {
        let idx = PI[i];
        let tmp = state[idx];
        state[idx] = current.rotate_left(RHO[i]);
        current = tmp;
    }
    for y in 0..5 {
        let base = 5 * y;
        let row: [u64; 5] = std::array::from_fn(|x| state[base + x]);
        for x in 0..5 {
            state[base + x] = row[x] ^ ((!row[(x + 1) % 5]) & row[(x + 2) % 5]);
        }
    }
    state[0] ^= rc[round];
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
        let shape = self.claim.shape;
        let f = shape.pad_pos();

        let enabler = eval.next_trace_mask();
        eval.add_constraint(enabler.clone() * (E::F::one() - enabler.clone()));
        let en = E::EF::from(enabler);

        // Read the absorb blocks in byte form, then their spread form.
        let blocks: Vec<[E::F; N_BYTES_IN_RATE]> = (0..shape.n_absorb)
            .map(|_| std::array::from_fn(|_| eval.next_trace_mask()))
            .collect();
        let blocks_spread: Vec<[E::F; N_BYTES_IN_RATE]> = (0..shape.n_absorb)
            .map(|_| std::array::from_fn(|_| eval.next_trace_mask()))
            .collect();

        // Padding constraints on the final block's byte form (constant positions).
        let last = shape.n_absorb - 1;
        let suffix = BaseField::from(DELIMITED_SUFFIX as u32);
        let final_bit = BaseField::from(FINAL_BIT as u32);
        for j in 0..N_BYTES_IN_RATE {
            let expected: Option<BaseField> = if j < f {
                None // a real message byte, bound via HashIo below
            } else if j == f && j == N_BYTES_IN_RATE - 1 {
                Some(suffix + final_bit) // 0x1F | 0x80 = 0x9F (disjoint bits)
            } else if j == f {
                Some(suffix)
            } else if j == N_BYTES_IN_RATE - 1 {
                Some(final_bit)
            } else {
                Some(BaseField::zero())
            };
            if let Some(v) = expected {
                eval.add_constraint(blocks[last][j].clone() - E::F::from(v));
            }
        }

        // conv: bind every block byte to its spread limb (byte→spread boundary).
        for a in 0..shape.n_absorb {
            for j in 0..N_BYTES_IN_RATE {
                conv_use(
                    &mut eval,
                    rel,
                    &blocks[a][j],
                    &blocks_spread[a][j],
                    en.clone(),
                );
            }
        }

        // HashIo: consume the L real message *bytes* (require, −).
        for p in 0..shape.message_len {
            let byte = blocks[p / N_BYTES_IN_RATE][p % N_BYTES_IN_RATE].clone();
            eval.add_to_relation(RelationEntry::new(
                &rel.hash_io,
                -en.clone(),
                &[
                    E::F::from(BaseField::from(shape.absorb_stream_id)),
                    E::F::from(BaseField::from(p as u32)),
                    byte,
                ],
            ));
        }

        // Running state (spread); capacity starts at zero.
        let mut S: [E::F; N_BYTES_IN_STATE] = std::array::from_fn(|_| E::F::zero());
        let mut squeeze_out: Vec<E::F> = Vec::with_capacity(shape.output_len());

        // Each permutation: yield IN(current spread S), require OUT(witnessed
        // post). The perm id is the GLOBAL `perm_id_base + local_idx` (matching
        // the trace's `state_tuple`, which stamps `perm_id_base + idx`).
        let base = shape.perm_id_base;
        let do_perm = |eval: &mut E, idx: usize, s: &mut [E::F; N_BYTES_IN_STATE]| {
            let perm_id = E::F::from(BaseField::from((base + idx) as u32));
            let mut in_tuple: Vec<E::F> = vec![perm_id.clone(), E::F::zero()];
            in_tuple.extend(s.iter().cloned());
            eval.add_to_relation(RelationEntry::new(&rel.keccak_state, en.clone(), &in_tuple));
            let post: [E::F; N_BYTES_IN_STATE] = std::array::from_fn(|_| eval.next_trace_mask());
            let mut out_tuple: Vec<E::F> = vec![perm_id, E::F::one()];
            out_tuple.extend(post.iter().cloned());
            eval.add_to_relation(RelationEntry::new(
                &rel.keccak_state,
                -en.clone(),
                &out_tuple,
            ));
            *s = post;
        };

        for a in 0..shape.n_absorb {
            if a == 0 {
                // pre-state rate = block 0 (spread; capacity 0).
                for j in 0..N_BYTES_IN_RATE {
                    S[j] = blocks_spread[0][j].clone();
                }
            } else {
                // rate ^= block via xor3(prev_rate, block_spread, 0); the
                // witnessed spread result becomes the pre-permutation rate.
                let new_rate: [E::F; N_BYTES_IN_RATE] =
                    std::array::from_fn(|_| eval.next_trace_mask());
                for j in 0..N_BYTES_IN_RATE {
                    xor3_use(
                        &mut eval,
                        rel,
                        &S[j],
                        &blocks_spread[a][j],
                        &new_rate[j],
                        en.clone(),
                    );
                    S[j] = new_rate[j].clone();
                }
            }
            do_perm(&mut eval, a, &mut S);
        }

        // First squeeze block comes from the post-absorb state (spread).
        for j in 0..N_BYTES_IN_RATE {
            squeeze_out.push(S[j].clone());
        }
        for s in 1..shape.n_squeeze {
            do_perm(&mut eval, shape.n_absorb + s - 1, &mut S);
            for j in 0..N_BYTES_IN_RATE {
                squeeze_out.push(S[j].clone());
            }
        }

        // Squeeze conv (spread→byte) then HashIo yields on the bytes.
        let squeeze_bytes: Vec<E::F> = (0..shape.output_len())
            .map(|_| eval.next_trace_mask())
            .collect();
        for (spread, byte) in squeeze_out.iter().zip(squeeze_bytes.iter()) {
            conv_use(&mut eval, rel, byte, spread, en.clone());
        }
        for (pos, byte) in squeeze_bytes.iter().enumerate() {
            eval.add_to_relation(RelationEntry::new(
                &rel.hash_io,
                en.clone(),
                &[
                    E::F::from(BaseField::from(shape.squeeze_stream_id)),
                    E::F::from(BaseField::from(pos as u32)),
                    byte.clone(),
                ],
            ));
        }

        eval.finalize_logup_in_pairs();
        eval
    }
}

/// xor3 use with third input 0: `key = a + b`, output `c` (rate absorb XOR).
fn xor3_use<E: EvalAtRow>(
    eval: &mut E,
    rel: &KeccakRelations,
    a: &E::F,
    b: &E::F,
    c: &E::F,
    en: E::EF,
) {
    eval.add_to_relation(RelationEntry::new(
        &rel.xor3,
        en,
        &[a.clone() + b.clone(), c.clone()],
    ));
}

/// conv use: bind `(byte, spread)` via the byte↔spread table.
fn conv_use<E: EvalAtRow>(
    eval: &mut E,
    rel: &KeccakRelations,
    byte: &E::F,
    spread: &E::F,
    en: E::EF,
) {
    eval.add_to_relation(RelationEntry::new(
        &rel.conv,
        en,
        &[byte.clone(), spread.clone()],
    ));
}

/// Enabler active on SIMD lane 0 only (single logical sponge instance).
fn lane0_enabler() -> PackedM31 {
    let mut lanes = [M31::from(0u32); N_LANES];
    lanes[0] = M31::from(1u32);
    PackedM31::from_array(lanes)
}

pub type Component = FrameworkComponent<Eval>;

// ─────────────────────────── Interaction (sponge) ──────────────────────────

#[derive(Clone, Serialize, Deserialize, Debug)]
pub struct InteractionClaim {
    pub claimed_sum: SecureField,
}

impl InteractionClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}

/// Build the sponge interaction trace, pairing lookups in AIR order:
/// io-absorb (−), then per absorb block [xor uses (+)] and [state IN (+), OUT
/// (−)], then per extra squeeze [state IN (+), OUT (−)], then io-squeeze (+).
pub fn generate_interaction_trace(
    rel: &KeccakRelations,
    data: &InteractionClaimData,
) -> (
    InteractionClaim,
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
) {
    let log_size = LOG_N_LANES;
    let mut gen = LogupTraceGenerator::new(log_size);

    // The sponge is one logical instance on lane 0; every numerator is scaled by
    // the lane-0 enabler so lanes 1..16 contribute nothing (matching the keccak
    // component's lane-0-only accounting).
    let en = PackedQM31::from(lane0_enabler());

    // Flatten every lookup into a single (num, den) per the single vec-row.
    let mut fracs: Vec<(PackedQM31, PackedQM31)> = Vec::with_capacity(data.shape.n_total_lookups());

    // Order MUST equal the AIR's add_to_relation order:
    //  1. conv on block bytes (136·n_absorb uses, +)
    //  2. io absorb consume (L uses, −)
    //  3. per absorb block a: if a>0, 136 xor3 uses (+); then state IN(+), OUT(−)
    //  4. per extra squeeze: state IN(+), OUT(−)
    //  5. conv on squeeze (output_len uses, +)
    //  6. io squeeze yield (output_len uses, +)
    let n_block_conv = N_BYTES_IN_RATE * data.shape.n_absorb;
    for tuple in &data.conv[..n_block_conv] {
        fracs.push((en, rel.conv.combine(tuple)));
    }

    let (absorb_yield, absorb_uses) = &data.io[0];
    debug_assert!(!absorb_yield);
    for tuple in absorb_uses {
        fracs.push((-en, rel.hash_io.combine(tuple)));
    }

    let mut xor_block = 0usize;
    for a in 0..data.shape.n_absorb {
        if a > 0 {
            for tuple in &data.xor[xor_block] {
                fracs.push((en, rel.xor3.combine(tuple)));
            }
            xor_block += 1;
        }
        // state IN (+), OUT (−)
        fracs.push((en, rel.keccak_state.combine(&data.state[2 * a][0])));
        fracs.push((-en, rel.keccak_state.combine(&data.state[2 * a + 1][0])));
    }
    for s in 1..data.shape.n_squeeze {
        let p = data.shape.n_absorb + s - 1;
        fracs.push((en, rel.keccak_state.combine(&data.state[2 * p][0])));
        fracs.push((-en, rel.keccak_state.combine(&data.state[2 * p + 1][0])));
    }

    for tuple in &data.conv[n_block_conv..] {
        fracs.push((en, rel.conv.combine(tuple)));
    }

    let (squeeze_yield, squeeze_uses) = &data.io[1];
    debug_assert!(squeeze_yield);
    for tuple in squeeze_uses {
        fracs.push((en, rel.hash_io.combine(tuple)));
    }

    // Finalize in pairs (single vec-row, index 0).
    let mut i = 0;
    while i + 2 <= fracs.len() {
        let mut col = gen.new_col();
        let (n0, d0) = fracs[i];
        let (n1, d1) = fracs[i + 1];
        col.write_frac(0, n0 * d1 + n1 * d0, d0 * d1);
        col.finalize_col();
        i += 2;
    }
    if i < fracs.len() {
        let mut col = gen.new_col();
        let (n, d) = fracs[i];
        col.write_frac(0, n, d);
        col.finalize_col();
    }

    let (trace, claimed_sum) = gen.finalize_last();
    (InteractionClaim { claimed_sum }, trace)
}

// ───────────────────────── HashIo provider (closure) ───────────────────────

/// Closes the HashIo balance for a standalone proof: *yields* the declared
/// absorb bytes and *requires* the expected squeeze bytes, pinning both to the
/// public message / expected output.
pub mod io_provider {
    use super::*;

    #[derive(Clone, Serialize, Deserialize, Debug)]
    pub struct Claim {
        pub log_size: u32,
        pub shape: Shape,
    }

    pub struct Data {
        pub shape: Shape,
        pub absorb: Vec<[PackedM31; 3]>,
        pub squeeze: Vec<[PackedM31; 3]>,
    }

    impl Claim {
        pub fn n_columns(&self) -> usize {
            1 // a single lane-0 enabler column
        }
        pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
            let n = (self.shape.message_len + self.shape.output_len()).div_ceil(2)
                * SECURE_EXTENSION_DEGREE;
            TreeVec::new(vec![vec![], vec![self.log_size; 1], vec![self.log_size; n]])
        }
    }

    /// The io_provider's one trace column: a lane-0 enabler (single instance).
    pub fn trace() -> Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
        let domain = stwo::core::poly::circle::CanonicCoset::new(LOG_N_LANES).circle_domain();
        let col: stwo::prover::backend::simd::column::BaseColumn =
            super::lane0_enabler().to_array().into_iter().collect();
        vec![CircleEvaluation::new(domain, col)]
    }

    #[derive(Clone, Serialize, Deserialize, Debug)]
    pub struct InteractionClaim {
        pub claimed_sum: SecureField,
    }
    impl InteractionClaim {
        pub fn mix_into(&self, channel: &mut impl Channel) {
            channel.mix_felts(&[self.claimed_sum]);
        }
    }

    /// Build provider data from the public message + expected output.
    pub fn build_data(message: &[u8], output: &[u8], shape: Shape) -> Data {
        let absorb = message
            .iter()
            .enumerate()
            .map(|(pos, &b)| {
                [
                    super::splat_u32(shape.absorb_stream_id),
                    super::splat_u32(pos as u32),
                    super::splat(b),
                ]
            })
            .collect();
        let squeeze = output
            .iter()
            .enumerate()
            .map(|(pos, &b)| {
                [
                    super::splat_u32(shape.squeeze_stream_id),
                    super::splat_u32(pos as u32),
                    super::splat(b),
                ]
            })
            .collect();
        Data {
            shape,
            absorb,
            squeeze,
        }
    }

    #[derive(Clone)]
    pub struct Eval {
        pub log_size: u32,
        pub shape: Shape,
        /// Public message and expected output as base felts (constant columns).
        pub message: Vec<u8>,
        pub output: Vec<u8>,
        pub relations: KeccakRelations,
    }

    impl FrameworkEval for Eval {
        fn log_size(&self) -> u32 {
            self.log_size
        }
        fn max_constraint_log_degree_bound(&self) -> u32 {
            self.log_size + 1
        }
        fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
            let rel = &self.relations;
            let enabler = eval.next_trace_mask();
            eval.add_constraint(enabler.clone() * (E::F::one() - enabler.clone()));
            let en = E::EF::from(enabler);
            // yield absorb bytes (+en): provider supplies the declared message.
            for (pos, &b) in self.message.iter().enumerate() {
                eval.add_to_relation(RelationEntry::new(
                    &rel.hash_io,
                    en.clone(),
                    &[
                        E::F::from(BaseField::from(self.shape.absorb_stream_id)),
                        E::F::from(BaseField::from(pos as u32)),
                        E::F::from(BaseField::from(b as u32)),
                    ],
                ));
            }
            // require squeeze bytes (−en): pins output to the expected value.
            for (pos, &b) in self.output.iter().enumerate() {
                eval.add_to_relation(RelationEntry::new(
                    &rel.hash_io,
                    -en.clone(),
                    &[
                        E::F::from(BaseField::from(self.shape.squeeze_stream_id)),
                        E::F::from(BaseField::from(pos as u32)),
                        E::F::from(BaseField::from(b as u32)),
                    ],
                ));
            }
            eval.finalize_logup_in_pairs();
            eval
        }
    }

    pub type Component = FrameworkComponent<Eval>;

    pub fn generate_interaction_trace(
        rel: &KeccakRelations,
        data: &Data,
    ) -> (
        InteractionClaim,
        Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    ) {
        let mut gen = LogupTraceGenerator::new(LOG_N_LANES);
        let en = PackedQM31::from(super::lane0_enabler());
        let mut fracs: Vec<(PackedQM31, PackedQM31)> = Vec::new();
        for tuple in &data.absorb {
            fracs.push((en, rel.hash_io.combine(tuple)));
        }
        for tuple in &data.squeeze {
            fracs.push((-en, rel.hash_io.combine(tuple)));
        }
        let mut i = 0;
        while i + 2 <= fracs.len() {
            let mut col = gen.new_col();
            let (n0, d0) = fracs[i];
            let (n1, d1) = fracs[i + 1];
            col.write_frac(0, n0 * d1 + n1 * d0, d0 * d1);
            col.finalize_col();
            i += 2;
        }
        if i < fracs.len() {
            let mut col = gen.new_col();
            let (n, d) = fracs[i];
            col.write_frac(0, n, d);
            col.finalize_col();
        }
        let (trace, claimed_sum) = gen.finalize_last();
        (InteractionClaim { claimed_sum }, trace)
    }
}
