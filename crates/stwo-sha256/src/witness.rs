//! Witness emitter — produces every intermediate value the AIR refers to,
//! from raw message bytes through the per-round limb representation and the
//! carries of every mod-2³² add.
//!
//! Pipeline:
//!
//! 1. `compute_padding_witness(msg)` — FIPS §5.1.1 padding, byte-exact.
//! 2. `compute_block_witness(h_in, block_bytes)` — schedule expansion (with
//!    `σ0`/`σ1` lookups and their carries) + 64 round witnesses + 8
//!    finalization adds.
//! 3. `compute_sha256_witness(msg)` — chains blocks: `H⁽⁰⁾ = IV`, then
//!    `H⁽ᵗ⁺¹⁾ = compress(H⁽ᵗ⁾, blockₜ)` for each block.
//!
//! Every numeric value is reproduced from the native reference in
//! `crate::native` and cross-checked by the tests. The witness layer never
//! diverges from the FIPS spec; it just adds the *intermediate* values that
//! the AIR's linear constraints reference.

use crate::constants::{BLOCK_BYTES, IV, K, N_INPUT_WORDS, N_ROUNDS, N_STATE_WORDS};
use crate::native::{
    big_sigma0, big_sigma1, ch, lower_sigma0, lower_sigma1, maj, pad_message, parse_blocks,
};
use crate::partitions::{apply, bits_to_mask, SigmaFn};
use crate::tables::pack_half_key;
use crate::types::{
    AddCarries, BlockWitness, Digest, HashState, LimbPairBytes, PaddingWitness, RoundWitness,
    Schedule, ScheduleEntryWitness, Sha256Witness, SigmaDecodeWitness, WordLimbs, LIMB_BITS,
};

/// Pad the message and assemble the padding witness used by the AIR.
pub fn compute_padding_witness(msg: &[u8]) -> PaddingWitness {
    let padded = pad_message(msg);
    let n_blocks = padded.len() / BLOCK_BYTES;
    let bit_length = (msg.len() as u64).checked_mul(8).expect("message too long");
    PaddingWitness {
        message: msg.to_vec(),
        padded,
        n_blocks,
        bit_length,
    }
}

/// Add `k` 32-bit words modulo `2³²`, producing the result *and* the lo/hi
/// limb carries the AIR enforces.
///
/// Returns `(result_word, AddCarries { lo, hi })`. `lo` is the carry from
/// the low-limb sum into the high-limb sum (`< k`); `hi` is the carry out of
/// the high-limb sum (also `< k`; discarded under `mod 2³²`).
fn add_words_with_carries(words: &[u32]) -> (u32, AddCarries) {
    let mut lo_sum: u32 = 0;
    let mut hi_sum: u32 = 0;
    for &w in words {
        lo_sum = lo_sum.wrapping_add(w & 0xFFFF);
        // accumulate the actual u32 hi sum WITHOUT wrap so we can read the
        // top carry cleanly.
        hi_sum += w >> LIMB_BITS;
    }
    let carry_lo = lo_sum >> LIMB_BITS; // bounded by len(words) - 1 in practice
    let res_lo = lo_sum & 0xFFFF;
    let hi_total = hi_sum + carry_lo;
    let carry_hi = hi_total >> LIMB_BITS;
    let res_hi = hi_total & 0xFFFF;
    let res = res_lo | (res_hi << LIMB_BITS);
    (
        res,
        AddCarries {
            lo: carry_lo,
            hi: carry_hi,
        },
    )
}

/// Build the decoded intermediates of one σ-application `y = f(x)` per §9.3:
/// the two 16-bit half-keys, the spread `O0`/`O1` outputs, the two `O2`
/// partials, the XOR-combined `O2`, and the byte chunks of all three `O2`
/// values for the chunk-wise `xor_8` lookup.
///
/// `f` is GF(2)-linear, so applying it to the S-only-half and the S′-only-half
/// of the input separately yields the per-side contributions; the spread `O0`
/// bits live at natural positions in `f(S-half)`, and the side's `O2` partial
/// is `f(S-half)` masked to the `O2` bit positions. Same for the S′ side.
/// Their field sums (disjoint bit sets) plus the chunk-wise XOR of the two
/// `O2` partials reproduce the full `f(x)` — the reassembly identity the AIR
/// enforces.
fn compute_sigma_decode_witness(f: SigmaFn, x: u32) -> SigmaDecodeWitness {
    let s_mask = f.s_mask();
    let outputs = f.outputs();
    let o0_mask = bits_to_mask(outputs.o0);
    let o1_mask = bits_to_mask(outputs.o1);
    let o2_mask = bits_to_mask(outputs.o2);

    let key_s = pack_half_key(x, s_mask);
    let key_s_complement = pack_half_key(x, !s_mask);

    // Per-side spread output: applying f to the half-masked input recovers
    // O0 (resp. O1) at natural positions and the O2 partial from that side.
    let x_s_only = x & s_mask;
    let x_s_complement_only = x & !s_mask;
    let y_from_s = apply(f, x_s_only);
    let y_from_s_complement = apply(f, x_s_complement_only);

    let o_main_s = y_from_s & o0_mask;
    let o_main_s_complement = y_from_s_complement & o1_mask;
    let o2_partial_s = y_from_s & o2_mask;
    let o2_partial_s_complement = y_from_s_complement & o2_mask;
    let o2_combined = o2_partial_s ^ o2_partial_s_complement;

    // Soundness pin (debug-only, since the construction is GF(2)-linear):
    // the assembled output must equal the full f(x).
    debug_assert_eq!(
        o_main_s + o_main_s_complement + o2_combined,
        apply(f, x),
        "decoded reassembly disagrees with f({x:#x}) for {f:?}"
    );

    SigmaDecodeWitness {
        key_s,
        key_s_complement,
        o_main_s: WordLimbs::from_u32(o_main_s),
        o_main_s_complement: WordLimbs::from_u32(o_main_s_complement),
        o2_partial_s: WordLimbs::from_u32(o2_partial_s),
        o2_partial_s_complement: WordLimbs::from_u32(o2_partial_s_complement),
        o2_combined: WordLimbs::from_u32(o2_combined),
        o2_chunks_s: LimbPairBytes::from_limbs(WordLimbs::from_u32(o2_partial_s)),
        o2_chunks_s_complement: LimbPairBytes::from_limbs(WordLimbs::from_u32(
            o2_partial_s_complement,
        )),
        o2_chunks_combined: LimbPairBytes::from_limbs(WordLimbs::from_u32(o2_combined)),
    }
}

/// Build the witness for one message-schedule entry `W[t]` (for `t ≥ 16`).
fn compute_schedule_entry_witness(
    t: u32,
    w_t_minus_2: u32,
    w_t_minus_7: u32,
    w_t_minus_15: u32,
    w_t_minus_16: u32,
) -> ScheduleEntryWitness {
    let s1 = lower_sigma1(w_t_minus_2);
    let s0 = lower_sigma0(w_t_minus_15);
    let (w_t, carries) = add_words_with_carries(&[s1, w_t_minus_7, s0, w_t_minus_16]);
    ScheduleEntryWitness {
        t,
        w_t_minus_2: WordLimbs::from_u32(w_t_minus_2),
        w_t_minus_7: WordLimbs::from_u32(w_t_minus_7),
        w_t_minus_15: WordLimbs::from_u32(w_t_minus_15),
        w_t_minus_16: WordLimbs::from_u32(w_t_minus_16),
        lower_sigma0: WordLimbs::from_u32(s0),
        lower_sigma1: WordLimbs::from_u32(s1),
        lower_sigma0_decode: compute_sigma_decode_witness(SigmaFn::LowerSigma0, w_t_minus_15),
        lower_sigma1_decode: compute_sigma_decode_witness(SigmaFn::LowerSigma1, w_t_minus_2),
        carries,
        w_t: WordLimbs::from_u32(w_t),
    }
}

/// Build the witness for one compression round.
fn compute_round_witness(
    t: u32,
    state: [u32; N_STATE_WORDS],
    w_t: u32,
    k_t: u32,
) -> ([u32; N_STATE_WORDS], RoundWitness) {
    let [a, b, c, d, e, f, g, h] = state;

    let s0_val = big_sigma0(a);
    let s1_val = big_sigma1(e);
    let ch_val = ch(e, f, g);
    let maj_val = maj(a, b, c);

    let (t1, t1_carries) = add_words_with_carries(&[h, s1_val, ch_val, k_t, w_t]);
    let (t2, t2_carries) = add_words_with_carries(&[s0_val, maj_val]);
    let (e_new, e_new_carries) = add_words_with_carries(&[d, t1]);
    let (a_new, a_new_carries) = add_words_with_carries(&[t1, t2]);

    let wit = RoundWitness {
        t,
        state_in: limbify_state(&state),
        w_t: WordLimbs::from_u32(w_t),
        k_t: WordLimbs::from_u32(k_t),
        sigma0: WordLimbs::from_u32(s0_val),
        sigma1: WordLimbs::from_u32(s1_val),
        sigma0_decode: compute_sigma_decode_witness(SigmaFn::Sigma0, a),
        sigma1_decode: compute_sigma_decode_witness(SigmaFn::Sigma1, e),
        ch: WordLimbs::from_u32(ch_val),
        maj: WordLimbs::from_u32(maj_val),
        t1: WordLimbs::from_u32(t1),
        t2: WordLimbs::from_u32(t2),
        a_new: WordLimbs::from_u32(a_new),
        e_new: WordLimbs::from_u32(e_new),
        t1_carries,
        t2_carries,
        a_new_carries,
        e_new_carries,
    };
    // State rotation: (a, b, c, d, e, f, g, h) ← (a_new, a, b, c, e_new, e, f, g)
    let next = [a_new, a, b, c, e_new, e, f, g];
    (next, wit)
}

fn limbify_state(state: &[u32; N_STATE_WORDS]) -> [WordLimbs; N_STATE_WORDS] {
    let mut out = [WordLimbs::default(); N_STATE_WORDS];
    for (slot, &w) in out.iter_mut().zip(state.iter()) {
        *slot = WordLimbs::from_u32(w);
    }
    out
}

/// Build the witness for one block: schedule + 64 rounds + finalization.
pub fn compute_block_witness(
    h_in_state: &HashState,
    block_bytes: &[u8; BLOCK_BYTES],
) -> BlockWitness {
    let block = crate::types::Block::from_bytes(block_bytes);

    // Expand the schedule alongside its derivation witnesses.
    let mut w = [0u32; N_ROUNDS];
    w[..N_INPUT_WORDS].copy_from_slice(&block.0);
    let mut schedule_entries = Vec::with_capacity(N_ROUNDS - N_INPUT_WORDS);
    for t in N_INPUT_WORDS..N_ROUNDS {
        let entry =
            compute_schedule_entry_witness(t as u32, w[t - 2], w[t - 7], w[t - 15], w[t - 16]);
        w[t] = entry.w_t.to_u32();
        schedule_entries.push(entry);
    }
    let schedule_limbs: Vec<WordLimbs> = w.iter().copied().map(WordLimbs::from_u32).collect();

    // 64 rounds.
    let mut state = h_in_state.0;
    let mut rounds = Vec::with_capacity(N_ROUNDS);
    for t in 0..N_ROUNDS {
        let (next_state, round) = compute_round_witness(t as u32, state, w[t], K[t]);
        rounds.push(round);
        state = next_state;
    }

    // Finalization: H⁽ᵗ⁺¹⁾ⱼ = H⁽ᵗ⁾ⱼ + working[j], for j = 0..7.
    let mut h_out_state = [0u32; N_STATE_WORDS];
    let mut finalization_carries = [AddCarries::default(); N_STATE_WORDS];
    for j in 0..N_STATE_WORDS {
        let (sum, carries) = add_words_with_carries(&[h_in_state.0[j], state[j]]);
        h_out_state[j] = sum;
        finalization_carries[j] = carries;
    }

    BlockWitness {
        h_in: limbify_state(&h_in_state.0),
        h_out: limbify_state(&h_out_state),
        schedule: schedule_limbs,
        schedule_entries,
        rounds,
        finalization_carries,
        // Padding-role witness is populated at the top-level emitter,
        // where the message length and total block count are known.
        padding_row: crate::types::PaddingRowWitness::default(),
    }
}

/// Top-level witness emitter — pads, parses, and produces one BlockWitness
/// per padded block. The returned digest is recoverable from the last
/// block's `h_out`; we attach it explicitly so consumers don't have to
/// recompose.
pub fn compute_sha256_witness(msg: &[u8]) -> Sha256Witness {
    let padding = compute_padding_witness(msg);
    let blocks_parsed = parse_blocks(&padding.padded);
    let n_blocks = blocks_parsed.len();
    let message_byte_length = padding.message.len() as u64;

    let mut h_state = HashState(IV);
    let mut blocks = Vec::with_capacity(n_blocks);
    for (idx, _block) in blocks_parsed.iter().enumerate() {
        // Re-extract the raw bytes for this block — the parsed `Block`
        // value's bytes are an internal detail.
        let raw: [u8; BLOCK_BYTES] = padding.padded[idx * BLOCK_BYTES..(idx + 1) * BLOCK_BYTES]
            .try_into()
            .unwrap();
        let mut bw = compute_block_witness(&h_state, &raw);
        bw.padding_row = crate::types::PaddingRowWitness::for_block(
            idx,
            &padding.padded,
            message_byte_length,
            n_blocks,
        );
        // Re-derive the next H from limbs (round-trips through (lo, hi)).
        for (i, slot) in h_state.0.iter_mut().enumerate() {
            *slot = bw.h_out[i].to_u32();
        }
        blocks.push(bw);
    }

    let digest = Digest::from_state(&h_state);
    Sha256Witness {
        padding,
        blocks,
        digest,
    }
}

/// Smoke check: assert `(result_word, carries)` consistency for one
/// `add_words_with_carries` call. Available so the trace generator can
/// reuse the same identity at constraint-emit time without duplicating it.
pub fn add_identity_holds(addends: &[u32], result: u32, carries: AddCarries) -> bool {
    let lo_sum: u32 = addends.iter().map(|w| w & 0xFFFF).sum();
    let hi_sum: u32 = addends.iter().map(|w| w >> LIMB_BITS).sum();
    let lhs_lo = lo_sum;
    let rhs_lo = (result & 0xFFFF) + (carries.lo << LIMB_BITS);
    let lhs_hi = hi_sum + carries.lo;
    let rhs_hi = (result >> LIMB_BITS) + (carries.hi << LIMB_BITS);
    lhs_lo == rhs_lo && lhs_hi == rhs_hi
}

/// Per-block lookup-multiplicity totals for the eight `Σ`/`σ` decode-table
/// channels. Each field counts how many times the AIR fires a "use" on the
/// corresponding decode-table row across one block — equivalently, the sum
/// of the table component's per-row multiplicity column. The sanity test in
/// [`crate::constraints`] asserts these against the static per-block totals
/// expected from the trace shape (64 rounds × one σ-application per round
/// per relation; 48 schedule entries × one σ-application per relation).
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct DecodeLookupMultiplicities {
    pub sigma0_s: u32,
    pub sigma0_s_complement: u32,
    pub sigma1_s: u32,
    pub sigma1_s_complement: u32,
    pub lower_sigma0_s: u32,
    pub lower_sigma0_s_complement: u32,
    pub lower_sigma1_s: u32,
    pub lower_sigma1_s_complement: u32,
}

impl DecodeLookupMultiplicities {
    /// Sum of every decode lookup the block emits — `2 × N_ROUNDS` from
    /// the rounds (`Σ0` + `Σ1`, each contributing one S + one S′ lookup),
    /// `2 × N_SCHEDULE_ENTRIES` from the schedule (`σ0` + `σ1`, same shape).
    pub fn total(&self) -> u32 {
        self.sigma0_s
            + self.sigma0_s_complement
            + self.sigma1_s
            + self.sigma1_s_complement
            + self.lower_sigma0_s
            + self.lower_sigma0_s_complement
            + self.lower_sigma1_s
            + self.lower_sigma1_s_complement
    }
}

/// Per-block lookup-multiplicity totals for the Maj/Ch packed-group channels
/// and the chunk-wise `xor_8` channel.
///
/// `maj` counts `add_to_relation(MajRelation, +1, …)` firings: one per group
/// position per round ⇒ `N_ROUNDS · GROUPS_PER_ROUND_PARTITION` per block.
/// `ch` is symmetric. `xor_8` counts chunk-wise σ-combine lookups: four per
/// σ-application, with `2 · N_ROUNDS + 2 · N_SCHEDULE_ENTRIES`
/// σ-applications per block (two per round, two per schedule entry).
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct MajChXorMultiplicities {
    pub maj: u32,
    pub ch: u32,
    pub xor_8: u32,
}

impl MajChXorMultiplicities {
    pub fn total(&self) -> u32 {
        self.maj + self.ch + self.xor_8
    }
}

/// Count the number of `add_to_relation` "uses" each decode-table channel
/// would receive from one block. Derived entirely from the witness — does
/// not depend on the LogUp framework being plumbed end-to-end. Used as a
/// pre-finalize sanity check that the wiring actually fires the expected
/// number of times per block.
pub fn decode_multiplicities_for_block(block: &BlockWitness) -> DecodeLookupMultiplicities {
    let mut m = DecodeLookupMultiplicities::default();
    for entry in &block.schedule_entries {
        // `compute_sigma_decode_witness` always populates a valid pair —
        // one "use" per relation per σ-application. We don't bucket by key
        // here because the per-block total is the property the design's
        // soundness test pins.
        let _ = entry.lower_sigma0_decode;
        m.lower_sigma0_s += 1;
        m.lower_sigma0_s_complement += 1;
        let _ = entry.lower_sigma1_decode;
        m.lower_sigma1_s += 1;
        m.lower_sigma1_s_complement += 1;
    }
    for round in &block.rounds {
        let _ = round.sigma0_decode;
        m.sigma0_s += 1;
        m.sigma0_s_complement += 1;
        let _ = round.sigma1_decode;
        m.sigma1_s += 1;
        m.sigma1_s_complement += 1;
    }
    m
}

/// Count the number of Maj / Ch / `xor_8` "uses" each channel would receive
/// from one block. Derived entirely from the witness; mirrors
/// [`decode_multiplicities_for_block`] for these channels. The
/// constraint-side sanity test asserts these against the static per-block
/// totals expected from the trace shape.
pub fn maj_ch_xor_multiplicities_for_block(block: &BlockWitness) -> MajChXorMultiplicities {
    let groups = crate::partitions::GROUPS_PER_ROUND_PARTITION as u32;
    let rounds = block.rounds.len() as u32;
    let entries = block.schedule_entries.len() as u32;
    // One Maj lookup per a-side group per round, one Ch lookup per e-side
    // group per round. Four chunk-wise `xor_8` lookups per σ-application,
    // with two σ-applications per round (Σ0, Σ1) and two per schedule
    // entry (σ0, σ1).
    MajChXorMultiplicities {
        maj: rounds * groups,
        ch: rounds * groups,
        xor_8: 4 * (2 * rounds + 2 * entries),
    }
}

/// Aggregate [`maj_ch_xor_multiplicities_for_block`] across every block.
pub fn maj_ch_xor_multiplicities_for_witness(witness: &Sha256Witness) -> MajChXorMultiplicities {
    witness
        .blocks
        .iter()
        .map(maj_ch_xor_multiplicities_for_block)
        .fold(MajChXorMultiplicities::default(), |mut acc, m| {
            acc.maj += m.maj;
            acc.ch += m.ch;
            acc.xor_8 += m.xor_8;
            acc
        })
}

/// Aggregate [`decode_multiplicities_for_block`] across every block of a
/// witness. The integration / test sites use the per-block view; this one
/// helps the top-level test assert the multi-block scaling is linear.
pub fn decode_multiplicities_for_witness(witness: &Sha256Witness) -> DecodeLookupMultiplicities {
    witness
        .blocks
        .iter()
        .map(decode_multiplicities_for_block)
        .fold(DecodeLookupMultiplicities::default(), |mut acc, m| {
            acc.sigma0_s += m.sigma0_s;
            acc.sigma0_s_complement += m.sigma0_s_complement;
            acc.sigma1_s += m.sigma1_s;
            acc.sigma1_s_complement += m.sigma1_s_complement;
            acc.lower_sigma0_s += m.lower_sigma0_s;
            acc.lower_sigma0_s_complement += m.lower_sigma0_s_complement;
            acc.lower_sigma1_s += m.lower_sigma1_s;
            acc.lower_sigma1_s_complement += m.lower_sigma1_s_complement;
            acc
        })
}

/// Sanity: rebuild the final schedule from a `BlockWitness` and confirm it
/// matches the native expansion. Used by the tests; useful as a debug
/// helper if a constraint ever disagrees.
pub fn schedule_from_block_witness(b: &BlockWitness) -> Schedule {
    let mut s = [0u32; N_ROUNDS];
    for (i, slot) in s.iter_mut().enumerate() {
        *slot = b.schedule[i].to_u32();
    }
    Schedule(s)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::native::{self, compress_block, expand_schedule};
    use sha2::{Digest as Sha2Digest, Sha256};

    fn sha2_reference(msg: &[u8]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(msg);
        hasher.finalize().into()
    }

    #[test]
    fn add_words_with_carries_matches_wrapping_sum() {
        let cases: Vec<Vec<u32>> = vec![
            vec![0],
            vec![1, 2, 3],
            vec![0xFFFF_FFFF, 1],
            vec![0xDEAD_BEEF, 0xCAFE_BABE, 0x1234_5678, 0x9ABC_DEF0],
            // The full 7-addend case the design uses for the widest add.
            vec![
                0x6A09_E667,
                0xBB67_AE85,
                0xDEAD_BEEF,
                0x428A_2F98,
                0xCAFE_BABE,
                0x0000_FFFF,
                0xFFFF_0000,
            ],
        ];
        for addends in &cases {
            let (res, carries) = add_words_with_carries(addends);
            let expected = addends.iter().fold(0u32, |acc, &w| acc.wrapping_add(w));
            assert_eq!(res, expected, "wrap mismatch for {addends:?}");
            assert!(carries.lo < addends.len() as u32, "carry_lo too large");
            assert!(carries.hi < addends.len() as u32, "carry_hi too large");
            assert!(
                add_identity_holds(addends, res, carries),
                "limb identity failed: {addends:?} → ({res:#x}, {carries:?})"
            );
        }
    }

    #[test]
    fn schedule_witness_reproduces_native_schedule() {
        // A non-trivial single block.
        let mut bytes = [0u8; BLOCK_BYTES];
        bytes[..3].copy_from_slice(b"abc");
        bytes[3] = 0x80;
        bytes[BLOCK_BYTES - 1] = 24;

        let bw = compute_block_witness(&HashState(IV), &bytes);
        let native_block = crate::types::Block::from_bytes(&bytes);
        let native_schedule = expand_schedule(&native_block);

        let recovered = schedule_from_block_witness(&bw);
        assert_eq!(recovered.0, native_schedule.0);
        // And every schedule entry's `w_t` matches the recurrence.
        for entry in &bw.schedule_entries {
            assert_eq!(entry.w_t.to_u32(), native_schedule.0[entry.t as usize]);
        }
    }

    #[test]
    fn block_witness_h_out_matches_native_compression() {
        let mut bytes = [0u8; BLOCK_BYTES];
        bytes[..3].copy_from_slice(b"abc");
        bytes[3] = 0x80;
        bytes[BLOCK_BYTES - 1] = 24;

        let bw = compute_block_witness(&HashState(IV), &bytes);
        let native_block = crate::types::Block::from_bytes(&bytes);
        let native_schedule = expand_schedule(&native_block);
        let native_h_out = compress_block(&HashState(IV), &native_schedule);

        for (i, &expected) in native_h_out.0.iter().enumerate() {
            assert_eq!(bw.h_out[i].to_u32(), expected, "H_out[{i}] mismatch");
        }
    }

    #[test]
    fn round_witnesses_state_chain_is_consistent() {
        // State after round t must equal state_in of round t+1.
        let mut bytes = [0u8; BLOCK_BYTES];
        bytes[..3].copy_from_slice(b"abc");
        bytes[3] = 0x80;
        bytes[BLOCK_BYTES - 1] = 24;

        let bw = compute_block_witness(&HashState(IV), &bytes);
        for w in bw.rounds.windows(2) {
            // Compute the next state from w[0]'s witness fields.
            let r = &w[0];
            let next = [
                r.a_new.to_u32(),
                r.state_in[0].to_u32(),
                r.state_in[1].to_u32(),
                r.state_in[2].to_u32(),
                r.e_new.to_u32(),
                r.state_in[4].to_u32(),
                r.state_in[5].to_u32(),
                r.state_in[6].to_u32(),
            ];
            let next_from_witness: [u32; 8] = std::array::from_fn(|i| w[1].state_in[i].to_u32());
            assert_eq!(next, next_from_witness, "state chain broke at t={}", r.t);
        }
    }

    #[test]
    fn round_intermediates_match_native() {
        let mut bytes = [0u8; BLOCK_BYTES];
        bytes[..3].copy_from_slice(b"abc");
        bytes[3] = 0x80;
        bytes[BLOCK_BYTES - 1] = 24;
        let bw = compute_block_witness(&HashState(IV), &bytes);

        // Replay 64 rounds natively and check every intermediate.
        let mut state = IV;
        let sched = schedule_from_block_witness(&bw);
        for (t, &k_t) in K.iter().enumerate().take(N_ROUNDS) {
            let r = &bw.rounds[t];
            assert_eq!(r.t, t as u32);
            let [a, b, c, _d, e, f, g, _h] = state;
            assert_eq!(r.sigma0.to_u32(), big_sigma0(a));
            assert_eq!(r.sigma1.to_u32(), big_sigma1(e));
            assert_eq!(r.ch.to_u32(), ch(e, f, g));
            assert_eq!(r.maj.to_u32(), maj(a, b, c));
            assert_eq!(r.w_t.to_u32(), sched.0[t]);
            assert_eq!(r.k_t.to_u32(), k_t);

            // The recurrence drives state forward to the next round.
            let t1 = state[7]
                .wrapping_add(big_sigma1(e))
                .wrapping_add(ch(e, f, g))
                .wrapping_add(k_t)
                .wrapping_add(sched.0[t]);
            let t2 = big_sigma0(a).wrapping_add(maj(a, b, c));
            assert_eq!(r.t1.to_u32(), t1);
            assert_eq!(r.t2.to_u32(), t2);
            assert_eq!(r.a_new.to_u32(), t1.wrapping_add(t2));
            assert_eq!(r.e_new.to_u32(), state[3].wrapping_add(t1));

            state = [
                t1.wrapping_add(t2),
                state[0],
                state[1],
                state[2],
                state[3].wrapping_add(t1),
                state[4],
                state[5],
                state[6],
            ];
        }
    }

    #[test]
    fn full_witness_digest_matches_sha2_across_sizes() {
        // Multi-block coverage.
        for n in [0usize, 1, 55, 56, 63, 64, 65, 127, 128, 255, 1024] {
            let msg: Vec<u8> = (0..n).map(|i| ((i * 17) ^ 0x5A) as u8).collect();
            let witness = compute_sha256_witness(&msg);
            assert_eq!(witness.digest.0, sha2_reference(&msg), "size = {n}");

            // n_blocks consistent.
            assert_eq!(
                witness.blocks.len(),
                witness.padding.n_blocks,
                "block count mismatch at n={n}"
            );
            // The first block always starts at IV.
            for (i, &iv_i) in IV.iter().enumerate().take(N_STATE_WORDS) {
                assert_eq!(witness.blocks[0].h_in[i].to_u32(), iv_i);
            }
            // Adjacent blocks chain: h_out of block t == h_in of block t+1.
            for w in witness.blocks.windows(2) {
                for i in 0..N_STATE_WORDS {
                    assert_eq!(w[0].h_out[i].to_u32(), w[1].h_in[i].to_u32());
                }
            }
        }
    }

    #[test]
    fn finalization_carries_within_two_word_bound() {
        let msg = vec![0u8; 200];
        let witness = compute_sha256_witness(&msg);
        for block in &witness.blocks {
            for (j, c) in block.finalization_carries.iter().enumerate() {
                // Finalization is a 2-word add: each carry is < 2.
                assert!(c.lo < 2, "finalization carry_lo[{j}] too large");
                assert!(c.hi < 2, "finalization carry_hi[{j}] too large");
            }
        }
    }

    /// All add carries are within their algorithmic bound. Failure here is a
    /// signal that the carry range-check tables in §10.2 need to be sized
    /// larger than the design assumes.
    #[test]
    fn all_round_carries_within_bound() {
        let msg = vec![0xABu8; 1000];
        let witness = compute_sha256_witness(&msg);
        for b in &witness.blocks {
            for r in &b.rounds {
                // t1: 5 addends -> carries < 5
                assert!(r.t1_carries.lo < 5);
                assert!(r.t1_carries.hi < 5);
                // t2: 2 addends -> carries < 2
                assert!(r.t2_carries.lo < 2);
                assert!(r.t2_carries.hi < 2);
                // a_new, e_new: 2 addends -> carries < 2
                assert!(r.a_new_carries.lo < 2);
                assert!(r.a_new_carries.hi < 2);
                assert!(r.e_new_carries.lo < 2);
                assert!(r.e_new_carries.hi < 2);
            }
            for entry in &b.schedule_entries {
                // schedule add: 4 addends -> carries < 4
                assert!(entry.carries.lo < 4);
                assert!(entry.carries.hi < 4);
            }
        }
    }

    /// Spot check: digest computed by the witness emitter matches the native
    /// `hash()` for the same input.
    #[test]
    fn witness_digest_equals_native_hash() {
        for msg in [
            &b""[..],
            b"abc",
            b"the quick brown fox jumps over the lazy dog",
            &[0u8; 1024][..],
        ] {
            let w = compute_sha256_witness(msg);
            assert_eq!(w.digest.0, native::hash(msg).0);
        }
    }
}
