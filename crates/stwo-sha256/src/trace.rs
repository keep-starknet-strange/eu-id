//! Trace generation — converts a [`Sha256Witness`] into M31 column data the
//! Stwo prover can commit to.
//!
//! Layout: **one row per padded block**, wide. With `n` blocks the trace has
//! `next_power_of_two(n)` rows; everything past row `n − 1` is padding.
//!
//! A row of the trace carries (in this order):
//!
//! - `enabler` (1 col) — `1` on real rows, `0` on padding rows. Multiplies
//!   every constraint so padding rows are constraint-free.
//! - `is_first_block` (1 col) — `1` on the first block, used by the AIR to
//!   force `h_in == IV` only there.
//! - `h_in` (16 cols) — 8 words × 2 limbs each, little-endian limb order.
//! - schedule words `W[0..63]` (128 cols) — 64 words × 2 limbs.
//! - schedule witnesses for `W[16..63]`: per entry, the `σ0`/`σ1` output
//!   limbs and add carries (`2 + 2 + 2 = 6` cols), then the decoded
//!   intermediates of `σ0` and `σ1` (2 × `SIGMA_DECODE_COLS`). Inputs
//!   (`W[t-2]`, `W[t-7]`, `W[t-15]`, `W[t-16]`) are *not* duplicated here —
//!   they live in the `W` columns above and are read by index in the AIR.
//!   ⇒ `48 × SCHEDULE_ENTRY_COLS` cells.
//! - per-round witnesses for `t ∈ [0, 64)` (`64 × ROUND_COLS` cols).
//!   See [`Layout::round_col`] for the per-round shape.
//! - finalization carries (16 cols) — 8 words × `(lo, hi)`.
//! - `h_out` (16 cols).
//!
//! Per-round cells (`ROUND_COLS`): `σ0`, `σ1`, `ch`, `maj`, `t1`, `t2`,
//! `a_new`, `e_new` (each `(lo, hi)` ⇒ 16 cells) plus 4 add carry pairs
//! (⇒ 8 cells), then the decoded intermediates of `Σ0(a)` and `Σ1(e)`
//! (2 × `SIGMA_DECODE_COLS`). The decode intermediates are appended after
//! the existing limb-add columns so the existing constraint reads stay in
//! place and the new decode-table `add_to_relation` calls / reassembly /
//! chunk-bind constraints read from a single contiguous range.
//!
//! Per σ-application (`SIGMA_DECODE_COLS = 24`):
//! `key_s, o_main_s.lo, o_main_s.hi, o2_partial_s.lo, o2_partial_s.hi,
//!  key_s_complement, o_main_s_complement.lo, o_main_s_complement.hi,
//!  o2_partial_s_complement.lo, o2_partial_s_complement.hi,
//!  o2_combined.lo, o2_combined.hi,
//!  o2_chunks_s (4 bytes),
//!  o2_chunks_s_complement (4 bytes),
//!  o2_chunks_combined (4 bytes)`.
//! The two 5-tuples `[key, o_main_lo, o_main_hi, o2_partial_lo, o2_partial_hi]`
//! at offsets 0 and 5 are the decode-table lookup keys for the S-side and
//! S′-side respectively — sharing the read order with the lookup tuple
//! keeps the AIR `add_to_relation` calls trivially aligned.

use stwo::core::fields::m31::{BaseField, M31};

use crate::constants::{N_ROUNDS, N_STATE_WORDS};
use crate::types::{
    AddCarries, BlockWitness, LimbPairBytes, Sha256Witness, SigmaDecodeWitness, WordLimbs,
};

/// Columns per σ-application's decoded intermediates (§9.3 of the design):
/// `key_s, o_main_s (lo, hi), o2_partial_s (lo, hi), key_s_complement,
///  o_main_s_complement (lo, hi), o2_partial_s_complement (lo, hi),
///  o2_combined (lo, hi), 3 × 4-byte chunk sets`.
///
/// The leading 5 cells (`key_s + o_main_s + o2_partial_s`) match the row
/// shape of the `S`-side decode table and the trailing 5 cells of the first
/// half (`key_s_complement + …`) match the `S′`-side table — so the
/// constraint loop's `add_to_relation` keys read in column order without
/// re-permutation.
pub const SIGMA_DECODE_COLS: usize = 5 + 5 + 2 + 4 + 4 + 4;
/// Columns per round: 8 word-results × 2 limbs + 4 carry pairs × 2 ends = 24,
/// then two σ-decodes (one for `Σ0(a)`, one for `Σ1(e)`).
pub const ROUND_COLS: usize = 8 * 2 + 4 * 2 + 2 * SIGMA_DECODE_COLS;
/// Columns per schedule entry (`W[t]` for `t ≥ 16`):
/// `σ0`, `σ1`, carries (= 6), then two σ-decodes (one for `σ0(W[t-15])`,
/// one for `σ1(W[t-2])`).
pub const SCHEDULE_ENTRY_COLS: usize = 6 + 2 * SIGMA_DECODE_COLS;
/// Number of schedule entries: `W[16..64]` ⇒ 48.
pub const N_SCHEDULE_ENTRIES: usize = N_ROUNDS - 16;

/// Named column-range layout. Every range is in `[start, end)`; the column
/// index in `Vec<Vec<BaseField>>` equals the start-of-range offset plus any
/// per-element offset.
pub struct Layout;

impl Layout {
    pub const COL_ENABLER: usize = 0;
    pub const COL_IS_FIRST_BLOCK: usize = 1;
    pub const COL_H_IN_START: usize = 2;
    pub const COL_H_IN_END: usize = Self::COL_H_IN_START + 2 * N_STATE_WORDS;
    pub const COL_SCHED_START: usize = Self::COL_H_IN_END;
    pub const COL_SCHED_END: usize = Self::COL_SCHED_START + 2 * N_ROUNDS;
    pub const COL_SCHED_ENTRY_START: usize = Self::COL_SCHED_END;
    pub const COL_SCHED_ENTRY_END: usize =
        Self::COL_SCHED_ENTRY_START + N_SCHEDULE_ENTRIES * SCHEDULE_ENTRY_COLS;
    pub const COL_ROUND_START: usize = Self::COL_SCHED_ENTRY_END;
    pub const COL_ROUND_END: usize = Self::COL_ROUND_START + N_ROUNDS * ROUND_COLS;
    pub const COL_FINAL_CARRIES_START: usize = Self::COL_ROUND_END;
    pub const COL_FINAL_CARRIES_END: usize = Self::COL_FINAL_CARRIES_START + 2 * N_STATE_WORDS;
    pub const COL_H_OUT_START: usize = Self::COL_FINAL_CARRIES_END;
    pub const COL_H_OUT_END: usize = Self::COL_H_OUT_START + 2 * N_STATE_WORDS;

    /// Total number of columns in the trace.
    pub const TOTAL_COLS: usize = Self::COL_H_OUT_END;

    /// `(lo, hi)` slot for the `j`-th word of `h_in`.
    #[inline]
    pub const fn h_in_word(j: usize) -> (usize, usize) {
        let base = Self::COL_H_IN_START + 2 * j;
        (base, base + 1)
    }

    /// `(lo, hi)` slot for `W[t]` (`t ∈ [0, 64)`).
    #[inline]
    pub const fn schedule_word(t: usize) -> (usize, usize) {
        let base = Self::COL_SCHED_START + 2 * t;
        (base, base + 1)
    }

    /// Columns of one schedule entry, in order: `σ0_lo, σ0_hi, σ1_lo, σ1_hi,
    /// carry_lo, carry_hi`, then two σ-decode blocks.
    /// Entry index `j ∈ [0, 48)` corresponds to `W[16+j]`. Only the leading
    /// 6 cells are returned here — the decode blocks are addressed by
    /// [`Self::schedule_entry_decode`] since their offset is fixed.
    #[inline]
    pub const fn schedule_entry(j: usize) -> [usize; 6] {
        let base = Self::COL_SCHED_ENTRY_START + j * SCHEDULE_ENTRY_COLS;
        [base, base + 1, base + 2, base + 3, base + 4, base + 5]
    }

    /// Start column of one σ-decode block of one schedule entry. `which` is
    /// `0` for `σ0(W[t-15])`, `1` for `σ1(W[t-2])` — the order written by
    /// [`write_block_row`] and read by `constraints::Sha256Eval`.
    #[inline]
    pub const fn schedule_entry_decode(j: usize, which: usize) -> usize {
        let base = Self::COL_SCHED_ENTRY_START + j * SCHEDULE_ENTRY_COLS;
        base + 6 + which * SIGMA_DECODE_COLS
    }

    /// Start column of one σ-decode block of one round. `which` is `0` for
    /// `Σ0(a)`, `1` for `Σ1(e)` — matching the witness field order and the
    /// AIR read order. The 24 cells starting here are a single
    /// `SigmaDecodeWitness`, laid out per [`SIGMA_DECODE_COLS`] above.
    #[inline]
    pub const fn round_decode(t: usize, which: usize) -> usize {
        let base = Self::COL_ROUND_START + t * ROUND_COLS;
        base + 24 + which * SIGMA_DECODE_COLS
    }

    /// One round's columns, in order:
    /// `σ0_lo, σ0_hi, σ1_lo, σ1_hi, ch_lo, ch_hi, maj_lo, maj_hi,
    ///  t1_lo, t1_hi, t2_lo, t2_hi, a_new_lo, a_new_hi, e_new_lo, e_new_hi,
    ///  t1_carry_lo, t1_carry_hi, t2_carry_lo, t2_carry_hi,
    ///  e_new_carry_lo, e_new_carry_hi, a_new_carry_lo, a_new_carry_hi`.
    #[inline]
    pub const fn round_col(t: usize) -> [usize; ROUND_COLS] {
        let base = Self::COL_ROUND_START + t * ROUND_COLS;
        let mut out = [0; ROUND_COLS];
        let mut i = 0;
        while i < ROUND_COLS {
            out[i] = base + i;
            i += 1;
        }
        out
    }

    /// `(lo, hi)` slot for the `j`-th word of `h_out`.
    #[inline]
    pub const fn h_out_word(j: usize) -> (usize, usize) {
        let base = Self::COL_H_OUT_START + 2 * j;
        (base, base + 1)
    }

    /// `(lo_carry, hi_carry)` slot for the `j`-th finalization add.
    #[inline]
    pub const fn final_carry(j: usize) -> (usize, usize) {
        let base = Self::COL_FINAL_CARRIES_START + 2 * j;
        (base, base + 1)
    }
}

/// Materialise the trace for a `Sha256Witness`.
///
/// Returns `Vec<Vec<BaseField>>`, one inner `Vec` per column. Length of
/// every inner `Vec` equals `1 << log_size`, padded with zeros past the
/// number of real rows.
///
/// Choose `log_size` so that `(1 << log_size) >= witness.blocks.len()`.
/// The function panics otherwise.
pub fn generate_trace(witness: &Sha256Witness, log_size: u32) -> Vec<Vec<BaseField>> {
    let n_rows = 1usize << log_size;
    assert!(
        witness.blocks.len() <= n_rows,
        "trace too small: {} blocks > {} rows",
        witness.blocks.len(),
        n_rows
    );

    let mut cols = vec![vec![BaseField::from(0u32); n_rows]; Layout::TOTAL_COLS];

    for (block_idx, block) in witness.blocks.iter().enumerate() {
        write_block_row(&mut cols, block_idx, block, block_idx == 0);
    }

    cols
}

/// Write all columns of one row from one `BlockWitness`.
fn write_block_row(
    cols: &mut [Vec<BaseField>],
    row: usize,
    block: &BlockWitness,
    is_first_block: bool,
) {
    cols[Layout::COL_ENABLER][row] = BaseField::from(1u32);
    cols[Layout::COL_IS_FIRST_BLOCK][row] = BaseField::from(is_first_block as u32);

    // h_in
    for j in 0..N_STATE_WORDS {
        let (lo, hi) = Layout::h_in_word(j);
        cols[lo][row] = m31(block.h_in[j].lo);
        cols[hi][row] = m31(block.h_in[j].hi);
    }

    // schedule W[0..63]
    for t in 0..N_ROUNDS {
        let (lo, hi) = Layout::schedule_word(t);
        cols[lo][row] = m31(block.schedule[t].lo);
        cols[hi][row] = m31(block.schedule[t].hi);
    }

    // schedule entries for W[16..63]
    for (j, entry) in block.schedule_entries.iter().enumerate() {
        let [s0_lo, s0_hi, s1_lo, s1_hi, c_lo, c_hi] = Layout::schedule_entry(j);
        cols[s0_lo][row] = m31(entry.lower_sigma0.lo);
        cols[s0_hi][row] = m31(entry.lower_sigma0.hi);
        cols[s1_lo][row] = m31(entry.lower_sigma1.lo);
        cols[s1_hi][row] = m31(entry.lower_sigma1.hi);
        cols[c_lo][row] = m31(entry.carries.lo);
        cols[c_hi][row] = m31(entry.carries.hi);

        write_sigma_decode_block(
            cols,
            row,
            Layout::schedule_entry_decode(j, 0),
            &entry.lower_sigma0_decode,
        );
        write_sigma_decode_block(
            cols,
            row,
            Layout::schedule_entry_decode(j, 1),
            &entry.lower_sigma1_decode,
        );
    }

    // 64 rounds
    for (t, round) in block.rounds.iter().enumerate() {
        let r = Layout::round_col(t);
        let limb_pairs: [WordLimbs; 8] = [
            round.sigma0,
            round.sigma1,
            round.ch,
            round.maj,
            round.t1,
            round.t2,
            round.a_new,
            round.e_new,
        ];
        for (i, lw) in limb_pairs.iter().enumerate() {
            cols[r[2 * i]][row] = m31(lw.lo);
            cols[r[2 * i + 1]][row] = m31(lw.hi);
        }
        let carry_pairs: [AddCarries; 4] = [
            round.t1_carries,
            round.t2_carries,
            round.e_new_carries,
            round.a_new_carries,
        ];
        for (i, c) in carry_pairs.iter().enumerate() {
            cols[r[16 + 2 * i]][row] = m31(c.lo);
            cols[r[16 + 2 * i + 1]][row] = m31(c.hi);
        }

        write_sigma_decode_block(cols, row, Layout::round_decode(t, 0), &round.sigma0_decode);
        write_sigma_decode_block(cols, row, Layout::round_decode(t, 1), &round.sigma1_decode);
    }

    // finalization carries
    for (j, c) in block.finalization_carries.iter().enumerate() {
        let (lo, hi) = Layout::final_carry(j);
        cols[lo][row] = m31(c.lo);
        cols[hi][row] = m31(c.hi);
    }

    // h_out
    for j in 0..N_STATE_WORDS {
        let (lo, hi) = Layout::h_out_word(j);
        cols[lo][row] = m31(block.h_out[j].lo);
        cols[hi][row] = m31(block.h_out[j].hi);
    }
}

#[inline]
fn m31(x: u32) -> BaseField {
    // The witness emitter guarantees x ∈ [0, 2¹⁶) for limbs and small bounds
    // for carries — both are well within M31 = [0, 2³¹ − 1).
    M31::from(x)
}

/// Lay out one [`SigmaDecodeWitness`] into `SIGMA_DECODE_COLS` contiguous
/// columns starting at `base`. The order matches the per-σ-application read
/// order documented on [`SIGMA_DECODE_COLS`] above and the lookup-tuple
/// shape used by the AIR's `add_to_relation` calls.
fn write_sigma_decode_block(
    cols: &mut [Vec<BaseField>],
    row: usize,
    base: usize,
    d: &SigmaDecodeWitness,
) {
    // S-side decode-table lookup tuple (5 cells, read as one slice).
    cols[base][row] = m31(d.key_s);
    cols[base + 1][row] = m31(d.o_main_s.lo);
    cols[base + 2][row] = m31(d.o_main_s.hi);
    cols[base + 3][row] = m31(d.o2_partial_s.lo);
    cols[base + 4][row] = m31(d.o2_partial_s.hi);
    // S′-side decode-table lookup tuple (5 cells).
    cols[base + 5][row] = m31(d.key_s_complement);
    cols[base + 6][row] = m31(d.o_main_s_complement.lo);
    cols[base + 7][row] = m31(d.o_main_s_complement.hi);
    cols[base + 8][row] = m31(d.o2_partial_s_complement.lo);
    cols[base + 9][row] = m31(d.o2_partial_s_complement.hi);
    // O2-combined limbs.
    cols[base + 10][row] = m31(d.o2_combined.lo);
    cols[base + 11][row] = m31(d.o2_combined.hi);
    // Byte chunks of the three O2 values — input to the `xor_8` chunk-wise
    // lookup wired in the follow-on task. The chunk-bind linear constraints
    // pin each `(b0, b1)` pair to its limb.
    write_chunk_quad(cols, row, base + 12, d.o2_chunks_s);
    write_chunk_quad(cols, row, base + 16, d.o2_chunks_s_complement);
    write_chunk_quad(cols, row, base + 20, d.o2_chunks_combined);
}

/// Write one [`LimbPairBytes`] (4 byte cells: `lo.b0, lo.b1, hi.b0, hi.b1`)
/// starting at `base`.
#[inline]
fn write_chunk_quad(cols: &mut [Vec<BaseField>], row: usize, base: usize, chunks: LimbPairBytes) {
    cols[base][row] = m31(chunks.lo.b0);
    cols[base + 1][row] = m31(chunks.lo.b1);
    cols[base + 2][row] = m31(chunks.hi.b0);
    cols[base + 3][row] = m31(chunks.hi.b1);
}

/// Required `log_size` for `n_blocks` blocks (smallest power of two
/// `≥ n_blocks`, and at least `LOG_MIN` so SIMD backends are happy).
pub fn min_log_size(n_blocks: usize) -> u32 {
    const LOG_MIN: u32 = 4; // SIMD lane count is 16 → at least 16 rows.
    let needed = (n_blocks.max(1)).next_power_of_two().ilog2();
    needed.max(LOG_MIN)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::witness::compute_sha256_witness;
    use sha2::{Digest as Sha2Digest, Sha256};

    fn sha2_reference(msg: &[u8]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(msg);
        hasher.finalize().into()
    }

    /// Round-trip: trace materialised from a witness, decoded back, yields
    /// the same digest as sha2.
    fn round_trip_digest(msg: &[u8]) {
        let witness = compute_sha256_witness(msg);
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);

        assert_eq!(trace.len(), Layout::TOTAL_COLS);
        let n_rows = 1usize << log_size;
        for col in &trace {
            assert_eq!(col.len(), n_rows);
        }

        // Decode the last block's h_out from the trace, recompose the digest.
        let last = witness.blocks.len() - 1;
        let mut digest_bytes = [0u8; 32];
        for j in 0..N_STATE_WORDS {
            let (lo, hi) = Layout::h_out_word(j);
            let lo_val = trace[lo][last].0;
            let hi_val = trace[hi][last].0;
            let word = lo_val | (hi_val << 16);
            digest_bytes[j * 4..(j + 1) * 4].copy_from_slice(&word.to_be_bytes());
        }
        assert_eq!(digest_bytes, sha2_reference(msg));
    }

    #[test]
    fn single_block_round_trip() {
        round_trip_digest(b"abc");
    }

    #[test]
    fn multi_block_round_trip() {
        round_trip_digest(&[0xAB; 200]);
    }

    #[test]
    fn empty_message_round_trip() {
        round_trip_digest(b"");
    }

    #[test]
    fn enabler_and_first_block_flags_are_correct() {
        let witness = compute_sha256_witness(&[0u8; 200]);
        let n_real = witness.blocks.len();
        let log_size = min_log_size(n_real);
        let trace = generate_trace(&witness, log_size);
        let n_rows = 1usize << log_size;

        for row in 0..n_rows {
            let expected_enabler = if row < n_real { 1u32 } else { 0 };
            let expected_first = if row == 0 { 1u32 } else { 0 };
            assert_eq!(trace[Layout::COL_ENABLER][row].0, expected_enabler);
            assert_eq!(trace[Layout::COL_IS_FIRST_BLOCK][row].0, expected_first);
        }
    }

    #[test]
    fn h_in_of_first_block_is_iv() {
        use crate::constants::IV;
        let witness = compute_sha256_witness(b"");
        let trace = generate_trace(&witness, min_log_size(witness.blocks.len()));
        for (j, &iv_j) in IV.iter().enumerate().take(N_STATE_WORDS) {
            let (lo, hi) = Layout::h_in_word(j);
            let lo_val = trace[lo][0].0;
            let hi_val = trace[hi][0].0;
            let word = lo_val | (hi_val << 16);
            assert_eq!(word, iv_j, "h_in[{j}] != IV[{j}]");
        }
    }

    #[test]
    fn block_chain_h_out_to_h_in_continuity() {
        let witness = compute_sha256_witness(&[0xAB; 200]);
        let trace = generate_trace(&witness, min_log_size(witness.blocks.len()));
        for row in 1..witness.blocks.len() {
            for j in 0..N_STATE_WORDS {
                let (h_in_lo, h_in_hi) = Layout::h_in_word(j);
                let (h_out_lo, h_out_hi) = Layout::h_out_word(j);
                assert_eq!(trace[h_in_lo][row].0, trace[h_out_lo][row - 1].0);
                assert_eq!(trace[h_in_hi][row].0, trace[h_out_hi][row - 1].0);
            }
        }
    }

    #[test]
    fn layout_total_cols_matches_expected_breakdown() {
        // Sanity check the byte budget.
        let expected = 1                       // enabler
            + 1                                // is_first_block
            + 2 * N_STATE_WORDS                // h_in
            + 2 * N_ROUNDS                     // schedule
            + N_SCHEDULE_ENTRIES * SCHEDULE_ENTRY_COLS
            + N_ROUNDS * ROUND_COLS
            + 2 * N_STATE_WORDS                // finalization carries
            + 2 * N_STATE_WORDS; // h_out
        assert_eq!(Layout::TOTAL_COLS, expected);
        // And the breakdown matches the explicit tally: the schedule and
        // round blocks each carry a base limb-add column set plus two
        // 24-cell σ-decode blocks (one per σ-application).
        let base_sched = 6;
        let base_round = 24;
        assert_eq!(SCHEDULE_ENTRY_COLS, base_sched + 2 * SIGMA_DECODE_COLS);
        assert_eq!(ROUND_COLS, base_round + 2 * SIGMA_DECODE_COLS);
        assert_eq!(
            expected,
            1 + 1
                + 16
                + 128
                + 48 * (base_sched + 2 * SIGMA_DECODE_COLS)
                + 64 * (base_round + 2 * SIGMA_DECODE_COLS)
                + 16
                + 16
        );
    }

    #[test]
    fn sigma_decode_cell_count_matches_witness_struct() {
        // SIGMA_DECODE_COLS must equal the cell count `write_sigma_decode_block`
        // writes — a regression here would corrupt the AIR's read order and
        // shift the lookup-tuple slices.
        // Cell layout: 5 (S-side tuple) + 5 (S′-side tuple) + 2 (o2_combined)
        // + 3 × 4 (three byte-chunk quads) = 24.
        assert_eq!(SIGMA_DECODE_COLS, 5 + 5 + 2 + 3 * 4);
    }

    #[test]
    fn sigma_decode_block_round_trips_through_trace() {
        // For one block, every σ-decode-block cell read from the trace must
        // match the corresponding `SigmaDecodeWitness` field. This pins
        // `write_sigma_decode_block`'s order against the on-disk layout the
        // AIR reads.
        let witness = compute_sha256_witness(b"abc");
        let trace = generate_trace(&witness, min_log_size(witness.blocks.len()));
        let block = &witness.blocks[0];

        // Schedule σ0 decode of entry j=0 (corresponds to W[16] = σ1(W[14]) + … + σ0(W[1]) + W[0]).
        let entry = &block.schedule_entries[0];
        let base = Layout::schedule_entry_decode(0, 0);
        let d = &entry.lower_sigma0_decode;
        assert_eq!(trace[base][0].0, d.key_s);
        assert_eq!(trace[base + 1][0].0, d.o_main_s.lo);
        assert_eq!(trace[base + 4][0].0, d.o2_partial_s.hi);
        assert_eq!(trace[base + 5][0].0, d.key_s_complement);
        assert_eq!(trace[base + 10][0].0, d.o2_combined.lo);
        assert_eq!(trace[base + 12][0].0, d.o2_chunks_s.lo.b0);
        assert_eq!(trace[base + 15][0].0, d.o2_chunks_s.hi.b1);
        assert_eq!(trace[base + 23][0].0, d.o2_chunks_combined.hi.b1);

        // Round Σ0 decode of round 0 (operating on a = IV[0]).
        let round = &block.rounds[0];
        let base = Layout::round_decode(0, 0);
        let d = &round.sigma0_decode;
        assert_eq!(trace[base][0].0, d.key_s);
        assert_eq!(trace[base + 5][0].0, d.key_s_complement);
        assert_eq!(trace[base + 11][0].0, d.o2_combined.hi);
    }
}
