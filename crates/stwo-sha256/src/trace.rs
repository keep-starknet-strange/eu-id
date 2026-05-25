//! Trace generation — converts a [`Sha256Witness`] into M31 column data the
//! Stwo prover can commit to.
//!
//! Layout: **one row per padded block**, wide. With `n` blocks the trace has
//! `next_power_of_two(n)` *slots* per column. Block `r` is written at the slot
//! returned by [`Layout::block_slot(r, log_size)`] — i.e., in **bit-reversed
//! circle-domain order with coset index = block index**, matching Stwo's
//! standard SIMD/CPU trace convention. Iterating coset indices `0..n` walks
//! the blocks in order, which makes the cross-row mask read at offset `-1`
//! resolve to "the previous block's row" — the basis of the block-chain
//! constraint `h_in[r] == h_out[r-1]` for `r > 0` in [`crate::constraints`].
//! Slots past the last real block remain zeroed and are padding.
//!
//! A row of the trace carries (in this order):
//!
//! - `enabler` (1 col) — `1` on real rows, `0` on padding rows. Multiplies
//!   every constraint so padding rows are constraint-free.
//! - `is_first_block` (1 col) — `1` on the first block, used by the AIR to
//!   force `h_in == IV` only there.
//! - `h_in` (16 cols) — 8 words × 2 limbs each, little-endian limb order.
//! - `H_IN_AUX_GRP_COLS` (24 cols) — per-block split-and-pack of `h_in[1]`,
//!   `h_in[2]`, `h_in[5]`, `h_in[6]` (the §8.1 reuse chain's initial
//!   `b`/`c`/`f`/`g` values that no prior round can supply). 4 operands
//!   × `GROUPS_PER_ROUND_PARTITION` = 24 cells, in the fixed operand
//!   order `[b_init, c_init, f_init, g_init]`.
//! - schedule words `W[0..63]` (128 cols) — 64 words × 2 limbs.
//! - schedule witnesses for `W[16..63]`: per entry, the `σ0`/`σ1` output
//!   limbs and add carries (`2 + 2 + 2 = 6` cols), then the decoded
//!   intermediates of `σ0` and `σ1` (2 × `SIGMA_DECODE_COLS`), then the
//!   σ-input split-and-pack outputs for `σ0(W[t-15])` and `σ1(W[t-2])`
//!   (2 × `SIGMA_INPUT_SPLIT_COLS`). Inputs (`W[t-2]`, `W[t-7]`,
//!   `W[t-15]`, `W[t-16]`) are *not* duplicated here — they live in the
//!   `W` columns above and are read by index in the AIR.
//!   ⇒ `48 × SCHEDULE_ENTRY_COLS` cells.
//! - per-round witnesses for `t ∈ [0, 64)` (`64 × ROUND_COLS` cols).
//!   See [`Layout::round_col`] for the per-round shape.
//! - finalization carries (16 cols) — 8 words × `(lo, hi)`.
//! - `h_out` (16 cols).
//!
//! Per-round cells (`ROUND_COLS`): `σ0`, `σ1`, `ch`, `maj`, `t1`, `t2`,
//! `a_new`, `e_new` (each `(lo, hi)` ⇒ 16 cells) plus 4 add carry pairs
//! (⇒ 8 cells), then the decoded intermediates of `Σ0(a)` and `Σ1(e)`
//! (2 × `SIGMA_DECODE_COLS`), then the Maj/Ch packed-group block
//! (`ROUND_MAJ_CH_COLS`). The decode intermediates are appended after
//! the existing limb-add columns so the existing constraint reads stay in
//! place; the Maj/Ch packed groups are appended at the tail so neither
//! the limb-add nor the σ-decode read order shifts.
//!
//! Per-round Maj/Ch block (`ROUND_MAJ_CH_COLS = 4 · 6 = 24`): packed-group
//! values of each *fresh* operand in the partition-enumeration order
//! (`groups_in_order` — `S[0..3]` then `S'[0..3]`). Operand order is
//! `a, maj_out` (a-side / `SIGMA0_GROUPS`) followed by `e, ch_out`
//! (e-side / `SIGMA1_GROUPS`). `b`, `c`, `f`, `g` are not committed — the
//! §8.1 reuse chain aliases them back to prior-round `a`/`e` columns
//! (and to the per-block `H_IN_AUX_GRP` columns for `t ∈ {0, 1}`). Each
//! cell is one packed group value in
//! `[0, 2^|group|) ⊆ [0, 2^MAX_ROUND_GROUP_BITS)`.
//!
//! Per-schedule-entry σ-input split block (`SIGMA_INPUT_SPLIT_COLS = 4`):
//! `(packed_s_lo, packed_s_complement_lo, packed_s_hi, packed_s_complement_hi)`
//! — the four split-and-pack outputs the σ partition emits per input word.
//! The AIR fires one σ-input split-and-pack lookup per half against the
//! corresponding partition's table, then linearly assembles the σ-decode
//! `key_s` / `key_s_complement` from these four values.
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
use stwo::core::utils::{bit_reverse_index, coset_index_to_circle_domain_index};

use crate::constants::{N_ROUNDS, N_STATE_WORDS};
use crate::partitions::GROUPS_PER_ROUND_PARTITION;
use crate::types::{
    AddCarries, BlockAuxSplitPackWitness, BlockWitness, LimbPairBytes, PaddingRowWitness,
    RoundMajChWitness, RoundPackedGroups, Sha256Witness, SigmaDecodeWitness,
    SigmaInputSplitPackWitness, WordLimbs, BYTES_PER_WORD, WORDS_PER_BLOCK,
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
/// Operands committed by the per-round Maj/Ch packed-group block, post
/// §8.1 reuse: `a, maj_out, e, ch_out` (the four *fresh* operands; the
/// `b`/`c`/`f`/`g` slots of the Maj/Ch lookup keys read from prior rounds'
/// `a`/`e` columns via in-row aliasing).
pub const ROUND_MAJ_CH_OPERANDS: usize = 4;
/// Columns per round dedicated to the Maj/Ch packed-group lookup
/// inputs/outputs. `4 operands · 6 groups = 24`. Each cell is one packed
/// value in `[0, 2^|group|) ⊆ [0, 2^MAX_ROUND_GROUP_BITS)`.
pub const ROUND_MAJ_CH_COLS: usize = ROUND_MAJ_CH_OPERANDS * GROUPS_PER_ROUND_PARTITION;
/// Columns per σ-input split-and-pack block: four packed values
/// `(packed_s_lo, packed_s_complement_lo, packed_s_hi, packed_s_complement_hi)`.
/// The AIR fires one σ split-and-pack lookup per half against the
/// partition's table (rows `(key=word.lo|hi, packed_s, packed_s')`).
pub const SIGMA_INPUT_SPLIT_COLS: usize = 4;
/// Columns per round: 8 word-results × 2 limbs + 4 carry pairs × 2 ends = 24,
/// then two σ-decodes (one for `Σ0(a)`, one for `Σ1(e)`), then the
/// Maj/Ch packed-group block.
pub const ROUND_COLS: usize = 8 * 2 + 4 * 2 + 2 * SIGMA_DECODE_COLS + ROUND_MAJ_CH_COLS;
/// Columns per schedule entry (`W[t]` for `t ≥ 16`):
/// `σ0`, `σ1`, carries (= 6), then two σ-decodes (one for `σ0(W[t-15])`,
/// one for `σ1(W[t-2])`), then two σ-input split-and-pack blocks.
pub const SCHEDULE_ENTRY_COLS: usize = 6 + 2 * SIGMA_DECODE_COLS + 2 * SIGMA_INPUT_SPLIT_COLS;
/// Per-block auxiliary split-and-pack operands for the §8.1 reuse chain:
/// `[b_init = h_in[1]_a-side, c_init = h_in[2]_a-side, f_init = h_in[5]_e-side,
///   g_init = h_in[6]_e-side]`. `h_in[0]`/`h_in[4]` are covered by
/// `a_grp[round 0]`/`e_grp[round 0]` (`a[0]=h_in[0]`, `e[0]=h_in[4]`);
/// `h_in[3]`/`h_in[7]` never enter Σ/Maj/Ch directly.
pub const H_IN_AUX_OPERANDS: usize = 4;
/// Columns dedicated to the per-block auxiliary split-and-pack of the
/// §8.1 reuse chain's initial values. `4 operands · 6 groups = 24` cells
/// per block.
pub const H_IN_AUX_GRP_COLS: usize = H_IN_AUX_OPERANDS * GROUPS_PER_ROUND_PARTITION;
/// Number of schedule entries: `W[16..64]` ⇒ 48.
pub const N_SCHEDULE_ENTRIES: usize = N_ROUNDS - 16;

/// Columns dedicated to the per-block padding-role witness (§10.4 of the
/// validated design). Laid out in the order
/// [`write_padding_row`] writes them:
///
/// 1. `is_marker_block` (1)
/// 2. `is_length_block` (1)
/// 3. `is_length_only_block` (1)  — aux, `(1 − is_marker) · is_length`
/// 4. `is_marker_only_block` (1)  — aux, `is_marker · (1 − is_length)`
/// 5. `is_marker_word[16]` (16)   — one-hot for the marker's word index
/// 6. `marker_byte_sel[4]` (4)    — one-hot for byte-in-word, BE order
/// 7. `marker_word_byte[4]` (4)   — BE byte decomposition of `W[marker_word_idx]`
/// 8. `marker_word_post_strict_15` (1) — aux, cum(15) · (1 − is_length)
/// 9. `bit_length_w14_lo` (1)
/// 10. `bit_length_w14_hi` (1)
/// 11. `bit_length_w15_lo` (1)
/// 12. `bit_length_w15_hi` (1)
///
/// `4 flags + 16 one-hot word selectors + 4 byte selectors + 4 marker bytes
///     + 1 post-strict aux + 4 bit-length limbs = 33` cells per block row.
///     The symmetric `marker_word_post_strict_14` aux was considered but
///     is identically zero on every valid trace (no marker block ever
///     places the marker before `W[14]`); see
///     [`crate::types::PaddingRowWitness`] for the asymmetry rationale.
pub const PADDING_ROW_COLS: usize = 4 + WORDS_PER_BLOCK + BYTES_PER_WORD + BYTES_PER_WORD + 1 + 4;

/// Named column-range layout. Every range is in `[start, end)`; the column
/// index in `Vec<Vec<BaseField>>` equals the start-of-range offset plus any
/// per-element offset.
pub struct Layout;

impl Layout {
    pub const COL_ENABLER: usize = 0;
    pub const COL_IS_FIRST_BLOCK: usize = 1;
    pub const COL_H_IN_START: usize = 2;
    pub const COL_H_IN_END: usize = Self::COL_H_IN_START + 2 * N_STATE_WORDS;
    pub const COL_H_IN_AUX_GRP_START: usize = Self::COL_H_IN_END;
    pub const COL_H_IN_AUX_GRP_END: usize = Self::COL_H_IN_AUX_GRP_START + H_IN_AUX_GRP_COLS;
    pub const COL_SCHED_START: usize = Self::COL_H_IN_AUX_GRP_END;
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

    /// Per-block padding-role region. Appended after `h_out` so the
    /// existing read order in [`crate::constraints::Sha256Eval`] stays
    /// intact — the AIR's `next_trace_mask` walk simply continues into
    /// these columns at the end of the row.
    pub const COL_PADDING_START: usize = Self::COL_H_OUT_END;
    pub const COL_IS_MARKER_BLOCK: usize = Self::COL_PADDING_START;
    pub const COL_IS_LENGTH_BLOCK: usize = Self::COL_PADDING_START + 1;
    pub const COL_IS_LENGTH_ONLY_BLOCK: usize = Self::COL_PADDING_START + 2;
    pub const COL_IS_MARKER_ONLY_BLOCK: usize = Self::COL_PADDING_START + 3;
    pub const COL_IS_MARKER_WORD_START: usize = Self::COL_PADDING_START + 4;
    pub const COL_IS_MARKER_WORD_END: usize = Self::COL_IS_MARKER_WORD_START + WORDS_PER_BLOCK;
    pub const COL_MARKER_BYTE_SEL_START: usize = Self::COL_IS_MARKER_WORD_END;
    pub const COL_MARKER_BYTE_SEL_END: usize = Self::COL_MARKER_BYTE_SEL_START + BYTES_PER_WORD;
    pub const COL_MARKER_WORD_BYTE_START: usize = Self::COL_MARKER_BYTE_SEL_END;
    pub const COL_MARKER_WORD_BYTE_END: usize = Self::COL_MARKER_WORD_BYTE_START + BYTES_PER_WORD;
    pub const COL_MARKER_WORD_POST_STRICT_15: usize = Self::COL_MARKER_WORD_BYTE_END;
    pub const COL_BIT_LENGTH_W14_LO: usize = Self::COL_MARKER_WORD_BYTE_END + 1;
    pub const COL_BIT_LENGTH_W14_HI: usize = Self::COL_MARKER_WORD_BYTE_END + 2;
    pub const COL_BIT_LENGTH_W15_LO: usize = Self::COL_MARKER_WORD_BYTE_END + 3;
    pub const COL_BIT_LENGTH_W15_HI: usize = Self::COL_MARKER_WORD_BYTE_END + 4;
    pub const COL_PADDING_END: usize = Self::COL_PADDING_START + PADDING_ROW_COLS;

    /// Total number of columns in the trace.
    pub const TOTAL_COLS: usize = Self::COL_PADDING_END;

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

    /// Start column of one round's Maj/Ch packed-group block — 24 cells
    /// laid out as 4 operands × 6 groups, in `write_round_maj_ch` order.
    /// `b`/`c`/`f`/`g` are not present here; the AIR aliases them via the
    /// §8.1 reuse chain.
    #[inline]
    pub const fn round_maj_ch_base(t: usize) -> usize {
        let base = Self::COL_ROUND_START + t * ROUND_COLS;
        base + 24 + 2 * SIGMA_DECODE_COLS
    }

    /// Column of one operand's packed-group cell within round `t`.
    ///
    /// `operand_idx ∈ [0, 4)` indexes the operands in the fixed order
    /// `[a, maj_out, e, ch_out]`. `group_idx ∈ [0, 6)` indexes the groups
    /// in the partition's `groups_in_order` enumeration.
    #[inline]
    pub const fn round_packed_group(t: usize, operand_idx: usize, group_idx: usize) -> usize {
        Self::round_maj_ch_base(t) + operand_idx * GROUPS_PER_ROUND_PARTITION + group_idx
    }

    /// Column of one packed-group cell within the per-block auxiliary
    /// split-and-pack region (`h_in[1]`/`h_in[2]`/`h_in[5]`/`h_in[6]`).
    ///
    /// `aux_idx ∈ [0, H_IN_AUX_OPERANDS)` indexes the four auxiliary
    /// operands in the fixed order `[b_init, c_init, f_init, g_init]`.
    /// `group_idx ∈ [0, GROUPS_PER_ROUND_PARTITION)` indexes the groups
    /// in the operand's partition (`SIGMA0_GROUPS` for the `b_init`/
    /// `c_init` slots, `SIGMA1_GROUPS` for `f_init`/`g_init`).
    #[inline]
    pub const fn h_in_aux_grp(aux_idx: usize, group_idx: usize) -> usize {
        Self::COL_H_IN_AUX_GRP_START + aux_idx * GROUPS_PER_ROUND_PARTITION + group_idx
    }

    /// Start column of the σ-input split-and-pack block of one schedule
    /// entry. `which` is `0` for the `σ0(W[t-15])` input and `1` for the
    /// `σ1(W[t-2])` input — the order written by [`write_block_row`].
    ///
    /// The 4 cells starting here are
    /// `(packed_s_lo, packed_s_complement_lo, packed_s_hi, packed_s_complement_hi)`.
    #[inline]
    pub const fn schedule_entry_input_split(j: usize, which: usize) -> usize {
        let base = Self::COL_SCHED_ENTRY_START + j * SCHEDULE_ENTRY_COLS;
        base + 6 + 2 * SIGMA_DECODE_COLS + which * SIGMA_INPUT_SPLIT_COLS
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

    /// Column of the `j`-th one-hot marker-word indicator (`j ∈ [0, 16)`).
    #[inline]
    pub const fn is_marker_word(j: usize) -> usize {
        Self::COL_IS_MARKER_WORD_START + j
    }

    /// Column of the `b`-th marker-byte selector (`b ∈ [0, 4)`, BE order).
    #[inline]
    pub const fn marker_byte_sel(b: usize) -> usize {
        Self::COL_MARKER_BYTE_SEL_START + b
    }

    /// Column of the `b`-th marker-word byte cell (`b ∈ [0, 4)`, BE order
    /// matching FIPS 180-4 §5.2.1's big-endian word parse).
    #[inline]
    pub const fn marker_word_byte(b: usize) -> usize {
        Self::COL_MARKER_WORD_BYTE_START + b
    }

    /// Row slot the `block_idx`-th block is written to, for a trace of size
    /// `2^log_size`.
    ///
    /// Block `r` lives at coset index `r`, which maps to circle-domain index
    /// `coset_index_to_circle_domain_index(r, log_size)`, stored at slot
    /// `bit_reverse_index(·, log_size)` to match Stwo's bit-reversed
    /// circle-domain convention. The result is the index callers should use
    /// to look the block up in the returned `Vec<Vec<BaseField>>`.
    ///
    /// The mapping `r ↔ coset_index` matters for the AIR's cross-row reads:
    /// `next_interaction_mask(_, [0, -1])` walks coset indices, so offset `-1`
    /// at the slot for block `r` returns the slot for block `r − 1` — exactly
    /// the chain link [`crate::constraints::Sha256Eval`] needs for
    /// `h_in[r] == h_out[r-1]`.
    #[inline]
    pub fn block_slot(block_idx: usize, log_size: u32) -> usize {
        bit_reverse_index(
            coset_index_to_circle_domain_index(block_idx, log_size),
            log_size,
        )
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
        let slot = Layout::block_slot(block_idx, log_size);
        write_block_row(&mut cols, slot, block, block_idx == 0);
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

    // Per-block §8.1 reuse chain initial packed groups
    write_h_in_aux_grp(cols, row, &block.aux_split_pack);

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

        write_sigma_input_split_block(
            cols,
            row,
            Layout::schedule_entry_input_split(j, 0),
            &entry.lower_sigma0_input_split,
        );
        write_sigma_input_split_block(
            cols,
            row,
            Layout::schedule_entry_input_split(j, 1),
            &entry.lower_sigma1_input_split,
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
        write_round_maj_ch(cols, row, t, &round.maj_ch);
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

    // padding-role witness — laid out per `PADDING_ROW_COLS` above.
    write_padding_row(cols, row, &block.padding_row);
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
    // Byte chunks of the three O2 values — input to the chunk-wise `xor_8`
    // lookup. The chunk-bind linear constraints pin each `(b0, b1)` pair to
    // its limb.
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

/// Write one round's Maj/Ch packed-group block — 4 operands × 6 cells each,
/// in the fixed operand order `[a, maj_out, e, ch_out]` and the partition's
/// `groups_in_order` enumeration. The §8.1 reuse chain handles `b`/`c`/
/// `f`/`g` via in-row aliasing to prior rounds' `a`/`e` columns (and to
/// the per-block `H_IN_AUX_GRP` region for `t ∈ {0, 1}`). The AIR's read
/// loop walks the columns in exactly this order.
fn write_round_maj_ch(
    cols: &mut [Vec<BaseField>],
    row: usize,
    t: usize,
    maj_ch: &RoundMajChWitness,
) {
    let operands: [&RoundPackedGroups; ROUND_MAJ_CH_OPERANDS] = [
        &maj_ch.a_grp,
        &maj_ch.maj_grp,
        &maj_ch.e_grp,
        &maj_ch.ch_grp,
    ];
    for (operand_idx, operand) in operands.iter().enumerate() {
        for (group_idx, &v) in operand.vals.iter().enumerate() {
            cols[Layout::round_packed_group(t, operand_idx, group_idx)][row] = m31(v);
        }
    }
}

/// Write the per-block auxiliary split-and-pack block — the §8.1 reuse
/// chain's initial values for `b`, `c`, `f`, `g`. Operand order is fixed:
/// `[b_init = h_in[1]_a-side, c_init = h_in[2]_a-side, f_init =
/// h_in[5]_e-side, g_init = h_in[6]_e-side]`, matching
/// [`Layout::h_in_aux_grp`].
fn write_h_in_aux_grp(cols: &mut [Vec<BaseField>], row: usize, aux: &BlockAuxSplitPackWitness) {
    let operands: [&RoundPackedGroups; H_IN_AUX_OPERANDS] =
        [&aux.b_init, &aux.c_init, &aux.f_init, &aux.g_init];
    for (aux_idx, operand) in operands.iter().enumerate() {
        for (group_idx, &v) in operand.vals.iter().enumerate() {
            cols[Layout::h_in_aux_grp(aux_idx, group_idx)][row] = m31(v);
        }
    }
}

/// Write one σ-input split-and-pack block — the 4 packed values
/// `(packed_s_lo, packed_s_complement_lo, packed_s_hi, packed_s_complement_hi)`.
/// The AIR reads them in this order and fires two σ split-and-pack
/// lookups (one per half) keyed on the word's `(lo, hi)` limbs.
fn write_sigma_input_split_block(
    cols: &mut [Vec<BaseField>],
    row: usize,
    base: usize,
    w: &SigmaInputSplitPackWitness,
) {
    cols[base][row] = m31(w.packed_s_lo);
    cols[base + 1][row] = m31(w.packed_s_complement_lo);
    cols[base + 2][row] = m31(w.packed_s_hi);
    cols[base + 3][row] = m31(w.packed_s_complement_hi);
}

/// Write the per-block padding-role witness — `PADDING_ROW_COLS` cells in
/// the column order documented on [`PADDING_ROW_COLS`]. The AIR reads
/// them in the same order, so this writer's cell sequence is the
/// load-bearing layout contract.
fn write_padding_row(cols: &mut [Vec<BaseField>], row: usize, p: &PaddingRowWitness) {
    cols[Layout::COL_IS_MARKER_BLOCK][row] = m31(p.is_marker_block);
    cols[Layout::COL_IS_LENGTH_BLOCK][row] = m31(p.is_length_block);
    cols[Layout::COL_IS_LENGTH_ONLY_BLOCK][row] = m31(p.is_length_only_block);
    cols[Layout::COL_IS_MARKER_ONLY_BLOCK][row] = m31(p.is_marker_only_block);
    for (j, &v) in p.is_marker_word.iter().enumerate() {
        cols[Layout::is_marker_word(j)][row] = m31(v);
    }
    for (b, &v) in p.marker_byte_sel.iter().enumerate() {
        cols[Layout::marker_byte_sel(b)][row] = m31(v);
    }
    for (b, &v) in p.marker_word_byte.iter().enumerate() {
        cols[Layout::marker_word_byte(b)][row] = m31(v);
    }
    cols[Layout::COL_MARKER_WORD_POST_STRICT_15][row] = m31(p.marker_word_post_strict_15);
    cols[Layout::COL_BIT_LENGTH_W14_LO][row] = m31(p.bit_length_w14_lo);
    cols[Layout::COL_BIT_LENGTH_W14_HI][row] = m31(p.bit_length_w14_hi);
    cols[Layout::COL_BIT_LENGTH_W15_LO][row] = m31(p.bit_length_w15_lo);
    cols[Layout::COL_BIT_LENGTH_W15_HI][row] = m31(p.bit_length_w15_hi);
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
        // Each block lives at its coset-indexed bit-reversed slot, so use
        // `Layout::block_slot` rather than the block index directly.
        let last_slot = Layout::block_slot(witness.blocks.len() - 1, log_size);
        let mut digest_bytes = [0u8; 32];
        for j in 0..N_STATE_WORDS {
            let (lo, hi) = Layout::h_out_word(j);
            let lo_val = trace[lo][last_slot].0;
            let hi_val = trace[hi][last_slot].0;
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

        // Real-block slots: every `Layout::block_slot(block_idx, log_size)`
        // for `block_idx ∈ [0, n_real)`, with the first block's slot tagged
        // by `is_first_block = 1`.
        let real_slots: std::collections::HashSet<usize> = (0..n_real)
            .map(|b| Layout::block_slot(b, log_size))
            .collect();
        let first_block_slot = Layout::block_slot(0, log_size);
        assert_eq!(real_slots.len(), n_real, "block slots must be distinct");

        for row in 0..n_rows {
            let expected_enabler = if real_slots.contains(&row) { 1u32 } else { 0 };
            let expected_first = if row == first_block_slot { 1u32 } else { 0 };
            assert_eq!(trace[Layout::COL_ENABLER][row].0, expected_enabler);
            assert_eq!(trace[Layout::COL_IS_FIRST_BLOCK][row].0, expected_first);
        }
    }

    #[test]
    fn h_in_of_first_block_is_iv() {
        use crate::constants::IV;
        let witness = compute_sha256_witness(b"");
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);
        let slot = Layout::block_slot(0, log_size);
        for (j, &iv_j) in IV.iter().enumerate().take(N_STATE_WORDS) {
            let (lo, hi) = Layout::h_in_word(j);
            let lo_val = trace[lo][slot].0;
            let hi_val = trace[hi][slot].0;
            let word = lo_val | (hi_val << 16);
            assert_eq!(word, iv_j, "h_in[{j}] != IV[{j}]");
        }
    }

    #[test]
    fn block_chain_h_out_to_h_in_continuity() {
        // Witness-level chain check — independent of the AIR. Block `b+1`'s
        // `h_in` should equal block `b`'s `h_out` limb-by-limb. The AIR's
        // cross-row copy constraint (3.9.6) enforces the same condition on
        // the polynomial; this test confirms the trace generator agrees.
        let witness = compute_sha256_witness(&[0xAB; 200]);
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);
        for block_idx in 1..witness.blocks.len() {
            let cur = Layout::block_slot(block_idx, log_size);
            let prev = Layout::block_slot(block_idx - 1, log_size);
            for j in 0..N_STATE_WORDS {
                let (h_in_lo, h_in_hi) = Layout::h_in_word(j);
                let (h_out_lo, h_out_hi) = Layout::h_out_word(j);
                assert_eq!(trace[h_in_lo][cur].0, trace[h_out_lo][prev].0);
                assert_eq!(trace[h_in_hi][cur].0, trace[h_out_hi][prev].0);
            }
        }
    }

    #[test]
    fn layout_total_cols_matches_expected_breakdown() {
        // Sanity check the byte budget.
        let expected = 1                       // enabler
            + 1                                // is_first_block
            + 2 * N_STATE_WORDS                // h_in
            + H_IN_AUX_GRP_COLS                // §8.1 reuse-chain initial splits
            + 2 * N_ROUNDS                     // schedule
            + N_SCHEDULE_ENTRIES * SCHEDULE_ENTRY_COLS
            + N_ROUNDS * ROUND_COLS
            + 2 * N_STATE_WORDS                // finalization carries
            + 2 * N_STATE_WORDS                // h_out
            + PADDING_ROW_COLS; // §10.4 padding-role witness
        assert_eq!(Layout::TOTAL_COLS, expected);
        // Breakdown: the schedule entry carries the base limb-add column
        // set, two 24-cell σ-decode blocks, and two 4-cell σ-input
        // split-and-pack blocks (the §8.1 chain's σ-side reuse).
        // The round adds two σ-decode blocks and a Maj/Ch packed-group
        // block whose §8.1 reuse cuts the operand count from 8 to 4.
        let base_sched = 6;
        let base_round = 24;
        assert_eq!(
            SCHEDULE_ENTRY_COLS,
            base_sched + 2 * SIGMA_DECODE_COLS + 2 * SIGMA_INPUT_SPLIT_COLS
        );
        assert_eq!(
            ROUND_COLS,
            base_round + 2 * SIGMA_DECODE_COLS + ROUND_MAJ_CH_COLS
        );
        assert_eq!(ROUND_MAJ_CH_COLS, 4 * 6);
        assert_eq!(H_IN_AUX_GRP_COLS, 4 * 6);
        assert_eq!(SIGMA_INPUT_SPLIT_COLS, 4);
        // 4 flags + 16 word-selector + 4 byte-selector + 4 byte cells
        // + 1 post-strict aux + 4 bit-length limbs = 33 padding cells.
        assert_eq!(PADDING_ROW_COLS, 4 + WORDS_PER_BLOCK + 4 + 4 + 1 + 4);
        assert_eq!(PADDING_ROW_COLS, 33);
        assert_eq!(
            expected,
            1 + 1
                + 16
                + H_IN_AUX_GRP_COLS
                + 128
                + 48 * (base_sched + 2 * SIGMA_DECODE_COLS + 2 * SIGMA_INPUT_SPLIT_COLS)
                + 64 * (base_round + 2 * SIGMA_DECODE_COLS + ROUND_MAJ_CH_COLS)
                + 16
                + 16
                + PADDING_ROW_COLS
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
    fn round_maj_ch_block_round_trips_through_trace() {
        // For a real block, every Maj/Ch packed-group cell read from the
        // trace at the layout's `(t, operand_idx, group_idx)` coordinate
        // must equal the corresponding `RoundMajChWitness` value. This
        // pins the operand & group enumeration order — the AIR's read
        // loop relies on it.
        let witness = crate::witness::compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);
        let block = &witness.blocks[0];
        let slot = Layout::block_slot(0, log_size);

        for (t, round) in block.rounds.iter().enumerate() {
            // §8.1 reuse: only the four fresh operands are committed.
            let operand_values: [[u32; 6]; 4] = [
                round.maj_ch.a_grp.vals,
                round.maj_ch.maj_grp.vals,
                round.maj_ch.e_grp.vals,
                round.maj_ch.ch_grp.vals,
            ];
            for (operand_idx, expected) in operand_values.iter().enumerate() {
                for (group_idx, &v) in expected.iter().enumerate() {
                    let col = Layout::round_packed_group(t, operand_idx, group_idx);
                    assert_eq!(
                        trace[col][slot].0, v,
                        "round[{t}] operand[{operand_idx}] group[{group_idx}]",
                    );
                }
            }
        }
    }

    /// Per-block aux split-and-pack region round-trips: each
    /// `[b_init, c_init, f_init, g_init]` operand's packed-group vector
    /// equals what `Layout::h_in_aux_grp` reads back from the trace.
    /// Regression here means the §8.1 reuse chain would alias to wrong
    /// initial values for rounds `t ∈ {0, 1, 2}`.
    #[test]
    fn h_in_aux_grp_round_trips_through_trace() {
        let witness = crate::witness::compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);
        let block = &witness.blocks[0];
        let slot = Layout::block_slot(0, log_size);

        let operands: [[u32; 6]; H_IN_AUX_OPERANDS] = [
            block.aux_split_pack.b_init.vals,
            block.aux_split_pack.c_init.vals,
            block.aux_split_pack.f_init.vals,
            block.aux_split_pack.g_init.vals,
        ];
        for (aux_idx, expected) in operands.iter().enumerate() {
            for (group_idx, &v) in expected.iter().enumerate() {
                let col = Layout::h_in_aux_grp(aux_idx, group_idx);
                assert_eq!(
                    trace[col][slot].0, v,
                    "aux operand[{aux_idx}] group[{group_idx}]"
                );
            }
        }
    }

    /// Per-schedule-entry σ-input split-and-pack block round-trips for one
    /// entry on each σ side. The lookup-tuple alignment depends on this
    /// per-cell ordering, so a regression would silently shift the AIR's
    /// reads against the witness layout.
    #[test]
    fn schedule_input_split_blocks_round_trip_through_trace() {
        let witness = crate::witness::compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);
        let block = &witness.blocks[0];
        let slot = Layout::block_slot(0, log_size);

        // First schedule entry (`j = 0`, i.e. derivation of `W[16]`).
        let entry = &block.schedule_entries[0];
        let base_lower_sigma0 = Layout::schedule_entry_input_split(0, 0);
        let w0 = &entry.lower_sigma0_input_split;
        assert_eq!(trace[base_lower_sigma0][slot].0, w0.packed_s_lo);
        assert_eq!(
            trace[base_lower_sigma0 + 1][slot].0,
            w0.packed_s_complement_lo
        );
        assert_eq!(trace[base_lower_sigma0 + 2][slot].0, w0.packed_s_hi);
        assert_eq!(
            trace[base_lower_sigma0 + 3][slot].0,
            w0.packed_s_complement_hi
        );

        let base_lower_sigma1 = Layout::schedule_entry_input_split(0, 1);
        let w1 = &entry.lower_sigma1_input_split;
        assert_eq!(trace[base_lower_sigma1][slot].0, w1.packed_s_lo);
        assert_eq!(
            trace[base_lower_sigma1 + 1][slot].0,
            w1.packed_s_complement_lo
        );
        assert_eq!(trace[base_lower_sigma1 + 2][slot].0, w1.packed_s_hi);
        assert_eq!(
            trace[base_lower_sigma1 + 3][slot].0,
            w1.packed_s_complement_hi
        );
    }

    #[test]
    fn sigma_decode_block_round_trips_through_trace() {
        // For one block, every σ-decode-block cell read from the trace must
        // match the corresponding `SigmaDecodeWitness` field. This pins
        // `write_sigma_decode_block`'s order against the on-disk layout the
        // AIR reads.
        let witness = compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);
        let block = &witness.blocks[0];
        let slot = Layout::block_slot(0, log_size);

        // Schedule σ0 decode of entry j=0 (corresponds to W[16] = σ1(W[14]) + … + σ0(W[1]) + W[0]).
        let entry = &block.schedule_entries[0];
        let base = Layout::schedule_entry_decode(0, 0);
        let d = &entry.lower_sigma0_decode;
        assert_eq!(trace[base][slot].0, d.key_s);
        assert_eq!(trace[base + 1][slot].0, d.o_main_s.lo);
        assert_eq!(trace[base + 4][slot].0, d.o2_partial_s.hi);
        assert_eq!(trace[base + 5][slot].0, d.key_s_complement);
        assert_eq!(trace[base + 10][slot].0, d.o2_combined.lo);
        assert_eq!(trace[base + 12][slot].0, d.o2_chunks_s.lo.b0);
        assert_eq!(trace[base + 15][slot].0, d.o2_chunks_s.hi.b1);
        assert_eq!(trace[base + 23][slot].0, d.o2_chunks_combined.hi.b1);

        // Round Σ0 decode of round 0 (operating on a = IV[0]).
        let round = &block.rounds[0];
        let base = Layout::round_decode(0, 0);
        let d = &round.sigma0_decode;
        assert_eq!(trace[base][slot].0, d.key_s);
        assert_eq!(trace[base + 5][slot].0, d.key_s_complement);
        assert_eq!(trace[base + 11][slot].0, d.o2_combined.hi);
    }
}
