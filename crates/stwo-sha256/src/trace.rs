//! Trace generation — converts a [`Sha256Witness`] into M31 column data the
//! Stwo prover can commit to.
//!
//! Layout: **one row per round**, narrow. Natural row index `b · 64 + t` for
//! block `b`, round `t ∈ [0, 64)`. With `n` blocks the trace has
//! `next_power_of_two(64 · n)` *slots* per column (at least one padding row —
//! see [`min_log_size`]). Row `r` is written at the slot returned by
//! [`row_slot(r, log_size)`] — i.e., in **bit-reversed circle-domain order
//! with coset index = natural row index**, matching Stwo's standard SIMD/CPU
//! trace convention. Iterating coset indices walks the rounds in order, which
//! makes cross-row mask reads at offset `-k` resolve to "`k` rounds earlier"
//! — the basis of the working-state chain (`b = a@−1`, …), the schedule
//! recurrence reads (`W@−2, −7, −15, −16`), and the block-chain constraint
//! (`h_in[t=0] == h_out@−1`, the previous block's `t = 63` row) in
//! [`crate::constraints`]. Slots past the last real row remain zeroed and are
//! padding.
//!
//! A row of the trace carries (in this order):
//!
//! - `enabler` (1 col) — `1` on real rows, `0` on padding rows. Multiplies
//!   every constraint so padding rows are constraint-free.
//! - `W` (2 cols, `(lo, hi)`) — the row's schedule word `W[t]`: a message
//!   word for `t < 16`, the recurrence output for `t ≥ 16`.
//! - the **round family** (`ROUND_COLS = 136` cols, live on every real row):
//!   `σ0, σ1, ch, maj, t1, t2, a_new, e_new` (each `(lo, hi)` ⇒ 16 cells),
//!   4 add carry pairs (⇒ 8 cells), the decoded intermediates of `Σ0(a)` and
//!   `Σ1(e)` (2 × [`SIGMA_DECODE_COLS`]), then the Maj/Ch packed-group block
//!   ([`ROUND_MAJ_CH_COLS`] — 8 operands `[a, maj, e, ch, b, c, f, g]`,
//!   the last four being the §8.1 reuse duplicates).
//! - the **schedule family** (`SCHEDULE_ENTRY_COLS = 62` cols, live only on
//!   rows with `t ≥ 16`, zero elsewhere): the `σ0`/`σ1` output limbs and add
//!   carries (6), the decoded intermediates of `σ0(W[t−15])` and
//!   `σ1(W[t−2])` (2 × [`SIGMA_DECODE_COLS`]), and the σ-input
//!   split-and-pack outputs (2 × [`SIGMA_INPUT_SPLIT_COLS`]). Recurrence
//!   inputs are *not* duplicated — they are the `W` columns of earlier rows,
//!   read via mask offsets `−2, −7, −15, −16`.
//! - **block-boundary families**, each live on one designated round row of
//!   its block and zero elsewhere:
//!   - `t = 0`: `is_first_block` (1), `h_in` (16), `H_IN_AUX_GRP` (32 — the
//!     §8.1 reuse chain's initial `b`/`c`/`f`/`g` splits).
//!   - `t = 63`: finalization carries (16), `h_out` (16), `is_last_block`
//!     (1), digest byte view (32).
//!   - `t = 15`: the §10.4 padding-role block ([`PADDING_ROW_COLS`] = 33);
//!     the message words it inspects are the `W` columns of rows
//!     `t = 0..16`, read via mask offsets `0..−15`.
//! - `enabler_step` (1 col) — C1 contiguity anchor: `1` exactly at the first
//!   real row (block 0, round 0) when the trace has padding.
//! - the optional credential-field byte tail (dynamic, live on `t = 15`
//!   rows; yields are gated to the configured target block in the AIR).
//!
//! Per-round Maj/Ch block (`ROUND_MAJ_CH_COLS = 4 · 8 = 32`): packed-group
//! values of each *fresh* operand in the partition-enumeration order
//! (`groups_in_order` — `S[0..4]` then `S'[0..4]`). Operand order is
//! `a, maj_out` (a-side / `SIGMA0_GROUPS`) followed by `e, ch_out`
//! (e-side / `SIGMA1_GROUPS`). `b`, `c`, `f`, `g` are not committed — the
//! §8.1 reuse chain aliases them to the `a`/`e` group columns of rows
//! `t−1`/`t−2` via mask offsets (and to the `t = 0` row's `H_IN_AUX_GRP`
//! columns for `t ∈ {0, 1}`). Each cell is one packed group value in
//! `[0, 2^|group|) ⊆ [0, 2^MAX_ROUND_GROUP_BITS)`.
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
//!
//! Per-schedule-entry σ-input split block (`SIGMA_INPUT_SPLIT_COLS = 4`):
//! `(packed_s_lo, packed_s_complement_lo, packed_s_hi, packed_s_complement_hi)`
//! — the four split-and-pack outputs the σ partition emits per input word.
//! The AIR fires one σ-input split-and-pack lookup per half against the
//! corresponding partition's table, then linearly assembles the σ-decode
//! `key_s` / `key_s_complement` from these four values.

use stwo::core::fields::m31::{BaseField, M31};
use stwo::core::utils::{
    bit_reverse_index, circle_domain_index_to_coset_index, coset_index_to_circle_domain_index,
};
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES, N_LANES};

use crate::constants::{DIGEST_BYTES, N_ROUNDS, N_STATE_WORDS};
use crate::field_exposure::FieldExposure;
use crate::native::{lower_sigma0, lower_sigma1};
use crate::partitions::GROUPS_PER_ROUND_PARTITION;
use crate::types::{
    AddCarries, BlockAuxSplitPackWitness, PaddingRowWitness, RoundPackedGroups, Sha256Witness,
    SigmaInputSplitPackWitness, WordLimbs,
};

use crate::constants::WORD_BYTES as BYTES_PER_WORD;

/// Words per 512-bit block: 16.
pub const WORDS_PER_BLOCK: usize = 16;

/// Rows one block occupies in the rotated layout: one per round.
pub const ROWS_PER_BLOCK: usize = N_ROUNDS;

/// Bits per SHA-256 word, committed LSB-first.
pub const WORD_BIT_COLS: usize = 32;
/// Round operand bit columns. The hybrid AIR keeps operand aliases as
/// committed bits so Maj/Ch formulas stay degree 3 even on boundary rows.
/// Operand order: `[a, b, c, e, f, g]`.
pub const ROUND_BIT_OPERANDS: usize = 6;
pub const ROUND_OPERAND_BIT_COLS: usize = ROUND_BIT_OPERANDS * WORD_BIT_COLS;
/// Packed output groups retained for round split-pack lookups. The bits of
/// `Maj` and `Ch` are virtual expressions; these committed packed groups keep
/// the surviving split-pack lookup keys degree 1.
pub const ROUND_OUTPUT_GROUP_OPERANDS: usize = 2;
pub const ROUND_OUTPUT_GROUP_COLS: usize = ROUND_OUTPUT_GROUP_OPERANDS * GROUPS_PER_ROUND_PARTITION;
/// Schedule lower-sigma output bits. The formulas are ungated; only their
/// linear recomposition into `s0`/`s1` is gated on active schedule rows.
pub const SCHEDULE_SIGMA_OUTPUT_BIT_COLS: usize = 2 * WORD_BIT_COLS;
/// Columns per σ-input split-and-pack block: four packed values
/// `(packed_s_lo, packed_s_complement_lo, packed_s_hi, packed_s_complement_hi)`.
/// The AIR fires one σ split-and-pack lookup per half against the
/// partition's table (rows `(key=word.lo|hi, packed_s, packed_s')`).
pub const SIGMA_INPUT_SPLIT_COLS: usize = 4;
/// Columns of the round family: 8 word-results × 2 limbs + 4 carry pairs
/// × 2 ends = 24, then committed operand bits and packed Maj/Ch output
/// groups for the surviving split-pack lookups.
pub const ROUND_COLS: usize = 8 * 2 + 4 * 2 + ROUND_OPERAND_BIT_COLS + ROUND_OUTPUT_GROUP_COLS;
/// Columns of the schedule family (live for `t ≥ 16`):
/// `σ0`, `σ1`, carries (= 6), lower-sigma output bits, then two σ-input
/// split-and-pack blocks.
pub const SCHEDULE_ENTRY_COLS: usize =
    6 + SCHEDULE_SIGMA_OUTPUT_BIT_COLS + 2 * SIGMA_INPUT_SPLIT_COLS;
/// Per-block auxiliary split-and-pack operands for the §8.1 reuse chain:
/// `[b_init = h_in[1]_a-side, c_init = h_in[2]_a-side, f_init = h_in[5]_e-side,
///   g_init = h_in[6]_e-side]`. `h_in[0]`/`h_in[4]` are covered by
/// `a_grp[round 0]`/`e_grp[round 0]` (`a[0]=h_in[0]`, `e[0]=h_in[4]`);
/// `h_in[3]`/`h_in[7]` never enter Σ/Maj/Ch directly.
pub const H_IN_AUX_OPERANDS: usize = 4;
/// Columns dedicated to the per-block auxiliary split-and-pack of the
/// §8.1 reuse chain's initial values. `4 operands · 8 groups = 32` cells
/// per block, live on the `t = 0` row.
pub const H_IN_AUX_GRP_COLS: usize = H_IN_AUX_OPERANDS * GROUPS_PER_ROUND_PARTITION;
/// Number of schedule entries: `W[16..64]` ⇒ 48.
pub const N_SCHEDULE_ENTRIES: usize = N_ROUNDS - 16;

/// Columns dedicated to the per-block padding-role witness (§10.4 of the
/// validated design), live on each block's `t = 15` row. Laid out in the
/// order [`write_padding_row`] writes them:
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
///     + 1 post-strict aux + 4 bit-length limbs = 33` cells per block.
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
    /// The row's schedule word `W[t]`, `(lo, hi)`.
    pub const COL_W_LO: usize = 1;
    pub const COL_W_HI: usize = 2;
    /// LSB-first bit decomposition of the row's schedule word `W[t]`.
    pub const COL_W_BITS_START: usize = Self::COL_W_HI + 1;
    pub const COL_W_BITS_END: usize = Self::COL_W_BITS_START + WORD_BIT_COLS;
    /// Round family — live on every real row.
    pub const COL_ROUND_START: usize = Self::COL_W_BITS_END;
    pub const COL_ROUND_END: usize = Self::COL_ROUND_START + ROUND_COLS;
    /// Schedule family — live on rows with `t ≥ 16`.
    pub const COL_SCHED_ENTRY_START: usize = Self::COL_ROUND_END;
    pub const COL_SCHED_ENTRY_END: usize = Self::COL_SCHED_ENTRY_START + SCHEDULE_ENTRY_COLS;
    /// `t = 0` family.
    pub const COL_IS_FIRST_BLOCK: usize = Self::COL_SCHED_ENTRY_END;
    pub const COL_H_IN_START: usize = Self::COL_IS_FIRST_BLOCK + 1;
    pub const COL_H_IN_END: usize = Self::COL_H_IN_START + 2 * N_STATE_WORDS;
    pub const COL_H_IN_AUX_GRP_START: usize = Self::COL_H_IN_END;
    pub const COL_H_IN_AUX_GRP_END: usize = Self::COL_H_IN_AUX_GRP_START + H_IN_AUX_GRP_COLS;
    /// `t = 63` family.
    pub const COL_FINAL_CARRIES_START: usize = Self::COL_H_IN_AUX_GRP_END;
    pub const COL_FINAL_CARRIES_END: usize = Self::COL_FINAL_CARRIES_START + 2 * N_STATE_WORDS;
    pub const COL_H_OUT_START: usize = Self::COL_FINAL_CARRIES_END;
    pub const COL_H_OUT_END: usize = Self::COL_H_OUT_START + 2 * N_STATE_WORDS;

    /// `is_last_block` flag (1 col): `1` on the `t = 63` row of the final
    /// real block of a multi-block hash, `0` everywhere else. The AIR pins
    /// it to `enabler · is_round_63 · (1 − enabler_next)` — with the
    /// guaranteed padding row after the last real row ([`min_log_size`]),
    /// this flags exactly the last real row. It gates the cross-component
    /// digest yield to the final block, since the intermediate blocks'
    /// `h_out` are multi-block chaining state, not the credential digest.
    pub const COL_IS_LAST_BLOCK: usize = Self::COL_H_OUT_END;

    /// Digest byte view (`DIGEST_BYTES = 32` cols): the 32 big-endian bytes
    /// of this block's `h_out`, laid out per state word `j` as
    /// `[hi.b1, hi.b0, lo.b1, lo.b0]` (i.e. `word_j.to_be_bytes()`, see
    /// [`h_out_digest_bytes`]). Each `(lo, hi)` limb is tied to its two
    /// bytes by the decomposition constraint `limb = 256·b1 + b0` in
    /// `crate::constraints::Sha256Eval`; these cells are exactly what the
    /// `Sha256Digest` relation yields on the final block. Materialised on
    /// every block's `t = 63` row (the decomposition fires under
    /// `enabler · is_round_63`); only the final block's bytes are yielded
    /// across the module boundary.
    pub const COL_DIGEST_BYTES_START: usize = Self::COL_IS_LAST_BLOCK + 1;
    pub const COL_DIGEST_BYTES_END: usize = Self::COL_DIGEST_BYTES_START + DIGEST_BYTES;

    /// Per-block padding-role region, live on the `t = 15` row.
    pub const COL_PADDING_START: usize = Self::COL_DIGEST_BYTES_END;
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

    /// C1-fix aux column: `enabler_step[r] = enabler[r] · (1 − enabler_prev[r])`.
    /// This is `1` at the *first* real row in coset order (after a padding
    /// predecessor) and `0` everywhere else. The constraint
    /// `(1 − is_first_row) · enabler_step = 0` (emitted in
    /// `crate::constraints::Sha256Eval`) then forces this "first real row"
    /// to be exactly row 0 (block 0, round 0) — eliminating the block-skip /
    /// state-injection variant of the C1 exploit. Using an aux column
    /// keeps the constraint family degree ≤ 2.
    pub const COL_ENABLER_STEP: usize = Self::COL_PADDING_END;

    /// Number of **base** trace columns — the full width when no credential
    /// field is exposed. The optional field-byte view is a dynamic tail
    /// appended after this (see [`Self::COL_FIELD_BYTES_START`]).
    pub const TOTAL_COLS: usize = Self::COL_ENABLER_STEP + 1;

    /// First column of the optional credential-field byte view.
    ///
    /// The field columns are a **dynamic tail** appended after every base
    /// column (including `enabler_step`), so enabling field exposure never
    /// shifts a base offset. The first `WORD_BYTES ×` (distinct exposed message
    /// words) columns are byte columns; multi-block exposure then appends a
    /// block counter and one selector per yielded byte (block-0 legacy exposure
    /// has neither) — see
    /// [`crate::field_exposure::FieldExposure::n_columns`]. Each `(lo, hi)` limb
    /// of an exposed word is tied to its two bytes by `limb = 256·b1 + b0` in
    /// `crate::constraints::Sha256Eval` on the `t = 15` row (which reads the
    /// exposed words' limbs via `W` mask offsets, the same offsets the
    /// padding family uses); only the exposed window bytes are yielded across
    /// the module boundary, gated to each byte's target block.
    pub const COL_FIELD_BYTES_START: usize = Self::TOTAL_COLS;

    /// Column of field tail `slot` (`0`-based within the dynamic field tail:
    /// byte columns packed by decomposed-word then big-endian byte position —
    /// see [`crate::field_exposure::FieldExposure::yield_column_slot`] — then,
    /// for multi-block exposure, the block counter and per-yield selectors).
    #[inline]
    pub const fn field_byte_col(slot: usize) -> usize {
        Self::COL_FIELD_BYTES_START + slot
    }

    /// Total trace width when a field exposure adds `n_field_cols` dynamic
    /// columns (`0` ⇒ [`Self::TOTAL_COLS`]).
    #[inline]
    pub const fn total_cols_with_fields(n_field_cols: usize) -> usize {
        Self::TOTAL_COLS + n_field_cols
    }

    /// `(lo, hi)` slot for the `j`-th word of `h_in` (`t = 0` row).
    #[inline]
    pub const fn h_in_word(j: usize) -> (usize, usize) {
        let base = Self::COL_H_IN_START + 2 * j;
        (base, base + 1)
    }

    /// `(lo, hi)` slot for the row's schedule word `W[t]`.
    #[inline]
    pub const fn schedule_word() -> (usize, usize) {
        (Self::COL_W_LO, Self::COL_W_HI)
    }

    /// Columns of the schedule family's leading cells, in order:
    /// `σ0_lo, σ0_hi, σ1_lo, σ1_hi, carry_lo, carry_hi`. Live on rows with
    /// `t ≥ 16`.
    #[inline]
    pub const fn schedule_entry() -> [usize; 6] {
        let base = Self::COL_SCHED_ENTRY_START;
        [base, base + 1, base + 2, base + 3, base + 4, base + 5]
    }

    /// Column of one bit in the row's schedule word.
    #[inline]
    pub const fn w_bit(bit: usize) -> usize {
        Self::COL_W_BITS_START + bit
    }

    /// Column of a round operand bit. Operand order is `[a, b, c, e, f, g]`.
    #[inline]
    pub const fn round_operand_bit(operand_idx: usize, bit: usize) -> usize {
        Self::COL_ROUND_START + 24 + operand_idx * WORD_BIT_COLS + bit
    }

    /// Start column of the round family's packed output groups: `Maj`, `Ch`.
    #[inline]
    pub const fn round_output_group_base() -> usize {
        Self::COL_ROUND_START + 24 + ROUND_OPERAND_BIT_COLS
    }

    /// Column of one packed output group. Output order is `[Maj, Ch]`.
    #[inline]
    pub const fn round_output_group(output_idx: usize, group_idx: usize) -> usize {
        Self::round_output_group_base() + output_idx * GROUPS_PER_ROUND_PARTITION + group_idx
    }

    /// Column of a lower-sigma output bit in the schedule family. `which` is
    /// `0` for `σ0(W[t-15])`, `1` for `σ1(W[t-2])`.
    #[inline]
    pub const fn schedule_sigma_bit(which: usize, bit: usize) -> usize {
        Self::COL_SCHED_ENTRY_START + 6 + which * WORD_BIT_COLS + bit
    }

    /// Column of one packed-group cell within the per-block auxiliary
    /// split-and-pack region (`h_in[1]`/`h_in[2]`/`h_in[5]`/`h_in[6]`,
    /// `t = 0` row).
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

    /// Start column of the σ-input split-and-pack block of the schedule
    /// family. `which` is `0` for the `σ0(W[t-15])` input and `1` for the
    /// `σ1(W[t-2])` input — the order written by [`write_round_row`].
    ///
    /// The 4 cells starting here are
    /// `(packed_s_lo, packed_s_complement_lo, packed_s_hi, packed_s_complement_hi)`.
    #[inline]
    pub const fn schedule_entry_input_split(which: usize) -> usize {
        Self::COL_SCHED_ENTRY_START
            + 6
            + SCHEDULE_SIGMA_OUTPUT_BIT_COLS
            + which * SIGMA_INPUT_SPLIT_COLS
    }

    /// The round family's leading columns, in order:
    /// `σ0_lo, σ0_hi, σ1_lo, σ1_hi, ch_lo, ch_hi, maj_lo, maj_hi,
    ///  t1_lo, t1_hi, t2_lo, t2_hi, a_new_lo, a_new_hi, e_new_lo, e_new_hi,
    ///  t1_carry_lo, t1_carry_hi, t2_carry_lo, t2_carry_hi,
    ///  e_new_carry_lo, e_new_carry_hi, a_new_carry_lo, a_new_carry_hi`.
    #[inline]
    pub const fn round_col() -> [usize; 24] {
        let base = Self::COL_ROUND_START;
        let mut out = [0; 24];
        let mut i = 0;
        while i < 24 {
            out[i] = base + i;
            i += 1;
        }
        out
    }

    /// `(lo, hi)` slot for the `j`-th word of `h_out` (`t = 63` row).
    #[inline]
    pub const fn h_out_word(j: usize) -> (usize, usize) {
        let base = Self::COL_H_OUT_START + 2 * j;
        (base, base + 1)
    }

    /// Column of digest byte `idx` (`idx ∈ [0, DIGEST_BYTES)`), in the
    /// big-endian `to_be_bytes` order of [`h_out_digest_bytes`].
    #[inline]
    pub const fn digest_byte(idx: usize) -> usize {
        Self::COL_DIGEST_BYTES_START + idx
    }

    /// `(lo_carry, hi_carry)` slot for the `j`-th finalization add
    /// (`t = 63` row).
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

    /// Storage slot of natural row `row_idx` (`= block · 64 + round`), for a
    /// trace of size `2^log_size`.
    ///
    /// Row `r` lives at coset index `r`, which maps to circle-domain index
    /// `coset_index_to_circle_domain_index(r, log_size)`, stored at slot
    /// `bit_reverse_index(·, log_size)` to match Stwo's bit-reversed
    /// circle-domain convention. The result is the index callers should use
    /// to look the row up in the returned `Vec<Vec<BaseField>>`.
    ///
    /// The mapping `r ↔ coset_index` matters for the AIR's cross-row reads:
    /// `next_interaction_mask(_, [0, -k])` walks coset indices, so offset
    /// `-k` at the slot for row `r` returns the slot for row `r − k` —
    /// exactly the working-state / schedule / block-chain links
    /// [`crate::constraints::Sha256Eval`] needs.
    #[inline]
    pub fn row_slot(row_idx: usize, log_size: u32) -> usize {
        bit_reverse_index(
            coset_index_to_circle_domain_index(row_idx, log_size),
            log_size,
        )
    }

    /// Storage slot of `(block_idx, round_t)`.
    #[inline]
    pub fn round_row_slot(block_idx: usize, round_t: usize, log_size: u32) -> usize {
        Self::row_slot(block_idx * ROWS_PER_BLOCK + round_t, log_size)
    }
}

/// The 32 digest bytes of a block's `h_out`, in the fixed big-endian order
/// the [`Layout::COL_DIGEST_BYTES_START`] columns and the
/// `crate::relations::Sha256Digest` relation use: per state word `j`,
/// `word_j.to_be_bytes()` = `[hi.b1, hi.b0, lo.b1, lo.b0]` (recall
/// `word_j = lo + 2¹⁶·hi`, so the high limb supplies the two most-significant
/// big-endian bytes). The trace generator fills the byte columns from this,
/// `crate::interaction` combines the digest LogUp tuple from this, and
/// `crate::constraints` reads the columns back in this order — keeping the
/// digest provider and any consumer byte-for-byte aligned (interface-contract
/// item 4). The two bytes of each limb satisfy `limb = 256·b1 + b0`, which is
/// the decomposition the AIR constrains.
pub fn h_out_digest_bytes(h_out: &[WordLimbs; N_STATE_WORDS]) -> [u32; DIGEST_BYTES] {
    let mut out = [0u32; DIGEST_BYTES];
    for (j, limb) in h_out.iter().enumerate() {
        let bytes = crate::field_exposure::word_be_bytes(limb.lo, limb.hi);
        out[4 * j..4 * j + 4].copy_from_slice(&bytes);
    }
    out
}

/// Materialise the trace for a `Sha256Witness`, with no credential field
/// exposed (the base width [`Layout::TOTAL_COLS`]). See
/// [`generate_trace_with_fields`] for the field-exposing variant.
///
/// Returns `Vec<Vec<BaseField>>`, one inner `Vec` per column. Length of
/// every inner `Vec` equals `1 << log_size`, padded with zeros past the
/// number of real rows.
///
/// Choose `log_size` so that `(1 << log_size) >= 64 · witness.blocks.len()`
/// (use [`min_log_size`]). The function panics otherwise.
pub fn generate_trace(witness: &Sha256Witness, log_size: u32) -> Vec<Vec<BaseField>> {
    generate_trace_with_fields(witness, log_size, &FieldExposure::empty())
}

/// Materialise the trace for a `Sha256Witness`, additionally committing the
/// credential-field byte view on every block's `t = 15` row when
/// `field_exposure` is non-empty.
///
/// The field byte columns are appended after every base column; an empty
/// exposure adds nothing and the result is identical to [`generate_trace`].
pub fn generate_trace_with_fields(
    witness: &Sha256Witness,
    log_size: u32,
    field_exposure: &FieldExposure,
) -> Vec<Vec<BaseField>> {
    generate_trace_with_fields_packed(witness, log_size, field_exposure)
}

#[cfg(test)]
fn generate_trace_with_fields_scalar(
    witness: &Sha256Witness,
    log_size: u32,
    field_exposure: &FieldExposure,
) -> Vec<Vec<BaseField>> {
    let n_rows = 1usize << log_size;
    let n_real_rows = witness.blocks.len() * ROWS_PER_BLOCK;
    assert!(
        n_real_rows <= n_rows,
        "trace too small: {} blocks × {ROWS_PER_BLOCK} rounds > {} rows",
        witness.blocks.len(),
        n_rows
    );

    let total_cols = Layout::total_cols_with_fields(field_exposure.n_columns());
    let mut cols = vec![vec![BaseField::from(0u32); n_rows]; total_cols];

    // `is_last_block` mirrors the AIR's `enabler · is_round_63 ·
    // (1 − enabler_next)` gate: it is `1` at the final real row *only if*
    // that row has a padding successor. [`min_log_size`] guarantees one, but
    // a caller-supplied exactly-full trace keeps the flag `0` everywhere and
    // the digest is simply not exposed — the trace value stays in lock-step
    // with the constraint either way.
    let last_block_idx = witness.blocks.len().saturating_sub(1);
    let has_padding = n_real_rows < n_rows;
    for block_idx in 0..witness.blocks.len() {
        for t in 0..N_ROUNDS {
            let slot = Layout::round_row_slot(block_idx, t, log_size);
            write_round_row(
                &mut cols,
                slot,
                witness,
                block_idx,
                t,
                n_rows,
                block_idx == 0,
                block_idx == last_block_idx && has_padding,
                field_exposure,
            );
        }
    }

    // C1-fix aux column: `enabler_step` is `1` only at the slot whose
    // cyclic predecessor (coset offset −1) is a padding row. With row 0
    // at coset 0, that predecessor wraps to coset `N − 1`. If the trace has
    // padding, coset `N − 1` is padding (`enabler = 0`) and
    // `enabler_step[0] = 1`. Every other storage index is `0` either because
    // the row is padding (`enabler = 0`) or because its coset predecessor is
    // also real (`enabler_prev = 1`).
    if has_padding {
        let first_slot = Layout::row_slot(0, log_size);
        cols[Layout::COL_ENABLER_STEP][first_slot] = BaseField::from(1u32);
    }
    fill_schedule_sigma_bits_columns(&mut cols, log_size);

    cols
}

fn generate_trace_with_fields_packed(
    witness: &Sha256Witness,
    log_size: u32,
    field_exposure: &FieldExposure,
) -> Vec<Vec<BaseField>> {
    generate_trace_base_columns_with_fields(witness, log_size, field_exposure)
        .into_iter()
        .map(BaseColumn::into_cpu_vec)
        .collect()
}

pub(crate) fn generate_trace_base_columns_with_fields(
    witness: &Sha256Witness,
    log_size: u32,
    field_exposure: &FieldExposure,
) -> Vec<BaseColumn> {
    if log_size < LOG_N_LANES || rayon::current_num_threads() == 1 {
        return generate_trace_with_fields_scalar_fallback(witness, log_size, field_exposure)
            .into_iter()
            .map(|values| values.into_iter().collect())
            .collect();
    }

    use rayon::prelude::*;

    let n_rows = 1usize << log_size;
    let n_real_rows = witness.blocks.len() * ROWS_PER_BLOCK;
    assert!(
        n_real_rows <= n_rows,
        "trace too small: {} blocks × {ROWS_PER_BLOCK} rounds > {} rows",
        witness.blocks.len(),
        n_rows
    );

    let total_cols = Layout::total_cols_with_fields(field_exposure.n_columns());
    let last_block_idx = witness.blocks.len().saturating_sub(1);
    let has_padding = n_real_rows < n_rows;
    let mut row_values = (0..n_rows)
        .into_par_iter()
        .map(|row_idx| {
            if row_idx >= n_real_rows {
                return vec![BaseField::from(0u32); total_cols];
            }
            let block_idx = row_idx / ROWS_PER_BLOCK;
            let t = row_idx % ROWS_PER_BLOCK;
            let mut values = vec![BaseField::from(0u32); total_cols];
            write_round_row_values(
                &mut values,
                witness,
                block_idx,
                t,
                n_rows,
                block_idx == 0,
                block_idx == last_block_idx && has_padding,
                field_exposure,
            );
            values
        })
        .collect::<Vec<_>>();
    fill_schedule_sigma_bits_rows(&mut row_values);

    let packed_rows = 1usize << (log_size - LOG_N_LANES);
    (0..total_cols)
        .into_par_iter()
        .map(|column| {
            let data = (0..packed_rows)
                .map(|packed_row| {
                    PackedM31::from_array(core::array::from_fn(|lane| {
                        let storage_index = packed_row * N_LANES + lane;
                        let circle_index = bit_reverse_index(storage_index, log_size);
                        let coset_index =
                            circle_domain_index_to_coset_index(circle_index, log_size);
                        if column == Layout::COL_ENABLER_STEP && has_padding && coset_index == 0 {
                            return BaseField::from(1u32);
                        }
                        row_values[coset_index][column]
                    }))
                })
                .collect();
            BaseColumn::from_simd(data)
        })
        .collect()
}

fn generate_trace_with_fields_scalar_fallback(
    witness: &Sha256Witness,
    log_size: u32,
    field_exposure: &FieldExposure,
) -> Vec<Vec<BaseField>> {
    let n_rows = 1usize << log_size;
    let n_real_rows = witness.blocks.len() * ROWS_PER_BLOCK;
    assert!(
        n_real_rows <= n_rows,
        "trace too small: {} blocks × {ROWS_PER_BLOCK} rounds > {} rows",
        witness.blocks.len(),
        n_rows
    );

    let total_cols = Layout::total_cols_with_fields(field_exposure.n_columns());
    let mut cols = vec![vec![BaseField::from(0u32); n_rows]; total_cols];
    let last_block_idx = witness.blocks.len().saturating_sub(1);
    let has_padding = n_real_rows < n_rows;
    for block_idx in 0..witness.blocks.len() {
        for t in 0..N_ROUNDS {
            let slot = Layout::round_row_slot(block_idx, t, log_size);
            write_round_row(
                &mut cols,
                slot,
                witness,
                block_idx,
                t,
                n_rows,
                block_idx == 0,
                block_idx == last_block_idx && has_padding,
                field_exposure,
            );
        }
    }
    if has_padding {
        let first_slot = Layout::row_slot(0, log_size);
        cols[Layout::COL_ENABLER_STEP][first_slot] = BaseField::from(1u32);
    }
    fill_schedule_sigma_bits_columns(&mut cols, log_size);
    cols
}

/// Write all columns of one `(block, round t)` row from one `BlockWitness`.
#[allow(clippy::too_many_arguments)]
fn write_round_row(
    cols: &mut [Vec<BaseField>],
    row: usize,
    witness: &Sha256Witness,
    block_idx: usize,
    t: usize,
    n_rows: usize,
    is_first_block: bool,
    is_last_block: bool,
    field_exposure: &FieldExposure,
) {
    let mut values = vec![BaseField::from(0u32); cols.len()];
    write_round_row_values(
        &mut values,
        witness,
        block_idx,
        t,
        n_rows,
        is_first_block,
        is_last_block,
        field_exposure,
    );
    for (column, value) in cols.iter_mut().zip(values) {
        column[row] = value;
    }
}

/// Write all columns of one `(block, round t)` row into a row-major buffer.
#[allow(clippy::too_many_arguments)]
fn write_round_row_values(
    row: &mut [BaseField],
    witness: &Sha256Witness,
    block_idx: usize,
    t: usize,
    n_rows: usize,
    is_first_block: bool,
    is_last_block: bool,
    field_exposure: &FieldExposure,
) {
    let block = &witness.blocks[block_idx];
    let natural_row = block_idx * ROWS_PER_BLOCK + t;
    row[Layout::COL_ENABLER] = BaseField::from(1u32);

    // The row's schedule word.
    row[Layout::COL_W_LO] = m31(block.schedule[t].lo);
    row[Layout::COL_W_HI] = m31(block.schedule[t].hi);
    write_word_bits_row(row, Layout::COL_W_BITS_START, block.schedule[t].to_u32());

    // Round family.
    let round = &block.rounds[t];
    let r = Layout::round_col();
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
        row[r[2 * i]] = m31(lw.lo);
        row[r[2 * i + 1]] = m31(lw.hi);
    }
    let carry_pairs: [AddCarries; 4] = [
        round.t1_carries,
        round.t2_carries,
        round.e_new_carries,
        round.a_new_carries,
    ];
    for (i, c) in carry_pairs.iter().enumerate() {
        row[r[16 + 2 * i]] = m31(c.lo);
        row[r[16 + 2 * i + 1]] = m31(c.hi);
    }
    write_round_operand_bits_row(row, round);
    write_round_output_groups_row(row, round);

    // Schedule family (t ≥ 16).
    let sched_sigma0_word = lower_sigma0(schedule_word_at_offset(witness, natural_row, n_rows, 15));
    let sched_sigma1_word = lower_sigma1(schedule_word_at_offset(witness, natural_row, n_rows, 2));
    write_word_bits_row(row, Layout::schedule_sigma_bit(0, 0), sched_sigma0_word);
    write_word_bits_row(row, Layout::schedule_sigma_bit(1, 0), sched_sigma1_word);
    if t >= 16 {
        let entry = &block.schedule_entries[t - 16];
        let [s0_lo, s0_hi, s1_lo, s1_hi, c_lo, c_hi] = Layout::schedule_entry();
        row[s0_lo] = m31(entry.lower_sigma0.lo);
        row[s0_hi] = m31(entry.lower_sigma0.hi);
        row[s1_lo] = m31(entry.lower_sigma1.lo);
        row[s1_hi] = m31(entry.lower_sigma1.hi);
        row[c_lo] = m31(entry.carries.lo);
        row[c_hi] = m31(entry.carries.hi);
        write_sigma_input_split_block_row(
            row,
            Layout::schedule_entry_input_split(0),
            &entry.lower_sigma0_input_split,
        );
        write_sigma_input_split_block_row(
            row,
            Layout::schedule_entry_input_split(1),
            &entry.lower_sigma1_input_split,
        );
    }

    // t = 0 family: block-input state + §8.1 initial splits.
    if t == 0 {
        row[Layout::COL_IS_FIRST_BLOCK] = BaseField::from(is_first_block as u32);
        for j in 0..N_STATE_WORDS {
            let (lo, hi) = Layout::h_in_word(j);
            row[lo] = m31(block.h_in[j].lo);
            row[hi] = m31(block.h_in[j].hi);
        }
        write_h_in_aux_grp_row(row, &block.aux_split_pack);
    }

    // t = 63 family: finalization + digest view.
    if t == N_ROUNDS - 1 {
        for (j, c) in block.finalization_carries.iter().enumerate() {
            let (lo, hi) = Layout::final_carry(j);
            row[lo] = m31(c.lo);
            row[hi] = m31(c.hi);
        }
        for j in 0..N_STATE_WORDS {
            let (lo, hi) = Layout::h_out_word(j);
            row[lo] = m31(block.h_out[j].lo);
            row[hi] = m31(block.h_out[j].hi);
        }
        row[Layout::COL_IS_LAST_BLOCK] = BaseField::from(is_last_block as u32);
        let digest_bytes = h_out_digest_bytes(&block.h_out);
        for (idx, &byte) in digest_bytes.iter().enumerate() {
            row[Layout::digest_byte(idx)] = m31(byte);
        }
    }

    // t = 15 family: padding-role witness + credential-field byte view.
    // Both inspect message words, which are the `W` columns of rows
    // `t = 0..16` — read in the AIR via mask offsets `0..−15` from here.
    if t == 15 {
        write_padding_row_values(row, &block.padding_row);
        for (word_slot, &word_idx) in field_exposure.decomposed_words().iter().enumerate() {
            let limb = block.schedule[word_idx];
            let bytes = crate::field_exposure::word_be_bytes(limb.lo, limb.hi);
            for (b, &byte) in bytes.iter().enumerate() {
                row[Layout::field_byte_col(word_slot * BYTES_PER_WORD + b)] = m31(byte);
            }
        }
        // Multi-block selectors: one-hot per yielded byte, live only on the
        // `t = 15` row of that byte's target block.
        if field_exposure.needs_block_witness() {
            for (yield_idx, y) in field_exposure.yields().iter().enumerate() {
                let slot = field_exposure
                    .selector_column_slot(yield_idx)
                    .expect("multi-block exposure has selector columns");
                row[Layout::field_byte_col(slot)] =
                    BaseField::from(u32::from(block_idx == y.block_idx));
            }
        }
    }

    // Multi-block block counter: `block_idx` on **every** row (the AIR pins it
    // to 0 on block 0, flat within a block, and +1 at each real boundary).
    if let Some(slot) = field_exposure.block_counter_column_slot() {
        row[Layout::field_byte_col(slot)] = BaseField::from(block_idx as u32);
    }
}

#[inline]
fn m31(x: u32) -> BaseField {
    // The witness emitter guarantees x ∈ [0, 2¹⁶) for limbs and small bounds
    // for carries — both are well within M31 = [0, 2³¹ − 1).
    M31::from(x)
}

#[inline]
fn write_word_bits_row(row: &mut [BaseField], base: usize, word: u32) {
    for bit in 0..WORD_BIT_COLS {
        row[base + bit] = m31((word >> bit) & 1);
    }
}

fn write_round_operand_bits_row(row: &mut [BaseField], round: &crate::types::RoundWitness) {
    let words = [
        round.state_in[0].to_u32(),
        round.state_in[1].to_u32(),
        round.state_in[2].to_u32(),
        round.state_in[4].to_u32(),
        round.state_in[5].to_u32(),
        round.state_in[6].to_u32(),
    ];
    for (operand_idx, &word) in words.iter().enumerate() {
        write_word_bits_row(row, Layout::round_operand_bit(operand_idx, 0), word);
    }
}

fn write_round_output_groups_row(row: &mut [BaseField], round: &crate::types::RoundWitness) {
    let operands: [&RoundPackedGroups; ROUND_OUTPUT_GROUP_OPERANDS] =
        [&round.maj_ch.maj_grp, &round.maj_ch.ch_grp];
    for (operand_idx, operand) in operands.iter().enumerate() {
        for (group_idx, &v) in operand.vals.iter().enumerate() {
            row[Layout::round_output_group(operand_idx, group_idx)] = m31(v);
        }
    }
}

fn schedule_word_at_offset(
    witness: &Sha256Witness,
    natural_row: usize,
    n_rows: usize,
    back: usize,
) -> u32 {
    let n_real_rows = witness.blocks.len() * ROWS_PER_BLOCK;
    let target = (natural_row + n_rows - back) % n_rows;
    if target >= n_real_rows {
        return 0;
    }
    let block_idx = target / ROWS_PER_BLOCK;
    let t = target % ROWS_PER_BLOCK;
    witness.blocks[block_idx].schedule[t].to_u32()
}

fn fill_schedule_sigma_bits_rows(rows: &mut [Vec<BaseField>]) {
    let n_rows = rows.len();
    for row_idx in 0..n_rows {
        let w_m15 = word_from_row_bits(&rows[(row_idx + n_rows - 15) % n_rows]);
        let w_m2 = word_from_row_bits(&rows[(row_idx + n_rows - 2) % n_rows]);
        write_word_bits_row(
            &mut rows[row_idx],
            Layout::schedule_sigma_bit(0, 0),
            lower_sigma0(w_m15),
        );
        write_word_bits_row(
            &mut rows[row_idx],
            Layout::schedule_sigma_bit(1, 0),
            lower_sigma1(w_m2),
        );
    }
}

fn fill_schedule_sigma_bits_columns(cols: &mut [Vec<BaseField>], log_size: u32) {
    let n_rows = 1usize << log_size;
    for storage_row in 0..n_rows {
        let coset_index =
            circle_domain_index_to_coset_index(bit_reverse_index(storage_row, log_size), log_size);
        let word_at_offset = |back: usize| {
            let target_coset = (coset_index + n_rows - back) % n_rows;
            let target_storage = bit_reverse_index(
                coset_index_to_circle_domain_index(target_coset, log_size),
                log_size,
            );
            let mut word = 0u32;
            for bit in 0..WORD_BIT_COLS {
                word |= cols[Layout::w_bit(bit)][target_storage].0 << bit;
            }
            word
        };
        let s0 = lower_sigma0(word_at_offset(15));
        let s1 = lower_sigma1(word_at_offset(2));
        for bit in 0..WORD_BIT_COLS {
            cols[Layout::schedule_sigma_bit(0, bit)][storage_row] = m31((s0 >> bit) & 1);
            cols[Layout::schedule_sigma_bit(1, bit)][storage_row] = m31((s1 >> bit) & 1);
        }
    }
}

fn word_from_row_bits(row: &[BaseField]) -> u32 {
    let mut word = 0u32;
    for bit in 0..WORD_BIT_COLS {
        word |= row[Layout::w_bit(bit)].0 << bit;
    }
    word
}

fn write_h_in_aux_grp_row(row: &mut [BaseField], aux: &BlockAuxSplitPackWitness) {
    let operands: [&RoundPackedGroups; H_IN_AUX_OPERANDS] =
        [&aux.b_init, &aux.c_init, &aux.f_init, &aux.g_init];
    for (aux_idx, operand) in operands.iter().enumerate() {
        for (group_idx, &v) in operand.vals.iter().enumerate() {
            row[Layout::h_in_aux_grp(aux_idx, group_idx)] = m31(v);
        }
    }
}

fn write_sigma_input_split_block_row(
    row: &mut [BaseField],
    base: usize,
    w: &SigmaInputSplitPackWitness,
) {
    row[base] = m31(w.packed_s_lo);
    row[base + 1] = m31(w.packed_s_complement_lo);
    row[base + 2] = m31(w.packed_s_hi);
    row[base + 3] = m31(w.packed_s_complement_hi);
}

fn write_padding_row_values(row: &mut [BaseField], p: &PaddingRowWitness) {
    row[Layout::COL_IS_MARKER_BLOCK] = m31(p.is_marker_block);
    row[Layout::COL_IS_LENGTH_BLOCK] = m31(p.is_length_block);
    row[Layout::COL_IS_LENGTH_ONLY_BLOCK] = m31(p.is_length_only_block);
    row[Layout::COL_IS_MARKER_ONLY_BLOCK] = m31(p.is_marker_only_block);
    for (j, &v) in p.is_marker_word.iter().enumerate() {
        row[Layout::is_marker_word(j)] = m31(v);
    }
    for (b, &v) in p.marker_byte_sel.iter().enumerate() {
        row[Layout::marker_byte_sel(b)] = m31(v);
    }
    for (b, &v) in p.marker_word_byte.iter().enumerate() {
        row[Layout::marker_word_byte(b)] = m31(v);
    }
    row[Layout::COL_MARKER_WORD_POST_STRICT_15] = m31(p.marker_word_post_strict_15);
    row[Layout::COL_BIT_LENGTH_W14_LO] = m31(p.bit_length_w14_lo);
    row[Layout::COL_BIT_LENGTH_W14_HI] = m31(p.bit_length_w14_hi);
    row[Layout::COL_BIT_LENGTH_W15_LO] = m31(p.bit_length_w15_lo);
    row[Layout::COL_BIT_LENGTH_W15_HI] = m31(p.bit_length_w15_hi);
}

/// Required `log_size` for `n_blocks` blocks (smallest power of two
/// `> 64 · n_blocks` — **strictly** greater, so the trace always ends with
/// at least one padding row and the `is_last_block` gate
/// `enabler · is_round_63 · (1 − enabler_next)` can fire — and at least
/// `LOG_MIN` so SIMD backends are happy).
pub fn min_log_size(n_blocks: usize) -> u32 {
    const LOG_MIN: u32 = 4; // SIMD lane count is 16 → at least 16 rows.
    let rows = n_blocks.max(1) * ROWS_PER_BLOCK;
    // Strictly-greater power of two: 64·n real rows never fill the trace.
    let needed = (rows + 1).next_power_of_two().ilog2();
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

    /// Round-trip: trace materialised from a witness, decoded back from the
    /// final block's `t = 63` row `h_out` columns, yields the sha2 digest.
    fn round_trip_digest(msg: &[u8]) {
        let witness = compute_sha256_witness(msg);
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);

        let last_block = witness.blocks.len() - 1;
        let slot = Layout::round_row_slot(last_block, N_ROUNDS - 1, log_size);
        let mut digest = [0u8; 32];
        for j in 0..N_STATE_WORDS {
            let (lo_col, hi_col) = Layout::h_out_word(j);
            let lo = trace[lo_col][slot].0;
            let hi = trace[hi_col][slot].0;
            let word = lo + (hi << 16);
            digest[4 * j..4 * j + 4].copy_from_slice(&word.to_be_bytes());
        }
        assert_eq!(digest, sha2_reference(msg), "digest mismatch");
    }

    #[test]
    fn single_block_round_trip() {
        round_trip_digest(b"abc");
    }

    #[test]
    fn multi_block_round_trip() {
        round_trip_digest(&[0x5a; 200]);
    }

    #[test]
    fn empty_message_round_trip() {
        round_trip_digest(b"");
    }

    /// The 32 digest byte columns on the final `t = 63` row recompose to the
    /// sha2 digest.
    fn digest_byte_columns_match(msg: &[u8]) {
        let witness = compute_sha256_witness(msg);
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);
        let last_block = witness.blocks.len() - 1;
        let slot = Layout::round_row_slot(last_block, N_ROUNDS - 1, log_size);
        let mut digest = [0u8; DIGEST_BYTES];
        for (idx, d) in digest.iter_mut().enumerate() {
            *d = trace[Layout::digest_byte(idx)][slot].0 as u8;
        }
        assert_eq!(digest, sha2_reference(msg), "digest byte view mismatch");
    }

    #[test]
    fn digest_byte_columns_single_block() {
        digest_byte_columns_match(b"abc");
    }

    #[test]
    fn digest_byte_columns_multi_block() {
        digest_byte_columns_match(&[0x77; 150]);
    }

    /// Enabler is 1 on exactly the `64 · n_blocks` real rows; the boundary
    /// flags live on their designated round rows only; `enabler_step` marks
    /// row 0.
    #[test]
    fn enabler_and_flags_are_correct() {
        let witness = compute_sha256_witness(&[0x11; 100]); // 2 blocks
        let n_blocks = witness.blocks.len();
        assert_eq!(n_blocks, 2);
        let log_size = min_log_size(n_blocks);
        let trace = generate_trace(&witness, log_size);
        let n_rows = 1usize << log_size;

        let mut enabled = 0u32;
        for slot in 0..n_rows {
            enabled += trace[Layout::COL_ENABLER][slot].0;
        }
        assert_eq!(enabled as usize, n_blocks * ROWS_PER_BLOCK);

        // is_first_block: only at (block 0, t = 0).
        for b in 0..n_blocks {
            for t in 0..N_ROUNDS {
                let slot = Layout::round_row_slot(b, t, log_size);
                let expected = u32::from(b == 0 && t == 0);
                assert_eq!(
                    trace[Layout::COL_IS_FIRST_BLOCK][slot].0,
                    expected,
                    "is_first_block at ({b}, {t})"
                );
                let expected_last = u32::from(b == n_blocks - 1 && t == N_ROUNDS - 1);
                assert_eq!(
                    trace[Layout::COL_IS_LAST_BLOCK][slot].0,
                    expected_last,
                    "is_last_block at ({b}, {t})"
                );
            }
        }
        assert_eq!(
            trace[Layout::COL_ENABLER_STEP][Layout::row_slot(0, log_size)].0,
            1
        );
    }

    /// `min_log_size` always leaves at least one padding row, including at
    /// power-of-two block counts, so the digest gate can fire.
    #[test]
    fn min_log_size_leaves_padding() {
        for n_blocks in [1usize, 2, 3, 4, 5, 8, 16, 31, 32] {
            let log = min_log_size(n_blocks);
            assert!(
                n_blocks * ROWS_PER_BLOCK < (1 << log),
                "no padding row at n_blocks={n_blocks} (log={log})"
            );
        }
    }

    /// h_in of the first block (its `t = 0` row) is the IV.
    #[test]
    fn h_in_of_first_block_is_iv() {
        use crate::constants::IV;
        let witness = compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);
        let slot = Layout::round_row_slot(0, 0, log_size);
        for (j, &iv) in IV.iter().enumerate() {
            let (lo_col, hi_col) = Layout::h_in_word(j);
            let word = trace[lo_col][slot].0 + (trace[hi_col][slot].0 << 16);
            assert_eq!(word, iv, "h_in[{j}] != IV");
        }
    }

    /// Block chaining: block b's `h_in` (t = 0 row) equals block b−1's
    /// `h_out` (t = 63 row) — the two rows are coset neighbours.
    #[test]
    fn block_chain_h_out_to_h_in_continuity() {
        let witness = compute_sha256_witness(&[0x22; 200]);
        assert!(witness.blocks.len() >= 2);
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);
        for b in 1..witness.blocks.len() {
            let cur = Layout::round_row_slot(b, 0, log_size);
            let prev = Layout::round_row_slot(b - 1, N_ROUNDS - 1, log_size);
            for j in 0..N_STATE_WORDS {
                let (in_lo, in_hi) = Layout::h_in_word(j);
                let (out_lo, out_hi) = Layout::h_out_word(j);
                assert_eq!(trace[in_lo][cur], trace[out_lo][prev], "lo j={j} b={b}");
                assert_eq!(trace[in_hi][cur], trace[out_hi][prev], "hi j={j} b={b}");
            }
        }
    }

    /// Coset adjacency: `(b, 0)` and `(b − 1, 63)` are natural-row
    /// neighbours, so the AIR's offset `−1` from a `t = 0` row lands on the
    /// previous block's `t = 63` row.
    #[test]
    fn round_rows_are_coset_adjacent() {
        let log_size = 9;
        for b in 1..4usize {
            assert_eq!(
                b * ROWS_PER_BLOCK - 1,
                (b - 1) * ROWS_PER_BLOCK + (N_ROUNDS - 1),
            );
        }
        // Natural indices map to slots injectively.
        let mut seen = std::collections::HashSet::new();
        for r in 0..(1usize << log_size) {
            assert!(seen.insert(Layout::row_slot(r, log_size)));
        }
    }

    /// The column-count breakdown documented on [`Layout`] adds up.
    #[test]
    fn layout_total_cols_matches_expected_breakdown() {
        let expected = 1 // enabler
            + 2 // W
            + WORD_BIT_COLS
            + ROUND_COLS
            + SCHEDULE_ENTRY_COLS
            + 1 // is_first_block
            + 2 * N_STATE_WORDS // h_in
            + H_IN_AUX_GRP_COLS
            + 2 * N_STATE_WORDS // final carries
            + 2 * N_STATE_WORDS // h_out
            + 1 // is_last_block
            + DIGEST_BYTES
            + PADDING_ROW_COLS
            + 1; // enabler_step
        assert_eq!(Layout::TOTAL_COLS, expected);
        assert_eq!(ROUND_COLS, 232);
        assert_eq!(SCHEDULE_ENTRY_COLS, 78);
        assert_eq!(Layout::TOTAL_COLS, 493);
    }

    /// Round family, schedule family, and boundary families round-trip a
    /// couple of spot cells through the trace.
    #[test]
    fn families_round_trip_through_trace() {
        let witness = compute_sha256_witness(&[0x33; 100]);
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);

        for (b, block) in witness.blocks.iter().enumerate() {
            for t in 0..N_ROUNDS {
                let slot = Layout::round_row_slot(b, t, log_size);
                // W word.
                assert_eq!(trace[Layout::COL_W_LO][slot].0, block.schedule[t].lo);
                assert_eq!(trace[Layout::COL_W_HI][slot].0, block.schedule[t].hi);
                // Round: a_new is limb pair 6.
                let r = Layout::round_col();
                assert_eq!(trace[r[12]][slot].0, block.rounds[t].a_new.lo);
                assert_eq!(trace[r[13]][slot].0, block.rounds[t].a_new.hi);
                // a bit 0 and Maj output group 0.
                assert_eq!(
                    trace[Layout::round_operand_bit(0, 0)][slot].0,
                    block.rounds[t].state_in[0].to_u32() & 1
                );
                assert_eq!(
                    trace[Layout::round_output_group(0, 0)][slot].0,
                    block.rounds[t].maj_ch.maj_grp.vals[0]
                );
                // Schedule family: σ0 output limb.
                if t >= 16 {
                    let [s0_lo, ..] = Layout::schedule_entry();
                    assert_eq!(
                        trace[s0_lo][slot].0,
                        block.schedule_entries[t - 16].lower_sigma0.lo
                    );
                    assert_eq!(
                        trace[Layout::schedule_entry_input_split(1)][slot].0,
                        block.schedule_entries[t - 16]
                            .lower_sigma1_input_split
                            .packed_s_lo
                    );
                } else {
                    // Schedule family is zero on t < 16 rows.
                    let [s0_lo, ..] = Layout::schedule_entry();
                    assert_eq!(trace[s0_lo][slot].0, 0);
                }
                // t = 0 family.
                if t == 0 {
                    assert_eq!(
                        trace[Layout::h_in_aux_grp(0, 0)][slot].0,
                        block.aux_split_pack.b_init.vals[0]
                    );
                } else {
                    assert_eq!(trace[Layout::h_in_aux_grp(0, 0)][slot].0, 0);
                }
                // t = 15 family.
                if t == 15 {
                    assert_eq!(
                        trace[Layout::COL_IS_MARKER_BLOCK][slot].0,
                        block.padding_row.is_marker_block
                    );
                }
                // t = 63 family.
                if t == N_ROUNDS - 1 {
                    let (lo, hi) = Layout::final_carry(3);
                    assert_eq!(trace[lo][slot].0, block.finalization_carries[3].lo);
                    assert_eq!(trace[hi][slot].0, block.finalization_carries[3].hi);
                }
            }
        }
    }

    #[test]
    fn packed_trace_writer_matches_scalar_writer_with_field_exposure() {
        let witness = compute_sha256_witness(&[0x44; 180]);
        let log_size = min_log_size(witness.blocks.len());
        let exposure = FieldExposure::from_preimage_windows(&[(7, 5, 4), (8, 9, 2)]);

        assert_eq!(
            generate_trace_with_fields_scalar(&witness, log_size, &exposure),
            generate_trace_with_fields_packed(&witness, log_size, &exposure)
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
    fn sha_trace_writer_timing() {
        let witness = compute_sha256_witness(&[0x55; 2048]);
        let log_size = min_log_size(witness.blocks.len());
        let exposure = FieldExposure::from_preimage_windows(&[(7, 5, 4), (8, 9, 2)]);
        let scalar = best_of(5, || {
            std::hint::black_box(generate_trace_with_fields_scalar(
                &witness, log_size, &exposure,
            ));
        });
        let packed = best_of(5, || {
            std::hint::black_box(generate_trace_with_fields_packed(
                &witness, log_size, &exposure,
            ));
        });
        eprintln!("sha trace scalar={scalar:?} packed={packed:?}");
    }
}
