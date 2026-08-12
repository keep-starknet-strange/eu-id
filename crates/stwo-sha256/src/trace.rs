//! Trace construction for the SHA-256 AIR.
//!
//! Each block has three state-seed rows followed by one row for each SHA
//! round. The seed rows place h3/h7, h2/h6, and h1/h5 in the rolling a/e
//! bit lanes; round zero places h0/h4 there.
//!
//! A mask offset of `-k` reads the row that is `k` rounds earlier. The AIR uses
//! these reads for state updates, schedule recurrence, and block chaining. See
//! [`crate::constraints`].
//!
//! Each row contains the `enabler`, `W`, and the `W` bit plane. It also
//! contains the round results, carries, and operand bit planes. Schedule rows
//! contain the lower-sigma results and carry values.
//!
//! Boundary rows contain the input state, output state, digest bytes, and
//! padding data. Packed message IDs and per-message block numbers are private
//! witness columns. Padding rows contain disabled random decoy data.

use stwo::core::fields::m31::{BaseField, M31};
use stwo::core::utils::{
    bit_reverse_index, circle_domain_index_to_coset_index, coset_index_to_circle_domain_index,
};
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES, N_LANES};

use crate::constants::{DIGEST_BYTES, N_INPUT_WORDS, N_ROUNDS, N_STATE_WORDS, WORD_BYTES};
use crate::native::{big_sigma0, big_sigma1, ch, lower_sigma0, lower_sigma1, maj};
use crate::types::{AddCarries, PackedSha256Witness, PaddingRowWitness, Sha256Witness, WordLimbs};

use rand::RngCore;

/// State rows before round zero. They seed the rolling a/e bit lanes.
pub const STATE_SEED_ROWS: usize = 3;

/// Rows one block occupies: three state seeds and one row per round.
pub const ROWS_PER_BLOCK: usize = STATE_SEED_ROWS + N_ROUNDS;

/// Bits per SHA-256 word, committed LSB-first.
pub const WORD_BIT_COLS: usize = 32;
/// Rolling state bit columns. Only a/e are committed; b/c/d and f/g/h are
/// read from the preceding three rows. Operand order: `[a, e]`.
pub const ROUND_BIT_OPERANDS: usize = 2;
pub const ROUND_OPERAND_BIT_COLS: usize = ROUND_BIT_OPERANDS * WORD_BIT_COLS;
/// Columns of the round family: 8 word-results × 2 limbs + 4 carry pairs
/// × 2 ends = 24, then committed operand bits. Σ0/Σ1/Maj/Ch are computed
/// directly from those boolean bit-planes (no packed-group columns).
pub const ROUND_COLS: usize = 8 * 2 + 4 * 2 + ROUND_OPERAND_BIT_COLS;
/// Columns of the schedule family: `σ0`, `σ1`, and carries. The sigma
/// words are constrained on every row; the recurrence and carries are live
/// only for `t ≥ 16`.
pub const SCHEDULE_ENTRY_COLS: usize = 6;
/// Columns dedicated to the per-block padding-role witness (§10.4 of the
/// validated design), live on each block's `t = 15` row. Laid out in the
/// order `write_padding_row_values` writes them:
///
/// 1. `is_marker_block` (1)
/// 2. `is_length_block` (1)
/// 3. `is_marker_word[16]` (16)   — one-hot for the marker's word index
/// 4. `marker_byte_sel[4]` (4)    — one-hot for byte-in-word, BE order
/// 5. `marker_word_byte[4]` (4)   — BE byte decomposition of `W[marker_word_idx]`
/// 6. `bit_length_w14_lo` (1)
/// 7. `bit_length_w14_hi` (1)
/// 8. `bit_length_w15_lo` (1)
/// 9. `bit_length_w15_hi` (1)
///
/// `2 flags + 16 one-hot word selectors + 4 byte selectors + 4 marker bytes
/// + 4 bit-length limbs = 30` cells per block. The former auxiliary flags
/// are derived in the AIR, or deleted when unused.
pub const PADDING_ROW_COLS: usize = 2 + N_INPUT_WORDS + WORD_BYTES + WORD_BYTES + 4;

/// Named column-range layout. Every range is in `[start, end)`. The column
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
    /// Message-start marker, written on each block's first seed row.
    pub const COL_MSG_START: usize = Self::COL_SCHED_ENTRY_END;
    /// `t = 63` family. The first 30 cells are also the padding-role
    /// witness on the disjoint `t = 15` family.
    pub const COL_FINAL_CARRIES_START: usize = Self::COL_MSG_START + 1;
    pub const COL_FINAL_CARRIES_END: usize = Self::COL_FINAL_CARRIES_START + 2 * N_STATE_WORDS;
    pub const COL_H_OUT_START: usize = Self::COL_FINAL_CARRIES_END;
    pub const COL_H_OUT_END: usize = Self::COL_H_OUT_START + 2 * N_STATE_WORDS;

    /// `is_msg_last` flag (1 col): `1` on the `t = 63` row immediately before
    /// the next message or disabled tail, `0` on continuation blocks.
    pub const COL_IS_MSG_LAST: usize = Self::COL_H_OUT_END;

    /// The 32 big-endian digest-byte columns for this block.
    ///
    /// For each state word, the order is
    /// `[hi.b1, hi.b0, lo.b1, lo.b0]`. The AIR checks
    /// `limb = 256 * b1 + b0`. Each `t = 63` row contains these bytes, but the
    /// packed digest relation emits them only for the final block.
    pub const COL_DIGEST_BYTES_START: usize = Self::COL_IS_MSG_LAST + 1;
    pub const COL_DIGEST_BYTES_END: usize = Self::COL_DIGEST_BYTES_START + DIGEST_BYTES;

    /// Per-block padding-role region, aliased onto the first 30 cells of the
    /// 32-cell finalization-carry/output region.
    pub const COL_PADDING_START: usize = Self::COL_FINAL_CARRIES_START;
    pub const COL_IS_MARKER_BLOCK: usize = Self::COL_PADDING_START;
    pub const COL_IS_LENGTH_BLOCK: usize = Self::COL_PADDING_START + 1;
    pub const COL_IS_MARKER_WORD_START: usize = Self::COL_PADDING_START + 2;
    pub const COL_IS_MARKER_WORD_END: usize = Self::COL_IS_MARKER_WORD_START + N_INPUT_WORDS;
    pub const COL_MARKER_BYTE_SEL_START: usize = Self::COL_IS_MARKER_WORD_END;
    pub const COL_MARKER_BYTE_SEL_END: usize = Self::COL_MARKER_BYTE_SEL_START + WORD_BYTES;
    pub const COL_MARKER_WORD_BYTE_START: usize = Self::COL_MARKER_BYTE_SEL_END;
    pub const COL_MARKER_WORD_BYTE_END: usize = Self::COL_MARKER_WORD_BYTE_START + WORD_BYTES;
    pub const COL_BIT_LENGTH_W14_LO: usize = Self::COL_MARKER_WORD_BYTE_END;
    pub const COL_BIT_LENGTH_W14_HI: usize = Self::COL_MARKER_WORD_BYTE_END + 1;
    pub const COL_BIT_LENGTH_W15_LO: usize = Self::COL_MARKER_WORD_BYTE_END + 2;
    pub const COL_BIT_LENGTH_W15_HI: usize = Self::COL_MARKER_WORD_BYTE_END + 3;
    pub const COL_PADDING_END: usize = Self::COL_PADDING_START + PADDING_ROW_COLS;

    /// Private packed-message key, flat over each message's blocks.
    pub const COL_MSG_ID: usize = Self::COL_DIGEST_BYTES_END;
    /// Private block number, reset at each message start.
    pub const COL_MSG_BLOCK: usize = Self::COL_MSG_ID + 1;
    pub const TOTAL_COLS: usize = Self::COL_MSG_BLOCK + 1;

    /// `(lo, hi)` slot for the row's schedule word `W[t]`.
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

    /// Column of a rolling state bit. Operand order is `[a, e]`.
    #[inline]
    pub const fn round_operand_bit(operand_idx: usize, bit: usize) -> usize {
        debug_assert!(operand_idx < ROUND_BIT_OPERANDS);
        Self::COL_ROUND_START + 24 + operand_idx * WORD_BIT_COLS + bit
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

    /// Storage slot of a natural row in the 67-row block layout, for a
    /// trace of size `2^log_size`.
    ///
    /// Row `r` has coset index `r`. First, map it to a circle-domain index.
    /// Then, reverse the index bits to get the storage slot.
    ///
    /// The `r ↔ coset_index` mapping controls the AIR's cross-row reads.
    /// `next_interaction_mask(_, [0, -k])` walks coset indices. Thus, offset `-k`
    /// from row `r` returns row `r − k`. This provides the working-state,
    /// schedule, and block-chain links required by [`crate::constraints::Sha256Eval`].
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
        Self::row_slot(
            block_idx * ROWS_PER_BLOCK + STATE_SEED_ROWS + round_t,
            log_size,
        )
    }

    /// Storage slot of one of the three state-seed rows.
    #[inline]
    pub fn seed_row_slot(block_idx: usize, seed: usize, log_size: u32) -> usize {
        debug_assert!(seed < STATE_SEED_ROWS);
        Self::row_slot(block_idx * ROWS_PER_BLOCK + seed, log_size)
    }
}

const _: () = assert!(Layout::COL_PADDING_END <= Layout::COL_H_OUT_END);

/// Return the 32 big-endian bytes of one `h_out` value.
///
/// Each state word has the order `[hi.b1, hi.b0, lo.b1, lo.b0]`. The trace,
/// constraints, and packed digest relation use this same order. Each limb
/// satisfies `limb = 256 * b1 + b0`.
pub fn h_out_digest_bytes(h_out: &[WordLimbs; N_STATE_WORDS]) -> [u32; DIGEST_BYTES] {
    let mut out = [0u32; DIGEST_BYTES];
    for (j, limb) in h_out.iter().enumerate() {
        let bytes = word_be_bytes(limb.lo, limb.hi);
        out[4 * j..4 * j + 4].copy_from_slice(&bytes);
    }
    out
}

pub fn word_be_bytes(lo: u32, hi: u32) -> [u32; WORD_BYTES] {
    [(hi >> 8) & 0xff, hi & 0xff, (lo >> 8) & 0xff, lo & 0xff]
}

pub fn generate_trace(witness: &PackedSha256Witness, log_size: u32) -> Vec<Vec<BaseField>> {
    generate_trace_base_columns(witness, log_size)
        .into_iter()
        .map(BaseColumn::into_cpu_vec)
        .collect()
}

pub(crate) fn generate_trace_base_columns(
    witness: &PackedSha256Witness,
    log_size: u32,
) -> Vec<BaseColumn> {
    assert!(log_size < usize::BITS, "trace log size is too large");
    let n_rows = 1usize << log_size;
    let n_real_rows = witness.total_blocks() * ROWS_PER_BLOCK;
    assert!(n_real_rows <= n_rows, "packed SHA trace is too small");
    assert!(n_real_rows.is_multiple_of(ROWS_PER_BLOCK));
    let decoys = decoy_witnesses_for_padding(n_real_rows, n_rows);
    generate_trace_base_columns_with_decoys(witness, log_size, &decoys)
}

fn generate_trace_base_columns_with_decoys(
    witness: &PackedSha256Witness,
    log_size: u32,
    decoys: &[Sha256Witness],
) -> Vec<BaseColumn> {
    if log_size < LOG_N_LANES || rayon::current_num_threads() == 1 {
        return generate_trace_scalar(witness, log_size, decoys)
            .into_iter()
            .map(|values| values.into_iter().collect())
            .collect();
    }

    use rayon::prelude::*;
    let n_rows = 1usize << log_size;
    let n_real_rows = witness.total_blocks() * ROWS_PER_BLOCK;
    let mut row_values = (0..n_rows)
        .into_par_iter()
        .map(|row_idx| {
            if row_idx >= n_real_rows {
                return disabled_decoy_row_values(
                    &decoys[(row_idx - n_real_rows) / ROWS_PER_BLOCK],
                    (row_idx - n_real_rows) % ROWS_PER_BLOCK,
                );
            }
            let (message_idx, block_idx) = locate_block(witness, row_idx / ROWS_PER_BLOCK);
            let mut values = vec![BaseField::from(0u32); Layout::TOTAL_COLS];
            let block_row = row_idx % ROWS_PER_BLOCK;
            if block_row < STATE_SEED_ROWS {
                write_seed_row_values(
                    &mut values,
                    &witness.messages[message_idx],
                    block_idx,
                    block_row,
                    message_idx,
                    block_idx == 0,
                );
            } else {
                write_round_row_values(
                    &mut values,
                    &witness.messages[message_idx],
                    block_idx,
                    block_row - STATE_SEED_ROWS,
                    message_idx,
                    witness.messages[message_idx].blocks.len() - 1 == block_idx,
                );
            }
            values
        })
        .collect::<Vec<_>>();
    fill_schedule_sigma_words_rows(&mut row_values);
    fill_round_function_limbs_rows(&mut row_values);

    let packed_rows = 1usize << (log_size - LOG_N_LANES);
    (0..Layout::TOTAL_COLS)
        .into_par_iter()
        .map(|column| {
            let data = (0..packed_rows)
                .map(|packed_row| {
                    PackedM31::from_array(core::array::from_fn(|lane| {
                        let storage_index = packed_row * N_LANES + lane;
                        let circle_index = bit_reverse_index(storage_index, log_size);
                        let coset_index =
                            circle_domain_index_to_coset_index(circle_index, log_size);
                        row_values[coset_index][column]
                    }))
                })
                .collect();
            BaseColumn::from_simd(data)
        })
        .collect()
}

fn generate_trace_scalar(
    witness: &PackedSha256Witness,
    log_size: u32,
    decoys: &[Sha256Witness],
) -> Vec<Vec<BaseField>> {
    let n_rows = 1usize << log_size;
    let n_real_rows = witness.total_blocks() * ROWS_PER_BLOCK;
    assert!(n_real_rows.is_multiple_of(ROWS_PER_BLOCK));
    let mut cols = vec![vec![BaseField::from(0u32); n_rows]; Layout::TOTAL_COLS];
    for row_idx in 0..n_real_rows {
        let (message_idx, block_idx) = locate_block(witness, row_idx / ROWS_PER_BLOCK);
        let slot = Layout::row_slot(row_idx, log_size);
        let block_row = row_idx % ROWS_PER_BLOCK;
        if block_row < STATE_SEED_ROWS {
            write_seed_row(
                &mut cols,
                slot,
                &witness.messages[message_idx],
                block_idx,
                block_row,
                message_idx,
                block_idx == 0,
            );
        } else {
            write_round_row(
                &mut cols,
                slot,
                &witness.messages[message_idx],
                block_idx,
                block_row - STATE_SEED_ROWS,
                message_idx,
                witness.messages[message_idx].blocks.len() - 1 == block_idx,
            );
        }
    }
    for row_idx in n_real_rows..n_rows {
        let slot = Layout::row_slot(row_idx, log_size);
        for (column, value) in cols.iter_mut().zip(disabled_decoy_row_values(
            &decoys[(row_idx - n_real_rows) / ROWS_PER_BLOCK],
            (row_idx - n_real_rows) % ROWS_PER_BLOCK,
        )) {
            column[slot] = value;
        }
    }
    fill_schedule_sigma_words_columns(&mut cols, log_size);
    fill_round_function_limbs_columns(&mut cols, log_size);
    cols
}

fn decoy_witnesses_for_padding(n_real_rows: usize, n_rows: usize) -> Vec<Sha256Witness> {
    decoy_witnesses_for_padding_with(n_real_rows, n_rows, &mut rand::thread_rng())
}

/// Create decoy blocks from the supplied random byte source.
///
/// Production code supplies `thread_rng`, which has an `OsRng` seed. The
/// scalar-to-packed equivalence test supplies one fixed seed to both writers.
/// This choice gives both writers the same decoys and the same boundary bits.
fn decoy_witnesses_for_padding_with(
    n_real_rows: usize,
    n_rows: usize,
    rng: &mut impl RngCore,
) -> Vec<Sha256Witness> {
    let pad_rows = n_rows.saturating_sub(n_real_rows);
    (0..pad_rows.div_ceil(ROWS_PER_BLOCK))
        .map(|_| random_one_block_decoy_witness(rng))
        .collect()
}

fn random_one_block_decoy_witness(rng: &mut impl RngCore) -> Sha256Witness {
    const DECOY_MESSAGE_BYTES: usize = 32;
    let mut message = [0u8; DECOY_MESSAGE_BYTES];
    rng.fill_bytes(&mut message);
    let witness = crate::witness::compute_sha256_witness(&message);
    debug_assert_eq!(witness.blocks.len(), 1);
    witness
}

fn disabled_decoy_row_values(decoy: &Sha256Witness, block_row: usize) -> Vec<BaseField> {
    let mut values = vec![BaseField::from(0u32); Layout::TOTAL_COLS];
    if block_row < STATE_SEED_ROWS {
        write_seed_row_values(&mut values, decoy, 0, block_row, 0, false);
    } else {
        write_round_row_values(&mut values, decoy, 0, block_row - STATE_SEED_ROWS, 0, false);
    }
    values[Layout::COL_ENABLER] = BaseField::from(0u32);
    values[Layout::COL_MSG_START] = BaseField::from(0u32);
    values[Layout::COL_IS_MSG_LAST] = BaseField::from(0u32);
    values[Layout::COL_MSG_ID] = BaseField::from(0u32);
    values[Layout::COL_MSG_BLOCK] = BaseField::from(0u32);
    // These cells alias live finalization data at t=63, so only clear the
    // padding-family view on other decoy rows.
    if block_row != STATE_SEED_ROWS + N_ROUNDS - 1 {
        values[Layout::COL_PADDING_START..Layout::COL_PADDING_END].fill(BaseField::from(0u32));
    }
    values
}

/// Write all columns of one `(block, round t)` row from one `BlockWitness`.
#[allow(clippy::too_many_arguments)]
fn write_round_row(
    cols: &mut [Vec<BaseField>],
    row: usize,
    witness: &Sha256Witness,
    block_idx: usize,
    t: usize,
    message_idx: usize,
    is_msg_last: bool,
) {
    let mut values = vec![BaseField::from(0u32); cols.len()];
    write_round_row_values(&mut values, witness, block_idx, t, message_idx, is_msg_last);
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
    message_idx: usize,
    is_msg_last: bool,
) {
    let block = &witness.blocks[block_idx];
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
    write_round_state_bits_row(row, round.state_in[0].to_u32(), round.state_in[4].to_u32());

    // Schedule family. The sigma words are filled for every row in a later
    // pass from the committed W bits; only the recurrence carries are live
    // for t ≥ 16.
    if t >= 16 {
        let entry = &block.schedule_entries[t - 16];
        let [_s0_lo, _s0_hi, _s1_lo, _s1_hi, c_lo, c_hi] = Layout::schedule_entry();
        row[c_lo] = m31(entry.carries.lo);
        row[c_hi] = m31(entry.carries.hi);
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
        row[Layout::COL_IS_MSG_LAST] = BaseField::from(is_msg_last as u32);
        let digest_bytes = h_out_digest_bytes(&block.h_out);
        for (idx, &byte) in digest_bytes.iter().enumerate() {
            row[Layout::digest_byte(idx)] = m31(byte);
        }
    }

    row[Layout::COL_MSG_ID] = m31(message_idx as u32);
    row[Layout::COL_MSG_BLOCK] = m31(block_idx as u32);

    // t = 15 family: padding-role witness.
    if t == 15 {
        write_padding_row_values(row, &block.padding_row);
    }
}

fn write_seed_row(
    cols: &mut [Vec<BaseField>],
    row: usize,
    witness: &Sha256Witness,
    block_idx: usize,
    seed: usize,
    message_idx: usize,
    msg_start: bool,
) {
    let mut values = vec![BaseField::from(0u32); cols.len()];
    write_seed_row_values(
        &mut values,
        witness,
        block_idx,
        seed,
        message_idx,
        msg_start,
    );
    for (column, value) in cols.iter_mut().zip(values) {
        column[row] = value;
    }
}

fn write_seed_row_values(
    row: &mut [BaseField],
    witness: &Sha256Witness,
    block_idx: usize,
    seed: usize,
    message_idx: usize,
    msg_start: bool,
) {
    debug_assert!(seed < STATE_SEED_ROWS);
    let block = &witness.blocks[block_idx];
    let state_index = STATE_SEED_ROWS - seed;
    row[Layout::COL_ENABLER] = BaseField::from(1u32);
    write_round_state_bits_row(
        row,
        block.h_in[state_index].to_u32(),
        block.h_in[N_STATE_WORDS / 2 + state_index].to_u32(),
    );
    if seed == 0 {
        row[Layout::COL_MSG_START] = BaseField::from(msg_start as u32);
    }
    row[Layout::COL_MSG_ID] = m31(message_idx as u32);
    row[Layout::COL_MSG_BLOCK] = m31(block_idx as u32);
}

fn locate_block(witness: &PackedSha256Witness, global_block: usize) -> (usize, usize) {
    let mut offset = global_block;
    for (message_idx, message) in witness.messages.iter().enumerate() {
        if offset < message.blocks.len() {
            return (message_idx, offset);
        }
        offset -= message.blocks.len();
    }
    panic!("packed SHA block index is out of range");
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

#[inline]
fn write_word_limbs_row(row: &mut [BaseField], base: usize, word: u32) {
    row[base] = m31(word & 0xffff);
    row[base + 1] = m31(word >> 16);
}

fn write_round_state_bits_row(row: &mut [BaseField], a: u32, e: u32) {
    let words = [a, e];
    for (operand_idx, &word) in words.iter().enumerate() {
        write_word_bits_row(row, Layout::round_operand_bit(operand_idx, 0), word);
    }
}

fn fill_schedule_sigma_words_rows(rows: &mut [Vec<BaseField>]) {
    let n_rows = rows.len();
    let [s0_lo, s0_hi, s1_lo, s1_hi, ..] = Layout::schedule_entry();
    for row_idx in 0..n_rows {
        let w_m15 = word_from_row_bits(&rows[(row_idx + n_rows - 15) % n_rows]);
        let w_m2 = word_from_row_bits(&rows[(row_idx + n_rows - 2) % n_rows]);
        write_word_limbs_row(&mut rows[row_idx], s0_lo, lower_sigma0(w_m15));
        write_word_limbs_row(&mut rows[row_idx], s1_lo, lower_sigma1(w_m2));
        debug_assert_eq!(s0_hi, s0_lo + 1);
        debug_assert_eq!(s1_hi, s1_lo + 1);
    }
}

fn fill_schedule_sigma_words_columns(cols: &mut [Vec<BaseField>], log_size: u32) {
    let n_rows = 1usize << log_size;
    let [s0_lo, s0_hi, s1_lo, s1_hi, ..] = Layout::schedule_entry();
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
        cols[s0_lo][storage_row] = m31(s0 & 0xffff);
        cols[s0_hi][storage_row] = m31(s0 >> 16);
        cols[s1_lo][storage_row] = m31(s1 & 0xffff);
        cols[s1_hi][storage_row] = m31(s1 >> 16);
    }
}

fn fill_round_function_limbs_rows(rows: &mut [Vec<BaseField>]) {
    let n_rows = rows.len();
    let round = Layout::round_col();
    for row_idx in 0..n_rows {
        let state_word = |back: usize, operand: usize| {
            round_state_word_from_row(&rows[(row_idx + n_rows - back) % n_rows], operand)
        };
        let words = [
            big_sigma0(state_word(0, 0)),
            big_sigma1(state_word(0, 1)),
            ch(state_word(0, 1), state_word(1, 1), state_word(2, 1)),
            maj(state_word(0, 0), state_word(1, 0), state_word(2, 0)),
        ];
        for (index, word) in words.into_iter().enumerate() {
            write_word_limbs_row(&mut rows[row_idx], round[2 * index], word);
        }
    }
}

fn fill_round_function_limbs_columns(cols: &mut [Vec<BaseField>], log_size: u32) {
    let n_rows = 1usize << log_size;
    let round = Layout::round_col();
    for storage_row in 0..n_rows {
        let coset_index =
            circle_domain_index_to_coset_index(bit_reverse_index(storage_row, log_size), log_size);
        let state_word = |back: usize, operand: usize| {
            let target_coset = (coset_index + n_rows - back) % n_rows;
            let target_storage = bit_reverse_index(
                coset_index_to_circle_domain_index(target_coset, log_size),
                log_size,
            );
            (0..WORD_BIT_COLS).fold(0u32, |word, bit| {
                word | (cols[Layout::round_operand_bit(operand, bit)][target_storage].0 << bit)
            })
        };
        let words = [
            big_sigma0(state_word(0, 0)),
            big_sigma1(state_word(0, 1)),
            ch(state_word(0, 1), state_word(1, 1), state_word(2, 1)),
            maj(state_word(0, 0), state_word(1, 0), state_word(2, 0)),
        ];
        for (index, word) in words.into_iter().enumerate() {
            cols[round[2 * index]][storage_row] = m31(word & 0xffff);
            cols[round[2 * index + 1]][storage_row] = m31(word >> 16);
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

fn round_state_word_from_row(row: &[BaseField], operand: usize) -> u32 {
    (0..WORD_BIT_COLS).fold(0u32, |word, bit| {
        word | (row[Layout::round_operand_bit(operand, bit)].0 << bit)
    })
}

fn write_padding_row_values(row: &mut [BaseField], p: &PaddingRowWitness) {
    row[Layout::COL_IS_MARKER_BLOCK] = m31(p.is_marker_block);
    row[Layout::COL_IS_LENGTH_BLOCK] = m31(p.is_length_block);
    for (j, &v) in p.is_marker_word.iter().enumerate() {
        row[Layout::is_marker_word(j)] = m31(v);
    }
    for (b, &v) in p.marker_byte_sel.iter().enumerate() {
        row[Layout::marker_byte_sel(b)] = m31(v);
    }
    for (b, &v) in p.marker_word_byte.iter().enumerate() {
        row[Layout::marker_word_byte(b)] = m31(v);
    }
    row[Layout::COL_BIT_LENGTH_W14_LO] = m31(p.bit_length_w14_lo);
    row[Layout::COL_BIT_LENGTH_W14_HI] = m31(p.bit_length_w14_hi);
    row[Layout::COL_BIT_LENGTH_W15_LO] = m31(p.bit_length_w15_lo);
    row[Layout::COL_BIT_LENGTH_W15_HI] = m31(p.bit_length_w15_hi);
}

/// Return the minimum `log_size` for `n_blocks`.
///
/// The trace size is the smallest power of two greater than
/// `67 * n_blocks`. This rule adds at least one padding row for the
/// `is_msg_last` gate. The result is also at least `LOG_MIN`.
pub fn min_log_size(n_blocks: usize) -> u32 {
    const LOG_MIN: u32 = 4; // SIMD lane count is 16 → at least 16 rows.
    let rows = n_blocks.max(1) * ROWS_PER_BLOCK;
    // Strictly-greater power of two: 67·n real rows never fill the trace.
    let needed = (rows + 1).next_power_of_two().ilog2();
    needed.max(LOG_MIN)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::witness::{compute_packed_sha256_witness, compute_sha256_witness};
    use rand::{rngs::StdRng, SeedableRng};
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
        let packed = compute_packed_sha256_witness(&[msg]).unwrap();
        let trace = generate_trace(&packed, log_size);

        let last_real_block = witness.blocks.len() - 1;
        let slot = Layout::round_row_slot(last_real_block, N_ROUNDS - 1, log_size);
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
        let packed = compute_packed_sha256_witness(&[msg]).unwrap();
        let trace = generate_trace(&packed, log_size);
        let last_real_block = witness.blocks.len() - 1;
        let slot = Layout::round_row_slot(last_real_block, N_ROUNDS - 1, log_size);
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

    /// Enabler is 1 on exactly the `67 · n_blocks` real rows. The boundary
    /// flags live on their designated round rows only. The preprocessed
    /// first-row selector marks row 0.
    #[test]
    fn enabler_and_flags_are_correct() {
        let witness = compute_sha256_witness(&[0x11; 100]); // 2 blocks
        let n_blocks = witness.blocks.len();
        assert_eq!(n_blocks, 2);
        let log_size = min_log_size(n_blocks);
        let packed = compute_packed_sha256_witness(&[&[0x11; 100][..]]).unwrap();
        let trace = generate_trace(&packed, log_size);
        let n_rows = 1usize << log_size;

        let enabled: u32 = trace[Layout::COL_ENABLER]
            .iter()
            .take(n_rows)
            .map(|value| value.0)
            .sum();
        assert_eq!(enabled as usize, n_blocks * ROWS_PER_BLOCK);

        // msg_start: only at block zero's first seed row.
        for b in 0..n_blocks {
            let seed0 = Layout::seed_row_slot(b, 0, log_size);
            assert_eq!(
                trace[Layout::COL_MSG_START][seed0].0,
                u32::from(b == 0),
                "msg_start at block {b} seed zero"
            );
            for t in 0..N_ROUNDS {
                let slot = Layout::round_row_slot(b, t, log_size);
                assert_eq!(trace[Layout::COL_MSG_START][slot].0, 0);
                let expected_last = u32::from(b == n_blocks - 1 && t == N_ROUNDS - 1);
                assert_eq!(
                    trace[Layout::COL_IS_MSG_LAST][slot].0,
                    expected_last,
                    "is_msg_last at ({b}, {t})"
                );
            }
        }
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

    #[test]
    fn scalar_and_simd_writers_match_with_partial_decoy_block() {
        let messages: [&[u8]; 5] = [b"a", b"bc", b"def", b"ghij", b"klmno"];
        let packed = compute_packed_sha256_witness(&messages).unwrap();
        let log_size = 9;
        let n_rows = 1usize << log_size;
        let n_real_rows = packed.total_blocks() * ROWS_PER_BLOCK;
        assert_ne!((n_rows - n_real_rows) % ROWS_PER_BLOCK, 0);

        let mut rng = StdRng::seed_from_u64(0x5348_4131_3937);
        let decoys = decoy_witnesses_for_padding_with(n_real_rows, n_rows, &mut rng);
        let scalar = generate_trace_scalar(&packed, log_size, &decoys);
        let simd = rayon::ThreadPoolBuilder::new()
            .num_threads(2)
            .build()
            .unwrap()
            .install(|| {
                generate_trace_base_columns_with_decoys(&packed, log_size, &decoys)
                    .into_iter()
                    .map(BaseColumn::into_cpu_vec)
                    .collect::<Vec<_>>()
            });
        assert_eq!(simd, scalar);
    }

    #[test]
    fn padding_rows_are_fresh_sha_decoys_with_public_flags_zero() {
        let witness = compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let real_rows = witness.blocks.len() * ROWS_PER_BLOCK;
        let first_real_slot = Layout::round_row_slot(0, 0, log_size);
        let first_pad_slot = Layout::row_slot(real_rows, log_size);
        let first_pad_round_slot = Layout::row_slot(real_rows + STATE_SEED_ROWS, log_size);
        let pad_t15_slot = Layout::row_slot(real_rows + STATE_SEED_ROWS + 15, log_size);

        let packed = compute_packed_sha256_witness(&[b"abc"]).unwrap();
        let first = generate_trace(&packed, log_size);
        let second = generate_trace(&packed, log_size);

        assert_eq!(
            first[Layout::COL_W_LO][first_real_slot],
            second[Layout::COL_W_LO][first_real_slot],
            "active witness rows must remain deterministic"
        );
        assert_eq!(first[Layout::COL_ENABLER][first_pad_slot].0, 0);
        assert_eq!(first[Layout::COL_MSG_START][first_pad_slot].0, 0);
        assert_eq!(first[Layout::COL_IS_MSG_LAST][first_pad_slot].0, 0);

        for (col, column) in first
            .iter()
            .enumerate()
            .skip(Layout::COL_PADDING_START)
            .take(Layout::COL_PADDING_END - Layout::COL_PADDING_START)
        {
            assert_eq!(
                column[pad_t15_slot].0, 0,
                "disabled-row padding role col {col} must stay public-zero"
            );
        }

        let mut decoy_cols: Vec<_> = (Layout::COL_W_LO..Layout::COL_ROUND_END).collect();
        decoy_cols.extend((0..ROUND_BIT_OPERANDS).flat_map(|operand| {
            (0..WORD_BIT_COLS).map(move |bit| Layout::round_operand_bit(operand, bit))
        }));
        assert!(
            decoy_cols
                .iter()
                .any(|&col| first[col][first_pad_round_slot] != BaseField::from(0u32)),
            "padding arithmetic cells should no longer be all zero"
        );
        assert!(
            decoy_cols
                .iter()
                .any(|&col| first[col][first_pad_round_slot] != second[col][first_pad_round_slot]),
            "same-witness padding arithmetic cells should be fresh per trace"
        );
    }

    fn seeded_state_word(
        trace: &[Vec<BaseField>],
        block: usize,
        word: usize,
        log_size: u32,
    ) -> u32 {
        let lane = usize::from(word >= N_STATE_WORDS / 2);
        let position = word % (N_STATE_WORDS / 2);
        let slot = if position == 0 {
            Layout::round_row_slot(block, 0, log_size)
        } else {
            Layout::seed_row_slot(block, STATE_SEED_ROWS - position, log_size)
        };
        (0..WORD_BIT_COLS).fold(0u32, |value, bit| {
            value | (trace[Layout::round_operand_bit(lane, bit)][slot].0 << bit)
        })
    }

    /// The first message's four rolling seed positions equal the IV.
    #[test]
    fn h_in_of_first_message_block_is_iv() {
        use crate::constants::IV;
        let witness = compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let packed = compute_packed_sha256_witness(&[b"abc"]).unwrap();
        let trace = generate_trace(&packed, log_size);
        for (j, &iv) in IV.iter().enumerate() {
            assert_eq!(seeded_state_word(&trace, 0, j, log_size), iv, "h[{j}]");
        }
    }

    /// Block chaining: block b's rolling seed state equals block b−1's
    /// `h_out` at t = 63.
    #[test]
    fn block_chain_h_out_to_h_in_continuity() {
        let witness = compute_sha256_witness(&[0x22; 200]);
        assert!(witness.blocks.len() >= 2);
        let log_size = min_log_size(witness.blocks.len());
        let packed = compute_packed_sha256_witness(&[&[0x22; 200][..]]).unwrap();
        let trace = generate_trace(&packed, log_size);
        for b in 1..witness.blocks.len() {
            let prev = Layout::round_row_slot(b - 1, N_ROUNDS - 1, log_size);
            for j in 0..N_STATE_WORDS {
                let (out_lo, out_hi) = Layout::h_out_word(j);
                let input = seeded_state_word(&trace, b, j, log_size);
                let output = trace[out_lo][prev].0 | (trace[out_hi][prev].0 << 16);
                assert_eq!(input, output, "word j={j} b={b}");
            }
        }
    }

    /// Coset geometry: `(b, 0)` and `(b − 1, 63)` are four rows apart, so the
    /// AIR's offset `−4` from a `t = 0` row lands on the
    /// previous block's `t = 63` row.
    #[test]
    fn round_rows_are_coset_adjacent() {
        let log_size = 9;
        for b in 1..4usize {
            assert_eq!(
                b * ROWS_PER_BLOCK + STATE_SEED_ROWS - 4,
                (b - 1) * ROWS_PER_BLOCK + STATE_SEED_ROWS + (N_ROUNDS - 1),
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
            + 1 // msg_start
            + 2 * N_STATE_WORDS // final carries
            + 2 * N_STATE_WORDS // h_out
            + 1 // is_msg_last
            + DIGEST_BYTES
            + 2; // msg_id + msg_block
        assert_eq!(Layout::TOTAL_COLS, expected);
        assert_eq!(ROUND_COLS, 88);
        assert_eq!(SCHEDULE_ENTRY_COLS, 6);
        assert_eq!(PADDING_ROW_COLS, 30);
        assert_eq!(Layout::TOTAL_COLS, 197);
        assert_eq!(Layout::COL_PADDING_START, Layout::COL_FINAL_CARRIES_START);
    }

    /// Round family, schedule family, and boundary families round-trip a
    /// couple of spot cells through the trace.
    #[test]
    fn families_round_trip_through_trace() {
        let witness = compute_sha256_witness(&[0x33; 100]);
        let log_size = min_log_size(witness.blocks.len());
        let packed = compute_packed_sha256_witness(&[&[0x33; 100][..]]).unwrap();
        let trace = generate_trace(&packed, log_size);

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
                // Schedule family: σ0 output limb.
                let [s0_lo, s0_hi, ..] = Layout::schedule_entry();
                if t >= 16 {
                    assert_eq!(
                        trace[s0_lo][slot].0,
                        block.schedule_entries[t - 16].lower_sigma0.lo
                    );
                } else {
                    // Sigma words are defined on every row from W[t-15].
                    let n_rows = 1usize << log_size;
                    let natural = b * ROWS_PER_BLOCK + STATE_SEED_ROWS + t;
                    let w15_slot = Layout::row_slot((natural + n_rows - 15) % n_rows, log_size);
                    let w15 = trace[Layout::COL_W_LO][w15_slot].0
                        | (trace[Layout::COL_W_HI][w15_slot].0 << 16);
                    let expected = lower_sigma0(w15);
                    assert_eq!(trace[s0_lo][slot].0, expected & 0xffff);
                    assert_eq!(trace[s0_hi][slot].0, expected >> 16);
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
}
