//! Convert a [`Sha256Witness`] into M31 trace columns.
//!
//! Each block uses three state-seed rows followed by 64 round rows. The seed
//! rows place `h3/h7`, `h2/h6`, and `h1/h5` in the rolling `a/e` bit lanes.
//! Round zero places `h0/h4` in the same lanes. Later rounds read the other
//! working-state words at offsets `-1`, `-2`, and `-3`.
//!
//! A mask offset of `-k` reads the row from `k` rounds earlier. The AIR uses
//! these offsets for the round state, message schedule, and block hash chain.
//! [`Layout`] defines the column order.
//!
use stwo::core::fields::m31::{BaseField, M31};
use stwo::core::utils::{
    bit_reverse_index, circle_domain_index_to_coset_index, coset_index_to_circle_domain_index,
};
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES, N_LANES};

use crate::constants::{DIGEST_BYTES, N_ROUNDS, N_STATE_WORDS};
use crate::field_exposure::FieldExposure;
use crate::native::{big_sigma0, big_sigma1, ch, lower_sigma0, lower_sigma1, maj};
use crate::types::{AddCarries, PaddingRowWitness, Sha256Witness, WordLimbs};

use crate::constants::WORD_BYTES as BYTES_PER_WORD;
use rand::{rngs::OsRng, RngCore};

/// Words per 512-bit block: 16.
pub const WORDS_PER_BLOCK: usize = 16;

/// State rows before round zero. They seed the rolling `a/e` bit lanes.
pub const STATE_SEED_ROWS: usize = 3;

/// Rows one block occupies: three state seeds and one row per round.
pub const ROWS_PER_BLOCK: usize = STATE_SEED_ROWS + N_ROUNDS;

/// Bits per SHA-256 word, committed LSB-first.
pub const WORD_BIT_COLS: usize = 32;
/// Rolling round-state bit columns. Only `a` and `e` are committed. The AIR
/// reads `b/c/d` and `f/g/h` from the preceding three rows.
/// Operand order: `[a, e]`.
pub const ROUND_BIT_OPERANDS: usize = 2;
pub const ROUND_OPERAND_BIT_COLS: usize = ROUND_BIT_OPERANDS * WORD_BIT_COLS;
/// Columns of the round family: 8 word-results × 2 limbs + 4 carry pairs
/// × 2 ends = 24, then committed operand bits.
pub const ROUND_COLS: usize = 8 * 2 + 4 * 2 + ROUND_OPERAND_BIT_COLS;
/// Columns of the schedule family (live for `t ≥ 16`): `σ0`, `σ1`, carries.
/// `σ0`/`σ1` are written and constrained on every row (ungated recomposition
/// from the already-committed `w_bits`), not only `t ≥ 16` — the schedule
/// recurrence add that consumes them stays gated by `is_sched`.
pub const SCHEDULE_ENTRY_COLS: usize = 6;
/// Columns for the per-block padding-role witness. They are active on each
/// block's `t = 15` row and follow the order in [`write_padding_row`]:
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
///     + 4 bit-length limbs = 30` cells per block. `is_length_only_block`,
///     `is_marker_only_block`, and `marker_word_post_strict_15` used to be
///     committed here; they are now inlined AIR-side expressions of
///     `is_marker_block`/`is_length_block` (degree 2), or (for
///     `is_marker_only_block`) deleted outright as dead — see
///     `constraints.rs` (P.C)/(P.C') and [`crate::types::PaddingRowWitness`].
pub const PADDING_ROW_COLS: usize = 2 + WORDS_PER_BLOCK + BYTES_PER_WORD + BYTES_PER_WORD + 4;

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
    /// Round family. It is active on round rows.
    pub const COL_ROUND_START: usize = Self::COL_W_BITS_END;
    pub const COL_ROUND_END: usize = Self::COL_ROUND_START + ROUND_COLS;
    /// Schedule family — live on rows with `t ≥ 16`.
    pub const COL_SCHED_ENTRY_START: usize = Self::COL_ROUND_END;
    pub const COL_SCHED_ENTRY_END: usize = Self::COL_SCHED_ENTRY_START + SCHEDULE_ENTRY_COLS;
    /// `t = 63` family. **ALIASED** with the per-block padding-role region
    /// (below): the first `PADDING_ROW_COLS` (30) of these 32
    /// finalization-carry/`h_out` cells double as the padding-role witness
    /// on each block's `t = 15` row. Only `h_out` word `N_STATE_WORDS − 1`
    /// (the last 2 cells) is never aliased — see [`Self::COL_PADDING_START`].
    /// Sound because `r15`/`r63` (the preprocessed round selectors) are
    /// structurally disjoint: `ROWS_PER_BLOCK = 67` is prime, and a natural
    /// row's position mod 67 is either `18` (round 15) or `66` (round 63),
    /// never both — so no row ever needs both meanings from one cell.
    pub const COL_FINAL_CARRIES_START: usize = Self::COL_SCHED_ENTRY_END;
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
    ///
    /// **Never aliased.** Unlike the padding-role region, `is_last_block`
    /// keeps its own column and its ungated defining equality — a
    /// malicious prover cannot forge it at a `t = 15` row, which is what
    /// keeps the digest-substitution attack (planting `is_last_block = 1`
    /// on a padding-controlled row so the digest relation yields
    /// attacker-chosen bytes) closed by construction.
    pub const COL_IS_LAST_BLOCK: usize = Self::COL_H_OUT_END;

    /// Per-block padding-role region, **ALIASED** onto the first
    /// `PADDING_ROW_COLS` (30) of the 32 `COL_FINAL_CARRIES_START..
    /// COL_H_OUT_END` cells (see the field-level docs there). Live on the
    /// `t = 15` row; the aliased final family is live on the `t = 63` row.
    /// The remaining 2 cells (`h_out` word `N_STATE_WORDS − 1`) are never
    /// reused for padding — see [`crate::constraints::Sha256Eval`]'s merged
    /// zero-pin vs. the plain finalization-only pin.
    pub const COL_PADDING_START: usize = Self::COL_FINAL_CARRIES_START;
    pub const COL_IS_MARKER_BLOCK: usize = Self::COL_PADDING_START;
    pub const COL_IS_LENGTH_BLOCK: usize = Self::COL_PADDING_START + 1;
    pub const COL_IS_MARKER_WORD_START: usize = Self::COL_PADDING_START + 2;
    pub const COL_IS_MARKER_WORD_END: usize = Self::COL_IS_MARKER_WORD_START + WORDS_PER_BLOCK;
    pub const COL_MARKER_BYTE_SEL_START: usize = Self::COL_IS_MARKER_WORD_END;
    pub const COL_MARKER_BYTE_SEL_END: usize = Self::COL_MARKER_BYTE_SEL_START + BYTES_PER_WORD;
    pub const COL_MARKER_WORD_BYTE_START: usize = Self::COL_MARKER_BYTE_SEL_END;
    pub const COL_MARKER_WORD_BYTE_END: usize = Self::COL_MARKER_WORD_BYTE_START + BYTES_PER_WORD;
    pub const COL_BIT_LENGTH_W14_LO: usize = Self::COL_MARKER_WORD_BYTE_END;
    pub const COL_BIT_LENGTH_W14_HI: usize = Self::COL_MARKER_WORD_BYTE_END + 1;
    pub const COL_BIT_LENGTH_W15_LO: usize = Self::COL_MARKER_WORD_BYTE_END + 2;
    pub const COL_BIT_LENGTH_W15_HI: usize = Self::COL_MARKER_WORD_BYTE_END + 3;
    pub const COL_PADDING_END: usize = Self::COL_PADDING_START + PADDING_ROW_COLS;

    /// Number of base trace columns. The padding-role region is aliased
    /// (not additive), so this ends at `is_last_block`, not at
    /// `COL_PADDING_END`.
    pub const TOTAL_COLS: usize = Self::COL_IS_LAST_BLOCK + 1;

    /// First column of the optional padded-stream block counter.
    pub const COL_FIELD_BYTES_START: usize = Self::TOTAL_COLS;

    /// Return a column in the optional field tail.
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

    /// `(lo, hi)` slot for the row's schedule word `W[t]`.
    #[inline]
    pub const fn schedule_word() -> (usize, usize) {
        (Self::COL_W_LO, Self::COL_W_HI)
    }

    /// Columns of the schedule family's leading cells, in order:
    /// `σ0_lo, σ0_hi, σ1_lo, σ1_hi, carry_lo, carry_hi`. `σ0`/`σ1` are
    /// written and ungated-constrained on every row (pure functions of the
    /// already-committed `w_bits`); `carry_lo`/`carry_hi` are only live —
    /// and only gated-constrained — on rows with `t ≥ 16`.
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

    /// Storage slot of natural row `row_idx`, for a
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

/// The 32 digest bytes of a block's `h_out`, in the fixed big-endian order
/// that the digest bridge and `crate::relations::Sha256Digest` use. For state
/// word `j`,
/// `word_j.to_be_bytes()` = `[hi.b1, hi.b0, lo.b1, lo.b0]` (recall
/// `word_j = lo + 2¹⁶·hi`, so the high limb supplies the two most-significant
/// big-endian bytes). The digest bridge trace and interaction trace use this
/// function. The two bytes of each limb satisfy `limb = 256 * b1 + b0`.
pub fn h_out_digest_bytes(h_out: &[WordLimbs; N_STATE_WORDS]) -> [u32; DIGEST_BYTES] {
    let mut out = [0u32; DIGEST_BYTES];
    for (j, limb) in h_out.iter().enumerate() {
        let bytes = crate::field_exposure::word_be_bytes(limb.lo, limb.hi);
        out[4 * j..4 * j + 4].copy_from_slice(&bytes);
    }
    out
}

/// Materialise a trace with no field provider.
///
/// Returns `Vec<Vec<BaseField>>`, one inner `Vec` per column. Length of
/// every inner `Vec` equals `1 << log_size`, padded with zeros past the
/// number of real rows.
///
/// Choose `log_size` so that `(1 << log_size) > 67 · witness.blocks.len()`
/// (use [`min_log_size`]). The function panics otherwise.
pub fn generate_trace(witness: &Sha256Witness, log_size: u32) -> Vec<Vec<BaseField>> {
    generate_trace_with_fields(witness, log_size, &FieldExposure::empty())
}

/// Materialise a trace with an optional padded-stream block counter.
pub fn generate_trace_with_fields(
    witness: &Sha256Witness,
    log_size: u32,
    field_exposure: &FieldExposure,
) -> Vec<Vec<BaseField>> {
    generate_trace_with_fields_packed(witness, log_size, field_exposure)
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
    let n_rows = 1usize << log_size;
    let n_real_rows = witness.blocks.len() * ROWS_PER_BLOCK;
    let decoys = decoy_witnesses_for_padding(n_real_rows, n_rows);
    generate_trace_base_columns_with_decoys(witness, log_size, field_exposure, &decoys)
}

fn generate_trace_base_columns_with_decoys(
    witness: &Sha256Witness,
    log_size: u32,
    field_exposure: &FieldExposure,
    decoys: &[Sha256Witness],
) -> Vec<BaseColumn> {
    if log_size < LOG_N_LANES || rayon::current_num_threads() == 1 {
        return generate_trace_with_fields_scalar_fallback_with_decoys(
            witness,
            log_size,
            field_exposure,
            decoys,
        )
        .into_iter()
        .map(|values| values.into_iter().collect())
        .collect();
    }

    use rayon::prelude::*;

    let n_rows = 1usize << log_size;
    let n_real_rows = witness.blocks.len() * ROWS_PER_BLOCK;
    assert!(
        n_real_rows <= n_rows,
        "trace too small: {} blocks × {ROWS_PER_BLOCK} rows > {} rows",
        witness.blocks.len(),
        n_rows
    );
    // Decoy indexing below (`(row_idx - n_real_rows) % ROWS_PER_BLOCK`)
    // assumes the real-row prefix ends on a block boundary — the aliased
    // padding/finalization region relies on this to line up `block_row`
    // with the right selector (`r15`/`r63`) on every padding row.
    assert!(n_real_rows.is_multiple_of(ROWS_PER_BLOCK));

    let total_cols = Layout::total_cols_with_fields(field_exposure.n_columns());
    let last_block_idx = witness.blocks.len().saturating_sub(1);
    let has_padding = n_real_rows < n_rows;
    let mut row_values = (0..n_rows)
        .into_par_iter()
        .map(|row_idx| {
            if row_idx >= n_real_rows {
                return disabled_decoy_row_values(
                    &decoys[(row_idx - n_real_rows) / ROWS_PER_BLOCK],
                    (row_idx - n_real_rows) % ROWS_PER_BLOCK,
                    field_exposure,
                    total_cols,
                );
            }
            let block_idx = row_idx / ROWS_PER_BLOCK;
            let block_row = row_idx % ROWS_PER_BLOCK;
            let mut values = vec![BaseField::from(0u32); total_cols];
            if block_row < STATE_SEED_ROWS {
                write_seed_row_values(&mut values, witness, block_idx, block_row, field_exposure);
            } else {
                let t = block_row - STATE_SEED_ROWS;
                write_round_row_values(
                    &mut values,
                    witness,
                    block_idx,
                    t,
                    block_idx == last_block_idx && has_padding,
                    field_exposure,
                );
            }
            values
        })
        .collect::<Vec<_>>();
    fill_schedule_sigma_words_rows(&mut row_values);
    fill_round_function_limbs_rows(&mut row_values);

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
                        row_values[coset_index][column]
                    }))
                })
                .collect();
            BaseColumn::from_simd(data)
        })
        .collect()
}

fn generate_trace_with_fields_scalar_fallback_with_decoys(
    witness: &Sha256Witness,
    log_size: u32,
    field_exposure: &FieldExposure,
    decoys: &[Sha256Witness],
) -> Vec<Vec<BaseField>> {
    let n_rows = 1usize << log_size;
    let n_real_rows = witness.blocks.len() * ROWS_PER_BLOCK;
    assert!(
        n_real_rows <= n_rows,
        "trace too small: {} blocks × {ROWS_PER_BLOCK} rows > {} rows",
        witness.blocks.len(),
        n_rows
    );
    // See the matching assert in `generate_trace_base_columns_with_decoys`.
    assert!(n_real_rows.is_multiple_of(ROWS_PER_BLOCK));

    let total_cols = Layout::total_cols_with_fields(field_exposure.n_columns());
    let mut cols = vec![vec![BaseField::from(0u32); n_rows]; total_cols];
    let last_block_idx = witness.blocks.len().saturating_sub(1);
    let has_padding = n_real_rows < n_rows;
    for block_idx in 0..witness.blocks.len() {
        for seed in 0..STATE_SEED_ROWS {
            let slot = Layout::seed_row_slot(block_idx, seed, log_size);
            write_seed_row(&mut cols, slot, witness, block_idx, seed, field_exposure);
        }
        for t in 0..N_ROUNDS {
            let slot = Layout::round_row_slot(block_idx, t, log_size);
            write_round_row(
                &mut cols,
                slot,
                witness,
                block_idx,
                t,
                block_idx == last_block_idx && has_padding,
                field_exposure,
            );
        }
    }
    for row_idx in n_real_rows..n_rows {
        let slot = Layout::row_slot(row_idx, log_size);
        let values = disabled_decoy_row_values(
            &decoys[(row_idx - n_real_rows) / ROWS_PER_BLOCK],
            (row_idx - n_real_rows) % ROWS_PER_BLOCK,
            field_exposure,
            total_cols,
        );
        for (column, value) in cols.iter_mut().zip(values) {
            column[slot] = value;
        }
    }
    fill_schedule_sigma_words_columns(&mut cols, log_size);
    fill_round_function_limbs_columns(&mut cols, log_size);
    cols
}

fn decoy_witnesses_for_padding(n_real_rows: usize, n_rows: usize) -> Vec<Sha256Witness> {
    decoy_witnesses_for_padding_with(n_real_rows, n_rows, &mut OsRng)
}

/// Decoy-block generator with an injectable byte source. Production paths pass
/// [`OsRng`] for fresh per-proof masking; the scalar/packed writer-equivalence
/// test passes a seeded RNG so both writers consume the *same* decoy witnesses
/// (otherwise the boundary sigma-bit columns, which recompute from padding
/// neighbours, would differ across two independent generations by design).
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

fn disabled_decoy_row_values(
    decoy: &Sha256Witness,
    block_row: usize,
    field_exposure: &FieldExposure,
    total_cols: usize,
) -> Vec<BaseField> {
    let mut values = vec![BaseField::from(0u32); total_cols];
    if block_row < STATE_SEED_ROWS {
        write_seed_row_values(&mut values, decoy, 0, block_row, field_exposure);
    } else {
        write_round_row_values(
            &mut values,
            decoy,
            0,
            block_row - STATE_SEED_ROWS,
            false,
            field_exposure,
        );
    }
    values[Layout::COL_ENABLER] = BaseField::from(0u32);
    values[Layout::COL_IS_LAST_BLOCK] = BaseField::from(0u32);
    // The padding-role region is ALIASED onto the finalization
    // carries/`h_out` cells (see `Layout::COL_PADDING_START`). At the
    // decoy's `t = 15` row those cells hold whatever `write_round_row_values`
    // left there for the padding family — zero them so the disabled-row
    // invariant (padding flags are public-zero off an active block) holds.
    // At the decoy's `t = 63` row (`block_row == STATE_SEED_ROWS + N_ROUNDS
    // − 1`), the SAME physical cells instead hold the decoy's own
    // finalization carries/`h_out` — real, honestly-computed values that
    // must NOT be zeroed, since they are the Class-D digest-relation blind
    // (a decoy's `h_out` masks the honest proof's final digest in the
    // logup sum). Every other `block_row` never writes these cells at all
    // (they stay zero-initialized), so the conditional is a no-op there.
    if block_row != STATE_SEED_ROWS + N_ROUNDS - 1 {
        values[Layout::COL_PADDING_START..Layout::COL_PADDING_END].fill(BaseField::from(0u32));
    }
    if field_exposure.n_columns() != 0 {
        values[Layout::COL_FIELD_BYTES_START..].fill(BaseField::from(0u32));
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
    is_last_block: bool,
    field_exposure: &FieldExposure,
) {
    let mut values = vec![BaseField::from(0u32); cols.len()];
    write_round_row_values(
        &mut values,
        witness,
        block_idx,
        t,
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
    is_last_block: bool,
    field_exposure: &FieldExposure,
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

    // Schedule family: the mod-add carries are only meaningful for t ≥ 16
    // (the schedule recurrence add is gated by `is_sched` in the AIR). `σ0`
    // /`σ1` (s0/s1) are filled for every row in a later unconditional pass
    // (`fill_schedule_sigma_words_rows`/`_columns`) since their recomposition
    // constraint is now ungated.
    if t >= 16 {
        let entry = &block.schedule_entries[t - 16];
        let [_s0_lo, _s0_hi, _s1_lo, _s1_hi, c_lo, c_hi] = Layout::schedule_entry();
        row[c_lo] = m31(entry.carries.lo);
        row[c_hi] = m31(entry.carries.hi);
    }

    // t = 63 family: finalization and block output.
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
    }

    // t = 15 family: padding-role witness.
    if t == 15 {
        write_padding_row_values(row, &block.padding_row);
    }

    // The block counter is present on every row when the field provider is on.
    if t < WORDS_PER_BLOCK {
        if let Some(slot) = field_exposure.block_counter_column_slot() {
            row[Layout::field_byte_col(slot)] = BaseField::from(block_idx as u32);
        }
    }
}

fn write_seed_row(
    cols: &mut [Vec<BaseField>],
    row: usize,
    witness: &Sha256Witness,
    block_idx: usize,
    seed: usize,
    field_exposure: &FieldExposure,
) {
    let mut values = vec![BaseField::from(0u32); cols.len()];
    write_seed_row_values(&mut values, witness, block_idx, seed, field_exposure);
    for (column, value) in cols.iter_mut().zip(values) {
        column[row] = value;
    }
}

fn write_seed_row_values(
    row: &mut [BaseField],
    witness: &Sha256Witness,
    block_idx: usize,
    seed: usize,
    _field_exposure: &FieldExposure,
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
        let sigma0 = big_sigma0(state_word(0, 0));
        let sigma1 = big_sigma1(state_word(0, 1));
        let choose = ch(state_word(0, 1), state_word(1, 1), state_word(2, 1));
        let majority = maj(state_word(0, 0), state_word(1, 0), state_word(2, 0));
        write_word_limbs_row(&mut rows[row_idx], round[0], sigma0);
        write_word_limbs_row(&mut rows[row_idx], round[2], sigma1);
        write_word_limbs_row(&mut rows[row_idx], round[4], choose);
        write_word_limbs_row(&mut rows[row_idx], round[6], majority);
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
            let mut word = 0u32;
            for bit in 0..WORD_BIT_COLS {
                word |= cols[Layout::round_operand_bit(operand, bit)][target_storage].0 << bit;
            }
            word
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
    let mut word = 0u32;
    for bit in 0..WORD_BIT_COLS {
        word |= row[Layout::round_operand_bit(operand, bit)].0 << bit;
    }
    word
}

fn write_word_limbs_row(row: &mut [BaseField], base: usize, word: u32) {
    row[base] = m31(word & 0xffff);
    row[base + 1] = m31(word >> 16);
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

/// Required `log_size` for `n_blocks` blocks (smallest power of two
/// `> 67 · n_blocks` — **strictly** greater, so the trace always ends with
/// at least one padding row and the `is_last_block` gate
/// `enabler · is_round_63 · (1 − enabler_next)` can fire — and at least
/// `LOG_MIN` so SIMD backends are happy).
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
    use crate::witness::compute_sha256_witness;
    use sha2::{Digest as Sha2Digest, Sha256};

    #[test]
    fn full_padded_stream_trace_adds_only_the_block_counter() {
        let witness = compute_sha256_witness(&[0x33; 100]);
        assert_eq!(witness.blocks.len(), 2);
        let log_size = min_log_size(witness.blocks.len());
        let exposure = FieldExposure::from_full_padded_stream(77, witness.padding.padded.len());
        let trace = generate_trace_with_fields(&witness, log_size, &exposure);

        assert_eq!(trace.len(), Layout::TOTAL_COLS + 1);
        assert_eq!(exposure.block_counter_column_slot(), Some(0));
        let counter_col = Layout::field_byte_col(0);
        for block_idx in 0..witness.blocks.len() {
            for t in 0..N_ROUNDS {
                let slot = Layout::round_row_slot(block_idx, t, log_size);
                assert_eq!(
                    trace[counter_col][slot].0,
                    if t < WORDS_PER_BLOCK {
                        block_idx as u32
                    } else {
                        0
                    },
                    "counter at block {block_idx}, round {t}",
                );
            }
        }
    }

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

    /// Enabler is one on exactly the 67 rows of each block. The final flag is
    /// one only on the last block's final round.
    #[test]
    fn enabler_and_flags_are_correct() {
        let witness = compute_sha256_witness(&[0x11; 100]); // 2 blocks
        let n_blocks = witness.blocks.len();
        assert_eq!(n_blocks, 2);
        let log_size = min_log_size(n_blocks);
        let trace = generate_trace(&witness, log_size);
        let n_rows = 1usize << log_size;

        let enabled: u32 = trace[Layout::COL_ENABLER]
            .iter()
            .take(n_rows)
            .map(|value| value.0)
            .sum();
        assert_eq!(enabled as usize, n_blocks * ROWS_PER_BLOCK);

        for b in 0..n_blocks {
            for t in 0..N_ROUNDS {
                let slot = Layout::round_row_slot(b, t, log_size);
                let expected_last = u32::from(b == n_blocks - 1 && t == N_ROUNDS - 1);
                assert_eq!(
                    trace[Layout::COL_IS_LAST_BLOCK][slot].0,
                    expected_last,
                    "is_last_block at ({b}, {t})"
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
    fn padding_rows_are_fresh_sha_decoys_with_public_flags_zero() {
        let witness = compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let real_rows = witness.blocks.len() * ROWS_PER_BLOCK;
        let first_real_slot = Layout::round_row_slot(0, 0, log_size);
        let first_pad_slot = Layout::row_slot(real_rows, log_size);
        let first_pad_round_slot = Layout::row_slot(real_rows + STATE_SEED_ROWS, log_size);
        let pad_t15_slot = Layout::row_slot(real_rows + STATE_SEED_ROWS + 15, log_size);

        let first = generate_trace(&witness, log_size);
        let second = generate_trace(&witness, log_size);

        assert_eq!(
            first[Layout::COL_W_LO][first_real_slot],
            second[Layout::COL_W_LO][first_real_slot],
            "active witness rows must remain deterministic"
        );
        assert_eq!(first[Layout::COL_ENABLER][first_pad_slot].0, 0);
        assert_eq!(first[Layout::COL_IS_LAST_BLOCK][first_pad_slot].0, 0);

        for (col, column) in first
            .iter()
            .enumerate()
            .take(Layout::COL_PADDING_END)
            .skip(Layout::COL_PADDING_START)
        {
            assert_eq!(
                column[pad_t15_slot].0, 0,
                "disabled-row padding role col {col} must stay public-zero"
            );
        }

        let mut decoy_cols: Vec<_> = (0..ROUND_BIT_OPERANDS)
            .flat_map(|operand| {
                (0..WORD_BIT_COLS).map(move |bit| Layout::round_operand_bit(operand, bit))
            })
            .collect();
        decoy_cols.extend([Layout::COL_W_LO, Layout::COL_W_HI]);
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
        let lane = usize::from(word >= 4);
        let position = word % 4;
        let slot = if position == 0 {
            Layout::round_row_slot(block, 0, log_size)
        } else {
            Layout::seed_row_slot(block, STATE_SEED_ROWS - position, log_size)
        };
        (0..WORD_BIT_COLS).fold(0u32, |value, bit| {
            value | (trace[Layout::round_operand_bit(lane, bit)][slot].0 << bit)
        })
    }

    /// The four rolling seed positions of the first block are the IV.
    #[test]
    fn h_in_of_first_block_is_iv() {
        use crate::constants::IV;
        let witness = compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);
        for (j, &iv) in IV.iter().enumerate() {
            assert_eq!(seeded_state_word(&trace, 0, j, log_size), iv, "h[{j}]");
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
            let prev = Layout::round_row_slot(b - 1, N_ROUNDS - 1, log_size);
            for j in 0..N_STATE_WORDS {
                let (out_lo, out_hi) = Layout::h_out_word(j);
                let state = seeded_state_word(&trace, b, j, log_size);
                let output = trace[out_lo][prev].0 | (trace[out_hi][prev].0 << 16);
                assert_eq!(state, output, "word j={j} b={b}");
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
    ///
    /// Wave C (2026-08-05, C10): the 30-cell padding-role region is now
    /// ALIASED onto 30 of the 32 finalization-carry/`h_out` cells, not
    /// additive — `TOTAL_COLS` ends at `is_last_block` (192 → 162).
    /// `PADDING_ROW_COLS` still pins the alias width (it must stay ≤ 32,
    /// the aliasable region's size, and equal to 30 exactly since 2 cells —
    /// `h_out` word `N_STATE_WORDS − 1` — are deliberately left unaliased).
    #[test]
    fn layout_total_cols_matches_expected_breakdown() {
        let expected = 1 // enabler
            + 2 // W
            + WORD_BIT_COLS
            + ROUND_COLS
            + SCHEDULE_ENTRY_COLS
            + 2 * N_STATE_WORDS // final carries
            + 2 * N_STATE_WORDS // h_out
            + 1; // is_last_block
        assert_eq!(Layout::TOTAL_COLS, expected);
        assert_eq!(ROUND_COLS, 88);
        assert_eq!(SCHEDULE_ENTRY_COLS, 6);
        assert_eq!(Layout::TOTAL_COLS, 162);
        assert_eq!(PADDING_ROW_COLS, 30);
        let aliasable_region_cols = 2 * (2 * N_STATE_WORDS); // final carries + h_out
        assert!(
            PADDING_ROW_COLS <= aliasable_region_cols,
            "alias-width must fit the 32-cell final_carries/h_out region"
        );
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
                // a bit 0.
                assert_eq!(
                    trace[Layout::round_operand_bit(0, 0)][slot].0,
                    block.rounds[t].state_in[0].to_u32() & 1
                );
                // Schedule family: σ0 output limb.
                if t >= 16 {
                    let [s0_lo, ..] = Layout::schedule_entry();
                    assert_eq!(
                        trace[s0_lo][slot].0,
                        block.schedule_entries[t - 16].lower_sigma0.lo
                    );
                } else {
                    // σ0/σ1 are now ungated: live and equal to
                    // lower_sigma0(W[t-15]) on every row, not only t ≥ 16.
                    let n_rows = 1usize << log_size;
                    let natural = b * ROWS_PER_BLOCK + STATE_SEED_ROWS + t;
                    let w15_slot = Layout::row_slot((natural + n_rows - 15) % n_rows, log_size);
                    let w15 = trace[Layout::COL_W_LO][w15_slot].0
                        | (trace[Layout::COL_W_HI][w15_slot].0 << 16);
                    let [s0_lo, s0_hi, ..] = Layout::schedule_entry();
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

    #[test]
    fn packed_trace_writer_matches_scalar_writer_with_stream_exposure() {
        use rand::{rngs::StdRng, SeedableRng};
        let witness = compute_sha256_witness(&[0x44; 180]);
        let log_size = min_log_size(witness.blocks.len());
        let exposure = FieldExposure::from_full_padded_stream(7, witness.padding.padded.len());
        // Both writers must consume the *same* decoy padding, else the boundary
        // sigma-bit columns (recomputed from padding neighbours) diverge by
        // design. Seed one decoy set and feed it to both.
        let n_rows = 1usize << log_size;
        let n_real_rows = witness.blocks.len() * ROWS_PER_BLOCK;
        let decoys = decoy_witnesses_for_padding_with(
            n_real_rows,
            n_rows,
            &mut StdRng::seed_from_u64(0xC1A55D),
        );
        let scalar = generate_trace_with_fields_scalar_fallback_with_decoys(
            &witness, log_size, &exposure, &decoys,
        );
        let packed =
            generate_trace_base_columns_with_decoys(&witness, log_size, &exposure, &decoys)
                .into_iter()
                .map(BaseColumn::into_cpu_vec)
                .collect::<Vec<_>>();
        let real_rows = witness.blocks.len() * ROWS_PER_BLOCK;
        let n_rows = 1usize << log_size;
        let total_cols = Layout::total_cols_with_fields(exposure.n_columns());

        for row_idx in 0..real_rows {
            let slot = Layout::row_slot(row_idx, log_size);
            for col in 0..total_cols {
                assert_eq!(
                    scalar[col][slot], packed[col][slot],
                    "active row {row_idx} col {col}"
                );
            }
        }

        let mut public_pad_cols = vec![Layout::COL_ENABLER, Layout::COL_IS_LAST_BLOCK];
        public_pad_cols.extend(Layout::COL_PADDING_START..Layout::COL_PADDING_END);
        public_pad_cols.extend(Layout::COL_FIELD_BYTES_START..total_cols);
        for row_idx in real_rows..n_rows {
            let slot = Layout::row_slot(row_idx, log_size);
            for &col in &public_pad_cols {
                assert_eq!(
                    scalar[col][slot], packed[col][slot],
                    "pad row {row_idx} col {col}"
                );
            }
        }
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
        let exposure = FieldExposure::from_full_padded_stream(7, witness.padding.padded.len());
        let n_rows = 1usize << log_size;
        let n_real_rows = witness.blocks.len() * ROWS_PER_BLOCK;
        let decoys = decoy_witnesses_for_padding(n_real_rows, n_rows);
        let scalar = best_of(5, || {
            std::hint::black_box(generate_trace_with_fields_scalar_fallback_with_decoys(
                &witness, log_size, &exposure, &decoys,
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
