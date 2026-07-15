//! Optional credential-field byte exposure for the SHA-256 preimage.
//!
//! The producer half of the `CRED_FIELD ↔ PREDICATE_INPUT` binding: the SHA-256
//! AIR can expose chosen byte windows of the signed preimage `C` as a LogUp
//! provider, so a downstream predicate can *require* exactly those
//! bytes and thereby reason about the attribute that was actually signed — not a
//! free-floating witness.
//!
//! The mechanism reuses the byte-decomposition machinery the digest provider
//! introduced: the message words `W[0..15]` already live in the trace as
//! 16-bit `(lo, hi)` limbs; exposing a field is just decomposing the limbs of
//! the word(s) that cover it into bytes and yielding the byte windows the
//! predicates consume. A field byte at preimage offset `o` lives in message word
//! `o / 4`, big-endian byte `o % 4` (FIPS 180-4 §5.2.1) — recall a word's
//! big-endian bytes are `[hi.b1, hi.b0, lo.b1, lo.b0]`.
//!
//! Each exposed byte is range-checked to `[0, 256)` inside the AIR (one `Range8`
//! lookup), so every covered limb's two-byte split is unique and a yielded byte
//! is provably the signed preimage byte. The digest provider uses the same
//! direct byte pin; it is essential here because a field window can be
//! **sub-word** (its edge byte shares a limb with a non-exposed neighbour).
//!
//! This module is **format-agnostic**: it knows nothing about the eu-id
//! credential. The caller supplies the byte windows (the credential layer keys
//! them off `docs/credential-format.md`); this type resolves them to the
//! word/byte coordinates the trace, constraints, and interaction iterate. The
//! `field_id` tags are opaque pass-throughs (see
//! [`air_core::relations::field_id`]).
//!
//! ## Scope
//!
//! The legacy constructor keeps the original single-block POC behavior. The
//! multi-block constructor resolves absolute preimage offsets to a
//! `(block_idx, word_idx, byte_in_word)` coordinate. A semantic field window may
//! straddle a SHA-256 block boundary: each byte carries its own block coordinate
//! and is gated independently by the AIR.

use crate::constants::{BLOCK_BYTES, N_INPUT_WORDS, WORD_BYTES};

/// One credential byte to yield across the field relation.
///
/// `(field_id, byte_index)` is the cross-module key the consumer pins; the value
/// is the byte read from the resolved `(word_idx, byte_in_word)` coordinate of
/// the SHA trace. Multiple yields with the same `field_id` and ascending
/// `byte_index` form a field's byte window.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldByteYield {
    /// Opaque credential-field tag (see [`air_core::relations::field_id`]).
    pub field_id: u32,
    /// Position of this byte within its field's window (`0`-based).
    pub byte_index: u32,
    /// Index of the SHA-256 message block containing this byte.
    pub block_idx: usize,
    /// Index of the message word (`W[word_idx]`, `0..16`) covering this byte.
    pub word_idx: usize,
    /// Big-endian byte position within `W[word_idx]` (`0..4`).
    pub byte_in_word: usize,
}

/// The set of credential-field bytes a SHA-256 proof exposes.
///
/// An **empty** exposure means the provider is off — the proof commits no field
/// byte columns and yields nothing (a standalone SHA proof, or the combined
/// proof before the predicate consumers are wired). A non-empty exposure adds
/// `4 ×` (distinct words) byte columns to the trace and yields one tuple per
/// [`FieldByteYield`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FieldExposure {
    yields: Vec<FieldByteYield>,
    // Memoized sorted-distinct projections of `yields`. `yield_column_slot`
    // runs inside constraint evaluation (per packed row, per yield), so these
    // must not be recomputed per call — the old alloc+sort per lookup was
    // ~10% of single-core prove time.
    decomposed_words: Vec<usize>,
    target_blocks: Vec<usize>,
}

impl FieldExposure {
    /// The provider-off exposure (no field columns, no yields).
    pub fn empty() -> Self {
        Self::default()
    }

    /// Build an exposure from preimage byte **windows**, each `(field_id,
    /// start_offset, len)`. Resolves every byte in every window to its
    /// `(word_idx, byte_in_word)` coordinate and assigns `byte_index` `0..len`
    /// within the field.
    ///
    /// # Panics
    ///
    /// If any window byte falls outside the first SHA-256 block (offset
    /// `>= BLOCK_BYTES`); see the module-level scope note.
    pub fn from_preimage_windows(windows: &[(u32, usize, usize)]) -> Self {
        for &(_, start, len) in windows {
            if len == 0 {
                continue;
            }
            let end = start
                .checked_add(len - 1)
                .expect("field-exposure window end offset overflow");
            assert!(
                end < BLOCK_BYTES,
                "field-exposure offset {end} is past the first SHA-256 block; \
                 multi-block field exposure is out of scope",
            );
        }
        Self::from_preimage_windows_multi(windows)
    }

    /// Build an exposure from absolute preimage byte **windows**, each
    /// `(field_id, start_offset, len)`.
    ///
    /// Every yielded byte is resolved to `(block_idx, word_idx, byte_in_word)`.
    /// A single field window may live in block 0, 1, 2, ... and may straddle a
    /// 64-byte SHA block boundary; each byte's block coordinate is enforced
    /// independently.
    ///
    /// # Panics
    ///
    /// If a window's end offset overflows `usize`.
    pub fn from_preimage_windows_multi(windows: &[(u32, usize, usize)]) -> Self {
        let mut yields = Vec::new();
        for &(field_id, start, len) in windows {
            if len != 0 {
                start
                    .checked_add(len - 1)
                    .expect("field-exposure window end offset overflow");
            }
            for i in 0..len {
                let offset = start + i;
                let block_offset = offset % BLOCK_BYTES;
                yields.push(FieldByteYield {
                    field_id,
                    byte_index: i as u32,
                    block_idx: offset / BLOCK_BYTES,
                    word_idx: block_offset / WORD_BYTES,
                    byte_in_word: block_offset % WORD_BYTES,
                });
            }
        }
        let mut decomposed_words: Vec<usize> = yields.iter().map(|y| y.word_idx).collect();
        decomposed_words.sort_unstable();
        decomposed_words.dedup();
        let mut target_blocks: Vec<usize> = yields.iter().map(|y| y.block_idx).collect();
        target_blocks.sort_unstable();
        target_blocks.dedup();
        Self {
            yields,
            decomposed_words,
            target_blocks,
        }
    }

    /// Whether the provider is off (no field columns, no yields).
    pub fn is_empty(&self) -> bool {
        self.yields.is_empty()
    }

    /// The yields, in the fixed order the trace, constraints, and interaction
    /// emit them.
    pub fn yields(&self) -> &[FieldByteYield] {
        &self.yields
    }

    /// Number of cross-module yields (one LogUp lookup each when exposed).
    pub fn n_yields(&self) -> usize {
        self.yields.len()
    }

    /// The distinct message-word indices that must be byte-decomposed, sorted
    /// ascending. Each contributes `WORD_BYTES` byte columns; a yield's column
    /// is found by this word's position here plus its `byte_in_word`.
    pub fn decomposed_words(&self) -> &[usize] {
        &self.decomposed_words
    }

    /// The distinct SHA block indices that contain at least one yielded field
    /// byte, sorted ascending. The SHA AIR uses this to allocate one fixed
    /// block selector per target block.
    pub fn target_blocks(&self) -> &[usize] {
        &self.target_blocks
    }

    /// Number of trace byte columns in the exposure (`WORD_BYTES` per distinct
    /// decomposed word).
    pub fn n_byte_columns(&self) -> usize {
        self.decomposed_words().len() * WORD_BYTES
    }

    /// Whether this exposure needs the multi-block witness tail. The legacy
    /// block-0 path keeps its original shape: only byte columns, no block
    /// counter and no per-yield selectors.
    pub fn needs_block_witness(&self) -> bool {
        self.yields.iter().any(|y| y.block_idx != 0)
    }

    /// Column slot of the optional block counter within the dynamic field tail.
    pub fn block_counter_column_slot(&self) -> Option<usize> {
        self.needs_block_witness().then(|| self.n_byte_columns())
    }

    /// Column slot of the selector shared by every yield in `block_idx`, if
    /// the multi-block witness tail is enabled.
    pub fn selector_column_slot_for_block(&self, block_idx: usize) -> Option<usize> {
        self.needs_block_witness().then(|| {
            let block_slot = self
                .target_blocks
                .iter()
                .position(|&target| target == block_idx)
                .expect("selector block is present in target_blocks");
            self.n_byte_columns() + 1 + block_slot
        })
    }

    /// Column slot of the selector for `yield_idx`. Yields targeting the same
    /// SHA block deliberately return the same slot.
    pub fn selector_column_slot(&self, yield_idx: usize) -> Option<usize> {
        self.yields
            .get(yield_idx)
            .and_then(|yield_| self.selector_column_slot_for_block(yield_.block_idx))
    }

    /// Number of dynamic trace columns the exposure adds. Block-0 legacy
    /// exposure adds only byte columns; multi-block exposure adds byte columns,
    /// one block counter, and one selector per distinct target block.
    pub fn n_columns(&self) -> usize {
        self.n_byte_columns()
            + if self.needs_block_witness() {
                1 + self.target_blocks().len()
            } else {
                0
            }
    }

    /// The column slot (`0`-based among the exposure's byte columns) of a
    /// yield's byte: the position of its word in [`Self::decomposed_words`] times
    /// `WORD_BYTES`, plus its big-endian byte position. Used identically by the
    /// trace generator, the constraint reader, and the interaction combine so
    /// the three stay byte-for-byte aligned.
    pub fn yield_column_slot(&self, y: &FieldByteYield) -> usize {
        let word_slot = self
            .decomposed_words()
            .iter()
            .position(|&w| w == y.word_idx)
            .expect("a yield's word is always in decomposed_words");
        word_slot * WORD_BYTES + y.byte_in_word
    }
}

/// The big-endian bytes of a SHA-256 32-bit word held as `(lo, hi)` 16-bit
/// limbs: `word = lo + 2¹⁶·hi`, so the bytes are `[hi.b1, hi.b0, lo.b1, lo.b0]`
/// (`b1` the high byte of a limb). Shared by the digest byte view
/// (`crate::trace::h_out_digest_bytes`) and the field byte view so both
/// decompose words the same way.
pub fn word_be_bytes(lo: u32, hi: u32) -> [u32; WORD_BYTES] {
    use crate::types::LimbBytes;
    let lo = LimbBytes::from_u16(lo);
    let hi = LimbBytes::from_u16(hi);
    [hi.b1, hi.b0, lo.b1, lo.b0]
}

// A message word index is always within the 16 input words.
const _: () = assert!(N_INPUT_WORDS == 16);
// The trace generator writes field bytes with `types::BYTES_PER_WORD`; this
// module resolves coordinates with `constants::WORD_BYTES`. They must agree or
// the field columns would misalign between generator and reader.
const _: () = assert!(WORD_BYTES == crate::types::BYTES_PER_WORD);

#[cfg(test)]
mod tests {
    use super::*;
    use air_core::relations::field_id;

    /// The eu-id credential windows (`docs/credential-format.md`): DOB at
    /// offsets 5..9, nationality at 9..11. They resolve to message words
    /// `W[1]`/`W[2]` of block 0, whose limbs are pinned by the schedule-word
    /// bit recomposition constraints.
    fn credential_exposure() -> FieldExposure {
        FieldExposure::from_preimage_windows(&[
            (field_id::DOB, 5, 4),
            (field_id::NATIONALITY, 9, 2),
        ])
    }

    #[test]
    fn empty_exposure_is_off() {
        let e = FieldExposure::empty();
        assert!(e.is_empty());
        assert_eq!(e.n_columns(), 0);
        assert_eq!(e.n_byte_columns(), 0);
        assert_eq!(e.n_yields(), 0);
        assert!(e.decomposed_words().is_empty());
    }

    #[test]
    fn credential_windows_resolve_to_words_1_and_2() {
        let e = credential_exposure();
        assert_eq!(e.decomposed_words(), vec![1, 2]);
        assert_eq!(e.target_blocks(), vec![0]);
        // 2 distinct words × 4 bytes = 8 byte columns.
        assert_eq!(e.n_columns(), 8);
        assert_eq!(e.n_byte_columns(), 8);
        assert!(!e.needs_block_witness());
        assert_eq!(e.n_yields(), 6); // 4 DOB + 2 nationality
    }

    #[test]
    fn credential_windows_resolve_each_byte_coordinate() {
        let e = credential_exposure();
        let y = e.yields();
        // DOB: C[5]=W1.b1, C[6]=W1.b2, C[7]=W1.b3, C[8]=W2.b0.
        assert_eq!(
            (
                y[0].field_id,
                y[0].byte_index,
                y[0].word_idx,
                y[0].byte_in_word
            ),
            (field_id::DOB, 0, 1, 1)
        );
        assert_eq!((y[1].word_idx, y[1].byte_in_word), (1, 2));
        assert_eq!((y[2].word_idx, y[2].byte_in_word), (1, 3));
        assert_eq!((y[3].word_idx, y[3].byte_in_word), (2, 0));
        // Nationality: C[9]=W2.b1, C[10]=W2.b2.
        assert_eq!(
            (
                y[4].field_id,
                y[4].byte_index,
                y[4].word_idx,
                y[4].byte_in_word
            ),
            (field_id::NATIONALITY, 0, 2, 1)
        );
        assert_eq!(
            (
                y[5].field_id,
                y[5].byte_index,
                y[5].word_idx,
                y[5].byte_in_word
            ),
            (field_id::NATIONALITY, 1, 2, 2)
        );
    }

    #[test]
    fn column_slots_pack_by_word_then_byte() {
        let e = credential_exposure();
        let y = e.yields();
        // Word 1 occupies slots 0..4, word 2 occupies slots 4..8.
        assert_eq!(e.yield_column_slot(&y[0]), 1); // W1.b1
        assert_eq!(e.yield_column_slot(&y[1]), 2); // W1.b2
        assert_eq!(e.yield_column_slot(&y[2]), 3); // W1.b3
        assert_eq!(e.yield_column_slot(&y[3]), 4); // W2.b0
        assert_eq!(e.yield_column_slot(&y[4]), 5); // W2.b1
        assert_eq!(e.yield_column_slot(&y[5]), 6); // W2.b2
    }

    #[test]
    fn word_be_bytes_is_big_endian() {
        // word = 0x0114 with lo = 0x0114, hi = 0 → bytes [00, 00, 01, 14].
        assert_eq!(word_be_bytes(0x0114, 0x0000), [0x00, 0x00, 0x01, 0x14]);
        // word = 0x01_07D7_03 packed as lo=0x07D7? Use an explicit split:
        // lo = 0xD703, hi = 0x0107 → bytes [0x01, 0x07, 0xD7, 0x03].
        assert_eq!(word_be_bytes(0xD703, 0x0107), [0x01, 0x07, 0xD7, 0x03]);
    }

    #[test]
    #[should_panic(expected = "past the first SHA-256 block")]
    fn rejects_offsets_past_the_first_block() {
        let _ = FieldExposure::from_preimage_windows(&[(field_id::DOB, 62, 4)]);
    }

    #[test]
    fn multi_block_windows_resolve_absolute_offsets() {
        let e = FieldExposure::from_preimage_windows_multi(&[
            (field_id::DOB, 5, 4),
            (field_id::NATIONALITY, BLOCK_BYTES + 8, 2),
            (99, 2 * BLOCK_BYTES + 12, 3),
        ]);
        let y = e.yields();
        assert_eq!(
            (y[0].block_idx, y[0].word_idx, y[0].byte_in_word),
            (0, 1, 1)
        );
        assert_eq!(
            (y[3].block_idx, y[3].word_idx, y[3].byte_in_word),
            (0, 2, 0)
        );
        assert_eq!(
            (y[4].block_idx, y[4].word_idx, y[4].byte_in_word),
            (1, 2, 0)
        );
        assert_eq!(
            (y[5].block_idx, y[5].word_idx, y[5].byte_in_word),
            (1, 2, 1)
        );
        assert_eq!(
            (y[6].block_idx, y[6].word_idx, y[6].byte_in_word),
            (2, 3, 0)
        );
        assert!(e.needs_block_witness());
        assert_eq!(e.block_counter_column_slot(), Some(e.n_byte_columns()));
        assert_eq!(e.selector_column_slot(0), Some(e.n_byte_columns() + 1));
        assert_eq!(
            e.selector_column_slot(4),
            e.selector_column_slot(5),
            "same-block yields share one selector",
        );
    }

    #[test]
    fn multi_block_windows_allow_straddling_window() {
        let e = FieldExposure::from_preimage_windows_multi(&[(field_id::DOB, BLOCK_BYTES - 2, 4)]);
        let y = e.yields();
        assert_eq!(
            y.iter().map(|b| b.block_idx).collect::<Vec<_>>(),
            vec![0, 0, 1, 1]
        );
        assert_eq!(
            y.iter().map(|b| b.byte_index).collect::<Vec<_>>(),
            vec![0, 1, 2, 3]
        );
    }

    /// The byte table has exactly the intended `[0, 256)` domain.
    #[test]
    fn byte_range_table_pins_to_a_byte() {
        const TABLE: u32 = 1 << 8;
        for b in [0u32, 1, 127, 200, 255] {
            assert!(b < TABLE, "in-range b={b} must fit the byte table");
        }
        for b in [256u32, 257, 1000, 0xFFFF] {
            assert!(b >= TABLE, "out-of-range b={b} must miss the byte table");
        }
    }
}
