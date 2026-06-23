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
//! Each exposed byte is range-checked to `[0, 256)` inside the AIR (two `Range16`
//! lookups, see [`BYTE_RANGE_CHECK_OFFSET`]), so every covered limb's two-byte
//! split is unique and a yielded byte is provably the signed preimage byte. The
//! digest provider can defer its byte range-check to the consumer because it
//! exposes whole words; a field window can be **sub-word** (its edge byte shares
//! a limb with a non-exposed neighbour), so this provider pins the bytes itself.
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
//! Exposed offsets must lie in the **first** SHA-256 block (offset `< 64`): the
//! yield is gated to `is_first_block`, since the credential's fields are at fixed
//! offsets from the start of the preimage. The MVP credential is a single block
//! (11 bytes), so this is always satisfied; multi-block field exposure is out of
//! scope (it would return with the deferred mdoc work).

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
        let mut yields = Vec::new();
        for &(field_id, start, len) in windows {
            for i in 0..len {
                let offset = start + i;
                assert!(
                    offset < BLOCK_BYTES,
                    "field-exposure offset {offset} is past the first SHA-256 block; \
                     multi-block field exposure is out of scope",
                );
                yields.push(FieldByteYield {
                    field_id,
                    byte_index: i as u32,
                    word_idx: offset / WORD_BYTES,
                    byte_in_word: offset % WORD_BYTES,
                });
            }
        }
        Self { yields }
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
    pub fn decomposed_words(&self) -> Vec<usize> {
        let mut words: Vec<usize> = self.yields.iter().map(|y| y.word_idx).collect();
        words.sort_unstable();
        words.dedup();
        words
    }

    /// Number of trace byte columns the exposure adds (`WORD_BYTES` per distinct
    /// decomposed word).
    pub fn n_columns(&self) -> usize {
        self.decomposed_words().len() * WORD_BYTES
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

/// Offset for the two-lookup byte range-check that pins an exposed field byte to
/// `[0, 256)`.
///
/// This AIR has no `[0, 2⁸)` range table — only the carry tables (`[0, 2)`,
/// `[0, 4)`, `[0, 5)`) and the 16-bit `Range16` (`[0, 2¹⁶)`). A byte `b` is
/// pinned to `[0, 256)` by **two** `Range16` lookups: on `b` and on `b +
/// BYTE_RANGE_CHECK_OFFSET`. The first forces `b ∈ [0, 2¹⁶)`; the second forces
/// `b ≤ 2¹⁶ − 1 − OFFSET = 255` (any `b ∈ [256, 2¹⁶)` makes `b + OFFSET ≥ 2¹⁶`,
/// off-table — and since `b + OFFSET < p` there is no field wrap to rescue it).
/// Together: `b ∈ [0, 256)`. Reuses the existing `Range16` producer — no new
/// table, trace column, or component. Why it's needed: a 16-bit limb's split
/// `256·b_hi + b_lo` is unique only when *both* bytes are in `[0, 256)`, so an
/// edge byte of a sub-word window cannot be forged by absorbing slack into a
/// non-exposed limb partner.
pub const BYTE_RANGE_CHECK_OFFSET: u32 = (1 << 16) - (1 << 8);

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
    /// `W[1]`/`W[2]` of block 0 — exactly the words the σ-input split-and-pack
    /// already 16-bit-pins.
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
        assert_eq!(e.n_yields(), 0);
        assert!(e.decomposed_words().is_empty());
    }

    #[test]
    fn credential_windows_resolve_to_words_1_and_2() {
        let e = credential_exposure();
        assert_eq!(e.decomposed_words(), vec![1, 2]);
        // 2 distinct words × 4 bytes = 8 byte columns.
        assert_eq!(e.n_columns(), 8);
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

    /// The two-`Range16` byte range-check: for every in-range byte both `b` and
    /// `b + OFFSET` land inside the `[0, 2¹⁶)` table, and for every out-of-range
    /// value `b + OFFSET` overflows the table (so the lookup cannot balance).
    /// This is the algebra that makes each exposed byte provably a byte.
    #[test]
    fn byte_range_offset_pins_to_a_byte() {
        const TABLE: u32 = 1 << 16;
        assert_eq!(BYTE_RANGE_CHECK_OFFSET, TABLE - (1 << 8));
        for b in [0u32, 1, 127, 200, 255] {
            assert!(b < TABLE, "b={b} in the table");
            assert!(
                b + BYTE_RANGE_CHECK_OFFSET < TABLE,
                "b={b}+OFFSET in the table"
            );
        }
        for b in [256u32, 257, 1000, 0xFFFF] {
            assert!(
                b + BYTE_RANGE_CHECK_OFFSET >= TABLE,
                "out-of-range b={b} must push b+OFFSET off the Range16 table",
            );
        }
    }
}
