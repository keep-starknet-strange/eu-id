//! Optional credential-field byte exposure for the SHA-256 preimage.
//!
//! This module supplies the producer side of the field binding.
//! The SHA-256 AIR exposes selected byte windows from signed preimage `C`.
//! A downstream predicate requires those bytes through LogUp.
//! The predicate then uses a signed attribute, not an independent witness.
//!
//! The mechanism reuses the 32 Boolean bit planes for each schedule word
//! `W[t]`. A field byte at offset `o` is in word `o / 4` at big-endian byte
//! `o % 4`. The AIR forms the byte from the corresponding eight `W` bits. It
//! checks that these bits are Boolean and that they reconstruct `W`. This
//! method needs no duplicate byte columns or range lookups.
//!
//! This module is **format-agnostic**. The caller supplies byte windows selected
//! by the credential layer. This type resolves them to the word/byte coordinates
//! the trace, constraints, and interaction iterate. The `field_id` tags are
//! opaque pass-throughs (see
//! [`air_core::relations::field_id`]).
//!
//! A field window can cross a SHA-256 block boundary. Absolute preimage offsets
//! resolve to `(block_idx, word_idx, byte_in_word)`, and the AIR checks every
//! byte against that coordinate.

use crate::constants::{BLOCK_BYTES, N_INPUT_WORDS, WORD_BYTES};

/// One preimage byte to yield across the field relation.
///
/// `(field_id, byte_index)` is the cross-module key the consumer pins. The value
/// is the byte read from the resolved `(word_idx, byte_in_word)` coordinate of
/// the SHA trace. Multiple yields with the same `field_id` and ascending
/// `byte_index` form a field's byte window.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldByteYield {
    /// Opaque field tag (see [`air_core::relations::field_id`]).
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

/// The set of preimage-field bytes a SHA-256 proof exposes.
///
/// An **empty** exposure means the provider is off. A single-block exposure
/// adds no trace columns: it uses the existing first-block selector. A
/// multi-block exposure adds one block-counter column and one selector per
/// distinct target block, then yields one tuple per [`FieldByteYield`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FieldExposure {
    yields: Vec<FieldByteYield>,
    target_blocks: Vec<usize>,
    /// Optional full padded-message byte stream. Unlike `yields`, this adds
    /// only 64 lookup sites (one per byte position in a SHA block), regardless
    /// of the message length. Every real block emits
    /// `(field_id, block_idx * 64 + byte_in_block, byte)`.
    padded_stream_field_id: Option<u32>,
}

impl FieldExposure {
    /// The provider-off exposure (no field columns, no yields).
    pub fn empty() -> Self {
        Self::default()
    }

    /// Enable a full padded-message stream under `field_id`.
    ///
    /// This is the efficient bridge for parsers that must consume the entire
    /// SHA preimage, including its padding. It composes with ordinary fixed
    /// windows and keeps the interaction width constant as messages grow.
    pub fn with_padded_stream(mut self, field_id: u32) -> Self {
        self.padded_stream_field_id = Some(field_id);
        self
    }

    /// Build an exposure from absolute preimage byte **windows**, each
    /// `(field_id, start_offset, len)`.
    ///
    /// Resolve each byte to `(block_idx, word_idx, byte_in_word)`.
    ///
    /// One field window can cross a 64-byte SHA block boundary. The AIR checks
    /// each byte against its block coordinate.
    ///
    /// # Panics
    ///
    /// If a window's end offset overflows `usize`.
    pub fn from_preimage_windows(windows: &[(u32, usize, usize)]) -> Self {
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
        let mut target_blocks: Vec<usize> = yields.iter().map(|y| y.block_idx).collect();
        target_blocks.sort_unstable();
        target_blocks.dedup();
        Self {
            yields,
            target_blocks,
            padded_stream_field_id: None,
        }
    }

    /// Whether the provider is off (no field columns, no yields).
    pub fn is_empty(&self) -> bool {
        self.yields.is_empty() && self.padded_stream_field_id.is_none()
    }

    /// The yields, in the fixed order the trace, constraints, and interaction
    /// emit them.
    pub fn yields(&self) -> &[FieldByteYield] {
        &self.yields
    }

    /// Number of cross-module yields (one LogUp lookup each when exposed).
    pub fn n_yields(&self) -> usize {
        self.yields.len() + usize::from(self.padded_stream_field_id.is_some()) * BLOCK_BYTES
    }

    /// Field id of the optional full padded-message stream.
    pub fn padded_stream_field_id(&self) -> Option<u32> {
        self.padded_stream_field_id
    }

    /// The distinct SHA block indices that contain at least one yielded field
    /// byte, sorted ascending. The SHA AIR uses this to allocate one fixed
    /// block selector per target block.
    pub fn target_blocks(&self) -> &[usize] {
        &self.target_blocks
    }

    /// Whether this exposure needs dynamic block-selection columns. Fixed
    /// windows wholly in block 0 reuse the existing first-block selector.
    pub fn needs_dynamic_block_columns(&self) -> bool {
        self.padded_stream_field_id.is_some() || self.yields.iter().any(|y| y.block_idx != 0)
    }

    /// Column slot of the optional block counter within the dynamic field tail.
    pub fn block_counter_column_slot(&self) -> Option<usize> {
        self.needs_dynamic_block_columns().then_some(0)
    }

    /// Column slot of the selector for `target_block`.
    ///
    /// Return `None` when the exposure has no dynamic block-selection columns.
    pub fn selector_column_slot(&self, target_block: usize) -> Option<usize> {
        self.needs_dynamic_block_columns().then(|| {
            1 + self
                .target_blocks
                .binary_search(&target_block)
                .expect("selector target is in target_blocks")
        })
    }

    /// Number of dynamic trace columns the exposure adds. Single-block
    /// exposure adds none. Multi-block exposure adds one block counter and one
    /// selector per distinct target block.
    pub fn n_columns(&self) -> usize {
        if self.needs_dynamic_block_columns() {
            1 + self.target_blocks.len()
        } else {
            0
        }
    }
}

/// Return the big-endian bytes of a SHA-256 word.
///
/// The word uses `(lo, hi)` 16-bit limbs.
/// Thus, `word = lo + 2¹⁶·hi`.
/// The byte order is `[hi.b1, hi.b0, lo.b1, lo.b0]`.
/// The digest and field byte views share this conversion.
pub fn word_be_bytes(lo: u32, hi: u32) -> [u32; WORD_BYTES] {
    use crate::types::LimbBytes;
    let lo = LimbBytes::from_u16(lo);
    let hi = LimbBytes::from_u16(hi);
    [hi.b1, hi.b0, lo.b1, lo.b0]
}

// A message word index is always within the 16 input words.
const _: () = assert!(N_INPUT_WORDS == 16);
// The exposure resolves coordinates with `constants::WORD_BYTES`. The native
// word helper uses `types::BYTES_PER_WORD`. They must agree.
const _: () = assert!(WORD_BYTES == crate::types::BYTES_PER_WORD);

#[cfg(test)]
mod tests {
    use super::*;
    use air_core::relations::field_id;

    /// Two sample windows at offsets 5..9 and 9..11. They resolve to message
    /// words `W[1]` and `W[2]` of block 0.
    fn sample_exposure() -> FieldExposure {
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
    }

    #[test]
    fn single_block_windows_need_no_auxiliary_columns() {
        let e = sample_exposure();
        assert_eq!(e.target_blocks(), vec![0]);
        assert_eq!(e.n_columns(), 0);
        assert!(!e.needs_dynamic_block_columns());
        assert_eq!(e.n_yields(), 6); // 4 DOB + 2 nationality
    }

    #[test]
    fn sample_windows_resolve_each_byte_coordinate() {
        let e = sample_exposure();
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
    fn word_be_bytes_is_big_endian() {
        // word = 0x0114 with lo = 0x0114, hi = 0 → bytes [00, 00, 01, 14].
        assert_eq!(word_be_bytes(0x0114, 0x0000), [0x00, 0x00, 0x01, 0x14]);
        // word = 0x01_07D7_03 packed as lo=0x07D7? Use an explicit split:
        // lo = 0xD703, hi = 0x0107 → bytes [0x01, 0x07, 0xD7, 0x03].
        assert_eq!(word_be_bytes(0xD703, 0x0107), [0x01, 0x07, 0xD7, 0x03]);
    }

    #[test]
    fn windows_resolve_absolute_offsets() {
        let e = FieldExposure::from_preimage_windows(&[
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
        assert!(e.needs_dynamic_block_columns());
        assert_eq!(e.target_blocks(), [0, 1, 2]);
        assert_eq!(e.n_columns(), 4);
        assert_eq!(e.block_counter_column_slot(), Some(0));
        assert_eq!(e.selector_column_slot(0), Some(1));
        assert_eq!(e.selector_column_slot(1), Some(2));
        assert_eq!(e.selector_column_slot(2), Some(3));
    }

    #[test]
    fn windows_allow_straddling_block_boundary() {
        let e = FieldExposure::from_preimage_windows(&[(field_id::DOB, BLOCK_BYTES - 2, 4)]);
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

    #[test]
    fn padded_stream_has_constant_width_and_block_counter() {
        let e = FieldExposure::empty().with_padded_stream(99);
        assert!(!e.is_empty());
        assert_eq!(e.padded_stream_field_id(), Some(99));
        assert_eq!(e.n_yields(), BLOCK_BYTES);
        assert!(e.needs_dynamic_block_columns());
        assert_eq!(e.n_columns(), 1);
        assert_eq!(e.block_counter_column_slot(), Some(0));
        assert!(e.target_blocks().is_empty());
    }

    #[test]
    fn padded_stream_composes_with_fixed_windows() {
        let e =
            FieldExposure::from_preimage_windows(&[(field_id::DOB, 5, 4)]).with_padded_stream(99);
        assert_eq!(e.n_yields(), BLOCK_BYTES + 4);
        assert_eq!(e.n_columns(), 2);
        assert_eq!(e.target_blocks(), [0]);
        assert_eq!(e.selector_column_slot(0), Some(1));
    }
}
