//! Full padded-stream exposure for the SHA-256 preimage.
//!
//! The SHA-256 AIR can expose each byte of one complete padded message through
//! the shared field relation. A parser can require the same byte sequence.
//! This binds the parsed input to the message that SHA-256 hashes.

use crate::constants::{BLOCK_BYTES, WORD_BYTES};

/// Number of field-relation sites on each enabled block's `t = 15` row.
pub const FULL_PADDED_STREAM_SITES_PER_ROW: usize = BLOCK_BYTES;

/// M31's modulus. Byte indices and field IDs must be canonical M31 values.
const M31_MODULUS: usize = (1usize << 31) - 1;

/// The optional complete padded-stream provider.
///
/// The active mode adds one block-counter column. It emits 64 field-relation
/// tuples on each enabled block's `t = 15` row.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FieldExposure {
    full_padded_stream: Option<(u32, usize)>,
}

impl FieldExposure {
    /// Disable the field provider.
    pub fn empty() -> Self {
        Self::default()
    }

    /// Expose each byte of one complete padded SHA-256 stream.
    ///
    /// The byte index is `block_counter * 64 + byte_in_block`. The AIR derives
    /// each byte from the constrained message-word bits.
    ///
    /// # Panics
    ///
    /// Panics if `padded_len` is zero, is not a whole number of SHA-256 blocks,
    /// or cannot use canonical M31 byte indices. It also panics if `field_id`
    /// is not a canonical M31 value.
    pub fn from_full_padded_stream(field_id: u32, padded_len: usize) -> Self {
        assert!(
            padded_len != 0 && padded_len.is_multiple_of(BLOCK_BYTES),
            "full padded SHA stream must contain whole non-empty blocks"
        );
        assert!(
            padded_len <= M31_MODULUS,
            "full padded SHA stream byte indices must fit canonically in M31"
        );
        assert!(
            (field_id as usize) < M31_MODULUS,
            "full padded SHA stream field_id must fit canonically in M31"
        );
        Self {
            full_padded_stream: Some((field_id, padded_len)),
        }
    }

    /// Return `true` when the field provider is disabled.
    pub fn is_empty(&self) -> bool {
        self.full_padded_stream.is_none()
    }

    /// Return `(field_id, padded_len)` for an active provider.
    pub fn full_padded_stream(&self) -> Option<(u32, usize)> {
        self.full_padded_stream
    }

    /// Return the fixed number of relation sites on each row.
    pub fn n_yields(&self) -> usize {
        usize::from(!self.is_empty()) * FULL_PADDED_STREAM_SITES_PER_ROW
    }

    /// Return the number of dynamic trace columns.
    pub fn n_columns(&self) -> usize {
        usize::from(!self.is_empty())
    }

    /// Return the block-counter slot in the dynamic trace tail.
    pub fn block_counter_column_slot(&self) -> Option<usize> {
        (!self.is_empty()).then_some(0)
    }
}

/// Return a SHA-256 word as four big-endian bytes.
///
/// The trace stores the word as `(lo, hi)` 16-bit limbs.
pub fn word_be_bytes(lo: u32, hi: u32) -> [u32; WORD_BYTES] {
    use crate::types::LimbBytes;
    let lo = LimbBytes::from_u16(lo);
    let hi = LimbBytes::from_u16(hi);
    [hi.b1, hi.b0, lo.b1, lo.b0]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn full_padded_stream_has_one_counter_and_fixed_relation_width() {
        for padded_len in [BLOCK_BYTES, 2 * BLOCK_BYTES, 65 * BLOCK_BYTES] {
            let exposure = FieldExposure::from_full_padded_stream(77, padded_len);
            assert_eq!(exposure.full_padded_stream(), Some((77, padded_len)));
            assert!(!exposure.is_empty());
            assert_eq!(exposure.n_columns(), 1);
            assert_eq!(exposure.block_counter_column_slot(), Some(0));
            assert_eq!(exposure.n_yields(), FULL_PADDED_STREAM_SITES_PER_ROW);
        }
    }

    #[test]
    fn empty_exposure_is_off() {
        let exposure = FieldExposure::empty();
        assert!(exposure.is_empty());
        assert_eq!(exposure.n_columns(), 0);
        assert_eq!(exposure.n_yields(), 0);
        assert_eq!(exposure.block_counter_column_slot(), None);
    }

    #[test]
    #[should_panic(expected = "whole non-empty blocks")]
    fn full_padded_stream_rejects_empty_length() {
        let _ = FieldExposure::from_full_padded_stream(77, 0);
    }

    #[test]
    #[should_panic(expected = "whole non-empty blocks")]
    fn full_padded_stream_rejects_partial_block() {
        let _ = FieldExposure::from_full_padded_stream(77, BLOCK_BYTES + 1);
    }

    #[test]
    #[should_panic(expected = "byte indices must fit canonically in M31")]
    fn full_padded_stream_rejects_wrapping_byte_indices() {
        let _ = FieldExposure::from_full_padded_stream(77, M31_MODULUS + 1);
    }

    #[test]
    #[should_panic(expected = "field_id must fit canonically in M31")]
    fn full_padded_stream_rejects_noncanonical_field_id() {
        let _ = FieldExposure::from_full_padded_stream(M31_MODULUS as u32, BLOCK_BYTES);
    }

    #[test]
    fn word_bytes_are_big_endian() {
        assert_eq!(word_be_bytes(0x0114, 0), [0, 0, 1, 0x14]);
        assert_eq!(word_be_bytes(0xD703, 0x0107), [1, 7, 0xD7, 3]);
    }
}
