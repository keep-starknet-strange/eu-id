//! Core types: the 32-bit-word → M31-limb representation, working state,
//! block bytes, and the witness records the trace generator consumes.
//!
//! The trace represents a SHA-256 word `w` as two 16-bit limbs `(lo, hi)`,
//! where `w = lo + 2¹⁶ * hi`. This split keeps each modulo-2³² addition linear
//! over M31. Bit planes constrain the SHA Boolean functions.

use crate::constants::{
    BLOCK_BYTES, DIGEST_BYTES, N_INPUT_WORDS, N_ROUNDS, N_STATE_WORDS, WORD_BYTES,
};

/// Width of a single limb. Two of these make a 32-bit word.
pub const LIMB_BITS: u32 = 16;

/// `2¹⁶ = 65 536`. A limb is in `[0, LIMB_BASE)`.
pub const LIMB_BASE: u32 = 1 << LIMB_BITS;

/// Maximum legal limb value, `2¹⁶ − 1`.
pub const LIMB_MAX: u32 = LIMB_BASE - 1;

/// One word as `(lo, hi)` limbs. `lo, hi ∈ [0, 2¹⁶)` in every native witness.
/// The AIR reconstructs the words from their constrained bit planes.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct WordLimbs {
    pub lo: u32,
    pub hi: u32,
}

impl WordLimbs {
    /// Decompose a 32-bit word into two 16-bit limbs.
    #[inline]
    pub const fn from_u32(w: u32) -> Self {
        Self {
            lo: w & LIMB_MAX,
            hi: (w >> LIMB_BITS) & LIMB_MAX,
        }
    }

    /// Recompose the 32-bit word `lo + 2¹⁶ · hi`. Wraps if `hi > 2¹⁶ − 1`.
    #[inline]
    pub const fn to_u32(self) -> u32 {
        self.lo | (self.hi << LIMB_BITS)
    }

    /// True iff both limbs are in `[0, 2¹⁶)`.
    #[inline]
    #[cfg(test)]
    pub(crate) const fn is_canonical(self) -> bool {
        self.lo <= LIMB_MAX && self.hi <= LIMB_MAX
    }
}

/// The hash state `H = (H₀, H₁, …, H₇)` carried across blocks.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct HashState(pub [u32; N_STATE_WORDS]);

/// A 512-bit padded block, as 16 big-endian 32-bit words.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Block(pub [u32; N_INPUT_WORDS]);

impl Block {
    /// Parse a 64-byte block as 16 big-endian `u32` words (FIPS 180-4 §5.2.1).
    pub fn from_bytes(bytes: &[u8; BLOCK_BYTES]) -> Self {
        let mut words = [0u32; N_INPUT_WORDS];
        for (i, w) in words.iter_mut().enumerate() {
            let start = i * WORD_BYTES;
            *w = u32::from_be_bytes(bytes[start..start + WORD_BYTES].try_into().unwrap());
        }
        Self(words)
    }
}

/// The 64-word message schedule `W[0..63]` for one block.
#[derive(Copy, Clone, Debug)]
pub struct Schedule(pub [u32; N_ROUNDS]);

impl Default for Schedule {
    fn default() -> Self {
        Self([0u32; N_ROUNDS])
    }
}

/// 256-bit digest as 8 big-endian `u32` words, equivalently 32 bytes.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct Digest(pub [u8; DIGEST_BYTES]);

impl Digest {
    /// Serialize `(H₀..H₇)` as 32 big-endian bytes.
    pub fn from_state(h: &HashState) -> Self {
        let mut out = [0u8; DIGEST_BYTES];
        for (i, &word) in h.0.iter().enumerate() {
            out[i * WORD_BYTES..(i + 1) * WORD_BYTES].copy_from_slice(&word.to_be_bytes());
        }
        Self(out)
    }
}

/// Witness for the padding step: the message we hash, its bit-length, and the
/// constrained padded byte stream that the AIR consumes block-by-block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PaddingWitness {
    /// The padded message — a multiple of `BLOCK_BYTES` bytes (FIPS §5.1.1).
    pub padded: Vec<u8>,
}

/// The witness values for one compression round.
///
/// Limb fields use `u32`. The trace converts them to M31 before commitment.
/// This representation also permits tests that do not import field types.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RoundWitness {
    /// Working state at the *start* of the round, as `(lo, hi)` limbs for
    /// each of the eight working-state words.
    pub state_in: [WordLimbs; N_STATE_WORDS],
    /// `Σ0(a)` and `Σ1(e)` results as `(lo, hi)` limbs.
    pub sigma0: WordLimbs,
    pub sigma1: WordLimbs,
    /// `Ch(e, f, g)` and `Maj(a, b, c)` results as `(lo, hi)` limbs.
    pub ch: WordLimbs,
    pub maj: WordLimbs,
    /// `T1 = h + Σ1 + Ch + K[t] + W[t]` (mod 2³²).
    pub t1: WordLimbs,
    /// `T2 = Σ0 + Maj` (mod 2³²).
    pub t2: WordLimbs,
    /// Updated `a` and `e` after this round.
    pub a_new: WordLimbs,
    pub e_new: WordLimbs,
    /// Limb carries for each of the four mod-2³² adds (`t1`, `t2`, `a_new`,
    /// `e_new`). For `t1` the addends are `h + Σ1 + Ch + K + W = 5` words so
    /// the low-limb sum is `< 5·2¹⁶`, the low carry is `< 5`. The high-limb
    /// sum likewise. Carries are range-checked in the AIR.
    pub t1_carries: AddCarries,
    pub t2_carries: AddCarries,
    pub a_new_carries: AddCarries,
    pub e_new_carries: AddCarries,
}

/// Carry chain for one modulo-2³² limb addition.
///
/// `lo` carries into the high-limb sum. `hi` carries out of that sum, and
/// modulo 2³² discards it. For `k` addends, each carry is at most `k - 1`.
/// The AIR checks these bounds.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct AddCarries {
    pub lo: u32,
    pub hi: u32,
}

/// Witness for one message-schedule entry `W[t]`, for `t ∈ [16, 64)`.
///
/// `W[t] = σ1(W[t−2]) + W[t−7] + σ0(W[t−15]) + W[t−16]` (mod 2³²).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ScheduleEntryWitness {
    pub lower_sigma0: WordLimbs,
    pub lower_sigma1: WordLimbs,
    /// The four-word `+` carries.
    pub carries: AddCarries,
}

/// Padding data for one block.
///
/// The flags identify message, marker-only, length-only, and combined
/// marker-and-length blocks. One-hot vectors locate the `0x80` marker. Four
/// 16-bit values contain the FIPS length field from `W[14]` and `W[15]`.
///
/// Padding auxiliary expressions are derived in the AIR from these primary
/// fields rather than committed as separate columns.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct PaddingRowWitness {
    /// 1 iff this block contains the `0x80` padding marker.
    pub is_marker_block: u32,
    /// 1 iff this block is the final block (carries the bit-length in its
    /// last 8 bytes / `W[14]` / `W[15]`).
    pub is_length_block: u32,
    /// One-hot indicator: `is_marker_word[j] == 1` iff word index `j` holds
    /// the `0x80` byte. All-zero on non-marker rows. Sums to
    /// `is_marker_block`.
    pub is_marker_word: [u32; N_INPUT_WORDS],
    /// One-hot indicator: `marker_byte_sel[b] == 1` iff byte position `b`
    /// within the marker word holds `0x80`. BE order — `b = 0` is the MSB
    /// of `W[k]`. All-zero on non-marker rows. Sums to `is_marker_block`.
    pub marker_byte_sel: [u32; WORD_BYTES],
    /// Big-endian byte decomposition of the marker word, in MSB-first
    /// order. All-zero on non-marker rows. The constraint layer binds
    /// these to `W[marker_word_idx]` via the `is_marker_word` selector.
    pub marker_word_byte: [u32; WORD_BYTES],
    /// Lo 16-bit limb of `W[14]` of the length block — the low half of
    /// the 32-bit high word of the bit-length. 0 on non-length-block rows.
    pub bit_length_w14_lo: u32,
    /// Hi 16-bit limb of `W[14]` of the length block.
    pub bit_length_w14_hi: u32,
    /// Lo 16-bit limb of `W[15]` of the length block — the low 16 bits of
    /// the 32-bit low word of the bit-length.
    pub bit_length_w15_lo: u32,
    /// Hi 16-bit limb of `W[15]` of the length block.
    pub bit_length_w15_hi: u32,
}

impl PaddingRowWitness {
    /// Build the padding-row witness for block `block_idx`.
    ///
    /// `padded` is the FIPS-padded message. `message_byte_length` is the raw
    /// message length. `n_blocks` is the total padded block count.
    ///
    /// The marker offset equals `message_byte_length` as specified in FIPS
    /// 180-4 section 5.1.1. Division by `BLOCK_BYTES` gives its block.
    /// Division by `WORD_BYTES` gives its word and byte positions.
    ///
    /// The final block contains the length. The marker and length share one
    /// block when `message_byte_length % 64` is below 56. Otherwise, the
    /// length uses a separate block.
    pub fn for_block(
        block_idx: usize,
        padded: &[u8],
        message_byte_length: u64,
        n_blocks: usize,
    ) -> Self {
        assert!(n_blocks >= 1, "padded message has at least one block");
        assert_eq!(
            padded.len(),
            n_blocks * crate::constants::BLOCK_BYTES,
            "padded length must be n_blocks · BLOCK_BYTES",
        );
        let block_bytes = crate::constants::BLOCK_BYTES;
        let marker_byte_offset = message_byte_length as usize;
        let marker_block_idx = marker_byte_offset / block_bytes;
        let length_block_idx = n_blocks - 1;

        let is_marker_block = u32::from(block_idx == marker_block_idx);
        let is_length_block = u32::from(block_idx == length_block_idx);
        let mut is_marker_word = [0u32; N_INPUT_WORDS];
        let mut marker_byte_sel = [0u32; WORD_BYTES];
        let mut marker_word_byte = [0u32; WORD_BYTES];

        if is_marker_block == 1 {
            let off = marker_byte_offset % block_bytes;
            let word_idx = off / WORD_BYTES;
            let byte_in_word = off % WORD_BYTES;
            is_marker_word[word_idx] = 1;
            marker_byte_sel[byte_in_word] = 1;
            // Marker word bytes in BE order (byte 0 = MSB). Bytes before
            // the marker come from the tail of the message. The marker
            // byte is 0x80. Bytes after it are 0 (per FIPS §5.1.1).
            let word_start = block_idx * block_bytes + word_idx * WORD_BYTES;
            for p in 0..WORD_BYTES {
                marker_word_byte[p] = padded[word_start + p] as u32;
            }
        }

        let (bit_length_w14_lo, bit_length_w14_hi, bit_length_w15_lo, bit_length_w15_hi) =
            if is_length_block == 1 {
                let bit_length = message_byte_length.wrapping_mul(8);
                let w14 = (bit_length >> 32) as u32;
                let w15 = bit_length as u32;
                (
                    w14 & 0xFFFF,
                    (w14 >> LIMB_BITS) & 0xFFFF,
                    w15 & 0xFFFF,
                    (w15 >> LIMB_BITS) & 0xFFFF,
                )
            } else {
                (0, 0, 0, 0)
            };

        Self {
            is_marker_block,
            is_length_block,
            is_marker_word,
            marker_byte_sel,
            marker_word_byte,
            bit_length_w14_lo,
            bit_length_w14_hi,
            bit_length_w15_lo,
            bit_length_w15_hi,
        }
    }
}

/// Witness for one block: schedule, 64-round state evolution, IV-in/out.
///
/// `schedule` is a `Vec` rather than `[WordLimbs; N_ROUNDS]`. The length is
/// always `N_ROUNDS`. The trace generator asserts this on construction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockWitness {
    /// `H⁽ᵗ⁾` at block entry. Block 0 has `H⁽⁰⁾ = IV` (the AIR constrains it).
    pub h_in: [WordLimbs; N_STATE_WORDS],
    /// `H⁽ᵗ⁺¹⁾` at block exit. Block `t+1` reads this as `h_in`.
    pub h_out: [WordLimbs; N_STATE_WORDS],
    /// `W[0..63]`. Length is always `N_ROUNDS`.
    pub schedule: Vec<WordLimbs>,
    /// `W[16..64]` derivation witnesses, in order.
    pub schedule_entries: Vec<ScheduleEntryWitness>,
    /// 64 rounds.
    pub rounds: Vec<RoundWitness>,
    /// Finalization carries: 8 mod-2³² adds `H⁽ᵗ⁺¹⁾ⱼ = H⁽ᵗ⁾ⱼ + working[j]`.
    pub finalization_carries: [AddCarries; N_STATE_WORDS],
    /// Padding-role witness: which structural slot this block plays in the
    /// padded stream, the marker location, and the bit-length limbs. See
    /// [`PaddingRowWitness`].
    pub padding_row: PaddingRowWitness,
}

/// Top-level witness for an arbitrary-length SHA-256 hash.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Sha256Witness {
    /// The padding witness (raw message → padded blocks).
    pub padding: PaddingWitness,
    /// One block witness per padded block.
    pub blocks: Vec<BlockWitness>,
}

/// Owning witness for one packed SHA-256 component.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackedSha256Witness {
    pub(crate) messages: Vec<Sha256Witness>,
}

impl PackedSha256Witness {
    pub(crate) fn total_blocks(&self) -> usize {
        self.messages
            .iter()
            .map(|message| message.blocks.len())
            .sum()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn word_limbs_roundtrip() {
        for w in [0u32, 1, 0xFFFF, 0x1_0000, 0xDEAD_BEEF, u32::MAX] {
            let lw = WordLimbs::from_u32(w);
            assert!(lw.is_canonical(), "limbs out of range for {w:#x}");
            assert_eq!(lw.to_u32(), w);
        }
    }

    #[test]
    fn block_from_bytes_is_big_endian() {
        // "abc" padded out to one block — the FIPS 180-4 Appendix B.1 example.
        // Padding: 'a','b','c', 0x80, then zeros, then 24 (the bit length) BE.
        let mut bytes = [0u8; BLOCK_BYTES];
        bytes[0] = b'a';
        bytes[1] = b'b';
        bytes[2] = b'c';
        bytes[3] = 0x80;
        // bit length 24 = 0x18, in the last 8 bytes BE.
        bytes[BLOCK_BYTES - 1] = 24;

        let block = Block::from_bytes(&bytes);
        assert_eq!(block.0[0], 0x61626380, "first word must be 'abc'+0x80");
        assert_eq!(block.0[15], 0x0000_0018, "last word must be the bit length");
    }
}
