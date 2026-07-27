//! Core types: the 32-bit-word → M31-limb representation, working state,
//! block bytes, and the witness records the trace generator consumes.
//!
//! Following §3 of `docs/research/sha256-air-design.md`, a SHA-256 word `w` is
//! stored as **two 16-bit limbs** `(lo, hi)` with `w = lo + 2¹⁶ · hi`. The
//! 16+16 split keeps every mod-2³² addition linear over M31 while the trace's
//! bit planes constrain the SHA boolean functions.

use crate::constants::{
    BLOCK_BYTES, DIGEST_BYTES, N_INPUT_WORDS, N_ROUNDS, N_STATE_WORDS, WORD_BYTES,
};

/// Width of a single limb. Two of these make a 32-bit word.
pub const LIMB_BITS: u32 = 16;

/// `2¹⁶ = 65 536`. A limb is in `[0, LIMB_BASE)`.
pub const LIMB_BASE: u32 = 1 << LIMB_BITS;

/// Maximum legal limb value, `2¹⁶ − 1`.
pub const LIMB_MAX: u32 = LIMB_BASE - 1;

/// One word as `(lo, hi)` limbs. `lo, hi ∈ [0, 2¹⁶)` in every native witness;
/// the AIR reconstructs the words from their constrained bit planes.
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
    pub const fn is_canonical(self) -> bool {
        self.lo <= LIMB_MAX && self.hi <= LIMB_MAX
    }
}

/// The SHA-256 working state `(a, b, c, d, e, f, g, h)`, in that order.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct WorkingState(pub [u32; N_STATE_WORDS]);

impl WorkingState {
    /// Index-into-name helpers — naming follows FIPS 180-4 §6.2.2 step 2.
    pub fn a(&self) -> u32 {
        self.0[0]
    }
    pub fn b(&self) -> u32 {
        self.0[1]
    }
    pub fn c(&self) -> u32 {
        self.0[2]
    }
    pub fn d(&self) -> u32 {
        self.0[3]
    }
    pub fn e(&self) -> u32 {
        self.0[4]
    }
    pub fn f(&self) -> u32 {
        self.0[5]
    }
    pub fn g(&self) -> u32 {
        self.0[6]
    }
    pub fn h(&self) -> u32 {
        self.0[7]
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
    /// The raw message bytes (private input).
    pub message: Vec<u8>,
    /// The padded message — a multiple of `BLOCK_BYTES` bytes (FIPS §5.1.1).
    pub padded: Vec<u8>,
    /// Number of blocks in `padded`.
    pub n_blocks: usize,
    /// Bit length of the message (the last 64 bits of `padded` encode this BE).
    pub bit_length: u64,
}

/// One row of the per-round witness, holding every value the AIR refers to
/// inside that round. Limb-level fields are `u32` because the trace converts
/// them to M31 just before commitment — and so this struct is testable
/// without pulling in field types.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RoundWitness {
    /// Round index `t ∈ [0, 64)`.
    pub t: u32,
    /// Working state at the *start* of the round, as `(lo, hi)` limbs for
    /// each of `a..h`. Index by `WorkingStateIdx`.
    pub state_in: [WordLimbs; N_STATE_WORDS],
    /// `W[t]` for this round as `(lo, hi)` limbs.
    pub w_t: WordLimbs,
    /// `K[t]` for this round as `(lo, hi)` limbs (hard-wired by the AIR).
    pub k_t: WordLimbs,
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

/// Carry chain of a single mod-2³² limb-add. `lo` carries from the low-limb
/// sum into the high-limb sum; `hi` carries out of the high-limb sum (and is
/// *discarded* — mod 2³²). Both are bounded by `k − 1` where `k` is the
/// number of words summed; the AIR range-checks them.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct AddCarries {
    pub lo: u32,
    pub hi: u32,
}

/// One 16-bit limb split into two 8-bit chunks (`b0 + 256 · b1 == limb`).
///
/// Used by field-exposure and terminal-byte helpers that need an explicit byte
/// view of a limb.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct LimbBytes {
    /// Low byte of the limb (`limb & 0xFF`).
    pub b0: u32,
    /// High byte of the limb (`limb >> 8`).
    pub b1: u32,
}

impl LimbBytes {
    /// Decompose a 16-bit limb into its two 8-bit chunks.
    #[inline]
    pub const fn from_u16(limb: u32) -> Self {
        Self {
            b0: limb & 0xFF,
            b1: (limb >> 8) & 0xFF,
        }
    }

    /// Recompose `b0 + 256 · b1`. Wraps if either byte exceeds `[0, 256)`.
    #[inline]
    pub const fn to_u16(self) -> u32 {
        self.b0 | (self.b1 << 8)
    }
}

/// Witness for one message-schedule entry `W[t]`, for `t ∈ [16, 64)`.
///
/// `W[t] = σ1(W[t−2]) + W[t−7] + σ0(W[t−15]) + W[t−16]` (mod 2³²).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ScheduleEntryWitness {
    /// Schedule index `t ∈ [16, 64)`.
    pub t: u32,
    pub w_t_minus_2: WordLimbs,
    pub w_t_minus_7: WordLimbs,
    pub w_t_minus_15: WordLimbs,
    pub w_t_minus_16: WordLimbs,
    pub lower_sigma0: WordLimbs,
    pub lower_sigma1: WordLimbs,
    /// The four-word `+` carries.
    pub carries: AddCarries,
    pub w_t: WordLimbs,
}

/// Number of 32-bit words in one padded block (= `N_INPUT_WORDS = 16`).
/// Exposed as a witness-layer constant so [`PaddingRowWitness`]'s one-hot
/// marker-word indicator vector has a stable size.
pub const WORDS_PER_BLOCK: usize = 16;

/// Number of bytes in a 32-bit word — the marker-byte selector vector's
/// length. Mirrors [`crate::constants::WORD_BYTES`] at the witness layer.
pub const BYTES_PER_WORD: usize = 4;

/// Per-block padding-role witness (§10.4 of the validated design).
///
/// One [`BlockWitness`] carries one of these. It pins:
/// 1. Which structural slot in the padded stream the block occupies —
///    pure message, marker-only (Case B penult), length-only (Case B last),
///    or marker-and-length (Case A trailing block).
/// 2. Where the `0x80` marker sits within the marker block: a 16-entry
///    one-hot vector for the word index and a 4-entry one-hot vector for
///    the byte position within that word, plus the marker word's 4-byte
///    big-endian decomposition.
/// 3. The four 16-bit limbs of the FIPS bit-length field (`W[14]`/`W[15]`
///    of the length block). Committed regardless of row so the
///    cross-component LogUp binding (deferred to Phase 2, item 2.4) can
///    expose them to the mdoc-parser stream uniformly.
///
/// Three small auxiliary booleans (`is_length_only_block`,
/// `is_marker_only_block`, `marker_word_post_strict_15`) are committed
/// rather than re-derived in the AIR so the [`crate::constraints`]
/// reformulation keeps each row constraint at degree ≤ 2 (per design
/// lesson L5). The witness generator pins them from the primary fields.
///
/// **Note on the asymmetric `_15`-only aux.** A symmetric `..._14`
/// auxiliary would express "force `W[14]` to zero on marker-only blocks
/// whose marker is strictly before `W[14]`." But the marker-only block
/// only appears in overflow Case B (`msg.len() % 64 ∈ [56, 64)`), where
/// the marker sits in `W[14]` or `W[15]` — never before `W[14]`. So
/// the aux would be identically zero and its W[14]-zero constraints
/// vacuous; we omit it.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct PaddingRowWitness {
    /// 1 iff this block contains the `0x80` padding marker.
    pub is_marker_block: u32,
    /// 1 iff this block is the final block (carries the bit-length in its
    /// last 8 bytes / `W[14]` / `W[15]`).
    pub is_length_block: u32,
    /// Aux: `(1 − is_marker_block) · is_length_block`. 1 on a pure
    /// length-only block (Case B's last block).
    pub is_length_only_block: u32,
    /// Aux: `is_marker_block · (1 − is_length_block)`. 1 on a pure
    /// marker-only block (Case B's penultimate block).
    pub is_marker_only_block: u32,
    /// One-hot indicator: `is_marker_word[j] == 1` iff word index `j` holds
    /// the `0x80` byte. All-zero on non-marker rows; sums to
    /// `is_marker_block`.
    pub is_marker_word: [u32; WORDS_PER_BLOCK],
    /// One-hot indicator: `marker_byte_sel[b] == 1` iff byte position `b`
    /// within the marker word holds `0x80`. BE order — `b = 0` is the MSB
    /// of `W[k]`. All-zero on non-marker rows; sums to `is_marker_block`.
    pub marker_byte_sel: [u32; BYTES_PER_WORD],
    /// Big-endian byte decomposition of the marker word, in MSB-first
    /// order. All-zero on non-marker rows. The constraint layer binds
    /// these to `W[marker_word_idx]` via the `is_marker_word` selector.
    pub marker_word_byte: [u32; BYTES_PER_WORD],
    /// Aux: `cumulative_marker_word_sel[15] · (1 − is_length_block)`.
    /// 1 iff this row is a marker-only block whose marker sits strictly
    /// before `W[15]` — i.e., marker at `W[14]` (overflow Case B with
    /// `msg.len() % 64 ∈ [56, 60)`). Then `W[15]` of this block must be
    /// 0, which the AIR enforces. Committed as a separate column so the
    /// `W[15]`-zero gate is degree 2 instead of the degree-3 triple
    /// product `cum[15] · (1 − is_length_block) · W[15]`.
    pub marker_word_post_strict_15: u32,
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
    /// Build the padding-row witness for block `block_idx` of a message
    /// whose FIPS-padded form is `padded`, given the raw message byte
    /// length `message_byte_length` and the total `n_blocks` in the
    /// padded stream.
    ///
    /// The marker sits at byte offset `message_byte_length` in the padded
    /// stream (FIPS §5.1.1). Its containing block is therefore
    /// `message_byte_length / BLOCK_BYTES`; its byte-within-block offset is
    /// `message_byte_length % BLOCK_BYTES`; from there the word index and
    /// byte-in-word fall out by dividing / modding by `BYTES_PER_WORD`.
    /// The length block is always the final block (`n_blocks − 1`); the
    /// two coincide in Case A (when `message_byte_length % 64 ∈ [0, 56)`)
    /// and differ in Case B (overflow into a separate length-only block).
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
        let is_length_only_block = (1 - is_marker_block) * is_length_block;
        let is_marker_only_block = is_marker_block * (1 - is_length_block);

        let mut is_marker_word = [0u32; WORDS_PER_BLOCK];
        let mut marker_byte_sel = [0u32; BYTES_PER_WORD];
        let mut marker_word_byte = [0u32; BYTES_PER_WORD];

        if is_marker_block == 1 {
            let off = marker_byte_offset % block_bytes;
            let word_idx = off / BYTES_PER_WORD;
            let byte_in_word = off % BYTES_PER_WORD;
            is_marker_word[word_idx] = 1;
            marker_byte_sel[byte_in_word] = 1;
            // Marker word bytes in BE order (byte 0 = MSB). Bytes before
            // the marker come from the tail of the message; the marker
            // byte is 0x80; bytes after are 0 (per FIPS §5.1.1).
            let word_start = block_idx * block_bytes + word_idx * BYTES_PER_WORD;
            for p in 0..BYTES_PER_WORD {
                marker_word_byte[p] = padded[word_start + p] as u32;
            }
        }

        let cumulative = |upto: usize| -> u32 { is_marker_word[..upto].iter().sum() };
        let marker_word_post_strict_15 = cumulative(15) * (1 - is_length_block);

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
            is_length_only_block,
            is_marker_only_block,
            is_marker_word,
            marker_byte_sel,
            marker_word_byte,
            marker_word_post_strict_15,
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
/// always `N_ROUNDS`; the trace generator asserts this on construction.
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
pub struct Sha256Witness {
    /// The padding witness (raw message → padded blocks).
    pub padding: PaddingWitness,
    /// One block witness per padded block.
    pub blocks: Vec<BlockWitness>,
    /// Final digest, recoverable from the last `BlockWitness.h_out`.
    pub digest: Digest,
}

impl Sha256Witness {
    /// Recompose the digest from the last block's `h_out` and assert
    /// consistency. Returns the canonical digest.
    pub fn digest_from_blocks(&self) -> Digest {
        let last = self.blocks.last().expect("at least one block");
        let mut state = HashState::default();
        for (i, slot) in state.0.iter_mut().enumerate() {
            *slot = last.h_out[i].to_u32();
        }
        Digest::from_state(&state)
    }
}

/// Working-state index mnemonics — useful for trace column naming.
#[derive(Copy, Clone, Debug)]
pub enum WorkingStateIdx {
    A = 0,
    B = 1,
    C = 2,
    D = 3,
    E = 4,
    F = 5,
    G = 6,
    H = 7,
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
