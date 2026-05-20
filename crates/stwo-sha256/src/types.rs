//! Core types: the 32-bit-word → M31-limb representation, working state,
//! block bytes, and the witness records the trace generator consumes.
//!
//! Following §3 of `research/sha256-air-design.md`, a SHA-256 word `w` is
//! stored as **two 16-bit limbs** `(lo, hi)` with `w = lo + 2¹⁶ · hi`. The
//! 16+16 split is the natural minimum that aligns with the lookup-key width
//! of the `Σ`/`σ` decode tables (whose keys are 16-bit half-words).
//!
//! `Serialize`/`Deserialize` is derived only where it costs nothing
//! (small-array and `Vec`-backed types). Witness records contain
//! `[T; N_ROUNDS]` arrays — `serde` does not auto-derive on `[T; 64]`, so
//! those types use `Vec` instead of fixed-size arrays for the long axis.

use serde::{Deserialize, Serialize};

use crate::constants::{
    BLOCK_BYTES, DIGEST_BYTES, N_INPUT_WORDS, N_ROUNDS, N_STATE_WORDS, WORD_BYTES,
};

/// Width of a single limb. Two of these make a 32-bit word.
pub const LIMB_BITS: u32 = 16;

/// `2¹⁶ = 65 536`. A limb is in `[0, LIMB_BASE)`.
pub const LIMB_BASE: u32 = 1 << LIMB_BITS;

/// Maximum legal limb value, `2¹⁶ − 1`.
pub const LIMB_MAX: u32 = LIMB_BASE - 1;

/// One word as `(lo, hi)` limbs. `lo, hi ∈ [0, 2¹⁶)`. The constraint layer
/// range-checks these via the lookup-table consumers (every limb is either an
/// input to or an output of a lookup keyed on `[0, 2¹⁶)`).
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
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

    /// True iff both limbs are in `[0, 2¹⁶)`. The native witness layer
    /// guarantees this; the AIR enforces it via the lookup tables.
    #[inline]
    pub const fn is_canonical(self) -> bool {
        self.lo <= LIMB_MAX && self.hi <= LIMB_MAX
    }
}

/// The SHA-256 working state `(a, b, c, d, e, f, g, h)`, in that order.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
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
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct HashState(pub [u32; N_STATE_WORDS]);

/// A 512-bit padded block, as 16 big-endian 32-bit words.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
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
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
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
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
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

/// Packed-group decomposition of one 32-bit value under a 6-group
/// round-function partition (`Σ0`/`Maj` a-side or `Σ1`/`Ch` e-side).
///
/// The Maj/Ch packed table at width `W ≥ MAX_ROUND_GROUP_BITS` is keyed on
/// these packed values: bit `j` of `vals[i]` is the bit of the source word
/// at the partition's `groups_in_order()[i][j]` position. Each value lies
/// in `[0, 2^|group_i|) ⊆ [0, 2^W)`, range-checked implicitly by being a
/// lookup-table input. Six values per word per partition — three `S`-side
/// groups followed by three `S'`-side groups.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct RoundPackedGroups {
    /// 6 packed values in `partitions::RoundGroups::groups_in_order()` order.
    pub vals: [u32; 6],
}

impl RoundPackedGroups {
    /// Pack the 6 group values of `w` against the given partition. Mirrors
    /// `partitions::pack_round_groups` but typed at the witness layer so
    /// every consumer reads the same field order.
    #[inline]
    pub fn pack(w: u32, groups: &crate::partitions::RoundGroups) -> Self {
        Self {
            vals: crate::partitions::pack_round_groups(w, groups),
        }
    }
}

/// Per-round Maj/Ch packed-group witness — the inputs and outputs of the
/// 6 Maj lookups and the 6 Ch lookups the AIR fires per round.
///
/// `a`/`b`/`c` and `maj_out` use the **a-side** partition (`SIGMA0_GROUPS`);
/// `e`/`f`/`g` and `ch_out` use the **e-side** partition (`SIGMA1_GROUPS`).
/// The lookup-key shape is `(a_grp[i], b_grp[i], c_grp[i], maj_grp[i])` for
/// Maj, `(e_grp[i], f_grp[i], g_grp[i], ch_grp[i])` for Ch — one entry per
/// group `i ∈ 0..6`.
///
/// Until 3.9.5 wires the split-and-pack lookup, the packed-group columns
/// are *free* in the trace: nothing forces `a_grp[i]` to actually come from
/// the bits of `a` committed elsewhere in the row. The Maj/Ch lookup pins
/// `(a, b, c) → maj` to a valid table row but not to the row's word values
/// — that tie-back is interface-contract item 4 of 3.9.5.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct RoundMajChWitness {
    pub a_grp: RoundPackedGroups,
    pub b_grp: RoundPackedGroups,
    pub c_grp: RoundPackedGroups,
    pub maj_grp: RoundPackedGroups,
    pub e_grp: RoundPackedGroups,
    pub f_grp: RoundPackedGroups,
    pub g_grp: RoundPackedGroups,
    pub ch_grp: RoundPackedGroups,
}

/// One row of the per-round witness, holding every value the AIR refers to
/// inside that round. Limb-level fields are `u32` because the trace converts
/// them to M31 just before commitment — and so this struct is testable
/// without pulling in field types.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
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
    /// Decoded intermediates of `Σ0(a)` — half-keys, spread `O0`/`O1`,
    /// `O2` partials, combined `O2`, and chunk decomposition for `xor_8`.
    pub sigma0_decode: SigmaDecodeWitness,
    /// Decoded intermediates of `Σ1(e)`.
    pub sigma1_decode: SigmaDecodeWitness,
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
    /// Packed-group decomposition of every operand the per-round Maj/Ch
    /// lookups consume. See [`RoundMajChWitness`].
    pub maj_ch: RoundMajChWitness,
}

/// Carry chain of a single mod-2³² limb-add. `lo` carries from the low-limb
/// sum into the high-limb sum; `hi` carries out of the high-limb sum (and is
/// *discarded* — mod 2³²). Both are bounded by `k − 1` where `k` is the
/// number of words summed; the AIR range-checks them.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AddCarries {
    pub lo: u32,
    pub hi: u32,
}

/// One 16-bit limb split into two 8-bit chunks (`b0 + 256 · b1 == limb`).
///
/// The `Σ`/`σ` output reassembly XORs the two side `O2` partials into the
/// combined `O2` contribution; the design (§9.3) avoids per-function 2²⁰
/// XOR-combine tables by chunking each 16-bit limb into bytes and XOR'ing
/// chunk-wise through the single generic `xor_8` table. This struct holds
/// the byte chunks of one limb so the witness can carry the values the
/// chunk-bind constraint (lo + 256·hi == limb) range-checks, and the
/// follow-on `xor_8` wiring (3.9.4) can look up `(b0_s, b0_s', b0_combined)`
/// directly.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
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

/// Byte chunks of one `(lo, hi)` limb pair (`O2` partial or combined output).
///
/// `lo` chunks `(lo.b0, lo.b1)` reconstruct the lo-limb; `hi` chunks the
/// hi-limb. Four bytes per limb pair — chunks for the S-side partial, the
/// S′-side partial, and their XOR-combined value are all committed (see
/// [`SigmaDecodeWitness`]) so the `xor_8` chunk-wise lookup can fire on
/// the three matched byte triples.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct LimbPairBytes {
    pub lo: LimbBytes,
    pub hi: LimbBytes,
}

impl LimbPairBytes {
    /// Build the chunks of a `WordLimbs` value (each limb split into 2 bytes).
    #[inline]
    pub const fn from_limbs(limbs: WordLimbs) -> Self {
        Self {
            lo: LimbBytes::from_u16(limbs.lo),
            hi: LimbBytes::from_u16(limbs.hi),
        }
    }

    /// Recompose the four-byte chunks back into a `WordLimbs`.
    #[inline]
    pub const fn to_limbs(self) -> WordLimbs {
        WordLimbs {
            lo: self.lo.to_u16(),
            hi: self.hi.to_u16(),
        }
    }
}

/// Per-σ-application decoded intermediates (§9.3 of the validated design).
///
/// A `Σ`/`σ` evaluation `y = f(x)` decomposes by GF(2)-linearity into three
/// disjoint output groups:
/// - `O0`: output bits whose input-bit dependency lies entirely in the
///   16-bit `S` half — computable from the S-half alone.
/// - `O1`: output bits whose dependency lies entirely in the `S′` half.
/// - `O2`: output bits whose dependency crosses both sides — emitted as
///   *two* "partials", one from each side, that XOR to the true `O2`
///   contribution.
///
/// Per side, one lookup into the `2¹⁶`-row decode table maps the half-key
/// to `(o_main_lo, o_main_hi, o2_partial_lo, o2_partial_hi)`. The two
/// `O2` partials XOR — chunk-wise through the generic `xor_8` table
/// (§9.3) — into `o2_combined`. The final output reassembles by field
/// addition of disjoint spread parts:
/// `y.lo = o_main_s.lo + o_main_s_complement.lo + o2_combined.lo`
/// (analogously for `.hi`).
///
/// This struct carries every intermediate the AIR commits per σ-call so the
/// decode-table `add_to_relation` calls and the `xor_8` chunk-wise lookups
/// can both be wired without re-deriving values from the input word.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SigmaDecodeWitness {
    /// 16-bit packing of the `S`-positions of the input word — the decode
    /// table is indexed by this.
    pub key_s: u32,
    /// 16-bit packing of the `S′`-positions of the input word.
    pub key_s_complement: u32,
    /// Spread `O0` output bits (at natural positions, split lo/hi).
    pub o_main_s: WordLimbs,
    /// Spread `O1` output bits.
    pub o_main_s_complement: WordLimbs,
    /// `O2` partial XOR contribution from the `S` half (natural positions, lo/hi).
    pub o2_partial_s: WordLimbs,
    /// `O2` partial XOR contribution from the `S′` half.
    pub o2_partial_s_complement: WordLimbs,
    /// `o2_partial_s ⊕ o2_partial_s_complement` — the true `O2` contribution.
    pub o2_combined: WordLimbs,
    /// Byte chunks of `o2_partial_s` (`lo + 256·hi == limb` per limb).
    pub o2_chunks_s: LimbPairBytes,
    /// Byte chunks of `o2_partial_s_complement`.
    pub o2_chunks_s_complement: LimbPairBytes,
    /// Byte chunks of `o2_combined`. The matched triple
    /// `(o2_chunks_s, o2_chunks_s_complement, o2_chunks_combined)` is what
    /// the chunk-wise `xor_8` lookup wired in the follow-on task reads.
    pub o2_chunks_combined: LimbPairBytes,
}

/// Witness for one message-schedule entry `W[t]`, for `t ∈ [16, 64)`.
///
/// `W[t] = σ1(W[t−2]) + W[t−7] + σ0(W[t−15]) + W[t−16]` (mod 2³²).
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScheduleEntryWitness {
    /// Schedule index `t ∈ [16, 64)`.
    pub t: u32,
    pub w_t_minus_2: WordLimbs,
    pub w_t_minus_7: WordLimbs,
    pub w_t_minus_15: WordLimbs,
    pub w_t_minus_16: WordLimbs,
    pub lower_sigma0: WordLimbs,
    pub lower_sigma1: WordLimbs,
    /// Decoded intermediates of `σ0(W[t-15])` — half-keys, spread `O0`/`O1`,
    /// `O2` partials, combined `O2`, and chunk decomposition for `xor_8`.
    pub lower_sigma0_decode: SigmaDecodeWitness,
    /// Decoded intermediates of `σ1(W[t-2])`.
    pub lower_sigma1_decode: SigmaDecodeWitness,
    /// The four-word `+` carries.
    pub carries: AddCarries,
    pub w_t: WordLimbs,
}

/// Witness for one block: schedule, 64-round state evolution, IV-in/out.
///
/// `schedule` is a `Vec` rather than `[WordLimbs; N_ROUNDS]` so that this
/// type can derive `Serialize`/`Deserialize` (serde does not auto-derive
/// `[T; N]` for `N > 32`). The length is always `N_ROUNDS`; the trace
/// generator asserts this on construction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
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
}

/// Top-level witness for an arbitrary-length SHA-256 hash.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
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
