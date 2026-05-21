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
/// 6 Maj lookups and the 6 Ch lookups the AIR fires per round, after the
/// §8.1 "split once, reuse" optimisation.
///
/// Only the **fresh** operands per round live here: the *new* a-side input
/// `a` (= a-side split of either `h_in[0]` on round 0 or `a_new[t−1]`
/// otherwise), the Maj output `maj_out`, the *new* e-side input `e`, and
/// the Ch output `ch_out`. The Maj lookup's `b`/`c` operands and the Ch
/// lookup's `f`/`g` operands are read from prior rounds' `a_grp`/`e_grp`
/// columns via in-row aliasing (`b[t]=a[t−1]`, `c[t]=a[t−2]`,
/// `f[t]=e[t−1]`, `g[t]=e[t−2]`) — the trace commits each value's split
/// once and Section 8.1 of the validated design carries it forward.
///
/// For the first two rounds the chain reaches back past the start of the
/// block; those slots are supplied by [`BlockAuxSplitPackWitness`] (the
/// per-block split-and-pack of `h_in[1]`, `h_in[2]`, `h_in[5]`, `h_in[6]`).
/// `a_grp[round 0]` *is* the split-and-pack of `h_in[0]` (since
/// `a[0]=h_in[0]`), so `h_in[0]` does not get its own auxiliary commitment;
/// the same holds for `e_grp[round 0]` against `h_in[4]`.
///
/// Each cell is pinned to the split-and-pack table row content by the
/// corresponding lookup, which also implicitly range-checks the
/// originating 16-bit limb to `[0, 2¹⁶)` (design §11 L1).
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct RoundMajChWitness {
    /// a-side packed groups (`SIGMA0_GROUPS`) of the round's *new* `a`
    /// input. Pinned to `a.(lo, hi)` by the Σ0/Maj split-and-pack lookup.
    pub a_grp: RoundPackedGroups,
    /// a-side packed groups of `Maj(a, b, c)` — the output the Maj lookup
    /// emits per group position.
    pub maj_grp: RoundPackedGroups,
    /// e-side packed groups (`SIGMA1_GROUPS`) of the round's *new* `e`
    /// input. Pinned to `e.(lo, hi)` by the Σ1/Ch split-and-pack lookup.
    pub e_grp: RoundPackedGroups,
    /// e-side packed groups of `Ch(e, f, g)`.
    pub ch_grp: RoundPackedGroups,
}

/// Per-block auxiliary packed-group witness for the §8.1 reuse chain.
///
/// Holds the four split-and-pack outputs that the early rounds cannot
/// alias from any prior round (the chain reaches past `t = 0`). Specifically:
///
///   - `b_init`  — a-side packed groups of `h_in[1]`. Used as `b[0]` and
///     as `c[1]` via the alias `c[1] = b[0]`.
///   - `c_init`  — a-side packed groups of `h_in[2]`. Used as `c[0]`.
///   - `f_init`  — e-side packed groups of `h_in[5]`. Used as `f[0]` and
///     as `g[1]` via the alias `g[1] = f[0]`.
///   - `g_init`  — e-side packed groups of `h_in[6]`. Used as `g[0]`.
///
/// `h_in[0]` and `h_in[4]` do *not* need entries here: the per-round
/// `a_grp[round 0]` / `e_grp[round 0]` are already the split-and-pack of
/// those values (`a[0]=h_in[0]`, `e[0]=h_in[4]`). `h_in[3]` and `h_in[7]`
/// never feed Σ/Maj/Ch directly — they enter only as plain mod-2³² adds
/// — so they get no auxiliary split-and-pack either.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BlockAuxSplitPackWitness {
    pub b_init: RoundPackedGroups,
    pub c_init: RoundPackedGroups,
    pub f_init: RoundPackedGroups,
    pub g_init: RoundPackedGroups,
}

/// Per-σ-application split-and-pack witness for the `σ0`/`σ1` input word.
///
/// The σ-decode table is keyed by `key_s` and `key_s_complement` — the
/// 16-bit packings of the input word's bits at the partition's `S` (resp.
/// `S'`) positions. With the §8.1 reuse path applied to the round
/// partitions, the natural symmetry is to also pin the σ-decode keys via
/// a split-and-pack lookup: one per half of the input word.
///
/// Each split-and-pack row exposes `(key=half_limb, packed_s, packed_s')`,
/// implicitly range-checking the limb to `[0, 2¹⁶)`. The σ-decode
/// `key_s`/`key_s_complement` then reassembles by linear combination:
///   `key_s            = packed_s_lo + (1 << |S∩lo|) · packed_s_hi`
///   `key_s_complement = packed_s_complement_lo
///                       + (1 << |S'∩lo|) · packed_s_complement_hi`
/// with the partition-specific coefficients living in
/// [`crate::partitions::lower_sigma_key_hi_coeff_s`] (and the `_s_complement`
/// twin).
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SigmaInputSplitPackWitness {
    /// Bits of the input word's lo half at the partition's `S∩lo`
    /// positions, packed contiguously into the low `|S∩lo|` bits.
    pub packed_s_lo: u32,
    /// Bits of the input word's lo half at the partition's `S'∩lo`
    /// positions, packed into the low `|S'∩lo|` bits.
    pub packed_s_complement_lo: u32,
    /// Bits of the input word's hi half at the partition's `S∩hi`
    /// positions, packed into the low `|S∩hi|` bits.
    pub packed_s_hi: u32,
    /// Bits of the input word's hi half at the partition's `S'∩hi`
    /// positions, packed into the low `|S'∩hi|` bits.
    pub packed_s_complement_hi: u32,
}

impl SigmaInputSplitPackWitness {
    /// Compute the split-and-pack outputs of `x` against the σ partition
    /// defined by `parts`. Mirrors the body of `pack_half_key` but emits
    /// the four per-half packed values that the AIR commits.
    pub fn from_word(x: u32, parts: &crate::partitions::SigmaParts) -> Self {
        let lo = x & 0xFFFF;
        let hi = (x >> 16) & 0xFFFF;
        let mut packed_s_lo = 0u32;
        for (i, &pos) in parts.s_lo.iter().enumerate() {
            packed_s_lo |= ((lo >> pos) & 1) << i;
        }
        let mut packed_s_complement_lo = 0u32;
        for (i, &pos) in parts.s_complement_lo.iter().enumerate() {
            packed_s_complement_lo |= ((lo >> pos) & 1) << i;
        }
        let mut packed_s_hi = 0u32;
        for (i, &pos) in parts.s_hi.iter().enumerate() {
            packed_s_hi |= ((hi >> (pos - 16)) & 1) << i;
        }
        let mut packed_s_complement_hi = 0u32;
        for (i, &pos) in parts.s_complement_hi.iter().enumerate() {
            packed_s_complement_hi |= ((hi >> (pos - 16)) & 1) << i;
        }
        Self {
            packed_s_lo,
            packed_s_complement_lo,
            packed_s_hi,
            packed_s_complement_hi,
        }
    }
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
    /// Split-and-pack outputs of `W[t-15]` against the `σ0` partition —
    /// the four per-half packed values the σ0 split-and-pack lookup
    /// emits, and which the AIR linearly assembles into
    /// `lower_sigma0_decode.key_s` / `.key_s_complement`.
    pub lower_sigma0_input_split: SigmaInputSplitPackWitness,
    /// Split-and-pack outputs of `W[t-2]` against the `σ1` partition.
    pub lower_sigma1_input_split: SigmaInputSplitPackWitness,
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
    /// Per-block split-and-pack of the `b`/`c`/`f`/`g` initial values that
    /// the §8.1 reuse chain cannot alias from any prior round. See
    /// [`BlockAuxSplitPackWitness`].
    pub aux_split_pack: BlockAuxSplitPackWitness,
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
