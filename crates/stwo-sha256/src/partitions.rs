//! Validated bit-index partitions for `Σ0`, `Σ1`, `σ0`, `σ1`.
//!
//! Implements §§6–8 of `docs/research/sha256-air-design.md`. Each function `F` is a
//! GF(2)-linear map from 32 input bits to 32 output bits. We pick a 16-bit
//! subset `S` of the input bits and classify every output bit `i` by its
//! input-bit dependency set `D(i)`:
//!
//! - `D(i) ⊆ S`        — group `O0`, computable from the `S` half alone,
//! - `D(i) ⊆ S' = ¬S`  — group `O1`, computable from the `S'` half alone,
//! - otherwise         — group `O2`, mixed, combined separately.
//!
//! The output is reassembled by *field addition* of the spread (bit-disjoint)
//! `O0`/`O1`/`O2` contributions — disjoint bit sets ⇒ `+` matches `⊕`.
//!
//! All constants here are LSB-0 (bit `i` of `w` has value `2ⁱ`, matching
//! Rust's `u32::rotate_right` and `>>`). The tests in this module reproduce
//! Appendix A of the design document deterministically.

use crate::constants::N_STATE_WORDS;

/// Bit width of a SHA-256 word.
pub const WORD_BITS: u32 = 32;

/// LSB-0 mask of the `S` half (16 bits) used by each `Σ`/`σ` partition.
pub mod s_mask {
    /// `Σ0` S = `{0,1,7,8,9,10,11, 18,19,20,21,22, 28,29,30,31}`.
    pub const SIGMA0: u32 = mask(&[0, 1, 7, 8, 9, 10, 11, 18, 19, 20, 21, 22, 28, 29, 30, 31]);
    /// `Σ1` S = `{2,3,6,7,11,12, 16,17,20,21,24,25,26, 29,30,31}`.
    pub const SIGMA1: u32 = mask(&[2, 3, 6, 7, 11, 12, 16, 17, 20, 21, 24, 25, 26, 29, 30, 31]);
    /// `σ0` S = `{3,5,7,9,11,13,14, 16,18,20,22,24,26,28,30,31}`.
    pub const LOWER_SIGMA0: u32 =
        mask(&[3, 5, 7, 9, 11, 13, 14, 16, 18, 20, 22, 24, 26, 28, 30, 31]);
    /// `σ1` S = `{1,2,3,4,6,8,13,15, 17,20,22,24,26,27,29,31}`.
    pub const LOWER_SIGMA1: u32 = mask(&[1, 2, 3, 4, 6, 8, 13, 15, 17, 20, 22, 24, 26, 27, 29, 31]);

    const fn mask(bits: &[u32]) -> u32 {
        let mut m = 0u32;
        let mut i = 0;
        while i < bits.len() {
            m |= 1u32 << bits[i];
            i += 1;
        }
        m
    }
}

/// Eight bit-groups per round-function partition (`W = 6` layout).
///
/// For `W = 6` the `Maj`/`Ch` packed table must address each group with
/// `≤ 6` bits, so the two 7-bit groups of the original `W = 7` partition
/// (`Σ0`: `L0`, `H2`; `Σ1`: `Le1`, `He0`) are each split into two ≤6-bit
/// sub-groups that stay inside their original 16-bit half. The bitwise
/// nature of `Maj`/`Ch` means *any* partition of a word's bits is sound
/// (design §8.1, §9.2), so the only constraints on a split are: ≤6 bits,
/// within one half, and balanced for packing efficiency.
///
/// Sub-group splits (design §9.2 "pad smaller groups into the single 2¹⁸
/// table"):
///
/// - `Σ0`: `L0 = {0,1,7,8,9,10,11}` → `L0a = {0,1}` (2b) + `L0b =
///   {7,8,9,10,11}` (5b); `H2 = {16,17,23,24,25,26,27}` → `H2a = {16,17}`
///   (2b) + `H2b = {23,24,25,26,27}` (5b). Result: `(L0a, L0b, H0, H1) ⊎
///   (L1, L2, H2a, H2b) = S ⊎ S'`.
/// - `Σ1`: `Le1 = {0,1,4,5,8,9,10}` → `Le1a = {0,1,4,5}` (4b) + `Le1b =
///   {8,9,10}` (3b); `He0 = {16,17,20,21,24,25,26}` → `He0a =
///   {16,17,20,21}` (4b) + `He0b = {24,25,26}` (3b). Result: `(Le0, He0a,
///   He0b, He1) ⊎ (Le1a, Le1b, Le2, He2) = S ⊎ S'`.
///
/// Each group is listed lowest-bit-index first within its side, and every
/// group's bits form a contiguous run in the side's ascending-bit order —
/// the invariant [`round_key_coeffs`] relies on. Group naming follows
/// `docs/research/sha256-air-design.md` so the design doc and code stay
/// traceable.
pub struct RoundGroups {
    /// Four groups composing the `S` half, lowest-bit-index first. LSB-0.
    pub s: [&'static [u32]; 4],
    /// Four groups composing the `S'` half, lowest-bit-index first. LSB-0.
    pub s_complement: [&'static [u32]; 4],
}

/// `Σ0` groups — `L0a/L0b/H0/H1` ⊎ `L1/L2/H2a/H2b` (W=6 split of §6.2's
/// `L0/H0/H1 ⊎ L1/L2/H2`; `L0` and `H2` subdivided to ≤6 bits).
pub const SIGMA0_GROUPS: RoundGroups = RoundGroups {
    s: [
        &[0, 1],               // L0a (2 bits)
        &[7, 8, 9, 10, 11],    // L0b (5 bits)
        &[18, 19, 20, 21, 22], // H0  (5 bits)
        &[28, 29, 30, 31],     // H1  (4 bits)
    ],
    s_complement: [
        &[2, 3, 4, 5, 6],      // L1  (5 bits)
        &[12, 13, 14, 15],     // L2  (4 bits)
        &[16, 17],             // H2a (2 bits)
        &[23, 24, 25, 26, 27], // H2b (5 bits)
    ],
};

/// `Σ1` groups — `Le0/He0a/He0b/He1` ⊎ `Le1a/Le1b/Le2/He2` (W=6 split of
/// §7's `Le0/He0/He1 ⊎ Le1/Le2/He2`; `He0` and `Le1` subdivided to ≤6 bits).
pub const SIGMA1_GROUPS: RoundGroups = RoundGroups {
    s: [
        &[2, 3, 6, 7, 11, 12], // Le0  (6 bits)
        &[16, 17, 20, 21],     // He0a (4 bits)
        &[24, 25, 26],         // He0b (3 bits)
        &[29, 30, 31],         // He1  (3 bits)
    ],
    s_complement: [
        &[0, 1, 4, 5],             // Le1a (4 bits)
        &[8, 9, 10],               // Le1b (3 bits)
        &[13, 14, 15],             // Le2  (3 bits)
        &[18, 19, 22, 23, 27, 28], // He2  (6 bits)
    ],
};

/// `σ0` partition. `σ` functions do not co-serve `Maj`/`Ch`, so no ≤7-bit cap
/// — just the `S∩lo / S∩hi / S'∩lo / S'∩hi` 4-part split per §8.2.
pub const LOWER_SIGMA0_PARTS: SigmaParts = SigmaParts {
    s_lo: &[3, 5, 7, 9, 11, 13, 14],
    s_hi: &[16, 18, 20, 22, 24, 26, 28, 30, 31],
    s_complement_lo: &[0, 1, 2, 4, 6, 8, 10, 12, 15],
    s_complement_hi: &[17, 19, 21, 23, 25, 27, 29],
};

/// `σ1` partition per §8.2.
pub const LOWER_SIGMA1_PARTS: SigmaParts = SigmaParts {
    s_lo: &[1, 2, 3, 4, 6, 8, 13, 15],
    s_hi: &[17, 20, 22, 24, 26, 27, 29, 31],
    s_complement_lo: &[0, 5, 7, 9, 10, 11, 12, 14],
    s_complement_hi: &[16, 18, 19, 21, 23, 25, 28, 30],
};

/// `S ∩ lo`, `S ∩ hi`, `S' ∩ lo`, `S' ∩ hi` — the four "parts" the design
/// document references as the lookup-key shape of a `σ` decode.
pub struct SigmaParts {
    pub s_lo: &'static [u32],
    pub s_hi: &'static [u32],
    pub s_complement_lo: &'static [u32],
    pub s_complement_hi: &'static [u32],
}

/// Output-bit classification `O0 ⊎ O1 ⊎ O2` for each function.
///
/// `O0` is computable from `S`-side inputs only; `O1` from `S'`-side only;
/// `O2` is the mixed (cross-side) tail combined via the `xor_8` table.
pub struct OutputClassification {
    pub o0: &'static [u32],
    pub o1: &'static [u32],
    pub o2: &'static [u32],
}

/// `Σ0` outputs — `|O0|=|O1|=11`, `|O2|=10` (§6.3).
pub const SIGMA0_OUTPUTS: OutputClassification = OutputClassification {
    o0: &[6, 7, 8, 9, 17, 18, 19, 20, 28, 29, 30],
    o1: &[1, 2, 3, 4, 12, 13, 14, 22, 23, 24, 25],
    o2: &[0, 5, 10, 11, 15, 16, 21, 26, 27, 31],
};

/// `Σ1` outputs — `|O0|=|O1|=11`, `|O2|=10` (§7).
pub const SIGMA1_OUTPUTS: OutputClassification = OutputClassification {
    o0: &[0, 1, 5, 6, 10, 14, 18, 19, 23, 24, 28],
    o1: &[2, 3, 7, 8, 12, 16, 17, 21, 22, 26, 30],
    o2: &[4, 9, 11, 13, 15, 20, 25, 27, 29, 31],
};

/// `σ0` outputs — `|O0|=|O1|=11`, `|O2|=10` (§8.2).
pub const LOWER_SIGMA0_OUTPUTS: OutputClassification = OutputClassification {
    o0: &[0, 2, 4, 6, 13, 17, 19, 21, 23, 28, 30],
    o1: &[1, 3, 5, 14, 16, 18, 20, 22, 26, 29, 31],
    o2: &[7, 8, 9, 10, 11, 12, 15, 24, 25, 27],
};

/// `σ1` outputs — `|O0|=|O1|=12`, `|O2|=8` (`SHR10` zeroes the dependency of
/// 10 output bits, so the partition is *better* than the rotates-only ones).
pub const LOWER_SIGMA1_OUTPUTS: OutputClassification = OutputClassification {
    o0: &[3, 5, 7, 10, 12, 14, 16, 17, 19, 21, 28, 30],
    o1: &[2, 4, 6, 11, 13, 20, 22, 24, 25, 27, 29, 31],
    o2: &[0, 1, 8, 9, 15, 18, 23, 26],
};

/// Per-output-bit dependency mask of one of the four functions, LSB-0.
///
/// `dependency_mask(SigmaFn::Sigma0)[i]` is the bitmask of input bits that
/// output bit `i` of `Σ0` depends on; equivalent to Appendix A's `big`/`small`
/// constructors.
pub fn dependency_mask(f: SigmaFn) -> [u32; WORD_BITS as usize] {
    let mut out = [0u32; WORD_BITS as usize];
    let (r1, r2, third) = f.params();
    for (i, slot) in out.iter_mut().enumerate() {
        let mut d = 0u32;
        d |= 1u32 << ((i as u32 + r1) % WORD_BITS);
        d |= 1u32 << ((i as u32 + r2) % WORD_BITS);
        match third {
            ThirdTerm::Rotr(r3) => d |= 1u32 << ((i as u32 + r3) % WORD_BITS),
            ThirdTerm::Shr(s) => {
                // SHR drops bits that would shift past bit 31.
                if (i as u32) + s < WORD_BITS {
                    d |= 1u32 << ((i as u32) + s);
                }
            }
        }
        *slot = d;
    }
    out
}

/// One of the four bit-shuffle functions appearing in SHA-256.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum SigmaFn {
    /// `Σ0(a) = ROTR2(a) ⊕ ROTR13(a) ⊕ ROTR22(a)`.
    Sigma0,
    /// `Σ1(e) = ROTR6(e) ⊕ ROTR11(e) ⊕ ROTR25(e)`.
    Sigma1,
    /// `σ0(x) = ROTR7(x) ⊕ ROTR18(x) ⊕ SHR3(x)`.
    LowerSigma0,
    /// `σ1(x) = ROTR17(x) ⊕ ROTR19(x) ⊕ SHR10(x)`.
    LowerSigma1,
}

enum ThirdTerm {
    Rotr(u32),
    Shr(u32),
}

impl SigmaFn {
    /// `(r1, r2, third)` for each function.
    fn params(self) -> (u32, u32, ThirdTerm) {
        match self {
            SigmaFn::Sigma0 => (2, 13, ThirdTerm::Rotr(22)),
            SigmaFn::Sigma1 => (6, 11, ThirdTerm::Rotr(25)),
            SigmaFn::LowerSigma0 => (7, 18, ThirdTerm::Shr(3)),
            SigmaFn::LowerSigma1 => (17, 19, ThirdTerm::Shr(10)),
        }
    }

    /// The 16-bit `S` mask for this function (LSB-0).
    pub fn s_mask(self) -> u32 {
        match self {
            SigmaFn::Sigma0 => s_mask::SIGMA0,
            SigmaFn::Sigma1 => s_mask::SIGMA1,
            SigmaFn::LowerSigma0 => s_mask::LOWER_SIGMA0,
            SigmaFn::LowerSigma1 => s_mask::LOWER_SIGMA1,
        }
    }

    /// The output classification for this function.
    pub fn outputs(self) -> &'static OutputClassification {
        match self {
            SigmaFn::Sigma0 => &SIGMA0_OUTPUTS,
            SigmaFn::Sigma1 => &SIGMA1_OUTPUTS,
            SigmaFn::LowerSigma0 => &LOWER_SIGMA0_OUTPUTS,
            SigmaFn::LowerSigma1 => &LOWER_SIGMA1_OUTPUTS,
        }
    }
}

/// Classify the 32 output bits of `f` given a candidate `S` mask. Used by the
/// verification tests to reproduce Appendix A independently of the constants.
pub fn classify(f: SigmaFn, s_set: u32) -> (Vec<u32>, Vec<u32>, Vec<u32>) {
    let dep = dependency_mask(f);
    let s_complement = !s_set;
    let mut o0 = Vec::new();
    let mut o1 = Vec::new();
    let mut o2 = Vec::new();
    for (i, &d) in dep.iter().enumerate() {
        let i = i as u32;
        if d & s_set == d {
            o0.push(i);
        } else if d & s_complement == d {
            o1.push(i);
        } else {
            o2.push(i);
        }
    }
    (o0, o1, o2)
}

/// Convenience: build a `u32` bitmask from a slice of bit indices.
pub fn bits_to_mask(bits: &[u32]) -> u32 {
    bits.iter().fold(0u32, |m, &b| m | (1u32 << b))
}

/// Apply `f` to a 32-bit input word directly (out-of-circuit oracle for the
/// lookup tables). Bit-for-bit reproduces the FIPS definitions in §2.
pub fn apply(f: SigmaFn, w: u32) -> u32 {
    match f {
        SigmaFn::Sigma0 => w.rotate_right(2) ^ w.rotate_right(13) ^ w.rotate_right(22),
        SigmaFn::Sigma1 => w.rotate_right(6) ^ w.rotate_right(11) ^ w.rotate_right(25),
        SigmaFn::LowerSigma0 => w.rotate_right(7) ^ w.rotate_right(18) ^ (w >> 3),
        SigmaFn::LowerSigma1 => w.rotate_right(17) ^ w.rotate_right(19) ^ (w >> 10),
    }
}

/// `O0 ⊎ O1 ⊎ O2` must cover all 32 output bits exactly once. Returned mask
/// is the union; the design is correct iff this equals `u32::MAX` for every
/// function.
pub fn output_coverage(c: &OutputClassification) -> u32 {
    bits_to_mask(c.o0) | bits_to_mask(c.o1) | bits_to_mask(c.o2)
}

/// `RoundGroups` ⊎ → `S` and `S'`. Each group must fit inside a 16-bit half,
/// so `Maj`/`Ch` packed lookups address a single half-word.
pub fn round_groups_consistent(groups: &RoundGroups, expected_s: u32) -> bool {
    let s_assembled = groups
        .s
        .iter()
        .flat_map(|g| g.iter().copied())
        .fold(0u32, |m, b| m | (1u32 << b));
    let s_complement_assembled = groups
        .s_complement
        .iter()
        .flat_map(|g| g.iter().copied())
        .fold(0u32, |m, b| m | (1u32 << b));

    let every_group_fits_in_a_half = groups.s.iter().chain(groups.s_complement.iter()).all(|g| {
        let hi = g.iter().all(|&b| b >= 16);
        let lo = g.iter().all(|&b| b < 16);
        hi || lo
    });

    s_assembled == expected_s
        && s_complement_assembled == !expected_s
        && (s_assembled & s_complement_assembled) == 0
        && (s_assembled | s_complement_assembled) == u32::MAX
        && every_group_fits_in_a_half
}

/// Sanity over the parts of a `σ` partition (`S∩lo / S∩hi / S'∩lo / S'∩hi`).
pub fn sigma_parts_consistent(parts: &SigmaParts, expected_s: u32) -> bool {
    let s_lo_mask = bits_to_mask(parts.s_lo);
    let s_hi_mask = bits_to_mask(parts.s_hi);
    let s_complement_lo_mask = bits_to_mask(parts.s_complement_lo);
    let s_complement_hi_mask = bits_to_mask(parts.s_complement_hi);

    let s_assembled = s_lo_mask | s_hi_mask;
    let s_complement_assembled = s_complement_lo_mask | s_complement_hi_mask;
    let lo_complete = (s_lo_mask | s_complement_lo_mask) == 0x0000_FFFF;
    let hi_complete = (s_hi_mask | s_complement_hi_mask) == 0xFFFF_0000;
    let s_lo_in_lo = parts.s_lo.iter().all(|&b| b < 16);
    let s_hi_in_hi = parts.s_hi.iter().all(|&b| b >= 16);
    let s_complement_lo_in_lo = parts.s_complement_lo.iter().all(|&b| b < 16);
    let s_complement_hi_in_hi = parts.s_complement_hi.iter().all(|&b| b >= 16);

    s_assembled == expected_s
        && s_complement_assembled == !expected_s
        && lo_complete
        && hi_complete
        && s_lo_in_lo
        && s_hi_in_hi
        && s_complement_lo_in_lo
        && s_complement_hi_in_hi
}

/// Max packed-group width `W`. At `W = 6` the `Maj`/`Ch` table is `2^(3·6)
/// = 2¹⁸` rows (≈ 262 k) — an 8× shrink from the `W = 7` `2²¹` table that
/// dominates prove cost (perf-doc §3.1, §4.1). Every round-function group
/// is `≤ 6` bits; smaller sub-groups pad with leading zeros into the same
/// table (design §9.2).
pub const MAX_ROUND_GROUP_BITS: u32 = 6;

/// Number of groups per round-function partition (4 `S`-side + 4 `S'`-side).
/// The constraint layer enumerates them in this order — `S[0..4]` then
/// `S'[0..4]` — and the Maj/Ch lookup fires once per group position
/// (8 lookups per function per round at `W = 6`, design §9.2).
pub const GROUPS_PER_ROUND_PARTITION: usize = 8;

impl RoundGroups {
    /// Eight groups in fixed enumeration order: `S[0..4]` then `S'[0..4]`.
    /// Used by the Maj/Ch witness emitter and the AIR's packed-group read
    /// loop to agree on which packed value corresponds to which set of
    /// natural bit-positions.
    pub fn groups_in_order(&self) -> [&'static [u32]; GROUPS_PER_ROUND_PARTITION] {
        [
            self.s[0],
            self.s[1],
            self.s[2],
            self.s[3],
            self.s_complement[0],
            self.s_complement[1],
            self.s_complement[2],
            self.s_complement[3],
        ]
    }
}

/// Positions within [`RoundGroups::groups_in_order`] whose bits live in the
/// lo (`< 16`) and hi (`≥ 16`) 16-bit word half, returned as
/// `(lo_indices, hi_indices)` in ascending index order.
///
/// This is the projection the round-side split-and-pack lookup keys on: the
/// lo-half table row carries the packed groups at `lo_indices`, the hi-half
/// row those at `hi_indices`. The order matches
/// [`crate::tables::build_round_split_pack_table`], which iterates
/// `s.chain(s_complement)` filtered by half — i.e. `groups_in_order()`
/// filtered by half, preserving index order. Under the `W = 6` partition
/// each half holds exactly four sub-groups, so both vectors have length 4
/// (matching `key + 4 groups = ROUND_SPLIT_PACK_REL_SIZE` cells). The split
/// differs per partition: `Σ0` projects lo `[0,1,4,5]` / hi `[2,3,6,7]`;
/// `Σ1` projects lo `[0,4,5,6]` / hi `[1,2,3,7]`.
pub fn round_groups_half_indices(groups: &RoundGroups) -> (Vec<usize>, Vec<usize>) {
    let mut lo = Vec::new();
    let mut hi = Vec::new();
    for (i, g) in groups.groups_in_order().iter().enumerate() {
        // Every group lies entirely in one half (round_groups_consistent).
        if g.iter().all(|&b| b < 16) {
            lo.push(i);
        } else {
            hi.push(i);
        }
    }
    (lo, hi)
}

/// Pack the bits of `w` at each of the partition's eight group positions into
/// the low bits of a packed value. Output `[i]` is the bits of `w` at
/// `groups_in_order()[i]`, compressed contiguously from bit 0. Each value
/// lies in `[0, 2^|group_i|) ⊆ [0, 2^MAX_ROUND_GROUP_BITS)`.
///
/// The packed-group representation is what the `Maj`/`Ch` lookup keys on —
/// because `Maj` and `Ch` are bitwise, the same packed-table row pattern
/// applies at every group position; the natural-position spread is what
/// the split-and-pack lookup (3.9.5) reconstructs.
pub fn pack_round_groups(w: u32, groups: &RoundGroups) -> [u32; GROUPS_PER_ROUND_PARTITION] {
    let mut out = [0u32; GROUPS_PER_ROUND_PARTITION];
    for (i, g) in groups.groups_in_order().iter().enumerate() {
        let mut p = 0u32;
        for (j, &bit) in g.iter().enumerate() {
            if (w >> bit) & 1 == 1 {
                p |= 1u32 << j;
            }
        }
        out[i] = p;
    }
    out
}

/// Coefficients linking the partition's 8 packed-group values to the
/// `(key_s, key_s_complement)` of the decode table, in `groups_in_order()`
/// ordering — `[c(s[0..4]), c(s'[0..4])]`.
///
/// The decode-table key is `pack_half_key(w, side_mask)` — bits at the
/// side's positions packed contiguously into the low bits in **ascending
/// source-position order** (per [`crate::tables::pack_half_key`]). Because
/// every group's bits are contiguous in the source-position order within
/// its side (`s[0]` covers the lowest |s[0]| key positions, `s[1]` covers
/// the next |s[1]|, etc.), each group contributes its packed value to
/// `key_s` (or `key_s_complement`) at the power-of-two offset equal to
/// the count of S-side bits that precede it.
///
/// So (four groups per side under `W = 6`):
///   `key_s            = c[0]·g[0] + c[1]·g[1] + c[2]·g[2] + c[3]·g[3]`
///   `key_s_complement = c[4]·g[4] + c[5]·g[5] + c[6]·g[6] + c[7]·g[7]`
///
/// where `g[i] = packed value of groups_in_order()[i]` and `c[i]` is this
/// function's `i`-th return.
pub const fn round_key_coeffs(groups: &RoundGroups) -> [u32; GROUPS_PER_ROUND_PARTITION] {
    let s = &groups.s;
    let sc = &groups.s_complement;
    [
        1,
        1u32 << s[0].len() as u32,
        1u32 << (s[0].len() + s[1].len()) as u32,
        1u32 << (s[0].len() + s[1].len() + s[2].len()) as u32,
        1,
        1u32 << sc[0].len() as u32,
        1u32 << (sc[0].len() + sc[1].len()) as u32,
        1u32 << (sc[0].len() + sc[1].len() + sc[2].len()) as u32,
    ]
}

/// Pack-key coefficient for the **hi-half** packed `S`-value of a `σ`
/// partition. The lo-half value's coefficient is always `1` (it sits at
/// the low end of the packed key). The hi-half value's coefficient equals
/// `2^|S∩lo|` because the lo-side bits fill the low `|S∩lo|` positions of
/// `key_s` first.
pub const fn lower_sigma_key_hi_coeff_s(parts: &SigmaParts) -> u32 {
    1u32 << parts.s_lo.len() as u32
}

/// Pack-key coefficient for the **hi-half** packed `S'`-value of a `σ`
/// partition. Mirrors [`lower_sigma_key_hi_coeff_s`] for the complementary
/// side.
pub const fn lower_sigma_key_hi_coeff_s_complement(parts: &SigmaParts) -> u32 {
    1u32 << parts.s_complement_lo.len() as u32
}

/// Smoke check that constant `IV` length matches state width.
const _: () = assert!(crate::constants::IV.len() == N_STATE_WORDS);

#[cfg(test)]
mod tests {
    use super::*;

    /// Reproduces Appendix A: each `S` mask has exactly 16 bits, and the
    /// classification matches the documented `O0`/`O1`/`O2` sets.
    #[test]
    fn classification_matches_design() {
        for (f, s, expected) in [
            (SigmaFn::Sigma0, s_mask::SIGMA0, &SIGMA0_OUTPUTS),
            (SigmaFn::Sigma1, s_mask::SIGMA1, &SIGMA1_OUTPUTS),
            (
                SigmaFn::LowerSigma0,
                s_mask::LOWER_SIGMA0,
                &LOWER_SIGMA0_OUTPUTS,
            ),
            (
                SigmaFn::LowerSigma1,
                s_mask::LOWER_SIGMA1,
                &LOWER_SIGMA1_OUTPUTS,
            ),
        ] {
            assert_eq!(s.count_ones(), 16, "{f:?}: S must have 16 bits");

            let (o0, o1, o2) = classify(f, s);
            assert_eq!(o0, expected.o0, "{f:?}: O0 mismatch");
            assert_eq!(o1, expected.o1, "{f:?}: O1 mismatch");
            assert_eq!(o2, expected.o2, "{f:?}: O2 mismatch");

            // O0 ⊎ O1 ⊎ O2 covers all 32 output bits.
            assert_eq!(output_coverage(expected), u32::MAX, "{f:?}: coverage gap");
        }
    }

    /// Reproduces the design's finding F3: the `Σ0` partition equals
    /// `{(11a + 20b) mod 32 : 0 ≤ a, b < 4}`.
    #[test]
    fn sigma0_partition_is_11a_plus_20b_mod_32() {
        let mut from_formula = 0u32;
        for a in 0..4u32 {
            for b in 0..4u32 {
                from_formula |= 1u32 << ((11 * a + 20 * b) % 32);
            }
        }
        assert_eq!(from_formula, s_mask::SIGMA0);
    }

    /// Reproduces the design's finding F5: the analogous `{(5a + 19b) mod 32}`
    /// construction for `Σ1` yields a bad partition with `|O2| = 15`. This is
    /// the negative result that justifies using a custom `Σ1` partition.
    #[test]
    fn sigma1_naive_formula_is_bad() {
        let mut naive = 0u32;
        for a in 0..4u32 {
            for b in 0..4u32 {
                naive |= 1u32 << ((5 * a + 19 * b) % 32);
            }
        }
        let (o0, o1, o2) = classify(SigmaFn::Sigma1, naive);
        assert_eq!((o0.len(), o1.len(), o2.len()), (9, 8, 15));
    }

    #[test]
    fn round_groups_consistent_with_s_masks() {
        assert!(round_groups_consistent(&SIGMA0_GROUPS, s_mask::SIGMA0));
        assert!(round_groups_consistent(&SIGMA1_GROUPS, s_mask::SIGMA1));
    }

    #[test]
    fn sigma_parts_consistent_with_s_masks() {
        assert!(sigma_parts_consistent(
            &LOWER_SIGMA0_PARTS,
            s_mask::LOWER_SIGMA0
        ));
        assert!(sigma_parts_consistent(
            &LOWER_SIGMA1_PARTS,
            s_mask::LOWER_SIGMA1
        ));
    }

    /// Every round-function group is at most `MAX_ROUND_GROUP_BITS = 6` wide,
    /// so a packed `Maj`/`Ch` lookup table of width `W = 6` suffices.
    #[test]
    fn round_groups_within_max_width() {
        for groups in [&SIGMA0_GROUPS, &SIGMA1_GROUPS] {
            for g in groups.s.iter().chain(groups.s_complement.iter()) {
                assert!(
                    g.len() as u32 <= MAX_ROUND_GROUP_BITS,
                    "group too wide: {g:?}"
                );
            }
        }
    }

    /// Pin the `W = 6` sub-group structure: each partition has 8 groups
    /// (4 `S`-side + 4 `S'`-side), every group is `≤ 6` bits and sits
    /// entirely within one 16-bit half, and the union is still `S ⊎ S'`
    /// (so subdividing the 7-bit groups did not change which bits the
    /// `Σ`/`Maj`/`Ch` decode keys on). A regression here is a soundness
    /// hazard — the decode tables are keyed by the full `S`/`S'` masks.
    #[test]
    fn round_groups_subdivided_for_w6() {
        assert_eq!(MAX_ROUND_GROUP_BITS, 6);
        assert_eq!(GROUPS_PER_ROUND_PARTITION, 8);
        for (groups, s) in [
            (&SIGMA0_GROUPS, s_mask::SIGMA0),
            (&SIGMA1_GROUPS, s_mask::SIGMA1),
        ] {
            assert_eq!(groups.s.len(), 4);
            assert_eq!(groups.s_complement.len(), 4);
            for g in groups.s.iter().chain(groups.s_complement.iter()) {
                assert!(!g.is_empty(), "empty group");
                assert!(g.len() as u32 <= 6, "group {g:?} wider than 6 bits");
                let lo = g.iter().all(|&b| b < 16);
                let hi = g.iter().all(|&b| b >= 16);
                assert!(lo || hi, "group {g:?} straddles the 16-bit half boundary");
            }
            // Union is still S ⊎ S' (no bits added, dropped, or moved sides).
            assert!(round_groups_consistent(groups, s));
        }
    }

    /// `groups_in_order` enumerates `S[0..4]` then `S'[0..4]` and matches
    /// what `pack_round_groups` reads — a regression on either would
    /// silently rotate the Maj/Ch lookup keys against the table content.
    #[test]
    fn groups_in_order_lists_eight_groups_s_then_s_complement() {
        for groups in [&SIGMA0_GROUPS, &SIGMA1_GROUPS] {
            let order = groups.groups_in_order();
            assert_eq!(order.len(), GROUPS_PER_ROUND_PARTITION);
            for i in 0..4 {
                assert!(std::ptr::eq(order[i], groups.s[i]));
                assert!(std::ptr::eq(order[4 + i], groups.s_complement[i]));
            }
        }
    }

    /// `round_groups_half_indices` projects `groups_in_order()` onto the
    /// lo/hi 16-bit word halves. Pin the exact projection for both
    /// partitions (it differs per partition) and cross-check that every
    /// listed index really points at a group living in that half. The
    /// constraint side (`wire_round_split_pack`) and the prover side
    /// (`write_round_split_pack_pair`) both key on this projection, so a
    /// drift here breaks the LogUp balance.
    #[test]
    fn round_groups_half_indices_match_sub_group_bit_lists() {
        let (lo0, hi0) = round_groups_half_indices(&SIGMA0_GROUPS);
        assert_eq!(lo0, vec![0, 1, 4, 5]); // L0a, L0b, L1, L2
        assert_eq!(hi0, vec![2, 3, 6, 7]); // H0, H1, H2a, H2b
        let (lo1, hi1) = round_groups_half_indices(&SIGMA1_GROUPS);
        assert_eq!(lo1, vec![0, 4, 5, 6]); // Le0, Le1a, Le1b, Le2
        assert_eq!(hi1, vec![1, 2, 3, 7]); // He0a, He0b, He1, He2

        for groups in [&SIGMA0_GROUPS, &SIGMA1_GROUPS] {
            let order = groups.groups_in_order();
            let (lo, hi) = round_groups_half_indices(groups);
            // Exactly 4 sub-groups per half, partitioning all 8 indices.
            assert_eq!(lo.len(), 4);
            assert_eq!(hi.len(), 4);
            assert!(lo.iter().all(|&i| order[i].iter().all(|&b| b < 16)));
            assert!(hi.iter().all(|&i| order[i].iter().all(|&b| b >= 16)));
            let mut all: Vec<usize> = lo.iter().chain(hi.iter()).copied().collect();
            all.sort_unstable();
            assert_eq!(all, (0..GROUPS_PER_ROUND_PARTITION).collect::<Vec<_>>());
        }
    }

    /// `pack_round_groups` round-trips: spreading each packed group back to
    /// its natural-position bits and OR-ing across all 6 groups recovers the
    /// input word exactly (since `S ⊎ S'` partitions all 32 bits).
    #[test]
    fn pack_round_groups_round_trips_via_natural_positions() {
        for w in [
            0u32,
            1,
            0xFFFF,
            0x1_0000,
            0xDEAD_BEEF,
            0xCAFE_BABE,
            u32::MAX,
        ] {
            for groups in [&SIGMA0_GROUPS, &SIGMA1_GROUPS] {
                let packed = pack_round_groups(w, groups);
                let mut spread = 0u32;
                for (g, &p) in groups.groups_in_order().iter().zip(packed.iter()) {
                    for (j, &bit) in g.iter().enumerate() {
                        if (p >> j) & 1 == 1 {
                            spread |= 1u32 << bit;
                        }
                    }
                }
                assert_eq!(spread, w, "round-trip failed for word {w:#x}");
            }
        }
    }

    /// Every group value `pack_round_groups` emits fits in
    /// `MAX_ROUND_GROUP_BITS` — the upper bound the Maj/Ch table size
    /// `2^(3·W)` is dimensioned against (`W ≥ MAX_ROUND_GROUP_BITS`).
    #[test]
    fn pack_round_groups_values_fit_max_width() {
        let cap = 1u32 << MAX_ROUND_GROUP_BITS;
        for w in [0u32, 0xDEAD_BEEF, u32::MAX] {
            for groups in [&SIGMA0_GROUPS, &SIGMA1_GROUPS] {
                let packed = pack_round_groups(w, groups);
                for (i, &p) in packed.iter().enumerate() {
                    assert!(p < cap, "group {i} value {p} ≥ {cap}");
                }
            }
        }
    }

    /// Linear assembly of the 8 packed groups via `round_key_coeffs`
    /// reproduces `pack_half_key(w, side_mask)` for both sides. This is
    /// the soundness property the AIR's σ-decode-key-pin constraint
    /// depends on: a row with the right packed groups must algebraically
    /// reassemble to the row's committed `key_s` / `key_s_complement`.
    #[test]
    fn round_key_coeffs_reassemble_pack_half_key() {
        use crate::tables::pack_half_key;
        for (groups, s_mask) in [
            (&SIGMA0_GROUPS, s_mask::SIGMA0),
            (&SIGMA1_GROUPS, s_mask::SIGMA1),
        ] {
            let coeffs = round_key_coeffs(groups);
            for w in [
                0u32,
                1,
                0xFFFF,
                0x1_0000,
                0xDEAD_BEEF,
                0xCAFE_BABE,
                0x6A09_E667,
                0xBB67_AE85,
                u32::MAX,
            ] {
                let packed = pack_round_groups(w, groups);
                // S-side reassembly: Σ_{i<4} c[i]·g[i].
                let key_s_built = (0..4).map(|i| coeffs[i] * packed[i]).sum::<u32>();
                assert_eq!(key_s_built, pack_half_key(w, s_mask), "{w:#x} S-side");
                // S'-side reassembly: Σ_{i in 4..8} c[i]·g[i].
                let key_s_complement_built = (4..8).map(|i| coeffs[i] * packed[i]).sum::<u32>();
                assert_eq!(
                    key_s_complement_built,
                    pack_half_key(w, !s_mask),
                    "{w:#x} S'-side"
                );
            }
        }
    }

    /// σ-partition equivalent: `(packed_s_lo + hi_coeff_s · packed_s_hi,
    /// packed_s_complement_lo + hi_coeff_s_complement · packed_s_complement_hi)`
    /// equals `pack_half_key(x, ±s_mask)`. The packed-{lo,hi} values come
    /// from the σ split-and-pack lookups; this test pins the coefficients
    /// to the value `pack_half_key` would produce.
    #[test]
    fn lower_sigma_key_coeffs_reassemble_pack_half_key() {
        use crate::tables::pack_half_key;
        for (parts, s_mask, f) in [
            (
                &LOWER_SIGMA0_PARTS,
                s_mask::LOWER_SIGMA0,
                SigmaFn::LowerSigma0,
            ),
            (
                &LOWER_SIGMA1_PARTS,
                s_mask::LOWER_SIGMA1,
                SigmaFn::LowerSigma1,
            ),
        ] {
            let _ = f; // not used here; only the partition shapes matter.
            let coeff_hi_s = lower_sigma_key_hi_coeff_s(parts);
            let coeff_hi_s_complement = lower_sigma_key_hi_coeff_s_complement(parts);
            for x in [
                0u32,
                1,
                0xFFFF,
                0x1_0000,
                0xDEAD_BEEF,
                0xCAFE_BABE,
                0x6A09_E667,
                0xBB67_AE85,
                u32::MAX,
            ] {
                // Lo-half packed S and S' values.
                let lo = x & 0xFFFF;
                let mut packed_s_lo = 0u32;
                for (i, &pos) in parts.s_lo.iter().enumerate() {
                    if (lo >> pos) & 1 == 1 {
                        packed_s_lo |= 1u32 << i;
                    }
                }
                let mut packed_s_complement_lo = 0u32;
                for (i, &pos) in parts.s_complement_lo.iter().enumerate() {
                    if (lo >> pos) & 1 == 1 {
                        packed_s_complement_lo |= 1u32 << i;
                    }
                }
                // Hi-half packed S and S' values — positions are shifted
                // by 16 (so we read the hi limb as a 0..2¹⁶ value).
                let hi = (x >> 16) & 0xFFFF;
                let mut packed_s_hi = 0u32;
                for (i, &pos) in parts.s_hi.iter().enumerate() {
                    let pos_in_hi = pos - 16;
                    if (hi >> pos_in_hi) & 1 == 1 {
                        packed_s_hi |= 1u32 << i;
                    }
                }
                let mut packed_s_complement_hi = 0u32;
                for (i, &pos) in parts.s_complement_hi.iter().enumerate() {
                    let pos_in_hi = pos - 16;
                    if (hi >> pos_in_hi) & 1 == 1 {
                        packed_s_complement_hi |= 1u32 << i;
                    }
                }
                let key_s_built = packed_s_lo + coeff_hi_s * packed_s_hi;
                assert_eq!(key_s_built, pack_half_key(x, s_mask), "{x:#x} S-side");
                let key_s_complement_built =
                    packed_s_complement_lo + coeff_hi_s_complement * packed_s_complement_hi;
                assert_eq!(
                    key_s_complement_built,
                    pack_half_key(x, !s_mask),
                    "{x:#x} S'-side"
                );
            }
        }
    }

    /// Spot-check the dependency masks reproduce the FIPS spec.
    /// `Σ0(1) = ROTR2(1) ^ ROTR13(1) ^ ROTR22(1) = 2^30 | 2^19 | 2^10`.
    #[test]
    fn dependency_mask_matches_apply() {
        // For any input bit-position k, applying f to (1 << k) marks exactly
        // the output bits that depend on k. So the j-th column of the
        // dependency-mask matrix (mask of input bits each output bit reads)
        // is consistent with apply(f, 1 << k) | apply(f, 1 << k') | ... .
        for f in [
            SigmaFn::Sigma0,
            SigmaFn::Sigma1,
            SigmaFn::LowerSigma0,
            SigmaFn::LowerSigma1,
        ] {
            let dep = dependency_mask(f);
            // Reconstruct by transposing: out_dep[i] = which input bits
            // contribute to output bit i = bits {k : apply(f, 1<<k) has bit i}.
            let mut reconstructed = [0u32; 32];
            for k in 0..32u32 {
                let y = apply(f, 1u32 << k);
                for i in 0..32u32 {
                    if (y >> i) & 1 == 1 {
                        reconstructed[i as usize] |= 1u32 << k;
                    }
                }
            }
            assert_eq!(dep, reconstructed, "{f:?}: dep matrix disagrees with apply");
        }
    }
}
