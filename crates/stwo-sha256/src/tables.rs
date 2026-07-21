//! Preprocessed lookup-table content for the SHA-256 AIR.
//!
//! Implements §9 of `docs/research/sha256-air-design.md`. Six families of tables
//! live here; all are deterministic functions of the FIPS spec and the
//! validated bit-index partitions:
//!
//! 1. **`Σ`/`σ` decode tables** (8 total: one `S`-side + one `S'`-side per
//!    function). Each has `2¹⁶` rows. Row `k` packs the contribution of one
//!    half of the input to the output word.
//! 2. **Packed `Maj`/`Ch` table** (1). Width-`W` table mapping
//!    `(a_packed, b_packed, c_packed) → (Maj_packed, Ch_packed)` per packed
//!    group. `W` is a tuning knob; the round-function partitions have
//!    group widths ≤ 7, so `W = 7` is the smallest table without padding.
//! 3. **Generic `xor_8` table** (1). `2¹⁶` rows; `(x, y) → x ⊕ y` for
//!    8-bit `x`, `y`. Used to combine the two `O2` partials chunk-wise.
//! 4. **Split-and-pack tables** (8: one per partition × lo/hi half).
//!    Maps a 16-bit half-word to the packed-group values its bits land in.
//!
//! Every row that crosses into the trace is an `M31` value in `[0, 2¹⁶)`
//! (limb-bounded) or `[0, 2^W)` (packed-bounded). Field range checks for
//! free, per §11 lesson L1.

use crate::native::{big_sigma0, big_sigma1, ch, lower_sigma0, lower_sigma1, maj};
use crate::partitions::{
    bits_to_mask, OutputClassification, RoundGroups, SigmaFn, SigmaParts, LOWER_SIGMA0_PARTS,
    LOWER_SIGMA1_PARTS, SIGMA0_GROUPS, SIGMA1_GROUPS,
};
use crate::types::{LIMB_BITS, LIMB_MAX};

/// Number of rows in every `Σ`/`σ` decode table and in the `xor_8_8` table.
pub const DECODE_TABLE_ROWS: usize = 1 << 16;

/// One row of a `Σ`/`σ` decode table.
///
/// For an `S`-side table (the half that contributes `O0` plus part of `O2`):
/// - `key` ∈ `[0, 2¹⁶)`: the 16 input bits at positions in `S`, packed
///   contiguously in ascending order.
/// - `o_main_lo`/`o_main_hi`: the `O0` output bits at their *natural* word
///   positions, split lo/hi (every limb stays `< 2¹⁶`).
/// - `o2_partial_lo`/`o2_partial_hi`: the `O2` partial-XOR contribution from
///   this side, at natural positions, split lo/hi.
///
/// `S'`-side tables have the same shape but `o_main_*` carries the `O1` bits.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct DecodeRow {
    pub key: u32,
    pub o_main_lo: u32,
    pub o_main_hi: u32,
    pub o2_partial_lo: u32,
    pub o2_partial_hi: u32,
}

/// Which half of an `S` ⊎ `S'` partition this row encodes.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Half {
    /// The 16-bit `S` half — contributes `O0` plus a partial `O2`.
    S,
    /// The 16-bit `S'` half — contributes `O1` plus a partial `O2`.
    SComplement,
}

/// Build one decode table (`2¹⁶` rows) for `f` × `half`.
pub fn build_decode_table(f: SigmaFn, half: Half) -> Vec<DecodeRow> {
    let s_mask = f.s_mask();
    let active_mask = match half {
        Half::S => s_mask,
        Half::SComplement => !s_mask,
    };
    let positions = positions_in_mask(active_mask);
    debug_assert_eq!(positions.len(), 16, "every half has exactly 16 active bits");

    let outputs = f.outputs();
    let (main_bits, _) = match half {
        Half::S => (outputs.o0, outputs.o1),
        Half::SComplement => (outputs.o1, outputs.o0),
    };
    let o_main_mask = bits_to_mask(main_bits);
    let o2_mask = bits_to_mask(outputs.o2);

    let mut rows = Vec::with_capacity(DECODE_TABLE_ROWS);
    for key in 0..DECODE_TABLE_ROWS as u32 {
        // Reconstruct the partial input word w_half: `key` bits scattered to
        // the half's natural positions, every other bit zero.
        let mut w_half = 0u32;
        for (i, &pos) in positions.iter().enumerate() {
            if (key >> i) & 1 == 1 {
                w_half |= 1u32 << pos;
            }
        }

        // Apply f to this partial input. Because f is GF(2)-linear, the
        // O0/O1 output bits (whose dependency is entirely in S or S') get
        // their true values; the O2 output bits get this side's contribution.
        let y = sigma_apply(f, w_half);
        let o_main = y & o_main_mask;
        let o2_part = y & o2_mask;

        rows.push(DecodeRow {
            key,
            o_main_lo: o_main & LIMB_MAX,
            o_main_hi: (o_main >> LIMB_BITS) & LIMB_MAX,
            o2_partial_lo: o2_part & LIMB_MAX,
            o2_partial_hi: (o2_part >> LIMB_BITS) & LIMB_MAX,
        });
    }
    rows
}

/// The `Σ`/`σ` function evaluator — wired here too so this module doesn't
/// have to know how `SigmaFn` maps to the natives.
fn sigma_apply(f: SigmaFn, w: u32) -> u32 {
    match f {
        SigmaFn::Sigma0 => big_sigma0(w),
        SigmaFn::Sigma1 => big_sigma1(w),
        SigmaFn::LowerSigma0 => lower_sigma0(w),
        SigmaFn::LowerSigma1 => lower_sigma1(w),
    }
}

/// Pack the 16 active bits of `key`-into-`half` so the resulting packed key
/// is what the corresponding decode table is indexed by. Used by the witness
/// generator (it has the full 32-bit input word and needs the table key).
pub fn pack_half_key(word: u32, active_mask: u32) -> u32 {
    let positions = positions_in_mask(active_mask);
    let mut packed = 0u32;
    for (i, &pos) in positions.iter().enumerate() {
        let bit = (word >> pos) & 1;
        packed |= bit << i;
    }
    packed
}

/// Sorted (ascending) list of bit positions where `mask` is 1.
pub fn positions_in_mask(mask: u32) -> Vec<u32> {
    (0..32).filter(|i| (mask >> i) & 1 == 1).collect()
}

/// One row of the packed `Maj`/`Ch` table at width `W`.
///
/// `a`, `b`, `c` are `[0, 2^W)` packed-group values; the output is
/// `(maj, ch)` of those bit-triples, also `[0, 2^W)`-bounded. The same
/// table serves any group position because both `Maj` and `Ch` are bitwise.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct MajChRow {
    pub a: u32,
    pub b: u32,
    pub c: u32,
    pub maj_val: u32,
    pub ch_val: u32,
}

/// Largest packed-group width `W` the Maj/Ch table supports. The table has
/// `2^(3·W)` rows, so `W = 8` is already `2²⁴ ≈ 16.8 M` rows; anything
/// larger is "oversized" and almost certainly a mis-tuned config. Together
/// with [`crate::partitions::MAX_ROUND_GROUP_BITS`] (the lower bound) this
/// brackets the legal `group_width` range `[MAX_ROUND_GROUP_BITS,
/// MAX_GROUP_WIDTH]`. The verifier reuses this bound to reject a malformed
/// `proof.group_width` before it can reach the `assert!` below.
pub const MAX_GROUP_WIDTH: u32 = 8;

/// Build the `(2^W)³` row packed `Maj`/`Ch` table.
///
/// `group_width` must be at least
/// [`crate::partitions::MAX_ROUND_GROUP_BITS`] — every packed-group value
/// the witness emits is in `[0, 2^|group|) ⊆ [0, 2^MAX_ROUND_GROUP_BITS)`,
/// so a smaller `W` would not cover the witness's lookup keys. The default
/// is `W = 6` (`2¹⁸` rows): the round partitions subdivide their 7-bit
/// groups into ≤6-bit sub-groups (design §9.2; smaller sub-groups pad with
/// leading zeros into the same table).
pub fn build_maj_ch_table(group_width: u32) -> Vec<MajChRow> {
    assert!(
        group_width <= MAX_GROUP_WIDTH,
        "group_width > {MAX_GROUP_WIDTH} generates an oversized table; tune W down"
    );
    assert!(
        group_width >= crate::partitions::MAX_ROUND_GROUP_BITS,
        "group_width {} below the partitions' max group width ({}); \
         every packed group must be ≤ W bits to key the table",
        group_width,
        crate::partitions::MAX_ROUND_GROUP_BITS,
    );
    let n = 1u32 << group_width;
    let mut rows = Vec::with_capacity((n as usize).pow(3));
    for a in 0..n {
        for b in 0..n {
            for c in 0..n {
                rows.push(MajChRow {
                    a,
                    b,
                    c,
                    maj_val: maj(a, b, c) & (n - 1),
                    ch_val: ch(a, b, c) & (n - 1),
                });
            }
        }
    }
    rows
}

/// One row of the generic `xor_8_8` table.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Xor8Row {
    pub x: u32,
    pub y: u32,
    pub z: u32, // = x ^ y
}

/// `2¹⁶` rows. Each row keyed by `(x, y)` in `[0, 256)²` packed as
/// `y · 256 + x`.
pub fn build_xor_8_table() -> Vec<Xor8Row> {
    let mut rows = Vec::with_capacity(256 * 256);
    for y in 0..256u32 {
        for x in 0..256u32 {
            rows.push(Xor8Row { x, y, z: x ^ y });
        }
    }
    rows
}

/// Lo vs. hi 16-bit half of a 32-bit word.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Half16 {
    Lo,
    Hi,
}

/// Identifier of one preprocessed table. The AIR consumes each by tag; the
/// integration layer (interface contract item 2) is where these names get
/// agreed across streams. Kept generic here so the names can change without
/// touching constraint code.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum TableId {
    Decode(SigmaFn, Half),
    MajCh(u32 /* group_width */),
    Xor8,
}

/// Which round-function partition (`a`-side for `Σ0` + `Maj`, or `e`-side
/// for `Σ1` + `Ch`).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum RoundPartition {
    Sigma0AndMaj,
    Sigma1AndCh,
}

impl RoundPartition {
    pub fn groups(self) -> &'static RoundGroups {
        match self {
            RoundPartition::Sigma0AndMaj => &SIGMA0_GROUPS,
            RoundPartition::Sigma1AndCh => &SIGMA1_GROUPS,
        }
    }

    pub fn s_mask(self) -> u32 {
        match self {
            RoundPartition::Sigma0AndMaj => crate::partitions::s_mask::SIGMA0,
            RoundPartition::Sigma1AndCh => crate::partitions::s_mask::SIGMA1,
        }
    }
}

/// Which message-schedule `σ` partition (`σ0` or `σ1`).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum LowerSigmaPartition {
    LowerSigma0,
    LowerSigma1,
}

impl LowerSigmaPartition {
    pub fn parts(self) -> &'static SigmaParts {
        match self {
            LowerSigmaPartition::LowerSigma0 => &LOWER_SIGMA0_PARTS,
            LowerSigmaPartition::LowerSigma1 => &LOWER_SIGMA1_PARTS,
        }
    }
}

/// Helper used by the round witness: given an output classification, return
/// the natural-position bitmask of `O0`/`O1`/`O2`.
pub fn output_masks(c: &OutputClassification) -> (u32, u32, u32) {
    (bits_to_mask(c.o0), bits_to_mask(c.o1), bits_to_mask(c.o2))
}

/// Convenience: build *both* decode tables for one function (`S` and `S'`).
pub fn build_decode_tables(f: SigmaFn) -> [Vec<DecodeRow>; 2] {
    [
        build_decode_table(f, Half::S),
        build_decode_table(f, Half::SComplement),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::partitions::{apply, classify, dependency_mask};

    /// For every function, summing the spread O0/O1 bits and the XOR of the
    /// two O2 partials reproduces the true Σ/σ output. This is the
    /// reassembly identity that the AIR will rely on as a linear constraint.
    #[test]
    fn decode_tables_reassemble_full_output() {
        for f in [
            SigmaFn::Sigma0,
            SigmaFn::Sigma1,
            SigmaFn::LowerSigma0,
            SigmaFn::LowerSigma1,
        ] {
            // Sample a few words; full 2^32 enumeration is overkill given the
            // GF(2)-linearity proof in the design doc, but a representative
            // sample catches accidental masking errors.
            for w in [
                0u32,
                1,
                0xFFFF,
                0x1_0000,
                0xDEAD_BEEF,
                0xCAFE_BABE,
                0x6A09_E667,
                0xBB67_AE85,
                0x428A_2F98,
                u32::MAX,
            ] {
                let key_s = pack_half_key(w, f.s_mask());
                let key_s_complement = pack_half_key(w, !f.s_mask());
                let row_s = build_decode_row(f, Half::S, key_s);
                let row_sc = build_decode_row(f, Half::SComplement, key_s_complement);

                let o0 = row_s.o_main_lo | (row_s.o_main_hi << LIMB_BITS);
                let o1 = row_sc.o_main_lo | (row_sc.o_main_hi << LIMB_BITS);
                let o2_s = row_s.o2_partial_lo | (row_s.o2_partial_hi << LIMB_BITS);
                let o2_sc = row_sc.o2_partial_lo | (row_sc.o2_partial_hi << LIMB_BITS);

                // Field reassembly per the design: spread parts add, the
                // two O2 partials XOR.
                let reassembled = o0 + o1 + (o2_s ^ o2_sc);
                assert_eq!(reassembled, apply(f, w), "{f:?} reassembly @ {w:#x}");
            }
        }
    }

    /// Spot-check a single decode-table row against the construction.
    fn build_decode_row(f: SigmaFn, half: Half, key: u32) -> DecodeRow {
        let positions = positions_in_mask(match half {
            Half::S => f.s_mask(),
            Half::SComplement => !f.s_mask(),
        });
        let mut w_half = 0u32;
        for (i, &pos) in positions.iter().enumerate() {
            if (key >> i) & 1 == 1 {
                w_half |= 1u32 << pos;
            }
        }
        let outputs = f.outputs();
        let (main_bits, _) = match half {
            Half::S => (outputs.o0, outputs.o1),
            Half::SComplement => (outputs.o1, outputs.o0),
        };
        let o_main_mask = bits_to_mask(main_bits);
        let o2_mask = bits_to_mask(outputs.o2);
        let y = sigma_apply(f, w_half);
        DecodeRow {
            key,
            o_main_lo: (y & o_main_mask) & LIMB_MAX,
            o_main_hi: ((y & o_main_mask) >> LIMB_BITS) & LIMB_MAX,
            o2_partial_lo: (y & o2_mask) & LIMB_MAX,
            o2_partial_hi: ((y & o2_mask) >> LIMB_BITS) & LIMB_MAX,
        }
    }

    #[test]
    fn maj_ch_table_at_w7_is_bitwise() {
        let rows = build_maj_ch_table(7);
        // Spot-check the corners.
        assert_eq!(rows.len(), 128 * 128 * 128);
        // (0, 0, 0) -> (0, 0)
        assert_eq!(rows[0].maj_val, 0);
        assert_eq!(rows[0].ch_val, 0);
        // (127, 127, 127) -> (127, 127)
        let last = rows.last().unwrap();
        assert_eq!(last.maj_val, 127);
        assert_eq!(last.ch_val, 127);
        // A random midpoint, computed via the natives directly.
        let a = 0b1010101;
        let b = 0b1100110;
        let c = 0b0011011;
        let idx = ((a as usize) * 128 + b as usize) * 128 + c as usize;
        assert_eq!(rows[idx].maj_val, maj(a, b, c) & 0x7F);
        assert_eq!(rows[idx].ch_val, ch(a, b, c) & 0x7F);
    }

    #[test]
    fn xor_8_table_is_complete() {
        let rows = build_xor_8_table();
        assert_eq!(rows.len(), 256 * 256);
        for row in &rows {
            assert_eq!(row.z, row.x ^ row.y);
        }
    }

    #[test]
    fn classify_and_output_masks_consistent() {
        for f in [
            SigmaFn::Sigma0,
            SigmaFn::Sigma1,
            SigmaFn::LowerSigma0,
            SigmaFn::LowerSigma1,
        ] {
            let (o0_masks, o1_masks, o2_masks) = output_masks(f.outputs());
            let (o0, o1, o2) = classify(f, f.s_mask());
            assert_eq!(o0_masks, bits_to_mask(&o0));
            assert_eq!(o1_masks, bits_to_mask(&o1));
            assert_eq!(o2_masks, bits_to_mask(&o2));
        }
    }

    /// Smoke: dependency_mask of each function is consistent with what the
    /// table generators read from the partitions.
    #[test]
    fn dependency_mask_aligns_with_outputs() {
        for f in [
            SigmaFn::Sigma0,
            SigmaFn::Sigma1,
            SigmaFn::LowerSigma0,
            SigmaFn::LowerSigma1,
        ] {
            let dep = dependency_mask(f);
            for i in 0..32 {
                let d = dep[i as usize];
                // Output bit i belongs to O0 iff d ⊆ S; O1 iff d ⊆ S'; else O2.
                let outputs = f.outputs();
                if d & f.s_mask() == d {
                    assert!(outputs.o0.contains(&i), "{f:?} bit {i} should be in O0");
                } else if d & !f.s_mask() == d {
                    assert!(outputs.o1.contains(&i), "{f:?} bit {i} should be in O1");
                } else {
                    assert!(outputs.o2.contains(&i), "{f:?} bit {i} should be in O2");
                }
            }
        }
    }
}
