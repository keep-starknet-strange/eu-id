//! Preprocessed lookup tables for the spread-form Keccak AIR.
//!
//! The Keccak state is carried in **spread form** (`spread(b) = Σ bᵢ·4ⁱ`, see
//! [`crate::utils`]). Four table families, all deterministic and
//! message-agnostic:
//!
//! - `xor3` — dense `2^16 × 2`, `(key, spread(xor))` with `key = s1+s2+s3` the
//!   carry-free base-4 digit-sum of three spread bytes. Every 16-bit `key` is a
//!   valid digit-sum (each base-4 slot 0..3), so the table is dense and its
//!   presence certifies `spread(xor)` is a valid spread value. Serves XOR of 2
//!   or 3 bytes (the 2-input case passes a third input of 0) and, on lane 0,
//!   folds the iota round-constant XOR as its third input.
//! - `andnot` — dense `2^16 × 2`, `(u, spread(¬b'∧b''))` with
//!   `u = spread(b') + 2·spread(b'')` injectively encoding the bit-pair per slot
//!   (slot value 0..3). Replaces the byte-pair `chi` table.
//! - `split_r` for `r ∈ {1..=7}` — spread byte-split range tables, `2^8` rows
//!   `(spread_byte, spread_hi, spread_lo)` with `spread_lo = spread(byte mod
//!   2^r)`, `spread_hi = spread(byte >> r)`. Because spread is additive across
//!   disjoint bit ranges, `spread_byte = spread_hi + spread_lo·4^r`.
//! - `conv` — `2^8 × 2`, `(byte, spread(byte))`. Used only at the HashIo
//!   boundary to convert absorbed message bytes into spread form and squeezed
//!   spread limbs back into bytes. Both directions are certified by the one
//!   dense table (the row pins the `(byte, spread)` pair either way it is keyed).
//!
//! ## Why the tables are self-certifying
//!
//! Each table enumerates exactly the valid rows. A witnessed tuple that is
//! present in a table can only be a canonical row — so a committed value that is
//! a lookup *output* (xor3/andnot result, split hi/lo, conv spread) needs no
//! separate range check: the dense table is the certificate that it is a valid
//! spread value. This mirrors M3's split tables, extended to the spread domain.

use crate::utils::spread_u32;

/// Log2 of a dense base-4 digit-sum table height (`xor3`, `andnot`): 2^16.
pub const LOG_SIZE_DENSE: u32 = 16;
/// Log2 of a split / conv table height (2^8 rows).
pub const LOG_SIZE_SPLIT: u32 = 8;
/// The sub-byte shift amounts that get their own split table.
pub const SPLIT_SHIFTS: [u32; 7] = [1, 2, 3, 4, 5, 6, 7];

/// The merged dense table: `(key, spread(xor), andnot)` over all `2^16` keys.
///
/// Both the xor3 and andnot lookups key a 16-bit value read as 8 base-4 digits
/// `d_i ∈ {0,1,2,3}`, so they share the same dense key space and can be served
/// by a single `2^16`-row table with two output columns:
/// - **xor3**: `key = s1+s2+s3`; output `spread(xor) = Σ (d_i mod 2)·4ⁱ`.
/// - **andnot**: `key = spread(b') + 2·spread(b'')`; per slot
///   `(¬b'∧b'')_i = 1` iff `d_i == 2`.
///
/// Merging halves the dominant fixed `2^16` commitment cost of M3b.
pub fn build_dense_table() -> Vec<[u32; 3]> {
    (0u32..(1 << LOG_SIZE_DENSE))
        .map(|key| {
            let mut xor_out = 0u32;
            let mut andnot_out = 0u32;
            for i in 0..8 {
                let d = (key >> (2 * i)) & 0b11;
                xor_out |= (d & 1) << (2 * i);
                if d == 2 {
                    andnot_out |= 1 << (2 * i);
                }
            }
            [key, xor_out, andnot_out]
        })
        .collect()
}

/// The spread split table for shift `r ∈ {1..=7}`: 256 rows
/// `(spread_byte, spread_hi, spread_lo)` indexed by `byte`, with
/// `spread_hi = spread(byte >> r)` and `spread_lo = spread(byte & (2^r-1))`.
pub fn build_split_table(r: u32) -> Vec<[u32; 3]> {
    assert!((1..=7).contains(&r), "split shift out of range: {r}");
    let lo_mask = (1u32 << r) - 1;
    (0u32..256)
        .map(|byte| {
            [
                spread_u32(byte),
                spread_u32(byte >> r),
                spread_u32(byte & lo_mask),
            ]
        })
        .collect()
}

/// The byte↔spread conversion table: 256 rows `(byte, spread(byte))`.
pub fn build_conv_table() -> Vec<[u32; 2]> {
    (0u32..256).map(|byte| [byte, spread_u32(byte)]).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::{unspread_u32, SPREAD_MAX};

    #[test]
    fn dense_table_matches_native_xor3_and_andnot() {
        let t = build_dense_table();
        assert_eq!(t.len(), 1 << LOG_SIZE_DENSE);
        // xor3: every valid triple hits a row whose xor column is the true xor.
        for &(a, b, c) in &[(0u32, 0u32, 0u32), (0xAB, 0xCD, 0x37), (0xFF, 0xFF, 0xFF), (0x80, 0x01, 0x40)] {
            let key = (spread_u32(a) + spread_u32(b) + spread_u32(c)) as usize;
            assert!(key < t.len(), "key {key} in range (max {})", 3 * SPREAD_MAX);
            let [k, xor_out, _] = t[key];
            assert_eq!(k as usize, key);
            assert_eq!(unspread_u32(xor_out), a ^ b ^ c, "xor3({a:#x},{b:#x},{c:#x})");
        }
        // andnot: key = spread(b')+2·spread(b'') → andnot column.
        for b1 in [0u32, 0x0F, 0xAA, 0xFF, 0x39] {
            for b2 in [0u32, 0xF0, 0x55, 0xFF, 0xC6] {
                let u = (spread_u32(b1) + 2 * spread_u32(b2)) as usize;
                let [k, _, andnot_out] = t[u];
                assert_eq!(k as usize, u);
                assert_eq!(unspread_u32(andnot_out), ((!b1) & b2) & 0xFF, "andnot({b1:#x},{b2:#x})");
            }
        }
        // The maximum key is exactly 2^16-1 (3·0xFF spread), so the table is dense.
        assert_eq!(3 * SPREAD_MAX, (1 << LOG_SIZE_DENSE) - 1);
    }

    #[test]
    fn split_tables_are_canonical_spread() {
        for r in SPLIT_SHIFTS {
            let t = build_split_table(r);
            assert_eq!(t.len(), 1 << LOG_SIZE_SPLIT);
            for (byte, &[sb, shi, slo]) in t.iter().enumerate() {
                assert_eq!(sb, spread_u32(byte as u32), "spread_byte column = spread(row index)");
                // Spread is additive across the disjoint hi/lo bit ranges:
                // spread_byte = spread_hi·4^r + spread_lo (hi occupies the high
                // 8-r bits, lo the low r bits).
                assert_eq!(shi * (1 << (2 * r)) + slo, sb, "spread recombination");
                assert!(unspread_u32(slo) < (1 << r), "lo fits in r bits");
                assert!(unspread_u32(shi) < (1 << (8 - r)), "hi fits in 8-r bits");
            }
        }
    }

    #[test]
    fn conv_table_round_trips() {
        let t = build_conv_table();
        assert_eq!(t.len(), 1 << LOG_SIZE_SPLIT);
        for (byte, &[b, s]) in t.iter().enumerate() {
            assert_eq!(b as usize, byte);
            assert_eq!(s, spread_u32(byte as u32));
            assert_eq!(unspread_u32(s), byte as u32);
        }
    }
}
