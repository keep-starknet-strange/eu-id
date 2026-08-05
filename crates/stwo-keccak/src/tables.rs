//! Preprocessed lookup tables for the spread-form Keccak AIR.
//!
//! The Keccak state is carried in **spread form** (`spread(b) = Σ bᵢ·4ⁱ`, see
//! [`crate::utils`]). Four table families, all deterministic and
//! message-agnostic:
//!
//! - `xor3`: dense `2^16 × 2`, `(key, spread(xor))` with `key = s1+s2+s3`, the
//!   carry-free base-4 digit-sum of three spread bytes. Every 16-bit `key` is a
//!   valid digit-sum (each base-4 slot 0..3), so the table is dense and its
//!   presence certifies `spread(xor)` is a valid spread value. Serves XOR of 2
//!   or 3 bytes (the 2-input case passes a third input of 0) and, on lane 0,
//!   folds the iota round-constant XOR as its third input. The chi step's
//!   `andnot = ¬b'∧b''` output retargets onto this same table via the identity
//!   `spread(b'⊕b'') = 2·spread(¬b'∧b'') + spread(b') − spread(b'')`: keying the
//!   row by `spread(b')+spread(b'')` (a genuine 2-input xor3 key) certifies the
//!   derived `spread(b'⊕b'')` expression is a valid spread value, which in turn
//!   pins `spread(¬b'∧b'')` (the committed andnot column) without a dedicated
//!   `andnot` relation or table column.
//! - `split_r` for `r ∈ {1..=7}`: spread byte-split range tables with `2^8` rows
//!   `(spread_byte, spread_hi)` with `spread_hi = spread(byte >> r)`. Because
//!   spread is additive across disjoint bit ranges, `spread_byte = spread_hi·4^r
//!   + spread_lo`, so `spread_lo = spread_byte − spread_hi·4^r` is a derived
//!   linear expression, not a committed column.
//! - `conv`: `2^8 × 2`, `(byte, spread(byte))`. Used only at the HashIo
//!   boundary to convert absorbed message bytes into spread form and squeezed
//!   spread limbs back into bytes. Both directions are certified by the one
//!   dense table (the row pins the `(byte, spread)` pair either way it is keyed).
//!
//! ## Why the tables are self-certifying
//!
//! Each table enumerates the valid rows. A tuple in a table is a canonical row.
//! Thus, a lookup output does not need a separate range check. This applies to
//! xor3 and andnot results, split outputs, and conv spread values.

use crate::utils::spread_u32;

/// Log2 of a dense base-4 digit-sum table height (`xor3`, `andnot`): 2^16.
pub const LOG_SIZE_DENSE: u32 = 16;
/// Log2 of a split / conv table height (2^8 rows).
pub const LOG_SIZE_SPLIT: u32 = 8;
/// The sub-byte shift amounts that get their own split table.
pub const SPLIT_SHIFTS: [u32; 7] = [1, 2, 3, 4, 5, 6, 7];

/// The dense table: `(key, spread(xor))` over all `2^16` keys.
///
/// `key = s1+s2+s3` reads as 8 base-4 digits `d_i ∈ {0,1,2,3}`; every 16-bit
/// key is a valid digit-sum, so the table is dense. `xor_out = Σ (d_i mod
/// 2)·4ⁱ`. The chi step's `andnot` lookup retargets onto this same table (see
/// module docs); it needs no dedicated output column.
pub fn build_dense_table() -> Vec<[u32; 2]> {
    (0u32..(1 << LOG_SIZE_DENSE))
        .map(|key| {
            let mut xor_out = 0u32;
            for i in 0..8 {
                let d = (key >> (2 * i)) & 0b11;
                xor_out |= (d & 1) << (2 * i);
            }
            [key, xor_out]
        })
        .collect()
}

/// The spread split table for shift `r ∈ {1..=7}`: 256 rows
/// `(spread_byte, spread_hi)` indexed by `byte`, with
/// `spread_hi = spread(byte >> r)`. `spread_lo = spread_byte − spread_hi·4^r`
/// is derived at each lookup site, not stored.
pub fn build_split_table(r: u32) -> Vec<[u32; 2]> {
    assert!((1..=7).contains(&r), "split shift out of range: {r}");
    (0u32..256)
        .map(|byte| [spread_u32(byte), spread_u32(byte >> r)])
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
    fn dense_table_matches_native_xor3() {
        let t = build_dense_table();
        assert_eq!(t.len(), 1 << LOG_SIZE_DENSE);
        // xor3: every valid triple hits a row whose xor column is the true xor.
        for &(a, b, c) in &[
            (0u32, 0u32, 0u32),
            (0xAB, 0xCD, 0x37),
            (0xFF, 0xFF, 0xFF),
            (0x80, 0x01, 0x40),
        ] {
            let key = (spread_u32(a) + spread_u32(b) + spread_u32(c)) as usize;
            assert!(key < t.len(), "key {key} in range (max {})", 3 * SPREAD_MAX);
            let [k, xor_out] = t[key];
            assert_eq!(k as usize, key);
            assert_eq!(
                unspread_u32(xor_out),
                a ^ b ^ c,
                "xor3({a:#x},{b:#x},{c:#x})"
            );
        }
        // The maximum key is exactly 2^16-1 (3·0xFF spread), so the table is dense.
        assert_eq!(3 * SPREAD_MAX, (1 << LOG_SIZE_DENSE) - 1);
    }

    /// Exhaustive check of the andnot-onto-xor3 retarget identity, over every
    /// one of the `2^16` `(b1, b2)` byte pairs: `spread(b1⊕b2) =
    /// 2·spread(¬b1∧b2) + spread(b1) − spread(b2)`. This is the algebraic fact
    /// that lets the chi step's `andnot` column be certified by a dense-table
    /// row keyed `spread(b1)+spread(b2)` instead of a dedicated `andnot`
    /// relation/table column.
    #[test]
    fn andnot_retargets_onto_xor3_identity_exhaustive() {
        for b1 in 0u32..256 {
            for b2 in 0u32..256 {
                let andnot = (!b1) & b2 & 0xFF;
                let lhs = spread_u32(b1 ^ b2) as i64;
                let rhs = 2 * spread_u32(andnot) as i64 + spread_u32(b1) as i64
                    - spread_u32(b2) as i64;
                assert_eq!(lhs, rhs, "b1={b1:#x} b2={b2:#x}");
            }
        }
    }

    #[test]
    fn split_tables_are_canonical_spread() {
        for r in SPLIT_SHIFTS {
            let t = build_split_table(r);
            assert_eq!(t.len(), 1 << LOG_SIZE_SPLIT);
            for (byte, &[sb, shi]) in t.iter().enumerate() {
                assert_eq!(
                    sb,
                    spread_u32(byte as u32),
                    "spread_byte column = spread(row index)"
                );
                // spread_lo is derived, not stored: spread_byte = spread_hi·4^r
                // + spread_lo (hi occupies the high 8-r bits, lo the low r bits).
                let slo = sb - shi * (1 << (2 * r));
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
