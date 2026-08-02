//! Preprocessed lookup tables for the spread-form sponge AIR.
//!
//! The Keccak state is carried in **spread form** (`spread(b) = Σ bᵢ·4ⁱ`, see
//! [`crate::utils`]). Both tables are deterministic and message-independent:
//!
//! - `xor3`: dense `2^16 × 2`, `(key, spread(xor))` with `key = s1+s2+s3`, the
//!   carry-free base-4 digit-sum of three spread bytes. Every 16-bit `key` is a
//!   valid digit-sum (each base-4 slot 0..3), so the table is dense and its
//!   presence certifies `spread(xor)` is a valid spread value. Serves XOR of 2
//!   or 3 bytes. The 2-input case uses zero as the third input.
//! - `conv`: `2^8 × 2`, `(byte, spread(byte))`. Binds every committed absorb
//!   block byte to spread form and converts squeezed spread limbs back into
//!   bytes at the HashIo boundary.

use crate::utils::spread_u32;

/// Log2 of the XOR table height.
pub const LOG_SIZE_XOR3: u32 = 16;
/// Log2 of the byte-conversion table height.
pub const LOG_SIZE_CONV: u32 = 8;

/// The XOR table: `(key, spread(xor))` over all 16-bit keys.
pub fn build_xor3_table() -> Vec<[u32; 2]> {
    (0u32..(1 << LOG_SIZE_XOR3))
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

/// The byte↔spread conversion table: 256 rows `(byte, spread(byte))`.
pub fn build_conv_table() -> Vec<[u32; 2]> {
    (0u32..256).map(|byte| [byte, spread_u32(byte)]).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::{unspread_u32, SPREAD_MAX};

    #[test]
    fn xor3_table_is_canonical() {
        let table = build_xor3_table();
        assert_eq!(table.len(), 1 << LOG_SIZE_XOR3);

        for (key, &[stored_key, xor_out]) in table.iter().enumerate() {
            assert_eq!(stored_key as usize, key);
            for digit in 0..8 {
                assert_eq!(
                    (xor_out >> (2 * digit)) & 0b11,
                    ((key as u32) >> (2 * digit)) & 1,
                    "digit {digit} for key {key}"
                );
            }
        }

        for &(a, b, c) in &[
            (0u32, 0u32, 0u32),
            (0xAB, 0xCD, 0x37),
            (0xFF, 0xFF, 0xFF),
            (0x80, 0x01, 0x40),
        ] {
            let key = (spread_u32(a) + spread_u32(b) + spread_u32(c)) as usize;
            assert!(
                key < table.len(),
                "key {key} in range (max {})",
                3 * SPREAD_MAX
            );
            let [k, xor_out] = table[key];
            assert_eq!(k as usize, key);
            assert_eq!(
                unspread_u32(xor_out),
                a ^ b ^ c,
                "xor3({a:#x},{b:#x},{c:#x})"
            );
        }
        assert_eq!(3 * SPREAD_MAX, (1 << LOG_SIZE_XOR3) - 1);
    }

    #[test]
    fn conv_table_round_trips() {
        let table = build_conv_table();
        assert_eq!(table.len(), 1 << LOG_SIZE_CONV);
        for (byte, &[b, s]) in table.iter().enumerate() {
            assert_eq!(b as usize, byte);
            assert_eq!(s, spread_u32(byte as u32));
            assert_eq!(unspread_u32(s), byte as u32);
        }
    }
}
