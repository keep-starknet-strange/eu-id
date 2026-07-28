//! Small helpers retained from the retired SHA-256 lookup-table builders.
//!
//! The live AIR no longer commits the decode, Maj/Ch, or xor_8 tables. The
//! relation draws for those legacy channels remain frozen in `relations.rs`;
//! this module keeps only helpers still used by witness construction and
//! structural verifier gates.

/// Which half of an `S` union `S'` partition a packed key encodes.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Half {
    /// The 16-bit `S` half.
    S,
    /// The 16-bit `S'` half.
    SComplement,
}

/// Largest historical packed-group width the standalone verifier accepts.
///
/// This is a structural cap on proof metadata, kept for wire compatibility with
/// the existing `group_width` field. It no longer sizes a committed Maj/Ch
/// table.
pub const MAX_GROUP_WIDTH: u32 = 8;

/// Pack the active bits of `word` under `active_mask` into contiguous low bits.
pub fn pack_half_key(word: u32, active_mask: u32) -> u32 {
    let positions = positions_in_mask(active_mask);
    let mut packed = 0u32;
    for (i, &pos) in positions.iter().enumerate() {
        let bit = (word >> pos) & 1;
        packed |= bit << i;
    }
    packed
}

/// Sorted ascending bit positions where `mask` is 1.
pub fn positions_in_mask(mask: u32) -> Vec<u32> {
    (0..32).filter(|i| (mask >> i) & 1 == 1).collect()
}
