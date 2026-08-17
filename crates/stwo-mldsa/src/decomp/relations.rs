//! LogUp relation contracts for the `mldsa_decomp` component.
//!
//! Cross-component bindings ([`WCellRelation`], [`HashIoRelation`]) live in
//! [`crate::binding`]; this module adds only the shared range-table instance
//! the decomp AIR draws for its own use. Decomp draws all relations together
//! after the base commit.
//!
//! | relation | arity | tuple | provider | consumer |
//! |----------|-------|-------|----------|----------|
//! | `WCell`  | 2 | `(w_bind_id, w)` | coeffs W rows (−1) | decomp (+1) |
//! | `HashIo` | 3 | `(stream_id, byte_pos, byte)` | decomp w1Encode (+1) | sponge or test (−1) |
//! | `Range`  | 2 | `(value, bound_id)` | shared range table (yield `−mult`) | w1/w1' (Rc4), w0 two-sided lo/hi (Rc13/Rc7), hint accumulator ≤ ω (Rc8) |
//!
//! C5 folded decomp's four private per-kind tables (`Rc4`, `Rc13`, `Rc7`,
//! `Rc8`) into [`crate::coeffs::relations::RangeRelation`], the same
//! proof-wide `(value, bound_id)` table `coeffs` / `ExpandA` /
//! `private_key_eval` already share. Every decomp lookup now carries its
//! [`crate::coeffs::tables::RcKind`] bound id as the tuple's second slot.

use crate::binding::{HashIoRelation, WCellRelation};
use crate::coeffs::relations::RangeRelation;

/// The relations the decomp module draws together after its base commit.
#[derive(Clone)]
pub struct DecompRelations {
    pub wcell: WCellRelation,
    pub hash_io: HashIoRelation,
    pub range: RangeRelation,
}

impl DecompRelations {
    pub fn draw(channel: &mut impl stwo::core::channel::Channel) -> Self {
        Self {
            wcell: WCellRelation::draw(channel),
            hash_io: HashIoRelation::draw(channel),
            range: RangeRelation::draw(channel),
        }
    }

    /// Composed-statement constructor. Every field decomp needs is a SHARED
    /// instance drawn once by the caller: `wcell` (from coeffs), `hash_io`
    /// (from the c̃-chain sponge), and `range` (the proof-wide range table,
    /// C5). Decomp itself draws nothing private, so there is no channel
    /// parameter here (unlike [`Self::draw`], which draws every field
    /// independently for standalone testing).
    pub fn draw_with(wcell: WCellRelation, hash_io: HashIoRelation, range: RangeRelation) -> Self {
        Self {
            wcell,
            hash_io,
            range,
        }
    }

    pub fn dummy() -> Self {
        Self {
            wcell: WCellRelation::dummy(),
            hash_io: HashIoRelation::dummy(),
            range: RangeRelation::dummy(),
        }
    }
}
