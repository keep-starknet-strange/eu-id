//! LogUp relation contracts for the `mldsa_decomp` component (M5, [DECOMP]+[HINT]).
//!
//! Cross-component bindings ([`WCellRelation`], [`HashIoRelation`]) live in
//! [`crate::binding`]; this module adds only the four range-table instances the
//! decomp AIR draws for its own use. All drawn together after the base commit.
//!
//! | relation | arity | tuple | provider | consumer |
//! |----------|-------|-------|----------|----------|
//! | `WCell`  | 2 | `(w_bind_id, w)` | coeffs W rows (−1) | decomp (+1) |
//! | `HashIo` | 3 | `(stream_id, byte_pos, byte)` | decomp w1Encode (+1) | sponge/M6 or test (−1) |
//! | `Rc4`    | 1 | `v ∈ [0,2^4)` | rc4 table | w1, w1' |
//! | `Rc13`   | 1 | `v ∈ [0,2^13)` | rc13 table | w0 two-sided lo |
//! | `Rc7`    | 1 | `v ∈ [0,2^7)`  | rc7 table | w0 two-sided hi |
//! | `Rc8`    | 1 | `v ∈ [0,2^8)`  | rc8 table | hint accumulator ≤ ω |

use stwo_constraint_framework::relation;

use crate::binding::{HashIoRelation, WCellRelation};

// Arity-1 range table relation (four independent instances).
relation!(RcRelation, 1);

/// The relations the decomp module draws together after its base commit.
#[derive(Clone)]
pub struct DecompRelations {
    pub wcell: WCellRelation,
    pub hash_io: HashIoRelation,
    pub rc4: RcRelation,
    pub rc13: RcRelation,
    pub rc7: RcRelation,
    pub rc8: RcRelation,
}

impl DecompRelations {
    pub fn draw(channel: &mut impl stwo::core::channel::Channel) -> Self {
        Self {
            wcell: WCellRelation::draw(channel),
            hash_io: HashIoRelation::draw(channel),
            rc4: RcRelation::draw(channel),
            rc13: RcRelation::draw(channel),
            rc7: RcRelation::draw(channel),
            rc8: RcRelation::draw(channel),
        }
    }

    /// Composed-statement constructor (M6): draw only the decomp-private range
    /// tables and reuse SHARED `wcell` (from coeffs) and `hash_io` (from the
    /// c̃-chain sponge) instances so the w-binding and w1Encode absorb bytes
    /// cancel across components. Private draw order matches [`Self::draw`].
    pub fn draw_with(
        channel: &mut impl stwo::core::channel::Channel,
        wcell: WCellRelation,
        hash_io: HashIoRelation,
    ) -> Self {
        Self {
            wcell,
            hash_io,
            rc4: RcRelation::draw(channel),
            rc13: RcRelation::draw(channel),
            rc7: RcRelation::draw(channel),
            rc8: RcRelation::draw(channel),
        }
    }

    pub fn dummy() -> Self {
        Self {
            wcell: WCellRelation::dummy(),
            hash_io: HashIoRelation::dummy(),
            rc4: RcRelation::dummy(),
            rc13: RcRelation::dummy(),
            rc7: RcRelation::dummy(),
            rc8: RcRelation::dummy(),
        }
    }
}
