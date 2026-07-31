//! LogUp relation contracts for the `mldsa_coeffs` component.
//!
//! | relation | arity | tuple | providers | consumers |
//! |----------|-------|-------|-----------|-----------|
//! | `EvalAtRs`  | 5 | `(poly_id, e0,e1,e2,e3)` | coeffs group-end (yield `−end`) | verifier-native fold (use `+`) |
//! | `Range`     | 2 | `(value, bound_id)` | combined range table (yield `−mult`) | coeffs range uses |
//!
//! The digit range uses a dedicated `2^9` table with offset `+2^8`
//! and does not use a scaled `Rc13` lookup. Carry range checks enforce
//! `|C| ≤ 2^20` through a 13+8 split of `C + 2^20 ∈ [0,2^21)`. The z-norm
//! check enforces `≤ γ1−β−1` through symmetric two-sided offsets. It uses
//! `Rc13` for the low part and `Rc7` for the high part.

use air_core::relations::SharedRelation;
use stwo::core::fields::qm31::SECURE_EXTENSION_DEGREE;
use stwo_constraint_framework::relation;

use crate::binding::{CCellRelation, WCellRelation};

/// `(poly_id, e0, e1, e2, e3)` — the claimed `P̂(r,s)` QM31 eval as 4 M31 coords.
pub const EVAL_ARITY: usize = 1 + SECURE_EXTENSION_DEGREE;
relation!(EvalAtRsRelation, EVAL_ARITY);

// The bound id is the SECOND tuple slot everywhere. It is always a literal or a
// constant-weighted preprocessed selector, never witness-controlled. This
// namespaces the five domains while letting disjoint row kinds share streams.
relation!(RangeRelation, 2);

/// Proof-wide range relation used by hosted ML-DSA instances.
pub type SharedRangeRelation = SharedRelation<RangeRelation>;

/// The relations, drawn together after the base commit.
///
/// `wcell` and `ccell` are cross-component bindings. The coeffs component
/// YIELDS `(w_bind_id, w)` for every w-coefficient and `(c_bind_id, c)` for every
/// challenge coefficient; decomp / sampleinball consume them. In the standalone
/// coeffs test these two yields would be unbalanced (no consumer), so the
/// standalone test wires a test-side balancer against the SAME instances (see
/// [`crate::balancer`]); the composed statement lets decomp / sampleinball close
/// them.
#[derive(Clone)]
pub struct CoeffsRelations {
    pub eval: EvalAtRsRelation,
    pub range: RangeRelation,
    pub wcell: WCellRelation,
    pub ccell: CCellRelation,
}

impl CoeffsRelations {
    pub fn draw(channel: &mut impl stwo::core::channel::Channel) -> Self {
        Self {
            eval: EvalAtRsRelation::draw(channel),
            range: RangeRelation::draw(channel),
            wcell: WCellRelation::draw(channel),
            ccell: CCellRelation::draw(channel),
        }
    }

    /// Composed-statement constructor. Draw only the coefficient-private
    /// relations from the channel and reuse SHARED `wcell` / `ccell` instances
    /// (drawn once by [`crate::statement`]) so the binding yields cancel against
    /// decomp / sampleinball. Draw order of the private relations matches
    /// [`Self::draw`].
    pub fn draw_with(
        channel: &mut impl stwo::core::channel::Channel,
        wcell: WCellRelation,
        ccell: CCellRelation,
    ) -> Self {
        Self {
            eval: EvalAtRsRelation::draw(channel),
            range: RangeRelation::draw(channel),
            wcell,
            ccell,
        }
    }

    /// Hosted constructor: draw only the instance-private eval relation and
    /// reuse the proof-wide range relation published by the shared table.
    pub fn draw_with_range(
        channel: &mut impl stwo::core::channel::Channel,
        range: RangeRelation,
        wcell: WCellRelation,
        ccell: CCellRelation,
    ) -> Self {
        Self {
            eval: EvalAtRsRelation::draw(channel),
            range,
            wcell,
            ccell,
        }
    }

    pub fn dummy() -> Self {
        Self {
            eval: EvalAtRsRelation::dummy(),
            range: RangeRelation::dummy(),
            wcell: WCellRelation::dummy(),
            ccell: CCellRelation::dummy(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::SharedRangeRelation;

    #[test]
    #[should_panic(expected = "shared relation read before it was drawn")]
    fn shared_range_relation_is_fail_closed_before_provider_draw() {
        SharedRangeRelation::new().get();
    }
}
