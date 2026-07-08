//! LogUp relation contracts for the `mldsa_coeffs` component (M4).
//!
//! | relation | arity | tuple | providers | consumers |
//! |----------|-------|-------|-----------|-----------|
//! | `EvalAtRs`  | 5 | `(poly_id, e0,e1,e2,e3)` | coeffs group-end (yield `−end`) | verifier-native fold (use `+`) |
//! | `Rc9`       | 1 | `(digit + 2^8)` ∈ [0,2^9) | `Rc9` table (yield `−mult`) | coeffs digit cells (use) |
//! | `Rc13`      | 1 | `v ∈ [0,2^13)` | `Rc13` table | carry-lo, norm-lo exprs |
//! | `Rc8`       | 1 | `v ∈ [0,2^8)`  | `Rc8` table | carry-hi cells |
//! | `Rc7`       | 1 | `v ∈ [0,2^7)`  | `Rc7` table | norm-hi cells |
//!
//! Digit range (worksheet §3.1): a **dedicated 2^9 table** with offset `+2^8`
//! (the ×16-scaled-rc13 shortcut is FORBIDDEN). Carry rc (§3.3): `|C| ≤ 2^20`
//! via `C + 2^20 ∈ [0,2^21)` split 13+8 (`Rc13` lo + new `Rc8` hi). z-norm
//! (§3.4 / review flag): exact `≤ γ1−β−1` via a symmetric two-sided offset split
//! (`Rc13` lo + new `Rc7` hi on both `a = z+off` and `b = off−z`).

use stwo::core::fields::qm31::SECURE_EXTENSION_DEGREE;
use stwo_constraint_framework::relation;

use crate::binding::{CCellRelation, WCellRelation};

/// `(poly_id, e0, e1, e2, e3)` — the claimed `P̂(r,s)` QM31 eval as 4 M31 coords.
pub const EVAL_ARITY: usize = 1 + SECURE_EXTENSION_DEGREE;
relation!(EvalAtRsRelation, EVAL_ARITY);

// One arity-1 table relation TYPE; the five tables (rc9/rc13/rc8/rc7 + the
// ternary `{0,1,2}` set) are five INDEPENDENT instances drawn from the channel
// (mirrors p256's `RangeCheckRelation`). Independent LogUp randomness keeps the
// tables disjoint: a use against the rc9 instance balances only against rc9.
//
// The ternary c-digit `c ∈ {−1,0,1}` is proven by a use of `c + 1` against the
// `{0,1,2}` table (degree-1 lookup instead of the cubic poly `c(c−1)(c+1)`,
// which would push the composition degree past `log_size+1` and break the
// interaction-tree Horner mask). Worksheet §3.2 c-cell obligation.
relation!(RcRelation, 1);

/// The relations, drawn together after the base commit.
///
/// `wcell` / `ccell` are the cross-component bindings (M6): the coeffs component
/// YIELDS `(w_bind_id, w)` for every w-coefficient and `(c_bind_id, c)` for every
/// challenge coefficient; decomp / sampleinball consume them. In the standalone
/// coeffs test these two yields would be unbalanced (no consumer), so the
/// standalone test wires a test-side balancer against the SAME instances (see
/// [`crate::balancer`]); the composed statement lets decomp / sampleinball close
/// them.
#[derive(Clone)]
pub struct CoeffsRelations {
    pub eval: EvalAtRsRelation,
    pub rc9: RcRelation,
    pub rc13: RcRelation,
    pub rc8: RcRelation,
    pub rc7: RcRelation,
    pub ternary: RcRelation,
    pub wcell: WCellRelation,
    pub ccell: CCellRelation,
}

impl CoeffsRelations {
    pub fn draw(channel: &mut impl stwo::core::channel::Channel) -> Self {
        Self {
            eval: EvalAtRsRelation::draw(channel),
            rc9: RcRelation::draw(channel),
            rc13: RcRelation::draw(channel),
            rc8: RcRelation::draw(channel),
            rc7: RcRelation::draw(channel),
            ternary: RcRelation::draw(channel),
            wcell: WCellRelation::draw(channel),
            ccell: CCellRelation::draw(channel),
        }
    }

    /// Composed-statement constructor (M6): draw only the coeffs-private
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
            rc9: RcRelation::draw(channel),
            rc13: RcRelation::draw(channel),
            rc8: RcRelation::draw(channel),
            rc7: RcRelation::draw(channel),
            ternary: RcRelation::draw(channel),
            wcell,
            ccell,
        }
    }

    pub fn dummy() -> Self {
        Self {
            eval: EvalAtRsRelation::dummy(),
            rc9: RcRelation::dummy(),
            rc13: RcRelation::dummy(),
            rc8: RcRelation::dummy(),
            rc7: RcRelation::dummy(),
            ternary: RcRelation::dummy(),
            wcell: WCellRelation::dummy(),
            ccell: CCellRelation::dummy(),
        }
    }

    /// The relation instance for a table kind.
    pub fn rc(&self, kind: super::tables::RcKind) -> &RcRelation {
        match kind {
            super::tables::RcKind::Rc9 => &self.rc9,
            super::tables::RcKind::Rc13 => &self.rc13,
            super::tables::RcKind::Rc8 => &self.rc8,
            super::tables::RcKind::Rc7 => &self.rc7,
            super::tables::RcKind::Ternary => &self.ternary,
        }
    }
}
