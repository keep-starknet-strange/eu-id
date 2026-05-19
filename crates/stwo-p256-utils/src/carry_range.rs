//! Per-equation-family `SignedCarryRange` bound derivation.
//!
//! The AIR's `SignedCarryRange` lookup table is preprocessed with a specific
//! signed bound `C` per equation family (FnMul, fake-GLV scalar, Fp Solinas,
//! RCB Alg 5/6, etc.). The bound comes from the headroom audit:
//! `C = max_{i} carry_bound_out[i]` across all limbs of the equation.
//!
//! See the AIR spec, "Relation Contracts → SignedCarryRange" and
//! "M31 headroom audit (BLOCKER)".

use crate::headroom::{EquationHeadroom, HeadroomStatus};

/// Per-family encoding parameters for the `SignedCarryRange` lookup table.
#[derive(Clone, Debug)]
pub struct CarryRangeSpec {
    pub equation_name: &'static str,
    /// Signed bound `C`: the preprocessed table contains every `c ∈ [−C, C]`,
    /// encoded as `enc(c) = c` for `c ≥ 0` and `enc(c) = M31_MODULUS + c` for
    /// `c < 0`.
    pub signed_bound: i128,
    /// Total table size: `2·C + 1` entries.
    pub table_size: usize,
}

/// Derive the `SignedCarryRange` spec for one audited equation family.
///
/// Returns `None` for `PendingFormula` audits; the caller is expected to
/// surface those as build-time errors so no AIR row is enabled with an
/// unaudited carry bound.
pub fn carry_range_spec(audit: &EquationHeadroom) -> Option<CarryRangeSpec> {
    match audit.status {
        HeadroomStatus::Fits => audit.signed_carry_bound.map(|c| CarryRangeSpec {
            equation_name: audit.name,
            signed_bound: c,
            table_size: (2 * c + 1) as usize,
        }),
        HeadroomStatus::RequiresSplit => None,
        HeadroomStatus::PendingFormula => None,
    }
}
