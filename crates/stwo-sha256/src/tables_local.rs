//! Local fallback for the workspace-shared range-check tables.
//!
//! The eu-id pipeline plans a workspace-shared range-check / LogUp helper
//! crate (owned by the ECDSA stream — `stwo-p256-utils` today, possibly
//! generalised or promoted into a new `stwo-air-utils`). Until that crate
//! ships, the SHA-256 AIR cannot wire its mod-2³² carry lookups (the
//! σ/Σ decode, packed Maj/Ch, split-and-pack, and per-family carry range
//! checks) without a parallel `tables_local` stub. This module **is** that
//! stub.
//!
//! ## Migration: one import swap
//!
//! Every public function here is named **exactly** the same as the
//! function the shared crate will eventually export. Migration is one
//! change at every call site:
//!
//! ```ignore
//! // before
//! use crate::tables_local::{range_2, range_4, range_5, range_16};
//! // after (shared crate landed)
//! use stwo_air_utils::range_tables::{range_2, range_4, range_5, range_16};
//! ```
//!
//! No call-site re-architecting; no parallel API pattern. The names
//! `range_2/4/5/16` are deliberately the obvious thing the shared crate
//! will export — no `local_*` prefix, no namespace collision with the
//! future import.
//!
//! ## What the upstream `stwo-p256-utils` already ships
//!
//! The P-256 audit infrastructure (branch `origin/lucas/p256`) ships:
//!
//! - `constants` — limb width, M31 modulus / centered bound, P-256 curve
//!   constants. SHA-256 has its own 16-bit limb convention; only the M31
//!   constants are migration candidates.
//! - `headroom` — per-equation audit, `HeadroomStatus` enum. Mirrored by
//!   [`crate::headroom`]; the SHA-256 audit is the simpler unsigned case.
//! - `carry_range` — derives a *signed* `CarryRangeSpec` (signed bound
//!   `C`, table size `2C + 1`) per equation. SHA-256 carries are unsigned
//!   (`∈ [0, k)`), so this stream needs *unsigned* `Range_k` tables sized
//!   `k`, not `2C + 1` — the shape this module ships.
//! - `selector_tables` — three P-256-specific preprocessed tables. The
//!   per-table-fn pattern (one `pub fn xxx() -> [Row; N]` per table) is
//!   what we mirror below.
//!
//! ## API shape rationale
//!
//! - **`Vec<u32>` return, not `[u32; N]` or const-generic.** [`range_16`]
//!   has 2¹⁶ rows; a const-sized array of that size doesn't fit naturally
//!   alongside the small `range_2`/`4`/`5`. One uniform return type keeps
//!   every call site committing the table the same way. The const-generic
//!   shape (`RangeTable<const N: u32>`) was rejected because the size is
//!   data, not a type parameter, and call sites are cleaner without
//!   `::<2>` everywhere.
//! - **Distinct functions per `k`.** Mirrors
//!   `stwo-p256-utils::selector_tables` exactly. The shared crate's
//!   eventual signed-carry variant (`signed_carry_range_c`) takes a
//!   runtime parameter; the unsigned variant having distinct fns means
//!   call sites read "this row reads from `range_4`" without parameter
//!   noise.
//!
//! ## What lives here
//!
//! - [`range_2`] / [`range_4`] / [`range_5`] — the three carry range-check
//!   tables for the four mod-2³² limb-add families audited in
//!   [`crate::headroom`]. Sizes are `RANGE_2 = 2`, `RANGE_4 = 4`,
//!   `RANGE_5 = 5`.
//! - [`range_16`] — the 16-bit limb range-check table. 2¹⁶ rows. Used for
//!   `(lo, hi)` limbs that are *not* immediately consumed by a downstream
//!   split-and-pack or σ/Σ decode lookup (the SHA-256-specific tables in
//!   [`crate::tables`] pin most limbs implicitly; the explicit `Range16` is
//!   needed for terminal limbs like the digest output, per design §10.2 /
//!   §11 L1).
//!
//! ## What does **not** live here
//!
//! - **The LogUp pair-batching finalizer.** Stwo's
//!   `stwo_constraint_framework::EvalAtRow::finalize_logup_in_pairs` is
//!   already callable directly; the shared crate's eventual contribution
//!   here is either a thin batching-policy wrapper or no wrapper at all.
//!   Either way, no local stub is needed — call sites use the trait
//!   method.
//! - **Relation-tag types** (`Range2Relation`, `Range16Relation`, …).
//!   These are emitted alongside `add_to_relation` wiring in the
//!   downstream lookup-wiring work; until that wiring is in flight there
//!   is nothing here to tag. Relation tags are component-owned, not
//!   foundation-owned.
//! - **The SHA-256-specific decode / packed-Maj-Ch / xor_8 / split-and-pack
//!   tables.** Those are component-owned and live in [`crate::tables`].

use crate::headroom::{RANGE_2, RANGE_4, RANGE_5};

/// Number of rows in the 16-bit limb range-check table: `2¹⁶ = 65 536`.
///
/// Exposed as a `pub const` so call sites can size preprocessed-column
/// allocations without recomputing `1u32 << 16` everywhere.
pub const RANGE_16: u32 = 1u32 << 16;

/// Preprocessed `Range_2` row content: `[0, 1]`.
///
/// Used to range-check carries from the **2-addend** mod-2³² adds —
/// `T2 = Σ0 + Maj`, `e_new = d + T1`, `a_new = T1 + T2`, and the eight
/// finalization adds `H⁽ᵗ⁺¹⁾ⱼ = H⁽ᵗ⁾ⱼ + working_varⱼ`. The honest carry per
/// limb sits in `[0, RANGE_2) = [0, 2)`, see [`crate::headroom`].
pub fn range_2() -> Vec<u32> {
    (0..RANGE_2).collect()
}

/// Preprocessed `Range_4` row content: `[0, 1, 2, 3]`.
///
/// Used to range-check carries from the **4-addend** message-schedule
/// recurrence `W[t] = σ1(W[t−2]) + W[t−7] + σ0(W[t−15]) + W[t−16]`. The
/// honest carry per limb sits in `[0, RANGE_4) = [0, 4)`, see
/// [`crate::headroom`].
pub fn range_4() -> Vec<u32> {
    (0..RANGE_4).collect()
}

/// Preprocessed `Range_5` row content: `[0, 1, 2, 3, 4]`.
///
/// Used to range-check carries from the **5-addend** round
/// `T1 = h + Σ1(e) + Ch(e,f,g) + K[t] + W[t]` — the widest add in
/// SHA-256. The honest carry per limb sits in `[0, RANGE_5) = [0, 5)`,
/// see [`crate::headroom`].
pub fn range_5() -> Vec<u32> {
    (0..RANGE_5).collect()
}

/// Preprocessed `Range_16` row content: `[0, 1, …, 2¹⁶ − 1]`.
///
/// Used to range-check **terminal** 16-bit limbs — limbs that are *not*
/// immediately consumed by a downstream lookup that already pins them to
/// `[0, 2¹⁶)`. Most working-state limbs are pinned implicitly via the
/// split-and-pack / σ-decode tables in [`crate::tables`]; the explicit
/// `Range_16` is needed for the digest output limbs and the small set of
/// other limbs §10.2 of the validated design calls out.
pub fn range_16() -> Vec<u32> {
    (0..RANGE_16).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each `Range_k` table contains exactly `k` rows.
    #[test]
    fn sizes_match_the_audited_carry_bounds() {
        assert_eq!(range_2().len() as u32, RANGE_2);
        assert_eq!(range_4().len() as u32, RANGE_4);
        assert_eq!(range_5().len() as u32, RANGE_5);
        assert_eq!(range_16().len() as u32, RANGE_16);
    }

    /// Row content is exactly `{0, 1, …, k − 1}` for every `Range_k`. The
    /// shared-foundation contract: the i-th row's value **is** `i`. Any
    /// shared-crate impl that breaks this property invalidates every call
    /// site that reads the row as the value.
    #[test]
    fn rows_are_consecutive_integers_from_zero() {
        for (i, row) in range_2().iter().enumerate() {
            assert_eq!(*row as usize, i, "range_2: row {i} has value {row}");
        }
        for (i, row) in range_4().iter().enumerate() {
            assert_eq!(*row as usize, i, "range_4: row {i} has value {row}");
        }
        for (i, row) in range_5().iter().enumerate() {
            assert_eq!(*row as usize, i, "range_5: row {i} has value {row}");
        }
        // Spot-check `range_16` at start, end, and a midpoint — full
        // iteration is 65 536 rows but the property is the same.
        let r16 = range_16();
        assert_eq!(r16[0], 0);
        assert_eq!(r16[42], 42);
        assert_eq!(r16[(RANGE_16 as usize) / 2], RANGE_16 / 2);
        assert_eq!(r16[(RANGE_16 as usize) - 1], RANGE_16 - 1);
    }

    /// Every audited carry bound from [`crate::headroom`] has a matching
    /// `Range_k` here. If a new add family is audited in `headroom.rs` but
    /// not given a table here, this assertion fails closed — preventing
    /// the lookup wiring from silently dropping a range check.
    #[test]
    fn every_audited_carry_family_has_a_local_table() {
        use crate::headroom::{current_headroom_audits, HeadroomStatus};

        for audit in current_headroom_audits() {
            // Skip pending audits — they have no carry bound yet by design.
            if audit.status != HeadroomStatus::Fits {
                continue;
            }
            let Some(signed_bound) = audit.signed_carry_bound else {
                continue;
            };
            // For SHA-256 the "signed bound" is `k − 1` for a `Range_k`
            // table; see `headroom.rs` rationale. The local table for this
            // family must be size `k = signed_bound + 1`.
            let table_size = (signed_bound + 1) as u32;
            let exists = matches!(table_size, RANGE_2 | RANGE_4 | RANGE_5);
            assert!(
                exists,
                "audit `{}` requires Range_{table_size}, which has no local table",
                audit.name,
            );
        }
    }
}
