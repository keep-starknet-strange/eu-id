//! Fixed local range-check table contents for the SHA-256 component.
//!
//! Each function returns the canonical row values for one `Range_k` producer.
//!
//! ## What lives here
//!
//! - [`range_2`], [`range_4`], and [`range_5`] are the carry range-check
//!   tables for the four mod-2³² limb-add families audited in
//!   [`crate::headroom`]. Sizes are `RANGE_2 = 2`, `RANGE_4 = 4`,
//!   `RANGE_5 = 5`.
//! - [`range_8`] is the byte range-check table. It has 2⁸ rows. It checks
//!   terminal digest bytes.

use crate::headroom::{RANGE_2, RANGE_4, RANGE_5};

/// Number of rows in the byte range-check table: `2⁸ = 256`.
///
/// Exposed as a `pub const` so call sites can size preprocessed-column
/// allocations without recomputing `1u32 << 8` everywhere.
pub const RANGE_8: u32 = 1u32 << 8;

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

/// Preprocessed `Range_8` row content: `[0, 1, …, 2⁸ − 1]`.
///
/// Used to range-check terminal digest bytes. The
/// `limb = 256·b_hi + b_lo` constraints pin the corresponding 16-bit digest
/// limbs without a 65,536-row table.
pub fn range_8() -> Vec<u32> {
    (0..RANGE_8).collect()
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
        assert_eq!(range_8().len() as u32, RANGE_8);
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
        let r8 = range_8();
        assert_eq!(r8[0], 0);
        assert_eq!(r8[42], 42);
        assert_eq!(r8[(RANGE_8 as usize) / 2], RANGE_8 / 2);
        assert_eq!(r8[(RANGE_8 as usize) - 1], RANGE_8 - 1);
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
