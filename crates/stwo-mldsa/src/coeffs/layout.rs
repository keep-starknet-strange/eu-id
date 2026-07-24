//! Row-stacking layout for the tall `mldsa_coeffs` component (worksheet S5 §3
//! row 1, amended by S5a §3). Every witnessed / carry polynomial's coefficients
//! are stacked into contiguous Horner groups; the accumulator (interaction tree)
//! evaluates each group at the drawn `(r, s)` and emits `P̂(r, s)` at its end row.
//!
//! ## Group order (fixed = `poly_id`)
//!
//! | kind    | groups | coeffs/group | coeffs/row | live digits/coeff | poly_id     |
//! |---------|--------|--------------|------------|-------------------|-------------|
//! | z_j     | L = 5  | N   = 256    | 2          | T_Z = 3           | 0 ..= 4     |
//! | w_i     | K = 6  | N   = 256    | 2          | T_W = 3           | 5 ..= 10    |
//! | e_i     | K = 6  | N   = 256    | 1          | T_E = 4           | 11 ..= 16   |
//! | v_i     | K = 6  | N-1 = 255    | 1          | T_V = 6           | 17 ..= 22   |
//! | c       | 1      | N   = 256    | 1          | 1                 | 23          |
//! | Ĉ_i     | K = 6  | 511          | 1          | 5 (t ∈ [0,4])     | 24 ..= 29   |
//!
//! Every row carries exactly `MAX_DIGITS = 6` digit cells (`T_V`). A z/w row
//! uses the first and second triplets for two consecutive high-to-low
//! coefficients; all other kinds retain one coefficient per row and constrain
//! their unused tail cells to zero. The paired Horner transition is
//! `acc' = (1 − start)·acc_prev·r² + digit_hi(s)·r + digit_lo(s)`, which is the
//! same polynomial evaluation as two ordinary Horner rows.

use crate::constants::{K, L, N};
use crate::witness::{T_E, T_MAX, T_V, T_W, T_Z};

/// Widest live-digit count over all kinds (`T_V = 6`); the uniform per-row digit
/// column count.
pub const MAX_DIGITS: usize = T_V;

/// Carry columns per carry coefficient: `t ∈ [0, T_MAX] ⇒ 5` (worksheet §3.3).
pub const CARRY_DIGITS: usize = T_MAX + 1;

/// The kind of polynomial a Horner group holds. `live_digits` is how many of the
/// `MAX_DIGITS` cells are meaningful; the rest are pinned to zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Z,
    W,
    E,
    V,
    C,
    Carry,
}

impl Kind {
    /// Digits in one logical coefficient of this kind.
    pub const fn live_digits(self) -> usize {
        match self {
            Kind::Z => T_Z,
            Kind::W => T_W,
            Kind::E => T_E,
            Kind::V => T_V,
            Kind::C => 1,
            Kind::Carry => CARRY_DIGITS,
        }
    }

    /// z/w have three digits each, so two coefficients exactly fill the six
    /// already-committed digit columns. Wider kinds remain one coefficient/row.
    pub const fn coefficients_per_row(self) -> usize {
        match self {
            Kind::Z | Kind::W => 2,
            _ => 1,
        }
    }

    /// Number of live digit cells in one physical row.
    pub const fn row_live_digits(self) -> usize {
        self.live_digits() * self.coefficients_per_row()
    }

    /// z and w are the paired/recomposed kinds. e, v, c, carries exist only as
    /// individual digit rows.
    pub const fn has_recomp(self) -> bool {
        matches!(self, Kind::Z | Kind::W)
    }
}

/// One Horner group: `count` contiguous coefficient rows of a single polynomial.
#[derive(Clone, Copy, Debug)]
pub struct Group {
    pub kind: Kind,
    pub poly_id: u32,
    /// Logical coefficients in this polynomial.
    pub coeffs: usize,
}

impl Group {
    /// Physical rows occupied by this group.
    pub fn rows(self) -> usize {
        self.coeffs.div_ceil(self.kind.coefficients_per_row())
    }

    /// Logical coefficient in packed slot `slot`, preserving the original
    /// high-to-low Horner order. Returns `None` only for a partial final row.
    pub fn coefficient_index(self, in_group: usize, slot: usize) -> Option<usize> {
        let from_high = in_group * self.kind.coefficients_per_row() + slot;
        if slot < self.kind.coefficients_per_row() && from_high < self.coeffs {
            Some(self.coeffs - 1 - from_high)
        } else {
            None
        }
    }
}

/// The full ordered group schedule (30 groups). `poly_id` is the group's index
/// into the flat `[z…, w…, e…, v…, c, Ĉ…]` order.
pub fn groups() -> Vec<Group> {
    let mut out = Vec::new();
    let mut poly_id = 0u32;
    let push =
        |kind: Kind, count: usize, groups: usize, poly_id: &mut u32, out: &mut Vec<Group>| {
            for _ in 0..groups {
                out.push(Group {
                    kind,
                    poly_id: *poly_id,
                    coeffs: count,
                });
                *poly_id += 1;
            }
        };
    push(Kind::Z, N, L, &mut poly_id, &mut out);
    push(Kind::W, N, K, &mut poly_id, &mut out);
    push(Kind::E, N, K, &mut poly_id, &mut out);
    push(Kind::V, N - 1, K, &mut poly_id, &mut out);
    push(Kind::C, N, 1, &mut poly_id, &mut out);
    push(
        Kind::Carry,
        crate::witness::U_LEN,
        K,
        &mut poly_id,
        &mut out,
    );
    out
}

/// Number of distinct claimed evaluations / groups (`= 30`).
pub const N_GROUPS: usize = L + K + K + K + 1 + K;

/// Total active (non-padding) rows across all groups.
pub fn active_rows() -> usize {
    groups().iter().map(|g| g.rows()).sum()
}

/// `poly_id` bases for the native fold to index claimed evals by kind.
pub const POLY_ID_Z0: u32 = 0;
pub const POLY_ID_W0: u32 = L as u32;
pub const POLY_ID_E0: u32 = (L + K) as u32;
pub const POLY_ID_V0: u32 = (L + 2 * K) as u32;
pub const POLY_ID_C: u32 = (L + 3 * K) as u32;
pub const POLY_ID_CARRY0: u32 = (L + 3 * K + 1) as u32;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn group_schedule_matches_worksheet() {
        let g = groups();
        assert_eq!(g.len(), N_GROUPS);
        assert_eq!(N_GROUPS, 30);
        // poly_id is dense 0..30.
        for (i, group) in g.iter().enumerate() {
            assert_eq!(group.poly_id, i as u32);
        }
        assert_eq!(g[0].poly_id, POLY_ID_Z0);
        assert_eq!(g[L].poly_id, POLY_ID_W0);
        assert_eq!(g[L + K].poly_id, POLY_ID_E0);
        assert_eq!(g[L + 2 * K].poly_id, POLY_ID_V0);
        assert_eq!(g[L + 3 * K].poly_id, POLY_ID_C);
        assert_eq!(g[L + 3 * K + 1].poly_id, POLY_ID_CARRY0);
    }

    #[test]
    fn active_rows_count() {
        // z/w pair two three-digit coefficients in each six-digit row.
        assert_eq!(active_rows(), 640 + 768 + 1536 + 1530 + 256 + 3066);
        assert_eq!(active_rows(), 7796);
    }

    #[test]
    fn paired_groups_preserve_high_to_low_coefficient_order() {
        let g = groups();
        for group in &g[..L + K] {
            assert_eq!(group.kind.coefficients_per_row(), 2);
            assert_eq!(group.kind.row_live_digits(), MAX_DIGITS);
            assert_eq!(group.rows(), N / 2);
            assert_eq!(group.coefficient_index(0, 0), Some(N - 1));
            assert_eq!(group.coefficient_index(0, 1), Some(N - 2));
            assert_eq!(group.coefficient_index(N / 2 - 1, 0), Some(1));
            assert_eq!(group.coefficient_index(N / 2 - 1, 1), Some(0));
        }
        for group in &g[L + K..] {
            assert_eq!(group.kind.coefficients_per_row(), 1);
            assert_eq!(group.rows(), group.coeffs);
        }
    }
}
