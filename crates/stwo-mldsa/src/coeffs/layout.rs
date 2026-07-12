//! Row-stacking layout for the tall `mldsa_coeffs` component (worksheet S5 §3
//! row 1, amended by S5a §3). Every witnessed / carry polynomial's coefficients
//! are stacked into contiguous Horner groups; the accumulator (interaction tree)
//! evaluates each group at the drawn `(r, s)` and emits `P̂(r, s)` at its end row.
//!
//! ## Group order (fixed = `poly_id`)
//!
//! | kind    | groups | coeffs/group | live digits/coeff | poly_id     |
//! |---------|--------|--------------|-------------------|-------------|
//! | z_j     | L = 5  | N   = 256    | T_Z = 3           | 0 ..= 4     |
//! | w_i     | K = 6  | N   = 256    | T_W = 3           | 5 ..= 10    |
//! | e_i     | K = 6  | N   = 256    | T_E = 4           | 11 ..= 16   |
//! | v_i     | K = 6  | N-1 = 255    | T_V = 6           | 17 ..= 22   |
//! | c       | 1      | N   = 256    | 1                 | 23          |
//! | Ĉ_i     | K = 6  | 511          | 5 (t ∈ [0,4])     | 24 ..= 29   |
//!
//! Every row carries up to `MAX_DIGITS = 6` digit cells (`T_V`). Unused tail
//! cells are constrained to zero (preprocessed live-count mask). The per-row
//! inner value is `digit_row(s) = Σ_t d_t · s^t` (s-powers are drawn constants,
//! so this is degree 1 in the digit cells); the group accumulator is the outer
//! Horner `acc' = (1 − start)·acc_prev·r + digit_row(s)` (worksheet §3.2).

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

    /// z and w carry the §3.4 recomposition binding (`cell = Σ_t d_t·B^t`, cell
    /// consumed by [NORM]/hash in M5). e, v, c, carries exist only as digits.
    pub const fn has_recomp(self) -> bool {
        matches!(self, Kind::Z | Kind::W)
    }
}

/// One Horner group: `count` contiguous coefficient rows of a single polynomial.
#[derive(Clone, Copy, Debug)]
pub struct Group {
    pub kind: Kind,
    pub poly_id: u32,
    /// Coefficient rows in this group.
    pub coeffs: usize,
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
    groups().iter().map(|g| g.coeffs).sum()
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
        // 5·256 + 6·256 + 6·256 + 6·255 + 256 + 6·511.
        assert_eq!(active_rows(), 1280 + 1536 + 1536 + 1530 + 256 + 3066);
        assert_eq!(active_rows(), 9204);
    }
}
