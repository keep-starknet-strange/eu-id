//! Shared column-order and spread-encoding utilities.

use num_traits::Zero;
use stwo::core::fields::m31::M31;

// ───────────────────────────── Spread encoding ─────────────────────────────
//
// Stride-2 "spread" form: a byte `b = Σ bᵢ·2ⁱ` maps to `spread(b) = Σ bᵢ·4ⁱ`
// (a 16-bit value whose 8 base-4 digits are exactly `b`'s bits). Sums of ≤3
// spread values stay carry-free in M31 (each base-4 slot sums to ≤3), so XOR of
// up to three bytes is one dense `sum → spread(xor)` table lookup. Byte form
// appears at the HashIo boundary, where the conversion table binds it to spread
// form.

/// Largest spread value: `spread(0xFF) = Σ 4ⁱ = (4⁸−1)/3 = 21845`.
pub const SPREAD_MAX: u32 = spread_u32(0xFF);

/// `spread(byte)`: interleave each of the byte's 8 bits into base-4 slots.
pub const fn spread_u32(byte: u32) -> u32 {
    let mut out = 0u32;
    let mut i = 0;
    while i < 8 {
        out |= ((byte >> i) & 1) << (2 * i);
        i += 1;
    }
    out
}

/// Inverse of [`spread_u32`] for a *valid* spread value (each base-4 digit 0/1).
pub const fn unspread_u32(spread: u32) -> u32 {
    let mut out = 0u32;
    let mut i = 0;
    while i < 8 {
        out |= ((spread >> (2 * i)) & 1) << i;
        i += 1;
    }
    out
}

// ───────────────────── Column ordering for row-offset masks ─────────────────

/// A base-field column evaluation over the circle domain (bit-reversed order).
pub type ColEval = stwo::prover::poly::circle::CircleEvaluation<
    stwo::prover::backend::simd::SimdBackend,
    M31,
    stwo::prover::poly::BitReversedOrder,
>;

/// Wrap a coset-ordered value vector (length `2^log_size`) into a circle-domain
/// `CircleEvaluation`, applying the coset→circle-domain permutation the
/// `[-1, 0]` masks expect (mirror of `stwo-mldsa`'s `air_util::col_eval`).
pub fn col_eval(log_size: u32, values: Vec<M31>) -> ColEval {
    use stwo::core::utils::{bit_reverse_index, coset_index_to_circle_domain_index};
    assert_eq!(
        values.len(),
        1usize << log_size,
        "column length must be 2^log_size"
    );
    let mut ordered = vec![M31::zero(); values.len()];
    for (coset_index, value) in values.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        );
        ordered[row] = value;
    }
    ColEval::new(
        stwo::core::poly::circle::CanonicCoset::new(log_size).circle_domain(),
        stwo::prover::backend::simd::column::BaseColumn::from_iter(ordered),
    )
}

/// Map circle-domain (bit-reversed) row → coset index, for packing interaction
/// columns whose logical order is coset order.
pub fn circle_row_to_coset(log_size: u32) -> Vec<usize> {
    use stwo::core::utils::{bit_reverse_index, coset_index_to_circle_domain_index};
    let rows = 1usize << log_size;
    let mut lookup = vec![0usize; rows];
    for coset in 0..rows {
        let domain_row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset, log_size),
            log_size,
        );
        lookup[domain_row] = coset;
    }
    lookup
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spread_round_trips_and_is_carry_free() {
        for b in 0u32..256 {
            let s = spread_u32(b);
            assert_eq!(unspread_u32(s), b, "round trip byte {b:#x}");
            // Every base-4 digit of a spread value is 0 or 1.
            for i in 0..8 {
                assert!((s >> (2 * i)) & 0b11 <= 1, "digit {i} of spread({b:#x})");
            }
        }
        assert_eq!(SPREAD_MAX, spread_u32(0xFF));
        // Sum of three spread bytes stays carry-free: each slot ≤ 3.
        let s = spread_u32(0xFF) + spread_u32(0xFF) + spread_u32(0xFF);
        for i in 0..8 {
            assert_eq!((s >> (2 * i)) & 0b11, 3, "triple-sum slot {i} == 3");
        }
        assert_eq!(s, (1 << 16) - 1, "3·spread(0xFF) fills the dense key space");
    }
}
