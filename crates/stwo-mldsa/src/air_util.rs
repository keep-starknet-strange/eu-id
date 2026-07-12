//! Small AIR helpers shared by the M4 `coeffs` component and its proof module —
//! local copies of the `stwo-p256` column/ordering utilities (the mldsa crate
//! does not depend on stwo-p256).

use stwo::core::fields::m31::M31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::utils::{bit_reverse_index, coset_index_to_circle_domain_index};
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;

/// A base-field column evaluation over the circle domain (bit-reversed order).
pub type ColEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;

/// `M31::from_u32_unchecked` shorthand.
pub fn m31(value: u32) -> M31 {
    M31::from_u32_unchecked(value)
}

/// Wrap a coset-ordered value vector (length `2^log_size`) into a
/// circle-domain `CircleEvaluation`, applying the coset→circle-domain
/// permutation the `[-1, 0]` interaction masks expect.
pub fn col_eval(log_size: u32, values: Vec<M31>) -> ColEval {
    assert_eq!(
        values.len(),
        1usize << log_size,
        "column length must be 2^log_size"
    );
    let mut ordered = vec![m31(0); values.len()];
    for (coset_index, value) in values.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        );
        ordered[row] = value;
    }
    CircleEvaluation::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(ordered),
    )
}

/// Smallest `log_size` covering `active_rows`, floored at the SIMD lane width.
pub fn padded_log_size(active_rows: usize) -> u32 {
    active_rows
        .max(1)
        .next_power_of_two()
        .trailing_zeros()
        .max(LOG_N_LANES)
}

/// Map circle-domain (bit-reversed) row → coset index, for packing interaction
/// columns whose logical order is coset order.
pub fn circle_row_to_coset(log_size: u32) -> Vec<usize> {
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
