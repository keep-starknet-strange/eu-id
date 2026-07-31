//! Small AIR helpers shared by the ML-DSA components and proof modules.

use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::SecureField;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::utils::{bit_reverse_index, coset_index_to_circle_domain_index};
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::LogupTraceGenerator;

/// A base-field column evaluation over the circle domain (bit-reversed order).
pub type ColEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;

/// `M31::from_u32_unchecked` shorthand.
pub fn m31(value: u32) -> M31 {
    M31::from_u32_unchecked(value)
}

/// Centered M31 encoding of a signed integer.
pub(crate) fn enc_signed(value: impl Into<i128>) -> M31 {
    const P: i128 = (1 << 31) - 1;
    m31(value.into().rem_euclid(P) as u32)
}

/// Smallest range-table log size covering `n_values`, floored at the SIMD lane width.
pub(crate) const fn table_log_size(n_values: usize) -> u32 {
    let bits = usize::BITS - (n_values - 1).leading_zeros();
    if bits < LOG_N_LANES {
        LOG_N_LANES
    } else {
        bits
    }
}

/// Stable ID for a canonical `[0, n_values)` value table.
///
/// Components with the same row count and values share one physical
/// preprocessing commitment.
pub(crate) fn value_table_preprocessed_id(log_size: u32, n_values: usize) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mldsa_value_table/log{log_size}/n{n_values}"),
    }
}

/// Preprocessed value column `[0, 1, …, n−1, 0, 0, …]`.
pub(crate) fn gen_value_table_preprocessed(log_size: u32, n_values: usize) -> ColEval {
    let rows = 1usize << log_size;
    col_eval(
        log_size,
        (0..rows)
            .map(|i| m31(if i < n_values { i as u32 } else { 0 }))
            .collect(),
    )
}

/// Multiplicity column: how many times each table value is consumed.
pub(crate) fn gen_value_table_multiplicities(
    log_size: u32,
    n_values: usize,
    uses: &[u32],
) -> ColEval {
    assert_eq!(uses.len(), n_values, "one multiplicity per table value");
    let rows = 1usize << log_size;
    col_eval(
        log_size,
        (0..rows)
            .map(|i| m31(if i < n_values { uses[i] } else { 0 }))
            .collect(),
    )
}

/// Interaction column for a value table provider: `−mult / denominator(value)`.
pub(crate) fn gen_value_table_interaction(
    log_size: u32,
    value: ColEval,
    multiplicity: &ColEval,
    denominator: impl Fn(PackedM31) -> PackedQM31 + Send + Sync,
) -> (Vec<ColEval>, SecureField) {
    let mut logup = LogupTraceGenerator::new(log_size);
    logup.col_from_fn(|row| {
        (
            -PackedQM31::from(multiplicity.data[row]),
            denominator(value.data[row]),
        )
    });
    logup.finalize_last()
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
