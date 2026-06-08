use stwo::{
    core::{
        fields::m31::M31,
        poly::circle::CanonicCoset,
        utils::{bit_reverse_index, coset_index_to_circle_domain_index},
    },
    prover::{
        backend::simd::{column::BaseColumn, m31::LOG_N_LANES, SimdBackend},
        poly::{circle::CircleEvaluation, BitReversedOrder},
    },
};

pub type M31ColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;

pub fn m31_column_eval(log_size: u32, values: Vec<M31>) -> M31ColumnEval {
    assert_eq!(
        values.len(),
        1usize << log_size,
        "column length must be exactly 2^log_size",
    );
    CircleEvaluation::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(coset_order_to_circle_domain_order(log_size, values)),
    )
}

fn coset_order_to_circle_domain_order(log_size: u32, values: Vec<M31>) -> Vec<M31> {
    let mut ordered = vec![M31::from_u32_unchecked(0); values.len()];
    for (coset_index, value) in values.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        );
        ordered[row] = value;
    }
    ordered
}

pub fn log_size_from_padded_len(len: usize) -> u32 {
    assert!(
        len.is_power_of_two(),
        "column length must be a power of two"
    );
    len.trailing_zeros()
}

pub fn padded_log_size(active_rows: usize) -> u32 {
    active_rows
        .max(1)
        .next_power_of_two()
        .trailing_zeros()
        .max(LOG_N_LANES)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn m31_column_eval_keeps_domain_size() {
        let eval = m31_column_eval(2, (0..4).map(M31::from_u32_unchecked).collect::<Vec<_>>());

        assert_eq!(eval.domain.log_size(), 2);
        assert_eq!(eval.domain.size(), 4);
    }

    #[test]
    #[should_panic(expected = "power of two")]
    fn log_size_from_padded_len_rejects_non_power_of_two() {
        let _ = log_size_from_padded_len(3);
    }

    #[test]
    fn padded_log_size_respects_simd_lane_width() {
        assert_eq!(padded_log_size(4), LOG_N_LANES);
        assert_eq!(padded_log_size(210), 8);
    }
}
