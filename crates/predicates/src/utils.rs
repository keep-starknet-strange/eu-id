use crate::age::types::{DATE_MONTH_BASE, DATE_YEAR_BASE};
use num_traits::{One, Zero};
use stwo::core::fields::m31::{BaseField, M31};
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo_constraint_framework::EvalAtRow;

pub(crate) fn push_repeated_column(
    columns: &mut Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    value: u32,
    log_size: u32,
) {
    let domain = CanonicCoset::new(log_size).circle_domain();
    let column = vec![M31::from_u32_unchecked(value); 1 << log_size];
    columns.push(CircleEvaluation::new(domain, BaseColumn::from_iter(column)));
}

pub(crate) fn push_repeated_bits(
    columns: &mut Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    value: u32,
    log_size: u32,
    n_bits: usize,
) {
    for bit_index in 0..n_bits {
        push_repeated_column(columns, (value >> bit_index) & 1, log_size);
    }
}

pub(crate) fn read_bits<E: EvalAtRow, const N: usize>(eval: &mut E) -> [E::F; N] {
    core::array::from_fn(|_| eval.next_trace_mask())
}

pub(crate) fn read_bits_dynamic<E: EvalAtRow>(eval: &mut E, n_bits: usize) -> Vec<E::F> {
    (0..n_bits).map(|_| eval.next_trace_mask()).collect()
}

pub(crate) fn constrain_bits<E: EvalAtRow>(eval: &mut E, bits: &[E::F]) {
    for bit in bits {
        eval.add_constraint(bit.clone() * (bit.clone() - E::F::one()));
    }
}

pub(crate) fn bit_sum<E: EvalAtRow>(bits: &[E::F]) -> E::F {
    bits.iter()
        .enumerate()
        .fold(E::F::zero(), |sum, (bit_index, bit)| {
            sum + bit.clone() * BaseField::from_u32_unchecked(1 << bit_index)
        })
}

pub(crate) fn field_const<E: EvalAtRow>(value: u32) -> E::F {
    E::F::from(BaseField::from_u32_unchecked(value))
}

/// A fresh uniform M31 cell from the host CSPRNG.
///
/// Class-C blind rows and Class-D dummy multiplicities (Q-015 p4c) fill their
/// inactive/dummy cells with these. The randomness is drawn from the OS entropy
/// source — NEVER from the Fiat-Shamir channel — so the mask stays secret from
/// the verifier. Rejection-samples the single `2^31 − 1` value that is out of
/// M31's `[0, 2^31 − 1)` range, giving a uniform draw over the field.
pub(crate) fn random_m31_cell() -> M31 {
    use rand::RngCore;
    loop {
        let value = rand::rngs::OsRng.next_u32() & 0x7fff_ffff;
        if value < (1u32 << 31) - 1 {
            return M31::from_u32_unchecked(value);
        }
    }
}

pub(crate) fn bits_needed(max_value: u32) -> usize {
    if max_value == 0 {
        return 1;
    }
    (u32::BITS - max_value.leading_zeros()) as usize
}

pub(crate) const fn date_key(year: u32, month: u32, day: u32) -> u32 {
    year * DATE_YEAR_BASE + month * DATE_MONTH_BASE + day
}

pub(crate) fn date_key_checked(year: u32, month: u32, day: u32) -> Option<u32> {
    year.checked_mul(DATE_YEAR_BASE)?
        .checked_add(month.checked_mul(DATE_MONTH_BASE)?)?
        .checked_add(day)
}
