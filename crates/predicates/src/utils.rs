use crate::age::types::{DATE_MONTH_BASE, DATE_YEAR_BASE};
use stwo::core::fields::m31::{BaseField, M31};
use stwo_constraint_framework::EvalAtRow;

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
    // thread_rng is a ChaCha12 CSPRNG seeded (and periodically reseeded) from
    // the OS entropy source; it keeps the mask secret from the verifier while
    // avoiding one getentropy syscall per drawn cell.
    let mut rng = rand::thread_rng();
    loop {
        let value = rng.next_u32() & 0x7fff_ffff;
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
