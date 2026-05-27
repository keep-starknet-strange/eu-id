//! Solinas reduction matrix for the P-256 base field.
//!
//! `p = 2^256 − (2^224 − 2^192 − 2^96 + 1)`, so
//! `2^256 ≡ 2^224 − 2^192 − 2^96 + 1 (mod p)`.
//!
//! For every high limb position `k ∈ [N_LIMBS, 2·N_LIMBS − 1)`, compute
//! signed integers `matrix[k − N_LIMBS][j]` such that
//!
//! ```text
//! 2^(LIMB_BITS · k)  ≡  Σ_{j=0..N_LIMBS-1}  matrix[k − N_LIMBS][j] · 2^(LIMB_BITS · j)   (mod p)
//! ```
//!
//! Termination: each substitution strictly decreases the maximum bit position
//! in the bag, so the loop exits after at most `⌈(13·k − 255) / 32⌉ ≤ 8`
//! substitutions per row.
//!
//! The matrix is a compile-time constant baked into the AIR's Fp reduction
//! polynomial — not a preprocessed lookup table consumed via LogUp.

use crate::constants::{LIMB_BITS, N_LIMBS};

const P256_FIELD_BITS: usize = 256;
const TERM_BITS: usize = 512;
const SHIFT_TO_224: usize = P256_FIELD_BITS - 224;
const SHIFT_TO_192: usize = P256_FIELD_BITS - 192;
const SHIFT_TO_96: usize = P256_FIELD_BITS - 96;
const SHIFT_TO_0: usize = P256_FIELD_BITS;
pub const MAX_ABS_REDUCTION_COEFFICIENT: i64 = 1 << 12;

type TermBag = [i64; TERM_BITS];

/// Number of high limb positions to fold. A 20×20 schoolbook convolution
/// produces output limbs at positions `0..2·N_LIMBS − 1`; the top
/// `N_LIMBS − 1 = 19` are the high positions reduced by the matrix.
pub const HIGH_LIMB_COUNT: usize = N_LIMBS - 1;

/// Signed reduction matrix. `matrix[k − N_LIMBS][j]` is the coefficient `c`
/// such that the high limb position `k` contributes `c · 2^(LIMB_BITS · j)`
/// modulo `p` to the canonical low-limb representation.
pub type ReductionMatrix = [[i64; N_LIMBS]; HIGH_LIMB_COUNT];

/// Compile-time P-256 Solinas reduction matrix.
pub const REDUCTION_MATRIX: ReductionMatrix = compute_reduction_matrix();

/// Compute the Solinas reduction matrix for P-256.
pub const fn compute_reduction_matrix() -> ReductionMatrix {
    let mut matrix = [[0i64; N_LIMBS]; HIGH_LIMB_COUNT];
    let mut high_limb = 0;

    while high_limb < HIGH_LIMB_COUNT {
        matrix[high_limb] = reduction_row_for_high_limb(high_limb);
        high_limb += 1;
    }

    matrix
}

const fn reduction_row_for_high_limb(high_limb: usize) -> [i64; N_LIMBS] {
    let mut terms = [0i64; TERM_BITS];
    terms[limb_bit_position(N_LIMBS + high_limb)] = 1;

    reduce_terms_mod_p256(&mut terms);
    collect_low_limb_coefficients(&terms)
}

const fn reduce_terms_mod_p256(terms: &mut TermBag) {
    while let Some(bit) = highest_unreduced_bit(terms) {
        fold_unreduced_term(terms, bit);
    }
}

const fn highest_unreduced_bit(terms: &TermBag) -> Option<usize> {
    let mut bit = TERM_BITS;

    while bit > P256_FIELD_BITS {
        bit -= 1;
        if terms[bit] != 0 {
            return Some(bit);
        }
    }

    None
}

const fn fold_unreduced_term(terms: &mut TermBag, bit: usize) {
    let coeff = terms[bit];
    terms[bit] = 0;

    // 2^bit = 2^(bit-32) - 2^(bit-64) - 2^(bit-160) + 2^(bit-256) mod p.
    terms[bit - SHIFT_TO_224] += coeff;
    terms[bit - SHIFT_TO_192] -= coeff;
    terms[bit - SHIFT_TO_96] -= coeff;
    terms[bit - SHIFT_TO_0] += coeff;
}

const fn collect_low_limb_coefficients(terms: &TermBag) -> [i64; N_LIMBS] {
    let mut row = [0i64; N_LIMBS];
    let mut bit = 0usize;

    while bit < P256_FIELD_BITS {
        let coeff = terms[bit];
        if coeff != 0 {
            let low_limb = bit / LIMB_BITS;
            let bit_offset = bit % LIMB_BITS;
            row[low_limb] += coeff * (1i64 << bit_offset);
        }
        bit += 1;
    }

    row
}

const fn limb_bit_position(limb_index: usize) -> usize {
    LIMB_BITS * limb_index
}

#[cfg(test)]
mod tests {
    use super::*;

    fn reduce_terms_mod_p256_for_test(terms: &mut [i128; TERM_BITS]) {
        loop {
            let high_bit = (P256_FIELD_BITS..TERM_BITS)
                .rev()
                .find(|&bit| terms[bit] != 0);
            let Some(bit) = high_bit else {
                return;
            };

            let coeff = terms[bit];
            terms[bit] = 0;
            terms[bit - SHIFT_TO_224] += coeff;
            terms[bit - SHIFT_TO_192] -= coeff;
            terms[bit - SHIFT_TO_96] -= coeff;
            terms[bit - SHIFT_TO_0] += coeff;
        }
    }

    fn add_scaled_limb_term(terms: &mut [i128; TERM_BITS], bit_base: usize, coeff: i128) {
        let sign = if coeff < 0 { -1 } else { 1 };
        let mut abs_coeff = coeff.abs();
        let mut offset = 0usize;

        while abs_coeff != 0 {
            if abs_coeff & 1 == 1 {
                terms[bit_base + offset] += sign;
            }
            abs_coeff >>= 1;
            offset += 1;
        }
    }

    fn normalize_binary_terms(terms: &mut [i128; TERM_BITS]) {
        let mut bit = 0usize;
        while bit + 1 < TERM_BITS {
            let coeff = terms[bit];
            let rem = coeff.rem_euclid(2);
            terms[bit] = rem;
            terms[bit + 1] += (coeff - rem) / 2;
            bit += 1;
        }
    }

    #[test]
    fn reduction_matrix_has_one_row_per_high_limb() {
        assert_eq!(REDUCTION_MATRIX.len(), HIGH_LIMB_COUNT);
        assert_eq!(REDUCTION_MATRIX[0].len(), N_LIMBS);
    }

    #[test]
    fn first_high_limb_matches_shifted_solinas_identity() {
        let mut expected = [0i64; N_LIMBS];
        expected[17] = 1 << 7;
        expected[15] = -(1 << 1);
        expected[7] = -(1 << 9);
        expected[0] = 1 << 4;

        assert_eq!(REDUCTION_MATRIX[0], expected);
    }

    #[test]
    fn named_matrix_matches_generated_matrix() {
        assert_eq!(REDUCTION_MATRIX, compute_reduction_matrix());
    }

    #[test]
    fn every_row_is_congruent_to_its_high_limb() {
        for (high_limb, row) in REDUCTION_MATRIX.iter().enumerate() {
            let limb_index = N_LIMBS + high_limb;
            let mut terms = [0i128; TERM_BITS];
            terms[LIMB_BITS * limb_index] = 1;

            for (low_limb, coeff) in row.iter().copied().enumerate() {
                let coeff = coeff as i128;
                add_scaled_limb_term(&mut terms, LIMB_BITS * low_limb, -coeff);
            }

            reduce_terms_mod_p256_for_test(&mut terms);
            normalize_binary_terms(&mut terms);

            assert!(
                terms.iter().all(|&coeff| coeff == 0),
                "row {high_limb} does not reduce to zero: {terms:?}"
            );
        }
    }

    #[test]
    fn matrix_coefficients_stay_small_enough_for_signed_limb_arithmetic() {
        let max_abs_coeff = REDUCTION_MATRIX
            .iter()
            .flatten()
            .map(|&coeff| coeff.abs())
            .max()
            .unwrap();

        assert_eq!(max_abs_coeff, MAX_ABS_REDUCTION_COEFFICIENT);
    }
}
