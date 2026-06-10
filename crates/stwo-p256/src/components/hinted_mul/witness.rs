//! Native witness builder for the hinted mod-p multiplication.
//!
//! Computes, for one mul `a · b ≡ r (mod p)`, the quotients `q1, q2, q3`, the
//! half-products `m1, m2`, the canonical result `r`, and the three carry
//! polynomials `h1, h2, h3` of the identities documented in [`super`] (the
//! module docs carry the full integer-lifting bounds worksheet). Every bound
//! the AIR relies on is asserted here, so an honest witness that violates the
//! worksheet fails loudly at build time rather than producing an unprovable
//! trace.

use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};

use crate::constants::P256_MODULUS;

use super::wide::{u512_divmod, u512_from_limbs13, u512_mul, u512_to_limbs13, U512};

/// Limb base `β = 2^13`.
pub const HINTED_MUL_BETA: i64 = 1 << LIMB_BITS;

/// `b` is split as `b = b_lo + β^HINTED_MUL_B_SPLIT · b_hi`.
pub const HINTED_MUL_B_SPLIT: usize = N_LIMBS / 2;

/// Quotient width: `a < 2^260`, `b_half < 2^130` ⟹ `q < 2^134`; and
/// `m1 + β^10·m2 < 2^391` ⟹ `q3 < 2^135`. Both fit 11 limbs (143 bits).
pub const HINTED_MUL_Q_LIMBS: usize = 11;

/// Each identity's coefficient vector has `deg(Q·P) + 1 = 30` entries, so the
/// carry polynomial `H` has 29 coefficients.
pub const HINTED_MUL_C_COEFFS: usize = HINTED_MUL_Q_LIMBS + N_LIMBS - 1;
pub const HINTED_MUL_H_COEFFS: usize = HINTED_MUL_C_COEFFS - 1;

/// Maximum absolute value of any identity coefficient:
/// `11·(β−1)² + (β−1)` (the `Q·P` convolution side; the positive side is at
/// most `10·(β−1)²` for the half-product or `2·(β−1)` for the recombination).
pub const HINTED_MUL_MAX_COEFF: i64 =
    (HINTED_MUL_Q_LIMBS as i64) * (HINTED_MUL_BETA - 1) * (HINTED_MUL_BETA - 1)
        + (HINTED_MUL_BETA - 1);

/// Honest carry bound: `|h_k| < MAX_COEFF / (β−1)`.
pub const HINTED_MUL_H_BOUND: i64 = HINTED_MUL_MAX_COEFF / (HINTED_MUL_BETA - 1);

/// AIR range split of a carry coefficient: `h = h_lo + β·h_hi` with
/// `h_lo ∈ [0, β)` (Range13) and `h_hi ∈ [−12, 12]` (small signed table).
pub const HINTED_MUL_H_HI_BOUND: i64 = 12;

/// Adversarial carry magnitude admitted by the split range checks.
pub const HINTED_MUL_H_RANGE_MAX: i64 =
    HINTED_MUL_H_HI_BOUND * HINTED_MUL_BETA + (HINTED_MUL_BETA - 1);

/// The M31 prime: coefficient relations are only proven mod this.
pub const M31_PRIME: i64 = (1 << 31) - 1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HintedMulWitnessError {
    /// An operand limb is not 13-bit.
    OperandLimbOutOfRange { operand: &'static str, index: usize },
    /// A computed quotient needs more than [`HINTED_MUL_Q_LIMBS`] limbs.
    QuotientTooWide { identity: usize },
    /// A carry coefficient exceeded the honest bound (worksheet violation).
    CarryOutOfBounds { identity: usize, index: usize },
    /// A carry identity failed to divide exactly (internal invariant).
    CarryRemainder { identity: usize },
    /// The recomputed canonical result differs from the silo's stored result.
    ResultMismatch { source_index: usize, mul_index: usize },
}

/// Full witness for one hinted mul. All limb vectors are little-endian 13-bit
/// limbs except the `h*` carry coefficients, which are signed `i64` within
/// `±HINTED_MUL_H_BOUND`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HintedMulWitness {
    pub a: [u32; N_LIMBS],
    pub b: [u32; N_LIMBS],
    pub q1: [u32; HINTED_MUL_Q_LIMBS],
    pub m1: [u32; N_LIMBS],
    pub h1: [i64; HINTED_MUL_H_COEFFS],
    pub q2: [u32; HINTED_MUL_Q_LIMBS],
    pub m2: [u32; N_LIMBS],
    pub h2: [i64; HINTED_MUL_H_COEFFS],
    pub q3: [u32; HINTED_MUL_Q_LIMBS],
    pub r: [u32; N_LIMBS],
    pub h3: [i64; HINTED_MUL_H_COEFFS],
}

impl HintedMulWitness {
    /// Builds the witness for `a · b mod p`. Operands may be any 20×13-bit
    /// values (non-canonical representatives included); `r` is the canonical
    /// `(a · b) mod p`.
    pub fn new(a: &[u32; N_LIMBS], b: &[u32; N_LIMBS]) -> Result<Self, HintedMulWitnessError> {
        check_operand("a", a)?;
        check_operand("b", b)?;

        let p_words = modulus_u512();
        let a_value = u512_from_limbs13(a);

        let b_lo: [u32; HINTED_MUL_B_SPLIT] = core::array::from_fn(|i| b[i]);
        let b_hi: [u32; HINTED_MUL_B_SPLIT] =
            core::array::from_fn(|i| b[HINTED_MUL_B_SPLIT + i]);

        // Identity 1: a · b_lo = q1 · p + m1.
        let n1 = u512_mul(&a_value, &u512_from_limbs13(&b_lo));
        let (q1w, m1w) = u512_divmod(&n1, &p_words);
        let q1 = quotient_limbs(&q1w, 1)?;
        let m1: [u32; N_LIMBS] = to_array(u512_to_limbs13(&m1w, N_LIMBS));

        // Identity 2: a · b_hi = q2 · p + m2.
        let n2 = u512_mul(&a_value, &u512_from_limbs13(&b_hi));
        let (q2w, m2w) = u512_divmod(&n2, &p_words);
        let q2 = quotient_limbs(&q2w, 2)?;
        let m2: [u32; N_LIMBS] = to_array(u512_to_limbs13(&m2w, N_LIMBS));

        // Identity 3: m1 + β^10 · m2 = q3 · p + r. The shift is exactly ten
        // limb positions, so build the numerator as an (un-normalized) limb
        // sum.
        let mut n3_limbs = [0u32; N_LIMBS + HINTED_MUL_B_SPLIT];
        for (i, &limb) in m1.iter().enumerate() {
            n3_limbs[i] += limb;
        }
        for (i, &limb) in m2.iter().enumerate() {
            n3_limbs[HINTED_MUL_B_SPLIT + i] += limb;
        }
        let n3 = u512_from_limbs13(&n3_limbs);
        let (q3w, rw) = u512_divmod(&n3, &p_words);
        let q3 = quotient_limbs(&q3w, 3)?;
        let r: [u32; N_LIMBS] = to_array(u512_to_limbs13(&rw, N_LIMBS));

        let p_limbs = modulus_limbs();
        let h1 = carry_polynomial(&identity_coefficients(a, &b_lo, &q1, &p_limbs, &m1, 0), 1)?;
        let h2 = carry_polynomial(&identity_coefficients(a, &b_hi, &q2, &p_limbs, &m2, 0), 2)?;
        let c3 = recombination_coefficients(&m1, &m2, &q3, &p_limbs, &r);
        let h3 = carry_polynomial(&c3, 3)?;

        let witness = Self {
            a: *a,
            b: *b,
            q1,
            m1,
            h1,
            q2,
            m2,
            h2,
            q3,
            r,
            h3,
        };
        debug_assert_eq!(witness.verify(), Ok(()));
        Ok(witness)
    }

    /// Re-checks every coefficient relation `c_k = h_{k−1} − β·h_k` over the
    /// integers plus all range bounds — exactly what the AIR enforces (the AIR
    /// checks the relations mod p_M31 at `z`; the worksheet margins make that
    /// equivalent to this integer check).
    pub fn verify(&self) -> Result<(), HintedMulWitnessError> {
        check_operand("a", &self.a)?;
        check_operand("b", &self.b)?;
        let p_limbs = modulus_limbs();
        let b_lo: [u32; HINTED_MUL_B_SPLIT] = core::array::from_fn(|i| self.b[i]);
        let b_hi: [u32; HINTED_MUL_B_SPLIT] =
            core::array::from_fn(|i| self.b[HINTED_MUL_B_SPLIT + i]);

        verify_identity(
            &identity_coefficients(&self.a, &b_lo, &self.q1, &p_limbs, &self.m1, 0),
            &self.h1,
            1,
        )?;
        verify_identity(
            &identity_coefficients(&self.a, &b_hi, &self.q2, &p_limbs, &self.m2, 0),
            &self.h2,
            2,
        )?;
        verify_identity(
            &recombination_coefficients(&self.m1, &self.m2, &self.q3, &p_limbs, &self.r),
            &self.h3,
            3,
        )?;
        Ok(())
    }
}

/// Coefficients of `A·B_half − Q·P − M` (30 entries). `shift` offsets the
/// half-product (unused for identities 1/2; kept for symmetry with the
/// recombination builder).
fn identity_coefficients(
    a: &[u32; N_LIMBS],
    b_half: &[u32; HINTED_MUL_B_SPLIT],
    q: &[u32; HINTED_MUL_Q_LIMBS],
    p_limbs: &[u32; N_LIMBS],
    m: &[u32; N_LIMBS],
    shift: usize,
) -> [i64; HINTED_MUL_C_COEFFS] {
    let mut c = [0i64; HINTED_MUL_C_COEFFS];
    for (i, &ai) in a.iter().enumerate() {
        for (j, &bj) in b_half.iter().enumerate() {
            c[shift + i + j] += i64::from(ai) * i64::from(bj);
        }
    }
    subtract_qp_and_value(&mut c, q, p_limbs, m, 0);
    c
}

/// Coefficients of `M1 + X^10·M2 − Q3·P − R` (30 entries).
fn recombination_coefficients(
    m1: &[u32; N_LIMBS],
    m2: &[u32; N_LIMBS],
    q3: &[u32; HINTED_MUL_Q_LIMBS],
    p_limbs: &[u32; N_LIMBS],
    r: &[u32; N_LIMBS],
) -> [i64; HINTED_MUL_C_COEFFS] {
    let mut c = [0i64; HINTED_MUL_C_COEFFS];
    for (i, &limb) in m1.iter().enumerate() {
        c[i] += i64::from(limb);
    }
    for (i, &limb) in m2.iter().enumerate() {
        c[HINTED_MUL_B_SPLIT + i] += i64::from(limb);
    }
    subtract_qp_and_value(&mut c, q3, p_limbs, r, 0);
    c
}

fn subtract_qp_and_value(
    c: &mut [i64; HINTED_MUL_C_COEFFS],
    q: &[u32; HINTED_MUL_Q_LIMBS],
    p_limbs: &[u32; N_LIMBS],
    value: &[u32; N_LIMBS],
    shift: usize,
) {
    for (i, &qi) in q.iter().enumerate() {
        for (j, &pj) in p_limbs.iter().enumerate() {
            c[shift + i + j] -= i64::from(qi) * i64::from(pj);
        }
    }
    for (i, &limb) in value.iter().enumerate() {
        c[shift + i] -= i64::from(limb);
    }
    for (index, &coeff) in c.iter().enumerate() {
        debug_assert!(
            coeff.abs() <= HINTED_MUL_MAX_COEFF,
            "identity coefficient {index} = {coeff} exceeds the worksheet bound",
        );
    }
}

/// Synthetic division of `C(X)` by `(X − β)`: bottom-up exact division
/// `h_k = (h_{k−1} − c_k) / β` (bounded by `MAX_COEFF/(β−1)`, so it never
/// overflows i64), with the final relation `h_top == c_top` asserting
/// `C(β) = 0`.
fn carry_polynomial(
    c: &[i64; HINTED_MUL_C_COEFFS],
    identity: usize,
) -> Result<[i64; HINTED_MUL_H_COEFFS], HintedMulWitnessError> {
    let mut h = [0i64; HINTED_MUL_H_COEFFS];
    let mut prev = 0i64;
    for k in 0..HINTED_MUL_H_COEFFS {
        let numerator = prev - c[k];
        if numerator % HINTED_MUL_BETA != 0 {
            return Err(HintedMulWitnessError::CarryRemainder { identity });
        }
        let value = numerator / HINTED_MUL_BETA;
        if value.abs() > HINTED_MUL_H_BOUND {
            return Err(HintedMulWitnessError::CarryOutOfBounds { identity, index: k });
        }
        h[k] = value;
        prev = value;
    }
    // Top relation: c_top = h_{top−1} − β·h_top with h_top = 0.
    if c[HINTED_MUL_C_COEFFS - 1] != prev {
        return Err(HintedMulWitnessError::CarryRemainder { identity });
    }
    Ok(h)
}

fn verify_identity(
    c: &[i64; HINTED_MUL_C_COEFFS],
    h: &[i64; HINTED_MUL_H_COEFFS],
    identity: usize,
) -> Result<(), HintedMulWitnessError> {
    for (k, &coeff) in c.iter().enumerate() {
        let prev = if k == 0 { 0 } else { h[k - 1] };
        let next = if k < HINTED_MUL_H_COEFFS { h[k] } else { 0 };
        if coeff != prev - HINTED_MUL_BETA * next {
            return Err(HintedMulWitnessError::CarryRemainder { identity });
        }
    }
    for (index, &value) in h.iter().enumerate() {
        if value.abs() > HINTED_MUL_H_BOUND {
            return Err(HintedMulWitnessError::CarryOutOfBounds { identity, index });
        }
    }
    Ok(())
}

/// Splits a signed carry coefficient into the AIR's committed pieces:
/// `h = h_lo + β·h_hi` with `h_lo ∈ [0, β)` and `h_hi ∈ [−12, 12]`.
pub fn split_carry(h: i64) -> (u32, i64) {
    let h_hi = h.div_euclid(HINTED_MUL_BETA);
    let h_lo = h.rem_euclid(HINTED_MUL_BETA);
    debug_assert!(h_hi.abs() <= HINTED_MUL_H_HI_BOUND);
    (h_lo as u32, h_hi)
}

fn check_operand(
    operand: &'static str,
    limbs: &[u32; N_LIMBS],
) -> Result<(), HintedMulWitnessError> {
    for (index, &limb) in limbs.iter().enumerate() {
        if i64::from(limb) >= HINTED_MUL_BETA {
            return Err(HintedMulWitnessError::OperandLimbOutOfRange { operand, index });
        }
    }
    Ok(())
}

fn quotient_limbs(
    value: &U512,
    identity: usize,
) -> Result<[u32; HINTED_MUL_Q_LIMBS], HintedMulWitnessError> {
    let used_bits: usize = value
        .iter()
        .enumerate()
        .map(|(i, &w)| if w == 0 { 0 } else { 64 * i + (64 - w.leading_zeros() as usize) })
        .max()
        .unwrap_or(0);
    if used_bits > LIMB_BITS as usize * HINTED_MUL_Q_LIMBS {
        return Err(HintedMulWitnessError::QuotientTooWide { identity });
    }
    Ok(to_array(u512_to_limbs13(value, HINTED_MUL_Q_LIMBS)))
}

fn modulus_u512() -> U512 {
    let mut out = [0u64; 8];
    out[..4].copy_from_slice(&P256_MODULUS);
    out
}

fn modulus_limbs() -> [u32; N_LIMBS] {
    to_array(u512_to_limbs13(&modulus_u512(), N_LIMBS))
}

fn to_array<const N: usize>(values: Vec<u32>) -> [u32; N] {
    let mut out = [0u32; N];
    out.copy_from_slice(&values);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::limbs::P256M31BigInt;
    use crate::types::{field_modulus, U256};

    /// Worksheet margin: no coefficient relation can wrap mod p_M31 within
    /// the committed range bounds. This constant inequality is the load-
    /// bearing soundness fact of the whole design (module docs); if a
    /// refactor changes any bound, this test fails before the AIR lies.
    #[test]
    fn wrap_margin_is_respected() {
        let slack = HINTED_MUL_MAX_COEFF
            + HINTED_MUL_H_RANGE_MAX
            + HINTED_MUL_BETA * HINTED_MUL_H_RANGE_MAX;
        assert!(
            slack < M31_PRIME,
            "coefficient relation slack {slack} must stay below p_M31 {M31_PRIME}",
        );
        // Honest carries must fit the committed split.
        assert!(HINTED_MUL_H_BOUND <= HINTED_MUL_H_RANGE_MAX);
        // And the documented numbers stay what the worksheet says. Note
        // MAX_C = (β−1)·(11·(β−1) + 1), so the honest carry bound is exact.
        assert_eq!(HINTED_MUL_MAX_COEFF, 738_025_482);
        assert_eq!(HINTED_MUL_H_BOUND, 90_102);
        assert_eq!(HINTED_MUL_H_RANGE_MAX, 106_495);
    }

    fn limbs_of(value: &U256) -> [u32; N_LIMBS] {
        let big = P256M31BigInt::from_u256(value);
        core::array::from_fn(|i| big.limbs()[i].0)
    }

    fn u256_from_u64(v: u64) -> U256 {
        U256::from_le_u64s(&[v, 0, 0, 0])
    }

    fn cmp_words4(a: &[u64; 4], b: &[u64; 4]) -> core::cmp::Ordering {
        for i in (0..4).rev() {
            match a[i].cmp(&b[i]) {
                core::cmp::Ordering::Equal => continue,
                other => return other,
            }
        }
        core::cmp::Ordering::Equal
    }

    fn sub_words4(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
        let mut out = [0u64; 4];
        let mut borrow = 0u64;
        for i in 0..4 {
            let (d1, b1) = a[i].overflowing_sub(b[i]);
            let (d2, b2) = d1.overflowing_sub(borrow);
            out[i] = d2;
            borrow = u64::from(b1) + u64::from(b2);
        }
        assert_eq!(borrow, 0, "sub_words4 underflow");
        out
    }

    /// Deterministic pseudo-random canonical field elements (no external deps).
    fn pseudo_random_value(seed: u64) -> U256 {
        let mut words = [0u64; 4];
        let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1);
        for word in words.iter_mut() {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            *word = state;
        }
        let p = field_modulus().to_le_u64s();
        if cmp_words4(&words, &p) != core::cmp::Ordering::Less {
            words = sub_words4(&words, &p);
        }
        U256::from_le_u64s(&words)
    }

    /// Canonical `(a · b) mod p` limbs via the existing native mul witness.
    fn reference_mul_mod_p(a: &U256, b: &U256) -> [u32; N_LIMBS] {
        let result = crate::field::ops::mul_mod_witness(a, b, &field_modulus()).result;
        core::array::from_fn(|i| result.limbs()[i].0)
    }

    #[test]
    fn witness_matches_reference_mul_for_small_values() {
        let a = u256_from_u64(123_456_789);
        let b = u256_from_u64(987_654_321);
        let witness = HintedMulWitness::new(&limbs_of(&a), &limbs_of(&b)).expect("witness builds");
        assert_eq!(witness.r, reference_mul_mod_p(&a, &b));
        witness.verify().expect("identities hold");
    }

    #[test]
    fn witness_matches_reference_mul_for_random_field_elements() {
        for seed in 0..32u64 {
            let a = pseudo_random_value(seed * 2 + 1);
            let b = pseudo_random_value(seed * 2 + 2);
            let witness =
                HintedMulWitness::new(&limbs_of(&a), &limbs_of(&b)).expect("witness builds");
            assert_eq!(witness.r, reference_mul_mod_p(&a, &b), "seed {seed}");
            witness.verify().expect("identities hold");
            for h in witness
                .h1
                .iter()
                .chain(witness.h2.iter())
                .chain(witness.h3.iter())
            {
                assert!(h.abs() <= HINTED_MUL_H_BOUND);
                let (lo, hi) = split_carry(*h);
                assert!(i64::from(lo) < HINTED_MUL_BETA);
                assert!(hi.abs() <= HINTED_MUL_H_HI_BOUND);
                assert_eq!(i64::from(lo) + HINTED_MUL_BETA * hi, *h);
            }
        }
    }

    #[test]
    fn witness_handles_edge_operands() {
        let p_minus_1 = U256::from_le_u64s(&sub_words4(
            &field_modulus().to_le_u64s(),
            &[1, 0, 0, 0],
        ));
        for (a, b) in [
            (U256::ZERO, pseudo_random_value(7)),
            (pseudo_random_value(8), U256::ZERO),
            (p_minus_1.clone(), p_minus_1.clone()),
            (u256_from_u64(1), p_minus_1.clone()),
        ] {
            let witness =
                HintedMulWitness::new(&limbs_of(&a), &limbs_of(&b)).expect("witness builds");
            assert_eq!(witness.r, reference_mul_mod_p(&a, &b));
            witness.verify().expect("identities hold");
        }
    }

    #[test]
    fn witness_accepts_non_canonical_operands() {
        // a = p + 41 (a non-canonical representative of 41, still a 256-bit
        // value whose canonical 13-bit limb decomposition the builder accepts).
        let mut words = field_modulus().to_le_u64s();
        let mut carry = 41u128;
        for word in words.iter_mut() {
            let total = u128::from(*word) + carry;
            *word = total as u64;
            carry = total >> 64;
        }
        assert_eq!(carry, 0, "p + 41 must stay below 2^256");
        let a_limbs = limbs_of(&U256::from_le_u64s(&words));
        let b = pseudo_random_value(9);
        let witness = HintedMulWitness::new(&a_limbs, &limbs_of(&b)).expect("witness builds");
        // (p + 41)·b ≡ 41·b (mod p).
        assert_eq!(witness.r, reference_mul_mod_p(&u256_from_u64(41), &b));
        witness.verify().expect("identities hold");
    }

    #[test]
    fn forged_witness_components_fail_verification() {
        let a = pseudo_random_value(21);
        let b = pseudo_random_value(22);
        let honest = HintedMulWitness::new(&limbs_of(&a), &limbs_of(&b)).expect("witness builds");

        // Mutated result limb breaks identity 3.
        let mut forged = honest.clone();
        forged.r[0] = (forged.r[0] + 1) % 8192;
        assert!(forged.verify().is_err(), "mutated r must fail");

        // Mutated quotient limb breaks identity 1.
        let mut forged = honest.clone();
        forged.q1[0] = (forged.q1[0] + 1) % 8192;
        assert!(forged.verify().is_err(), "mutated q1 must fail");

        // Mutated half-product limb breaks identities 1 and 3.
        let mut forged = honest.clone();
        forged.m2[3] = (forged.m2[3] + 1) % 8192;
        assert!(forged.verify().is_err(), "mutated m2 must fail");

        // Mutated carry coefficient breaks its identity.
        let mut forged = honest;
        forged.h3[5] += 1;
        assert!(forged.verify().is_err(), "mutated h3 must fail");
    }
}
