//! Native witness-only fake-GLV decomposition for any scalar `k ∈ [0, n)`,
//! where `n` is the P-256 curve order.
//!
//! Algorithm: Garaga `precompute_lattice` (Crypto-2001 GLV Algorithm 3.7,
//! half-GCD lattice basis on `(n, k)`).
//!     <https://www.iacr.org/archive/crypto2001/21390189.pdf>
//! Reference: `~/garaga/hydra/garaga/hints/fake_glv.py::precompute_lattice`.
//!
//! Identity proven (Garaga form):
//! ```text
//!     s1_signed + scalar · s2_signed ≡ 0  (mod n)
//! ```
//! with `|s1|, |s2| ≲ √n ≈ 2^128` and `s1 > 0` after normalization.
//!
//! eu-id AIR form (proven via `ScalarModMul` with external limb links):
//! ```text
//!     bit = 0  ⇔  s2_signed = +s2_abs  ⇔  k · s2_abs − q · n + s1 = 0  ⇔  selected_s1 = n − s1
//!     bit = 1  ⇔  s2_signed = −s2_abs  ⇔  k · s2_abs − q · n − s1 = 0  ⇔  selected_s1 =    s1
//! ```
//! The polarity matches `signed_hint_point` (`bit = 1` ⇒ `R = −h`).
//!
//! Three witness-time identities are checked via `debug_assert!` to catch
//! every sign/polarity bug immediately:
//!     (1) Garaga:      `s1_signed + k · s2_signed ≡ 0 mod n`
//!     (2) AIR integer: `k · s2_abs − q · n ± s1 = 0` in the chosen branch
//!     (3) Result:      `k · s2_abs ≡ selected_s1 (mod n)`
//!
//! This module is a witness builder — verifier soundness must not depend on
//! the `num_bigint` / `num_integer` crates; the AIR proves the identity
//! independently.

use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Signed, Zero};
use stwo_p256_utils::scalar_arithmetic::P256_ORDER;

use crate::types::U256;

/// Maximum bit length of each component (`s1`, `s2_abs`, `q`) returned by
/// the decomposer. For P-256 this matches `⌈log₂(n) / 2⌉ = 128`.
pub const FAKE_GLV_BOUND_BITS: usize = 128;

/// Output of [`decompose_scalar_mod_n`]. All magnitudes are bounded by
/// `2^FAKE_GLV_BOUND_BITS`. For `scalar == 0` every field is zero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FakeGlvDecomposition {
    /// Positive magnitude of `s1` (Garaga invariant: `s1 > 0` whenever
    /// `scalar != 0`). Strictly less than `2^128`.
    pub s1: U256,
    /// `|s2_signed|`. Greater than zero whenever `scalar != 0`, strictly
    /// less than `2^128`.
    pub s2_abs: U256,
    /// eu-id polarity: `false ⇒ s2_signed = +s2_abs`,
    /// `true ⇒ s2_signed = −s2_abs`.
    pub s2_sign_bit: bool,
    /// AIR-form quotient. Always `≥ 0`, strictly less than `2^128`.
    pub q: U256,
}

impl FakeGlvDecomposition {
    /// All-zero decomposition; corresponds to `scalar == 0`.
    pub const ZERO: Self = Self {
        s1: U256::ZERO,
        s2_abs: U256::ZERO,
        s2_sign_bit: false,
        q: U256::ZERO,
    };
}

/// Decompose `scalar mod n` via Garaga's half-GCD lattice and convert to
/// the eu-id AIR-form quadruple `(s1, s2_abs, s2_sign_bit, q)`. Returns
/// `None` if the lattice degenerates (e.g. pathological inputs like
/// `scalar = n − 1`) or if any output exceeds `2^128`.
pub fn decompose_scalar_mod_n(scalar: &U256) -> Option<FakeGlvDecomposition> {
    let n: BigInt = biguint_from_u256(&U256::from_le_u64s(&P256_ORDER)).into();
    let n_unsigned = n.to_biguint().expect("n > 0");
    let k = BigInt::from(biguint_from_u256(scalar).mod_floor(&n_unsigned));
    if k.is_zero() {
        return Some(FakeGlvDecomposition::ZERO);
    }

    // --- Garaga half-GCD lattice on (n, k) ---
    let (mut s1_signed, mut s2_signed) = precompute_lattice_v1(&n, &k);

    // Witness assertion 1: Garaga identity.
    debug_assert_eq!(
        (&s1_signed + &k * &s2_signed).mod_floor(&n),
        BigInt::zero(),
        "Garaga: s1 + k·s2_signed ≡ 0 mod n",
    );

    // Normalize: force `s1 > 0`. Relation is invariant under `V1 → −V1`.
    if s1_signed.sign() == Sign::Minus {
        s1_signed = -s1_signed;
        s2_signed = -s2_signed;
    }
    if s1_signed.is_zero() || s2_signed.is_zero() {
        // Pathological scalar (e.g. `k = n − 1` can degenerate); caller may
        // special-case via a Garaga-style remap (`k → 1` with adjusted hint
        // point). For now signal that no bounded hint was found.
        return None;
    }

    let bound = BigInt::one() << FAKE_GLV_BOUND_BITS;
    if s1_signed >= bound || s2_signed.abs() >= bound {
        return None;
    }

    let s1_pos = s1_signed.to_biguint().expect("s1 > 0 after normalize");
    let s2_abs_big = s2_signed.abs();

    // --- Branch-direct q aligned with ScalarModMul's `A·B = Q·n + R` ---
    // ScalarModMul takes `A=k`, `B=s2_abs`, `Q=q`, `R=selected_s1` (the
    // canonical positive residue) and proves the integer identity. We must
    // compute `q` exactly as ScalarModMul does:
    //   `q = (k·s2_abs − selected_s1) / n`
    // which equals `(k·s2_abs − s1)/n` for bit=1 (selected_s1 = s1) and
    // `(k·s2_abs − (n − s1))/n = (k·s2_abs + s1)/n − 1` for bit=0
    // (selected_s1 = n − s1). The two AIR branches share the unified
    // identity `k·s2_abs − q·n − selected_s1 = 0`.
    let (s2_sign_bit, selected_s1, q_unsigned) = if s2_signed.sign() == Sign::Minus {
        // bit = 1 branch: selected_s1 = s1.
        let numerator = &k * &s2_abs_big - BigInt::from(s1_pos.clone());
        debug_assert!(
            numerator.mod_floor(&n).is_zero(),
            "ScalarModMul identity (bit=1): k·s2_abs ≡ s1 (mod n)",
        );
        let q = (&numerator / &n)
            .to_biguint()
            .expect("q ≥ 0 by construction (bit=1)");
        (true, s1_pos.clone(), q)
    } else {
        // bit = 0 branch: selected_s1 = n − s1.
        // `k·s2_abs ≡ n − s1 (mod n)` ⇔ `k·s2_abs ≡ −s1 (mod n)` ⇔ Garaga.
        let selected_s1 = &n_unsigned - &s1_pos;
        let numerator = &k * &s2_abs_big - BigInt::from(selected_s1.clone());
        debug_assert!(
            numerator.mod_floor(&n).is_zero(),
            "ScalarModMul identity (bit=0): k·s2_abs ≡ n − s1 (mod n)",
        );
        let q_signed = &numerator / &n;
        if q_signed.sign() == Sign::Minus {
            // Pathological corner where `k·s2_abs < n − s1`. The
            // ScalarModMul convention requires `q ≥ 0`, so signal failure.
            return None;
        }
        let q = q_signed
            .to_biguint()
            .expect("q ≥ 0 after the negative-q early return");
        (false, selected_s1, q)
    };

    if BigInt::from(q_unsigned.clone()) >= bound {
        return None;
    }

    // Witness assertion 3: third independent identity catches `selected_s1`
    // bugs that the first two assertions might miss.
    debug_assert_eq!(
        (BigInt::from(biguint_from_u256(scalar)) * &s2_abs_big).mod_floor(&n),
        BigInt::from(selected_s1.clone()),
        "selected_s1 must equal k·s2_abs mod n",
    );

    let s2_abs_biguint = s2_abs_big.to_biguint().expect("|s2| ≥ 0");
    Some(FakeGlvDecomposition {
        s1: u256_from_biguint(&s1_pos)?,
        s2_abs: u256_from_biguint(&s2_abs_biguint)?,
        s2_sign_bit,
        q: u256_from_biguint(&q_unsigned)?,
    })
}

/// Half-GCD / extended Euclidean state on `(n, k)`. Stops at the first
/// remainder magnitude `< ⌊√n⌋`. Maintains the triple
/// `(rem_i, s_i, t_i)` such that `rem_i = s_i · n + t_i · k`.
///
/// Returns `V1 = (rem, −t)` so that `rem + k · (−t) ≡ 0 (mod n)`,
/// which is the canonical short basis vector of the GLV lattice.
fn precompute_lattice_v1(n: &BigInt, k: &BigInt) -> (BigInt, BigInt) {
    let mut prev = (n.clone(), BigInt::one(), BigInt::zero());
    let mut curr = (k.clone(), BigInt::zero(), BigInt::one());
    let sqrt_n = n.sqrt();
    while curr.0.abs() >= sqrt_n {
        let q = &prev.0 / &curr.0;
        let next = (
            &prev.0 - &q * &curr.0,
            &prev.1 - &q * &curr.1,
            &prev.2 - &q * &curr.2,
        );
        prev = curr;
        curr = next;
    }
    (curr.0, -curr.2)
}

fn biguint_from_u256(value: &U256) -> BigUint {
    BigUint::from_bytes_be(&value.0)
}

fn u256_from_biguint(value: &BigUint) -> Option<U256> {
    let bytes = value.to_bytes_be();
    if bytes.len() > 32 {
        return None;
    }
    let mut out = [0u8; 32];
    out[32 - bytes.len()..].copy_from_slice(&bytes);
    Some(U256(out))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n_biguint() -> BigUint {
        biguint_from_u256(&U256::from_le_u64s(&P256_ORDER))
    }

    fn u256_from_biguint_unwrap(value: &BigUint) -> U256 {
        u256_from_biguint(value).expect("fits in 256 bits")
    }

    fn check_decomposition(scalar: &U256) {
        let n = BigInt::from(n_biguint());
        let bound = BigInt::one() << FAKE_GLV_BOUND_BITS;
        let decomp = decompose_scalar_mod_n(scalar).expect("decomposition found");

        let k = BigInt::from(biguint_from_u256(scalar).mod_floor(&n.to_biguint().unwrap()));
        if k.is_zero() {
            assert_eq!(decomp, FakeGlvDecomposition::ZERO);
            return;
        }

        let s1 = BigInt::from(biguint_from_u256(&decomp.s1));
        let s2_abs = BigInt::from(biguint_from_u256(&decomp.s2_abs));
        let q = BigInt::from(biguint_from_u256(&decomp.q));
        let s2_signed = if decomp.s2_sign_bit {
            -&s2_abs
        } else {
            s2_abs.clone()
        };

        // 128-bit bounds.
        assert!(s1 > BigInt::zero() && s1 < bound, "s1 bound");
        assert!(s2_abs > BigInt::zero() && s2_abs < bound, "s2_abs bound");
        assert!(q >= BigInt::zero() && q < bound, "q bound");

        // Identity (1): Garaga.
        assert_eq!(
            (&s1 + &k * &s2_signed).mod_floor(&n),
            BigInt::zero(),
            "Garaga identity (k = {k}, bit = {})",
            decomp.s2_sign_bit,
        );

        // Identity (2): ScalarModMul integer equation
        // `k · s2_abs − q · n − selected_s1 = 0` where
        // `selected_s1 = s1` for bit=1 and `selected_s1 = n − s1` for bit=0.
        let selected_s1 = if decomp.s2_sign_bit {
            s1.clone()
        } else {
            &n - &s1
        };
        let air_lhs = &k * &s2_abs - &q * &n - &selected_s1;
        assert_eq!(
            air_lhs,
            BigInt::zero(),
            "ScalarModMul integer identity (k = {k}, bit = {})",
            decomp.s2_sign_bit,
        );
    }

    #[test]
    fn decomposes_zero_scalar() {
        assert_eq!(
            decompose_scalar_mod_n(&U256::ZERO).unwrap(),
            FakeGlvDecomposition::ZERO,
        );
    }

    #[test]
    fn decomposes_one() {
        check_decomposition(&U256::from_le_u64s(&[1, 0, 0, 0]));
    }

    #[test]
    fn decomposes_small_scalar() {
        check_decomposition(&U256::from_le_u64s(&[7, 0, 0, 0]));
    }

    #[test]
    fn decomposes_near_order_scalar() {
        // n − 123: well inside the lattice's "general" regime.
        let scalar = u256_from_biguint_unwrap(&(n_biguint() - BigUint::from(123u32)));
        check_decomposition(&scalar);
    }

    #[test]
    fn decomposes_half_order_scalar() {
        let scalar = u256_from_biguint_unwrap(&(n_biguint() / 2u32));
        check_decomposition(&scalar);
    }

    #[test]
    fn decomposes_2_pow_128_minus_1() {
        // Largest scalar that *could* satisfy the trivial hint — the
        // general decomposer must still produce a valid bounded triple.
        let mut scalar = U256::ZERO;
        scalar.0[16..].copy_from_slice(&[0xFFu8; 16]);
        check_decomposition(&scalar);
    }

    #[test]
    fn decomposes_2_pow_128() {
        // First scalar above the trivial hint's window.
        let mut scalar = U256::ZERO;
        scalar.0[15] = 0x01;
        check_decomposition(&scalar);
    }
}
