//! Verifier-native scalar fold for the integer lift.
//!
//! The AIR (`coeffs`) yields each committed poly's `P̂(r,s)` into the
//! `EvalAtRsRelation`. The verifier computes the public `Â_ij`, `t̂1_i`, and
//! `q̂(s)` directly from the transcript-mixed public key. The folded identity
//! consumes the claimed `ẑ_j, ŵ_i, ê_i, v̂_i, ĉ, Ĉ_i` evaluations:
//!
//! ```text
//!   Σ_i ρ_RLC^i·[ Σ_j Â_ij(r,s)·ẑ_j(r,s) − ĉ(r,s)·t̂1_i(r,s) − ŵ_i(r,s)
//!                 − (r^256 + 1)·v̂_i(r,s) − q̂(s)·ê_i(r,s) − (s − B)·Ĉ_i(r,s) ] == 0
//! ```
//!
//! The public evaluations are bivariate:
//! `Â_ij(r,s) = Σ_{m,t} A_{m,t}·s^t·r^m`, NOT `A_ij(r)`. Evaluating the univariate
//! value silently reintroduces the unliftable §2 coefficient-granularity check.
//!
//! `Ĉ_i` is folded here multiplied by `(s − B)` (the AIR emits the raw
//! `Ĉ_i(r,s)` Horner value; the `(s−B)` factor lives on this native side).

// Numeric kernel: `i/j/m` indices are the polynomial coordinates.
#![allow(clippy::needless_range_loop)]

use stwo::core::fields::qm31::SecureField;

use crate::air_util::enc_signed;
use crate::coeffs::layout::{
    POLY_ID_C, POLY_ID_CARRY0, POLY_ID_E0, POLY_ID_V0, POLY_ID_W0, POLY_ID_Z0,
};
use crate::constants::{D, K, L, N};
use crate::profile::ML_DSA_65;
use crate::reference::ntt::ntt_inverse;
use crate::types::MlDsaVerifyInput;
use crate::witness::{balanced_digits, B, Q_DIGITS, T_A, T_T1};

/// Bivariate eval `P̂(r,s) = Σ_{m} (Σ_t d_{m,t}·s^t)·r^m` of a public integer
/// poly given as coefficients (index = m), decomposed into `t_digits` balanced
/// base-B digits. Matches the AIR's high-to-low group Horner: iterate m from the
/// TOP so the forward Horner `acc·r + digit_row` weights coeff m by exactly r^m.
fn bivariate_eval<const T: usize>(coeffs: &[i128], r: SecureField, s: SecureField) -> SecureField {
    let mut acc = SecureField::from(stwo::core::fields::m31::M31::from_u32_unchecked(0));
    for &c in coeffs.iter().rev() {
        let digits = balanced_digits::<T>(c);
        let mut digit_row = SecureField::from(stwo::core::fields::m31::M31::from_u32_unchecked(0));
        let mut s_pow = SecureField::from(stwo::core::fields::m31::M31::from_u32_unchecked(1));
        for &d in &digits {
            digit_row += s_pow * signed_qm31(d);
            s_pow *= s;
        }
        acc = acc * r + digit_row;
    }
    acc
}

/// QM31 embedding of a signed integer (|x| ≪ p).
fn signed_qm31(x: i128) -> SecureField {
    SecureField::from(enc_signed(x))
}

/// Public bivariate evals the verifier computes natively from `(ρ, t1)`.
pub struct PublicEvals {
    /// `Â_ij(r,s)`, indexed `[i][j]`.
    pub a_hat: Vec<Vec<SecureField>>,
    /// `t̂1_i(r,s)` (i.e. `(t1_i·2^d)^(r,s)`), indexed `[i]`.
    pub t1_hat: Vec<SecureField>,
    /// `q̂(s) = 1 − 16 s + 32 s²`.
    pub q_hat: SecureField,
}

/// Assemble the public bivariate evals from precomputed row-major matrix
/// evaluations. Used by [`compute_public_evals`] after native ExpandA.
fn compute_public_evals_from_a(
    input: &MlDsaVerifyInput,
    a_evals: &[SecureField],
    r: SecureField,
    s: SecureField,
) -> PublicEvals {
    assert_eq!(a_evals.len(), K * L, "one matrix evaluation per (i,j)");
    let two_d = 1i128 << D;

    let mut a_hat = vec![vec![SecureField::default(); L]; K];
    for i in 0..K {
        for j in 0..L {
            a_hat[i][j] = a_evals[i * L + j];
        }
    }

    let mut t1_hat = vec![SecureField::default(); K];
    for i in 0..K {
        let coeffs: Vec<i128> = (0..N).map(|m| input.t1[i][m] as i128 * two_d).collect();
        t1_hat[i] = bivariate_eval::<T_T1>(&coeffs, r, s);
    }

    // q̂(s) from its exact digits (1, −16, 32).
    let mut q_hat = SecureField::from(stwo::core::fields::m31::M31::from_u32_unchecked(0));
    let mut s_pow = SecureField::from(stwo::core::fields::m31::M31::from_u32_unchecked(1));
    for &qd in &Q_DIGITS {
        q_hat += s_pow * signed_qm31(qd);
        s_pow *= s;
    }
    PublicEvals {
        a_hat,
        t1_hat,
        q_hat,
    }
}

/// Derive `A` from the public `rho`, invert the NTT, and evaluate the public
/// matrix and `t1` terms bivariately at `(r, s)`.
pub fn compute_public_evals(
    input: &MlDsaVerifyInput,
    r: SecureField,
    s: SecureField,
) -> PublicEvals {
    let a_hat_matrix = crate::reference::expand_a::expand_a(ML_DSA_65, &input.rho);
    let mut a_evals = Vec::with_capacity(K * L);
    for i in 0..K {
        for j in 0..L {
            let poly = ntt_inverse(&a_hat_matrix.matrix[i][j]);
            let coeffs: Vec<i128> = poly.iter().map(|&c| c as i128).collect();
            a_evals.push(bivariate_eval::<T_A>(&coeffs, r, s));
        }
    }
    compute_public_evals_from_a(input, &a_evals, r, s)
}

/// The claimed evaluations the verifier consumes, indexed by poly_id.
pub struct ClaimedEvals<'a>(pub &'a [SecureField]);

impl ClaimedEvals<'_> {
    fn z(&self, j: usize) -> SecureField {
        self.0[POLY_ID_Z0 as usize + j]
    }
    fn w(&self, i: usize) -> SecureField {
        self.0[POLY_ID_W0 as usize + i]
    }
    fn e(&self, i: usize) -> SecureField {
        self.0[POLY_ID_E0 as usize + i]
    }
    fn v(&self, i: usize) -> SecureField {
        self.0[POLY_ID_V0 as usize + i]
    }
    fn c(&self) -> SecureField {
        self.0[POLY_ID_C as usize]
    }
    fn carry(&self, i: usize) -> SecureField {
        self.0[POLY_ID_CARRY0 as usize + i]
    }
}

/// The folded identity value. An honest value is zero.
pub fn folded_check(
    public: &PublicEvals,
    claimed: &ClaimedEvals<'_>,
    rho_rlc: SecureField,
    r: SecureField,
    s: SecureField,
) -> SecureField {
    let one = SecureField::from(stwo::core::fields::m31::M31::from_u32_unchecked(1));
    let b_field = signed_qm31(B);

    // (r^256 + 1): X^256 fold factor.
    let mut r256 = one;
    for _ in 0..N {
        r256 *= r;
    }
    let x_fold = r256 + one;
    let s_minus_b = s - b_field;

    let mut total = SecureField::default();
    let mut rho_pow = one;
    for i in 0..K {
        // Σ_j Â_ij·ẑ_j
        let mut row = SecureField::default();
        for j in 0..L {
            row += public.a_hat[i][j] * claimed.z(j);
        }
        // − ĉ·t̂1_i
        row -= claimed.c() * public.t1_hat[i];
        // − ŵ_i
        row -= claimed.w(i);
        // − (r^256+1)·v̂_i
        row -= x_fold * claimed.v(i);
        // − q̂(s)·ê_i
        row -= public.q_hat * claimed.e(i);
        // − (s − B)·Ĉ_i
        row -= s_minus_b * claimed.carry(i);

        total += rho_pow * row;
        rho_pow *= rho_rlc;
    }
    total
}
