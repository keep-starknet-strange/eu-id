//! Top-level ML-DSA-65 verification (FIPS 204 Algorithm 3 `ML-DSA.Verify`,
//! pure mode, delegating to Algorithm 8 `ML-DSA.Verify_internal`).
//!
//! [`verify_internals`] runs the whole algorithm and returns a [`VerifyTrace`]
//! exposing every intermediate the future witness generator needs: the decoded
//! `ρ`, `t1`, the hashes `tr` and `µ`, the challenge `c` (both coefficient and
//! NTT domain), the response `ẑ`, the approximate commitment
//! `w'approx = A·z − c·t1·2^d` in both domains, the recovered `w1'`, the sponge
//! transcripts for `µ`, `c̃`, and `SampleInBall`, and the final verdict.
//!
//! ## The µ domain prefix (a common bug)
//!
//! Algorithm 3 computes `µ = H( tr ‖ IntegerToBytes(0,1) ‖
//! IntegerToBytes(|ctx|,1) ‖ ctx ‖ M , 512 )`, where `tr = H(pk, 512)`. The two
//! leading bytes are: `0x00` (the domain separator selecting *pure*, non
//! pre-hash mode) and `|ctx|` (the context length). For the mdoc use, `ctx` is
//! empty, so the prefix is `tr ‖ 0x00 ‖ 0x00 ‖ M`. Getting either byte wrong
//! silently breaks interop with every conformant signer.

use crate::constants::{C_TILDE_BYTES, D, GAMMA1, K, L, N, TAU};
use crate::reference::decompose::{use_hint_poly, w1_encode};
use crate::reference::encoding::{pk_decode, sig_decode, PublicKey, SignatureParts};
use crate::reference::error::{MlDsaError, RejectReason};
use crate::reference::expand_a::expand_a;
use crate::reference::ntt::{ntt, ntt_inverse, pointwise, NttPoly, Poly};
use crate::reference::sample_in_ball::sample_in_ball;
use crate::reference::sponge::{shake256, SpongeTranscript};

/// Domain separator byte for *pure* (non pre-hash) ML-DSA (Algorithm 3).
const DOMAIN_SEP_PURE: u8 = 0x00;
/// SHAKE-256 output length for `tr` and `µ`: 64 bytes (512 bits).
const HASH64: usize = 64;

/// Every intermediate produced by [`verify_internals`], for the witness
/// generator and for auditing. Field names track FIPS 204 notation.
#[derive(Clone, Debug)]
pub struct VerifyTrace {
    /// Matrix seed `ρ` decoded from the public key.
    pub rho: [u8; 32],
    /// `t1`, `k` polynomials decoded from the public key.
    pub t1: [[u32; N]; K],
    /// `tr = H(pk, 512)`, the 64-byte public-key digest.
    pub tr: [u8; HASH64],
    /// `µ = H(tr ‖ 0x00 ‖ |ctx| ‖ ctx ‖ M, 512)`, 64 bytes.
    pub mu: [u8; HASH64],
    /// Commitment hash `c̃` from the signature.
    pub c_tilde: [u8; C_TILDE_BYTES],
    /// Challenge polynomial `c` in the coefficient domain (`{−1,0,1}`).
    pub c: [i32; N],
    /// Challenge polynomial `ĉ = NTT(c)`.
    pub c_hat: NttPoly,
    /// Response `z` (coefficient domain) from the signature.
    pub z: [[i32; N]; L],
    /// `ẑ = NTT(z)` per column.
    pub z_hat: [NttPoly; L],
    /// `w'approx = A·z − c·t1·2^d` in the coefficient domain, `k` polynomials.
    pub w_approx: [[u32; N]; K],
    /// `ŵ'approx`, the same vector in the NTT domain.
    pub w_approx_hat: [NttPoly; K],
    /// `w1' = UseHint(h, w'approx)`, `k` polynomials of values in `[0, 16)`.
    pub w1: [[u32; N]; K],
    /// Recomputed commitment hash `c̃' = H(µ ‖ w1Encode(w1'), 2λ)`.
    pub c_tilde_prime: [u8; C_TILDE_BYTES],
    /// SHAKE-256 transcript that produced `µ`.
    pub mu_transcript: SpongeTranscript,
    /// SHAKE-256 transcript that produced `c̃'`.
    pub c_tilde_transcript: SpongeTranscript,
    /// SHAKE-256 transcript inside `SampleInBall`.
    pub sample_in_ball_transcript: SpongeTranscript,
    /// The reject reason (or [`RejectReason::Accepted`]).
    pub reason: RejectReason,
    /// Final verdict: `reason == Accepted`.
    pub accepted: bool,
}

/// Verify an ML-DSA-65 signature in pure mode with empty context (the mdoc
/// path). Thin wrapper over [`verify_internals_with_context`].
pub fn verify_internals(
    pk: &[u8],
    msg: &[u8],
    sig: &[u8],
) -> Result<VerifyTrace, MlDsaError> {
    verify_internals_with_context(pk, msg, &[], sig)
}

/// Verify an ML-DSA-65 signature in pure mode (FIPS 204 Algorithm 3), with an
/// explicit signing context `ctx`. `ctx` empty is the common case; ACVP
/// external+pure vectors may carry a non-empty context.
pub fn verify_internals_with_context(
    pk: &[u8],
    msg: &[u8],
    ctx: &[u8],
    sig: &[u8],
) -> Result<VerifyTrace, MlDsaError> {
    if ctx.len() > 255 {
        return Err(MlDsaError::ContextTooLong { got: ctx.len() });
    }
    let PublicKey { rho, t1 } = pk_decode(pk)?;
    let SignatureParts { c_tilde, z, h } = sig_decode(sig)?;

    // tr = H(pk, 512).
    let (tr_vec, _) = shake256(&[pk], HASH64);
    let mut tr = [0u8; HASH64];
    tr.copy_from_slice(&tr_vec);

    // µ = H(tr ‖ 0x00 ‖ |ctx| ‖ ctx ‖ M, 512). The two leading bytes 0x00,|ctx|
    // are the pure-mode domain prefix — see the module docs.
    let ctx_len = [ctx.len() as u8];
    let (mu_vec, mu_transcript) =
        shake256(&[&tr, &[DOMAIN_SEP_PURE], &ctx_len, ctx, msg], HASH64);
    let mut mu = [0u8; HASH64];
    mu.copy_from_slice(&mu_vec);

    // c = SampleInBall(c̃); ĉ = NTT(c).
    let sib = sample_in_ball(&c_tilde);
    let c = sib.c;
    let c_poly = signed_to_zq(&c);
    let c_hat = ntt(&c_poly);

    // ẑ = NTT(z) per column.
    let mut z_hat = [[0u32; N]; L];
    for (dst, col) in z_hat.iter_mut().zip(z.iter()) {
        *dst = ntt(&signed_to_zq(col));
    }

    // Â = ExpandA(ρ).
    let a = expand_a(&rho);

    // t1·2^d in the NTT domain, per row.
    let two_d = 1u32 << D;
    let mut t1_2d_hat = [[0u32; N]; K];
    for r in 0..K {
        let mut scaled = [0u32; N];
        for i in 0..N {
            scaled[i] = ((t1[r][i] as u64 * two_d as u64) % crate::constants::Q as u64) as u32;
        }
        t1_2d_hat[r] = ntt(&scaled);
    }

    // ŵ'approx[r] = Σ_s Â[r][s]·ẑ[s] − ĉ·(t1·2^d)^[r].
    let mut w_approx_hat = [[0u32; N]; K];
    let mut w_approx = [[0u32; N]; K];
    for r in 0..K {
        let mut acc = [0u32; N];
        for (a_rs, z_s) in a.matrix[r].iter().zip(z_hat.iter()) {
            let prod = pointwise(a_rs, z_s);
            acc = add_ntt(&acc, &prod);
        }
        let ct = pointwise(&c_hat, &t1_2d_hat[r]);
        let row_hat = sub_ntt(&acc, &ct);
        w_approx_hat[r] = row_hat;
        w_approx[r] = ntt_inverse(&row_hat);
    }

    // w1' = UseHint(h, w'approx).
    let mut w1 = [[0u32; N]; K];
    for r in 0..K {
        w1[r] = use_hint_poly(&h[r], &w_approx[r]);
    }

    // c̃' = H(µ ‖ w1Encode(w1'), 2λ).
    let w1_bytes = w1_encode(&w1);
    let (ctp_vec, c_tilde_transcript) = shake256(&[&mu, &w1_bytes], C_TILDE_BYTES);
    let mut c_tilde_prime = [0u8; C_TILDE_BYTES];
    c_tilde_prime.copy_from_slice(&ctp_vec);

    // Verdict: z-norm bound then commitment equality (Algorithm 8).
    let reason = if !z_norm_in_bound(&z) {
        RejectReason::ZNormOutOfBound
    } else if c_tilde_prime != c_tilde {
        RejectReason::CommitmentMismatch
    } else {
        RejectReason::Accepted
    };
    let accepted = reason == RejectReason::Accepted;

    Ok(VerifyTrace {
        rho,
        t1,
        tr,
        mu,
        c_tilde,
        c,
        c_hat,
        z,
        z_hat,
        w_approx,
        w_approx_hat,
        w1,
        c_tilde_prime,
        mu_transcript,
        c_tilde_transcript,
        sample_in_ball_transcript: sib.transcript,
        reason,
        accepted,
    })
}

/// Boolean-only verification, discarding the trace. Convenience wrapper.
pub fn verify(pk: &[u8], msg: &[u8], sig: &[u8]) -> bool {
    verify_internals(pk, msg, sig)
        .map(|t| t.accepted)
        .unwrap_or(false)
}

/// `‖z‖_∞ < γ1 − β` (Algorithm 8). `β = τ·η`; the check keeps `z` small enough
/// that the honest signer's rejection sampling could have produced it.
fn z_norm_in_bound(z: &[[i32; N]; L]) -> bool {
    let bound = (GAMMA1 - crate::constants::BETA) as i32;
    z.iter()
        .flatten()
        .all(|&c| c.abs() < bound)
}

/// Lift signed `{−1,0,1}`-style coefficients into `[0, q)`.
fn signed_to_zq(coeffs: &[i32; N]) -> Poly {
    let q = crate::constants::Q as i64;
    let mut out = [0u32; N];
    for i in 0..N {
        out[i] = (coeffs[i] as i64).rem_euclid(q) as u32;
    }
    out
}

#[inline]
fn add_ntt(a: &NttPoly, b: &NttPoly) -> NttPoly {
    let mut out = [0u32; N];
    for i in 0..N {
        let s = a[i] + b[i];
        out[i] = if s >= crate::constants::Q {
            s - crate::constants::Q
        } else {
            s
        };
    }
    out
}

#[inline]
fn sub_ntt(a: &NttPoly, b: &NttPoly) -> NttPoly {
    let mut lifted = [0i32; N];
    for i in 0..N {
        lifted[i] = a[i] as i32 - b[i] as i32;
    }
    signed_to_zq(&lifted)
}

// TAU pins the SampleInBall contract this module relies on.
const _: () = assert!(TAU == 49);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wrong_length_inputs_are_hard_errors() {
        assert!(verify_internals(&[0u8; 5], b"m", &[0u8; crate::constants::SIG_BYTES]).is_err());
        assert!(verify_internals(&[0u8; crate::constants::PK_BYTES], b"m", &[0u8; 5]).is_err());
    }

    #[test]
    fn context_over_255_rejected() {
        let ctx = [0u8; 256];
        let e = verify_internals_with_context(
            &[0u8; crate::constants::PK_BYTES],
            b"m",
            &ctx,
            &[0u8; crate::constants::SIG_BYTES],
        );
        assert!(matches!(e, Err(MlDsaError::ContextTooLong { got: 256 })));
    }
}
