//! `SampleInBall` (FIPS 204 §7.3, Algorithm 29): expand the 32-byte challenge
//! seed (the first `λ/4` bytes of `c̃`) into the challenge polynomial `c` — a
//! polynomial with exactly `τ = 49` coefficients in `{−1, +1}` and the rest
//! zero.
//!
//! The seed is the whole `c̃` (`λ/4` bytes; ML-DSA-65 `λ = 192 ⇒ 48` bytes are
//! absorbed). The first 8 squeezed bytes form the sign source `s`; subsequent
//! bytes drive Fisher–Yates-style placement.

use crate::constants::{N, TAU};
use crate::reference::sponge::{shake256, SpongeTranscript};

/// Result of `SampleInBall`, with the recorded sponge transcript exposed for
/// the witness generator.
#[derive(Clone, Debug)]
pub struct SampleInBallResult {
    /// The challenge polynomial `c`, coefficients in `{−1, 0, +1}` represented
    /// as signed `i32` (so callers can lift to `Z_q` however they need).
    pub c: [i32; N],
    /// The SHAKE-256 transcript (absorbed `c̃`, squeezed stream) that produced `c`.
    pub transcript: SpongeTranscript,
}

/// FIPS 204 Algorithm 29 `SampleInBall(ρ)` where `ρ = c̃`.
///
/// Squeezes an unbounded SHAKE-256 stream: the first 8 bytes are the sign bits
/// `s`, then for each `i ∈ [n−τ, n)` a rejection-sampled index `j ≤ i` is drawn
/// and `c[i] ← c[j]; c[j] ← (−1)^{bit}`.
pub fn sample_in_ball(c_tilde: &[u8]) -> SampleInBallResult {
    // Squeeze generously: 8 sign bytes + a stream long enough that the
    // rejection sampler never exhausts it in practice (τ placements, each
    // needing on average slightly more than one byte). 8 + 256 is comfortably
    // beyond the worst realistic case; if it ever ran short we would panic
    // below rather than return a wrong result.
    let (stream, transcript) = shake256(&[c_tilde], 8 + 8 * N);

    let mut c = [0i32; N];
    let sign_bits = u64::from_le_bytes(stream[0..8].try_into().expect("8 bytes"));
    let mut sign = sign_bits;
    let mut pos = 8usize;

    for i in (N - TAU)..N {
        // Rejection-sample j ∈ [0, i].
        let j = loop {
            let byte = *stream
                .get(pos)
                .expect("SampleInBall stream exhausted (increase squeeze length)");
            pos += 1;
            if (byte as usize) <= i {
                break byte as usize;
            }
        };
        c[i] = c[j];
        c[j] = if sign & 1 == 1 { -1 } else { 1 };
        sign >>= 1;
    }

    SampleInBallResult { c, transcript }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sampled_challenge_has_tau_nonzero_pm1() {
        let c_tilde = [0x42u8; crate::constants::C_TILDE_BYTES];
        let res = sample_in_ball(&c_tilde);
        let nonzero = res.c.iter().filter(|&&x| x != 0).count();
        assert_eq!(nonzero, TAU, "exactly τ nonzero coefficients");
        assert!(
            res.c.iter().all(|&x| x == -1 || x == 0 || x == 1),
            "coefficients are in {{-1,0,1}}"
        );
        assert_eq!(res.transcript.absorbed, c_tilde);
    }

    #[test]
    fn deterministic_in_the_seed() {
        let a = sample_in_ball(&[1u8; crate::constants::C_TILDE_BYTES]);
        let b = sample_in_ball(&[1u8; crate::constants::C_TILDE_BYTES]);
        let c = sample_in_ball(&[2u8; crate::constants::C_TILDE_BYTES]);
        assert_eq!(a.c, b.c);
        assert_ne!(a.c, c.c);
    }
}
