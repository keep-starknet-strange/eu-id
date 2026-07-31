//! `SampleInBall` (FIPS 204 §7.3, Algorithm 29): expand the 32-byte challenge
//! seed (the first `λ/4` bytes of `c̃`) into the challenge polynomial `c`. The
//! polynomial with exactly `τ = 49` coefficients in `{−1, +1}` and the rest
//! zero.
//!
//! The seed is the whole `c̃` (`λ/4` bytes; ML-DSA-65 `λ = 192 ⇒ 48` bytes are
//! absorbed). The first 8 squeezed bytes form the sign source `s`; subsequent
//! bytes drive Fisher–Yates-style placement.

use crate::constants::{N, TAU};
use crate::reference::sponge::{Shake256Reader, SpongeTranscript};

/// SHAKE-256 rate in bytes (must match `statement::RATE` /
/// `stwo_keccak::constants::N_BYTES_IN_RATE`).
const RATE: usize = 136;

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
    // Squeeze one SHAKE-256 rate block (136 bytes) at a time.
    // the spec's streaming XOF. The recorded transcript is then block-aligned
    // to what the sampler actually consumed
    // (`squeezed.len() == RATE · ceil(consumed_len / RATE)`), which is exactly
    // the stream the in-circuit sponge job replays (`statement::n_squeeze_sib`)
    // and sets the SIB component's log size. Squeezing more bytes would increase
    // that component without adding consumed data.
    let mut reader = Shake256Reader::new(&[c_tilde]);
    let mut stream = reader.read(RATE);

    let mut c = [0i32; N];
    let sign_bits = u64::from_le_bytes(stream[0..8].try_into().expect("8 bytes"));
    let mut sign = sign_bits;
    let mut pos = 8usize;

    for i in (N - TAU)..N {
        // Rejection-sample j ∈ [0, i].
        let j = loop {
            if pos == stream.len() {
                stream.extend(reader.read(RATE));
            }
            let byte = stream[pos];
            pos += 1;
            if (byte as usize) <= i {
                break byte as usize;
            }
        };
        c[i] = c[j];
        c[j] = if sign & 1 == 1 { -1 } else { 1 };
        sign >>= 1;
    }

    let transcript = reader.transcript().clone();
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
