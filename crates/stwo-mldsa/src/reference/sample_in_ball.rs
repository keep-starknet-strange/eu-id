//! `SampleInBall` (FIPS 204 §7.3, Algorithm 29) expands the `λ/4`-byte
//! challenge `c̃` into the challenge polynomial `c`. The selected profile fixes
//! `λ` and the exact number `τ` of coefficients in `{−1, +1}`. All other
//! coefficients are zero.
//!
//! The seed is the whole `c̃`. The first 8 squeezed bytes form the sign source
//! `s`. Later bytes drive Fisher-Yates placement.

use crate::constants::N;
use crate::profile::MlDsaProfile;
use crate::reference::error::MlDsaError;
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
///
/// The circuit profile fixes an explicit squeeze resource cap. ML-DSA-44 uses
/// one 136-byte block. The probability that the 128 candidate bytes after the
/// sign source fail to place all 39 coefficients is approximately 2^-202.929.
/// Exhaustion is a typed error, not an implicit extension of the proof
/// geometry.
pub fn sample_in_ball(
    profile: MlDsaProfile,
    c_tilde: &[u8],
) -> Result<SampleInBallResult, MlDsaError> {
    // Squeeze one SHAKE-256 rate block (136 bytes) at a time from the standard
    // streaming XOF. The recorded transcript is then block-aligned to what the
    // sampler actually consumed
    // (`squeezed.len() == RATE · ceil(consumed_len / RATE)`), which is exactly
    // the stream the in-circuit sponge job replays (`statement::n_squeeze_sib`)
    // and which sets the SIB component's log size. Squeezing more bytes would
    // grow that component without adding consumed data.
    let mut reader = Shake256Reader::new(&[c_tilde]);
    let mut stream = reader.read(RATE);

    let mut c = [0i32; N];
    let sign_bits = u64::from_le_bytes(stream[0..8].try_into().expect("8 bytes"));
    let mut sign = sign_bits;
    let mut pos = 8usize;

    let tau = profile.tau();
    let max_bytes = RATE * profile.sample_in_ball_squeeze_blocks();
    for (accepted, i) in ((N - tau)..N).enumerate() {
        // Rejection-sample j ∈ [0, i].
        let j = loop {
            if pos == stream.len() {
                if stream.len() == max_bytes {
                    return Err(MlDsaError::SampleInBallExhausted {
                        accepted,
                        required: tau,
                        squeeze_bytes: max_bytes,
                    });
                }
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
    Ok(SampleInBallResult { c, transcript })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::profile::ML_DSA_65;

    #[test]
    fn sampled_challenge_has_tau_nonzero_pm1() {
        let c_tilde = [0x42u8; crate::constants::C_TILDE_BYTES];
        let res = sample_in_ball(ML_DSA_65, &c_tilde).unwrap();
        let nonzero = res.c.iter().filter(|&&x| x != 0).count();
        assert_eq!(nonzero, ML_DSA_65.tau(), "exactly τ nonzero coefficients");
        assert!(
            res.c.iter().all(|&x| x == -1 || x == 0 || x == 1),
            "coefficients are in {{-1,0,1}}"
        );
        assert_eq!(res.transcript.absorbed, c_tilde);
    }

    #[test]
    fn deterministic_in_the_seed() {
        let a = sample_in_ball(ML_DSA_65, &[1u8; crate::constants::C_TILDE_BYTES]).unwrap();
        let b = sample_in_ball(ML_DSA_65, &[1u8; crate::constants::C_TILDE_BYTES]).unwrap();
        let c = sample_in_ball(ML_DSA_65, &[2u8; crate::constants::C_TILDE_BYTES]).unwrap();
        assert_eq!(a.c, b.c);
        assert_ne!(a.c, c.c);
    }

    #[test]
    fn mldsa44_one_block_exhaustion_probability_is_below_two_to_minus_202_9() {
        use crate::profile::ML_DSA_44;

        let candidates = RATE - 8;
        let mut state = vec![0.0f64; ML_DSA_44.tau() + 1];
        state[0] = 1.0;
        for _ in 0..candidates {
            let mut next = vec![0.0f64; state.len()];
            next[ML_DSA_44.tau()] += state[ML_DSA_44.tau()];
            for placed in 0..ML_DSA_44.tau() {
                let accept = (N - ML_DSA_44.tau() + placed + 1) as f64 / 256.0;
                next[placed + 1] += state[placed] * accept;
                next[placed] += state[placed] * (1.0 - accept);
            }
            state = next;
        }
        let failure: f64 = state[..ML_DSA_44.tau()].iter().sum();
        assert!((-202.94..-202.92).contains(&failure.log2()));
    }
}
