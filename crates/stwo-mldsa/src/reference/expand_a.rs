//! `ExpandA` (FIPS 204 §7.3, Algorithm 32) and its inner `RejNTTPoly`
//! (Algorithm 30): deterministically expand the 32-byte seed `ρ` into the
//! `k × l` matrix `Â` of NTT-domain polynomials.
//!
//! Each entry `Â[r][s]` is `RejNTTPoly(ρ ‖ IntegerToBytes(s, 1) ‖
//! IntegerToBytes(r, 1))`. The column index is absorbed before the row
//! index (FIPS 204 Algorithm 32, line 3). Each coefficient is rejection-sampled
//! from a 3-byte little-endian value masked to 23 bits, accepted iff `< q`.

use crate::constants::{K, L, N, Q};
use crate::reference::ntt::NttPoly;
use crate::reference::sponge::{Shake128Reader, SpongeTranscript};

/// The expanded matrix `Â` (row-major `k × l`) plus the per-entry sponge
/// transcripts, exposed for the witness generator.
pub struct ExpandedA {
    /// `matrix[r][s] = Â[r][s]`, an NTT-domain polynomial.
    pub matrix: [[NttPoly; L]; K],
    /// `transcripts[r][s]` is the SHAKE-128 transcript for that entry.
    pub transcripts: Vec<Vec<SpongeTranscript>>,
}

/// FIPS 204 Algorithm 30 `RejNTTPoly(ρ')`: reject-sample 256 coefficients in
/// `[0, q)` from a streaming SHAKE-128 output over `ρ'`.
fn rej_ntt_poly(rho_prime: &[&[u8]]) -> (NttPoly, SpongeTranscript) {
    let mut reader = Shake128Reader::new(rho_prime);
    let mut poly = [0u32; N];
    let mut j = 0usize;
    while j < N {
        // Squeeze 3 bytes at a time (one SHAKE-128 rate block yields many; we
        // pull small chunks to keep the recorded stream aligned to the sampler).
        let bytes = reader.read(3);
        let mut z = bytes[0] as u32 | ((bytes[1] as u32) << 8) | ((bytes[2] as u32) << 16);
        z &= 0x7f_ffff; // mask to 23 bits (CoeffFromThreeBytes)
        if z < Q {
            poly[j] = z;
            j += 1;
        }
    }
    (poly, reader.transcript().clone())
}

/// FIPS 204 Algorithm 32 `ExpandA(ρ)`.
pub fn expand_a(rho: &[u8; 32]) -> ExpandedA {
    let mut matrix = [[[0u32; N]; L]; K];
    let mut transcripts = vec![vec![SpongeTranscript::default(); L]; K];
    for r in 0..K {
        for s in 0..L {
            // Domain-separate with (column s, row r) each as one byte.
            let sr = [s as u8, r as u8];
            let (poly, transcript) = rej_ntt_poly(&[rho, &sr[..1], &sr[1..2]]);
            matrix[r][s] = poly;
            transcripts[r][s] = transcript;
        }
    }
    ExpandedA {
        matrix,
        transcripts,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expand_a_shapes_and_ranges() {
        let rho = [3u8; 32];
        let a = expand_a(&rho);
        for r in 0..K {
            for s in 0..L {
                assert!(a.matrix[r][s].iter().all(|&c| c < Q));
                // Domain separation: column index absorbed before row index.
                let ds = &a.transcripts[r][s].absorbed[32..34];
                assert_eq!(ds, &[s as u8, r as u8]);
            }
        }
    }

    #[test]
    fn expand_a_is_deterministic() {
        let rho = [9u8; 32];
        let a = expand_a(&rho);
        let b = expand_a(&rho);
        assert_eq!(a.matrix, b.matrix);
    }
}
