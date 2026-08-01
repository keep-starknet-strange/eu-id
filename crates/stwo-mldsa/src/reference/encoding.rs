//! Byte-level decoding of the public key and signature (FIPS 204 §§7.1 and 7.2).
//!
//! - `pkDecode` (Algorithm 23) → `(ρ, t1)`; `t1` uses `SimpleBitUnpack` at 10
//!   bits/coefficient (values already in `[0, 2^10)`).
//! - `sigDecode` (Algorithm 27) → `(c̃, z, h)`; `z` uses `BitUnpack(·, γ1−1, γ1)`
//!   at the selected profile width, and `h` uses `HintBitUnpack`
//!   (Algorithm 21), which also *validates* the hint encoding.
//!
//! Decoding is the verifier's first trust boundary, so malformed lengths and
//! illegal hint encodings are hard errors, not silent truncations.

use crate::constants::{C_TILDE_BYTES, K, L, N, T1_BITS};
#[cfg(test)]
use crate::constants::{GAMMA1, OMEGA, PK_BYTES, SIG_BYTES};
use crate::profile::MlDsaProfile;
#[cfg(test)]
use crate::profile::ML_DSA_65;
use crate::reference::error::MlDsaError;

/// Decoded public key: seed `ρ` and the vector `t1` (`k` polynomials).
#[derive(Clone, Debug)]
pub struct PublicKey {
    /// 32-byte matrix seed.
    pub rho: [u8; 32],
    /// `t1`, `k` polynomials of coefficients in `[0, 2^10)`.
    pub t1: [[u32; N]; K],
}

/// Decoded signature: commitment hash `c̃`, response `z`, and hint `h`.
#[derive(Clone, Debug)]
pub struct SignatureParts {
    /// Maximum storage for `c̃`. The selected `2λ/8`-byte prefix is the
    /// `SampleInBall` seed and the value compared with the recomputed hash.
    pub c_tilde: [u8; C_TILDE_BYTES],
    /// Maximum storage for `z`. The selected `l` polynomials are active.
    pub z: [[i32; N]; L],
    /// Maximum storage for `h`. The selected `k` polynomials are active.
    pub h: [[u8; N]; K],
}

/// Little-endian bit writer, the inverse of [`BitReader`]. Packs `width`-bit
/// values LSB-first into a growing byte buffer.
struct BitWriter {
    bytes: Vec<u8>,
    bit_pos: usize,
}

impl BitWriter {
    fn with_capacity(byte_len: usize) -> Self {
        Self {
            bytes: vec![0u8; byte_len],
            bit_pos: 0,
        }
    }

    /// Write the low `width` bits of `v`, LSB-first.
    fn write(&mut self, v: u32, width: usize) {
        for i in 0..width {
            let bit = ((v >> i) & 1) as u8;
            self.bytes[self.bit_pos / 8] |= bit << (self.bit_pos % 8);
            self.bit_pos += 1;
        }
    }
}

/// FIPS 204 Algorithm 22 `pkEncode` for the selected profile. It packs `ρ`
/// followed by each `t1` coefficient at `T1_BITS` bits, least-significant bit first.
pub fn pk_encode(profile: MlDsaProfile, rho: &[u8; 32], t1: &[[u32; N]; K]) -> Vec<u8> {
    let poly_bytes = N * T1_BITS / 8;
    let mut out = Vec::with_capacity(profile.pk_bytes());
    out.extend_from_slice(rho);
    for poly in &t1[..profile.k()] {
        let mut w = BitWriter::with_capacity(poly_bytes);
        for &coeff in poly {
            w.write(coeff, T1_BITS);
        }
        out.extend_from_slice(&w.bytes);
    }
    debug_assert_eq!(out.len(), profile.pk_bytes());
    out
}

/// FIPS 204 Algorithm 26 `sigEncode` for the selected profile. It encodes
/// `c̃ ‖ z ‖ h`, where `z` uses `BitPack` and `h` uses `HintBitPack`.
pub fn sig_encode(
    profile: MlDsaProfile,
    c_tilde: &[u8; C_TILDE_BYTES],
    z: &[[i32; N]; L],
    h: &[[u8; N]; K],
) -> Vec<u8> {
    let mut out = Vec::with_capacity(profile.sig_bytes());
    out.extend_from_slice(&c_tilde[..profile.c_tilde_bytes()]);

    let z_poly_bytes = N * profile.z_bits() / 8;
    for poly in &z[..profile.l()] {
        let mut w = BitWriter::with_capacity(z_poly_bytes);
        for &coeff in poly {
            let raw = (profile.gamma1() as i32 - coeff) as u32;
            w.write(raw, profile.z_bits());
        }
        out.extend_from_slice(&w.bytes);
    }

    // HintBitPack (Algorithm 20): the first ω bytes list the set-hint indices
    // per polynomial in increasing order; the trailing k bytes are running end
    // pointers into that list. Padding stays zero.
    let mut h_bytes = vec![0u8; profile.omega() + profile.k()];
    let mut index = 0usize;
    for (i, poly) in h[..profile.k()].iter().enumerate() {
        for (coeff, &bit) in poly.iter().enumerate() {
            if bit == 1 {
                h_bytes[index] = coeff as u8;
                index += 1;
            }
        }
        h_bytes[profile.omega() + i] = index as u8;
    }
    out.extend_from_slice(&h_bytes);

    debug_assert_eq!(out.len(), profile.sig_bytes());
    out
}

/// Little-endian bit reader over a byte slice.
struct BitReader<'a> {
    bytes: &'a [u8],
    bit_pos: usize,
}

impl<'a> BitReader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, bit_pos: 0 }
    }

    /// Read `width` bits (≤ 32) as an unsigned integer, LSB-first.
    fn read(&mut self, width: usize) -> u32 {
        let mut v = 0u32;
        for i in 0..width {
            let byte = self.bytes[self.bit_pos / 8];
            let bit = (byte >> (self.bit_pos % 8)) & 1;
            v |= (bit as u32) << i;
            self.bit_pos += 1;
        }
        v
    }
}

/// FIPS 204 Algorithm 23 `pkDecode` for the selected profile.
pub fn pk_decode(profile: MlDsaProfile, pk: &[u8]) -> Result<PublicKey, MlDsaError> {
    if pk.len() != profile.pk_bytes() {
        return Err(MlDsaError::BadPublicKeyLength {
            expected: profile.pk_bytes(),
            got: pk.len(),
        });
    }
    let mut rho = [0u8; 32];
    rho.copy_from_slice(&pk[..32]);

    // Each t1 polynomial: 256 coeffs × 10 bits = 320 bytes.
    let poly_bytes = N * T1_BITS / 8;
    let mut t1 = [[0u32; N]; K];
    for (r, poly) in t1[..profile.k()].iter_mut().enumerate() {
        let start = 32 + r * poly_bytes;
        let mut reader = BitReader::new(&pk[start..start + poly_bytes]);
        for coeff in poly.iter_mut() {
            *coeff = reader.read(T1_BITS);
        }
    }
    Ok(PublicKey { rho, t1 })
}

/// FIPS 204 Algorithm 27 `sigDecode` for the selected profile. It rejects a
/// malformed Algorithm 21 `HintBitUnpack` encoding.
pub fn sig_decode(profile: MlDsaProfile, sig: &[u8]) -> Result<SignatureParts, MlDsaError> {
    if sig.len() != profile.sig_bytes() {
        return Err(MlDsaError::BadSignatureLength {
            expected: profile.sig_bytes(),
            got: sig.len(),
        });
    }
    let mut c_tilde = [0u8; C_TILDE_BYTES];
    c_tilde[..profile.c_tilde_bytes()].copy_from_slice(&sig[..profile.c_tilde_bytes()]);

    // z: l polynomials, 20 bits/coeff, BitUnpack(·, γ1−1, γ1): value = γ1 − raw.
    let z_poly_bytes = N * profile.z_bits() / 8;
    let mut z = [[0i32; N]; L];
    let z_start = profile.c_tilde_bytes();
    for (idx, poly) in z[..profile.l()].iter_mut().enumerate() {
        let start = z_start + idx * z_poly_bytes;
        let mut reader = BitReader::new(&sig[start..start + z_poly_bytes]);
        for coeff in poly.iter_mut() {
            let raw = reader.read(profile.z_bits());
            *coeff = profile.gamma1() as i32 - raw as i32;
        }
    }

    // h: HintBitUnpack over the trailing ω + k bytes.
    let h_start = z_start + profile.l() * z_poly_bytes;
    let h_bytes = &sig[h_start..h_start + profile.omega() + profile.k()];
    let h = hint_bit_unpack(profile, h_bytes)?;

    Ok(SignatureParts { c_tilde, z, h })
}

/// FIPS 204 Algorithm 21 `HintBitUnpack`: reconstruct the hint vector `h` and
/// validate the encoding (indices strictly increasing within each polynomial,
/// unused slots zero). Rejects malformed encodings. Several ACVP
/// "modified signature - hint" negatives exercise.
fn hint_bit_unpack(profile: MlDsaProfile, bytes: &[u8]) -> Result<[[u8; N]; K], MlDsaError> {
    let mut h = [[0u8; N]; K];
    let mut index = 0usize; // running position into the first ω bytes
    for i in 0..profile.k() {
        let end = bytes[profile.omega() + i] as usize;
        if end < index || end > profile.omega() {
            return Err(MlDsaError::MalformedHint);
        }
        let first = index;
        while index < end {
            let coeff = bytes[index] as usize;
            // Indices within one polynomial must be strictly increasing.
            if index > first && bytes[index] <= bytes[index - 1] {
                return Err(MlDsaError::MalformedHint);
            }
            h[i][coeff] = 1;
            index += 1;
        }
    }
    // All remaining "padding" bytes in the first ω region must be zero.
    for &b in &bytes[index..profile.omega()] {
        if b != 0 {
            return Err(MlDsaError::MalformedHint);
        }
    }
    Ok(h)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pk_decode_rejects_bad_length() {
        assert!(matches!(
            pk_decode(ML_DSA_65, &[0u8; 10]),
            Err(MlDsaError::BadPublicKeyLength { .. })
        ));
    }

    #[test]
    fn sig_decode_rejects_bad_length() {
        assert!(matches!(
            sig_decode(ML_DSA_65, &[0u8; 10]),
            Err(MlDsaError::BadSignatureLength { .. })
        ));
    }

    #[test]
    fn hint_bit_unpack_rejects_nonincreasing_indices() {
        let mut bytes = vec![0u8; OMEGA + K];
        // Poly 0 claims two equal hint indices: [5, 5].
        bytes[0] = 5;
        bytes[1] = 5;
        bytes[OMEGA] = 2; // end pointer for poly 0
        assert!(matches!(
            hint_bit_unpack(ML_DSA_65, &bytes),
            Err(MlDsaError::MalformedHint)
        ));
    }

    #[test]
    fn pk_encode_round_trips_decode() {
        // Deterministic pseudo-random pk bytes, decoded then re-encoded.
        let mut pk = vec![0u8; PK_BYTES];
        for (i, b) in pk.iter_mut().enumerate() {
            *b = (i as u32 * 131 + 7) as u8;
        }
        let decoded = pk_decode(ML_DSA_65, &pk).unwrap();
        let re = pk_encode(ML_DSA_65, &decoded.rho, &decoded.t1);
        // t1 is only 10 of the low bits per coeff; the encoding is canonical, so
        // decode∘encode∘decode is stable and rho survives verbatim.
        let decoded2 = pk_decode(ML_DSA_65, &re).unwrap();
        assert_eq!(decoded.rho, decoded2.rho);
        assert_eq!(decoded.t1, decoded2.t1);
        assert_eq!(re.len(), PK_BYTES);
    }

    #[test]
    fn sig_encode_round_trips_decode() {
        let mut c_tilde = [0u8; C_TILDE_BYTES];
        for (i, b) in c_tilde.iter_mut().enumerate() {
            *b = (i as u8).wrapping_mul(3);
        }
        // z coefficients in the valid centered range (|z| < γ1).
        let mut z = [[0i32; N]; L];
        for (j, poly) in z.iter_mut().enumerate() {
            for (i, c) in poly.iter_mut().enumerate() {
                *c = ((i as i32 * 37 + j as i32 * 11) % (2 * GAMMA1 as i32)) - GAMMA1 as i32 + 1;
            }
        }
        // A well-formed hint: a few increasing indices in each poly.
        let mut h = [[0u8; N]; K];
        for (r, poly) in h.iter_mut().enumerate() {
            for t in 0..3 {
                poly[r * 5 + t * 7] = 1;
            }
        }
        let sig = sig_encode(ML_DSA_65, &c_tilde, &z, &h);
        assert_eq!(sig.len(), SIG_BYTES);
        let decoded = sig_decode(ML_DSA_65, &sig).unwrap();
        assert_eq!(decoded.c_tilde, c_tilde);
        assert_eq!(decoded.z, z);
        assert_eq!(decoded.h, h);
    }

    #[test]
    fn hint_bit_unpack_accepts_well_formed() {
        let mut bytes = vec![0u8; OMEGA + K];
        bytes[0] = 3;
        bytes[1] = 7;
        bytes[OMEGA] = 2; // poly 0 ends after 2 indices
        for i in 1..K {
            bytes[OMEGA + i] = 2; // remaining polys empty
        }
        let h = hint_bit_unpack(ML_DSA_65, &bytes).unwrap();
        assert_eq!(h[0][3], 1);
        assert_eq!(h[0][7], 1);
        assert_eq!(h[0].iter().filter(|&&x| x == 1).count(), 2);
    }

    #[test]
    fn mldsa44_wire_lengths_round_trip() {
        use crate::profile::ML_DSA_44;

        let rho = [0x44; 32];
        let mut t1 = [[0u32; N]; K];
        for (index, coefficient) in t1[..ML_DSA_44.k()].iter_mut().flatten().enumerate() {
            *coefficient = (index as u32 * 17) & 0x3ff;
        }
        let pk = pk_encode(ML_DSA_44, &rho, &t1);
        assert_eq!(pk.len(), 1_312);
        let decoded_pk = pk_decode(ML_DSA_44, &pk).unwrap();
        assert_eq!(decoded_pk.rho, rho);
        assert_eq!(decoded_pk.t1, t1);

        let mut c_tilde = [0u8; C_TILDE_BYTES];
        c_tilde[..ML_DSA_44.c_tilde_bytes()].fill(0x5a);
        let mut z = [[0i32; N]; L];
        z[0][0] = ML_DSA_44.gamma1() as i32 - 1;
        z[3][255] = -(ML_DSA_44.gamma1() as i32) + 1;
        let mut h = [[0u8; N]; K];
        h[0][3] = 1;
        h[3][200] = 1;
        let signature = sig_encode(ML_DSA_44, &c_tilde, &z, &h);
        assert_eq!(signature.len(), 2_420);
        let decoded_signature = sig_decode(ML_DSA_44, &signature).unwrap();
        assert_eq!(decoded_signature.c_tilde, c_tilde);
        assert_eq!(decoded_signature.z, z);
        assert_eq!(decoded_signature.h, h);
    }
}
