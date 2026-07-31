//! Byte-level decoding of the public key and signature (FIPS 204 §§7.1 and 7.2).
//!
//! - `pkDecode` (Algorithm 23) → `(ρ, t1)`; `t1` uses `SimpleBitUnpack` at 10
//!   bits/coefficient (values already in `[0, 2^10)`).
//! - `sigDecode` (Algorithm 27) → `(c̃, z, h)`; `z` uses `BitUnpack(·, γ1−1, γ1)`
//!   at 20 bits/coefficient (centered around 0), `h` uses `HintBitUnpack`
//!   (Algorithm 21), which also *validates* the hint encoding.
//!
//! Decoding is the verifier's first trust boundary, so malformed lengths and
//! illegal hint encodings are hard errors, not silent truncations.

use crate::constants::{
    C_TILDE_BYTES, GAMMA1, K, L, N, OMEGA, PK_BYTES, SIG_BYTES, T1_BITS, Z_BITS,
};
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
    /// `c̃`, `2λ/8 = 48` bytes; the `SampleInBall` seed and the value compared
    /// against the recomputed commitment.
    pub c_tilde: [u8; C_TILDE_BYTES],
    /// `z`, `l` polynomials with signed coefficients (centered around 0).
    pub z: [[i32; N]; L],
    /// `h`, `k` polynomials of hint bits `{0, 1}`.
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

/// FIPS 204 Algorithm 22 `pkEncode`: inverse of [`pk_decode`]. Packs `ρ` then
/// each `t1` coefficient at `T1_BITS` bits, LSB-first.
pub fn pk_encode(rho: &[u8; 32], t1: &[[u32; N]; K]) -> Vec<u8> {
    let poly_bytes = N * T1_BITS / 8;
    let mut out = Vec::with_capacity(PK_BYTES);
    out.extend_from_slice(rho);
    for poly in t1 {
        let mut w = BitWriter::with_capacity(poly_bytes);
        for &coeff in poly {
            w.write(coeff, T1_BITS);
        }
        out.extend_from_slice(&w.bytes);
    }
    debug_assert_eq!(out.len(), PK_BYTES);
    out
}

/// FIPS 204 Algorithm 26 `sigEncode`: inverse of [`sig_decode`]. `c̃ ‖ z ‖ h`,
/// where `z` uses `BitPack(·, γ1−1, γ1)` (`raw = γ1 − coeff`) and `h` uses
/// `HintBitPack` (Algorithm 20).
pub fn sig_encode(c_tilde: &[u8; C_TILDE_BYTES], z: &[[i32; N]; L], h: &[[u8; N]; K]) -> Vec<u8> {
    let mut out = Vec::with_capacity(SIG_BYTES);
    out.extend_from_slice(c_tilde);

    let z_poly_bytes = N * Z_BITS / 8;
    for poly in z {
        let mut w = BitWriter::with_capacity(z_poly_bytes);
        for &coeff in poly {
            // Inverse of BitUnpack(·, γ1−1, γ1): raw = γ1 − coeff.
            let raw = (GAMMA1 as i32 - coeff) as u32;
            w.write(raw, Z_BITS);
        }
        out.extend_from_slice(&w.bytes);
    }

    // HintBitPack (Algorithm 20): the first ω bytes list the set-hint indices
    // per polynomial in increasing order; the trailing k bytes are running end
    // pointers into that list. Padding stays zero.
    let mut h_bytes = vec![0u8; OMEGA + K];
    let mut index = 0usize;
    for (i, poly) in h.iter().enumerate() {
        for (coeff, &bit) in poly.iter().enumerate() {
            if bit == 1 {
                h_bytes[index] = coeff as u8;
                index += 1;
            }
        }
        h_bytes[OMEGA + i] = index as u8;
    }
    out.extend_from_slice(&h_bytes);

    debug_assert_eq!(out.len(), SIG_BYTES);
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

/// FIPS 204 Algorithm 23 `pkDecode`.
pub fn pk_decode(pk: &[u8]) -> Result<PublicKey, MlDsaError> {
    if pk.len() != PK_BYTES {
        return Err(MlDsaError::BadPublicKeyLength {
            expected: PK_BYTES,
            got: pk.len(),
        });
    }
    let mut rho = [0u8; 32];
    rho.copy_from_slice(&pk[..32]);

    // Each t1 polynomial: 256 coeffs × 10 bits = 320 bytes.
    let poly_bytes = N * T1_BITS / 8;
    let mut t1 = [[0u32; N]; K];
    for (r, poly) in t1.iter_mut().enumerate() {
        let start = 32 + r * poly_bytes;
        let mut reader = BitReader::new(&pk[start..start + poly_bytes]);
        for coeff in poly.iter_mut() {
            *coeff = reader.read(T1_BITS);
        }
    }
    Ok(PublicKey { rho, t1 })
}

/// FIPS 204 Algorithm 27 `sigDecode`. Returns `None`-style error on a malformed
/// hint (Algorithm 21 `HintBitUnpack` rejection).
pub fn sig_decode(sig: &[u8]) -> Result<SignatureParts, MlDsaError> {
    if sig.len() != SIG_BYTES {
        return Err(MlDsaError::BadSignatureLength {
            expected: SIG_BYTES,
            got: sig.len(),
        });
    }
    let mut c_tilde = [0u8; C_TILDE_BYTES];
    c_tilde.copy_from_slice(&sig[..C_TILDE_BYTES]);

    // z: l polynomials, 20 bits/coeff, BitUnpack(·, γ1−1, γ1): value = γ1 − raw.
    let z_poly_bytes = N * Z_BITS / 8; // 640 bytes
    let mut z = [[0i32; N]; L];
    let z_start = C_TILDE_BYTES;
    for (idx, poly) in z.iter_mut().enumerate() {
        let start = z_start + idx * z_poly_bytes;
        let mut reader = BitReader::new(&sig[start..start + z_poly_bytes]);
        for coeff in poly.iter_mut() {
            let raw = reader.read(Z_BITS);
            *coeff = GAMMA1 as i32 - raw as i32;
        }
    }

    // h: HintBitUnpack over the trailing ω + k bytes.
    let h_start = z_start + L * z_poly_bytes;
    let h_bytes = &sig[h_start..h_start + OMEGA + K];
    let h = hint_bit_unpack(h_bytes)?;

    Ok(SignatureParts { c_tilde, z, h })
}

/// FIPS 204 Algorithm 21 `HintBitUnpack`: reconstruct the hint vector `h` and
/// validate the encoding (indices strictly increasing within each polynomial,
/// unused slots zero). Rejects malformed encodings. Several ACVP
/// "modified signature - hint" negatives exercise.
fn hint_bit_unpack(bytes: &[u8]) -> Result<[[u8; N]; K], MlDsaError> {
    let mut h = [[0u8; N]; K];
    let mut index = 0usize; // running position into the first ω bytes
    for i in 0..K {
        let end = bytes[OMEGA + i] as usize;
        if end < index || end > OMEGA {
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
    for &b in &bytes[index..OMEGA] {
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
            pk_decode(&[0u8; 10]),
            Err(MlDsaError::BadPublicKeyLength { .. })
        ));
    }

    #[test]
    fn sig_decode_rejects_bad_length() {
        assert!(matches!(
            sig_decode(&[0u8; 10]),
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
            hint_bit_unpack(&bytes),
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
        let decoded = pk_decode(&pk).unwrap();
        let re = pk_encode(&decoded.rho, &decoded.t1);
        // t1 is only 10 of the low bits per coeff; the encoding is canonical, so
        // decode∘encode∘decode is stable and rho survives verbatim.
        let decoded2 = pk_decode(&re).unwrap();
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
        let sig = sig_encode(&c_tilde, &z, &h);
        assert_eq!(sig.len(), SIG_BYTES);
        let decoded = sig_decode(&sig).unwrap();
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
        let h = hint_bit_unpack(&bytes).unwrap();
        assert_eq!(h[0][3], 1);
        assert_eq!(h[0][7], 1);
        assert_eq!(h[0].iter().filter(|&&x| x == 1).count(), 2);
    }
}
