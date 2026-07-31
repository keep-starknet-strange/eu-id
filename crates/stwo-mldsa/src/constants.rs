//! FIPS 204 ML-DSA-65 parameters, pinned to the final standard.
//!
//! All values are taken from *NIST FIPS 204, Module-Lattice-Based Digital
//! Signature Standard* (final, August 2024). Section citations refer to that
//! document. ML-DSA-65 is the "Category 3" parameter set (Table 1, §4).
//!
//! These constants are authoritative for this implementation. Tests compare
//! them with the `ml-dsa` oracle, but the oracle does not define them.

/// Modulus `q = 2^23 − 2^13 + 1 = 8_380_417`. Shared by every ML-DSA parameter
/// set (FIPS 204 §4, Eq. 4.1 / Table 1).
pub const Q: u32 = 8_380_417;

/// Ring degree `n = 256`: every polynomial in `R_q = Z_q[X]/(X^256 + 1)` has
/// 256 coefficients (FIPS 204 §2.3, Table 1).
pub const N: usize = 256;

/// Dropped low-order bits `d = 13` in Power2Round / `t = t1·2^d + t0`
/// (FIPS 204 §4, Table 1; Algorithm 35 `Power2Round`).
pub const D: u32 = 13;

/// Rows of the matrix `A` / length of the `t`, `w`, `s2` vectors: `k = 6`
/// (FIPS 204 §4, Table 1).
pub const K: usize = 6;

/// Columns of `A` / length of the `z`, `s1`, `y` vectors: `l = 5`
/// (FIPS 204 §4, Table 1).
pub const L: usize = 5;

/// Number of ±1 entries in the challenge polynomial `c`: `τ = 49`
/// (FIPS 204 §4, Table 1; Algorithm 29 `SampleInBall`).
pub const TAU: usize = 49;

/// Coefficient range of the mask `y` and signature part `z`:
/// `γ1 = 2^19 = 524_288` (FIPS 204 §4, Table 1).
pub const GAMMA1: u32 = 1 << 19;

/// Low-order rounding range: `γ2 = (q − 1) / 32 = 261_888`
/// (FIPS 204 §4, Table 1; used by Decompose / UseHint / w1Encode).
pub const GAMMA2: u32 = (Q - 1) / 32;

/// Maximum number of `1`s in the hint `h`: `ω = 55` (FIPS 204 §4, Table 1;
/// Algorithm 20 `HintBitPack` / Algorithm 21 `HintBitUnpack`).
pub const OMEGA: usize = 55;

/// Secret-key coefficient bound: `η = 4` (FIPS 204 §4, Table 1). Not needed by
/// verification (which never sees `s1`, `s2`) but pinned for completeness.
pub const ETA: u32 = 4;

/// Rejection bound `β = τ · η = 49 · 4 = 196` (FIPS 204 §4, Table 1). The
/// verifier checks `‖z‖_∞ < γ1 − β` (Algorithm 8, step 3 uses `γ1 − β`).
pub const BETA: u32 = TAU as u32 * ETA;

/// Collision-strength parameter `λ = 192` bits ⇒ the commitment hash `c̃` is
/// `2λ/8 = 48` bytes (FIPS 204 §4, Table 1; Algorithm 29 seeds SampleInBall
/// from the first 32 bytes of `c̃`).
pub const LAMBDA: usize = 192;

/// Byte length of the commitment hash `c̃`: `2λ/8 = 48` bytes
/// (FIPS 204 §4, Table 1; §7.2 `sigEncode`).
pub const C_TILDE_BYTES: usize = 2 * LAMBDA / 8;

/// Encoded public-key length in bytes: `32 + 32·k·(bitlen(q−1) − d)`
/// `= 32 + 32·6·(23 − 13) = 1952` (FIPS 204 §4, Table 2; Algorithm 22 `pkEncode`).
pub const PK_BYTES: usize = 1952;

/// Encoded signature length in bytes: `c̃ ‖ z ‖ h`
/// `= 48 + 32·l·(1 + bitlen(γ1−1)) + (ω + k)`
/// `= 48 + 32·5·20 + 61 = 3309` (FIPS 204 §4, Table 2; Algorithm 26 `sigEncode`).
pub const SIG_BYTES: usize = 3309;

/// Bit width used to pack each `t1` coefficient: `bitlen(q−1) − d = 23 − 13 = 10`
/// (FIPS 204 §7.2, Algorithm 22 `pkEncode` packs `t1` at 10 bits per coeff).
pub const T1_BITS: usize = 10;

/// Bit width used to pack each `z` coefficient: `1 + bitlen(γ1 − 1) = 1 + 19 = 20`
/// (FIPS 204 §7.2, Algorithm 26 `sigEncode`; `BitPack(z, γ1−1, γ1)`).
pub const Z_BITS: usize = 20;

/// Bit width used to pack each `w1` coefficient in `w1Encode`:
/// `bitlen((q−1)/(2·γ2) − 1) = bitlen(15) = 4` (FIPS 204 §7.4, Algorithm 28
/// `w1Encode`; for ML-DSA-65 each `w1` coefficient is in `[0, 15]`).
pub const W1_BITS: usize = 4;

/// ζ = 1753, the primitive 512-th root of unity mod `q` that generates the NTT
/// (FIPS 204 §7.5, Appendix B; `zetas[i] = ζ^{brv(i)} mod q`).
pub const ZETA: u32 = 1753;

// ---------------------------------------------------------------------------
// COSE / IANA identifiers for the mdoc issuerAuth `COSE_Sign1`.
// ---------------------------------------------------------------------------

/// COSE algorithm identifier for ML-DSA-65 in the issuer `protected` header
/// (`alg` label `1`).
///
/// RFC 9964 and the IANA COSE Algorithms registry assign `-49`.
pub const COSE_ALG_ML_DSA_65: i64 = -49;

/// COSE Key Type (`kty`) for the "AKP" (Algorithm Key Pair) family that carries
/// ML-DSA keys. RFC 9964 and the IANA COSE Key Types registry assign `7`.
pub const COSE_KTY_AKP: i64 = 7;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn derived_constants_are_self_consistent() {
        assert_eq!(Q, (1 << 23) - (1 << 13) + 1);
        assert_eq!(GAMMA1, 524_288);
        assert_eq!(GAMMA2, 261_888);
        assert_eq!(BETA, 196);
        assert_eq!(C_TILDE_BYTES, 48);
        // pkEncode: 32 (ρ) + k·(n·T1_BITS/8) = 32 + 6·320 = 1952.
        assert_eq!(PK_BYTES, 32 + K * (N * T1_BITS / 8));
        // sigEncode: 48 (c̃) + l·(n·Z_BITS/8) (z) + (ω + k) (h) = 48 + 5·640 + 61.
        assert_eq!(
            SIG_BYTES,
            C_TILDE_BYTES + L * (N * Z_BITS / 8) + (OMEGA + K)
        );
        // w1 range [0,15] ⇒ (q−1)/(2·γ2) = 16 values ⇒ 4 bits.
        assert_eq!((Q - 1) / (2 * GAMMA2), 16);
        assert_eq!(W1_BITS, 4);
    }
}
