//! Serializable public/private inputs to in-circuit ML-DSA-65 verification.
//!
//! Mirrors `stwo-p256`'s [`EcdsaVerifyInput`](../../stwo-p256/src/types.rs)
//! serde conventions: a single `#[derive(Serialize, Deserialize)]` struct whose
//! fields are the semantically-decoded verification inputs (not raw wire bytes),
//! so a caller can construct one by name and the witness generator (M2) /
//! future AIR (M4/M5) consume typed values directly.
//!
//! ## What is public vs private
//!
//! Public (enters the transcript via public-input mixing — S5 [BIND], I-4):
//! `rho`, `t1`, `tr`, `message`. Private (the signature, kept off the public
//! transcript for unlinkability): `c_tilde`, `z`, `hint`. All are carried in
//! one struct because the *prover* needs every field to build the witness; the
//! public/private split is a property of how each field is later bound, not of
//! this container.
//!
//! ## `t1` form (M4 consumption)
//!
//! `t1` is stored **decoded** (`[[u32; N]; K]`, coefficients in `[0, 2^10)`) —
//! the form the S5a integer-lift identity needs: the verifier evaluates the
//! public term `c·t1_i·2^d` natively from these coefficients (worksheet §3.2),
//! so M4 wants decoded `u32` coefficients, not the packed 10-bit encoding. The
//! `rho` and `tr` are byte arrays because they are only ever hashed / mixed,
//! never arithmetized.

use serde::{Deserialize, Serialize};

use crate::constants::{C_TILDE_BYTES, K, L, N};
use crate::reference::encoding::{PublicKey, SignatureParts};

/// A ring polynomial with signed coefficients (the response `z`), serialized as
/// a plain array. `serde` handles `[i32; 256]` via const-generic array support.
pub type SignedPoly = [i32; N];

/// A `t1` polynomial: coefficients in `[0, 2^10)`.
pub type T1Poly = [u32; N];

/// A hint polynomial: one bit per coefficient (`{0, 1}`).
pub type HintPoly = [u8; N];

/// Every input needed to (a) verify an ML-DSA-65 signature with the M1 reference
/// and (b) generate the proving witness (M2).
///
/// Field-by-field mapping to FIPS 204 notation and the S5a worksheet:
/// - `rho`   — matrix seed `ρ`; `Â = ExpandA(ρ)` is verifier-computable.
/// - `t1`    — public key vector `t1` (decoded); `t1_i·2^d` is a public term.
/// - `tr`    — `tr = H(pk, 512)`; absorbed into `µ`. Carried so the witness
///   generator need not re-decode/re-hash the public key to obtain it.
/// - `message` — the full COSE `Sig_structure` (pure mode, empty context); the
///   `M` absorbed into `µ = H(tr ‖ 0x00 ‖ 0x00 ‖ M, 512)`.
/// - `c_tilde` — commitment hash `c̃` (private); `SampleInBall` seed.
/// - `z`     — response `z` (private, signed, centered).
/// - `hint`  — hint bits `h` (private); drives `UseHint`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MlDsaVerifyInput {
    /// Matrix seed `ρ` (32 bytes). `[u8; 32]` has a native serde impl.
    pub rho: [u8; 32],
    /// Public-key vector `t1`, `k` polynomials, coefficients in `[0, 2^10)`.
    #[serde(with = "flat_u32_kn")]
    pub t1: [T1Poly; K],
    /// `tr = H(pk, 512)`, the 64-byte public-key digest.
    #[serde(with = "flat_bytes")]
    pub tr: [u8; 64],
    /// The full COSE `Sig_structure` (pure mode, empty context).
    pub message: Vec<u8>,
    /// Commitment hash `c̃` (48 bytes), private.
    #[serde(with = "flat_bytes")]
    pub c_tilde: [u8; C_TILDE_BYTES],
    /// Response `z`, `l` polynomials of signed coefficients, private.
    #[serde(with = "flat_i32_ln")]
    pub z: [SignedPoly; L],
    /// Hint `h`, `k` polynomials of `{0, 1}` bits, private.
    #[serde(with = "flat_u8_kn")]
    pub hint: [HintPoly; K],
}

impl MlDsaVerifyInput {
    /// Build from the reference's decoded public-key and signature structs plus
    /// the message and `tr`. This is the natural constructor once you have run
    /// `pk_decode` / `sig_decode`.
    pub fn from_decoded(
        pk: &PublicKey,
        sig: &SignatureParts,
        tr: [u8; 64],
        message: Vec<u8>,
    ) -> Self {
        Self {
            rho: pk.rho,
            t1: pk.t1,
            tr,
            message,
            c_tilde: sig.c_tilde,
            z: sig.z,
            hint: sig.h,
        }
    }

    /// Re-encode the public key to FIPS 204 `pkEncode` wire bytes so the M1
    /// reference verifier (which ingests raw bytes) can be driven from this
    /// decoded input. Inverse of `pk_decode`.
    pub fn encode_pk(&self) -> Vec<u8> {
        crate::reference::encoding::pk_encode(&self.rho, &self.t1)
    }

    /// Re-encode the signature to FIPS 204 `sigEncode` wire bytes. Inverse of
    /// `sig_decode`.
    pub fn encode_sig(&self) -> Vec<u8> {
        crate::reference::encoding::sig_encode(&self.c_tilde, &self.z, &self.hint)
    }
}

// serde helpers: `serde` only implements `Serialize`/`Deserialize` for arrays of
// length ≤ 32, so every field here (`[u8; 48/64]`, `[[u32/i32/u8; 256]; K/L]`)
// needs a `#[serde(with)]` shim. Each shim flattens to a length-prefixed `Vec`
// and rebuilds with a length check — self-describing and format-agnostic.
// ponytail: hand-rolled over pulling in `serde-big-array` for four call sites.

/// `[u8; N]` (N > 32) ⇆ `Vec<u8>`.
mod flat_bytes {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S, const N: usize>(arr: &[u8; N], s: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        arr.as_slice().serialize(s)
    }

    pub fn deserialize<'de, D, const N: usize>(d: D) -> Result<[u8; N], D::Error>
    where
        D: Deserializer<'de>,
    {
        let v = Vec::<u8>::deserialize(d)?;
        <[u8; N]>::try_from(v.as_slice())
            .map_err(|_| serde::de::Error::invalid_length(v.len(), &"expected array"))
    }
}

macro_rules! flat_nested {
    ($modname:ident, $elem:ty, $outer:expr, $inner:expr) => {
        /// `[[$elem; $inner]; $outer]` ⇆ flat `Vec<$elem>`.
        mod $modname {
            use super::*;
            use serde::{Deserialize, Deserializer, Serialize, Serializer};

            pub fn serialize<S>(arr: &[[$elem; $inner]; $outer], s: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                let flat: Vec<$elem> = arr.iter().flatten().copied().collect();
                flat.serialize(s)
            }

            pub fn deserialize<'de, D>(d: D) -> Result<[[$elem; $inner]; $outer], D::Error>
            where
                D: Deserializer<'de>,
            {
                let flat = Vec::<$elem>::deserialize(d)?;
                if flat.len() != $outer * $inner {
                    return Err(serde::de::Error::invalid_length(
                        flat.len(),
                        &concat!(stringify!($outer), "*", stringify!($inner), " elements"),
                    ));
                }
                let mut out = [[<$elem>::default(); $inner]; $outer];
                for (o, chunk) in out.iter_mut().zip(flat.chunks_exact($inner)) {
                    o.copy_from_slice(chunk);
                }
                Ok(out)
            }
        }
    };
}

flat_nested!(flat_u32_kn, u32, K, N);
flat_nested!(flat_i32_ln, i32, L, N);
flat_nested!(flat_u8_kn, u8, K, N);
