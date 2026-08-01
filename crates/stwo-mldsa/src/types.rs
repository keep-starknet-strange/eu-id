//! Serializable public and private inputs to in-circuit ML-DSA verification.
//!
//! [`MlDsaVerifyInput`] carries the semantically decoded values the prover and
//! native verifier need. [`MlDsaPrivateKeyPublicInput`] is the deliberately
//! smaller verifier envelope for hosted private-key proofs.
//!
//! ## What is public vs private
//!
//! Public-key modes mix `rho`, decoded `t1`, recomputed `tr`, and `message`.
//! Hosted private-key mode mixes only `message`: `rho`, `t1`, `tr`, and the
//! signature stay in the proof witness and are bound through the packed-key,
//! NTT, evaluation, and Keccak relations. The private-key verifier therefore
//! accepts [`MlDsaPrivateKeyPublicInput`] and cannot receive stable key data.
//!
//! ## Decoded `t1` form
//!
//! `t1` is stored **decoded** (`[[u32; N]; K]`, coefficients in `[0, 2^10)`) —
//! the form witness generation needs. Public-key mode evaluates
//! `c·t1_i·2^d` natively; private-key mode proves the 10-bit packed-key split
//! and evaluates `2^d·t1_i` inside the AIR.

use serde::{Deserialize, Serialize};

use crate::constants::{C_TILDE_BYTES, K, L, N};
use crate::profile::MlDsaProfile;
use crate::reference::encoding::{PublicKey, SignatureParts};

/// A ring polynomial with signed coefficients (the response `z`), serialized as
/// a plain array. `serde` handles `[i32; 256]` via const-generic array support.
pub type SignedPoly = [i32; N];

/// A `t1` polynomial: coefficients in `[0, 2^10)`.
pub type T1Poly = [u32; N];

/// Exclusive upper bound for a canonically decoded ML-DSA `t1` coefficient.
pub const T1_COEFFICIENT_BOUND: u32 = 1 << 10;

/// A hint polynomial: one bit per coefficient (`{0, 1}`).
pub type HintPoly = [u8; N];

/// Public verifier input for a hosted device statement whose ML-DSA public key
/// and signature are witness-only. The request-bound device message is the
/// only clear ML-DSA value the verifier needs.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MlDsaPrivateKeyPublicInput {
    pub message: Vec<u8>,
}

/// Inputs to verify an ML-DSA signature and generate its proof witness.
///
/// Field mapping to FIPS 204 notation:
/// - `rho`   — matrix seed `ρ`; public mode computes `Â = ExpandA(ρ)`
///   natively, private-key mode proves it through `NttCell`.
/// - `t1`    — public key vector `t1` (decoded); public mode treats
///   `t1_i·2^d` as a public term, private-key mode proves its packed binding.
/// - `tr`    — `tr = H(pk, 512)`; absorbed into `µ`. Proof constructors derive
///   it from `pkEncode` before use.
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
    /// Storage for `tr = H(pk, 512)`. Proof constructors derive this value from
    /// `pkEncode`.
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
    /// Reject non-canonical decoded public keys before they reach transcript
    /// mixing or verifier-native public-polynomial evaluation.
    pub fn validate_public_key(&self, profile: MlDsaProfile) -> Result<(), &'static str> {
        if self.t1[..profile.k()]
            .iter()
            .flatten()
            .any(|&coefficient| coefficient >= T1_COEFFICIENT_BOUND)
        {
            return Err("decoded ML-DSA t1 coefficient is not canonical");
        }
        if self.t1[profile.k()..]
            .iter()
            .flatten()
            .any(|&coefficient| coefficient != 0)
        {
            return Err("inactive ML-DSA t1 coefficient is not zero");
        }
        Ok(())
    }

    /// Reject hidden values outside the selected parameter set's wire image.
    pub fn validate_signature(&self, profile: MlDsaProfile) -> Result<(), &'static str> {
        if self.c_tilde[profile.c_tilde_bytes()..]
            .iter()
            .any(|&byte| byte != 0)
            || self.z[profile.l()..]
                .iter()
                .flatten()
                .any(|&coefficient| coefficient != 0)
            || self.hint[profile.k()..]
                .iter()
                .flatten()
                .any(|&bit| bit != 0)
        {
            return Err("inactive ML-DSA signature storage is not zero");
        }
        if self.hint[..profile.k()]
            .iter()
            .flatten()
            .any(|&bit| bit > 1)
        {
            return Err("decoded ML-DSA hint is not binary");
        }
        Ok(())
    }

    /// Build from the reference's decoded public-key and signature structs plus
    /// the message and `tr`. This is the natural constructor once you have run
    /// `pk_decode` / `sig_decode`.
    pub fn from_decoded(
        profile: MlDsaProfile,
        pk: &PublicKey,
        sig: &SignatureParts,
        tr: [u8; 64],
        message: Vec<u8>,
    ) -> Self {
        debug_assert!(pk.t1[profile.k()..].iter().flatten().all(|&v| v == 0));
        debug_assert!(sig.c_tilde[profile.c_tilde_bytes()..]
            .iter()
            .all(|&v| v == 0));
        debug_assert!(sig.z[profile.l()..].iter().flatten().all(|&v| v == 0));
        debug_assert!(sig.h[profile.k()..].iter().flatten().all(|&v| v == 0));
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

    /// Re-encode the public key to FIPS 204 `pkEncode` bytes so the reference
    /// verifier, which ingests raw bytes, can use this
    /// decoded input. Inverse of `pk_decode`.
    pub fn encode_pk(&self, profile: MlDsaProfile) -> Vec<u8> {
        crate::reference::encoding::pk_encode(profile, &self.rho, &self.t1)
    }

    /// Re-encode the signature to FIPS 204 `sigEncode` wire bytes. Inverse of
    /// `sig_decode`.
    pub fn encode_sig(&self, profile: MlDsaProfile) -> Vec<u8> {
        crate::reference::encoding::sig_encode(profile, &self.c_tilde, &self.z, &self.hint)
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
