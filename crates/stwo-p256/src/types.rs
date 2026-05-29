use crypto_bigint::U256;
use serde::{Deserialize, Serialize};
use crate::ops::affine_point::AffinePoint;

/// An ECDSA signature (r, s) where both are 256-bit scalars mod n.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Signature {
    pub r: U256,
    pub s: U256,
}

/// All inputs needed to verify an ECDSA P-256 signature.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EcdsaVerifyInput {
    pub message_hash: U256,
    pub signature: Signature,
    pub public_key: AffinePoint,
}