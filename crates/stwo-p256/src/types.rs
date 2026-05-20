use serde::{Deserialize, Serialize};
use crate::constants::{P256_GX, P256_GY, P256_MODULUS, P256_ORDER};

/// A 256-bit unsigned integer stored as big-endian bytes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct U256(pub [u8; 32]);

impl U256 {
    pub const ZERO: Self = Self([0u8; 32]);

    pub fn from_le_u64s(limbs: &[u64; 4]) -> Self {
        let mut bytes = [0u8; 32];
        for (i, limb) in limbs.iter().enumerate() {
            bytes[24 - i * 8..32 - i * 8].copy_from_slice(&limb.to_be_bytes());
        }
        Self(bytes)
    }

    pub fn to_le_u64s(&self) -> [u64; 4] {
        let mut limbs = [0u64; 4];
        for (i, limb) in limbs.iter_mut().enumerate() {
            let start = 24 - i * 8;
            *limb = u64::from_be_bytes(self.0[start..start + 8].try_into().unwrap());
        }
        limbs
    }
}

/// An affine point on P-256. None represents the point at infinity.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AffinePoint {
    pub x: U256,
    pub y: U256,
}

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

/// The P-256 generator point.
pub fn generator() -> AffinePoint {
    AffinePoint {
        x: U256::from_le_u64s(&P256_GX),
        y: U256::from_le_u64s(&P256_GY),
    }
}

/// The P-256 base field modulus.
pub fn field_modulus() -> U256 {
    U256::from_le_u64s(&P256_MODULUS)
}

/// The P-256 curve order.
pub fn curve_order() -> U256 {
    U256::from_le_u64s(&P256_ORDER)
}
