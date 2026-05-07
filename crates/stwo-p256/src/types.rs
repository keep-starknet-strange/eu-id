use serde::{Deserialize, Serialize};

pub const P256_FIELD_BITS: usize = 256;
pub const LIMB_BITS: usize = 13;
pub const N_LIMBS: usize = 20; // 20 * 13 = 260 bits >= 256

/// P-256 base field prime: p = 2^256 - 2^224 + 2^192 + 2^96 - 1
pub const P256_MODULUS: [u64; 4] = [
    0xFFFF_FFFF_FFFF_FFFF,
    0x0000_0000_FFFF_FFFF,
    0x0000_0000_0000_0000,
    0xFFFF_FFFF_0000_0001,
];

/// P-256 curve order: n
pub const P256_ORDER: [u64; 4] = [
    0xF3B9_CAC2_FC63_2551,
    0xBCE6_FAAD_A717_9E84,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_0000_0000,
];

/// P-256 generator point x-coordinate
pub const P256_GX: [u64; 4] = [
    0xF4A1_3945_D898_C296,
    0x7703_7D81_2DEB_33A0,
    0xF8BC_E6E5_63A4_40F2,
    0x6B17_D1F2_E12C_4247,
];

/// P-256 generator point y-coordinate
pub const P256_GY: [u64; 4] = [
    0xCBB6_4068_37BF_51F5,
    0x2BCE_3357_6B31_5ECE,
    0x8EE7_EB4A_7C0F_9E16,
    0x4FE3_42E2_FE1A_7F9B,
];

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
        for i in 0..4 {
            let start = 24 - i * 8;
            limbs[i] = u64::from_be_bytes(self.0[start..start + 8].try_into().unwrap());
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
