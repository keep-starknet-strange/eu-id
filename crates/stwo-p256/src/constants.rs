use stwo_p256_utils::constants::LIMB_BITS;

/// Maximum value of a single 13-bit limb: `2^13 − 1 = 8191`.
pub const LIMB_MAX: u32 = (1 << LIMB_BITS) - 1;

/// P-256 base field prime `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`,
/// little-endian u64 limbs.
pub const P256_MODULUS: [u64; 4] = [
    0xFFFF_FFFF_FFFF_FFFF,
    0x0000_0000_FFFF_FFFF,
    0x0000_0000_0000_0000,
    0xFFFF_FFFF_0000_0001,
];

/// P-256 curve order `n`, little-endian u64 limbs.
pub const P256_ORDER: [u64; 4] = [
    0xF3B9_CAC2_FC63_2551,
    0xBCE6_FAAD_A717_9E84,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_0000_0000,
];

/// P-256 generator point x-coordinate, little-endian u64 limbs.
pub const P256_GX: [u64; 4] = [
    0xF4A1_3945_D898_C296,
    0x7703_7D81_2DEB_33A0,
    0xF8BC_E6E5_63A4_40F2,
    0x6B17_D1F2_E12C_4247,
];

/// P-256 generator point y-coordinate, little-endian u64 limbs.
pub const P256_GY: [u64; 4] = [
    0xCBB6_4068_37BF_51F5,
    0x2BCE_3357_6B31_5ECE,
    0x8EE7_EB4A_7C0F_9E16,
    0x4FE3_42E2_FE1A_7F9B,
];

/// P-256 point `3·G` x-coordinate, little-endian u64 limbs.
///
/// Used to pin the cert0 (generator) prepared-table `P3 = 3·P` cells to a fixed
/// constant, since cert0 has no `DoubleP`/`AddP2P` setup rows. Verified against
/// `scalar_mul(3, G)` in `constants` tests.
pub const P256_3GX: [u64; 4] = [
    0xFB41_661B_C6E7_FD6C,
    0xE6C6_B721_EFAD_A985,
    0xC8F7_EF95_1D4B_F165,
    0x5ECB_E4D1_A633_0A44,
];

/// P-256 point `3·G` y-coordinate, little-endian u64 limbs.
pub const P256_3GY: [u64; 4] = [
    0x9A79_B127_A27D_5032,
    0xD82A_B036_384F_B83D,
    0x374B_06CE_1A64_A2EC,
    0x8734_640C_4998_FF7E,
];

/// P-256 curve coefficient `b`, little-endian u64 limbs.
pub const P256_B: [u64; 4] = [
    0x3BCE_3C3E_27D2_604B,
    0x651D_06B0_CC53_B0F6,
    0xB3EB_BD55_7698_86BC,
    0x5AC6_35D8_AA3A_93E7,
];

#[cfg(test)]
mod tests {
    use super::{P256_3GX, P256_3GY, P256_GX, P256_GY};
    use crate::curve::scalar_mul;
    use crate::types::{AffinePoint, U256};

    #[test]
    fn p256_3g_constant_matches_scalar_mul() {
        let generator = AffinePoint {
            x: U256::from_le_u64s(&P256_GX),
            y: U256::from_le_u64s(&P256_GY),
        };
        let three = U256::from_le_u64s(&[3, 0, 0, 0]);
        let three_g = scalar_mul(&three, &generator).expect("3*G is finite");
        assert_eq!(three_g.x, U256::from_le_u64s(&P256_3GX));
        assert_eq!(three_g.y, U256::from_le_u64s(&P256_3GY));
    }
}
