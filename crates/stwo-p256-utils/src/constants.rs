//! Workspace-wide constants.
//!
//! Single source of truth for limb width, M31 modulus, and raw P-256 curve
//! constants. The main AIR crate re-exports these so existing
//! `use crate::types::LIMB_BITS` imports continue to work.

/// Width of one big-integer limb in bits. With `N_LIMBS = 20`, a single limb
/// product `(2^13 − 1)^2` summed over 20 convolution terms equals
/// `20 · (2^13 − 1)^2 < 2^31`, fitting M31.
pub const LIMB_BITS: usize = 13;

/// Number of limbs per 256-bit value. `20 · 13 = 260 ≥ 256`.
pub const N_LIMBS: usize = 20;

/// Maximum value of a single 13-bit limb: `2^13 − 1 = 8191`.
pub const LIMB_MAX: u32 = (1 << LIMB_BITS) - 1;

/// Place-value of one limb position, as `i128` for headroom calculations.
pub const LIMB_BASE: i128 = 1i128 << LIMB_BITS;

/// Logical bit width of the P-256 base field.
pub const P256_FIELD_BITS: usize = 256;

/// M31 modulus `2^31 − 1`. AIR field elements are reduced modulo this.
pub const M31_MODULUS: i128 = (1i128 << 31) - 1;

/// Centered-representative bound: `(M31_MODULUS − 1) / 2`. The combined
/// expression in any signed-carry arithmetic row must satisfy
/// `|expr| < M31_CENTER_LIMIT` to ensure non-aliasing under the centered
/// encoding used by `SignedCarryRange`.
pub const M31_CENTER_LIMIT: i128 = (M31_MODULUS - 1) / 2;

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
