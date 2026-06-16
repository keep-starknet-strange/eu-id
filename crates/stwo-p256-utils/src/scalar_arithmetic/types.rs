use crate::constants::N_LIMBS;

pub type U256Words = [u64; 4];
pub type BigIntLimbs = [u32; N_LIMBS];

pub const PRODUCT_EQUATION_LIMBS: usize = 2 * N_LIMBS;
pub type ProductCarries = [i64; PRODUCT_EQUATION_LIMBS];
pub type BigIntCarries = [i64; N_LIMBS];

pub const P256_ORDER: U256Words = [
    0xF3B9_CAC2_FC63_2551,
    0xBCE6_FAAD_A717_9E84,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_0000_0000,
];
