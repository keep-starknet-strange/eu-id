use crypto_bigint::U256;

pub const LIMB_BITS: usize = 13;
pub const N_LIMBS: usize = 20; // 20 * 13 = 260 bits >= 256


pub const MODULUS: U256 = U256::from_be_hex(
    "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff"
);
// MODULUS - 3
pub const A_COEFF: U256 = U256::from_be_hex(
    "ffffffff00000001000000000000000000000000fffffffffffffffffffffffc"
);
pub const ORDER: U256 = U256::from_be_hex(
    "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551"
);
pub const GX: U256 = U256::from_be_hex(
    "6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296"
);
pub const GY: U256 = U256::from_be_hex(
    "4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5"
);