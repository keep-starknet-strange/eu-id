pub const GF128_BYTES: usize = 16;
pub const GF128_BITS: usize = 128;

pub type Gf128 = [u8; GF128_BYTES];

pub fn xor_128(left: &Gf128, right: &Gf128) -> Gf128 {
    std::array::from_fn(|i| left[i] ^ right[i])
}

pub fn gf128_tag(ap: &Gf128, av: &Gf128, x: &Gf128) -> Gf128 {
    gf128_mul(&xor_128(ap, av), x)
}

pub fn gf128_mul(left: &Gf128, right: &Gf128) -> Gf128 {
    let left = bytes_to_bits(left);
    let right = bytes_to_bits(right);
    let mut coeffs = [false; 255];
    for i in 0..GF128_BITS {
        for j in 0..GF128_BITS {
            coeffs[i + j] ^= left[i] & right[j];
        }
    }
    for high in (GF128_BITS..255).rev() {
        if coeffs[high] {
            coeffs[high] = false;
            for offset in [0usize, 1, 2, 7] {
                coeffs[high - GF128_BITS + offset] ^= true;
            }
        }
    }
    let mut out = [false; GF128_BITS];
    out.copy_from_slice(&coeffs[..GF128_BITS]);
    bits_to_bytes(&out)
}

pub fn bytes_to_bits(bytes: &Gf128) -> [bool; GF128_BITS] {
    let mut bits = [false; GF128_BITS];
    for (byte_index, byte) in bytes.iter().enumerate() {
        for bit_index in 0..8 {
            bits[byte_index * 8 + bit_index] = ((byte >> bit_index) & 1) == 1;
        }
    }
    bits
}

pub fn bits_to_bytes(bits: &[bool; GF128_BITS]) -> Gf128 {
    let mut bytes = [0u8; GF128_BYTES];
    for (bit_index, bit) in bits.iter().enumerate() {
        if *bit {
            bytes[bit_index / 8] |= 1 << (bit_index % 8);
        }
    }
    bytes
}
