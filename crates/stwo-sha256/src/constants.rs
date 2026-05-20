//! SHA-256 spec constants (FIPS 180-4 §4.2.2, §5.3.3).
//!
//! These are circuit constants — never free trace columns. The AIR hard-wires
//! `K[t]` per round and constrains the initial hash state to equal `IV`.

/// Round constants `K[0..63]`: first 32 bits of the fractional parts of the
/// cube roots of the first 64 primes (FIPS 180-4 §4.2.2).
pub const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// Initial hash value `H⁽⁰⁾ = IV`: first 32 bits of the fractional parts of
/// the square roots of the first 8 primes (FIPS 180-4 §5.3.3).
pub const IV: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// 64 rounds per block.
pub const N_ROUNDS: usize = 64;

/// 16 message-schedule input words; the remaining `64 - 16 = 48` are derived.
pub const N_INPUT_WORDS: usize = 16;

/// Total schedule length per block: `W[0..63]`.
pub const N_SCHEDULE_WORDS: usize = N_ROUNDS;

/// 8 working state words `(a..h)` and 8 hash words `(H₀..H₇)`.
pub const N_STATE_WORDS: usize = 8;

/// Block size in bytes (`512 bits / 8`).
pub const BLOCK_BYTES: usize = 64;

/// Word size in bytes (`32 bits / 8`).
pub const WORD_BYTES: usize = 4;

/// Digest size in bytes (`256 bits / 8`).
pub const DIGEST_BYTES: usize = 32;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_constants_spec_anchors() {
        // First, last, and the boundaries of each row in the FIPS table.
        assert_eq!(K[0], 0x428a2f98);
        assert_eq!(K[7], 0xab1c5ed5);
        assert_eq!(K[63], 0xc67178f2);
        assert_eq!(K.len(), N_ROUNDS);
    }

    #[test]
    fn iv_spec_anchors() {
        assert_eq!(IV[0], 0x6a09e667);
        assert_eq!(IV[7], 0x5be0cd19);
        assert_eq!(IV.len(), N_STATE_WORDS);
    }

    #[test]
    fn size_constants_consistent() {
        assert_eq!(BLOCK_BYTES, N_INPUT_WORDS * WORD_BYTES);
        assert_eq!(DIGEST_BYTES, N_STATE_WORDS * WORD_BYTES);
        assert_eq!(N_SCHEDULE_WORDS, N_ROUNDS);
    }
}
