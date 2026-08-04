//! Pure-Rust SHA-256 reference, used as the out-of-circuit oracle.
//!
//! Implements FIPS 180-4 §5 (padding, parsing, hash computation) bit-for-bit.
//! Every operation is `u32::wrapping_*` arithmetic — no `i64`/`u64` carry
//! tricks — so the witness generator can mirror it exactly.
//!
//! The tests cross-check this against the `sha2` crate for arbitrary input
//! sizes, including multi-block messages and zero-length input.

use crate::constants::{BLOCK_BYTES, IV, K, N_INPUT_WORDS, N_ROUNDS, N_STATE_WORDS, WORD_BYTES};
use crate::types::{Block, Digest, HashState, Schedule};

/// Pad a message as FIPS 180-4 §5.1.1 specifies.
///
/// Append `0x80`.
/// Then append zeros until eight bytes remain in the block.
/// Append the bit length as a big-endian `u64`.
/// The output length is a multiple of `BLOCK_BYTES`.
///
/// Examples:
/// - `msg.len() = 0`  → one block (`0x80` + 55 zeros + 8-byte length).
/// - `msg.len() = 55` → one block (`msg` + `0x80` + 0 zeros + length).
/// - `msg.len() = 56` → two blocks (`0x80` does not fit with length in 64 B).
pub fn pad_message(msg: &[u8]) -> Vec<u8> {
    let bit_len = (msg.len() as u64).checked_mul(8).expect("message too long");
    let mut out = Vec::with_capacity(msg.len() + 9 + 64);
    out.extend_from_slice(msg);
    out.push(0x80);
    // Zero-fill until `out.len() ≡ 56 (mod 64)`, leaving 8 bytes for length.
    while out.len() % BLOCK_BYTES != BLOCK_BYTES - 8 {
        out.push(0);
    }
    out.extend_from_slice(&bit_len.to_be_bytes());
    debug_assert_eq!(out.len() % BLOCK_BYTES, 0);
    out
}

/// Split a padded byte string into 64-byte blocks, each parsed as 16 BE words.
pub fn parse_blocks(padded: &[u8]) -> Vec<Block> {
    assert_eq!(
        padded.len() % BLOCK_BYTES,
        0,
        "padded input not block-aligned"
    );
    let mut blocks = Vec::with_capacity(padded.len() / BLOCK_BYTES);
    for chunk in padded.chunks_exact(BLOCK_BYTES) {
        let mut block_bytes = [0u8; BLOCK_BYTES];
        block_bytes.copy_from_slice(chunk);
        blocks.push(Block::from_bytes(&block_bytes));
    }
    blocks
}

/// `σ0(x) = ROTR7(x) ⊕ ROTR18(x) ⊕ SHR3(x)`.
#[inline]
pub fn lower_sigma0(x: u32) -> u32 {
    x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3)
}

/// `σ1(x) = ROTR17(x) ⊕ ROTR19(x) ⊕ SHR10(x)`.
#[inline]
pub fn lower_sigma1(x: u32) -> u32 {
    x.rotate_right(17) ^ x.rotate_right(19) ^ (x >> 10)
}

/// `Σ0(a) = ROTR2(a) ⊕ ROTR13(a) ⊕ ROTR22(a)`.
#[inline]
pub fn big_sigma0(a: u32) -> u32 {
    a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22)
}

/// `Σ1(e) = ROTR6(e) ⊕ ROTR11(e) ⊕ ROTR25(e)`.
#[inline]
pub fn big_sigma1(e: u32) -> u32 {
    e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25)
}

/// `Ch(e, f, g) = (e ∧ f) ⊕ (¬e ∧ g)` — bitwise.
#[inline]
pub fn ch(e: u32, f: u32, g: u32) -> u32 {
    (e & f) ^ (!e & g)
}

/// `Maj(a, b, c) = (a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)` — bitwise.
#[inline]
pub fn maj(a: u32, b: u32, c: u32) -> u32 {
    (a & b) ^ (a & c) ^ (b & c)
}

/// Expand the 16-word block to a 64-word schedule (FIPS §6.2.2 step 1).
pub fn expand_schedule(block: &Block) -> Schedule {
    let mut w = [0u32; N_ROUNDS];
    w[..N_INPUT_WORDS].copy_from_slice(&block.0);
    for t in N_INPUT_WORDS..N_ROUNDS {
        w[t] = lower_sigma1(w[t - 2])
            .wrapping_add(w[t - 7])
            .wrapping_add(lower_sigma0(w[t - 15]))
            .wrapping_add(w[t - 16]);
    }
    Schedule(w)
}

/// Compress one block (FIPS §6.2.2 steps 2–4): 64 rounds plus finalization.
pub fn compress_block(h_in: &HashState, schedule: &Schedule) -> HashState {
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = h_in.0;
    for (t, &k_t) in K.iter().enumerate().take(N_ROUNDS) {
        let t1 = h
            .wrapping_add(big_sigma1(e))
            .wrapping_add(ch(e, f, g))
            .wrapping_add(k_t)
            .wrapping_add(schedule.0[t]);
        let t2 = big_sigma0(a).wrapping_add(maj(a, b, c));
        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
    }
    let mut h_out = h_in.0;
    for (slot, working) in h_out.iter_mut().zip([a, b, c, d, e, f, g, h].iter()) {
        *slot = slot.wrapping_add(*working);
    }
    HashState(h_out)
}

/// Multi-block SHA-256: `pad → parse → for each block, expand + compress`.
pub fn hash(msg: &[u8]) -> Digest {
    let padded = pad_message(msg);
    let blocks = parse_blocks(&padded);
    let mut h = HashState(IV);
    for block in &blocks {
        let schedule = expand_schedule(block);
        h = compress_block(&h, &schedule);
    }
    Digest::from_state(&h)
}

/// Number of blocks needed for a message of `n_bytes`.
pub fn n_blocks_for(n_bytes: usize) -> usize {
    // After appending 0x80 + 8 length bytes, round up to a multiple of 64.
    let total = n_bytes + 9;
    total.div_ceil(BLOCK_BYTES)
}

const _: () = {
    // Internal consistency: block/word/state sizing.
    assert!(BLOCK_BYTES == N_INPUT_WORDS * WORD_BYTES);
    assert!(N_STATE_WORDS == 8);
};

#[cfg(test)]
mod tests {
    use super::*;
    use sha2::{Digest as Sha2Digest, Sha256};

    fn sha2_reference(msg: &[u8]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(msg);
        hasher.finalize().into()
    }

    #[test]
    fn empty_message_matches_sha2() {
        let ours = hash(b"");
        let theirs = sha2_reference(b"");
        assert_eq!(ours.0, theirs);
    }

    #[test]
    fn abc_matches_fips_appendix_b_1() {
        // FIPS 180-4 Appendix B.1: SHA-256("abc") =
        // ba7816bf 8f01cfea 414140de 5dae2223 b00361a3 96177a9c b410ff61 f20015ad
        let digest = hash(b"abc");
        let expected =
            hex_decode_32("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
        assert_eq!(digest.0, expected);
    }

    #[test]
    fn two_block_fips_appendix_b_2_matches_sha2() {
        // FIPS Appendix B.2 uses a 448-bit (= 56-byte) message. Padding pushes
        // it into a second block.
        let msg = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
        assert_eq!(msg.len(), 56);
        let ours = hash(msg);
        let theirs = sha2_reference(msg);
        assert_eq!(ours.0, theirs);
    }

    #[test]
    fn boundary_lengths_match_sha2() {
        // Lengths that exercise the padding boundary cases.
        for n in [
            0usize, 1, 55, 56, 63, 64, 65, 127, 128, 129, 200, 511, 512, 1000,
        ] {
            let msg: Vec<u8> = (0..n).map(|i| (i * 7) as u8).collect();
            let ours = hash(&msg);
            let theirs = sha2_reference(&msg);
            assert_eq!(ours.0, theirs, "mismatch at n = {n}");
        }
    }

    #[test]
    fn padding_invariants() {
        for n in [0usize, 1, 55, 56, 63, 64, 100, 1000] {
            let msg: Vec<u8> = vec![0xAB; n];
            let padded = pad_message(&msg);
            assert_eq!(padded.len() % BLOCK_BYTES, 0, "n={n}: not block-aligned");
            // First `n` bytes are the message.
            assert_eq!(&padded[..n], &msg[..]);
            // The byte right after the message is the 0x80 marker.
            assert_eq!(padded[n], 0x80);
            // All padding bytes between the marker and the length field are 0.
            assert!(padded[n + 1..padded.len() - 8].iter().all(|&b| b == 0));
            // The last 8 bytes are the bit length, big-endian.
            let len_bytes: [u8; 8] = padded[padded.len() - 8..].try_into().unwrap();
            assert_eq!(u64::from_be_bytes(len_bytes), (n as u64) * 8);
        }
    }

    #[test]
    fn n_blocks_for_matches_padding_length() {
        for n in 0..200 {
            let padded = pad_message(&vec![0u8; n]);
            assert_eq!(padded.len() / BLOCK_BYTES, n_blocks_for(n));
        }
    }

    #[test]
    fn iv_round_trip_on_empty_message() {
        // Block 0's schedule consumes the padded empty message. Block 0's
        // h_in must be IV. h_out must produce the canonical empty-string
        // digest. Check that the computation carries the IV through.
        let padded = pad_message(b"");
        let blocks = parse_blocks(&padded);
        assert_eq!(blocks.len(), 1);
        let schedule = expand_schedule(&blocks[0]);
        let h_out = compress_block(&HashState(IV), &schedule);
        let expected =
            hex_decode_32("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
        assert_eq!(Digest::from_state(&h_out).0, expected);
    }

    #[test]
    fn schedule_matches_inline_recurrence() {
        let block = Block::from_bytes(
            // Just some non-trivial block bytes.
            &[
                0x61, 0x62, 0x63, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24,
            ],
        );
        let sched = expand_schedule(&block);
        // Spot-check the recurrence in the middle of the schedule range.
        for t in [16, 17, 32, 47, 63] {
            let recomputed = lower_sigma1(sched.0[t - 2])
                .wrapping_add(sched.0[t - 7])
                .wrapping_add(lower_sigma0(sched.0[t - 15]))
                .wrapping_add(sched.0[t - 16]);
            assert_eq!(sched.0[t], recomputed, "W[{t}] disagrees with recurrence");
        }
    }

    fn hex_decode_32(s: &str) -> [u8; 32] {
        let v = hex::decode(s).unwrap();
        v.try_into().unwrap()
    }
}
