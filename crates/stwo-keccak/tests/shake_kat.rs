//! FIPS 202 SHAKE-256 known-answer tests against the `sha3` crate, exercising
//! every padding branch (empty, one-block, block-boundary, multi-block, long
//! squeeze). Each case proves and verifies end-to-end and checks the sponge
//! output byte-for-byte against `sha3`.

use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::Shake256;
use stwo::core::pcs::PcsConfig;
use stwo_keccak::{prove_shake256, verify_shake256};

fn sha3_shake256(msg: &[u8], out_len: usize) -> Vec<u8> {
    let mut h = Shake256::default();
    h.update(msg);
    let mut r = h.finalize_xof();
    let mut out = vec![0u8; out_len];
    r.read(&mut out);
    out
}

/// Prove+verify `msg` with `n_squeeze` blocks and check the output vs sha3.
fn check(msg: &[u8], n_squeeze: usize) {
    let proof = prove_shake256(msg, n_squeeze, PcsConfig::default())
        .unwrap_or_else(|e| panic!("prove (len={}, sq={}): {e:?}", msg.len(), n_squeeze));
    let expected = sha3_shake256(msg, n_squeeze * 136);
    assert_eq!(
        proof.output,
        expected,
        "sponge output != sha3 (len={}, sq={})",
        msg.len(),
        n_squeeze
    );
    verify_shake256(&proof).unwrap_or_else(|e| panic!("verify (len={}): {e:?}", msg.len()));
}

#[test]
fn kat_empty_message() {
    check(b"", 1);
}

#[test]
fn kat_one_block_135_bytes() {
    // L mod 136 == 135: the tricky f==135 case (pad byte 0x1F|0x80 = 0x9F).
    check(&[0xA5u8; 135], 1);
}

#[test]
fn kat_block_boundary_136_bytes() {
    // L mod 136 == 0: a fresh final padding block (0x1F at pos 0, 0x80 at 135).
    check(&[0x5Au8; 136], 1);
}

#[test]
fn kat_multi_block_mu_shape() {
    // ~1.5 KB, the ML-DSA μ absorb shape (spans many rate blocks).
    let msg: Vec<u8> = (0..1536u32).map(|i| (i.wrapping_mul(31) & 0xFF) as u8).collect();
    check(&msg, 1);
}

#[test]
fn kat_long_squeeze() {
    // Several squeeze blocks from a short message.
    check(b"squeeze me across many blocks", 5);
}

#[test]
fn kat_partial_block_137_bytes() {
    // Spills into a second absorb block with a small remainder.
    check(&[0x11u8; 137], 1);
}
