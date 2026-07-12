//! Smoke test: the whole pipeline proves and verifies, and the sponge output
//! matches the `sha3` reference for a small message.

use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::Shake256;
use stwo::core::fri::FriConfig;
use stwo::core::pcs::PcsConfig;
use stwo_keccak::{prove_shake256, verify_shake256};

/// Batch-4 logup constraints have log-degree excess 2, so proving needs
/// `log_blowup >= 2` (production uses 3).
fn pcs_config() -> PcsConfig {
    PcsConfig {
        fri_config: FriConfig::new(0, 2, 3, 1),
        ..PcsConfig::default()
    }
}

fn shake256(msg: &[u8], out_len: usize) -> Vec<u8> {
    let mut h = Shake256::default();
    h.update(msg);
    let mut r = h.finalize_xof();
    let mut out = vec![0u8; out_len];
    r.read(&mut out);
    out
}

#[test]
fn prove_verify_empty_message() {
    let msg: &[u8] = b"";
    let n_squeeze = 1;
    let proof = prove_shake256(msg, n_squeeze, pcs_config()).expect("prove");

    // Output matches sha3 reference (first 136 bytes).
    let expected = shake256(msg, 136);
    assert_eq!(proof.output, expected, "sponge output != sha3");

    verify_shake256(&proof).expect("verify");
}
