//! Prove and verify one SHA-256 message with the standalone component.
//!
//! ## Usage
//!
//! ```bash
//! # Use the FIPS 180-4 Appendix B.1 `"abc"` test vector.
//! cargo run --release --example prove_demo -p stwo-sha256
//!
//! # Use a custom message.
//! cargo run --release --example prove_demo -p stwo-sha256 -- "the quick brown fox"
//! ```
//!
//! The exit code is `0` after successful proof and verification. It is `1`
//! after an error.

use std::process::ExitCode;
use std::time::Instant;

use stwo_sha256::stark::{native_digest, prove_sha256, verify_sha256_proof, ProverConfig};
use stwo_sha256::trace::min_log_size;
use stwo_sha256::witness::compute_sha256_witness;

fn main() -> ExitCode {
    // Use the first argument as the message.
    let mut args = std::env::args().skip(1);
    let message: Vec<u8> = match args.next() {
        Some(s) => s.into_bytes(),
        None => b"abc".to_vec(),
    };

    // Size `log_n_rows` to the witness so any message length proves
    // without manual config tweaking; `ProverConfig::default()`'s
    // `log_n_rows = LOG_N_LANES` only fits messages ≤ ~1 KiB.
    let witness = compute_sha256_witness(&message);
    let config = ProverConfig {
        log_n_rows: min_log_size(witness.blocks.len()),
        ..ProverConfig::default()
    };
    let native = native_digest(&message);

    eprintln!(
        "prove_sha256({:?}) — {} byte(s), config (log_n_rows={})",
        String::from_utf8_lossy(&message),
        message.len(),
        config.log_n_rows,
    );
    eprintln!("native digest: {}", hex(&native.0));

    let t0 = Instant::now();
    let proof = match prove_sha256(&message, &config) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("prove_sha256 failed: {e}");
            return ExitCode::from(1);
        }
    };
    let prove_ms = t0.elapsed().as_millis();
    eprintln!(
        "proof: {} block(s), proved in {prove_ms} ms",
        proof.n_blocks
    );

    if proof.digest != native.0 {
        eprintln!(
            "digest mismatch — proof.digest = {}, native = {}",
            hex(&proof.digest),
            hex(&native.0),
        );
        return ExitCode::from(1);
    }

    let t1 = Instant::now();
    if let Err(e) = verify_sha256_proof(&proof) {
        eprintln!("verify_sha256_proof rejected the proof: {e}");
        return ExitCode::from(1);
    }
    let verify_ms = t1.elapsed().as_millis();

    println!(
        "ok: SHA-256({:?}) = {} — proved in {prove_ms} ms, verified in {verify_ms} ms",
        String::from_utf8_lossy(&message),
        hex(&proof.digest),
    );
    ExitCode::SUCCESS
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
