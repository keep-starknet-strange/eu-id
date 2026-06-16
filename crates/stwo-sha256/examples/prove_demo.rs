//! End-to-end SHA-256 prove → verify demo for a single user-supplied
//! message — the shortest path to running the standalone component without
//! writing a unit test.
//!
//! ## Usage
//!
//! ```bash
//! # default message — FIPS 180-4 Appendix B.1 `"abc"` test vector
//! cargo run --release --example prove_demo -p stwo-sha256
//!
//! # custom message via positional argument
//! cargo run --release --example prove_demo -p stwo-sha256 -- "the quick brown fox"
//! ```
//!
//! Build in `--release`: the 2¹⁸-row packed Maj/Ch preprocessed table
//! generation dominates wall time and is ~100× slower in debug. The
//! eventual `bin/eu-id` (owned by the integration stream) replaces this
//! example with a real CLI.
//!
//! Exit code is `0` on a successful prove→verify, `1` on any failure
//! (mismatched native digest, prover error, verifier error).

use std::process::ExitCode;
use std::time::Instant;

use stwo_sha256::stark::{native_digest, prove_sha256, verify_sha256_proof, ProverConfig};
use stwo_sha256::trace::min_log_size;
use stwo_sha256::witness::compute_sha256_witness;

fn main() -> ExitCode {
    // First non-program arg is the message; default to FIPS 180-4 B.1.
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
        "prove_sha256({:?}) — {} byte(s), config (log_n_rows={}, group_width={})",
        String::from_utf8_lossy(&message),
        message.len(),
        config.log_n_rows,
        config.group_width,
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
