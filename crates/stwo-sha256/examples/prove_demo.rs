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
//! Use a release build for representative proof performance. Debug builds are
//! much slower. This example is the standalone command-line entry point.
//!
//! Exit code is `0` on a successful prove→verify, `1` on any failure
//! (mismatched native digest, prover error, verifier error).

use std::process::ExitCode;
use std::time::Instant;

use stwo_sha256::native::n_blocks_for;
use stwo_sha256::stark::{native_digest, prove_sha256, verify_sha256_proof, ProverConfig};
use stwo_sha256::trace::min_log_size;

fn main() -> ExitCode {
    // First non-program arg is the message. Default to FIPS 180-4 B.1.
    let mut args = std::env::args().skip(1);
    let message: Vec<u8> = match args.next() {
        Some(s) => s.into_bytes(),
        None => b"abc".to_vec(),
    };

    // Size `log_n_rows` to the witness so any message length proves
    // without manual config tweaking. `ProverConfig::default()` proves one
    // padded block.
    let config = ProverConfig {
        log_n_rows: min_log_size(n_blocks_for(message.len())),
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
    eprintln!("proof generated in {prove_ms} ms");

    let t1 = Instant::now();
    if let Err(e) = verify_sha256_proof(&proof) {
        eprintln!("verify_sha256_proof rejected the proof: {e}");
        return ExitCode::from(1);
    }
    let verify_ms = t1.elapsed().as_millis();

    println!(
        "ok: SHA-256({:?}) = {} — proved in {prove_ms} ms, verified in {verify_ms} ms",
        String::from_utf8_lossy(&message),
        hex(&native.0),
    );
    ExitCode::SUCCESS
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
