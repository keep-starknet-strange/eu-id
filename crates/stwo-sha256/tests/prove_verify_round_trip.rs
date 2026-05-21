//! Round-trip test for the SHA-256 component (roadmap task 3.9.9).
//!
//! `prove_sha256(msg).and_then(verify_sha256_proof)` must succeed for at
//! least one representative `msg` — the deliverable that closes the task.
//!
//! Test scope: a single representative message (`b"abc"`, one padded
//! block). Multi-block and edge-case round-trips land with the laptop
//! benchmark gate (3.9.12). The single-block test alone exercises:
//!
//! - The entire 19-component composition (`Sha256Eval` consumer +
//!   8 σ/Σ decode producers + 1 packed Maj/Ch + 1 xor_8 + 4 round
//!   split-pack + 4 σ split-pack).
//! - The preprocessed-trace commitment (76 columns).
//! - The base-trace commitment (9 355 SHA-256 columns + 19 producer
//!   multiplicity columns).
//! - The LogUp interaction trace across every component, with
//!   consumer ⇄ producer sums totalling zero — the soundness backbone.
//! - The Blake2s channel + PCS commitment scheme + FRI proof flow.
//! - The Sha256VerifyError surface (the soundness gate that catches a
//!   non-zero claimed-sum total).
//!
//! This is the slowest test in the suite — the packed Maj/Ch table is
//! 2²¹ rows, so the preprocessed trace generation and commitment
//! dominate. Marked `#[ignore]` so `cargo test` stays quick; run
//! explicitly with `cargo test -p stwo-sha256 --release
//! prove_verify_round_trip -- --ignored`.

use stwo_sha256::stark::{native_digest, prove_sha256, verify_sha256_proof, ProverConfig};

/// Closing assertion of roadmap 3.9.9: prove → verify succeeds on the
/// canonical FIPS-180-4 Appendix B.1 message `"abc"`.
#[ignore = "slow: 2^21-row Maj/Ch preprocessed trace dominates; run in release with --ignored"]
#[test]
fn prove_and_verify_abc() {
    let msg = b"abc";
    let config = ProverConfig::default();

    let proof = prove_sha256(msg, &config).expect("prove_sha256 on b\"abc\"");

    // Public surface sanity: the proof stamps the correct digest.
    assert_eq!(proof.digest, native_digest(msg).0);
    assert_eq!(proof.n_blocks, 1);

    // The actual deliverable: verify accepts the proof.
    verify_sha256_proof(&proof).expect("verify_sha256_proof on prove output");
}

/// Negative half of the closure: mutating the proof's claimed-sum
/// surface to a non-zero total trips the `LogupSumNonZero` gate before
/// the Stwo verifier even runs. Pins the soundness-backbone check.
#[ignore = "slow: produces a real proof first; same cost as prove_and_verify_abc"]
#[test]
fn verify_rejects_logup_sum_mutation() {
    use num_traits::One;
    use stwo::core::fields::qm31::SecureField;
    use stwo_sha256::stark::Sha256VerifyError;

    let msg = b"abc";
    let config = ProverConfig::default();
    let mut proof = prove_sha256(msg, &config).expect("prove_sha256 on b\"abc\"");

    // Bump one of the producer-side claimed sums by 1. The total now
    // differs from zero by 1, so the soundness gate catches it.
    proof.interaction_claim.xor_8.claimed_sum += SecureField::one();

    match verify_sha256_proof(&proof) {
        Err(Sha256VerifyError::LogupSumNonZero) => {}
        other => panic!("expected LogupSumNonZero, got {other:?}"),
    }
}
