//! Round-trip test for the SHA-256 component (roadmap task 3.9.9).
//!
//! `prove_sha256(msg).and_then(verify_sha256_proof)` must succeed for at
//! least one representative `msg` — the deliverable that closes the task.
//!
//! Test scope: a single representative message (`b"abc"`, one padded
//! block). Multi-block and edge-case round-trips land with the laptop
//! benchmark gate (3.9.12). The single-block test alone exercises:
//!
//! - The entire 23-component composition (`Sha256Eval` consumer +
//!   8 σ/Σ decode producers + 1 packed Maj/Ch + 1 xor_8 + 4 round
//!   split-pack + 4 σ split-pack + 4 `Range_k` producers).
//! - The preprocessed-trace commitment (80 columns).
//! - The base-trace commitment (9 355 SHA-256 columns + 23 producer
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

/// Carry-out-of-range soundness coverage for the four new `Range_k`
/// channels (`Range_2`/`Range_4`/`Range_5`/`Range_16`). Each is verified
/// the same way as the `xor_8` channel in [`verify_rejects_logup_sum_mutation`]:
/// bumping any one producer's claimed sum makes the per-component sums no
/// longer total zero, so the `LogupSumNonZero` gate rejects.
///
/// **Why this is the meaningful test rather than a witness-mutation
/// prove-and-reject:** an out-of-range carry that *also* keeps the
/// mod-2³² linear identity satisfied requires cascading edits to the
/// downstream `e_new`/`a_new`/finalization cells that consume it. The
/// soundness-gate test isolates the `Range_k` LogUp loop without that
/// cascade; the linear-path negative for carries is already covered by
/// `tests/constraint_negative.rs::rejects_swapped_carry_within_row`.
#[ignore = "slow: produces a real proof first; same cost as prove_and_verify_abc"]
#[test]
fn verify_rejects_range_k_claimed_sum_mutations() {
    use num_traits::One;
    use stwo::core::fields::qm31::SecureField;
    use stwo_sha256::stark::Sha256VerifyError;

    let msg = b"abc";
    let config = ProverConfig::default();
    let proof = prove_sha256(msg, &config).expect("prove_sha256 on b\"abc\"");

    // Sanity-check the baseline accepts before we exercise the four
    // range mutations.
    verify_sha256_proof(&proof).expect("baseline proof must verify");

    // For each of the four `Range_k` producers (index 0..4 corresponds
    // to `RANGE_TABLES` order: Range_2, Range_4, Range_5, Range_16),
    // bump that producer's claimed sum and assert the soundness gate
    // rejects. Iterating in-place catches a regression on any one
    // channel.
    for kind_idx in 0..4 {
        let mut mutated = proof.clone();
        mutated.interaction_claim.range[kind_idx].claimed_sum += SecureField::one();
        match verify_sha256_proof(&mutated) {
            Err(Sha256VerifyError::LogupSumNonZero) => {}
            other => panic!(
                "Range channel #{kind_idx} mutation: expected LogupSumNonZero, got {other:?}"
            ),
        }
    }
}
