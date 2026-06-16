//! Composes the P256 ECDSA module and the SHA-256 module into one STARK proof
//! and round-trips it through the shared orchestrator.
//!
//! This validates the multi-module pipeline end-to-end: two heterogeneous
//! circuits (different constraint degrees, P256's lifting/store-coefficients
//! path, distinct preprocessed namespaces) prove and verify under one channel,
//! one commitment scheme, and one global LogUp balance. The composition is
//! unbound (see the crate docs).
//!
//! Marked `#[ignore]` — a real STARK prove/verify dominated by P256 is slow;
//! run with `--release --ignored`.

use eu_id_prover::{prove, verify};
use stwo_p256::ecdsa::ecdsa_verify;
use stwo_p256::proof::P256ProofDraft;
use stwo_p256::types::{AffinePoint, EcdsaVerifyInput, Signature, U256};
use stwo_sha256::trace::min_log_size;
use stwo_sha256::witness::compute_sha256_witness;

/// A real P256 signature over a SHA-256 message digest, as an `EcdsaVerifyInput`
/// (mirrors the stwo-p256 test fixture).
fn signed_input(message: &[u8]) -> EcdsaVerifyInput {
    use ::ecdsa::signature::Signer;
    use p256::ecdsa::{Signature as P256Signature, SigningKey};
    use sha2::{Digest, Sha256};

    let signing_key = SigningKey::from_bytes((&[7u8; 32]).into()).expect("valid signing key");
    let verifying_key = signing_key.verifying_key();
    let digest = Sha256::digest(message);
    let signature: P256Signature = signing_key.sign(message);
    let encoded = verifying_key.to_encoded_point(false);

    let r_bytes: [u8; 32] = signature.r().to_bytes().into();
    let s_bytes: [u8; 32] = signature.s().to_bytes().into();
    let x_bytes: [u8; 32] = encoded.x().expect("x")[..].try_into().expect("x len");
    let y_bytes: [u8; 32] = encoded.y().expect("y")[..].try_into().expect("y len");

    EcdsaVerifyInput {
        message_hash: U256(digest.into()),
        signature: Signature {
            r: U256(r_bytes),
            s: U256(s_bytes),
        },
        public_key: AffinePoint {
            x: U256(x_bytes),
            y: U256(y_bytes),
        },
    }
}

#[test]
#[ignore = "slow: full P256 + SHA STARK prove/verify; run with --release --ignored"]
fn composes_and_verifies_p256_and_sha() {
    let message = b"eu-id combined p256 + sha256 fixture";

    // P256 module: prove the ECDSA signature verifies.
    let input = signed_input(message);
    assert!(ecdsa_verify(&input), "native verifier must accept the fixture");
    let draft = P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![input])
        .expect("signature builds a proof draft");

    // SHA module: prove the message hashes (any message; the link to P256 is the
    // next step). Size the trace to the message's block count.
    let witness = compute_sha256_witness(message);
    let log_n_rows = min_log_size(witness.blocks.len()).max(4);
    let group_width = 7; // MAX_ROUND_GROUP_BITS, SHA's default group width.

    let proof = prove(&draft, &witness, log_n_rows, group_width).expect("combined proof generates");

    // Bound to its own P256 statement, the combined proof verifies (global
    // LogUp balance holds across both modules).
    let expected = proof.p256_instances().to_vec();
    verify(&proof, &expected).expect("combined proof verifies");

    // Caller-argument binding: a mismatched expected statement is rejected.
    let mut wrong = expected;
    wrong.truncate(0);
    assert!(verify(&proof, &wrong).is_err());
}
