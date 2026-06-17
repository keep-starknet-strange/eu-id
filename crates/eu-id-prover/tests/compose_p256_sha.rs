//! Composes the P256 ECDSA module, the SHA-256 module, the digest-bind bridge,
//! and the age + nationality predicate modules into one STARK proof and
//! round-trips it through the shared orchestrator.
//!
//! Two things are validated here. First, the digest binding: the global LogUp
//! balance cancels only when the ECDSA message hash `z` equals the digest SHA
//! actually computed — the positive case proves a consistent witness (P256 signs
//! `SHA-256(m)`, SHA hashes the same `m`), the negative case signs one message
//! but hashes another and asserts rejection. Second, that all five modules
//! compose: `composes_all_modules_for_an_honest_credential` drives a real signed
//! credential through the full slice. The predicate modules are present but not
//! yet credential-bound, so each nets to zero and does not change the balance.
//!
//! Marked `#[ignore]` — a real STARK prove/verify dominated by P256 is slow; run
//! with `--release --ignored`.

use eu_id_prover::{fixtures, prove, verify};
use stwo_p256::ecdsa::ecdsa_verify;
use stwo_p256::proof::P256ProofDraft;
use stwo_p256::types::{AffinePoint, EcdsaVerifyInput, Signature, U256};
use stwo_sha256::trace::min_log_size;
use stwo_sha256::witness::compute_sha256_witness;

/// A real P256 signature over `SHA-256(message)`, as an `EcdsaVerifyInput`
/// (mirrors the stwo-p256 test fixture). The instance's `z` is `SHA-256(message)`.
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

fn sha_params(witness_blocks: usize) -> (u32, u32) {
    let log_n_rows = min_log_size(witness_blocks).max(4);
    let group_width = 7; // MAX_ROUND_GROUP_BITS, SHA's default group width.
    (log_n_rows, group_width)
}

/// Valid predicate inputs (over-18, accepted nationality) for the appended age
/// and nationality modules, taken from the honest `valid_over_18` fixture. The
/// digest-binding tests pair these with their own P256/SHA witnesses; the
/// predicates net to zero, so they compose without affecting the binding the
/// test exercises. `_lite` skips the (unused) P256 draft.
fn valid_predicate_inputs() -> eu_id_prover::PipelineWitness {
    fixtures::valid_over_18().pipeline_witness_lite()
}

#[test]
#[ignore = "slow: full P256 + SHA + bridge + predicates STARK prove/verify; run with --release --ignored"]
fn binds_p256_z_to_sha_digest() {
    let message = b"eu-id combined p256 + sha256 fixture";

    // P256 signs SHA-256(message); SHA hashes the same message. So z == digest.
    let input = signed_input(message);
    assert!(
        ecdsa_verify(&input),
        "native verifier must accept the fixture"
    );
    let draft = P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![input])
        .expect("signature builds a proof draft");

    let witness = compute_sha256_witness(message);
    let (log_n_rows, group_width) = sha_params(witness.blocks.len());

    let preds = valid_predicate_inputs();
    let proof = prove(
        &draft,
        &witness,
        log_n_rows,
        group_width,
        &preds.age_public,
        &preds.age_dob,
        &preds.nat_public,
        &preds.nat_private,
    )
    .expect("combined proof generates");

    // Bound to its own ECDSA statement, the cross-bound proof verifies (the
    // global LogUp balance holds: z == SHA-256(message) at the byte level).
    let expected = proof.p256_instances().to_vec();
    verify(&proof, &expected).expect("cross-bound proof verifies");

    // Caller-argument binding: a mismatched expected statement is rejected.
    let mut wrong = expected;
    wrong.truncate(0);
    assert!(verify(&proof, &wrong).is_err());
}

#[test]
#[ignore = "slow: full P256 + SHA + bridge + predicates STARK prove/verify; run with --release --ignored"]
fn rejects_signed_one_message_hashed_another() {
    // The binding the whole task exists for: P256 signs message B (so its `z` is
    // the digest of B), but the SHA module hashes message A. `z` no longer equals
    // the computed digest, so the global balance must break.
    let message_a = b"the message SHA-256 actually hashes";
    let message_b = b"a DIFFERENT message the signature is over";
    assert_ne!(&message_a[..], &message_b[..]);

    let input = signed_input(message_b); // z = SHA-256(message_b)
    assert!(ecdsa_verify(&input), "the signature itself is valid over B");
    let draft = P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![input])
        .expect("signature builds a proof draft");

    let witness = compute_sha256_witness(message_a); // SHA computes digest of A
    let (log_n_rows, group_width) = sha_params(witness.blocks.len());

    // The prover still produces a proof (each module is internally consistent;
    // the cross-module imbalance is a verify-time check). The appended predicates
    // are valid and net to zero, so the only imbalance is the digest mismatch.
    let preds = valid_predicate_inputs();
    let proof = prove(
        &draft,
        &witness,
        log_n_rows,
        group_width,
        &preds.age_public,
        &preds.age_dob,
        &preds.nat_public,
        &preds.nat_private,
    )
    .expect("prover accepts the mismatch");

    // The verifier rejects: digest(B) (the ECDSA z) ≠ digest(A) (what SHA hashed),
    // so the digest-bind LogUp term does not cancel SHA's yield.
    let expected = proof.p256_instances().to_vec();
    assert!(
        verify(&proof, &expected).is_err(),
        "signing one message while hashing another must be rejected",
    );
}

#[test]
#[ignore = "slow: full P256 + SHA + bridge + predicates STARK prove/verify; run with --release --ignored"]
fn composes_all_modules_for_an_honest_credential() {
    // The honest end-to-end witness from the credential generator: a signed
    // credential whose holder is over 18 and whose nationality is in the accepted
    // set. This drives all five modules — P256, SHA-256, the digest bridge, age,
    // and nationality — through one `air_core::prove`/`verify`, the unbound
    // pipeline the predicate-binding tasks build on.
    let pw = fixtures::valid_over_18().pipeline_witness();
    assert!(
        pw.check_consistency().all_ok(),
        "fixture witness must be self-consistent"
    );
    let draft = pw
        .p256_draft
        .as_ref()
        .expect("a valid signature builds a P256 draft");

    let proof = prove(
        draft,
        &pw.sha_witness,
        pw.sha_log_n_rows,
        pw.sha_group_width,
        &pw.age_public,
        &pw.age_dob,
        &pw.nat_public,
        &pw.nat_private,
    )
    .expect("five-module proof generates");

    // The full proof verifies against its own ECDSA statement: the digest binds
    // (z == SHA-256(C)) and each predicate's sub-balance nets to zero, so the
    // global LogUp balance holds.
    let expected = proof.p256_instances().to_vec();
    verify(&proof, &expected).expect("five-module proof verifies");
}
