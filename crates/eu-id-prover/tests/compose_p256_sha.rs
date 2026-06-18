//! End-to-end composition + binding tests for the combined `eu-id` proof.
//!
//! Drives the P256 ECDSA module, the SHA-256 module, the digest-bind bridge, and
//! the age + nationality predicate modules through one STARK proof and exercises
//! the cross-module bindings that are wired so far:
//!
//! - **Digest binding** (§6.3): the global LogUp balance cancels only when the
//!   ECDSA message hash `z` equals the digest SHA actually computed —
//!   `rejects_signed_one_message_hashed_another` hashes a credential but signs a
//!   different message and asserts rejection.
//! - **Age↔credential binding** (§6.6): the date of birth the age module clears
//!   against the threshold must be the credential's signed DOB bytes —
//!   `rejects_age_dob_not_matching_credential` proves an over-18 date the
//!   credential does not contain and asserts rejection, while the honest and
//!   boundary fixtures (exactly-18, leap-year) verify and under-18 is rejected.
//!
//! Nationality is not yet credential-bound (§6.7), so the nat module nets to zero
//! internally and composes without changing the balance.
//!
//! Marked `#[ignore]` — a real STARK prove/verify dominated by P256 is slow; run
//! with `--release --ignored`.

use eu_id_prover::credential::Credential;
use eu_id_prover::generator::{sign_credential, IssuerKey};
use eu_id_prover::{fixtures, prove, verify, Error, PipelineWitness, Proof};
use stwo_p256::proof::P256ProofDraft;
use stwo_p256::types::{AffinePoint, EcdsaVerifyInput, Signature, U256};

/// A real P256 signature over `SHA-256(message)`, as an `EcdsaVerifyInput`. The
/// instance's `z` is `SHA-256(message)`. Used to forge a digest mismatch (sign a
/// message other than the hashed credential).
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

/// Drive a pipeline witness through the five-module combined prover.
fn prove_pipeline(pw: &PipelineWitness) -> Result<Proof, Error> {
    let draft = pw
        .p256_draft
        .as_ref()
        .expect("a valid signature builds a P256 draft");
    prove(
        draft,
        &pw.sha_witness,
        pw.sha_log_n_rows,
        pw.sha_group_width,
        &pw.age_public,
        &pw.age_dob,
        &pw.nat_public,
        &pw.nat_private,
    )
}

/// The honest end-to-end witness: a signed credential whose holder is over 18 and
/// whose nationality is accepted. Drives all five modules — P256, SHA-256, the
/// digest bridge, the **credential-bound** age module, and nationality — and
/// verifies. The age binding holds (the date of birth the module clears against
/// the threshold is the credential's signed DOB), and the digest binds, so the
/// global LogUp balance cancels.
#[test]
#[ignore = "slow: full P256 + SHA + bridge + predicates STARK prove/verify; run with --release --ignored"]
fn composes_all_modules_for_an_honest_credential() {
    let pw = fixtures::valid_over_18().pipeline_witness();
    assert!(
        pw.check_consistency().all_ok(),
        "fixture witness must be self-consistent"
    );

    let proof = prove_pipeline(&pw).expect("five-module proof generates");

    let expected = proof.p256_instances().to_vec();
    verify(&proof, &expected).expect("five-module bound proof verifies");

    // Caller-argument binding: a mismatched expected statement is rejected.
    assert!(
        verify(&proof, &[]).is_err(),
        "an empty expected statement must be rejected",
    );
}

/// The digest binding (§6.3), isolated: SHA hashes the credential `C` (so the age
/// binding holds), but the signature is over a *different* message, so its `z`
/// is the digest of that other message, not `SHA-256(C)`. The digest-bind
/// LogUp term cannot cancel SHA's yield → the verifier rejects.
#[test]
#[ignore = "slow: full P256 + SHA + bridge + predicates STARK prove/verify; run with --release --ignored"]
fn rejects_signed_one_message_hashed_another() {
    // SHA hashes the credential and the predicates use its attributes, so age
    // and nationality both hold — the only broken relation is the digest binding.
    let pw = fixtures::valid_over_18().pipeline_witness();

    // The signature is over a message that is NOT the credential bytes, so
    // z = SHA-256(other) ≠ SHA-256(C).
    let other = signed_input(b"a different message than the signed credential");
    let draft = P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![other])
        .expect("signature builds a proof draft");

    let proof = prove(
        &draft,
        &pw.sha_witness,
        pw.sha_log_n_rows,
        pw.sha_group_width,
        &pw.age_public,
        &pw.age_dob,
        &pw.nat_public,
        &pw.nat_private,
    )
    .expect("prover accepts the mismatch (imbalance is a verify-time check)");

    let expected = proof.p256_instances().to_vec();
    assert!(
        verify(&proof, &expected).is_err(),
        "signing one message while hashing another must be rejected",
    );
}

/// The age↔credential binding (§6.6), the headline of this task: a real under-18
/// credential (born 2010-01-01) is signed, but the age module is fed an over-18
/// date of birth (2000-01-01). The signature is valid and the age sub-statement
/// passes against the injected date — only the binding is broken. The age
/// module's DOB-byte requires (for 2000) no longer cancel SHA's yields (for
/// 2010), so the global balance breaks and the verifier rejects.
#[test]
#[ignore = "slow: full P256 + SHA + bridge + predicates STARK prove/verify; run with --release --ignored"]
fn rejects_age_dob_not_matching_credential() {
    let f = fixtures::tampered_dob_bytes();
    // The fixture isolates exactly this: crypto + age statement pass, binding fails.
    assert!(!f.expectation.binding_consistent);
    assert!(f.expectation.age_ge_threshold);

    let pw = f.pipeline_witness();
    let proof = prove_pipeline(&pw).expect("prover accepts the mismatch");

    let expected = proof.p256_instances().to_vec();
    assert!(
        verify(&proof, &expected).is_err(),
        "an age proved from a DOB the credential does not contain must be rejected",
    );
}

/// Boundary case through the bound path: a holder who turns exactly 18 on the
/// reference date (born 2008-06-17, cutoff 2008-06-17, DOB == cutoff is accepted).
/// The age binding holds and the proof verifies.
#[test]
#[ignore = "slow: full P256 + SHA + bridge + predicates STARK prove/verify; run with --release --ignored"]
fn binds_exactly_18_credential() {
    let pw = fixtures::valid_exactly_18().pipeline_witness();
    let proof = prove_pipeline(&pw).expect("exactly-18 proof generates");
    let expected = proof.p256_instances().to_vec();
    verify(&proof, &expected).expect("exactly-18 bound proof verifies");
}

/// Boundary case through the bound path: an under-18 credential (born 2008-06-18,
/// one day too young on the reference date). The validating age module rejects
/// the date of birth at witness generation, so the bound prover never emits a
/// proof — under-18 cannot be attested.
#[test]
#[ignore = "slow: builds the P256 draft before the age module rejects; run with --release --ignored"]
fn rejects_under_18_credential() {
    let pw = fixtures::under_18().pipeline_witness();
    let result = prove_pipeline(&pw);
    assert!(
        matches!(result, Err(Error::AgePrepare(_))),
        "an under-18 date of birth must be rejected by the bound prover, got: {:?}",
        result.err(),
    );
}

/// Boundary case through the bound path: a leap-day date of birth (born
/// 2000-02-29 — 2000 is a leap year, so Feb 29 exists). Exercises the calendar /
/// valid-day path of the bound age module; the binding holds and the proof
/// verifies. 2000-02-29 reconciles to DOB bytes `[0x07, 0xD0, 0x02, 0x1D]`.
#[test]
#[ignore = "slow: full P256 + SHA + bridge + predicates STARK prove/verify; run with --release --ignored"]
fn binds_leap_year_credential() {
    let credential = Credential::new(2000, 2, 29, 276);
    let signed = sign_credential(&credential, &IssuerKey::demo());
    let pw = PipelineWitness::build(signed, fixtures::demo_policy());
    assert!(
        pw.check_consistency().all_ok(),
        "leap-year credential witness must be self-consistent"
    );

    let proof = prove_pipeline(&pw).expect("leap-year proof generates");
    let expected = proof.p256_instances().to_vec();
    verify(&proof, &expected).expect("leap-year bound proof verifies");
}
