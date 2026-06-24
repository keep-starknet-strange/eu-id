//! End-to-end **soundness & negative-test suite** — the integration backbone.
//!
//! The standalone components each ship their own negative suites; this suite
//! proves the *bindings* hold once the five modules (P256, SHA-256, the
//! digest-bind bridge, age, nationality) are welded into one proof. For each
//! mutation class it feeds a deliberately malformed witness through the combined
//! prover and asserts no accepting proof results, isolating one broken relation
//! at a time so a regression is always localised:
//!
//! | mutation                         | broken relation             | rejected by                |
//! |----------------------------------|-----------------------------|----------------------------|
//! | digest mismatch                  | SHA digest ↔ ECDSA z        | global LogUp balance       |
//! | DOB ≠ credential                 | age ↔ credential bytes      | global LogUp balance       |
//! | nationality ≠ credential         | nat ↔ credential bytes      | global LogUp balance       |
//! | wrong issuer key Q               | caller statement            | caller-argument binding    |
//! | weakened PCS config              | security profile            | config pin (pre-STARK)     |
//! | tampered signature               | ECDSA validity              | prover-side: witness build |
//! | under-age date of birth          | age statement               | prover-side: witness build |
//! | nationality outside accepted set | nat membership statement    | prover-side: witness build |
//!
//! Three failure modes, by where the lie lives. A **global-balance** break is a
//! well-formed per-module witness whose cross-module LogUp relation does not
//! cancel — caught at verify. A **caller-argument** break is an honest proof
//! checked against the wrong public statement — caught before the STARK check. A
//! **prover-side** break is an input no honest witness exists for (a false
//! predicate, an invalid signature) — the witness builder rejects it, so no proof
//! is ever produced.
//!
//! The positive case asserts the **bound statement** verifies: an honest
//! credential proves, and `verify_identity` accepts it against `{ Q, policy }`
//! only — the date of birth, the nationality, and the digest are proven equal to
//! the credential's, never supplied.
//!
//! Every case that builds a P256 trace is dominated by the ECDSA work and is
//! marked `#[ignore]`; the scheduled CI `e2e` job runs them with
//! `cargo test --workspace --release -- --ignored` (see `.github/workflows/
//! ci.yml`). One fast, prove-free test (`fixture_expectations_pin_the_mutation_
//! classes`) runs on every push, so a fixture drift that would silently defang a
//! heavy test is caught immediately rather than a day later.

use eu_id_prover::generator::IssuerKey;
use eu_id_prover::{
    fixtures, prove, prove_identity, verify, verify_identity, Error, PipelineWitness, Policy,
    Proof, PublicStatement,
};
use stwo_p256::proof::{P256ProofDraft, P256ProofError};
use stwo_p256::types::{AffinePoint, EcdsaVerifyInput, Signature, U256};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// A real P256 signature over `SHA-256(message)`, as an `EcdsaVerifyInput`. The
/// instance's `z` is `SHA-256(message)`. Used to forge a digest mismatch — sign
/// a message other than the hashed credential.
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

/// The relying party's public statement for a policy: the demo issuer's *public*
/// key (the trusted anchor) plus the policy. Rebuilt independently of any proof.
fn demo_statement(policy: &Policy) -> PublicStatement {
    PublicStatement::new(IssuerKey::demo().public_key(), policy.clone())
}

// ---------------------------------------------------------------------------
// Fast per-push guard (no `#[ignore]`)
// ---------------------------------------------------------------------------

/// The fixtures the heavy soundness tests rely on still declare the expectations
/// those tests assume. Each negative fixture must isolate exactly the one
/// property its mutation class targets; if a fixture drifts so that, say,
/// `tampered_dob_bytes` no longer isolates a binding break, the `#[ignore]` test
/// below would still "pass" for the wrong reason. This prove-free check catches
/// that on every push, ahead of the daily `e2e` job that runs the real proofs.
#[test]
fn fixture_expectations_pin_the_mutation_classes() {
    // Positive: every property holds, so the bound proof should verify.
    assert!(fixtures::valid_over_18().expectation.should_verify());

    // DOB-binding mutation: crypto sound and the age statement holds against the
    // injected date — only the credential binding is broken.
    let dob = fixtures::tampered_dob_bytes().expectation;
    assert!(dob.crypto_consistent && dob.age_ge_threshold && dob.nationality_accepted);
    assert!(
        !dob.binding_consistent,
        "tampered_dob_bytes must isolate a binding break",
    );

    // Nationality-binding mutation: crypto sound and membership holds against the
    // injected (also-accepted) code — only the binding is broken.
    let nat = fixtures::tampered_nationality_bytes().expectation;
    assert!(nat.crypto_consistent && nat.age_ge_threshold && nat.nationality_accepted);
    assert!(
        !nat.binding_consistent,
        "tampered_nationality_bytes must isolate a binding break",
    );

    // Under-age: only the age statement is false.
    let young = fixtures::under_18().expectation;
    assert!(young.crypto_consistent && young.binding_consistent && young.nationality_accepted);
    assert!(!young.age_ge_threshold);

    // Nationality outside the accepted set: only membership is false.
    let outside = fixtures::wrong_nationality().expectation;
    assert!(outside.crypto_consistent && outside.binding_consistent && outside.age_ge_threshold);
    assert!(!outside.nationality_accepted);

    // Tampered signature: only the crypto is false.
    let bad = fixtures::bad_signature().expectation;
    assert!(bad.binding_consistent && bad.age_ge_threshold && bad.nationality_accepted);
    assert!(!bad.crypto_consistent);
}

// ---------------------------------------------------------------------------
// Positive: the bound statement verifies
// ---------------------------------------------------------------------------

/// The honest path: an over-18 credential proves through `prove_identity` and
/// verifies through `verify_identity` against its public statement `{ Q, policy }`
/// — the date of birth, the nationality, and the digest are proven equal to the
/// credential's, never supplied. Every binding holds, so the global LogUp balance
/// cancels.
#[test]
#[ignore = "slow: full P256 + SHA + bridge + predicates STARK prove/verify; run with --release --ignored"]
fn honest_credential_verifies_against_its_bound_statement() {
    let fixture = fixtures::valid_over_18();
    let proof = prove_identity(
        &fixture.signed.credential,
        &IssuerKey::demo(),
        &fixture.policy,
    )
    .expect("an honest over-18 credential proves");

    verify_identity(&proof, &demo_statement(&fixture.policy))
        .expect("the bound proof verifies against its public statement");
}

// ---------------------------------------------------------------------------
// Negatives: global LogUp balance broken (well-formed witness, broken binding)
// ---------------------------------------------------------------------------

/// Digest binding: SHA hashes the credential `C` (so the age/nat bindings hold),
/// but the signature is over a *different* message, so its `z = SHA-256(other)`
/// ≠ `SHA-256(C)`. The digest-bind term cannot cancel SHA's yield → imbalance →
/// rejection.
#[test]
#[ignore = "slow: full P256 + SHA + bridge + predicates STARK prove/verify; run with --release --ignored"]
fn rejects_digest_mismatch() {
    let pw = fixtures::valid_over_18().pipeline_witness();

    // z = SHA-256(other) ≠ SHA-256(C).
    let other = signed_input(b"a different message than the signed credential");
    let draft = P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![other])
        .expect("a real signature builds a proof draft");

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
    .expect("the prover accepts the mismatch — the imbalance is a verify-time check");

    let expected = proof.p256_instances().to_vec();
    assert!(
        verify(&proof, &expected).is_err(),
        "signing one message while hashing another must be rejected",
    );
}

/// Age↔credential binding: a real under-18 credential (born 2010-01-01) is
/// signed, but the age module is fed an over-18 date of birth (2000-01-01). The
/// signature is valid and the age sub-statement passes against the injected date
/// — only the binding is broken. The age module's DOB-byte requires (for 2000)
/// no longer cancel SHA's yields (for 2010) → imbalance → rejection.
#[test]
#[ignore = "slow: full P256 + SHA + bridge + predicates STARK prove/verify; run with --release --ignored"]
fn rejects_dob_not_matching_credential() {
    let f = fixtures::tampered_dob_bytes();
    // The fixture isolates exactly this: crypto + age statement pass, binding fails.
    assert!(!f.expectation.binding_consistent);
    assert!(f.expectation.age_ge_threshold);

    let proof = prove_pipeline(&f.pipeline_witness()).expect("the prover accepts the mismatch");
    let expected = proof.p256_instances().to_vec();
    assert!(
        verify(&proof, &expected).is_err(),
        "an age proved from a DOB the credential does not contain must be rejected",
    );
}

/// Nationality↔credential binding: a credential for one nationality (DE = 276) is
/// signed, but the nat module proves set-membership for a *different* code
/// (FR = 250) that is also in the accepted set. The signature is valid, the age
/// sub-statement holds, and membership passes against the injected code — only
/// the binding is broken. The nat module's nationality-byte requires (for 250) no
/// longer cancel SHA's yields (for 276) → imbalance → rejection.
#[test]
#[ignore = "slow: full P256 + SHA + bridge + predicates STARK prove/verify; run with --release --ignored"]
fn rejects_nationality_not_matching_credential() {
    let f = fixtures::tampered_nationality_bytes();
    // The fixture isolates exactly this: crypto + age + membership pass, binding fails.
    assert!(!f.expectation.binding_consistent);
    assert!(f.expectation.nationality_accepted);

    let proof = prove_pipeline(&f.pipeline_witness()).expect("the prover accepts the mismatch");
    let expected = proof.p256_instances().to_vec();
    assert!(
        verify(&proof, &expected).is_err(),
        "a nationality proved from a code the credential does not contain must be rejected",
    );
}

// ---------------------------------------------------------------------------
// Negative: caller-argument binding (honest proof, wrong statement)
// ---------------------------------------------------------------------------

/// Wrong issuer key: an honest proof, checked against a statement that names a
/// *different* issuer. `verify_identity` rejects it before the STARK check — the
/// proof's ECDSA public-key limbs do not equal the statement's `Q`.
#[test]
#[ignore = "slow: full P256 + SHA + bridge + predicates STARK prove/verify; run with --release --ignored"]
fn rejects_wrong_issuer_key() {
    let fixture = fixtures::valid_over_18();
    let proof = prove_identity(
        &fixture.signed.credential,
        &IssuerKey::demo(),
        &fixture.policy,
    )
    .expect("an honest credential proves");

    // Sanity: it verifies against the true issuer.
    verify_identity(&proof, &demo_statement(&fixture.policy))
        .expect("the proof verifies against the true issuer");

    // A statement naming a different issuer key is rejected, with a distinct error.
    let wrong_issuer = IssuerKey::from_seed(&[9u8; 32]).public_key();
    let wrong = PublicStatement::new(wrong_issuer, fixture.policy.clone());
    assert!(
        matches!(
            verify_identity(&proof, &wrong),
            Err(Error::IssuerKeyMismatch)
        ),
        "a statement with the wrong issuer key must be rejected",
    );
}

/// Weakened PCS config: an honest proof whose prover-supplied FRI/grinding config
/// is downgraded after the fact (a single FRI query, no grinding). The combined
/// verifier pins the config against the security profile (96-bit conjectured) and
/// rejects it *before* the STARK check, so a low-query proof can never be
/// inherited. This is the combined-proof counterpart of the standalone P256
/// `current_p256_monolithic_verifier_rejects_weakened_pcs_config` test.
#[test]
#[ignore = "slow: full P256 + SHA + bridge + predicates STARK prove/verify; run with --release --ignored"]
fn rejects_weakened_pcs_config() {
    let fixture = fixtures::valid_over_18();
    let mut proof = prove_identity(
        &fixture.signed.credential,
        &IssuerKey::demo(),
        &fixture.policy,
    )
    .expect("an honest credential proves");

    // Sanity: it verifies at the pinned (security-calibrated) config.
    verify_identity(&proof, &demo_statement(&fixture.policy))
        .expect("the proof verifies at the pinned config");

    // Downgrade the prover-supplied config to a single FRI query and no grinding —
    // the cheap-to-forge setting the pin exists to reject.
    proof.stark_proof.0.config.fri_config.n_queries = 1;
    proof.stark_proof.0.config.pow_bits = 0;

    assert!(
        matches!(
            verify_identity(&proof, &demo_statement(&fixture.policy)),
            Err(Error::WeakConfig { .. })
        ),
        "a weakened PCS config must be rejected before the STARK check",
    );
}

// ---------------------------------------------------------------------------
// Negatives: no honest witness exists (prover-side rejection)
// ---------------------------------------------------------------------------

/// Tampered signature: an honest credential, but the issuer signature is
/// corrupted (a flipped bit in `s`). An invalid ECDSA signature cannot even enter
/// the pipeline — composing the P256 witness runs the native final-ECDSA check
/// (`R.x == r`) and rejects the mismatch outright, so no draft, and therefore no
/// proof, is ever produced. (The honest pipeline never reaches this: a
/// `PipelineWitness` only builds a draft for a signature that natively verifies,
/// so a bad signature yields `p256_draft = None`.)
#[test]
#[ignore = "slow: builds the P256 witness, whose final-ECDSA check rejects the bad signature; run with --release --ignored"]
fn rejects_tampered_signature() {
    let f = fixtures::bad_signature();
    // The fixture isolates exactly this: bindings + statements hold, crypto fails.
    assert!(!f.expectation.crypto_consistent);

    // Composing the in-circuit witness for the corrupted `(r, s')` fails its
    // final-ECDSA check: the recovered point's x-coordinate does not equal `r`.
    let result = P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![f
        .signed
        .ecdsa_input
        .clone()]);
    assert!(
        matches!(&result, Err(P256ProofError::FinalEcdsaCheck(_))),
        "a tampered signature must be rejected by the final-ECDSA check, got: {:?}",
        result.err(),
    );
}

/// Under-age: a false age statement cannot be proved at all. The validating age
/// module rejects the under-18 date of birth at witness generation, so the bound
/// prover never emits a proof.
#[test]
#[ignore = "slow: builds the P256 draft before the age module rejects; run with --release --ignored"]
fn rejects_under_age() {
    let fixture = fixtures::under_18();
    let result = prove_identity(
        &fixture.signed.credential,
        &IssuerKey::demo(),
        &fixture.policy,
    );
    assert!(
        matches!(result, Err(Error::AgePrepare(_))),
        "an under-age credential must be unprovable, got: {:?}",
        result.err(),
    );
}

/// Nationality outside the accepted set: a false membership statement cannot be
/// proved. The nat module finds no private code in the accepted set and rejects
/// at witness generation, so the bound prover never emits a proof.
#[test]
#[ignore = "slow: builds the P256 draft before the nat module rejects; run with --release --ignored"]
fn rejects_nationality_outside_accepted_set() {
    let fixture = fixtures::wrong_nationality();
    let result = prove_identity(
        &fixture.signed.credential,
        &IssuerKey::demo(),
        &fixture.policy,
    );
    assert!(
        matches!(result, Err(Error::NatPrepare(_))),
        "a nationality outside the accepted set must be unprovable, got: {:?}",
        result.err(),
    );
}
