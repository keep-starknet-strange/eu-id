//! Tests for the relying-party API (`prove_identity` / `verify_identity`) and
//! the combined-proof serialization the `eu-id` CLI relies on.
//!
//! `prove_identity` signs a credential with an issuer key and a policy and
//! returns one bound proof; `verify_identity` checks it against a
//! `PublicStatement` `{ issuer key Q, policy }` only. The headline properties:
//!
//! - an honest credential proves and verifies against its statement;
//! - caller-argument binding rejects a mismatched statement — wrong issuer key,
//!   wrong age threshold, or wrong accepted set — *before* the STARK check;
//! - the proof round-trips through bincode (the CLI's prove→file→verify path);
//! - a false statement (under-age) cannot be proved at all.
//!
//! Marked `#[ignore]` — a real STARK prove/verify dominated by P256 is slow; run
//! with `--release --ignored`.

use eu_id_prover::generator::IssuerKey;
use eu_id_prover::{
    fixtures, identity_expected_preprocessed_root, prove_identity, verify_identity,
    verify_identity_with_preprocessed_root, Error, Policy, Proof, PublicStatement,
};

/// The relying party's statement for a policy: the demo issuer's *public* key
/// (the trusted anchor) plus the policy. Rebuilt independently of any proof.
fn demo_statement(policy: &Policy) -> PublicStatement {
    PublicStatement::new(
        IssuerKey::demo().public_key(),
        policy.clone(),
        fixtures::demo_nonce_statement(),
    )
}

/// The headline happy path: prove an honest credential through `prove_identity`
/// and verify it through `verify_identity` against its public statement.
#[test]
#[ignore = "slow: full P256 + SHA + bridge + predicates STARK prove/verify; run with --release --ignored"]
fn prove_identity_then_verify_identity_round_trips() {
    let fixture = fixtures::valid_over_18();
    let proof = prove_identity(
        &fixture.signed.credential,
        &IssuerKey::demo(),
        &fixture.policy,
        &fixtures::demo_nonce_statement(),
    )
    .expect("honest credential proves");

    verify_identity(&proof, &demo_statement(&fixture.policy))
        .expect("bound proof verifies against its statement");
}

/// Caller-argument binding (requirement: the verifier rejects unless the proof's
/// public values equal the caller's statement). One proof, checked against
/// several wrong statements — each must be rejected, and each before the STARK
/// check, with a distinct error.
#[test]
#[ignore = "slow: full P256 + SHA + bridge + predicates STARK prove/verify; run with --release --ignored"]
fn verify_identity_binds_the_full_statement() {
    let fixture = fixtures::valid_over_18();
    let proof = prove_identity(
        &fixture.signed.credential,
        &IssuerKey::demo(),
        &fixture.policy,
        &fixtures::demo_nonce_statement(),
    )
    .expect("honest credential proves");

    // Correct statement verifies.
    verify_identity(&proof, &demo_statement(&fixture.policy)).expect("correct statement verifies");

    // Wrong issuer key Q (a different signing key's public key).
    let wrong_issuer = IssuerKey::from_seed(&[9u8; 32]).public_key();
    let wrong_q = PublicStatement::new(
        wrong_issuer,
        fixture.policy.clone(),
        fixtures::demo_nonce_statement(),
    );
    assert!(
        matches!(
            verify_identity(&proof, &wrong_q),
            Err(Error::IssuerKeyMismatch)
        ),
        "a statement with the wrong issuer key must be rejected",
    );

    // Wrong age threshold.
    let mut higher_threshold = fixture.policy.clone();
    higher_threshold.min_age_years = 21;
    assert!(
        matches!(
            verify_identity(&proof, &demo_statement(&higher_threshold)),
            Err(Error::AgePolicyMismatch)
        ),
        "a statement with a different age threshold must be rejected",
    );

    // Wrong accepted-nationality set.
    let mut other_set = fixture.policy.clone();
    other_set.accepted_nationalities = vec![999];
    assert!(
        matches!(
            verify_identity(&proof, &demo_statement(&other_set)),
            Err(Error::NatPolicyMismatch)
        ),
        "a statement with a different accepted set must be rejected",
    );
}

/// The CLI's persistence path: a proof serialized with bincode and read back
/// verifies identically (the combined `Proof` is serde-serializable end to end).
#[test]
#[ignore = "slow: full P256 + SHA + bridge + predicates STARK prove/verify; run with --release --ignored"]
fn proof_round_trips_through_bincode() {
    let fixture = fixtures::valid_over_18();
    let proof = prove_identity(
        &fixture.signed.credential,
        &IssuerKey::demo(),
        &fixture.policy,
        &fixtures::demo_nonce_statement(),
    )
    .expect("honest credential proves");

    let bytes = bincode::serialize(&proof).expect("proof serializes");
    let restored: Proof = bincode::deserialize(&bytes).expect("proof deserializes");

    verify_identity(&restored, &demo_statement(&fixture.policy))
        .expect("a deserialized proof verifies against its statement");
}

/// The F-ROOT pin end to end: the default verifier reconstructs tree 0 from
/// canonical verifier-side columns. The explicit-root API additionally checks
/// a caller-derived root, and both paths reject tampering before the STARK.
#[test]
#[ignore = "slow: full identity STARK prove/verify plus a tree-0 rebuild; run with --release --ignored"]
fn verify_identity_pins_the_preprocessed_root() {
    let fixture = fixtures::valid_over_18();
    let mut proof = prove_identity(
        &fixture.signed.credential,
        &IssuerKey::demo(),
        &fixture.policy,
        &fixtures::demo_nonce_statement(),
    )
    .expect("honest credential proves");

    verify_identity(&proof, &demo_statement(&fixture.policy))
        .expect("the default verifier pins and accepts the canonical tree-0 root");

    // The verifier's own derivation of the tree-0 root — from trusted module
    // constructions, never from the proof.
    let expected_root = identity_expected_preprocessed_root(
        &fixture.signed.credential,
        &IssuerKey::demo(),
        &fixture.policy,
        &fixtures::demo_nonce_statement(),
    )
    .expect("expected preprocessed root computes");

    verify_identity_with_preprocessed_root(&proof, &demo_statement(&fixture.policy), expected_root)
        .expect("honest proof verifies against the derived preprocessed root");

    // A proof whose tree-0 root does not match the pin is rejected fail-closed.
    let mut wrong_root = expected_root;
    wrong_root.0[0] ^= 1;
    assert!(
        matches!(
            verify_identity_with_preprocessed_root(
                &proof,
                &demo_statement(&fixture.policy),
                wrong_root,
            ),
            Err(Error::PreprocessedRootMismatch { .. })
        ),
        "a mismatched preprocessed root must be rejected before the STARK check",
    );

    // A proof whose tree-0 root is TAMPERED is rejected by the default verifier;
    // no caller-supplied root is needed to close F-ROOT.
    proof.stark_proof.0.commitments[0].0[0] ^= 1;
    assert!(
        matches!(
            verify_identity(&proof, &demo_statement(&fixture.policy)),
            Err(Error::PreprocessedRootMismatch { .. })
        ),
        "the default verifier must reject a tampered tree-0 root before the STARK check",
    );
}

/// A false statement cannot be proved: `prove_identity` for an under-age
/// credential is rejected at the age module's witness generation — there is no
/// proof to verify.
#[test]
#[ignore = "slow: builds the P256 draft before the age module rejects; run with --release --ignored"]
fn prove_identity_rejects_under_age() {
    let fixture = fixtures::under_18();
    let result = prove_identity(
        &fixture.signed.credential,
        &IssuerKey::demo(),
        &fixture.policy,
        &fixtures::demo_nonce_statement(),
    );
    assert!(
        matches!(result, Err(Error::AgePrepare(_))),
        "an under-age credential must not be provable, got: {:?}",
        result.err(),
    );
}
