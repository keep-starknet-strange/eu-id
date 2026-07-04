use ecdsa::signature::Signer;
use eu_id_prover::fixtures::{self, signed_nonce_statement};
use eu_id_prover::{
    prove_identity, prove_nonce_signature, verify_identity, verify_nonce_signature, Error,
    IssuerKey, NonceSignatureStatement, PublicStatement,
};
use p256::ecdsa::{Signature as P256Signature, SigningKey};
use sha2::{Digest, Sha256};
use stwo_p256::types::{AffinePoint, Signature, U256};

/// A nonce statement signed with an arbitrary device-key seed — used to forge a
/// *different device key* than the fixtures' demo key.
fn signed_nonce_statement_with_seed(seed: [u8; 32], nonce: &[u8]) -> NonceSignatureStatement {
    let signing_key = SigningKey::from_bytes((&seed).into()).expect("valid signing key");
    let message = eu_id_prover::nonce_signature_message(nonce);
    let signature: P256Signature = signing_key.sign(&message);
    let encoded = signing_key.verifying_key().to_encoded_point(false);

    let r: [u8; 32] = signature.r().to_bytes().into();
    let s: [u8; 32] = signature.s().to_bytes().into();
    let x: [u8; 32] = encoded.x().expect("x")[..].try_into().expect("x len");
    let y: [u8; 32] = encoded.y().expect("y")[..].try_into().expect("y len");

    NonceSignatureStatement {
        device_key: AffinePoint {
            x: U256(x),
            y: U256(y),
        },
        nonce: nonce.to_vec(),
        signature: Signature {
            r: U256(r),
            s: U256(s),
        },
    }
}

#[test]
fn nonce_signature_message_is_domain_separated() {
    let message = eu_id_prover::nonce_signature_message(b"session-123");

    assert!(message.starts_with(b"EU-ID nonce signature v1\0"));
    assert!(message.ends_with(b"session-123"));
    assert_eq!(
        NonceSignatureStatement::message_hash_for_nonce(b"session-123").0,
        <[u8; 32]>::from(Sha256::digest(&message))
    );
}

#[test]
#[ignore = "slow: proves one P-256 nonce signature"]
fn nonce_signature_proof_verifies() {
    let statement = signed_nonce_statement(b"session-123");

    let proof = prove_nonce_signature(&statement).expect("nonce signature proves");

    verify_nonce_signature(&proof, &statement).expect("nonce signature verifies");
}

#[test]
#[ignore = "slow: proves one P-256 nonce signature"]
fn nonce_signature_proof_rejects_wrong_nonce() {
    let statement = signed_nonce_statement(b"session-123");
    let proof = prove_nonce_signature(&statement).expect("nonce signature proves");
    let mut wrong = statement.clone();
    wrong.nonce = b"session-456".to_vec();

    assert!(matches!(
        verify_nonce_signature(&proof, &wrong),
        Err(Error::P256InstanceMismatch)
    ));
}

#[test]
fn nonce_signature_rejects_tampered_signature_before_proving() {
    let mut statement = signed_nonce_statement(b"session-123");
    statement.signature.s.0[31] ^= 1;

    assert!(matches!(
        prove_nonce_signature(&statement),
        Err(Error::SignatureInvalid)
    ));
}

/// The holder nonce signature is now folded into the primary monolithic proof:
/// `prove_identity` takes the nonce statement and `verify_identity` binds it
/// (full instance, including the `z` it recomputes from the nonce).
#[test]
#[ignore = "slow: full six-module identity proof (credential + nonce P256)"]
fn identity_with_nonce_flow_verifies() {
    let fixture = fixtures::valid_over_18();
    let issuer = IssuerKey::demo();
    let nonce = signed_nonce_statement(b"session-123");
    let statement =
        PublicStatement::new(issuer.public_key(), fixture.policy.clone(), nonce.clone());

    let proof = prove_identity(&fixture.signed.credential, &issuer, &fixture.policy, &nonce)
        .expect("identity plus nonce proves");

    verify_identity(&proof, &statement).expect("identity plus nonce verifies");
}

/// A DIFFERENT nonce in the verifier's statement changes the recomputed `z`, so
/// the folded nonce module's instance no longer matches → `P256InstanceMismatch`.
#[test]
#[ignore = "slow: full six-module identity proof (credential + nonce P256)"]
fn identity_with_nonce_flow_rejects_wrong_nonce() {
    let fixture = fixtures::valid_over_18();
    let issuer = IssuerKey::demo();
    let nonce = signed_nonce_statement(b"session-123");
    let proof = prove_identity(&fixture.signed.credential, &issuer, &fixture.policy, &nonce)
        .expect("identity plus nonce proves");

    // Verify against a statement carrying a *different* nonce — same device key,
    // fresh session. The recomputed `z` differs, so the full-instance binding
    // rejects it.
    let wrong_nonce = signed_nonce_statement(b"session-456");
    let wrong = PublicStatement::new(issuer.public_key(), fixture.policy.clone(), wrong_nonce);
    assert!(matches!(
        verify_identity(&proof, &wrong),
        Err(Error::P256InstanceMismatch)
    ));
}

/// A DIFFERENT device key in the verifier's statement changes the instance's
/// public-key limbs, so the folded nonce module's instance no longer matches →
/// `P256InstanceMismatch`.
#[test]
#[ignore = "slow: full six-module identity proof (credential + nonce P256)"]
fn identity_with_nonce_flow_rejects_wrong_device_key() {
    let fixture = fixtures::valid_over_18();
    let issuer = IssuerKey::demo();
    let nonce = signed_nonce_statement(b"session-123");
    let proof = prove_identity(&fixture.signed.credential, &issuer, &fixture.policy, &nonce)
        .expect("identity plus nonce proves");

    // A statement whose nonce signature is over the same nonce but from a
    // different device key (seed [22; 32] ≠ the demo [11; 32]).
    let wrong_key_nonce = signed_nonce_statement_with_seed([22u8; 32], b"session-123");
    let wrong = PublicStatement::new(issuer.public_key(), fixture.policy.clone(), wrong_key_nonce);
    assert!(matches!(
        verify_identity(&proof, &wrong),
        Err(Error::P256InstanceMismatch)
    ));
}
