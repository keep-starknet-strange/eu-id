#[allow(dead_code)]
#[path = "support/mldsa_fixture.rs"]
mod fixture;

use fixture::*;
use stwo_mldsa::profile::{MlDsaProfile, ML_DSA_44, ML_DSA_65};
use stwo_mldsa::reference::verify::verify_internals;

fn rejects(profile: MlDsaProfile, public_key: &[u8], message: &[u8], signature: &[u8]) -> bool {
    match verify_internals(profile, public_key, message, signature) {
        Ok(trace) => !trace.accepted,
        Err(_) => true,
    }
}

#[test]
fn independent_credentials_change_private_facts_without_changing_shape() {
    let transcript =
        eu_id_prover::mdoc::openid4vp_session_transcript(b"ts13-unlinkable-shape-control");
    let credential_a = mldsa_ts13_credential_a_with_transcript(&transcript);
    let credential_b = mldsa_ts13_credential_b_with_transcript(&transcript);

    assert_eq!(credential_a.issuer_pk, credential_b.issuer_pk);
    assert_eq!(credential_a.revocation_pk, credential_b.revocation_pk);
    assert_ne!(credential_a.device_pk, credential_b.device_pk);
    assert_ne!(credential_a.mso, credential_b.mso);
    assert_ne!(credential_a.issuer_signature, credential_b.issuer_signature);
    assert_ne!(credential_a.device_signature, credential_b.device_signature);
    assert_ne!(
        eu_id_prover::ts13::ts13_mso_derived_revocation_id(&credential_a.mso),
        eu_id_prover::ts13::ts13_mso_derived_revocation_id(&credential_b.mso),
    );

    assert_eq!(credential_a.document.len(), credential_b.document.len());
    assert_eq!(credential_a.mso.len(), credential_b.mso.len());
    assert_eq!(
        credential_a.issuer_sig_structure.len(),
        credential_b.issuer_sig_structure.len()
    );
    assert_eq!(
        credential_a.device_sig_structure.len(),
        credential_b.device_sig_structure.len()
    );
    assert_eq!(credential_a.document.len(), 12_136);
    assert_eq!(credential_a.mso.len(), 2_513);
    assert_eq!(credential_a.issuer_sig_structure.len(), 2_534);
    assert_eq!(credential_a.device_sig_structure.len(), 130);
    let request = eu_id_prover::MdocPidRequest::age_over_18(transcript);
    let extracted = eu_id_prover::mdoc::extract_pid_mdoc(&credential_a.document, &request)
        .expect("unlinkability fixture extracts");
    assert_eq!(extracted.attribute.item.len(), 100);
    assert_eq!(
        stwo_sha256::native::pad_message(&extracted.attribute.item).len(),
        128
    );
}

#[test]
fn identity_fixture_issuer_and_device_verify_natively() {
    let fixture = mldsa_identity_fixture();
    assert_eq!(fixture.issuer_pk.len(), stwo_mldsa::constants::PK_BYTES);
    assert_eq!(fixture.device_pk.len(), stwo_mldsa::constants::PK_BYTES);
    assert_eq!(
        fixture.issuer_signature.len(),
        stwo_mldsa::constants::SIG_BYTES
    );
    assert_eq!(
        fixture.device_signature.len(),
        stwo_mldsa::constants::SIG_BYTES
    );

    let issuer = verify_internals(
        ML_DSA_65,
        &fixture.issuer_pk,
        &fixture.issuer_sig_structure,
        &fixture.issuer_signature,
    )
    .expect("issuer signature decodes");
    assert!(
        issuer.accepted,
        "ML-DSA issuer signature must verify: {:?}",
        issuer.reason
    );
    let device = verify_internals(
        ML_DSA_44,
        &fixture.device_pk,
        &fixture.device_sig_structure,
        &fixture.device_signature,
    )
    .expect("device signature decodes");
    assert!(
        device.accepted,
        "ML-DSA device signature must verify: {:?}",
        device.reason
    );
}

#[test]
fn identity_fixture_device_key_is_akp_with_anchor() {
    let fixture = mldsa_identity_fixture();
    let mut anchor = vec![0x20, 0x59, 0x07, 0xA0];
    anchor.extend_from_slice(&fixture.device_pk);
    assert!(
        fixture
            .document
            .windows(anchor.len())
            .any(|window| window == anchor),
        "the document must contain the encoded device public key"
    );
}

#[test]
fn identity_fixture_rejects_tampered_issuer_signature() {
    let mut fixture = mldsa_identity_fixture();
    fixture.issuer_signature[stwo_mldsa::constants::C_TILDE_BYTES + 200] ^= 1;
    assert!(rejects(
        ML_DSA_65,
        &fixture.issuer_pk,
        &fixture.issuer_sig_structure,
        &fixture.issuer_signature
    ));
}

#[test]
fn identity_fixture_rejects_tampered_device_signature() {
    let mut fixture = mldsa_identity_fixture();
    fixture.device_signature[stwo_mldsa::constants::C_TILDE_BYTES + 200] ^= 1;
    assert!(rejects(
        ML_DSA_44,
        &fixture.device_pk,
        &fixture.device_sig_structure,
        &fixture.device_signature
    ));
}

#[test]
fn identity_fixture_is_deterministic() {
    let a = mldsa_identity_fixture();
    let b = mldsa_identity_fixture();
    assert_eq!(a.document, b.document);
    assert_eq!(a.device_pk, b.device_pk);
    assert_eq!(a.revocation_pk, b.revocation_pk);
}

#[test]
fn revocation_fixture_verifies_and_rejects_tamper() {
    let (public_key, signature) = mldsa_revocation_fixture(41, 4141, 7);
    assert_eq!(public_key.len(), stwo_mldsa::constants::PK_BYTES);
    assert_eq!(signature.len(), stwo_mldsa::constants::SIG_BYTES);
    assert_eq!(public_key, mldsa_identity_fixture().revocation_pk);

    let message = eu_id_prover::ts13::ts13_revocation_message(41, 4141, 7);
    let trace = verify_internals(ML_DSA_65, &public_key, &message, &signature)
        .expect("revocation signature decodes");
    assert!(
        trace.accepted,
        "ML-DSA revocation signature must verify: {:?}",
        trace.reason
    );

    let mut changed_signature = signature.clone();
    changed_signature[stwo_mldsa::constants::C_TILDE_BYTES + 200] ^= 1;
    assert!(rejects(
        ML_DSA_65,
        &public_key,
        &message,
        &changed_signature
    ));
    assert!(rejects(
        ML_DSA_65,
        &public_key,
        &eu_id_prover::ts13::ts13_revocation_message(41, 4141, 8),
        &signature
    ));
}
