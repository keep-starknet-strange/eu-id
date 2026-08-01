//! Mixed-profile ML-DSA mdoc extraction checks.
//!
//! These tests check issuer and device signatures and fixed public resource
//! shapes.

use eu_id_prover::mdoc::{
    extract_pid_mdoc, openid4vp_session_transcript, ExtractedPidMdoc, MdocError, MdocPidRequest,
};

#[allow(dead_code)]
#[path = "support/mldsa_fixture.rs"]
mod mldsa_fixture;

/// Return the canonical credential and request.
fn identity_fixture_and_request_for(
    nonce: &[u8],
) -> (mldsa_fixture::MldsaIdentityFixture, MdocPidRequest) {
    let session_transcript = openid4vp_session_transcript(nonce);
    let fixture = mldsa_fixture::mldsa_realistic_pid_fixture_with_age_over_18(&session_transcript);
    let request = MdocPidRequest::age_over_18(session_transcript);
    (fixture, request)
}

#[test]
fn identity_mdoc_extracts_concrete_mldsa_inputs() {
    let (fixture, request) = identity_fixture_and_request_for(b"session-transcript-123");
    let extracted = extract_pid_mdoc(&fixture.document, &request).expect("identity mdoc extracts");
    assert_eq!(
        extracted.issuer_auth_input.message,
        fixture.issuer_sig_structure
    );
    assert_eq!(
        extracted.device_auth_input.message,
        fixture.device_sig_structure
    );
}

#[test]
fn canonical_extraction_has_fixed_resource_shape() {
    let (fixture, request) = identity_fixture_and_request_for(b"session-transcript-123");
    let extracted = extract_pid_mdoc(&fixture.document, &request).expect("identity mdoc extracts");
    assert_eq!(
        extracted.mso.len(),
        eu_id_prover::mdoc::TS13_DEMO_MSO_PAYLOAD_BYTES
    );
    assert_eq!(
        stwo_sha256::native::pad_message(&extracted.attribute.item).len(),
        usize::from(eu_id_prover::mdoc::TS13_DEMO_ITEM_PADDED_BYTES)
    );
}

#[test]
fn independent_credentials_share_the_canonical_public_shape() {
    let transcript = openid4vp_session_transcript(b"public-shape");
    let credential_a = mldsa_fixture::mldsa_ts13_credential_a_with_transcript(&transcript);
    let credential_b = mldsa_fixture::mldsa_ts13_credential_b_with_transcript(&transcript);
    assert_ne!(credential_a.document, credential_b.document);

    let extract = |fixture: &mldsa_fixture::MldsaIdentityFixture| {
        let request = MdocPidRequest::age_over_18(transcript.clone());
        extract_pid_mdoc(&fixture.document, &request).expect("credential extracts")
    };
    let a = extract(&credential_a);
    let b = extract(&credential_b);
    let shape = |extracted: &ExtractedPidMdoc| {
        (
            extracted.mso.len(),
            stwo_sha256::native::pad_message(&extracted.attribute.item).len(),
            extracted.issuer_auth_input.message.len(),
            extracted.device_auth_input.message.len(),
        )
    };
    assert_eq!(shape(&a), shape(&b));
}

#[test]
fn fresh_transcript_changes_device_auth_but_not_the_issuer_credential() {
    let (fixture_a, request_a) = identity_fixture_and_request_for(b"transcript-a");
    let (fixture_b, request_b) = identity_fixture_and_request_for(b"transcript-b");
    let extracted_a = extract_pid_mdoc(&fixture_a.document, &request_a).expect("A extracts");
    let extracted_b = extract_pid_mdoc(&fixture_b.document, &request_b).expect("B extracts");

    assert_eq!(fixture_a.issuer_signature, fixture_b.issuer_signature);
    assert_eq!(
        extracted_a.issuer_auth_input.message,
        extracted_b.issuer_auth_input.message
    );
    assert_ne!(
        extracted_a.device_auth_input.message,
        extracted_b.device_auth_input.message
    );
    assert_eq!(extracted_a.attribute.item, extracted_b.attribute.item);
}

#[test]
fn ts13_equality_fixture_extracts_only_the_boolean_claim() {
    let session_transcript = openid4vp_session_transcript(b"ts13-equality-fixture");
    let fixture =
        mldsa_fixture::mldsa_age_over_18_fixture_with_digest_id(&session_transcript, 17, 17);
    let request = MdocPidRequest::age_over_18(session_transcript);

    let extracted =
        extract_pid_mdoc(&fixture.document, &request).expect("TS13 equality fixture extracts");
    let item = &extracted.attribute.item;
    assert!(item
        .windows("age_over_18".len())
        .any(|window| window == b"age_over_18"));
    assert!(item.contains(&0xf5));
}

#[test]
fn high_digest_id_credentials_preserve_public_resource_shape() {
    const BASE_DIGEST_ID: u64 = 0x1234;
    const VARIANT_DIGEST_ID: u64 = 0x4321;

    let session_transcript = openid4vp_session_transcript(b"high-digest-id-shape");
    let base = mldsa_fixture::mldsa_age_over_18_fixture_with_digest_id(
        &session_transcript,
        BASE_DIGEST_ID,
        0x17,
    );
    let variant = mldsa_fixture::mldsa_age_over_18_fixture_with_digest_id(
        &session_transcript,
        VARIANT_DIGEST_ID,
        0x42,
    );
    assert_eq!(base.issuer_pk, variant.issuer_pk);
    assert_eq!(base.device_pk, variant.device_pk);
    assert_ne!(base.document, variant.document);

    let request = MdocPidRequest::age_over_18(session_transcript);
    let base_extracted =
        extract_pid_mdoc(&base.document, &request).expect("high-ID base credential extracts");
    let variant_extracted =
        extract_pid_mdoc(&variant.document, &request).expect("high-ID variant credential extracts");
    assert_eq!(base_extracted.mso.len(), variant_extracted.mso.len());
    assert_eq!(
        stwo_sha256::native::pad_message(&base_extracted.attribute.item).len(),
        stwo_sha256::native::pad_message(&variant_extracted.attribute.item).len()
    );
}

/// Reject a changed issuer signature during extraction.
/// Also reject a changed device signature during extraction.
#[test]
fn identity_signature_tampers_reject_at_extraction() {
    let (fixture, request) = identity_fixture_and_request_for(b"session-transcript-123");

    let tamper = |needle: &[u8]| {
        let offset = fixture
            .document
            .windows(needle.len())
            .position(|window| window == needle)
            .expect("signature embedded in document");
        let mut tampered = fixture.document.clone();
        // Flip a byte inside the z region (past the 48-byte c̃).
        tampered[offset + stwo_mldsa::constants::C_TILDE_BYTES + 200] ^= 0x01;
        tampered
    };

    let issuer_tampered = tamper(&fixture.issuer_signature);
    assert!(matches!(
        extract_pid_mdoc(&issuer_tampered, &request),
        Err(MdocError::InvalidSignature("issuerAuth"))
    ));

    let device_tampered = tamper(&fixture.device_signature);
    assert!(matches!(
        extract_pid_mdoc(&device_tampered, &request),
        Err(MdocError::InvalidSignature("deviceSignature"))
    ));
}
