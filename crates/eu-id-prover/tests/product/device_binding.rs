//! Current ISO mdoc device-binding and request-context tests.

use super::{decode, flip_unique_document_value};
use ciborium::value::Value;
use eu_id_prover::mdoc::{self, MdocError};
use eu_id_prover::{prove_mdoc, Error, MdocStatement};

#[test]
fn device_authentication_is_tag24_wrapped_and_context_bound() {
    let session = mdoc::openid4vp_session_transcript(b"session-123");
    let doctype = "eu.europa.ec.eudi.pid.1";
    let authentication =
        mdoc::device_authentication_bytes(&session, doctype).expect("device context encodes");

    let Value::Tag(24, inner) = decode(&authentication) else {
        panic!("DeviceAuthenticationBytes must use tag 24");
    };
    let Value::Bytes(encoded) = *inner else {
        panic!("tag 24 must contain encoded DeviceAuthentication bytes");
    };
    let Value::Array(fields) = decode(&encoded) else {
        panic!("DeviceAuthentication must be an array");
    };
    assert_eq!(fields.len(), 4);
    assert_eq!(fields[0], Value::Text("DeviceAuthentication".to_string()));
    assert_eq!(fields[2], Value::Text(doctype.to_string()));

    let canonical_hash = mdoc::device_authentication_sig_structure_hash(&session, doctype)
        .expect("canonical device signature hash");
    assert_ne!(
        canonical_hash,
        mdoc::device_authentication_sig_structure_hash(
            &mdoc::openid4vp_session_transcript(b"session-456"),
            doctype,
        )
        .expect("changed-session hash")
    );
    assert_ne!(
        canonical_hash,
        mdoc::device_authentication_sig_structure_hash(&session, "wrong.doctype")
            .expect("changed-doctype hash")
    );
}

#[test]
fn current_product_rejects_session_and_device_signature_tampering() {
    let fixture = mdoc::demo_mdoc_circuit_fixture();
    let public = MdocStatement::from_circuit(&fixture.statement);
    assert_eq!(
        public.device_message_hash,
        fixture.extracted.device_ecdsa_input.message_hash
    );

    let mut wrong_session = fixture.request.clone();
    wrong_session.session_transcript = mdoc::openid4vp_session_transcript(b"wrong-session");
    assert!(matches!(
        prove_mdoc(
            &fixture.document,
            &wrong_session,
            fixture.statement.policy.clone()
        ),
        Err(Error::Mdoc(MdocError::InvalidSignature("deviceSignature")))
    ));

    let mut tampered_document = fixture.document;
    flip_unique_document_value(
        &mut tampered_document,
        &fixture.statement.device_input.signature.s.0,
    );
    assert!(matches!(
        prove_mdoc(
            &tampered_document,
            &fixture.request,
            fixture.statement.policy
        ),
        Err(Error::Mdoc(MdocError::InvalidSignature("deviceSignature")))
    ));
}
