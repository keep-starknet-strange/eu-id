use super::flip_unique_document_value;
use eu_id_prover::{mdoc, prove_mdoc, Error};

#[test]
fn product_api_rejects_zero_request_binding_before_document_work() {
    let fixture = mdoc::demo_mdoc_circuit_fixture();
    let mut request = fixture.request;
    request.request_binding = [0; 32];

    assert!(matches!(
        prove_mdoc(&fixture.document, &request, fixture.statement.policy),
        Err(Error::RequestBindingMissing)
    ));
}

#[test]
fn product_api_rejects_malformed_cbor() {
    let fixture = mdoc::demo_mdoc_circuit_fixture();

    assert!(matches!(
        prove_mdoc(&[0xff], &fixture.request, fixture.statement.policy),
        Err(Error::Mdoc(_))
    ));
}

#[test]
fn product_api_rejects_device_context_issuer_and_revocation_tampering_before_proving() {
    let fixture = mdoc::demo_mdoc_circuit_fixture();
    let policy = fixture.statement.policy.clone();

    let mut changed_context = fixture.request.clone();
    changed_context.session_transcript = mdoc::openid4vp_session_transcript(b"other-session");
    assert!(matches!(
        prove_mdoc(&fixture.document, &changed_context, policy.clone()),
        Err(Error::Mdoc(_))
    ));

    let mut changed_issuer = fixture.request.clone();
    changed_issuer.required_issuer_public_key.x.0[0] ^= 1;
    assert!(matches!(
        prove_mdoc(&fixture.document, &changed_issuer, policy.clone()),
        Err(Error::Mdoc(_))
    ));

    let mut changed_revocation_signature = fixture.request;
    changed_revocation_signature.revocation.signature.s.0[31] ^= 1;
    assert!(matches!(
        prove_mdoc(&fixture.document, &changed_revocation_signature, policy),
        Err(Error::Revocation(_))
    ));
}

#[test]
fn product_api_rejects_each_tampered_p256_signature_before_proving() {
    let issuer_fixture = mdoc::demo_mdoc_circuit_fixture();
    let mut issuer_document = issuer_fixture.document.clone();
    flip_unique_document_value(
        &mut issuer_document,
        &issuer_fixture.statement.issuer_input.signature.s.0,
    );
    assert!(matches!(
        prove_mdoc(
            &issuer_document,
            &issuer_fixture.request,
            issuer_fixture.statement.policy
        ),
        Err(Error::Mdoc(_))
    ));

    let device_fixture = mdoc::demo_mdoc_circuit_fixture();
    let mut device_document = device_fixture.document.clone();
    flip_unique_document_value(
        &mut device_document,
        &device_fixture.statement.device_input.signature.s.0,
    );
    assert!(matches!(
        prove_mdoc(
            &device_document,
            &device_fixture.request,
            device_fixture.statement.policy
        ),
        Err(Error::Mdoc(_))
    ));

    let mut revocation_fixture = mdoc::demo_mdoc_circuit_fixture();
    revocation_fixture.request.revocation.signature.s.0[31] ^= 1;
    assert!(matches!(
        prove_mdoc(
            &revocation_fixture.document,
            &revocation_fixture.request,
            revocation_fixture.statement.policy
        ),
        Err(Error::Revocation(_))
    ));
}
