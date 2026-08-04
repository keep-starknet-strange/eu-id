use eu_id_prover::{mdoc, prove_mdoc, verify_product_mdoc, Error};

fn flip_unique_document_value(document: &mut [u8], value: &[u8]) {
    let offsets = document
        .windows(value.len())
        .enumerate()
        .filter_map(|(offset, window)| (window == value).then_some(offset))
        .collect::<Vec<_>>();
    assert_eq!(offsets.len(), 1, "fixture value must occur exactly once");
    document[offsets[0] + value.len() - 1] ^= 1;
}

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

#[test]
#[ignore = "proof-heavy product API round trip"]
fn product_api_round_trip_rejects_public_statement_drift() {
    let fixture = mdoc::demo_mdoc_circuit_fixture();
    let (proof, statement) = prove_mdoc(
        &fixture.document,
        &fixture.request,
        fixture.statement.policy,
    )
    .expect("current product proof builds");
    verify_product_mdoc(&proof, &statement).expect("current product proof verifies");

    let mut changed_binding = statement.clone();
    changed_binding.request_binding[0] ^= 1;
    assert!(verify_product_mdoc(&proof, &changed_binding).is_err());

    let mut changed_doctype = statement.clone();
    changed_doctype.doctype = "wrong.doctype".to_string();
    assert!(verify_product_mdoc(&proof, &changed_doctype).is_err());

    let mut changed_namespace = statement.clone();
    changed_namespace.namespace = "wrong.namespace".to_string();
    assert!(verify_product_mdoc(&proof, &changed_namespace).is_err());

    let mut changed_issuer = statement.clone();
    changed_issuer.issuer_public_key.x.0[0] ^= 1;
    assert!(verify_product_mdoc(&proof, &changed_issuer).is_err());

    let mut changed_device_hash = statement.clone();
    changed_device_hash.device_message_hash.0[0] ^= 1;
    assert!(verify_product_mdoc(&proof, &changed_device_hash).is_err());

    let mut changed_revocation_epoch = statement.clone();
    changed_revocation_epoch.ts13_revocation.epoch = changed_revocation_epoch
        .ts13_revocation
        .epoch
        .checked_add(1)
        .expect("fixture epoch can increment");
    assert!(verify_product_mdoc(&proof, &changed_revocation_epoch).is_err());

    let mut changed_revocation_key = statement.clone();
    changed_revocation_key
        .ts13_revocation
        .revocation_public_key
        .x
        .0[0] ^= 1;
    assert!(verify_product_mdoc(&proof, &changed_revocation_key).is_err());

    let mut changed_scope = statement.clone();
    changed_scope.attributes.pop();
    assert!(verify_product_mdoc(&proof, &changed_scope).is_err());

    let mut changed_policy = statement;
    changed_policy.policy.min_age_years = changed_policy
        .policy
        .min_age_years
        .checked_add(1)
        .expect("fixture age can increment");
    assert!(verify_product_mdoc(&proof, &changed_policy).is_err());
}
