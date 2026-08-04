//! Current product proof API integration tests.
//!
//! The SDK owns the `proveIdentity`/`verifyIdentity` application API. This
//! crate exposes only its current mdoc proof payload and caller-authoritative
//! public statement.

use eu_id_prover::mdoc::{self, MdocDisclosureMode, MdocError};
use eu_id_prover::{prove_mdoc, verify_product_mdoc, Error, MdocProof, MdocStatement};

#[test]
fn public_statement_contains_only_caller_authoritative_inputs() {
    let fixture = mdoc::demo_mdoc_circuit_fixture();
    let public = MdocStatement::from_circuit(&fixture.statement);

    assert_eq!(public.request_binding, fixture.request.request_binding);
    assert_eq!(public.doctype, fixture.request.doctype);
    assert_eq!(public.namespace, fixture.request.namespace);
    assert_eq!(
        public.issuer_public_key,
        fixture.request.required_issuer_public_key
    );
    assert_eq!(
        public.device_message_hash,
        fixture.extracted.device_ecdsa_input.message_hash
    );
    assert_eq!(
        public.verification_time_epoch_seconds,
        fixture.request.verification_time_epoch_seconds
    );
    assert_eq!(
        public.ts13_revocation,
        fixture.request.revocation.public_inputs
    );
    assert_eq!(public.attributes, fixture.request.attributes);
    assert_eq!(public.policy, fixture.statement.policy);

    let object = serde_json::to_value(&public)
        .expect("public statement serializes")
        .as_object()
        .expect("public statement is an object")
        .clone();
    for private_field in [
        "birth_date",
        "nationality",
        "issuer_signature",
        "device_signature",
        "ts13_revocation_range",
        "ts13_revocation_signature",
        "id",
        "id_lo",
        "id_hi",
    ] {
        assert!(
            !object.contains_key(private_field),
            "private field {private_field} leaked into the public statement"
        );
    }
}

#[test]
fn product_api_rejects_noncurrent_request_and_policy_shapes_before_proving() {
    let fixture = mdoc::demo_mdoc_circuit_fixture();

    let mut wrong_doctype = fixture.request.clone();
    wrong_doctype.doctype = "org.iso.18013.5.1.mDL".to_string();
    assert!(matches!(
        prove_mdoc(
            &fixture.document,
            &wrong_doctype,
            fixture.statement.policy.clone()
        ),
        Err(Error::Mdoc(MdocError::ProductDoctypeMismatch))
    ));

    let mut wrong_namespace = fixture.request.clone();
    wrong_namespace.namespace = "org.iso.18013.5.1".to_string();
    assert!(matches!(
        prove_mdoc(
            &fixture.document,
            &wrong_namespace,
            fixture.statement.policy.clone()
        ),
        Err(Error::Mdoc(MdocError::ProductNamespaceMismatch))
    ));

    let mut wrong_attribute_order = fixture.request.clone();
    wrong_attribute_order.attributes.reverse();
    assert!(matches!(
        prove_mdoc(
            &fixture.document,
            &wrong_attribute_order,
            fixture.statement.policy.clone()
        ),
        Err(Error::Mdoc(MdocError::UnsupportedProductAttributeLayout))
    ));

    let mut duplicate_mode = fixture.request.clone();
    duplicate_mode.attributes[1].mode = MdocDisclosureMode::AgeOver;
    assert!(matches!(
        prove_mdoc(
            &fixture.document,
            &duplicate_mode,
            fixture.statement.policy.clone()
        ),
        Err(Error::Mdoc(MdocError::DuplicatePredicateMode("AgeOver")))
    ));

    let mut invalid_time = fixture.request.clone();
    invalid_time.verification_time_epoch_seconds = 0;
    assert!(matches!(
        prove_mdoc(
            &fixture.document,
            &invalid_time,
            fixture.statement.policy.clone()
        ),
        Err(Error::Mdoc(MdocError::InvalidVerificationTime))
    ));

    let mut unsorted_policy = fixture.statement.policy;
    unsorted_policy.accepted_nationalities = vec![*b"FR", *b"DE"];
    assert!(matches!(
        prove_mdoc(&fixture.document, &fixture.request, unsorted_policy),
        Err(Error::Mdoc(MdocError::InvalidNationality(_)))
    ));
}

#[test]
#[ignore = "proof-heavy current product proof serialization round trip"]
fn product_proof_payload_round_trips_through_the_current_api() {
    let fixture = mdoc::demo_mdoc_circuit_fixture();
    let (proof, statement) = prove_mdoc(
        &fixture.document,
        &fixture.request,
        fixture.statement.policy,
    )
    .expect("current product proof builds");
    verify_product_mdoc(&proof, &statement).expect("current product proof verifies");

    let bytes = bincode::serialize(&proof).expect("current proof payload serializes");
    let restored: MdocProof =
        bincode::deserialize(&bytes).expect("current proof payload deserializes");
    verify_product_mdoc(&restored, &statement).expect("restored current proof verifies");
}
