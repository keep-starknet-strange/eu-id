use ciborium::value::Value;
use eu_id_prover::mdoc::{self, MdocCircuitStatement};
use eu_id_prover::{prove_mdoc, verify_product_mdoc, Error, MdocProof};

fn decode(bytes: &[u8]) -> Value {
    ciborium::de::from_reader(bytes).expect("fixture CBOR decodes")
}

fn flip_unique_document_value(document: &mut [u8], value: &[u8]) {
    let offsets = document
        .windows(value.len())
        .enumerate()
        .filter_map(|(offset, window)| (window == value).then_some(offset))
        .collect::<Vec<_>>();
    assert_eq!(offsets.len(), 1, "fixture value must occur exactly once");
    document[offsets[0] + value.len() - 1] ^= 1;
}

#[path = "product/device_binding.rs"]
mod device_binding;
#[path = "product/e2e_soundness.rs"]
mod e2e_soundness;
#[path = "product/identity_api.rs"]
mod identity_api;
#[path = "product/mdoc_support.rs"]
mod mdoc_support;
#[path = "product/product_api.rs"]
mod product_api;

#[test]
#[ignore = "proof-heavy product pins, serialization, and public statement matrix"]
fn product_proof_serialization_pins_and_statement_matrix() {
    let fixture = mdoc::demo_mdoc_circuit_fixture();
    let (proof, public_statement) = prove_mdoc(
        &fixture.document,
        &fixture.request,
        fixture.statement.policy.clone(),
    )
    .expect("current product proof builds");
    verify_product_mdoc(&proof, &public_statement).expect("current product proof verifies");

    let mut weak_pcs = proof.clone();
    weak_pcs.stark_proof.0.config.pow_bits = 0;
    weak_pcs.stark_proof.0.config.fri_config.n_queries = 1;
    assert!(matches!(
        verify_product_mdoc(&weak_pcs, &public_statement),
        Err(Error::WeakConfig { .. })
    ));

    let mut tampered_tree = proof.clone();
    tampered_tree.stark_proof.0.commitments[0].0[0] ^= 1;
    assert!(matches!(
        verify_product_mdoc(&tampered_tree, &public_statement),
        Err(Error::PreprocessedRootMismatch { .. })
    ));

    let reconstructed = MdocCircuitStatement::from_extracted_at(
        &fixture.extracted,
        public_statement.policy.clone(),
        public_statement.verification_time_epoch_seconds,
    )
    .expect("current caller statement reconstructs");
    assert_eq!(
        reconstructed.request_binding,
        public_statement.request_binding
    );

    let mut changed_binding = public_statement.clone();
    changed_binding.request_binding[0] ^= 1;
    assert!(verify_product_mdoc(&proof, &changed_binding).is_err());

    let mut changed_doctype = public_statement.clone();
    changed_doctype.doctype = "wrong.doctype".to_string();
    assert!(verify_product_mdoc(&proof, &changed_doctype).is_err());

    let mut changed_namespace = public_statement.clone();
    changed_namespace.namespace = "wrong.namespace".to_string();
    assert!(verify_product_mdoc(&proof, &changed_namespace).is_err());

    let mut changed_issuer = public_statement.clone();
    changed_issuer.issuer_public_key.x.0[0] ^= 1;
    assert!(verify_product_mdoc(&proof, &changed_issuer).is_err());

    let mut changed_device_hash = public_statement.clone();
    changed_device_hash.device_message_hash.0[0] ^= 1;
    assert!(verify_product_mdoc(&proof, &changed_device_hash).is_err());

    let mut changed_revocation_epoch = public_statement.clone();
    changed_revocation_epoch.ts13_revocation.epoch = changed_revocation_epoch
        .ts13_revocation
        .epoch
        .checked_add(1)
        .expect("fixture epoch can increment");
    assert!(verify_product_mdoc(&proof, &changed_revocation_epoch).is_err());

    let mut changed_revocation_key = public_statement.clone();
    changed_revocation_key
        .ts13_revocation
        .revocation_public_key
        .x
        .0[0] ^= 1;
    assert!(verify_product_mdoc(&proof, &changed_revocation_key).is_err());

    let mut changed_scope = public_statement.clone();
    changed_scope.attributes.pop();
    assert!(verify_product_mdoc(&proof, &changed_scope).is_err());

    let mut changed_policy = public_statement.clone();
    changed_policy.policy.min_age_years = changed_policy
        .policy
        .min_age_years
        .checked_add(1)
        .expect("fixture age can increment");
    assert!(verify_product_mdoc(&proof, &changed_policy).is_err());

    let bytes = bincode::serialize(&proof).expect("current proof payload serializes");
    let restored: MdocProof =
        bincode::deserialize(&bytes).expect("current proof payload deserializes");
    verify_product_mdoc(&restored, &public_statement).expect("restored current proof verifies");
}
