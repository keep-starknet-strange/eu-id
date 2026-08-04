//! Current product end-to-end soundness boundaries.
//!
//! Granular AIR and parser negative cases live beside their implementations.
//! These tests keep the supported public path bound across extraction, proving,
//! serialization, and verification.

use eu_id_prover::mdoc::{self, MdocCircuitStatement, MdocError};
use eu_id_prover::{prove_mdoc, verify_product_mdoc, Error};

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
fn extraction_binds_signed_digest_issuer_trust_and_device_context() {
    let fixture = mdoc::demo_mdoc_circuit_fixture();

    let mut changed_attribute = fixture.document.clone();
    flip_unique_document_value(&mut changed_attribute, b"1990-07-15");
    assert!(matches!(
        prove_mdoc(
            &changed_attribute,
            &fixture.request,
            fixture.statement.policy.clone()
        ),
        Err(Error::Mdoc(MdocError::ItemDigestMismatch {
            element,
            digest_id: 7
        })) if element == "birth_date"
    ));

    let mut wrong_issuer = fixture.request.clone();
    wrong_issuer.required_issuer_public_key.x.0[0] ^= 1;
    assert!(matches!(
        prove_mdoc(
            &fixture.document,
            &wrong_issuer,
            fixture.statement.policy.clone()
        ),
        Err(Error::Mdoc(MdocError::UntrustedIssuerCertificate))
    ));

    let mut wrong_session = fixture.request.clone();
    wrong_session.session_transcript = mdoc::openid4vp_session_transcript(b"other-session");
    assert!(matches!(
        prove_mdoc(&fixture.document, &wrong_session, fixture.statement.policy),
        Err(Error::Mdoc(MdocError::InvalidSignature("deviceSignature")))
    ));
}

#[test]
#[ignore = "proof-heavy false private age and nationality predicates"]
fn false_private_predicates_cannot_produce_a_product_proof() {
    let age_fixture = mdoc::demo_mdoc_circuit_fixture();
    let mut age_policy = age_fixture.statement.policy;
    age_policy.min_age_years = 80;
    assert!(matches!(
        prove_mdoc(&age_fixture.document, &age_fixture.request, age_policy),
        Err(Error::AgePrepare(_))
    ));

    let nationality_fixture = mdoc::demo_mdoc_circuit_fixture();
    let mut nationality_policy = nationality_fixture.statement.policy;
    nationality_policy.accepted_nationalities = vec![*b"FR"];
    assert!(matches!(
        prove_mdoc(
            &nationality_fixture.document,
            &nationality_fixture.request,
            nationality_policy
        ),
        Err(Error::NatPrepare(_))
    ));
}

#[test]
#[ignore = "proof-heavy product PCS and canonical preprocessed-root pins"]
fn product_verifier_pins_pcs_and_canonical_preprocessed_root() {
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

    let mut tampered_tree = proof;
    tampered_tree.stark_proof.0.commitments[0].0[0] ^= 1;
    assert!(matches!(
        verify_product_mdoc(&tampered_tree, &public_statement),
        Err(Error::PreprocessedRootMismatch { .. })
    ));

    let reconstructed = MdocCircuitStatement::from_extracted_at(
        &fixture.extracted,
        public_statement.policy,
        public_statement.verification_time_epoch_seconds,
    )
    .expect("current caller statement reconstructs");
    assert_eq!(
        reconstructed.request_binding,
        public_statement.request_binding
    );
}
