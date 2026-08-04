//! Current product end-to-end soundness boundaries.
//!
//! Granular AIR and parser negative cases live beside their implementations.
//! These tests keep the supported public path bound across extraction, proving,
//! serialization, and verification.

use super::flip_unique_document_value;
use eu_id_prover::mdoc::{self, MdocError};
use eu_id_prover::{prove_mdoc, Error};

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
