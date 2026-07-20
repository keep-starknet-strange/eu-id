//! Dedicated TS13 equality-and-revocation envelope regression.
//!
//! This uses a real ML-DSA issuer, device, and revocation signature. It is
//! intentionally separate from the product profile, whose mdoc request proves
//! age/nationality predicates rather than the TS13 Boolean equality claim.

use ciborium::value::Value;
use euid_zk_sdk::{
    ts13_default_circuit_hash, ts13_prove_zk_document, ts13_verify_zk_document, Ts13MdocWitness,
    Ts13PresentationRequest,
};
use sha2::{Digest, Sha256};

#[allow(dead_code)]
#[path = "../../eu-id-prover/tests/mldsa_fixture.rs"]
mod mldsa_fixture;

const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const ML_DSA_65_PUBLIC_KEY_BYTES: usize = 1952;

fn hex_sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn ts13_request(
    session_transcript: Vec<u8>,
    issuer_public_key: &[u8],
    revocation_public_key: Vec<u8>,
) -> Ts13PresentationRequest {
    Ts13PresentationRequest {
        credential_format: "mso_mdoc_zk".to_string(),
        zk_system_id: "stwo-euid-v1".to_string(),
        doctype: PID_DOCTYPE.to_string(),
        namespace: PID_NAMESPACE.to_string(),
        circuit_hash: ts13_default_circuit_hash(),
        num_attributes: 1,
        max_mdoc_bytes: 16_384,
        max_attribute_bytes: 32,
        potential_issuers: 1,
        revocation_enabled: true,
        revocation_id_width_bytes: 8,
        device_auth_profile: "iso18013-5".to_string(),
        current_date_epoch_day: 20_637,
        session_transcript,
        trusted_issuer_hashes: vec![hex_sha256(issuer_public_key)],
        revocation_public_key,
        revocation_epoch: 7,
    }
}

#[test]
fn ts13_equality_envelope_proves_and_verifies_with_public_only_artifact() {
    let session_transcript =
        eu_id_prover::mdoc::openid4vp_session_transcript(b"sdk-ts13-equality-session");
    let fixture = mldsa_fixture::mldsa_full_pq_fixture_with_attribute(
        &session_transcript,
        "age_over_18",
        Value::Bool(true),
    );
    assert_eq!(fixture.revocation_pk.len(), ML_DSA_65_PUBLIC_KEY_BYTES);

    let extraction_request = eu_id_prover::MdocPidRequest {
        doctype: PID_DOCTYPE.to_string(),
        namespace: PID_NAMESPACE.to_string(),
        attributes: vec![eu_id_prover::mdoc::MdocRequestedAttribute {
            element_identifier: "age_over_18".to_string(),
            mode: eu_id_prover::mdoc::MdocDisclosureMode::ValueEquality(vec![0xf5]),
        }],
        birth_date_element: "birth_date".to_string(),
        nationality_element: "nationality".to_string(),
        session_transcript: session_transcript.clone(),
        trusted_mldsa_issuer_public_keys: vec![fixture.issuer_pk.clone()],
        device_authentication_profile:
            eu_id_prover::mdoc::MdocDeviceAuthenticationProfile::Iso180135,
    };
    let extracted = eu_id_prover::mdoc::extract_pid_mdoc(&fixture.document, &extraction_request)
        .expect("TS13 equality fixture extracts");
    let id = eu_id_prover::ts13::ts13_mso_derived_revocation_id(&extracted.mso);
    const DISTINCTIVE_BOUND_OFFSET: u64 = 0x1122_3344_5566_7788;
    assert!(id > DISTINCTIVE_BOUND_OFFSET && id < u64::MAX - DISTINCTIVE_BOUND_OFFSET);
    let id_lo = id - DISTINCTIVE_BOUND_OFFSET;
    let id_hi = id + DISTINCTIVE_BOUND_OFFSET;
    let (_, revocation_signature) = mldsa_fixture::mldsa_revocation_fixture(id_lo, id_hi, 7);

    let request = ts13_request(
        session_transcript,
        &fixture.issuer_pk,
        fixture.revocation_pk.clone(),
    );
    let document = ts13_prove_zk_document(
        request.clone(),
        Ts13MdocWitness {
            document: fixture.document,
            trusted_issuer_public_keys: vec![fixture.issuer_pk],
            revocation_id_lo: id_lo,
            revocation_id_hi: id_hi,
            revocation_signature,
        },
    )
    .expect("dedicated TS13 equality proof builds");

    assert!(
        ts13_verify_zk_document(&request, &document).expect("TS13 verification runs"),
        "real TS13 equality envelope must verify"
    );
    let mut changed_epoch = request;
    changed_epoch.revocation_epoch += 1;
    assert!(
        !ts13_verify_zk_document(&changed_epoch, &document).expect("tampered request runs"),
        "TS13 verifier must bind the revocation epoch"
    );

    let id_lo_bytes = id_lo.to_le_bytes();
    let id_hi_bytes = id_hi.to_le_bytes();
    assert!(
        !document
            .proof
            .windows(id_lo_bytes.len())
            .any(|window| window == id_lo_bytes),
        "serialized TS13 verifier envelope must not contain id_lo"
    );
    assert!(
        !document
            .proof
            .windows(id_hi_bytes.len())
            .any(|window| window == id_hi_bytes),
        "serialized TS13 verifier envelope must not contain id_hi"
    );
}
