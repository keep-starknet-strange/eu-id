//! Dedicated TS13 equality-and-revocation envelope regression.
//!
//! This uses cryptographically real, deterministic RustCrypto ML-DSA issuer,
//! device, and revocation signatures around a realistic seven-attribute PID.
//! It is not a deployed issuer credential. The test is intentionally separate
//! from the product age/nationality-predicate profile.

use euid_zk_sdk::{
    ts13_default_circuit_hash, ts13_prove_zk_document, ts13_verify_zk_document, Ts13MdocWitness,
    Ts13PresentationRequest,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

#[allow(dead_code)]
#[path = "../../eu-id-prover/tests/mldsa_fixture.rs"]
mod mldsa_fixture;

const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const ML_DSA_65_PUBLIC_KEY_BYTES: usize = 1952;

#[derive(Serialize, Deserialize)]
struct Ts13ProofEnvelopeForTest {
    envelope_format: u16,
    request_binding_hash: String,
    mdoc_statement: eu_id_prover::MdocTs13Statement,
    stark_proof: Vec<u8>,
}

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
        max_mso_payload_bytes: eu_id_prover::ts13::TS13_MAX_MSO_PAYLOAD_BYTES as u32,
        max_attribute_bytes: 32,
        max_attribute_item_bytes: eu_id_prover::ts13::TS13_MAX_ATTRIBUTE_ITEM_BYTES as u32,
        max_requested_digest_id: eu_id_prover::ts13::TS13_MAX_REQUESTED_DIGEST_ID,
        max_issuer_mldsa_message_bytes: eu_id_prover::ts13::TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES
            as u32,
        max_device_mldsa_message_bytes: eu_id_prover::ts13::TS13_MAX_DEVICE_MLDSA_MESSAGE_BYTES
            as u32,
        merged_sha_slot_log: eu_id_prover::ts13::TS13_MERGED_SHA_SLOT_LOG,
        merged_sha_log_n_rows: eu_id_prover::ts13::TS13_MERGED_SHA_LOG_N_ROWS,
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

fn tamper_ts13_stark_proof(proof: &[u8]) -> Vec<u8> {
    let mut envelope: Ts13ProofEnvelopeForTest =
        bincode::deserialize(proof).expect("TS13 proof envelope decodes in test");
    assert!(
        !envelope.stark_proof.is_empty(),
        "TS13 envelope carries an inner STARK proof"
    );
    let tamper_index = envelope.stark_proof.len() / 2;
    envelope.stark_proof[tamper_index] ^= 0x01;
    bincode::serialize(&envelope).expect("tampered TS13 proof envelope serializes")
}

#[test]
fn ts13_equality_envelope_proves_and_verifies_with_public_only_artifact() {
    let session_transcript =
        eu_id_prover::mdoc::openid4vp_session_transcript(b"sdk-ts13-equality-session");
    let fixture = mldsa_fixture::mldsa_realistic_pid_fixture_with_age_over_18(&session_transcript);
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
    let issuer_c_tilde = extracted
        .issuer_auth_input
        .as_mldsa()
        .expect("ML-DSA issuer")
        .c_tilde;
    let device_c_tilde = extracted
        .device_auth_input
        .as_mldsa()
        .expect("ML-DSA device")
        .c_tilde;
    let requested_item_len = extracted.extracted_attributes[0].item.len();
    let expected_requested_item_padded_len = ((requested_item_len + 9 + 63) / 64 * 64) as u16;
    let id = eu_id_prover::ts13::ts13_mso_derived_revocation_id(&extracted.mso);
    const DISTINCTIVE_BOUND_OFFSET: u64 = 0x1122_3344_5566_7788;
    assert!(id > DISTINCTIVE_BOUND_OFFSET && id < u64::MAX - DISTINCTIVE_BOUND_OFFSET);
    let id_lo = id - DISTINCTIVE_BOUND_OFFSET;
    let id_hi = id + DISTINCTIVE_BOUND_OFFSET;
    let (_, revocation_signature) = mldsa_fixture::mldsa_revocation_fixture(id_lo, id_hi, 7);
    let revocation_signature_marker = revocation_signature[..64].to_vec();

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

    let envelope: Ts13ProofEnvelopeForTest =
        bincode::deserialize(&document.proof).expect("public TS13 envelope decodes");
    assert_eq!(envelope.envelope_format, 2);
    assert_eq!(
        envelope.mdoc_statement.attributes,
        extraction_request.attributes
    );
    assert_eq!(envelope.mdoc_statement.requested_digest_id, 17);
    assert_eq!(
        envelope.mdoc_statement.requested_item_padded_len,
        expected_requested_item_padded_len
    );
    assert!(
        ts13_verify_zk_document(&request, &document).expect("TS13 verification runs"),
        "real TS13 equality envelope must verify"
    );
    let mut changed_epoch = request.clone();
    changed_epoch.revocation_epoch += 1;
    assert!(
        !ts13_verify_zk_document(&changed_epoch, &document).expect("tampered request runs"),
        "TS13 verifier must bind the revocation epoch"
    );

    let mut changed_digest_id = document.clone();
    let mut envelope: Ts13ProofEnvelopeForTest =
        bincode::deserialize(&changed_digest_id.proof).expect("TS13 envelope decodes");
    envelope.mdoc_statement.requested_digest_id += 1;
    changed_digest_id.proof =
        bincode::serialize(&envelope).expect("changed TS13 envelope serializes");
    assert!(
        !ts13_verify_zk_document(&request, &changed_digest_id)
            .expect("tampered digest ID request runs"),
        "TS13 verifier must bind the requested digest ID"
    );

    let mut changed_item_padded_len = document.clone();
    let mut envelope: Ts13ProofEnvelopeForTest =
        bincode::deserialize(&changed_item_padded_len.proof).expect("TS13 envelope decodes");
    envelope.mdoc_statement.requested_item_padded_len = if expected_requested_item_padded_len == 64
    {
        128
    } else {
        64
    };
    changed_item_padded_len.proof =
        bincode::serialize(&envelope).expect("changed TS13 envelope serializes");
    assert!(
        !ts13_verify_zk_document(&request, &changed_item_padded_len)
            .expect("tampered item padded length request runs"),
        "TS13 verifier must bind the requested item padded length"
    );

    let mut tampered_document = document.clone();
    tampered_document.proof = tamper_ts13_stark_proof(&document.proof);
    assert!(
        !ts13_verify_zk_document(&request, &tampered_document).expect("tampered proof runs"),
        "TS13 verifier must reject a tampered inner STARK proof"
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
    for (name, private_marker) in [
        ("issuer c_tilde", issuer_c_tilde.as_slice()),
        ("device c_tilde", device_c_tilde.as_slice()),
        (
            "revocation signature",
            revocation_signature_marker.as_slice(),
        ),
        // The credential carries a birth_date the request never asks for. The
        // product (window-bind) path puts undisclosed attribute values in the
        // statement it ships; the TS13 equality path must not.
        ("undisclosed birth_date", b"1985-05-05".as_slice()),
    ] {
        assert!(
            !document
                .proof
                .windows(private_marker.len())
                .any(|window| window == private_marker),
            "serialized TS13 verifier envelope must not contain {name}"
        );
    }
}
