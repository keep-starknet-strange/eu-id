//! Dedicated TS13 equality-and-revocation envelope regression.
//!
//! This uses cryptographically real, deterministic RustCrypto ML-DSA issuer,
//! device, and revocation signatures around a realistic seven-attribute PID.
//! It is not a deployed issuer credential. The test is intentionally separate
//! from the product age/nationality-predicate profile.

use euid_zk_sdk::{
    prove_identity, ts13_default_circuit_hash, ts13_prove_zk_document, ts13_verify_zk_document,
    verify_identity, IssuerKey, NatMode, PredicateMode, TrustedIssuers, Ts13MdocWitness,
    Ts13PresentationRequest, ZkMdocWitness, ZkPublicStatement,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::HashSet;

#[allow(dead_code)]
#[path = "../../eu-id-prover/tests/mldsa_fixture.rs"]
mod mldsa_fixture;

const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const ML_DSA_65_PUBLIC_KEY_BYTES: usize = 1952;
const SHA256_BLOCK_BYTES: usize = 64;
const TS13_ENVELOPE_FORMAT_V3: u16 = 3;

#[derive(Serialize, Deserialize)]
struct Ts13ProofEnvelopeForTest {
    envelope_format: u16,
    request_binding_hash: String,
    mdoc_statement: eu_id_prover::MdocTs13Statement,
    stark_proof: Vec<u8>,
}

#[derive(Serialize, Deserialize)]
struct IdentityTs13ProofEnvelopeForTest {
    envelope_format: u16,
    document: Vec<u8>,
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
        value_digests_scan_log_size: eu_id_prover::ts13::TS13_VALUE_DIGESTS_SCAN_LOG_SIZE,
        value_digests_scan_max_items: eu_id_prover::ts13::TS13_VALUE_DIGESTS_SCAN_MAX_ITEMS,
        value_digests_scan_preprocessed_cols:
            eu_id_prover::ts13::TS13_VALUE_DIGESTS_SCAN_PREPROCESSED_COLS,
        value_digests_scan_trace_cols: eu_id_prover::ts13::TS13_VALUE_DIGESTS_SCAN_TRACE_COLS,
        value_digests_scan_relation_sites:
            eu_id_prover::ts13::TS13_VALUE_DIGESTS_SCAN_RELATION_SITES,
        value_digests_scan_interaction_cols:
            eu_id_prover::ts13::TS13_VALUE_DIGESTS_SCAN_INTERACTION_COLS,
        country_code_dataset: eu_id_prover::ts13::TS13_COUNTRY_CODE_DATASET.to_string(),
        country_code_table_log_size: eu_id_prover::ts13::TS13_COUNTRY_CODE_TABLE_LOG_SIZE,
        country_code_count: eu_id_prover::ts13::TS13_COUNTRY_CODE_COUNT,
        country_code_table_preprocessed_cols:
            eu_id_prover::ts13::TS13_COUNTRY_CODE_TABLE_PREPROCESSED_COLS,
        country_code_table_trace_cols: eu_id_prover::ts13::TS13_COUNTRY_CODE_TABLE_TRACE_COLS,
        country_code_table_interaction_cols:
            eu_id_prover::ts13::TS13_COUNTRY_CODE_TABLE_INTERACTION_COLS,
        country_code_table_sha256: eu_id_prover::ts13::TS13_COUNTRY_CODE_TABLE_SHA256.to_vec(),
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

fn identity_statement(
    request: Ts13PresentationRequest,
    issuer_public_key: &[u8],
) -> ZkPublicStatement {
    ZkPublicStatement {
        spec_id: "stwo-euid-pid-v1".to_string(),
        version: 1,
        doctype: request.doctype.clone(),
        namespace: request.namespace.clone(),
        issuer_key: IssuerKey::MlDsa {
            pk_hash: Sha256::digest(issuer_public_key).to_vec(),
        },
        today_epoch_day: request.current_date_epoch_day,
        nonce: request.session_transcript.clone(),
        predicate_mode: PredicateMode::Age,
        age_threshold_years: Some(18),
        accepted_numeric_countries: None,
        nat_mode: NatMode::Any,
        ts13_request: Some(request),
    }
}

fn distinctive_revocation_bounds(id: u64) -> (u64, u64) {
    const PREFERRED_BOUND_OFFSET: u64 = 0x1122_3344_5566_7788;
    let bound_offset = PREFERRED_BOUND_OFFSET.min(id / 2).min((u64::MAX - id) / 2);
    assert!(
        bound_offset > 0,
        "fixture-derived id supports strict bounds"
    );
    (id - bound_offset, id + bound_offset)
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

fn signature_witness_markers(
    role: &str,
    input: &stwo_mldsa::MlDsaVerifyInput,
) -> Vec<(String, Vec<u8>)> {
    let z = input.z.iter().flatten().copied().collect::<Vec<_>>();
    let hint = input.hint.iter().flatten().copied().collect::<Vec<_>>();
    vec![
        (
            format!("{role} c_tilde"),
            bincode::serialize(input.c_tilde.as_slice()).expect("c_tilde marker serializes"),
        ),
        (
            format!("{role} z"),
            bincode::serialize(&z).expect("z marker serializes"),
        ),
        (
            format!("{role} hint"),
            bincode::serialize(&hint).expect("hint marker serializes"),
        ),
    ]
}

#[test]
fn ts13_equality_envelope_proves_and_verifies_with_public_only_envelope() {
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
    let signature_witness_markers = [
        (
            "issuer",
            extracted
                .issuer_auth_input
                .as_mldsa()
                .expect("ML-DSA issuer"),
        ),
        (
            "device",
            extracted
                .device_auth_input
                .as_mldsa()
                .expect("ML-DSA device"),
        ),
    ]
    .into_iter()
    .flat_map(|(role, input)| signature_witness_markers(role, input))
    .collect::<Vec<_>>();
    let serialized_private_auth_inputs = [
        bincode::serialize(&extracted.issuer_auth_input).expect("issuer auth input serializes"),
        bincode::serialize(&extracted.device_auth_input).expect("device auth input serializes"),
    ];
    for (name, marker) in &signature_witness_markers {
        assert!(
            serialized_private_auth_inputs.iter().any(|input| {
                input
                    .windows(marker.len())
                    .any(|window| window == marker.as_slice())
            }),
            "private-input control must contain the serialized {name} witness"
        );
    }
    let requested_item_len = extracted.extracted_attributes[0].item.len();
    let expected_requested_item_padded_len =
        ((requested_item_len + 9).div_ceil(SHA256_BLOCK_BYTES) * SHA256_BLOCK_BYTES) as u16;
    let id = eu_id_prover::ts13::ts13_mso_derived_revocation_id(&extracted.mso);
    let (id_lo, id_hi) = distinctive_revocation_bounds(id);
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
            document: fixture.document.clone(),
            trusted_issuer_public_keys: vec![fixture.issuer_pk.clone()],
            revocation_id_lo: id_lo,
            revocation_id_hi: id_hi,
            revocation_signature: revocation_signature.clone(),
        },
    )
    .expect("dedicated TS13 equality proof builds");

    let envelope: Ts13ProofEnvelopeForTest =
        bincode::deserialize(&document.proof).expect("public TS13 envelope decodes");
    assert_eq!(envelope.envelope_format, TS13_ENVELOPE_FORMAT_V3);

    let phase1_stable_region_whitelist: [(&str, &[u8]); 2] = [
        // U7/U9: the full device public key remains public in Phase 1 and this
        // exact entry must disappear when private device-key binding lands.
        ("1,952-byte device public key", fixture.device_pk.as_slice()),
        // Permanent: the issuer trust key is verifier input and is never removed.
        ("issuer trust key", fixture.issuer_pk.as_slice()),
    ];
    assert_eq!(
        phase1_stable_region_whitelist.len(),
        2,
        "Phase-1 stable-region whitelist is exactly enumerated"
    );
    assert_eq!(
        phase1_stable_region_whitelist[0].1.len(),
        ML_DSA_65_PUBLIC_KEY_BYTES
    );
    for (name, stable_region) in phase1_stable_region_whitelist {
        assert!(
            document
                .proof
                .windows(stable_region.len())
                .any(|window| window == stable_region),
            "serialized TS13 envelope must contain the explicitly whitelisted {name}"
        );
    }

    assert_eq!(
        envelope.mdoc_statement.attributes,
        extraction_request.attributes
    );
    // `requested_digest_id` is deliberately absent from the verifier
    // envelope. Wrong-ID, wrong-position, and decoy substitution are covered
    // by proof-level valueDigests scanner negatives in the prover crate.
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
    for (name, private_marker) in &signature_witness_markers {
        assert!(
            !document
                .proof
                .windows(private_marker.len())
                .any(|window| window == private_marker.as_slice()),
            "serialized TS13 verifier envelope must not contain {name}"
        );
    }
    for (name, private_marker) in [
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

    let identity_statement = identity_statement(request.clone(), &fixture.issuer_pk);
    let identity_witness = ZkMdocWitness {
        document: fixture.document.clone(),
        trusted_issuers: TrustedIssuers::PublicKeys(vec![fixture.issuer_pk.clone()]),
        ts13_trusted_issuer_public_keys: Some(vec![fixture.issuer_pk.clone()]),
        ts13_revocation_id_lo: Some(id_lo),
        ts13_revocation_id_hi: Some(id_hi),
        ts13_revocation_signature: Some(revocation_signature.clone()),
    };
    let mut incomplete_witness = identity_witness.clone();
    incomplete_witness.ts13_revocation_id_hi = None;
    assert!(
        prove_identity(identity_statement.clone(), incomplete_witness).is_err(),
        "partial TS13 witness fields must fail closed"
    );

    let identity_proof =
        prove_identity(identity_statement.clone(), identity_witness).expect("identity TS13 proves");
    assert!(
        verify_identity(identity_statement.clone(), identity_proof.clone())
            .expect("identity TS13 verification runs")
            .ok,
        "identity TS13 proof verifies"
    );
    let identity_envelope: IdentityTs13ProofEnvelopeForTest =
        bincode::deserialize(&identity_proof).expect("identity TS13 envelope decodes");
    assert_eq!(identity_envelope.envelope_format, 8);
    let routed_document: euid_zk_sdk::Ts13ZkDocument =
        bincode::deserialize(&identity_envelope.document).expect("routed TS13 document decodes");
    let routed_inner: Ts13ProofEnvelopeForTest =
        bincode::deserialize(&routed_document.proof).expect("routed TS13 proof decodes");
    assert_eq!(routed_inner.envelope_format, TS13_ENVELOPE_FORMAT_V3);

    for (name, private_marker) in &signature_witness_markers {
        assert!(
            !identity_proof
                .windows(private_marker.len())
                .any(|window| window == private_marker.as_slice()),
            "identity TS13 envelope must not contain {name}"
        );
    }
    for (name, private_marker) in [
        (
            "revocation signature",
            revocation_signature_marker.as_slice(),
        ),
        ("id_lo", id_lo_bytes.as_slice()),
        ("id_hi", id_hi_bytes.as_slice()),
    ] {
        assert!(
            !identity_proof
                .windows(private_marker.len())
                .any(|window| window == private_marker),
            "identity TS13 envelope must not contain {name}"
        );
    }

    let mut product_statement = identity_statement.clone();
    product_statement.ts13_request = None;
    assert!(
        !verify_identity(product_statement, identity_proof.clone())
            .expect("product statement cross-rejection runs")
            .ok,
        "TS13 envelope must not reach the product verifier"
    );
    let mut product_tag: IdentityTs13ProofEnvelopeForTest =
        bincode::deserialize(&identity_proof).expect("identity TS13 envelope re-decodes");
    product_tag.envelope_format = 7;
    let product_tag = bincode::serialize(&product_tag).expect("product-tag tamper serializes");
    assert!(
        !verify_identity(identity_statement.clone(), product_tag)
            .expect("TS13 statement product-tag rejection runs")
            .ok,
        "product envelope tag must not reach the TS13 verifier"
    );

    let mut unknown_tag = identity_envelope;
    unknown_tag.envelope_format = 0xffff;
    let unknown_tag = bincode::serialize(&unknown_tag).expect("unknown-tag envelope serializes");
    assert!(
        verify_identity(identity_statement, unknown_tag).is_err(),
        "unknown identity envelope tags must reject"
    );
}

#[test]
#[ignore = "U9 Phase-2 gate: the device public key is intentionally public in Phase 1"]
fn phase2_u9_device_key_whitelist_is_empty_and_envelope_has_no_stable_run() {
    const MIN_STABLE_DEVICE_KEY_RUN_BYTES: usize = 32;

    let session_transcript =
        eu_id_prover::mdoc::openid4vp_session_transcript(b"sdk-ts13-phase2-u9-gate");
    let fixture = mldsa_fixture::mldsa_realistic_pid_fixture_with_age_over_18(&session_transcript);
    let device_public_key = fixture.device_pk.clone();
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
        .expect("U9 gate fixture extracts");
    let id = eu_id_prover::ts13::ts13_mso_derived_revocation_id(&extracted.mso);
    let (id_lo, id_hi) = distinctive_revocation_bounds(id);
    let (_, revocation_signature) = mldsa_fixture::mldsa_revocation_fixture(id_lo, id_hi, 7);
    let request = ts13_request(
        session_transcript,
        &fixture.issuer_pk,
        fixture.revocation_pk.clone(),
    );
    let document = ts13_prove_zk_document(
        request,
        Ts13MdocWitness {
            document: fixture.document,
            trusted_issuer_public_keys: vec![fixture.issuer_pk],
            revocation_id_lo: id_lo,
            revocation_id_hi: id_hi,
            revocation_signature,
        },
    )
    .expect("U9 gate proof builds");

    let phase2_device_key_stable_region_whitelist = Vec::<&[u8]>::new();
    assert!(
        phase2_device_key_stable_region_whitelist.is_empty(),
        "Phase-2 device-key stable-region whitelist must be empty"
    );

    let envelope_runs: HashSet<&[u8]> = document
        .proof
        .windows(MIN_STABLE_DEVICE_KEY_RUN_BYTES)
        .collect();
    let leaked_device_key_offset = device_public_key
        .windows(MIN_STABLE_DEVICE_KEY_RUN_BYTES)
        .position(|run| envelope_runs.contains(run));
    assert!(
        leaked_device_key_offset.is_none(),
        "serialized TS13 envelope contains a device-key run of at least \
         {MIN_STABLE_DEVICE_KEY_RUN_BYTES} bytes beginning at device-key offset {}",
        leaked_device_key_offset.unwrap_or_default()
    );
}
