//! Dedicated TS13 equality-and-revocation envelope regression.
//!
//! This uses cryptographically real, deterministic RustCrypto ML-DSA issuer,
//! device, and revocation signatures around a realistic seven-attribute PID.
//! It is not a deployed issuer credential. The test is intentionally separate
//! from the product age/nationality-predicate profile.

use bincode::Options;
use ciborium::value::Value;
use euid_zk_sdk::{
    prove_identity, ts13_default_circuit_hash, ts13_prove_zk_document, ts13_verify_zk_document,
    verify_identity, IssuerKey, NatMode, PredicateMode, ProductPublicStatementV1,
    Ts13DemoPublicStatementV1, Ts13DemoWitnessV1, Ts13MdocWitness, Ts13PresentationRequest,
    ZkError, ZkMdocWitness, ZkPublicStatement,
};
use ml_dsa::signature::Signer;
use ml_dsa::{EncodedSignature, MlDsa65, SigningKey};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::HashSet;
use std::io::Cursor;

#[allow(dead_code)]
#[path = "../../eu-id-prover/tests/mldsa_fixture.rs"]
mod mldsa_fixture;

const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const ML_DSA_65_PUBLIC_KEY_BYTES: usize = 1952;
const SHA256_BLOCK_BYTES: usize = 64;
const PRIVATE_FRAGMENT_BYTES: usize = 64;
const TS13_ENVELOPE_FORMAT_V3: u16 = 3;
const TS13_V4_HEADER_BYTES: usize = 46;
const TS13_DEMO_VERIFY_AT: i64 = 1_798_761_600;
const TS13_DEMO_REVOCATION_EPOCH: u32 = 17;
const TS13_SELECTED_DIGEST_ID: u64 = 17;
const DEMO_ISSUER_SEED: [u8; 32] = [0x5a; 32];

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
    let circuit_hash = request
        .circuit_hash
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            let hex = std::str::from_utf8(pair).expect("ASCII circuit hash");
            u8::from_str_radix(hex, 16).expect("hex circuit hash")
        })
        .collect();
    ZkPublicStatement::Ts13DemoV1(Ts13DemoPublicStatementV1 {
        circuit_hash,
        zk_system_id: "rp-local-ts13-legacy-regression".to_string(),
        document_type: request.doctype,
        namespace: request.namespace,
        element_identifier: "age_over_18".to_string(),
        expected_value_cbor: vec![0xf5],
        timestamp_epoch_seconds: i64::from(request.current_date_epoch_day) * 86_400,
        session_transcript: request.session_transcript,
        trusted_issuer_public_key: issuer_public_key.to_vec(),
        revocation_public_key: request.revocation_public_key,
        revocation_epoch: request.revocation_epoch,
    })
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

fn unlinkable_identity_statement(
    zk_system_id: &str,
    session_transcript: Vec<u8>,
    issuer_public_key: &[u8],
    revocation_public_key: &[u8],
) -> Ts13DemoPublicStatementV1 {
    Ts13DemoPublicStatementV1 {
        circuit_hash: eu_id_prover::ts13_demo_artifact_constants::TS13_DEMO_CIRCUIT_HASH.to_vec(),
        zk_system_id: zk_system_id.to_string(),
        document_type: PID_DOCTYPE.to_string(),
        namespace: PID_NAMESPACE.to_string(),
        element_identifier: "age_over_18".to_string(),
        expected_value_cbor: vec![0xf5],
        timestamp_epoch_seconds: TS13_DEMO_VERIFY_AT,
        session_transcript,
        trusted_issuer_public_key: issuer_public_key.to_vec(),
        revocation_public_key: revocation_public_key.to_vec(),
        revocation_epoch: TS13_DEMO_REVOCATION_EPOCH,
    }
}

fn normalized_fresh_context(statement: Ts13DemoPublicStatementV1) -> Ts13DemoPublicStatementV1 {
    let Ts13DemoPublicStatementV1 {
        circuit_hash,
        zk_system_id: _,
        document_type,
        namespace,
        element_identifier,
        expected_value_cbor,
        timestamp_epoch_seconds,
        session_transcript: _,
        trusted_issuer_public_key,
        revocation_public_key,
        revocation_epoch,
    } = statement;
    Ts13DemoPublicStatementV1 {
        circuit_hash,
        zk_system_id: "<fresh-rp-local-id>".to_string(),
        document_type,
        namespace,
        element_identifier,
        expected_value_cbor,
        timestamp_epoch_seconds,
        session_transcript: vec![0x80],
        trusted_issuer_public_key,
        revocation_public_key,
        revocation_epoch,
    }
}

fn semantic_public_bytes(statement: &Ts13DemoPublicStatementV1) -> Vec<u8> {
    let Ts13DemoPublicStatementV1 {
        circuit_hash,
        zk_system_id,
        document_type,
        namespace,
        element_identifier,
        expected_value_cbor,
        timestamp_epoch_seconds,
        session_transcript,
        trusted_issuer_public_key,
        revocation_public_key,
        revocation_epoch,
    } = statement;
    bincode::serialize(&(
        circuit_hash,
        zk_system_id,
        document_type,
        namespace,
        element_identifier,
        expected_value_cbor,
        timestamp_epoch_seconds,
        session_transcript,
        trusted_issuer_public_key,
        revocation_public_key,
        revocation_epoch,
    ))
    .expect("test-only semantic public surface serializes")
}

fn decode_cbor(bytes: &[u8], label: &str) -> Value {
    ciborium::de::from_reader(bytes).unwrap_or_else(|error| panic!("{label} CBOR decodes: {error}"))
}

fn encode_cbor(value: &Value, label: &str) -> Vec<u8> {
    let mut encoded = Vec::new();
    ciborium::ser::into_writer(value, &mut encoded)
        .unwrap_or_else(|error| panic!("{label} CBOR encodes: {error}"));
    encoded
}

fn text_map_value_mut<'a>(value: &'a mut Value, key: &str) -> &'a mut Value {
    let Value::Map(entries) = value else {
        panic!("{key} parent is a CBOR map");
    };
    entries
        .iter_mut()
        .find_map(|(candidate, value)| {
            (candidate == &Value::Text(key.to_string())).then_some(value)
        })
        .unwrap_or_else(|| panic!("CBOR map contains {key}"))
}

fn array_mut<'a>(value: &'a mut Value, label: &str) -> &'a mut Vec<Value> {
    let Value::Array(values) = value else {
        panic!("{label} is a CBOR array");
    };
    values
}

fn bytes_mut<'a>(value: &'a mut Value, label: &str) -> &'a mut Vec<u8> {
    let Value::Bytes(bytes) = value else {
        panic!("{label} is a CBOR byte string");
    };
    bytes
}

fn issuer_auth_mut(document: &mut Value) -> &mut Vec<Value> {
    let issuer_signed = text_map_value_mut(document, "issuerSigned");
    let issuer_auth = text_map_value_mut(issuer_signed, "issuerAuth");
    array_mut(issuer_auth, "issuerAuth")
}

fn device_signature_mut(document: &mut Value) -> &mut Vec<Value> {
    let device_signed = text_map_value_mut(document, "deviceSigned");
    let device_auth = text_map_value_mut(device_signed, "deviceAuth");
    let device_signature = text_map_value_mut(device_auth, "deviceSignature");
    array_mut(device_signature, "deviceSignature")
}

fn selected_item_mut(document: &mut Value) -> &mut Value {
    let issuer_signed = text_map_value_mut(document, "issuerSigned");
    let namespaces = text_map_value_mut(issuer_signed, "nameSpaces");
    let items = array_mut(
        text_map_value_mut(namespaces, PID_NAMESPACE),
        "PID namespace items",
    );
    items
        .iter_mut()
        .find(|item| {
            let Value::Bytes(encoded) = item else {
                return false;
            };
            encoded
                .windows(b"age_over_18".len())
                .any(|window| window == b"age_over_18")
        })
        .expect("fixture contains the selected age_over_18 item")
}

fn mutate_document(document: &[u8], mutation: impl FnOnce(&mut Value)) -> Vec<u8> {
    let mut value = decode_cbor(document, "mdoc document");
    mutation(&mut value);
    encode_cbor(&value, "mutated mdoc document")
}

fn cose_sig_structure(protected: &[u8], payload: &[u8]) -> Vec<u8> {
    encode_cbor(
        &Value::Array(vec![
            Value::Text("Signature1".to_string()),
            Value::Bytes(protected.to_vec()),
            Value::Bytes(Vec::new()),
            Value::Bytes(payload.to_vec()),
        ]),
        "COSE Sig_structure",
    )
}

fn resign_issuer_auth(document: &mut Value) {
    let issuer_auth = issuer_auth_mut(document);
    let protected = bytes_mut(&mut issuer_auth[0], "issuer protected header").clone();
    let payload = bytes_mut(&mut issuer_auth[2], "issuer MSO payload").clone();
    let signing_key = SigningKey::<MlDsa65>::from_seed(&DEMO_ISSUER_SEED.into());
    let signature = signing_key.sign(&cose_sig_structure(&protected, &payload));
    let encoded_signature: EncodedSignature<MlDsa65> = signature.encode();
    issuer_auth[3] = Value::Bytes(encoded_signature.to_vec());
}

fn mutate_mso_and_resign(document: &mut Value, mutation: impl FnOnce(&mut Value)) {
    let mut mso = {
        let issuer_auth = issuer_auth_mut(document);
        decode_cbor(
            bytes_mut(&mut issuer_auth[2], "issuer MSO payload"),
            "MSO payload",
        )
    };
    mutation(&mut mso);
    issuer_auth_mut(document)[2] = Value::Bytes(encode_cbor(&mso, "mutated MSO payload"));
    resign_issuer_auth(document);
}

fn mutate_selected_item(document: &mut Value, mutation: impl FnOnce(&mut Value)) {
    let encoded_item = bytes_mut(selected_item_mut(document), "selected IssuerSignedItem");
    let mut tagged = decode_cbor(encoded_item, "selected IssuerSignedItem");
    let Value::Tag(24, inner) = &mut tagged else {
        panic!("selected IssuerSignedItem has CBOR tag 24");
    };
    let encoded_inner = bytes_mut(inner, "selected IssuerSignedItem tag payload");
    let mut item = decode_cbor(encoded_inner, "selected IssuerSignedItem map");
    mutation(&mut item);
    *encoded_inner = encode_cbor(&item, "mutated IssuerSignedItem map");
    *encoded_item = encode_cbor(&tagged, "mutated IssuerSignedItem");
}

fn append_selected_item_trailing_cbor(document: &mut Value) {
    let encoded_item = bytes_mut(selected_item_mut(document), "selected IssuerSignedItem");
    let mut tagged = decode_cbor(encoded_item, "selected IssuerSignedItem");
    let Value::Tag(24, inner) = &mut tagged else {
        panic!("selected IssuerSignedItem has CBOR tag 24");
    };
    bytes_mut(inner, "selected IssuerSignedItem tag payload").push(0xf6);
    *encoded_item = encode_cbor(&tagged, "IssuerSignedItem with trailing CBOR");
}

fn update_selected_digest_and_resign(document: &mut Value) {
    let selected_item = bytes_mut(selected_item_mut(document), "selected IssuerSignedItem").clone();
    let selected_digest = Sha256::digest(&selected_item).to_vec();
    mutate_mso_and_resign(document, |mso| {
        let value_digests = text_map_value_mut(mso, "valueDigests");
        let namespace_digests = text_map_value_mut(value_digests, PID_NAMESPACE);
        let Value::Map(entries) = namespace_digests else {
            panic!("PID valueDigests entry is a map");
        };
        let digest = entries
            .iter_mut()
            .find_map(|(digest_id, digest)| {
                (digest_id == &Value::from(TS13_SELECTED_DIGEST_ID)).then_some(digest)
            })
            .expect("MSO contains the selected digest ID");
        *digest = Value::Bytes(selected_digest);
    });
}

fn flip_middle_byte(value: &mut Value, label: &str) {
    let bytes = bytes_mut(value, label);
    assert!(!bytes.is_empty(), "{label} is non-empty");
    let index = bytes.len() / 2;
    bytes[index] ^= 1;
}

fn v4_tree_zero_root(envelope: &[u8]) -> Vec<u8> {
    let mut cursor = Cursor::new(&envelope[TS13_V4_HEADER_BYTES..]);
    let proof: eu_id_prover::MdocProof = bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_little_endian()
        .allow_trailing_bytes()
        .deserialize_from(&mut cursor)
        .expect("valid V4 canonical proof prefix decodes");
    bincode::serialize(
        proof
            .stark_proof
            .commitments
            .first()
            .expect("TS13 proof has tree-zero commitment"),
    )
    .expect("tree-zero root serializes")
}

fn ts13_identity_witness(fixture: &mldsa_fixture::MldsaFullPqFixture) -> (ZkMdocWitness, Vec<u8>) {
    let id = eu_id_prover::ts13::ts13_mso_derived_revocation_id(&fixture.mso);
    let (id_lo, id_hi) = distinctive_revocation_bounds(id);
    let (_, revocation_signature) =
        mldsa_fixture::mldsa_revocation_fixture(id_lo, id_hi, TS13_DEMO_REVOCATION_EPOCH);
    (
        ZkMdocWitness::Ts13DemoV1(Ts13DemoWitnessV1 {
            document: fixture.document.clone(),
            revocation_id_lo: id_lo,
            revocation_id_hi: id_hi,
            revocation_signature: revocation_signature.clone(),
        }),
        revocation_signature,
    )
}

fn contains_marker(haystack: &[u8], marker: &[u8]) -> bool {
    haystack
        .windows(marker.len())
        .any(|window| window == marker)
}

fn variable_length_session_transcript(challenge: &[u8]) -> Vec<u8> {
    let mut transcript = Vec::new();
    ciborium::ser::into_writer(
        &ciborium::value::Value::Array(vec![
            ciborium::value::Value::Null,
            ciborium::value::Value::Null,
            ciborium::value::Value::Array(vec![
                "OpenID4VPHandover".into(),
                ciborium::value::Value::Bytes(challenge.to_vec()),
            ]),
        ]),
        &mut transcript,
    )
    .expect("canonical test SessionTranscript serializes");
    transcript
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

fn byte_context(haystack: &[u8], needle: &[u8], before: usize, after: usize) -> Vec<u8> {
    let offset = haystack
        .windows(needle.len())
        .position(|window| window == needle)
        .expect("private marker source contains its needle");
    haystack[offset.saturating_sub(before)..(offset + needle.len() + after).min(haystack.len())]
        .to_vec()
}

fn validity_markers(mso: &[u8]) -> Vec<(String, Vec<u8>)> {
    let value: ciborium::value::Value =
        ciborium::de::from_reader(mso).expect("fixture MSO decodes");
    let ciborium::value::Value::Map(mso_entries) = value else {
        panic!("fixture MSO is a map");
    };
    let validity = mso_entries
        .into_iter()
        .find_map(|(key, value)| {
            (key == ciborium::value::Value::Text("validityInfo".to_string())).then_some(value)
        })
        .expect("fixture MSO has validityInfo");
    let ciborium::value::Value::Map(validity_entries) = validity else {
        panic!("fixture validityInfo is a map");
    };

    ["signed", "validFrom", "validUntil"]
        .into_iter()
        .map(|field| {
            let value = validity_entries
                .iter()
                .find_map(|(key, value)| {
                    (key == &ciborium::value::Value::Text(field.to_string()))
                        .then_some(value.clone())
                })
                .unwrap_or_else(|| panic!("fixture validityInfo has {field}"));
            let mut encoded_entry = Vec::new();
            ciborium::ser::into_writer(
                &ciborium::value::Value::Map(vec![(
                    ciborium::value::Value::Text(field.to_string()),
                    value,
                )]),
                &mut encoded_entry,
            )
            .expect("validity entry serializes");
            assert_eq!(encoded_entry.remove(0), 0xa1);
            assert!(contains_marker(mso, &encoded_entry));
            (format!("validityInfo.{field}"), encoded_entry)
        })
        .collect()
}

fn private_fragments(label: &str, bytes: &[u8]) -> Vec<(String, Vec<u8>)> {
    assert!(bytes.len() >= 3 * PRIVATE_FRAGMENT_BYTES);
    [
        ("prefix", 0),
        ("middle", (bytes.len() - PRIVATE_FRAGMENT_BYTES) / 2),
        ("suffix", bytes.len() - PRIVATE_FRAGMENT_BYTES),
    ]
    .into_iter()
    .map(|(position, start)| {
        (
            format!("{label} {position}"),
            bytes[start..start + PRIVATE_FRAGMENT_BYTES].to_vec(),
        )
    })
    .collect()
}

fn private_identity_markers(
    fixture: &mldsa_fixture::MldsaFullPqFixture,
    statement: &Ts13DemoPublicStatementV1,
    revocation_signature: &[u8],
) -> Vec<(String, Vec<u8>)> {
    let mut request = eu_id_prover::MdocPidRequest::eudi_pid(statement.session_transcript.clone());
    request.attributes = vec![eu_id_prover::mdoc::MdocRequestedAttribute {
        element_identifier: "age_over_18".to_string(),
        mode: eu_id_prover::mdoc::MdocDisclosureMode::ValueEquality(vec![0xf5]),
    }];
    request.trusted_mldsa_issuer_public_keys = vec![fixture.issuer_pk.clone()];
    let extracted = eu_id_prover::mdoc::extract_pid_mdoc(&fixture.document, &request)
        .expect("unlinkability fixture extracts");
    let [attribute] = extracted.extracted_attributes.as_slice() else {
        panic!("unlinkability fixture has exactly one selected item");
    };

    let random_offset = attribute
        .item
        .windows(b"random".len())
        .position(|window| window == b"random")
        .expect("selected item has random");
    let digest_id_offset = attribute
        .item
        .windows(b"digestID".len())
        .position(|window| window == b"digestID")
        .expect("selected item has digestID");
    assert!(random_offset < digest_id_offset);
    let randomizer_context = attribute.item[random_offset.saturating_sub(1)
        ..(digest_id_offset + b"digestID".len() + 4).min(attribute.item.len())]
        .to_vec();

    let item_digest: [u8; 32] = Sha256::digest(&attribute.item).into();
    let digest_entry_context = byte_context(&fixture.mso, &item_digest, 12, 0);
    let mut encoded_digest_id = Vec::new();
    ciborium::ser::into_writer(
        &ciborium::value::Value::from(u64::from(attribute.digest_id)),
        &mut encoded_digest_id,
    )
    .expect("digest ID serializes");
    assert!(contains_marker(&digest_entry_context, &encoded_digest_id));

    let mso_digest: [u8; 32] = Sha256::digest(&fixture.mso).into();
    let revocation_id = eu_id_prover::ts13::ts13_mso_derived_revocation_id(&fixture.mso);
    assert_eq!(revocation_id.to_le_bytes(), mso_digest[..8]);
    let (id_lo, id_hi) = distinctive_revocation_bounds(revocation_id);
    let mut revocation_endpoints = Vec::with_capacity(16);
    revocation_endpoints.extend_from_slice(&id_lo.to_le_bytes());
    revocation_endpoints.extend_from_slice(&id_hi.to_le_bytes());
    let device_key_offset = fixture
        .mso
        .windows(fixture.device_pk.len())
        .position(|window| window == fixture.device_pk.as_slice())
        .expect("MSO contains the private device key");
    let mso_stable_fragment = fixture.mso
        [device_key_offset + 512..device_key_offset + 512 + PRIVATE_FRAGMENT_BYTES]
        .to_vec();

    assert!(contains_marker(&fixture.document, &attribute.item));
    assert!(contains_marker(&attribute.item, &randomizer_context));
    assert!(contains_marker(&fixture.mso, &digest_entry_context));

    let mut markers = vec![
        (
            "selected IssuerSignedItem".to_string(),
            attribute.item.clone(),
        ),
        (
            "selected item randomizer/digest-ID context".to_string(),
            randomizer_context,
        ),
        (
            "valueDigests digest-ID/item-digest context".to_string(),
            digest_entry_context,
        ),
        ("MSO SHA-256 digest".to_string(), mso_digest.to_vec()),
        (
            "derived revocation identifier".to_string(),
            revocation_id.to_le_bytes().to_vec(),
        ),
        (
            "revocation range endpoints".to_string(),
            revocation_endpoints,
        ),
        (
            "device ML-DSA rho".to_string(),
            fixture.device_pk[..32].to_vec(),
        ),
        (
            "device ML-DSA t1 fragment".to_string(),
            fixture.device_pk[32..32 + PRIVATE_FRAGMENT_BYTES].to_vec(),
        ),
        (
            "independent MSO stable fragment".to_string(),
            mso_stable_fragment,
        ),
    ];
    markers.extend(validity_markers(&fixture.mso));
    markers.extend(private_fragments(
        "issuer signature",
        &fixture.issuer_signature,
    ));
    markers.extend(private_fragments(
        "device signature",
        &fixture.device_signature,
    ));
    markers.extend(private_fragments(
        "revocation signature",
        revocation_signature,
    ));
    assert!(
        markers.iter().all(|(_, marker)| marker.len() >= 8),
        "private scan uses only high-entropy or composite markers"
    );
    markers
}

#[test]
fn ts13_public_input_unlinkability_a1_a2_b_uses_compiled_artifact() {
    let transcript_a1 = variable_length_session_transcript(b"a1-verifier-challenge");
    let transcript_a2 =
        variable_length_session_transcript(b"a2-verifier-challenge-with-a-different-length");
    let transcript_b =
        variable_length_session_transcript(b"b-verifier-challenge-with-another-fresh-length");
    let credential_a1 =
        mldsa_fixture::mldsa_ts13_unlinkable_credential_a_with_transcript(&transcript_a1);
    let credential_a2 =
        mldsa_fixture::mldsa_ts13_unlinkable_credential_a_with_transcript(&transcript_a2);
    let credential_b =
        mldsa_fixture::mldsa_ts13_unlinkable_credential_b_with_transcript(&transcript_b);

    assert_ne!(transcript_a1.len(), transcript_a2.len());
    assert_ne!("rp-a1".len(), "rp-a2-with-a-different-length".len());
    assert_eq!(credential_a1.mso, credential_a2.mso);
    assert_ne!(credential_a1.mso, credential_b.mso);
    assert_eq!(credential_a1.device_pk, credential_a2.device_pk);
    assert_ne!(credential_a1.device_pk, credential_b.device_pk);
    assert_ne!(
        credential_a1.device_sig_structure.len(),
        credential_a2.device_sig_structure.len()
    );

    let statement_a1 = unlinkable_identity_statement(
        "rp-a1",
        transcript_a1,
        &credential_a1.issuer_pk,
        &credential_a1.revocation_pk,
    );
    let statement_a2 = unlinkable_identity_statement(
        "rp-a2-with-a-different-length",
        transcript_a2,
        &credential_a2.issuer_pk,
        &credential_a2.revocation_pk,
    );
    let statement_b = unlinkable_identity_statement(
        "rp-b-with-a-third-length",
        transcript_b,
        &credential_b.issuer_pk,
        &credential_b.revocation_pk,
    );
    assert_eq!(
        normalized_fresh_context(statement_a1.clone()),
        normalized_fresh_context(statement_a2.clone())
    );
    assert_eq!(
        normalized_fresh_context(statement_a1.clone()),
        normalized_fresh_context(statement_b.clone())
    );

    let (witness_a1, revocation_signature_a1) = ts13_identity_witness(&credential_a1);
    let (witness_a2, revocation_signature_a2) = ts13_identity_witness(&credential_a2);
    let (witness_b, revocation_signature_b) = ts13_identity_witness(&credential_b);

    let mut unknown_artifact = statement_a1.clone();
    unknown_artifact.circuit_hash[0] ^= 1;
    assert!(matches!(
        prove_identity(
            ZkPublicStatement::Ts13DemoV1(unknown_artifact),
            witness_a1.clone(),
        ),
        Err(ZkError::UnsupportedCircuitHash)
    ));

    let proof_a1 = prove_identity(
        ZkPublicStatement::Ts13DemoV1(statement_a1.clone()),
        witness_a1,
    )
    .expect("A1 proves through the public compiled-artifact route");
    let proof_a2 = prove_identity(
        ZkPublicStatement::Ts13DemoV1(statement_a2.clone()),
        witness_a2,
    )
    .expect("A2 proves through the public compiled-artifact route");
    let proof_b = prove_identity(
        ZkPublicStatement::Ts13DemoV1(statement_b.clone()),
        witness_b,
    )
    .expect("B proves through the public compiled-artifact route");

    for (name, statement, proof) in [
        ("A1", &statement_a1, &proof_a1),
        ("A2", &statement_a2, &proof_a2),
        ("B", &statement_b, &proof_b),
    ] {
        assert!(
            verify_identity(
                ZkPublicStatement::Ts13DemoV1(statement.clone()),
                proof.clone(),
            )
            .unwrap_or_else(|error| panic!("{name} verification failed: {error}"))
            .ok
        );
    }
    let product_statement = ZkPublicStatement::ProductV1(ProductPublicStatementV1 {
        spec_id: "stwo-euid-pid-v1".to_string(),
        version: 1,
        doctype: PID_DOCTYPE.to_string(),
        namespace: PID_NAMESPACE.to_string(),
        issuer_key: IssuerKey::MlDsa {
            pk_hash: Sha256::digest(&credential_a1.issuer_pk).to_vec(),
        },
        today_epoch_day: 20_819,
        nonce: vec![0x51; 32],
        predicate_mode: PredicateMode::Age,
        age_threshold_years: Some(18),
        accepted_numeric_countries: None,
        nat_mode: NatMode::Any,
    });
    assert!(
        verify_identity(product_statement, proof_a1.clone()).is_err(),
        "the exported Product V1 verifier must reject a valid TS13 Demo V4 proof"
    );

    let capacity = eu_id_prover::ts13_demo_artifact_constants::TS13_DEMO_PROOF_BODY_CAPACITY;
    let expected_len = TS13_V4_HEADER_BYTES + capacity as usize;
    for proof in [&proof_a1, &proof_a2, &proof_b] {
        assert_eq!(proof.len(), expected_len);
        assert_eq!(&proof[..8], b"EUIDTS13");
        assert_eq!(&proof[8..10], &4u16.to_le_bytes());
        assert_eq!(
            &proof[10..42],
            &eu_id_prover::ts13_demo_artifact_constants::TS13_DEMO_CIRCUIT_HASH
        );
        assert_eq!(&proof[42..46], &capacity.to_le_bytes());
    }
    assert_eq!(
        &proof_a1[..TS13_V4_HEADER_BYTES],
        &proof_a2[..TS13_V4_HEADER_BYTES]
    );
    assert_eq!(
        &proof_a1[..TS13_V4_HEADER_BYTES],
        &proof_b[..TS13_V4_HEADER_BYTES]
    );
    assert_eq!(v4_tree_zero_root(&proof_a1), v4_tree_zero_root(&proof_a2));
    assert_eq!(v4_tree_zero_root(&proof_a1), v4_tree_zero_root(&proof_b));

    for (name, statement, proof, fixture, revocation_signature) in [
        (
            "A1",
            &statement_a1,
            &proof_a1,
            &credential_a1,
            &revocation_signature_a1,
        ),
        (
            "A2",
            &statement_a2,
            &proof_a2,
            &credential_a2,
            &revocation_signature_a2,
        ),
        (
            "B",
            &statement_b,
            &proof_b,
            &credential_b,
            &revocation_signature_b,
        ),
    ] {
        let semantic = semantic_public_bytes(statement);
        let header = &proof[..TS13_V4_HEADER_BYTES];
        // Public-input unlinkability is the frozen claim. The transparent
        // STARK body is deliberately excluded: transcript zero knowledge
        // remains pending until proof-system masking is added.
        for (marker_name, marker) in
            private_identity_markers(fixture, statement, revocation_signature)
        {
            assert!(
                !contains_marker(&semantic, &marker),
                "{name} semantic public statement contains private {marker_name}"
            );
            assert!(
                !contains_marker(header, &marker),
                "{name} V4 header contains private {marker_name}"
            );
        }
    }

    let assert_relabel_rejected = |statement: Ts13DemoPublicStatementV1| {
        assert!(matches!(
            verify_identity(ZkPublicStatement::Ts13DemoV1(statement), proof_a1.clone()),
            Err(ZkError::ProofVerificationFailed)
        ));
    };
    let mut relabelled = statement_a1.clone();
    relabelled.zk_system_id.push_str("-other");
    assert_relabel_rejected(relabelled);
    let mut relabelled = statement_a1.clone();
    relabelled.timestamp_epoch_seconds += 1;
    assert_relabel_rejected(relabelled);
    let mut relabelled = statement_a1.clone();
    relabelled.session_transcript =
        eu_id_prover::mdoc::openid4vp_session_transcript(b"fresh-relabelled-session");
    assert_relabel_rejected(relabelled);
    let mut relabelled = statement_a1.clone();
    relabelled.trusted_issuer_public_key[0] ^= 1;
    assert_relabel_rejected(relabelled);
    let mut relabelled = statement_a1.clone();
    relabelled.revocation_public_key[0] ^= 1;
    assert_relabel_rejected(relabelled);
    let mut relabelled = statement_a1;
    relabelled.revocation_epoch += 1;
    assert_relabel_rejected(relabelled);
}

#[test]
fn ts13_exported_api_theorem_mutation_matrix_fails_closed() {
    let transcript =
        eu_id_prover::mdoc::openid4vp_session_transcript(b"ts13-exported-theorem-matrix");
    let fixture = mldsa_fixture::mldsa_ts13_unlinkable_credential_a_with_transcript(&transcript);
    let statement = unlinkable_identity_statement(
        "rp-local-ts13-theorem-matrix",
        transcript,
        &fixture.issuer_pk,
        &fixture.revocation_pk,
    );
    let id = eu_id_prover::ts13::ts13_mso_derived_revocation_id(&fixture.mso);
    let (id_lo, id_hi) = distinctive_revocation_bounds(id);
    let (_, revocation_signature) =
        mldsa_fixture::mldsa_revocation_fixture(id_lo, id_hi, TS13_DEMO_REVOCATION_EPOCH);
    let base_witness = Ts13DemoWitnessV1 {
        document: fixture.document.clone(),
        revocation_id_lo: id_lo,
        revocation_id_hi: id_hi,
        revocation_signature,
    };

    let control_proof = prove_identity(
        ZkPublicStatement::Ts13DemoV1(statement.clone()),
        ZkMdocWitness::Ts13DemoV1(base_witness.clone()),
    )
    .expect("the theorem-matrix control proves");
    assert!(
        verify_identity(
            ZkPublicStatement::Ts13DemoV1(statement.clone()),
            control_proof,
        )
        .expect("the theorem-matrix control verifies")
        .ok
    );

    let document_case = |document| Ts13DemoWitnessV1 {
        document,
        ..base_witness.clone()
    };
    let mut cases = Vec::new();

    cases.push((
        "issuer signature",
        document_case(mutate_document(&fixture.document, |document| {
            flip_middle_byte(&mut issuer_auth_mut(document)[3], "issuer signature");
        })),
    ));
    cases.push((
        "issuer protected header",
        document_case(mutate_document(&fixture.document, |document| {
            flip_middle_byte(&mut issuer_auth_mut(document)[0], "issuer protected header");
        })),
    ));
    cases.push((
        "issuer MSO payload",
        document_case(mutate_document(&fixture.document, |document| {
            flip_middle_byte(&mut issuer_auth_mut(document)[2], "issuer MSO payload");
        })),
    ));

    cases.push((
        "MSO docType",
        document_case(mutate_document(&fixture.document, |document| {
            mutate_mso_and_resign(document, |mso| {
                *text_map_value_mut(mso, "docType") =
                    Value::Text("eu.europa.ec.eudi.pid.2".to_string());
            });
        })),
    ));
    cases.push((
        "MSO digestAlgorithm",
        document_case(mutate_document(&fixture.document, |document| {
            mutate_mso_and_resign(document, |mso| {
                *text_map_value_mut(mso, "digestAlgorithm") = Value::Text("SHA-512".to_string());
            });
        })),
    ));
    cases.push((
        "MSO device-key region",
        document_case(mutate_document(&fixture.document, |document| {
            mutate_mso_and_resign(document, |mso| {
                let device_key_info = text_map_value_mut(mso, "deviceKeyInfo");
                let device_key = text_map_value_mut(device_key_info, "deviceKey");
                let Value::Map(entries) = device_key else {
                    panic!("MSO deviceKey is a COSE_Key map");
                };
                let public_key = entries
                    .iter_mut()
                    .find_map(|(label, value)| (label == &Value::from(-1i64)).then_some(value))
                    .expect("device COSE_Key contains the public-key label");
                flip_middle_byte(public_key, "MSO device public key");
            });
        })),
    ));

    cases.push((
        "selected item randomizer",
        document_case(mutate_document(&fixture.document, |document| {
            mutate_selected_item(document, |item| {
                flip_middle_byte(text_map_value_mut(item, "random"), "item randomizer");
            });
        })),
    ));
    cases.push((
        "selected item value",
        document_case(mutate_document(&fixture.document, |document| {
            mutate_selected_item(document, |item| {
                *text_map_value_mut(item, "elementValue") = Value::Bool(false);
            });
            update_selected_digest_and_resign(document);
        })),
    ));
    cases.push((
        "selected item digest context",
        document_case(mutate_document(&fixture.document, |document| {
            mutate_mso_and_resign(document, |mso| {
                let value_digests = text_map_value_mut(mso, "valueDigests");
                let namespace_digests = text_map_value_mut(value_digests, PID_NAMESPACE);
                let Value::Map(entries) = namespace_digests else {
                    panic!("PID valueDigests entry is a map");
                };
                let digest = entries
                    .iter_mut()
                    .find_map(|(digest_id, digest)| {
                        (digest_id == &Value::from(TS13_SELECTED_DIGEST_ID)).then_some(digest)
                    })
                    .expect("MSO contains the selected digest ID");
                flip_middle_byte(digest, "selected item digest");
            });
        })),
    ));

    cases.push((
        "device signature",
        document_case(mutate_document(&fixture.document, |document| {
            flip_middle_byte(&mut device_signature_mut(document)[3], "device signature");
        })),
    ));
    cases.push((
        "device protected header",
        document_case(mutate_document(&fixture.document, |document| {
            flip_middle_byte(
                &mut device_signature_mut(document)[0],
                "device protected header",
            );
        })),
    ));
    cases.push((
        "device payload",
        document_case(mutate_document(&fixture.document, |document| {
            flip_middle_byte(&mut device_signature_mut(document)[2], "device payload");
        })),
    ));

    let mut wrong_endpoints = base_witness.clone();
    wrong_endpoints.revocation_id_lo = wrong_endpoints
        .revocation_id_lo
        .checked_add(1)
        .expect("fixture lower endpoint can move inward");
    cases.push(("revocation endpoints", wrong_endpoints));
    let mut wrong_revocation_signature = base_witness.clone();
    let signature_index = wrong_revocation_signature.revocation_signature.len() / 2;
    wrong_revocation_signature.revocation_signature[signature_index] ^= 1;
    cases.push(("revocation signature", wrong_revocation_signature));

    cases.push((
        "fixed-shape short MSO",
        document_case(mutate_document(&fixture.document, |document| {
            mutate_mso_and_resign(document, |mso| {
                let value_digests = text_map_value_mut(mso, "valueDigests");
                let Value::Map(entries) = value_digests else {
                    panic!("MSO valueDigests is a map");
                };
                entries.retain(|(namespace, _)| {
                    namespace != &Value::Text("org.example.issuer.metadata".to_string())
                });
            });
        })),
    ));
    cases.push((
        "fixed-shape long MSO",
        document_case(mutate_document(&fixture.document, |document| {
            mutate_mso_and_resign(document, |mso| {
                let value_digests = text_map_value_mut(mso, "valueDigests");
                let Value::Map(entries) = value_digests else {
                    panic!("MSO valueDigests is a map");
                };
                entries.push((
                    Value::Text("org.example.extra".to_string()),
                    Value::Map(vec![(Value::from(0u64), Value::Bytes(vec![0x5c; 32]))]),
                ));
            });
        })),
    ));
    cases.push((
        "selected item trailing CBOR",
        document_case(mutate_document(&fixture.document, |document| {
            append_selected_item_trailing_cbor(document);
            update_selected_digest_and_resign(document);
        })),
    ));

    assert_eq!(cases.len(), 17);
    for (name, witness) in cases {
        let outcome = prove_identity(
            ZkPublicStatement::Ts13DemoV1(statement.clone()),
            ZkMdocWitness::Ts13DemoV1(witness),
        );
        eprintln!(
            "{name}: {}",
            match &outcome {
                Ok(proof) => format!("proof built ({} bytes)", proof.len()),
                Err(error) => format!("pre-proof rejection ({error:?})"),
            }
        );
        match outcome {
            Err(error) => assert!(
                matches!(
                    error,
                    ZkError::UnsupportedDemoCredentialShape
                        | ZkError::InvalidPrivateCredential
                        | ZkError::InvalidRevocationWitness
                        | ZkError::ProofGenerationFailed
                ),
                "{name} returned an imprecise pre-proof error: {error:?}"
            ),
            Ok(proof) => {
                match verify_identity(ZkPublicStatement::Ts13DemoV1(statement.clone()), proof) {
                    Ok(result) => assert!(!result.ok, "{name} produced a verifying proof"),
                    Err(error) => assert!(
                        matches!(
                            error,
                            ZkError::ProofContextMismatch | ZkError::ProofVerificationFailed
                        ),
                        "{name} returned an unexpected verification error: {error:?}"
                    ),
                }
            }
        }
    }
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

    let compiled_statement = ZkPublicStatement::Ts13DemoV1(unlinkable_identity_statement(
        "rp-local-ts13-legacy-regression",
        request.session_transcript.clone(),
        &fixture.issuer_pk,
        &fixture.revocation_pk,
    ));
    assert!(matches!(
        verify_identity(compiled_statement.clone(), document.proof.clone()),
        Err(ZkError::MalformedProofEnvelope)
    ));
    let mut legacy_v2: Ts13ProofEnvelopeForTest =
        bincode::deserialize(&document.proof).expect("full legacy V3 envelope decodes");
    legacy_v2.envelope_format = 2;
    let legacy_v2 = bincode::serialize(&legacy_v2).expect("full legacy V2 envelope re-encodes");
    assert!(matches!(
        verify_identity(compiled_statement, legacy_v2),
        Err(ZkError::MalformedProofEnvelope)
    ));

    let identity_statement = identity_statement(request.clone(), &fixture.issuer_pk);
    let identity_witness = ZkMdocWitness::Ts13DemoV1(Ts13DemoWitnessV1 {
        document: fixture.document.clone(),
        revocation_id_lo: id_lo,
        revocation_id_hi: id_hi,
        revocation_signature,
    });
    assert!(matches!(
        prove_identity(identity_statement, identity_witness),
        Err(ZkError::UnsupportedCircuitHash)
    ));
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
