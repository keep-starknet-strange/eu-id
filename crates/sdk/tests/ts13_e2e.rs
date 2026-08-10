//! Test the TS13 identity and revocation proof.
//!
//! The fixture uses deterministic ML-DSA issuer, device, and revocation
//! signatures. It contains seven PID attributes. It is not a deployed
//! credential.

use bincode::Options;
use ciborium::value::Value;
use euid_zk_sdk::{IdentityStatement, IdentityWitness, ZkError, ZkMdocWitness, ZkPublicStatement};
use ml_dsa::signature::Signer;
use ml_dsa::{EncodedSignature, MlDsa65, SigningKey};
use sha2::{Digest, Sha256};
use std::io::Cursor;

#[allow(dead_code)]
#[path = "../../eu-id-prover/tests/support/mldsa_fixture.rs"]
mod mldsa_fixture;

/// The canonical TS13 flow through the public tagged API.
fn prove_identity(
    statement: IdentityStatement,
    witness: IdentityWitness,
) -> Result<Vec<u8>, ZkError> {
    euid_zk_sdk::prove_identity(
        ZkPublicStatement::Ts13DemoV1(statement),
        ZkMdocWitness::Ts13DemoV1(witness),
    )
}

fn verify_identity(statement: IdentityStatement, proof: Vec<u8>) -> Result<(), ZkError> {
    euid_zk_sdk::verify_identity(ZkPublicStatement::Ts13DemoV1(statement), proof).map(|_| ())
}

const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const PRIVATE_FRAGMENT_BYTES: usize = 64;
const DEVICE_T1_POLYNOMIAL_BYTES: usize =
    (stwo_mldsa::constants::PK_BYTES - 32) / stwo_mldsa::constants::K;
const ENVELOPE_HEADER_BYTES: usize = 46;
const TS13_DEMO_VERIFY_AT: i64 = 1_798_761_600;
const TS13_DEMO_REVOCATION_EPOCH: u32 = 17;
const TS13_SELECTED_DIGEST_ID: u64 = 17;
const DEMO_ISSUER_SEED: [u8; 32] = [0x5a; 32];

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
) -> IdentityStatement {
    IdentityStatement {
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

fn normalized_fresh_context(statement: IdentityStatement) -> IdentityStatement {
    let IdentityStatement {
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
    IdentityStatement {
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

fn semantic_public_bytes(statement: &IdentityStatement) -> Vec<u8> {
    let IdentityStatement {
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

fn envelope_tree_zero_root(envelope: &[u8]) -> Vec<u8> {
    let mut cursor = Cursor::new(&envelope[ENVELOPE_HEADER_BYTES..]);
    let proof: eu_id_prover::MdocProof = bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_little_endian()
        .allow_trailing_bytes()
        .deserialize_from(&mut cursor)
        .expect("valid canonical proof prefix decodes");
    bincode::serialize(
        proof
            .stark_proof
            .commitments
            .first()
            .expect("TS13 proof has tree-zero commitment"),
    )
    .expect("tree-zero root serializes")
}

fn ts13_identity_witness(
    fixture: &mldsa_fixture::MldsaIdentityFixture,
) -> (IdentityWitness, Vec<u8>) {
    let id = eu_id_prover::ts13::ts13_mso_derived_revocation_id(&fixture.mso);
    let (id_lo, id_hi) = distinctive_revocation_bounds(id);
    let (_, revocation_signature) =
        mldsa_fixture::mldsa_revocation_fixture(id_lo, id_hi, TS13_DEMO_REVOCATION_EPOCH);
    (
        IdentityWitness {
            document: fixture.document.clone(),
            revocation_id_lo: id_lo,
            revocation_id_hi: id_hi,
            revocation_signature: revocation_signature.clone(),
        },
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
    fixture: &mldsa_fixture::MldsaIdentityFixture,
    statement: &IdentityStatement,
    revocation_signature: &[u8],
) -> Vec<(String, Vec<u8>)> {
    let request = eu_id_prover::MdocPidRequest::age_over_18(statement.session_transcript.clone());
    let extracted = eu_id_prover::mdoc::extract_pid_mdoc(&fixture.document, &request)
        .expect("unlinkability fixture extracts");
    let attribute = &extracted.attribute;

    let Value::Tag(24, encoded_item) = decode_cbor(&attribute.item, "selected item") else {
        panic!("selected item has CBOR tag 24");
    };
    let Value::Bytes(encoded_item) = *encoded_item else {
        panic!("selected item tag contains a byte string");
    };
    let Value::Map(item_fields) = decode_cbor(&encoded_item, "selected item fields") else {
        panic!("selected item contains a CBOR map");
    };
    let randomizer = item_fields
        .iter()
        .find_map(|(key, value)| (key == &Value::Text("random".to_string())).then_some(value))
        .expect("selected item has random");
    let Value::Bytes(randomizer) = randomizer else {
        panic!("selected item random is a byte string");
    };
    let randomizer_context = byte_context(&attribute.item, randomizer, 12, 12);

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
            "selected item randomizer context".to_string(),
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
            "independent MSO stable fragment".to_string(),
            mso_stable_fragment,
        ),
    ];
    markers.extend((0..stwo_mldsa::constants::K).map(|polynomial| {
        let start = 32 + polynomial * DEVICE_T1_POLYNOMIAL_BYTES;
        (
            format!("device ML-DSA t1 polynomial {polynomial} fragment"),
            fixture.device_pk[start..start + PRIVATE_FRAGMENT_BYTES].to_vec(),
        )
    }));
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
    let credential_a1 = mldsa_fixture::mldsa_ts13_credential_a_with_transcript(&transcript_a1);
    let credential_a2 = mldsa_fixture::mldsa_ts13_credential_a_with_transcript(&transcript_a2);
    let credential_b = mldsa_fixture::mldsa_ts13_credential_b_with_transcript(&transcript_b);

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
        prove_identity(unknown_artifact, witness_a1.clone()),
        Err(ZkError::UnsupportedCircuitHash)
    ));

    let proof_a1 = prove_identity(statement_a1.clone(), witness_a1)
        .expect("A1 proves through the public compiled-artifact route");
    let proof_a2 = prove_identity(statement_a2.clone(), witness_a2)
        .expect("A2 proves through the public compiled-artifact route");
    let proof_b = prove_identity(statement_b.clone(), witness_b)
        .expect("B proves through the public compiled-artifact route");

    for (name, statement, proof) in [
        ("A1", &statement_a1, &proof_a1),
        ("A2", &statement_a2, &proof_a2),
        ("B", &statement_b, &proof_b),
    ] {
        verify_identity(statement.clone(), proof.clone())
            .unwrap_or_else(|error| panic!("{name} verification failed: {error}"));
    }

    let capacity = eu_id_prover::ts13_demo_artifact_constants::TS13_DEMO_PROOF_BODY_CAPACITY;
    let expected_len = ENVELOPE_HEADER_BYTES + capacity as usize;
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
        &proof_a1[..ENVELOPE_HEADER_BYTES],
        &proof_a2[..ENVELOPE_HEADER_BYTES]
    );
    assert_eq!(
        &proof_a1[..ENVELOPE_HEADER_BYTES],
        &proof_b[..ENVELOPE_HEADER_BYTES]
    );
    assert_eq!(
        envelope_tree_zero_root(&proof_a1),
        envelope_tree_zero_root(&proof_a2)
    );
    assert_eq!(
        envelope_tree_zero_root(&proof_a1),
        envelope_tree_zero_root(&proof_b)
    );

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
        let header = &proof[..ENVELOPE_HEADER_BYTES];
        // Check the public statement and the fixed envelope header. Do not inspect
        // the proof-system body.
        for (marker_name, marker) in
            private_identity_markers(fixture, statement, revocation_signature)
        {
            assert!(
                !contains_marker(&semantic, &marker),
                "{name} semantic public statement contains private {marker_name}"
            );
            assert!(
                !contains_marker(header, &marker),
                "{name} envelope header contains private {marker_name}"
            );
        }
    }

    let assert_relabel_rejected = |statement: IdentityStatement| {
        assert!(matches!(
            verify_identity(statement, proof_a1.clone()),
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
fn ts13_exported_prover_rejects_invalid_witness_matrix() {
    let transcript =
        eu_id_prover::mdoc::openid4vp_session_transcript(b"ts13-exported-invalid-witness-matrix");
    let fixture = mldsa_fixture::mldsa_ts13_credential_a_with_transcript(&transcript);
    let statement = unlinkable_identity_statement(
        "rp-local-ts13-invalid-witness-matrix",
        transcript,
        &fixture.issuer_pk,
        &fixture.revocation_pk,
    );
    let id = eu_id_prover::ts13::ts13_mso_derived_revocation_id(&fixture.mso);
    let (id_lo, id_hi) = distinctive_revocation_bounds(id);
    let (_, revocation_signature) =
        mldsa_fixture::mldsa_revocation_fixture(id_lo, id_hi, TS13_DEMO_REVOCATION_EPOCH);
    let base_witness = IdentityWitness {
        document: fixture.document.clone(),
        revocation_id_lo: id_lo,
        revocation_id_hi: id_hi,
        revocation_signature,
    };

    let control_proof = prove_identity(statement.clone(), base_witness.clone())
        .expect("the invalid-witness matrix control proves");
    verify_identity(statement.clone(), control_proof)
        .expect("the invalid-witness matrix control verifies");

    let document_case = |document| IdentityWitness {
        document,
        ..base_witness.clone()
    };
    let mut cases = Vec::new();

    cases.push((
        "issuer signature",
        document_case(mutate_document(&fixture.document, |document| {
            flip_middle_byte(&mut issuer_auth_mut(document)[3], "issuer signature");
        })),
        ZkError::InvalidPrivateCredential,
    ));
    cases.push((
        "issuer protected header",
        document_case(mutate_document(&fixture.document, |document| {
            flip_middle_byte(&mut issuer_auth_mut(document)[0], "issuer protected header");
        })),
        ZkError::InvalidPrivateCredential,
    ));
    cases.push((
        "issuer MSO payload",
        document_case(mutate_document(&fixture.document, |document| {
            flip_middle_byte(&mut issuer_auth_mut(document)[2], "issuer MSO payload");
        })),
        ZkError::InvalidPrivateCredential,
    ));

    cases.push((
        "MSO docType",
        document_case(mutate_document(&fixture.document, |document| {
            mutate_mso_and_resign(document, |mso| {
                *text_map_value_mut(mso, "docType") =
                    Value::Text("eu.europa.ec.eudi.pid.2".to_string());
            });
        })),
        ZkError::InvalidPrivateCredential,
    ));
    cases.push((
        "MSO digestAlgorithm",
        document_case(mutate_document(&fixture.document, |document| {
            mutate_mso_and_resign(document, |mso| {
                *text_map_value_mut(mso, "digestAlgorithm") = Value::Text("SHA-512".to_string());
            });
        })),
        ZkError::InvalidPrivateCredential,
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
        ZkError::InvalidPrivateCredential,
    ));

    cases.push((
        "selected item randomizer",
        document_case(mutate_document(&fixture.document, |document| {
            mutate_selected_item(document, |item| {
                flip_middle_byte(text_map_value_mut(item, "random"), "item randomizer");
            });
        })),
        ZkError::InvalidPrivateCredential,
    ));
    cases.push((
        "selected item value",
        document_case(mutate_document(&fixture.document, |document| {
            mutate_selected_item(document, |item| {
                *text_map_value_mut(item, "elementValue") = Value::Bool(false);
            });
            update_selected_digest_and_resign(document);
        })),
        ZkError::InvalidPrivateCredential,
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
        ZkError::InvalidPrivateCredential,
    ));

    cases.push((
        "device signature",
        document_case(mutate_document(&fixture.document, |document| {
            flip_middle_byte(&mut device_signature_mut(document)[3], "device signature");
        })),
        ZkError::InvalidPrivateCredential,
    ));
    cases.push((
        "device protected header",
        document_case(mutate_document(&fixture.document, |document| {
            flip_middle_byte(
                &mut device_signature_mut(document)[0],
                "device protected header",
            );
        })),
        ZkError::InvalidPrivateCredential,
    ));
    cases.push((
        "device payload",
        document_case(mutate_document(&fixture.document, |document| {
            flip_middle_byte(&mut device_signature_mut(document)[2], "device payload");
        })),
        ZkError::InvalidPrivateCredential,
    ));

    let mut wrong_endpoints = base_witness.clone();
    wrong_endpoints.revocation_id_lo = wrong_endpoints
        .revocation_id_lo
        .checked_add(1)
        .expect("fixture lower endpoint can move inward");
    cases.push((
        "revocation endpoints",
        wrong_endpoints,
        ZkError::ProofGenerationFailed,
    ));
    let mut wrong_revocation_signature = base_witness.clone();
    let signature_index = wrong_revocation_signature.revocation_signature.len() / 2;
    wrong_revocation_signature.revocation_signature[signature_index] ^= 1;
    cases.push((
        "revocation signature",
        wrong_revocation_signature,
        ZkError::ProofGenerationFailed,
    ));

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
        ZkError::UnsupportedDemoCredentialShape,
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
        ZkError::UnsupportedDemoCredentialShape,
    ));
    cases.push((
        "selected item trailing CBOR",
        document_case(mutate_document(&fixture.document, |document| {
            append_selected_item_trailing_cbor(document);
            update_selected_digest_and_resign(document);
        })),
        ZkError::InvalidPrivateCredential,
    ));

    assert_eq!(cases.len(), 17);
    for (name, witness, expected) in cases {
        let error = match prove_identity(statement.clone(), witness) {
            Err(error) => error,
            Ok(_) => panic!("{name} built a proof instead of rejecting the invalid witness"),
        };
        assert_eq!(error, expected, "{name} returned the wrong host error");
    }
}
