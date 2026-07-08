use ecdsa::signature::{hazmat::PrehashSigner, Signer};
use p256::ecdsa::{Signature as P256Signature, SigningKey};
use p256::pkcs8::DecodePrivateKey;
use sha2::{Digest as _, Sha256};
use std::time::Instant;

use ciborium::value::Value;
use eu_id_prover::mdoc::{
    demo_mdoc_sizing_waste, device_authentication_bytes, device_authentication_sig_structure_hash,
    extract_pid_mdoc, mdoc_production_pcs_config, mdoc_proof_byte_breakdown,
    openid4vp_session_transcript, prove_mdoc_circuit, verify_mdoc_circuit,
    verify_mdoc_circuit_with_pcs_config, verify_mdoc_circuit_with_preprocessed_root,
    MdocBirthDateBinding, MdocCircuitStatement, MdocDeviceAuthenticationProfile,
    MdocDisclosureMode, MdocError, MdocNationalityBinding, MdocPidRequest, MdocPublicStatement,
    MdocRequestedAttribute, MdocRevocationPublicInputs, MdocRevocationRangeWitness,
};
use eu_id_prover::ts13::{
    ts13_default_circuit_hash, ts13_default_preprocessed_root, ts13_mso_derived_revocation_id,
    ts13_revocation_message_hash, Ts13MdocProofArtifact, Ts13MdocProofArtifactError,
    Ts13RevocationStatement, Ts13RevocationWitness,
};
use eu_id_prover::{Date, Policy};
use stwo_p256::types::{AffinePoint, Signature, U256};

const DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const BIRTH_DATE: &str = "birth_date";
const NATIONALITY: &str = "nationality";
const PROTECTED_ES256: &[u8] = &[0xA1, 0x01, 0x26];
const PHASE_0B_REFACTOR_THRESHOLD_CELLS: u64 = 1_000_000;
const X5CHAIN_LABEL: i128 = 33;
const CBOR_TAG_ENCODED_CBOR: u64 = 24;
const CBOR_TAG_FULL_DATE: u64 = 1004;
const LONGFELLOW_MDL_DOCTYPE: &str = "org.iso.18013.5.1.mDL";
const LONGFELLOW_MDL_NAMESPACE: &str = "org.iso.18013.5.1";
const LONGFELLOW_EUAV_DOCTYPE: &str = "eu.europa.ec.av.1";
const LONGFELLOW_EUAV_NAMESPACE: &str = "eu.europa.ec.av.1";
const MIN_SALT_LEN: usize = 16;
const REAL_VECTOR_BIRTH_DATE_OFFSET: usize = 69;
const DER_SEQUENCE: u8 = 0x30;
const DER_LONG_FORM: u8 = 0x80;
const DER_LEN_MASK: u8 = 0x7F;

struct MdocFixture {
    doc: Vec<u8>,
    mso: Vec<u8>,
    issuer_sig_structure: Vec<u8>,
    device_sig_structure: Vec<u8>,
    birth_date_item: Vec<u8>,
    nationality_item: Vec<u8>,
    issuer_key: AffinePoint,
    device_key: AffinePoint,
    issuer_signature: Signature,
    device_signature: Signature,
}

#[derive(Clone)]
struct ExtraItem {
    digest_id: u64,
    element: String,
    value: Value,
    random: Vec<u8>,
}

#[derive(Clone)]
struct FixtureOptions {
    birth_item_digest_id: u64,
    nationality_item_digest_id: u64,
    birth_mso_digest_id: u64,
    nationality_mso_digest_id: u64,
    birth_digest_override: Option<[u8; 32]>,
    birth_random: Vec<u8>,
    nationality_random: Vec<u8>,
    extra_items: Vec<ExtraItem>,
    tag24_bstr: bool,
    canonical_item_order: bool,
    value_last: bool,
    protected: Vec<u8>,
    issuer_unprotected: Option<Value>,
    device_unprotected: Value,
    extra_device_key_field: bool,
    doc_doctype: String,
    namespace: String,
    mso_version: String,
    mso_doctype: String,
    validity_info: Option<Value>,
}

impl Default for FixtureOptions {
    fn default() -> Self {
        Self {
            birth_item_digest_id: 7,
            nationality_item_digest_id: 9,
            birth_mso_digest_id: 7,
            nationality_mso_digest_id: 9,
            birth_digest_override: None,
            birth_random: vec![7; 16],
            nationality_random: vec![9; 16],
            extra_items: Vec::new(),
            tag24_bstr: true,
            canonical_item_order: true,
            value_last: false,
            protected: PROTECTED_ES256.to_vec(),
            issuer_unprotected: None,
            device_unprotected: map(Vec::new()),
            extra_device_key_field: false,
            doc_doctype: DOCTYPE.to_string(),
            namespace: NAMESPACE.to_string(),
            mso_version: "2.0".to_string(),
            mso_doctype: DOCTYPE.to_string(),
            validity_info: Some(validity_info(
                "2026-01-01T00:00:00Z",
                "2026-01-01T00:00:00Z",
                "2030-01-01T00:00:00Z",
            )),
        }
    }
}

fn cbor(value: Value) -> Vec<u8> {
    let mut out = Vec::new();
    ciborium::ser::into_writer(&value, &mut out).expect("fixture cbor serializes");
    out
}

fn map(entries: Vec<(Value, Value)>) -> Value {
    Value::Map(entries)
}

fn cose_key(signing_key: &SigningKey) -> (Value, AffinePoint) {
    let encoded = signing_key.verifying_key().to_encoded_point(false);
    let x: [u8; 32] = encoded.x().expect("x")[..].try_into().expect("x len");
    let y: [u8; 32] = encoded.y().expect("y")[..].try_into().expect("y len");
    (
        map(vec![
            (Value::from(1), Value::from(2)),  // kty: EC2
            (Value::from(3), Value::from(-7)), // alg: ES256
            (Value::from(-1), Value::from(1)), // crv: P-256
            (Value::from(-2), Value::Bytes(x.to_vec())),
            (Value::from(-3), Value::Bytes(y.to_vec())),
        ]),
        AffinePoint {
            x: U256(x),
            y: U256(y),
        },
    )
}

fn add_extra_cose_key_field(key: &mut Value) {
    let Value::Map(entries) = key else {
        panic!("fixture COSE_Key is a map");
    };
    entries.push((Value::from(99), Value::from(0)));
}

fn signature(sig: &P256Signature) -> Signature {
    let r: [u8; 32] = sig.r().to_bytes().into();
    let s: [u8; 32] = sig.s().to_bytes().into();
    Signature {
        r: U256(r),
        s: U256(s),
    }
}

fn compact_signature(sig: &P256Signature) -> Vec<u8> {
    let mut out = Vec::with_capacity(64);
    out.extend_from_slice(&sig.r().to_bytes());
    out.extend_from_slice(&sig.s().to_bytes());
    out
}

fn real_vector_document(session_transcript: &[u8]) -> (Vec<u8>, Vec<u8>) {
    let issuer_signed = include_bytes!("vectors/pid_pymdoc_v1/issuer_signed.cbor");
    let issuer_signed_value: Value =
        ciborium::de::from_reader(&issuer_signed[..]).expect("real issuerSigned decodes");
    assert_real_vector_preconditions(&issuer_signed_value);

    let device_key =
        SigningKey::from_pkcs8_pem(include_str!("vectors/pid_pymdoc_v1/device_key.pem"))
            .expect("real vector device key decodes");
    let device_auth_payload =
        device_authentication_bytes(session_transcript, DOCTYPE).expect("device auth bytes");
    let (device_signature, _, _) = cose_sign1(
        &device_key,
        PROTECTED_ES256,
        map(Vec::new()),
        &device_auth_payload,
    );
    let device_signed = map(vec![(
        "deviceAuth".into(),
        map(vec![("deviceSignature".into(), device_signature)]),
    )]);

    let mut document = Vec::new();
    document.push(0xA3);
    document.extend(cbor("docType".into()));
    document.extend(cbor(DOCTYPE.into()));
    document.extend(cbor("issuerSigned".into()));
    document.extend_from_slice(issuer_signed);
    document.extend(cbor("deviceSigned".into()));
    document.extend(cbor(device_signed));

    let trusted_root =
        split_concatenated_der(include_bytes!("vectors/pid_pymdoc_v1/issuer_chain.der"))
            .last()
            .expect("real vector issuer chain has a root")
            .clone();

    (document, trusted_root)
}

struct LongfellowVector {
    name: &'static str,
    mdoc: &'static [u8],
    transcript: &'static [u8],
    issuer_pk_json: &'static str,
    now: &'static str,
    doctype: &'static str,
    namespace: &'static str,
}

fn longfellow_mdl3() -> LongfellowVector {
    LongfellowVector {
        name: "longfellow_mdl3",
        mdoc: include_bytes!("vectors/longfellow_mdl3/mdoc.cbor"),
        transcript: include_bytes!("vectors/longfellow_mdl3/transcript.bin"),
        issuer_pk_json: include_str!("vectors/longfellow_mdl3/issuer_pk.json"),
        now: include_str!("vectors/longfellow_mdl3/now.txt"),
        doctype: LONGFELLOW_MDL_DOCTYPE,
        namespace: LONGFELLOW_MDL_NAMESPACE,
    }
}

fn longfellow_euav11() -> LongfellowVector {
    LongfellowVector {
        name: "longfellow_euav11",
        mdoc: include_bytes!("vectors/longfellow_euav11/mdoc.cbor"),
        transcript: include_bytes!("vectors/longfellow_euav11/transcript.bin"),
        issuer_pk_json: include_str!("vectors/longfellow_euav11/issuer_pk.json"),
        now: include_str!("vectors/longfellow_euav11/now.txt"),
        doctype: LONGFELLOW_EUAV_DOCTYPE,
        namespace: LONGFELLOW_EUAV_NAMESPACE,
    }
}

fn longfellow_request(
    vector: &LongfellowVector,
    attributes: Vec<MdocRequestedAttribute>,
) -> MdocPidRequest {
    MdocPidRequest {
        doctype: vector.doctype.to_string(),
        namespace: vector.namespace.to_string(),
        attributes,
        birth_date_element: "birth_date".to_string(),
        nationality_element: "nationality".to_string(),
        session_transcript: vector.transcript.to_vec(),
        trusted_issuer_certificates: Vec::new(),
        trusted_issuer_public_keys: vec![longfellow_issuer_public_key(vector.issuer_pk_json)],
        device_authentication_profile: MdocDeviceAuthenticationProfile::LongfellowLegacy,
    }
}

fn longfellow_issuer_public_key(json: &str) -> AffinePoint {
    let value: serde_json::Value = serde_json::from_str(json).expect("issuer_pk.json parses");
    AffinePoint {
        x: U256(hex_32(value["x"].as_str().expect("issuer x hex"))),
        y: U256(hex_32(value["y"].as_str().expect("issuer y hex"))),
    }
}

fn hex_32(hex: &str) -> [u8; 32] {
    let hex = hex.strip_prefix("0x").unwrap_or(hex);
    assert_eq!(hex.len(), 64, "expected 32-byte hex string");
    let mut out = [0u8; 32];
    for (index, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&hex[index * 2..index * 2 + 2], 16).expect("hex byte parses");
    }
    out
}

fn policy_from_longfellow_now(vector: &LongfellowVector) -> Policy {
    let bytes = vector.now.trim().as_bytes();
    assert_eq!(bytes[4], b'-');
    assert_eq!(bytes[7], b'-');
    Policy {
        current_date: Date {
            year: std::str::from_utf8(&bytes[0..4])
                .expect("year utf8")
                .parse()
                .expect("year parses"),
            month: std::str::from_utf8(&bytes[5..7])
                .expect("month utf8")
                .parse()
                .expect("month parses"),
            day: std::str::from_utf8(&bytes[8..10])
                .expect("day utf8")
                .parse()
                .expect("day parses"),
        },
        min_age_years: 18,
        accepted_nationalities: Vec::new(),
        accepted_nationalities_alpha2: Vec::new(),
    }
}

fn split_concatenated_der(bytes: &[u8]) -> Vec<Vec<u8>> {
    let mut rest = bytes;
    let mut out = Vec::new();
    while !rest.is_empty() {
        let len = der_tlv_len(rest);
        out.push(rest[..len].to_vec());
        rest = &rest[len..];
    }
    out
}

fn der_tlv_len(bytes: &[u8]) -> usize {
    assert!(bytes.len() >= 2, "DER TLV needs tag and length");
    assert_eq!(bytes[0], DER_SEQUENCE, "certificate must be a DER sequence");
    let first_len = bytes[1];
    if first_len & DER_LONG_FORM == 0 {
        return 2 + usize::from(first_len);
    }
    let len_len = usize::from(first_len & DER_LEN_MASK);
    assert!(len_len > 0, "DER indefinite length is not allowed");
    assert!(bytes.len() >= 2 + len_len, "DER long length is truncated");
    let mut len = 0usize;
    for byte in &bytes[2..2 + len_len] {
        len = (len << 8) | usize::from(*byte);
    }
    2 + len_len + len
}

fn assert_real_vector_preconditions(issuer_signed: &Value) {
    let issuer_signed = value_map(issuer_signed, "issuerSigned");
    let issuer_auth = value_array(map_text(issuer_signed, "issuerAuth"), "issuerAuth");
    assert_eq!(
        value_bytes(&issuer_auth[0], "issuerAuth.protected"),
        PROTECTED_ES256
    );

    let unprotected = value_map(&issuer_auth[1], "issuerAuth.unprotected");
    assert!(
        map_int(unprotected, X5CHAIN_LABEL).is_some(),
        "issuerAuth unprotected header must carry x5chain label 33"
    );

    let payload = value_bytes(&issuer_auth[2], "issuerAuth.payload");
    let mso_value: Value = ciborium::de::from_reader(payload).expect("MSO payload decodes");
    let mso_bytes = match mso_value {
        Value::Tag(CBOR_TAG_ENCODED_CBOR, tagged) => {
            value_bytes(&tagged, "MobileSecurityObjectBytes").to_vec()
        }
        _ => payload.to_vec(),
    };
    let mso_value: Value = ciborium::de::from_reader(&mso_bytes[..]).expect("MSO decodes");
    let mso = value_map(&mso_value, "MobileSecurityObject");
    assert_eq!(
        value_text(map_text(mso, "digestAlgorithm"), "digestAlgorithm"),
        "SHA-256"
    );

    let namespaces = value_map(map_text(issuer_signed, "nameSpaces"), "nameSpaces");
    let items = value_array(map_text(namespaces, NAMESPACE), NAMESPACE);
    let mut saw_birth_date = false;
    let mut saw_nationality = false;
    for item in items {
        let item_bytes = match item {
            Value::Tag(CBOR_TAG_ENCODED_CBOR, tagged) => {
                value_bytes(tagged, "IssuerSignedItemBytes")
            }
            Value::Bytes(bytes) => bytes.as_slice(),
            _ => panic!("IssuerSignedItemBytes must be tag-24 or bstr"),
        };
        let item_value: Value =
            ciborium::de::from_reader(item_bytes).expect("IssuerSignedItem decodes");
        let item = value_map(&item_value, "IssuerSignedItem");
        assert!(
            value_bytes(map_text(item, "random"), "random").len() >= MIN_SALT_LEN,
            "IssuerSignedItem salt must be at least 16 bytes"
        );
        let element = value_text(map_text(item, "elementIdentifier"), "elementIdentifier");
        if element == BIRTH_DATE {
            saw_birth_date = true;
            let Value::Tag(CBOR_TAG_FULL_DATE, value) = map_text(item, "elementValue") else {
                panic!("birth_date must be tag-1004 full-date");
            };
            assert_eq!(value_text(value, "birth_date"), "1985-05-05");
            assert_eq!(
                item_bytes
                    .windows(b"1985-05-05".len())
                    .position(|window| window == b"1985-05-05"),
                Some(REAL_VECTOR_BIRTH_DATE_OFFSET)
            );
        }
        if element == NATIONALITY {
            saw_nationality = true;
            assert_eq!(
                value_text(map_text(item, "elementValue"), "nationality"),
                "DE"
            );
        }
    }
    assert!(saw_birth_date, "real vector must contain birth_date");
    assert!(saw_nationality, "real vector must contain nationality");
}

fn value_map<'a>(value: &'a Value, label: &str) -> &'a [(Value, Value)] {
    match value {
        Value::Map(entries) => entries,
        _ => panic!("{label} must be a map"),
    }
}

fn value_array<'a>(value: &'a Value, label: &str) -> &'a [Value] {
    match value {
        Value::Array(items) => items,
        _ => panic!("{label} must be an array"),
    }
}

fn value_bytes<'a>(value: &'a Value, label: &str) -> &'a [u8] {
    match value {
        Value::Bytes(bytes) => bytes,
        _ => panic!("{label} must be bytes"),
    }
}

fn value_text<'a>(value: &'a Value, label: &str) -> &'a str {
    match value {
        Value::Text(text) => text,
        _ => panic!("{label} must be text"),
    }
}

fn map_text<'a>(map: &'a [(Value, Value)], key: &str) -> &'a Value {
    map.iter()
        .find_map(|(candidate, value)| {
            (candidate == &Value::Text(key.to_string())).then_some(value)
        })
        .unwrap_or_else(|| panic!("missing map key {key}"))
}

fn map_int<'a>(map: &'a [(Value, Value)], key: i128) -> Option<&'a Value> {
    map.iter().find_map(|(candidate, value)| {
        let Value::Integer(candidate) = candidate else {
            return None;
        };
        (i128::from(*candidate) == key).then_some(value)
    })
}

fn der_tlv(tag: u8, value: Vec<u8>) -> Vec<u8> {
    let mut out = vec![tag];
    if value.len() < 128 {
        out.push(value.len() as u8);
    } else {
        let len_bytes = (value.len() as u64).to_be_bytes();
        let first = len_bytes
            .iter()
            .position(|byte| *byte != 0)
            .unwrap_or(len_bytes.len() - 1);
        out.push(0x80 | u8::try_from(len_bytes.len() - first).expect("DER length byte count"));
        out.extend_from_slice(&len_bytes[first..]);
    }
    out.extend(value);
    out
}

fn der_sequence(fields: Vec<Vec<u8>>) -> Vec<u8> {
    der_tlv(0x30, fields.concat())
}

fn der_integer_u64(value: u64) -> Vec<u8> {
    let bytes = value.to_be_bytes();
    let first = bytes
        .iter()
        .position(|byte| *byte != 0)
        .unwrap_or(bytes.len() - 1);
    let mut value_bytes = bytes[first..].to_vec();
    if value_bytes[0] & 0x80 != 0 {
        value_bytes.insert(0, 0);
    }
    der_tlv(0x02, value_bytes)
}

fn der_bit_string(bytes: &[u8]) -> Vec<u8> {
    let mut value = Vec::with_capacity(bytes.len() + 1);
    value.push(0);
    value.extend_from_slice(bytes);
    der_tlv(0x03, value)
}

fn ecdsa_with_sha256_algorithm_identifier() -> Vec<u8> {
    der_sequence(vec![der_tlv(
        0x06,
        vec![0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x04, 0x03, 0x02],
    )])
}

fn p256_subject_public_key_info(signing_key: &SigningKey) -> Vec<u8> {
    let point = signing_key.verifying_key().to_encoded_point(false);
    der_sequence(vec![
        der_sequence(vec![
            der_tlv(0x06, vec![0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x02, 0x01]),
            der_tlv(0x06, vec![0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x03, 0x01, 0x07]),
        ]),
        der_bit_string(point.as_bytes()),
    ])
}

fn self_signed_certificate_der(signing_key: &SigningKey) -> Vec<u8> {
    let signature_algorithm = ecdsa_with_sha256_algorithm_identifier();
    let tbs = der_sequence(vec![
        der_tlv(0xA0, der_integer_u64(2)),
        der_integer_u64(1),
        signature_algorithm.clone(),
        der_sequence(Vec::new()),
        der_sequence(vec![
            der_tlv(0x17, b"260101000000Z".to_vec()),
            der_tlv(0x17, b"300101000000Z".to_vec()),
        ]),
        der_sequence(Vec::new()),
        p256_subject_public_key_info(signing_key),
    ]);
    let sig: P256Signature = signing_key.sign(&tbs);
    der_sequence(vec![
        tbs,
        signature_algorithm,
        der_bit_string(sig.to_der().as_bytes()),
    ])
}

fn tdate(text: &str) -> Value {
    Value::Tag(0, Box::new(text.into()))
}

fn validity_info(signed: &str, valid_from: &str, valid_until: &str) -> Value {
    map(vec![
        ("signed".into(), tdate(signed)),
        ("validFrom".into(), tdate(valid_from)),
        ("validUntil".into(), tdate(valid_until)),
    ])
}

fn issuer_signed_item(
    digest_id: u64,
    element: &str,
    value: Value,
    random: Vec<u8>,
    tag24_bstr: bool,
    canonical_item_order: bool,
    value_last: bool,
) -> Vec<u8> {
    let entries = if canonical_item_order {
        vec![
            ("random".into(), Value::Bytes(random)),
            ("digestID".into(), Value::from(digest_id)),
            ("elementValue".into(), value),
            ("elementIdentifier".into(), element.into()),
        ]
    } else if value_last {
        vec![
            ("digestID".into(), Value::from(digest_id)),
            ("random".into(), Value::Bytes(random)),
            ("elementIdentifier".into(), element.into()),
            ("elementValue".into(), value),
        ]
    } else {
        vec![
            ("elementValue".into(), value),
            ("digestID".into(), Value::from(digest_id)),
            ("random".into(), Value::Bytes(random)),
            ("elementIdentifier".into(), element.into()),
        ]
    };
    let item = map(entries);
    if tag24_bstr {
        cbor(Value::Tag(24, Box::new(Value::Bytes(cbor(item)))))
    } else {
        cbor(Value::Tag(24, Box::new(item)))
    }
}

fn sig_structure(protected: &[u8], payload: &[u8]) -> Vec<u8> {
    cbor(Value::Array(vec![
        "Signature1".into(),
        Value::Bytes(protected.to_vec()),
        Value::Bytes(Vec::new()),
        Value::Bytes(payload.to_vec()),
    ]))
}

fn test_session_transcript() -> Vec<u8> {
    openid4vp_session_transcript(b"session-transcript-123")
}

fn cose_sign1(
    signing_key: &SigningKey,
    protected: &[u8],
    unprotected: Value,
    payload: &[u8],
) -> (Value, Vec<u8>, Signature) {
    let sig_structure = sig_structure(protected, payload);
    let sig: P256Signature = signing_key.sign(&sig_structure);
    (
        Value::Array(vec![
            Value::Bytes(protected.to_vec()),
            unprotected,
            Value::Bytes(payload.to_vec()),
            Value::Bytes(compact_signature(&sig)),
        ]),
        sig_structure,
        signature(&sig),
    )
}

fn valid_fixture(session_transcript: &[u8]) -> MdocFixture {
    fixture_with_values(session_transcript, "1990-07-15".into(), "DE".into(), None)
}

fn valid_fixture_with_birth_digest(
    session_transcript: &[u8],
    birth_digest_override: Option<[u8; 32]>,
) -> MdocFixture {
    let options = FixtureOptions {
        birth_digest_override,
        ..FixtureOptions::default()
    };
    fixture_with_options(
        session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        options,
    )
}

fn circuit_fixture(session_transcript: &[u8]) -> MdocFixture {
    fixture_with_values(
        session_transcript,
        Value::Bytes(vec![0x07, 0xC6, 7, 15]), // 1990-07-15
        Value::Bytes(276u16.to_be_bytes().to_vec()), // DE numeric
        None,
    )
}

fn ts13_revocation_key(seed: u8) -> (SigningKey, AffinePoint) {
    let signing_key = SigningKey::from_bytes((&[seed; 32]).into()).expect("revocation key");
    let (_, public_key) = cose_key(&signing_key);
    (signing_key, public_key)
}

fn ts13_revocation_witness_for_id(
    signing_key: &SigningKey,
    id: u64,
    id_lo: u64,
    id_hi: u64,
    epoch: u32,
) -> Ts13RevocationWitness {
    let message_hash = ts13_revocation_message_hash(id_lo, id_hi, epoch);
    let pair_signature: P256Signature = signing_key
        .sign_prehash(&message_hash)
        .expect("revocation prehash signs");
    Ts13RevocationWitness {
        id,
        id_lo,
        id_hi,
        epoch,
        signature: signature(&pair_signature),
    }
}

fn hex_bytes(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[test]
#[ignore = "release gate for TS13 revocation positive path"]
fn ts13_revocation_non_revoked_end_to_end() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("mdoc extracts for revocation");
    let id = ts13_mso_derived_revocation_id(&extracted.mso);
    let (signing_key, revocation_key) = ts13_revocation_key(23);
    let statement = Ts13RevocationStatement {
        revocation_public_key: revocation_key,
        epoch: 42,
    };
    let witness = ts13_revocation_witness_for_id(
        &signing_key,
        id,
        id.saturating_sub(1),
        id.saturating_add(1),
        statement.epoch,
    );

    statement.verify_witness(&extracted, &witness).unwrap();
}

#[test]
fn ts13_revocation_sentinel_pair_end_to_end() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("mdoc extracts for sentinel revocation");
    let id = ts13_mso_derived_revocation_id(&extracted.mso);
    assert_ne!(id, 0);
    assert_ne!(id, u64::MAX);
    let (signing_key, revocation_key) = ts13_revocation_key(24);
    let statement = Ts13RevocationStatement {
        revocation_public_key: revocation_key,
        epoch: 43,
    };
    let witness = ts13_revocation_witness_for_id(&signing_key, id, 0, u64::MAX, statement.epoch);

    statement.verify_witness(&extracted, &witness).unwrap();
}

#[test]
fn ts13_revocation_rejects_id_equal_lo() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("mdoc extracts for revocation");
    let id = ts13_mso_derived_revocation_id(&extracted.mso);
    let (signing_key, revocation_key) = ts13_revocation_key(25);
    let statement = Ts13RevocationStatement {
        revocation_public_key: revocation_key,
        epoch: 44,
    };
    let witness = ts13_revocation_witness_for_id(&signing_key, id, id, id + 1, statement.epoch);

    assert!(statement.verify_witness(&extracted, &witness).is_err());
}

#[test]
fn ts13_revocation_rejects_id_equal_hi() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("mdoc extracts for revocation");
    let id = ts13_mso_derived_revocation_id(&extracted.mso);
    let (signing_key, revocation_key) = ts13_revocation_key(26);
    let statement = Ts13RevocationStatement {
        revocation_public_key: revocation_key,
        epoch: 45,
    };
    let witness = ts13_revocation_witness_for_id(&signing_key, id, id - 1, id, statement.epoch);

    assert!(statement.verify_witness(&extracted, &witness).is_err());
}

#[test]
fn ts13_revocation_rejects_forged_pair_signature() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("mdoc extracts for revocation");
    let id = ts13_mso_derived_revocation_id(&extracted.mso);
    let (honest_key, revocation_key) = ts13_revocation_key(27);
    let (forger_key, _) = ts13_revocation_key(28);
    let statement = Ts13RevocationStatement {
        revocation_public_key: revocation_key,
        epoch: 46,
    };
    let honest = ts13_revocation_witness_for_id(&honest_key, id, id - 1, id + 1, statement.epoch);
    statement.verify_witness(&extracted, &honest).unwrap();
    let forged = ts13_revocation_witness_for_id(&forger_key, id, id - 1, id + 1, statement.epoch);

    assert!(statement.verify_witness(&extracted, &forged).is_err());
}

#[test]
fn ts13_revocation_rejects_stale_epoch() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("mdoc extracts for revocation");
    let id = ts13_mso_derived_revocation_id(&extracted.mso);
    let (signing_key, revocation_key) = ts13_revocation_key(29);
    let statement = Ts13RevocationStatement {
        revocation_public_key: revocation_key,
        epoch: 47,
    };
    let witness = ts13_revocation_witness_for_id(&signing_key, id, id - 1, id + 1, 46);

    assert!(statement.verify_witness(&extracted, &witness).is_err());
}

#[test]
fn ts13_revocation_rejects_missing_caller_binding() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("mdoc extracts for revocation");
    let id = ts13_mso_derived_revocation_id(&extracted.mso);
    let (signing_key, revocation_key) = ts13_revocation_key(30);
    let (_, wrong_revocation_key) = ts13_revocation_key(31);
    let statement = Ts13RevocationStatement {
        revocation_public_key: wrong_revocation_key,
        epoch: 48,
    };
    let witness = ts13_revocation_witness_for_id(&signing_key, id, id - 1, id + 1, 48);

    assert!(statement.verify_witness(&extracted, &witness).is_err());
    let missing_epoch_statement = Ts13RevocationStatement {
        revocation_public_key: revocation_key,
        epoch: 49,
    };
    assert!(missing_epoch_statement
        .verify_witness(&extracted, &witness)
        .is_err());
}

#[test]
fn ts13_revocation_artifact_binds_to_mdoc_mso() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("mdoc extracts for revocation artifact");
    let mdoc_statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("mdoc statement builds for revocation artifact");
    let id = ts13_mso_derived_revocation_id(&extracted.mso);
    let (signing_key, revocation_key) = ts13_revocation_key(32);
    let revocation_statement = Ts13RevocationStatement {
        revocation_public_key: revocation_key,
        epoch: 50,
    };
    let mdoc_statement = mdoc_statement.with_ts13_revocation((&revocation_statement).into());
    let witness = ts13_revocation_witness_for_id(
        &signing_key,
        id,
        id - 1,
        id + 1,
        revocation_statement.epoch,
    );
    let expected_preprocessed_root = ts13_default_preprocessed_root();
    let artifact = Ts13MdocProofArtifact {
        circuit_hash: ts13_default_circuit_hash(),
        preprocessed_root: expected_preprocessed_root,
        mdoc_proof: b"serialized mdoc proof".to_vec(),
        revocation_statement,
        revocation_witness: witness,
    };

    artifact
        .verify_revocation_binding(&extracted, expected_preprocessed_root)
        .unwrap();
    assert!(matches!(
        artifact.verify_mdoc_and_revocation(&extracted, &mdoc_statement),
        Err(Ts13MdocProofArtifactError::ProofDecode)
    ));

    let mut wrong_hash = artifact.clone();
    wrong_hash.circuit_hash = "00".repeat(32);
    assert!(matches!(
        wrong_hash.verify_revocation_binding(&extracted, expected_preprocessed_root),
        Err(Ts13MdocProofArtifactError::CircuitHash)
    ));

    let mut wrong_root = artifact.clone();
    wrong_root.preprocessed_root[0] ^= 1;
    assert!(matches!(
        wrong_root.verify_revocation_binding(&extracted, expected_preprocessed_root),
        Err(Ts13MdocProofArtifactError::PreprocessedRoot)
    ));

    let mut empty_proof = artifact.clone();
    empty_proof.mdoc_proof.clear();
    assert!(matches!(
        empty_proof.verify_revocation_binding(&extracted, expected_preprocessed_root),
        Err(Ts13MdocProofArtifactError::EmptyProof)
    ));

    let other_fixture = fixture_with_values(
        &test_session_transcript(),
        "1991-07-15".into(),
        "DE".into(),
        None,
    );
    let other_extracted = extract_pid_mdoc(&other_fixture.doc, &request(test_session_transcript()))
        .expect("other mdoc extracts for artifact mismatch");
    assert!(matches!(
        artifact.verify_revocation_binding(&other_extracted, expected_preprocessed_root),
        Err(Ts13MdocProofArtifactError::Revocation(
            eu_id_prover::ts13::Ts13RevocationError::DerivedIdMismatch
        ))
    ));
}

#[test]
fn ts13_revocation_artifact_rejects_statement_without_revocation_policy() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("mdoc extracts for revocation statement binding");
    let mdoc_statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("mdoc statement builds for revocation statement binding");
    let id = ts13_mso_derived_revocation_id(&extracted.mso);
    let (signing_key, revocation_key) = ts13_revocation_key(33);
    let revocation_statement = Ts13RevocationStatement {
        revocation_public_key: revocation_key,
        epoch: 51,
    };
    let witness = ts13_revocation_witness_for_id(
        &signing_key,
        id,
        id - 1,
        id + 1,
        revocation_statement.epoch,
    );
    let artifact = Ts13MdocProofArtifact {
        circuit_hash: ts13_default_circuit_hash(),
        preprocessed_root: ts13_default_preprocessed_root(),
        mdoc_proof: b"serialized mdoc proof".to_vec(),
        revocation_statement,
        revocation_witness: witness,
    };

    assert!(matches!(
        artifact.verify_mdoc_and_revocation(&extracted, &mdoc_statement),
        Err(Ts13MdocProofArtifactError::StatementRevocationMissing)
    ));
}

#[test]
fn ts13_revocation_artifact_rejects_statement_revocation_policy_drift() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("mdoc extracts for revocation statement drift");
    let mdoc_statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("mdoc statement builds for revocation statement drift");
    let id = ts13_mso_derived_revocation_id(&extracted.mso);
    let (signing_key, revocation_key) = ts13_revocation_key(34);
    let (_, wrong_revocation_key) = ts13_revocation_key(35);
    let revocation_statement = Ts13RevocationStatement {
        revocation_public_key: revocation_key,
        epoch: 52,
    };
    let mdoc_statement = mdoc_statement.with_ts13_revocation(MdocRevocationPublicInputs {
        revocation_public_key: wrong_revocation_key,
        epoch: revocation_statement.epoch,
    });
    let witness = ts13_revocation_witness_for_id(
        &signing_key,
        id,
        id - 1,
        id + 1,
        revocation_statement.epoch,
    );
    let artifact = Ts13MdocProofArtifact {
        circuit_hash: ts13_default_circuit_hash(),
        preprocessed_root: ts13_default_preprocessed_root(),
        mdoc_proof: b"serialized mdoc proof".to_vec(),
        revocation_statement,
        revocation_witness: witness,
    };

    assert!(matches!(
        artifact.verify_mdoc_and_revocation(&extracted, &mdoc_statement),
        Err(Ts13MdocProofArtifactError::StatementRevocationMismatch)
    ));
}

#[test]
#[ignore = "slow: proves TS13 revocation public policy is mixed into the STARK transcript"]
fn ts13_revocation_public_inputs_are_stark_bound() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("mdoc extracts for revocation transcript binding");
    let statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("mdoc statement builds for revocation transcript binding");
    let (_, revocation_key) = ts13_revocation_key(36);
    let (_, wrong_revocation_key) = ts13_revocation_key(37);
    let statement = statement.with_ts13_revocation(MdocRevocationPublicInputs {
        revocation_public_key: revocation_key,
        epoch: 53,
    });
    let proof = prove_mdoc_circuit(&extracted, &statement)
        .expect("mdoc proof builds with TS13 revocation public inputs");
    verify_mdoc_circuit(&proof, &statement)
        .expect("mdoc proof verifies with original TS13 revocation public inputs");

    let mut drifted = statement.clone();
    drifted.ts13_revocation = Some(MdocRevocationPublicInputs {
        revocation_public_key: wrong_revocation_key,
        epoch: 53,
    });
    assert!(
        verify_mdoc_circuit(&proof, &drifted).is_err(),
        "raw mdoc verification must bind revocation public key into the STARK transcript"
    );

    let mut stale_epoch = statement.clone();
    stale_epoch.ts13_revocation = Some(MdocRevocationPublicInputs {
        revocation_public_key: statement
            .ts13_revocation
            .as_ref()
            .expect("statement has revocation inputs")
            .revocation_public_key
            .clone(),
        epoch: 54,
    });
    assert!(
        verify_mdoc_circuit(&proof, &stale_epoch).is_err(),
        "raw mdoc verification must bind revocation epoch into the STARK transcript"
    );
}

#[test]
#[ignore = "slow: proves TS13 revocation range is constrained by the STARK"]
fn ts13_revocation_range_rejects_id_equal_lo_in_stark() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("mdoc extracts for revocation range");
    let id = ts13_mso_derived_revocation_id(&extracted.mso);
    let (_, revocation_key) = ts13_revocation_key(38);
    let statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("mdoc statement builds for revocation range")
        .with_ts13_revocation(MdocRevocationPublicInputs {
            revocation_public_key: revocation_key,
            epoch: 55,
        })
        .with_ts13_revocation_range(MdocRevocationRangeWitness {
            id,
            id_lo: id,
            id_hi: id + 1,
        });

    assert!(
        prove_mdoc_circuit(&extracted, &statement).is_err(),
        "id == id_lo must be rejected by the in-STARK revocation range constraint"
    );
}

#[test]
#[ignore = "slow: proves TS13 revocation id is derived from the MSO hash in the STARK"]
fn ts13_revocation_range_rejects_id_not_derived_from_mso_in_stark() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("mdoc extracts for revocation id binding");
    let derived_id = ts13_mso_derived_revocation_id(&extracted.mso);
    let wrong_id = if derived_id == 1 { 2 } else { derived_id ^ 1 };
    let (_, revocation_key) = ts13_revocation_key(40);
    let statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("mdoc statement builds for revocation id binding")
        .with_ts13_revocation(MdocRevocationPublicInputs {
            revocation_public_key: revocation_key,
            epoch: 57,
        })
        .with_ts13_revocation_range(MdocRevocationRangeWitness {
            id: wrong_id,
            id_lo: wrong_id - 1,
            id_hi: wrong_id + 1,
        });

    let proof = prove_mdoc_circuit(&extracted, &statement)
        .expect("wrong but in-range id can still produce a malformed proof candidate");
    assert!(
        verify_mdoc_circuit(&proof, &statement).is_err(),
        "revocation id must be bound to LE64(SHA-256(MSO bytes)[0..8]) in the STARK"
    );
}

#[test]
#[ignore = "slow: proves TS13 MSO SHA preimage is the issuerAuth signed payload"]
fn ts13_revocation_rejects_mso_sha_preimage_not_issuer_payload_in_stark() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let mut extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("mdoc extracts for MSO payload binding");
    let (_, revocation_key) = ts13_revocation_key(41);
    let statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("mdoc statement builds for MSO payload binding")
        .with_ts13_revocation(MdocRevocationPublicInputs {
            revocation_public_key: revocation_key,
            epoch: 58,
        });

    extracted.mso[0] ^= 1;
    let forged_id = ts13_mso_derived_revocation_id(&extracted.mso);
    let statement = statement.with_ts13_revocation_range(MdocRevocationRangeWitness {
        id: forged_id,
        id_lo: forged_id.saturating_sub(1),
        id_hi: forged_id.saturating_add(1),
    });

    let proof = prove_mdoc_circuit(&extracted, &statement)
        .expect("forged MSO preimage can still produce a malformed proof candidate");
    assert!(
        verify_mdoc_circuit(&proof, &statement).is_err(),
        "MSO SHA preimage must be byte-bound to the issuerAuth signed payload in the STARK"
    );
}

#[test]
#[ignore = "slow: proves TS13 revocation pair signature is verified in the STARK"]
fn ts13_revocation_pair_signature_verifies_in_stark() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("mdoc extracts for revocation pair signature");
    let id = ts13_mso_derived_revocation_id(&extracted.mso);
    let (signing_key, revocation_key) = ts13_revocation_key(42);
    let epoch = 59;
    let witness = ts13_revocation_witness_for_id(
        &signing_key,
        id,
        id.saturating_sub(1),
        id.saturating_add(1),
        epoch,
    );
    let statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("mdoc statement builds for revocation pair signature")
        .with_ts13_revocation(MdocRevocationPublicInputs {
            revocation_public_key: revocation_key,
            epoch,
        })
        .with_ts13_revocation_range(MdocRevocationRangeWitness {
            id: witness.id,
            id_lo: witness.id_lo,
            id_hi: witness.id_hi,
        })
        .with_ts13_revocation_signature(witness.signature.clone());

    let proof =
        prove_mdoc_circuit(&extracted, &statement).expect("revocation pair signature proof builds");
    verify_mdoc_circuit(&proof, &statement).expect("revocation pair signature verifies in STARK");
}

#[test]
#[ignore = "slow: rejects forged TS13 revocation pair signatures in the STARK"]
fn ts13_revocation_rejects_forged_pair_signature_in_stark() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("mdoc extracts for forged revocation pair signature");
    let id = ts13_mso_derived_revocation_id(&extracted.mso);
    let (_, revocation_key) = ts13_revocation_key(43);
    let (forger_key, _) = ts13_revocation_key(44);
    let epoch = 60;
    let forged = ts13_revocation_witness_for_id(
        &forger_key,
        id,
        id.saturating_sub(1),
        id.saturating_add(1),
        epoch,
    );
    let statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("mdoc statement builds for forged revocation pair signature")
        .with_ts13_revocation(MdocRevocationPublicInputs {
            revocation_public_key: revocation_key,
            epoch,
        })
        .with_ts13_revocation_range(MdocRevocationRangeWitness {
            id: forged.id,
            id_lo: forged.id_lo,
            id_hi: forged.id_hi,
        })
        .with_ts13_revocation_signature(forged.signature.clone());

    assert!(
        prove_mdoc_circuit(&extracted, &statement).is_err(),
        "forged revocation pair signatures must not produce a valid STARK proof"
    );
}

#[test]
fn ts13_public_statement_keeps_revocation_range_layout_without_private_values() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("mdoc extracts for public revocation range layout");
    let id = ts13_mso_derived_revocation_id(&extracted.mso);
    let (_, revocation_key) = ts13_revocation_key(39);
    let statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("mdoc statement builds for public revocation range layout")
        .with_ts13_revocation(MdocRevocationPublicInputs {
            revocation_public_key: revocation_key,
            epoch: 56,
        })
        .with_ts13_revocation_range(MdocRevocationRangeWitness {
            id,
            id_lo: id.saturating_sub(1),
            id_hi: id.saturating_add(1),
        });

    let public_statement = MdocPublicStatement::from_circuit(&statement);

    assert!(
        public_statement.ts13_revocation_range_enabled,
        "public verification must instantiate the private range gadget without exposing its witness"
    );
}

fn fixture_with_values(
    session_transcript: &[u8],
    birth_date_value: Value,
    nationality_value: Value,
    birth_digest_override: Option<[u8; 32]>,
) -> MdocFixture {
    let options = FixtureOptions {
        birth_digest_override,
        ..FixtureOptions::default()
    };
    fixture_with_options(
        session_transcript,
        birth_date_value,
        nationality_value,
        options,
    )
}

fn fixture_with_options(
    session_transcript: &[u8],
    birth_date_value: Value,
    nationality_value: Value,
    options: FixtureOptions,
) -> MdocFixture {
    let issuer_signing_key =
        SigningKey::from_bytes((&[7u8; 32]).into()).expect("issuer signing key");
    let device_signing_key =
        SigningKey::from_bytes((&[11u8; 32]).into()).expect("device signing key");
    let (issuer_cose_key, issuer_key) = cose_key(&issuer_signing_key);
    let (mut device_cose_key, device_key) = cose_key(&device_signing_key);
    if options.extra_device_key_field {
        add_extra_cose_key_field(&mut device_cose_key);
    }

    let birth_date_item = issuer_signed_item(
        options.birth_item_digest_id,
        BIRTH_DATE,
        birth_date_value,
        options.birth_random,
        options.tag24_bstr,
        options.canonical_item_order,
        options.value_last,
    );
    let nationality_item = issuer_signed_item(
        options.nationality_item_digest_id,
        NATIONALITY,
        nationality_value,
        options.nationality_random,
        options.tag24_bstr,
        options.canonical_item_order,
        options.value_last,
    );
    let extra_items: Vec<_> = options
        .extra_items
        .iter()
        .map(|item| {
            let bytes = issuer_signed_item(
                item.digest_id,
                &item.element,
                item.value.clone(),
                item.random.clone(),
                options.tag24_bstr,
                options.canonical_item_order,
                options.value_last,
            );
            let digest: [u8; 32] = Sha256::digest(&bytes).into();
            (item.digest_id, bytes, digest)
        })
        .collect();
    let mut birth_digest: [u8; 32] = Sha256::digest(&birth_date_item).into();
    if let Some(override_digest) = options.birth_digest_override {
        birth_digest = override_digest;
    }
    let nat_digest: [u8; 32] = Sha256::digest(&nationality_item).into();

    let mut value_digest_entries = vec![
        (
            Value::from(options.birth_mso_digest_id),
            Value::Bytes(birth_digest.to_vec()),
        ),
        (
            Value::from(options.nationality_mso_digest_id),
            Value::Bytes(nat_digest.to_vec()),
        ),
    ];
    value_digest_entries.extend(
        extra_items
            .iter()
            .map(|(digest_id, _, digest)| (Value::from(*digest_id), Value::Bytes(digest.to_vec()))),
    );

    let mut mso_entries = vec![
        ("version".into(), options.mso_version.into()),
        ("docType".into(), options.mso_doctype.into()),
        ("digestAlgorithm".into(), "SHA-256".into()),
        (
            "valueDigests".into(),
            map(vec![(
                options.namespace.clone().into(),
                map(value_digest_entries),
            )]),
        ),
        (
            "deviceKeyInfo".into(),
            map(vec![("deviceKey".into(), device_cose_key)]),
        ),
    ];
    if let Some(validity_info) = options.validity_info {
        mso_entries.push(("validityInfo".into(), validity_info));
    }
    let mso = cbor(map(mso_entries));

    let issuer_unprotected = options
        .issuer_unprotected
        .unwrap_or_else(|| map(vec![("issuerKey".into(), issuer_cose_key)]));
    let (issuer_auth, issuer_sig_structure, issuer_signature) = cose_sign1(
        &issuer_signing_key,
        &options.protected,
        issuer_unprotected,
        &mso,
    );
    let device_auth_payload = device_authentication_bytes(session_transcript, &options.doc_doctype)
        .expect("device auth bytes");
    let (device_signature_cose, device_sig_structure, device_signature) = cose_sign1(
        &device_signing_key,
        &options.protected,
        options.device_unprotected,
        &device_auth_payload,
    );

    let mut namespace_items = vec![
        Value::Bytes(birth_date_item.clone()),
        Value::Bytes(nationality_item.clone()),
    ];
    namespace_items.extend(
        extra_items
            .iter()
            .map(|(_, bytes, _)| Value::Bytes(bytes.clone())),
    );

    let doc = cbor(map(vec![
        ("docType".into(), options.doc_doctype.clone().into()),
        (
            "issuerSigned".into(),
            map(vec![
                (
                    "nameSpaces".into(),
                    map(vec![(
                        options.namespace.into(),
                        Value::Array(namespace_items),
                    )]),
                ),
                ("issuerAuth".into(), issuer_auth),
            ]),
        ),
        (
            "deviceSigned".into(),
            map(vec![(
                "deviceAuth".into(),
                map(vec![("deviceSignature".into(), device_signature_cose)]),
            )]),
        ),
    ]));

    MdocFixture {
        doc,
        mso,
        issuer_sig_structure,
        device_sig_structure,
        birth_date_item,
        nationality_item,
        issuer_key,
        device_key,
        issuer_signature,
        device_signature,
    }
}

fn request(session_transcript: Vec<u8>) -> MdocPidRequest {
    MdocPidRequest::eudi_pid(session_transcript)
}

fn policy_on(year: u32, month: u32, day: u32) -> Policy {
    Policy {
        current_date: Date { year, month, day },
        min_age_years: 18,
        accepted_nationalities: vec![276, 250],
        accepted_nationalities_alpha2: vec![*b"DE", *b"FR"],
    }
}

#[test]
fn device_authentication_bytes_are_tag24_wrapped_and_embed_session_transcript_array() {
    let transcript = openid4vp_session_transcript(b"handover-info");
    let payload = device_authentication_bytes(&transcript, DOCTYPE).expect("payload builds");

    let Value::Tag(24, tagged) =
        ciborium::de::from_reader::<Value, _>(&payload[..]).expect("payload decodes")
    else {
        panic!("DeviceAuthenticationBytes must be CBOR tag 24");
    };
    let Value::Bytes(device_auth_cbor) = *tagged else {
        panic!("DeviceAuthenticationBytes tag must wrap a bstr");
    };
    let Value::Array(device_auth) = ciborium::de::from_reader::<Value, _>(&device_auth_cbor[..])
        .expect("DeviceAuthentication decodes")
    else {
        panic!("DeviceAuthentication must be an array");
    };

    assert_eq!(device_auth.len(), 4);
    assert_eq!(
        device_auth[0],
        Value::Text("DeviceAuthentication".to_string())
    );
    assert!(
        matches!(device_auth[1], Value::Array(_)),
        "SessionTranscript must be embedded as a CBOR array data item, not opaque bytes"
    );
    assert_eq!(device_auth[2], Value::Text(DOCTYPE.to_string()));

    let Value::Bytes(device_namespaces_bytes) = &device_auth[3] else {
        panic!("DeviceNameSpacesBytes must be a bstr");
    };
    assert!(
        matches!(
            ciborium::de::from_reader::<Value, _>(&device_namespaces_bytes[..])
                .expect("DeviceNameSpacesBytes decodes"),
            Value::Tag(24, _)
        ),
        "DeviceNameSpacesBytes must carry tag-24 wrapped namespaces"
    );

    let Value::Array(transcript_array) = &device_auth[1] else {
        unreachable!("checked above");
    };
    assert_eq!(transcript_array.len(), 3);
    assert_eq!(transcript_array[0], Value::Null);
    assert_eq!(transcript_array[1], Value::Null);
    assert!(matches!(&transcript_array[2], Value::Array(handover) if handover.len() == 2));
}

#[test]
fn transcript_and_doctype_mutations_change_device_authentication_hash() {
    let transcript = openid4vp_session_transcript(b"handover-info");
    let other_transcript = openid4vp_session_transcript(b"other-handover-info");

    let expected =
        device_authentication_sig_structure_hash(&transcript, DOCTYPE).expect("hash builds");

    assert_ne!(
        expected,
        device_authentication_sig_structure_hash(&other_transcript, DOCTYPE)
            .expect("hash builds for other transcript"),
        "transcript mutation must change the detached-payload signature hash"
    );
    assert_ne!(
        expected,
        device_authentication_sig_structure_hash(&transcript, "wrong.doctype")
            .expect("hash builds for other docType"),
        "docType mutation must change the detached-payload signature hash"
    );
}

#[test]
fn extracts_pid_items_mso_device_key_and_signatures() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);

    let extracted =
        extract_pid_mdoc(&fixture.doc, &request(session_transcript)).expect("mdoc extracts");

    assert_eq!(extracted.doctype, DOCTYPE);
    assert_eq!(extracted.namespace, NAMESPACE);
    assert_eq!(extracted.birth_date, "1990-07-15");
    assert_eq!(extracted.nationalities, vec![276]);
    assert_eq!(extracted.signed_at, (2026, 1, 1));
    assert_eq!(extracted.valid_from, (2026, 1, 1));
    assert_eq!(extracted.valid_until, (2030, 1, 1));
    assert_eq!(extracted.digest_ids.get(BIRTH_DATE), Some(&7));
    assert_eq!(extracted.digest_ids.get(NATIONALITY), Some(&9));
    assert_eq!(extracted.birth_date_item, fixture.birth_date_item);
    assert_eq!(extracted.nationality_item, fixture.nationality_item);
    assert_eq!(extracted.mso, fixture.mso);
    assert_eq!(extracted.issuer_key, fixture.issuer_key);
    assert_eq!(extracted.device_key, fixture.device_key);
    assert_eq!(extracted.issuer_signature, fixture.issuer_signature);
    assert_eq!(extracted.device_signature, fixture.device_signature);
    assert_eq!(extracted.issuer_sig_structure, fixture.issuer_sig_structure);
    assert_eq!(extracted.device_sig_structure, fixture.device_sig_structure);
    assert_eq!(
        extracted.issuer_ecdsa_input.message_hash.0,
        <[u8; 32]>::from(Sha256::digest(&fixture.issuer_sig_structure))
    );
    assert_eq!(
        extracted.device_ecdsa_input.message_hash.0,
        <[u8; 32]>::from(Sha256::digest(&fixture.device_sig_structure))
    );
}

#[test]
fn phase0b_sizing_waste_stays_below_refactor_threshold() {
    let waste = demo_mdoc_sizing_waste().expect("mdoc sizing waste computes");
    let logs: Vec<_> = waste
        .sha
        .iter()
        .map(|row| (row.name, row.natural_log, row.shared_log, row.wasted_cells))
        .collect();

    assert_eq!(
        waste.p256_namespaced_identical_preprocessed_cells, 0,
        "mdoc/device currently namespaces only hinted-mul schedules; deterministic P256 tables should still dedupe"
    );
    assert!(
        waste.combined_wasted_cells() < PHASE_0B_REFACTOR_THRESHOLD_CELLS,
        "Phase 0b accepted-waste threshold exceeded: logs={logs:?}, sha_waste={}, p256_waste={}, combined={}",
        waste.sha_wasted_cells,
        waste.p256_namespaced_identical_preprocessed_cells,
        waste.combined_wasted_cells()
    );
}

#[test]
fn rejects_item_digest_mismatch() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture_with_birth_digest(&session_transcript, Some([0xAA; 32]));

    let err = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect_err("digest mismatch rejects");

    assert!(matches!(
        err,
        MdocError::ItemDigestMismatch {
            element,
            digest_id: 7
        } if element == BIRTH_DATE
    ));
}

#[test]
fn rejects_wrong_session_transcript() {
    let fixture = valid_fixture(&test_session_transcript());

    let err = extract_pid_mdoc(
        &fixture.doc,
        &request(openid4vp_session_transcript(b"session-transcript-456")),
    )
    .expect_err("wrong transcript rejects");

    assert!(matches!(err, MdocError::DeviceAuthPayloadMismatch));
}

#[test]
fn rejects_wrong_requested_doctype() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let mut request = request(session_transcript);
    request.doctype = "wrong.doctype".to_string();

    let err = extract_pid_mdoc(&fixture.doc, &request).expect_err("wrong doctype rejects");

    assert!(matches!(err, MdocError::DoctypeMismatch));
}

#[test]
fn rejects_non_profile_requested_namespace() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let mut request = request(session_transcript);
    request.namespace = "wrong.namespace".to_string();

    let err = extract_pid_mdoc(&fixture.doc, &request).expect_err("non-profile namespace rejects");

    assert_eq!(err, MdocError::NamespaceMissing);
}

#[test]
fn issuer_x5chain_requires_trusted_root_and_supplies_issuer_key() {
    let session_transcript = test_session_transcript();
    let issuer_signing_key =
        SigningKey::from_bytes((&[7u8; 32]).into()).expect("issuer signing key");
    let issuer_certificate = self_signed_certificate_der(&issuer_signing_key);
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        FixtureOptions {
            issuer_unprotected: Some(map(vec![(
                Value::from(33),
                Value::Bytes(issuer_certificate.clone()),
            )])),
            ..FixtureOptions::default()
        },
    );

    let err = extract_pid_mdoc(&fixture.doc, &request(session_transcript.clone()))
        .expect_err("untrusted root rejects");
    assert_eq!(err, MdocError::UntrustedIssuerCertificate);

    let mut trusted_request = request(session_transcript);
    trusted_request
        .trusted_issuer_certificates
        .push(issuer_certificate);
    let extracted =
        extract_pid_mdoc(&fixture.doc, &trusted_request).expect("trusted x5chain extracts");
    assert_eq!(extracted.issuer_key, fixture.issuer_key);
}

#[test]
fn rejects_non_bstr_tag24() {
    let session_transcript = test_session_transcript();
    let options = FixtureOptions {
        tag24_bstr: false,
        ..FixtureOptions::default()
    };
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        options,
    );

    let err = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect_err("non-bstr tag24 rejects");

    assert_eq!(err, MdocError::WrongType("IssuerSignedItemBytes"));
}

#[test]
fn rejects_bad_protected_header() {
    let session_transcript = test_session_transcript();
    let options = FixtureOptions {
        protected: vec![0xA1, 0x01, 0x27],
        ..FixtureOptions::default()
    };
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        options,
    );

    let err = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect_err("bad protected header rejects");

    assert_eq!(
        err,
        MdocError::InvalidCoseSign1("protected header must be ES256")
    );
}

#[test]
fn rejects_short_salt() {
    let session_transcript = test_session_transcript();
    let options = FixtureOptions {
        birth_random: vec![7; 8],
        ..FixtureOptions::default()
    };
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        options,
    );

    let err =
        extract_pid_mdoc(&fixture.doc, &request(session_transcript)).expect_err("salt rejects");

    assert_eq!(err, MdocError::SaltTooShort { len: 8 });
}

#[test]
fn accepts_legacy_noncanonical_issuer_signed_item_key_order() {
    let session_transcript = test_session_transcript();
    let options = FixtureOptions {
        canonical_item_order: false,
        value_last: true,
        mso_version: "1.0".to_string(),
        ..FixtureOptions::default()
    };
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        options,
    );

    extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("legacy alternate-order IssuerSignedItem parses");
}

#[test]
fn rejects_v2_noncanonical_issuer_signed_item_order() {
    let session_transcript = test_session_transcript();
    let options = FixtureOptions {
        canonical_item_order: false,
        value_last: true,
        ..FixtureOptions::default()
    };
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        options,
    );

    let err = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect_err("v2 noncanonical IssuerSignedItem order rejects");

    assert_eq!(
        err,
        MdocError::UnsupportedCircuitValue("IssuerSignedItem canonical key order")
    );
}

#[test]
fn rejects_digest_id_over_u32() {
    let session_transcript = test_session_transcript();
    let options = FixtureOptions {
        birth_item_digest_id: u64::from(u32::MAX) + 1,
        ..FixtureOptions::default()
    };
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        options,
    );

    let err = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect_err("oversized digestID rejects");

    assert_eq!(err, MdocError::WrongType("digestID"));
}

#[test]
fn rejects_device_unprotected_not_map() {
    let session_transcript = test_session_transcript();
    let options = FixtureOptions {
        device_unprotected: "not-a-map".into(),
        ..FixtureOptions::default()
    };
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        options,
    );

    let err = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect_err("device unprotected map rejects");

    assert_eq!(err, MdocError::WrongType("COSE_Sign1.unprotected"));
}

#[test]
fn rejects_extra_cose_key_field() {
    let session_transcript = test_session_transcript();
    let options = FixtureOptions {
        extra_device_key_field: true,
        ..FixtureOptions::default()
    };
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        options,
    );

    let err = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect_err("extra COSE_Key field rejects");

    assert_eq!(err, MdocError::InvalidCoseKey("expected ES256 P-256 key"));
}

#[test]
fn rejects_missing_validity_info() {
    let session_transcript = test_session_transcript();
    let options = FixtureOptions {
        validity_info: None,
        ..FixtureOptions::default()
    };
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        options,
    );

    let err = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect_err("missing validityInfo rejects");

    assert_eq!(err, MdocError::MissingField("validityInfo"));
}

#[test]
fn rejects_malformed_tdate() {
    let session_transcript = test_session_transcript();
    let options = FixtureOptions {
        validity_info: Some(map(vec![
            ("signed".into(), tdate("bad")),
            ("validFrom".into(), tdate("2026-01-01T00:00:00Z")),
            ("validUntil".into(), tdate("2030-01-01T00:00:00Z")),
        ])),
        ..FixtureOptions::default()
    };
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        options,
    );

    let err = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect_err("malformed tdate rejects");

    assert_eq!(err, MdocError::InvalidTdate("validityInfo.signed"));
}

#[test]
fn rejects_mso_doctype_mismatch() {
    let session_transcript = test_session_transcript();
    let options = FixtureOptions {
        mso_doctype: "wrong.doctype".to_string(),
        ..FixtureOptions::default()
    };
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        options,
    );

    let err = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect_err("MSO doctype mismatch rejects");

    assert_eq!(err, MdocError::DoctypeMismatch);
}

#[test]
fn rejects_unsupported_mso_version() {
    // Profile v1 ("1.0") and v2 ("2.0") are accepted; anything else is rejected.
    let session_transcript = test_session_transcript();
    let options = FixtureOptions {
        mso_version: "3.0".to_string(),
        ..FixtureOptions::default()
    };
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        options,
    );

    let err = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect_err("unsupported MSO version rejects");

    assert_eq!(err, MdocError::UnsupportedMsoVersion("3.0".to_string()));
}

#[test]
fn statement_rejects_expired_credential() {
    let session_transcript = test_session_transcript();
    let options = FixtureOptions {
        validity_info: Some(validity_info(
            "2026-01-01T00:00:00Z",
            "2026-01-01T00:00:00Z",
            "2026-06-01T00:00:00Z",
        )),
        ..FixtureOptions::default()
    };
    let fixture = fixture_with_options(
        &session_transcript,
        Value::Bytes(vec![0x07, 0xC6, 7, 15]),
        Value::Bytes(276u16.to_be_bytes().to_vec()),
        options,
    );
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("expired mdoc still extracts");

    let err = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect_err("expired statement rejects");

    assert_eq!(err, MdocError::CredentialExpired);
}

#[test]
fn statement_rejects_not_yet_valid_credential() {
    let session_transcript = test_session_transcript();
    let options = FixtureOptions {
        validity_info: Some(validity_info(
            "2026-01-01T00:00:00Z",
            "2027-01-01T00:00:00Z",
            "2030-01-01T00:00:00Z",
        )),
        ..FixtureOptions::default()
    };
    let fixture = fixture_with_options(
        &session_transcript,
        Value::Bytes(vec![0x07, 0xC6, 7, 15]),
        Value::Bytes(276u16.to_be_bytes().to_vec()),
        options,
    );
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("future mdoc still extracts");

    let err = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect_err("not-yet-valid statement rejects");

    assert_eq!(err, MdocError::CredentialNotYetValid);
}

#[test]
fn statement_accepts_text_birth_date() {
    // Profile v2: a text (`tstr`) `YYYY-MM-DD` birth date builds a valid
    // statement with a `Text` binding (v1 rejected text values).
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("text birth date extracts");

    let statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("text birth date builds a v2 statement");

    assert!(matches!(
        statement.birth_date_binding,
        MdocBirthDateBinding::Text(_)
    ));
}

#[test]
fn statement_accepts_text_nationality() {
    // Profile v2: an alpha-2 (`tstr`) nationality builds a valid statement with
    // an `Alpha2` binding (v1 rejected text values).
    let session_transcript = test_session_transcript();
    let fixture = fixture_with_options(
        &session_transcript,
        Value::Bytes(vec![0x07, 0xC6, 7, 15]),
        "DE".into(),
        FixtureOptions::default(),
    );
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("text nationality extracts");

    let statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("text nationality builds a v2 statement");

    assert!(matches!(
        statement.nationality_binding,
        MdocNationalityBinding::Alpha2(_)
    ));
}

#[test]
fn statement_carries_mso_binding_offsets() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted =
        extract_pid_mdoc(&fixture.doc, &request(session_transcript)).expect("mdoc extracts");
    let statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("statement builds");

    assert_eq!(
        &extracted.birth_date_item
            [statement.birth_date_element_offset..statement.birth_date_element_offset + 10],
        b"birth_date"
    );
    assert_eq!(
        &extracted.nationality_item
            [statement.nationality_element_offset..statement.nationality_element_offset + 11],
        b"nationality"
    );
    assert_eq!(
        &extracted.issuer_sig_structure
            [statement.mso_device_key_x_offset..statement.mso_device_key_x_offset + 32],
        &extracted.device_key.x.0
    );
    assert_eq!(
        &extracted.issuer_sig_structure
            [statement.mso_device_key_y_offset..statement.mso_device_key_y_offset + 32],
        &extracted.device_key.y.0
    );
    assert_eq!(
        &extracted.issuer_sig_structure
            [statement.mso_valid_from_date_offset..statement.mso_valid_from_date_offset + 10],
        b"2026-01-01"
    );
    assert_eq!(
        &extracted.issuer_sig_structure
            [statement.mso_valid_until_date_offset..statement.mso_valid_until_date_offset + 10],
        b"2030-01-01"
    );
    assert_eq!(
        &extracted.issuer_sig_structure[statement.mso_birth_date_digest_anchor_offset
            ..statement.mso_birth_date_digest_anchor_offset
                + statement.mso_birth_date_digest_anchor.len()],
        statement.mso_birth_date_digest_anchor.as_slice()
    );
    assert_eq!(statement.mso_birth_date_digest_anchor, vec![7, 0x58, 0x20]);
    assert_eq!(
        &extracted.issuer_sig_structure[statement.mso_nationality_digest_anchor_offset
            ..statement.mso_nationality_digest_anchor_offset
                + statement.mso_nationality_digest_anchor.len()],
        statement.mso_nationality_digest_anchor.as_slice()
    );
    assert_eq!(statement.mso_nationality_digest_anchor, vec![9, 0x58, 0x20]);
    assert_eq!(statement.mso_device_key_x_anchor, vec![0x21, 0x58, 0x20]);
    assert_eq!(statement.mso_device_key_y_anchor, vec![0x22, 0x58, 0x20]);
    assert_eq!(
        statement.mso_valid_from_anchor,
        [b"\x69validFrom".as_slice(), &[0xC0, 0x74]].concat()
    );
    assert_eq!(
        statement.mso_valid_until_anchor,
        [b"\x6AvalidUntil".as_slice(), &[0xC0, 0x74]].concat()
    );
}

#[test]
fn rejects_duplicate_age_over_modes() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let mut request = request(session_transcript);
    request.attributes = vec![
        MdocRequestedAttribute {
            element_identifier: BIRTH_DATE.to_string(),
            mode: MdocDisclosureMode::AgeOver,
        },
        MdocRequestedAttribute {
            element_identifier: "age_over_18".to_string(),
            mode: MdocDisclosureMode::AgeOver,
        },
    ];

    let err = extract_pid_mdoc(&fixture.doc, &request).expect_err("duplicate AgeOver rejects");

    assert_eq!(err, MdocError::DuplicatePredicateMode("AgeOver"));
}

#[test]
fn rejects_oversized_value_equality_window() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let mut request = request(session_transcript);
    request.attributes = vec![MdocRequestedAttribute {
        element_identifier: "family_name".to_string(),
        mode: MdocDisclosureMode::ValueEquality(vec![b'A'; 33]),
    }];

    let err =
        extract_pid_mdoc(&fixture.doc, &request).expect_err("oversized value equality rejects");

    assert_eq!(
        err,
        MdocError::ValueEqualityTooLong {
            element: "family_name".to_string(),
            len: 33
        }
    );
}

#[test]
fn value_equality_n1_statement_builds_for_bool() {
    let session_transcript = test_session_transcript();
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        FixtureOptions {
            extra_items: vec![ExtraItem {
                digest_id: 11,
                element: "age_over_18".to_string(),
                value: Value::Bool(true),
                random: vec![11; 16],
            }],
            ..FixtureOptions::default()
        },
    );
    let mut request = request(session_transcript);
    request.attributes = vec![MdocRequestedAttribute {
        element_identifier: "age_over_18".to_string(),
        mode: MdocDisclosureMode::ValueEquality(cbor(Value::Bool(true))),
    }];

    let extracted = extract_pid_mdoc(&fixture.doc, &request).expect("N=1 extracts");
    let statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("N=1 builds");

    assert_eq!(statement.attributes.len(), 1);
    assert!(statement.age_attribute_index.is_none());
    assert!(statement.nationality_attribute_index.is_none());
    assert_eq!(statement.attributes[0].value, cbor(Value::Bool(true)));
    assert_eq!(statement.attributes[0].value_head, cbor(Value::Bool(true)));
}

#[test]
fn mixed_n3_statement_builds_with_value_equality() {
    let session_transcript = test_session_transcript();
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        FixtureOptions {
            extra_items: vec![ExtraItem {
                digest_id: 11,
                element: "family_name".to_string(),
                value: "Mustermann".into(),
                random: vec![11; 16],
            }],
            ..FixtureOptions::default()
        },
    );
    let mut request = request(session_transcript);
    request.attributes.push(MdocRequestedAttribute {
        element_identifier: "family_name".to_string(),
        mode: MdocDisclosureMode::ValueEquality(cbor("Mustermann".into())),
    });

    let extracted = extract_pid_mdoc(&fixture.doc, &request).expect("N=3 extracts");
    let statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("N=3 builds");

    assert_eq!(statement.attributes.len(), 3);
    assert_eq!(statement.age_attribute_index, Some(0));
    assert_eq!(statement.nationality_attribute_index, Some(1));
    assert_eq!(statement.attributes[2].value, cbor("Mustermann".into()));
    assert_eq!(statement.attributes[2].value_head, vec![0x6A]);
}

#[test]
fn mixed_n4_statement_builds_with_value_equality_remainder() {
    let session_transcript = test_session_transcript();
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        FixtureOptions {
            extra_items: vec![
                ExtraItem {
                    digest_id: 11,
                    element: "family_name".to_string(),
                    value: "Mustermann".into(),
                    random: vec![11; 16],
                },
                ExtraItem {
                    digest_id: 13,
                    element: "age_over_18".to_string(),
                    value: Value::Bool(true),
                    random: vec![13; 16],
                },
            ],
            ..FixtureOptions::default()
        },
    );
    let mut request = request(session_transcript);
    request.attributes.extend([
        MdocRequestedAttribute {
            element_identifier: "family_name".to_string(),
            mode: MdocDisclosureMode::ValueEquality(cbor("Mustermann".into())),
        },
        MdocRequestedAttribute {
            element_identifier: "age_over_18".to_string(),
            mode: MdocDisclosureMode::ValueEquality(cbor(Value::Bool(true))),
        },
    ]);

    let extracted = extract_pid_mdoc(&fixture.doc, &request).expect("N=4 extracts");
    let statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("N=4 builds");

    assert_eq!(statement.attributes.len(), 4);
    assert_eq!(statement.age_attribute_index, Some(0));
    assert_eq!(statement.nationality_attribute_index, Some(1));
    assert_eq!(statement.attributes[2].value_head, vec![0x6A]);
    assert_eq!(statement.attributes[3].value_head, vec![0xF5]);
}

#[test]
fn value_equality_statement_uses_request_profile() {
    let session_transcript = test_session_transcript();
    let doctype = "org.iso.18013.5.1.mDL".to_string();
    let namespace = "org.iso.18013.5.1".to_string();
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        FixtureOptions {
            doc_doctype: doctype.clone(),
            namespace: namespace.clone(),
            mso_doctype: doctype.clone(),
            extra_items: vec![ExtraItem {
                digest_id: 11,
                element: "family_name".to_string(),
                value: "Mustermann".into(),
                random: vec![11; 16],
            }],
            ..FixtureOptions::default()
        },
    );
    let mut request = request(session_transcript);
    request.doctype = doctype;
    request.namespace = namespace;
    request.attributes = vec![MdocRequestedAttribute {
        element_identifier: "family_name".to_string(),
        mode: MdocDisclosureMode::ValueEquality(cbor("Mustermann".into())),
    }];

    let extracted = extract_pid_mdoc(&fixture.doc, &request).expect("custom profile extracts");
    let statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("custom profile statement builds");

    assert_eq!(statement.attributes.len(), 1);
    assert!(statement.age_attribute_index.is_none());
    assert!(statement.nationality_attribute_index.is_none());
    assert_eq!(statement.attributes[0].element_identifier, "family_name");
}

#[test]
fn wrong_value_equality_rejects() {
    let session_transcript = test_session_transcript();
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        FixtureOptions {
            extra_items: vec![ExtraItem {
                digest_id: 11,
                element: "family_name".to_string(),
                value: "Mustermann".into(),
                random: vec![11; 16],
            }],
            ..FixtureOptions::default()
        },
    );
    let mut request = request(session_transcript);
    request.attributes = vec![MdocRequestedAttribute {
        element_identifier: "family_name".to_string(),
        mode: MdocDisclosureMode::ValueEquality(cbor("Erika".into())),
    }];

    let err = extract_pid_mdoc(&fixture.doc, &request).expect_err("wrong value rejects");

    assert_eq!(
        err,
        MdocError::ValueEqualityMismatch {
            element: "family_name".to_string()
        }
    );
}

#[test]
fn truncated_value_equality_rejects() {
    let session_transcript = test_session_transcript();
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        FixtureOptions {
            extra_items: vec![ExtraItem {
                digest_id: 11,
                element: "family_name".to_string(),
                value: "Mustermann".into(),
                random: vec![11; 16],
            }],
            ..FixtureOptions::default()
        },
    );
    let mut request = request(session_transcript);
    request.attributes = vec![MdocRequestedAttribute {
        element_identifier: "family_name".to_string(),
        mode: MdocDisclosureMode::ValueEquality(vec![0x6A, b'M', b'u']),
    }];

    let err = extract_pid_mdoc(&fixture.doc, &request).expect_err("truncated value rejects");

    assert_eq!(
        err,
        MdocError::ValueEqualityMismatch {
            element: "family_name".to_string()
        }
    );
}

#[test]
#[ignore = "slow: proves N=1 value-equality mdoc profile"]
fn value_equality_n1_proves_and_verifies() {
    let session_transcript = test_session_transcript();
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        FixtureOptions {
            extra_items: vec![ExtraItem {
                digest_id: 11,
                element: "age_over_18".to_string(),
                value: Value::Bool(true),
                random: vec![11; 16],
            }],
            ..FixtureOptions::default()
        },
    );
    let mut request = request(session_transcript);
    request.attributes = vec![MdocRequestedAttribute {
        element_identifier: "age_over_18".to_string(),
        mode: MdocDisclosureMode::ValueEquality(cbor(Value::Bool(true))),
    }];
    let extracted = extract_pid_mdoc(&fixture.doc, &request).expect("N=1 extracts");
    let statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("N=1 builds");

    let proof = prove_mdoc_circuit(&extracted, &statement).expect("N=1 proves");

    verify_mdoc_circuit(&proof, &statement).expect("N=1 verifies");
}

#[test]
#[ignore = "release gate: proves TS13 N=1 tuple and prints evidence measurements"]
fn ts13_evidence_pack_n1_measurements() {
    let session_transcript = test_session_transcript();
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        FixtureOptions {
            extra_items: vec![ExtraItem {
                digest_id: 11,
                element: "age_over_18".to_string(),
                value: Value::Bool(true),
                random: vec![11; 16],
            }],
            ..FixtureOptions::default()
        },
    );
    let mut request = request(session_transcript);
    request.attributes = vec![MdocRequestedAttribute {
        element_identifier: "age_over_18".to_string(),
        mode: MdocDisclosureMode::ValueEquality(cbor(Value::Bool(true))),
    }];
    let extracted = extract_pid_mdoc(&fixture.doc, &request).expect("TS13 N=1 extracts");
    let statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("TS13 N=1 builds");
    let id = ts13_mso_derived_revocation_id(&extracted.mso);
    let (signing_key, revocation_key) = ts13_revocation_key(33);
    let revocation_statement = Ts13RevocationStatement {
        revocation_public_key: revocation_key,
        epoch: 51,
    };
    let revocation_witness = ts13_revocation_witness_for_id(
        &signing_key,
        id,
        id.saturating_sub(1),
        id.saturating_add(1),
        revocation_statement.epoch,
    );
    let statement = statement
        .with_ts13_revocation((&revocation_statement).into())
        .with_ts13_revocation_range(MdocRevocationRangeWitness {
            id: revocation_witness.id,
            id_lo: revocation_witness.id_lo,
            id_hi: revocation_witness.id_hi,
        })
        .with_ts13_revocation_signature(revocation_witness.signature.clone());

    let prove_start = Instant::now();
    let proof = prove_mdoc_circuit(&extracted, &statement).expect("TS13 N=1 proves");
    let prove_ms = prove_start.elapsed().as_millis();
    let expected_preprocessed_root = proof.stark_proof.commitments[0].0;

    let verify_start = Instant::now();
    verify_mdoc_circuit_with_preprocessed_root(
        &proof,
        &statement,
        proof.stark_proof.commitments[0],
    )
    .expect("TS13 N=1 verifies with root pin");
    let verify_ms = verify_start.elapsed().as_millis();

    let proof_bytes = bincode::serialize(&proof).expect("TS13 mdoc proof serializes");
    let artifact = Ts13MdocProofArtifact {
        circuit_hash: ts13_default_circuit_hash(),
        preprocessed_root: expected_preprocessed_root,
        mdoc_proof: proof_bytes,
        revocation_statement,
        revocation_witness,
    };
    artifact
        .verify_revocation_binding(&extracted, expected_preprocessed_root)
        .expect("TS13 revocation artifact binds to this mdoc");
    artifact
        .verify_mdoc_and_revocation(&extracted, &statement)
        .expect("TS13 artifact verifies mdoc proof and revocation together");

    let breakdown = mdoc_proof_byte_breakdown(&proof);
    println!(
        "ts13_evidence_n1 proof_bytes={} stark_proof_bytes={} non_stark_metadata_bytes={} prove_ms={} verify_ms={} preprocessed_root={} circuit_hash={}",
        breakdown.proof_bytes,
        breakdown.stark_proof_bytes,
        breakdown.non_stark_metadata_bytes,
        prove_ms,
        verify_ms,
        hex_bytes(&expected_preprocessed_root),
        ts13_default_circuit_hash()
    );
}

/// Build a revocation-enabled TS13 N=1 mdoc `(extracted, statement)`. The
/// revocation path engages the digest-bind bridge, whose range8/range13 tables
/// carry the Q-015 §4b / p4c Class-D dummy-key multiplicity blinding — so a
/// revocation proof exercises Class D end-to-end.
fn ts13_class_d_revocation_case() -> (
    eu_id_prover::mdoc::ExtractedPidMdoc,
    eu_id_prover::mdoc::MdocCircuitStatement,
) {
    let session_transcript = test_session_transcript();
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        FixtureOptions {
            extra_items: vec![ExtraItem {
                digest_id: 11,
                element: "age_over_18".to_string(),
                value: Value::Bool(true),
                random: vec![11; 16],
            }],
            ..FixtureOptions::default()
        },
    );
    let mut request = request(session_transcript);
    request.attributes = vec![MdocRequestedAttribute {
        element_identifier: "age_over_18".to_string(),
        mode: MdocDisclosureMode::ValueEquality(cbor(Value::Bool(true))),
    }];
    let extracted = extract_pid_mdoc(&fixture.doc, &request).expect("class-d case extracts");
    let statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("class-d case builds");
    let id = ts13_mso_derived_revocation_id(&extracted.mso);
    let (signing_key, revocation_key) = ts13_revocation_key(33);
    let revocation_statement = Ts13RevocationStatement {
        revocation_public_key: revocation_key,
        epoch: 51,
    };
    let revocation_witness = ts13_revocation_witness_for_id(
        &signing_key,
        id,
        id.saturating_sub(1),
        id.saturating_add(1),
        revocation_statement.epoch,
    );
    let statement = statement
        .with_ts13_revocation((&revocation_statement).into())
        .with_ts13_revocation_range(MdocRevocationRangeWitness {
            id: revocation_witness.id,
            id_lo: revocation_witness.id_lo,
            id_hi: revocation_witness.id_hi,
        })
        .with_ts13_revocation_signature(revocation_witness.signature.clone());
    (extracted, statement)
}

/// Class D (Q-015 §4b / p4c): proving the same revocation mdoc witness twice
/// yields DIFFERENT serialized proofs — the digest-bridge range tables' Class-D
/// dummy-region multiplicity cells are fresh random per proof — and BOTH proofs
/// verify. The bridge carries a 2× (log_size + 1) blinded domain for its
/// range8/range13 tables (asserted directly in the stwo-p256 unit test
/// `class_d_bridge_range_tables_use_doubled_domain`).
#[test]
#[ignore = "slow: proves the revocation mdoc twice to check Class-D multiplicity freshness"]
fn mdoc_zk_class_d_dummy_key_multiplicities() {
    let (extracted, statement) = ts13_class_d_revocation_case();

    let first = prove_mdoc_circuit(&extracted, &statement).expect("first class-d mdoc proves");
    verify_mdoc_circuit(&first, &statement).expect("first class-d mdoc verifies");
    let second = prove_mdoc_circuit(&extracted, &statement).expect("second class-d mdoc proves");
    verify_mdoc_circuit(&second, &statement).expect("second class-d mdoc verifies");

    let first_bytes = bincode::serialize(&first).expect("first proof serializes");
    let second_bytes = bincode::serialize(&second).expect("second proof serializes");
    assert_ne!(
        first_bytes, second_bytes,
        "same-witness revocation proofs must differ (fresh Class-D blind multiplicities)",
    );
}

/// Class D (Q-015 §4b / p4c): tampering the cancelling-pair term in a serialized
/// revocation proof breaks the bridge range table's LogUp boundary at OODS, so
/// verification fails. Sweeps a byte flip across the serialized proof and
/// asserts NO tamper verifies (the balance is bound, not a free term).
#[test]
#[ignore = "slow: proves Class-D balance tamper is rejected"]
fn mdoc_zk_class_d_balance_tamper_rejected() {
    let (extracted, statement) = ts13_class_d_revocation_case();

    let proof = prove_mdoc_circuit(&extracted, &statement).expect("class-d mdoc proves");
    verify_mdoc_circuit(&proof, &statement).expect("honest class-d mdoc verifies");

    let bytes = bincode::serialize(&proof).expect("proof serializes");
    // Flip one bit in a spread of positions across the serialized proof (which
    // includes the revocation-bridge Class-D claimed sums). Every corrupted
    // proof that still deserializes must fail verification.
    let mut any_checked = false;
    for &pos in &[
        bytes.len() / 4,
        bytes.len() / 2,
        (bytes.len() * 3) / 4,
        bytes.len() - 8,
    ] {
        let mut tampered_bytes = bytes.clone();
        tampered_bytes[pos] ^= 0x01;
        let Ok(tampered) =
            bincode::deserialize::<eu_id_prover::mdoc::MdocCircuitProof>(&tampered_bytes)
        else {
            continue;
        };
        any_checked = true;
        assert!(
            verify_mdoc_circuit(&tampered, &statement).is_err(),
            "a tampered Class-D revocation proof must be rejected (byte {pos})",
        );
    }
    assert!(
        any_checked,
        "at least one byte flip must deserialize so the tamper is actually exercised",
    );
}

#[test]
#[ignore = "slow: proves rejection for ValueEquality elementIdentifier anchor tamper"]
fn value_equality_element_identifier_anchor_offset_rejects_in_proof() {
    let session_transcript = test_session_transcript();
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        FixtureOptions {
            extra_items: vec![ExtraItem {
                digest_id: 11,
                element: "age_over_18".to_string(),
                value: Value::Bool(true),
                random: vec![11; 16],
            }],
            ..FixtureOptions::default()
        },
    );
    let mut request = request(session_transcript);
    request.attributes = vec![MdocRequestedAttribute {
        element_identifier: "age_over_18".to_string(),
        mode: MdocDisclosureMode::ValueEquality(cbor(Value::Bool(true))),
    }];
    let extracted = extract_pid_mdoc(&fixture.doc, &request).expect("N=1 extracts");
    let mut statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("N=1 builds");
    statement.attributes[0].element_identifier_anchor_offset += 1;

    match prove_mdoc_circuit(&extracted, &statement) {
        Err(eu_id_prover::Error::Prove(_)) => {}
        Err(other) => panic!("expected proof rejection, got {other:?}"),
        Ok(proof) => {
            assert!(
                verify_mdoc_circuit(&proof, &statement).is_err(),
                "mispointed ValueEquality elementIdentifier anchor verified unexpectedly"
            );
        }
    }
}

#[test]
#[ignore = "slow: proves N=3 mixed mdoc profile"]
fn mixed_n3_proves_and_verifies() {
    let session_transcript = test_session_transcript();
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        FixtureOptions {
            extra_items: vec![ExtraItem {
                digest_id: 11,
                element: "family_name".to_string(),
                value: "Mustermann".into(),
                random: vec![11; 16],
            }],
            ..FixtureOptions::default()
        },
    );
    let mut request = request(session_transcript);
    request.attributes.push(MdocRequestedAttribute {
        element_identifier: "family_name".to_string(),
        mode: MdocDisclosureMode::ValueEquality(cbor("Mustermann".into())),
    });
    let extracted = extract_pid_mdoc(&fixture.doc, &request).expect("N=3 extracts");
    let statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("N=3 builds");

    let proof = prove_mdoc_circuit(&extracted, &statement).expect("N=3 proves");

    verify_mdoc_circuit(&proof, &statement).expect("N=3 verifies");
}

#[test]
#[ignore = "slow: proves rejection for validity-window policy tamper"]
fn prove_rejects_policy_after_valid_until_when_statement_guard_is_bypassed() {
    let session_transcript = test_session_transcript();
    let options = FixtureOptions {
        validity_info: Some(validity_info(
            "2026-01-01T00:00:00Z",
            "2026-01-01T00:00:00Z",
            "2026-07-02T00:00:00Z",
        )),
        ..FixtureOptions::default()
    };
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        options,
    );
    let extracted =
        extract_pid_mdoc(&fixture.doc, &request(session_transcript)).expect("mdoc extracts");
    let mut statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 1))
        .expect("statement builds while credential is valid");
    assert_eq!(statement.valid_until, (2026, 7, 2));
    statement.policy.current_date = Date {
        year: 2026,
        month: 7,
        day: 3,
    };

    match prove_mdoc_circuit(&extracted, &statement) {
        Err(eu_id_prover::Error::Prove(_)) => {}
        Err(other) => panic!("expected validity proof rejection, got {other:?}"),
        Ok(_) => panic!("expired policy date proved unexpectedly"),
    }
}

#[test]
fn statement_rejects_mispointed_value_window() {
    // Profile v2 drops the "window in the first SHA-256 block" rule; the only
    // host-side guard is byte-equality at the prover-supplied offset, so a
    // mispointed offset (whose bytes do not match the parsed value) still
    // rejects.
    let session_transcript = test_session_transcript();
    let fixture = circuit_fixture(&session_transcript);
    let mut extracted =
        extract_pid_mdoc(&fixture.doc, &request(session_transcript)).expect("binary mdoc extracts");
    extracted.birth_date_value_offset += 1;

    let err = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect_err("mispointed value window rejects");

    assert_eq!(
        err,
        MdocError::UnsupportedCircuitValue("element value bytes at offset")
    );
}

#[test]
#[ignore = "slow: proves product mdoc circuit profile"]
fn isolated_mdoc_circuit_profile_proves_and_verifies() {
    let session_transcript = test_session_transcript();
    let fixture = circuit_fixture(&session_transcript);
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("circuit profile mdoc extracts");
    let policy = policy_on(2026, 7, 3);
    let statement =
        MdocCircuitStatement::from_extracted(&extracted, policy).expect("statement builds");

    let proof = prove_mdoc_circuit(&extracted, &statement).expect("mdoc circuit proves");

    verify_mdoc_circuit(&proof, &statement).expect("mdoc circuit verifies");
}

#[test]
#[ignore = "slow: proves real pyMDOC PID vector end-to-end"]
fn real_vector_pid_pymdoc_end_to_end() {
    // Q-002's "no hand-crafted fake vector" rule is satisfied by consuming the
    // byte-frozen issuer half from pyMDOC-CBOR; this test only builds the
    // wallet-side deviceSigned presentation over the Phase-E-exact payload.
    let session_transcript = openid4vp_session_transcript(b"phase-v-real-vector-handover");
    let (document, trusted_root) = real_vector_document(&session_transcript);
    let mut request = request(session_transcript);
    request.trusted_issuer_certificates.push(trusted_root);

    let extracted = extract_pid_mdoc(&document, &request).expect("real PID mdoc extracts");
    assert_eq!(extracted.birth_date, "1985-05-05");
    assert_eq!(extracted.nationalities, vec![276]);
    assert_eq!(
        &extracted.birth_date_item[extracted.birth_date_value_offset
            ..extracted.birth_date_value_offset + b"1985-05-05".len()],
        b"1985-05-05"
    );
    assert_eq!(
        extracted.birth_date_binding,
        MdocBirthDateBinding::Text(*b"1985-05-05")
    );
    assert_eq!(
        extracted.nationality_binding,
        MdocNationalityBinding::Alpha2(*b"DE")
    );

    let policy = Policy {
        current_date: Date {
            year: 2026,
            month: 7,
            day: 1,
        },
        min_age_years: 18,
        accepted_nationalities: Vec::new(),
        accepted_nationalities_alpha2: vec![*b"DE"],
    };
    let statement =
        MdocCircuitStatement::from_extracted(&extracted, policy).expect("statement builds");

    let prove_start = Instant::now();
    let proof = prove_mdoc_circuit(&extracted, &statement).expect("real PID mdoc proves");
    let prove_elapsed = prove_start.elapsed();

    let verify_start = Instant::now();
    verify_mdoc_circuit(&proof, &statement).expect("real PID mdoc verifies");
    let verify_elapsed = verify_start.elapsed();

    let bytes = mdoc_proof_byte_breakdown(&proof).proof_bytes;
    println!(
        "phase_v_real_vector prove_ms={} verify_ms={} proof_bytes={bytes}",
        prove_elapsed.as_millis(),
        verify_elapsed.as_millis()
    );
}

#[test]
fn longfellow_vectors_extract_and_match_inventory() {
    let mdl = longfellow_mdl3();
    assert_longfellow_inventory(
        &mdl,
        &[
            ("age_over_18", "bool:true"),
            ("birth_date", "tag1004:1971-09-01"),
            ("family_name", "text:Mustermann"),
            ("height", "uint:175"),
            ("issue_date", "tag1004:2024-03-15"),
        ],
    );
    let mdl_request = longfellow_request(
        &mdl,
        vec![
            MdocRequestedAttribute {
                element_identifier: "age_over_18".to_string(),
                mode: MdocDisclosureMode::ValueEquality(cbor(Value::Bool(true))),
            },
            MdocRequestedAttribute {
                element_identifier: "birth_date".to_string(),
                mode: MdocDisclosureMode::AgeOver,
            },
        ],
    );
    let mdl_extracted = extract_pid_mdoc(mdl.mdoc, &mdl_request).expect("mDL extracts");
    assert_eq!(mdl_extracted.doctype, LONGFELLOW_MDL_DOCTYPE);
    assert_eq!(mdl_extracted.birth_date, "1971-09-01");
    assert_eq!(
        mdl_extracted.birth_date_binding,
        MdocBirthDateBinding::Text(*b"1971-09-01")
    );
    MdocCircuitStatement::from_extracted(&mdl_extracted, policy_from_longfellow_now(&mdl))
        .expect("mDL statement builds");

    let euav = longfellow_euav11();
    assert_longfellow_inventory(&euav, &[("age_over_18", "bool:true")]);
    let euav_request = longfellow_request(
        &euav,
        vec![MdocRequestedAttribute {
            element_identifier: "age_over_18".to_string(),
            mode: MdocDisclosureMode::ValueEquality(cbor(Value::Bool(true))),
        }],
    );
    let euav_extracted = extract_pid_mdoc(euav.mdoc, &euav_request).expect("EUAV extracts");
    assert_eq!(euav_extracted.doctype, LONGFELLOW_EUAV_DOCTYPE);
    MdocCircuitStatement::from_extracted(&euav_extracted, policy_from_longfellow_now(&euav))
        .expect("EUAV statement builds");
}

#[test]
#[ignore = "slow: proves Longfellow mDL N=1 vector end-to-end"]
fn longfellow_mdl3_n1_age_over_18_end_to_end() {
    let vector = longfellow_mdl3();
    longfellow_vector_end_to_end(
        &vector,
        vec![MdocRequestedAttribute {
            element_identifier: "age_over_18".to_string(),
            mode: MdocDisclosureMode::ValueEquality(cbor(Value::Bool(true))),
        }],
    );
}

#[test]
#[ignore = "slow: proves Longfellow mDL N=2 vector end-to-end"]
fn longfellow_mdl3_n2_age_over_18_birth_date_end_to_end() {
    let vector = longfellow_mdl3();
    longfellow_vector_end_to_end(
        &vector,
        vec![
            MdocRequestedAttribute {
                element_identifier: "age_over_18".to_string(),
                mode: MdocDisclosureMode::ValueEquality(cbor(Value::Bool(true))),
            },
            MdocRequestedAttribute {
                element_identifier: "birth_date".to_string(),
                mode: MdocDisclosureMode::AgeOver,
            },
        ],
    );
}

#[test]
#[ignore = "slow: proves Longfellow EUAV #11 vector end-to-end"]
fn longfellow_euav11_age_over_18_end_to_end() {
    let vector = longfellow_euav11();
    longfellow_vector_end_to_end(
        &vector,
        vec![MdocRequestedAttribute {
            element_identifier: "age_over_18".to_string(),
            mode: MdocDisclosureMode::ValueEquality(cbor(Value::Bool(true))),
        }],
    );
}

fn longfellow_vector_end_to_end(
    vector: &LongfellowVector,
    attributes: Vec<MdocRequestedAttribute>,
) {
    let request = longfellow_request(vector, attributes);
    let extracted = extract_pid_mdoc(vector.mdoc, &request).expect("Longfellow vector extracts");
    let statement =
        MdocCircuitStatement::from_extracted(&extracted, policy_from_longfellow_now(vector))
            .expect("Longfellow statement builds");

    let prove_start = Instant::now();
    let proof = prove_mdoc_circuit(&extracted, &statement).expect("Longfellow mdoc proves");
    let prove_elapsed = prove_start.elapsed();

    let verify_start = Instant::now();
    verify_mdoc_circuit(&proof, &statement).expect("Longfellow mdoc verifies");
    let verify_elapsed = verify_start.elapsed();

    let bytes = mdoc_proof_byte_breakdown(&proof).proof_bytes;
    println!(
        "longfellow_vector={} n={} security_bits={} prove_ms={} verify_ms={} proof_bytes={bytes} preprocessed_root={}",
        vector.name,
        statement.attributes.len(),
        proof.stark_proof.config.security_bits(),
        prove_elapsed.as_millis(),
        verify_elapsed.as_millis(),
        hex_bytes(&proof.stark_proof.commitments[0].0)
    );
}

fn assert_longfellow_inventory(vector: &LongfellowVector, expected: &[(&str, &str)]) {
    let response: Value = ciborium::de::from_reader(vector.mdoc).expect("DeviceResponse decodes");
    let response = value_map(&response, "DeviceResponse");
    assert_eq!(
        value_text(map_text(response, "version"), "DeviceResponse.version"),
        "1.0"
    );
    let documents = value_array(map_text(response, "documents"), "documents");
    assert_eq!(
        documents.len(),
        1,
        "Longfellow vector must carry one document"
    );
    let document = value_map(&documents[0], "document");
    assert_eq!(
        value_text(map_text(document, "docType"), "docType"),
        vector.doctype
    );
    let issuer_signed = value_map(map_text(document, "issuerSigned"), "issuerSigned");
    let namespaces = value_map(map_text(issuer_signed, "nameSpaces"), "nameSpaces");
    let items = value_array(map_text(namespaces, vector.namespace), vector.namespace);
    assert_eq!(
        items.len(),
        expected.len(),
        "unexpected namespace item count"
    );

    let mut actual = Vec::new();
    for item in items {
        let item = issuer_signed_item_map(item);
        let element = value_text(map_text(&item, "elementIdentifier"), "elementIdentifier");
        actual.push((
            element.to_string(),
            longfellow_value_label(map_text(&item, "elementValue")),
        ));
    }
    actual.sort();
    let mut expected: Vec<_> = expected
        .iter()
        .map(|(element, label)| ((*element).to_string(), (*label).to_string()))
        .collect();
    expected.sort();
    assert_eq!(actual, expected);
}

fn issuer_signed_item_map(value: &Value) -> Vec<(Value, Value)> {
    let bytes = match value {
        Value::Tag(CBOR_TAG_ENCODED_CBOR, inner) => value_bytes(inner, "IssuerSignedItemBytes"),
        Value::Bytes(bytes) => bytes,
        _ => panic!("IssuerSignedItemBytes must be tag24 or bstr"),
    };
    let item: Value = ciborium::de::from_reader(bytes).expect("IssuerSignedItem decodes");
    value_map(&item, "IssuerSignedItem").to_vec()
}

fn longfellow_value_label(value: &Value) -> String {
    match value {
        Value::Bool(true) => "bool:true".to_string(),
        Value::Integer(integer) => format!("uint:{}", i128::from(*integer)),
        Value::Text(text) => format!("text:{text}"),
        Value::Tag(CBOR_TAG_FULL_DATE, inner) => {
            format!("tag1004:{}", value_text(inner, "tag1004 full-date"))
        }
        _ => panic!("unexpected Longfellow elementValue {value:?}"),
    }
}

#[test]
#[ignore = "slow: proves rejection for digest membership tamper"]
fn digest_membership_offset_swap_rejects_in_proof() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted =
        extract_pid_mdoc(&fixture.doc, &request(session_transcript)).expect("mdoc extracts");
    let mut statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("statement builds");
    std::mem::swap(
        &mut statement.mso_birth_date_digest_offset,
        &mut statement.mso_nationality_digest_offset,
    );

    match prove_mdoc_circuit(&extracted, &statement) {
        Err(eu_id_prover::Error::Prove(_)) => {}
        Err(other) => panic!("expected proof rejection, got {other:?}"),
        Ok(proof) => {
            assert!(
                verify_mdoc_circuit(&proof, &statement).is_err(),
                "digest membership offset swap verified unexpectedly"
            );
        }
    }
}

#[test]
#[ignore = "slow: proves rejection for deviceKey binding tamper"]
fn device_key_binding_offset_rejects_in_proof() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted =
        extract_pid_mdoc(&fixture.doc, &request(session_transcript)).expect("mdoc extracts");
    let mut statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("statement builds");
    statement.mso_device_key_x_offset += 1;

    match prove_mdoc_circuit(&extracted, &statement) {
        Err(eu_id_prover::Error::Prove(_)) => {}
        Err(other) => panic!("expected proof rejection, got {other:?}"),
        Ok(proof) => {
            assert!(
                verify_mdoc_circuit(&proof, &statement).is_err(),
                "mispointed MSO device-key offset verified unexpectedly"
            );
        }
    }
}

#[test]
#[ignore = "slow: proves rejection for digest anchor tamper"]
fn digest_membership_anchor_offset_rejects_in_proof() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted =
        extract_pid_mdoc(&fixture.doc, &request(session_transcript)).expect("mdoc extracts");
    let mut statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("statement builds");
    statement.mso_birth_date_digest_anchor_offset += 1;

    match prove_mdoc_circuit(&extracted, &statement) {
        Err(eu_id_prover::Error::Prove(_)) => {}
        Err(other) => panic!("expected proof rejection, got {other:?}"),
        Ok(proof) => {
            assert!(
                verify_mdoc_circuit(&proof, &statement).is_err(),
                "mispointed digest anchor verified unexpectedly"
            );
        }
    }
}

#[test]
#[ignore = "slow: proves rejection for deviceKey anchor tamper"]
fn device_key_anchor_offset_rejects_in_proof() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted =
        extract_pid_mdoc(&fixture.doc, &request(session_transcript)).expect("mdoc extracts");
    let mut statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("statement builds");
    statement.mso_device_key_x_anchor_offset += 1;

    match prove_mdoc_circuit(&extracted, &statement) {
        Err(eu_id_prover::Error::Prove(_)) => {}
        Err(other) => panic!("expected proof rejection, got {other:?}"),
        Ok(proof) => {
            assert!(
                verify_mdoc_circuit(&proof, &statement).is_err(),
                "mispointed deviceKey anchor verified unexpectedly"
            );
        }
    }
}

#[test]
#[ignore = "slow: proves rejection for validity anchor tamper"]
fn validity_anchor_offset_rejects_in_proof() {
    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted =
        extract_pid_mdoc(&fixture.doc, &request(session_transcript)).expect("mdoc extracts");
    let mut statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("statement builds");
    statement.mso_valid_from_anchor_offset += 1;

    match prove_mdoc_circuit(&extracted, &statement) {
        Err(eu_id_prover::Error::Prove(_)) => {}
        Err(other) => panic!("expected proof rejection, got {other:?}"),
        Ok(proof) => {
            assert!(
                verify_mdoc_circuit(&proof, &statement).is_err(),
                "mispointed validity anchor verified unexpectedly"
            );
        }
    }
}

/// WO-P3 pow/query rebalance negative: an honest proof produced at the pinned
/// production config (pow_bits 20, n_queries 54) verifies, but the same proof
/// re-labeled with the OLD config (pow_bits 10, n_queries 59) is rejected by the
/// verifier's `expected_pcs_config` equality gate *before* any STARK check. This
/// keeps a low-grinding old-config proof from being inherited after the
/// rebalance.
#[test]
#[ignore = "slow: full mdoc STARK prove/verify; run with --release --ignored"]
fn rejects_old_pcs_config_after_pow_query_rebalance() {
    use stwo::core::fri::FriConfig;
    use stwo::core::pcs::PcsConfig;

    let session_transcript = test_session_transcript();
    let fixture = valid_fixture(&session_transcript);
    let extracted =
        extract_pid_mdoc(&fixture.doc, &request(session_transcript)).expect("mdoc extracts");
    let statement = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect("statement builds");

    let mut proof = prove_mdoc_circuit(&extracted, &statement).expect("honest mdoc proves");

    // Sanity: it verifies at the pinned (rebalanced) config.
    verify_mdoc_circuit(&proof, &statement).expect("proof verifies at the pinned config");
    assert_eq!(
        proof.stark_proof.config,
        mdoc_production_pcs_config(),
        "prover must emit the rebalanced production config",
    );

    // The pre-rebalance config that a stale prover would have emitted.
    let old_config = PcsConfig {
        pow_bits: 10,
        fri_config: FriConfig::new(1, 2, 59, 2),
        lifting_log_size: None,
    };
    assert_ne!(
        old_config,
        mdoc_production_pcs_config(),
        "old config must differ from the rebalanced pin",
    );

    // Re-label the honest proof with the old (pre-rebalance) config and verify
    // against the current production pin: the config equality gate must reject it
    // before any STARK check.
    proof.stark_proof.0.config = old_config;
    let rejected =
        verify_mdoc_circuit_with_pcs_config(&proof, &statement, mdoc_production_pcs_config());
    assert!(
        matches!(rejected, Err(eu_id_prover::Error::WeakConfig { .. })),
        "an old-config proof must be rejected by the config pin, got {rejected:?}",
    );
}

/// Class D for the shared SHA tables (Q-015 §4b / p4c): the SHA split-pack and
/// range producers that the product mdoc proof consumes are now multiplicity-
/// blinded — a doubled (`L + 1`) committed domain with a random dummy upper
/// half. This test pins the two product-level observables:
/// 1. every shared SHA-table component is committed at the blinded log size
///    (domain 2× extended) — read directly from the shared prover's shapes;
/// 2. proving the SAME credential twice yields DIFFERENT product proofs (the
///    SHA-table dummy multiplicities are fresh per proof) and BOTH verify.
#[test]
#[ignore = "slow: proves the product mdoc twice to check Class-D SHA-table blinding"]
fn mdoc_zk_class_d_sha_tables_dummy_region() {
    use stwo_sha256::components::RANGE_TABLES;
    use stwo_sha256::field_exposure::FieldExposure as ShaFieldExposure;
    use stwo_sha256::relations::SharedShaTableRelations;
    use stwo_sha256::shared_tables::{ShaTableMultiplicities, ShaTablesProver};
    use stwo_sha256::witness::compute_sha256_witness;

    // (1) Shape check: the shared SHA-table producers commit blinded domains.
    // The blinded log size is `LOG_SIZE_16 + 1 = 17` for every producer (all
    // real tables are padded to 2^16). Build the shared prover from a couple of
    // heterogeneous witnesses — the shapes are witness-independent.
    let w0 = compute_sha256_witness(b"abc");
    let w1 = compute_sha256_witness(&[0x42u8; 200]);
    let consumers = [
        (&w0, ShaFieldExposure::empty()),
        (&w1, ShaFieldExposure::empty()),
    ];
    let sha_tables = ShaTablesProver::new(
        ShaTableMultiplicities::from_consumers(&consumers),
        SharedShaTableRelations::new(),
    );
    let shapes = sha_tables.component_shapes();
    assert!(!shapes.is_empty(), "shared SHA tables must expose shapes");
    // The split-pack producers commit at LOG_SIZE_16 (real) → 17 (blinded); the
    // small range tables (Range2/4/5) are padded to 2^LOG_N_LANES = 2^4 (real) →
    // 5 (blinded); Range16 is 2^16 → 17. Under Class D every committed domain is
    // exactly one log above its real width, so every shape's log_size is the
    // blinded size {5, 17}. Assert each is blinded (never a bare real size).
    for shape in &shapes {
        assert!(
            shape.log_size == 5 || shape.log_size == 17,
            "shared SHA-table component {} log_size {} is not a Class-D blinded (real+1) size",
            shape.name,
            shape.log_size,
        );
    }
    // Explicit per-kind check that the blinded range widths are exactly real+1.
    for &kind in RANGE_TABLES {
        let real = stwo_sha256::components::range_log_size(kind);
        let blind = real + 1;
        assert!(
            shapes
                .iter()
                .any(|s| s.name.contains(kind.tag()) && s.log_size == blind),
            "range {kind:?} must appear at its blinded log size {blind}",
        );
    }

    // (2) Two same-credential product proofs differ (fresh SHA + bridge dummy
    // multiplicities) and both verify.
    let (extracted, statement) = ts13_class_d_revocation_case();
    let first = prove_mdoc_circuit(&extracted, &statement).expect("first product proof proves");
    verify_mdoc_circuit(&first, &statement).expect("first product proof verifies");
    let second = prove_mdoc_circuit(&extracted, &statement).expect("second product proof proves");
    verify_mdoc_circuit(&second, &statement).expect("second product proof verifies");

    let first_bytes = bincode::serialize(&first).expect("first product proof serializes");
    let second_bytes = bincode::serialize(&second).expect("second product proof serializes");
    assert_ne!(
        first_bytes, second_bytes,
        "same-credential product proofs must differ (fresh Class-D SHA-table blind multiplicities)",
    );
}
