use ecdsa::signature::Signer;
use p256::ecdsa::{Signature as P256Signature, SigningKey};
use p256::pkcs8::DecodePrivateKey;
use sha2::{Digest as _, Sha256};
use std::time::Instant;

use ciborium::value::Value;
use eu_id_prover::mdoc::{
    demo_mdoc_sizing_waste, device_authentication_bytes, device_authentication_sig_structure_hash,
    extract_pid_mdoc, mdoc_proof_byte_breakdown, openid4vp_session_transcript, prove_mdoc_circuit,
    verify_mdoc_circuit, MdocBirthDateBinding, MdocCircuitStatement, MdocError,
    MdocNationalityBinding, MdocPidRequest,
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
struct FixtureOptions {
    birth_item_digest_id: u64,
    nationality_item_digest_id: u64,
    birth_mso_digest_id: u64,
    nationality_mso_digest_id: u64,
    birth_digest_override: Option<[u8; 32]>,
    birth_random: Vec<u8>,
    nationality_random: Vec<u8>,
    tag24_bstr: bool,
    canonical_item_order: bool,
    value_last: bool,
    protected: Vec<u8>,
    issuer_unprotected: Option<Value>,
    device_unprotected: Value,
    extra_device_key_field: bool,
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
            tag24_bstr: true,
            canonical_item_order: true,
            value_last: false,
            protected: PROTECTED_ES256.to_vec(),
            issuer_unprotected: None,
            device_unprotected: map(Vec::new()),
            extra_device_key_field: false,
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
    let mut birth_digest: [u8; 32] = Sha256::digest(&birth_date_item).into();
    if let Some(override_digest) = options.birth_digest_override {
        birth_digest = override_digest;
    }
    let nat_digest: [u8; 32] = Sha256::digest(&nationality_item).into();

    let mut mso_entries = vec![
        ("version".into(), options.mso_version.into()),
        ("docType".into(), options.mso_doctype.into()),
        ("digestAlgorithm".into(), "SHA-256".into()),
        (
            "valueDigests".into(),
            map(vec![(
                NAMESPACE.into(),
                map(vec![
                    (
                        Value::from(options.birth_mso_digest_id),
                        Value::Bytes(birth_digest.to_vec()),
                    ),
                    (
                        Value::from(options.nationality_mso_digest_id),
                        Value::Bytes(nat_digest.to_vec()),
                    ),
                ]),
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
    let device_auth_payload =
        device_authentication_bytes(session_transcript, DOCTYPE).expect("device auth bytes");
    let (device_signature_cose, device_sig_structure, device_signature) = cose_sign1(
        &device_signing_key,
        &options.protected,
        options.device_unprotected,
        &device_auth_payload,
    );

    let doc = cbor(map(vec![
        ("docType".into(), DOCTYPE.into()),
        (
            "issuerSigned".into(),
            map(vec![
                (
                    "nameSpaces".into(),
                    map(vec![(
                        NAMESPACE.into(),
                        Value::Array(vec![
                            Value::Bytes(birth_date_item.clone()),
                            Value::Bytes(nationality_item.clone()),
                        ]),
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
