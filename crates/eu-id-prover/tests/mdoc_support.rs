use ecdsa::signature::Signer;
use p256::ecdsa::{Signature as P256Signature, SigningKey};
use sha2::{Digest as _, Sha256};

use ciborium::value::Value;
use eu_id_prover::mdoc::{
    demo_mdoc_sizing_waste, extract_pid_mdoc, prove_mdoc_circuit, verify_mdoc_circuit,
    MdocCircuitStatement, MdocError, MdocPidRequest,
};
use eu_id_prover::{Date, Policy};
use stwo_p256::types::{AffinePoint, Signature, U256};

const DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const BIRTH_DATE: &str = "birth_date";
const NATIONALITY: &str = "nationality";
const PROTECTED_ES256: &[u8] = &[0xA1, 0x01, 0x26];
const PHASE_0B_REFACTOR_THRESHOLD_CELLS: u64 = 1_000_000;

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
    value_last: bool,
    protected: Vec<u8>,
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
            value_last: false,
            protected: PROTECTED_ES256.to_vec(),
            device_unprotected: map(Vec::new()),
            extra_device_key_field: false,
            mso_version: "1.0".to_string(),
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
    value_last: bool,
) -> Vec<u8> {
    let entries = if value_last {
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
        options.value_last,
    );
    let nationality_item = issuer_signed_item(
        options.nationality_item_digest_id,
        NATIONALITY,
        nationality_value,
        options.nationality_random,
        options.tag24_bstr,
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

    let (issuer_auth, issuer_sig_structure, issuer_signature) = cose_sign1(
        &issuer_signing_key,
        &options.protected,
        map(vec![("issuerKey".into(), issuer_cose_key)]),
        &mso,
    );
    let (device_signature_cose, device_sig_structure, device_signature) = cose_sign1(
        &device_signing_key,
        &options.protected,
        options.device_unprotected,
        session_transcript,
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
    MdocPidRequest {
        doctype: DOCTYPE.to_string(),
        namespace: NAMESPACE.to_string(),
        birth_date_element: BIRTH_DATE.to_string(),
        nationality_element: NATIONALITY.to_string(),
        session_transcript,
    }
}

fn policy_on(year: u32, month: u32, day: u32) -> Policy {
    Policy {
        current_date: Date { year, month, day },
        min_age_years: 18,
        accepted_nationalities: vec![276, 250],
    }
}

#[test]
fn extracts_pid_items_mso_device_key_and_signatures() {
    let session_transcript = b"session-transcript-123".to_vec();
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
    let session_transcript = b"session-transcript-123".to_vec();
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
    let fixture = valid_fixture(b"session-transcript-123");

    let err = extract_pid_mdoc(&fixture.doc, &request(b"session-transcript-456".to_vec()))
        .expect_err("wrong transcript rejects");

    assert!(matches!(err, MdocError::DeviceAuthPayloadMismatch));
}

#[test]
fn rejects_wrong_requested_doctype() {
    let session_transcript = b"session-transcript-123".to_vec();
    let fixture = valid_fixture(&session_transcript);
    let mut request = request(session_transcript);
    request.doctype = "wrong.doctype".to_string();

    let err = extract_pid_mdoc(&fixture.doc, &request).expect_err("wrong doctype rejects");

    assert!(matches!(err, MdocError::DoctypeMismatch));
}

#[test]
fn rejects_non_profile_requested_namespace() {
    let session_transcript = b"session-transcript-123".to_vec();
    let fixture = valid_fixture(&session_transcript);
    let mut request = request(session_transcript);
    request.namespace = "wrong.namespace".to_string();

    let err = extract_pid_mdoc(&fixture.doc, &request).expect_err("non-profile namespace rejects");

    assert_eq!(err, MdocError::NamespaceMissing);
}

#[test]
fn rejects_non_bstr_tag24() {
    let session_transcript = b"session-transcript-123".to_vec();
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
    let session_transcript = b"session-transcript-123".to_vec();
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
    let session_transcript = b"session-transcript-123".to_vec();
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
fn rejects_issuer_signed_item_key_order() {
    let session_transcript = b"session-transcript-123".to_vec();
    let options = FixtureOptions {
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
        .expect_err("key order rejects");

    assert_eq!(
        err,
        MdocError::UnsupportedCircuitValue("IssuerSignedItem key order")
    );
}

#[test]
fn rejects_digest_id_over_u32() {
    let session_transcript = b"session-transcript-123".to_vec();
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
    let session_transcript = b"session-transcript-123".to_vec();
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
    let session_transcript = b"session-transcript-123".to_vec();
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
    let session_transcript = b"session-transcript-123".to_vec();
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
    let session_transcript = b"session-transcript-123".to_vec();
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
    let session_transcript = b"session-transcript-123".to_vec();
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
fn rejects_mso_version_mismatch() {
    let session_transcript = b"session-transcript-123".to_vec();
    let options = FixtureOptions {
        mso_version: "2.0".to_string(),
        ..FixtureOptions::default()
    };
    let fixture = fixture_with_options(
        &session_transcript,
        "1990-07-15".into(),
        "DE".into(),
        options,
    );

    let err = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect_err("MSO version mismatch rejects");

    assert_eq!(err, MdocError::UnsupportedMsoVersion("2.0".to_string()));
}

#[test]
fn statement_rejects_expired_credential() {
    let session_transcript = b"session-transcript-123".to_vec();
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
    let session_transcript = b"session-transcript-123".to_vec();
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
fn statement_rejects_text_birth_date() {
    let session_transcript = b"session-transcript-123".to_vec();
    let fixture = valid_fixture(&session_transcript);
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("text birth date extracts for review");

    let err = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect_err("text birth date rejects for circuit");

    assert_eq!(
        err,
        MdocError::UnsupportedCircuitValue("element value bytes at offset")
    );
}

#[test]
fn statement_rejects_text_nationality() {
    let session_transcript = b"session-transcript-123".to_vec();
    let fixture = fixture_with_options(
        &session_transcript,
        Value::Bytes(vec![0x07, 0xC6, 7, 15]),
        "DE".into(),
        FixtureOptions::default(),
    );
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("text nationality extracts for review");

    let err = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect_err("text nationality rejects for circuit");

    assert_eq!(
        err,
        MdocError::UnsupportedCircuitValue("element value bytes at offset")
    );
}

#[test]
fn statement_rejects_value_window_past_first_block() {
    let session_transcript = b"session-transcript-123".to_vec();
    let fixture = circuit_fixture(&session_transcript);
    let mut extracted =
        extract_pid_mdoc(&fixture.doc, &request(session_transcript)).expect("binary mdoc extracts");
    extracted.birth_date_value_offset = 65;

    let err = MdocCircuitStatement::from_extracted(&extracted, policy_on(2026, 7, 3))
        .expect_err("block-1 value window rejects");

    assert_eq!(
        err,
        MdocError::UnsupportedCircuitValue("value window must lie in first SHA-256 block")
    );
}

#[test]
#[ignore = "slow: proves isolated mdoc circuit profile"]
fn isolated_mdoc_circuit_profile_proves_and_verifies() {
    let session_transcript = b"session-transcript-123".to_vec();
    let fixture = circuit_fixture(&session_transcript);
    let extracted = extract_pid_mdoc(&fixture.doc, &request(session_transcript))
        .expect("circuit profile mdoc extracts");
    let policy = policy_on(2026, 7, 3);
    let statement =
        MdocCircuitStatement::from_extracted(&extracted, policy).expect("statement builds");

    let proof = prove_mdoc_circuit(&extracted, &statement).expect("mdoc circuit proves");

    verify_mdoc_circuit(&proof, &statement).expect("mdoc circuit verifies");
}
