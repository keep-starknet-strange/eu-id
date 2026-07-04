//! Isolated host-side EUID mdoc profile v1 support.
//!
//! This module parses the frozen isolated PID mdoc profile into reviewable
//! witness material. It intentionally does not call the current identity proof
//! APIs; integration into that flow is a later explicit step.

use std::collections::HashMap;

use air_core::relations::{field_id, SharedDigestRelation, SharedFieldRelation};
use air_core::{Air, AirProver, TreeLayout};
use ciborium::value::Value;
use ecdsa::signature::{Signer, Verifier};
use p256::ecdsa::{Signature as P256Signature, SigningKey, VerifyingKey};
use p256::EncodedPoint;
use predicates::nat::NationalityPredicate;
use predicates::{AgeRangeCheck, DateOfBirth, PredicateProver, PredicateVerifier};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;
use stwo_p256::components::digest_bind::module::{
    DigestBindInteractionClaim, DigestBindProver, DigestBindVerifier,
};
use stwo_p256::components::digest_bind::SharedScalarZRelation;
use stwo_p256::types::{AffinePoint, EcdsaVerifyInput, Signature, U256};
use stwo_p256::{
    proof::air::{P256Prover, P256Verifier},
    proof::{P256CurrentAirInteractionClaim, P256CurrentAirProofClaim, P256ProofDraft},
    public_inputs::PublicEcdsaInstance,
};
use stwo_sha256::air::{Sha256Prover, Sha256Verifier};
use stwo_sha256::field_exposure::FieldExposure;
use stwo_sha256::interaction::InteractionClaim as Sha256InteractionClaim;
use stwo_sha256::trace::min_log_size;
use stwo_sha256::witness::compute_sha256_witness;

use crate::generator::{Policy, SHA_GROUP_WIDTH};
use crate::public_digest_bind::{PublicDigestBind, PublicDigestBindInteractionClaim};
use crate::Error;

const MDOC_PROFILE_VERSION: &str = "1.0";
const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const ES256_PROTECTED_HEADER: &[u8] = &[0xA1, 0x01, 0x26];
const SHA256_FIRST_BLOCK_LEN: usize = 64;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MdocPidRequest {
    pub doctype: String,
    pub namespace: String,
    pub birth_date_element: String,
    pub nationality_element: String,
    pub session_transcript: Vec<u8>,
}

#[derive(Clone, Debug)]
pub struct ExtractedPidMdoc {
    pub doctype: String,
    pub namespace: String,
    pub birth_date: String,
    pub nationalities: Vec<u32>,
    pub birth_date_bytes: [u8; 4],
    pub nationality_bytes: [u8; 2],
    pub birth_date_value_offset: usize,
    pub nationality_value_offset: usize,
    pub signed_at: (u16, u8, u8),
    pub valid_from: (u16, u8, u8),
    pub valid_until: (u16, u8, u8),
    pub digest_ids: HashMap<String, u32>,
    pub birth_date_item: Vec<u8>,
    pub nationality_item: Vec<u8>,
    pub mso: Vec<u8>,
    pub issuer_key: AffinePoint,
    pub device_key: AffinePoint,
    pub issuer_signature: Signature,
    pub device_signature: Signature,
    pub issuer_sig_structure: Vec<u8>,
    pub device_sig_structure: Vec<u8>,
    pub issuer_ecdsa_input: EcdsaVerifyInput,
    pub device_ecdsa_input: EcdsaVerifyInput,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MdocError {
    Cbor(String),
    MissingField(&'static str),
    WrongType(&'static str),
    DoctypeMismatch,
    NamespaceMissing,
    ElementMissing(String),
    UnsupportedDigestAlgorithm(String),
    ItemDigestMismatch { element: String, digest_id: u32 },
    DeviceAuthPayloadMismatch,
    InvalidCoseKey(&'static str),
    InvalidCoseSign1(&'static str),
    InvalidSignature(&'static str),
    InvalidNationality(String),
    UnsupportedCircuitValue(&'static str),
    UnsupportedMsoVersion(String),
    InvalidTdate(&'static str),
    CredentialNotYetValid,
    CredentialExpired,
    SaltTooShort { len: usize },
}

#[derive(Clone, Debug)]
pub struct DemoMdocCircuitFixture {
    pub extracted: ExtractedPidMdoc,
    pub statement: MdocCircuitStatement,
}

pub struct MdocModuleShape {
    pub name: &'static str,
    pub layout: TreeLayout,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MdocShaSizingWaste {
    pub name: &'static str,
    pub natural_log: u32,
    pub shared_log: u32,
    pub wasted_cells: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MdocSizingWaste {
    pub sha: Vec<MdocShaSizingWaste>,
    pub sha_wasted_cells: u64,
    pub p256_namespaced_identical_preprocessed_cells: u64,
}

impl MdocSizingWaste {
    pub fn combined_wasted_cells(&self) -> u64 {
        self.sha_wasted_cells + self.p256_namespaced_identical_preprocessed_cells
    }
}

/// Deterministic EUID mdoc profile-v1 fixture used by benches and FFI timing.
pub fn demo_mdoc_circuit_fixture() -> DemoMdocCircuitFixture {
    let session_transcript = b"session-transcript-123".to_vec();
    let document = demo_mdoc_document(&session_transcript);
    let request = MdocPidRequest {
        doctype: PID_DOCTYPE.to_string(),
        namespace: PID_NAMESPACE.to_string(),
        birth_date_element: "birth_date".to_string(),
        nationality_element: "nationality".to_string(),
        session_transcript,
    };
    let extracted = extract_pid_mdoc(&document, &request).expect("demo mdoc extracts");
    let statement = MdocCircuitStatement::from_extracted(
        &extracted,
        Policy {
            current_date: predicates::Date {
                year: 2026,
                month: 7,
                day: 3,
            },
            min_age_years: 18,
            accepted_nationalities: vec![276, 250],
        },
    )
    .expect("demo mdoc statement builds");
    DemoMdocCircuitFixture {
        extracted,
        statement,
    }
}

pub fn demo_mdoc_module_shapes() -> Result<Vec<MdocModuleShape>, Error> {
    let fixture = demo_mdoc_circuit_fixture();
    let extracted = &fixture.extracted;
    let statement = &fixture.statement;

    let issuer_draft = single_p256_draft(statement.issuer_input.clone())?;
    let device_draft = single_p256_draft(statement.device_input.clone())?;
    let (issuer_sha_witness, issuer_sha_log) = sha_params(&extracted.issuer_sig_structure);
    let (device_sha_witness, device_sha_log) = sha_params(&extracted.device_sig_structure);
    let (birth_sha_witness, birth_sha_log) = sha_params(&extracted.birth_date_item);
    let (nat_sha_witness, nat_sha_log) = sha_params(&extracted.nationality_item);
    let shared_sha_log = [issuer_sha_log, device_sha_log, birth_sha_log, nat_sha_log]
        .into_iter()
        .max()
        .expect("sha log list is non-empty");
    let issuer_scalar_z = SharedScalarZRelation::new();
    let issuer_digest = SharedDigestRelation::new();
    let device_scalar_z = SharedScalarZRelation::new();
    let device_digest = SharedDigestRelation::new();
    let birth_digest = SharedDigestRelation::new();
    let nat_digest = SharedDigestRelation::new();
    let birth_field = SharedFieldRelation::new();
    let nat_field = SharedFieldRelation::new();

    let birth_exposure = FieldExposure::from_preimage_windows(&[(
        field_id::DOB,
        statement.birth_date_value_offset,
        4,
    )]);
    let nat_exposure = FieldExposure::from_preimage_windows(&[(
        field_id::NATIONALITY,
        statement.nationality_value_offset,
        2,
    )]);

    let issuer_p256 = P256Prover::new(&issuer_draft)
        .map_err(Error::P256Prepare)?
        .with_z_binding(issuer_scalar_z.clone());
    let device_p256 = P256Prover::new(&device_draft)
        .map_err(Error::P256Prepare)?
        .with_preprocessed_namespace("mdoc/device")
        .with_z_binding(device_scalar_z.clone());
    let issuer_sha = Sha256Prover::new(&issuer_sha_witness, shared_sha_log, SHA_GROUP_WIDTH)
        .with_digest_handle(issuer_digest.clone());
    let device_sha = Sha256Prover::new(&device_sha_witness, shared_sha_log, SHA_GROUP_WIDTH)
        .with_digest_handle(device_digest.clone());
    let birth_sha = Sha256Prover::new(&birth_sha_witness, shared_sha_log, SHA_GROUP_WIDTH)
        .with_digest_handle(birth_digest.clone())
        .with_field_handle(birth_exposure, birth_field.clone());
    let nat_sha = Sha256Prover::new(&nat_sha_witness, shared_sha_log, SHA_GROUP_WIDTH)
        .with_digest_handle(nat_digest.clone())
        .with_field_handle(nat_exposure, nat_field.clone());

    let issuer_bridge_rows = crate::bridge_rows(&issuer_p256.proof_claim().public_inputs.instances);
    let issuer_bridge_log = crate::bridge_log_size(issuer_bridge_rows.len());
    let issuer_bridge = DigestBindProver::new(
        issuer_bridge_rows,
        issuer_bridge_log,
        issuer_scalar_z,
        issuer_digest.clone(),
    );
    let device_bridge_rows = crate::bridge_rows(&device_p256.proof_claim().public_inputs.instances);
    let device_bridge_log = crate::bridge_log_size(device_bridge_rows.len());
    let device_bridge = DigestBindProver::new(
        device_bridge_rows,
        device_bridge_log,
        device_scalar_z,
        device_digest.clone(),
    );
    let birth_digest_bind = PublicDigestBind::new(statement.birth_date_digest, birth_digest);
    let nat_digest_bind = PublicDigestBind::new(statement.nationality_digest, nat_digest);

    let age_public = statement.policy.age_public_input();
    let nat_public = statement.policy.nat_public_input();
    let age_dob = DateOfBirth(predicates::Date {
        year: u32::from(u16::from_be_bytes([
            extracted.birth_date_bytes[0],
            extracted.birth_date_bytes[1],
        ])),
        month: u32::from(extracted.birth_date_bytes[2]),
        day: u32::from(extracted.birth_date_bytes[3]),
    });
    let nat_code = u32::from(u16::from_be_bytes(extracted.nationality_bytes));
    let nat_private = predicates::NatPrivateInput {
        nationalities: vec![nat_code],
    };
    let age = AgeRangeCheck::new(PcsConfig::default())
        .prover(&age_public, &age_dob)
        .map_err(Error::AgePrepare)?
        .with_dob_binding(birth_field);
    let nat = NationalityPredicate::new(PcsConfig::default())
        .prover(&nat_public, &nat_private)
        .map_err(Error::NatPrepare)?
        .with_nat_binding(nat_field);

    Ok(vec![
        MdocModuleShape {
            name: "mdoc_issuer_p256",
            layout: issuer_p256.layout(),
        },
        MdocModuleShape {
            name: "mdoc_issuer_sha",
            layout: issuer_sha.layout(),
        },
        MdocModuleShape {
            name: "mdoc_issuer_bridge",
            layout: issuer_bridge.layout(),
        },
        MdocModuleShape {
            name: "mdoc_device_p256",
            layout: device_p256.layout(),
        },
        MdocModuleShape {
            name: "mdoc_device_sha",
            layout: device_sha.layout(),
        },
        MdocModuleShape {
            name: "mdoc_device_bridge",
            layout: device_bridge.layout(),
        },
        MdocModuleShape {
            name: "mdoc_birth_sha",
            layout: birth_sha.layout(),
        },
        MdocModuleShape {
            name: "mdoc_birth_digest_bind",
            layout: birth_digest_bind.layout(),
        },
        MdocModuleShape {
            name: "mdoc_nat_sha",
            layout: nat_sha.layout(),
        },
        MdocModuleShape {
            name: "mdoc_nat_digest_bind",
            layout: nat_digest_bind.layout(),
        },
        MdocModuleShape {
            name: "mdoc_age",
            layout: age.layout(),
        },
        MdocModuleShape {
            name: "mdoc_nat",
            layout: nat.layout(),
        },
    ])
}

pub fn demo_mdoc_sizing_waste() -> Result<MdocSizingWaste, Error> {
    let fixture = demo_mdoc_circuit_fixture();
    mdoc_sizing_waste(&fixture.extracted, &fixture.statement)
}

pub fn extract_pid_mdoc(
    document: &[u8],
    request: &MdocPidRequest,
) -> Result<ExtractedPidMdoc, MdocError> {
    if request.doctype != PID_DOCTYPE {
        return Err(MdocError::DoctypeMismatch);
    }
    if request.namespace != PID_NAMESPACE {
        return Err(MdocError::NamespaceMissing);
    }
    let doc = decode_value(document)?;
    let doc_map = expect_map(&doc, "document")?;
    let doctype = text_field(doc_map, "docType")?.to_string();
    if doctype != PID_DOCTYPE || doctype != request.doctype {
        return Err(MdocError::DoctypeMismatch);
    }

    let issuer_signed = map_field(doc_map, "issuerSigned")?;
    let issuer_auth = parse_cose_sign1(value_field(issuer_signed, "issuerAuth")?)?;
    let issuer_key = parse_cose_key(value_field(
        expect_map(&issuer_auth.unprotected, "issuerAuth.unprotected")?,
        "issuerKey",
    )?)?;
    verify_signature(
        &issuer_key,
        &issuer_auth.sig_structure,
        &issuer_auth.signature_bytes,
        "issuerAuth",
    )?;

    let mso = parse_mso(&issuer_auth.payload, &request.namespace)?;
    if mso.version != MDOC_PROFILE_VERSION {
        return Err(MdocError::UnsupportedMsoVersion(mso.version));
    }
    if mso.doc_type != request.doctype {
        return Err(MdocError::DoctypeMismatch);
    }
    let device_key = mso.device_key;

    let namespace_items = namespace_items(issuer_signed, &request.namespace)?;
    let birth_date_item = find_item(namespace_items, &request.birth_date_element)?
        .ok_or_else(|| MdocError::ElementMissing(request.birth_date_element.clone()))?;
    let nationality_item = find_item(namespace_items, &request.nationality_element)?
        .ok_or_else(|| MdocError::ElementMissing(request.nationality_element.clone()))?;

    let parsed_birth = parse_birth_date_value(&birth_date_item)?;
    let parsed_nat = parse_nationality_value(&nationality_item)?;

    validate_item_digest(
        &mso.value_digests,
        &request.birth_date_element,
        birth_date_item.digest_id,
        &birth_date_item.bytes,
    )?;
    validate_item_digest(
        &mso.value_digests,
        &request.nationality_element,
        nationality_item.digest_id,
        &nationality_item.bytes,
    )?;

    let device_signed = map_field(doc_map, "deviceSigned")?;
    let device_auth = map_field(device_signed, "deviceAuth")?;
    let device_signature = parse_cose_sign1(value_field(device_auth, "deviceSignature")?)?;
    if device_signature.payload != request.session_transcript {
        return Err(MdocError::DeviceAuthPayloadMismatch);
    }
    verify_signature(
        &device_key,
        &device_signature.sig_structure,
        &device_signature.signature_bytes,
        "deviceSignature",
    )?;

    let mut digest_ids = HashMap::new();
    digest_ids.insert(
        request.birth_date_element.clone(),
        birth_date_item.digest_id,
    );
    digest_ids.insert(
        request.nationality_element.clone(),
        nationality_item.digest_id,
    );

    let issuer_signature = signature_from_compact(&issuer_auth.signature_bytes)?;
    let device_signature_value = signature_from_compact(&device_signature.signature_bytes)?;
    let issuer_ecdsa_input = ecdsa_input(
        &issuer_auth.sig_structure,
        issuer_signature.clone(),
        issuer_key.clone(),
    );
    let device_ecdsa_input = ecdsa_input(
        &device_signature.sig_structure,
        device_signature_value.clone(),
        device_key.clone(),
    );

    Ok(ExtractedPidMdoc {
        doctype,
        namespace: request.namespace.clone(),
        birth_date: parsed_birth.display,
        nationalities: vec![parsed_nat.numeric],
        birth_date_bytes: parsed_birth.bytes,
        nationality_bytes: parsed_nat.bytes,
        birth_date_value_offset: parsed_birth.offset,
        nationality_value_offset: parsed_nat.offset,
        signed_at: mso.signed_at,
        valid_from: mso.valid_from,
        valid_until: mso.valid_until,
        digest_ids,
        birth_date_item: birth_date_item.bytes,
        nationality_item: nationality_item.bytes,
        mso: issuer_auth.payload,
        issuer_key,
        device_key,
        issuer_signature,
        device_signature: device_signature_value,
        issuer_sig_structure: issuer_auth.sig_structure,
        device_sig_structure: device_signature.sig_structure,
        issuer_ecdsa_input,
        device_ecdsa_input,
    })
}

#[derive(Clone)]
struct ParsedBirthDateValue {
    display: String,
    bytes: [u8; 4],
    offset: usize,
}

#[derive(Clone)]
struct ParsedNationalityValue {
    numeric: u32,
    bytes: [u8; 2],
    offset: usize,
}

#[derive(Clone)]
struct CoseSign1 {
    unprotected: Value,
    payload: Vec<u8>,
    signature_bytes: Vec<u8>,
    sig_structure: Vec<u8>,
}

struct ParsedMso {
    version: String,
    doc_type: String,
    value_digests: HashMap<u32, [u8; 32]>,
    device_key: AffinePoint,
    signed_at: (u16, u8, u8),
    valid_from: (u16, u8, u8),
    valid_until: (u16, u8, u8),
}

#[derive(Clone)]
struct ParsedItem {
    digest_id: u32,
    element: String,
    value: Value,
    bytes: Vec<u8>,
}

fn parse_birth_date_value(item: &ParsedItem) -> Result<ParsedBirthDateValue, MdocError> {
    match &item.value {
        Value::Text(text) => {
            let (year, month, day) = parse_birth_date_text(text)?;
            let display = text.clone();
            let value_bytes = text.as_bytes();
            let offset = find_subslice(&item.bytes, value_bytes)
                .ok_or(MdocError::UnsupportedCircuitValue("birth_date text offset"))?;
            Ok(ParsedBirthDateValue {
                display,
                bytes: [(year >> 8) as u8, (year & 0xFF) as u8, month, day],
                offset,
            })
        }
        Value::Bytes(bytes) => {
            let raw: [u8; 4] = bytes
                .as_slice()
                .try_into()
                .map_err(|_| MdocError::UnsupportedCircuitValue("birth_date binary length"))?;
            let year = u16::from_be_bytes([raw[0], raw[1]]);
            let month = raw[2];
            let day = raw[3];
            let offset = find_subslice(&item.bytes, &raw).ok_or(
                MdocError::UnsupportedCircuitValue("birth_date binary offset"),
            )?;
            Ok(ParsedBirthDateValue {
                display: format!("{year:04}-{month:02}-{day:02}"),
                bytes: raw,
                offset,
            })
        }
        _ => Err(MdocError::WrongType("birth_date elementValue")),
    }
}

fn parse_nationality_value(item: &ParsedItem) -> Result<ParsedNationalityValue, MdocError> {
    match &item.value {
        Value::Text(alpha2) => {
            let numeric = numeric_country(alpha2)?;
            let bytes = [(numeric >> 8) as u8, (numeric & 0xFF) as u8];
            let offset = find_subslice(&item.bytes, alpha2.as_bytes()).ok_or(
                MdocError::UnsupportedCircuitValue("nationality text offset"),
            )?;
            Ok(ParsedNationalityValue {
                numeric,
                bytes,
                offset,
            })
        }
        Value::Bytes(bytes) => {
            let raw: [u8; 2] = bytes
                .as_slice()
                .try_into()
                .map_err(|_| MdocError::UnsupportedCircuitValue("nationality binary length"))?;
            let numeric = u16::from_be_bytes(raw) as u32;
            let offset = find_subslice(&item.bytes, &raw).ok_or(
                MdocError::UnsupportedCircuitValue("nationality binary offset"),
            )?;
            Ok(ParsedNationalityValue {
                numeric,
                bytes: raw,
                offset,
            })
        }
        _ => Err(MdocError::WrongType("nationality elementValue")),
    }
}

fn parse_birth_date_text(text: &str) -> Result<(u16, u8, u8), MdocError> {
    let bytes = text.as_bytes();
    if bytes.len() != 10 || bytes[4] != b'-' || bytes[7] != b'-' {
        return Err(MdocError::UnsupportedCircuitValue(
            "birth_date text must be YYYY-MM-DD",
        ));
    }
    let year = parse_digits(&bytes[0..4])? as u16;
    let month = parse_digits(&bytes[5..7])? as u8;
    let day = parse_digits(&bytes[8..10])? as u8;
    Ok((year, month, day))
}

fn parse_digits(bytes: &[u8]) -> Result<u32, MdocError> {
    let mut value = 0u32;
    for &byte in bytes {
        if !byte.is_ascii_digit() {
            return Err(MdocError::UnsupportedCircuitValue("non-digit date byte"));
        }
        value = value * 10 + u32::from(byte - b'0');
    }
    Ok(value)
}

fn find_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() {
        return Some(0);
    }
    haystack
        .windows(needle.len())
        .position(|candidate| candidate == needle)
}

fn decode_value(bytes: &[u8]) -> Result<Value, MdocError> {
    ciborium::de::from_reader(bytes).map_err(|error| MdocError::Cbor(error.to_string()))
}

fn encode_value(value: Value) -> Vec<u8> {
    let mut out = Vec::new();
    ciborium::ser::into_writer(&value, &mut out).expect("CBOR serialization into Vec");
    out
}

fn parse_cose_sign1(value: &Value) -> Result<CoseSign1, MdocError> {
    let Value::Array(items) = value else {
        return Err(MdocError::WrongType("COSE_Sign1"));
    };
    if items.len() != 4 {
        return Err(MdocError::InvalidCoseSign1("expected four-element array"));
    }

    let protected = expect_bytes(&items[0], "COSE_Sign1.protected")?.to_vec();
    if protected != ES256_PROTECTED_HEADER {
        return Err(MdocError::InvalidCoseSign1(
            "protected header must be ES256",
        ));
    }
    expect_map(&items[1], "COSE_Sign1.unprotected")?;
    let unprotected = items[1].clone();
    let payload = expect_bytes(&items[2], "COSE_Sign1.payload")?.to_vec();
    let signature_bytes = expect_bytes(&items[3], "COSE_Sign1.signature")?.to_vec();
    signature_from_compact(&signature_bytes)?;
    let sig_structure = sig_structure(&protected, &payload);

    Ok(CoseSign1 {
        unprotected,
        payload,
        signature_bytes,
        sig_structure,
    })
}

fn sig_structure(protected: &[u8], payload: &[u8]) -> Vec<u8> {
    encode_value(Value::Array(vec![
        "Signature1".into(),
        Value::Bytes(protected.to_vec()),
        Value::Bytes(Vec::new()),
        Value::Bytes(payload.to_vec()),
    ]))
}

fn demo_mdoc_document(session_transcript: &[u8]) -> Vec<u8> {
    let issuer_signing_key =
        SigningKey::from_bytes((&[7u8; 32]).into()).expect("demo issuer signing key");
    let device_signing_key =
        SigningKey::from_bytes((&[11u8; 32]).into()).expect("demo device signing key");
    let issuer_cose_key = demo_cose_key(&issuer_signing_key);
    let device_cose_key = demo_cose_key(&device_signing_key);

    let birth_date_item = demo_issuer_signed_item(
        7,
        "birth_date",
        Value::Bytes(vec![0x07, 0xC6, 7, 15]),
        vec![7; 16],
    );
    let nationality_item = demo_issuer_signed_item(
        9,
        "nationality",
        Value::Bytes(276u16.to_be_bytes().to_vec()),
        vec![9; 16],
    );
    let birth_digest: [u8; 32] = Sha256::digest(&birth_date_item).into();
    let nat_digest: [u8; 32] = Sha256::digest(&nationality_item).into();

    let mso = encode_value(Value::Map(vec![
        ("version".into(), MDOC_PROFILE_VERSION.into()),
        ("docType".into(), PID_DOCTYPE.into()),
        ("digestAlgorithm".into(), "SHA-256".into()),
        (
            "valueDigests".into(),
            Value::Map(vec![(
                PID_NAMESPACE.into(),
                Value::Map(vec![
                    (Value::from(7), Value::Bytes(birth_digest.to_vec())),
                    (Value::from(9), Value::Bytes(nat_digest.to_vec())),
                ]),
            )]),
        ),
        (
            "deviceKeyInfo".into(),
            Value::Map(vec![("deviceKey".into(), device_cose_key)]),
        ),
        (
            "validityInfo".into(),
            Value::Map(vec![
                ("signed".into(), demo_tdate("2026-01-01T00:00:00Z")),
                ("validFrom".into(), demo_tdate("2026-01-01T00:00:00Z")),
                ("validUntil".into(), demo_tdate("2030-01-01T00:00:00Z")),
            ]),
        ),
    ]));

    let issuer_auth = demo_cose_sign1(
        &issuer_signing_key,
        Value::Map(vec![("issuerKey".into(), issuer_cose_key)]),
        &mso,
    );
    let device_signature = demo_cose_sign1(
        &device_signing_key,
        Value::Map(Vec::new()),
        session_transcript,
    );

    encode_value(Value::Map(vec![
        ("docType".into(), PID_DOCTYPE.into()),
        (
            "issuerSigned".into(),
            Value::Map(vec![
                (
                    "nameSpaces".into(),
                    Value::Map(vec![(
                        PID_NAMESPACE.into(),
                        Value::Array(vec![
                            Value::Bytes(birth_date_item),
                            Value::Bytes(nationality_item),
                        ]),
                    )]),
                ),
                ("issuerAuth".into(), issuer_auth),
            ]),
        ),
        (
            "deviceSigned".into(),
            Value::Map(vec![(
                "deviceAuth".into(),
                Value::Map(vec![("deviceSignature".into(), device_signature)]),
            )]),
        ),
    ]))
}

fn demo_cose_key(signing_key: &SigningKey) -> Value {
    let encoded = signing_key.verifying_key().to_encoded_point(false);
    let x: [u8; 32] = encoded.x().expect("demo key has x coordinate")[..]
        .try_into()
        .expect("demo x coordinate length");
    let y: [u8; 32] = encoded.y().expect("demo key has y coordinate")[..]
        .try_into()
        .expect("demo y coordinate length");
    Value::Map(vec![
        (Value::from(1), Value::from(2)),
        (Value::from(3), Value::from(-7)),
        (Value::from(-1), Value::from(1)),
        (Value::from(-2), Value::Bytes(x.to_vec())),
        (Value::from(-3), Value::Bytes(y.to_vec())),
    ])
}

fn demo_issuer_signed_item(
    digest_id: u64,
    element: &str,
    value: Value,
    random: Vec<u8>,
) -> Vec<u8> {
    let item = Value::Map(vec![
        ("elementValue".into(), value),
        ("digestID".into(), Value::from(digest_id)),
        ("random".into(), Value::Bytes(random)),
        ("elementIdentifier".into(), element.into()),
    ]);
    encode_value(Value::Tag(24, Box::new(Value::Bytes(encode_value(item)))))
}

fn demo_tdate(text: &str) -> Value {
    Value::Tag(0, Box::new(text.into()))
}

fn demo_cose_sign1(signing_key: &SigningKey, unprotected: Value, payload: &[u8]) -> Value {
    let sig_structure = sig_structure(ES256_PROTECTED_HEADER, payload);
    let signature: P256Signature = signing_key.sign(&sig_structure);
    let mut compact = Vec::with_capacity(64);
    compact.extend_from_slice(&signature.r().to_bytes());
    compact.extend_from_slice(&signature.s().to_bytes());
    Value::Array(vec![
        Value::Bytes(ES256_PROTECTED_HEADER.to_vec()),
        unprotected,
        Value::Bytes(payload.to_vec()),
        Value::Bytes(compact),
    ])
}

fn parse_mso(bytes: &[u8], namespace: &str) -> Result<ParsedMso, MdocError> {
    let value = decode_value(bytes)?;
    let mso = expect_map(&value, "MobileSecurityObject")?;
    let version = text_field(mso, "version")?.to_string();
    let doc_type = text_field(mso, "docType")?.to_string();
    let digest_algorithm = text_field(mso, "digestAlgorithm")?;
    if digest_algorithm != "SHA-256" {
        return Err(MdocError::UnsupportedDigestAlgorithm(
            digest_algorithm.to_string(),
        ));
    }

    let value_digests = map_field(mso, "valueDigests")?;
    let namespace_digests = value_digests
        .iter()
        .find_map(|(key, value)| (key == &Value::Text(namespace.to_string())).then_some(value))
        .ok_or(MdocError::NamespaceMissing)?;
    let namespace_digests = expect_map(namespace_digests, "valueDigests namespace")?;
    let mut digests = HashMap::new();
    for (key, value) in namespace_digests {
        let digest_id = expect_u32(key, "digestID")?;
        let digest = expect_digest(value, "elementDigest")?;
        digests.insert(digest_id, digest);
    }

    let device_key_info = map_field(mso, "deviceKeyInfo")?;
    let device_key = parse_cose_key(value_field(device_key_info, "deviceKey")?)?;
    let validity_info = map_field(mso, "validityInfo")?;
    let signed_at = parse_tdate(value_field(validity_info, "signed")?, "validityInfo.signed")?;
    let valid_from = parse_tdate(
        value_field(validity_info, "validFrom")?,
        "validityInfo.validFrom",
    )?;
    let valid_until = parse_tdate(
        value_field(validity_info, "validUntil")?,
        "validityInfo.validUntil",
    )?;

    Ok(ParsedMso {
        version,
        doc_type,
        value_digests: digests,
        device_key,
        signed_at,
        valid_from,
        valid_until,
    })
}

fn parse_tdate(value: &Value, field: &'static str) -> Result<(u16, u8, u8), MdocError> {
    let Value::Tag(0, inner) = value else {
        return Err(MdocError::InvalidTdate(field));
    };
    let text = expect_text(inner, field).map_err(|_| MdocError::InvalidTdate(field))?;
    let bytes = text.as_bytes();
    if bytes.len() != 20
        || bytes[4] != b'-'
        || bytes[7] != b'-'
        || bytes[10] != b'T'
        || bytes[13] != b':'
        || bytes[16] != b':'
        || bytes[19] != b'Z'
    {
        return Err(MdocError::InvalidTdate(field));
    }
    let year = parse_tdate_digits(&bytes[0..4], field)? as u16;
    let month = parse_tdate_digits(&bytes[5..7], field)? as u8;
    let day = parse_tdate_digits(&bytes[8..10], field)? as u8;
    let hour = parse_tdate_digits(&bytes[11..13], field)? as u8;
    let minute = parse_tdate_digits(&bytes[14..16], field)? as u8;
    let second = parse_tdate_digits(&bytes[17..19], field)? as u8;
    if !(1..=12).contains(&month)
        || !(1..=31).contains(&day)
        || hour > 23
        || minute > 59
        || second > 59
    {
        return Err(MdocError::InvalidTdate(field));
    }
    Ok((year, month, day))
}

fn parse_tdate_digits(bytes: &[u8], field: &'static str) -> Result<u32, MdocError> {
    let mut value = 0u32;
    for &byte in bytes {
        if !byte.is_ascii_digit() {
            return Err(MdocError::InvalidTdate(field));
        }
        value = value * 10 + u32::from(byte - b'0');
    }
    Ok(value)
}

fn namespace_items<'a>(
    issuer_signed: &'a [(Value, Value)],
    namespace: &str,
) -> Result<&'a [Value], MdocError> {
    let namespaces = map_field(issuer_signed, "nameSpaces")?;
    let value = namespaces
        .iter()
        .find_map(|(key, value)| (key == &Value::Text(namespace.to_string())).then_some(value))
        .ok_or(MdocError::NamespaceMissing)?;
    let Value::Array(items) = value else {
        return Err(MdocError::WrongType("issuerSigned.nameSpaces namespace"));
    };
    Ok(items)
}

fn find_item(items: &[Value], element: &str) -> Result<Option<ParsedItem>, MdocError> {
    for item in items {
        let item_bytes = expect_bytes(item, "IssuerSignedItemBytes")?;
        let parsed = parse_issuer_signed_item_bytes(item_bytes)?;
        if parsed.element == element {
            return Ok(Some(parsed));
        }
    }
    Ok(None)
}

fn parse_issuer_signed_item_bytes(bytes: &[u8]) -> Result<ParsedItem, MdocError> {
    let value = decode_value(bytes)?;
    let Value::Tag(24, inner) = value else {
        return Err(MdocError::WrongType("IssuerSignedItemBytes tag 24"));
    };
    let item_bytes = expect_bytes(&inner, "IssuerSignedItemBytes")?;
    let item_value = decode_value(item_bytes)?;
    let item = expect_map(&item_value, "IssuerSignedItem")?;
    ensure_issuer_signed_item_key_order(item)?;
    let digest_id = u32_field(item, "digestID")?;
    let element = text_field(item, "elementIdentifier")?.to_string();
    let random_len = expect_bytes(value_field(item, "random")?, "random")?.len();
    if random_len < 16 {
        return Err(MdocError::SaltTooShort { len: random_len });
    }
    let value = value_field(item, "elementValue")?.clone();
    Ok(ParsedItem {
        digest_id,
        element,
        value,
        bytes: bytes.to_vec(),
    })
}

fn ensure_issuer_signed_item_key_order(item: &[(Value, Value)]) -> Result<(), MdocError> {
    const EXPECTED: [&str; 4] = ["elementValue", "digestID", "random", "elementIdentifier"];
    if item.len() != EXPECTED.len() {
        return Err(MdocError::UnsupportedCircuitValue(
            "IssuerSignedItem key order",
        ));
    }
    for ((key, _), expected) in item.iter().zip(EXPECTED) {
        if key != &Value::Text(expected.to_string()) {
            return Err(MdocError::UnsupportedCircuitValue(
                "IssuerSignedItem key order",
            ));
        }
    }
    Ok(())
}

fn validate_item_digest(
    digests: &HashMap<u32, [u8; 32]>,
    element: &str,
    digest_id: u32,
    item_bytes: &[u8],
) -> Result<(), MdocError> {
    let expected = digests
        .get(&digest_id)
        .ok_or_else(|| MdocError::ItemDigestMismatch {
            element: element.to_string(),
            digest_id,
        })?;
    let actual: [u8; 32] = Sha256::digest(item_bytes).into();
    if &actual != expected {
        return Err(MdocError::ItemDigestMismatch {
            element: element.to_string(),
            digest_id,
        });
    }
    Ok(())
}

fn parse_cose_key(value: &Value) -> Result<AffinePoint, MdocError> {
    let key = expect_map(value, "COSE_Key")?;
    if key.len() != 5 {
        return Err(MdocError::InvalidCoseKey("expected ES256 P-256 key"));
    }
    let kty = int_field(key, 1, "COSE_Key.kty")?;
    let alg = int_field(key, 3, "COSE_Key.alg")?;
    let crv = int_field(key, -1, "COSE_Key.crv")?;
    if kty != 2 || alg != -7 || crv != 1 {
        return Err(MdocError::InvalidCoseKey("expected ES256 P-256 key"));
    }
    let x = expect_32(bytes_int_field(key, -2, "COSE_Key.x")?, "COSE_Key.x")?;
    let y = expect_32(bytes_int_field(key, -3, "COSE_Key.y")?, "COSE_Key.y")?;
    Ok(AffinePoint {
        x: U256(x),
        y: U256(y),
    })
}

fn verify_signature(
    public_key: &AffinePoint,
    message: &[u8],
    signature: &[u8],
    label: &'static str,
) -> Result<(), MdocError> {
    let encoded = EncodedPoint::from_affine_coordinates(
        (&public_key.x.0).into(),
        (&public_key.y.0).into(),
        false,
    );
    let verifying_key = VerifyingKey::from_encoded_point(&encoded)
        .map_err(|_| MdocError::InvalidCoseKey("invalid P-256 public key point"))?;
    let signature = P256Signature::from_slice(signature)
        .map_err(|_| MdocError::InvalidCoseSign1("invalid compact P-256 signature"))?;
    verifying_key
        .verify(message, &signature)
        .map_err(|_| MdocError::InvalidSignature(label))
}

fn signature_from_compact(bytes: &[u8]) -> Result<Signature, MdocError> {
    if bytes.len() != 64 {
        return Err(MdocError::InvalidCoseSign1("P-256 signature must be r||s"));
    }
    let r: [u8; 32] = bytes[..32]
        .try_into()
        .map_err(|_| MdocError::InvalidCoseSign1("invalid r length"))?;
    let s: [u8; 32] = bytes[32..]
        .try_into()
        .map_err(|_| MdocError::InvalidCoseSign1("invalid s length"))?;
    Ok(Signature {
        r: U256(r),
        s: U256(s),
    })
}

fn ecdsa_input(
    sig_structure: &[u8],
    signature: Signature,
    public_key: AffinePoint,
) -> EcdsaVerifyInput {
    EcdsaVerifyInput {
        message_hash: U256(Sha256::digest(sig_structure).into()),
        signature,
        public_key,
    }
}

#[derive(Clone, Debug)]
pub struct MdocCircuitStatement {
    pub issuer_input: EcdsaVerifyInput,
    pub device_input: EcdsaVerifyInput,
    pub birth_date_digest: [u8; 32],
    pub nationality_digest: [u8; 32],
    pub birth_date_value_offset: usize,
    pub nationality_value_offset: usize,
    pub policy: Policy,
}

impl MdocCircuitStatement {
    pub fn from_extracted(extracted: &ExtractedPidMdoc, policy: Policy) -> Result<Self, MdocError> {
        if extracted.doctype != PID_DOCTYPE {
            return Err(MdocError::DoctypeMismatch);
        }
        if extracted.namespace != PID_NAMESPACE {
            return Err(MdocError::NamespaceMissing);
        }
        ensure_first_block_value_window(
            &extracted.birth_date_item,
            extracted.birth_date_value_offset,
            &extracted.birth_date_bytes,
        )?;
        ensure_first_block_value_window(
            &extracted.nationality_item,
            extracted.nationality_value_offset,
            &extracted.nationality_bytes,
        )?;
        let current_date = policy_date_tuple(&policy)?;
        if current_date < extracted.valid_from {
            return Err(MdocError::CredentialNotYetValid);
        }
        if current_date > extracted.valid_until {
            return Err(MdocError::CredentialExpired);
        }

        let birth_date_digest_id = *extracted
            .digest_ids
            .get("birth_date")
            .ok_or_else(|| MdocError::ElementMissing("birth_date".to_string()))?;
        let nationality_digest_id = *extracted
            .digest_ids
            .get("nationality")
            .ok_or_else(|| MdocError::ElementMissing("nationality".to_string()))?;
        let mso = parse_mso(&extracted.mso, &extracted.namespace)?;
        if mso.version != MDOC_PROFILE_VERSION {
            return Err(MdocError::UnsupportedMsoVersion(mso.version));
        }
        if mso.doc_type != extracted.doctype {
            return Err(MdocError::DoctypeMismatch);
        }
        let birth_date_digest = *mso
            .value_digests
            .get(&birth_date_digest_id)
            .ok_or_else(|| MdocError::ItemDigestMismatch {
                element: "birth_date".to_string(),
                digest_id: birth_date_digest_id,
            })?;
        let nationality_digest =
            *mso.value_digests
                .get(&nationality_digest_id)
                .ok_or_else(|| MdocError::ItemDigestMismatch {
                    element: "nationality".to_string(),
                    digest_id: nationality_digest_id,
                })?;

        Ok(Self {
            issuer_input: extracted.issuer_ecdsa_input.clone(),
            device_input: extracted.device_ecdsa_input.clone(),
            birth_date_digest,
            nationality_digest,
            birth_date_value_offset: extracted.birth_date_value_offset,
            nationality_value_offset: extracted.nationality_value_offset,
            policy,
        })
    }
}

fn ensure_first_block_value_window(
    item: &[u8],
    offset: usize,
    expected: &[u8],
) -> Result<(), MdocError> {
    let end = offset
        .checked_add(expected.len())
        .ok_or(MdocError::UnsupportedCircuitValue(
            "element value bytes at offset",
        ))?;
    if end > SHA256_FIRST_BLOCK_LEN {
        return Err(MdocError::UnsupportedCircuitValue(
            "value window must lie in first SHA-256 block",
        ));
    }
    if item.get(offset..end) != Some(expected) {
        return Err(MdocError::UnsupportedCircuitValue(
            "element value bytes at offset",
        ));
    }
    Ok(())
}

fn policy_date_tuple(policy: &Policy) -> Result<(u16, u8, u8), MdocError> {
    Ok((
        u16::try_from(policy.current_date.year)
            .map_err(|_| MdocError::InvalidTdate("policy.current_date"))?,
        u8::try_from(policy.current_date.month)
            .map_err(|_| MdocError::InvalidTdate("policy.current_date"))?,
        u8::try_from(policy.current_date.day)
            .map_err(|_| MdocError::InvalidTdate("policy.current_date"))?,
    ))
}

#[derive(Serialize, Deserialize)]
pub struct MdocCircuitProof {
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
    issuer_p256_claim: P256CurrentAirProofClaim,
    issuer_p256_interaction_claim: P256CurrentAirInteractionClaim,
    device_p256_claim: P256CurrentAirProofClaim,
    device_p256_interaction_claim: P256CurrentAirInteractionClaim,
    issuer_sha_log_n_rows: u32,
    issuer_sha_interaction_claim: Sha256InteractionClaim,
    device_sha_log_n_rows: u32,
    device_sha_interaction_claim: Sha256InteractionClaim,
    birth_sha_log_n_rows: u32,
    birth_sha_interaction_claim: Sha256InteractionClaim,
    nat_sha_log_n_rows: u32,
    nat_sha_interaction_claim: Sha256InteractionClaim,
    issuer_bridge_log_size: u32,
    issuer_bridge_interaction_claim: DigestBindInteractionClaim,
    device_bridge_log_size: u32,
    device_bridge_interaction_claim: DigestBindInteractionClaim,
    birth_digest_bind_interaction_claim: PublicDigestBindInteractionClaim,
    nat_digest_bind_interaction_claim: PublicDigestBindInteractionClaim,
    age_public: predicates::PublicInput,
    age_claimed_sums: Vec<QM31>,
    nat_public: predicates::NatPublicInput,
    nat_claimed_sums: Vec<QM31>,
}

fn sha_params(bytes: &[u8]) -> (stwo_sha256::types::Sha256Witness, u32) {
    let witness = compute_sha256_witness(bytes);
    let log_n_rows = min_log_size(witness.blocks.len());
    (witness, log_n_rows)
}

fn single_p256_draft(input: EcdsaVerifyInput) -> Result<P256ProofDraft, Error> {
    P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![input])
        .map_err(Error::P256Prepare)
}

fn mdoc_sizing_waste(
    extracted: &ExtractedPidMdoc,
    statement: &MdocCircuitStatement,
) -> Result<MdocSizingWaste, Error> {
    let issuer_draft = single_p256_draft(statement.issuer_input.clone())?;
    let device_draft = single_p256_draft(statement.device_input.clone())?;
    let (issuer_sha_witness, issuer_sha_log) = sha_params(&extracted.issuer_sig_structure);
    let (device_sha_witness, device_sha_log) = sha_params(&extracted.device_sig_structure);
    let (birth_sha_witness, birth_sha_log) = sha_params(&extracted.birth_date_item);
    let (nat_sha_witness, nat_sha_log) = sha_params(&extracted.nationality_item);
    let shared_sha_log = [issuer_sha_log, device_sha_log, birth_sha_log, nat_sha_log]
        .into_iter()
        .max()
        .expect("sha log list is non-empty");

    let birth_exposure = FieldExposure::from_preimage_windows(&[(
        field_id::DOB,
        statement.birth_date_value_offset,
        4,
    )]);
    let nat_exposure = FieldExposure::from_preimage_windows(&[(
        field_id::NATIONALITY,
        statement.nationality_value_offset,
        2,
    )]);

    let sha = vec![
        sha_sizing_waste(
            "issuer",
            &issuer_sha_witness,
            issuer_sha_log,
            shared_sha_log,
            FieldExposure::empty(),
        ),
        sha_sizing_waste(
            "device",
            &device_sha_witness,
            device_sha_log,
            shared_sha_log,
            FieldExposure::empty(),
        ),
        sha_sizing_waste(
            "birth_date",
            &birth_sha_witness,
            birth_sha_log,
            shared_sha_log,
            birth_exposure,
        ),
        sha_sizing_waste(
            "nationality",
            &nat_sha_witness,
            nat_sha_log,
            shared_sha_log,
            nat_exposure,
        ),
    ];
    let sha_wasted_cells = sha.iter().map(|row| row.wasted_cells).sum();

    let mut issuer_p256 = P256Prover::new(&issuer_draft).map_err(Error::P256Prepare)?;
    let issuer_fingerprints = issuer_p256.preprocessed_column_fingerprints();
    let mut device_p256 = P256Prover::new(&device_draft)
        .map_err(Error::P256Prepare)?
        .with_preprocessed_namespace("mdoc/device");
    let device_fingerprints = device_p256.preprocessed_column_fingerprints();
    let p256_namespaced_identical_preprocessed_cells = device_fingerprints
        .iter()
        .filter(|fingerprint| fingerprint.id.id.starts_with("mdoc/device/"))
        .filter(|device| {
            issuer_fingerprints
                .iter()
                .any(|issuer| issuer.log_size == device.log_size && issuer.hash == device.hash)
        })
        .map(|fingerprint| 1u64 << fingerprint.log_size)
        .sum();

    Ok(MdocSizingWaste {
        sha,
        sha_wasted_cells,
        p256_namespaced_identical_preprocessed_cells,
    })
}

fn sha_sizing_waste(
    name: &'static str,
    witness: &stwo_sha256::types::Sha256Witness,
    natural_log: u32,
    shared_log: u32,
    field_exposure: FieldExposure,
) -> MdocShaSizingWaste {
    let natural = Sha256Prover::new(witness, natural_log, SHA_GROUP_WIDTH)
        .with_digest_provider()
        .with_field_provider(field_exposure.clone())
        .layout();
    let shared = Sha256Prover::new(witness, shared_log, SHA_GROUP_WIDTH)
        .with_digest_provider()
        .with_field_provider(field_exposure)
        .layout();
    let natural_cells = trace_and_interaction_cells(&natural);
    let shared_cells = trace_and_interaction_cells(&shared);
    MdocShaSizingWaste {
        name,
        natural_log,
        shared_log,
        wasted_cells: shared_cells.saturating_sub(natural_cells),
    }
}

fn trace_and_interaction_cells(layout: &TreeLayout) -> u64 {
    layout
        .trace
        .iter()
        .chain(&layout.interaction)
        .map(|&log_size| 1u64 << log_size)
        .sum()
}

fn expected_instance(input: &EcdsaVerifyInput) -> PublicEcdsaInstance<M31> {
    PublicEcdsaInstance::from_input(0, input)
}

fn ecdsa_inputs_equal(left: &EcdsaVerifyInput, right: &EcdsaVerifyInput) -> bool {
    left.message_hash.0 == right.message_hash.0
        && left.signature.r.0 == right.signature.r.0
        && left.signature.s.0 == right.signature.s.0
        && left.public_key.x.0 == right.public_key.x.0
        && left.public_key.y.0 == right.public_key.y.0
}

pub fn prove_mdoc_circuit(
    extracted: &ExtractedPidMdoc,
    statement: &MdocCircuitStatement,
) -> Result<MdocCircuitProof, Error> {
    if statement.birth_date_value_offset != extracted.birth_date_value_offset
        || statement.nationality_value_offset != extracted.nationality_value_offset
    {
        return Err(Error::Prove(
            "mdoc statement offsets do not match extracted witness".to_string(),
        ));
    }
    if !ecdsa_inputs_equal(&statement.issuer_input, &extracted.issuer_ecdsa_input)
        || !ecdsa_inputs_equal(&statement.device_input, &extracted.device_ecdsa_input)
    {
        return Err(Error::P256InstanceMismatch);
    }

    let issuer_draft = single_p256_draft(statement.issuer_input.clone())?;
    let device_draft = single_p256_draft(statement.device_input.clone())?;
    // All four SHA instances share one `log_n_rows`. This is NOT the wasteful
    // choice the phase-0b plan assumed: the bulk SHA preprocessed (σ/Σ decode,
    // xor_8, split-pack tables — the ~6.3M-cell class) sits at the fixed
    // `LOG_SIZE_16` and is deduped across instances regardless of trace log.
    // Only 10 preprocessed columns (`is_first_row` + 9 round-cyclic) are sized to
    // `log_n_rows`, and their column *ids* are log-independent while their
    // *content* is not — so under air-core first-writer-wins tree-0 dedup all
    // four instances must agree on the log or the content-invariant assertion
    // fires. Sizing each instance to its own `min_log_size` would force a
    // per-instance preprocessed namespace, duplicating the 6.3M-cell table set
    // ~4× to save only ~0.5M padded trace/interaction cells (<1% of the circuit).
    // Measured: shared-log waste is 529,792 cells of 79.99M (0.66%); see
    // `mdoc_sizing_waste`. Equal sizing is the correct, cheaper choice.
    let (issuer_sha_witness, issuer_sha_log) = sha_params(&extracted.issuer_sig_structure);
    let (device_sha_witness, device_sha_log) = sha_params(&extracted.device_sig_structure);
    let (birth_sha_witness, birth_sha_log) = sha_params(&extracted.birth_date_item);
    let (nat_sha_witness, nat_sha_log) = sha_params(&extracted.nationality_item);
    let shared_sha_log = [issuer_sha_log, device_sha_log, birth_sha_log, nat_sha_log]
        .into_iter()
        .max()
        .expect("sha log list is non-empty");
    let issuer_scalar_z = SharedScalarZRelation::new();
    let issuer_digest = SharedDigestRelation::new();
    let device_scalar_z = SharedScalarZRelation::new();
    let device_digest = SharedDigestRelation::new();
    let birth_digest = SharedDigestRelation::new();
    let nat_digest = SharedDigestRelation::new();
    let birth_field = SharedFieldRelation::new();
    let nat_field = SharedFieldRelation::new();

    let birth_exposure = FieldExposure::from_preimage_windows(&[(
        field_id::DOB,
        statement.birth_date_value_offset,
        4,
    )]);
    let nat_exposure = FieldExposure::from_preimage_windows(&[(
        field_id::NATIONALITY,
        statement.nationality_value_offset,
        2,
    )]);

    let mut issuer_p256 = P256Prover::new(&issuer_draft)
        .map_err(Error::P256Prepare)?
        .with_z_binding(issuer_scalar_z.clone());
    // The `mdoc/device` namespace is REQUIRED, not waste: the hinted-mul schedule
    // preprocessed columns are witness-dependent (measured: 18 of 215 columns —
    // the log-13 schedule set — differ between the issuer and device signatures).
    // Without the namespace the device module would alias onto the issuer's
    // schedule under air-core first-writer-wins tree-0 dedup, binding the wrong
    // constraints. Two genuinely distinct signatures cannot share the schedule.
    let mut device_p256 = P256Prover::new(&device_draft)
        .map_err(Error::P256Prepare)?
        .with_preprocessed_namespace("mdoc/device")
        .with_z_binding(device_scalar_z.clone());
    let mut issuer_sha = Sha256Prover::new(&issuer_sha_witness, shared_sha_log, SHA_GROUP_WIDTH)
        .with_digest_handle(issuer_digest.clone());
    let mut device_sha = Sha256Prover::new(&device_sha_witness, shared_sha_log, SHA_GROUP_WIDTH)
        .with_digest_handle(device_digest.clone());
    let mut birth_sha = Sha256Prover::new(&birth_sha_witness, shared_sha_log, SHA_GROUP_WIDTH)
        .with_digest_handle(birth_digest.clone())
        .with_field_handle(birth_exposure.clone(), birth_field.clone());
    let mut nat_sha = Sha256Prover::new(&nat_sha_witness, shared_sha_log, SHA_GROUP_WIDTH)
        .with_digest_handle(nat_digest.clone())
        .with_field_handle(nat_exposure.clone(), nat_field.clone());

    let issuer_bridge_rows = crate::bridge_rows(&issuer_p256.proof_claim().public_inputs.instances);
    let issuer_bridge_log = crate::bridge_log_size(issuer_bridge_rows.len());
    let mut issuer_bridge = DigestBindProver::new(
        issuer_bridge_rows,
        issuer_bridge_log,
        issuer_scalar_z,
        issuer_digest.clone(),
    );
    let device_bridge_rows = crate::bridge_rows(&device_p256.proof_claim().public_inputs.instances);
    let device_bridge_log = crate::bridge_log_size(device_bridge_rows.len());
    let mut device_bridge = DigestBindProver::new(
        device_bridge_rows,
        device_bridge_log,
        device_scalar_z,
        device_digest.clone(),
    );
    let mut birth_digest_bind =
        PublicDigestBind::new(statement.birth_date_digest, birth_digest.clone());
    let mut nat_digest_bind =
        PublicDigestBind::new(statement.nationality_digest, nat_digest.clone());

    let age_public = statement.policy.age_public_input();
    let nat_public = statement.policy.nat_public_input();
    let age_dob = DateOfBirth(predicates::Date {
        year: u32::from(u16::from_be_bytes([
            extracted.birth_date_bytes[0],
            extracted.birth_date_bytes[1],
        ])),
        month: u32::from(extracted.birth_date_bytes[2]),
        day: u32::from(extracted.birth_date_bytes[3]),
    });
    let nat_code = u32::from(u16::from_be_bytes(extracted.nationality_bytes));
    let nat_private = predicates::NatPrivateInput {
        nationalities: vec![nat_code],
    };
    let mut age = AgeRangeCheck::new(PcsConfig::default())
        .prover(&age_public, &age_dob)
        .map_err(Error::AgePrepare)?
        .with_dob_binding(birth_field.clone());
    let mut nat = NationalityPredicate::new(PcsConfig::default())
        .prover(&nat_public, &nat_private)
        .map_err(Error::NatPrepare)?
        .with_nat_binding(nat_field.clone());

    let config = issuer_p256.pcs_config();
    let stark_proof = {
        let mut modules: [&mut dyn AirProver; 12] = [
            &mut issuer_p256,
            &mut issuer_sha,
            &mut issuer_bridge,
            &mut device_p256,
            &mut device_sha,
            &mut device_bridge,
            &mut birth_sha,
            &mut birth_digest_bind,
            &mut nat_sha,
            &mut nat_digest_bind,
            &mut age,
            &mut nat,
        ];
        air_core::prove(&mut modules, config).map_err(|e| Error::Prove(format!("{e:?}")))?
    };

    Ok(MdocCircuitProof {
        stark_proof,
        issuer_p256_claim: issuer_p256.proof_claim().clone(),
        issuer_p256_interaction_claim: issuer_p256.interaction_claim().clone(),
        device_p256_claim: device_p256.proof_claim().clone(),
        device_p256_interaction_claim: device_p256.interaction_claim().clone(),
        issuer_sha_log_n_rows: shared_sha_log,
        issuer_sha_interaction_claim: issuer_sha.interaction_claim().clone(),
        device_sha_log_n_rows: shared_sha_log,
        device_sha_interaction_claim: device_sha.interaction_claim().clone(),
        birth_sha_log_n_rows: shared_sha_log,
        birth_sha_interaction_claim: birth_sha.interaction_claim().clone(),
        nat_sha_log_n_rows: shared_sha_log,
        nat_sha_interaction_claim: nat_sha.interaction_claim().clone(),
        issuer_bridge_log_size: issuer_bridge_log,
        issuer_bridge_interaction_claim: issuer_bridge.interaction_claim().clone(),
        device_bridge_log_size: device_bridge_log,
        device_bridge_interaction_claim: device_bridge.interaction_claim().clone(),
        birth_digest_bind_interaction_claim: birth_digest_bind.interaction_claim().clone(),
        nat_digest_bind_interaction_claim: nat_digest_bind.interaction_claim().clone(),
        age_public,
        age_claimed_sums: age.claimed_sums(),
        nat_public,
        nat_claimed_sums: nat.claimed_sums(),
    })
}

pub fn verify_mdoc_circuit(
    proof: &MdocCircuitProof,
    statement: &MdocCircuitStatement,
) -> Result<(), Error> {
    if proof.issuer_p256_claim.public_inputs.instances.as_slice()
        != [expected_instance(&statement.issuer_input)]
    {
        return Err(Error::P256InstanceMismatch);
    }
    if proof.device_p256_claim.public_inputs.instances.as_slice()
        != [expected_instance(&statement.device_input)]
    {
        return Err(Error::P256InstanceMismatch);
    }
    if proof.age_public != statement.policy.age_public_input() {
        return Err(Error::AgePolicyMismatch);
    }
    if proof.nat_public != statement.policy.nat_public_input() {
        return Err(Error::NatPolicyMismatch);
    }

    let issuer_scalar_z = SharedScalarZRelation::new();
    let issuer_digest = SharedDigestRelation::new();
    let device_scalar_z = SharedScalarZRelation::new();
    let device_digest = SharedDigestRelation::new();
    let birth_digest = SharedDigestRelation::new();
    let nat_digest = SharedDigestRelation::new();
    let birth_field = SharedFieldRelation::new();
    let nat_field = SharedFieldRelation::new();

    let mut issuer_p256 = P256Verifier::new(
        proof.issuer_p256_claim.clone(),
        proof.issuer_p256_interaction_claim.clone(),
    )
    .with_z_binding(issuer_scalar_z.clone());
    let mut device_p256 = P256Verifier::new(
        proof.device_p256_claim.clone(),
        proof.device_p256_interaction_claim.clone(),
    )
    .with_preprocessed_namespace("mdoc/device")
    .with_z_binding(device_scalar_z.clone());
    if proof.stark_proof.config != issuer_p256.expected_pcs_config() {
        return Err(Error::WeakConfig {
            got: proof.stark_proof.config,
            expected: issuer_p256.expected_pcs_config(),
        });
    }

    let mut issuer_sha = Sha256Verifier::new(
        proof.issuer_sha_log_n_rows,
        SHA_GROUP_WIDTH,
        proof.issuer_sha_interaction_claim.clone(),
    )
    .with_digest_handle(issuer_digest.clone());
    let mut device_sha = Sha256Verifier::new(
        proof.device_sha_log_n_rows,
        SHA_GROUP_WIDTH,
        proof.device_sha_interaction_claim.clone(),
    )
    .with_digest_handle(device_digest.clone());

    let birth_exposure = FieldExposure::from_preimage_windows(&[(
        field_id::DOB,
        statement.birth_date_value_offset,
        4,
    )]);
    let nat_exposure = FieldExposure::from_preimage_windows(&[(
        field_id::NATIONALITY,
        statement.nationality_value_offset,
        2,
    )]);
    let mut birth_sha = Sha256Verifier::new(
        proof.birth_sha_log_n_rows,
        SHA_GROUP_WIDTH,
        proof.birth_sha_interaction_claim.clone(),
    )
    .with_digest_handle(birth_digest.clone())
    .with_field_handle(birth_exposure, birth_field.clone());
    let mut nat_sha = Sha256Verifier::new(
        proof.nat_sha_log_n_rows,
        SHA_GROUP_WIDTH,
        proof.nat_sha_interaction_claim.clone(),
    )
    .with_digest_handle(nat_digest.clone())
    .with_field_handle(nat_exposure, nat_field.clone());

    let mut issuer_bridge = DigestBindVerifier::new(
        proof.issuer_bridge_log_size,
        proof.issuer_bridge_interaction_claim.clone(),
        issuer_scalar_z,
        issuer_digest,
    );
    let mut device_bridge = DigestBindVerifier::new(
        proof.device_bridge_log_size,
        proof.device_bridge_interaction_claim.clone(),
        device_scalar_z,
        device_digest,
    );
    let mut birth_digest_bind = PublicDigestBind::verifier(
        statement.birth_date_digest,
        birth_digest.clone(),
        proof.birth_digest_bind_interaction_claim.clone(),
    );
    let mut nat_digest_bind = PublicDigestBind::verifier(
        statement.nationality_digest,
        nat_digest.clone(),
        proof.nat_digest_bind_interaction_claim.clone(),
    );
    let mut age = AgeRangeCheck::new(PcsConfig::default())
        .verifier(&proof.age_public, &proof.age_claimed_sums)
        .map_err(Error::AgePrepare)?
        .with_dob_binding(birth_field.clone());
    let mut nat = NationalityPredicate::new(PcsConfig::default())
        .verifier(&proof.nat_public, &proof.nat_claimed_sums)
        .map_err(Error::NatPrepare)?
        .with_nat_binding(nat_field.clone());

    let mut modules: [&mut dyn Air; 12] = [
        &mut issuer_p256,
        &mut issuer_sha,
        &mut issuer_bridge,
        &mut device_p256,
        &mut device_sha,
        &mut device_bridge,
        &mut birth_sha,
        &mut birth_digest_bind,
        &mut nat_sha,
        &mut nat_digest_bind,
        &mut age,
        &mut nat,
    ];
    air_core::verify(&mut modules, &proof.stark_proof).map_err(|e| Error::Verify(format!("{e:?}")))
}

fn numeric_country(alpha2: &str) -> Result<u32, MdocError> {
    celes::Country::from_alpha2(alpha2)
        .map(|country| country.value as u32)
        .map_err(|_| MdocError::InvalidNationality(alpha2.to_string()))
}

fn value_field<'a>(map: &'a [(Value, Value)], field: &'static str) -> Result<&'a Value, MdocError> {
    map.iter()
        .find_map(|(key, value)| (key == &Value::Text(field.to_string())).then_some(value))
        .ok_or(MdocError::MissingField(field))
}

fn map_field<'a>(
    map: &'a [(Value, Value)],
    field: &'static str,
) -> Result<&'a [(Value, Value)], MdocError> {
    expect_map(value_field(map, field)?, field)
}

fn text_field<'a>(map: &'a [(Value, Value)], field: &'static str) -> Result<&'a str, MdocError> {
    expect_text(value_field(map, field)?, field)
}

fn u32_field(map: &[(Value, Value)], field: &'static str) -> Result<u32, MdocError> {
    expect_u32(value_field(map, field)?, field)
}

fn int_field(map: &[(Value, Value)], key: i128, field: &'static str) -> Result<i128, MdocError> {
    let value = map
        .iter()
        .find_map(|(candidate, value)| {
            value_i128(candidate)
                .ok()
                .filter(|candidate| *candidate == key)
                .map(|_| value)
        })
        .ok_or(MdocError::MissingField(field))?;
    value_i128(value)
}

fn bytes_int_field<'a>(
    map: &'a [(Value, Value)],
    key: i128,
    field: &'static str,
) -> Result<&'a [u8], MdocError> {
    let value = map
        .iter()
        .find_map(|(candidate, value)| {
            value_i128(candidate)
                .ok()
                .filter(|candidate| *candidate == key)
                .map(|_| value)
        })
        .ok_or(MdocError::MissingField(field))?;
    expect_bytes(value, field)
}

fn expect_map<'a>(
    value: &'a Value,
    field: &'static str,
) -> Result<&'a [(Value, Value)], MdocError> {
    match value {
        Value::Map(entries) => Ok(entries),
        _ => Err(MdocError::WrongType(field)),
    }
}

fn expect_text<'a>(value: &'a Value, field: &'static str) -> Result<&'a str, MdocError> {
    match value {
        Value::Text(text) => Ok(text),
        _ => Err(MdocError::WrongType(field)),
    }
}

fn expect_bytes<'a>(value: &'a Value, field: &'static str) -> Result<&'a [u8], MdocError> {
    match value {
        Value::Bytes(bytes) => Ok(bytes),
        _ => Err(MdocError::WrongType(field)),
    }
}

fn expect_u32(value: &Value, field: &'static str) -> Result<u32, MdocError> {
    let int = value_i128(value)?;
    u32::try_from(int).map_err(|_| MdocError::WrongType(field))
}

fn value_i128(value: &Value) -> Result<i128, MdocError> {
    let Value::Integer(int) = value else {
        return Err(MdocError::WrongType("integer"));
    };
    Ok((*int).into())
}

fn expect_digest(value: &Value, field: &'static str) -> Result<[u8; 32], MdocError> {
    expect_32(expect_bytes(value, field)?, field)
}

fn expect_32(bytes: &[u8], field: &'static str) -> Result<[u8; 32], MdocError> {
    bytes.try_into().map_err(|_| MdocError::WrongType(field))
}
