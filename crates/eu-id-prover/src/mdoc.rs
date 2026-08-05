//! Product EUID PID mdoc proof path.
//!
//! This module parses the constrained ISO/IEC 18013-5 PID profile.
//! It prepares the mdoc statement and witness.
//! One proof covers the signatures, digest membership, validity, device key, age, and nationality.
//! The device authentication signature binds freshness.
//!
//! In this module, “private” identifies a logical witness value, not a public input.
//! It does not claim proof confidentiality.
//! The current composed proof is transparent and is not zero-knowledge.

use std::collections::{HashMap, HashSet};

use air_core::relations::{FieldBytesRelation, SharedFieldRelation};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use ciborium::value::Value;
use ecdsa::signature::{Signer, Verifier};
use p256::ecdsa::{Signature as P256Signature, SigningKey, VerifyingKey};
use p256::pkcs8::DecodePublicKey;
use p256::EncodedPoint;
use predicates::nat::NationalityPredicate;
use predicates::{AgeRangeCheck, DateOfBirth, PredicateProver, PredicateVerifier};
use rand::RngCore;
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{QM31, SECURE_EXTENSION_DEGREE};
use stwo::core::fri::FriConfig;
use stwo::core::pcs::PcsConfig;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof::StarkProof;
use stwo::core::utils::{bit_reverse_index, coset_index_to_circle_domain_index};
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;

use stwo::core::verifier::VerificationError;
use stwo::core::{
    air::Component,
    channel::{Blake2sChannel, Channel},
};
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::{
    preprocessed_columns::PreProcessedColumnId, TraceLocationAllocator,
};
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
};

use stwo_p256::types::{AffinePoint, EcdsaVerifyInput, Signature, U256};

use stwo_sha256::air::{Sha256Prover, Sha256Verifier};
use stwo_sha256::interaction::InteractionClaim as Sha256InteractionClaim;
use stwo_sha256::relations::{
    PackedShaDigestRelation, SharedPackedShaDigestRelation, SharedShaTableRelations,
    PACKED_SHA_STREAM_FIELD_BASE,
};
use stwo_sha256::shared_tables::{ShaTablesInteractionClaim, ShaTablesProver, ShaTablesVerifier};
use stwo_sha256::witness::compute_packed_sha256_witness;

use crate::mdoc_cbor_stream::{
    MdocCborInputMode, MdocCborStream, MdocCborStreamInteractionClaim, MdocCborWitness,
};
use crate::product_profile::Policy;

use crate::mdoc_mac::{
    MdocMacBind, MdocMacInteractionClaim, MdocP4bMacPublic, MdocP4bMacSharedState,
};
use crate::mdoc_scope::{
    MdocScope, MdocScopeHandles, MdocScopeInteractionClaim, MdocScopeItem, MdocScopeMode,
    MdocScopeParserInput, MdocScopeProofMetadata, MdocScopeStatement, MDOC_SCOPE_MAX_DIGEST_ID,
    MDOC_SCOPE_MAX_ITEMS, MDOC_SCOPE_MSO_PAYLOAD_FIELD_ID, NORMALIZED_MSO_STREAM_ID,
};
use crate::mdoc_validity::{mdoc_validity_rows, MdocValidityBind, MdocValidityInteractionClaim};

use crate::Error;
use air_core::claim_mask::{
    add_claim_mask_fraction, ClaimMaskChallengeModule, ClaimMaskRing, ClaimMaskTrace,
    SharedClaimMaskChallenge, CLAIM_MASK_TRACE_COLUMNS,
};

/// Current product profile: deterministic CBOR with text-form values.
const MDOC_PROFILE_VERSION: &str = "2.0";
const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const PRODUCT_SEMANTICS_ERROR: &str =
    "product profile requires 1..=2 mdoc 2.0 text-date/alpha-2 predicate attributes";
const DEMO_REQUEST_BINDING: [u8; 32] = [0x51; 32];
const DEMO_VERIFICATION_TIME_EPOCH_SECONDS: u64 = 1_783_080_000;

fn take_claim_masks(
    ring: &mut ClaimMaskRing,
    log_sizes: &[u32],
) -> Result<Vec<ClaimMaskTrace>, air_core::claim_mask::ClaimMaskError> {
    log_sizes
        .iter()
        .map(|&log_size| ring.take(log_size))
        .collect()
}
const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const ES256_PROTECTED_HEADER: &[u8] = &[0xA1, 0x01, 0x26];
const CBOR_TAG_ENCODED_CBOR: u64 = 24;
const CBOR_TAG_FULL_DATE: u64 = 1004;
pub(crate) const MDOC_MSO_PAYLOAD_FIELD_ID: u32 = MDOC_SCOPE_MSO_PAYLOAD_FIELD_ID;
const MDOC_REVOCATION_MESSAGE_FIELD_ID: u32 = 41;
const TS13_REVOCATION_MESSAGE_LEN: usize = 20;
const PRODUCT_SESSION_TRANSCRIPT_BYTES: usize = 56;
const PACKED_SHA_ISSUER_SLOT: u32 = 0;
const PACKED_SHA_MSO_SLOT: u32 = 1;
const PACKED_SHA_REVOCATION_SLOT: u32 = 2;
const PACKED_SHA_ITEM_SLOT_BASE: u32 = 3;
const DEMO_PRIVATE_RANDOM_CANARY: [u8; 32] = [
    0x9f, 0x4a, 0x7c, 0x1d, 0x2e, 0x8b, 0x63, 0x50, 0xa6, 0xd9, 0x41, 0x73, 0xbc, 0x05, 0x28, 0xee,
    0x4d, 0x7a, 0x91, 0x63, 0xf0, 0xc2, 0xb8, 0x5e, 0x11, 0x74, 0xda, 0xc9, 0x6e, 0x3f, 0x70, 0x2b,
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MdocPidRequest {
    /// Domain-separated hash of the verifier's complete product request.
    ///
    /// The SDK computes this from its canonical public-statement encoding.
    /// Product proving requires an exact nonzero value.
    pub request_binding: [u8; 32],
    pub doctype: String,
    pub namespace: String,
    pub attributes: Vec<MdocRequestedAttribute>,
    pub session_transcript: Vec<u8>,
    /// Exact verifier-authoritative issuer leaf key for a product request.
    pub required_issuer_public_key: AffinePoint,
    /// Verifier time in whole UTC seconds since 1970-01-01T00:00:00Z.
    pub verification_time_epoch_seconds: u64,
    /// Mandatory sorted-pair revocation data for the product request.
    pub revocation: MdocRevocationRequest,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MdocRevocationRequest {
    pub public_inputs: MdocRevocationPublicInputs,
    pub id_lo: u64,
    pub id_hi: u64,
    pub signature: Signature,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct MdocTimestamp {
    pub year: u16,
    pub month: u8,
    pub day: u8,
    pub hour: u8,
    pub minute: u8,
    pub second: u8,
}

impl MdocTimestamp {
    pub(crate) fn text_bytes(self) -> [u8; 20] {
        format!(
            "{:04}-{:02}-{:02}T{:02}:{:02}:{:02}Z",
            self.year, self.month, self.day, self.hour, self.minute, self.second
        )
        .as_bytes()
        .try_into()
        .expect("formatted tdate has YYYY-MM-DDThh:mm:ssZ length")
    }
}

pub(crate) const fn is_gregorian_leap_year(year: u16) -> bool {
    year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)
}

pub(crate) const fn gregorian_days_in_month(year: u16, month: u8) -> Option<u8> {
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => Some(31),
        4 | 6 | 9 | 11 => Some(30),
        2 if is_gregorian_leap_year(year) => Some(29),
        2 => Some(28),
        _ => None,
    }
}

pub(crate) const fn is_gregorian_date(year: u16, month: u8, day: u8) -> bool {
    match gregorian_days_in_month(year, month) {
        Some(max_day) => day >= 1 && day <= max_day,
        None => false,
    }
}

pub fn utc_timestamp_from_epoch_seconds(seconds: u64) -> Result<MdocTimestamp, MdocError> {
    const MAX_SUPPORTED_EPOCH_SECONDS: u64 = 253_402_300_799;
    if seconds > MAX_SUPPORTED_EPOCH_SECONDS {
        return Err(MdocError::InvalidVerificationTime);
    }
    let epoch_day =
        i64::try_from(seconds / 86_400).map_err(|_| MdocError::InvalidVerificationTime)?;
    let seconds_of_day = seconds % 86_400;
    let z = epoch_day + 719_468;
    let era = z / 146_097;
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1_460 + doe / 36_524 - doe / 146_096) / 365;
    let year = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
    let year = year + i64::from(month <= 2);
    Ok(MdocTimestamp {
        year: u16::try_from(year).map_err(|_| MdocError::InvalidVerificationTime)?,
        month: month as u8,
        day: day as u8,
        hour: (seconds_of_day / 3_600) as u8,
        minute: ((seconds_of_day % 3_600) / 60) as u8,
        second: (seconds_of_day % 60) as u8,
    })
}

fn strict_verification_timestamp(seconds: u64) -> Result<MdocTimestamp, MdocError> {
    if seconds == 0
        || seconds
            .checked_add(1)
            .and_then(|next| utc_timestamp_from_epoch_seconds(next).ok())
            .is_none()
    {
        return Err(MdocError::InvalidVerificationTime);
    }
    utc_timestamp_from_epoch_seconds(seconds)
}

fn validate_product_policy(
    policy: &Policy,
    verification_time_epoch_seconds: u64,
) -> Result<(), MdocError> {
    if policy.accepted_nationalities.is_empty()
        || policy
            .accepted_nationalities
            .iter()
            .any(|code| !crate::is_assigned_iso_alpha2(*code))
        || policy
            .accepted_nationalities
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
    {
        return Err(MdocError::InvalidNationality(
            "accepted policy must be a nonempty, sorted, unique set of assigned ISO alpha-2 codes"
                .to_string(),
        ));
    }

    let verification_date = strict_verification_timestamp(verification_time_epoch_seconds)?;
    if policy.current_date.year != u32::from(verification_date.year)
        || policy.current_date.month != u32::from(verification_date.month)
        || policy.current_date.day != u32::from(verification_date.day)
    {
        return Err(MdocError::InvalidVerificationTime);
    }
    Ok(())
}

pub fn p256_affine_point_from_coordinates(x: &[u8], y: &[u8]) -> Option<AffinePoint> {
    let x: [u8; 32] = x.try_into().ok()?;
    let y: [u8; 32] = y.try_into().ok()?;
    let point = AffinePoint {
        x: U256(x),
        y: U256(y),
    };
    let encoded = EncodedPoint::from_affine_coordinates((&x).into(), (&y).into(), false);
    VerifyingKey::from_encoded_point(&encoded)
        .ok()
        .map(|_| point)
}

pub fn p256_signature_from_scalars(r: &[u8], s: &[u8]) -> Option<Signature> {
    let r: [u8; 32] = r.try_into().ok()?;
    let s: [u8; 32] = s.try_into().ok()?;
    let mut compact = [0u8; 64];
    compact[..32].copy_from_slice(&r);
    compact[32..].copy_from_slice(&s);
    P256Signature::from_slice(&compact).ok()?;
    Some(Signature {
        r: U256(r),
        s: U256(s),
    })
}

/// Constructs the P-256 digest value used by the public mdoc statement.
pub fn p256_digest(bytes: [u8; 32]) -> U256 {
    U256(bytes)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MdocDisclosureMode {
    AgeOver,
    Alpha2Set,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocRequestedAttribute {
    pub element_identifier: String,
    pub mode: MdocDisclosureMode,
}

#[derive(Clone, Debug)]
pub struct ExtractedMdocAttribute {
    pub request: MdocRequestedAttribute,
    pub digest_id: u32,
    pub item: Vec<u8>,
    pub element_identifier_offset: usize,
    pub value_offset: usize,
    pub value: Vec<u8>,
}

fn validate_requested_attributes(attributes: &[MdocRequestedAttribute]) -> Result<(), MdocError> {
    if !(1..=MDOC_SCOPE_MAX_ITEMS).contains(&attributes.len()) {
        return Err(MdocError::InvalidAttributeCount {
            count: attributes.len(),
        });
    }
    let mut age_seen = false;
    let mut alpha2_seen = false;
    for attribute in attributes {
        match &attribute.mode {
            MdocDisclosureMode::AgeOver => {
                if attribute.element_identifier.len() > 32 {
                    return Err(MdocError::ElementIdentifierTooLong {
                        element: attribute.element_identifier.clone(),
                        len: attribute.element_identifier.len(),
                    });
                }
                if std::mem::replace(&mut age_seen, true) {
                    return Err(MdocError::DuplicatePredicateMode("AgeOver"));
                }
            }
            MdocDisclosureMode::Alpha2Set => {
                if attribute.element_identifier.len() > 32 {
                    return Err(MdocError::ElementIdentifierTooLong {
                        element: attribute.element_identifier.clone(),
                        len: attribute.element_identifier.len(),
                    });
                }
                if std::mem::replace(&mut alpha2_seen, true) {
                    return Err(MdocError::DuplicatePredicateMode("Alpha2Set"));
                }
            }
        }
    }
    Ok(())
}

pub(crate) fn validate_product_requested_attributes(
    attributes: &[MdocRequestedAttribute],
) -> Result<(), MdocError> {
    if !(1..=crate::product_profile::PRODUCT_MAX_ATTRIBUTES).contains(&attributes.len()) {
        return Err(MdocError::InvalidAttributeCount {
            count: attributes.len(),
        });
    }
    validate_requested_attributes(attributes)?;
    let current_layout = match attributes {
        [attribute] => matches!(
            (attribute.element_identifier.as_str(), &attribute.mode),
            ("birth_date", MdocDisclosureMode::AgeOver)
                | ("nationality", MdocDisclosureMode::Alpha2Set)
        ),
        [birth_date, nationality] => {
            birth_date.element_identifier == "birth_date"
                && matches!(birth_date.mode, MdocDisclosureMode::AgeOver)
                && nationality.element_identifier == "nationality"
                && matches!(nationality.mode, MdocDisclosureMode::Alpha2Set)
        }
        _ => false,
    };
    if !current_layout {
        return Err(MdocError::UnsupportedProductAttributeLayout);
    }
    Ok(())
}

fn validate_product_sha_input_sizes(
    mso: &[u8],
    issuer: &[u8],
    selected_items: &[&[u8]],
) -> Result<(), MdocError> {
    if mso.len() > crate::product_profile::PRODUCT_MAX_MSO_PAYLOAD_BYTES {
        return Err(MdocError::InputTooLarge {
            input: "MSO payload",
            actual: mso.len(),
            maximum: crate::product_profile::PRODUCT_MAX_MSO_PAYLOAD_BYTES,
        });
    }
    let issuer_maximum = mso
        .len()
        .checked_add(crate::product_profile::PRODUCT_ISSUER_SIG_STRUCTURE_MAX_OVERHEAD_BYTES)
        .ok_or(MdocError::InputTooLarge {
            input: "MSO payload",
            actual: mso.len(),
            maximum: usize::MAX
                - crate::product_profile::PRODUCT_ISSUER_SIG_STRUCTURE_MAX_OVERHEAD_BYTES,
        })?;
    if issuer.len() > issuer_maximum {
        return Err(MdocError::InputTooLarge {
            input: "issuer Sig_structure",
            actual: issuer.len(),
            maximum: issuer_maximum,
        });
    }
    for &item in selected_items {
        if item.len() > crate::product_profile::PRODUCT_MAX_SELECTED_ITEM_BYTES {
            return Err(MdocError::InputTooLarge {
                input: "selected IssuerSignedItem",
                actual: item.len(),
                maximum: crate::product_profile::PRODUCT_MAX_SELECTED_ITEM_BYTES,
            });
        }
    }
    let invalid_count = MdocError::InvalidAttributeCount {
        count: selected_items.len(),
    };
    let message_count = 3usize
        .checked_add(selected_items.len())
        .ok_or_else(|| invalid_count.clone())?;
    if selected_items.len() > crate::product_profile::PRODUCT_MAX_ATTRIBUTES
        || message_count > crate::product_profile::PRODUCT_MAX_PACKED_SHA_MESSAGES
    {
        return Err(invalid_count);
    }
    Ok(())
}

pub(crate) fn validate_product_mdoc_request(request: &MdocPidRequest) -> Result<(), MdocError> {
    if request.doctype != PID_DOCTYPE {
        return Err(MdocError::ProductDoctypeMismatch);
    }
    if request.namespace != PID_NAMESPACE {
        return Err(MdocError::ProductNamespaceMismatch);
    }
    strict_verification_timestamp(request.verification_time_epoch_seconds)?;
    validate_product_requested_attributes(&request.attributes)?;
    validate_product_session_transcript_cbor(&request.session_transcript)
}

#[derive(Clone, Debug)]
pub struct ExtractedPidMdoc {
    pub request_binding: [u8; 32],
    pub doctype: String,
    pub namespace: String,
    pub attributes: Vec<MdocRequestedAttribute>,
    pub extracted_attributes: Vec<ExtractedMdocAttribute>,
    pub birth_date_bytes: [u8; 4],
    pub birth_date_binding: MdocBirthDateBinding,
    pub nationality_binding: MdocNationalityBinding,
    pub birth_date_value_offset: usize,
    pub nationality_value_offset: usize,
    /// Every nationality disclosed by the holder. The AIR consumes the
    /// complete signed array and proves `any(is_acceptable)`.
    pub nationality_candidates: Vec<ParsedNationalityValue>,
    pub valid_from_timestamp: MdocTimestamp,
    pub valid_until_timestamp: MdocTimestamp,
    pub birth_date_item: Vec<u8>,
    pub nationality_item: Vec<u8>,
    pub mso: Vec<u8>,
    pub device_key: AffinePoint,
    pub issuer_sig_structure: Vec<u8>,
    pub issuer_ecdsa_input: EcdsaVerifyInput,
    pub device_ecdsa_input: EcdsaVerifyInput,
    pub revocation: MdocRevocationRequest,
}

/// Canonical `YYYY-MM-DD` bytes bound from the tagged `birth_date` value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocBirthDateBinding(pub [u8; 10]);

impl MdocBirthDateBinding {
    fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

/// Canonical alpha-2 bytes bound from a signed nationality array entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocNationalityBinding(pub [u8; 2]);

impl MdocNationalityBinding {
    fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MdocError {
    Cbor(String),
    NonCanonicalSessionTranscript,
    MissingField(&'static str),
    WrongType(&'static str),
    DoctypeMismatch,
    NamespaceMissing,
    ElementMissing(String),
    UnsupportedDigestAlgorithm(String),
    ItemDigestMismatch {
        element: String,
        digest_id: u32,
    },
    DeviceAuthPayloadMismatch,
    InvalidCoseKey(&'static str),
    InvalidCoseSign1(&'static str),
    InvalidCertificate(&'static str),
    UntrustedIssuerCertificate,
    InvalidSignature(&'static str),
    InvalidNationality(String),
    UnsupportedCircuitValue(&'static str),
    UnsupportedMsoVersion(String),
    InvalidTdate(&'static str),
    CredentialNotYetValid,
    CredentialExpired,
    InvalidVerificationTime,
    SaltTooShort {
        len: usize,
    },
    InvalidAttributeCount {
        count: usize,
    },
    DuplicatePredicateMode(&'static str),
    ElementIdentifierTooLong {
        element: String,
        len: usize,
    },
    UnsupportedProductAttributeLayout,
    ProductDoctypeMismatch,
    ProductNamespaceMismatch,
    UnsupportedDeviceAuthenticationProfile,
    RevocationRequestMismatch(&'static str),
    InvalidProductDocumentShape(&'static str),
    InputTooLarge {
        input: &'static str,
        actual: usize,
        maximum: usize,
    },
}

#[derive(Clone, Debug)]
pub struct DemoMdocCircuitFixture {
    pub document: Vec<u8>,
    pub request: MdocPidRequest,
    pub extracted: ExtractedPidMdoc,
    pub statement: MdocCircuitStatement,
}

/// Deterministic current-product fixture used by SDK tests and probes.
pub fn demo_mdoc_circuit_fixture() -> DemoMdocCircuitFixture {
    demo_mdoc_circuit_fixture_with_attributes(vec![
        MdocRequestedAttribute {
            element_identifier: "birth_date".to_string(),
            mode: MdocDisclosureMode::AgeOver,
        },
        MdocRequestedAttribute {
            element_identifier: "nationality".to_string(),
            mode: MdocDisclosureMode::Alpha2Set,
        },
    ])
}

fn demo_mdoc_circuit_fixture_with_attributes(
    attributes: Vec<MdocRequestedAttribute>,
) -> DemoMdocCircuitFixture {
    let session_transcript = openid4vp_session_transcript(b"session-transcript-123");
    validate_product_requested_attributes(&attributes).expect("current demo attribute scope");
    let demo_document = demo_mdoc_document(&session_transcript);
    let (revocation_statement, revocation_witness) =
        crate::ts13::demo_ts13_revocation_inputs(&demo_document.mso_payload);
    let request = MdocPidRequest {
        request_binding: DEMO_REQUEST_BINDING,
        doctype: PID_DOCTYPE.to_string(),
        namespace: PID_NAMESPACE.to_string(),
        attributes,
        session_transcript,
        required_issuer_public_key: demo_document.issuer_key.clone(),
        verification_time_epoch_seconds: DEMO_VERIFICATION_TIME_EPOCH_SECONDS,
        revocation: MdocRevocationRequest {
            public_inputs: (&revocation_statement).into(),
            id_lo: revocation_witness.id_lo,
            id_hi: revocation_witness.id_hi,
            signature: revocation_witness.signature,
        },
    };
    let extracted = extract_product_pid_mdoc(&demo_document.bytes, &request)
        .expect("current demo mdoc extracts");
    let statement = MdocCircuitStatement::from_extracted_at(
        &extracted,
        Policy {
            current_date: predicates::Date {
                year: 2026,
                month: 7,
                day: 3,
            },
            min_age_years: 18,
            accepted_nationalities: vec![*b"DE", *b"FR"],
        },
        DEMO_VERIFICATION_TIME_EPOCH_SECONDS,
    )
    .expect("demo mdoc statement builds");
    DemoMdocCircuitFixture {
        document: demo_document.bytes,
        request,
        extracted,
        statement,
    }
}

/// Extracts the fail-closed current product specialization.
pub(crate) fn extract_product_pid_mdoc(
    document: &[u8],
    request: &MdocPidRequest,
) -> Result<ExtractedPidMdoc, MdocError> {
    validate_product_mdoc_request(request)?;
    extract_product_pid_mdoc_inner(document, request)
}

fn extract_product_pid_mdoc_inner(
    document: &[u8],
    request: &MdocPidRequest,
) -> Result<ExtractedPidMdoc, MdocError> {
    let requested_attributes = request.attributes.clone();
    validate_requested_attributes(&requested_attributes)?;
    let doc = decode_value(document)?;
    let doc_map = current_product_document_map(&doc, request)?;
    let doctype = text_field(doc_map, "docType")?.to_string();
    if doctype != request.doctype {
        return Err(MdocError::DoctypeMismatch);
    }

    let issuer_signed = map_field(doc_map, "issuerSigned")?;
    let issuer_auth = parse_cose_sign1(value_field(issuer_signed, "issuerAuth")?)?;
    let issuer_unprotected = expect_map(&issuer_auth.unprotected, "issuerAuth.unprotected")?;
    validate_current_product_mso_payload(&issuer_auth.payload)?;
    let issuer_key = current_product_issuer_key_from_unprotected(issuer_unprotected, request)?;
    if request.required_issuer_public_key != issuer_key {
        return Err(MdocError::UntrustedIssuerCertificate);
    }
    verify_signature(
        &issuer_key,
        &issuer_auth.sig_structure,
        &issuer_auth.signature_bytes,
        "issuerAuth",
    )?;

    let mso = parse_mso(&issuer_auth.payload, &request.namespace)?;
    if !is_supported_mdoc_profile_version(&mso.version) {
        return Err(MdocError::UnsupportedMsoVersion(mso.version));
    }
    if mso.doc_type != request.doctype {
        return Err(MdocError::DoctypeMismatch);
    }
    let device_key = mso.device_key;

    let namespace_items = namespace_items(issuer_signed, &request.namespace)?;
    validate_current_product_selected_items(namespace_items, &requested_attributes)?;
    let mut extracted_attributes = Vec::with_capacity(requested_attributes.len());
    for attribute in &requested_attributes {
        let item = find_item(namespace_items, &attribute.element_identifier)?
            .ok_or_else(|| MdocError::ElementMissing(attribute.element_identifier.clone()))?;
        validate_item_digest(
            &mso.value_digests,
            &attribute.element_identifier,
            item.digest_id,
            &item.bytes,
        )?;
        let element_identifier_offset =
            find_subslice(&item.bytes, attribute.element_identifier.as_bytes()).ok_or(
                MdocError::UnsupportedCircuitValue("attribute elementIdentifier offset"),
            )?;
        let value = encode_value(item.value.clone());
        let value_offset = find_subslice(&item.bytes, &value)
            .ok_or(MdocError::UnsupportedCircuitValue("attribute value offset"))?;
        extracted_attributes.push(ExtractedMdocAttribute {
            request: attribute.clone(),
            digest_id: item.digest_id,
            item: item.bytes,
            element_identifier_offset,
            value_offset,
            value,
        });
    }
    let selected_items: Vec<&[u8]> = extracted_attributes
        .iter()
        .map(|attribute| attribute.item.as_slice())
        .collect();
    validate_product_sha_input_sizes(
        &issuer_auth.payload,
        &issuer_auth.sig_structure,
        &selected_items,
    )?;
    let birth_date_element = requested_attributes.iter().find_map(|attribute| {
        matches!(attribute.mode, MdocDisclosureMode::AgeOver)
            .then_some(attribute.element_identifier.as_str())
    });
    let nationality_element = requested_attributes.iter().find_map(|attribute| {
        matches!(attribute.mode, MdocDisclosureMode::Alpha2Set)
            .then_some(attribute.element_identifier.as_str())
    });
    let birth_date_item = if let Some(element) = birth_date_element {
        Some(
            find_item(namespace_items, element)?
                .ok_or_else(|| MdocError::ElementMissing(element.to_string()))?,
        )
    } else {
        None
    };
    let nationality_item = if let Some(element) = nationality_element {
        Some(
            find_item(namespace_items, element)?
                .ok_or_else(|| MdocError::ElementMissing(element.to_string()))?,
        )
    } else {
        None
    };

    let parsed_birth = if let Some(item) = &birth_date_item {
        validate_item_digest(
            &mso.value_digests,
            birth_date_element.expect("AgeOver element is present"),
            item.digest_id,
            &item.bytes,
        )?;
        parse_birth_date_value(item)?
    } else {
        ParsedBirthDateValue::default()
    };
    let nationality_candidates = if let Some(item) = &nationality_item {
        validate_item_digest(
            &mso.value_digests,
            nationality_element.expect("Alpha2Set element is present"),
            item.digest_id,
            &item.bytes,
        )?;
        parse_nationality_value(item)?
    } else {
        Vec::new()
    };
    let parsed_nat = nationality_candidates.first().cloned().unwrap_or_default();

    let device_signed = map_field(doc_map, "deviceSigned")?;
    let device_auth = map_field(device_signed, "deviceAuth")?;
    let expected_device_payload = expected_current_device_authentication_bytes(
        request,
        value_field(device_signed, "nameSpaces")?,
    )?;
    let device_signature_value = value_field(device_auth, "deviceSignature")?;
    validate_current_product_device_signature_cose(device_signature_value)?;
    let device_signature =
        parse_cose_sign1_with_detached_payload(device_signature_value, &expected_device_payload)?;
    if device_signature.payload != expected_device_payload {
        return Err(MdocError::DeviceAuthPayloadMismatch);
    }
    verify_signature(
        &device_key,
        &device_signature.sig_structure,
        &device_signature.signature_bytes,
        "deviceSignature",
    )?;

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
        request_binding: request.request_binding,
        doctype,
        namespace: request.namespace.clone(),
        attributes: requested_attributes,
        extracted_attributes,
        birth_date_bytes: parsed_birth.bytes,
        birth_date_binding: parsed_birth.binding,
        nationality_binding: parsed_nat.binding,
        birth_date_value_offset: parsed_birth.offset,
        nationality_value_offset: parsed_nat.offset,
        nationality_candidates,
        valid_from_timestamp: mso.valid_from,
        valid_until_timestamp: mso.valid_until,
        birth_date_item: birth_date_item.map(|item| item.bytes).unwrap_or_default(),
        nationality_item: nationality_item.map(|item| item.bytes).unwrap_or_default(),
        mso: issuer_auth.payload,
        device_key,
        issuer_sig_structure: issuer_auth.sig_structure,
        issuer_ecdsa_input,
        device_ecdsa_input,
        revocation: request.revocation.clone(),
    })
}

fn current_product_document_map<'a>(
    value: &'a Value,
    request: &MdocPidRequest,
) -> Result<&'a [(Value, Value)], MdocError> {
    let document = expect_map(value, "product document")?;
    require_exact_text_fields(
        document,
        "product document keys",
        &["docType", "issuerSigned", "deviceSigned"],
    )?;

    let issuer_signed = map_field(document, "issuerSigned")?;
    require_exact_text_fields(
        issuer_signed,
        "issuerSigned keys",
        &["nameSpaces", "issuerAuth"],
    )?;
    let namespaces = map_field(issuer_signed, "nameSpaces")?;
    require_single_text_field(
        namespaces,
        &request.namespace,
        "issuerSigned.nameSpaces must contain exactly one PID namespace",
    )?;

    let device_signed = map_field(document, "deviceSigned")?;
    require_exact_text_fields(
        device_signed,
        "deviceSigned keys",
        &["nameSpaces", "deviceAuth"],
    )?;
    let device_auth = map_field(device_signed, "deviceAuth")?;
    require_exact_text_fields(device_auth, "deviceAuth keys", &["deviceSignature"])?;
    Ok(document)
}

fn require_single_text_field(
    map: &[(Value, Value)],
    expected: &str,
    label: &'static str,
) -> Result<(), MdocError> {
    if map.len() == 1 && map[0].0 == Value::Text(expected.to_string()) {
        Ok(())
    } else {
        Err(MdocError::InvalidProductDocumentShape(label))
    }
}

fn require_exact_text_fields(
    map: &[(Value, Value)],
    label: &'static str,
    expected: &[&str],
) -> Result<(), MdocError> {
    if map.len() != expected.len() {
        return Err(MdocError::InvalidProductDocumentShape(label));
    }
    let mut seen = vec![false; expected.len()];
    for (key, _) in map {
        let Value::Text(key) = key else {
            return Err(MdocError::InvalidProductDocumentShape(label));
        };
        let Some(index) = expected.iter().position(|expected| key == expected) else {
            return Err(MdocError::InvalidProductDocumentShape(label));
        };
        if std::mem::replace(&mut seen[index], true) {
            return Err(MdocError::InvalidProductDocumentShape(label));
        }
    }
    if seen.into_iter().all(|present| present) {
        Ok(())
    } else {
        Err(MdocError::InvalidProductDocumentShape(label))
    }
}

fn require_unique_digest_ids(map: &[(Value, Value)], label: &'static str) -> Result<(), MdocError> {
    let mut seen = HashSet::with_capacity(map.len());
    for (key, _) in map {
        let id = expect_u32(key, "digestID")?;
        if id > MDOC_SCOPE_MAX_DIGEST_ID || !seen.insert(id) {
            return Err(MdocError::InvalidProductDocumentShape(label));
        }
    }
    Ok(())
}

fn require_current_product_cose_key_fields(map: &[(Value, Value)]) -> Result<(), MdocError> {
    let mut seen = Vec::with_capacity(map.len());
    for (key, _) in map {
        let label = value_i128(key)
            .map_err(|_| MdocError::InvalidProductDocumentShape("deviceKey COSE_Key labels"))?;
        if !matches!(label, 1 | 3 | -1 | -2 | -3) || seen.contains(&label) {
            return Err(MdocError::InvalidProductDocumentShape(
                "deviceKey COSE_Key labels",
            ));
        }
        seen.push(label);
    }
    if [1, -1, -2, -3]
        .into_iter()
        .all(|required| seen.contains(&required))
        && matches!(map.len(), 4 | 5)
    {
        Ok(())
    } else {
        Err(MdocError::InvalidProductDocumentShape(
            "deviceKey COSE_Key labels",
        ))
    }
}

#[derive(Clone)]
struct ParsedBirthDateValue {
    bytes: [u8; 4],
    binding: MdocBirthDateBinding,
    offset: usize,
}

impl Default for ParsedBirthDateValue {
    fn default() -> Self {
        Self {
            bytes: [0; 4],
            binding: MdocBirthDateBinding(*b"0000-00-00"),
            offset: 0,
        }
    }
}

#[derive(Clone, Debug)]
pub struct ParsedNationalityValue {
    binding: MdocNationalityBinding,
    offset: usize,
}

impl Default for ParsedNationalityValue {
    fn default() -> Self {
        Self {
            binding: MdocNationalityBinding([0; 2]),
            offset: 0,
        }
    }
}

impl ParsedNationalityValue {
    fn predicate_code(&self) -> u32 {
        match self.binding {
            MdocNationalityBinding(alpha2) => u32::from(u16::from_be_bytes(alpha2)),
        }
    }
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
    valid_from: MdocTimestamp,
    valid_until: MdocTimestamp,
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
        Value::Tag(CBOR_TAG_FULL_DATE, inner) => {
            let text = expect_text(inner, "birth_date elementValue")?;
            parse_birth_date_text_value(item, text)
        }
        _ => Err(MdocError::WrongType("birth_date elementValue")),
    }
}

fn parse_birth_date_text_value(
    item: &ParsedItem,
    text: &str,
) -> Result<ParsedBirthDateValue, MdocError> {
    let (year, month, day) = parse_birth_date_text(text)?;
    let value_bytes = text.as_bytes();
    let offset = find_subslice(&item.bytes, value_bytes)
        .ok_or(MdocError::UnsupportedCircuitValue("birth_date text offset"))?;
    Ok(ParsedBirthDateValue {
        bytes: [(year >> 8) as u8, (year & 0xFF) as u8, month, day],
        binding: MdocBirthDateBinding(
            value_bytes
                .try_into()
                .map_err(|_| MdocError::UnsupportedCircuitValue("birth_date text length"))?,
        ),
        offset,
    })
}

fn parse_nationality_value(item: &ParsedItem) -> Result<Vec<ParsedNationalityValue>, MdocError> {
    let values = match &item.value {
        Value::Array(entries) if !entries.is_empty() => entries,
        Value::Array(_) => return Err(MdocError::WrongType("nationality elementValue")),
        _ => return Err(MdocError::WrongType("nationality elementValue")),
    };
    values
        .iter()
        .map(|value| parse_one_nationality(item, value))
        .collect()
}

fn parse_one_nationality(
    item: &ParsedItem,
    value: &Value,
) -> Result<ParsedNationalityValue, MdocError> {
    match value {
        Value::Text(alpha2) => {
            let bytes: [u8; 2] = alpha2
                .as_bytes()
                .try_into()
                .map_err(|_| MdocError::InvalidNationality(alpha2.clone()))?;
            if !predicates::is_valid_signed_alpha2(predicates::pack_alpha2(bytes)) {
                return Err(MdocError::InvalidNationality(alpha2.clone()));
            }
            let offset = find_subslice(&item.bytes, alpha2.as_bytes()).ok_or(
                MdocError::UnsupportedCircuitValue("nationality text offset"),
            )?;
            Ok(ParsedNationalityValue {
                binding: MdocNationalityBinding(bytes),
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

fn labeled_tdate_date_offset(
    mso: &[u8],
    label: &[u8],
    timestamp: MdocTimestamp,
    error: &'static str,
) -> Result<usize, MdocError> {
    let label_offset =
        find_subslice(mso, label).ok_or(MdocError::UnsupportedCircuitValue(error))?;
    let date_bytes = timestamp.text_bytes();
    let search_start = label_offset + label.len();
    let relative = find_subslice(&mso[search_start..], &date_bytes)
        .ok_or(MdocError::UnsupportedCircuitValue(error))?;
    Ok(search_start + relative)
}

fn cbor_uint_key(value: u32) -> Vec<u8> {
    match value {
        0..=23 => vec![value as u8],
        24..=0xFF => vec![0x18, value as u8],
        0x100..=0xFFFF => {
            let bytes = (value as u16).to_be_bytes();
            vec![0x19, bytes[0], bytes[1]]
        }
        _ => {
            let bytes = value.to_be_bytes();
            vec![0x1A, bytes[0], bytes[1], bytes[2], bytes[3]]
        }
    }
}

fn digest_anchor_bytes(digest_id: u32) -> Vec<u8> {
    let mut anchor = cbor_uint_key(digest_id);
    anchor.extend_from_slice(&[0x58, 0x20]);
    anchor
}

fn cbor_tdate_anchor_bytes(label: &str) -> Vec<u8> {
    assert!(label.len() < 24, "short text label expected");
    let mut anchor = Vec::with_capacity(1 + label.len() + 2);
    anchor.push(0x60 + label.len() as u8);
    anchor.extend_from_slice(label.as_bytes());
    anchor.extend_from_slice(&[0xC0, 0x74]);
    anchor
}

fn anchor_before_offset(
    preimage: &[u8],
    value_offset: usize,
    anchor: &[u8],
    error: &'static str,
) -> Result<usize, MdocError> {
    let anchor_offset = value_offset
        .checked_sub(anchor.len())
        .ok_or(MdocError::UnsupportedCircuitValue(error))?;
    ensure_value_window_with_message(preimage, anchor_offset, anchor, error)?;
    Ok(anchor_offset)
}

fn mdoc_scope_statement(statement: &MdocCircuitStatement) -> MdocScopeStatement {
    MdocScopeStatement {
        request_binding: statement.request_binding,
        doc_type: statement.doctype.as_bytes().to_vec(),
        namespace: statement.namespace.as_bytes().to_vec(),
        items: statement
            .attributes
            .iter()
            .map(|attribute| MdocScopeItem {
                element_identifier: attribute.element_identifier.as_bytes().to_vec(),
                mode: match attribute.mode {
                    MdocDisclosureMode::AgeOver => MdocScopeMode::AgeOver,
                    MdocDisclosureMode::Alpha2Set => MdocScopeMode::Alpha2Set,
                },
            })
            .collect(),
    }
}

fn mdoc_scope_parser_count(attribute_count: usize) -> Option<usize> {
    attribute_count.checked_mul(2)?.checked_add(3)
}

fn ts13_revocation_message_bytes(id_lo: u64, id_hi: u64, epoch: u32) -> [u8; 20] {
    let mut bytes = [0u8; TS13_REVOCATION_MESSAGE_LEN];
    bytes[..8].copy_from_slice(&id_lo.to_le_bytes());
    bytes[8..16].copy_from_slice(&id_hi.to_le_bytes());
    bytes[16..].copy_from_slice(&epoch.to_le_bytes());
    bytes
}

fn current_product_circuit_semantics(statement: &MdocCircuitStatement) -> bool {
    let mut age_indices =
        statement
            .attributes
            .iter()
            .enumerate()
            .filter_map(|(index, attribute)| {
                matches!(attribute.mode, MdocDisclosureMode::AgeOver).then_some(index)
            });
    let expected_age_index = age_indices.next();
    let unique_age = age_indices.next().is_none();
    let mut nationality_indices =
        statement
            .attributes
            .iter()
            .enumerate()
            .filter_map(|(index, attribute)| {
                matches!(attribute.mode, MdocDisclosureMode::Alpha2Set).then_some(index)
            });
    let expected_nationality_index = nationality_indices.next();
    let unique_nationality = nationality_indices.next().is_none();

    let current_attribute_layout = match statement.attributes.as_slice() {
        [attribute] => matches!(
            (attribute.element_identifier.as_str(), &attribute.mode),
            ("birth_date", MdocDisclosureMode::AgeOver)
                | ("nationality", MdocDisclosureMode::Alpha2Set)
        ),
        [birth_date, nationality] => {
            birth_date.element_identifier == "birth_date"
                && matches!(birth_date.mode, MdocDisclosureMode::AgeOver)
                && nationality.element_identifier == "nationality"
                && matches!(nationality.mode, MdocDisclosureMode::Alpha2Set)
        }
        _ => false,
    };

    statement.request_binding != [0u8; 32]
        && statement.doctype == PID_DOCTYPE
        && statement.namespace == PID_NAMESPACE
        && validate_product_policy(&statement.policy, statement.verification_time_epoch_seconds)
            .is_ok()
        && current_attribute_layout
        && unique_age
        && statement.age_attribute_index == expected_age_index
        && unique_nationality
        && statement.nationality_attribute_index == expected_nationality_index
}

fn current_product_public_semantics(statement: &MdocPublicStatement) -> bool {
    statement.request_binding != [0u8; 32]
        && statement.doctype == PID_DOCTYPE
        && statement.namespace == PID_NAMESPACE
        && validate_product_policy(&statement.policy, statement.verification_time_epoch_seconds)
            .is_ok()
        && validate_product_requested_attributes(&statement.attributes).is_ok()
}

fn ts13_revocation_p256_input(statement: &MdocCircuitStatement) -> EcdsaVerifyInput {
    let revocation = &statement.ts13_revocation;
    let range = &statement.ts13_revocation_range;
    let message = ts13_revocation_message_bytes(range.id_lo, range.id_hi, revocation.epoch);
    EcdsaVerifyInput {
        message_hash: U256(Sha256::digest(message).into()),
        signature: statement.ts13_revocation_signature.clone(),
        public_key: revocation.revocation_public_key.clone(),
    }
}

fn mdoc_p4b_mac_values(
    statement: &MdocCircuitStatement,
    revocation_input: &EcdsaVerifyInput,
) -> [eu_id_ec_coprocessor::mac::Gf128; eu_id_ec_coprocessor::ecdsa::MDOC_P4B_MAC_HALF_COUNT] {
    let [issuer_z_lo, issuer_z_hi] =
        eu_id_ec_coprocessor::ecdsa::gf128_halves_from_be32(statement.issuer_input.message_hash.0);
    let [device_qx_lo, device_qx_hi] =
        eu_id_ec_coprocessor::ecdsa::gf128_halves_from_be32(statement.device_input.public_key.x.0);
    let [device_qy_lo, device_qy_hi] =
        eu_id_ec_coprocessor::ecdsa::gf128_halves_from_be32(statement.device_input.public_key.y.0);
    let [revocation_z_lo, revocation_z_hi] =
        eu_id_ec_coprocessor::ecdsa::gf128_halves_from_be32(revocation_input.message_hash.0);
    [
        issuer_z_lo,
        issuer_z_hi,
        device_qx_lo,
        device_qx_hi,
        device_qy_lo,
        device_qy_hi,
        revocation_z_lo,
        revocation_z_hi,
    ]
}

/// The product nationality policy in packed ISO alpha-2 form.
fn nat_public_input_for(statement: &MdocCircuitStatement) -> predicates::NatPublicInput {
    statement.policy.nat_public_input()
}

/// Validates an untrusted product mdoc CBOR envelope before recursive decoding.
///
/// The byte-stream parser enforces the circuit's structural limits: one
/// complete root, definite-length containers, minimal arguments, and nesting
/// depth at most eight. Only structurally valid input reaches `ciborium`.
pub fn validate_product_mdoc_cbor_structure(bytes: &[u8]) -> Result<(), MdocError> {
    validate_product_cbor_structure(bytes)
}

/// Largest raw CBOR envelope accepted by the product structural parser.
pub const PRODUCT_MDOC_CBOR_MAX_BYTES: usize = crate::mdoc_cbor_stream::MDOC_CBOR_MAX_ACTIVE_BYTES;

fn validate_product_cbor_structure(bytes: &[u8]) -> Result<(), MdocError> {
    MdocCborWitness::new(bytes, MdocCborInputMode::Raw)
        .map_err(|error| MdocError::Cbor(error.to_string()))?;
    Ok(())
}

fn decode_value(bytes: &[u8]) -> Result<Value, MdocError> {
    let mut cursor = std::io::Cursor::new(bytes);
    let value = ciborium::de::from_reader(&mut cursor)
        .map_err(|error| MdocError::Cbor(error.to_string()))?;
    if cursor.position() != bytes.len() as u64 {
        return Err(MdocError::Cbor(
            "trailing bytes after the CBOR value".to_string(),
        ));
    }
    Ok(value)
}

fn encode_value(value: Value) -> Vec<u8> {
    let mut out = Vec::new();
    ciborium::ser::into_writer(&value, &mut out).expect("CBOR serialization into Vec");
    out
}

fn canonicalize_product_cbor_value(value: Value) -> Result<Value, MdocError> {
    match value {
        Value::Array(values) => Ok(Value::Array(
            values
                .into_iter()
                .map(canonicalize_product_cbor_value)
                .collect::<Result<Vec<_>, _>>()?,
        )),
        Value::Tag(tag, value) => Ok(Value::Tag(
            tag,
            Box::new(canonicalize_product_cbor_value(*value)?),
        )),
        Value::Map(entries) => {
            let mut canonical = entries
                .into_iter()
                .map(|(key, value)| {
                    let key = canonicalize_product_cbor_value(key)?;
                    let value = canonicalize_product_cbor_value(value)?;
                    let encoded_key = encode_value(key.clone());
                    Ok((encoded_key, key, value))
                })
                .collect::<Result<Vec<_>, MdocError>>()?;
            canonical.sort_by(|left, right| {
                left.0
                    .len()
                    .cmp(&right.0.len())
                    .then_with(|| left.0.cmp(&right.0))
            });
            if canonical.windows(2).any(|pair| pair[0].0 == pair[1].0) {
                return Err(MdocError::NonCanonicalSessionTranscript);
            }
            Ok(Value::Map(
                canonical
                    .into_iter()
                    .map(|(_, key, value)| (key, value))
                    .collect(),
            ))
        }
        Value::Float(_) => Err(MdocError::NonCanonicalSessionTranscript),
        scalar => Ok(scalar),
    }
}

/// Enforces the deterministic CBOR subset used by the EUDI product request.
///
/// This function requires the exact OpenID4VP SessionTranscript shape used by
/// the product profile. It also requires preferred-length encodings, definite
/// containers, recursive deterministic map order, and unique canonical map
/// keys.
/// The product profile excludes floating-point values. This is not a
/// general-purpose RFC 8949 deterministic-encoding validator.
pub fn validate_product_session_transcript_cbor(
    session_transcript: &[u8],
) -> Result<(), MdocError> {
    if session_transcript.len() != PRODUCT_SESSION_TRANSCRIPT_BYTES {
        return Err(MdocError::InvalidProductDocumentShape(
            "SessionTranscript must be exactly 56 canonical bytes",
        ));
    }
    validate_product_cbor_structure(session_transcript)?;
    let value = decode_value(session_transcript)?;
    let Value::Array(outer) = &value else {
        return Err(MdocError::WrongType("SessionTranscript"));
    };
    let [Value::Null, Value::Null, Value::Array(handover)] = outer.as_slice() else {
        return Err(MdocError::InvalidProductDocumentShape(
            "SessionTranscript must be exact OpenID4VP handover",
        ));
    };
    let [Value::Text(label), Value::Bytes(hash)] = handover.as_slice() else {
        return Err(MdocError::InvalidProductDocumentShape(
            "OpenID4VP handover must contain label and 32-byte hash",
        ));
    };
    if label != "OpenID4VPHandover" || hash.len() != 32 {
        return Err(MdocError::InvalidProductDocumentShape(
            "OpenID4VP handover must contain label and 32-byte hash",
        ));
    }
    let canonical = encode_value(canonicalize_product_cbor_value(value)?);
    if canonical != session_transcript {
        return Err(MdocError::NonCanonicalSessionTranscript);
    }
    Ok(())
}

fn cbor_value_head(value: &[u8]) -> Result<Vec<u8>, MdocError> {
    if value.is_empty() {
        return Err(MdocError::UnsupportedCircuitValue(
            "attribute value CBOR head",
        ));
    }
    match value[0] {
        0xF4 | 0xF5 => Ok(value[..1].to_vec()),
        0x60..=0x77 => Ok(value[..1].to_vec()),
        0x78 => {
            if value.len() < 2 {
                return Err(MdocError::UnsupportedCircuitValue(
                    "attribute value CBOR head",
                ));
            }
            Ok(value[..2].to_vec())
        }
        0x79 => {
            if value.len() < 3 {
                return Err(MdocError::UnsupportedCircuitValue(
                    "attribute value CBOR head",
                ));
            }
            Ok(value[..3].to_vec())
        }
        0xD9 if value.get(1..3) == Some(&[0x03, 0xEC]) => {
            let inner = value.get(3).ok_or(MdocError::UnsupportedCircuitValue(
                "attribute value CBOR head",
            ))?;
            match inner {
                0x60..=0x77 => Ok(value[..4].to_vec()),
                0x78 => {
                    if value.len() < 5 {
                        return Err(MdocError::UnsupportedCircuitValue(
                            "attribute value CBOR head",
                        ));
                    }
                    Ok(value[..5].to_vec())
                }
                _ => Err(MdocError::UnsupportedCircuitValue(
                    "attribute value CBOR head",
                )),
            }
        }
        _ => Err(MdocError::UnsupportedCircuitValue(
            "attribute value CBOR head",
        )),
    }
}

fn cbor_text_value_head(text: &str) -> Result<Vec<u8>, MdocError> {
    cbor_value_head(&encode_value(Value::Text(text.to_string())))
}

fn element_identifier_anchor_bytes(element_identifier: &str) -> Result<Vec<u8>, MdocError> {
    let mut anchor = encode_value(Value::Text("elementIdentifier".to_string()));
    anchor.extend_from_slice(&cbor_text_value_head(element_identifier)?);
    Ok(anchor)
}

fn parse_cose_sign1(value: &Value) -> Result<CoseSign1, MdocError> {
    parse_cose_sign1_inner(value, None)
}

fn parse_cose_sign1_with_detached_payload(
    value: &Value,
    detached_payload: &[u8],
) -> Result<CoseSign1, MdocError> {
    parse_cose_sign1_inner(value, Some(detached_payload))
}

fn validate_current_product_device_signature_cose(value: &Value) -> Result<(), MdocError> {
    let items = expect_array(value, "deviceSignature")?;
    if items.len() != 4 {
        return Err(MdocError::InvalidCoseSign1("expected four-element array"));
    }
    if !expect_map(&items[1], "deviceSignature.unprotected")?.is_empty() {
        return Err(MdocError::InvalidProductDocumentShape(
            "deviceSignature unprotected header must be empty",
        ));
    }
    if !matches!(items[2], Value::Null) {
        return Err(MdocError::InvalidProductDocumentShape(
            "deviceSignature payload must be detached",
        ));
    }
    Ok(())
}

fn parse_cose_sign1_inner(
    value: &Value,
    detached_payload: Option<&[u8]>,
) -> Result<CoseSign1, MdocError> {
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
    let payload = match (&items[2], detached_payload) {
        (Value::Bytes(payload), _) => payload.clone(),
        (Value::Null, Some(detached_payload)) => detached_payload.to_vec(),
        (Value::Null, None) => return Err(MdocError::InvalidCoseSign1("detached payload")),
        _ => return Err(MdocError::WrongType("COSE_Sign1.payload")),
    };
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

pub fn openid4vp_session_transcript(handover_info: &[u8]) -> Vec<u8> {
    encode_value(Value::Array(vec![
        Value::Null,
        Value::Null,
        Value::Array(vec![
            "OpenID4VPHandover".into(),
            Value::Bytes(Sha256::digest(handover_info).to_vec()),
        ]),
    ]))
}

pub fn device_authentication_bytes(
    session_transcript: &[u8],
    doc_type: &str,
) -> Result<Vec<u8>, MdocError> {
    device_authentication_bytes_with_namespaces(
        session_transcript,
        doc_type,
        &canonical_empty_device_namespaces(),
    )
}

fn device_authentication_bytes_with_namespaces(
    session_transcript: &[u8],
    doc_type: &str,
    device_namespaces: &Value,
) -> Result<Vec<u8>, MdocError> {
    let session_transcript = decode_value(session_transcript)?;
    if !matches!(session_transcript, Value::Array(_)) {
        return Err(MdocError::WrongType("SessionTranscript"));
    }

    let device_authentication = encode_value(Value::Array(vec![
        "DeviceAuthentication".into(),
        session_transcript,
        doc_type.into(),
        device_namespaces.clone(),
    ]));
    Ok(encode_value(Value::Tag(
        24,
        Box::new(Value::Bytes(device_authentication)),
    )))
}

fn canonical_empty_device_namespaces() -> Value {
    Value::Tag(
        CBOR_TAG_ENCODED_CBOR,
        Box::new(Value::Bytes(encode_value(Value::Map(Vec::new())))),
    )
}

fn expected_current_device_authentication_bytes(
    request: &MdocPidRequest,
    received_device_namespaces: &Value,
) -> Result<Vec<u8>, MdocError> {
    if received_device_namespaces != &canonical_empty_device_namespaces() {
        return Err(MdocError::InvalidProductDocumentShape(
            "deviceSigned.nameSpaces must be exact canonical empty DeviceNameSpacesBytes",
        ));
    }
    device_authentication_bytes_with_namespaces(
        &request.session_transcript,
        &request.doctype,
        received_device_namespaces,
    )
}

pub fn device_authentication_sig_structure_hash(
    session_transcript: &[u8],
    doc_type: &str,
) -> Result<[u8; 32], MdocError> {
    let payload = device_authentication_bytes(session_transcript, doc_type)?;
    Ok(Sha256::digest(sig_structure(ES256_PROTECTED_HEADER, &payload)).into())
}

struct DemoMdocDocument {
    bytes: Vec<u8>,
    mso_payload: Vec<u8>,
    issuer_key: AffinePoint,
}

fn demo_mdoc_document(session_transcript: &[u8]) -> DemoMdocDocument {
    demo_mdoc_document_with_values(session_transcript, "1990-07-15", &["DE"])
}

fn demo_mdoc_document_with_values(
    session_transcript: &[u8],
    birth_date: &str,
    nationalities: &[&str],
) -> DemoMdocDocument {
    let issuer_signing_key =
        SigningKey::from_bytes((&[7u8; 32]).into()).expect("demo issuer signing key");
    let device_signing_key =
        SigningKey::from_bytes((&[11u8; 32]).into()).expect("demo device signing key");
    let issuer_certificate = demo_self_signed_certificate_der(&issuer_signing_key);
    let issuer_key = demo_affine_point(&issuer_signing_key);
    let device_cose_key = demo_cose_key(&device_signing_key);

    // Profile v2: canonical IssuerSignedItemBytes with PID Rulebook values.
    let birth_date_item = demo_issuer_signed_item(
        7,
        "birth_date",
        Value::Tag(
            CBOR_TAG_FULL_DATE,
            Box::new(Value::Text(birth_date.to_string())),
        ),
        DEMO_PRIVATE_RANDOM_CANARY.to_vec(),
    );
    let nationality_item = demo_issuer_signed_item(
        9,
        "nationality",
        Value::Array(
            nationalities
                .iter()
                .map(|value| Value::Text((*value).to_string()))
                .collect(),
        ),
        vec![9; 16],
    );
    let birth_digest: [u8; 32] = Sha256::digest(&birth_date_item).into();
    let nat_digest: [u8; 32] = Sha256::digest(&nationality_item).into();
    let value_digest_entries = vec![
        (Value::from(7), Value::Bytes(birth_digest.to_vec())),
        (Value::from(9), Value::Bytes(nat_digest.to_vec())),
    ];
    let namespace_items = vec![
        decode_value(&birth_date_item).expect("demo birth date item decodes"),
        decode_value(&nationality_item).expect("demo nationality item decodes"),
    ];
    let mso = canonicalize_product_cbor_value(Value::Map(vec![
        ("version".into(), MDOC_PROFILE_VERSION.into()),
        ("docType".into(), PID_DOCTYPE.into()),
        ("digestAlgorithm".into(), "SHA-256".into()),
        (
            "valueDigests".into(),
            Value::Map(vec![(
                PID_NAMESPACE.into(),
                Value::Map(value_digest_entries),
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
    ]))
    .expect("demo MSO canonicalizes");
    let mso = encode_value(mso);
    let mso_payload = encode_value(Value::Tag(
        CBOR_TAG_ENCODED_CBOR,
        Box::new(Value::Bytes(mso)),
    ));

    let issuer_auth = demo_cose_sign1(
        &issuer_signing_key,
        Value::Map(vec![(
            Value::from(33),
            Value::Bytes(issuer_certificate.clone()),
        )]),
        &mso_payload,
    );
    let device_signature = demo_cose_sign1_detached(
        &device_signing_key,
        Value::Map(Vec::new()),
        &device_authentication_bytes(session_transcript, PID_DOCTYPE)
            .expect("demo device auth payload builds"),
    );

    let bytes = encode_value(Value::Map(vec![
        ("docType".into(), PID_DOCTYPE.into()),
        (
            "issuerSigned".into(),
            Value::Map(vec![
                (
                    "nameSpaces".into(),
                    Value::Map(vec![(PID_NAMESPACE.into(), Value::Array(namespace_items))]),
                ),
                ("issuerAuth".into(), issuer_auth),
            ]),
        ),
        (
            "deviceSigned".into(),
            Value::Map(vec![
                ("nameSpaces".into(), canonical_empty_device_namespaces()),
                (
                    "deviceAuth".into(),
                    Value::Map(vec![("deviceSignature".into(), device_signature)]),
                ),
            ]),
        ),
    ]));
    DemoMdocDocument {
        bytes,
        mso_payload,
        issuer_key,
    }
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

fn demo_affine_point(signing_key: &SigningKey) -> AffinePoint {
    let encoded = signing_key.verifying_key().to_encoded_point(false);
    let x: [u8; 32] = encoded.x().expect("demo key has x coordinate")[..]
        .try_into()
        .expect("demo x coordinate length");
    let y: [u8; 32] = encoded.y().expect("demo key has y coordinate")[..]
        .try_into()
        .expect("demo y coordinate length");
    AffinePoint {
        x: U256(x),
        y: U256(y),
    }
}

fn demo_der_tlv(tag: u8, value: Vec<u8>) -> Vec<u8> {
    let mut encoded = vec![tag];
    if value.len() < 128 {
        encoded.push(value.len() as u8);
    } else {
        let length = (value.len() as u64).to_be_bytes();
        let first = length
            .iter()
            .position(|byte| *byte != 0)
            .unwrap_or(length.len() - 1);
        encoded.push(0x80 | u8::try_from(length.len() - first).expect("DER length byte count"));
        encoded.extend_from_slice(&length[first..]);
    }
    encoded.extend(value);
    encoded
}

fn demo_der_sequence(fields: Vec<Vec<u8>>) -> Vec<u8> {
    demo_der_tlv(0x30, fields.concat())
}

fn demo_der_integer(value: u64) -> Vec<u8> {
    let bytes = value.to_be_bytes();
    let first = bytes
        .iter()
        .position(|byte| *byte != 0)
        .unwrap_or(bytes.len() - 1);
    let mut value = bytes[first..].to_vec();
    if value[0] & 0x80 != 0 {
        value.insert(0, 0);
    }
    demo_der_tlv(0x02, value)
}

fn demo_der_bit_string(bytes: &[u8]) -> Vec<u8> {
    let mut value = Vec::with_capacity(bytes.len() + 1);
    value.push(0);
    value.extend_from_slice(bytes);
    demo_der_tlv(0x03, value)
}

fn demo_ecdsa_sha256_algorithm_identifier() -> Vec<u8> {
    demo_der_sequence(vec![demo_der_tlv(
        0x06,
        vec![0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x04, 0x03, 0x02],
    )])
}

fn demo_p256_subject_public_key_info(signing_key: &SigningKey) -> Vec<u8> {
    let point = signing_key.verifying_key().to_encoded_point(false);
    demo_der_sequence(vec![
        demo_der_sequence(vec![
            demo_der_tlv(0x06, vec![0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x02, 0x01]),
            demo_der_tlv(0x06, vec![0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x03, 0x01, 0x07]),
        ]),
        demo_der_bit_string(point.as_bytes()),
    ])
}

fn demo_self_signed_certificate_der(signing_key: &SigningKey) -> Vec<u8> {
    let signature_algorithm = demo_ecdsa_sha256_algorithm_identifier();
    let tbs = demo_der_sequence(vec![
        demo_der_tlv(0xA0, demo_der_integer(2)),
        demo_der_integer(1),
        signature_algorithm.clone(),
        demo_der_sequence(Vec::new()),
        demo_der_sequence(vec![
            demo_der_tlv(0x17, b"260101000000Z".to_vec()),
            demo_der_tlv(0x17, b"300101000000Z".to_vec()),
        ]),
        demo_der_sequence(Vec::new()),
        demo_p256_subject_public_key_info(signing_key),
    ]);
    let signature: P256Signature = signing_key.sign(&tbs);
    demo_der_sequence(vec![
        tbs,
        signature_algorithm,
        demo_der_bit_string(signature.to_der().as_bytes()),
    ])
}

fn demo_issuer_signed_item(
    digest_id: u64,
    element: &str,
    value: Value,
    random: Vec<u8>,
) -> Vec<u8> {
    // Profile v2 canonical (RFC 8949 core deterministic) key order:
    // shortest-encoded-key-first ⇒ `random, digestID, elementValue,
    // elementIdentifier` with key lengths 7, 8, 12, and 17 bytes.
    let item = Value::Map(vec![
        ("random".into(), Value::Bytes(random)),
        ("digestID".into(), Value::from(digest_id)),
        ("elementValue".into(), value),
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

fn demo_cose_sign1_detached(signing_key: &SigningKey, unprotected: Value, payload: &[u8]) -> Value {
    let mut cose = demo_cose_sign1(signing_key, unprotected, payload);
    let Value::Array(items) = &mut cose else {
        unreachable!("demo COSE_Sign1 is an array");
    };
    items[2] = Value::Null;
    cose
}

fn parse_mso(bytes: &[u8], namespace: &str) -> Result<ParsedMso, MdocError> {
    let value = decode_value(bytes)?;
    let value = match value {
        Value::Tag(CBOR_TAG_ENCODED_CBOR, inner) => {
            let mso_bytes = expect_bytes(&inner, "MobileSecurityObjectBytes")?;
            decode_value(mso_bytes)?
        }
        value => value,
    };
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
    parse_tdate(value_field(validity_info, "signed")?, "validityInfo.signed")?;
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
        valid_from,
        valid_until,
    })
}

fn validate_current_product_mso_payload(payload: &[u8]) -> Result<(), MdocError> {
    validate_product_cbor_structure(payload)?;
    let Value::Tag(CBOR_TAG_ENCODED_CBOR, encoded_mso) = decode_value(payload)? else {
        return Err(MdocError::InvalidProductDocumentShape(
            "issuerAuth payload must be MobileSecurityObjectBytes",
        ));
    };
    let mso_bytes = expect_bytes(&encoded_mso, "MobileSecurityObjectBytes")?;
    validate_product_cbor_structure(mso_bytes)?;
    let mso = decode_value(mso_bytes)?;
    let mso = expect_map(&mso, "MobileSecurityObject")?;
    validate_current_product_mso_fields(mso)?;
    // ISO map semantics do not impose key order. The V2 scope DFA proves the
    // exact MSO field set, types, and uniqueness while accepting any order.
    // The byte parser above still requires definite, preferred-length CBOR.
    Ok(())
}

fn validate_current_product_mso_fields(mso: &[(Value, Value)]) -> Result<(), MdocError> {
    require_exact_text_fields(
        mso,
        "MobileSecurityObject keys",
        &[
            "version",
            "docType",
            "digestAlgorithm",
            "valueDigests",
            "deviceKeyInfo",
            "validityInfo",
        ],
    )?;

    let value_digests = map_field(mso, "valueDigests")?;
    require_single_text_field(
        value_digests,
        PID_NAMESPACE,
        "valueDigests must contain exactly one PID namespace",
    )?;
    let namespace_digests = expect_map(&value_digests[0].1, "valueDigests PID namespace")?;
    require_unique_digest_ids(namespace_digests, "duplicate valueDigests digestID")?;

    let device_key_info = map_field(mso, "deviceKeyInfo")?;
    require_exact_text_fields(device_key_info, "deviceKeyInfo keys", &["deviceKey"])?;
    let device_key = expect_map(
        value_field(device_key_info, "deviceKey")?,
        "deviceKey COSE_Key",
    )?;
    require_current_product_cose_key_fields(device_key)?;

    let validity_info = map_field(mso, "validityInfo")?;
    match validity_info.len() {
        3 => require_exact_text_fields(
            validity_info,
            "validityInfo keys",
            &["signed", "validFrom", "validUntil"],
        ),
        4 => require_exact_text_fields(
            validity_info,
            "validityInfo keys",
            &["signed", "validFrom", "validUntil", "expectedUpdate"],
        ),
        _ => Err(MdocError::InvalidProductDocumentShape("validityInfo keys")),
    }?;
    if validity_info.len() == 4 {
        parse_tdate(
            value_field(validity_info, "expectedUpdate")?,
            "validityInfo.expectedUpdate",
        )?;
    }
    Ok(())
}

fn parse_tdate(value: &Value, field: &'static str) -> Result<MdocTimestamp, MdocError> {
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
    if !is_gregorian_date(year, month, day) || hour > 23 || minute > 59 || second > 59 {
        return Err(MdocError::InvalidTdate(field));
    }
    Ok(MdocTimestamp {
        year,
        month,
        day,
        hour,
        minute,
        second,
    })
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
        let item_bytes = issuer_signed_item_bytes(item)?;
        let parsed = parse_issuer_signed_item_bytes(&item_bytes)?;
        if parsed.element == element {
            return Ok(Some(parsed));
        }
    }
    Ok(None)
}

fn validate_current_product_selected_items(
    items: &[Value],
    requested_attributes: &[MdocRequestedAttribute],
) -> Result<(), MdocError> {
    let mut counts = vec![0usize; requested_attributes.len()];
    for item in items {
        let item_bytes = issuer_signed_item_bytes(item)?;
        let parsed = parse_issuer_signed_item_bytes(&item_bytes)?;
        for (index, requested) in requested_attributes.iter().enumerate() {
            if parsed.element == requested.element_identifier {
                if parsed.digest_id > MDOC_SCOPE_MAX_DIGEST_ID {
                    return Err(MdocError::InvalidProductDocumentShape(
                        "requested PID digestID exceeds product bound",
                    ));
                }
                counts[index] += 1;
            }
        }
    }
    if counts.into_iter().all(|count| count == 1) {
        Ok(())
    } else {
        Err(MdocError::InvalidProductDocumentShape(
            "each requested PID element must occur exactly once",
        ))
    }
}

fn issuer_signed_item_bytes(item: &Value) -> Result<Vec<u8>, MdocError> {
    match item {
        Value::Tag(CBOR_TAG_ENCODED_CBOR, inner) => {
            expect_bytes(inner, "IssuerSignedItemBytes")?;
            Ok(encode_value(item.clone()))
        }
        _ => Err(MdocError::WrongType("IssuerSignedItemBytes")),
    }
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

/// Checks the four `IssuerSignedItem` keys in RFC 8949 canonical order.
fn ensure_issuer_signed_item_key_order(item: &[(Value, Value)]) -> Result<(), MdocError> {
    const KEY_SET: [&str; 4] = ["elementValue", "digestID", "random", "elementIdentifier"];
    const V2_CANONICAL: [&str; 4] = ["random", "digestID", "elementValue", "elementIdentifier"];
    if item.len() != KEY_SET.len() {
        return Err(MdocError::UnsupportedCircuitValue(
            "IssuerSignedItem key set",
        ));
    }
    for expected in KEY_SET {
        let present = item
            .iter()
            .any(|(key, _)| key == &Value::Text(expected.to_string()));
        if !present {
            return Err(MdocError::UnsupportedCircuitValue(
                "IssuerSignedItem key set",
            ));
        }
    }
    let canonical = item
        .iter()
        .map(|(key, _)| key)
        .zip(V2_CANONICAL)
        .all(|(key, expected)| key == &Value::Text(expected.to_string()));
    if !canonical {
        return Err(MdocError::UnsupportedCircuitValue(
            "IssuerSignedItem canonical key order",
        ));
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
    if !(4..=5).contains(&key.len()) {
        return Err(MdocError::InvalidCoseKey("expected ES256 P-256 key"));
    }
    let kty = int_field(key, 1, "COSE_Key.kty")?;
    let crv = int_field(key, -1, "COSE_Key.crv")?;
    let alg = value_int_key(key, 3)
        .map(value_i128)
        .transpose()
        .map_err(|_| MdocError::InvalidCoseKey("expected ES256 P-256 key"))?;
    if kty != 2 || alg.is_some_and(|alg| alg != -7) || crv != 1 {
        return Err(MdocError::InvalidCoseKey("expected ES256 P-256 key"));
    }
    let x = expect_32(bytes_int_field(key, -2, "COSE_Key.x")?, "COSE_Key.x")?;
    let y = expect_32(bytes_int_field(key, -3, "COSE_Key.y")?, "COSE_Key.y")?;
    Ok(AffinePoint {
        x: U256(x),
        y: U256(y),
    })
}

fn current_product_issuer_key_from_unprotected(
    unprotected: &[(Value, Value)],
    request: &MdocPidRequest,
) -> Result<AffinePoint, MdocError> {
    if unprotected.len() != 1 || value_i128(&unprotected[0].0).ok() != Some(33) {
        return Err(MdocError::InvalidProductDocumentShape(
            "issuerAuth unprotected header must contain only x5chain",
        ));
    }
    caller_authoritative_leaf_key(&unprotected[0].1, &request.required_issuer_public_key)
}

fn caller_authoritative_leaf_key(
    x5chain: &Value,
    required_key: &AffinePoint,
) -> Result<AffinePoint, MdocError> {
    let certificates = x5chain_certificates(x5chain)?;
    if certificates.len() != 1 {
        return Err(MdocError::InvalidCertificate(
            "x5chain must contain exactly one leaf certificate",
        ));
    }
    let certificate = parse_x509_certificate(certificates[0])?;
    let issuer_key = affine_point_from_spki(certificate.spki_der)?;
    if &issuer_key != required_key {
        return Err(MdocError::UntrustedIssuerCertificate);
    }
    Ok(issuer_key)
}

fn x5chain_certificates(value: &Value) -> Result<Vec<&[u8]>, MdocError> {
    match value {
        Value::Bytes(certificate) => Ok(vec![certificate.as_slice()]),
        Value::Array(certificates) => {
            if certificates.is_empty() {
                return Err(MdocError::InvalidCertificate("empty x5chain"));
            }
            certificates
                .iter()
                .map(|certificate| expect_bytes(certificate, "x5chain certificate"))
                .collect()
        }
        _ => Err(MdocError::WrongType("x5chain")),
    }
}

#[derive(Clone, Copy)]
struct ParsedCertificate<'a> {
    spki_der: &'a [u8],
}

#[derive(Clone, Copy)]
struct DerTlv<'a> {
    tag: u8,
    value: &'a [u8],
    full: &'a [u8],
}

fn parse_x509_certificate(certificate: &[u8]) -> Result<ParsedCertificate<'_>, MdocError> {
    let mut certificate_input = certificate;
    let certificate = der_read_tlv(&mut certificate_input, "certificate")?;
    if certificate.tag != 0x30 || !certificate_input.is_empty() {
        return Err(MdocError::InvalidCertificate("certificate sequence"));
    }

    let mut certificate_fields = certificate.value;
    let tbs = der_read_tlv(&mut certificate_fields, "certificate.tbsCertificate")?;
    if tbs.tag != 0x30 {
        return Err(MdocError::InvalidCertificate("tbsCertificate sequence"));
    }
    let _signature_algorithm =
        der_read_tlv(&mut certificate_fields, "certificate.signatureAlgorithm")?;
    let signature = der_read_tlv(&mut certificate_fields, "certificate.signatureValue")?;
    if signature.tag != 0x03 || !certificate_fields.is_empty() {
        return Err(MdocError::InvalidCertificate("certificate signature"));
    }
    der_bit_string_bytes(signature, "certificate.signatureValue")?;

    let spki_der = certificate_spki_der(tbs.value)?;
    Ok(ParsedCertificate { spki_der })
}

fn certificate_spki_der(tbs_certificate: &[u8]) -> Result<&[u8], MdocError> {
    let mut fields = tbs_certificate;
    let first = der_read_tlv(&mut fields, "tbsCertificate.first")?;
    if first.tag != 0xA0 {
        fields = tbs_certificate;
    }
    for field in [
        "tbsCertificate.serialNumber",
        "tbsCertificate.signature",
        "tbsCertificate.issuer",
        "tbsCertificate.validity",
        "tbsCertificate.subject",
    ] {
        let _ = der_read_tlv(&mut fields, field)?;
    }
    let spki = der_read_tlv(&mut fields, "tbsCertificate.subjectPublicKeyInfo")?;
    if spki.tag != 0x30 {
        return Err(MdocError::InvalidCertificate(
            "subjectPublicKeyInfo sequence",
        ));
    }
    Ok(spki.full)
}

fn der_read_tlv<'a>(input: &mut &'a [u8], label: &'static str) -> Result<DerTlv<'a>, MdocError> {
    if input.len() < 2 {
        return Err(MdocError::InvalidCertificate(label));
    }
    let original = *input;
    let tag = original[0];
    let first_len = original[1];
    let (len, len_len) = if first_len & 0x80 == 0 {
        (usize::from(first_len), 1)
    } else {
        let len_len = usize::from(first_len & 0x7F);
        if len_len == 0 || len_len > std::mem::size_of::<usize>() || original.len() < 2 + len_len {
            return Err(MdocError::InvalidCertificate(label));
        }
        let mut len = 0usize;
        for byte in &original[2..2 + len_len] {
            len = len
                .checked_mul(256)
                .and_then(|value| value.checked_add(usize::from(*byte)))
                .ok_or(MdocError::InvalidCertificate(label))?;
        }
        (len, 1 + len_len)
    };
    let header_len = 1 + len_len;
    let end = header_len
        .checked_add(len)
        .ok_or(MdocError::InvalidCertificate(label))?;
    if original.len() < end {
        return Err(MdocError::InvalidCertificate(label));
    }
    let value = &original[header_len..end];
    let full = &original[..end];
    *input = &original[end..];
    Ok(DerTlv { tag, value, full })
}

fn der_bit_string_bytes<'a>(
    bit_string: DerTlv<'a>,
    label: &'static str,
) -> Result<&'a [u8], MdocError> {
    if bit_string.value.first() != Some(&0) {
        return Err(MdocError::InvalidCertificate(label));
    }
    Ok(&bit_string.value[1..])
}

fn affine_point_from_spki(spki_der: &[u8]) -> Result<AffinePoint, MdocError> {
    let verifying_key = VerifyingKey::from_public_key_der(spki_der)
        .map_err(|_| MdocError::InvalidCertificate("subjectPublicKeyInfo"))?;
    let encoded = verifying_key.to_encoded_point(false);
    let x: [u8; 32] = encoded.x().ok_or(MdocError::InvalidCertificate(
        "subjectPublicKeyInfo x coordinate",
    ))?[..]
        .try_into()
        .map_err(|_| MdocError::InvalidCertificate("subjectPublicKeyInfo x coordinate"))?;
    let y: [u8; 32] = encoded.y().ok_or(MdocError::InvalidCertificate(
        "subjectPublicKeyInfo y coordinate",
    ))?[..]
        .try_into()
        .map_err(|_| MdocError::InvalidCertificate("subjectPublicKeyInfo y coordinate"))?;
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
    /// Domain-separated binding of the complete verifier-controlled request.
    pub request_binding: [u8; 32],
    /// Requested document type and namespace. These are public protocol scope,
    /// not credential witness material.
    pub doctype: String,
    pub namespace: String,
    pub issuer_input: EcdsaVerifyInput,
    pub device_input: EcdsaVerifyInput,
    /// Verifier-authoritative UTC time used for strict credential validity.
    pub verification_time_epoch_seconds: u64,
    pub ts13_revocation: MdocRevocationPublicInputs,
    pub ts13_revocation_range: MdocRevocationRangeWitness,
    pub ts13_revocation_signature: Signature,
    pub attributes: Vec<MdocStatementAttribute>,
    pub age_attribute_index: Option<usize>,
    pub nationality_attribute_index: Option<usize>,
    pub policy: Policy,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocPublicStatement {
    pub request_binding: [u8; 32],
    pub doctype: String,
    pub namespace: String,
    pub issuer_public_key: AffinePoint,
    pub device_message_hash: U256,
    pub verification_time_epoch_seconds: u64,
    pub ts13_revocation: MdocRevocationPublicInputs,
    /// Verifier-requested private predicate scope.
    pub attributes: Vec<MdocRequestedAttribute>,
    pub policy: Policy,
}

impl MdocPublicStatement {
    pub fn from_circuit(statement: &MdocCircuitStatement) -> Self {
        Self {
            request_binding: statement.request_binding,
            doctype: statement.doctype.clone(),
            namespace: statement.namespace.clone(),
            issuer_public_key: statement.issuer_input.public_key.clone(),
            device_message_hash: statement.device_input.message_hash.clone(),
            verification_time_epoch_seconds: statement.verification_time_epoch_seconds,
            ts13_revocation: statement.ts13_revocation.clone(),
            attributes: statement
                .attributes
                .iter()
                .map(|attribute| MdocRequestedAttribute {
                    element_identifier: attribute.element_identifier.clone(),
                    mode: attribute.mode.clone(),
                })
                .collect(),
            policy: statement.policy.clone(),
        }
    }

    fn age_attribute_index(&self) -> Option<usize> {
        self.attributes
            .iter()
            .position(|attribute| matches!(attribute.mode, MdocDisclosureMode::AgeOver))
    }

    fn nationality_attribute_index(&self) -> Option<usize> {
        self.attributes
            .iter()
            .position(|attribute| matches!(attribute.mode, MdocDisclosureMode::Alpha2Set))
    }

    fn verifier_circuit_statement(&self) -> MdocCircuitStatement {
        let zero_sig = Signature {
            r: U256([0u8; 32]),
            s: U256([0u8; 32]),
        };
        let age_attribute_index = self.age_attribute_index();
        let nationality_attribute_index = self.nationality_attribute_index();
        let attributes = self
            .attributes
            .iter()
            .map(|attribute| MdocStatementAttribute {
                element_identifier: attribute.element_identifier.clone(),
                mode: attribute.mode.clone(),
            })
            .collect();
        MdocCircuitStatement {
            request_binding: self.request_binding,
            doctype: self.doctype.clone(),
            namespace: self.namespace.clone(),
            issuer_input: EcdsaVerifyInput {
                message_hash: U256([0u8; 32]),
                signature: zero_sig.clone(),
                public_key: self.issuer_public_key.clone(),
            },
            device_input: EcdsaVerifyInput {
                message_hash: self.device_message_hash.clone(),
                signature: zero_sig.clone(),
                public_key: AffinePoint {
                    x: U256([0u8; 32]),
                    y: U256([0u8; 32]),
                },
            },
            verification_time_epoch_seconds: self.verification_time_epoch_seconds,
            ts13_revocation: self.ts13_revocation.clone(),
            ts13_revocation_range: MdocRevocationRangeWitness {
                id: 0,
                id_lo: 0,
                id_hi: 0,
            },
            ts13_revocation_signature: zero_sig,
            attributes,
            age_attribute_index,
            nationality_attribute_index,
            policy: self.policy.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocRevocationPublicInputs {
    pub revocation_public_key: AffinePoint,
    pub epoch: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocRevocationRangeWitness {
    pub id: u64,
    pub id_lo: u64,
    pub id_hi: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MdocStatementAttribute {
    pub element_identifier: String,
    pub mode: MdocDisclosureMode,
}

impl MdocCircuitStatement {
    pub fn from_extracted_at(
        extracted: &ExtractedPidMdoc,
        policy: Policy,
        verification_time_epoch_seconds: u64,
    ) -> Result<Self, MdocError> {
        validate_requested_attributes(&extracted.attributes)?;
        validate_product_policy(&policy, verification_time_epoch_seconds)?;
        let verification_time = strict_verification_timestamp(verification_time_epoch_seconds)?;
        if verification_time <= extracted.valid_from_timestamp {
            return Err(MdocError::CredentialNotYetValid);
        }
        if verification_time >= extracted.valid_until_timestamp {
            return Err(MdocError::CredentialExpired);
        }

        let mso = parse_mso(&extracted.mso, &extracted.namespace)?;
        if mso.version != MDOC_PROFILE_VERSION {
            return Err(MdocError::UnsupportedMsoVersion(mso.version));
        }
        if mso.doc_type != extracted.doctype {
            return Err(MdocError::DoctypeMismatch);
        }
        let mut statement_attributes = Vec::with_capacity(extracted.extracted_attributes.len());
        for attribute in &extracted.extracted_attributes {
            let digest = *mso.value_digests.get(&attribute.digest_id).ok_or_else(|| {
                MdocError::ItemDigestMismatch {
                    element: attribute.request.element_identifier.clone(),
                    digest_id: attribute.digest_id,
                }
            })?;
            let mso_digest_offset = find_subslice(&extracted.issuer_sig_structure, &digest).ok_or(
                MdocError::UnsupportedCircuitValue("attribute digest offset"),
            )?;
            let mso_digest_anchor = digest_anchor_bytes(attribute.digest_id);
            anchor_before_offset(
                &extracted.issuer_sig_structure,
                mso_digest_offset,
                &mso_digest_anchor,
                "attribute digest anchor offset",
            )?;
            ensure_value_window_with_message(
                &attribute.item,
                attribute.element_identifier_offset,
                attribute.request.element_identifier.as_bytes(),
                "attribute elementIdentifier offset",
            )?;
            let element_identifier_anchor =
                element_identifier_anchor_bytes(&attribute.request.element_identifier)?;
            anchor_before_offset(
                &attribute.item,
                attribute.element_identifier_offset,
                &element_identifier_anchor,
                "attribute elementIdentifier anchor offset",
            )?;
            ensure_value_window_with_message(
                &attribute.item,
                attribute.value_offset,
                &attribute.value,
                "attribute value offset",
            )?;
            ensure_value_window_with_message(
                &extracted.issuer_sig_structure,
                mso_digest_offset,
                &digest,
                "attribute digest offset",
            )?;
            statement_attributes.push(MdocStatementAttribute {
                element_identifier: attribute.request.element_identifier.clone(),
                mode: attribute.request.mode.clone(),
            });
        }
        let age_attribute_index = statement_attributes
            .iter()
            .position(|attribute| matches!(attribute.mode, MdocDisclosureMode::AgeOver));
        let nationality_attribute_index = statement_attributes
            .iter()
            .position(|attribute| matches!(attribute.mode, MdocDisclosureMode::Alpha2Set));

        // Locate the windows for the MSO bindings.
        // The circuit obtains the digests and device key from these offsets.
        // The window binding checks the bytes at each offset.
        // The issuer signature covers the surrounding bytes.
        if age_attribute_index.is_some() {
            ensure_value_window(
                &extracted.birth_date_item,
                extracted.birth_date_value_offset,
                extracted.birth_date_binding.as_bytes(),
            )?;
        }
        if nationality_attribute_index.is_some() {
            ensure_value_window(
                &extracted.nationality_item,
                extracted.nationality_value_offset,
                extracted.nationality_binding.as_bytes(),
            )?;
        }
        let mso_device_key_x_offset =
            find_subslice(&extracted.issuer_sig_structure, &extracted.device_key.x.0)
                .ok_or(MdocError::UnsupportedCircuitValue("device key x offset"))?;
        let mso_device_key_y_offset =
            find_subslice(&extracted.issuer_sig_structure, &extracted.device_key.y.0)
                .ok_or(MdocError::UnsupportedCircuitValue("device key y offset"))?;
        let mso_payload_offset = find_subslice(&extracted.issuer_sig_structure, &extracted.mso)
            .ok_or(MdocError::UnsupportedCircuitValue("MSO payload offset"))?;
        let mso_valid_from_date_offset = mso_payload_offset
            + labeled_tdate_date_offset(
                &extracted.mso,
                b"validFrom",
                extracted.valid_from_timestamp,
                "validFrom date offset",
            )?;
        let mso_valid_until_date_offset = mso_payload_offset
            + labeled_tdate_date_offset(
                &extracted.mso,
                b"validUntil",
                extracted.valid_until_timestamp,
                "validUntil date offset",
            )?;
        let mso_device_key_x_anchor = vec![0x21, 0x58, 0x20];
        anchor_before_offset(
            &extracted.issuer_sig_structure,
            mso_device_key_x_offset,
            &mso_device_key_x_anchor,
            "device key x anchor offset",
        )?;
        let mso_device_key_y_anchor = vec![0x22, 0x58, 0x20];
        anchor_before_offset(
            &extracted.issuer_sig_structure,
            mso_device_key_y_offset,
            &mso_device_key_y_anchor,
            "device key y anchor offset",
        )?;
        let mso_valid_from_anchor = cbor_tdate_anchor_bytes("validFrom");
        anchor_before_offset(
            &extracted.issuer_sig_structure,
            mso_valid_from_date_offset,
            &mso_valid_from_anchor,
            "validFrom anchor offset",
        )?;
        let mso_valid_until_anchor = cbor_tdate_anchor_bytes("validUntil");
        anchor_before_offset(
            &extracted.issuer_sig_structure,
            mso_valid_until_date_offset,
            &mso_valid_until_anchor,
            "validUntil anchor offset",
        )?;
        ensure_value_window_with_message(
            &extracted.issuer_sig_structure,
            mso_device_key_x_offset,
            &extracted.device_key.x.0,
            "device key x offset",
        )?;
        ensure_value_window_with_message(
            &extracted.issuer_sig_structure,
            mso_device_key_y_offset,
            &extracted.device_key.y.0,
            "device key y offset",
        )?;
        ensure_value_window_with_message(
            &extracted.issuer_sig_structure,
            mso_valid_from_date_offset,
            &extracted.valid_from_timestamp.text_bytes(),
            "validFrom date offset",
        )?;
        ensure_value_window_with_message(
            &extracted.issuer_sig_structure,
            mso_valid_until_date_offset,
            &extracted.valid_until_timestamp.text_bytes(),
            "validUntil date offset",
        )?;
        Ok(Self {
            request_binding: extracted.request_binding,
            doctype: extracted.doctype.clone(),
            namespace: extracted.namespace.clone(),
            issuer_input: extracted.issuer_ecdsa_input.clone(),
            device_input: extracted.device_ecdsa_input.clone(),
            verification_time_epoch_seconds,
            ts13_revocation: extracted.revocation.public_inputs.clone(),
            ts13_revocation_range: MdocRevocationRangeWitness {
                id: crate::ts13::ts13_mso_derived_revocation_id(&extracted.mso),
                id_lo: extracted.revocation.id_lo,
                id_hi: extracted.revocation.id_hi,
            },
            ts13_revocation_signature: extracted.revocation.signature.clone(),
            attributes: statement_attributes,
            age_attribute_index,
            nationality_attribute_index,
            policy,
        })
    }
}

/// Checks that `item[offset..offset+expected.len()] == expected`.
///
/// Multi-block field binding permits a window across a SHA-256 block boundary.
/// The host must only check the bytes at the supplied offset.
fn ensure_value_window(item: &[u8], offset: usize, expected: &[u8]) -> Result<(), MdocError> {
    ensure_value_window_with_message(item, offset, expected, "element value bytes at offset")
}

fn ensure_value_window_with_message(
    item: &[u8],
    offset: usize,
    expected: &[u8],
    mismatch_message: &'static str,
) -> Result<(), MdocError> {
    let end = offset
        .checked_add(expected.len())
        .ok_or(MdocError::UnsupportedCircuitValue(mismatch_message))?;
    if item.get(offset..end) != Some(expected) {
        return Err(MdocError::UnsupportedCircuitValue(mismatch_message));
    }
    Ok(())
}

#[cfg(test)]
fn days_from_civil(year: i64, month: i64, day: i64) -> Result<i64, MdocError> {
    let calendar_date = u16::try_from(year)
        .ok()
        .zip(u8::try_from(month).ok())
        .zip(u8::try_from(day).ok())
        .map(|((year, month), day)| (year, month, day));
    if !(1970..=9999).contains(&year)
        || !calendar_date
            .map(|(year, month, day)| is_gregorian_date(year, month, day))
            .unwrap_or(false)
    {
        return Err(MdocError::InvalidVerificationTime);
    }
    let year = if month <= 2 { year - 1 } else { year };
    let era = year / 400;
    let year_of_era = year - era * 400;
    let shifted_month = if month > 2 { month - 3 } else { month + 9 };
    let day_of_year = (153 * shifted_month + 2) / 5 + day - 1;
    let day_of_era = year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year;
    Ok(era * 146_097 + day_of_era - 719_468)
}

#[derive(Clone, Serialize, Deserialize)]
pub struct MdocCircuitProof {
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
    sha_tables_interaction_claim: ShaTablesInteractionClaim,
    packed_sha_interaction_claim: Sha256InteractionClaim,

    coprocessor_bundle: eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle,

    mdoc_mac_interaction_claim: MdocMacInteractionClaim,
    mdoc_cbor_log_sizes: Vec<u32>,
    mdoc_cbor_interaction_claims: Vec<MdocCborStreamInteractionClaim>,
    mso_exact_cbor_interaction_claim: MdocCborStreamInteractionClaim,
    mdoc_scope_metadata: MdocScopeProofMetadata,
    mdoc_scope_interaction_claim: MdocScopeInteractionClaim,

    mdoc_validity_interaction_claim: MdocValidityInteractionClaim,
    revocation_message_bind_interaction_claim: MdocExactShaMessageInteractionClaim,
    ts13_revocation_range_interaction_claim: MdocRevocationRangeInteractionClaim,
    age_public: Option<predicates::PublicInput>,
    age_claimed_sums: Option<Vec<QM31>>,
    nat_public: Option<predicates::NatPublicInput>,
    nat_claimed_sums: Option<Vec<QM31>>,
}

fn validate_product_fixed_shape_logs(
    sha_log_size: u32,
    cbor_log_sizes: impl IntoIterator<Item = u32>,
    scope_log_size: u32,
) -> Result<(), Error> {
    let sha_shape_is_fixed = sha_log_size == crate::product_profile::PRODUCT_SHA_LOG_N_ROWS;
    let mut cbor_log_sizes = cbor_log_sizes.into_iter().peekable();
    let cbor_shape_is_fixed = cbor_log_sizes.peek().is_some()
        && cbor_log_sizes
            .all(|log_size| log_size == crate::product_profile::PRODUCT_MAX_CBOR_LOG_SIZE);
    if !sha_shape_is_fixed
        || !cbor_shape_is_fixed
        || scope_log_size != crate::product_profile::PRODUCT_MAX_SCOPE_LOG_SIZE
    {
        return Err(Error::Verify(
            "mdoc proof shape does not match the fixed product profile".to_string(),
        ));
    }
    Ok(())
}

impl MdocCircuitProof {
    fn validate_product_fixed_shape(&self) -> Result<(), Error> {
        validate_product_fixed_shape_logs(
            crate::product_profile::PRODUCT_SHA_LOG_N_ROWS,
            self.mdoc_cbor_log_sizes.iter().copied(),
            self.mdoc_scope_metadata.log_size,
        )
    }
}

fn ecdsa_inputs_equal(left: &EcdsaVerifyInput, right: &EcdsaVerifyInput) -> bool {
    left.message_hash.0 == right.message_hash.0
        && left.signature.r.0 == right.signature.r.0
        && left.signature.s.0 == right.signature.s.0
        && left.public_key.x.0 == right.public_key.x.0
        && left.public_key.y.0 == right.public_key.y.0
}

struct MdocRevocationPublicBind {
    inputs: MdocRevocationPublicInputs,
}

impl MdocRevocationPublicBind {
    fn new(inputs: MdocRevocationPublicInputs) -> Self {
        Self { inputs }
    }
}

impl Air for MdocRevocationPublicBind {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(0x5453_3133_5245_5601);
        for byte in self.inputs.revocation_public_key.x.0 {
            channel.mix_u64(u64::from(byte));
        }
        for byte in self.inputs.revocation_public_key.y.0 {
            channel.mix_u64(u64::from(byte));
        }
        channel.mix_u64(u64::from(self.inputs.epoch));
    }

    fn draw_relations(&mut self, _channel: &mut Blake2sChannel) {}

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: Vec::new(),
            trace: Vec::new(),
            interaction: Vec::new(),
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        Vec::new()
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        Vec::new()
    }

    fn build_components(&mut self, _allocator: &mut TraceLocationAllocator) {}

    fn components(&self) -> Vec<&dyn Component> {
        Vec::new()
    }
}

impl AirProver for MdocRevocationPublicBind {
    fn max_log_size(&self) -> u32 {
        0
    }

    fn write_preprocessed(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

    fn write_trace(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

    fn write_interaction(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        Vec::new()
    }
}

type MdocExactShaMessageColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type MdocExactShaMessageComponent = FrameworkComponent<MdocExactShaMessageEval>;

struct MdocExactShaMessageBind {
    bytes: Option<Vec<u8>>,
    len: usize,
    namespace: &'static str,
    source_field_id: u32,
    sha_field_id: u32,
    source_multiplicity: i32,
    draw_source_relation: bool,
    source_field_handle: SharedFieldRelation,
    sha_field_handle: SharedFieldRelation,
    claim_mask_trace: Option<ClaimMaskTrace>,
    claim_mask_challenge: Option<SharedClaimMaskChallenge>,
    interaction_claim: Option<MdocExactShaMessageInteractionClaim>,
    component: Option<MdocExactShaMessageComponent>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct MdocExactShaMessageInteractionClaim {
    claimed_sum: QM31,
}

#[derive(Clone)]
struct MdocExactShaMessageEval {
    log_size: u32,
    namespace: &'static str,
    source_field_id: u32,
    sha_field_id: u32,
    source_multiplicity: i32,
    source_field_relation: FieldBytesRelation,
    sha_field_relation: FieldBytesRelation,
    claim_mask_beta: Option<QM31>,
}

impl MdocExactShaMessageBind {
    fn prover(
        namespace: &'static str,
        source_field_id: u32,
        sha_field_id: u32,
        source_multiplicity: i32,
        draw_source_relation: bool,
        bytes: Vec<u8>,
        source_field_handle: SharedFieldRelation,
        sha_field_handle: SharedFieldRelation,
    ) -> Self {
        assert!(matches!(source_multiplicity, -1 | 1));
        Self {
            len: bytes.len(),
            bytes: Some(bytes),
            namespace,
            source_field_id,
            sha_field_id,
            source_multiplicity,
            draw_source_relation,
            source_field_handle,
            sha_field_handle,
            claim_mask_trace: None,
            claim_mask_challenge: None,
            interaction_claim: None,
            component: None,
        }
    }

    fn verifier(
        namespace: &'static str,
        source_field_id: u32,
        sha_field_id: u32,
        source_multiplicity: i32,
        draw_source_relation: bool,
        len: usize,
        source_field_handle: SharedFieldRelation,
        sha_field_handle: SharedFieldRelation,
        interaction_claim: MdocExactShaMessageInteractionClaim,
    ) -> Self {
        assert!(matches!(source_multiplicity, -1 | 1));
        Self {
            bytes: None,
            len,
            namespace,
            source_field_id,
            sha_field_id,
            source_multiplicity,
            draw_source_relation,
            source_field_handle,
            sha_field_handle,
            claim_mask_trace: None,
            claim_mask_challenge: None,
            interaction_claim: Some(interaction_claim),
            component: None,
        }
    }

    fn log_size(&self) -> u32 {
        exact_sha_message_log_size(self.len)
    }

    fn source_field_relation(&self) -> FieldBytesRelation {
        self.source_field_handle.get()
    }

    fn sha_field_relation(&self) -> FieldBytesRelation {
        self.sha_field_handle.get()
    }

    fn interaction_claim(&self) -> &MdocExactShaMessageInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("exact SHA message interaction claim is set")
    }

    fn ordered_claim_mask_log_sizes(&self) -> Vec<u32> {
        vec![self.log_size()]
    }

    fn with_claim_mask(
        mut self,
        trace: ClaimMaskTrace,
        challenge: SharedClaimMaskChallenge,
    ) -> Self {
        assert_eq!(trace.log_size(), self.log_size());
        self.claim_mask_trace = Some(trace);
        self.claim_mask_challenge = Some(challenge);
        self
    }

    fn with_claim_mask_verifier(mut self, challenge: SharedClaimMaskChallenge) -> Self {
        self.claim_mask_challenge = Some(challenge);
        self
    }

    fn claim_mask_beta(&self) -> Option<QM31> {
        self.claim_mask_challenge
            .as_ref()
            .map(|shared| shared.require().expect("claim-mask anchor drawn first"))
    }
}

const EXACT_SHA_MESSAGE_BLIND_ROWS: usize = 256;

fn exact_sha_padded_len(len: usize) -> usize {
    len.checked_add(9)
        .and_then(|needed| needed.checked_add(63))
        .map(|rounded| rounded / 64 * 64)
        .expect("validated SHA message length does not overflow")
}

fn exact_sha_message_log_size(len: usize) -> u32 {
    exact_sha_padded_len(len)
        .checked_add(EXACT_SHA_MESSAGE_BLIND_ROWS)
        .expect("validated SHA message trace length does not overflow")
        .next_power_of_two()
        .ilog2()
        .max(LOG_N_LANES)
}

fn exact_sha_padding_byte(len: usize, row: usize, padded_len: usize) -> u8 {
    debug_assert!(row >= len && row < padded_len);
    if row == len {
        return 0x80;
    }
    if row >= padded_len - 8 {
        let bit_len = u64::try_from(len)
            .expect("bounded message length fits u64")
            .checked_mul(8)
            .expect("bounded message bit length fits u64")
            .to_be_bytes();
        return bit_len[row - (padded_len - 8)];
    }
    0
}

fn exact_sha_message_col_id(namespace: &str, name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mdoc/ts13/exact_sha_message/{namespace}/{name}"),
    }
}

fn exact_sha_message_preprocessed_column_ids(namespace: &str) -> Vec<PreProcessedColumnId> {
    vec![
        exact_sha_message_col_id(namespace, "raw_active"),
        exact_sha_message_col_id(namespace, "sha_active"),
        exact_sha_message_col_id(namespace, "byte_index"),
        exact_sha_message_col_id(namespace, "expected_padding"),
    ]
}

fn exact_sha_message_column_eval(
    log_size: u32,
    coset_values: Vec<M31>,
) -> MdocExactShaMessageColumnEval {
    let mut ordered = vec![M31::from_u32_unchecked(0); 1usize << log_size];
    for (coset_index, value) in coset_values.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        );
        ordered[row] = value;
    }
    CircleEvaluation::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(ordered),
    )
}

fn exact_sha_message_preprocessed_columns(len: usize) -> Vec<MdocExactShaMessageColumnEval> {
    let log_size = exact_sha_message_log_size(len);
    let rows = 1usize << log_size;
    let padded_len = exact_sha_padded_len(len);
    let mut raw_active = vec![M31::from_u32_unchecked(0); rows];
    let mut sha_active = vec![M31::from_u32_unchecked(0); rows];
    let mut byte_index = vec![M31::from_u32_unchecked(0); rows];
    let mut expected_padding = vec![M31::from_u32_unchecked(0); rows];
    for row in 0..len {
        raw_active[row] = M31::from_u32_unchecked(1);
    }
    for row in 0..padded_len {
        sha_active[row] = M31::from_u32_unchecked(1);
        byte_index[row] = M31::from_u32_unchecked(row as u32);
        if row >= len {
            expected_padding[row] =
                M31::from_u32_unchecked(u32::from(exact_sha_padding_byte(len, row, padded_len)));
        }
    }
    vec![
        exact_sha_message_column_eval(log_size, raw_active),
        exact_sha_message_column_eval(log_size, sha_active),
        exact_sha_message_column_eval(log_size, byte_index),
        exact_sha_message_column_eval(log_size, expected_padding),
    ]
}

fn random_exact_sha_message_m31(rng: &mut impl RngCore) -> M31 {
    loop {
        let value = rng.next_u32() & 0x7fff_ffff;
        if value != 0x7fff_ffff {
            return M31::from_u32_unchecked(value);
        }
    }
}

fn exact_sha_message_base_trace(bytes: &[u8]) -> Vec<MdocExactShaMessageColumnEval> {
    let log_size = exact_sha_message_log_size(bytes.len());
    let padded = stwo_sha256::native::pad_message(bytes);
    let mut rng = rand::thread_rng();
    let mut values = (0..1usize << log_size)
        .map(|_| random_exact_sha_message_m31(&mut rng))
        .collect::<Vec<_>>();
    for (row, &byte) in padded.iter().enumerate() {
        values[row] = M31::from_u32_unchecked(u32::from(byte));
    }
    vec![exact_sha_message_column_eval(log_size, values)]
}

fn exact_sha_message_interaction_trace(
    bytes: &[u8],
    source_field_id: u32,
    sha_field_id: u32,
    source_multiplicity: i32,
    source_field_relation: &FieldBytesRelation,
    sha_field_relation: &FieldBytesRelation,
    claim_mask: Option<(&ClaimMaskTrace, QM31)>,
) -> (Vec<MdocExactShaMessageColumnEval>, QM31) {
    let log_size = exact_sha_message_log_size(bytes.len());
    let preprocessed = exact_sha_message_preprocessed_columns(bytes.len());
    let trace = exact_sha_message_base_trace(bytes);
    let n_vec_rows = 1usize << (log_size - LOG_N_LANES);
    let mut logup = LogupTraceGenerator::new(log_size);
    logup.col_from_iter((0..n_vec_rows).map(|vec_row| {
        let raw_active = preprocessed[0].data[vec_row];
        let sha_active = preprocessed[1].data[vec_row];
        let byte_index = preprocessed[2].data[vec_row];
        let value = trace[0].data[vec_row];
        let source_numerator = if source_multiplicity == 1 {
            PackedQM31::from(raw_active)
        } else {
            -PackedQM31::from(raw_active)
        };
        let sha_numerator = PackedQM31::from(sha_active);
        let source_denominator: PackedQM31 = source_field_relation.combine(&[
            PackedM31::broadcast(M31::from_u32_unchecked(source_field_id)),
            byte_index,
            value,
        ]);
        let sha_denominator: PackedQM31 = sha_field_relation.combine(&[
            PackedM31::broadcast(M31::from_u32_unchecked(sha_field_id)),
            byte_index,
            value,
        ]);
        (
            source_numerator * sha_denominator + sha_numerator * source_denominator,
            source_denominator * sha_denominator,
        )
    }));
    if let Some((mask, beta)) = claim_mask {
        assert_eq!(mask.packed_rows(), n_vec_rows);
        logup.col_from_fn(|vec_row| mask.packed_fraction_at(vec_row, beta));
    }
    logup.finalize_last()
}

impl FrameworkEval for MdocExactShaMessageEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let raw_active =
            eval.get_preprocessed_column(exact_sha_message_col_id(self.namespace, "raw_active"));
        let sha_active =
            eval.get_preprocessed_column(exact_sha_message_col_id(self.namespace, "sha_active"));
        let byte_index =
            eval.get_preprocessed_column(exact_sha_message_col_id(self.namespace, "byte_index"));
        let expected_padding = eval
            .get_preprocessed_column(exact_sha_message_col_id(self.namespace, "expected_padding"));
        let value = eval.next_trace_mask();
        let one = m31_const::<E>(1);
        eval.add_constraint(raw_active.clone() * (raw_active.clone() - one.clone()));
        eval.add_constraint(sha_active.clone() * (sha_active.clone() - one));
        eval.add_constraint(raw_active.clone() * (raw_active.clone() - sha_active.clone()));
        eval.add_constraint(
            (sha_active.clone() - raw_active.clone()) * (value.clone() - expected_padding),
        );
        let source_field_id = m31_const::<E>(self.source_field_id);
        let sha_field_id = m31_const::<E>(self.sha_field_id);
        let source_multiplicity = if self.source_multiplicity == 1 {
            E::EF::from(raw_active)
        } else {
            -E::EF::from(raw_active)
        };
        eval.add_to_relation(RelationEntry::new(
            &self.source_field_relation,
            source_multiplicity,
            &[source_field_id.clone(), byte_index.clone(), value.clone()],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.sha_field_relation,
            E::EF::from(sha_active),
            &[sha_field_id, byte_index, value],
        ));
        if let Some(beta) = self.claim_mask_beta {
            add_claim_mask_fraction(&mut eval, beta);
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

impl Air for MdocExactShaMessageBind {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(0x5453_3133_4558_5348);
        channel.mix_u64(self.len as u64);
        channel.mix_u64(u64::from(self.source_field_id));
        channel.mix_u64(u64::from(self.sha_field_id));
        channel.mix_u64(self.source_multiplicity as i64 as u64);
        channel.mix_u64(u64::from(self.draw_source_relation));
        channel.mix_u64(self.namespace.len() as u64);
        for &byte in self.namespace.as_bytes() {
            channel.mix_u64(u64::from(byte));
        }
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        if self.draw_source_relation {
            assert!(
                !self.source_field_handle.is_set(),
                "exact SHA source relation must be drawn exactly once"
            );
            self.source_field_handle
                .set(FieldBytesRelation::draw(channel));
        }
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![self.log_size(); 4],
            trace: vec![
                self.log_size();
                1 + usize::from(self.claim_mask_challenge.is_some())
                    * CLAIM_MASK_TRACE_COLUMNS
            ],
            // The two exact-message relation entries form one paired column.
            // Enabling privacy appends a third logical fraction and one
            // additional extension column.
            interaction: vec![
                self.log_size();
                (1 + usize::from(self.claim_mask_challenge.is_some()))
                    * SECURE_EXTENSION_DEGREE
            ],
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        vec![self.interaction_claim().claimed_sum]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        exact_sha_message_preprocessed_column_ids(self.namespace)
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(exact_sha_message_preprocessed_columns(self.len))
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let claim = self.interaction_claim().clone();
        self.component = Some(MdocExactShaMessageComponent::new(
            allocator,
            MdocExactShaMessageEval {
                log_size: self.log_size(),
                namespace: self.namespace,
                source_field_id: self.source_field_id,
                sha_field_id: self.sha_field_id,
                source_multiplicity: self.source_multiplicity,
                source_field_relation: self.source_field_relation(),
                sha_field_relation: self.sha_field_relation(),
                claim_mask_beta: self.claim_mask_beta(),
            },
            claim.claimed_sum,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![self
            .component
            .as_ref()
            .expect("exact SHA message component is built")]
    }
}

impl AirProver for MdocExactShaMessageBind {
    fn max_log_size(&self) -> u32 {
        self.log_size()
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(exact_sha_message_preprocessed_columns(self.len));
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc::MdocExactShaMessageBind",
            &exact_sha_message_preprocessed_column_ids(self.namespace),
            &exact_sha_message_preprocessed_columns(self.len),
        )
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(exact_sha_message_base_trace(
            self.bytes
                .as_ref()
                .expect("exact SHA message bytes are set"),
        ));
        if let Some(mask) = &self.claim_mask_trace {
            tb.extend_evals(mask.columns().to_vec());
        }
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let claim_mask = self.claim_mask_trace.as_ref().zip(self.claim_mask_beta());
        let (trace, claimed_sum) = exact_sha_message_interaction_trace(
            self.bytes
                .as_ref()
                .expect("exact SHA message bytes are set"),
            self.source_field_id,
            self.sha_field_id,
            self.source_multiplicity,
            &self.source_field_relation(),
            &self.sha_field_relation(),
            claim_mask,
        );
        tb.extend_evals(trace);
        self.interaction_claim = Some(MdocExactShaMessageInteractionClaim { claimed_sum });
        self.bytes.take();
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![self
            .component
            .as_ref()
            .expect("exact SHA message component is built")]
    }
}

const MDOC_REVOCATION_RANGE_LOG_SIZE: u32 = 9;
const REVOCATION_U64_BYTES: usize = 8;
const REVOCATION_RANGE_BYTE_COLS: usize = 5 * REVOCATION_U64_BYTES;
const REVOCATION_RANGE_BIT_COLS: usize = REVOCATION_RANGE_BYTE_COLS * 8;
const REVOCATION_RANGE_CARRY_COLS: usize = 2 * REVOCATION_U64_BYTES;
const REVOCATION_RANGE_DIGEST_TAIL_COLS: usize = 32 - REVOCATION_U64_BYTES;
const REVOCATION_RANGE_TRACE_COLS: usize = REVOCATION_RANGE_BYTE_COLS
    + REVOCATION_RANGE_BIT_COLS
    + REVOCATION_RANGE_CARRY_COLS
    + REVOCATION_RANGE_DIGEST_TAIL_COLS;

type MdocRevocationRangeColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type MdocRevocationRangeComponent = FrameworkComponent<MdocRevocationRangeEval>;

struct MdocRevocationRangeBind {
    witness: Option<MdocRevocationRangeWitness>,
    mso_digest: Option<[u8; 32]>,
    epoch: u32,
    mso_digest_handle: SharedPackedShaDigestRelation,
    message_field_handle: SharedFieldRelation,
    claim_mask_trace: Option<ClaimMaskTrace>,
    claim_mask_challenge: Option<SharedClaimMaskChallenge>,
    interaction_claim: Option<MdocRevocationRangeInteractionClaim>,
    component: Option<MdocRevocationRangeComponent>,
}

#[derive(Clone)]
struct MdocRevocationRangeEval {
    mso_digest_relation: stwo_sha256::relations::PackedShaDigestRelation,
    message_field_relation: FieldBytesRelation,
    epoch: u32,
    claim_mask_beta: Option<QM31>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct MdocRevocationRangeInteractionClaim {
    claimed_sum: QM31,
}

impl MdocRevocationRangeBind {
    fn prover(
        witness: MdocRevocationRangeWitness,
        mso_digest: [u8; 32],
        mso_digest_handle: SharedPackedShaDigestRelation,
        epoch: u32,
        message_field_handle: SharedFieldRelation,
    ) -> Self {
        Self {
            witness: Some(witness),
            mso_digest: Some(mso_digest),
            epoch,
            mso_digest_handle,
            message_field_handle,
            claim_mask_trace: None,
            claim_mask_challenge: None,
            interaction_claim: None,
            component: None,
        }
    }

    fn verifier(
        mso_digest_handle: SharedPackedShaDigestRelation,
        epoch: u32,
        message_field_handle: SharedFieldRelation,
        interaction_claim: MdocRevocationRangeInteractionClaim,
    ) -> Self {
        Self {
            witness: None,
            mso_digest: None,
            epoch,
            mso_digest_handle,
            message_field_handle,
            claim_mask_trace: None,
            claim_mask_challenge: None,
            interaction_claim: Some(interaction_claim),
            component: None,
        }
    }

    fn relation(&self) -> stwo_sha256::relations::PackedShaDigestRelation {
        self.mso_digest_handle.get()
    }

    fn message_relation(&self) -> FieldBytesRelation {
        self.message_field_handle.get()
    }

    fn interaction_claim(&self) -> &MdocRevocationRangeInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("mdoc revocation range interaction claim is set")
    }

    fn ordered_claim_mask_log_sizes(&self) -> Vec<u32> {
        vec![MDOC_REVOCATION_RANGE_LOG_SIZE]
    }

    fn with_claim_mask(
        mut self,
        trace: ClaimMaskTrace,
        challenge: SharedClaimMaskChallenge,
    ) -> Self {
        assert_eq!(trace.log_size(), MDOC_REVOCATION_RANGE_LOG_SIZE);
        self.claim_mask_trace = Some(trace);
        self.claim_mask_challenge = Some(challenge);
        self
    }

    fn with_claim_mask_verifier(mut self, challenge: SharedClaimMaskChallenge) -> Self {
        self.claim_mask_challenge = Some(challenge);
        self
    }

    fn claim_mask_beta(&self) -> Option<QM31> {
        self.claim_mask_challenge
            .as_ref()
            .map(|shared| shared.require().expect("claim-mask anchor drawn first"))
    }
}

fn revocation_range_active_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: "mdoc/ts13/revocation_range_active".to_string(),
    }
}

fn m31_const<E: EvalAtRow>(value: u32) -> E::F {
    E::F::from(M31::from_u32_unchecked(value))
}

fn mdoc_column_eval(log_size: u32, coset_values: Vec<M31>) -> MdocRevocationRangeColumnEval {
    let mut ordered = vec![M31::from_u32_unchecked(0); 1usize << log_size];
    for (coset_index, value) in coset_values.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        );
        ordered[row] = value;
    }
    CircleEvaluation::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(ordered),
    )
}

fn revocation_range_active_column() -> MdocRevocationRangeColumnEval {
    let mut values = vec![M31::from_u32_unchecked(0); 1usize << MDOC_REVOCATION_RANGE_LOG_SIZE];
    values[0] = M31::from_u32_unchecked(1);
    mdoc_column_eval(MDOC_REVOCATION_RANGE_LOG_SIZE, values)
}

fn byte_bits(byte: u8) -> [u8; 8] {
    std::array::from_fn(|bit| (byte >> bit) & 1)
}

fn comparison_carries(lhs: [u8; 8], rhs: [u8; 8], slack: [u8; 8]) -> [u8; 8] {
    let mut carry = 0u16;
    std::array::from_fn(|idx| {
        let add_one = u16::from(idx == 0);
        let sum = u16::from(lhs[idx]) + u16::from(slack[idx]) + add_one + carry;
        carry = sum >> 8;
        debug_assert_eq!((sum & 0xff) as u8, rhs[idx]);
        carry as u8
    })
}

fn revocation_range_base_trace(
    witness: &MdocRevocationRangeWitness,
    mso_digest: &[u8; 32],
) -> Vec<MdocRevocationRangeColumnEval> {
    let id = witness.id.to_le_bytes();
    let id_lo = witness.id_lo.to_le_bytes();
    let id_hi = witness.id_hi.to_le_bytes();
    let lower_slack = witness
        .id
        .wrapping_sub(witness.id_lo)
        .wrapping_sub(1)
        .to_le_bytes();
    let upper_slack = witness
        .id_hi
        .wrapping_sub(witness.id)
        .wrapping_sub(1)
        .to_le_bytes();
    let lower_carries = comparison_carries(id_lo, id, lower_slack);
    let upper_carries = comparison_carries(id, id_hi, upper_slack);

    let mut first_row = Vec::with_capacity(REVOCATION_RANGE_TRACE_COLS);
    for byte in id
        .into_iter()
        .chain(id_lo)
        .chain(id_hi)
        .chain(lower_slack)
        .chain(upper_slack)
    {
        first_row.push(u32::from(byte));
    }
    let range_bytes = first_row[..REVOCATION_RANGE_BYTE_COLS].to_vec();
    for byte in range_bytes {
        first_row.extend(byte_bits(byte as u8).into_iter().map(u32::from));
    }
    first_row.extend(lower_carries.into_iter().map(u32::from));
    first_row.extend(upper_carries.into_iter().map(u32::from));
    first_row.extend(
        mso_digest[REVOCATION_U64_BYTES..]
            .iter()
            .map(|&byte| u32::from(byte)),
    );
    debug_assert_eq!(first_row.len(), REVOCATION_RANGE_TRACE_COLS);

    let mut rng = rand::thread_rng();
    first_row
        .into_iter()
        .map(|value| {
            let mut column = (0..1usize << MDOC_REVOCATION_RANGE_LOG_SIZE)
                .map(|_| random_exact_sha_message_m31(&mut rng))
                .collect::<Vec<_>>();
            column[0] = M31::from_u32_unchecked(value);
            mdoc_column_eval(MDOC_REVOCATION_RANGE_LOG_SIZE, column)
        })
        .collect()
}

fn revocation_range_interaction_trace(
    witness: &MdocRevocationRangeWitness,
    mso_digest: &[u8; 32],
    relation: &PackedShaDigestRelation,
    epoch: u32,
    message_relation: &FieldBytesRelation,
    claim_mask: Option<(&ClaimMaskTrace, QM31)>,
) -> (Vec<MdocRevocationRangeColumnEval>, QM31) {
    let base = revocation_range_base_trace(witness, mso_digest);
    let active = revocation_range_active_column();
    let n_vec_rows = 1usize << (MDOC_REVOCATION_RANGE_LOG_SIZE - LOG_N_LANES);
    let digest_tail_offset =
        REVOCATION_RANGE_BYTE_COLS + REVOCATION_RANGE_BIT_COLS + REVOCATION_RANGE_CARRY_COLS;
    let mut sites: Vec<Vec<(PackedQM31, PackedQM31)>> = Vec::new();
    sites.push(
        (0..n_vec_rows)
            .map(|vec_row| {
                let numerator = PackedQM31::from(active.data[vec_row]);
                let mut values = vec![PackedM31::broadcast(M31::from_u32_unchecked(0)); 33];
                values[0] = PackedM31::broadcast(M31::from_u32_unchecked(PACKED_SHA_MSO_SLOT));
                for byte_idx in 0..REVOCATION_U64_BYTES {
                    values[byte_idx + 1] = base[byte_idx].data[vec_row];
                }
                for byte_idx in REVOCATION_U64_BYTES..32 {
                    values[byte_idx + 1] =
                        base[digest_tail_offset + byte_idx - REVOCATION_U64_BYTES].data[vec_row];
                }
                (numerator, relation.combine(&values))
            })
            .collect(),
    );
    let epoch_bytes = epoch.to_le_bytes();
    for byte_idx in 0..TS13_REVOCATION_MESSAGE_LEN {
        sites.push(
            (0..n_vec_rows)
                .map(|vec_row| {
                    let numerator = PackedQM31::from(active.data[vec_row]);
                    let value = match byte_idx {
                        0..=7 => base[REVOCATION_U64_BYTES + byte_idx].data[vec_row],
                        8..=15 => base[2 * REVOCATION_U64_BYTES + byte_idx - 8].data[vec_row],
                        _ => PackedM31::broadcast(M31::from_u32_unchecked(u32::from(
                            epoch_bytes[byte_idx - 16],
                        ))),
                    };
                    let denominator: PackedQM31 = message_relation.combine(&[
                        PackedM31::broadcast(M31::from_u32_unchecked(
                            MDOC_REVOCATION_MESSAGE_FIELD_ID,
                        )),
                        PackedM31::broadcast(M31::from_u32_unchecked(byte_idx as u32)),
                        value,
                    ]);
                    (numerator, denominator)
                })
                .collect(),
        );
    }
    if let Some((mask, beta)) = claim_mask {
        assert_eq!(mask.packed_rows(), n_vec_rows);
        sites.push(
            (0..n_vec_rows)
                .map(|vec_row| mask.packed_fraction_at(vec_row, beta))
                .collect(),
        );
    }

    let mut logup = LogupTraceGenerator::new(MDOC_REVOCATION_RANGE_LOG_SIZE);
    let mut site = 0;
    while site + 1 < sites.len() {
        let left = &sites[site];
        let right = &sites[site + 1];
        logup.col_from_iter((0..n_vec_rows).map(|row| {
            let (left_num, left_den) = left[row];
            let (right_num, right_den) = right[row];
            (
                left_num * right_den + right_num * left_den,
                left_den * right_den,
            )
        }));
        site += 2;
    }
    if site < sites.len() {
        logup.col_from_iter((0..n_vec_rows).map(|row| sites[site][row]));
    }
    logup.finalize_last()
}

fn byte_from_bits<E: EvalAtRow>(bits: &[E::F]) -> E::F {
    bits.iter()
        .enumerate()
        .fold(m31_const::<E>(0), |acc, (bit, value)| {
            acc + m31_const::<E>(1u32 << bit) * value.clone()
        })
}

impl FrameworkEval for MdocRevocationRangeEval {
    fn log_size(&self) -> u32 {
        MDOC_REVOCATION_RANGE_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        MDOC_REVOCATION_RANGE_LOG_SIZE + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(revocation_range_active_id());
        let one = m31_const::<E>(1);
        eval.add_constraint(active.clone() * (active.clone() - one.clone()));

        let values: Vec<E::F> = (0..REVOCATION_RANGE_TRACE_COLS)
            .map(|_| eval.next_trace_mask())
            .collect();

        for byte_idx in 0..REVOCATION_RANGE_BYTE_COLS {
            let byte = values[byte_idx].clone();
            let bits = &values[REVOCATION_RANGE_BYTE_COLS + byte_idx * 8
                ..REVOCATION_RANGE_BYTE_COLS + (byte_idx + 1) * 8];
            for bit in bits {
                eval.add_constraint(active.clone() * bit.clone() * (bit.clone() - one.clone()));
            }
            eval.add_constraint(active.clone() * (byte - byte_from_bits::<E>(bits)));
        }

        let lower_carries_offset = REVOCATION_RANGE_BYTE_COLS + REVOCATION_RANGE_BIT_COLS;
        let upper_carries_offset = lower_carries_offset + REVOCATION_U64_BYTES;
        for carry in &values[lower_carries_offset..upper_carries_offset + REVOCATION_U64_BYTES] {
            eval.add_constraint(active.clone() * carry.clone() * (carry.clone() - one.clone()));
        }

        for byte_idx in 0..REVOCATION_U64_BYTES {
            let id = values[byte_idx].clone();
            let id_lo = values[REVOCATION_U64_BYTES + byte_idx].clone();
            let id_hi = values[2 * REVOCATION_U64_BYTES + byte_idx].clone();
            let lower_slack = values[3 * REVOCATION_U64_BYTES + byte_idx].clone();
            let upper_slack = values[4 * REVOCATION_U64_BYTES + byte_idx].clone();
            let lower_carry_in = if byte_idx == 0 {
                m31_const::<E>(0)
            } else {
                values[lower_carries_offset + byte_idx - 1].clone()
            };
            let lower_carry_out = values[lower_carries_offset + byte_idx].clone();
            let upper_carry_in = if byte_idx == 0 {
                m31_const::<E>(0)
            } else {
                values[upper_carries_offset + byte_idx - 1].clone()
            };
            let upper_carry_out = values[upper_carries_offset + byte_idx].clone();
            let add_one = m31_const::<E>(u32::from(byte_idx == 0));
            eval.add_constraint(
                active.clone()
                    * (id_lo + lower_slack + add_one.clone() + lower_carry_in
                        - id.clone()
                        - m31_const::<E>(256) * lower_carry_out),
            );
            eval.add_constraint(
                active.clone()
                    * (id + upper_slack + add_one + upper_carry_in
                        - id_hi
                        - m31_const::<E>(256) * upper_carry_out),
            );
        }
        eval.add_constraint(active.clone() * values[lower_carries_offset + 7].clone());
        eval.add_constraint(active.clone() * values[upper_carries_offset + 7].clone());

        let digest_tail_offset = upper_carries_offset + REVOCATION_U64_BYTES;
        let mut digest_values = Vec::with_capacity(33);
        digest_values.push(m31_const::<E>(PACKED_SHA_MSO_SLOT));
        digest_values.extend((0..REVOCATION_U64_BYTES).map(|index| values[index].clone()));
        digest_values.extend(
            (0..REVOCATION_RANGE_DIGEST_TAIL_COLS)
                .map(|index| values[digest_tail_offset + index].clone()),
        );
        eval.add_to_relation(RelationEntry::new(
            &self.mso_digest_relation,
            E::EF::from(active.clone()),
            &digest_values,
        ));
        let field_id = m31_const::<E>(MDOC_REVOCATION_MESSAGE_FIELD_ID);
        for byte_idx in 0..TS13_REVOCATION_MESSAGE_LEN {
            let value = match byte_idx {
                0..=7 => values[REVOCATION_U64_BYTES + byte_idx].clone(),
                8..=15 => values[2 * REVOCATION_U64_BYTES + byte_idx - 8].clone(),
                _ => m31_const::<E>(u32::from(self.epoch.to_le_bytes()[byte_idx - 16])),
            };
            eval.add_to_relation(RelationEntry::new(
                &self.message_field_relation,
                E::EF::from(active.clone()),
                &[field_id.clone(), m31_const::<E>(byte_idx as u32), value],
            ));
        }
        if let Some(beta) = self.claim_mask_beta {
            add_claim_mask_fraction(&mut eval, beta);
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

impl Air for MdocRevocationRangeBind {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(0x5453_3133_524e_4702);
    }

    fn draw_relations(&mut self, _channel: &mut Blake2sChannel) {}

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![MDOC_REVOCATION_RANGE_LOG_SIZE],
            trace: vec![
                MDOC_REVOCATION_RANGE_LOG_SIZE;
                REVOCATION_RANGE_TRACE_COLS
                    + usize::from(self.claim_mask_challenge.is_some())
                        * CLAIM_MASK_TRACE_COLUMNS
            ],
            interaction: vec![
                MDOC_REVOCATION_RANGE_LOG_SIZE;
                (1 + TS13_REVOCATION_MESSAGE_LEN
                    + usize::from(self.claim_mask_challenge.is_some()))
                .div_ceil(2)
                    * SECURE_EXTENSION_DEGREE
            ],
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        vec![self.interaction_claim().claimed_sum]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        vec![revocation_range_active_id()]
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(vec![revocation_range_active_column()])
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let claim = self.interaction_claim().clone();
        self.component = Some(MdocRevocationRangeComponent::new(
            allocator,
            MdocRevocationRangeEval {
                mso_digest_relation: self.relation(),
                message_field_relation: self.message_relation(),
                epoch: self.epoch,
                claim_mask_beta: self.claim_mask_beta(),
            },
            claim.claimed_sum,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![self
            .component
            .as_ref()
            .expect("mdoc revocation range component is built")]
    }
}

impl AirProver for MdocRevocationRangeBind {
    fn max_log_size(&self) -> u32 {
        MDOC_REVOCATION_RANGE_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        MDOC_REVOCATION_RANGE_LOG_SIZE + 1
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(vec![revocation_range_active_column()]);
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc::MdocRevocationRangeBind",
            &[revocation_range_active_id()],
            &[revocation_range_active_column()],
        )
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(revocation_range_base_trace(
            self.witness
                .as_ref()
                .expect("mdoc revocation range witness is set"),
            self.mso_digest
                .as_ref()
                .expect("mdoc revocation range MSO digest is set"),
        ));
        if let Some(mask) = &self.claim_mask_trace {
            tb.extend_evals(mask.columns().to_vec());
        }
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let claim_mask = self.claim_mask_trace.as_ref().zip(self.claim_mask_beta());
        let (trace, claimed_sum) = revocation_range_interaction_trace(
            self.witness
                .as_ref()
                .expect("mdoc revocation range witness is set"),
            self.mso_digest
                .as_ref()
                .expect("mdoc revocation range MSO digest is set"),
            &self.relation(),
            self.epoch,
            &self.message_relation(),
            claim_mask,
        );
        tb.extend_evals(trace);
        self.interaction_claim = Some(MdocRevocationRangeInteractionClaim { claimed_sum });
        self.witness.take();
        self.mso_digest.take();
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![self
            .component
            .as_ref()
            .expect("mdoc revocation range component is built")]
    }
}

struct MdocCoprocessorBindingProver {
    issuer_input: EcdsaVerifyInput,
    device_input: EcdsaVerifyInput,
    /// Revocation sorted-pair signature, proven as the bundle's third ECDSA
    /// instance set.
    revocation_input: EcdsaVerifyInput,
    issuer_witness: eu_id_ec_coprocessor::ecdsa::Witness,
    device_witness: eu_id_ec_coprocessor::ecdsa::Witness,
    revocation_witness: eu_id_ec_coprocessor::ecdsa::Witness,
    mac_key_shares: eu_id_ec_coprocessor::ecdsa::MdocP4bMacKeyShares,
    mac_state: MdocP4bMacSharedState,
    bundle: Option<eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle>,
}

fn random_mdoc_p4b_mac_key_shares() -> eu_id_ec_coprocessor::ecdsa::MdocP4bMacKeyShares {
    eu_id_ec_coprocessor::ecdsa::MdocP4bMacKeyShares(std::array::from_fn(|_| {
        let mut share = [0u8; 16];
        rand::thread_rng().fill_bytes(&mut share);
        share
    }))
}

impl MdocCoprocessorBindingProver {
    fn new(
        issuer_input: EcdsaVerifyInput,
        device_input: EcdsaVerifyInput,
        revocation_input: EcdsaVerifyInput,
        mac_key_shares: eu_id_ec_coprocessor::ecdsa::MdocP4bMacKeyShares,
        mac_state: MdocP4bMacSharedState,
    ) -> Result<Self, Error> {
        let issuer_witness = crate::ec_coprocessor::generate_witness_from_stwo(&issuer_input)
            .map_err(Error::CoprocessorWitness)?;
        let device_witness = crate::ec_coprocessor::generate_witness_from_stwo(&device_input)
            .map_err(Error::CoprocessorWitness)?;
        // Build and check the revocation witness before proof generation.
        // Return an error for an invalid sorted-pair signature.
        let revocation_witness =
            crate::ec_coprocessor::generate_witness_from_stwo(&revocation_input)
                .map_err(Error::CoprocessorWitness)?;
        crate::ec_coprocessor::verify_witness_from_stwo(&revocation_input, &revocation_witness)
            .map_err(Error::CoprocessorWitness)?;
        Ok(Self {
            issuer_input,
            device_input,
            revocation_input,
            issuer_witness,
            device_witness,
            revocation_witness,
            mac_key_shares,
            mac_state,
            bundle: None,
        })
    }
}

impl Air for MdocCoprocessorBindingProver {
    fn mix_public(&self, _channel: &mut Blake2sChannel) {}
    fn draw_relations(&mut self, _channel: &mut Blake2sChannel) {}

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: Vec::new(),
            trace: Vec::new(),
            interaction: Vec::new(),
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        Vec::new()
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        Vec::new()
    }

    fn build_components(&mut self, _allocator: &mut TraceLocationAllocator) {}

    fn components(&self) -> Vec<&dyn Component> {
        Vec::new()
    }
}

impl AirProver for MdocCoprocessorBindingProver {
    fn max_log_size(&self) -> u32 {
        0
    }

    fn write_preprocessed(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}
    fn write_trace(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}
    fn write_interaction(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

    fn prove_post_interaction(&mut self, channel: &mut air_core::Ch) {
        let issuer_projection =
            crate::ec_coprocessor::issuer_key_projection_from_stwo(&self.issuer_input);
        let device_projection =
            crate::ec_coprocessor::message_hash_projection_from_stwo(&self.device_input);
        // Only the revocation key is public. The message hash is rejoined to
        // the STARK-side revocation SHA through the final two private MAC
        // values. R and s remain entirely inside the coprocessor witness.
        let revocation_projection =
            crate::ec_coprocessor::public_key_projection_from_stwo(&self.revocation_input);
        let tagged: Vec<(&[u8], &eu_id_ec_coprocessor::ecdsa::EcdsaPublicProjection)> = vec![
            (b"issuer".as_slice(), &issuer_projection),
            (b"device".as_slice(), &device_projection),
            (b"revocation".as_slice(), &revocation_projection),
        ];
        crate::mix_coprocessor_tagged_projections(channel, &tagged)
            .expect("mdoc coprocessor public projections mix");
        let seed = crate::draw_coprocessor_seed(channel);
        let revocation = (
            &self.revocation_input,
            &revocation_projection,
            &self.revocation_witness,
        );
        let bundle = crate::ec_coprocessor::prove_mdoc_p4b_circuit_bundle_from_stwo(
            &self.issuer_input,
            &issuer_projection,
            &self.issuer_witness,
            &self.device_input,
            &device_projection,
            &self.device_witness,
            revocation,
            &self.mac_key_shares,
            seed,
        )
        .expect("mdoc P4b coprocessor bundle proves MAC-bound witnesses");
        let av = crate::ec_coprocessor::mdoc_p4b_av_from_bundle(&bundle, seed);
        self.mac_state.publish(MdocP4bMacPublic {
            av,
            tags: bundle.mac_tags.clone(),
        });
        crate::mix_coprocessor_rejoin(channel, &bundle).expect("mdoc coprocessor rejoin mixes");
        self.bundle = Some(bundle);
        self.issuer_witness.values.clear();
        self.device_witness.values.clear();
        self.revocation_witness.values.clear();
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        Vec::new()
    }
}

struct MdocCoprocessorBindingVerifier {
    issuer_input: EcdsaVerifyInput,
    device_input: EcdsaVerifyInput,
    /// Statement-recomputed mandatory revocation input.
    revocation_input: EcdsaVerifyInput,
    bundle: eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle,
    mac_state: MdocP4bMacSharedState,
}

impl Air for MdocCoprocessorBindingVerifier {
    fn mix_public(&self, _channel: &mut Blake2sChannel) {}
    fn draw_relations(&mut self, _channel: &mut Blake2sChannel) {}

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: Vec::new(),
            trace: Vec::new(),
            interaction: Vec::new(),
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        Vec::new()
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        Vec::new()
    }

    fn build_components(&mut self, _allocator: &mut TraceLocationAllocator) {}

    fn components(&self) -> Vec<&dyn Component> {
        Vec::new()
    }

    fn verify_post_interaction(
        &mut self,
        channel: &mut air_core::Ch,
    ) -> Result<(), VerificationError> {
        let issuer_projection =
            crate::ec_coprocessor::issuer_key_projection_from_stwo(&self.issuer_input);
        let device_projection =
            crate::ec_coprocessor::message_hash_projection_from_stwo(&self.device_input);
        let revocation_projection =
            crate::ec_coprocessor::public_key_projection_from_stwo(&self.revocation_input);
        let tagged: Vec<(&[u8], &eu_id_ec_coprocessor::ecdsa::EcdsaPublicProjection)> = vec![
            (b"issuer".as_slice(), &issuer_projection),
            (b"device".as_slice(), &device_projection),
            (b"revocation".as_slice(), &revocation_projection),
        ];
        crate::mix_coprocessor_tagged_projections(channel, &tagged)
            .map_err(VerificationError::InvalidStructure)?;
        let seed = crate::draw_coprocessor_seed(channel);
        crate::ec_coprocessor::verify_mdoc_p4b_circuit_bundle_from_stwo(
            &issuer_projection,
            &device_projection,
            &revocation_projection,
            &self.bundle,
            seed,
        )
        .map_err(|err| VerificationError::InvalidStructure(format!("{err:?}")))?;
        let av = crate::ec_coprocessor::mdoc_p4b_av_from_bundle(&self.bundle, seed);
        self.mac_state.publish(MdocP4bMacPublic {
            av,
            tags: self.bundle.mac_tags.clone(),
        });
        crate::mix_coprocessor_rejoin(channel, &self.bundle)
            .map_err(VerificationError::InvalidStructure)?;
        Ok(())
    }
}

/// Runtime switch for the per-phase prove profile. Off unless
/// `EUID_PROVE_PROFILE=1`, so the default prove path pays one env lookup.
fn prove_profile_enabled() -> bool {
    std::env::var_os("EUID_PROVE_PROFILE").is_some_and(|value| value == "1")
}

pub(crate) fn prove_mdoc_circuit(
    extracted: &ExtractedPidMdoc,
    statement: &MdocCircuitStatement,
) -> Result<MdocCircuitProof, Error> {
    strict_verification_timestamp(statement.verification_time_epoch_seconds)
        .map_err(|_| Error::Prove("invalid verifier timestamp".to_string()))?;
    if !current_product_circuit_semantics(statement) {
        return Err(Error::Prove(PRODUCT_SEMANTICS_ERROR.to_string()));
    }
    prove_mdoc_circuit_with_pcs_config(extracted, statement, mdoc_production_pcs_config())
}

fn product_sha_messages<'a>(
    extracted: &'a ExtractedPidMdoc,
    revocation_message: &'a [u8; TS13_REVOCATION_MESSAGE_LEN],
) -> Result<Vec<&'a [u8]>, MdocError> {
    let selected_items: Vec<&[u8]> = extracted
        .extracted_attributes
        .iter()
        .map(|attribute| attribute.item.as_slice())
        .collect();
    validate_product_sha_input_sizes(
        extracted.mso.as_slice(),
        extracted.issuer_sig_structure.as_slice(),
        &selected_items,
    )?;

    let mut messages = Vec::with_capacity(3 + selected_items.len());
    messages.push(extracted.issuer_sig_structure.as_slice());
    messages.push(extracted.mso.as_slice());
    messages.push(revocation_message.as_slice());
    messages.extend(selected_items);
    Ok(messages)
}

fn prove_mdoc_circuit_with_pcs_config(
    extracted: &ExtractedPidMdoc,
    statement: &MdocCircuitStatement,
    config: PcsConfig,
) -> Result<MdocCircuitProof, Error> {
    if !ecdsa_inputs_equal(&statement.issuer_input, &extracted.issuer_ecdsa_input)
        || !ecdsa_inputs_equal(&statement.device_input, &extracted.device_ecdsa_input)
    {
        return Err(Error::P256InstanceMismatch);
    }

    let revocation_p256_input = ts13_revocation_p256_input(statement);

    // The product owns exactly one packed SHA component at the fixed profile
    // size. Its five message slots are ordered by the contract and exclude
    // DeviceAuthentication, whose hash is bound by the EC coprocessor path.
    let revocation_message = ts13_revocation_message_bytes(
        statement.ts13_revocation_range.id_lo,
        statement.ts13_revocation_range.id_hi,
        statement.ts13_revocation.epoch,
    );
    let packed_messages =
        product_sha_messages(extracted, &revocation_message).map_err(Error::Mdoc)?;
    let packed_sha_witness = compute_packed_sha256_witness(&packed_messages)
        .map_err(|error| Error::Prove(format!("packed SHA witness: {error}")))?;
    let shared_sha_log = crate::product_profile::PRODUCT_SHA_LOG_N_ROWS;
    let packed_sha_digest = SharedPackedShaDigestRelation::new();
    let sha_field = SharedFieldRelation::new();
    let scope_statement = mdoc_scope_statement(statement);
    let scope_handles = MdocScopeHandles::fresh(&scope_statement, packed_sha_digest.clone())
        .map_err(|error| Error::Prove(format!("mdoc scope handles: {error}")))?;
    let revocation_message_field = SharedFieldRelation::new();
    let sha_table_relations = SharedShaTableRelations::new();

    let item_outer_streams: Vec<_> = extracted
        .extracted_attributes
        .iter()
        .map(|attribute| attribute.item.clone())
        .collect();
    let mut mdoc_scope = MdocScope::new(
        scope_statement.clone(),
        extracted.issuer_sig_structure.clone(),
        item_outer_streams,
        scope_handles.clone(),
    )
    .map_err(|error| Error::Prove(format!("mdoc semantic scope: {error}")))?;
    mdoc_scope = mdoc_scope.with_payload_hash_binding();
    mdoc_scope = mdoc_scope
        .with_fixed_log_size(crate::product_profile::PRODUCT_MAX_SCOPE_LOG_SIZE)
        .map_err(|error| Error::Prove(format!("fixed mdoc scope: {error}")))?;
    let parser_stream_bytes = mdoc_scope.parser_stream_bytes().to_vec();
    let parser_specs = scope_handles
        .stream_specs(&scope_statement)
        .map_err(|error| Error::Prove(format!("mdoc parser specs: {error}")))?;
    if parser_specs.len() != parser_stream_bytes.len() {
        return Err(Error::Prove(
            "mdoc parser specification/witness count mismatch".to_string(),
        ));
    }
    let mut mdoc_cbor_streams = Vec::with_capacity(parser_specs.len());
    for (slot, spec) in parser_specs.into_iter().enumerate() {
        let (input_handle, input_field_id, max_message_len) = match spec.input {
            MdocScopeParserInput::ShaIssuer => (
                sha_field.clone(),
                PACKED_SHA_STREAM_FIELD_BASE + PACKED_SHA_ISSUER_SLOT,
                Some(6_164),
            ),
            MdocScopeParserInput::ShaItem(index) => {
                if index >= extracted.extracted_attributes.len() {
                    return Err(Error::Prove(
                        "mdoc item parser index is out of range".to_string(),
                    ));
                }
                (
                    sha_field.clone(),
                    PACKED_SHA_STREAM_FIELD_BASE + PACKED_SHA_ITEM_SLOT_BASE + index as u32,
                    Some(1_024),
                )
            }
            MdocScopeParserInput::Raw(handle) => (handle, spec.stream_id, None),
        };
        let bytes = match spec.mode {
            MdocCborInputMode::ShaPadded => {
                stwo_sha256::native::pad_message(&parser_stream_bytes[slot])
            }
            MdocCborInputMode::Raw => parser_stream_bytes[slot].clone(),
        };
        let parser = MdocCborStream::new_with_log_size(
            bytes,
            spec.mode,
            spec.stream_id,
            input_field_id,
            input_handle,
            Some(spec.parsed),
            crate::product_profile::PRODUCT_MAX_CBOR_LOG_SIZE,
            max_message_len,
        )
        .map_err(|error| Error::Prove(format!("mdoc CBOR parser: {error}")))?;
        mdoc_cbor_streams.push(parser);
    }
    let mut mso_exact_cbor = MdocCborStream::new_exact_sha(
        stwo_sha256::native::pad_message(&extracted.mso),
        NORMALIZED_MSO_STREAM_ID,
        PACKED_SHA_STREAM_FIELD_BASE + PACKED_SHA_MSO_SLOT,
        sha_field.clone(),
        MDOC_MSO_PAYLOAD_FIELD_ID,
        scope_handles.payload_hash_fields.clone(),
        None,
        crate::product_profile::PRODUCT_MAX_CBOR_LOG_SIZE,
        u32::try_from(crate::product_profile::PRODUCT_MAX_MSO_PAYLOAD_BYTES)
            .expect("product MSO bound fits u32"),
    )
    .map_err(|error| Error::Prove(format!("exact MSO CBOR/SHA binding: {error}")))?;

    let mut sha_tables = ShaTablesProver::new(&packed_sha_witness, sha_table_relations.clone());
    let mut packed_sha = Sha256Prover::new(&packed_sha_witness, shared_sha_log)
        .map_err(|error| Error::Prove(format!("packed SHA prover: {error}")))?
        .with_shared_tables(sha_table_relations.clone())
        .with_digest_handle(packed_sha_digest.clone())
        .with_field_handle(sha_field.clone());
    let mut mdoc_validity = MdocValidityBind::new(
        statement.verification_time_epoch_seconds,
        mdoc_validity_rows(
            extracted.valid_from_timestamp.text_bytes(),
            extracted.valid_until_timestamp.text_bytes(),
        ),
        scope_handles.semantic_fields.clone(),
    );
    let mut revocation_message_bind = MdocExactShaMessageBind::prover(
        "revocation_message",
        MDOC_REVOCATION_MESSAGE_FIELD_ID,
        PACKED_SHA_STREAM_FIELD_BASE + PACKED_SHA_REVOCATION_SLOT,
        -1,
        true,
        revocation_message.to_vec(),
        revocation_message_field.clone(),
        sha_field.clone(),
    );

    let mac_key_shares = random_mdoc_p4b_mac_key_shares();

    let mac_state = MdocP4bMacSharedState::default();

    let mut mdoc_mac = MdocMacBind::prover(
        &mac_key_shares,
        mdoc_p4b_mac_values(statement, &revocation_p256_input),
        mac_state.clone(),
        packed_sha_digest.clone(),
        scope_handles.semantic_fields.clone(),
    );

    let mut coprocessor = MdocCoprocessorBindingProver::new(
        statement.issuer_input.clone(),
        statement.device_input.clone(),
        revocation_p256_input.clone(),
        mac_key_shares,
        mac_state,
    )?;

    let age_public = statement.policy.age_public_input();
    let nat_public = nat_public_input_for(statement);
    let age_dob = DateOfBirth(predicates::Date {
        year: u32::from(u16::from_be_bytes([
            extracted.birth_date_bytes[0],
            extracted.birth_date_bytes[1],
        ])),
        month: u32::from(extracted.birth_date_bytes[2]),
        day: u32::from(extracted.birth_date_bytes[3]),
    });
    let nat_private = predicates::NatPrivateInput {
        nationalities: extracted
            .nationality_candidates
            .iter()
            .map(ParsedNationalityValue::predicate_code)
            .collect(),
    };
    let mut age = if statement.age_attribute_index.is_some() {
        let age = AgeRangeCheck::new(PcsConfig::default())
            .prover(&age_public, &age_dob)
            .map_err(Error::AgePrepare)?;
        Some(age.with_text_dob_binding(scope_handles.semantic_fields.clone()))
    } else {
        None
    };
    let mut nat = if statement.nationality_attribute_index.is_some() {
        Some(
            NationalityPredicate::new(PcsConfig::default())
                .prover(&nat_public, &nat_private)
                .map_err(Error::NatPrepare)?
                .with_nat_binding(scope_handles.semantic_fields.clone()),
        )
    } else {
        None
    };
    let mut ts13_revocation_public =
        MdocRevocationPublicBind::new(statement.ts13_revocation.clone());
    let mso_digest_bytes: [u8; 32] = Sha256::digest(&extracted.mso).into();
    let mut ts13_revocation_range = MdocRevocationRangeBind::prover(
        statement.ts13_revocation_range.clone(),
        mso_digest_bytes,
        packed_sha_digest.clone(),
        statement.ts13_revocation.epoch,
        revocation_message_field.clone(),
    );

    // Every private interaction claim receives one committed mask from a
    // single per-proof ring. The ring targets sum to zero, while the shared
    // challenge is drawn only after every mask column has been committed.
    let claim_mask_challenge = SharedClaimMaskChallenge::new();
    let mut claim_mask_log_sizes = Vec::new();
    claim_mask_log_sizes.extend(sha_tables.ordered_claim_mask_log_sizes());
    claim_mask_log_sizes.extend(packed_sha.ordered_claim_mask_log_sizes());
    for parser in &mdoc_cbor_streams {
        claim_mask_log_sizes.extend(parser.ordered_claim_mask_log_sizes());
    }
    claim_mask_log_sizes.extend(mso_exact_cbor.ordered_claim_mask_log_sizes());
    claim_mask_log_sizes.extend(mdoc_scope.ordered_claim_mask_log_sizes());
    claim_mask_log_sizes.extend(mdoc_validity.ordered_claim_mask_log_sizes());
    claim_mask_log_sizes.extend(revocation_message_bind.ordered_claim_mask_log_sizes());
    if let Some(age) = &age {
        claim_mask_log_sizes.extend(age.ordered_claim_mask_log_sizes());
    }
    if let Some(nat) = &nat {
        claim_mask_log_sizes.extend(nat.ordered_claim_mask_log_sizes());
    }
    claim_mask_log_sizes.extend(ts13_revocation_range.ordered_claim_mask_log_sizes());

    claim_mask_log_sizes.extend(mdoc_mac.ordered_claim_mask_log_sizes());

    let mut claim_mask_ring = ClaimMaskRing::new(&claim_mask_log_sizes)
        .map_err(|error| Error::Prove(format!("claim-mask ring: {error}")))?;

    let logs = sha_tables.ordered_claim_mask_log_sizes();
    let masks = take_claim_masks(&mut claim_mask_ring, &logs)
        .map_err(|error| Error::Prove(format!("SHA-table claim masks: {error}")))?;
    sha_tables = sha_tables
        .with_claim_masks(masks, claim_mask_challenge.clone())
        .map_err(|error| Error::Prove(format!("SHA-table claim masks: {error}")))?;

    let logs = packed_sha.ordered_claim_mask_log_sizes();
    let masks = take_claim_masks(&mut claim_mask_ring, &logs)
        .map_err(|error| Error::Prove(format!("packed SHA claim masks: {error}")))?;
    packed_sha = packed_sha
        .with_claim_masks(masks, claim_mask_challenge.clone())
        .map_err(|error| Error::Prove(format!("packed SHA claim masks: {error}")))?;
    mdoc_cbor_streams = mdoc_cbor_streams
        .into_iter()
        .enumerate()
        .map(|(index, parser)| {
            let log_size = parser.ordered_claim_mask_log_sizes()[0];
            let mask = claim_mask_ring.take(log_size).map_err(|error| {
                Error::Prove(format!("mdoc parser {index} claim mask: {error}"))
            })?;
            Ok(parser.with_claim_mask(mask, claim_mask_challenge.clone()))
        })
        .collect::<Result<Vec<_>, Error>>()?;
    let log_size = mso_exact_cbor.ordered_claim_mask_log_sizes()[0];
    let mask = claim_mask_ring
        .take(log_size)
        .map_err(|error| Error::Prove(format!("exact MSO parser claim mask: {error}")))?;
    mso_exact_cbor = mso_exact_cbor.with_claim_mask(mask, claim_mask_challenge.clone());

    let logs = mdoc_scope.ordered_claim_mask_log_sizes();
    let masks = take_claim_masks(&mut claim_mask_ring, &logs)
        .map_err(|error| Error::Prove(format!("mdoc scope claim masks: {error}")))?;
    mdoc_scope = mdoc_scope.with_claim_masks(masks, claim_mask_challenge.clone());

    let log_size = mdoc_validity.ordered_claim_mask_log_sizes()[0];
    let mask = claim_mask_ring
        .take(log_size)
        .map_err(|error| Error::Prove(format!("mdoc validity claim mask: {error}")))?;
    mdoc_validity = mdoc_validity.with_claim_mask(mask, claim_mask_challenge.clone());

    let log_size = revocation_message_bind.ordered_claim_mask_log_sizes()[0];
    let mask = claim_mask_ring
        .take(log_size)
        .map_err(|error| Error::Prove(format!("revocation message claim mask: {error}")))?;
    revocation_message_bind =
        revocation_message_bind.with_claim_mask(mask, claim_mask_challenge.clone());
    age = age
        .map(|age| {
            let logs = age.ordered_claim_mask_log_sizes();
            let masks = take_claim_masks(&mut claim_mask_ring, &logs)
                .map_err(|error| Error::Prove(format!("age claim masks: {error}")))?;
            age.with_claim_masks(masks, claim_mask_challenge.clone())
                .map_err(|error| Error::Prove(format!("age claim masks: {error}")))
        })
        .transpose()?;
    nat = nat
        .map(|nat| {
            let logs = nat.ordered_claim_mask_log_sizes();
            let masks = take_claim_masks(&mut claim_mask_ring, &logs)
                .map_err(|error| Error::Prove(format!("nationality claim masks: {error}")))?;
            nat.with_claim_masks(masks, claim_mask_challenge.clone())
                .map_err(|error| Error::Prove(format!("nationality claim masks: {error}")))
        })
        .transpose()?;
    let log_size = ts13_revocation_range.ordered_claim_mask_log_sizes()[0];
    let mask = claim_mask_ring
        .take(log_size)
        .map_err(|error| Error::Prove(format!("revocation range claim mask: {error}")))?;
    ts13_revocation_range =
        ts13_revocation_range.with_claim_mask(mask, claim_mask_challenge.clone());

    {
        let logs = mdoc_mac.ordered_claim_mask_log_sizes();
        let masks = take_claim_masks(&mut claim_mask_ring, &logs)
            .map_err(|error| Error::Prove(format!("mdoc MAC claim masks: {error}")))?;
        mdoc_mac = mdoc_mac
            .with_claim_masks(masks, claim_mask_challenge.clone())
            .map_err(|error| Error::Prove(format!("mdoc MAC claim masks: {error}")))?;
    }
    claim_mask_ring
        .finish()
        .map_err(|error| Error::Prove(format!("claim-mask ring: {error}")))?;
    let mut claim_mask_anchor =
        ClaimMaskChallengeModule::new(claim_mask_challenge, claim_mask_log_sizes)
            .map_err(|error| Error::Prove(format!("claim-mask anchor: {error}")))?;

    let stark_proof = {
        let mut modules: Vec<&mut dyn AirProver> = vec![&mut sha_tables, &mut packed_sha];
        for parser in &mut mdoc_cbor_streams {
            modules.push(parser);
        }
        modules.push(&mut mso_exact_cbor);
        modules.push(&mut mdoc_scope);
        modules.push(&mut mdoc_validity);
        modules.push(&mut revocation_message_bind);
        if let Some(age) = age.as_mut() {
            modules.push(age);
        }
        if let Some(nat) = nat.as_mut() {
            modules.push(nat);
        }
        modules.push(&mut ts13_revocation_public);
        modules.push(&mut ts13_revocation_range);

        modules.push(&mut coprocessor);

        modules.push(&mut mdoc_mac);
        modules.push(&mut claim_mask_anchor);
        let (proof, profile) = air_core::prove_profiled(modules.as_mut_slice(), config)
            .map_err(|e| Error::Prove(format!("{e:?}")))?;
        if prove_profile_enabled() {
            eprintln!("[euid-prove-profile] mdoc stark\n{profile}");
        }
        proof
    };

    let coprocessor_bundle = coprocessor.bundle.take().ok_or(Error::CoprocessorMissing)?;

    Ok(MdocCircuitProof {
        stark_proof,
        sha_tables_interaction_claim: sha_tables.interaction_claim().clone(),
        packed_sha_interaction_claim: packed_sha.interaction_claim().clone(),

        coprocessor_bundle,

        mdoc_mac_interaction_claim: mdoc_mac.interaction_claim().clone(),
        mdoc_cbor_log_sizes: mdoc_cbor_streams
            .iter()
            .map(MdocCborStream::log_size)
            .collect(),
        mdoc_cbor_interaction_claims: mdoc_cbor_streams
            .iter()
            .map(|parser| parser.interaction_claim().clone())
            .collect(),
        mso_exact_cbor_interaction_claim: mso_exact_cbor.interaction_claim().clone(),
        mdoc_scope_metadata: mdoc_scope.metadata().clone(),
        mdoc_scope_interaction_claim: mdoc_scope.interaction_claim().clone(),

        mdoc_validity_interaction_claim: mdoc_validity.interaction_claim().clone(),
        revocation_message_bind_interaction_claim: revocation_message_bind
            .interaction_claim()
            .clone(),
        ts13_revocation_range_interaction_claim: ts13_revocation_range.interaction_claim().clone(),
        age_public: age.as_ref().map(|_| age_public),
        // Predicate public inputs remain statement-bound, while every private
        // LogUp claimed sum is randomized by its committed claim-mask column.
        age_claimed_sums: age.as_ref().map(|age| age.claimed_sums()),
        nat_public: nat.as_ref().map(|_| nat_public),
        nat_claimed_sums: nat.as_ref().map(|nat| nat.claimed_sums()),
    })
}

#[cfg(test)]
fn verify_mdoc_circuit(
    proof: &MdocCircuitProof,
    statement: &MdocCircuitStatement,
) -> Result<(), Error> {
    if !current_product_circuit_semantics(statement) {
        return Err(Error::Verify(PRODUCT_SEMANTICS_ERROR.to_string()));
    }
    proof.validate_product_fixed_shape()?;
    verify_mdoc_circuit_with_pcs_config(proof, statement, mdoc_production_pcs_config())
}

pub fn verify_product_mdoc_public_statement(
    proof: &MdocCircuitProof,
    statement: &MdocPublicStatement,
) -> Result<(), Error> {
    if !current_product_public_semantics(statement) {
        return Err(Error::Verify(PRODUCT_SEMANTICS_ERROR.to_string()));
    }
    proof.validate_product_fixed_shape()?;
    strict_verification_timestamp(statement.verification_time_epoch_seconds)
        .map_err(|_| Error::Verify("invalid verifier timestamp".to_string()))?;
    validate_product_requested_attributes(&statement.attributes)
        .map_err(|error| Error::Verify(format!("invalid mdoc disclosure scope: {error:?}")))?;
    let verifier_statement = statement.verifier_circuit_statement();
    verify_mdoc_circuit_with_pcs_config(proof, &verifier_statement, mdoc_production_pcs_config())
}

fn verify_mdoc_circuit_with_pcs_config(
    proof: &MdocCircuitProof,
    statement: &MdocCircuitStatement,
    expected_pcs_config: PcsConfig,
) -> Result<(), Error> {
    verify_mdoc_circuit_with_pcs_config_impl(proof, statement, expected_pcs_config, None)
}

/// `shape_sink` is instrumentation only. Verification behaviour is identical
/// whether or not a sink is supplied; [`mdoc_proof_byte_breakdown`] passes one
/// so the byte accounting reads the verifier's own module list instead of a
/// copy that could drift from it.
fn verify_mdoc_circuit_with_pcs_config_impl(
    proof: &MdocCircuitProof,
    statement: &MdocCircuitStatement,
    expected_pcs_config: PcsConfig,
    shape_sink: Option<&mut Vec<MdocModuleShape>>,
) -> Result<(), Error> {
    strict_verification_timestamp(statement.verification_time_epoch_seconds)
        .map_err(|_| Error::Verify("invalid verifier timestamp".to_string()))?;

    if proof.age_public
        != statement
            .age_attribute_index
            .map(|_| statement.policy.age_public_input())
        || proof.age_claimed_sums.is_some() != statement.age_attribute_index.is_some()
    {
        return Err(Error::AgePolicyMismatch);
    }
    if proof.nat_public
        != statement
            .nationality_attribute_index
            .map(|_| nat_public_input_for(statement))
        || proof.nat_claimed_sums.is_some() != statement.nationality_attribute_index.is_some()
    {
        return Err(Error::NatPolicyMismatch);
    }

    let packed_sha_digest = SharedPackedShaDigestRelation::new();
    let sha_field = SharedFieldRelation::new();
    let revocation_message_field = SharedFieldRelation::new();
    let attribute_count = statement.attributes.len();
    let expected_parser_count = mdoc_scope_parser_count(attribute_count)
        .ok_or_else(|| Error::Verify("mdoc parser count overflow".to_string()))?;
    if proof.mdoc_cbor_log_sizes.len() != expected_parser_count
        || proof.mdoc_cbor_interaction_claims.len() != expected_parser_count
    {
        return Err(Error::Verify(
            "mdoc proof carries an unsupported parser count".to_string(),
        ));
    }

    let scope_statement = mdoc_scope_statement(statement);
    let scope_handles = MdocScopeHandles::fresh(&scope_statement, packed_sha_digest.clone())
        .map_err(|error| Error::Verify(format!("mdoc scope handles: {error}")))?;
    let sha_table_relations = SharedShaTableRelations::new();

    if proof.stark_proof.config != expected_pcs_config {
        return Err(Error::WeakConfig {
            got: proof.stark_proof.config,
            expected: expected_pcs_config,
        });
    }

    let mut sha_tables = ShaTablesVerifier::new(
        proof.sha_tables_interaction_claim.clone(),
        sha_table_relations.clone(),
    );
    let mut packed_sha = Sha256Verifier::new(
        crate::product_profile::PRODUCT_SHA_LOG_N_ROWS,
        proof.packed_sha_interaction_claim.clone(),
    )
    .with_shared_tables(sha_table_relations.clone())
    .with_digest_handle(packed_sha_digest.clone())
    .with_field_handle(sha_field.clone());
    let parser_specs = scope_handles
        .stream_specs(&scope_statement)
        .map_err(|error| Error::Verify(format!("mdoc parser specs: {error}")))?;
    let mut mdoc_cbor_streams = Vec::with_capacity(expected_parser_count);
    for (index, spec) in parser_specs.into_iter().enumerate() {
        let (input_handle, input_field_id, max_message_len) = match spec.input {
            MdocScopeParserInput::ShaIssuer => (
                sha_field.clone(),
                PACKED_SHA_STREAM_FIELD_BASE + PACKED_SHA_ISSUER_SLOT,
                Some(6_164),
            ),
            MdocScopeParserInput::ShaItem(item_index) => {
                if item_index >= attribute_count {
                    return Err(Error::Verify(
                        "mdoc item parser index is out of range".to_string(),
                    ));
                }
                (
                    sha_field.clone(),
                    PACKED_SHA_STREAM_FIELD_BASE + PACKED_SHA_ITEM_SLOT_BASE + item_index as u32,
                    Some(1_024),
                )
            }
            MdocScopeParserInput::Raw(handle) => (handle, spec.stream_id, None),
        };
        mdoc_cbor_streams.push(
            MdocCborStream::verifier(
                spec.mode,
                spec.stream_id,
                input_field_id,
                proof.mdoc_cbor_log_sizes[index],
                input_handle,
                Some(spec.parsed),
                max_message_len,
                proof.mdoc_cbor_interaction_claims[index].clone(),
            )
            .map_err(|error| Error::Verify(format!("mdoc CBOR parser: {error}")))?,
        );
    }
    let mut mso_exact_cbor = MdocCborStream::verifier_exact_sha(
        NORMALIZED_MSO_STREAM_ID,
        PACKED_SHA_STREAM_FIELD_BASE + PACKED_SHA_MSO_SLOT,
        sha_field.clone(),
        MDOC_MSO_PAYLOAD_FIELD_ID,
        scope_handles.payload_hash_fields.clone(),
        None,
        crate::product_profile::PRODUCT_MAX_CBOR_LOG_SIZE,
        u32::try_from(crate::product_profile::PRODUCT_MAX_MSO_PAYLOAD_BYTES)
            .expect("product MSO bound fits u32"),
        proof.mso_exact_cbor_interaction_claim.clone(),
    )
    .map_err(|error| Error::Verify(format!("exact MSO CBOR/SHA binding: {error}")))?;
    let mut mdoc_scope = MdocScope::verifier(
        scope_statement,
        proof.mdoc_scope_metadata.clone(),
        scope_handles.clone(),
        proof.mdoc_scope_interaction_claim.clone(),
    )
    .map_err(|error| Error::Verify(format!("mdoc semantic scope: {error}")))?;
    mdoc_scope = mdoc_scope.with_payload_hash_binding();

    let mut mdoc_validity = MdocValidityBind::verifier(
        statement.verification_time_epoch_seconds,
        mdoc_validity_rows([0; 20], [0; 20]),
        scope_handles.semantic_fields.clone(),
        proof.mdoc_validity_interaction_claim.clone(),
    );
    let mut revocation_message_bind = MdocExactShaMessageBind::verifier(
        "revocation_message",
        MDOC_REVOCATION_MESSAGE_FIELD_ID,
        PACKED_SHA_STREAM_FIELD_BASE + PACKED_SHA_REVOCATION_SLOT,
        -1,
        true,
        TS13_REVOCATION_MESSAGE_LEN,
        revocation_message_field.clone(),
        sha_field.clone(),
        proof.revocation_message_bind_interaction_claim.clone(),
    );
    let mut age = if statement.age_attribute_index.is_some() {
        let public = proof.age_public.as_ref().ok_or(Error::AgePolicyMismatch)?;
        let claimed_sums = proof
            .age_claimed_sums
            .as_ref()
            .ok_or(Error::AgePolicyMismatch)?;
        let age = AgeRangeCheck::new(PcsConfig::default())
            .verifier(public, claimed_sums)
            .map_err(Error::AgePrepare)?;
        Some(age.with_text_dob_binding(scope_handles.semantic_fields.clone()))
    } else {
        None
    };
    let mut nat = if statement.nationality_attribute_index.is_some() {
        let public = proof.nat_public.as_ref().ok_or(Error::NatPolicyMismatch)?;
        let claimed_sums = proof
            .nat_claimed_sums
            .as_ref()
            .ok_or(Error::NatPolicyMismatch)?;
        Some(
            NationalityPredicate::new(PcsConfig::default())
                .verifier_for_private_prefix(public, claimed_sums)
                .map_err(Error::NatPrepare)?
                .with_nat_binding(scope_handles.semantic_fields.clone()),
        )
    } else {
        None
    };

    let mac_state = MdocP4bMacSharedState::default();

    let mut mdoc_mac = MdocMacBind::verifier(
        mac_state.clone(),
        packed_sha_digest.clone(),
        scope_handles.semantic_fields.clone(),
        proof.mdoc_mac_interaction_claim.clone(),
    );

    let revocation_coprocessor_input = EcdsaVerifyInput {
        message_hash: U256([0; 32]),
        signature: Signature {
            r: U256([0; 32]),
            s: U256([0; 32]),
        },
        public_key: statement.ts13_revocation.revocation_public_key.clone(),
    };

    let mut coprocessor = MdocCoprocessorBindingVerifier {
        issuer_input: statement.issuer_input.clone(),
        device_input: statement.device_input.clone(),
        revocation_input: revocation_coprocessor_input,
        bundle: proof.coprocessor_bundle.clone(),
        mac_state,
    };
    let mut ts13_revocation_public =
        MdocRevocationPublicBind::new(statement.ts13_revocation.clone());
    let mut ts13_revocation_range = MdocRevocationRangeBind::verifier(
        packed_sha_digest.clone(),
        statement.ts13_revocation.epoch,
        revocation_message_field.clone(),
        proof.ts13_revocation_range_interaction_claim.clone(),
    );

    let claim_mask_challenge = SharedClaimMaskChallenge::new();
    let mut claim_mask_log_sizes = Vec::new();
    claim_mask_log_sizes.extend(sha_tables.ordered_claim_mask_log_sizes());
    claim_mask_log_sizes.extend(packed_sha.ordered_claim_mask_log_sizes());
    for parser in &mdoc_cbor_streams {
        claim_mask_log_sizes.extend(parser.ordered_claim_mask_log_sizes());
    }
    claim_mask_log_sizes.extend(mso_exact_cbor.ordered_claim_mask_log_sizes());
    claim_mask_log_sizes.extend(mdoc_scope.ordered_claim_mask_log_sizes());
    claim_mask_log_sizes.extend(mdoc_validity.ordered_claim_mask_log_sizes());
    claim_mask_log_sizes.extend(revocation_message_bind.ordered_claim_mask_log_sizes());
    if let Some(age) = &age {
        claim_mask_log_sizes.extend(age.ordered_claim_mask_log_sizes());
    }
    if let Some(nat) = &nat {
        claim_mask_log_sizes.extend(nat.ordered_claim_mask_log_sizes());
    }
    claim_mask_log_sizes.extend(ts13_revocation_range.ordered_claim_mask_log_sizes());

    claim_mask_log_sizes.extend(mdoc_mac.ordered_claim_mask_log_sizes());

    sha_tables = sha_tables.with_claim_masks(claim_mask_challenge.clone());
    packed_sha = packed_sha.with_claim_masks(claim_mask_challenge.clone());
    mdoc_cbor_streams = mdoc_cbor_streams
        .into_iter()
        .map(|parser| parser.with_claim_mask_verifier(claim_mask_challenge.clone()))
        .collect();
    mso_exact_cbor = mso_exact_cbor.with_claim_mask_verifier(claim_mask_challenge.clone());
    mdoc_scope = mdoc_scope.with_claim_mask_verifier(claim_mask_challenge.clone());
    mdoc_validity = mdoc_validity.with_claim_mask_verifier(claim_mask_challenge.clone());
    revocation_message_bind =
        revocation_message_bind.with_claim_mask_verifier(claim_mask_challenge.clone());
    age = age.map(|age| age.with_claim_masks(claim_mask_challenge.clone()));
    nat = nat.map(|nat| nat.with_claim_masks(claim_mask_challenge.clone()));
    ts13_revocation_range =
        ts13_revocation_range.with_claim_mask_verifier(claim_mask_challenge.clone());

    {
        mdoc_mac = mdoc_mac.with_claim_masks_verifier(claim_mask_challenge.clone());
    }
    let mut claim_mask_anchor =
        ClaimMaskChallengeModule::new(claim_mask_challenge, claim_mask_log_sizes)
            .map_err(|error| Error::Verify(format!("claim-mask anchor: {error}")))?;

    // Read before the module list borrows `age`/`nat` mutably.
    let has_age = age.is_some();
    let has_nationality = nat.is_some();

    let mut modules: Vec<&mut dyn Air> = vec![&mut sha_tables, &mut packed_sha];
    for parser in &mut mdoc_cbor_streams {
        modules.push(parser);
    }
    modules.push(&mut mso_exact_cbor);
    modules.push(&mut mdoc_scope);
    modules.push(&mut mdoc_validity);
    modules.push(&mut revocation_message_bind);
    if let Some(age) = age.as_mut() {
        modules.push(age);
    }
    if let Some(nat) = nat.as_mut() {
        modules.push(nat);
    }
    modules.push(&mut ts13_revocation_public);
    modules.push(&mut ts13_revocation_range);

    modules.push(&mut coprocessor);

    modules.push(&mut mdoc_mac);
    modules.push(&mut claim_mask_anchor);
    if let Some(sink) = shape_sink {
        let names = mdoc_module_names(
            attribute_count,
            expected_parser_count,
            has_age,
            has_nationality,
        );
        assert_eq!(
            names.len(),
            modules.len(),
            "mdoc module name list drifted from the verifier module list"
        );
        *sink = names
            .into_iter()
            .zip(modules.iter())
            .map(|(name, module)| MdocModuleShape {
                name,
                preprocessed_ids: module.preprocessed_column_ids(),
                layout: module.layout(),
                post_interaction: module.post_interaction_log_sizes(),
            })
            .collect();
    }
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let canonical_root = air_core::compute_canonical_preprocessed_root(
            modules.as_mut_slice(),
            expected_pcs_config,
        )?;
        air_core::verify_with_expected_preprocessed_root(
            modules.as_mut_slice(),
            &proof.stark_proof,
            Some(canonical_root),
        )
    })) {
        Ok(Ok(())) => Ok(()),
        Ok(Err(air_core::VerifyError::PreprocessedRootMismatch { got, expected })) => {
            Err(Error::PreprocessedRootMismatch { got, expected })
        }
        Ok(Err(error)) => Err(Error::Verify(format!("{error:?}"))),
        Err(_) => Err(Error::Verify(
            "malformed mdoc proof panicked during verification".to_string(),
        )),
    }
}

/// One module's committed shape, captured from the verifier's own module list.
struct MdocModuleShape {
    name: String,
    preprocessed_ids: Vec<PreProcessedColumnId>,
    layout: TreeLayout,
    post_interaction: Vec<u32>,
}

/// Module labels in the exact order the prover and verifier push them.
///
/// Kept beside the two module lists it names; the capture in
/// [`verify_mdoc_circuit_with_pcs_config_impl`] asserts the lengths agree, so a
/// module added or removed without a label here fails loudly.
fn mdoc_module_names(
    _attribute_count: usize,
    parser_count: usize,
    has_age: bool,
    has_nationality: bool,
) -> Vec<String> {
    let mut names: Vec<String> = ["sha_tables", "packed_sha"]
        .iter()
        .map(|name| (*name).to_string())
        .collect();
    names.extend((0..parser_count).map(|index| format!("mdoc_cbor_stream[{index}]")));
    names.push("mso_exact_cbor".to_string());
    names.push("mdoc_scope".to_string());
    names.push("mdoc_validity".to_string());
    names.push("revocation_message_bind".to_string());
    if has_age {
        names.push("age_predicate".to_string());
    }
    if has_nationality {
        names.push("nationality_predicate".to_string());
    }
    names.push("ts13_revocation_public".to_string());
    names.push("ts13_revocation_range".to_string());
    names.push("coprocessor".to_string());
    names.push("mdoc_mac".to_string());
    names.push("claim_mask_anchor".to_string());
    names
}

/// Bytes a single module (or one sub-component group inside it) contributes.
///
/// Only per-column proof data is attributable to a module. Commitment roots and
/// Merkle/FRI decommitments are per-tree, not per-column, so they live in
/// [`MdocProofByteBreakdown::shared`] instead of being split here.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MdocModuleByteBreakdown {
    /// Module label, suffixed with the column log-size when a module commits
    /// several differently-sized sub-components. `mdoc_scope` splits this way
    /// into its stream trace and its DFA edge table.
    ///
    /// Sub-components that share a log size cannot be told apart from
    /// [`TreeLayout`] alone and are reported as one bucket — `mdoc_scope`'s
    /// digest-id universe shares log-size 16 with its stream trace, so those
    /// two are pooled. Splitting them further needs per-component sizes from
    /// the module itself, not just its layout.
    pub label: String,
    pub oods_sampled_values: usize,
    pub queried_values: usize,
    pub columns: usize,
}

impl MdocModuleByteBreakdown {
    pub fn total(&self) -> usize {
        self.oods_sampled_values + self.queried_values
    }
}

/// Proof bytes that exist once for the whole proof rather than per module.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct MdocSharedByteBreakdown {
    pub pcs_config: usize,
    pub commitment_roots: usize,
    pub trace_decommitments: usize,
    pub proof_of_work: usize,
    pub fri_proof: usize,
    /// Composition-tree OODS samples and queried values. The composition
    /// polynomial mixes every module, so these bytes have no single owner.
    pub composition_oods_sampled_values: usize,
    pub composition_queried_values: usize,
}

impl MdocSharedByteBreakdown {
    pub fn total(&self) -> usize {
        self.pcs_config
            + self.commitment_roots
            + self.trace_decommitments
            + self.proof_of_work
            + self.fri_proof
            + self.composition_oods_sampled_values
            + self.composition_queried_values
    }
}

/// Exact byte attribution for a serialized [`MdocCircuitProof`].
///
/// `modules`, `shared`, `coprocessor_bundle` and `framing_other` partition
/// [`Self::proof_bytes`] exactly — see [`Self::attributed_bytes`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MdocProofByteBreakdown {
    /// `bincode::serialize(proof).len()`: the raw bytes the SDK compresses into
    /// the V8 transport envelope.
    pub proof_bytes: usize,
    pub modules: Vec<MdocModuleByteBreakdown>,
    pub shared: MdocSharedByteBreakdown,
    /// The EC coprocessor bundle as one opaque blob. Its internals are broken
    /// down inside `eu-id-ec-coprocessor`, not here.
    pub coprocessor_bundle: usize,
    /// Bincode container framing plus the proof's non-STARK metadata fields
    /// (per-module interaction claims, log sizes, predicate public inputs).
    /// Derived by subtraction so nothing can go unreported.
    pub framing_other: usize,
}

impl MdocProofByteBreakdown {
    pub fn attributed_bytes(&self) -> usize {
        self.modules
            .iter()
            .map(MdocModuleByteBreakdown::total)
            .sum::<usize>()
            + self.shared.total()
            + self.coprocessor_bundle
            + self.framing_other
    }
}

fn bincode_len<T: Serialize>(value: &T) -> usize {
    bincode::serialize(value)
        .expect("mdoc proof byte breakdown value serializes")
        .len()
}

/// Split one tree's per-column byte costs across the modules that own them.
///
/// `column_owners` is the tree's column list in commit order, each entry the
/// index of the owning label. Returns the per-label totals plus the container
/// framing that belongs to no column.
fn attribute_tree_columns<T: Serialize>(
    columns: &[Vec<T>],
    column_owners: &[usize],
    label_count: usize,
) -> (Vec<usize>, usize) {
    assert_eq!(
        columns.len(),
        column_owners.len(),
        "committed column count does not match the module layout"
    );
    let mut per_label = vec![0usize; label_count];
    for (column, &owner) in columns.iter().zip(column_owners) {
        per_label[owner] += bincode_len(column);
    }
    // Every tree is a `Vec`, so it carries a length prefix of its own.
    (per_label, bincode_len(&Vec::<Vec<T>>::new()))
}

/// Byte-exact breakdown of the V8 mdoc identity proof.
///
/// Runs verification to capture the committed module shape, so a proof that
/// does not verify against `statement` returns that verification error rather
/// than a breakdown of unvalidated bytes.
pub fn mdoc_proof_byte_breakdown(
    proof: &MdocCircuitProof,
    statement: &MdocCircuitStatement,
) -> Result<MdocProofByteBreakdown, Error> {
    let mut shapes = Vec::new();
    verify_mdoc_circuit_with_pcs_config_impl(
        proof,
        statement,
        mdoc_production_pcs_config(),
        Some(&mut shapes),
    )?;

    // Label modules, splitting any module that commits several differently
    // sized sub-components into one label per contiguous same-log-size run.
    // This is what separates `mdoc_scope`'s DFA edge table and digest-id
    // universe from its main stream trace without hard-coding their widths.
    let mut labels: Vec<String> = Vec::new();
    // Per tree, the owning label index of each column in commit order.
    let mut preprocessed_owners: Vec<usize> = Vec::new();
    let mut trace_owners: Vec<usize> = Vec::new();
    let mut interaction_owners: Vec<usize> = Vec::new();
    let mut post_interaction_owners: Vec<usize> = Vec::new();
    let mut seen_preprocessed_ids: HashSet<PreProcessedColumnId> = HashSet::new();

    for shape in &shapes {
        // One label per distinct log size this module commits, so a module's
        // sub-components stay separable across all four trees.
        let mut label_of_log_size: HashMap<u32, usize> = HashMap::new();
        let mut multi_size = shape
            .layout
            .preprocessed
            .iter()
            .chain(&shape.layout.trace)
            .chain(&shape.layout.interaction)
            .chain(&shape.post_interaction)
            .collect::<Vec<_>>();
        multi_size.sort_unstable();
        multi_size.dedup();
        let names_by_log_size: HashMap<u32, String> = if multi_size.len() > 1 {
            multi_size
                .iter()
                .map(|&&log_size| (log_size, format!("{} (log_size={log_size})", shape.name)))
                .collect()
        } else {
            multi_size
                .iter()
                .map(|&&log_size| (log_size, shape.name.clone()))
                .collect()
        };
        let mut owner_of = |log_size: u32| -> usize {
            *label_of_log_size.entry(log_size).or_insert_with(|| {
                labels.push(names_by_log_size[&log_size].clone());
                labels.len() - 1
            })
        };

        // Tree 0 is deduplicated by column id, first declaring module wins.
        for (id, &log_size) in shape
            .preprocessed_ids
            .iter()
            .zip(&shape.layout.preprocessed)
        {
            if seen_preprocessed_ids.insert(id.clone()) {
                preprocessed_owners.push(owner_of(log_size));
            }
        }
        for &log_size in &shape.layout.trace {
            trace_owners.push(owner_of(log_size));
        }
        for &log_size in &shape.layout.interaction {
            interaction_owners.push(owner_of(log_size));
        }
        for &log_size in &shape.post_interaction {
            post_interaction_owners.push(owner_of(log_size));
        }
    }

    let commitment_scheme_proof = &proof.stark_proof.0;
    let sampled_values = &commitment_scheme_proof.sampled_values;
    let queried_values = &commitment_scheme_proof.queried_values;

    // Trees in commit order: preprocessed, trace, interaction, then the
    // optional post-interaction tree, then composition. Composition is always
    // last and belongs to no module.
    let mut owners_by_tree = vec![preprocessed_owners, trace_owners, interaction_owners];
    if !post_interaction_owners.is_empty() {
        owners_by_tree.push(post_interaction_owners);
    }
    if sampled_values.len() != owners_by_tree.len() + 1 {
        return Err(Error::Verify(format!(
            "mdoc proof has {} committed trees, expected {} module trees plus composition",
            sampled_values.len(),
            owners_by_tree.len()
        )));
    }

    let label_count = labels.len();
    let mut oods_per_label = vec![0usize; label_count];
    let mut queried_per_label = vec![0usize; label_count];
    let mut columns_per_label = vec![0usize; label_count];
    // Container framing: the outer `TreeVec` length prefix plus one per tree.
    let mut oods_framing = bincode_len(&Vec::<Vec<Vec<QM31>>>::new());
    let mut queried_framing = bincode_len(&Vec::<Vec<Vec<M31>>>::new());

    for (tree, owners) in owners_by_tree.iter().enumerate() {
        let (oods, framing) = attribute_tree_columns(&sampled_values[tree], owners, label_count);
        oods_framing += framing;
        let (queried, framing) = attribute_tree_columns(&queried_values[tree], owners, label_count);
        queried_framing += framing;
        for (label, bytes) in oods.into_iter().enumerate() {
            oods_per_label[label] += bytes;
        }
        for (label, bytes) in queried.into_iter().enumerate() {
            queried_per_label[label] += bytes;
        }
        for &owner in owners {
            columns_per_label[owner] += 1;
        }
    }

    let composition = owners_by_tree.len();
    let composition_oods: usize = sampled_values[composition].iter().map(bincode_len).sum();
    let composition_queried: usize = queried_values[composition].iter().map(bincode_len).sum();
    oods_framing += bincode_len(&Vec::<Vec<QM31>>::new());
    queried_framing += bincode_len(&Vec::<Vec<M31>>::new());

    // Falsifiable: the per-column attribution plus container framing must
    // reproduce the serialized field exactly.
    let oods_total: usize = oods_per_label.iter().sum::<usize>() + composition_oods + oods_framing;
    assert_eq!(
        oods_total,
        bincode_len(sampled_values),
        "OODS sampled-value attribution does not reproduce the serialized field"
    );
    let queried_total: usize =
        queried_per_label.iter().sum::<usize>() + composition_queried + queried_framing;
    assert_eq!(
        queried_total,
        bincode_len(queried_values),
        "queried-value attribution does not reproduce the serialized field"
    );

    let shared = MdocSharedByteBreakdown {
        pcs_config: bincode_len(&commitment_scheme_proof.config),
        commitment_roots: bincode_len(&commitment_scheme_proof.commitments),
        trace_decommitments: bincode_len(&commitment_scheme_proof.decommitments),
        proof_of_work: bincode_len(&commitment_scheme_proof.proof_of_work),
        fri_proof: bincode_len(&commitment_scheme_proof.fri_proof),
        composition_oods_sampled_values: composition_oods,
        composition_queried_values: composition_queried,
    };

    // Falsifiable: a bincode struct is its fields concatenated, so the seven
    // `CommitmentSchemeProof` fields must sum to the serialized `StarkProof`.
    let stark_proof_bytes = bincode_len(&proof.stark_proof);
    assert_eq!(
        shared.pcs_config
            + shared.commitment_roots
            + shared.trace_decommitments
            + shared.proof_of_work
            + shared.fri_proof
            + oods_total
            + queried_total,
        stark_proof_bytes,
        "STARK proof field attribution does not reproduce the serialized proof"
    );

    let proof_bytes = bincode_len(proof);
    let coprocessor_bundle = bincode_len(&proof.coprocessor_bundle);
    let modules: Vec<MdocModuleByteBreakdown> = labels
        .into_iter()
        .enumerate()
        .map(|(label, name)| MdocModuleByteBreakdown {
            label: name,
            oods_sampled_values: oods_per_label[label],
            queried_values: queried_per_label[label],
            columns: columns_per_label[label],
        })
        .collect();

    // Everything not attributed above: bincode container framing for the
    // sampled/queried trees plus the proof's non-STARK metadata fields.
    let attributed = modules
        .iter()
        .map(MdocModuleByteBreakdown::total)
        .sum::<usize>()
        + shared.total()
        + coprocessor_bundle;
    let framing_other = proof_bytes.checked_sub(attributed).ok_or_else(|| {
        Error::Verify(format!(
            "mdoc proof byte attribution ({attributed}) exceeds the serialized proof ({proof_bytes})"
        ))
    })?;

    Ok(MdocProofByteBreakdown {
        proof_bytes,
        modules,
        shared,
        coprocessor_bundle,
        framing_other,
    })
}

pub fn mdoc_production_pcs_config() -> PcsConfig {
    // `20 + 54 * 2` is the configured query/PoW work-factor heuristic. It is
    // not a theorem-level composed soundness bound for this QM31 proof.
    // A fold step of three reduces the proof size.
    // The verifier pins this exact configuration.
    PcsConfig {
        pow_bits: 20,
        fri_config: FriConfig::new(1, 2, 54, 3),
        lifting_log_size: None,
    }
}

#[cfg(test)]
mod mdoc_sha_table_tests {
    use super::*;
    use stwo::core::fields::FieldExpOps;

    fn value_map_mut<'a>(value: &'a mut Value, label: &str) -> &'a mut Vec<(Value, Value)> {
        let Value::Map(map) = value else {
            panic!("{label} must be a map");
        };
        map
    }

    fn value_array_mut<'a>(value: &'a mut Value, label: &str) -> &'a mut Vec<Value> {
        let Value::Array(array) = value else {
            panic!("{label} must be an array");
        };
        array
    }

    fn text_value_mut<'a>(map: &'a mut [(Value, Value)], key: &str) -> &'a mut Value {
        map.iter_mut()
            .find_map(|(candidate, value)| {
                (candidate == &Value::Text(key.to_string())).then_some(value)
            })
            .unwrap_or_else(|| panic!("missing map key {key}"))
    }

    fn issuer_auth_mut(document: &mut Value) -> &mut Vec<Value> {
        let document = value_map_mut(document, "document");
        let issuer_signed = value_map_mut(text_value_mut(document, "issuerSigned"), "issuerSigned");
        value_array_mut(text_value_mut(issuer_signed, "issuerAuth"), "issuerAuth")
    }

    fn device_signed_mut(document: &mut Value) -> &mut Vec<(Value, Value)> {
        let document = value_map_mut(document, "document");
        value_map_mut(text_value_mut(document, "deviceSigned"), "deviceSigned")
    }

    fn product_fixture_value() -> (Value, MdocPidRequest) {
        let fixture = demo_mdoc_circuit_fixture();
        (
            decode_value(&fixture.document).expect("demo document decodes"),
            fixture.request,
        )
    }

    fn issuer_namespaces_mut(document: &mut Value) -> &mut Vec<(Value, Value)> {
        let document = value_map_mut(document, "document");
        let issuer_signed = value_map_mut(text_value_mut(document, "issuerSigned"), "issuerSigned");
        value_map_mut(
            text_value_mut(issuer_signed, "nameSpaces"),
            "issuerSigned.nameSpaces",
        )
    }

    fn mutate_mso(document: &mut Value, mutate: impl FnOnce(&mut Vec<(Value, Value)>)) {
        let issuer_auth = issuer_auth_mut(document);
        let Value::Bytes(payload) = &issuer_auth[2] else {
            panic!("issuerAuth payload must be bytes");
        };
        let Value::Tag(CBOR_TAG_ENCODED_CBOR, encoded_mso) =
            decode_value(payload).expect("wrapped MSO decodes")
        else {
            panic!("fixture MSO must be wrapped");
        };
        let Value::Bytes(mso) = *encoded_mso else {
            panic!("wrapped MSO must contain bytes");
        };
        let Value::Map(mut mso) = decode_value(&mso).expect("MSO decodes") else {
            panic!("MSO must be a map");
        };
        mutate(&mut mso);
        issuer_auth[2] = Value::Bytes(encode_value(Value::Tag(
            CBOR_TAG_ENCODED_CBOR,
            Box::new(Value::Bytes(encode_value(Value::Map(mso)))),
        )));
    }

    fn resign_issuer_auth(document: &mut Value) {
        let issuer_auth = issuer_auth_mut(document);
        let Value::Bytes(protected) = &issuer_auth[0] else {
            panic!("issuerAuth protected header must be bytes");
        };
        let Value::Bytes(payload) = &issuer_auth[2] else {
            panic!("issuerAuth payload must be bytes");
        };
        let signature_input = sig_structure(protected, payload);
        let signing_key =
            SigningKey::from_bytes((&[7u8; 32]).into()).expect("demo issuer signing key");
        let signature: P256Signature = signing_key.sign(&signature_input);
        issuer_auth[3] = Value::Bytes(signature.to_bytes().to_vec());
    }

    fn mutate_selected_item(
        document: &mut Value,
        index: usize,
        mutate: impl FnOnce(&mut Vec<(Value, Value)>),
    ) {
        let namespaces = issuer_namespaces_mut(document);
        let items = value_array_mut(&mut namespaces[0].1, "PID namespace items");
        let Value::Tag(CBOR_TAG_ENCODED_CBOR, inner) = &items[index] else {
            panic!("selected item must use tag 24");
        };
        let Value::Bytes(inner) = inner.as_ref() else {
            panic!("selected item tag must contain bytes");
        };
        let Value::Map(mut item) = decode_value(inner).expect("selected item inner decodes") else {
            panic!("selected item must contain a map");
        };
        mutate(&mut item);
        items[index] = Value::Tag(
            CBOR_TAG_ENCODED_CBOR,
            Box::new(Value::Bytes(encode_value(Value::Map(item)))),
        );
    }

    fn product_mso_mutation_error(
        document: &Value,
        request: &MdocPidRequest,
        mutate: impl FnOnce(&mut Vec<(Value, Value)>),
    ) -> MdocError {
        let mut changed = document.clone();
        mutate_mso(&mut changed, mutate);
        extract_product_value(changed, request).unwrap_err()
    }

    fn extract_product_value(
        document: Value,
        request: &MdocPidRequest,
    ) -> Result<ExtractedPidMdoc, MdocError> {
        extract_product_pid_mdoc(&encode_value(document), request)
    }

    fn product_policy_on(year: u32, month: u32, day: u32) -> Policy {
        let mut policy = demo_mdoc_circuit_fixture().statement.policy;
        policy.current_date = predicates::Date { year, month, day };
        policy
    }

    fn epoch_seconds(year: i64, month: i64, day: i64, seconds_of_day: u64) -> u64 {
        u64::try_from(days_from_civil(year, month, day).expect("valid test date"))
            .expect("test date follows the Unix epoch")
            * 86_400
            + seconds_of_day
    }

    fn assert_invalid_witness_rejects(
        label: &str,
        extracted: &ExtractedPidMdoc,
        statement: &MdocCircuitStatement,
    ) {
        if let Ok(proof) = prove_mdoc_circuit(extracted, statement) {
            assert!(
                verify_mdoc_circuit(&proof, statement).is_err(),
                "{label}: invalid witness produced a verifying proof"
            );
        }
    }

    #[test]
    fn product_mdoc_structure_validation_precedes_recursive_decode() {
        let valid = encode_value(Value::Map(vec![(
            Value::Text("documents".to_string()),
            Value::Array(Vec::new()),
        )]));
        validate_product_mdoc_cbor_structure(&valid).expect("bounded CBOR structure is valid");

        for (label, bytes) in [
            ("indefinite container", vec![0x9f, 0xff]),
            ("trailing root", vec![0xf6, 0xf6]),
            ("non-minimal argument", vec![0x18, 0x01]),
        ] {
            assert!(
                matches!(
                    validate_product_mdoc_cbor_structure(&bytes),
                    Err(MdocError::Cbor(_))
                ),
                "{label} must be rejected by the structural parser"
            );
        }

        let mut too_deep = vec![0xc0; 8];
        too_deep.push(0xf6);
        assert!(matches!(
            validate_product_mdoc_cbor_structure(&too_deep),
            Err(MdocError::Cbor(message)) if message.contains("nesting exceeds 8")
        ));
    }

    #[test]
    fn current_product_rejects_item_tag_salt_digest_and_protected_header_mutations() {
        let (document, request) = product_fixture_value();

        let mut untagged = document.clone();
        let namespaces = issuer_namespaces_mut(&mut untagged);
        let items = value_array_mut(&mut namespaces[0].1, "PID namespace items");
        let Value::Tag(CBOR_TAG_ENCODED_CBOR, inner) = &items[0] else {
            panic!("selected item must use tag 24");
        };
        let Value::Bytes(inner) = inner.as_ref() else {
            panic!("selected item tag must contain bytes");
        };
        items[0] = decode_value(inner).expect("untagged selected item decodes");
        assert_eq!(
            extract_product_value(untagged, &request).unwrap_err(),
            MdocError::WrongType("IssuerSignedItemBytes")
        );

        let mut short_salt = document.clone();
        mutate_selected_item(&mut short_salt, 0, |item| {
            *text_value_mut(item, "random") = Value::Bytes(vec![7; 15]);
        });
        assert_eq!(
            extract_product_value(short_salt, &request).unwrap_err(),
            MdocError::SaltTooShort { len: 15 }
        );

        let mut digest_mismatch = document.clone();
        mutate_selected_item(&mut digest_mismatch, 0, |item| {
            *text_value_mut(item, "elementValue") = Value::Tag(
                CBOR_TAG_FULL_DATE,
                Box::new(Value::Text("1991-07-15".to_string())),
            );
        });
        assert!(matches!(
            extract_product_value(digest_mismatch, &request),
            Err(MdocError::ItemDigestMismatch {
                element,
                digest_id: 7
            }) if element == "birth_date"
        ));

        for target in ["issuer", "device"] {
            let mut bad_protected = document.clone();
            if target == "issuer" {
                issuer_auth_mut(&mut bad_protected)[0] = Value::Bytes(Vec::new());
            } else {
                let device_signed = device_signed_mut(&mut bad_protected);
                let device_auth =
                    value_map_mut(text_value_mut(device_signed, "deviceAuth"), "deviceAuth");
                let signature = value_array_mut(
                    text_value_mut(device_auth, "deviceSignature"),
                    "deviceSignature",
                );
                signature[0] = Value::Bytes(Vec::new());
            }
            assert_eq!(
                extract_product_value(bad_protected, &request).unwrap_err(),
                MdocError::InvalidCoseSign1("protected header must be ES256"),
                "{target} protected-header mutation must reject"
            );
        }
    }

    #[test]
    fn current_product_issuer_trust_requires_one_exact_leaf_pin() {
        let (document, request) = product_fixture_value();
        extract_product_value(document.clone(), &request).expect("exact leaf pin extracts");

        let mut wrong_key = request.clone();
        let other_key = SigningKey::from_bytes((&[19u8; 32]).into()).expect("other key");
        wrong_key.required_issuer_public_key = demo_affine_point(&other_key);
        assert_eq!(
            extract_product_value(document.clone(), &wrong_key).unwrap_err(),
            MdocError::UntrustedIssuerCertificate
        );

        let mut multiple = document.clone();
        let issuer_auth = issuer_auth_mut(&mut multiple);
        let unprotected = value_map_mut(&mut issuer_auth[1], "issuerAuth.unprotected");
        let certificate = unprotected[0].1.clone();
        unprotected[0].1 = Value::Array(vec![certificate.clone(), certificate]);
        assert_eq!(
            extract_product_value(multiple, &request).unwrap_err(),
            MdocError::InvalidCertificate("x5chain must contain exactly one leaf certificate")
        );

        let mut direct_key = document;
        let issuer_auth = issuer_auth_mut(&mut direct_key);
        issuer_auth[1] = Value::Map(vec![(
            "issuerKey".into(),
            demo_cose_key(&SigningKey::from_bytes((&[7u8; 32]).into()).expect("demo issuer key")),
        )]);
        assert!(matches!(
            extract_product_value(direct_key, &request),
            Err(MdocError::InvalidProductDocumentShape(
                "issuerAuth unprotected header must contain only x5chain"
            ))
        ));
    }

    #[test]
    fn current_product_binds_received_empty_device_namespaces() {
        let (document, request) = product_fixture_value();

        let mut missing = document.clone();
        device_signed_mut(&mut missing).remove(0);
        assert!(matches!(
            extract_product_value(missing, &request),
            Err(MdocError::InvalidProductDocumentShape("deviceSigned keys"))
        ));

        for replacement in [
            Value::Tag(
                CBOR_TAG_ENCODED_CBOR,
                Box::new(Value::Bytes(vec![0xB8, 0x00])),
            ),
            Value::Tag(
                CBOR_TAG_ENCODED_CBOR,
                Box::new(Value::Bytes(encode_value(Value::Map(vec![(
                    "x".into(),
                    Value::from(1),
                )])))),
            ),
            Value::Bytes(vec![0xA0]),
        ] {
            let mut changed = document.clone();
            let device_signed = device_signed_mut(&mut changed);
            *text_value_mut(device_signed, "nameSpaces") = replacement;
            assert!(matches!(
                extract_product_value(changed, &request),
                Err(MdocError::InvalidProductDocumentShape(
                    "deviceSigned.nameSpaces must be exact canonical empty DeviceNameSpacesBytes"
                ))
            ));
        }

        let mut bad_signature = document;
        let device_signed = device_signed_mut(&mut bad_signature);
        let device_auth = value_map_mut(text_value_mut(device_signed, "deviceAuth"), "deviceAuth");
        let signature = value_array_mut(
            text_value_mut(device_auth, "deviceSignature"),
            "deviceSignature",
        );
        let Value::Bytes(signature_bytes) = &mut signature[3] else {
            panic!("device signature must be bytes");
        };
        signature_bytes[0] ^= 1;
        assert_eq!(
            extract_product_value(bad_signature, &request).unwrap_err(),
            MdocError::InvalidSignature("deviceSignature")
        );

        for unprotected in [
            Value::Map(vec![("extra".into(), Value::Null)]),
            Value::Map(vec![
                ("duplicate".into(), Value::Null),
                ("duplicate".into(), Value::Null),
            ]),
        ] {
            let mut changed = product_fixture_value().0;
            let device_signed = device_signed_mut(&mut changed);
            let device_auth =
                value_map_mut(text_value_mut(device_signed, "deviceAuth"), "deviceAuth");
            let signature = value_array_mut(
                text_value_mut(device_auth, "deviceSignature"),
                "deviceSignature",
            );
            signature[1] = unprotected;
            assert!(matches!(
                extract_product_value(changed, &request),
                Err(MdocError::InvalidProductDocumentShape(
                    "deviceSignature unprotected header must be empty"
                ))
            ));
        }

        let mut embedded_payload = product_fixture_value().0;
        let device_signed = device_signed_mut(&mut embedded_payload);
        let device_auth = value_map_mut(text_value_mut(device_signed, "deviceAuth"), "deviceAuth");
        let signature = value_array_mut(
            text_value_mut(device_auth, "deviceSignature"),
            "deviceSignature",
        );
        signature[2] = Value::Bytes(
            device_authentication_bytes(&request.session_transcript, &request.doctype)
                .expect("device authentication payload"),
        );
        assert!(matches!(
            extract_product_value(embedded_payload, &request),
            Err(MdocError::InvalidProductDocumentShape(
                "deviceSignature payload must be detached"
            ))
        ));
    }

    #[test]
    fn current_product_requires_wrapped_mso() {
        let (mut document, request) = product_fixture_value();
        let issuer_auth = issuer_auth_mut(&mut document);
        let Value::Bytes(payload) = &issuer_auth[2] else {
            panic!("issuerAuth payload must be bytes");
        };
        let Value::Tag(CBOR_TAG_ENCODED_CBOR, encoded_mso) =
            decode_value(payload).expect("wrapped MSO decodes")
        else {
            panic!("fixture MSO must be wrapped");
        };
        let Value::Bytes(mso) = *encoded_mso else {
            panic!("wrapped MSO must contain bytes");
        };
        issuer_auth[2] = Value::Bytes(mso);

        assert!(matches!(
            extract_product_value(document, &request),
            Err(MdocError::InvalidProductDocumentShape(
                "issuerAuth payload must be MobileSecurityObjectBytes"
            ))
        ));
    }

    #[test]
    fn current_product_mso_accepts_iso_map_order_inside_exact_wrapper() {
        let (mut document, _) = product_fixture_value();
        let issuer_auth = issuer_auth_mut(&mut document);
        let Value::Bytes(payload) = &issuer_auth[2] else {
            panic!("issuerAuth payload must be bytes");
        };
        let Value::Tag(CBOR_TAG_ENCODED_CBOR, encoded_mso) =
            decode_value(payload).expect("wrapped MSO decodes")
        else {
            panic!("fixture MSO must be wrapped");
        };
        let Value::Bytes(mso) = *encoded_mso else {
            panic!("wrapped MSO must contain bytes");
        };
        let Value::Map(mut entries) = decode_value(&mso).expect("MSO decodes") else {
            panic!("MSO must be a map");
        };
        entries.reverse();
        let reordered = encode_value(Value::Tag(
            CBOR_TAG_ENCODED_CBOR,
            Box::new(Value::Bytes(encode_value(Value::Map(entries)))),
        ));

        validate_current_product_mso_payload(&reordered)
            .expect("ISO map order remains valid inside exact wrapper");
    }

    #[test]
    fn current_product_rejects_duplicate_or_ambiguous_mso_fields() {
        let (document, request) = product_fixture_value();

        let error = product_mso_mutation_error(&document, &request, |mso| {
            let entry = mso
                .iter()
                .find(|(key, _)| key == &Value::Text("valueDigests".to_string()))
                .expect("valueDigests entry")
                .clone();
            mso.push(entry);
        });
        assert_eq!(
            error,
            MdocError::InvalidProductDocumentShape("MobileSecurityObject keys")
        );

        let error = product_mso_mutation_error(&document, &request, |mso| {
            let value_digests = value_map_mut(text_value_mut(mso, "valueDigests"), "valueDigests");
            let digests = value_map_mut(&mut value_digests[0].1, "PID digests");
            digests.push(digests[0].clone());
        });
        assert_eq!(
            error,
            MdocError::InvalidProductDocumentShape("duplicate valueDigests digestID")
        );

        let error = product_mso_mutation_error(&document, &request, |mso| {
            let value_digests = value_map_mut(text_value_mut(mso, "valueDigests"), "valueDigests");
            let digests = value_map_mut(&mut value_digests[0].1, "PID digests");
            digests[0].0 = Value::from(u64::from(MDOC_SCOPE_MAX_DIGEST_ID) + 1);
        });
        assert_eq!(
            error,
            MdocError::InvalidProductDocumentShape("duplicate valueDigests digestID")
        );

        let error = product_mso_mutation_error(&document, &request, |mso| {
            let validity = value_map_mut(text_value_mut(mso, "validityInfo"), "validityInfo");
            validity.push(validity[0].clone());
        });
        assert_eq!(
            error,
            MdocError::InvalidProductDocumentShape("validityInfo keys")
        );

        let error = product_mso_mutation_error(&document, &request, |mso| {
            let validity = value_map_mut(text_value_mut(mso, "validityInfo"), "validityInfo");
            validity.push(("expectedUpdate".into(), Value::Null));
        });
        assert_eq!(
            error,
            MdocError::InvalidTdate("validityInfo.expectedUpdate")
        );

        let error = product_mso_mutation_error(&document, &request, |mso| {
            let device_key_info =
                value_map_mut(text_value_mut(mso, "deviceKeyInfo"), "deviceKeyInfo");
            device_key_info.push(device_key_info[0].clone());
        });
        assert_eq!(
            error,
            MdocError::InvalidProductDocumentShape("deviceKeyInfo keys")
        );

        let error = product_mso_mutation_error(&document, &request, |mso| {
            let device_key_info =
                value_map_mut(text_value_mut(mso, "deviceKeyInfo"), "deviceKeyInfo");
            let device_key =
                value_map_mut(text_value_mut(device_key_info, "deviceKey"), "deviceKey");
            device_key.push(device_key[0].clone());
        });
        assert_eq!(
            error,
            MdocError::InvalidProductDocumentShape("deviceKey COSE_Key labels")
        );
    }

    #[test]
    fn current_product_rejects_missing_or_invalid_mso_security_fields() {
        let (document, request) = product_fixture_value();

        let missing_validity = product_mso_mutation_error(&document, &request, |mso| {
            mso.retain(|(key, _)| key != &Value::Text("validityInfo".to_string()));
        });
        assert_eq!(
            missing_validity,
            MdocError::InvalidProductDocumentShape("MobileSecurityObject keys")
        );

        for (label, field, value, expected) in [
            (
                "version",
                "version",
                Value::Text("1.0".to_string()),
                MdocError::UnsupportedMsoVersion("1.0".to_string()),
            ),
            (
                "docType",
                "docType",
                Value::Text("wrong.doctype".to_string()),
                MdocError::DoctypeMismatch,
            ),
            (
                "digest algorithm",
                "digestAlgorithm",
                Value::Text("SHA-384".to_string()),
                MdocError::UnsupportedDigestAlgorithm("SHA-384".to_string()),
            ),
        ] {
            let mut changed = document.clone();
            mutate_mso(&mut changed, |mso| *text_value_mut(mso, field) = value);
            resign_issuer_auth(&mut changed);
            assert_eq!(
                extract_product_value(changed, &request).unwrap_err(),
                expected,
                "{label} mutation must reject"
            );
        }

        let mut malformed_validity = document;
        mutate_mso(&mut malformed_validity, |mso| {
            let validity = value_map_mut(text_value_mut(mso, "validityInfo"), "validityInfo");
            *text_value_mut(validity, "validFrom") =
                Value::Tag(0, Box::new(Value::Text("2026-02-30T00:00:00Z".to_string())));
        });
        resign_issuer_auth(&mut malformed_validity);
        assert_eq!(
            extract_product_value(malformed_validity, &request).unwrap_err(),
            MdocError::InvalidTdate("validityInfo.validFrom")
        );
    }

    #[test]
    fn current_product_requires_unique_pid_namespace_and_selected_items() {
        let (document, request) = product_fixture_value();

        for insert_first in [true, false] {
            let mut duplicate_namespace = document.clone();
            let namespaces = issuer_namespaces_mut(&mut duplicate_namespace);
            let entry = namespaces[0].clone();
            if insert_first {
                namespaces.insert(0, entry);
            } else {
                namespaces.push(entry);
            }
            assert!(matches!(
                extract_product_value(duplicate_namespace, &request),
                Err(MdocError::InvalidProductDocumentShape(
                    "issuerSigned.nameSpaces must contain exactly one PID namespace"
                ))
            ));

            let mut duplicate_item = document.clone();
            let namespaces = issuer_namespaces_mut(&mut duplicate_item);
            let items = value_array_mut(&mut namespaces[0].1, "PID namespace items");
            let item = items[0].clone();
            if insert_first {
                items.insert(0, item);
            } else {
                items.push(item);
            }
            assert!(matches!(
                extract_product_value(duplicate_item, &request),
                Err(MdocError::InvalidProductDocumentShape(
                    "each requested PID element must occur exactly once"
                ))
            ));
        }

        let mut oversized_digest_id = document;
        mutate_selected_item(&mut oversized_digest_id, 0, |item| {
            *text_value_mut(item, "digestID") =
                Value::from(u64::from(MDOC_SCOPE_MAX_DIGEST_ID) + 1);
        });
        assert!(matches!(
            extract_product_value(oversized_digest_id, &request),
            Err(MdocError::InvalidProductDocumentShape(
                "requested PID digestID exceeds product bound"
            ))
        ));
    }

    #[test]
    fn current_product_rejects_duplicate_and_ambiguous_outer_fields() {
        let (document, request) = product_fixture_value();

        for insert_first in [true, false] {
            let mut duplicate = document.clone();
            let map = value_map_mut(&mut duplicate, "document");
            let entry = map
                .iter()
                .find(|(key, _)| key == &Value::Text("docType".to_string()))
                .expect("docType entry")
                .clone();
            if insert_first {
                map.insert(0, entry);
            } else {
                map.push(entry);
            }
            assert!(matches!(
                extract_product_value(duplicate, &request),
                Err(MdocError::InvalidProductDocumentShape(
                    "product document keys"
                ))
            ));

            let mut duplicate = document.clone();
            let document_map = value_map_mut(&mut duplicate, "document");
            let issuer_signed =
                value_map_mut(text_value_mut(document_map, "issuerSigned"), "issuerSigned");
            let entry = issuer_signed
                .iter()
                .find(|(key, _)| key == &Value::Text("issuerAuth".to_string()))
                .expect("issuerAuth entry")
                .clone();
            if insert_first {
                issuer_signed.insert(0, entry);
            } else {
                issuer_signed.push(entry);
            }
            assert!(matches!(
                extract_product_value(duplicate, &request),
                Err(MdocError::InvalidProductDocumentShape("issuerSigned keys"))
            ));

            let mut duplicate = document.clone();
            let device_signed = device_signed_mut(&mut duplicate);
            let entry = device_signed
                .iter()
                .find(|(key, _)| key == &Value::Text("deviceAuth".to_string()))
                .expect("deviceAuth entry")
                .clone();
            if insert_first {
                device_signed.insert(0, entry);
            } else {
                device_signed.push(entry);
            }
            assert!(matches!(
                extract_product_value(duplicate, &request),
                Err(MdocError::InvalidProductDocumentShape("deviceSigned keys"))
            ));

            let mut duplicate = document.clone();
            let device_signed = device_signed_mut(&mut duplicate);
            let device_auth =
                value_map_mut(text_value_mut(device_signed, "deviceAuth"), "deviceAuth");
            let entry = device_auth[0].clone();
            if insert_first {
                device_auth.insert(0, entry);
            } else {
                device_auth.push(entry);
            }
            assert!(matches!(
                extract_product_value(duplicate, &request),
                Err(MdocError::InvalidProductDocumentShape("deviceAuth keys"))
            ));
        }

        for insert_first in [true, false] {
            let mut duplicate = document.clone();
            let issuer_auth = issuer_auth_mut(&mut duplicate);
            let unprotected = value_map_mut(&mut issuer_auth[1], "issuerAuth.unprotected");
            let entry = unprotected[0].clone();
            if insert_first {
                unprotected.insert(0, entry);
            } else {
                unprotected.push(entry);
            }
            assert!(matches!(
                extract_product_value(duplicate, &request),
                Err(MdocError::InvalidProductDocumentShape(
                    "issuerAuth unprotected header must contain only x5chain"
                ))
            ));
        }

        for extra_key in ["deviceMac", "unknown"] {
            let mut ambiguous = document.clone();
            let device_signed = device_signed_mut(&mut ambiguous);
            let device_auth =
                value_map_mut(text_value_mut(device_signed, "deviceAuth"), "deviceAuth");
            device_auth.push((extra_key.into(), Value::Null));
            assert!(matches!(
                extract_product_value(ambiguous, &request),
                Err(MdocError::InvalidProductDocumentShape("deviceAuth keys"))
            ));
        }
    }

    #[test]
    fn product_attribute_scope_is_exact_and_canonical() {
        let age = MdocRequestedAttribute {
            element_identifier: "birth_date".to_string(),
            mode: MdocDisclosureMode::AgeOver,
        };
        let nationality = MdocRequestedAttribute {
            element_identifier: "nationality".to_string(),
            mode: MdocDisclosureMode::Alpha2Set,
        };
        validate_product_requested_attributes(std::slice::from_ref(&age)).unwrap();
        validate_product_requested_attributes(std::slice::from_ref(&nationality)).unwrap();
        validate_product_requested_attributes(&[age.clone(), nationality.clone()]).unwrap();

        for attributes in [
            Vec::new(),
            vec![nationality.clone(), age.clone()],
            vec![MdocRequestedAttribute {
                element_identifier: "issue_date".to_string(),
                mode: MdocDisclosureMode::AgeOver,
            }],
            vec![MdocRequestedAttribute {
                element_identifier: "birth_date".to_string(),
                mode: MdocDisclosureMode::Alpha2Set,
            }],
            vec![age.clone(), age.clone()],
            vec![age.clone(), nationality.clone(), nationality],
        ] {
            assert!(validate_product_requested_attributes(&attributes).is_err());
        }
    }

    #[test]
    fn product_circuit_semantics_bind_scope_and_predicate_indices_exactly() {
        let mut current = demo_mdoc_circuit_fixture().statement;
        current.request_binding = [0x51; 32];
        assert!(current_product_circuit_semantics(&current));

        let mut mutations = Vec::new();
        let mut zero_binding = current.clone();
        zero_binding.request_binding = [0; 32];
        mutations.push(("zero request binding", zero_binding));
        let mut wrong_doctype = current.clone();
        wrong_doctype.doctype.push_str(".other");
        mutations.push(("wrong doctype", wrong_doctype));
        let mut wrong_namespace = current.clone();
        wrong_namespace.namespace.push_str(".other");
        mutations.push(("wrong namespace", wrong_namespace));
        let mut wrong_element = current.clone();
        wrong_element.attributes[0].element_identifier = "issue_date".to_string();
        mutations.push(("predicate on wrong element", wrong_element));
        let mut reordered = current.clone();
        reordered.attributes.swap(0, 1);
        reordered.age_attribute_index = Some(1);
        reordered.nationality_attribute_index = Some(0);
        mutations.push(("noncanonical attribute order", reordered));

        for (label, age_index, nationality_index) in [
            ("missing age index", None, Some(1)),
            ("age index points at nationality", Some(1), Some(1)),
            ("age index is out of range", Some(2), Some(1)),
            ("missing nationality index", Some(0), None),
            ("nationality index points at age", Some(0), Some(0)),
            ("nationality index is out of range", Some(0), Some(2)),
        ] {
            let mut statement = current.clone();
            statement.age_attribute_index = age_index;
            statement.nationality_attribute_index = nationality_index;
            mutations.push((label, statement));
        }

        for (label, statement) in mutations {
            assert!(
                !current_product_circuit_semantics(&statement),
                "{label} unexpectedly passed the product gate"
            );
        }
    }

    #[test]
    fn product_public_semantics_bind_current_pid_scope() {
        let mut circuit = demo_mdoc_circuit_fixture().statement;
        circuit.request_binding = [0x51; 32];
        let current = MdocPublicStatement::from_circuit(&circuit);
        assert!(current_product_public_semantics(&current));

        let day_start = u64::try_from(days_from_civil(2026, 7, 3).unwrap()).unwrap() * 86_400;
        let mut same_day = current.clone();
        same_day.verification_time_epoch_seconds = day_start + 17 * 3_600 + 42;
        assert!(current_product_public_semantics(&same_day));

        let mut end_of_day = current.clone();
        end_of_day.verification_time_epoch_seconds = day_start + 86_399;
        assert!(current_product_public_semantics(&end_of_day));
        end_of_day.verification_time_epoch_seconds += 1;
        assert!(!current_product_public_semantics(&end_of_day));

        let mut zero_binding = current.clone();
        zero_binding.request_binding = [0; 32];
        assert!(!current_product_public_semantics(&zero_binding));

        for accepted_nationalities in [
            vec![*b"ZZ"],
            vec![*b"QU"],
            vec![*b"DE", *b"DE"],
            vec![*b"FR", *b"DE"],
        ] {
            let mut invalid_policy = current.clone();
            invalid_policy.policy.accepted_nationalities = accepted_nationalities;
            assert!(!current_product_public_semantics(&invalid_policy));
        }

        let mut mismatched_date = current.clone();
        mismatched_date.policy.current_date.day += 1;
        assert!(!current_product_public_semantics(&mismatched_date));

        let mut wrong_element = current;
        wrong_element.attributes[0].element_identifier = "issue_date".to_string();
        assert!(!current_product_public_semantics(&wrong_element));
    }

    #[test]
    fn device_authentication_rejects_trailing_session_transcript_bytes() {
        let mut transcript = openid4vp_session_transcript(b"request-context");
        transcript.push(0);
        assert!(matches!(
            device_authentication_bytes(&transcript, PID_DOCTYPE),
            Err(MdocError::Cbor(message)) if message.contains("trailing bytes")
        ));
    }

    #[test]
    fn product_cbor_canonicalizer_recurses_and_rejects_duplicate_map_keys() {
        let nested_map = Value::Array(vec![Value::Tag(
            1000,
            Box::new(Value::Map(vec![
                (Value::Text("long".to_string()), Value::from(1)),
                (Value::Text("x".to_string()), Value::from(2)),
            ])),
        )]);
        let reordered = encode_value(nested_map.clone());
        let canonical =
            encode_value(canonicalize_product_cbor_value(nested_map).expect("canonical map"));
        assert_ne!(reordered, canonical, "nested map order must be normalized");
        assert_eq!(
            canonicalize_product_cbor_value(Value::Map(vec![
                (Value::from(0), Value::from(1)),
                (Value::from(0), Value::from(2)),
            ])),
            Err(MdocError::NonCanonicalSessionTranscript),
            "duplicate canonical map keys must be rejected"
        );
    }

    #[test]
    fn product_session_transcript_requires_recursive_deterministic_cbor() {
        let canonical = openid4vp_session_transcript(b"request-context");
        validate_product_session_transcript_cbor(&canonical).unwrap();

        for bytes in [vec![0; 55], vec![0; 57], vec![0; 16 * 1024]] {
            assert_eq!(
                validate_product_session_transcript_cbor(&bytes),
                Err(MdocError::InvalidProductDocumentShape(
                    "SessionTranscript must be exactly 56 canonical bytes",
                ))
            );
        }

        for (label, bytes) in [
            ("indefinite array", vec![0x9f, 0x00, 0xff]),
            ("non-shortest integer", vec![0x81, 0x18, 0x00]),
        ] {
            assert!(
                validate_product_session_transcript_cbor(&bytes).is_err(),
                "{label} must be rejected by the bounded structural parser"
            );
        }
        assert!(
            validate_product_session_transcript_cbor(&[0x81, 0xa2, 0x00, 0x01, 0x00, 0x02])
                .is_err(),
            "a map-bearing non-OpenID4VP transcript must be rejected"
        );

        for (label, bytes) in [
            ("f16", vec![0x81, 0xf9, 0x3e, 0x00]),
            ("f32", vec![0x81, 0xfa, 0x3f, 0xc0, 0x00, 0x00]),
            (
                "f64",
                vec![0x81, 0xfb, 0x3f, 0xf8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
            ),
            ("NaN", vec![0x81, 0xf9, 0x7e, 0x00]),
        ] {
            assert!(
                validate_product_session_transcript_cbor(&bytes).is_err(),
                "product SessionTranscript {label} must be rejected by the bounded structural parser"
            );
        }

        let nested_map = Value::Array(vec![Value::Tag(
            1000,
            Box::new(Value::Map(vec![
                (Value::Text("long".to_string()), Value::from(1)),
                (Value::Text("x".to_string()), Value::from(2)),
            ])),
        )]);
        let reordered = encode_value(nested_map.clone());
        assert!(
            validate_product_session_transcript_cbor(&reordered).is_err(),
            "a non-OpenID4VP nested transcript must be rejected"
        );
        let canonical_nested =
            encode_value(canonicalize_product_cbor_value(nested_map).expect("canonical map"));
        assert!(
            validate_product_session_transcript_cbor(&canonical_nested).is_err(),
            "canonical CBOR alone is insufficient without the exact OpenID4VP shape"
        );

        for (label, value) in [
            (
                "short outer array",
                Value::Array(vec![Value::Null, Value::Null]),
            ),
            (
                "long outer array",
                Value::Array(vec![Value::Null, Value::Null, Value::Null, Value::Null]),
            ),
            (
                "wrong null",
                Value::Array(vec![
                    Value::from(0),
                    Value::Null,
                    Value::Array(vec!["OpenID4VPHandover".into(), Value::Bytes(vec![0; 32])]),
                ]),
            ),
            (
                "wrong second null",
                Value::Array(vec![
                    Value::Null,
                    Value::from(0),
                    Value::Array(vec!["OpenID4VPHandover".into(), Value::Bytes(vec![0; 32])]),
                ]),
            ),
            (
                "wrong handover type",
                Value::Array(vec![Value::Null, Value::Null, Value::Null]),
            ),
            (
                "short handover array",
                Value::Array(vec![
                    Value::Null,
                    Value::Null,
                    Value::Array(vec!["OpenID4VPHandover".into()]),
                ]),
            ),
            (
                "long handover array",
                Value::Array(vec![
                    Value::Null,
                    Value::Null,
                    Value::Array(vec![
                        "OpenID4VPHandover".into(),
                        Value::Bytes(vec![0; 32]),
                        Value::Null,
                    ]),
                ]),
            ),
            (
                "wrong handover label",
                Value::Array(vec![
                    Value::Null,
                    Value::Null,
                    Value::Array(vec!["OtherHandover".into(), Value::Bytes(vec![0; 32])]),
                ]),
            ),
            (
                "wrong handover hash type",
                Value::Array(vec![
                    Value::Null,
                    Value::Null,
                    Value::Array(vec!["OpenID4VPHandover".into(), Value::Text("x".into())]),
                ]),
            ),
            (
                "short handover hash",
                Value::Array(vec![
                    Value::Null,
                    Value::Null,
                    Value::Array(vec!["OpenID4VPHandover".into(), Value::Bytes(vec![0; 31])]),
                ]),
            ),
            (
                "long handover hash",
                Value::Array(vec![
                    Value::Null,
                    Value::Null,
                    Value::Array(vec!["OpenID4VPHandover".into(), Value::Bytes(vec![0; 33])]),
                ]),
            ),
        ] {
            assert!(
                matches!(
                    validate_product_session_transcript_cbor(&encode_value(value)),
                    Err(MdocError::InvalidProductDocumentShape(_))
                ),
                "{label} must be rejected by the exact OpenID4VP shape gate"
            );
        }

        let mut trailing = canonical;
        trailing.push(0);
        assert_eq!(
            validate_product_session_transcript_cbor(&trailing),
            Err(MdocError::InvalidProductDocumentShape(
                "SessionTranscript must be exactly 56 canonical bytes",
            ))
        );

        let mut too_deep = vec![0x81; 8];
        too_deep.push(0xf6);
        assert_eq!(
            validate_product_session_transcript_cbor(&too_deep),
            Err(MdocError::InvalidProductDocumentShape(
                "SessionTranscript must be exactly 56 canonical bytes",
            ))
        );
    }

    #[test]
    fn product_sha_input_size_boundaries_are_exact() {
        let accepted_item = vec![0; crate::product_profile::PRODUCT_MAX_SELECTED_ITEM_BYTES];
        validate_product_sha_input_sizes(&[], &[], &[&accepted_item]).unwrap();
        assert_eq!(
            validate_product_sha_input_sizes(
                &[],
                &[],
                &[&vec![
                    0;
                    crate::product_profile::PRODUCT_MAX_SELECTED_ITEM_BYTES
                        + 1
                ]],
            ),
            Err(MdocError::InputTooLarge {
                input: "selected IssuerSignedItem",
                actual: crate::product_profile::PRODUCT_MAX_SELECTED_ITEM_BYTES + 1,
                maximum: crate::product_profile::PRODUCT_MAX_SELECTED_ITEM_BYTES,
            })
        );

        let accepted_mso = vec![0; crate::product_profile::PRODUCT_MAX_MSO_PAYLOAD_BYTES];
        validate_product_sha_input_sizes(&accepted_mso, &[], &[]).unwrap();
        assert_eq!(
            validate_product_sha_input_sizes(
                &vec![0; crate::product_profile::PRODUCT_MAX_MSO_PAYLOAD_BYTES + 1],
                &[],
                &[],
            ),
            Err(MdocError::InputTooLarge {
                input: "MSO payload",
                actual: crate::product_profile::PRODUCT_MAX_MSO_PAYLOAD_BYTES + 1,
                maximum: crate::product_profile::PRODUCT_MAX_MSO_PAYLOAD_BYTES,
            })
        );

        let accepted_issuer =
            vec![0; crate::product_profile::PRODUCT_MAX_ISSUER_SIG_STRUCTURE_BYTES];
        validate_product_sha_input_sizes(&accepted_mso, &accepted_issuer, &[]).unwrap();
        assert_eq!(
            validate_product_sha_input_sizes(
                &accepted_mso,
                &vec![0; crate::product_profile::PRODUCT_MAX_ISSUER_SIG_STRUCTURE_BYTES + 1],
                &[],
            ),
            Err(MdocError::InputTooLarge {
                input: "issuer Sig_structure",
                actual: crate::product_profile::PRODUCT_MAX_ISSUER_SIG_STRUCTURE_BYTES + 1,
                maximum: crate::product_profile::PRODUCT_MAX_ISSUER_SIG_STRUCTURE_BYTES,
            })
        );
        assert_eq!(
            validate_product_sha_input_sizes(&[], &[], &[&accepted_item, &accepted_item, &[]]),
            Err(MdocError::InvalidAttributeCount { count: 3 })
        );
    }

    #[test]
    fn sig_structure_overhead_stays_within_product_bound() {
        for payload_len in [0, 23, 24, 255, 256, 6_144] {
            let payload = vec![0; payload_len];
            let structure = sig_structure(ES256_PROTECTED_HEADER, &payload);
            assert!(structure.len() - payload.len() <= 20);
            if payload_len == 6_144 {
                assert_eq!(structure.len() - payload.len(), 20);
            }
        }
        let fixture = demo_mdoc_circuit_fixture();
        assert!(fixture.extracted.mso.len() >= 256);
        assert_eq!(
            fixture.extracted.issuer_sig_structure.len() - fixture.extracted.mso.len(),
            20
        );
    }

    #[test]
    fn maximum_nationality_item_fits_selected_item_profile() {
        let value = Value::Array((0..256).map(|_| Value::Text("DE".to_string())).collect());
        let item = demo_issuer_signed_item(9, "nationality", value, vec![9; 16]);
        assert!(item.len() <= crate::product_profile::PRODUCT_MAX_SELECTED_ITEM_BYTES);
    }

    #[test]
    fn tdate_parser_enforces_gregorian_calendar_boundaries() {
        let parse = |text: &str| {
            parse_tdate(
                &Value::Tag(0, Box::new(Value::Text(text.to_string()))),
                "test.tdate",
            )
        };
        for valid in [
            "2000-02-29T00:00:00Z",
            "2004-02-29T23:59:59Z",
            "2024-04-30T00:00:00Z",
        ] {
            assert!(parse(valid).is_ok(), "valid tdate rejected: {valid}");
        }
        for invalid in [
            "1900-02-29T00:00:00Z",
            "2023-02-29T00:00:00Z",
            "2024-02-30T00:00:00Z",
            "2024-04-31T00:00:00Z",
            "2100-02-29T00:00:00Z",
        ] {
            assert_eq!(
                parse(invalid),
                Err(MdocError::InvalidTdate("test.tdate")),
                "invalid tdate accepted: {invalid}"
            );
        }
        assert_eq!(
            days_from_civil(2024, 4, 31),
            Err(MdocError::InvalidVerificationTime),
            "public verification dates must use the same calendar rule"
        );
    }

    #[test]
    fn statement_uses_exact_verifier_seconds_for_validity_boundaries() {
        let fixture = demo_mdoc_circuit_fixture();
        let valid_from = epoch_seconds(2026, 1, 1, 0);
        let valid_until = epoch_seconds(2030, 1, 1, 0);

        assert_eq!(
            MdocCircuitStatement::from_extracted_at(
                &fixture.extracted,
                product_policy_on(2026, 1, 1),
                valid_from,
            )
            .unwrap_err(),
            MdocError::CredentialNotYetValid
        );
        MdocCircuitStatement::from_extracted_at(
            &fixture.extracted,
            product_policy_on(2026, 1, 1),
            valid_from + 1,
        )
        .expect("one second after validFrom is valid");

        MdocCircuitStatement::from_extracted_at(
            &fixture.extracted,
            product_policy_on(2029, 12, 31),
            valid_until - 1,
        )
        .expect("one second before validUntil is valid");
        assert_eq!(
            MdocCircuitStatement::from_extracted_at(
                &fixture.extracted,
                product_policy_on(2030, 1, 1),
                valid_until,
            )
            .unwrap_err(),
            MdocError::CredentialExpired
        );
    }

    #[test]
    fn prover_rejects_invalid_verifier_timestamps_without_panicking() {
        let fixture = demo_mdoc_circuit_fixture();
        for timestamp in [0, 253_402_300_799, u64::MAX] {
            let mut statement = fixture.statement.clone();
            statement.verification_time_epoch_seconds = timestamp;
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                prove_mdoc_circuit(&fixture.extracted, &statement)
            }));
            assert!(result.is_ok(), "timestamp {timestamp} panicked");
            assert!(
                matches!(result.unwrap(), Err(Error::Prove(message)) if message == "invalid verifier timestamp"),
                "timestamp {timestamp} must reject before evaluator construction"
            );
        }
    }

    #[test]
    #[ignore = "slow: proves age and validity guard-bypass witnesses"]
    fn proof_rejects_underage_and_out_of_window_guard_bypasses() {
        let fixture = demo_mdoc_circuit_fixture();

        let mut underage = fixture.extracted.clone();
        underage.birth_date_bytes = [0x07, 0xDA, 7, 15]; // 2010-07-15.
        let underage_statement = MdocCircuitStatement::from_extracted_at(
            &underage,
            fixture.statement.policy.clone(),
            fixture.statement.verification_time_epoch_seconds,
        )
        .expect("private age result remains a proof relation");
        assert_invalid_witness_rejects("underage birth date", &underage, &underage_statement);

        for (label, timestamp, policy) in [
            (
                "timestamp equals validFrom",
                epoch_seconds(2026, 1, 1, 0),
                product_policy_on(2026, 1, 1),
            ),
            (
                "timestamp equals validUntil",
                epoch_seconds(2030, 1, 1, 0),
                product_policy_on(2030, 1, 1),
            ),
        ] {
            let mut statement = fixture.statement.clone();
            statement.verification_time_epoch_seconds = timestamp;
            statement.policy = policy;
            assert_invalid_witness_rejects(label, &fixture.extracted, &statement);
        }
    }

    fn test_claim_mask(log_size: u32) -> (ClaimMaskTrace, QM31) {
        let mut ring = ClaimMaskRing::new(&[log_size, log_size]).unwrap();
        let mask = ring.take(log_size).unwrap();
        let shared = SharedClaimMaskChallenge::new();
        let mut anchor =
            ClaimMaskChallengeModule::new(shared.clone(), vec![log_size, log_size]).unwrap();
        let mut channel = Blake2sChannel::default();
        anchor.mix_public(&mut channel);
        anchor.draw_relations(&mut channel);
        (mask, shared.require().unwrap())
    }

    fn field_lookup_sum(relation: &FieldBytesRelation, field_id: u32, bytes: &[u8]) -> QM31 {
        bytes.iter().enumerate().fold(
            QM31::from_u32_unchecked(0, 0, 0, 0),
            |sum, (index, &byte)| {
                let denominator: QM31 = relation.combine(&[
                    M31::from_u32_unchecked(field_id),
                    M31::from_u32_unchecked(index as u32),
                    M31::from_u32_unchecked(u32::from(byte)),
                ]);
                sum + denominator.inverse()
            },
        )
    }

    #[test]
    fn exact_sha_claim_mask_delta_is_beta_times_target() {
        let bytes = b"exact private SHA message";
        let mut channel = Blake2sChannel::default();
        let source_relation = FieldBytesRelation::draw(&mut channel);
        let sha_relation = FieldBytesRelation::draw(&mut channel);
        let (mask, beta) = test_claim_mask(exact_sha_message_log_size(bytes.len()));
        let (_, unmasked) = exact_sha_message_interaction_trace(
            bytes,
            MDOC_MSO_PAYLOAD_FIELD_ID,
            PACKED_SHA_STREAM_FIELD_BASE + PACKED_SHA_MSO_SLOT,
            1,
            &source_relation,
            &sha_relation,
            None,
        );
        let (_, masked) = exact_sha_message_interaction_trace(
            bytes,
            MDOC_MSO_PAYLOAD_FIELD_ID,
            PACKED_SHA_STREAM_FIELD_BASE + PACKED_SHA_MSO_SLOT,
            1,
            &source_relation,
            &sha_relation,
            Some((&mask, beta)),
        );

        assert_eq!(masked - unmasked, beta * mask.target_sum());
    }

    #[test]
    fn revocation_range_claim_mask_delta_is_beta_times_target() {
        let witness = MdocRevocationRangeWitness {
            id: 20,
            id_lo: 10,
            id_hi: 30,
        };
        let mut mso_digest = [0x5a; 32];
        mso_digest[..REVOCATION_U64_BYTES].copy_from_slice(&witness.id.to_le_bytes());
        let mut channel = Blake2sChannel::default();
        let digest_relation = PackedShaDigestRelation::draw(&mut channel);
        let message_relation = FieldBytesRelation::draw(&mut channel);
        let (mask, beta) = test_claim_mask(MDOC_REVOCATION_RANGE_LOG_SIZE);
        let (_, unmasked) = revocation_range_interaction_trace(
            &witness,
            &mso_digest,
            &digest_relation,
            42,
            &message_relation,
            None,
        );
        let (_, masked) = revocation_range_interaction_trace(
            &witness,
            &mso_digest,
            &digest_relation,
            42,
            &message_relation,
            Some((&mask, beta)),
        );

        assert_eq!(masked - unmasked, beta * mask.target_sum());
    }

    #[test]
    fn exact_sha_padding_covers_boundary_lengths() {
        for (len, expected_padded_len) in [(55, 64), (56, 128), (63, 128), (64, 128)] {
            let message = vec![0x42; len];
            let padded = stwo_sha256::native::pad_message(&message);
            assert_eq!(exact_sha_padded_len(len), expected_padded_len);
            assert_eq!(padded.len(), expected_padded_len);
            for row in len..expected_padded_len {
                assert_eq!(
                    exact_sha_padding_byte(len, row, expected_padded_len),
                    padded[row],
                    "wrong canonical SHA padding byte for len={len}, row={row}",
                );
            }
        }
    }

    #[test]
    fn exact_sha_bridge_rejects_mso_and_revocation_suffix_extensions_algebraically() {
        let mut channel = Blake2sChannel::default();
        let source_relation = FieldBytesRelation::draw(&mut channel);
        let sha_relation = FieldBytesRelation::draw(&mut channel);
        let zero = QM31::from_u32_unchecked(0, 0, 0, 0);

        let mso_payload = b"\xa1\x67version\x63" as &[u8];
        let mso_padded = stwo_sha256::native::pad_message(mso_payload);
        let (_, mso_bridge) = exact_sha_message_interaction_trace(
            mso_payload,
            MDOC_MSO_PAYLOAD_FIELD_ID,
            PACKED_SHA_STREAM_FIELD_BASE + PACKED_SHA_MSO_SLOT,
            1,
            &source_relation,
            &sha_relation,
            None,
        );
        let mso_total = mso_bridge
            - field_lookup_sum(&source_relation, MDOC_MSO_PAYLOAD_FIELD_ID, mso_payload)
            - field_lookup_sum(
                &sha_relation,
                PACKED_SHA_STREAM_FIELD_BASE + PACKED_SHA_MSO_SLOT,
                &mso_padded,
            );
        assert_eq!(mso_total, zero);

        let mut extended_mso = mso_payload.to_vec();
        extended_mso.push(0);
        let extended_mso_padded = stwo_sha256::native::pad_message(&extended_mso);
        let extended_mso_total = mso_bridge
            - field_lookup_sum(&source_relation, MDOC_MSO_PAYLOAD_FIELD_ID, mso_payload)
            - field_lookup_sum(
                &sha_relation,
                PACKED_SHA_STREAM_FIELD_BASE + PACKED_SHA_MSO_SLOT,
                &extended_mso_padded,
            );
        assert_ne!(extended_mso_total, zero);

        let revocation_message = [0x5a; TS13_REVOCATION_MESSAGE_LEN];
        let revocation_padded = stwo_sha256::native::pad_message(&revocation_message);
        let (_, revocation_bridge) = exact_sha_message_interaction_trace(
            &revocation_message,
            MDOC_REVOCATION_MESSAGE_FIELD_ID,
            PACKED_SHA_STREAM_FIELD_BASE + PACKED_SHA_REVOCATION_SLOT,
            -1,
            &source_relation,
            &sha_relation,
            None,
        );
        let revocation_total = revocation_bridge
            + field_lookup_sum(
                &source_relation,
                MDOC_REVOCATION_MESSAGE_FIELD_ID,
                &revocation_message,
            )
            - field_lookup_sum(
                &sha_relation,
                PACKED_SHA_STREAM_FIELD_BASE + PACKED_SHA_REVOCATION_SLOT,
                &revocation_padded,
            );
        assert_eq!(revocation_total, zero);

        let mut extended_revocation = revocation_message.to_vec();
        extended_revocation.push(0);
        let extended_revocation_padded = stwo_sha256::native::pad_message(&extended_revocation);
        let extended_revocation_total = revocation_bridge
            + field_lookup_sum(
                &source_relation,
                MDOC_REVOCATION_MESSAGE_FIELD_ID,
                &revocation_message,
            )
            - field_lookup_sum(
                &sha_relation,
                PACKED_SHA_STREAM_FIELD_BASE + PACKED_SHA_REVOCATION_SLOT,
                &extended_revocation_padded,
            );
        assert_ne!(extended_revocation_total, zero);
    }

    #[test]
    fn product_fixed_shape_rejects_downward_log_mutations() {
        const SHA: u32 = crate::product_profile::PRODUCT_SHA_LOG_N_ROWS;
        const CBOR: u32 = crate::product_profile::PRODUCT_MAX_CBOR_LOG_SIZE;
        const SCOPE: u32 = crate::product_profile::PRODUCT_MAX_SCOPE_LOG_SIZE;

        validate_product_fixed_shape_logs(SHA, [CBOR, CBOR], SCOPE).unwrap();
        for (sha, cbor, scope, label) in [
            (SHA - 1, [CBOR, CBOR], SCOPE, "SHA"),
            (SHA, [CBOR - 1, CBOR], SCOPE, "CBOR"),
            (SHA, [CBOR, CBOR], SCOPE - 1, "scope"),
        ] {
            assert!(
                matches!(
                    validate_product_fixed_shape_logs(sha, cbor, scope),
                    Err(Error::Verify(message))
                        if message == "mdoc proof shape does not match the fixed product profile"
                ),
                "downward {label} mutation must fail the exact product-profile gate"
            );
        }
    }

    fn sha_claimed_sums(claim: &Sha256InteractionClaim) -> Vec<QM31> {
        std::iter::once(claim.sha256.claimed_sum)
            .chain(claim.range.iter().map(|component| component.claimed_sum))
            .collect()
    }

    fn assert_all_claims_fresh(name: &str, first: &[QM31], second: &[QM31]) {
        assert_eq!(first.len(), second.len(), "{name} claim-count drift");
        assert!(
            first
                .iter()
                .zip(second)
                .all(|(first, second)| first != second),
            "{name} contains a deterministic published private claim"
        );
    }

    /// Same-witness proofs must randomize every private claimed sum while both
    /// proofs remain valid. The mask traces and their private target sums are
    /// committed inside the STARK. None are serialized as proof metadata.
    #[test]
    #[ignore = "slow: proves product mdoc circuit profile twice"]
    fn mdoc_private_claim_masks_are_fresh_and_not_serialized() {
        let fixture = demo_mdoc_circuit_fixture();
        let mut statement = fixture.statement.clone();
        statement.request_binding = [0x51; 32];
        let proof_a = prove_mdoc_circuit(&fixture.extracted, &statement).expect("proof A proves");
        let proof_b = prove_mdoc_circuit(&fixture.extracted, &statement).expect("proof B proves");
        verify_mdoc_circuit(&proof_a, &statement).expect("proof A verifies");
        verify_mdoc_circuit(&proof_b, &statement).expect("proof B verifies");

        assert_all_claims_fresh(
            "shared SHA tables",
            &proof_a.sha_tables_interaction_claim.claimed_sums(),
            &proof_b.sha_tables_interaction_claim.claimed_sums(),
        );
        assert_all_claims_fresh(
            "packed SHA",
            &sha_claimed_sums(&proof_a.packed_sha_interaction_claim),
            &sha_claimed_sums(&proof_b.packed_sha_interaction_claim),
        );
        for (index, (first, second)) in proof_a
            .mdoc_cbor_interaction_claims
            .iter()
            .zip(&proof_b.mdoc_cbor_interaction_claims)
            .enumerate()
        {
            assert_ne!(
                first.claimed_sum, second.claimed_sum,
                "mdoc parser {index} published a deterministic private claim"
            );
        }
        assert_ne!(
            proof_a.mdoc_scope_interaction_claim.claimed_sum,
            proof_b.mdoc_scope_interaction_claim.claimed_sum,
            "mdoc scope published a deterministic private claim"
        );
        assert_ne!(
            proof_a.mso_exact_cbor_interaction_claim.claimed_sum,
            proof_b.mso_exact_cbor_interaction_claim.claimed_sum,
            "exact-MSO parser published a deterministic private claim"
        );
        assert_ne!(
            proof_a.mdoc_validity_interaction_claim.claimed_sum,
            proof_b.mdoc_validity_interaction_claim.claimed_sum,
            "mdoc validity published a deterministic private claim"
        );
        assert_ne!(
            proof_a
                .revocation_message_bind_interaction_claim
                .claimed_sum,
            proof_b
                .revocation_message_bind_interaction_claim
                .claimed_sum,
        );
        assert_ne!(
            proof_a.ts13_revocation_range_interaction_claim.claimed_sum,
            proof_b.ts13_revocation_range_interaction_claim.claimed_sum,
        );
        assert_all_claims_fresh(
            "age",
            proof_a
                .age_claimed_sums
                .as_ref()
                .expect("product age claim"),
            proof_b
                .age_claimed_sums
                .as_ref()
                .expect("product age claim"),
        );
        assert_all_claims_fresh(
            "nationality",
            proof_a
                .nat_claimed_sums
                .as_ref()
                .expect("product nationality claim"),
            proof_b
                .nat_claimed_sums
                .as_ref()
                .expect("product nationality claim"),
        );

        assert_all_claims_fresh(
            "mdoc MAC",
            &[
                proof_a.mdoc_mac_interaction_claim.consumer,
                proof_a.mdoc_mac_interaction_claim.binding,
            ],
            &[
                proof_b.mdoc_mac_interaction_claim.consumer,
                proof_b.mdoc_mac_interaction_claim.binding,
            ],
        );

        let first_bundle = &proof_a.coprocessor_bundle;
        let second_bundle = &proof_b.coprocessor_bundle;
        assert_eq!(first_bundle.mac_tags.len(), second_bundle.mac_tags.len());
        assert_ne!(
            first_bundle.mac_tags, second_bundle.mac_tags,
            "same-witness mdoc proofs reused MAC tags"
        );
        for tag in &first_bundle.mac_tags {
            assert!(
                !second_bundle.mac_tags.contains(tag),
                "same-witness mdoc proofs shared MAC tag {tag:?}"
            );
        }
        assert_ne!(
            first_bundle.root, second_bundle.root,
            "same-witness mdoc proofs reused group-A Ligero root"
        );
        assert_ne!(
            first_bundle.root_b, second_bundle.root_b,
            "same-witness mdoc proofs reused group-B Ligero root"
        );

        let serialized = serde_json::to_string(&proof_a).expect("proof serializes");
        assert!(
            !serialized.contains("blinder") && !serialized.contains("claim_mask"),
            "claim-mask secrets must not be serialized as proof metadata"
        );
        assert_ne!(
            bincode::serialize(&proof_a).expect("proof A serializes"),
            bincode::serialize(&proof_b).expect("proof B serializes"),
            "same-witness product proofs must not serialize identically"
        );
    }

    /// The byte breakdown must partition the serialized proof exactly.
    ///
    /// This is the accounting gate: bytes that cannot be attributed to a module
    /// or a shared bucket have to surface in `framing_other`, never vanish. The
    /// breakdown also asserts internally that its per-column attribution
    /// reproduces each serialized field, so a wrong column-to-module map fails
    /// here rather than silently mislabelling bytes.
    #[test]
    #[ignore = "slow: proves the product metadata and statement matrix once"]
    fn current_product_proof_metadata_and_statement_matrix() {
        const PROVER_STACK_SIZE: usize = 32 * 1024 * 1024;
        std::thread::Builder::new()
            .stack_size(PROVER_STACK_SIZE)
            .spawn(current_product_proof_metadata_and_statement_matrix_body)
            .expect("spawns a prover-sized thread")
            .join()
            .expect("product metadata matrix thread does not panic");
    }

    fn current_product_proof_metadata_and_statement_matrix_body() {
        let fixture = demo_mdoc_circuit_fixture();
        let proof =
            prove_mdoc_circuit(&fixture.extracted, &fixture.statement).expect("mdoc proves");
        verify_mdoc_circuit(&proof, &fixture.statement).expect("mdoc verifies");
        let breakdown = mdoc_proof_byte_breakdown(&proof, &fixture.statement)
            .expect("byte breakdown for a verifying proof");

        assert_eq!(
            breakdown.proof_bytes,
            bincode::serialize(&proof).expect("proof serializes").len(),
            "breakdown total is not the raw serialized proof length",
        );
        assert_eq!(
            breakdown.attributed_bytes(),
            breakdown.proof_bytes,
            "byte buckets do not partition the serialized proof",
        );
        assert!(
            breakdown.coprocessor_bundle > 0,
            "coprocessor bundle bucket is empty",
        );
        for module in &breakdown.modules {
            assert!(
                module.columns > 0,
                "module bucket '{}' owns no committed column",
                module.label,
            );
        }
        // Modules the product profile always commits columns for. The
        // coprocessor is absent by design: it commits no STARK column, its data
        // is the opaque bundle asserted above.
        for expected in ["packed_sha", "mdoc_cbor_stream[0]", "mdoc_validity"] {
            assert!(
                breakdown
                    .modules
                    .iter()
                    .any(|module| module.label == expected),
                "breakdown is missing module bucket '{expected}'",
            );
        }
        // `mdoc_scope` commits its DFA edge table at its own log size, so scope
        // must appear as several log-size-suffixed buckets.
        assert!(
            breakdown
                .modules
                .iter()
                .filter(|module| module.label.starts_with("mdoc_scope"))
                .count()
                > 1,
            "mdoc_scope sub-components were not separated",
        );

        for stale in [
            PcsConfig {
                pow_bits: 20,
                fri_config: FriConfig::new(1, 2, 54, 2),
                lifting_log_size: None,
            },
            PcsConfig {
                pow_bits: 10,
                fri_config: FriConfig::new(1, 2, 59, 2),
                lifting_log_size: None,
            },
        ] {
            let mut stale_proof = proof.clone();
            stale_proof.stark_proof.0.config = stale;
            assert!(matches!(
                verify_mdoc_circuit_with_pcs_config(
                    &stale_proof,
                    &fixture.statement,
                    mdoc_production_pcs_config(),
                ),
                Err(Error::WeakConfig { .. })
            ));
        }

        let mut split_tamper = proof.clone();
        let shift = QM31::from_u32_unchecked(1, 0, 0, 0);
        split_tamper.mdoc_scope_interaction_claim.claimed_sum += shift;
        split_tamper.mdoc_validity_interaction_claim.claimed_sum -= shift;
        assert!(
            verify_mdoc_circuit(&split_tamper, &fixture.statement).is_err(),
            "balanced cross-component claimed-sum tamper unexpectedly verified",
        );

        let mut extra_table_claim = proof.clone();
        extra_table_claim
            .sha_tables_interaction_claim
            .pairs
            .push(extra_table_claim.sha_tables_interaction_claim.pairs[0].clone());
        assert!(
            verify_mdoc_circuit(&extra_table_claim, &fixture.statement).is_err(),
            "unbound fourth shared-table claim unexpectedly verified",
        );

        let mut extra_sha_claim = proof.clone();
        extra_sha_claim.packed_sha_interaction_claim.range.push(
            stwo_sha256::interaction::ComponentClaim {
                claimed_sum: QM31::from_u32_unchecked(0, 0, 0, 0),
            },
        );
        assert!(
            verify_mdoc_circuit(&extra_sha_claim, &fixture.statement).is_err(),
            "unbound shared-SHA range claim unexpectedly verified",
        );

        let mut extra_age_claim = proof.clone();
        extra_age_claim
            .age_claimed_sums
            .as_mut()
            .expect("demo statement has age predicate")
            .push(QM31::from_u32_unchecked(0, 0, 0, 0));
        assert!(
            verify_mdoc_circuit(&extra_age_claim, &fixture.statement).is_err(),
            "unbound seventh age claim unexpectedly verified",
        );

        let mut extra_nat_claim = proof.clone();
        extra_nat_claim
            .nat_claimed_sums
            .as_mut()
            .expect("demo statement has nationality predicate")
            .push(QM31::from_u32_unchecked(0, 0, 0, 0));
        assert!(
            verify_mdoc_circuit(&extra_nat_claim, &fixture.statement).is_err(),
            "unbound third nationality claim unexpectedly verified",
        );

        let mut tampered_root = proof.clone();
        tampered_root.stark_proof.0.commitments[0].0[0] ^= 1;
        assert!(matches!(
            verify_mdoc_circuit(&tampered_root, &fixture.statement),
            Err(Error::PreprocessedRootMismatch { .. })
        ));

        let mut shared_claim = proof.clone();
        shared_claim.sha_tables_interaction_claim.pairs[0].claimed_sum =
            -shared_claim.sha_tables_interaction_claim.pairs[0].claimed_sum;
        assert!(
            verify_mdoc_circuit(&shared_claim, &fixture.statement).is_err(),
            "tampered shared SHA table provider claim unexpectedly verified",
        );

        let mut request_binding = fixture.statement.clone();
        request_binding.request_binding[0] ^= 1;
        assert!(verify_mdoc_circuit(&proof, &request_binding).is_err());
        let mut doctype = fixture.statement.clone();
        doctype.doctype.push_str(".other");
        assert!(verify_mdoc_circuit(&proof, &doctype).is_err());
        let mut namespace = fixture.statement.clone();
        namespace.namespace.push_str(".other");
        assert!(verify_mdoc_circuit(&proof, &namespace).is_err());
        let mut element_identifier = fixture.statement.clone();
        element_identifier.attributes[0]
            .element_identifier
            .push_str("_other");
        assert!(verify_mdoc_circuit(&proof, &element_identifier).is_err());
        let mut mode = fixture.statement.clone();
        mode.attributes[0].mode = MdocDisclosureMode::Alpha2Set;
        assert!(verify_mdoc_circuit(&proof, &mode).is_err());

        let mut malformed_claim = proof.clone();
        malformed_claim.sha_tables_interaction_claim.pairs.clear();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            verify_mdoc_circuit(&malformed_claim, &fixture.statement)
        }));
        assert!(
            matches!(result, Ok(Err(Error::Verify(_)))),
            "malformed shared SHA table claim should reject gracefully, got {result:?}",
        );
    }

    #[test]
    fn product_sha_message_order_and_terminal_digests_are_exact() {
        let cases = [
            vec![MdocRequestedAttribute {
                element_identifier: "birth_date".to_string(),
                mode: MdocDisclosureMode::AgeOver,
            }],
            vec![MdocRequestedAttribute {
                element_identifier: "nationality".to_string(),
                mode: MdocDisclosureMode::Alpha2Set,
            }],
            vec![
                MdocRequestedAttribute {
                    element_identifier: "birth_date".to_string(),
                    mode: MdocDisclosureMode::AgeOver,
                },
                MdocRequestedAttribute {
                    element_identifier: "nationality".to_string(),
                    mode: MdocDisclosureMode::Alpha2Set,
                },
            ],
        ];

        for attributes in cases {
            let expected_message_count = if attributes.len() == 2 { 5 } else { 4 };
            let fixture = demo_mdoc_circuit_fixture_with_attributes(attributes);
            let revocation_message = ts13_revocation_message_bytes(
                fixture.statement.ts13_revocation_range.id_lo,
                fixture.statement.ts13_revocation_range.id_hi,
                fixture.statement.ts13_revocation.epoch,
            );
            let messages = product_sha_messages(&fixture.extracted, &revocation_message)
                .expect("product messages fit the fixed profile");
            let witness = compute_packed_sha256_witness(&messages).expect("packed witness");
            let trace = stwo_sha256::trace::generate_trace(
                &witness,
                crate::product_profile::PRODUCT_SHA_LOG_N_ROWS,
            );
            let mut next_block = 0usize;
            for (message_id, message) in messages.iter().enumerate() {
                let block_count = stwo_sha256::native::n_blocks_for(message.len());
                next_block += block_count;
                let terminal_block = next_block - 1;
                let terminal_slot = stwo_sha256::trace::Layout::row_slot(
                    terminal_block * stwo_sha256::trace::ROWS_PER_BLOCK + 63,
                    crate::product_profile::PRODUCT_SHA_LOG_N_ROWS,
                );
                assert_eq!(
                    trace[stwo_sha256::trace::Layout::COL_MSG_ID][terminal_slot].0,
                    message_id as u32
                );
                let actual: Vec<u8> = (0..32)
                    .map(|index| {
                        trace[stwo_sha256::trace::Layout::digest_byte(index)][terminal_slot].0 as u8
                    })
                    .collect();
                let expected = Sha256::digest(message);
                assert_eq!(actual.as_slice(), &expected[..]);
            }
            assert_eq!(messages.len(), expected_message_count);
        }
    }
}

#[cfg(test)]
mod coprocessor_tests {
    use super::*;
    use crate::Error;

    #[derive(Debug, PartialEq, Eq)]
    struct TestCoprocessorDigests {
        post_statement: [u8; 32],
        post_seed: [u8; 32],
        post_rejoin: [u8; 32],
    }

    fn unlinkability_fixture(birth_date: &str, nationalities: &[&str]) -> DemoMdocCircuitFixture {
        let attributes = vec![
            MdocRequestedAttribute {
                element_identifier: "birth_date".to_string(),
                mode: MdocDisclosureMode::AgeOver,
            },
            MdocRequestedAttribute {
                element_identifier: "nationality".to_string(),
                mode: MdocDisclosureMode::Alpha2Set,
            },
        ];
        let session_transcript = openid4vp_session_transcript(b"unlinkability-session");
        let document =
            demo_mdoc_document_with_values(&session_transcript, birth_date, nationalities);
        let (revocation, revocation_witness) =
            crate::ts13::demo_ts13_revocation_inputs(&document.mso_payload);
        let request = MdocPidRequest {
            request_binding: DEMO_REQUEST_BINDING,
            doctype: PID_DOCTYPE.to_string(),
            namespace: PID_NAMESPACE.to_string(),
            attributes,
            session_transcript,
            required_issuer_public_key: document.issuer_key.clone(),
            verification_time_epoch_seconds: DEMO_VERIFICATION_TIME_EPOCH_SECONDS,
            revocation: MdocRevocationRequest {
                public_inputs: (&revocation).into(),
                id_lo: revocation_witness.id_lo,
                id_hi: revocation_witness.id_hi,
                signature: revocation_witness.signature,
            },
        };
        let extracted = extract_product_pid_mdoc(&document.bytes, &request)
            .expect("unlinkability fixture extracts");
        let statement = MdocCircuitStatement::from_extracted_at(
            &extracted,
            Policy {
                current_date: predicates::Date {
                    year: 2026,
                    month: 7,
                    day: 3,
                },
                min_age_years: 18,
                accepted_nationalities: vec![*b"DE", *b"FR"],
            },
            DEMO_VERIFICATION_TIME_EPOCH_SECONDS,
        )
        .expect("unlinkability statement builds");
        DemoMdocCircuitFixture {
            document: document.bytes,
            request,
            extracted,
            statement,
        }
    }

    fn assert_verify_rejects(
        label: &str,
        proof: &MdocCircuitProof,
        statement: &MdocCircuitStatement,
    ) {
        assert!(
            verify_mdoc_circuit(proof, statement).is_err(),
            "{label} unexpectedly verified"
        );
    }

    fn sign_revocation_range(statement: &mut MdocCircuitStatement, id_lo: u64, id_hi: u64) {
        let signing_key =
            SigningKey::from_bytes((&[23u8; 32]).into()).expect("revocation signing key");
        let message = ts13_revocation_message_bytes(id_lo, id_hi, statement.ts13_revocation.epoch);
        let signature: P256Signature = signing_key.sign(&message);
        statement.ts13_revocation.revocation_public_key = demo_affine_point(&signing_key);
        statement.ts13_revocation_range.id_lo = id_lo;
        statement.ts13_revocation_range.id_hi = id_hi;
        let signature_bytes: [u8; 64] = signature.to_bytes().into();
        statement.ts13_revocation_signature =
            signature_from_compact(&signature_bytes).expect("compact revocation signature");
    }

    fn assert_prove_or_verify_rejects(
        label: &str,
        extracted: &ExtractedPidMdoc,
        statement: &MdocCircuitStatement,
    ) {
        if let Ok(proof) = prove_mdoc_circuit(extracted, statement) {
            assert_verify_rejects(label, &proof, statement);
        }
    }

    fn tampered_bundle(
        bundle: &eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle,
    ) -> eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle {
        let original_hash = crate::coprocessor_bundle_hash(bundle).expect("bundle hashes");
        let mut bytes = bincode::serialize(bundle).expect("bundle serializes");
        for index in (0..bytes.len()).rev() {
            bytes[index] ^= 1;
            if let Ok(candidate) = bincode::deserialize(&bytes) {
                if crate::coprocessor_bundle_hash(&candidate).expect("candidate hashes")
                    != original_hash
                {
                    return candidate;
                }
            }
            bytes[index] ^= 1;
        }
        panic!("one serialized bundle byte can be tampered");
    }

    fn mdoc_coprocessor_digests(
        issuer_tag: &'static [u8],
        issuer_input: &EcdsaVerifyInput,
        device_tag: &'static [u8],
        device_input: &EcdsaVerifyInput,
        bundle: &eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle,
    ) -> TestCoprocessorDigests {
        let mut channel = air_core::Ch::default();
        let issuer_projection =
            crate::ec_coprocessor::issuer_key_projection_from_stwo(issuer_input);
        let device_projection =
            crate::ec_coprocessor::message_hash_projection_from_stwo(device_input);
        crate::mix_coprocessor_tagged_projections(
            &mut channel,
            &[
                (issuer_tag, &issuer_projection),
                (device_tag, &device_projection),
            ],
        )
        .expect("mdoc tagged projections mix");
        let post_statement = crate::channel_digest(&channel);
        let post_seed = crate::draw_coprocessor_seed(&mut channel);
        crate::mix_coprocessor_rejoin(&mut channel, bundle).expect("mdoc rejoin mixes");
        let post_rejoin = crate::channel_digest(&channel);
        TestCoprocessorDigests {
            post_statement,
            post_seed,
            post_rejoin,
        }
    }

    #[test]
    #[ignore = "slow: proves product mdoc circuit with coprocessor bundle"]
    fn mdoc_coprocessor_rejects_required_negative_mutations() {
        let fixture = demo_mdoc_circuit_fixture();
        let statement = fixture.statement;
        let proof = prove_mdoc_circuit(&fixture.extracted, &statement).expect("mdoc proves");
        verify_mdoc_circuit(&proof, &statement).expect("mdoc verifies");

        let public_statement = MdocPublicStatement::from_circuit(&statement);
        verify_product_mdoc_public_statement(&proof, &public_statement)
            .expect("reduced public statement verifies");
        let mut wrong_issuer_key = public_statement.clone();
        wrong_issuer_key.issuer_public_key.x.0[0] ^= 1;
        assert!(
            verify_product_mdoc_public_statement(&proof, &wrong_issuer_key).is_err(),
            "issuer public key mutation unexpectedly verified"
        );
        let mut wrong_device_z = public_statement.clone();
        wrong_device_z.device_message_hash.0[0] ^= 1;
        assert!(
            verify_product_mdoc_public_statement(&proof, &wrong_device_z).is_err(),
            "device z mutation unexpectedly verified"
        );
        let mut wrong_policy_date = public_statement.clone();
        wrong_policy_date.policy.current_date.day += 1;
        assert!(
            verify_product_mdoc_public_statement(&proof, &wrong_policy_date).is_err(),
            "policy date mutation unexpectedly verified"
        );

        let mut tampered = proof.clone();
        tampered.coprocessor_bundle = tampered_bundle(&proof.coprocessor_bundle);
        assert_verify_rejects(
            "serialized coprocessor bundle tamper",
            &tampered,
            &statement,
        );

        let mut mac_tag_tamper = proof.clone();
        mac_tag_tamper.coprocessor_bundle.mac_tags[0][0] ^= 1;
        assert_verify_rejects("MAC tag tamper", &mac_tag_tamper, &statement);

        let mut mac_claim_tamper = proof.clone();
        mac_claim_tamper.mdoc_mac_interaction_claim.binding += QM31::from_u32_unchecked(1, 0, 0, 0);
        assert_verify_rejects("MAC binding claim tamper", &mac_claim_tamper, &statement);

        let mut mac_consumer_claim_tamper = proof.clone();
        mac_consumer_claim_tamper
            .mdoc_mac_interaction_claim
            .consumer += QM31::from_u32_unchecked(1, 0, 0, 0);
        assert_verify_rejects(
            "MAC consumer claim tamper",
            &mac_consumer_claim_tamper,
            &statement,
        );

        let mut device_z_mismatch = statement.clone();
        device_z_mismatch.device_input.message_hash.0[0] ^= 1;
        assert_verify_rejects("device z mismatch", &proof, &device_z_mismatch);

        let mut cross_slot_z = statement.clone();
        std::mem::swap(
            &mut cross_slot_z.issuer_input.message_hash,
            &mut cross_slot_z.device_input.message_hash,
        );
        assert_verify_rejects("cross-slot z swap", &proof, &cross_slot_z);

        let mut cross_signature = statement.clone();
        std::mem::swap(
            &mut cross_signature.issuer_input,
            &mut cross_signature.device_input,
        );
        assert_verify_rejects("cross-signature swap", &proof, &cross_signature);

        let bundle = &proof.coprocessor_bundle;
        let canonical = mdoc_coprocessor_digests(
            b"issuer",
            &statement.issuer_input,
            b"device",
            &statement.device_input,
            bundle,
        );
        let swapped_statement_order = mdoc_coprocessor_digests(
            b"device",
            &statement.device_input,
            b"issuer",
            &statement.issuer_input,
            bundle,
        );
        assert_ne!(canonical, swapped_statement_order);

        let tampered_rejoin = mdoc_coprocessor_digests(
            b"issuer",
            &statement.issuer_input,
            b"device",
            &statement.device_input,
            &tampered_bundle(bundle),
        );
        assert_ne!(canonical.post_rejoin, tampered_rejoin.post_rejoin);

        let issuer_projection =
            crate::ec_coprocessor::issuer_key_projection_from_stwo(&statement.issuer_input);
        let device_projection =
            crate::ec_coprocessor::message_hash_projection_from_stwo(&statement.device_input);
        let mut without_rejoin = air_core::Ch::default();
        crate::mix_coprocessor_tagged_projections(
            &mut without_rejoin,
            &[
                (b"issuer".as_slice(), &issuer_projection),
                (b"device".as_slice(), &device_projection),
            ],
        )
        .expect("mdoc tagged projections mix");
        let _seed = crate::draw_coprocessor_seed(&mut without_rejoin);
        let without_rejoin_next = crate::draw_coprocessor_seed(&mut without_rejoin);

        let mut with_rejoin = air_core::Ch::default();
        crate::mix_coprocessor_tagged_projections(
            &mut with_rejoin,
            &[
                (b"issuer".as_slice(), &issuer_projection),
                (b"device".as_slice(), &device_projection),
            ],
        )
        .expect("mdoc tagged projections mix");
        let _seed = crate::draw_coprocessor_seed(&mut with_rejoin);
        crate::mix_coprocessor_rejoin(&mut with_rejoin, bundle).expect("mdoc rejoin mixes");
        let with_rejoin_next = crate::draw_coprocessor_seed(&mut with_rejoin);
        assert_ne!(with_rejoin_next, without_rejoin_next);
    }

    /// Distinct valid private credentials reconstruct the same caller-owned
    /// public statement and fixed proof shape. This is the current
    /// public-input unlinkability gate. Transparent STWO transcript-wide zero
    /// knowledge remains future work and is not asserted here.
    #[test]
    #[ignore = "slow: proves two distinct credentials for public-input unlinkability"]
    fn distinct_credentials_share_only_the_caller_authoritative_statement() {
        let first_fixture = unlinkability_fixture("1990-07-15", &["DE"]);
        let second_fixture = unlinkability_fixture("1985-05-05", &["FR", "BE", "CY"]);
        let first_public = MdocPublicStatement::from_circuit(&first_fixture.statement);
        let second_public = MdocPublicStatement::from_circuit(&second_fixture.statement);
        assert_eq!(
            first_public, second_public,
            "private credential values changed the caller-authoritative statement"
        );
        assert_eq!(
            bincode::serialize(&first_public).expect("first public statement serializes"),
            bincode::serialize(&second_public).expect("second public statement serializes"),
            "caller-authoritative statement bytes differ"
        );
        assert_eq!(
            first_fixture.request.session_transcript,
            second_fixture.request.session_transcript
        );
        assert_eq!(
            first_fixture.request.required_issuer_public_key,
            second_fixture.request.required_issuer_public_key
        );
        assert_eq!(
            first_fixture.request.request_binding,
            second_fixture.request.request_binding
        );
        assert_ne!(
            first_fixture.extracted.nationality_item.len(),
            second_fixture.extracted.nationality_item.len(),
            "unlinkability fixtures must have different private item lengths"
        );

        let public_json =
            serde_json::to_string(&first_public).expect("public statement serializes");
        for canary in ["1990-07-15", "1985-05-05"] {
            assert!(
                !public_json.contains(canary),
                "private birth-date canary leaked into the public statement"
            );
        }

        let first = prove_mdoc_circuit(&first_fixture.extracted, &first_fixture.statement)
            .expect("first distinct credential proves");
        let second = prove_mdoc_circuit(&second_fixture.extracted, &second_fixture.statement)
            .expect("second distinct credential proves");
        verify_product_mdoc_public_statement(&first, &first_public)
            .expect("first distinct credential verifies");
        verify_product_mdoc_public_statement(&second, &second_public)
            .expect("second distinct credential verifies");

        assert_eq!(
            first.packed_sha_interaction_claim.range.len(),
            second.packed_sha_interaction_claim.range.len()
        );
        assert_eq!(first.mdoc_cbor_log_sizes, second.mdoc_cbor_log_sizes);
        assert_eq!(
            first.mdoc_scope_metadata.log_size,
            second.mdoc_scope_metadata.log_size
        );

        let mut first_shapes = Vec::new();
        let mut second_shapes = Vec::new();
        verify_mdoc_circuit_with_pcs_config_impl(
            &first,
            &first_fixture.statement,
            mdoc_production_pcs_config(),
            Some(&mut first_shapes),
        )
        .expect("first shape capture verifies");
        verify_mdoc_circuit_with_pcs_config_impl(
            &second,
            &second_fixture.statement,
            mdoc_production_pcs_config(),
            Some(&mut second_shapes),
        )
        .expect("second shape capture verifies");
        let first_packed = first_shapes
            .iter()
            .find(|shape| shape.name == "packed_sha")
            .expect("first packed SHA shape");
        let second_packed = second_shapes
            .iter()
            .find(|shape| shape.name == "packed_sha")
            .expect("second packed SHA shape");
        assert_eq!(
            first_packed.layout.preprocessed,
            second_packed.layout.preprocessed
        );
        assert_eq!(first_packed.layout.trace, second_packed.layout.trace);
        assert_eq!(
            first_packed.layout.interaction,
            second_packed.layout.interaction
        );
        assert_eq!(
            first_packed.post_interaction,
            second_packed.post_interaction
        );
        for log_sizes in [
            &first_packed.layout.preprocessed,
            &first_packed.layout.trace,
            &first_packed.layout.interaction,
            &first_packed.post_interaction,
        ] {
            assert!(log_sizes
                .iter()
                .all(|&log_size| log_size == crate::product_profile::PRODUCT_SHA_LOG_N_ROWS));
        }

        assert_ne!(
            bincode::serialize(&first).expect("first proof serializes"),
            bincode::serialize(&second).expect("second proof serializes"),
            "distinct private credentials produced identical proof bytes"
        );
        assert_ne!(
            first.coprocessor_bundle.mac_tags, second.coprocessor_bundle.mac_tags,
            "distinct private credentials reused P4b MAC tags"
        );
    }

    #[test]
    fn public_statement_exposes_only_caller_authoritative_revocation_inputs() {
        let statement = demo_mdoc_circuit_fixture().statement;
        let public = MdocPublicStatement::from_circuit(&statement);

        assert_eq!(public.ts13_revocation, statement.ts13_revocation);
        let serialized = serde_json::to_value(&public).expect("public statement serializes");
        let object = serialized
            .as_object()
            .expect("public statement is an object");
        for private_name in [
            "ts13_revocation_range",
            "ts13_revocation_signature",
            "id",
            "id_lo",
            "id_hi",
            "signature",
        ] {
            assert!(
                !object.contains_key(private_name),
                "private revocation field {private_name} leaked into the public statement"
            );
        }
    }

    #[test]
    #[ignore = "slow: proves the mandatory revocation boundary and signature matrix"]
    fn mandatory_revocation_boundary_and_signature_matrix() {
        let fixture = demo_mdoc_circuit_fixture();
        let id = fixture.statement.ts13_revocation_range.id;
        assert!(
            (1..u64::MAX).contains(&id),
            "demo MSO revocation id must have both adjacent boundaries"
        );

        let mut sentinel = fixture.statement.clone();
        sign_revocation_range(&mut sentinel, 0, u64::MAX);
        let proof = prove_mdoc_circuit(&fixture.extracted, &sentinel)
            .expect("sentinel non-revocation range proves");
        verify_mdoc_circuit(&proof, &sentinel).expect("sentinel non-revocation range verifies");

        let invalid_ranges = [
            ("id equals lower bound", id, id + 1),
            ("id equals upper bound", id - 1, id),
            ("reversed bounds", id + 1, id - 1),
            ("wrapped bounds", u64::MAX, 0),
        ];
        for (label, id_lo, id_hi) in invalid_ranges {
            let mut statement = fixture.statement.clone();
            sign_revocation_range(&mut statement, id_lo, id_hi);
            assert_prove_or_verify_rejects(label, &fixture.extracted, &statement);
        }

        let mut wrong_derived_id = fixture.statement.clone();
        wrong_derived_id.ts13_revocation_range.id ^= 1;
        sign_revocation_range(
            &mut wrong_derived_id,
            fixture.statement.ts13_revocation_range.id_lo,
            fixture.statement.ts13_revocation_range.id_hi,
        );
        assert_prove_or_verify_rejects(
            "revocation id is not derived from the signed MSO",
            &fixture.extracted,
            &wrong_derived_id,
        );

        let mut wrong_mso_preimage = fixture.extracted.clone();
        let valid_until = find_subslice(&wrong_mso_preimage.mso, b"2030-01-01T00:00:00Z")
            .expect("demo MSO contains validUntil");
        wrong_mso_preimage.mso[valid_until] = b'4';
        assert_prove_or_verify_rejects(
            "revocation MSO preimage is not the signed issuer payload",
            &wrong_mso_preimage,
            &fixture.statement,
        );

        let mut forged_signature = fixture.statement.clone();
        forged_signature.ts13_revocation_signature.r.0[0] ^= 1;
        assert!(
            prove_mdoc_circuit(&fixture.extracted, &forged_signature).is_err(),
            "forged revocation signature unexpectedly proved"
        );

        let honest = prove_mdoc_circuit(&fixture.extracted, &fixture.statement)
            .expect("honest revocation proof");
        let mut wrong_epoch = fixture.statement.clone();
        wrong_epoch.ts13_revocation.epoch = wrong_epoch.ts13_revocation.epoch.wrapping_add(1);
        assert_verify_rejects(
            "caller-authoritative revocation epoch",
            &honest,
            &wrong_epoch,
        );
        let mut wrong_key = fixture.statement.clone();
        wrong_key.ts13_revocation.revocation_public_key.x.0[0] ^= 1;
        assert_verify_rejects("caller-authoritative revocation key", &honest, &wrong_key);
    }

    #[test]
    #[ignore = "slow: proves the fixed product shape before downward metadata mutations"]
    fn product_real_proof_rejects_downward_shape_mutations() {
        let fixture = demo_mdoc_circuit_fixture();
        let mut statement = fixture.statement.clone();
        statement.request_binding = [0x51; 32];
        let proof =
            prove_mdoc_circuit(&fixture.extracted, &statement).expect("product mdoc proves");
        verify_mdoc_circuit(&proof, &statement).expect("honest fixed-shape product proof verifies");

        for (label, age_index, nationality_index) in [
            ("missing age index", None, Some(1)),
            ("age index points at nationality", Some(1), Some(1)),
            ("age index is out of range", Some(2), Some(1)),
            ("missing nationality index", Some(0), None),
            ("nationality index points at age", Some(0), Some(0)),
            ("nationality index is out of range", Some(0), Some(2)),
        ] {
            let mut tampered = statement.clone();
            tampered.age_attribute_index = age_index;
            tampered.nationality_attribute_index = nationality_index;
            assert!(
                matches!(
                    verify_mdoc_circuit(&proof, &tampered),
                    Err(Error::Verify(message))
                        if message.contains("text-date/alpha-2 predicate attributes")
                ),
                "{label} must reject at the product semantic gate"
            );
        }

        let mut sha = proof.clone();
        sha.packed_sha_interaction_claim.sha256.claimed_sum += QM31::from_u32_unchecked(1, 0, 0, 0);
        assert!(
            verify_mdoc_circuit(&sha, &statement).is_err(),
            "tampered product SHA interaction claim unexpectedly verified"
        );

        let mut cbor = proof.clone();
        cbor.mdoc_cbor_log_sizes[0] -= 1;
        assert!(
            verify_mdoc_circuit(&cbor, &statement).is_err(),
            "downward product CBOR log unexpectedly verified"
        );

        let mut scope = proof.clone();
        scope.mdoc_scope_metadata.log_size -= 1;
        assert!(
            verify_mdoc_circuit(&scope, &statement).is_err(),
            "downward product scope log unexpectedly verified"
        );

        let revocation_input = ts13_revocation_p256_input(&statement);
        let encoded = bincode::serialize(&proof).expect("revocation proof serializes");
        for (label, secret) in [
            (
                "revocation message hash",
                revocation_input.message_hash.0.as_slice(),
            ),
            (
                "revocation signature r",
                revocation_input.signature.r.0.as_slice(),
            ),
            (
                "revocation signature s",
                revocation_input.signature.s.0.as_slice(),
            ),
        ] {
            assert!(
                !encoded.windows(secret.len()).any(|window| window == secret),
                "{label} is serialized verbatim in the proof",
            );
        }

        let mut wrong_key_statement = statement.clone();
        wrong_key_statement
            .ts13_revocation
            .revocation_public_key
            .x
            .0[0] ^= 1;
        assert_verify_rejects(
            "tampered revocation public key",
            &proof,
            &wrong_key_statement,
        );

        let mut stripped_bundle = proof.clone();
        stripped_bundle.coprocessor_bundle.entries.pop();
        assert_verify_rejects("stripped revocation instance", &stripped_bundle, &statement);

        let mut tampered_tag = proof.clone();
        let tags = &mut tampered_tag.coprocessor_bundle.mac_tags;
        tags[eu_id_ec_coprocessor::ecdsa::MDOC_P4B_MAC_HALF_COUNT - 1][0] ^= 1;
        assert_verify_rejects("tampered revocation MAC tag", &tampered_tag, &statement);
    }

    /// A proof whose packed SHA trace carries the wrong message count for the
    /// statement's predicate mode must never verify: an `And` proof packs five
    /// messages, a one-predicate proof packs four, and the statement-driven
    /// consumer set is the only thing that enforces the count (§6.3 LogUp
    /// balance — there is no message-count field anywhere in the proof).
    #[test]
    #[ignore = "slow: proves both predicate modes and cross-checks the packed SHA message count"]
    fn product_rejects_wrong_packed_sha_message_count_for_statement() {
        let age_attributes = vec![MdocRequestedAttribute {
            element_identifier: "birth_date".to_string(),
            mode: MdocDisclosureMode::AgeOver,
        }];
        let and_attributes = vec![
            MdocRequestedAttribute {
                element_identifier: "birth_date".to_string(),
                mode: MdocDisclosureMode::AgeOver,
            },
            MdocRequestedAttribute {
                element_identifier: "nationality".to_string(),
                mode: MdocDisclosureMode::Alpha2Set,
            },
        ];
        let age_fixture = demo_mdoc_circuit_fixture_with_attributes(age_attributes);
        let and_fixture = demo_mdoc_circuit_fixture_with_attributes(and_attributes);

        let age_proof = prove_mdoc_circuit(&age_fixture.extracted, &age_fixture.statement)
            .expect("honest four-message Age proof proves");
        verify_mdoc_circuit(&age_proof, &age_fixture.statement)
            .expect("honest four-message Age proof verifies");
        let and_proof = prove_mdoc_circuit(&and_fixture.extracted, &and_fixture.statement)
            .expect("honest five-message And proof proves");
        verify_mdoc_circuit(&and_proof, &and_fixture.statement)
            .expect("honest five-message And proof verifies");

        assert!(
            verify_mdoc_circuit(&and_proof, &age_fixture.statement).is_err(),
            "five-message And proof verified against a four-consumer Age statement"
        );
        assert!(
            verify_mdoc_circuit(&age_proof, &and_fixture.statement).is_err(),
            "four-message Age proof verified against a five-consumer And statement"
        );

        for (label, extracted, statement) in [
            (
                "five-message extraction against a four-consumer statement",
                &and_fixture.extracted,
                &age_fixture.statement,
            ),
            (
                "four-message extraction against a five-consumer statement",
                &age_fixture.extracted,
                &and_fixture.statement,
            ),
        ] {
            if let Ok(proof) = prove_mdoc_circuit(extracted, statement) {
                assert!(
                    verify_mdoc_circuit(&proof, statement).is_err(),
                    "{label} produced a verifying proof"
                );
            }
        }
    }
}

fn is_supported_mdoc_profile_version(version: &str) -> bool {
    version == MDOC_PROFILE_VERSION
}

fn value_field<'a>(map: &'a [(Value, Value)], field: &'static str) -> Result<&'a Value, MdocError> {
    map.iter()
        .find_map(|(key, value)| (key == &Value::Text(field.to_string())).then_some(value))
        .ok_or(MdocError::MissingField(field))
}

fn value_int_key(map: &[(Value, Value)], key: i128) -> Option<&Value> {
    map.iter().find_map(|(candidate, value)| {
        value_i128(candidate)
            .ok()
            .filter(|candidate| *candidate == key)
            .map(|_| value)
    })
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

fn expect_array<'a>(value: &'a Value, field: &'static str) -> Result<&'a [Value], MdocError> {
    match value {
        Value::Array(items) => Ok(items),
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
