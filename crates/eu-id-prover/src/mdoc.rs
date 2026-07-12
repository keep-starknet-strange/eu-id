//! Product EUID PID mdoc proof path.
//!
//! This module parses the constrained ISO/IEC 18013-5 PID profile, prepares the
//! mdoc statement/witness, and proves issuer signature, ISO device
//! authentication, MSO digest membership, validity, device-key origin, and the
//! age/nationality predicates in one verifier-facing proof. The legacy nonce
//! module is not part of this path; the device-auth signature binds freshness.

use std::collections::HashMap;
use std::time::{Duration, Instant};

use air_core::relations::{
    field_id, DigestBytesRelation, FieldBytesRelation, SharedDigestRelation, SharedFieldRelation,
};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use ciborium::value::Value;
#[cfg(feature = "p256")]
use ecdsa::signature::{Signer, Verifier};
#[cfg(feature = "p256")]
use p256::ecdsa::{Signature as P256Signature, SigningKey, VerifyingKey};
#[cfg(feature = "p256")]
use p256::pkcs8::DecodePublicKey;
#[cfg(feature = "p256")]
use p256::EncodedPoint;
use predicates::nat::NationalityPredicate;
use predicates::{AgeRangeCheck, DateOfBirth, PredicateProver, PredicateVerifier};
#[cfg(feature = "ec-coprocessor")]
use rand_core::{OsRng, RngCore};
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
#[cfg(feature = "ec-coprocessor")]
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
#[cfg(feature = "ml-dsa")]
use stwo_mldsa::statement::HOSTED_MSG_FIELD_ID;
#[cfg(all(feature = "ml-dsa", not(feature = "ec-coprocessor")))]
use stwo_mldsa::statement::{
    keccak_job_shapes, MlDsaProver as MlDsaStatementProver, MlDsaVerifier as MlDsaStatementVerifier,
};
#[cfg(all(feature = "ml-dsa", not(feature = "ec-coprocessor")))]
use stwo_mldsa::stwo_keccak::relations::SharedKeccakRelations;
#[cfg(all(feature = "ml-dsa", not(feature = "ec-coprocessor")))]
use stwo_mldsa::stwo_keccak::service::{KeccakServiceProver, KeccakServiceVerifier};
#[cfg(feature = "ml-dsa")]
use stwo_mldsa::types::MlDsaVerifyInput;
#[cfg(feature = "p256")]
use stwo_p256::components::digest_bind::module::{
    DigestBindInteractionClaim, DigestBindProver, DigestBindVerifier,
};
#[cfg(feature = "p256")]
use stwo_p256::components::digest_bind::SharedScalarZRelation;
#[cfg(feature = "p256")]
use stwo_p256::public_inputs::PublicEcdsaInstance;
#[cfg(feature = "p256")]
use stwo_p256::types::{AffinePoint, EcdsaVerifyInput, Signature, U256};
#[cfg(feature = "p256")]
use stwo_p256::{proof::air::P256Prover, proof::P256ProofDraft};
#[cfg(feature = "p256")]
use stwo_p256::{
    proof::air::P256Verifier,
    proof::{P256CurrentAirInteractionClaim, P256CurrentAirProofClaim},
};
use stwo_sha256::air::{Sha256MultiProver, Sha256MultiVerifier};
use stwo_sha256::field_exposure::FieldExposure;
use stwo_sha256::interaction::InteractionClaim as Sha256InteractionClaim;
use stwo_sha256::relations::SharedShaTableRelations;
use stwo_sha256::shared_tables::{
    ShaTableMultiplicities, ShaTablesInteractionClaim, ShaTablesProver, ShaTablesVerifier,
};
use stwo_sha256::slots::{MultiSlotConfig, SlotSpec};
use stwo_sha256::trace::min_log_size;
use stwo_sha256::witness::compute_sha256_witness;

use crate::claimed_sum_blinder::{
    add_blinder_relation_entry, blinder_counter_interaction, random_qm31, ClaimedSumBlinderEval,
    ClaimedSumBlinderRelation,
};
#[cfg(feature = "ec-coprocessor")]
use crate::mdoc_mac::{
    MdocMacBind, MdocMacInteractionClaim, MdocP4bMacPublic, MdocP4bMacSharedState,
};
use crate::mdoc_window_bind::{MdocWindowBind, MdocWindowBindInteractionClaim, MdocWindowBindRow};
use crate::policy::Policy;
#[cfg(any(feature = "ec-coprocessor", feature = "ml-dsa"))]
use crate::public_digest_bind::{PublicDigestBind, PublicDigestBindInteractionClaim};
use crate::Error;

/// Legacy profile: `elementValue` packed as a fixed-width CBOR `bstr`.
const MDOC_PROFILE_VERSION_V1: &str = "1.0";
/// Profile v2: canonical (RFC 8949 core deterministic) CBOR, text-form values.
const MDOC_PROFILE_VERSION_V2: &str = "2.0";
/// The profile the demo fixture emits and the parser advertises by default.
#[cfg(feature = "p256")]
const MDOC_PROFILE_VERSION: &str = MDOC_PROFILE_VERSION_V2;
const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
/// COSE protected header `{1: -49}` (ML-DSA-65,
/// `stwo_mldsa::constants::COSE_ALG_ML_DSA_65`): CBOR `A1 01 38 30`.
const MLDSA_PROTECTED_HEADER: &[u8] = &[0xA1, 0x01, 0x38, 0x30];
const CBOR_TAG_ENCODED_CBOR: u64 = 24;
const CBOR_TAG_FULL_DATE: u64 = 1004;
const MDOC_ATTRIBUTE_ELEMENT_ID_BASE: u32 = 16;
const MDOC_ATTRIBUTE_VALUE_BASE: u32 = 20;
const MDOC_ATTRIBUTE_VALUE_HEAD_BASE: u32 = 32;
const MDOC_ATTRIBUTE_ELEMENT_ANCHOR_BASE: u32 = 36;
const MDOC_REVOCATION_MESSAGE_FIELD_ID: u32 = 41;
const TS13_REVOCATION_MESSAGE_LEN: usize = 20;
/// Per-role instance namespaces for hosted ML-DSA modules. Prover and verifier
/// must agree; the namespace is mixed into the transcript (role/domain
/// separation — a device claim tree cannot be replayed against the revocation
/// slot) and prefixes the witness-dependent preprocessed column ids (so two
/// instances cannot alias each other's SIB schedules under tree-0 dedup).
#[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
const MDOC_ISSUER_MLDSA_NAMESPACE: &str = "mdoc/issuer";
#[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
const MDOC_DEVICE_MLDSA_NAMESPACE: &str = "mdoc/device";
#[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
const MDOC_REVOCATION_MLDSA_NAMESPACE: &str = "mdoc/ts13/revocation";
/// Per-role HashIo stream-id bases for hosted ML-DSA modules (S1): every
/// instance shares the ONE keccak-service relation set, so stream ids must be
/// globally unique. Prover and verifier must agree per role; each base must be
/// a multiple of [`stwo_mldsa::statement::STREAM_BASE_STRIDE`] (0x100/0x200/
/// 0x300 all are).
#[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
const MDOC_ISSUER_MLDSA_STREAM_BASE: u32 = 0x100;
#[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
const MDOC_DEVICE_MLDSA_STREAM_BASE: u32 = 0x200;
#[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
const MDOC_REVOCATION_MLDSA_STREAM_BASE: u32 = 0x300;
#[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
const _: () = assert!(
    MDOC_ISSUER_MLDSA_STREAM_BASE.is_multiple_of(stwo_mldsa::statement::STREAM_BASE_STRIDE)
        && MDOC_DEVICE_MLDSA_STREAM_BASE.is_multiple_of(stwo_mldsa::statement::STREAM_BASE_STRIDE)
        && MDOC_REVOCATION_MLDSA_STREAM_BASE
            .is_multiple_of(stwo_mldsa::statement::STREAM_BASE_STRIDE)
);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MdocPidRequest {
    pub doctype: String,
    pub namespace: String,
    pub attributes: Vec<MdocRequestedAttribute>,
    pub birth_date_element: String,
    pub nationality_element: String,
    pub session_transcript: Vec<u8>,
    /// ML-DSA-65 issuer trust pins: FIPS 204 `pkEncode` bytes (1,952 each). An
    /// ML-DSA issuer REQUIRES a non-empty pin list and the header AKP key must
    /// be byte-equal to a member — a self-carried key is never a trust decision
    /// (no PQ PKI profile exists yet, so there is no x5chain equivalent).
    pub trusted_mldsa_issuer_public_keys: Vec<Vec<u8>>,
    pub device_authentication_profile: MdocDeviceAuthenticationProfile,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MdocDeviceAuthenticationProfile {
    Iso180135,
    LongfellowLegacy,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MdocDisclosureMode {
    ValueEquality(Vec<u8>),
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

impl MdocPidRequest {
    pub fn eudi_pid(session_transcript: Vec<u8>) -> Self {
        Self {
            doctype: PID_DOCTYPE.to_string(),
            namespace: PID_NAMESPACE.to_string(),
            attributes: vec![
                MdocRequestedAttribute {
                    element_identifier: "birth_date".to_string(),
                    mode: MdocDisclosureMode::AgeOver,
                },
                MdocRequestedAttribute {
                    element_identifier: "nationality".to_string(),
                    mode: MdocDisclosureMode::Alpha2Set,
                },
            ],
            birth_date_element: "birth_date".to_string(),
            nationality_element: "nationality".to_string(),
            session_transcript,
            trusted_mldsa_issuer_public_keys: Vec::new(),
            device_authentication_profile: MdocDeviceAuthenticationProfile::Iso180135,
        }
    }

    /// See [`MdocPidRequest::trusted_mldsa_issuer_public_keys`].
    pub fn with_trusted_mldsa_issuer_public_keys(mut self, public_keys: Vec<Vec<u8>>) -> Self {
        self.trusted_mldsa_issuer_public_keys = public_keys;
        self
    }

    pub fn with_device_authentication_profile(
        mut self,
        profile: MdocDeviceAuthenticationProfile,
    ) -> Self {
        self.device_authentication_profile = profile;
        self
    }

    pub fn disclosed_attributes(&self) -> Vec<MdocRequestedAttribute> {
        self.attributes.clone()
    }
}

fn validate_requested_attributes(attributes: &[MdocRequestedAttribute]) -> Result<(), MdocError> {
    if !(1..=crate::mdoc_window_bind::MDOC_MAX_DISCLOSED_ATTRIBUTES).contains(&attributes.len()) {
        return Err(MdocError::InvalidAttributeCount {
            count: attributes.len(),
        });
    }
    let mut age_seen = false;
    let mut alpha2_seen = false;
    for attribute in attributes {
        match &attribute.mode {
            MdocDisclosureMode::ValueEquality(bytes) => {
                if bytes.len() > 32 {
                    return Err(MdocError::ValueEqualityTooLong {
                        element: attribute.element_identifier.clone(),
                        len: bytes.len(),
                    });
                }
                if attribute.element_identifier.len() > 32 {
                    return Err(MdocError::ElementIdentifierTooLong {
                        element: attribute.element_identifier.clone(),
                        len: attribute.element_identifier.len(),
                    });
                }
            }
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

/// ML-DSA-65 signature-verification input shared by issuer and device roles.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum MdocAuthInput {
    /// Boxed because an `MlDsaVerifyInput` is roughly 20 KiB inline.
    MlDsa(Box<MlDsaVerifyInput>),
}

/// The issuer-role view of [`MdocAuthInput`] (historical name, kept as alias).
pub type IssuerAuthInput = MdocAuthInput;
/// The device-role view of [`MdocAuthInput`].
pub type DeviceAuthInput = MdocAuthInput;

impl MdocAuthInput {
    pub fn as_mldsa(&self) -> Option<&MlDsaVerifyInput> {
        match self {
            Self::MlDsa(input) => Some(input.as_ref()),
        }
    }

    /// Whether this is an ML-DSA-65 issuer. Always available (returns `false`
    /// when the `ml-dsa` feature is disabled, since the variant cannot exist) so
    /// digest-handle selection compiles in every feature combination.
    pub fn is_mldsa(&self) -> bool {
        true
    }
}

fn auth_inputs_equal(left: &MdocAuthInput, right: &MdocAuthInput) -> bool {
    match (left, right) {
        (MdocAuthInput::MlDsa(l), MdocAuthInput::MlDsa(r)) => l == r,
    }
}

#[derive(Clone, Debug)]
pub struct ExtractedPidMdoc {
    pub doctype: String,
    pub namespace: String,
    pub attributes: Vec<MdocRequestedAttribute>,
    pub extracted_attributes: Vec<ExtractedMdocAttribute>,
    pub birth_date: String,
    pub nationalities: Vec<u32>,
    pub birth_date_bytes: [u8; 4],
    pub nationality_bytes: [u8; 2],
    pub birth_date_binding: MdocBirthDateBinding,
    pub nationality_binding: MdocNationalityBinding,
    pub birth_date_value_offset: usize,
    pub nationality_value_offset: usize,
    pub signed_at: (u16, u8, u8),
    pub valid_from: (u16, u8, u8),
    pub valid_until: (u16, u8, u8),
    pub digest_ids: HashMap<String, u32>,
    pub birth_date_item: Vec<u8>,
    pub nationality_item: Vec<u8>,
    pub mso: Vec<u8>,
    pub issuer_sig_structure: Vec<u8>,
    pub device_sig_structure: Vec<u8>,
    /// The issuer-auth verification input (ECDSA or ML-DSA-65). For an ML-DSA
    /// issuer, `issuer_key`/`issuer_signature` above are zeroed placeholders —
    /// the real key/signature live in this enum's `MlDsa` arm.
    pub issuer_auth_input: IssuerAuthInput,
    /// The device-auth verification input (ECDSA or ML-DSA-65). For an ML-DSA
    /// device, `device_key`/`device_signature` above are zeroed placeholders.
    /// Signature schemes are uniform across roles (fail-closed at extraction):
    /// this arm always matches `issuer_auth_input`'s.
    pub device_auth_input: DeviceAuthInput,
}

/// How the `birth_date` element value is encoded in the item preimage. The
/// window bytes exposed to the age predicate differ per encoding: `Packed`
/// exposes the 4 raw big-endian date bytes; `Text` exposes the 10 ASCII bytes
/// of the canonical `YYYY-MM-DD` tstr (profile v2).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MdocBirthDateBinding {
    Packed([u8; 4]),
    Text([u8; 10]),
}

impl MdocBirthDateBinding {
    fn as_bytes(&self) -> &[u8] {
        match self {
            Self::Packed(bytes) => bytes,
            Self::Text(bytes) => bytes,
        }
    }
}

/// How the `nationality` element value is encoded in the item preimage.
/// `Numeric` exposes the 2 raw big-endian country-code bytes; `Alpha2` exposes
/// the 2 ASCII bytes of the ISO 3166-1 alpha-2 code (profile v2).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MdocNationalityBinding {
    Numeric([u8; 2]),
    Alpha2([u8; 2]),
}

impl MdocNationalityBinding {
    fn as_bytes(&self) -> &[u8] {
        match self {
            Self::Numeric(bytes) | Self::Alpha2(bytes) => bytes,
        }
    }

    fn code(&self) -> u32 {
        match self {
            Self::Numeric(bytes) | Self::Alpha2(bytes) => u32::from(u16::from_be_bytes(*bytes)),
        }
    }
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
    UntrustedIssuerKey,
    InvalidSignature(&'static str),
    InvalidNationality(String),
    UnsupportedCircuitValue(&'static str),
    UnsupportedMsoVersion(String),
    InvalidTdate(&'static str),
    CredentialNotYetValid,
    CredentialExpired,
    SaltTooShort { len: usize },
    InvalidAttributeCount { count: usize },
    DuplicatePredicateMode(&'static str),
    ValueEqualityTooLong { element: String, len: usize },
    ElementIdentifierTooLong { element: String, len: usize },
    ValueEqualityMismatch { element: String },
}

/// Parse + natively pre-check an ML-DSA-65 issuerAuth (FIPS 204 Algorithm 3,
/// pure mode, empty context) and build the in-circuit witness. Shared by the
/// `p256` and quantum-only extraction shells.
#[cfg(feature = "ml-dsa")]
fn mldsa_issuer_input(
    issuer_unprotected: &[(Value, Value)],
    request: &MdocPidRequest,
    issuer_auth: &CoseSign1,
) -> Result<MlDsaVerifyInput, MdocError> {
    let pk = mldsa_issuer_pk_from_unprotected(issuer_unprotected, request)?;
    let trace = stwo_mldsa::reference::verify::verify_internals(
        &pk,
        &issuer_auth.sig_structure,
        &issuer_auth.signature_bytes,
    )
    .map_err(|_| MdocError::InvalidSignature("issuerAuth"))?;
    if !trace.accepted {
        return Err(MdocError::InvalidSignature("issuerAuth"));
    }
    let decoded_pk = stwo_mldsa::reference::encoding::pk_decode(&pk)
        .map_err(|_| MdocError::InvalidCoseKey("ML-DSA-65 public key"))?;
    let decoded_sig = stwo_mldsa::reference::encoding::sig_decode(&issuer_auth.signature_bytes)
        .map_err(|_| MdocError::InvalidSignature("issuerAuth"))?;
    Ok(MlDsaVerifyInput::from_decoded(
        &decoded_pk,
        &decoded_sig,
        trace.tr,
        issuer_auth.sig_structure.clone(),
    ))
}

/// Mirror of [`mldsa_issuer_input`] for the device role: native FIPS 204
/// pre-check over the device `Sig_structure`, then the decoded in-circuit
/// input. Rejects the mixed ML-DSA-device / ES256-issuer row fail-closed.
#[cfg(feature = "ml-dsa")]
fn mldsa_device_auth_input(
    pk: &[u8],
    device_signature: &CoseSign1,
) -> Result<MdocAuthInput, MdocError> {
    let trace = stwo_mldsa::reference::verify::verify_internals(
        pk,
        &device_signature.sig_structure,
        &device_signature.signature_bytes,
    )
    .map_err(|_| MdocError::InvalidSignature("deviceSignature"))?;
    if !trace.accepted {
        return Err(MdocError::InvalidSignature("deviceSignature"));
    }
    let decoded_pk = stwo_mldsa::reference::encoding::pk_decode(pk)
        .map_err(|_| MdocError::InvalidCoseKey("ML-DSA-65 public key"))?;
    let decoded_sig =
        stwo_mldsa::reference::encoding::sig_decode(&device_signature.signature_bytes)
            .map_err(|_| MdocError::InvalidSignature("deviceSignature"))?;
    let input = MlDsaVerifyInput::from_decoded(
        &decoded_pk,
        &decoded_sig,
        trace.tr,
        device_signature.sig_structure.clone(),
    );
    Ok(MdocAuthInput::MlDsa(Box::new(input)))
}

pub fn extract_pid_mdoc(
    document: &[u8],
    request: &MdocPidRequest,
) -> Result<ExtractedPidMdoc, MdocError> {
    let requested_attributes = request.disclosed_attributes();
    validate_requested_attributes(&requested_attributes)?;
    let doc = decode_value(document)?;
    let doc_map = document_map(&doc)?;
    let doctype = text_field(doc_map, "docType")?.to_string();
    if doctype != request.doctype {
        return Err(MdocError::DoctypeMismatch);
    }

    let issuer_signed = map_field(doc_map, "issuerSigned")?;
    let issuer_auth = parse_cose_sign1(value_field(issuer_signed, "issuerAuth")?)?;
    let issuer_unprotected = expect_map(&issuer_auth.unprotected, "issuerAuth.unprotected")?;
    let issuer_mldsa_input = mldsa_issuer_input(issuer_unprotected, request, &issuer_auth)?;

    let mso = parse_mso(&issuer_auth.payload, &request.namespace)?;
    if !is_supported_mdoc_profile_version(&mso.version) {
        return Err(MdocError::UnsupportedMsoVersion(mso.version));
    }
    if mso.doc_type != request.doctype {
        return Err(MdocError::DoctypeMismatch);
    }

    let namespace_items = namespace_items(issuer_signed, &request.namespace)?;
    let mut extracted_attributes = Vec::with_capacity(requested_attributes.len());
    for attribute in &requested_attributes {
        let item = find_item(namespace_items, &attribute.element_identifier, &mso.version)?
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
        if let MdocDisclosureMode::ValueEquality(expected) = &attribute.mode {
            if &value != expected {
                return Err(MdocError::ValueEqualityMismatch {
                    element: attribute.element_identifier.clone(),
                });
            }
        }
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
            find_item(namespace_items, element, &mso.version)?
                .ok_or_else(|| MdocError::ElementMissing(element.to_string()))?,
        )
    } else {
        None
    };
    let nationality_item = if let Some(element) = nationality_element {
        Some(
            find_item(namespace_items, element, &mso.version)?
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
    let parsed_nat = if let Some(item) = &nationality_item {
        validate_item_digest(
            &mso.value_digests,
            nationality_element.expect("Alpha2Set element is present"),
            item.digest_id,
            &item.bytes,
        )?;
        parse_nationality_value(item)?
    } else {
        ParsedNationalityValue::default()
    };

    let device_signed = map_field(doc_map, "deviceSigned")?;
    let device_auth = map_field(device_signed, "deviceAuth")?;
    let expected_device_payload = expected_device_authentication_bytes(request)?;
    let device_signature = parse_cose_sign1_with_detached_payload(
        value_field(device_auth, "deviceSignature")?,
        &expected_device_payload,
    )?;
    if device_signature.payload != expected_device_payload {
        return Err(MdocError::DeviceAuthPayloadMismatch);
    }
    let device_auth_input = mldsa_device_auth_input(&mso.device_key, &device_signature)?;

    let mut digest_ids = HashMap::new();
    for attribute in &extracted_attributes {
        digest_ids.insert(
            attribute.request.element_identifier.clone(),
            attribute.digest_id,
        );
    }
    if let (Some(element), Some(item)) = (birth_date_element, &birth_date_item) {
        digest_ids.insert(element.to_string(), item.digest_id);
    }
    if let (Some(element), Some(item)) = (nationality_element, &nationality_item) {
        digest_ids.insert(element.to_string(), item.digest_id);
    }

    let issuer_auth_input = IssuerAuthInput::MlDsa(Box::new(issuer_mldsa_input));

    Ok(ExtractedPidMdoc {
        doctype,
        namespace: request.namespace.clone(),
        attributes: requested_attributes,
        extracted_attributes,
        birth_date: parsed_birth.display,
        nationalities: vec![parsed_nat.numeric],
        birth_date_bytes: parsed_birth.bytes,
        nationality_bytes: parsed_nat.bytes,
        birth_date_binding: parsed_birth.binding,
        nationality_binding: parsed_nat.binding,
        birth_date_value_offset: parsed_birth.offset,
        nationality_value_offset: parsed_nat.offset,
        signed_at: mso.signed_at,
        valid_from: mso.valid_from,
        valid_until: mso.valid_until,
        digest_ids,
        birth_date_item: birth_date_item.map(|item| item.bytes).unwrap_or_default(),
        nationality_item: nationality_item.map(|item| item.bytes).unwrap_or_default(),
        mso: issuer_auth.payload,
        issuer_sig_structure: issuer_auth.sig_structure,
        device_sig_structure: device_signature.sig_structure,
        issuer_auth_input,
        device_auth_input,
    })
}

fn document_map(value: &Value) -> Result<&[(Value, Value)], MdocError> {
    let map = expect_map(value, "document")?;
    if value_field(map, "docType").is_ok() {
        return Ok(map);
    }
    if let Ok(status) = value_field(map, "status") {
        if value_i128(status)? != 0 {
            return Err(MdocError::WrongType("DeviceResponse.status"));
        }
    }
    let documents = expect_array(value_field(map, "documents")?, "DeviceResponse.documents")?;
    let first_document = documents
        .first()
        .ok_or(MdocError::MissingField("documents"))?;
    expect_map(first_document, "DeviceResponse.documents[0]")
}

#[derive(Clone)]
struct ParsedBirthDateValue {
    display: String,
    bytes: [u8; 4],
    binding: MdocBirthDateBinding,
    offset: usize,
}

impl Default for ParsedBirthDateValue {
    fn default() -> Self {
        Self {
            display: String::new(),
            bytes: [0; 4],
            binding: MdocBirthDateBinding::Text(*b"0000-00-00"),
            offset: 0,
        }
    }
}

#[derive(Clone)]
struct ParsedNationalityValue {
    numeric: u32,
    bytes: [u8; 2],
    binding: MdocNationalityBinding,
    offset: usize,
}

impl Default for ParsedNationalityValue {
    fn default() -> Self {
        Self {
            numeric: 0,
            bytes: [0; 2],
            binding: MdocNationalityBinding::Alpha2([0; 2]),
            offset: 0,
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
    device_key: Vec<u8>,
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
        Value::Text(text) => parse_birth_date_text_value(item, text),
        Value::Tag(CBOR_TAG_FULL_DATE, inner) => {
            let text = expect_text(inner, "birth_date elementValue")?;
            parse_birth_date_text_value(item, text)
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
                binding: MdocBirthDateBinding::Packed(raw),
                offset,
            })
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
        display: text.to_string(),
        bytes: [(year >> 8) as u8, (year & 0xFF) as u8, month, day],
        binding: MdocBirthDateBinding::Text(
            value_bytes
                .try_into()
                .map_err(|_| MdocError::UnsupportedCircuitValue("birth_date text length"))?,
        ),
        offset,
    })
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
                binding: MdocNationalityBinding::Alpha2(
                    alpha2.as_bytes().try_into().map_err(|_| {
                        MdocError::UnsupportedCircuitValue("nationality text length")
                    })?,
                ),
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
                binding: MdocNationalityBinding::Numeric(raw),
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

fn full_date_text_bytes(date: (u16, u8, u8)) -> [u8; 10] {
    format!("{:04}-{:02}-{:02}", date.0, date.1, date.2)
        .as_bytes()
        .try_into()
        .expect("formatted full-date has YYYY-MM-DD length")
}

fn labeled_tdate_date_offset(
    mso: &[u8],
    label: &[u8],
    date: (u16, u8, u8),
    error: &'static str,
) -> Result<usize, MdocError> {
    let label_offset =
        find_subslice(mso, label).ok_or(MdocError::UnsupportedCircuitValue(error))?;
    let date_bytes = full_date_text_bytes(date);
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

/// Field exposure over the `birth_date` item preimage: the value window
/// (consumed by the age predicate) plus the `elementIdentifier` window (D1,
/// consumed by the MSO window-bind component). The window length tracks the
/// binding form (4 raw bytes for v1 packed, 10 ASCII bytes for v2 text), and the
/// multi-block constructor tolerates a window straddling a SHA-256 block
/// boundary.
#[cfg(feature = "p256")]
fn birth_date_exposure(statement: &MdocCircuitStatement) -> FieldExposure {
    let Some(index) = statement.age_attribute_index else {
        return FieldExposure::empty();
    };
    attribute_exposure(statement, index)
}

/// Field exposure over the `nationality` item preimage: the value window
/// (2 bytes) plus the `elementIdentifier` window (D1).
#[cfg(feature = "p256")]
fn nationality_exposure(statement: &MdocCircuitStatement) -> FieldExposure {
    let Some(index) = statement.nationality_attribute_index else {
        return FieldExposure::empty();
    };
    attribute_exposure(statement, index)
}

fn attribute_exposure(statement: &MdocCircuitStatement, index: usize) -> FieldExposure {
    let attribute = &statement.attributes[index];
    let mut windows = vec![(
        MdocStatementAttribute::element_field_id(index),
        attribute.element_identifier_offset,
        attribute.element_identifier.len(),
    )];
    windows.push((
        MdocStatementAttribute::element_anchor_field_id(index),
        attribute.element_identifier_anchor_offset,
        attribute.element_identifier_anchor.len(),
    ));
    match &attribute.mode {
        MdocDisclosureMode::AgeOver => windows.push((
            field_id::DOB,
            statement.birth_date_value_offset,
            statement.birth_date_binding.as_bytes().len(),
        )),
        MdocDisclosureMode::Alpha2Set => windows.push((
            field_id::NATIONALITY,
            statement.nationality_value_offset,
            statement.nationality_binding.as_bytes().len(),
        )),
        MdocDisclosureMode::ValueEquality(_) => windows.push((
            MdocStatementAttribute::value_field_id(index),
            attribute.value_offset,
            attribute.value.len(),
        )),
    }
    if matches!(attribute.mode, MdocDisclosureMode::ValueEquality(_)) {
        windows.push((
            MdocStatementAttribute::value_head_field_id(index),
            attribute.value_offset,
            attribute.value_head.len(),
        ));
    }
    FieldExposure::from_preimage_windows_multi(&windows)
}

/// Field exposure over the issuer `Sig_structure` preimage: the two 32-byte
/// `valueDigests` windows (D2) and the two 32-byte deviceKey coordinate windows
/// (D3), all consumed by the MSO window-bind component.
fn ts13_revocation_message_bytes(id_lo: u64, id_hi: u64, epoch: u32) -> [u8; 20] {
    let mut bytes = [0u8; TS13_REVOCATION_MESSAGE_LEN];
    bytes[..8].copy_from_slice(&id_lo.to_le_bytes());
    bytes[8..16].copy_from_slice(&id_hi.to_le_bytes());
    bytes[16..].copy_from_slice(&epoch.to_le_bytes());
    bytes
}

fn check_mldsa_extracted_statement_coherence(
    extracted: &ExtractedPidMdoc,
    statement: &MdocCircuitStatement,
) -> Result<(), Error> {
    if let Some(input) = statement.issuer_input.as_mldsa() {
        if extracted.issuer_sig_structure != input.message {
            return Err(Error::Prove(
                "mdoc extracted issuer Sig_structure does not match the statement's public ML-DSA message".to_string(),
            ));
        }
    }
    if let Some(input) = statement.device_input.as_mldsa() {
        if extracted.device_sig_structure != input.message {
            return Err(Error::Prove(
                "mdoc extracted device Sig_structure does not match the statement's public ML-DSA message".to_string(),
            ));
        }
    }
    Ok(())
}

fn check_mldsa_device_key_binding(statement: &MdocCircuitStatement) -> Result<(), Error> {
    let (Some(issuer_input), Some(device_input)) = (
        statement.issuer_input.as_mldsa(),
        statement.device_input.as_mldsa(),
    ) else {
        return Ok(());
    };
    let bind_err =
        |context: &str| Error::Prove(format!("mdoc ML-DSA device-key MSO binding: {context}"));
    let sig_structure =
        decode_value(&issuer_input.message).map_err(|_| bind_err("Sig_structure decode"))?;
    let Value::Array(items) = sig_structure else {
        return Err(bind_err("Sig_structure shape"));
    };
    let payload = items
        .get(3)
        .and_then(|payload| payload.as_bytes())
        .ok_or_else(|| bind_err("Sig_structure payload"))?;
    let mso = parse_mso_device_key(payload).map_err(|_| bind_err("MSO deviceKey parse"))?;
    let mso_pk = mso;
    if mso_pk != device_input.encode_pk() {
        return Err(bind_err(
            "MSO deviceKey does not match the statement device public key",
        ));
    }
    Ok(())
}

/// Navigate `MobileSecurityObjectBytes` (or a bare MSO map) to
/// `deviceKeyInfo.deviceKey` and parse it. Shares the exact decode helpers the
/// extraction-time `parse_mso` uses.
#[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
fn parse_mso_device_key(bytes: &[u8]) -> Result<Vec<u8>, MdocError> {
    let value = decode_value(bytes)?;
    let value = match value {
        Value::Tag(CBOR_TAG_ENCODED_CBOR, inner) => {
            let mso_bytes = expect_bytes(&inner, "MobileSecurityObjectBytes")?;
            decode_value(mso_bytes)?
        }
        value => value,
    };
    let mso = expect_map(&value, "MobileSecurityObject")?;
    let device_key_info = map_field(mso, "deviceKeyInfo")?;
    parse_device_cose_key(value_field(device_key_info, "deviceKey")?)
}

/// S4 host-side public-MSO facts for the ML-DSA scheme, derived identically on
/// BOTH prove and verify from the PUBLIC issuer `Sig_structure` before any
/// STARK work.
#[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
struct MdocMlDsaPublicMsoFacts {
    /// Per-statement-attribute 32-byte `valueDigests` window (anchor-verified);
    /// feeds the per-attribute `PublicDigestBind` components.
    attribute_digests: Vec<[u8; 32]>,
    /// `Sha256` over the CBOR-navigated MSO payload; feeds the TS13
    /// revocation-range public digest binding.
    mso_digest: [u8; 32],
}

/// Compute [`MdocMlDsaPublicMsoFacts`] and run the host-side checks that
/// replace the deleted in-circuit conveyors (S4). `None` for a non-ML-DSA
/// issuer (the P-256 path keeps its in-circuit bindings).
///
/// # Soundness
///
/// In ML-DSA mode the issuer `Sig_structure` is a PUBLIC statement input: it
/// is mixed into Fiat–Shamir and absorbed in-circuit by the issuer instance's
/// public-message producer, so substituting a different message is an ML-DSA
/// forgery. Every fact below is therefore a fail-closed host-side check over
/// those public bytes, run IDENTICALLY at prove and verify:
///
/// * **attribute digests** — anchor content + anchor↔window adjacency checked,
///   then the 32-byte digest read out; the value pins the in-circuit
///   attribute-SHA digest through `PublicDigestBind` (replaces the window-bind
///   digest rows + issuer SHA conveyor);
/// * **validity** — anchor content + adjacency checked, the `YYYY-MM-DD`
///   windows parsed and compared against the policy date
///   (`validFrom <= current_date <= validUntil`, replaces `MdocValidityBind`);
/// * **MSO digest** — the MSO is the CBOR-navigated `Sig_structure` payload
///   (no prover-supplied offsets), hashed natively (replaces `mso_sha` +
///   `MdocMsoPayloadBind`).
#[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
fn mldsa_public_mso_facts(
    statement: &MdocCircuitStatement,
) -> Result<Option<MdocMlDsaPublicMsoFacts>, Error> {
    let Some(issuer_input) = statement.issuer_input.as_mldsa() else {
        return Ok(None);
    };
    let message = issuer_input.message.as_slice();
    let bind_err =
        |context: &str| Error::Prove(format!("mdoc ML-DSA public MSO binding: {context}"));
    let window = |offset: usize, len: usize, context: &'static str| {
        offset
            .checked_add(len)
            .and_then(|end| message.get(offset..end))
            .ok_or_else(|| bind_err(context))
    };
    let anchored_window = |anchor_offset: usize,
                           anchor: &[u8],
                           window_offset: usize,
                           window_len: usize,
                           context: &'static str| {
        if anchor.is_empty() {
            return Err(bind_err(context));
        }
        if window(anchor_offset, anchor.len(), context)? != anchor {
            return Err(bind_err(context));
        }
        if anchor_offset + anchor.len() != window_offset {
            return Err(bind_err(context));
        }
        window(window_offset, window_len, context)
    };

    // Attribute `valueDigests` windows.
    let mut attribute_digests = Vec::with_capacity(statement.attributes.len());
    for attribute in &statement.attributes {
        let digest: [u8; 32] = anchored_window(
            attribute.mso_digest_anchor_offset,
            &attribute.mso_digest_anchor,
            attribute.mso_digest_offset,
            32,
            "attribute digest window",
        )?
        .try_into()
        .expect("32-byte digest window");
        attribute_digests.push(digest);
    }

    // Validity windows vs the policy date (mirror of `MdocValidityBind`).
    let policy_date = policy_date_tuple(&statement.policy).map_err(Error::Mdoc)?;
    let parse_date = |bytes: &[u8]| -> Result<(u16, u8, u8), Error> {
        if bytes.len() != 10 || bytes[4] != b'-' || bytes[7] != b'-' {
            return Err(bind_err("validity date format"));
        }
        let digits = |range: std::ops::Range<usize>| -> Result<u32, Error> {
            bytes[range].iter().try_fold(0u32, |acc, &b| {
                if b.is_ascii_digit() {
                    Ok(acc * 10 + u32::from(b - b'0'))
                } else {
                    Err(bind_err("validity date digit"))
                }
            })
        };
        Ok((
            digits(0..4)? as u16,
            digits(5..7)? as u8,
            digits(8..10)? as u8,
        ))
    };
    let valid_from = parse_date(anchored_window(
        statement.mso_valid_from_anchor_offset,
        &statement.mso_valid_from_anchor,
        statement.mso_valid_from_date_offset,
        10,
        "validFrom window",
    )?)?;
    let valid_until = parse_date(anchored_window(
        statement.mso_valid_until_anchor_offset,
        &statement.mso_valid_until_anchor,
        statement.mso_valid_until_date_offset,
        10,
        "validUntil window",
    )?)?;
    if valid_from > policy_date || policy_date > valid_until {
        return Err(bind_err("policy date outside the validity window"));
    }

    // MSO digest from the CBOR-navigated payload (device-key D2 pattern).
    let sig_structure = decode_value(message).map_err(|_| bind_err("Sig_structure decode"))?;
    let Value::Array(items) = sig_structure else {
        return Err(bind_err("Sig_structure shape"));
    };
    let payload = items
        .get(3)
        .and_then(|payload| payload.as_bytes())
        .ok_or_else(|| bind_err("Sig_structure payload"))?;
    let mso_digest: [u8; 32] = Sha256::digest(payload).into();

    Ok(Some(MdocMlDsaPublicMsoFacts {
        attribute_digests,
        mso_digest,
    }))
}

/// Build the ML-DSA revocation verification input from the statement's public
/// key/signature bytes and the given 20-byte message. The prover passes the
/// REAL message (from the private range witness); the verifier passes 20 zero
/// bytes — the hosted instance runs in private-message mode, which mixes only
/// the message LENGTH into the transcript, and the real bytes flow exclusively
/// through the revocation SHA module's field relation (G6 privacy invariant:
/// `id_lo`/`id_hi` never enter the serialized statement or proof).
#[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
fn ts13_revocation_mldsa_input(
    statement: &MdocCircuitStatement,
    message: Vec<u8>,
) -> Result<Option<Box<MlDsaVerifyInput>>, Error> {
    let Some(signature) = statement
        .ts13_revocation_signature
        .as_ref()
        .and_then(|signature| signature.as_mldsa())
    else {
        return Ok(None);
    };
    let revocation = statement.ts13_revocation.as_ref().ok_or_else(|| {
        Error::Prove("TS13 revocation signature requires public revocation inputs".to_string())
    })?;
    let pk = revocation.revocation_public_key.as_mldsa().ok_or_else(|| {
        Error::Prove(
            "TS13 ML-DSA revocation signature requires an ML-DSA revocation key".to_string(),
        )
    })?;
    let decoded_pk = stwo_mldsa::reference::encoding::pk_decode(pk)
        .map_err(|error| Error::Prove(format!("TS13 revocation pk decode: {error:?}")))?;
    let decoded_sig = stwo_mldsa::reference::encoding::sig_decode(signature)
        .map_err(|error| Error::Prove(format!("TS13 revocation sig decode: {error:?}")))?;
    // tr = SHAKE-256(pk, 64 bytes) — a pure function of the PUBLIC key, so
    // both sides recompute it identically without touching the message.
    let (tr_bytes, _) = stwo_mldsa::reference::sponge::shake256(&[pk], 64);
    let tr: [u8; 64] = tr_bytes
        .try_into()
        .expect("shake256 returns the requested 64 bytes");
    Ok(Some(Box::new(MlDsaVerifyInput::from_decoded(
        &decoded_pk,
        &decoded_sig,
        tr,
        message,
    ))))
}

#[cfg(feature = "ec-coprocessor")]
fn mdoc_p4b_mac_values(statement: &MdocCircuitStatement) -> [eu_id_ec_coprocessor::mac::Gf128; 6] {
    let [issuer_z_lo, issuer_z_hi] = eu_id_ec_coprocessor::ecdsa::gf128_halves_from_be32(
        statement
            .issuer_input
            .as_ecdsa()
            .expect("ec-coprocessor MAC values require a P-256 issuer (guarded upstream)")
            .message_hash
            .0,
    );
    let device_input = statement
        .device_input
        .as_ecdsa()
        .expect("ec-coprocessor MAC values require a P-256 device (guarded upstream)");
    let [device_qx_lo, device_qx_hi] =
        eu_id_ec_coprocessor::ecdsa::gf128_halves_from_be32(device_input.public_key.x.0);
    let [device_qy_lo, device_qy_hi] =
        eu_id_ec_coprocessor::ecdsa::gf128_halves_from_be32(device_input.public_key.y.0);
    [
        issuer_z_lo,
        issuer_z_hi,
        device_qx_lo,
        device_qx_hi,
        device_qy_lo,
        device_qy_hi,
    ]
}

/// Build the six window-bind rows. On the prover the digest witness bytes are
/// read from the issuer preimage at the two digest offsets; the verifier passes
/// `None` (the digest bytes are reconstructed through the shared LogUp
/// relations, not asserted host-side).
fn mdoc_window_bind_rows_from(
    statement: &MdocCircuitStatement,
    _issuer_sig_structure: Option<&[u8]>,
) -> Vec<MdocWindowBindRow> {
    // S4 ML-DSA issuer: NO in-circuit issuer byte provider exists — every
    // `IssuerMso`-sourced row (digest windows + anchors, validity anchors) is
    // replaced by the host-side checks in `mldsa_public_mso_facts`, and the
    // attribute digests bind to PUBLIC values via `PublicDigestBind`. Only the
    // AttributeItem-sourced rows (private item preimages) remain.
    let mut rows = Vec::new();
    for (index, attribute) in statement.attributes.iter().enumerate() {
        rows.push(MdocWindowBindRow::constant(
            MdocStatementAttribute::element_field_id(index),
            index,
            attribute.element_identifier.as_bytes(),
        ));
        rows.push(MdocWindowBindRow::constant(
            MdocStatementAttribute::element_anchor_field_id(index),
            index,
            &attribute.element_identifier_anchor,
        ));
        if let MdocDisclosureMode::ValueEquality(_) = &attribute.mode {
            rows.push(MdocWindowBindRow::constant(
                MdocStatementAttribute::value_field_id(index),
                index,
                &attribute.value,
            ));
            rows.push(MdocWindowBindRow::constant(
                MdocStatementAttribute::value_head_field_id(index),
                index,
                &attribute.value_head,
            ));
        }
    }
    rows
}

/// The nationality public input matching the statement's binding form: the
/// alpha-2 code space for the v2 text path, the ISO-numeric space otherwise.
fn nat_public_input_for(statement: &MdocCircuitStatement) -> predicates::NatPublicInput {
    match statement.nationality_binding {
        MdocNationalityBinding::Numeric(_) => statement.policy.nat_public_input(),
        MdocNationalityBinding::Alpha2(_) => statement.policy.nat_alpha2_public_input(),
    }
}

fn decode_value(bytes: &[u8]) -> Result<Value, MdocError> {
    ciborium::de::from_reader(bytes).map_err(|error| MdocError::Cbor(error.to_string()))
}

fn encode_value(value: Value) -> Vec<u8> {
    let mut out = Vec::new();
    ciborium::ser::into_writer(&value, &mut out).expect("CBOR serialization into Vec");
    out
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
    if protected != MLDSA_PROTECTED_HEADER {
        return Err(MdocError::InvalidCoseSign1(
            "protected header must be ML-DSA-65",
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
    if signature_bytes.len() != stwo_mldsa::constants::SIG_BYTES {
        return Err(MdocError::InvalidCoseSign1("ML-DSA-65 signature length"));
    }
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
    let session_transcript = decode_value(session_transcript)?;
    if !matches!(session_transcript, Value::Array(_)) {
        return Err(MdocError::WrongType("SessionTranscript"));
    }

    let device_namespaces = encode_value(Value::Map(Vec::new()));
    let device_namespaces_bytes =
        encode_value(Value::Tag(24, Box::new(Value::Bytes(device_namespaces))));
    let device_authentication = encode_value(Value::Array(vec![
        "DeviceAuthentication".into(),
        session_transcript,
        doc_type.into(),
        Value::Bytes(device_namespaces_bytes),
    ]));
    Ok(encode_value(Value::Tag(
        24,
        Box::new(Value::Bytes(device_authentication)),
    )))
}

fn expected_device_authentication_bytes(request: &MdocPidRequest) -> Result<Vec<u8>, MdocError> {
    match request.device_authentication_profile {
        MdocDeviceAuthenticationProfile::Iso180135 => {
            device_authentication_bytes(&request.session_transcript, &request.doctype)
        }
        MdocDeviceAuthenticationProfile::LongfellowLegacy => {
            longfellow_legacy_device_authentication_bytes(
                &request.session_transcript,
                &request.doctype,
            )
        }
    }
}

fn longfellow_legacy_device_authentication_bytes(
    session_transcript: &[u8],
    doc_type: &str,
) -> Result<Vec<u8>, MdocError> {
    let session_transcript_value = decode_value(session_transcript)?;
    if !matches!(session_transcript_value, Value::Array(_)) {
        return Err(MdocError::WrongType("SessionTranscript"));
    }
    let mut device_authentication = encode_value(Value::Array(vec!["DeviceAuthentication".into()]));
    device_authentication[0] = 0x84;
    device_authentication.extend_from_slice(session_transcript);
    device_authentication.extend_from_slice(&encode_value(Value::Text(doc_type.to_string())));
    device_authentication.extend_from_slice(&encode_value(Value::Tag(
        24,
        Box::new(Value::Bytes(encode_value(Value::Map(Vec::new())))),
    )));
    Ok(encode_value(Value::Tag(
        24,
        Box::new(Value::Bytes(device_authentication)),
    )))
}

pub fn device_authentication_sig_structure_hash(
    session_transcript: &[u8],
    doc_type: &str,
) -> Result<[u8; 32], MdocError> {
    let payload = device_authentication_bytes(session_transcript, doc_type)?;
    Ok(Sha256::digest(sig_structure(MLDSA_PROTECTED_HEADER, &payload)).into())
}

#[cfg(feature = "p256")]
fn demo_mdoc_document(session_transcript: &[u8], include_extra_items: bool) -> Vec<u8> {
    let issuer_signing_key =
        SigningKey::from_bytes((&[7u8; 32]).into()).expect("demo issuer signing key");
    let device_signing_key =
        SigningKey::from_bytes((&[11u8; 32]).into()).expect("demo device signing key");
    let issuer_cose_key = demo_cose_key(&issuer_signing_key);
    let device_cose_key = demo_cose_key(&device_signing_key);

    // Profile v2: canonical CBOR items with text-form (`tstr`) element values.
    let birth_date_item = demo_issuer_signed_item(
        7,
        "birth_date",
        Value::Text("1990-07-15".to_string()),
        vec![7; 16],
    );
    let nationality_item =
        demo_issuer_signed_item(9, "nationality", Value::Text("DE".to_string()), vec![9; 16]);
    let birth_digest: [u8; 32] = Sha256::digest(&birth_date_item).into();
    let nat_digest: [u8; 32] = Sha256::digest(&nationality_item).into();
    let mut value_digest_entries = vec![
        (Value::from(7), Value::Bytes(birth_digest.to_vec())),
        (Value::from(9), Value::Bytes(nat_digest.to_vec())),
    ];
    let mut namespace_items = vec![
        Value::Bytes(birth_date_item),
        Value::Bytes(nationality_item),
    ];
    if include_extra_items {
        let family_name_item = demo_issuer_signed_item(
            11,
            "family_name",
            Value::Text("Mustermann".to_string()),
            vec![11; 16],
        );
        let age_over_18_item =
            demo_issuer_signed_item(13, "age_over_18", Value::Bool(true), vec![13; 16]);
        let family_name_digest: [u8; 32] = Sha256::digest(&family_name_item).into();
        let age_over_18_digest: [u8; 32] = Sha256::digest(&age_over_18_item).into();
        value_digest_entries.extend([
            (Value::from(11), Value::Bytes(family_name_digest.to_vec())),
            (Value::from(13), Value::Bytes(age_over_18_digest.to_vec())),
        ]);
        namespace_items.extend([
            Value::Bytes(family_name_item),
            Value::Bytes(age_over_18_item),
        ]);
    }

    let mso = encode_value(Value::Map(vec![
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
    ]));

    let issuer_auth = demo_cose_sign1(
        &issuer_signing_key,
        Value::Map(vec![("issuerKey".into(), issuer_cose_key)]),
        &mso,
    );
    let device_signature = demo_cose_sign1(
        &device_signing_key,
        Value::Map(Vec::new()),
        &device_authentication_bytes(session_transcript, PID_DOCTYPE)
            .expect("demo device auth payload builds"),
    );

    encode_value(Value::Map(vec![
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
            Value::Map(vec![(
                "deviceAuth".into(),
                Value::Map(vec![("deviceSignature".into(), device_signature)]),
            )]),
        ),
    ]))
}

#[cfg(feature = "p256")]
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

#[cfg(feature = "p256")]
fn demo_issuer_signed_item(
    digest_id: u64,
    element: &str,
    value: Value,
    random: Vec<u8>,
) -> Vec<u8> {
    // Profile v2 canonical (RFC 8949 core deterministic) key order:
    // shortest-encoded-key-first ⇒ `random, digestID, elementValue,
    // elementIdentifier` (7, 8, 12, 17 bytes of key text respectively).
    let item = Value::Map(vec![
        ("random".into(), Value::Bytes(random)),
        ("digestID".into(), Value::from(digest_id)),
        ("elementValue".into(), value),
        ("elementIdentifier".into(), element.into()),
    ]);
    encode_value(Value::Tag(24, Box::new(Value::Bytes(encode_value(item)))))
}

#[cfg(feature = "p256")]
fn demo_tdate(text: &str) -> Value {
    Value::Tag(0, Box::new(text.into()))
}

#[cfg(feature = "p256")]
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
    let device_key = parse_device_cose_key(value_field(device_key_info, "deviceKey")?)?;
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

fn find_item(
    items: &[Value],
    element: &str,
    profile_version: &str,
) -> Result<Option<ParsedItem>, MdocError> {
    for item in items {
        let item_bytes = issuer_signed_item_bytes(item)?;
        let parsed = parse_issuer_signed_item_bytes(&item_bytes, profile_version)?;
        if parsed.element == element {
            return Ok(Some(parsed));
        }
    }
    Ok(None)
}

fn issuer_signed_item_bytes(item: &Value) -> Result<Vec<u8>, MdocError> {
    match item {
        Value::Bytes(bytes) => Ok(bytes.clone()),
        Value::Tag(CBOR_TAG_ENCODED_CBOR, inner) => {
            expect_bytes(inner, "IssuerSignedItemBytes")?;
            Ok(encode_value(item.clone()))
        }
        _ => Err(MdocError::WrongType("IssuerSignedItemBytes")),
    }
}

fn parse_issuer_signed_item_bytes(
    bytes: &[u8],
    profile_version: &str,
) -> Result<ParsedItem, MdocError> {
    let value = decode_value(bytes)?;
    let Value::Tag(24, inner) = value else {
        return Err(MdocError::WrongType("IssuerSignedItemBytes tag 24"));
    };
    let item_bytes = expect_bytes(&inner, "IssuerSignedItemBytes")?;
    let item_value = decode_value(item_bytes)?;
    let item = expect_map(&item_value, "IssuerSignedItem")?;
    ensure_issuer_signed_item_key_order(item, profile_version)?;
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

/// Require the four `IssuerSignedItem` keys. Profile v1 accepts legacy key
/// ordering; profile v2 requires the RFC 8949 canonical order used by the
/// canonical-CBOR profile.
fn ensure_issuer_signed_item_key_order(
    item: &[(Value, Value)],
    profile_version: &str,
) -> Result<(), MdocError> {
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
    if profile_version == MDOC_PROFILE_VERSION_V2 {
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

/// Parse the MSO ML-DSA-65 AKP `deviceKey`.
fn parse_device_cose_key(value: &Value) -> Result<Vec<u8>, MdocError> {
    let key = expect_map(value, "COSE_Key")?;
    Ok(parse_akp_mldsa_cose_key(key)?.to_vec())
}

#[cfg(feature = "p256")]
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

#[cfg(feature = "p256")]
fn issuer_key_from_unprotected(
    unprotected: &[(Value, Value)],
    request: &MdocPidRequest,
) -> Result<AffinePoint, MdocError> {
    if let Some(x5chain) = value_int_key(unprotected, 33) {
        return issuer_key_from_x5chain(
            x5chain,
            &request.trusted_issuer_certificates,
            &request.trusted_issuer_public_keys,
        );
    }
    let issuer_key = parse_cose_key(value_field(unprotected, "issuerKey")?)?;
    if !request.trusted_issuer_public_keys.is_empty()
        && !request
            .trusted_issuer_public_keys
            .iter()
            .any(|trusted| trusted == &issuer_key)
    {
        return Err(MdocError::UntrustedIssuerCertificate);
    }
    Ok(issuer_key)
}

/// The FIPS 204 `pkEncode` bytes of the statement's ML-DSA issuer key,
/// recomputed from the PUBLIC `(ρ, t1)` in the statement — never read from the
/// prover-supplied `tr` digest. A relying party binds its issuer trust anchor
/// against this (e.g. the SDK's statement-binding layer compares a pinned
/// SHA-256 of these bytes); `None` for a P-256 issuer statement.
#[cfg(feature = "ml-dsa")]
pub fn mdoc_statement_issuer_mldsa_pk(statement: &MdocCircuitStatement) -> Option<Vec<u8>> {
    statement
        .issuer_input
        .as_mldsa()
        .map(|input| stwo_mldsa::reference::encoding::pk_encode(&input.rho, &input.t1))
}

/// ML-DSA-65 issuer key from the unprotected `issuerKey` COSE_Key: AKP key
/// type (`kty = 7`), `alg = -49`, raw 1952-byte public key in label `-1`.
///
/// Trust is FAIL-CLOSED: the request MUST carry a non-empty
/// `trusted_mldsa_issuer_public_keys` pin list and the header key must be
/// byte-equal to a member — the self-carried AKP key is never a trust
/// decision.
fn mldsa_issuer_pk_from_unprotected(
    unprotected: &[(Value, Value)],
    request: &MdocPidRequest,
) -> Result<Vec<u8>, MdocError> {
    let key = expect_map(value_field(unprotected, "issuerKey")?, "COSE_Key")?;
    let pk = parse_akp_mldsa_cose_key(key)?;
    if !request
        .trusted_mldsa_issuer_public_keys
        .iter()
        .any(|trusted| trusted.as_slice() == pk)
    {
        // Also the empty-pin-list case: no pins ⇒ nothing is trusted.
        return Err(MdocError::UntrustedIssuerKey);
    }
    Ok(pk.to_vec())
}

/// Parse an AKP ML-DSA-65 COSE_Key map (`kty = 7`, `alg = -49`, raw 1952-byte
/// public key in label `-1`). Shared by the issuer header key and the MSO
/// `deviceKey` parser.
fn parse_akp_mldsa_cose_key(key: &[(Value, Value)]) -> Result<&[u8], MdocError> {
    let kty = int_field(key, 1, "COSE_Key.kty")?;
    let alg = int_field(key, 3, "COSE_Key.alg")?;
    if kty != i128::from(stwo_mldsa::constants::COSE_KTY_AKP)
        || alg != i128::from(stwo_mldsa::constants::COSE_ALG_ML_DSA_65)
    {
        return Err(MdocError::InvalidCoseKey("expected ML-DSA-65 AKP key"));
    }
    let pk = bytes_int_field(key, -1, "COSE_Key.pub")?;
    if pk.len() != stwo_mldsa::constants::PK_BYTES {
        return Err(MdocError::InvalidCoseKey("ML-DSA-65 public key length"));
    }
    Ok(pk)
}

#[cfg(feature = "p256")]
fn issuer_key_from_x5chain(
    value: &Value,
    trusted_roots: &[Vec<u8>],
    trusted_public_keys: &[AffinePoint],
) -> Result<AffinePoint, MdocError> {
    let chain = x5chain_certificates(value)?;
    let parsed_chain = chain
        .iter()
        .map(|certificate| parse_x509_certificate(certificate))
        .collect::<Result<Vec<_>, _>>()?;
    for pair in parsed_chain.windows(2) {
        verify_certificate_signature(&pair[0], &pair[1])?;
    }
    let issuer_key = affine_point_from_spki(parsed_chain[0].spki_der)?;
    if trusted_public_keys
        .iter()
        .any(|trusted| trusted == &issuer_key)
    {
        return Ok(issuer_key);
    }
    let chain_anchor = chain
        .last()
        .ok_or(MdocError::InvalidCertificate("empty x5chain"))?;
    let parsed_anchor = parsed_chain
        .last()
        .ok_or(MdocError::InvalidCertificate("empty x5chain"))?;
    if !is_trusted_x5chain_anchor(*chain_anchor, parsed_anchor, trusted_roots)? {
        return Err(MdocError::UntrustedIssuerCertificate);
    }
    Ok(issuer_key)
}

#[cfg(feature = "p256")]
fn is_trusted_x5chain_anchor(
    anchor_der: &[u8],
    anchor: &ParsedCertificate<'_>,
    trusted_roots: &[Vec<u8>],
) -> Result<bool, MdocError> {
    for trusted_root in trusted_roots {
        if trusted_root.as_slice() == anchor_der {
            return Ok(true);
        }
        let trusted_root = parse_x509_certificate(trusted_root)?;
        if verify_certificate_signature(anchor, &trusted_root).is_ok() {
            return Ok(true);
        }
    }
    Ok(false)
}

#[cfg(feature = "p256")]
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
#[cfg(feature = "p256")]
struct ParsedCertificate<'a> {
    tbs_der: &'a [u8],
    spki_der: &'a [u8],
    signature_der: &'a [u8],
}

#[derive(Clone, Copy)]
#[cfg(feature = "p256")]
struct DerTlv<'a> {
    tag: u8,
    value: &'a [u8],
    full: &'a [u8],
}

#[cfg(feature = "p256")]
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
    let signature_der = der_bit_string_bytes(signature, "certificate.signatureValue")?;

    let spki_der = certificate_spki_der(tbs.value)?;
    Ok(ParsedCertificate {
        tbs_der: tbs.full,
        spki_der,
        signature_der,
    })
}

#[cfg(feature = "p256")]
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

#[cfg(feature = "p256")]
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

#[cfg(feature = "p256")]
fn der_bit_string_bytes<'a>(
    bit_string: DerTlv<'a>,
    label: &'static str,
) -> Result<&'a [u8], MdocError> {
    if bit_string.value.first() != Some(&0) {
        return Err(MdocError::InvalidCertificate(label));
    }
    Ok(&bit_string.value[1..])
}

#[cfg(feature = "p256")]
fn verify_certificate_signature(
    certificate: &ParsedCertificate<'_>,
    issuer: &ParsedCertificate<'_>,
) -> Result<(), MdocError> {
    let issuer_key = VerifyingKey::from_public_key_der(issuer.spki_der)
        .map_err(|_| MdocError::InvalidCertificate("issuer subjectPublicKeyInfo"))?;
    let signature = P256Signature::from_der(certificate.signature_der)
        .map_err(|_| MdocError::InvalidCertificate("certificate signature DER"))?;
    issuer_key
        .verify(certificate.tbs_der, &signature)
        .map_err(|_| MdocError::InvalidSignature("issuer x5chain"))
}

#[cfg(feature = "p256")]
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

#[cfg(feature = "p256")]
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

#[cfg(feature = "p256")]
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

#[cfg(feature = "p256")]
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

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MdocCircuitStatement {
    pub issuer_input: IssuerAuthInput,
    /// Device-auth input. Scheme uniformity with `issuer_input` (and, when
    /// present, the revocation key/signature) is enforced fail-closed at prove
    /// AND verify — a mixed statement never reaches STARK work.
    pub device_input: DeviceAuthInput,
    pub ts13_revocation: Option<MdocRevocationPublicInputs>,
    pub ts13_revocation_range: Option<MdocRevocationRangeWitness>,
    pub ts13_revocation_signature: Option<MdocRevocationSignature>,
    pub attributes: Vec<MdocStatementAttribute>,
    pub age_attribute_index: Option<usize>,
    pub nationality_attribute_index: Option<usize>,
    pub birth_date_binding: MdocBirthDateBinding,
    pub nationality_binding: MdocNationalityBinding,
    pub birth_date_value_offset: usize,
    pub nationality_value_offset: usize,
    /// Offset of the `"birth_date"` `elementIdentifier` window in the birth_date
    /// item preimage (D1).
    pub birth_date_element_offset: usize,
    /// Offset of the `"nationality"` `elementIdentifier` window in the
    /// nationality item preimage (D1).
    pub nationality_element_offset: usize,
    /// Offset of the birth_date `valueDigests` 32-byte window in the issuer
    /// `Sig_structure` preimage (D2).
    pub mso_birth_date_digest_offset: usize,
    pub mso_birth_date_digest_anchor_offset: usize,
    pub mso_birth_date_digest_anchor: Vec<u8>,
    /// Offset of the nationality `valueDigests` 32-byte window in the issuer
    /// `Sig_structure` preimage (D2).
    pub mso_nationality_digest_offset: usize,
    pub mso_nationality_digest_anchor_offset: usize,
    pub mso_nationality_digest_anchor: Vec<u8>,
    /// Offset of the deviceKey x-coordinate 32-byte window in the issuer
    /// `Sig_structure` preimage (D3).
    pub mso_device_key_x_offset: usize,
    pub mso_device_key_x_anchor_offset: usize,
    pub mso_device_key_x_anchor: Vec<u8>,
    /// Offset of the deviceKey y-coordinate 32-byte window in the issuer
    /// `Sig_structure` preimage (D3).
    pub mso_device_key_y_offset: usize,
    pub mso_device_key_y_anchor_offset: usize,
    pub mso_device_key_y_anchor: Vec<u8>,
    pub valid_from: (u16, u8, u8),
    pub valid_until: (u16, u8, u8),
    /// Offset of the `validityInfo.validFrom` `YYYY-MM-DD` date window in the
    /// issuer `Sig_structure` preimage (validity binding).
    pub mso_valid_from_date_offset: usize,
    pub mso_valid_from_anchor_offset: usize,
    pub mso_valid_from_anchor: Vec<u8>,
    /// Offset of the `validityInfo.validUntil` `YYYY-MM-DD` date window in the
    /// issuer `Sig_structure` preimage (validity binding).
    pub mso_valid_until_date_offset: usize,
    pub mso_valid_until_anchor_offset: usize,
    pub mso_valid_until_anchor: Vec<u8>,
    /// Offset and length of the issuerAuth payload MSO bytes inside the issuer
    /// `Sig_structure` preimage. Used by TS13 revocation id binding.
    pub mso_payload_offset: usize,
    pub mso_payload_len: usize,
    pub policy: Policy,
}

#[cfg(feature = "p256")]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MdocPublicStatement {
    pub issuer_public_key: AffinePoint,
    pub device_message_hash: U256,
    pub ts13_revocation: Option<MdocRevocationPublicInputs>,
    pub ts13_revocation_range_enabled: bool,
    pub ts13_revocation_signature_enabled: bool,
    pub attributes: Vec<MdocStatementAttribute>,
    pub age_attribute_index: Option<usize>,
    pub nationality_attribute_index: Option<usize>,
    pub birth_date_binding: MdocBirthDateBinding,
    pub nationality_binding: MdocNationalityBinding,
    pub birth_date_value_offset: usize,
    pub nationality_value_offset: usize,
    pub birth_date_element_offset: usize,
    pub nationality_element_offset: usize,
    pub mso_birth_date_digest_offset: usize,
    pub mso_birth_date_digest_anchor_offset: usize,
    pub mso_birth_date_digest_anchor: Vec<u8>,
    pub mso_nationality_digest_offset: usize,
    pub mso_nationality_digest_anchor_offset: usize,
    pub mso_nationality_digest_anchor: Vec<u8>,
    pub mso_device_key_x_offset: usize,
    pub mso_device_key_x_anchor_offset: usize,
    pub mso_device_key_x_anchor: Vec<u8>,
    pub mso_device_key_y_offset: usize,
    pub mso_device_key_y_anchor_offset: usize,
    pub mso_device_key_y_anchor: Vec<u8>,
    pub valid_from: (u16, u8, u8),
    pub valid_until: (u16, u8, u8),
    pub mso_valid_from_date_offset: usize,
    pub mso_valid_from_anchor_offset: usize,
    pub mso_valid_from_anchor: Vec<u8>,
    pub mso_valid_until_date_offset: usize,
    pub mso_valid_until_anchor_offset: usize,
    pub mso_valid_until_anchor: Vec<u8>,
    pub mso_payload_offset: usize,
    pub mso_payload_len: usize,
    pub policy: Policy,
}

#[cfg(feature = "p256")]
impl MdocPublicStatement {
    pub fn from_circuit(statement: &MdocCircuitStatement) -> Self {
        Self {
            // Zeroed for an ML-DSA issuer: this public-statement projection is
            // consumed by the ec-coprocessor path, which is P-256-only.
            issuer_public_key: statement
                .issuer_input
                .as_ecdsa()
                .map(|input| input.public_key.clone())
                .unwrap_or(AffinePoint {
                    x: U256([0u8; 32]),
                    y: U256([0u8; 32]),
                }),
            // Zeroed for an ML-DSA device: this projection is consumed by the
            // ec-coprocessor path, which is P-256-only.
            device_message_hash: statement
                .device_input
                .as_ecdsa()
                .map(|input| input.message_hash.clone())
                .unwrap_or(U256([0u8; 32])),
            ts13_revocation: statement.ts13_revocation.clone(),
            ts13_revocation_range_enabled: statement.ts13_revocation_range.is_some(),
            ts13_revocation_signature_enabled: statement.ts13_revocation_signature.is_some(),
            attributes: statement.attributes.clone(),
            age_attribute_index: statement.age_attribute_index,
            nationality_attribute_index: statement.nationality_attribute_index,
            birth_date_binding: statement.birth_date_binding,
            nationality_binding: statement.nationality_binding,
            birth_date_value_offset: statement.birth_date_value_offset,
            nationality_value_offset: statement.nationality_value_offset,
            birth_date_element_offset: statement.birth_date_element_offset,
            nationality_element_offset: statement.nationality_element_offset,
            mso_birth_date_digest_offset: statement.mso_birth_date_digest_offset,
            mso_birth_date_digest_anchor_offset: statement.mso_birth_date_digest_anchor_offset,
            mso_birth_date_digest_anchor: statement.mso_birth_date_digest_anchor.clone(),
            mso_nationality_digest_offset: statement.mso_nationality_digest_offset,
            mso_nationality_digest_anchor_offset: statement.mso_nationality_digest_anchor_offset,
            mso_nationality_digest_anchor: statement.mso_nationality_digest_anchor.clone(),
            mso_device_key_x_offset: statement.mso_device_key_x_offset,
            mso_device_key_x_anchor_offset: statement.mso_device_key_x_anchor_offset,
            mso_device_key_x_anchor: statement.mso_device_key_x_anchor.clone(),
            mso_device_key_y_offset: statement.mso_device_key_y_offset,
            mso_device_key_y_anchor_offset: statement.mso_device_key_y_anchor_offset,
            mso_device_key_y_anchor: statement.mso_device_key_y_anchor.clone(),
            valid_from: statement.valid_from,
            valid_until: statement.valid_until,
            mso_valid_from_date_offset: statement.mso_valid_from_date_offset,
            mso_valid_from_anchor_offset: statement.mso_valid_from_anchor_offset,
            mso_valid_from_anchor: statement.mso_valid_from_anchor.clone(),
            mso_valid_until_date_offset: statement.mso_valid_until_date_offset,
            mso_valid_until_anchor_offset: statement.mso_valid_until_anchor_offset,
            mso_valid_until_anchor: statement.mso_valid_until_anchor.clone(),
            mso_payload_offset: statement.mso_payload_offset,
            mso_payload_len: statement.mso_payload_len,
            policy: statement.policy.clone(),
        }
    }

    #[cfg(feature = "ec-coprocessor")]
    fn verifier_circuit_statement(&self) -> MdocCircuitStatement {
        let zero_sig = Signature {
            r: U256([0u8; 32]),
            s: U256([0u8; 32]),
        };
        MdocCircuitStatement {
            issuer_input: IssuerAuthInput::Ecdsa(EcdsaVerifyInput {
                message_hash: U256([0u8; 32]),
                signature: zero_sig.clone(),
                public_key: self.issuer_public_key.clone(),
            }),
            device_input: MdocAuthInput::Ecdsa(EcdsaVerifyInput {
                message_hash: self.device_message_hash.clone(),
                signature: zero_sig.clone(),
                public_key: AffinePoint {
                    x: U256([0u8; 32]),
                    y: U256([0u8; 32]),
                },
            }),
            ts13_revocation: self.ts13_revocation.clone(),
            ts13_revocation_range: self.ts13_revocation_range_enabled.then_some(
                MdocRevocationRangeWitness {
                    id: 0,
                    id_lo: 0,
                    id_hi: 0,
                },
            ),
            ts13_revocation_signature: self
                .ts13_revocation_signature_enabled
                .then_some(MdocRevocationSignature::Ecdsa(zero_sig)),
            attributes: self.attributes.clone(),
            age_attribute_index: self.age_attribute_index,
            nationality_attribute_index: self.nationality_attribute_index,
            birth_date_binding: self.birth_date_binding,
            nationality_binding: self.nationality_binding,
            birth_date_value_offset: self.birth_date_value_offset,
            nationality_value_offset: self.nationality_value_offset,
            birth_date_element_offset: self.birth_date_element_offset,
            nationality_element_offset: self.nationality_element_offset,
            mso_birth_date_digest_offset: self.mso_birth_date_digest_offset,
            mso_birth_date_digest_anchor_offset: self.mso_birth_date_digest_anchor_offset,
            mso_birth_date_digest_anchor: self.mso_birth_date_digest_anchor.clone(),
            mso_nationality_digest_offset: self.mso_nationality_digest_offset,
            mso_nationality_digest_anchor_offset: self.mso_nationality_digest_anchor_offset,
            mso_nationality_digest_anchor: self.mso_nationality_digest_anchor.clone(),
            mso_device_key_x_offset: self.mso_device_key_x_offset,
            mso_device_key_x_anchor_offset: self.mso_device_key_x_anchor_offset,
            mso_device_key_x_anchor: self.mso_device_key_x_anchor.clone(),
            mso_device_key_y_offset: self.mso_device_key_y_offset,
            mso_device_key_y_anchor_offset: self.mso_device_key_y_anchor_offset,
            mso_device_key_y_anchor: self.mso_device_key_y_anchor.clone(),
            valid_from: self.valid_from,
            valid_until: self.valid_until,
            mso_valid_from_date_offset: self.mso_valid_from_date_offset,
            mso_valid_from_anchor_offset: self.mso_valid_from_anchor_offset,
            mso_valid_from_anchor: self.mso_valid_from_anchor.clone(),
            mso_valid_until_date_offset: self.mso_valid_until_date_offset,
            mso_valid_until_anchor_offset: self.mso_valid_until_anchor_offset,
            mso_valid_until_anchor: self.mso_valid_until_anchor.clone(),
            mso_payload_offset: self.mso_payload_offset,
            mso_payload_len: self.mso_payload_len,
            policy: self.policy.clone(),
        }
    }
}

/// The TS13 revocation-authority public key, scheme-tagged. The scheme must
/// match the issuer/device scheme (uniformity is enforced at statement
/// validation): an ML-DSA credential with a P-256 revocation authority (or
/// vice versa) is rejected fail-closed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MdocRevocationKey {
    #[cfg(feature = "p256")]
    Ecdsa(AffinePoint),
    /// FIPS 204 `pkEncode` bytes (1,952).
    #[cfg(feature = "ml-dsa")]
    MlDsa(Vec<u8>),
}

impl MdocRevocationKey {
    #[cfg(feature = "p256")]
    pub fn as_ecdsa(&self) -> Option<&AffinePoint> {
        match self {
            Self::Ecdsa(key) => Some(key),
            #[cfg(feature = "ml-dsa")]
            Self::MlDsa(_) => None,
        }
    }

    #[cfg(feature = "ml-dsa")]
    pub fn as_mldsa(&self) -> Option<&[u8]> {
        match self {
            #[cfg(feature = "p256")]
            Self::Ecdsa(_) => None,
            Self::MlDsa(pk) => Some(pk),
        }
    }

    pub fn is_mldsa(&self) -> bool {
        match self {
            #[cfg(feature = "p256")]
            Self::Ecdsa(_) => false,
            #[cfg(feature = "ml-dsa")]
            Self::MlDsa(_) => true,
        }
    }
}

/// The TS13 revocation-authority signature over the raw 20-byte message
/// `LE64(id_lo) ‖ LE64(id_hi) ‖ LE32(epoch)`, scheme-tagged. The P-256 arm
/// signs the SHA-256 prehash of the message; the ML-DSA arm is a pure FIPS 204
/// signature over the raw bytes (no prehash — the message stays private via
/// the hosted module's private-message mode).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MdocRevocationSignature {
    #[cfg(feature = "p256")]
    Ecdsa(Signature),
    /// FIPS 204 `sigEncode` bytes (3,309).
    #[cfg(feature = "ml-dsa")]
    MlDsa(Vec<u8>),
}

impl MdocRevocationSignature {
    #[cfg(feature = "p256")]
    pub fn as_ecdsa(&self) -> Option<&Signature> {
        match self {
            Self::Ecdsa(signature) => Some(signature),
            #[cfg(feature = "ml-dsa")]
            Self::MlDsa(_) => None,
        }
    }

    #[cfg(feature = "ml-dsa")]
    pub fn as_mldsa(&self) -> Option<&[u8]> {
        match self {
            #[cfg(feature = "p256")]
            Self::Ecdsa(_) => None,
            Self::MlDsa(signature) => Some(signature),
        }
    }

    pub fn is_mldsa(&self) -> bool {
        match self {
            #[cfg(feature = "p256")]
            Self::Ecdsa(_) => false,
            #[cfg(feature = "ml-dsa")]
            Self::MlDsa(_) => true,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocRevocationPublicInputs {
    pub revocation_public_key: MdocRevocationKey,
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
    pub element_identifier_offset: usize,
    pub element_identifier_anchor_offset: usize,
    pub element_identifier_anchor: Vec<u8>,
    pub value_offset: usize,
    pub value: Vec<u8>,
    pub value_head: Vec<u8>,
    pub digest_id: u32,
    pub mso_digest_offset: usize,
    pub mso_digest_anchor_offset: usize,
    pub mso_digest_anchor: Vec<u8>,
}

impl MdocStatementAttribute {
    fn element_field_id(index: usize) -> u32 {
        MDOC_ATTRIBUTE_ELEMENT_ID_BASE + index as u32
    }

    fn value_field_id(index: usize) -> u32 {
        MDOC_ATTRIBUTE_VALUE_BASE + index as u32
    }

    fn value_head_field_id(index: usize) -> u32 {
        MDOC_ATTRIBUTE_VALUE_HEAD_BASE + index as u32
    }

    fn element_anchor_field_id(index: usize) -> u32 {
        MDOC_ATTRIBUTE_ELEMENT_ANCHOR_BASE + index as u32
    }
}

impl MdocCircuitStatement {
    pub fn with_ts13_revocation(mut self, revocation: MdocRevocationPublicInputs) -> Self {
        self.ts13_revocation = Some(revocation);
        self
    }

    pub fn with_ts13_revocation_range(mut self, range: MdocRevocationRangeWitness) -> Self {
        self.ts13_revocation_range = Some(range);
        self
    }

    pub fn with_ts13_revocation_signature(mut self, signature: MdocRevocationSignature) -> Self {
        self.ts13_revocation_signature = Some(signature);
        self
    }

    pub fn from_extracted(extracted: &ExtractedPidMdoc, policy: Policy) -> Result<Self, MdocError> {
        validate_requested_attributes(&extracted.attributes)?;
        let current_date = policy_date_tuple(&policy)?;
        if current_date < extracted.valid_from {
            return Err(MdocError::CredentialNotYetValid);
        }
        if current_date > extracted.valid_until {
            return Err(MdocError::CredentialExpired);
        }

        let mso = parse_mso(&extracted.mso, &extracted.namespace)?;
        if !is_supported_mdoc_profile_version(&mso.version) {
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
            let mso_digest_anchor_offset = anchor_before_offset(
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
            let element_identifier_anchor_offset = anchor_before_offset(
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
                element_identifier_offset: attribute.element_identifier_offset,
                element_identifier_anchor_offset,
                element_identifier_anchor,
                value_offset: attribute.value_offset,
                value: attribute.value.clone(),
                value_head: if matches!(
                    attribute.request.mode,
                    MdocDisclosureMode::ValueEquality(_)
                ) {
                    cbor_value_head(&attribute.value)?
                } else {
                    Vec::new()
                },
                digest_id: attribute.digest_id,
                mso_digest_offset,
                mso_digest_anchor_offset,
                mso_digest_anchor,
            });
        }
        let age_attribute_index = statement_attributes
            .iter()
            .position(|attribute| matches!(attribute.mode, MdocDisclosureMode::AgeOver));
        let nationality_attribute_index = statement_attributes
            .iter()
            .position(|attribute| matches!(attribute.mode, MdocDisclosureMode::Alpha2Set));

        // Phase D: locate the windows the in-circuit MSO bindings pin. The two
        // digests and the device key are no longer public inputs; they are
        // bound in-circuit from these prover-supplied offsets. Each offset is a
        // hint whose *content* the window-bind component pins, and the
        // surrounding bytes are covered by the issuer signature — so a
        // mispointed offset must still exhibit issuer-signed bytes.
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
        let (
            birth_date_element_offset,
            mso_birth_date_digest_offset,
            mso_birth_date_digest_anchor_offset,
            mso_birth_date_digest_anchor,
        ) = age_attribute_index
            .map(|index| {
                let attribute = &statement_attributes[index];
                (
                    attribute.element_identifier_offset,
                    attribute.mso_digest_offset,
                    attribute.mso_digest_anchor_offset,
                    attribute.mso_digest_anchor.clone(),
                )
            })
            .unwrap_or((0, 0, 0, Vec::new()));
        let (
            nationality_element_offset,
            mso_nationality_digest_offset,
            mso_nationality_digest_anchor_offset,
            mso_nationality_digest_anchor,
        ) = nationality_attribute_index
            .map(|index| {
                let attribute = &statement_attributes[index];
                (
                    attribute.element_identifier_offset,
                    attribute.mso_digest_offset,
                    attribute.mso_digest_anchor_offset,
                    attribute.mso_digest_anchor.clone(),
                )
            })
            .unwrap_or((0, 0, 0, Vec::new()));
        // ML-DSA device: the 32-byte coordinate-window mechanism does not apply
        // (the deviceKey is a 1,952-byte AKP key); the device-key ↔ MSO binding
        // is the canonical-CBOR byte-equality check both prove and verify run
        // host-side (`check_mldsa_device_key_binding`) — the issuer
        // Sig_structure is public statement input there, so no window/offset
        // hint exists to tamper with. Offsets/anchors are zeroed placeholders.
        #[cfg(feature = "p256")]
        let device_is_ecdsa = extracted.device_auth_input.as_ecdsa().is_some();
        #[cfg(feature = "p256")]
        let (mso_device_key_x_offset, mso_device_key_y_offset) = if device_is_ecdsa {
            (
                find_subslice(&extracted.issuer_sig_structure, &extracted.device_key.x.0)
                    .ok_or(MdocError::UnsupportedCircuitValue("device key x offset"))?,
                find_subslice(&extracted.issuer_sig_structure, &extracted.device_key.y.0)
                    .ok_or(MdocError::UnsupportedCircuitValue("device key y offset"))?,
            )
        } else {
            (0, 0)
        };
        #[cfg(not(feature = "p256"))]
        let (mso_device_key_x_offset, mso_device_key_y_offset) = (0usize, 0usize);
        let mso_payload_offset = find_subslice(&extracted.issuer_sig_structure, &extracted.mso)
            .ok_or(MdocError::UnsupportedCircuitValue("MSO payload offset"))?;
        let mso_valid_from_date_offset = mso_payload_offset
            + labeled_tdate_date_offset(
                &extracted.mso,
                b"validFrom",
                extracted.valid_from,
                "validFrom date offset",
            )?;
        let mso_valid_until_date_offset = mso_payload_offset
            + labeled_tdate_date_offset(
                &extracted.mso,
                b"validUntil",
                extracted.valid_until,
                "validUntil date offset",
            )?;
        #[cfg(not(feature = "p256"))]
        let (
            mso_device_key_x_anchor,
            mso_device_key_x_anchor_offset,
            mso_device_key_y_anchor,
            mso_device_key_y_anchor_offset,
        ) = (Vec::new(), 0usize, Vec::new(), 0usize);
        #[cfg(feature = "p256")]
        let (
            mso_device_key_x_anchor,
            mso_device_key_x_anchor_offset,
            mso_device_key_y_anchor,
            mso_device_key_y_anchor_offset,
        ) = if device_is_ecdsa {
            let x_anchor = vec![0x21, 0x58, 0x20];
            let x_anchor_offset = anchor_before_offset(
                &extracted.issuer_sig_structure,
                mso_device_key_x_offset,
                &x_anchor,
                "device key x anchor offset",
            )?;
            let y_anchor = vec![0x22, 0x58, 0x20];
            let y_anchor_offset = anchor_before_offset(
                &extracted.issuer_sig_structure,
                mso_device_key_y_offset,
                &y_anchor,
                "device key y anchor offset",
            )?;
            (x_anchor, x_anchor_offset, y_anchor, y_anchor_offset)
        } else {
            (Vec::new(), 0, Vec::new(), 0)
        };
        let mso_valid_from_anchor = cbor_tdate_anchor_bytes("validFrom");
        let mso_valid_from_anchor_offset = anchor_before_offset(
            &extracted.issuer_sig_structure,
            mso_valid_from_date_offset,
            &mso_valid_from_anchor,
            "validFrom anchor offset",
        )?;
        let mso_valid_until_anchor = cbor_tdate_anchor_bytes("validUntil");
        let mso_valid_until_anchor_offset = anchor_before_offset(
            &extracted.issuer_sig_structure,
            mso_valid_until_date_offset,
            &mso_valid_until_anchor,
            "validUntil anchor offset",
        )?;
        #[cfg(feature = "p256")]
        if device_is_ecdsa {
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
        }
        ensure_value_window_with_message(
            &extracted.issuer_sig_structure,
            mso_valid_from_date_offset,
            &full_date_text_bytes(extracted.valid_from),
            "validFrom date offset",
        )?;
        ensure_value_window_with_message(
            &extracted.issuer_sig_structure,
            mso_valid_until_date_offset,
            &full_date_text_bytes(extracted.valid_until),
            "validUntil date offset",
        )?;
        let mso_payload_offset = find_subslice(&extracted.issuer_sig_structure, &extracted.mso)
            .ok_or(MdocError::UnsupportedCircuitValue("MSO payload offset"))?;

        Ok(Self {
            issuer_input: extracted.issuer_auth_input.clone(),
            device_input: extracted.device_auth_input.clone(),
            ts13_revocation: None,
            ts13_revocation_range: None,
            ts13_revocation_signature: None,
            attributes: statement_attributes,
            age_attribute_index,
            nationality_attribute_index,
            birth_date_binding: extracted.birth_date_binding,
            nationality_binding: extracted.nationality_binding,
            birth_date_value_offset: extracted.birth_date_value_offset,
            nationality_value_offset: extracted.nationality_value_offset,
            birth_date_element_offset,
            nationality_element_offset,
            mso_birth_date_digest_offset,
            mso_birth_date_digest_anchor_offset,
            mso_birth_date_digest_anchor,
            mso_nationality_digest_offset,
            mso_nationality_digest_anchor_offset,
            mso_nationality_digest_anchor,
            mso_device_key_x_offset,
            mso_device_key_x_anchor_offset,
            mso_device_key_x_anchor,
            mso_device_key_y_offset,
            mso_device_key_y_anchor_offset,
            mso_device_key_y_anchor,
            valid_from: extracted.valid_from,
            valid_until: extracted.valid_until,
            mso_valid_from_date_offset,
            mso_valid_from_anchor_offset,
            mso_valid_from_anchor,
            mso_valid_until_date_offset,
            mso_valid_until_anchor_offset,
            mso_valid_until_anchor,
            mso_payload_offset,
            mso_payload_len: extracted.mso.len(),
            policy,
        })
    }
}

/// Assert that `item[offset..offset+expected.len()] == expected`.
///
/// Profile v2 drops the v1 "window lies in the first SHA-256 block" rule: the
/// Phase A multi-block field exposure resolves a window straddling a 64-byte
/// block boundary, so the only host-side requirement is byte-equality at the
/// prover-supplied offset.
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

fn policy_date_tuple(policy: &Policy) -> Result<(u16, u8, u8), MdocError> {
    if policy.current_date.year > 9999 {
        return Err(MdocError::InvalidTdate("policy.current_date"));
    }
    Ok((
        u16::try_from(policy.current_date.year)
            .map_err(|_| MdocError::InvalidTdate("policy.current_date"))?,
        u8::try_from(policy.current_date.month)
            .map_err(|_| MdocError::InvalidTdate("policy.current_date"))?,
        u8::try_from(policy.current_date.day)
            .map_err(|_| MdocError::InvalidTdate("policy.current_date"))?,
    ))
}

/// The public claim tree of a hosted in-circuit ML-DSA-65 statement instance —
/// one per role (issuer / device / revocation) — mirroring
/// `stwo_mldsa::statement::MlDsaProof` minus the STARK, which lives in the
/// shared `MdocCircuitProof::stark_proof`.
///
/// Fields are `pub` so negative tests (role-replay claim swaps) can exercise
/// the verifier's rejection paths; soundness never rests on their integrity —
/// the per-role instance namespace is mixed into the transcript, so a claim
/// tree presented in the wrong role slot fails verification.
#[derive(Clone, Serialize, Deserialize)]
pub struct MdocMlDsaClaims {
    pub group_evals: Vec<QM31>,
    pub claimed_sums: Vec<QM31>,
    pub sib_stream_len: usize,
    pub sib_squeezed_len: usize,
}

impl MdocMlDsaClaims {
    fn from_prover(prover: &MlDsaStatementProver) -> Self {
        Self {
            group_evals: prover.group_evals().to_vec(),
            claimed_sums: prover.claimed_sums(),
            sib_stream_len: prover.sib_stream_len(),
            sib_squeezed_len: prover.sib_squeezed_len(),
        }
    }

    /// Shape-gate BEFORE `Claims::from_flat`: a short vector would panic
    /// inside claim-tree construction (outside the verify catch_unwind),
    /// turning a malformed proof into a crash.
    fn has_expected_shape(&self) -> bool {
        self.group_evals.len() == stwo_mldsa::statement::n_group_evals()
            && self.claimed_sums.len() == stwo_mldsa::statement::hosted_claimed_sums_len()
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct MdocCircuitProof {
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
    sha_tables_interaction_claim: ShaTablesInteractionClaim,
    pub mldsa: Option<MdocMlDsaClaims>,
    pub device_mldsa: Option<MdocMlDsaClaims>,
    pub revocation_mldsa: Option<MdocMlDsaClaims>,
    pub keccak_service_claimed_sums: Option<Vec<QM31>>,
    merged_sha_log_n_rows: Option<u32>,
    merged_sha_slot_log: Option<u32>,
    merged_sha_interaction_claim: Option<Sha256InteractionClaim>,
    mdoc_window_bind_interaction_claim: MdocWindowBindInteractionClaim,
    attribute_public_digest_bind_interaction_claims: Option<Vec<PublicDigestBindInteractionClaim>>,
    ts13_revocation_range_interaction_claim: Option<MdocRevocationRangeInteractionClaim>,
    age_public: Option<predicates::PublicInput>,
    age_claimed_sums: Option<Vec<QM31>>,
    nat_public: Option<predicates::NatPublicInput>,
    nat_claimed_sums: Option<Vec<QM31>>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MdocCircuitProveProfile {
    pub total: Duration,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MdocCircuitVerifyProfile {
    pub total: Duration,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MdocProofByteBreakdown {
    pub proof_bytes: usize,
    pub stark_proof_bytes: usize,
    pub non_stark_metadata_bytes: usize,
    pub stark: MdocStarkProofByteBreakdown,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MdocStarkProofByteBreakdown {
    pub config: usize,
    pub commitments: usize,
    pub sampled_values: usize,
    pub decommitments: usize,
    pub queried_values: usize,
    pub proof_of_work: usize,
    pub fri_proof: usize,
}

pub fn mdoc_proof_byte_breakdown(proof: &MdocCircuitProof) -> MdocProofByteBreakdown {
    let stark = &proof.stark_proof.0;
    let proof_bytes = bincode_len(proof);
    let stark_proof_bytes = bincode_len(&proof.stark_proof);
    let non_stark_metadata_bytes = proof_bytes.saturating_sub(stark_proof_bytes);

    MdocProofByteBreakdown {
        proof_bytes,
        stark_proof_bytes,
        non_stark_metadata_bytes,
        stark: MdocStarkProofByteBreakdown {
            config: bincode_len(&stark.config),
            commitments: bincode_len(&stark.commitments),
            sampled_values: bincode_len(&stark.sampled_values),
            decommitments: bincode_len(&stark.decommitments),
            queried_values: bincode_len(&stark.queried_values),
            proof_of_work: bincode_len(&stark.proof_of_work),
            fri_proof: bincode_len(&stark.fri_proof),
        },
    }
}

fn bincode_len<T: Serialize>(value: &T) -> usize {
    bincode::serialize(value)
        .expect("mdoc proof byte breakdown value serializes")
        .len()
}

fn sha_params(bytes: &[u8]) -> (stwo_sha256::types::Sha256Witness, u32) {
    let witness = compute_sha256_witness(bytes);
    let log_n_rows = min_log_size(witness.blocks.len());
    (witness, log_n_rows)
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
        // Scheme discriminant + key bytes: a P-256 key and an ML-DSA key can
        // never produce the same transcript (domain separation per arm).
        match &self.inputs.revocation_public_key {
            #[cfg(feature = "p256")]
            MdocRevocationKey::Ecdsa(key) => {
                channel.mix_u64(1);
                for byte in key.x.0 {
                    channel.mix_u64(u64::from(byte));
                }
                for byte in key.y.0 {
                    channel.mix_u64(u64::from(byte));
                }
            }
            #[cfg(feature = "ml-dsa")]
            MdocRevocationKey::MlDsa(pk) => {
                channel.mix_u64(2);
                for &byte in pk {
                    channel.mix_u64(u64::from(byte));
                }
            }
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

const MDOC_REVOCATION_RANGE_LOG_SIZE: u32 = LOG_N_LANES;
const REVOCATION_U64_BYTES: usize = 8;
const REVOCATION_RANGE_BYTE_COLS: usize = 5 * REVOCATION_U64_BYTES;
const REVOCATION_RANGE_CARRY_COLS: usize = 2 * REVOCATION_U64_BYTES;
const REVOCATION_RANGE_DIGEST_TAIL_COLS: usize = 32 - REVOCATION_U64_BYTES;

fn revocation_range_bit_byte_indices(public_digest: bool, has_message: bool) -> Vec<usize> {
    let mut indices = Vec::with_capacity(REVOCATION_RANGE_BYTE_COLS);
    if !public_digest {
        indices.extend(0..REVOCATION_U64_BYTES);
    }
    if public_digest || !has_message {
        indices.extend(REVOCATION_U64_BYTES..3 * REVOCATION_U64_BYTES);
    }
    indices.extend(3 * REVOCATION_U64_BYTES..REVOCATION_RANGE_BYTE_COLS);
    indices
}

fn revocation_range_bit_cols(public_digest: bool, has_message: bool) -> usize {
    revocation_range_bit_byte_indices(public_digest, has_message).len() * 8
}

type MdocRevocationRangeColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type MdocRevocationRangeComponent = FrameworkComponent<MdocRevocationRangeEval>;

/// How the revocation-range component binds the 32-byte MSO digest.
/// (`Public` is only constructed on the ML-DSA in-STARK path; classical-only
/// builds see it as dead code.)
#[derive(Clone)]
#[allow(dead_code)]
enum MsoDigestBinding {
    /// In-circuit (P-256 mode — the MSO is private witness): the digest bytes
    /// are required from the MSO SHA module's digest relation.
    Relation(SharedDigestRelation),
    /// Host-side public (S4 ML-DSA mode): the MSO is the CBOR-navigated
    /// payload of the PUBLIC issuer Sig_structure, so BOTH sides compute
    /// `Sha256(MSO)` natively (see `mldsa_public_mso_facts`) and the
    /// in-circuit id bytes are pinned to it by constant constraints — no
    /// digest relation, no digest-tail trace columns, no MSO SHA module.
    /// The digest bytes are mixed into Fiat–Shamir by `mix_public`.
    Public([u8; 32]),
}

impl MsoDigestBinding {
    fn is_public(&self) -> bool {
        matches!(self, MsoDigestBinding::Public(_))
    }
}

/// Trace column count per (digest-binding, message-relation) mode: the digest
/// TAIL columns exist only when the digest is bound through the relation, and
/// the bit columns exist only for externally-unpinned bytes (see
/// [`revocation_range_bit_byte_indices`]).
fn revocation_range_trace_cols(public_digest: bool, has_message: bool) -> usize {
    let tail = if public_digest {
        0
    } else {
        REVOCATION_RANGE_DIGEST_TAIL_COLS
    };
    REVOCATION_RANGE_BYTE_COLS
        + revocation_range_bit_cols(public_digest, has_message)
        + REVOCATION_RANGE_CARRY_COLS
        + tail
}

struct MdocRevocationRangeBind {
    witness: Option<MdocRevocationRangeWitness>,
    mso_digest: Option<[u8; 32]>,
    epoch: Option<u32>,
    digest_binding: MsoDigestBinding,
    message_field_handle: Option<SharedFieldRelation>,
    blinder_relation: Option<ClaimedSumBlinderRelation>,
    interaction_claim: Option<MdocRevocationRangeInteractionClaim>,
    component: Option<MdocRevocationRangeComponent>,
    blinder_component: Option<FrameworkComponent<ClaimedSumBlinderEval>>,
}

/// The eval-side digest binding (relations resolved).
#[derive(Clone)]
enum RangeDigestEval {
    Relation(Box<DigestBytesRelation>),
    Public([u8; 32]),
}

#[derive(Clone)]
struct MdocRevocationRangeEval {
    digest_binding: RangeDigestEval,
    message_field_relation: Option<FieldBytesRelation>,
    epoch: u32,
    blinder_relation: ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct MdocRevocationRangeInteractionClaim {
    claimed_sum: QM31,
    /// Q-015 §4b blinder pair (see `claimed_sum_blinder`).
    blinder_v: QM31,
    blinder_m: QM31,
    blinder_claimed_sum: QM31,
}

impl MdocRevocationRangeBind {
    fn prover(
        witness: MdocRevocationRangeWitness,
        mso_digest: [u8; 32],
        digest_binding: MsoDigestBinding,
        epoch: Option<u32>,
        message_field_handle: Option<SharedFieldRelation>,
    ) -> Self {
        if let MsoDigestBinding::Public(public) = &digest_binding {
            assert_eq!(
                *public, mso_digest,
                "public MSO digest binding must match the prover's digest"
            );
        }
        Self {
            witness: Some(witness),
            mso_digest: Some(mso_digest),
            epoch,
            digest_binding,
            message_field_handle,
            blinder_relation: None,
            interaction_claim: None,
            component: None,
            blinder_component: None,
        }
    }

    fn verifier(
        digest_binding: MsoDigestBinding,
        epoch: Option<u32>,
        message_field_handle: Option<SharedFieldRelation>,
        interaction_claim: MdocRevocationRangeInteractionClaim,
    ) -> Self {
        Self {
            witness: None,
            mso_digest: None,
            epoch,
            digest_binding,
            message_field_handle,
            blinder_relation: None,
            interaction_claim: Some(interaction_claim),
            component: None,
            blinder_component: None,
        }
    }

    fn eval_digest_binding(&self) -> RangeDigestEval {
        match &self.digest_binding {
            MsoDigestBinding::Relation(handle) => RangeDigestEval::Relation(Box::new(handle.get())),
            MsoDigestBinding::Public(digest) => RangeDigestEval::Public(*digest),
        }
    }

    fn message_relation(&self) -> Option<FieldBytesRelation> {
        self.message_field_handle
            .as_ref()
            .map(|handle| handle.get())
    }

    fn interaction_claim(&self) -> &MdocRevocationRangeInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("mdoc revocation range interaction claim is set")
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

/// Base trace; `digest_tail` carries `mso_digest[8..]` in Relation mode and is
/// `None` in Public mode (the tail columns do not exist — the digest is a
/// public constant pinned in the eval).
fn revocation_range_base_trace(
    witness: &MdocRevocationRangeWitness,
    digest_tail: Option<&[u8; 32]>,
    has_message: bool,
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

    let public_digest = digest_tail.is_none();
    let mut first_row = Vec::with_capacity(revocation_range_trace_cols(public_digest, has_message));
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
    for byte_idx in revocation_range_bit_byte_indices(public_digest, has_message) {
        first_row.extend(
            byte_bits(range_bytes[byte_idx] as u8)
                .into_iter()
                .map(u32::from),
        );
    }
    first_row.extend(lower_carries.into_iter().map(u32::from));
    first_row.extend(upper_carries.into_iter().map(u32::from));
    if let Some(mso_digest) = digest_tail {
        first_row.extend(
            mso_digest[REVOCATION_U64_BYTES..]
                .iter()
                .map(|&byte| u32::from(byte)),
        );
    }
    debug_assert_eq!(
        first_row.len(),
        revocation_range_trace_cols(public_digest, has_message)
    );

    first_row
        .into_iter()
        .map(|value| {
            let mut column = vec![M31::from_u32_unchecked(0); 1 << MDOC_REVOCATION_RANGE_LOG_SIZE];
            column[0] = M31::from_u32_unchecked(value);
            mdoc_column_eval(MDOC_REVOCATION_RANGE_LOG_SIZE, column)
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn revocation_range_interaction_trace(
    witness: &MdocRevocationRangeWitness,
    mso_digest: &[u8; 32],
    digest_binding: &RangeDigestEval,
    epoch: Option<u32>,
    message_relation: Option<&FieldBytesRelation>,
    blinder_relation: &ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
) -> (Vec<MdocRevocationRangeColumnEval>, QM31) {
    let relation = match digest_binding {
        RangeDigestEval::Relation(relation) => Some(relation),
        RangeDigestEval::Public(_) => None,
    };
    let base = revocation_range_base_trace(
        witness,
        relation.is_some().then_some(mso_digest),
        message_relation.is_some(),
    );
    let active = revocation_range_active_column();
    let n_vec_rows = 1usize << (MDOC_REVOCATION_RANGE_LOG_SIZE - LOG_N_LANES);
    let digest_tail_offset = REVOCATION_RANGE_BYTE_COLS
        + revocation_range_bit_cols(relation.is_none(), message_relation.is_some())
        + REVOCATION_RANGE_CARRY_COLS;
    // Q-015 blinder `+m/(z−combine(v))`, emitted LAST (paired with the lone
    // message site in the TS13 Relation branch, its own column otherwise).
    let blinder_num = PackedQM31::broadcast(blinder_m);
    let blinder_den = crate::claimed_sum_blinder::blinder_denominator(blinder_relation, blinder_v);
    let mut logup = LogupTraceGenerator::new(MDOC_REVOCATION_RANGE_LOG_SIZE);
    if let (Some(epoch), Some(message_relation), Some(relation)) =
        (epoch, message_relation, relation)
    {
        let epoch_bytes = epoch.to_le_bytes();
        for first_lookup in (0..=TS13_REVOCATION_MESSAGE_LEN).step_by(2) {
            logup.col_from_fn(|vec_row| {
                let entry = |lookup: usize| {
                    let numerator = PackedQM31::from(active.data[vec_row]);
                    if lookup == 0 {
                        let mut values = [PackedM31::broadcast(M31::from_u32_unchecked(0)); 32];
                        for byte_idx in 0..REVOCATION_U64_BYTES {
                            values[byte_idx] = base[byte_idx].data[vec_row];
                        }
                        for byte_idx in REVOCATION_U64_BYTES..32 {
                            values[byte_idx] = base
                                [digest_tail_offset + byte_idx - REVOCATION_U64_BYTES]
                                .data[vec_row];
                        }
                        return (numerator, relation.combine(&values));
                    }

                    let byte_idx = lookup - 1;
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
                };
                let (left_num, left_den) = entry(first_lookup);
                if first_lookup == TS13_REVOCATION_MESSAGE_LEN {
                    // Pair the lone last message site with the blinder.
                    return (
                        left_num * blinder_den + blinder_num * left_den,
                        left_den * blinder_den,
                    );
                }
                let (right_num, right_den) = entry(first_lookup + 1);
                (
                    left_num * right_den + right_num * left_den,
                    left_den * right_den,
                )
            });
        }
    } else if let (Some(epoch), Some(message_relation)) = (epoch, message_relation) {
        // Public-digest TS13 branch (S4): the digest has NO LogUp site (it is
        // pinned to public constants in the eval), so the 20 message sites
        // pair among themselves and the blinder takes its own column.
        let epoch_bytes = epoch.to_le_bytes();
        for first_lookup in (0..TS13_REVOCATION_MESSAGE_LEN).step_by(2) {
            logup.col_from_fn(|vec_row| {
                let entry = |byte_idx: usize| {
                    let numerator = -PackedQM31::from(active.data[vec_row]);
                    let value = match byte_idx {
                        0..=7 => base[REVOCATION_U64_BYTES + byte_idx].data[vec_row],
                        8..=15 => base[2 * REVOCATION_U64_BYTES + byte_idx - 8].data[vec_row],
                        _ => PackedM31::broadcast(M31::from_u32_unchecked(u32::from(
                            epoch_bytes[byte_idx - 16],
                        ))),
                    };
                    let denominator: PackedQM31 = message_relation.combine(&[
                        PackedM31::broadcast(M31::from_u32_unchecked(HOSTED_MSG_FIELD_ID)),
                        PackedM31::broadcast(M31::from_u32_unchecked(byte_idx as u32)),
                        value,
                    ]);
                    (numerator, denominator)
                };
                let (left_num, left_den) = entry(first_lookup);
                let (right_num, right_den) = entry(first_lookup + 1);
                (
                    left_num * right_den + right_num * left_den,
                    left_den * right_den,
                )
            });
        }
        logup.col_from_fn(|_| (blinder_num, blinder_den));
    } else {
        if let Some(relation) = relation {
            logup.col_from_fn(|vec_row| {
                let numerator = PackedQM31::from(active.data[vec_row]);
                let mut values = [PackedM31::broadcast(M31::from_u32_unchecked(0)); 32];
                for byte_idx in 0..REVOCATION_U64_BYTES {
                    values[byte_idx] = base[byte_idx].data[vec_row];
                }
                for byte_idx in REVOCATION_U64_BYTES..32 {
                    values[byte_idx] =
                        base[digest_tail_offset + byte_idx - REVOCATION_U64_BYTES].data[vec_row];
                }
                let denominator = relation.combine(&values);
                (numerator, denominator)
            });
        }
        logup.col_from_fn(|_| (blinder_num, blinder_den));
    }
    debug_assert_eq!(n_vec_rows, 1);
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

        let public_digest = matches!(self.digest_binding, RangeDigestEval::Public(_));
        let has_message = self.message_field_relation.is_some();
        let values: Vec<E::F> = (0..revocation_range_trace_cols(public_digest, has_message))
            .map(|_| eval.next_trace_mask())
            .collect();
        for value in &values {
            eval.add_constraint((one.clone() - active.clone()) * value.clone());
        }

        // Bit-pin exactly the externally-unpinned bytes (see
        // `revocation_range_bit_byte_indices` for the per-byte exemptions).
        for (slot, byte_idx) in revocation_range_bit_byte_indices(public_digest, has_message)
            .into_iter()
            .enumerate()
        {
            let byte = values[byte_idx].clone();
            let bits = &values[REVOCATION_RANGE_BYTE_COLS + slot * 8
                ..REVOCATION_RANGE_BYTE_COLS + (slot + 1) * 8];
            for bit in bits {
                eval.add_constraint(bit.clone() * (bit.clone() - one.clone()));
            }
            eval.add_constraint(active.clone() * (byte - byte_from_bits::<E>(bits)));
        }

        let lower_carries_offset =
            REVOCATION_RANGE_BYTE_COLS + revocation_range_bit_cols(public_digest, has_message);
        let upper_carries_offset = lower_carries_offset + REVOCATION_U64_BYTES;
        for carry in &values[lower_carries_offset..upper_carries_offset + REVOCATION_U64_BYTES] {
            eval.add_constraint(carry.clone() * (carry.clone() - one.clone()));
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

        match &self.digest_binding {
            RangeDigestEval::Relation(mso_digest_relation) => {
                let digest_tail_offset = upper_carries_offset + REVOCATION_U64_BYTES;
                let mut digest_values = Vec::with_capacity(32);
                digest_values.extend(values.iter().take(REVOCATION_U64_BYTES).cloned());
                for byte_idx in 0..REVOCATION_RANGE_DIGEST_TAIL_COLS {
                    digest_values.push(values[digest_tail_offset + byte_idx].clone());
                }
                eval.add_to_relation(RelationEntry::new(
                    mso_digest_relation.as_ref(),
                    E::EF::from(active.clone()),
                    &digest_values,
                ));
            }
            RangeDigestEval::Public(digest) => {
                // S4: the revocation id bytes are the first 8 bytes of the
                // PUBLIC `Sha256(MSO)` (both sides compute it natively; the
                // bytes are FS-mixed in `mix_public`) — pin them as constants.
                for byte_idx in 0..REVOCATION_U64_BYTES {
                    eval.add_constraint(
                        active.clone()
                            * (values[byte_idx].clone()
                                - m31_const::<E>(u32::from(digest[byte_idx]))),
                    );
                }
            }
        }
        if let Some(message_relation) = &self.message_field_relation {
            let field_id = m31_const::<E>(if public_digest {
                HOSTED_MSG_FIELD_ID
            } else {
                MDOC_REVOCATION_MESSAGE_FIELD_ID
            });
            for byte_idx in 0..TS13_REVOCATION_MESSAGE_LEN {
                let value = match byte_idx {
                    0..=7 => values[REVOCATION_U64_BYTES + byte_idx].clone(),
                    8..=15 => values[2 * REVOCATION_U64_BYTES + byte_idx - 8].clone(),
                    _ => m31_const::<E>(u32::from(self.epoch.to_le_bytes()[byte_idx - 16])),
                };
                eval.add_to_relation(RelationEntry::new(
                    message_relation,
                    if public_digest {
                        -E::EF::from(active.clone())
                    } else {
                        E::EF::from(active.clone())
                    },
                    &[field_id.clone(), m31_const::<E>(byte_idx as u32), value],
                ));
            }
            // Q-015 blinder `+m/(z−combine(v))`, ungated, emitted LAST to
            // match the generator's pairing of the lone message site.
            add_blinder_relation_entry(
                &mut eval,
                &self.blinder_relation,
                self.blinder_v,
                self.blinder_m,
                false,
            );
            eval.finalize_logup_in_pairs();
        } else {
            add_blinder_relation_entry(
                &mut eval,
                &self.blinder_relation,
                self.blinder_v,
                self.blinder_m,
                false,
            );
            eval.finalize_logup();
        }
        eval
    }
}

impl Air for MdocRevocationRangeBind {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(0x5453_3133_524e_4701);
        // Public-digest mode (S4): the digest bytes are part of the public
        // statement — mix them so the constant pins are FS-bound fail-closed.
        if let MsoDigestBinding::Public(digest) = &self.digest_binding {
            channel.mix_u64(1);
            for &byte in digest {
                channel.mix_u64(u64::from(byte));
            }
        }
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        if let Some(handle) = &self.message_field_handle {
            // On the quantum path this component is the field-byte provider;
            // legacy SHA providers have already populated the same handle.
            if !handle.is_set() {
                handle.set(FieldBytesRelation::draw(channel));
            }
        }
        self.blinder_relation = Some(ClaimedSumBlinderRelation::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        let public = self.digest_binding.is_public();
        // Main component columns plus the counterpart component column.
        // Relation + message: digest site pairs with message sites, the lone
        // last message site pairs with the blinder. Public + message: the 20
        // message sites pair among themselves, blinder alone. Digest-only:
        // digest (Relation only) + blinder each take a column.
        let interaction_cols = match (self.message_field_handle.is_some(), public) {
            (true, false) => {
                ((2 + TS13_REVOCATION_MESSAGE_LEN).div_ceil(2) + 1) * SECURE_EXTENSION_DEGREE
            }
            (true, true) => (TS13_REVOCATION_MESSAGE_LEN.div_ceil(2) + 2) * SECURE_EXTENSION_DEGREE,
            (false, false) => 3 * SECURE_EXTENSION_DEGREE,
            (false, true) => 2 * SECURE_EXTENSION_DEGREE,
        };
        TreeLayout {
            preprocessed: vec![MDOC_REVOCATION_RANGE_LOG_SIZE],
            trace: vec![
                MDOC_REVOCATION_RANGE_LOG_SIZE;
                revocation_range_trace_cols(public, self.message_field_handle.is_some())
            ],
            interaction: vec![MDOC_REVOCATION_RANGE_LOG_SIZE; interaction_cols],
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        let claim = self.interaction_claim();
        vec![claim.claimed_sum, claim.blinder_claimed_sum]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        vec![revocation_range_active_id()]
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let claim = self.interaction_claim().clone();
        let blinder_relation = self
            .blinder_relation
            .clone()
            .expect("mdoc revocation range blinder relation drawn before components");
        self.component = Some(MdocRevocationRangeComponent::new(
            allocator,
            MdocRevocationRangeEval {
                digest_binding: self.eval_digest_binding(),
                message_field_relation: self.message_relation(),
                epoch: self.epoch.unwrap_or(0),
                blinder_relation: blinder_relation.clone(),
                blinder_v: claim.blinder_v,
                blinder_m: claim.blinder_m,
            },
            claim.claimed_sum,
        ));
        self.blinder_component = Some(FrameworkComponent::new(
            allocator,
            ClaimedSumBlinderEval {
                log_size: MDOC_REVOCATION_RANGE_LOG_SIZE,
                relation: blinder_relation,
                v: claim.blinder_v,
                m: claim.blinder_m,
            },
            claim.blinder_claimed_sum,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![
            self.component
                .as_ref()
                .expect("mdoc revocation range component is built"),
            self.blinder_component
                .as_ref()
                .expect("mdoc revocation range blinder component is built"),
        ]
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
        let digest_tail = (!self.digest_binding.is_public()).then(|| {
            *self
                .mso_digest
                .as_ref()
                .expect("mdoc revocation range MSO digest is set")
        });
        tb.extend_evals(revocation_range_base_trace(
            self.witness
                .as_ref()
                .expect("mdoc revocation range witness is set"),
            digest_tail.as_ref(),
            self.message_field_handle.is_some(),
        ));
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let blinder_v = random_qm31();
        let blinder_m = random_qm31();
        let blinder_relation = self
            .blinder_relation
            .clone()
            .expect("mdoc revocation range blinder relation drawn before interaction");
        let (trace, claimed_sum) = revocation_range_interaction_trace(
            self.witness
                .as_ref()
                .expect("mdoc revocation range witness is set"),
            self.mso_digest
                .as_ref()
                .expect("mdoc revocation range MSO digest is set"),
            &self.eval_digest_binding(),
            self.epoch,
            self.message_relation().as_ref(),
            &blinder_relation,
            blinder_v,
            blinder_m,
        );
        tb.extend_evals(trace);
        let (blinder_trace, blinder_claimed_sum) = blinder_counter_interaction(
            MDOC_REVOCATION_RANGE_LOG_SIZE,
            &blinder_relation,
            blinder_v,
            blinder_m,
        );
        tb.extend_evals(blinder_trace);
        self.interaction_claim = Some(MdocRevocationRangeInteractionClaim {
            claimed_sum,
            blinder_v,
            blinder_m,
            blinder_claimed_sum,
        });
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            self.component
                .as_ref()
                .expect("mdoc revocation range component is built"),
            self.blinder_component
                .as_ref()
                .expect("mdoc revocation range blinder component is built"),
        ]
    }
}

#[cfg(feature = "ec-coprocessor")]
struct MdocCoprocessorBindingProver {
    issuer_input: EcdsaVerifyInput,
    device_input: EcdsaVerifyInput,
    issuer_witness: eu_id_ec_coprocessor::ecdsa::Witness,
    device_witness: eu_id_ec_coprocessor::ecdsa::Witness,
    mac_key_shares: eu_id_ec_coprocessor::ecdsa::MdocP4bMacKeyShares,
    mac_state: MdocP4bMacSharedState,
    bundle: Option<eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle>,
    profile: Option<eu_id_ec_coprocessor::ecdsa::MdocP4bProveProfile>,
}

#[cfg(feature = "ec-coprocessor")]
fn random_mdoc_p4b_mac_key_shares() -> eu_id_ec_coprocessor::ecdsa::MdocP4bMacKeyShares {
    eu_id_ec_coprocessor::ecdsa::MdocP4bMacKeyShares(std::array::from_fn(|_| {
        let mut share = [0u8; 16];
        OsRng.fill_bytes(&mut share);
        share
    }))
}

#[cfg(feature = "ec-coprocessor")]
impl MdocCoprocessorBindingProver {
    fn new(
        issuer_input: EcdsaVerifyInput,
        device_input: EcdsaVerifyInput,
        mac_key_shares: eu_id_ec_coprocessor::ecdsa::MdocP4bMacKeyShares,
        mac_state: MdocP4bMacSharedState,
    ) -> Result<Self, Error> {
        let issuer_witness = crate::ec_coprocessor::generate_witness_from_stwo(&issuer_input)
            .map_err(Error::CoprocessorWitness)?;
        let device_witness = crate::ec_coprocessor::generate_witness_from_stwo(&device_input)
            .map_err(Error::CoprocessorWitness)?;
        Ok(Self {
            issuer_input,
            device_input,
            issuer_witness,
            device_witness,
            mac_key_shares,
            mac_state,
            bundle: None,
            profile: None,
        })
    }
}

#[cfg(feature = "ec-coprocessor")]
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

#[cfg(feature = "ec-coprocessor")]
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
        crate::mix_coprocessor_tagged_projections(
            channel,
            &[
                (b"issuer".as_slice(), &issuer_projection),
                (b"device".as_slice(), &device_projection),
            ],
        )
        .expect("mdoc coprocessor public projections mix");
        let seed = crate::draw_coprocessor_seed(channel);
        let (bundle, profile) =
            crate::ec_coprocessor::prove_mdoc_p4b_circuit_bundle_from_stwo_profiled(
                &self.issuer_input,
                &issuer_projection,
                &self.issuer_witness,
                &self.device_input,
                &device_projection,
                &self.device_witness,
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
        self.profile = Some(profile);
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        Vec::new()
    }
}

#[cfg(feature = "ec-coprocessor")]
struct MdocCoprocessorBindingVerifier {
    issuer_input: EcdsaVerifyInput,
    device_input: EcdsaVerifyInput,
    bundle: eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle,
    mac_state: MdocP4bMacSharedState,
    profile: Option<eu_id_ec_coprocessor::ecdsa::MdocP4bVerifyProfile>,
}

#[cfg(feature = "ec-coprocessor")]
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
        crate::mix_coprocessor_tagged_projections(
            channel,
            &[
                (b"issuer".as_slice(), &issuer_projection),
                (b"device".as_slice(), &device_projection),
            ],
        )
        .map_err(VerificationError::InvalidStructure)?;
        let seed = crate::draw_coprocessor_seed(channel);
        let profile = crate::ec_coprocessor::verify_mdoc_p4b_circuit_bundle_from_stwo_profiled(
            &issuer_projection,
            &device_projection,
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
        self.profile = Some(profile);
        Ok(())
    }
}

pub fn prove_mdoc_circuit(
    extracted: &ExtractedPidMdoc,
    statement: &MdocCircuitStatement,
) -> Result<MdocCircuitProof, Error> {
    prove_mdoc_circuit_with_pcs_config(extracted, statement, mdoc_production_pcs_config())
}

/// What [`prove_or_root_mdoc`] should do once the module set is assembled: run
/// the full STARK, or stop at the tree-0 (preprocessed) commit and return its
/// root (the F-ROOT pin path).
enum MdocProveMode {
    Prove,
    PreprocessedRoot,
}

/// The two possible outcomes of [`prove_or_root_mdoc`], one per [`MdocProveMode`].
enum MdocProveOutcome {
    Proof(Box<MdocCircuitProof>),
    Root(air_core::CommitmentRoot),
}

/// Compute the expected tree-0 (preprocessed) commitment root for an mdoc
/// statement, by assembling the exact same prover-side [`air_core::AirProver`]
/// module set (in the exact commit order) [`prove_mdoc_circuit_with_pcs_config`]
/// uses and running only the prover's tree-0 commit path
/// ([`air_core::compute_preprocessed_root`]) — no STARK is proven. Pass the
/// result to [`verify_mdoc_circuit_with_preprocessed_root`]; the root is
/// recomputed from the public statement + witness, never taken from the proof.
///
/// # Soundness
///
/// This Blake2s Merkle root — not the prover-side 64-bit `DefaultHasher` column
/// fingerprint — is the tree-0 soundness pin (F-ROOT class): it binds the
/// contents, order, and sizes of every preprocessed range table, SHA/keccak
/// schedule, and constant column at once. A proof carrying a forged
/// preprocessed tree is rejected with [`Error::PreprocessedRootMismatch`]
/// before any STARK work. Do not downgrade the pin to the fingerprint.
pub fn mdoc_expected_preprocessed_root(
    extracted: &ExtractedPidMdoc,
    statement: &MdocCircuitStatement,
    config: PcsConfig,
) -> Result<air_core::CommitmentRoot, Error> {
    match prove_or_root_mdoc(
        extracted,
        statement,
        config,
        MdocProveMode::PreprocessedRoot,
    )? {
        MdocProveOutcome::Root(root) => Ok(root),
        MdocProveOutcome::Proof(_) => unreachable!("PreprocessedRoot mode never returns a proof"),
    }
}

pub fn prove_mdoc_circuit_with_pcs_config(
    extracted: &ExtractedPidMdoc,
    statement: &MdocCircuitStatement,
    config: PcsConfig,
) -> Result<MdocCircuitProof, Error> {
    match prove_or_root_mdoc(extracted, statement, config, MdocProveMode::Prove)? {
        MdocProveOutcome::Proof(proof) => Ok(*proof),
        MdocProveOutcome::Root(_) => unreachable!("Prove mode never returns a root"),
    }
}

fn prove_or_root_mdoc(
    extracted: &ExtractedPidMdoc,
    statement: &MdocCircuitStatement,
    config: PcsConfig,
    mode: MdocProveMode,
) -> Result<MdocProveOutcome, Error> {
    if statement.birth_date_value_offset != extracted.birth_date_value_offset
        || statement.nationality_value_offset != extracted.nationality_value_offset
    {
        return Err(Error::Prove(
            "mdoc statement offsets do not match extracted witness".to_string(),
        ));
    }
    if !auth_inputs_equal(&statement.issuer_input, &extracted.issuer_auth_input)
        || !auth_inputs_equal(&statement.device_input, &extracted.device_auth_input)
    {
        return Err(Error::AuthInputMismatch);
    }
    // Host-side checks mirror the verifier and run before any STARK work.
    check_mldsa_device_key_binding(statement)?;
    let mldsa_mso_facts = mldsa_public_mso_facts(statement)?;
    check_mldsa_extracted_statement_coherence(extracted, statement)?;
    // Issuer, device, and revocation messages are absorbed directly by hosted
    // ML-DSA modules. SHA-256 remains only for ISO mdoc attribute digests.
    let revocation_message = match (
        &statement.ts13_revocation_signature,
        &statement.ts13_revocation,
        &statement.ts13_revocation_range,
    ) {
        (Some(_), Some(revocation), Some(range)) => Some(ts13_revocation_message_bytes(
            range.id_lo,
            range.id_hi,
            revocation.epoch,
        )),
        _ => None,
    };
    let attribute_items: Vec<_> = extracted
        .extracted_attributes
        .iter()
        .map(|attribute| attribute.item.as_slice())
        .collect();
    let attribute_sha_params: Vec<_> = attribute_items
        .iter()
        .map(|item| sha_params(item))
        .collect();
    let shared_sha_log = attribute_sha_params
        .iter()
        .map(|(_, log)| *log)
        .max()
        .expect("sha log list is non-empty (attributes are 1..=4)");
    // Fully post-quantum composition: the remaining format-required attribute
    // SHA consumers merge into one multi-slot instance. Revocation is not a
    // SHA slot; its range AIR directly provides the raw signed message.
    // See tasks/sha-multimessage-design.md.
    let attribute_digests: Vec<_> = (0..attribute_sha_params.len())
        .map(|_| SharedDigestRelation::new())
        .collect();
    // The proof-wide keccak service's relations handle (S1): drawn ONCE by the
    // service module, consumed by every hosted ML-DSA instance.
    let mldsa_keccak_handle = SharedKeccakRelations::new();
    let revocation_message_field = statement
        .ts13_revocation_signature
        .as_ref()
        .map(|_| SharedFieldRelation::new());
    let attribute_fields: Vec<_> = (0..attribute_sha_params.len())
        .map(|_| SharedFieldRelation::new())
        .collect();
    let sha_table_relations = SharedShaTableRelations::new();
    let attribute_exposures: Vec<_> = (0..statement.attributes.len())
        .map(|index| attribute_exposure(statement, index))
        .collect();

    let sha_consumers: Vec<_> = attribute_sha_params
        .iter()
        .zip(&attribute_exposures)
        .map(|((witness, _), exposure)| (witness, exposure.clone()))
        .collect();
    let sha_table_multiplicities = ShaTableMultiplicities::from_consumers(&sha_consumers);
    let mut sha_tables =
        ShaTablesProver::new(sha_table_multiplicities, sha_table_relations.clone());
    // Hosted in-circuit ML-DSA statement (M7/S4): the issuer Sig_structure is
    // PUBLIC, so the instance runs in public-message mode — its in-module
    // producer feeds the µ-absorption directly (no shared-field msg bridge).
    let mut issuer_mldsa = statement
        .issuer_input
        .as_mldsa()
        .map(|input| -> Result<MlDsaStatementProver, Error> {
            let witness = stwo_mldsa::witness::generate_witness(input)
                .map_err(|error| Error::Prove(format!("mldsa witness: {error:?}")))?;
            Ok(MlDsaStatementProver::hosted_public(
                witness,
                input.clone(),
                mldsa_keccak_handle.clone(),
            )
            .with_instance_namespace(MDOC_ISSUER_MLDSA_NAMESPACE)
            .with_stream_base(MDOC_ISSUER_MLDSA_STREAM_BASE))
        })
        .transpose()?;
    // Hosted in-circuit ML-DSA device statement, public-message mode (S4).
    let mut device_mldsa = statement
        .device_input
        .as_mldsa()
        .map(|input| -> Result<MlDsaStatementProver, Error> {
            let witness = stwo_mldsa::witness::generate_witness(input)
                .map_err(|error| Error::Prove(format!("mldsa device witness: {error:?}")))?;
            Ok(MlDsaStatementProver::hosted_public(
                witness,
                input.clone(),
                mldsa_keccak_handle.clone(),
            )
            .with_instance_namespace(MDOC_DEVICE_MLDSA_NAMESPACE)
            .with_stream_base(MDOC_DEVICE_MLDSA_STREAM_BASE))
        })
        .transpose()?;
    // Hosted in-circuit ML-DSA revocation statement, private-message mode: the
    // prover's input carries the REAL 20-byte message (from the private range
    // witness); only its LENGTH is mixed into the transcript.
    let mut revocation_mldsa = revocation_message
        .as_ref()
        .map(|message| ts13_revocation_mldsa_input(statement, message.to_vec()))
        .transpose()?
        .flatten()
        .map(|input| -> Result<MlDsaStatementProver, Error> {
            let witness = stwo_mldsa::witness::generate_witness(&input)
                .map_err(|error| Error::Prove(format!("mldsa revocation witness: {error:?}")))?;
            Ok(MlDsaStatementProver::hosted(
                witness,
                *input,
                revocation_message_field
                    .clone()
                    .expect("revocation field relation exists with a revocation signature"),
                mldsa_keccak_handle.clone(),
            )
            .with_instance_namespace(MDOC_REVOCATION_MLDSA_NAMESPACE)
            .with_stream_base(MDOC_REVOCATION_MLDSA_STREAM_BASE)
            .with_private_message())
        })
        .transpose()?;
    // The ONE proof-wide keccak service (S1): built from the concatenated
    // sponge jobs of every present hosted ML-DSA instance, in fixed role order
    // (issuer, device, revocation) — the verifier rebuilds the same list from
    // public data. Present iff any instance is. Composed BEFORE the first
    // instance in module order so its `draw_relations` publishes the shared
    // keccak relations every consumer draws.
    let mut mldsa_keccak_service = {
        let mut shapes = Vec::new();
        let mut streams = Vec::new();
        for prover in [&issuer_mldsa, &device_mldsa, &revocation_mldsa]
            .into_iter()
            .flatten()
        {
            let (job_shapes, job_streams) = prover.keccak_jobs();
            shapes.extend(job_shapes);
            streams.extend(job_streams);
        }
        (!shapes.is_empty())
            .then(|| KeccakServiceProver::new(shapes, streams, mldsa_keccak_handle.clone()))
    };
    // Merged multi-slot SHA consumer. In the quantum composition its slots are
    // exactly the hidden attributes; the legacy revocation slot is absent.
    let merged_sha_config = MultiSlotConfig::new(
        shared_sha_log,
        attribute_exposures
            .iter()
            .cloned()
            .map(|field_exposure| SlotSpec {
                expose_digest: true,
                field_exposure,
            })
            .collect(),
    );
    let merged_sha_log_n_rows = merged_sha_config.min_log_n_rows();
    let mut merged_sha = {
        let witnesses = attribute_sha_params
            .iter()
            .map(|(witness, _)| witness)
            .collect();
        let mut prover = Sha256MultiProver::new(
            witnesses,
            merged_sha_log_n_rows,
            merged_sha_config,
            sha_table_relations.clone(),
        );
        for index in 0..attribute_sha_params.len() {
            prover = prover
                .with_slot_digest_handle(index, attribute_digests[index].clone())
                .with_slot_field_handle(index, attribute_fields[index].clone());
        }
        prover
    };

    let mut mdoc_window_bind = MdocWindowBind::new_for_attributes(
        mdoc_window_bind_rows_from(statement, None),
        attribute_fields.clone(),
    );
    // S4 ML-DSA: attribute digests bind to the PUBLIC `valueDigests` values
    // (host-derived facts) instead of the window-bind digest rows; validity is
    // a host-side check over the public MSO windows.
    let mut attribute_public_digest_binds: Vec<PublicDigestBind> = match &mldsa_mso_facts {
        Some(facts) => facts
            .attribute_digests
            .iter()
            .zip(attribute_digests.iter())
            .map(|(digest, handle)| PublicDigestBind::new(*digest, handle.clone()))
            .collect(),
        None => Vec::new(),
    };
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
        nationalities: vec![statement.nationality_binding.code()],
    };
    let mut age = if let Some(index) = statement.age_attribute_index {
        let age = AgeRangeCheck::new(PcsConfig::default())
            .prover(&age_public, &age_dob)
            .map_err(Error::AgePrepare)?;
        Some(match statement.birth_date_binding {
            MdocBirthDateBinding::Packed(_) => {
                age.with_dob_binding(attribute_fields[index].clone())
            }
            MdocBirthDateBinding::Text(_) => {
                age.with_text_dob_binding(attribute_fields[index].clone())
            }
        })
    } else {
        None
    };
    let mut nat = if let Some(index) = statement.nationality_attribute_index {
        Some(
            NationalityPredicate::new(PcsConfig::default())
                .prover(&nat_public, &nat_private)
                .map_err(Error::NatPrepare)?
                .with_nat_binding(attribute_fields[index].clone()),
        )
    } else {
        None
    };
    let mut ts13_revocation_public = statement
        .ts13_revocation
        .clone()
        .map(MdocRevocationPublicBind::new);
    let mut ts13_revocation_range = statement.ts13_revocation_range.clone().map(|range| {
        let mso_digest_bytes: [u8; 32] = Sha256::digest(&extracted.mso).into();
        // S4 ML-DSA: the digest is PUBLIC (host-derived from the public
        // Sig_structure payload) — the in-circuit id bytes pin to it as
        // constants; no MSO SHA module / digest relation exists.
        let digest_binding = MsoDigestBinding::Public(
            mldsa_mso_facts
                .as_ref()
                .expect("quantum-safe statements always expose ML-DSA MSO facts")
                .mso_digest,
        );
        MdocRevocationRangeBind::prover(
            range,
            mso_digest_bytes,
            digest_binding,
            statement
                .ts13_revocation
                .as_ref()
                .map(|revocation| revocation.epoch)
                .filter(|_| statement.ts13_revocation_signature.is_some()),
            revocation_message_field.clone(),
        )
    });

    let stark_proof = {
        // The keccak service draws shared relations before every hosted ML-DSA
        // consumer. The range AIR publishes the private revocation message
        // before the revocation verifier consumes it.
        let mut modules: Vec<&mut dyn AirProver> = vec![&mut sha_tables];
        if let Some(service) = mldsa_keccak_service.as_mut() {
            modules.push(service);
        }
        if let Some(issuer) = issuer_mldsa.as_mut() {
            modules.push(issuer);
        }
        if let Some(device) = device_mldsa.as_mut() {
            modules.push(device);
        }
        modules.push(&mut merged_sha);
        // Quantum revocation: the range AIR owns and publishes the private
        // message relation, so it must draw that handle before the hosted
        // ML-DSA bridge reads it.
        if let Some(revocation_range) = ts13_revocation_range.as_mut() {
            modules.push(revocation_range);
        }
        if let Some(revocation_mldsa) = revocation_mldsa.as_mut() {
            modules.push(revocation_mldsa);
        }
        // S4 ML-DSA: per-attribute PUBLIC digest binds, right after their SHA
        // providers (mirror on verify).
        for bind in &mut attribute_public_digest_binds {
            modules.push(bind);
        }
        modules.push(&mut mdoc_window_bind);
        if let Some(age) = age.as_mut() {
            modules.push(age);
        }
        if let Some(nat) = nat.as_mut() {
            modules.push(nat);
        }
        if let Some(revocation_public) = ts13_revocation_public.as_mut() {
            modules.push(revocation_public);
        }
        // Root mode stops at the tree-0 commit — no STARK, no proof. This
        // returns before the borrow of `modules` (and the components it holds)
        // is used to read back interaction claims, so the two paths never
        // conflict on those borrows.
        match mode {
            MdocProveMode::PreprocessedRoot => {
                // UNCACHED: the ML-DSA `sampleinball` schedule preprocessed
                // columns depend on the witness through `stream_len(witness)`
                // (the SIB squeeze length), which varies per signature while the
                // padded `sib_log_size` shape key stays fixed — so the per-shape
                // cache would return the first signature's root for a second,
                // distinct one (spurious PreprocessedRootMismatch). Same reason
                // the standalone stwo-mldsa helper uses `_uncached`.
                return Ok(MdocProveOutcome::Root(
                    air_core::compute_preprocessed_root_uncached(modules.as_mut_slice(), config),
                ));
            }
            MdocProveMode::Prove => air_core::prove(modules.as_mut_slice(), config)
                .map_err(|e| Error::Prove(format!("{e:?}")))?,
        }
    };
    Ok(MdocProveOutcome::Proof(Box::new(MdocCircuitProof {
        stark_proof,
        sha_tables_interaction_claim: sha_tables.interaction_claim().clone(),
        mldsa: issuer_mldsa.as_ref().map(MdocMlDsaClaims::from_prover),
        device_mldsa: device_mldsa.as_ref().map(MdocMlDsaClaims::from_prover),
        revocation_mldsa: revocation_mldsa.as_ref().map(MdocMlDsaClaims::from_prover),
        keccak_service_claimed_sums: mldsa_keccak_service
            .as_ref()
            .map(|service| service.claimed_sums()),
        merged_sha_log_n_rows: Some(merged_sha_log_n_rows),
        merged_sha_slot_log: Some(shared_sha_log),
        merged_sha_interaction_claim: Some(merged_sha.interaction_claim().clone()),
        mdoc_window_bind_interaction_claim: mdoc_window_bind.interaction_claim().clone(),
        attribute_public_digest_bind_interaction_claims: Some({
            attribute_public_digest_binds
                .iter()
                .map(|bind| bind.interaction_claim().clone())
                .collect()
        }),
        ts13_revocation_range_interaction_claim: ts13_revocation_range
            .as_ref()
            .map(|range| range.interaction_claim().clone()),
        age_public: age.as_ref().map(|_| age_public),
        // Q-015 §4b: no blinder pair on the age/nat predicate sums. The
        // verifier RECOMPUTES these from the public statement (that is the
        // public-binding fix), so a blinder term here would either break the
        // recomputation or have to live in a verifier-recomputed public sum,
        // which the pair rules forbid.
        age_claimed_sums: age.as_ref().map(|age| age.claimed_sums()),
        nat_public: nat.as_ref().map(|_| nat_public),
        nat_claimed_sums: nat.as_ref().map(|nat| nat.claimed_sums()),
    })))
}

pub fn verify_mdoc_circuit(
    proof: &MdocCircuitProof,
    statement: &MdocCircuitStatement,
) -> Result<(), Error> {
    verify_mdoc_circuit_with_pcs_config(proof, statement, mdoc_production_pcs_config())
}

#[cfg(feature = "ec-coprocessor")]
pub fn verify_mdoc_public_statement(
    proof: &MdocCircuitProof,
    statement: &MdocPublicStatement,
) -> Result<(), Error> {
    let verifier_statement = statement.verifier_circuit_statement();
    verify_mdoc_circuit_with_pcs_config(proof, &verifier_statement, mdoc_production_pcs_config())
}

pub fn verify_mdoc_circuit_with_pcs_config(
    proof: &MdocCircuitProof,
    statement: &MdocCircuitStatement,
    expected_pcs_config: PcsConfig,
) -> Result<(), Error> {
    verify_mdoc_circuit_with_pcs_config_profiled(proof, statement, expected_pcs_config, None)
        .map(|_| ())
}

/// [`verify_mdoc_circuit`], with the tree-0 (preprocessed) commitment root
/// pinned — the F-ROOT fix. The caller supplies `expected_preprocessed_root`,
/// computed once via [`mdoc_expected_preprocessed_root`], never taken from the
/// proof. A proof carrying a forged preprocessed tree (SHA/keccak schedules,
/// range tables, constants) is rejected with
/// [`Error::PreprocessedRootMismatch`] before the STARK check. Mirrors
/// `verify_identity_with_preprocessed_root`.
pub fn verify_mdoc_circuit_with_preprocessed_root(
    proof: &MdocCircuitProof,
    statement: &MdocCircuitStatement,
    expected_preprocessed_root: air_core::CommitmentRoot,
) -> Result<(), Error> {
    verify_mdoc_circuit_with_pcs_config_and_preprocessed_root(
        proof,
        statement,
        mdoc_production_pcs_config(),
        expected_preprocessed_root,
    )
}

pub fn verify_mdoc_circuit_with_pcs_config_and_preprocessed_root(
    proof: &MdocCircuitProof,
    statement: &MdocCircuitStatement,
    expected_pcs_config: PcsConfig,
    expected_preprocessed_root: air_core::CommitmentRoot,
) -> Result<(), Error> {
    verify_mdoc_circuit_with_pcs_config_profiled_impl(
        proof,
        statement,
        expected_pcs_config,
        Some(expected_preprocessed_root),
    )
    .map(|_| ())
}

pub fn verify_mdoc_circuit_with_pcs_config_profiled(
    proof: &MdocCircuitProof,
    statement: &MdocCircuitStatement,
    expected_pcs_config: PcsConfig,
    expected_preprocessed_root: Option<air_core::CommitmentRoot>,
) -> Result<MdocCircuitVerifyProfile, Error> {
    verify_mdoc_circuit_with_pcs_config_profiled_impl(
        proof,
        statement,
        expected_pcs_config,
        expected_preprocessed_root,
    )
}

fn verify_mdoc_circuit_with_pcs_config_profiled_impl(
    proof: &MdocCircuitProof,
    statement: &MdocCircuitStatement,
    expected_pcs_config: PcsConfig,
    expected_preprocessed_root: Option<air_core::CommitmentRoot>,
) -> Result<MdocCircuitVerifyProfile, Error> {
    let total_start = Instant::now();
    check_mldsa_device_key_binding(statement)?;
    let mldsa_mso_facts = mldsa_public_mso_facts(statement)?;
    match &proof.mldsa {
        Some(claims) if claims.has_expected_shape() => {}
        _ => {
            return Err(Error::Verify(
                "mdoc proof ML-DSA issuer claim tree has the wrong shape".to_string(),
            ))
        }
    }
    match &proof.device_mldsa {
        Some(claims) if claims.has_expected_shape() => {}
        _ => {
            return Err(Error::Verify(
                "mdoc proof ML-DSA device claim tree has the wrong shape".to_string(),
            ))
        }
    }
    if proof.age_public
        != statement
            .age_attribute_index
            .map(|_| statement.policy.age_public_input())
    {
        return Err(Error::AgePolicyMismatch);
    }
    if proof.nat_public
        != statement
            .nationality_attribute_index
            .map(|_| nat_public_input_for(statement))
    {
        return Err(Error::NatPolicyMismatch);
    }

    let has_revocation_range = statement.ts13_revocation_range.is_some();
    let has_revocation_signature = statement.ts13_revocation_signature.is_some();
    if proof.ts13_revocation_range_interaction_claim.is_some() != has_revocation_range {
        return Err(Error::Verify(
            "mdoc proof revocation layout mismatch".to_string(),
        ));
    }
    if proof.merged_sha_log_n_rows.is_none()
        || proof.merged_sha_slot_log.is_none()
        || proof.merged_sha_interaction_claim.is_none()
    {
        return Err(Error::Verify(
            "mdoc proof merged SHA layout does not match the statement".to_string(),
        ));
    }
    // Sanity-bound the proof-carried schedule so a malformed proof errors
    // instead of panicking inside the schedule constructors. The values are
    // transcript-mixed and layout-determining, so a lie cannot verify.
    if let (Some(slot_log), Some(log_n_rows)) =
        (proof.merged_sha_slot_log, proof.merged_sha_log_n_rows)
    {
        if !(7..=16).contains(&slot_log) || !(slot_log..=slot_log + 8).contains(&log_n_rows) {
            return Err(Error::Verify(
                "mdoc proof merged SHA schedule out of bounds".to_string(),
            ));
        }
    }
    match &proof.attribute_public_digest_bind_interaction_claims {
        Some(claims) if claims.len() == statement.attributes.len() => {}
        _ => {
            return Err(Error::Verify(
                "mdoc proof attribute digest-bind shape mismatch".into(),
            ))
        }
    }
    match (&proof.revocation_mldsa, has_revocation_signature) {
        (Some(claims), true) if claims.has_expected_shape() => {}
        (None, false) => {}
        _ => {
            return Err(Error::Verify(
                "mdoc proof ML-DSA revocation claim tree does not match the statement".to_string(),
            ))
        }
    }
    match &proof.keccak_service_claimed_sums {
        Some(sums)
            if sums.len() == stwo_mldsa::stwo_keccak::service::service_claimed_sums_len() => {}
        _ => {
            return Err(Error::Verify(
                "mdoc proof keccak service claims do not match the statement".to_string(),
            ))
        }
    }
    let revocation_message_field = has_revocation_signature.then(SharedFieldRelation::new);
    let attribute_count = statement.attributes.len();
    let attribute_digests: Vec<_> = (0..attribute_count)
        .map(|_| SharedDigestRelation::new())
        .collect();
    // The proof-wide keccak service's relations handle (mirror of the prover).
    let mldsa_keccak_handle = SharedKeccakRelations::new();
    let attribute_fields: Vec<_> = (0..attribute_count)
        .map(|_| SharedFieldRelation::new())
        .collect();
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
    // Hosted ML-DSA verifier (M7): rebuilt from the statement's public input +
    // the proof's claim tree; composed AFTER `issuer_sha` (shared field draw).
    let mut issuer_mldsa = match (statement.issuer_input.as_mldsa(), &proof.mldsa) {
        (Some(input), Some(claims)) => Some(
            MlDsaStatementVerifier::hosted_public(
                input.clone(),
                claims.group_evals.clone(),
                claims.claimed_sums.clone(),
                claims.sib_stream_len,
                claims.sib_squeezed_len,
                mldsa_keccak_handle.clone(),
            )
            .with_instance_namespace(MDOC_ISSUER_MLDSA_NAMESPACE)
            .with_stream_base(MDOC_ISSUER_MLDSA_STREAM_BASE),
        ),
        _ => None,
    };
    // Hosted ML-DSA device verifier, public-message mode (S4): rebuilt from
    // the statement's public input + the proof's claim tree.
    let mut device_mldsa = match (statement.device_input.as_mldsa(), &proof.device_mldsa) {
        (Some(input), Some(claims)) => Some(
            MlDsaStatementVerifier::hosted_public(
                input.clone(),
                claims.group_evals.clone(),
                claims.claimed_sums.clone(),
                claims.sib_stream_len,
                claims.sib_squeezed_len,
                mldsa_keccak_handle.clone(),
            )
            .with_instance_namespace(MDOC_DEVICE_MLDSA_NAMESPACE)
            .with_stream_base(MDOC_DEVICE_MLDSA_STREAM_BASE),
        ),
        _ => None,
    };
    // Hosted ML-DSA revocation verifier, private-message mode: the input is
    // rebuilt from the statement's PUBLIC key/signature bytes with 20 ZEROED
    // message bytes — the real id bounds never enter the verifier's inputs,
    // the transcript (only the length is mixed), or the serialized proof.
    let mut revocation_mldsa = match &proof.revocation_mldsa {
        Some(claims) => {
            ts13_revocation_mldsa_input(statement, vec![0u8; TS13_REVOCATION_MESSAGE_LEN])?.map(
                |input| {
                    MlDsaStatementVerifier::hosted(
                        *input,
                        claims.group_evals.clone(),
                        claims.claimed_sums.clone(),
                        claims.sib_stream_len,
                        claims.sib_squeezed_len,
                        revocation_message_field
                            .clone()
                            .expect("revocation field relation exists with a revocation signature"),
                        mldsa_keccak_handle.clone(),
                    )
                    .with_instance_namespace(MDOC_REVOCATION_MLDSA_NAMESPACE)
                    .with_stream_base(MDOC_REVOCATION_MLDSA_STREAM_BASE)
                    .with_private_message()
                },
            )
        }
        None => None,
    };
    // The proof-wide keccak service verifier (S1): job shapes rebuilt from
    // PUBLIC data only, in the prover's fixed role order (issuer, device,
    // revocation) — message lengths from the statement (the revocation
    // message is the fixed 20-byte private-message window), sib stream
    // lengths from the shape-gated per-role claim trees, stream bases from
    // the role constants. Claimed sums come from the proof.
    let mut mldsa_keccak_service = proof.keccak_service_claimed_sums.as_ref().map(|sums| {
        let mut shapes = Vec::new();
        if let Some(input) = statement.issuer_input.as_mldsa() {
            let claims = proof.mldsa.as_ref().expect("issuer claim tree gated above");
            shapes.extend(keccak_job_shapes(
                input.message.len(),
                claims.sib_stream_len,
                MDOC_ISSUER_MLDSA_STREAM_BASE,
            ));
        }
        if let Some(input) = statement.device_input.as_mldsa() {
            let claims = proof
                .device_mldsa
                .as_ref()
                .expect("device claim tree gated above");
            shapes.extend(keccak_job_shapes(
                input.message.len(),
                claims.sib_stream_len,
                MDOC_DEVICE_MLDSA_STREAM_BASE,
            ));
        }
        if let Some(claims) = proof.revocation_mldsa.as_ref() {
            shapes.extend(keccak_job_shapes(
                TS13_REVOCATION_MESSAGE_LEN,
                claims.sib_stream_len,
                MDOC_REVOCATION_MLDSA_STREAM_BASE,
            ));
        }
        KeccakServiceVerifier::new(shapes, sums.clone(), mldsa_keccak_handle.clone())
    });

    let attribute_exposures: Vec<_> = (0..statement.attributes.len())
        .map(|index| attribute_exposure(statement, index))
        .collect();
    let mut merged_sha = (|| -> Result<Sha256MultiVerifier, Error> {
        let mut slot_specs = Vec::new();
        for exposure in &attribute_exposures {
            slot_specs.push(SlotSpec {
                expose_digest: true,
                field_exposure: exposure.clone(),
            });
        }
        if slot_specs.is_empty() {
            return Err(Error::Verify(
                "mdoc merged SHA instance requires at least one slot".to_string(),
            ));
        }
        let config = MultiSlotConfig::new(
            proof
                .merged_sha_slot_log
                .expect("merged slot log shape-gated above"),
            slot_specs,
        );
        let log_n_rows = proof
            .merged_sha_log_n_rows
            .expect("merged log shape-gated above");
        if log_n_rows < config.min_log_n_rows() {
            return Err(Error::Verify(
                "mdoc proof merged SHA log cannot hold the slot schedule".to_string(),
            ));
        }
        let mut verifier = Sha256MultiVerifier::new(
            log_n_rows,
            config,
            sha_table_relations.clone(),
            proof
                .merged_sha_interaction_claim
                .clone()
                .expect("merged claim shape-gated above"),
        );
        for index in 0..attribute_count {
            verifier = verifier
                .with_slot_digest_handle(index, attribute_digests[index].clone())
                .with_slot_field_handle(index, attribute_fields[index].clone());
        }
        Ok(verifier)
    })()?;

    let mut mdoc_window_bind = MdocWindowBind::verifier_for_attributes(
        mdoc_window_bind_rows_from(statement, None),
        attribute_fields.clone(),
        proof.mdoc_window_bind_interaction_claim.clone(),
    );
    // S4 ML-DSA: per-attribute PUBLIC digest binds against the host-derived
    // `valueDigests` values (mirror of the prover; shape-gated above).
    let mut attribute_public_digest_binds: Vec<PublicDigestBind> = match (
        &mldsa_mso_facts,
        &proof.attribute_public_digest_bind_interaction_claims,
    ) {
        (Some(facts), Some(claims)) => facts
            .attribute_digests
            .iter()
            .zip(attribute_digests.iter())
            .zip(claims.iter())
            .map(|((digest, handle), claim)| {
                PublicDigestBind::verifier(*digest, handle.clone(), claim.clone())
            })
            .collect(),
        _ => Vec::new(),
    };
    let mut age = if let Some(index) = statement.age_attribute_index {
        let public = proof.age_public.as_ref().ok_or(Error::AgePolicyMismatch)?;
        let claimed_sums = proof
            .age_claimed_sums
            .as_ref()
            .ok_or(Error::AgePolicyMismatch)?;
        let age = AgeRangeCheck::new(PcsConfig::default())
            .verifier(public, claimed_sums)
            .map_err(Error::AgePrepare)?;
        Some(match statement.birth_date_binding {
            MdocBirthDateBinding::Packed(_) => {
                age.with_dob_binding(attribute_fields[index].clone())
            }
            MdocBirthDateBinding::Text(_) => {
                age.with_text_dob_binding(attribute_fields[index].clone())
            }
        })
    } else {
        None
    };
    let mut nat = if let Some(index) = statement.nationality_attribute_index {
        let public = proof.nat_public.as_ref().ok_or(Error::NatPolicyMismatch)?;
        let claimed_sums = proof
            .nat_claimed_sums
            .as_ref()
            .ok_or(Error::NatPolicyMismatch)?;
        Some(
            NationalityPredicate::new(PcsConfig::default())
                .verifier(public, claimed_sums)
                .map_err(Error::NatPrepare)?
                .with_nat_binding(attribute_fields[index].clone()),
        )
    } else {
        None
    };
    let mut ts13_revocation_public = statement
        .ts13_revocation
        .clone()
        .map(MdocRevocationPublicBind::new);
    let mut ts13_revocation_range = statement.ts13_revocation_range.as_ref().map(|_| {
        // S4 ML-DSA: the digest binding is the PUBLIC host-derived Sha256 of
        // the Sig_structure payload (mirror of the prover).
        let digest_binding = MsoDigestBinding::Public(
            mldsa_mso_facts
                .as_ref()
                .expect("quantum-safe statements always expose ML-DSA MSO facts")
                .mso_digest,
        );
        MdocRevocationRangeBind::verifier(
            digest_binding,
            statement
                .ts13_revocation
                .as_ref()
                .map(|revocation| revocation.epoch)
                .filter(|_| has_revocation_signature),
            revocation_message_field.clone(),
            proof
                .ts13_revocation_range_interaction_claim
                .clone()
                .expect("revocation range interaction claim exists when range is set"),
        )
    });

    // Mirror the prover's module order exactly (transcript identity).
    let mut modules: Vec<&mut dyn Air> = vec![&mut sha_tables];
    if let Some(service) = mldsa_keccak_service.as_mut() {
        modules.push(service);
    }
    if let Some(issuer) = issuer_mldsa.as_mut() {
        modules.push(issuer);
    }
    if let Some(device) = device_mldsa.as_mut() {
        modules.push(device);
    }
    modules.push(&mut merged_sha);
    if let Some(revocation_range) = ts13_revocation_range.as_mut() {
        modules.push(revocation_range);
    }
    if let Some(revocation_mldsa) = revocation_mldsa.as_mut() {
        modules.push(revocation_mldsa);
    }
    // S4 ML-DSA: per-attribute PUBLIC digest binds, right after their SHA
    // providers (mirror of the prover's module order).
    for bind in &mut attribute_public_digest_binds {
        modules.push(bind);
    }
    modules.push(&mut mdoc_window_bind);
    if let Some(age) = age.as_mut() {
        modules.push(age);
    }
    if let Some(nat) = nat.as_mut() {
        modules.push(nat);
    }
    if let Some(revocation_public) = ts13_revocation_public.as_mut() {
        modules.push(revocation_public);
    }
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        air_core::verify_with_expected_preprocessed_root(
            modules.as_mut_slice(),
            &proof.stark_proof,
            expected_preprocessed_root,
        )
    })) {
        Ok(Ok(())) => Ok(MdocCircuitVerifyProfile {
            total: total_start.elapsed(),
        }),
        Ok(Err(air_core::VerifyError::PreprocessedRootMismatch { got, expected })) => {
            Err(Error::PreprocessedRootMismatch { got, expected })
        }
        Ok(Err(error)) => Err(Error::Verify(format!("{error:?}"))),
        Err(_) => Err(Error::Verify(
            "malformed mdoc proof panicked during verification".to_string(),
        )),
    }
}

pub fn mdoc_production_pcs_config() -> PcsConfig {
    // S6 bake-off picked log_blowup 4 over 3: −340 KB of queried_values for
    // +40% prove time (proof-size-first rule; verify unchanged). S7 query
    // shave: pow_bits 25 + n_queries 26 keeps 26·4 + 25 = 129 ≥ 128-bit
    // security and trades one query (−~38 KB) for a 2^25 blake2s grind
    // (measured +~0.3 s single-thread prove). The verifier pins this exact
    // config (see verify_mdoc_circuit_with_pcs_config) so an old-config
    // proof is rejected.
    PcsConfig {
        pow_bits: 25,
        fri_config: FriConfig::new(1, 4, 26, 2),
        lifting_log_size: None,
    }
}

pub fn mdoc_longfellow_parity_pcs_config() -> PcsConfig {
    PcsConfig {
        pow_bits: 10,
        fri_config: FriConfig::new(1, 2, 50, 2),
        lifting_log_size: None,
    }
}

#[cfg(all(test, feature = "p256"))]
mod mdoc_sha_table_tests {
    use super::*;

    #[test]
    fn mdoc_module_shape_starts_with_shared_sha_tables() {
        let shapes = demo_mdoc_module_shapes().expect("mdoc shapes build");
        assert_eq!(
            shapes.first().map(|shape| shape.name),
            Some("mdoc_sha_tables"),
            "the shared SHA table provider must draw relations before SHA consumers",
        );
        // Phase D folds the two per-digest binds into one MdocWindowBind, then
        // adds the validity-window comparator as its own issuer-field consumer.
        #[cfg(not(feature = "ec-coprocessor"))]
        assert_eq!(shapes.len(), 13);
        #[cfg(feature = "ec-coprocessor")]
        assert_eq!(shapes.len(), 12);
    }

    #[test]
    #[cfg(feature = "ec-coprocessor")]
    fn mdoc_mac_shape_stays_under_q014_budget() {
        let shapes = demo_mdoc_module_shapes().expect("mdoc shapes build");
        let mdoc_mac = shapes
            .iter()
            .find(|shape| shape.name == "mdoc_mac")
            .expect("mdoc_mac module shape");
        let cells: u64 = mdoc_mac
            .layout
            .preprocessed
            .iter()
            .chain(&mdoc_mac.layout.trace)
            .chain(&mdoc_mac.layout.interaction)
            .map(|&log_size| 1u64 << log_size)
            .sum();
        // 332_288 pre-P4c + 4_096 for the Q-015 consumer blinder interaction
        // column (4 base cols x 2^10 rows); the binding-side counterpart pairs
        // into the existing 18 binding columns at no extra cost.
        assert_eq!(
            cells, 336_384,
            "mdoc_mac should keep log-10 consumer rows and log-9 binding blind rows"
        );
        assert!(
            cells <= 1_200_000,
            "Q014 mdoc_mac cell budget exceeded: {cells}"
        );
    }

    /// Q-015 §4b acceptance: proving the same witness twice must publish
    /// DIFFERENT per-component claimed sums for every blinded module (the
    /// split is randomized by the fresh (v, m) pair), while both proofs
    /// verify.
    #[test]
    #[ignore = "slow: proves product mdoc circuit profile twice"]
    fn mdoc_zk_claimed_sum_blinder_pairs_present() {
        let fixture = demo_mdoc_circuit_fixture();
        let proof_a =
            prove_mdoc_circuit(&fixture.extracted, &fixture.statement).expect("proof A proves");
        let proof_b =
            prove_mdoc_circuit(&fixture.extracted, &fixture.statement).expect("proof B proves");
        verify_mdoc_circuit(&proof_a, &fixture.statement).expect("proof A verifies");
        verify_mdoc_circuit(&proof_b, &fixture.statement).expect("proof B verifies");

        let mut checked = Vec::new();
        let mut check = |name: &'static str, a: QM31, b: QM31| {
            assert_ne!(
                a, b,
                "{name} published claimed sum is identical across same-witness proves; \
                 the Q-015 blinder pair is not randomizing the split"
            );
            checked.push(name);
        };
        check(
            "mdoc_window_bind claimed_sum",
            proof_a.mdoc_window_bind_interaction_claim.claimed_sum,
            proof_b.mdoc_window_bind_interaction_claim.claimed_sum,
        );
        check(
            "mdoc_window_bind blinder_claimed_sum",
            proof_a
                .mdoc_window_bind_interaction_claim
                .blinder_claimed_sum,
            proof_b
                .mdoc_window_bind_interaction_claim
                .blinder_claimed_sum,
        );
        check(
            "mdoc_validity claimed_sum",
            proof_a.mdoc_validity_interaction_claim.claimed_sum,
            proof_b.mdoc_validity_interaction_claim.claimed_sum,
        );
        check(
            "mdoc_validity blinder_claimed_sum",
            proof_a.mdoc_validity_interaction_claim.blinder_claimed_sum,
            proof_b.mdoc_validity_interaction_claim.blinder_claimed_sum,
        );
        if let (Some(a), Some(b)) = (
            proof_a.mso_payload_bind_interaction_claim.as_ref(),
            proof_b.mso_payload_bind_interaction_claim.as_ref(),
        ) {
            check("mso_payload claimed_sum", a.claimed_sum, b.claimed_sum);
            check(
                "mso_payload blinder_claimed_sum",
                a.blinder_claimed_sum,
                b.blinder_claimed_sum,
            );
        }
        if let (Some(a), Some(b)) = (
            proof_a.ts13_revocation_range_interaction_claim.as_ref(),
            proof_b.ts13_revocation_range_interaction_claim.as_ref(),
        ) {
            check("revocation_range claimed_sum", a.claimed_sum, b.claimed_sum);
            check(
                "revocation_range blinder_claimed_sum",
                a.blinder_claimed_sum,
                b.blinder_claimed_sum,
            );
        }
        #[cfg(feature = "ec-coprocessor")]
        {
            check(
                "mdoc_mac consumer claimed_sum",
                proof_a.mdoc_mac_interaction_claim.consumer,
                proof_b.mdoc_mac_interaction_claim.consumer,
            );
            check(
                "mdoc_mac binding claimed_sum",
                proof_a.mdoc_mac_interaction_claim.binding,
                proof_b.mdoc_mac_interaction_claim.binding,
            );
        }
        assert!(
            checked.len() >= 4,
            "expected at least the window/validity pairs to be checked, got {checked:?}"
        );
    }

    /// Q-015 §4b acceptance: the global LogUp balance still verifies with the
    /// blinder pairs active, and flipping the blinder multiplicity `m` in one
    /// serialized member (leaving all published sums untouched, so the global
    /// fold still cancels) must be rejected at the OODS/LogUp boundary — the
    /// pair is bound, not a free claimed-sum term.
    #[test]
    #[ignore = "slow: proves product mdoc circuit profile"]
    fn mdoc_zk_claimed_sum_blinder_balance_preserved() {
        let fixture = demo_mdoc_circuit_fixture();
        let proof =
            prove_mdoc_circuit(&fixture.extracted, &fixture.statement).expect("mdoc proves");
        verify_mdoc_circuit(&proof, &fixture.statement)
            .expect("mdoc verifies with blinder pairs active");

        let mut m_tamper = proof.clone();
        m_tamper.mdoc_window_bind_interaction_claim.blinder_m +=
            QM31::from_u32_unchecked(1, 0, 0, 0);
        assert!(
            verify_mdoc_circuit(&m_tamper, &fixture.statement).is_err(),
            "flipped blinder multiplicity m unexpectedly verified",
        );

        let mut split_tamper = proof.clone();
        let shift = QM31::from_u32_unchecked(1, 0, 0, 0);
        split_tamper.mdoc_window_bind_interaction_claim.claimed_sum += shift;
        split_tamper
            .mdoc_window_bind_interaction_claim
            .blinder_claimed_sum -= shift;
        assert!(
            verify_mdoc_circuit(&split_tamper, &fixture.statement).is_err(),
            "re-splitting the published pair without re-proving unexpectedly verified",
        );
    }

    #[test]
    #[ignore = "slow: proves product mdoc circuit profile"]
    fn mdoc_preprocessed_root_tamper_rejects_before_stark() {
        let fixture = demo_mdoc_circuit_fixture();
        let mut proof =
            prove_mdoc_circuit(&fixture.extracted, &fixture.statement).expect("mdoc proves");
        let expected_preprocessed_root = proof.stark_proof.commitments[0];
        verify_mdoc_circuit_with_preprocessed_root(
            &proof,
            &fixture.statement,
            expected_preprocessed_root,
        )
        .expect("mdoc verifies before tamper");

        proof.stark_proof.0.commitments[0].0[0] ^= 1;

        assert!(matches!(
            verify_mdoc_circuit_with_preprocessed_root(
                &proof,
                &fixture.statement,
                expected_preprocessed_root,
            ),
            Err(Error::PreprocessedRootMismatch { .. })
        ));
    }

    #[test]
    #[ignore = "slow: proves product mdoc circuit profile"]
    fn shared_sha_table_provider_claim_is_bound() {
        let fixture = demo_mdoc_circuit_fixture();
        let mut proof =
            prove_mdoc_circuit(&fixture.extracted, &fixture.statement).expect("mdoc proves");
        verify_mdoc_circuit(&proof, &fixture.statement).expect("mdoc verifies before tamper");

        proof.sha_tables_interaction_claim.pairs[0].claimed_sum =
            -proof.sha_tables_interaction_claim.pairs[0].claimed_sum;

        assert!(
            verify_mdoc_circuit(&proof, &fixture.statement).is_err(),
            "tampered shared SHA table provider claim unexpectedly verified",
        );
    }

    #[test]
    #[ignore = "slow: proves product mdoc circuit profile"]
    fn shared_sha_table_mdoc_digest_and_field_swaps_reject() {
        let fixture = demo_mdoc_circuit_fixture();
        let proof =
            prove_mdoc_circuit(&fixture.extracted, &fixture.statement).expect("mdoc proves");
        verify_mdoc_circuit(&proof, &fixture.statement).expect("mdoc verifies before tamper");

        // Phase D: the digests are bound in-circuit from the issuer MSO
        // preimage, not carried in the statement. Swapping the two digest window
        // offsets points each digest bind at the other's bytes, so the
        // window↔item-SHA LogUp no longer balances.
        let mut digest_offset_swap = fixture.statement.clone();
        std::mem::swap(
            &mut digest_offset_swap.mso_birth_date_digest_offset,
            &mut digest_offset_swap.mso_nationality_digest_offset,
        );
        assert!(
            verify_mdoc_circuit(&proof, &digest_offset_swap).is_err(),
            "birth/nationality digest offset swap unexpectedly verified",
        );

        if fixture.statement.birth_date_value_offset != fixture.statement.nationality_value_offset {
            let mut field_exposure_swap = fixture.statement.clone();
            std::mem::swap(
                &mut field_exposure_swap.birth_date_value_offset,
                &mut field_exposure_swap.nationality_value_offset,
            );
            assert!(
                verify_mdoc_circuit(&proof, &field_exposure_swap).is_err(),
                "birth/nationality field exposure swap unexpectedly verified",
            );
        } else {
            let mut birth_offset_tamper = fixture.statement.clone();
            birth_offset_tamper.birth_date_value_offset += 1;
            assert!(
                verify_mdoc_circuit(&proof, &birth_offset_tamper).is_err(),
                "birth-date field exposure offset tamper unexpectedly verified",
            );

            let mut nat_offset_tamper = fixture.statement.clone();
            nat_offset_tamper.nationality_value_offset += 1;
            assert!(
                verify_mdoc_circuit(&proof, &nat_offset_tamper).is_err(),
                "nationality field exposure offset tamper unexpectedly verified",
            );
        }
    }

    /// Phase D: each of the three in-circuit MSO bind surfaces (D1 element-id
    /// pin, D2 digest membership, D3 device-key origin) rejects when its window
    /// offset is moved off the genuine bytes.
    #[test]
    #[ignore = "slow: proves product mdoc circuit profile"]
    fn mdoc_window_bind_offset_tampers_reject() {
        let fixture = demo_mdoc_circuit_fixture();
        let proof =
            prove_mdoc_circuit(&fixture.extracted, &fixture.statement).expect("mdoc proves");
        verify_mdoc_circuit(&proof, &fixture.statement).expect("mdoc verifies before tamper");

        // D1: birth_date elementIdentifier window (the exposed field bytes no
        // longer spell "birth_date" at the shifted offset).
        let mut d1 = fixture.statement.clone();
        d1.birth_date_element_offset += 1;
        assert!(
            verify_mdoc_circuit(&proof, &d1).is_err(),
            "D1 element-id offset tamper unexpectedly verified",
        );

        // D2: birth_date valueDigests window in the issuer preimage.
        let mut d2 = fixture.statement.clone();
        d2.mso_birth_date_digest_offset += 1;
        assert!(
            verify_mdoc_circuit(&proof, &d2).is_err(),
            "D2 digest-window offset tamper unexpectedly verified",
        );

        // D3: deviceKey x-coordinate window in the issuer preimage. Moving the
        // offset breaks the byte-equality against the coprocessor's proven
        // device public key x.
        let mut d3 = fixture.statement.clone();
        d3.mso_device_key_x_offset += 1;
        assert!(
            verify_mdoc_circuit(&proof, &d3).is_err(),
            "D3 device-key-window offset tamper unexpectedly verified",
        );

        // Validity: validUntil full-date window in the issuer preimage. Moving
        // the offset breaks the in-circuit date parser/comparison against the
        // public policy date.
        let mut validity = fixture.statement.clone();
        validity.mso_valid_until_date_offset += 1;
        assert!(
            verify_mdoc_circuit(&proof, &validity).is_err(),
            "validity-window offset tamper unexpectedly verified",
        );
    }

    #[test]
    #[ignore = "slow: proves product mdoc circuit profile"]
    fn malformed_shared_sha_table_provider_claim_rejects_without_panic() {
        let fixture = demo_mdoc_circuit_fixture();
        let mut proof =
            prove_mdoc_circuit(&fixture.extracted, &fixture.statement).expect("mdoc proves");
        verify_mdoc_circuit(&proof, &fixture.statement).expect("mdoc verifies before tamper");

        proof.sha_tables_interaction_claim.pairs.clear();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            verify_mdoc_circuit(&proof, &fixture.statement)
        }));
        assert!(
            matches!(result, Ok(Err(Error::Verify(_)))),
            "malformed shared SHA table claim should reject gracefully, got {result:?}",
        );
    }

    #[test]
    fn mdoc_sha_witnesses_match_native_digest_for_all_four_messages() {
        let fixture = demo_mdoc_circuit_fixture();
        let extracted = &fixture.extracted;
        let cases = [
            ("issuer", extracted.issuer_sig_structure.as_slice()),
            ("device", extracted.device_sig_structure.as_slice()),
            ("birth_date", extracted.birth_date_item.as_slice()),
            ("nationality", extracted.nationality_item.as_slice()),
        ];

        for (name, message) in cases {
            let (witness, _log_n_rows) = sha_params(message);
            let native: [u8; 32] = Sha256::digest(message).into();
            assert_eq!(witness.digest.0, native, "{name} digest");
            assert_eq!(
                witness.digest_from_blocks().0,
                native,
                "{name} digest from block chain",
            );
        }
    }
}

#[cfg(all(test, feature = "ec-coprocessor"))]
mod coprocessor_tests {
    use super::*;
    use crate::{fixtures, prove_identity, Error, IssuerKey};

    #[derive(Debug, PartialEq, Eq)]
    struct TestCoprocessorDigests {
        post_statement: [u8; 32],
        post_seed: [u8; 32],
        post_rejoin: [u8; 32],
    }

    fn verified_mdoc_proof() -> (MdocCircuitProof, MdocCircuitStatement) {
        let fixture = demo_mdoc_circuit_fixture();
        let proof =
            prove_mdoc_circuit(&fixture.extracted, &fixture.statement).expect("mdoc proves");
        verify_mdoc_circuit(&proof, &fixture.statement).expect("mdoc verifies");
        (proof, fixture.statement)
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
        crate::mix_coprocessor_tagged_statements(
            &mut channel,
            &[(issuer_tag, issuer_input), (device_tag, device_input)],
        )
        .expect("mdoc tagged statements mix");
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
        let (proof, statement) = verified_mdoc_proof();

        let public_statement = MdocPublicStatement::from_circuit(&statement);
        verify_mdoc_public_statement(&proof, &public_statement)
            .expect("reduced public statement verifies");
        let mut wrong_issuer_key = public_statement.clone();
        wrong_issuer_key.issuer_public_key.x.0[0] ^= 1;
        assert!(
            verify_mdoc_public_statement(&proof, &wrong_issuer_key).is_err(),
            "issuer public key mutation unexpectedly verified"
        );
        let mut wrong_device_z = public_statement.clone();
        wrong_device_z.device_message_hash.0[0] ^= 1;
        assert!(
            verify_mdoc_public_statement(&proof, &wrong_device_z).is_err(),
            "device z mutation unexpectedly verified"
        );

        let mut missing_bundle = proof.clone();
        missing_bundle.coprocessor_bundle = None;
        assert!(matches!(
            verify_mdoc_circuit(&missing_bundle, &statement),
            Err(Error::CoprocessorMissing)
        ));

        let mut tampered = proof.clone();
        tampered.coprocessor_bundle =
            Some(tampered_bundle(proof.coprocessor_bundle.as_ref().unwrap()));
        assert_verify_rejects(
            "serialized coprocessor bundle tamper",
            &tampered,
            &statement,
        );

        let mut mac_tag_tamper = proof.clone();
        let bundle = mac_tag_tamper
            .coprocessor_bundle
            .as_mut()
            .expect("mdoc proof has a coprocessor bundle");
        bundle.mac_tags[0][0] ^= 1;
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
        device_z_mismatch
            .device_input
            .expect_ecdsa_mut()
            .message_hash
            .0[0] ^= 1;
        assert_verify_rejects("device z mismatch", &proof, &device_z_mismatch);

        let mut cross_slot_z = statement.clone();
        let IssuerAuthInput::Ecdsa(cross_slot_issuer) = &mut cross_slot_z.issuer_input else {
            panic!("demo statement issuer is P-256");
        };
        std::mem::swap(
            &mut cross_slot_issuer.message_hash,
            &mut cross_slot_z.device_input.expect_ecdsa_mut().message_hash,
        );
        assert_verify_rejects("cross-slot z swap", &proof, &cross_slot_z);

        let mut cross_signature = statement.clone();
        let IssuerAuthInput::Ecdsa(cross_sig_issuer) = &mut cross_signature.issuer_input else {
            panic!("demo statement issuer is P-256");
        };
        std::mem::swap(
            cross_sig_issuer,
            cross_signature.device_input.expect_ecdsa_mut(),
        );
        assert_verify_rejects("cross-signature swap", &proof, &cross_signature);

        let identity_fixture = fixtures::valid_over_18();
        let issuer = IssuerKey::demo();
        let nonce = fixtures::demo_nonce_statement();
        let identity_proof = prove_identity(
            &identity_fixture.signed.credential,
            &issuer,
            &identity_fixture.policy,
            &nonce,
        )
        .expect("identity proves");
        let mut replayed_identity_bundle = proof.clone();
        replayed_identity_bundle.coprocessor_bundle =
            Some(identity_proof.coprocessor_bundle().unwrap().clone());
        assert_verify_rejects(
            "identity coprocessor bundle replay",
            &replayed_identity_bundle,
            &statement,
        );
    }

    #[test]
    #[ignore = "slow: proves product mdoc circuit with coprocessor bundle"]
    fn mdoc_coprocessor_statement_order_and_rejoin_guards_are_bound() {
        let (proof, statement) = verified_mdoc_proof();
        let bundle = proof.coprocessor_bundle.as_ref().unwrap();

        let canonical = mdoc_coprocessor_digests(
            b"issuer",
            statement
                .issuer_input
                .as_ecdsa()
                .expect("demo issuer is P-256"),
            b"device",
            statement
                .device_input
                .as_ecdsa()
                .expect("demo device is P-256"),
            bundle,
        );
        let swapped_statement_order = mdoc_coprocessor_digests(
            b"device",
            statement
                .device_input
                .as_ecdsa()
                .expect("demo device is P-256"),
            b"issuer",
            statement
                .issuer_input
                .as_ecdsa()
                .expect("demo issuer is P-256"),
            bundle,
        );
        assert_ne!(canonical, swapped_statement_order);

        let tampered_rejoin = mdoc_coprocessor_digests(
            b"issuer",
            statement
                .issuer_input
                .as_ecdsa()
                .expect("demo issuer is P-256"),
            b"device",
            statement
                .device_input
                .as_ecdsa()
                .expect("demo device is P-256"),
            &tampered_bundle(bundle),
        );
        assert_ne!(canonical.post_rejoin, tampered_rejoin.post_rejoin);

        let mut without_rejoin = air_core::Ch::default();
        crate::mix_coprocessor_tagged_statements(
            &mut without_rejoin,
            &[
                (
                    b"issuer".as_slice(),
                    statement
                        .issuer_input
                        .as_ecdsa()
                        .expect("demo issuer is P-256"),
                ),
                (
                    b"device".as_slice(),
                    statement
                        .device_input
                        .as_ecdsa()
                        .expect("demo device is P-256"),
                ),
            ],
        )
        .expect("mdoc tagged statements mix");
        let _seed = crate::draw_coprocessor_seed(&mut without_rejoin);
        let without_rejoin_next = crate::draw_coprocessor_seed(&mut without_rejoin);

        let mut with_rejoin = air_core::Ch::default();
        crate::mix_coprocessor_tagged_statements(
            &mut with_rejoin,
            &[
                (
                    b"issuer".as_slice(),
                    statement
                        .issuer_input
                        .as_ecdsa()
                        .expect("demo issuer is P-256"),
                ),
                (
                    b"device".as_slice(),
                    statement
                        .device_input
                        .as_ecdsa()
                        .expect("demo device is P-256"),
                ),
            ],
        )
        .expect("mdoc tagged statements mix");
        let _seed = crate::draw_coprocessor_seed(&mut with_rejoin);
        crate::mix_coprocessor_rejoin(&mut with_rejoin, bundle).expect("mdoc rejoin mixes");
        let with_rejoin_next = crate::draw_coprocessor_seed(&mut with_rejoin);

        assert_ne!(with_rejoin_next, without_rejoin_next);
    }

    #[test]
    #[ignore = "slow: proves the same mdoc witness twice to check P4b MAC freshness"]
    fn a_p_freshness_linkability() {
        let fixture = demo_mdoc_circuit_fixture();
        let first =
            prove_mdoc_circuit(&fixture.extracted, &fixture.statement).expect("first mdoc proves");
        verify_mdoc_circuit(&first, &fixture.statement).expect("first mdoc verifies");
        let second =
            prove_mdoc_circuit(&fixture.extracted, &fixture.statement).expect("second mdoc proves");
        verify_mdoc_circuit(&second, &fixture.statement).expect("second mdoc verifies");

        let first_bundle = first
            .coprocessor_bundle
            .as_ref()
            .expect("first proof has coprocessor bundle");
        let second_bundle = second
            .coprocessor_bundle
            .as_ref()
            .expect("second proof has coprocessor bundle");

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
    }
}

fn is_supported_mdoc_profile_version(version: &str) -> bool {
    matches!(version, MDOC_PROFILE_VERSION_V1 | MDOC_PROFILE_VERSION_V2)
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
