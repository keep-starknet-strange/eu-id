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
use ecdsa::signature::{Signer, Verifier};
use p256::ecdsa::{Signature as P256Signature, SigningKey, VerifyingKey};
#[cfg(feature = "ec-coprocessor")]
use p256::elliptic_curve::rand_core::{OsRng, RngCore};
#[cfg(feature = "p256")]
use p256::pkcs8::DecodePublicKey;
use p256::EncodedPoint;
use predicates::nat::NationalityPredicate;
use predicates::{AgeRangeCheck, DateOfBirth, PredicateProver, PredicateVerifier};
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
    MlDsaProver as MlDsaStatementProver, MlDsaVerifier as MlDsaStatementVerifier,
};
#[cfg(feature = "ml-dsa")]
use stwo_mldsa::types::MlDsaVerifyInput;
use stwo_p256::components::digest_bind::module::{
    DigestBindInteractionClaim, DigestBindProver, DigestBindVerifier,
};
use stwo_p256::components::digest_bind::SharedScalarZRelation;
use stwo_p256::public_inputs::PublicEcdsaInstance;
use stwo_p256::types::{AffinePoint, EcdsaVerifyInput, Signature, U256};
use stwo_p256::{proof::air::P256Prover, proof::P256ProofDraft};
use stwo_p256::{
    proof::air::P256Verifier,
    proof::{P256CurrentAirInteractionClaim, P256CurrentAirProofClaim},
};
use stwo_sha256::air::{Sha256Prover, Sha256Verifier};
use stwo_sha256::field_exposure::FieldExposure;
use stwo_sha256::interaction::InteractionClaim as Sha256InteractionClaim;
use stwo_sha256::relations::SharedShaTableRelations;
use stwo_sha256::shared_tables::{
    ShaTableMultiplicities, ShaTablesInteractionClaim, ShaTablesProver, ShaTablesVerifier,
};
use stwo_sha256::trace::min_log_size;
use stwo_sha256::witness::compute_sha256_witness;

use crate::claimed_sum_blinder::{
    add_blinder_relation_entry, blinder_counter_interaction, random_qm31, ClaimedSumBlinderEval,
    ClaimedSumBlinderRelation,
};
use crate::generator::{Policy, SHA_GROUP_WIDTH};
#[cfg(feature = "ec-coprocessor")]
use crate::mdoc_mac::{
    MdocMacBind, MdocMacInteractionClaim, MdocP4bMacPublic, MdocP4bMacSharedState,
};
use crate::mdoc_validity::{
    mdoc_validity_rows, MdocValidityBind, MdocValidityInteractionClaim, MdocValidityRow,
};
use crate::mdoc_window_bind::{
    MdocFieldSource, MdocWindowBind, MdocWindowBindInteractionClaim, MdocWindowBindRow,
};
#[cfg(feature = "ec-coprocessor")]
use crate::public_digest_bind::{PublicDigestBind, PublicDigestBindInteractionClaim};
use crate::Error;

/// Legacy profile: `elementValue` packed as a fixed-width CBOR `bstr`.
const MDOC_PROFILE_VERSION_V1: &str = "1.0";
/// Profile v2: canonical (RFC 8949 core deterministic) CBOR, text-form values.
const MDOC_PROFILE_VERSION_V2: &str = "2.0";
/// The profile the demo fixture emits and the parser advertises by default.
const MDOC_PROFILE_VERSION: &str = MDOC_PROFILE_VERSION_V2;
const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const ES256_PROTECTED_HEADER: &[u8] = &[0xA1, 0x01, 0x26];
/// COSE protected header `{1: -49}` (ML-DSA-65,
/// `stwo_mldsa::constants::COSE_ALG_ML_DSA_65`): CBOR `A1 01 38 30`.
const MLDSA_PROTECTED_HEADER: &[u8] = &[0xA1, 0x01, 0x38, 0x30];
const CBOR_TAG_ENCODED_CBOR: u64 = 24;
const CBOR_TAG_FULL_DATE: u64 = 1004;
const MDOC_ATTRIBUTE_ELEMENT_ID_BASE: u32 = 16;
const MDOC_ATTRIBUTE_VALUE_BASE: u32 = 20;
const MDOC_ATTRIBUTE_DIGEST_BASE: u32 = 24;
const MDOC_ATTRIBUTE_DIGEST_ANCHOR_BASE: u32 = 28;
const MDOC_ATTRIBUTE_VALUE_HEAD_BASE: u32 = 32;
const MDOC_ATTRIBUTE_ELEMENT_ANCHOR_BASE: u32 = 36;
const MDOC_MSO_PAYLOAD_FIELD_ID: u32 = 40;
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MdocPidRequest {
    pub doctype: String,
    pub namespace: String,
    pub attributes: Vec<MdocRequestedAttribute>,
    pub birth_date_element: String,
    pub nationality_element: String,
    pub session_transcript: Vec<u8>,
    pub trusted_issuer_certificates: Vec<Vec<u8>>,
    pub trusted_issuer_public_keys: Vec<AffinePoint>,
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
            trusted_issuer_certificates: Vec::new(),
            trusted_issuer_public_keys: Vec::new(),
            trusted_mldsa_issuer_public_keys: Vec::new(),
            device_authentication_profile: MdocDeviceAuthenticationProfile::Iso180135,
        }
    }

    pub fn with_trusted_issuer_certificates(mut self, certificates: Vec<Vec<u8>>) -> Self {
        self.trusted_issuer_certificates = certificates;
        self
    }

    pub fn with_trusted_issuer_public_keys(mut self, public_keys: Vec<AffinePoint>) -> Self {
        self.trusted_issuer_public_keys = public_keys;
        self
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

/// A scheme-tagged mdoc signature-verification input, shared by the issuer and
/// device roles: ECDSA P-256 (COSE `ES256`, alg `-7`) or ML-DSA-65 (COSE alg
/// `-49`). Externally-tagged serde (bincode-safe); the `Ecdsa` arm carries the
/// exact `EcdsaVerifyInput` shape the P-256 path always used. The ML-DSA arm's
/// `message` is the full role `Sig_structure` (public to the verifier — unlike
/// the P-256 arm, which only publishes its SHA-256 hash; the in-circuit SHAKE
/// absorb needs the byte-level statement binding).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum MdocAuthInput {
    Ecdsa(EcdsaVerifyInput),
    /// Boxed: an `MlDsaVerifyInput` is ~20 KiB inline (t1/z/hint arrays).
    #[cfg(feature = "ml-dsa")]
    MlDsa(Box<MlDsaVerifyInput>),
}

/// The issuer-role view of [`MdocAuthInput`] (historical name, kept as alias).
pub type IssuerAuthInput = MdocAuthInput;
/// The device-role view of [`MdocAuthInput`].
pub type DeviceAuthInput = MdocAuthInput;

impl MdocAuthInput {
    pub fn as_ecdsa(&self) -> Option<&EcdsaVerifyInput> {
        match self {
            Self::Ecdsa(input) => Some(input),
            #[cfg(feature = "ml-dsa")]
            Self::MlDsa(_) => None,
        }
    }

    #[cfg(feature = "ml-dsa")]
    pub fn as_mldsa(&self) -> Option<&MlDsaVerifyInput> {
        match self {
            Self::Ecdsa(_) => None,
            Self::MlDsa(input) => Some(input.as_ref()),
        }
    }

    /// Whether this is an ML-DSA-65 issuer. Always available (returns `false`
    /// when the `ml-dsa` feature is disabled, since the variant cannot exist) so
    /// digest-handle selection compiles in every feature combination.
    pub fn is_mldsa(&self) -> bool {
        match self {
            Self::Ecdsa(_) => false,
            #[cfg(feature = "ml-dsa")]
            Self::MlDsa(_) => true,
        }
    }

    /// The Ecdsa arm, for call sites that structurally require a P-256 input
    /// (the ec-coprocessor path and P-256-only fixtures).
    fn expect_ecdsa(&self, context: &'static str) -> Result<&EcdsaVerifyInput, Error> {
        self.as_ecdsa().ok_or_else(|| {
            Error::Prove(format!(
                "{context}: ML-DSA-65 auth input is not supported on this path"
            ))
        })
    }

    /// Mutable Ecdsa access for the coprocessor negative-mutation tests.
    #[cfg(all(test, feature = "ec-coprocessor"))]
    fn expect_ecdsa_mut(&mut self) -> &mut EcdsaVerifyInput {
        match self {
            Self::Ecdsa(input) => input,
            #[cfg(feature = "ml-dsa")]
            Self::MlDsa(_) => panic!("expected a P-256 auth input"),
        }
    }
}

/// The decoded ML-DSA issuer witness produced during parsing, if any. Aliased so
/// the issuer-alg dispatch compiles in both feature states: with `ml-dsa` it is
/// the real witness type; without, an uninhabited placeholder that only ever
/// holds `None`. Only referenced from the `p256` issuer arm's `None` literal.
#[cfg(feature = "p256")]
#[cfg(feature = "ml-dsa")]
type IssuerMlDsaSlot = MlDsaVerifyInput;
#[cfg(feature = "p256")]
#[cfg(not(feature = "ml-dsa"))]
type IssuerMlDsaSlot = std::convert::Infallible;

fn auth_inputs_equal(left: &MdocAuthInput, right: &MdocAuthInput) -> bool {
    match (left, right) {
        (MdocAuthInput::Ecdsa(l), MdocAuthInput::Ecdsa(r)) => ecdsa_inputs_equal(l, r),
        #[cfg(feature = "ml-dsa")]
        (MdocAuthInput::MlDsa(l), MdocAuthInput::MlDsa(r)) => l == r,
        #[cfg(feature = "ml-dsa")]
        _ => false,
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
    pub issuer_key: AffinePoint,
    pub device_key: AffinePoint,
    pub issuer_signature: Signature,
    pub device_signature: Signature,
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
    SaltTooShort {
        len: usize,
    },
    InvalidAttributeCount {
        count: usize,
    },
    DuplicatePredicateMode(&'static str),
    ValueEqualityTooLong {
        element: String,
        len: usize,
    },
    ElementIdentifierTooLong {
        element: String,
        len: usize,
    },
    ValueEqualityMismatch {
        element: String,
    },
    /// The issuerAuth advertised a COSE algorithm whose issuer proving path is
    /// not compiled into this build (missing `p256` or `ml-dsa` feature). The
    /// message names the feature to enable.
    UnsupportedIssuerAlg(&'static str),
    /// The (MSO deviceKey scheme, deviceSignature alg, issuer scheme) triple is
    /// not uniform. Mixed signature schemes fail closed in both directions: a
    /// partially post-quantum credential has the security of its weakest link,
    /// so only all-P-256 and all-ML-DSA documents are accepted.
    MixedSignatureSchemes(&'static str),
}

#[derive(Clone, Debug)]
pub struct DemoMdocCircuitFixture {
    pub document: Vec<u8>,
    pub request: MdocPidRequest,
    pub extracted: ExtractedPidMdoc,
    pub statement: MdocCircuitStatement,
}

pub struct MdocModuleShape {
    pub name: &'static str,
    pub layout: TreeLayout,
    /// TRUE per-component committed shape, when the module aggregates multiple
    /// distinct producer tables under one [`TreeLayout`] (today: only the
    /// shared-SHA table module). Empty for single-component modules, whose
    /// `layout` buckets already identify the component 1:1.
    pub components: Vec<stwo_sha256::shared_tables::ShaTableComponentShape>,
}

impl MdocModuleShape {
    /// Single-component module: its `layout` buckets identify the component 1:1.
    fn single(name: &'static str, layout: TreeLayout) -> Self {
        Self {
            name,
            layout,
            components: Vec::new(),
        }
    }

    /// Multi-component module carrying TRUE per-producer shapes.
    fn with_components(
        name: &'static str,
        layout: TreeLayout,
        components: Vec<stwo_sha256::shared_tables::ShaTableComponentShape>,
    ) -> Self {
        Self {
            name,
            layout,
            components,
        }
    }
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

/// Deterministic EUID mdoc profile-v2 fixture used by benches and SDK tests.
pub fn demo_mdoc_circuit_fixture() -> DemoMdocCircuitFixture {
    let request = MdocPidRequest::eudi_pid(openid4vp_session_transcript(b"session-transcript-123"));
    demo_mdoc_circuit_fixture_for_request(request)
}

pub fn demo_mdoc_circuit_fixture_with_attributes(
    attributes: Vec<MdocRequestedAttribute>,
) -> DemoMdocCircuitFixture {
    let session_transcript = openid4vp_session_transcript(b"session-transcript-123");
    let mut request = MdocPidRequest::eudi_pid(session_transcript);
    request.attributes = attributes;
    demo_mdoc_circuit_fixture_for_request(request)
}

fn demo_mdoc_circuit_fixture_for_request(request: MdocPidRequest) -> DemoMdocCircuitFixture {
    let session_transcript = request.session_transcript.clone();
    let include_extra_items = request.attributes.iter().any(|attribute| {
        matches!(
            attribute.element_identifier.as_str(),
            "family_name" | "age_over_18"
        )
    });
    let document = demo_mdoc_document(&session_transcript, include_extra_items);
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
            accepted_nationalities_alpha2: vec![*b"DE", *b"FR"],
        },
    )
    .expect("demo mdoc statement builds");
    DemoMdocCircuitFixture {
        document,
        request,
        extracted,
        statement,
    }
}

pub fn demo_mdoc_module_shapes() -> Result<Vec<MdocModuleShape>, Error> {
    let fixture = demo_mdoc_circuit_fixture();
    let extracted = &fixture.extracted;
    let statement = &fixture.statement;

    #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
    let issuer_draft = single_p256_draft(
        statement
            .issuer_input
            .expect_ecdsa("P-256 shape/sizing probe")?
            .clone(),
    )?;
    #[cfg(not(feature = "ec-coprocessor"))]
    let device_draft = single_p256_draft(
        statement
            .device_input
            .expect_ecdsa("P-256 shape/sizing probe")?
            .clone(),
    )?;
    let (issuer_sha_witness, issuer_sha_log) = sha_params(&extracted.issuer_sig_structure);
    let (device_sha_witness, device_sha_log) = sha_params(&extracted.device_sig_structure);
    let attribute_items: Vec<_> = extracted
        .extracted_attributes
        .iter()
        .map(|attribute| attribute.item.as_slice())
        .collect();
    let attribute_sha_params: Vec<_> = attribute_items
        .iter()
        .map(|item| sha_params(item))
        .collect();
    let shared_sha_log = std::iter::once(issuer_sha_log)
        .chain(std::iter::once(device_sha_log))
        .chain(attribute_sha_params.iter().map(|(_, log)| *log))
        .max()
        .expect("sha log list is non-empty");
    let issuer_digest = SharedDigestRelation::new();
    let device_digest = SharedDigestRelation::new();
    let attribute_digests: Vec<_> = (0..attribute_sha_params.len())
        .map(|_| SharedDigestRelation::new())
        .collect();
    let issuer_field = SharedFieldRelation::new();
    let attribute_fields: Vec<_> = (0..attribute_sha_params.len())
        .map(|_| SharedFieldRelation::new())
        .collect();
    let sha_table_relations = SharedShaTableRelations::new();
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
    let issuer_scalar_z = SharedScalarZRelation::new();
    #[cfg(not(feature = "ec-coprocessor"))]
    let device_scalar_z = SharedScalarZRelation::new();

    let issuer_exposure = issuer_mso_exposure(statement);
    let attribute_exposures: Vec<_> = (0..statement.attributes.len())
        .map(|index| attribute_exposure(statement, index))
        .collect();

    #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
    let issuer_p256 = P256Prover::new(&issuer_draft)
        .map_err(Error::P256Prepare)?
        .with_z_binding(issuer_scalar_z.clone());
    #[cfg(not(feature = "ec-coprocessor"))]
    let device_p256 = P256Prover::new(&device_draft)
        .map_err(Error::P256Prepare)?
        .with_preprocessed_namespace("mdoc/device")
        .with_z_binding(device_scalar_z.clone());
    let mut sha_consumers = vec![
        (&issuer_sha_witness, issuer_exposure.clone()),
        (&device_sha_witness, FieldExposure::empty()),
    ];
    for ((witness, _), exposure) in attribute_sha_params.iter().zip(attribute_exposures.iter()) {
        sha_consumers.push((witness, exposure.clone()));
    }
    let sha_table_multiplicities = ShaTableMultiplicities::from_consumers(&sha_consumers);
    let sha_tables = ShaTablesProver::new(sha_table_multiplicities, sha_table_relations.clone());
    let issuer_sha = Sha256Prover::new(&issuer_sha_witness, shared_sha_log, SHA_GROUP_WIDTH)
        .with_shared_tables(sha_table_relations.clone())
        .with_digest_handle(issuer_digest.clone())
        .with_field_handle(issuer_exposure.clone(), issuer_field.clone());
    let device_sha = Sha256Prover::new(&device_sha_witness, shared_sha_log, SHA_GROUP_WIDTH)
        .with_shared_tables(sha_table_relations.clone())
        .with_digest_handle(device_digest.clone());
    let attribute_sha: Vec<_> = attribute_sha_params
        .iter()
        .zip(attribute_exposures.iter())
        .zip(attribute_digests.iter())
        .zip(attribute_fields.iter())
        .map(
            |((((witness, _), exposure), digest_handle), field_handle)| {
                Sha256Prover::new(witness, shared_sha_log, SHA_GROUP_WIDTH)
                    .with_shared_tables(sha_table_relations.clone())
                    .with_digest_handle(digest_handle.clone())
                    .with_field_handle(exposure.clone(), field_handle.clone())
            },
        )
        .collect();

    #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
    let issuer_bridge_rows = crate::bridge_rows(&issuer_p256.proof_claim().public_inputs.instances);
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
    let issuer_bridge_log = crate::bridge_log_size(issuer_bridge_rows.len());
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
    let issuer_bridge = DigestBindProver::new(
        issuer_bridge_rows,
        issuer_bridge_log,
        issuer_scalar_z,
        issuer_digest.clone(),
    );
    #[cfg(not(feature = "ec-coprocessor"))]
    let device_bridge_rows = crate::bridge_rows(&device_p256.proof_claim().public_inputs.instances);
    #[cfg(not(feature = "ec-coprocessor"))]
    let device_bridge_log = crate::bridge_log_size(device_bridge_rows.len());
    #[cfg(not(feature = "ec-coprocessor"))]
    let device_bridge = DigestBindProver::new(
        device_bridge_rows,
        device_bridge_log,
        device_scalar_z,
        device_digest.clone(),
    );
    #[cfg(feature = "ec-coprocessor")]
    let device_public_digest_bind = PublicDigestBind::new(
        statement
            .device_input
            .expect_ecdsa("P-256 shape/sizing probe")?
            .message_hash
            .0,
        device_digest.clone(),
    );
    let mdoc_window_bind = MdocWindowBind::new_for_attributes(
        mdoc_window_bind_rows_from(statement, Some(&extracted.issuer_sig_structure)),
        issuer_field.clone(),
        attribute_fields.clone(),
        attribute_digests.clone(),
    );
    let mdoc_validity = MdocValidityBind::new(
        statement.policy.current_date,
        mdoc_validity_rows_from(statement, Some(&extracted.issuer_sig_structure)),
        issuer_field.clone(),
    );
    #[cfg(feature = "ec-coprocessor")]
    let mac_key_shares = random_mdoc_p4b_mac_key_shares();
    #[cfg(feature = "ec-coprocessor")]
    let mac_state = MdocP4bMacSharedState::default();
    #[cfg(feature = "ec-coprocessor")]
    let mdoc_mac = MdocMacBind::prover(
        &mac_key_shares,
        mdoc_p4b_mac_values(statement),
        mac_state.clone(),
        issuer_digest.clone(),
        issuer_field.clone(),
    );
    #[cfg(feature = "ec-coprocessor")]
    let coprocessor = MdocCoprocessorBindingProver::new(
        statement
            .issuer_input
            .expect_ecdsa("ec-coprocessor module shapes")?
            .clone(),
        statement
            .device_input
            .expect_ecdsa("ec-coprocessor module shapes")?
            .clone(),
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
        nationalities: vec![statement.nationality_binding.code()],
    };
    let age = AgeRangeCheck::new(PcsConfig::default())
        .prover(&age_public, &age_dob)
        .map_err(Error::AgePrepare)?;
    let age_field = attribute_fields[statement
        .age_attribute_index
        .expect("demo mdoc carries an AgeOver attribute")]
    .clone();
    let age = match statement.birth_date_binding {
        MdocBirthDateBinding::Packed(_) => age.with_dob_binding(age_field),
        MdocBirthDateBinding::Text(_) => age.with_text_dob_binding(age_field),
    };
    let nat = NationalityPredicate::new(PcsConfig::default())
        .prover(&nat_public, &nat_private)
        .map_err(Error::NatPrepare)?
        .with_nat_binding(
            attribute_fields[statement
                .nationality_attribute_index
                .expect("demo mdoc carries an Alpha2Set attribute")]
            .clone(),
        );

    #[cfg(not(feature = "ec-coprocessor"))]
    let shapes = vec![
        MdocModuleShape::with_components(
            "mdoc_sha_tables",
            sha_tables.layout(),
            sha_tables.component_shapes(),
        ),
        #[cfg(feature = "p256")]
        MdocModuleShape::single("mdoc_issuer_p256", issuer_p256.layout()),
        MdocModuleShape::single("mdoc_issuer_sha", issuer_sha.layout()),
        #[cfg(feature = "p256")]
        MdocModuleShape::single("mdoc_issuer_bridge", issuer_bridge.layout()),
        MdocModuleShape::single("mdoc_device_p256", device_p256.layout()),
        MdocModuleShape::single("mdoc_device_sha", device_sha.layout()),
        MdocModuleShape::single("mdoc_device_bridge", device_bridge.layout()),
        MdocModuleShape::single("mdoc_birth_sha", attribute_sha[0].layout()),
        MdocModuleShape::single("mdoc_nat_sha", attribute_sha[1].layout()),
        MdocModuleShape::single("mdoc_window_bind", mdoc_window_bind.layout()),
        MdocModuleShape::single("mdoc_validity", mdoc_validity.layout()),
        MdocModuleShape::single("mdoc_age", age.layout()),
        MdocModuleShape::single("mdoc_nat", nat.layout()),
    ];
    #[cfg(feature = "ec-coprocessor")]
    let shapes = vec![
        MdocModuleShape::with_components(
            "mdoc_sha_tables",
            sha_tables.layout(),
            sha_tables.component_shapes(),
        ),
        MdocModuleShape::single("mdoc_issuer_sha", issuer_sha.layout()),
        MdocModuleShape::single("mdoc_device_sha", device_sha.layout()),
        MdocModuleShape::single(
            "mdoc_device_public_digest_bind",
            device_public_digest_bind.layout(),
        ),
        MdocModuleShape::single("mdoc_birth_sha", attribute_sha[0].layout()),
        MdocModuleShape::single("mdoc_nat_sha", attribute_sha[1].layout()),
        MdocModuleShape::single("mdoc_window_bind", mdoc_window_bind.layout()),
        MdocModuleShape::single("mdoc_validity", mdoc_validity.layout()),
        MdocModuleShape::single("mdoc_age", age.layout()),
        MdocModuleShape::single("mdoc_nat", nat.layout()),
        MdocModuleShape::single("mdoc_coprocessor", coprocessor.layout()),
        MdocModuleShape::single("mdoc_mac", mdoc_mac.layout()),
    ];
    Ok(shapes)
}

pub fn demo_mdoc_sizing_waste() -> Result<MdocSizingWaste, Error> {
    let fixture = demo_mdoc_circuit_fixture();
    mdoc_sizing_waste(&fixture.extracted, &fixture.statement)
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
    // Issuer-alg dispatch: ES256 keeps the exact P-256 flow; ML-DSA-65 parses
    // the AKP key and natively pre-checks the signature with the stwo-mldsa
    // reference verifier (FIPS 204 Algorithm 3, pure mode, empty context).
    let (issuer_key, issuer_mldsa_input) = match issuer_auth.alg {
        CoseAlg::Es256 => {
            // The issuer P-256 (COSE ES256) proving path is only compiled in
            // under the `p256` feature; otherwise a clean error, never a panic.
            // (Device auth stays P-256 unconditionally — see below.)
            #[cfg(not(feature = "p256"))]
            {
                let _ = issuer_unprotected;
                return Err(MdocError::UnsupportedIssuerAlg(
                    "P-256 ES256 issuer (COSE alg -7): rebuild eu-id-prover with the `p256` feature",
                ));
            }
            #[cfg(feature = "p256")]
            {
                let issuer_key = issuer_key_from_unprotected(issuer_unprotected, request)?;
                verify_signature(
                    &issuer_key,
                    &issuer_auth.sig_structure,
                    &issuer_auth.signature_bytes,
                    "issuerAuth",
                )?;
                (issuer_key, None::<IssuerMlDsaSlot>)
            }
        }
        #[cfg(feature = "ml-dsa")]
        CoseAlg::MlDsa65 => {
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
            let decoded_sig =
                stwo_mldsa::reference::encoding::sig_decode(&issuer_auth.signature_bytes)
                    .map_err(|_| MdocError::InvalidSignature("issuerAuth"))?;
            let input = MlDsaVerifyInput::from_decoded(
                &decoded_pk,
                &decoded_sig,
                trace.tr,
                issuer_auth.sig_structure.clone(),
            );
            // The AffinePoint slot is a zeroed placeholder for ML-DSA issuers;
            // the real key lives in `issuer_auth_input`.
            let zero_key = AffinePoint {
                x: U256([0u8; 32]),
                y: U256([0u8; 32]),
            };
            (zero_key, Some(input))
        }
    };

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
    // FAIL-CLOSED scheme matrix over (MSO deviceKey type, deviceSignature alg,
    // issuer scheme): only the all-P-256 and all-ML-DSA rows are accepted; any
    // mixed combination — in either direction — is rejected here, before any
    // signature work on the mismatched arm.
    let issuer_is_mldsa = issuer_mldsa_input.is_some();
    let (device_key, device_signature_value, device_auth_input) =
        match (&mso.device_key, device_signature.alg) {
            (ParsedDeviceKey::Ec2(device_key), CoseAlg::Es256) => {
                if issuer_is_mldsa {
                    return Err(MdocError::MixedSignatureSchemes(
                        "ES256 device authentication with an ML-DSA-65 issuer",
                    ));
                }
                verify_signature(
                    device_key,
                    &device_signature.sig_structure,
                    &device_signature.signature_bytes,
                    "deviceSignature",
                )?;
                let signature = signature_from_compact(&device_signature.signature_bytes)?;
                let input = MdocAuthInput::Ecdsa(ecdsa_input(
                    &device_signature.sig_structure,
                    signature.clone(),
                    device_key.clone(),
                ));
                (device_key.clone(), signature, input)
            }
            // Mirror of the issuer ML-DSA arm: native FIPS 204 pre-check over
            // the device Sig_structure, then the decoded in-circuit input.
            #[cfg(feature = "ml-dsa")]
            (ParsedDeviceKey::MlDsa(pk), CoseAlg::MlDsa65) => {
                if !issuer_is_mldsa {
                    return Err(MdocError::MixedSignatureSchemes(
                        "ML-DSA-65 device authentication with an ES256 issuer",
                    ));
                }
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
                // Zeroed AffinePoint/Signature placeholders (see
                // `ExtractedPidMdoc::device_auth_input`).
                let zero_key = AffinePoint {
                    x: U256([0u8; 32]),
                    y: U256([0u8; 32]),
                };
                let zero_sig = Signature {
                    r: U256([0u8; 32]),
                    s: U256([0u8; 32]),
                };
                (zero_key, zero_sig, MdocAuthInput::MlDsa(Box::new(input)))
            }
            #[cfg(feature = "ml-dsa")]
            _ => {
                return Err(MdocError::MixedSignatureSchemes(
                    "MSO deviceKey scheme does not match the deviceSignature algorithm",
                ))
            }
        };

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

    let (issuer_signature, issuer_auth_input) = match issuer_mldsa_input {
        None => {
            let signature = signature_from_compact(&issuer_auth.signature_bytes)?;
            let input = IssuerAuthInput::Ecdsa(ecdsa_input(
                &issuer_auth.sig_structure,
                signature.clone(),
                issuer_key.clone(),
            ));
            (signature, input)
        }
        #[cfg(feature = "ml-dsa")]
        Some(input) => {
            // Zeroed placeholder Signature for ML-DSA issuers (see
            // `ExtractedPidMdoc::issuer_auth_input`).
            let zero = Signature {
                r: U256([0u8; 32]),
                s: U256([0u8; 32]),
            };
            (zero, IssuerAuthInput::MlDsa(Box::new(input)))
        }
    };

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
        issuer_key,
        device_key,
        issuer_signature,
        device_signature: device_signature_value,
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

/// The COSE `alg` advertised by a `COSE_Sign1` protected header.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CoseAlg {
    Es256,
    #[cfg(feature = "ml-dsa")]
    MlDsa65,
}

#[derive(Clone)]
struct CoseSign1 {
    alg: CoseAlg,
    unprotected: Value,
    payload: Vec<u8>,
    signature_bytes: Vec<u8>,
    sig_structure: Vec<u8>,
}

/// The MSO `deviceKeyInfo.deviceKey`, scheme-tagged at parse time: an EC2
/// P-256 point (ES256 device auth) or an AKP ML-DSA-65 encoded public key.
#[derive(Clone, Debug, PartialEq, Eq)]
enum ParsedDeviceKey {
    Ec2(AffinePoint),
    #[cfg(feature = "ml-dsa")]
    MlDsa(Vec<u8>),
}

struct ParsedMso {
    version: String,
    doc_type: String,
    value_digests: HashMap<u32, [u8; 32]>,
    device_key: ParsedDeviceKey,
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
fn birth_date_exposure(statement: &MdocCircuitStatement) -> FieldExposure {
    let Some(index) = statement.age_attribute_index else {
        return FieldExposure::empty();
    };
    attribute_exposure(statement, index)
}

/// Field exposure over the `nationality` item preimage: the value window
/// (2 bytes) plus the `elementIdentifier` window (D1).
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
fn issuer_mso_exposure(statement: &MdocCircuitStatement) -> FieldExposure {
    let mut windows: Vec<_> = statement
        .attributes
        .iter()
        .enumerate()
        .map(|(index, attribute)| {
            (
                MdocStatementAttribute::digest_field_id(index),
                attribute.mso_digest_offset,
                32,
            )
        })
        .collect();
    // ML-DSA device: no 32-byte coordinate windows exist in the MSO (the AKP
    // key is bound by the host-side canonical byte-equality check over the
    // public issuer Sig_structure instead — see `check_mldsa_device_key_binding`).
    if statement.device_input.as_ecdsa().is_some() {
        windows.extend([
            (
                field_id::MDOC_DEVICE_KEY_X,
                statement.mso_device_key_x_offset,
                32,
            ),
            (
                field_id::MDOC_DEVICE_KEY_Y,
                statement.mso_device_key_y_offset,
                32,
            ),
        ]);
    }
    windows.extend([
        (
            field_id::MDOC_VALID_FROM,
            statement.mso_valid_from_date_offset,
            10,
        ),
        (
            field_id::MDOC_VALID_UNTIL,
            statement.mso_valid_until_date_offset,
            10,
        ),
    ]);
    if statement.ts13_revocation_range.is_some() {
        windows.push((
            MDOC_MSO_PAYLOAD_FIELD_ID,
            statement.mso_payload_offset,
            statement.mso_payload_len,
        ));
    }
    windows.extend(
        statement
            .attributes
            .iter()
            .enumerate()
            .map(|(index, attribute)| {
                (
                    MdocStatementAttribute::digest_anchor_field_id(index),
                    attribute.mso_digest_anchor_offset,
                    attribute.mso_digest_anchor.len(),
                )
            }),
    );
    if statement.device_input.as_ecdsa().is_some() {
        windows.extend([
            (
                field_id::MDOC_DEVICE_KEY_X_ANCHOR,
                statement.mso_device_key_x_anchor_offset,
                statement.mso_device_key_x_anchor.len(),
            ),
            (
                field_id::MDOC_DEVICE_KEY_Y_ANCHOR,
                statement.mso_device_key_y_anchor_offset,
                statement.mso_device_key_y_anchor.len(),
            ),
        ]);
    }
    windows.extend([
        (
            field_id::MDOC_VALID_FROM_ANCHOR,
            statement.mso_valid_from_anchor_offset,
            statement.mso_valid_from_anchor.len(),
        ),
        (
            field_id::MDOC_VALID_UNTIL_ANCHOR,
            statement.mso_valid_until_anchor_offset,
            statement.mso_valid_until_anchor.len(),
        ),
    ]);
    // ML-DSA issuer (M7 MsgLink swap): expose the WHOLE Sig_structure as one
    // window under the hosted-msg field id. The hosted mldsa module's µ-absorb
    // bridge consumes exactly these yields, so the SHAKE-absorbed message IS
    // the SHA-constrained preimage. (`HOSTED_MSG_FIELD_ID` only needs to be
    // unique within the issuer field relation; the DOB/NATIONALITY ids live on
    // the per-attribute relations.)
    #[cfg(feature = "ml-dsa")]
    if let Some(input) = statement.issuer_input.as_mldsa() {
        windows.push((HOSTED_MSG_FIELD_ID, 0, input.message.len()));
    }
    FieldExposure::from_preimage_windows_multi(&windows)
}

/// The device SHA module's field exposure: empty for a P-256 device (the
/// device binding is the digest handle → device bridge), the whole device
/// `Sig_structure` under the hosted-msg field id for an ML-DSA device (the
/// hosted module's µ-absorb bridge consumes exactly these yields — mirror of
/// the issuer instance's MsgLink swap).
fn device_sig_structure_exposure(statement: &MdocCircuitStatement) -> FieldExposure {
    #[cfg(feature = "ml-dsa")]
    if let Some(input) = statement.device_input.as_mldsa() {
        return FieldExposure::from_preimage_windows_multi(&[(
            HOSTED_MSG_FIELD_ID,
            0,
            input.message.len(),
        )]);
    }
    let _ = statement;
    FieldExposure::empty()
}

fn mso_payload_exposure(statement: &MdocCircuitStatement) -> FieldExposure {
    if statement.ts13_revocation_range.is_none() {
        return FieldExposure::empty();
    }
    FieldExposure::from_preimage_windows_multi(&[(
        MDOC_MSO_PAYLOAD_FIELD_ID,
        0,
        statement.mso_payload_len,
    )])
}

fn ts13_revocation_message_bytes(id_lo: u64, id_hi: u64, epoch: u32) -> [u8; 20] {
    let mut bytes = [0u8; TS13_REVOCATION_MESSAGE_LEN];
    bytes[..8].copy_from_slice(&id_lo.to_le_bytes());
    bytes[8..16].copy_from_slice(&id_hi.to_le_bytes());
    bytes[16..].copy_from_slice(&epoch.to_le_bytes());
    bytes
}

fn ts13_revocation_message_exposure(statement: &MdocCircuitStatement) -> FieldExposure {
    let Some(signature) = &statement.ts13_revocation_signature else {
        return FieldExposure::empty();
    };
    #[cfg_attr(not(feature = "ml-dsa"), allow(unused_mut))]
    let mut windows = vec![(
        MDOC_REVOCATION_MESSAGE_FIELD_ID,
        0,
        TS13_REVOCATION_MESSAGE_LEN,
    )];
    // ML-DSA revocation: additionally expose the whole 20-byte message under
    // the hosted-msg field id — the hosted module's µ-absorb bridge consumes
    // exactly these yields, so the SHAKE-absorbed message IS the
    // SHA-constrained preimage (same MsgLink swap as the issuer instance).
    // `MdocRevocationRangeBind` keeps consuming the field id above; the bounds
    // check never moves host-side.
    #[cfg(feature = "ml-dsa")]
    if signature.is_mldsa() {
        windows.push((HOSTED_MSG_FIELD_ID, 0, TS13_REVOCATION_MESSAGE_LEN));
    }
    #[cfg(not(feature = "ml-dsa"))]
    let _ = signature;
    FieldExposure::from_preimage_windows_multi(&windows)
}

/// The P-256 in-STARK revocation verification input; `None` when no revocation
/// signature is present OR the revocation authority is ML-DSA (the ML-DSA arm
/// is proven by the hosted `revocation_mldsa` module instead).
fn ts13_revocation_p256_input(
    statement: &MdocCircuitStatement,
) -> Result<Option<EcdsaVerifyInput>, Error> {
    let Some(signature) = statement
        .ts13_revocation_signature
        .as_ref()
        .and_then(|signature| signature.as_ecdsa())
        .cloned()
    else {
        return Ok(None);
    };
    let revocation = statement.ts13_revocation.as_ref().ok_or_else(|| {
        Error::Prove("TS13 revocation signature requires public revocation inputs".to_string())
    })?;
    let public_key = revocation
        .revocation_public_key
        .as_ecdsa()
        .ok_or_else(|| {
            Error::Prove(
                "TS13 P-256 revocation signature requires a P-256 revocation key".to_string(),
            )
        })?
        .clone();
    let range = statement.ts13_revocation_range.as_ref().ok_or_else(|| {
        Error::Prove("TS13 revocation signature requires private range witness".to_string())
    })?;
    let message = ts13_revocation_message_bytes(range.id_lo, range.id_hi, revocation.epoch);
    Ok(Some(EcdsaVerifyInput {
        message_hash: U256(Sha256::digest(message).into()),
        signature,
        public_key,
    }))
}

/// Enforce signature-scheme uniformity across the statement's roles: the
/// device arm — and, when present, the revocation key and signature — must
/// match the issuer's scheme. Checked once on BOTH prove and verify, before
/// any STARK work, so mixed statements fail closed in every direction.
fn ensure_statement_scheme_uniformity(statement: &MdocCircuitStatement) -> Result<(), Error> {
    let issuer_is_mldsa = statement.issuer_input.is_mldsa();
    if statement.device_input.is_mldsa() != issuer_is_mldsa {
        return Err(Error::Prove(
            "mdoc statement mixes issuer and device signature schemes".to_string(),
        ));
    }
    if let Some(revocation) = &statement.ts13_revocation {
        if revocation.revocation_public_key.is_mldsa() != issuer_is_mldsa {
            return Err(Error::Prove(
                "mdoc statement mixes issuer and revocation-key signature schemes".to_string(),
            ));
        }
    }
    if let Some(signature) = &statement.ts13_revocation_signature {
        if signature.is_mldsa() != issuer_is_mldsa {
            return Err(Error::Prove(
                "mdoc statement mixes issuer and revocation-signature schemes".to_string(),
            ));
        }
    }
    Ok(())
}

/// D2 device-key ↔ MSO binding for the ML-DSA scheme, run host-side on BOTH
/// prove and verify before any STARK work.
///
/// # Soundness
///
/// In ML-DSA mode the issuer `Sig_structure` and the device public key are
/// both PUBLIC statement inputs, already mixed into Fiat-Shamir and bound
/// in-circuit by the issuer instance's µ-absorption — so the binding reduces
/// to a canonical byte equality: decode the Sig_structure payload (the MSO),
/// navigate to `deviceKeyInfo.deviceKey` through the CBOR structure (no
/// prover-supplied offsets exist to tamper with), and require the AKP `-1`
/// bytes to equal the statement device key's `pkEncode`. Any parse failure or
/// mismatch rejects.
#[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
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
    let ParsedDeviceKey::MlDsa(mso_pk) = mso else {
        return Err(bind_err("MSO deviceKey is not an AKP ML-DSA-65 key"));
    };
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
fn parse_mso_device_key(bytes: &[u8]) -> Result<ParsedDeviceKey, MdocError> {
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
    issuer_sig_structure: Option<&[u8]>,
) -> Vec<MdocWindowBindRow> {
    let mut rows = Vec::new();
    for (index, attribute) in statement.attributes.iter().enumerate() {
        rows.push(MdocWindowBindRow::constant(
            MdocStatementAttribute::element_field_id(index),
            MdocFieldSource::AttributeItem(index),
            attribute.element_identifier.as_bytes(),
        ));
        rows.push(MdocWindowBindRow::constant(
            MdocStatementAttribute::element_anchor_field_id(index),
            MdocFieldSource::AttributeItem(index),
            &attribute.element_identifier_anchor,
        ));
        if let MdocDisclosureMode::ValueEquality(_) = &attribute.mode {
            rows.push(MdocWindowBindRow::constant(
                MdocStatementAttribute::value_field_id(index),
                MdocFieldSource::AttributeItem(index),
                &attribute.value,
            ));
            rows.push(MdocWindowBindRow::constant(
                MdocStatementAttribute::value_head_field_id(index),
                MdocFieldSource::AttributeItem(index),
                &attribute.value_head,
            ));
        }
        let digest = issuer_sig_structure
            .map(|preimage| {
                preimage[attribute.mso_digest_offset..attribute.mso_digest_offset + 32]
                    .try_into()
                    .expect("attribute digest window length")
            })
            .unwrap_or([0u8; 32]);
        rows.push(MdocWindowBindRow::digest(
            MdocStatementAttribute::digest_field_id(index),
            index,
            digest,
        ));
        rows.push(MdocWindowBindRow::constant(
            MdocStatementAttribute::digest_anchor_field_id(index),
            MdocFieldSource::IssuerMso,
            &attribute.mso_digest_anchor,
        ));
    }
    // ML-DSA device: the coordinate windows/anchors do not exist in the MSO;
    // the exposure side skips them symmetrically (LogUp balance) and the
    // binding is the host-side canonical byte-equality check.
    if let Some(device_input) = statement.device_input.as_ecdsa() {
        #[cfg(not(feature = "ec-coprocessor"))]
        rows.extend([
            MdocWindowBindRow::constant(
                field_id::MDOC_DEVICE_KEY_X,
                MdocFieldSource::IssuerMso,
                &device_input.public_key.x.0,
            ),
            MdocWindowBindRow::constant(
                field_id::MDOC_DEVICE_KEY_Y,
                MdocFieldSource::IssuerMso,
                &device_input.public_key.y.0,
            ),
        ]);
        #[cfg(feature = "ec-coprocessor")]
        let _ = device_input;
        rows.extend([
            MdocWindowBindRow::constant(
                field_id::MDOC_DEVICE_KEY_X_ANCHOR,
                MdocFieldSource::IssuerMso,
                &statement.mso_device_key_x_anchor,
            ),
            MdocWindowBindRow::constant(
                field_id::MDOC_DEVICE_KEY_Y_ANCHOR,
                MdocFieldSource::IssuerMso,
                &statement.mso_device_key_y_anchor,
            ),
        ]);
    }
    rows.extend([
        MdocWindowBindRow::constant(
            field_id::MDOC_VALID_FROM_ANCHOR,
            MdocFieldSource::IssuerMso,
            &statement.mso_valid_from_anchor,
        ),
        MdocWindowBindRow::constant(
            field_id::MDOC_VALID_UNTIL_ANCHOR,
            MdocFieldSource::IssuerMso,
            &statement.mso_valid_until_anchor,
        ),
    ]);
    rows
}

fn mdoc_validity_rows_from(
    statement: &MdocCircuitStatement,
    issuer_sig_structure: Option<&[u8]>,
) -> Vec<MdocValidityRow> {
    let dates = issuer_sig_structure.map(|preimage| {
        let valid_from = preimage
            [statement.mso_valid_from_date_offset..statement.mso_valid_from_date_offset + 10]
            .try_into()
            .expect("validFrom window length");
        let valid_until = preimage
            [statement.mso_valid_until_date_offset..statement.mso_valid_until_date_offset + 10]
            .try_into()
            .expect("validUntil window length");
        (valid_from, valid_until)
    });
    let (valid_from, valid_until) = dates.unwrap_or((
        full_date_text_bytes(statement.valid_from),
        full_date_text_bytes(statement.valid_until),
    ));
    mdoc_validity_rows(valid_from, valid_until)
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
    let alg = if protected == ES256_PROTECTED_HEADER {
        CoseAlg::Es256
    } else if protected == MLDSA_PROTECTED_HEADER {
        // COSE alg -49 (ML-DSA-65) is only accepted when the `ml-dsa` feature is
        // compiled in; otherwise it is a clean parse error, never a panic.
        #[cfg(not(feature = "ml-dsa"))]
        return Err(MdocError::UnsupportedIssuerAlg(
            "ML-DSA-65 (COSE alg -49): rebuild eu-id-prover with the `ml-dsa` feature",
        ));
        #[cfg(feature = "ml-dsa")]
        CoseAlg::MlDsa65
    } else {
        return Err(MdocError::InvalidCoseSign1(
            "protected header must be ES256 or ML-DSA-65",
        ));
    };
    expect_map(&items[1], "COSE_Sign1.unprotected")?;
    let unprotected = items[1].clone();
    let payload = match (&items[2], detached_payload) {
        (Value::Bytes(payload), _) => payload.clone(),
        (Value::Null, Some(detached_payload)) => detached_payload.to_vec(),
        (Value::Null, None) => return Err(MdocError::InvalidCoseSign1("detached payload")),
        _ => return Err(MdocError::WrongType("COSE_Sign1.payload")),
    };
    let signature_bytes = expect_bytes(&items[3], "COSE_Sign1.signature")?.to_vec();
    match alg {
        CoseAlg::Es256 => {
            signature_from_compact(&signature_bytes)?;
        }
        #[cfg(feature = "ml-dsa")]
        CoseAlg::MlDsa65 => {
            if signature_bytes.len() != stwo_mldsa::constants::SIG_BYTES {
                return Err(MdocError::InvalidCoseSign1("ML-DSA-65 signature length"));
            }
        }
    }
    let sig_structure = sig_structure(&protected, &payload);

    Ok(CoseSign1 {
        alg,
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
    Ok(Sha256::digest(sig_structure(ES256_PROTECTED_HEADER, &payload)).into())
}

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

/// Parse the MSO `deviceKey`: EC2 P-256 (existing profile) or, under `ml-dsa`,
/// an AKP ML-DSA-65 key. Any other key type is rejected; the scheme tag is
/// checked against the deviceSignature alg and the issuer scheme at extraction
/// (fail-closed matrix).
fn parse_device_cose_key(value: &Value) -> Result<ParsedDeviceKey, MdocError> {
    let key = expect_map(value, "COSE_Key")?;
    let kty = int_field(key, 1, "COSE_Key.kty")?;
    #[cfg(feature = "ml-dsa")]
    if kty == i128::from(stwo_mldsa::constants::COSE_KTY_AKP) {
        return Ok(ParsedDeviceKey::MlDsa(
            parse_akp_mldsa_cose_key(key)?.to_vec(),
        ));
    }
    let _ = kty;
    Ok(ParsedDeviceKey::Ec2(parse_cose_key(value)?))
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

/// ML-DSA-65 issuer key from the unprotected `issuerKey` COSE_Key: AKP key
/// type (`kty = 7`), `alg = -49`, raw 1952-byte public key in label `-1`.
///
/// Trust is FAIL-CLOSED: the request MUST carry a non-empty
/// `trusted_mldsa_issuer_public_keys` pin list and the header key must be
/// byte-equal to a member — the self-carried AKP key is never a trust
/// decision. P-256 trust material (x5chain header / P-256 pins) combined with
/// an ML-DSA issuer is rejected.
#[cfg(feature = "ml-dsa")]
fn mldsa_issuer_pk_from_unprotected(
    unprotected: &[(Value, Value)],
    request: &MdocPidRequest,
) -> Result<Vec<u8>, MdocError> {
    if value_int_key(unprotected, 33).is_some()
        || !request.trusted_issuer_certificates.is_empty()
        || !request.trusted_issuer_public_keys.is_empty()
    {
        return Err(MdocError::InvalidCoseKey(
            "ML-DSA-65 issuer with P-256 trust material is unsupported",
        ));
    }
    let key = expect_map(value_field(unprotected, "issuerKey")?, "COSE_Key")?;
    let pk = parse_akp_mldsa_cose_key(key)?;
    if !request
        .trusted_mldsa_issuer_public_keys
        .iter()
        .any(|trusted| trusted.as_slice() == pk)
    {
        // Also the empty-pin-list case: no pins ⇒ nothing is trusted.
        return Err(MdocError::UntrustedIssuerCertificate);
    }
    Ok(pk.to_vec())
}

/// Parse an AKP ML-DSA-65 COSE_Key map (`kty = 7`, `alg = -49`, raw 1952-byte
/// public key in label `-1`). Shared by the issuer header key and the MSO
/// `deviceKey` parser.
#[cfg(feature = "ml-dsa")]
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
    Ecdsa(AffinePoint),
    /// FIPS 204 `pkEncode` bytes (1,952).
    #[cfg(feature = "ml-dsa")]
    MlDsa(Vec<u8>),
}

impl MdocRevocationKey {
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
            Self::Ecdsa(_) => None,
            Self::MlDsa(pk) => Some(pk),
        }
    }

    pub fn is_mldsa(&self) -> bool {
        match self {
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
    Ecdsa(Signature),
    /// FIPS 204 `sigEncode` bytes (3,309).
    #[cfg(feature = "ml-dsa")]
    MlDsa(Vec<u8>),
}

impl MdocRevocationSignature {
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
            Self::Ecdsa(_) => None,
            Self::MlDsa(signature) => Some(signature),
        }
    }

    pub fn is_mldsa(&self) -> bool {
        match self {
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

    fn digest_field_id(index: usize) -> u32 {
        MDOC_ATTRIBUTE_DIGEST_BASE + index as u32
    }

    fn digest_anchor_field_id(index: usize) -> u32 {
        MDOC_ATTRIBUTE_DIGEST_ANCHOR_BASE + index as u32
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
        let device_is_ecdsa = extracted.device_auth_input.as_ecdsa().is_some();
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
#[cfg(feature = "ml-dsa")]
#[derive(Clone, Serialize, Deserialize)]
pub struct MdocMlDsaClaims {
    pub group_evals: Vec<QM31>,
    pub claimed_sums: Vec<QM31>,
    pub sib_stream_len: usize,
    pub sib_squeezed_len: usize,
}

#[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
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
    /// `Some` iff the issuer is P-256 (ES256); `None` for ML-DSA issuers.
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
    issuer_p256_claim: Option<P256CurrentAirProofClaim>,
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
    issuer_p256_interaction_claim: Option<P256CurrentAirInteractionClaim>,
    /// `Some` iff the issuer is ML-DSA-65 (biconditional, gated at verify).
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
    pub mldsa: Option<MdocMlDsaClaims>,
    /// `Some` iff the device is ML-DSA-65 (biconditional, gated at verify).
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
    pub device_mldsa: Option<MdocMlDsaClaims>,
    /// `Some` iff an ML-DSA revocation signature is present (biconditional).
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
    pub revocation_mldsa: Option<MdocMlDsaClaims>,
    /// `Some` iff the device is P-256 (ES256); `None` for ML-DSA devices.
    #[cfg(not(feature = "ec-coprocessor"))]
    device_p256_claim: Option<P256CurrentAirProofClaim>,
    #[cfg(not(feature = "ec-coprocessor"))]
    device_p256_interaction_claim: Option<P256CurrentAirInteractionClaim>,
    #[cfg(feature = "ec-coprocessor")]
    device_public_digest_bind_interaction_claim: PublicDigestBindInteractionClaim,
    #[cfg(feature = "ec-coprocessor")]
    coprocessor_bundle: Option<eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle>,
    #[cfg(feature = "ec-coprocessor")]
    mdoc_mac_interaction_claim: MdocMacInteractionClaim,
    issuer_sha_log_n_rows: u32,
    issuer_sha_interaction_claim: Sha256InteractionClaim,
    device_sha_log_n_rows: u32,
    device_sha_interaction_claim: Sha256InteractionClaim,
    mso_sha_log_n_rows: Option<u32>,
    mso_sha_interaction_claim: Option<Sha256InteractionClaim>,
    revocation_sha_log_n_rows: Option<u32>,
    revocation_sha_interaction_claim: Option<Sha256InteractionClaim>,
    attribute_sha_log_n_rows: Vec<u32>,
    attribute_sha_interaction_claims: Vec<Sha256InteractionClaim>,
    revocation_p256_claim: Option<P256CurrentAirProofClaim>,
    revocation_p256_interaction_claim: Option<P256CurrentAirInteractionClaim>,
    revocation_bridge_log_size: Option<u32>,
    revocation_bridge_interaction_claim: Option<DigestBindInteractionClaim>,
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
    issuer_bridge_log_size: Option<u32>,
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
    issuer_bridge_interaction_claim: Option<DigestBindInteractionClaim>,
    #[cfg(not(feature = "ec-coprocessor"))]
    device_bridge_log_size: Option<u32>,
    #[cfg(not(feature = "ec-coprocessor"))]
    device_bridge_interaction_claim: Option<DigestBindInteractionClaim>,
    mdoc_window_bind_interaction_claim: MdocWindowBindInteractionClaim,
    mdoc_validity_interaction_claim: MdocValidityInteractionClaim,
    mso_payload_bind_interaction_claim: Option<MdocMsoPayloadInteractionClaim>,
    ts13_revocation_range_interaction_claim: Option<MdocRevocationRangeInteractionClaim>,
    age_public: Option<predicates::PublicInput>,
    age_claimed_sums: Option<Vec<QM31>>,
    nat_public: Option<predicates::NatPublicInput>,
    nat_claimed_sums: Option<Vec<QM31>>,
    #[cfg(feature = "ec-coprocessor")]
    #[serde(skip)]
    p4b_prove_profile: Option<eu_id_ec_coprocessor::ecdsa::MdocP4bProveProfile>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MdocCircuitProveProfile {
    pub total: Duration,
    #[cfg(feature = "ec-coprocessor")]
    pub p4b: Option<eu_id_ec_coprocessor::ecdsa::MdocP4bProveProfile>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MdocCircuitVerifyProfile {
    pub total: Duration,
    #[cfg(feature = "ec-coprocessor")]
    pub p4b: Option<eu_id_ec_coprocessor::ecdsa::MdocP4bVerifyProfile>,
}

impl MdocCircuitProof {
    #[cfg(feature = "ec-coprocessor")]
    pub fn p4b_prove_profile(&self) -> Option<&eu_id_ec_coprocessor::ecdsa::MdocP4bProveProfile> {
        self.p4b_prove_profile.as_ref()
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MdocProofByteBreakdown {
    pub proof_bytes: usize,
    pub stark_proof_bytes: usize,
    pub coprocessor_bundle_bytes: Option<usize>,
    pub non_stark_metadata_bytes: usize,
    pub stark: MdocStarkProofByteBreakdown,
    pub coprocessor_bundle: Option<MdocCoprocessorBundleByteBreakdown>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MdocCoprocessorBundleByteBreakdown {
    pub params_and_roots: usize,
    pub proximity_openings: usize,
    pub proximity_openings_b: usize,
    pub proximity_claim: usize,
    pub claim_batch: usize,
    pub consistency_claim_values: usize,
    pub mac_tags: usize,
    pub entries: usize,
    pub entry_count: usize,
    pub opening_count: usize,
    pub opened_column_rows: usize,
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
    #[cfg(feature = "ec-coprocessor")]
    let coprocessor_bundle_bytes = proof.coprocessor_bundle.as_ref().map(bincode_len);
    #[cfg(not(feature = "ec-coprocessor"))]
    let coprocessor_bundle_bytes = None;
    let non_stark_metadata_bytes = proof_bytes
        .saturating_sub(stark_proof_bytes)
        .saturating_sub(coprocessor_bundle_bytes.unwrap_or(0));
    #[cfg(feature = "ec-coprocessor")]
    let coprocessor_bundle =
        proof
            .coprocessor_bundle
            .as_ref()
            .map(|bundle| MdocCoprocessorBundleByteBreakdown {
                params_and_roots: bincode_len(&bundle.params)
                    + bincode_len(&bundle.root)
                    + bincode_len(&bundle.root_b),
                proximity_openings: bincode_len(&bundle.proximity_openings),
                proximity_openings_b: bincode_len(&bundle.proximity_openings_b),
                proximity_claim: bincode_len(&bundle.proximity_claim),
                claim_batch: bincode_len(&bundle.claim_batch),
                consistency_claim_values: bincode_len(&bundle.consistency_claim_values),
                mac_tags: bincode_len(&bundle.mac_tags),
                entries: bincode_len(&bundle.entries),
                entry_count: bundle.entries.len(),
                opening_count: bundle.proximity_openings.len(),
                opened_column_rows: bundle
                    .proximity_openings
                    .first()
                    .map(|opening| opening.column.len())
                    .unwrap_or(0),
            });
    #[cfg(not(feature = "ec-coprocessor"))]
    let coprocessor_bundle = None;

    MdocProofByteBreakdown {
        proof_bytes,
        stark_proof_bytes,
        coprocessor_bundle_bytes,
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
        coprocessor_bundle,
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

fn single_p256_draft(input: EcdsaVerifyInput) -> Result<P256ProofDraft, Error> {
    P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![input])
        .map_err(Error::P256Prepare)
}

fn mdoc_sizing_waste(
    extracted: &ExtractedPidMdoc,
    statement: &MdocCircuitStatement,
) -> Result<MdocSizingWaste, Error> {
    let issuer_draft = single_p256_draft(
        statement
            .issuer_input
            .expect_ecdsa("P-256 shape/sizing probe")?
            .clone(),
    )?;
    let device_draft = single_p256_draft(
        statement
            .device_input
            .expect_ecdsa("P-256 shape/sizing probe")?
            .clone(),
    )?;
    let (issuer_sha_witness, issuer_sha_log) = sha_params(&extracted.issuer_sig_structure);
    let (device_sha_witness, device_sha_log) = sha_params(&extracted.device_sig_structure);
    let (birth_sha_witness, birth_sha_log) = sha_params(&extracted.birth_date_item);
    let (nat_sha_witness, nat_sha_log) = sha_params(&extracted.nationality_item);
    let shared_sha_log = [issuer_sha_log, device_sha_log, birth_sha_log, nat_sha_log]
        .into_iter()
        .max()
        .expect("sha log list is non-empty");

    let issuer_exposure = issuer_mso_exposure(statement);
    let birth_exposure = birth_date_exposure(statement);
    let nat_exposure = nationality_exposure(statement);

    let sha = vec![
        sha_sizing_waste(
            "issuer",
            &issuer_sha_witness,
            issuer_sha_log,
            shared_sha_log,
            issuer_exposure,
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

#[cfg(not(feature = "ec-coprocessor"))]
fn expected_instance(input: &EcdsaVerifyInput) -> PublicEcdsaInstance<M31> {
    PublicEcdsaInstance::from_input(0, input)
}

fn public_instance_key_matches(
    instance: &PublicEcdsaInstance<M31>,
    public_key: &AffinePoint,
) -> bool {
    let zero_sig = Signature {
        r: U256([0u8; 32]),
        s: U256([0u8; 32]),
    };
    let expected = PublicEcdsaInstance::from_input(
        0,
        &EcdsaVerifyInput {
            message_hash: U256([0u8; 32]),
            signature: zero_sig,
            public_key: public_key.clone(),
        },
    );
    instance.sig_id == expected.sig_id
        && instance.pub_x == expected.pub_x
        && instance.pub_y == expected.pub_y
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
        // Scheme discriminant + key bytes: a P-256 key and an ML-DSA key can
        // never produce the same transcript (domain separation per arm).
        match &self.inputs.revocation_public_key {
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

type MdocMsoPayloadColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type MdocMsoPayloadComponent = FrameworkComponent<MdocMsoPayloadEval>;

struct MdocMsoPayloadBind {
    bytes: Option<Vec<u8>>,
    len: usize,
    issuer_field_handle: SharedFieldRelation,
    mso_field_handle: SharedFieldRelation,
    blinder_relation: Option<ClaimedSumBlinderRelation>,
    interaction_claim: Option<MdocMsoPayloadInteractionClaim>,
    component: Option<MdocMsoPayloadComponent>,
    blinder_component: Option<FrameworkComponent<ClaimedSumBlinderEval>>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct MdocMsoPayloadInteractionClaim {
    claimed_sum: QM31,
    /// Q-015 §4b blinder pair (see `claimed_sum_blinder`).
    blinder_v: QM31,
    blinder_m: QM31,
    blinder_claimed_sum: QM31,
}

#[derive(Clone)]
struct MdocMsoPayloadEval {
    log_size: u32,
    issuer_field_relation: FieldBytesRelation,
    mso_field_relation: FieldBytesRelation,
    blinder_relation: ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
}

impl MdocMsoPayloadBind {
    fn prover(
        bytes: Vec<u8>,
        issuer_field_handle: SharedFieldRelation,
        mso_field_handle: SharedFieldRelation,
    ) -> Self {
        Self {
            len: bytes.len(),
            bytes: Some(bytes),
            issuer_field_handle,
            mso_field_handle,
            blinder_relation: None,
            interaction_claim: None,
            component: None,
            blinder_component: None,
        }
    }

    fn verifier(
        len: usize,
        issuer_field_handle: SharedFieldRelation,
        mso_field_handle: SharedFieldRelation,
        interaction_claim: MdocMsoPayloadInteractionClaim,
    ) -> Self {
        Self {
            bytes: None,
            len,
            issuer_field_handle,
            mso_field_handle,
            blinder_relation: None,
            interaction_claim: Some(interaction_claim),
            component: None,
            blinder_component: None,
        }
    }

    fn log_size(&self) -> u32 {
        mso_payload_log_size(self.len)
    }

    fn issuer_field_relation(&self) -> FieldBytesRelation {
        self.issuer_field_handle.get()
    }

    fn mso_field_relation(&self) -> FieldBytesRelation {
        self.mso_field_handle.get()
    }

    fn interaction_claim(&self) -> &MdocMsoPayloadInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("mdoc MSO payload interaction claim is set")
    }
}

fn mso_payload_log_size(len: usize) -> u32 {
    let rows = len.max(1).next_power_of_two();
    rows.ilog2().max(LOG_N_LANES)
}

fn mso_payload_col_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mdoc/ts13/mso_payload/{name}"),
    }
}

fn mso_payload_preprocessed_column_ids() -> Vec<PreProcessedColumnId> {
    vec![
        mso_payload_col_id("active"),
        mso_payload_col_id("byte_index"),
    ]
}

fn mso_payload_column_eval(log_size: u32, coset_values: Vec<M31>) -> MdocMsoPayloadColumnEval {
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

fn mso_payload_preprocessed_columns(len: usize) -> Vec<MdocMsoPayloadColumnEval> {
    let log_size = mso_payload_log_size(len);
    let rows = 1usize << log_size;
    let mut active = vec![M31::from_u32_unchecked(0); rows];
    let mut byte_index = vec![M31::from_u32_unchecked(0); rows];
    for row in 0..len {
        active[row] = M31::from_u32_unchecked(1);
        byte_index[row] = M31::from_u32_unchecked(row as u32);
    }
    vec![
        mso_payload_column_eval(log_size, active),
        mso_payload_column_eval(log_size, byte_index),
    ]
}

fn mso_payload_base_trace(bytes: &[u8]) -> Vec<MdocMsoPayloadColumnEval> {
    let log_size = mso_payload_log_size(bytes.len());
    let mut values = vec![M31::from_u32_unchecked(0); 1usize << log_size];
    for (row, &byte) in bytes.iter().enumerate() {
        values[row] = M31::from_u32_unchecked(u32::from(byte));
    }
    vec![mso_payload_column_eval(log_size, values)]
}

fn mso_payload_interaction_trace(
    bytes: &[u8],
    issuer_field_relation: &FieldBytesRelation,
    mso_field_relation: &FieldBytesRelation,
    blinder_relation: &ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
) -> (Vec<MdocMsoPayloadColumnEval>, QM31) {
    let log_size = mso_payload_log_size(bytes.len());
    let preprocessed = mso_payload_preprocessed_columns(bytes.len());
    let trace = mso_payload_base_trace(bytes);
    let n_vec_rows = 1usize << (log_size - LOG_N_LANES);
    let mut logup = LogupTraceGenerator::new(log_size);
    logup.col_from_iter((0..n_vec_rows).map(|vec_row| {
        let active = preprocessed[0].data[vec_row];
        let byte_index = preprocessed[1].data[vec_row];
        let value = trace[0].data[vec_row];
        let numerator = PackedQM31::from(active);
        let issuer_denominator: PackedQM31 = issuer_field_relation.combine(&[
            PackedM31::broadcast(M31::from_u32_unchecked(MDOC_MSO_PAYLOAD_FIELD_ID)),
            byte_index,
            value,
        ]);
        let mso_denominator: PackedQM31 = mso_field_relation.combine(&[
            PackedM31::broadcast(M31::from_u32_unchecked(MDOC_MSO_PAYLOAD_FIELD_ID)),
            byte_index,
            value,
        ]);
        (
            numerator * mso_denominator + numerator * issuer_denominator,
            issuer_denominator * mso_denominator,
        )
    }));
    // Q-015 blinder `+m/(z−combine(v))` on every row, emitted LAST to match
    // `MdocMsoPayloadEval::evaluate` (lone third entry under
    // `finalize_logup_in_pairs`).
    let blinder_num = PackedQM31::broadcast(blinder_m);
    let blinder_den = crate::claimed_sum_blinder::blinder_denominator(blinder_relation, blinder_v);
    logup.col_from_fn(|_| (blinder_num, blinder_den));
    logup.finalize_last()
}

impl FrameworkEval for MdocMsoPayloadEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(mso_payload_col_id("active"));
        let byte_index = eval.get_preprocessed_column(mso_payload_col_id("byte_index"));
        let value = eval.next_trace_mask();
        let one = m31_const::<E>(1);
        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint((one - active.clone()) * value.clone());
        let field_id = m31_const::<E>(MDOC_MSO_PAYLOAD_FIELD_ID);
        eval.add_to_relation(RelationEntry::new(
            &self.issuer_field_relation,
            E::EF::from(active.clone()),
            &[field_id.clone(), byte_index.clone(), value.clone()],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.mso_field_relation,
            E::EF::from(active),
            &[field_id, byte_index, value],
        ));
        // Q-015 blinder `+m/(z−combine(v))`, ungated, emitted LAST to match
        // the generator's column order.
        add_blinder_relation_entry(
            &mut eval,
            &self.blinder_relation,
            self.blinder_v,
            self.blinder_m,
            false,
        );
        eval.finalize_logup_in_pairs();
        eval
    }
}

impl Air for MdocMsoPayloadBind {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(0x5453_3133_4d53_4f50);
        channel.mix_u64(self.len as u64);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.blinder_relation = Some(ClaimedSumBlinderRelation::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![self.log_size(); 2],
            trace: vec![self.log_size()],
            // One paired column + the lone Q-015 blinder `+m` column in the
            // main component, plus the counterpart component's column.
            interaction: vec![self.log_size(); 3 * SECURE_EXTENSION_DEGREE],
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        let claim = self.interaction_claim();
        vec![claim.claimed_sum, claim.blinder_claimed_sum]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        mso_payload_preprocessed_column_ids()
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let claim = self.interaction_claim().clone();
        let blinder_relation = self
            .blinder_relation
            .clone()
            .expect("mdoc MSO payload blinder relation drawn before components");
        self.component = Some(MdocMsoPayloadComponent::new(
            allocator,
            MdocMsoPayloadEval {
                log_size: self.log_size(),
                issuer_field_relation: self.issuer_field_relation(),
                mso_field_relation: self.mso_field_relation(),
                blinder_relation: blinder_relation.clone(),
                blinder_v: claim.blinder_v,
                blinder_m: claim.blinder_m,
            },
            claim.claimed_sum,
        ));
        self.blinder_component = Some(FrameworkComponent::new(
            allocator,
            ClaimedSumBlinderEval {
                log_size: self.log_size(),
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
                .expect("mdoc MSO payload component is built"),
            self.blinder_component
                .as_ref()
                .expect("mdoc MSO payload blinder component is built"),
        ]
    }
}

impl AirProver for MdocMsoPayloadBind {
    fn max_log_size(&self) -> u32 {
        self.log_size()
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(mso_payload_preprocessed_columns(self.len));
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc::MdocMsoPayloadBind",
            &mso_payload_preprocessed_column_ids(),
            &mso_payload_preprocessed_columns(self.len),
        )
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(mso_payload_base_trace(
            self.bytes.as_ref().expect("mdoc MSO payload bytes are set"),
        ));
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let blinder_v = random_qm31();
        let blinder_m = random_qm31();
        let blinder_relation = self
            .blinder_relation
            .clone()
            .expect("mdoc MSO payload blinder relation drawn before interaction");
        let (trace, claimed_sum) = mso_payload_interaction_trace(
            self.bytes.as_ref().expect("mdoc MSO payload bytes are set"),
            &self.issuer_field_relation(),
            &self.mso_field_relation(),
            &blinder_relation,
            blinder_v,
            blinder_m,
        );
        tb.extend_evals(trace);
        let (blinder_trace, blinder_claimed_sum) =
            blinder_counter_interaction(self.log_size(), &blinder_relation, blinder_v, blinder_m);
        tb.extend_evals(blinder_trace);
        self.interaction_claim = Some(MdocMsoPayloadInteractionClaim {
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
                .expect("mdoc MSO payload component is built"),
            self.blinder_component
                .as_ref()
                .expect("mdoc MSO payload blinder component is built"),
        ]
    }
}

const MDOC_REVOCATION_RANGE_LOG_SIZE: u32 = LOG_N_LANES;
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
    epoch: Option<u32>,
    mso_digest_handle: SharedDigestRelation,
    message_field_handle: Option<SharedFieldRelation>,
    blinder_relation: Option<ClaimedSumBlinderRelation>,
    interaction_claim: Option<MdocRevocationRangeInteractionClaim>,
    component: Option<MdocRevocationRangeComponent>,
    blinder_component: Option<FrameworkComponent<ClaimedSumBlinderEval>>,
}

#[derive(Clone)]
struct MdocRevocationRangeEval {
    mso_digest_relation: DigestBytesRelation,
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
        mso_digest_handle: SharedDigestRelation,
        epoch: Option<u32>,
        message_field_handle: Option<SharedFieldRelation>,
    ) -> Self {
        Self {
            witness: Some(witness),
            mso_digest: Some(mso_digest),
            epoch,
            mso_digest_handle,
            message_field_handle,
            blinder_relation: None,
            interaction_claim: None,
            component: None,
            blinder_component: None,
        }
    }

    fn verifier(
        mso_digest_handle: SharedDigestRelation,
        epoch: Option<u32>,
        message_field_handle: Option<SharedFieldRelation>,
        interaction_claim: MdocRevocationRangeInteractionClaim,
    ) -> Self {
        Self {
            witness: None,
            mso_digest: None,
            epoch,
            mso_digest_handle,
            message_field_handle,
            blinder_relation: None,
            interaction_claim: Some(interaction_claim),
            component: None,
            blinder_component: None,
        }
    }

    fn relation(&self) -> DigestBytesRelation {
        self.mso_digest_handle.get()
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

    first_row
        .into_iter()
        .map(|value| {
            let mut column = vec![M31::from_u32_unchecked(0); 1 << MDOC_REVOCATION_RANGE_LOG_SIZE];
            column[0] = M31::from_u32_unchecked(value);
            mdoc_column_eval(MDOC_REVOCATION_RANGE_LOG_SIZE, column)
        })
        .collect()
}

fn revocation_range_interaction_trace(
    witness: &MdocRevocationRangeWitness,
    mso_digest: &[u8; 32],
    relation: &DigestBytesRelation,
    epoch: Option<u32>,
    message_relation: Option<&FieldBytesRelation>,
    blinder_relation: &ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
) -> (Vec<MdocRevocationRangeColumnEval>, QM31) {
    let base = revocation_range_base_trace(witness, mso_digest);
    let active = revocation_range_active_column();
    let n_vec_rows = 1usize << (MDOC_REVOCATION_RANGE_LOG_SIZE - LOG_N_LANES);
    let digest_tail_offset =
        REVOCATION_RANGE_BYTE_COLS + REVOCATION_RANGE_BIT_COLS + REVOCATION_RANGE_CARRY_COLS;
    // Q-015 blinder `+m/(z−combine(v))`, emitted LAST (paired with the lone
    // message site in the TS13 branch, its own column otherwise).
    let blinder_num = PackedQM31::broadcast(blinder_m);
    let blinder_den = crate::claimed_sum_blinder::blinder_denominator(blinder_relation, blinder_v);
    let mut logup = LogupTraceGenerator::new(MDOC_REVOCATION_RANGE_LOG_SIZE);
    if let (Some(epoch), Some(message_relation)) = (epoch, message_relation) {
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
    } else {
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

        let values: Vec<E::F> = (0..REVOCATION_RANGE_TRACE_COLS)
            .map(|_| eval.next_trace_mask())
            .collect();
        for value in &values {
            eval.add_constraint((one.clone() - active.clone()) * value.clone());
        }

        for byte_idx in 0..REVOCATION_RANGE_BYTE_COLS {
            let byte = values[byte_idx].clone();
            let bits = &values[REVOCATION_RANGE_BYTE_COLS + byte_idx * 8
                ..REVOCATION_RANGE_BYTE_COLS + (byte_idx + 1) * 8];
            for bit in bits {
                eval.add_constraint(bit.clone() * (bit.clone() - one.clone()));
            }
            eval.add_constraint(active.clone() * (byte - byte_from_bits::<E>(bits)));
        }

        let lower_carries_offset = REVOCATION_RANGE_BYTE_COLS + REVOCATION_RANGE_BIT_COLS;
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

        let digest_tail_offset = upper_carries_offset + REVOCATION_U64_BYTES;
        let mut digest_values = Vec::with_capacity(32);
        for byte_idx in 0..REVOCATION_U64_BYTES {
            digest_values.push(values[byte_idx].clone());
        }
        for byte_idx in 0..REVOCATION_RANGE_DIGEST_TAIL_COLS {
            digest_values.push(values[digest_tail_offset + byte_idx].clone());
        }
        eval.add_to_relation(RelationEntry::new(
            &self.mso_digest_relation,
            E::EF::from(active.clone()),
            &digest_values,
        ));
        if let Some(message_relation) = &self.message_field_relation {
            let field_id = m31_const::<E>(MDOC_REVOCATION_MESSAGE_FIELD_ID);
            for byte_idx in 0..TS13_REVOCATION_MESSAGE_LEN {
                let value = match byte_idx {
                    0..=7 => values[REVOCATION_U64_BYTES + byte_idx].clone(),
                    8..=15 => values[2 * REVOCATION_U64_BYTES + byte_idx - 8].clone(),
                    _ => m31_const::<E>(u32::from(self.epoch.to_le_bytes()[byte_idx - 16])),
                };
                eval.add_to_relation(RelationEntry::new(
                    message_relation,
                    E::EF::from(active.clone()),
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
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.blinder_relation = Some(ClaimedSumBlinderRelation::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![MDOC_REVOCATION_RANGE_LOG_SIZE],
            trace: vec![MDOC_REVOCATION_RANGE_LOG_SIZE; REVOCATION_RANGE_TRACE_COLS],
            // Main component columns (the Q-015 blinder site pairs with the
            // lone message site in the TS13 branch, or gets its own column in
            // the digest-only branch) plus the counterpart component column.
            interaction: vec![
                MDOC_REVOCATION_RANGE_LOG_SIZE;
                if self.message_field_handle.is_some() {
                    ((2 + TS13_REVOCATION_MESSAGE_LEN).div_ceil(2) + 1) * SECURE_EXTENSION_DEGREE
                } else {
                    3 * SECURE_EXTENSION_DEGREE
                }
            ],
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
                mso_digest_relation: self.relation(),
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
        tb.extend_evals(revocation_range_base_trace(
            self.witness
                .as_ref()
                .expect("mdoc revocation range witness is set"),
            self.mso_digest
                .as_ref()
                .expect("mdoc revocation range MSO digest is set"),
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
            &self.relation(),
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
        return Err(Error::P256InstanceMismatch);
    }
    ensure_statement_scheme_uniformity(statement)?;
    // D2: host-side canonical device-key ↔ MSO binding for the ML-DSA scheme,
    // before any STARK work (the verifier runs the identical check).
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
    check_mldsa_device_key_binding(statement)?;
    // ML-DSA issuers prove in the in-STARK composition only: the P4b
    // coprocessor bundle is a fixed two-ECDSA MAC format (device-only bundle
    // pending — see tasks/mldsa-todo.md M7).
    #[cfg(feature = "ec-coprocessor")]
    statement
        .issuer_input
        .expect_ecdsa("ec-coprocessor mdoc prove")?;
    #[cfg(feature = "ec-coprocessor")]
    statement
        .device_input
        .expect_ecdsa("ec-coprocessor mdoc prove")?;

    #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
    let issuer_draft = statement
        .issuer_input
        .as_ecdsa()
        .map(|input| single_p256_draft(input.clone()))
        .transpose()?;
    #[cfg(not(feature = "ec-coprocessor"))]
    let device_draft = statement
        .device_input
        .as_ecdsa()
        .map(|input| single_p256_draft(input.clone()))
        .transpose()?;
    let revocation_p256_input = ts13_revocation_p256_input(statement)?;
    let revocation_draft = revocation_p256_input
        .clone()
        .map(single_p256_draft)
        .transpose()?;
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
    let mso_sha_params = statement
        .ts13_revocation_range
        .as_ref()
        .map(|_| sha_params(&extracted.mso));
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
    let revocation_sha_params = revocation_message
        .as_ref()
        .map(|message| sha_params(message.as_slice()));
    let attribute_items: Vec<_> = extracted
        .extracted_attributes
        .iter()
        .map(|attribute| attribute.item.as_slice())
        .collect();
    let attribute_sha_params: Vec<_> = attribute_items
        .iter()
        .map(|item| sha_params(item))
        .collect();
    let shared_sha_log = std::iter::once(issuer_sha_log)
        .chain(std::iter::once(device_sha_log))
        .chain(mso_sha_params.iter().map(|(_, log)| *log))
        .chain(revocation_sha_params.iter().map(|(_, log)| *log))
        .chain(attribute_sha_params.iter().map(|(_, log)| *log))
        .max()
        .expect("sha log list is non-empty");
    let issuer_digest = SharedDigestRelation::new();
    // The device digest/z relations only exist for a P-256 device (their sole
    // consumer is the device bridge); an ML-DSA device gets a field relation
    // for the hosted module's µ-absorb bridge instead.
    #[cfg(not(feature = "ec-coprocessor"))]
    let device_digest = statement
        .device_input
        .as_ecdsa()
        .map(|_| SharedDigestRelation::new());
    #[cfg(feature = "ec-coprocessor")]
    let device_digest = SharedDigestRelation::new();
    let mso_digest = statement
        .ts13_revocation_range
        .as_ref()
        .map(|_| SharedDigestRelation::new());
    // Same split per revocation scheme: digest/z only for the P-256 arm.
    let revocation_digest = statement
        .ts13_revocation_signature
        .as_ref()
        .and_then(|signature| signature.as_ecdsa())
        .map(|_| SharedDigestRelation::new());
    let attribute_digests: Vec<_> = (0..attribute_sha_params.len())
        .map(|_| SharedDigestRelation::new())
        .collect();
    let issuer_field = SharedFieldRelation::new();
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
    let device_field = statement
        .device_input
        .as_mldsa()
        .map(|_| SharedFieldRelation::new());
    let mso_field = statement
        .ts13_revocation_range
        .as_ref()
        .map(|_| SharedFieldRelation::new());
    let revocation_message_field = statement
        .ts13_revocation_signature
        .as_ref()
        .map(|_| SharedFieldRelation::new());
    let attribute_fields: Vec<_> = (0..attribute_sha_params.len())
        .map(|_| SharedFieldRelation::new())
        .collect();
    let sha_table_relations = SharedShaTableRelations::new();
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
    let issuer_scalar_z = SharedScalarZRelation::new();
    #[cfg(not(feature = "ec-coprocessor"))]
    let device_scalar_z = statement
        .device_input
        .as_ecdsa()
        .map(|_| SharedScalarZRelation::new());
    let revocation_scalar_z = statement
        .ts13_revocation_signature
        .as_ref()
        .and_then(|signature| signature.as_ecdsa())
        .map(|_| SharedScalarZRelation::new());

    let issuer_exposure = issuer_mso_exposure(statement);
    let device_exposure = device_sig_structure_exposure(statement);
    let mso_exposure = mso_payload_exposure(statement);
    let revocation_exposure = ts13_revocation_message_exposure(statement);
    let attribute_exposures: Vec<_> = (0..statement.attributes.len())
        .map(|index| attribute_exposure(statement, index))
        .collect();

    #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
    let mut issuer_p256 = issuer_draft
        .as_ref()
        .map(P256Prover::new)
        .transpose()
        .map_err(Error::P256Prepare)?
        .map(|prover| prover.with_z_binding(issuer_scalar_z.clone()));
    // The `mdoc/device` namespace is REQUIRED, not waste: the hinted-mul schedule
    // preprocessed columns are witness-dependent (measured: 18 of 215 columns —
    // the log-13 schedule set — differ between the issuer and device signatures).
    // Without the namespace the device module would alias onto the issuer's
    // schedule under air-core first-writer-wins tree-0 dedup, binding the wrong
    // constraints. Two genuinely distinct signatures cannot share the schedule.
    #[cfg(not(feature = "ec-coprocessor"))]
    let mut device_p256 = device_draft
        .as_ref()
        .map(|draft| {
            Ok::<_, Error>(
                P256Prover::new(draft)
                    .map_err(Error::P256Prepare)?
                    .with_preprocessed_namespace("mdoc/device")
                    .with_z_binding(
                        device_scalar_z
                            .clone()
                            .expect("device z relation exists for a P-256 device"),
                    ),
            )
        })
        .transpose()?;
    let mut sha_consumers = vec![
        (&issuer_sha_witness, issuer_exposure.clone()),
        (&device_sha_witness, device_exposure.clone()),
    ];
    if let Some((mso_sha_witness, _)) = &mso_sha_params {
        sha_consumers.push((mso_sha_witness, mso_exposure.clone()));
    }
    if let Some((revocation_sha_witness, _)) = &revocation_sha_params {
        sha_consumers.push((revocation_sha_witness, revocation_exposure.clone()));
    }
    for ((witness, _), exposure) in attribute_sha_params.iter().zip(attribute_exposures.iter()) {
        sha_consumers.push((witness, exposure.clone()));
    }
    let sha_table_multiplicities = ShaTableMultiplicities::from_consumers(&sha_consumers);
    let mut sha_tables =
        ShaTablesProver::new(sha_table_multiplicities, sha_table_relations.clone());
    // ML-DSA issuer: no digest consumer exists (no issuer P-256 bridge), so the
    // digest handle is omitted to keep the global LogUp balance; the issuer
    // binding is the in-circuit ML-DSA verification over the exposed preimage.
    let issuer_sha_base = Sha256Prover::new(&issuer_sha_witness, shared_sha_log, SHA_GROUP_WIDTH)
        .with_shared_tables(sha_table_relations.clone());
    let issuer_sha_base = if statement.issuer_input.is_mldsa() {
        issuer_sha_base
    } else {
        issuer_sha_base.with_digest_handle(issuer_digest.clone())
    };
    let mut issuer_sha =
        issuer_sha_base.with_field_handle(issuer_exposure.clone(), issuer_field.clone());
    // Hosted in-circuit ML-DSA statement (M7): composed AFTER `issuer_sha` in
    // the module order so its `draw_relations` can read the shared field
    // relation `issuer_sha` draws + sets.
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
    let mut issuer_mldsa = statement
        .issuer_input
        .as_mldsa()
        .map(|input| -> Result<MlDsaStatementProver, Error> {
            let witness = stwo_mldsa::witness::generate_witness(input)
                .map_err(|error| Error::Prove(format!("mldsa witness: {error:?}")))?;
            Ok(
                MlDsaStatementProver::hosted(witness, input.clone(), issuer_field.clone())
                    .with_instance_namespace(MDOC_ISSUER_MLDSA_NAMESPACE),
            )
        })
        .transpose()?;
    // ML-DSA device: no digest consumer exists (no device bridge), mirror the
    // issuer treatment — byte provider only, on the device field relation.
    let device_sha_base = Sha256Prover::new(&device_sha_witness, shared_sha_log, SHA_GROUP_WIDTH)
        .with_shared_tables(sha_table_relations.clone());
    #[cfg(not(feature = "ec-coprocessor"))]
    let device_sha_base = if let Some(device_digest) = &device_digest {
        device_sha_base.with_digest_handle(device_digest.clone())
    } else {
        device_sha_base
    };
    #[cfg(feature = "ec-coprocessor")]
    let device_sha_base = device_sha_base.with_digest_handle(device_digest.clone());
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
    let mut device_sha = if let Some(device_field) = &device_field {
        device_sha_base.with_field_handle(device_exposure.clone(), device_field.clone())
    } else {
        device_sha_base
    };
    #[cfg(not(all(not(feature = "ec-coprocessor"), feature = "ml-dsa")))]
    let mut device_sha = device_sha_base;
    // Hosted in-circuit ML-DSA device statement: composed AFTER `device_sha`
    // (which draws + sets the shared field relation), namespaced per role.
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
    let mut device_mldsa = statement
        .device_input
        .as_mldsa()
        .map(|input| -> Result<MlDsaStatementProver, Error> {
            let witness = stwo_mldsa::witness::generate_witness(input)
                .map_err(|error| Error::Prove(format!("mldsa device witness: {error:?}")))?;
            Ok(MlDsaStatementProver::hosted(
                witness,
                input.clone(),
                device_field
                    .clone()
                    .expect("device field relation exists for an ML-DSA device"),
            )
            .with_instance_namespace(MDOC_DEVICE_MLDSA_NAMESPACE))
        })
        .transpose()?;
    let mut mso_sha = match (&mso_sha_params, &mso_digest) {
        (Some((mso_sha_witness, _)), Some(mso_digest)) => Some({
            let sha = Sha256Prover::new(mso_sha_witness, shared_sha_log, SHA_GROUP_WIDTH)
                .with_shared_tables(sha_table_relations.clone())
                .with_digest_handle(mso_digest.clone());
            if let Some(mso_field) = &mso_field {
                sha.with_field_handle(mso_exposure.clone(), mso_field.clone())
            } else {
                sha
            }
        }),
        _ => None,
    };
    // The revocation SHA module exists whenever a revocation signature does.
    // Its digest handle only exists for the P-256 arm (consumer: revocation
    // bridge); the ML-DSA arm keeps it as a pure byte provider (mirror of the
    // issuer/device treatment) feeding both `MdocRevocationRangeBind` and the
    // hosted module's µ-absorb bridge on the same field relation.
    let mut revocation_sha = revocation_sha_params
        .as_ref()
        .map(|(revocation_sha_witness, _)| {
            let sha = Sha256Prover::new(revocation_sha_witness, shared_sha_log, SHA_GROUP_WIDTH)
                .with_shared_tables(sha_table_relations.clone());
            let sha = if let Some(revocation_digest) = &revocation_digest {
                sha.with_digest_handle(revocation_digest.clone())
            } else {
                sha
            };
            if let Some(revocation_message_field) = &revocation_message_field {
                sha.with_field_handle(
                    revocation_exposure.clone(),
                    revocation_message_field.clone(),
                )
            } else {
                sha
            }
        });
    // Hosted in-circuit ML-DSA revocation statement, private-message mode: the
    // prover's input carries the REAL 20-byte message (from the private range
    // witness); only its LENGTH is mixed into the transcript.
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
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
            )
            .with_instance_namespace(MDOC_REVOCATION_MLDSA_NAMESPACE)
            .with_private_message())
        })
        .transpose()?;
    let mut revocation_p256 = revocation_draft
        .as_ref()
        .map(|draft| {
            let prover = P256Prover::new(draft).map_err(Error::P256Prepare)?;
            Ok::<_, Error>(if let Some(revocation_scalar_z) = &revocation_scalar_z {
                prover
                    .with_preprocessed_namespace("mdoc/ts13/revocation")
                    .with_z_binding(revocation_scalar_z.clone())
            } else {
                prover.with_preprocessed_namespace("mdoc/ts13/revocation")
            })
        })
        .transpose()?;
    let mut attribute_sha = Vec::with_capacity(attribute_sha_params.len());
    for index in 0..attribute_sha_params.len() {
        attribute_sha.push(
            Sha256Prover::new(
                &attribute_sha_params[index].0,
                shared_sha_log,
                SHA_GROUP_WIDTH,
            )
            .with_shared_tables(sha_table_relations.clone())
            .with_digest_handle(attribute_digests[index].clone())
            .with_field_handle(
                attribute_exposures[index].clone(),
                attribute_fields[index].clone(),
            ),
        );
    }

    #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
    let issuer_bridge_log = issuer_p256.as_ref().map(|issuer_p256| {
        crate::bridge_log_size(
            crate::bridge_rows(&issuer_p256.proof_claim().public_inputs.instances).len(),
        )
    });
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
    let mut issuer_bridge = issuer_p256.as_ref().map(|issuer_p256| {
        let issuer_bridge_rows =
            crate::bridge_rows(&issuer_p256.proof_claim().public_inputs.instances);
        DigestBindProver::new(
            issuer_bridge_rows,
            issuer_bridge_log.expect("issuer bridge log derived above"),
            issuer_scalar_z,
            issuer_digest.clone(),
        )
    });
    #[cfg(not(feature = "ec-coprocessor"))]
    let device_bridge_log = device_p256.as_ref().map(|device_p256| {
        crate::bridge_log_size(
            crate::bridge_rows(&device_p256.proof_claim().public_inputs.instances).len(),
        )
    });
    #[cfg(not(feature = "ec-coprocessor"))]
    let mut device_bridge = device_p256.as_ref().map(|device_p256| {
        let device_bridge_rows =
            crate::bridge_rows(&device_p256.proof_claim().public_inputs.instances);
        DigestBindProver::new(
            device_bridge_rows,
            device_bridge_log.expect("device bridge log derived above"),
            device_scalar_z
                .clone()
                .expect("device z relation exists for a P-256 device"),
            device_digest
                .clone()
                .expect("device digest relation exists for a P-256 device"),
        )
    });
    let mut revocation_bridge_log_size = None;
    let mut revocation_bridge = match (
        revocation_p256.as_ref(),
        revocation_scalar_z.clone(),
        revocation_digest.clone(),
    ) {
        (Some(revocation_p256), Some(revocation_scalar_z), Some(revocation_digest)) => {
            let rows = crate::bridge_rows(&revocation_p256.proof_claim().public_inputs.instances);
            let log = crate::bridge_log_size(rows.len());
            revocation_bridge_log_size = Some(log);
            Some(DigestBindProver::new(
                rows,
                log,
                revocation_scalar_z,
                revocation_digest,
            ))
        }
        _ => None,
    };
    #[cfg(feature = "ec-coprocessor")]
    let mut device_public_digest_bind = PublicDigestBind::new(
        statement
            .device_input
            .expect_ecdsa("ec-coprocessor mdoc prove")?
            .message_hash
            .0,
        device_digest.clone(),
    );
    let mut mdoc_window_bind = MdocWindowBind::new_for_attributes(
        mdoc_window_bind_rows_from(statement, Some(&extracted.issuer_sig_structure)),
        issuer_field.clone(),
        attribute_fields.clone(),
        attribute_digests.clone(),
    );
    let mut mdoc_validity = MdocValidityBind::new(
        statement.policy.current_date,
        mdoc_validity_rows_from(statement, Some(&extracted.issuer_sig_structure)),
        issuer_field.clone(),
    );
    let mut mso_payload_bind = statement.ts13_revocation_range.as_ref().map(|_| {
        MdocMsoPayloadBind::prover(
            extracted.mso.clone(),
            issuer_field.clone(),
            mso_field
                .clone()
                .expect("MSO field handle exists when revocation range is set"),
        )
    });
    #[cfg(feature = "ec-coprocessor")]
    let mac_key_shares = random_mdoc_p4b_mac_key_shares();
    #[cfg(feature = "ec-coprocessor")]
    let mac_state = MdocP4bMacSharedState::default();
    #[cfg(feature = "ec-coprocessor")]
    let mut mdoc_mac = MdocMacBind::prover(
        &mac_key_shares,
        mdoc_p4b_mac_values(statement),
        mac_state.clone(),
        issuer_digest.clone(),
        issuer_field.clone(),
    );
    #[cfg(feature = "ec-coprocessor")]
    let mut coprocessor = MdocCoprocessorBindingProver::new(
        statement
            .issuer_input
            .expect_ecdsa("ec-coprocessor mdoc prove")?
            .clone(),
        statement
            .device_input
            .expect_ecdsa("ec-coprocessor mdoc prove")?
            .clone(),
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
        MdocRevocationRangeBind::prover(
            range,
            mso_digest_bytes,
            mso_digest
                .clone()
                .expect("MSO digest handle exists when revocation range is set"),
            statement
                .ts13_revocation
                .as_ref()
                .map(|revocation| revocation.epoch)
                .filter(|_| statement.ts13_revocation_signature.is_some()),
            revocation_message_field.clone(),
        )
    });

    let stark_proof = {
        #[cfg(not(feature = "ec-coprocessor"))]
        let mut modules: Vec<&mut dyn AirProver> = {
            // P-256 issuer order is EXACTLY the historical one (shape gate);
            // an ML-DSA issuer swaps [issuer_p256, issuer_bridge] for the
            // hosted mldsa module placed right after issuer_sha (which draws
            // the shared field relation the mldsa msg bridge consumes).
            let mut modules: Vec<&mut dyn AirProver> = vec![&mut sha_tables];
            #[cfg(feature = "p256")]
            if let Some(issuer_p256) = issuer_p256.as_mut() {
                modules.push(issuer_p256);
            }
            modules.push(&mut issuer_sha);
            #[cfg(feature = "ml-dsa")]
            if let Some(issuer_mldsa) = issuer_mldsa.as_mut() {
                modules.push(issuer_mldsa);
            }
            #[cfg(feature = "p256")]
            if let Some(issuer_bridge) = issuer_bridge.as_mut() {
                modules.push(issuer_bridge);
            }
            // P-256 device order is EXACTLY the historical one; an ML-DSA
            // device swaps [device_p256, device_bridge] for the hosted mldsa
            // module placed right after device_sha (shared field draw).
            if let Some(device_p256) = device_p256.as_mut() {
                modules.push(device_p256);
            }
            modules.push(&mut device_sha);
            #[cfg(feature = "ml-dsa")]
            if let Some(device_mldsa) = device_mldsa.as_mut() {
                modules.push(device_mldsa);
            }
            if let Some(device_bridge) = device_bridge.as_mut() {
                modules.push(device_bridge);
            }
            modules
        };
        #[cfg(feature = "ec-coprocessor")]
        let mut modules: Vec<&mut dyn AirProver> = vec![
            &mut sha_tables,
            &mut issuer_sha,
            &mut device_sha,
            &mut device_public_digest_bind,
        ];
        if let Some(revocation_p256) = revocation_p256.as_mut() {
            modules.push(revocation_p256);
        }
        if let Some(mso_sha) = mso_sha.as_mut() {
            modules.push(mso_sha);
        }
        if let Some(revocation_sha) = revocation_sha.as_mut() {
            modules.push(revocation_sha);
        }
        // ML-DSA revocation: hosted module right after its byte provider.
        #[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
        if let Some(revocation_mldsa) = revocation_mldsa.as_mut() {
            modules.push(revocation_mldsa);
        }
        if let Some(revocation_bridge) = revocation_bridge.as_mut() {
            modules.push(revocation_bridge);
        }
        for sha in &mut attribute_sha {
            modules.push(sha);
        }
        modules.push(&mut mdoc_window_bind);
        modules.push(&mut mdoc_validity);
        if let Some(mso_payload_bind) = mso_payload_bind.as_mut() {
            modules.push(mso_payload_bind);
        }
        if let Some(age) = age.as_mut() {
            modules.push(age);
        }
        if let Some(nat) = nat.as_mut() {
            modules.push(nat);
        }
        if let Some(revocation_public) = ts13_revocation_public.as_mut() {
            modules.push(revocation_public);
        }
        if let Some(revocation_range) = ts13_revocation_range.as_mut() {
            modules.push(revocation_range);
        }
        #[cfg(feature = "ec-coprocessor")]
        modules.push(&mut coprocessor);
        #[cfg(feature = "ec-coprocessor")]
        modules.push(&mut mdoc_mac);
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
    #[cfg(feature = "ec-coprocessor")]
    let coprocessor_bundle = coprocessor.bundle.take().ok_or(Error::CoprocessorMissing)?;
    #[cfg(feature = "ec-coprocessor")]
    let p4b_prove_profile = coprocessor.profile.take();

    Ok(MdocProveOutcome::Proof(Box::new(MdocCircuitProof {
        stark_proof,
        sha_tables_interaction_claim: sha_tables.interaction_claim().clone(),
        #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
        issuer_p256_claim: issuer_p256
            .as_ref()
            .map(|issuer_p256| issuer_p256.proof_claim().clone()),
        #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
        issuer_p256_interaction_claim: issuer_p256
            .as_ref()
            .map(|issuer_p256| issuer_p256.interaction_claim().clone()),
        #[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
        mldsa: issuer_mldsa.as_ref().map(MdocMlDsaClaims::from_prover),
        #[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
        device_mldsa: device_mldsa.as_ref().map(MdocMlDsaClaims::from_prover),
        #[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
        revocation_mldsa: revocation_mldsa.as_ref().map(MdocMlDsaClaims::from_prover),
        #[cfg(not(feature = "ec-coprocessor"))]
        device_p256_claim: device_p256
            .as_ref()
            .map(|device_p256| device_p256.proof_claim().clone()),
        #[cfg(not(feature = "ec-coprocessor"))]
        device_p256_interaction_claim: device_p256
            .as_ref()
            .map(|device_p256| device_p256.interaction_claim().clone()),
        #[cfg(feature = "ec-coprocessor")]
        device_public_digest_bind_interaction_claim: device_public_digest_bind
            .interaction_claim()
            .clone(),
        #[cfg(feature = "ec-coprocessor")]
        coprocessor_bundle: Some(coprocessor_bundle),
        #[cfg(feature = "ec-coprocessor")]
        mdoc_mac_interaction_claim: mdoc_mac.interaction_claim().clone(),
        issuer_sha_log_n_rows: shared_sha_log,
        issuer_sha_interaction_claim: issuer_sha.interaction_claim().clone(),
        device_sha_log_n_rows: shared_sha_log,
        device_sha_interaction_claim: device_sha.interaction_claim().clone(),
        mso_sha_log_n_rows: mso_sha.as_ref().map(|_| shared_sha_log),
        mso_sha_interaction_claim: mso_sha.as_ref().map(|sha| sha.interaction_claim().clone()),
        revocation_sha_log_n_rows: revocation_sha.as_ref().map(|_| shared_sha_log),
        revocation_sha_interaction_claim: revocation_sha
            .as_ref()
            .map(|sha| sha.interaction_claim().clone()),
        attribute_sha_log_n_rows: vec![shared_sha_log; attribute_sha.len()],
        attribute_sha_interaction_claims: attribute_sha
            .iter()
            .map(|sha| sha.interaction_claim().clone())
            .collect(),
        revocation_p256_claim: revocation_p256
            .as_ref()
            .map(|p256| p256.proof_claim().clone()),
        revocation_p256_interaction_claim: revocation_p256
            .as_ref()
            .map(|p256| p256.interaction_claim().clone()),
        revocation_bridge_log_size,
        revocation_bridge_interaction_claim: revocation_bridge
            .as_ref()
            .map(|bridge| bridge.interaction_claim().clone()),
        #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
        issuer_bridge_log_size: issuer_bridge_log,
        #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
        issuer_bridge_interaction_claim: issuer_bridge
            .as_ref()
            .map(|issuer_bridge| issuer_bridge.interaction_claim().clone()),
        #[cfg(not(feature = "ec-coprocessor"))]
        device_bridge_log_size: device_bridge_log,
        #[cfg(not(feature = "ec-coprocessor"))]
        device_bridge_interaction_claim: device_bridge
            .as_ref()
            .map(|device_bridge| device_bridge.interaction_claim().clone()),
        mdoc_window_bind_interaction_claim: mdoc_window_bind.interaction_claim().clone(),
        mdoc_validity_interaction_claim: mdoc_validity.interaction_claim().clone(),
        mso_payload_bind_interaction_claim: mso_payload_bind
            .as_ref()
            .map(|bind| bind.interaction_claim().clone()),
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
        #[cfg(feature = "ec-coprocessor")]
        p4b_prove_profile,
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
    ensure_statement_scheme_uniformity(statement)?;
    // D2: host-side canonical device-key ↔ MSO binding for the ML-DSA scheme,
    // before any STARK work (the prover runs the identical check).
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
    check_mldsa_device_key_binding(statement)?;
    // Per-role statement arm and proof shape must agree BICONDITIONALLY
    // (rejects ECDSA-statement + ML-DSA-proof cross-mode confusion and vice
    // versa, per role), and a P-256 claim must carry exactly the statement's
    // instance. The checks are split per compiled-in scheme;
    // `issuer_p256_claim`/`mldsa` only exist under `p256`/`ml-dsa`, so an
    // issuer of an uncompiled scheme falls through and is rejected.
    #[cfg(not(feature = "ec-coprocessor"))]
    match &statement.issuer_input {
        MdocAuthInput::Ecdsa(issuer_input) => {
            #[cfg(feature = "ml-dsa")]
            if proof.mldsa.is_some() {
                return Err(Error::Verify(
                    "mdoc proof carries ML-DSA issuer claims for a P-256 issuer".to_string(),
                ));
            }
            #[cfg(feature = "p256")]
            match &proof.issuer_p256_claim {
                Some(issuer_claim)
                    if issuer_claim.public_inputs.instances.as_slice()
                        == [expected_instance(issuer_input)] => {}
                _ => return Err(Error::P256InstanceMismatch),
            }
            #[cfg(not(feature = "p256"))]
            {
                let _ = issuer_input;
                return Err(Error::P256InstanceMismatch);
            }
        }
        #[cfg(feature = "ml-dsa")]
        MdocAuthInput::MlDsa(_) => match &proof.mldsa {
            Some(claims) if claims.has_expected_shape() => {}
            _ => {
                return Err(Error::Verify(
                    "mdoc proof ML-DSA claim tree has the wrong shape".to_string(),
                ))
            }
        },
    }
    #[cfg(feature = "ec-coprocessor")]
    statement
        .issuer_input
        .expect_ecdsa("ec-coprocessor mdoc verify")?;
    #[cfg(feature = "ec-coprocessor")]
    statement
        .device_input
        .expect_ecdsa("ec-coprocessor mdoc verify")?;
    // Device arm ↔ proof shape (same biconditional gate as the issuer).
    #[cfg(not(feature = "ec-coprocessor"))]
    match &statement.device_input {
        MdocAuthInput::Ecdsa(device_input) => {
            #[cfg(feature = "ml-dsa")]
            if proof.device_mldsa.is_some() {
                return Err(Error::Verify(
                    "mdoc proof carries ML-DSA device claims for a P-256 device".to_string(),
                ));
            }
            match &proof.device_p256_claim {
                Some(device_claim)
                    if device_claim.public_inputs.instances.as_slice()
                        == [expected_instance(device_input)] => {}
                _ => return Err(Error::P256InstanceMismatch),
            }
        }
        #[cfg(feature = "ml-dsa")]
        MdocAuthInput::MlDsa(_) => {
            if proof.device_p256_claim.is_some()
                || proof.device_p256_interaction_claim.is_some()
                || proof.device_bridge_log_size.is_some()
                || proof.device_bridge_interaction_claim.is_some()
            {
                return Err(Error::Verify(
                    "mdoc proof carries P-256 device claims for an ML-DSA device".to_string(),
                ));
            }
            match &proof.device_mldsa {
                Some(claims) if claims.has_expected_shape() => {}
                _ => {
                    return Err(Error::Verify(
                        "mdoc proof ML-DSA device claim tree has the wrong shape".to_string(),
                    ))
                }
            }
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

    let issuer_digest = SharedDigestRelation::new();
    let device_digest = statement
        .device_input
        .as_ecdsa()
        .map(|_| SharedDigestRelation::new());
    #[cfg(feature = "ml-dsa")]
    let device_field = statement
        .device_input
        .as_mldsa()
        .map(|_| SharedFieldRelation::new());
    let has_revocation_range = statement.ts13_revocation_range.is_some();
    let has_revocation_signature = statement.ts13_revocation_signature.is_some();
    // The P-256 revocation module set exists iff the statement carries a P-256
    // revocation signature; the ML-DSA claim tree iff an ML-DSA one.
    let has_p256_revocation_signature = statement
        .ts13_revocation_signature
        .as_ref()
        .is_some_and(|signature| signature.as_ecdsa().is_some());
    if proof.mso_sha_log_n_rows.is_some() != has_revocation_range
        || proof.mso_sha_interaction_claim.is_some() != has_revocation_range
        || proof.mso_payload_bind_interaction_claim.is_some() != has_revocation_range
        || proof.ts13_revocation_range_interaction_claim.is_some() != has_revocation_range
        || proof.revocation_sha_log_n_rows.is_some() != has_revocation_signature
        || proof.revocation_sha_interaction_claim.is_some() != has_revocation_signature
        || proof.revocation_p256_claim.is_some() != has_p256_revocation_signature
        || proof.revocation_p256_interaction_claim.is_some() != has_p256_revocation_signature
        || proof.revocation_bridge_log_size.is_some() != has_p256_revocation_signature
        || proof.revocation_bridge_interaction_claim.is_some() != has_p256_revocation_signature
    {
        return Err(Error::Verify(
            "mdoc proof revocation layout mismatch".to_string(),
        ));
    }
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
    {
        let has_mldsa_revocation_signature = statement
            .ts13_revocation_signature
            .as_ref()
            .is_some_and(|signature| signature.is_mldsa());
        match (&proof.revocation_mldsa, has_mldsa_revocation_signature) {
            (Some(claims), true) if claims.has_expected_shape() => {}
            (None, false) => {}
            _ => {
                return Err(Error::Verify(
                    "mdoc proof ML-DSA revocation claim tree does not match the statement"
                        .to_string(),
                ))
            }
        }
    }
    let mso_digest = has_revocation_range.then(SharedDigestRelation::new);
    let mso_field = has_revocation_range.then(SharedFieldRelation::new);
    let revocation_digest = has_p256_revocation_signature.then(SharedDigestRelation::new);
    let revocation_message_field = has_revocation_signature.then(SharedFieldRelation::new);
    let attribute_count = proof.attribute_sha_interaction_claims.len();
    if attribute_count != proof.attribute_sha_log_n_rows.len()
        || attribute_count != statement.attributes.len()
    {
        return Err(Error::Verify(
            "mdoc proof carries an unsupported attribute count".to_string(),
        ));
    }
    let attribute_digests: Vec<_> = (0..attribute_count)
        .map(|_| SharedDigestRelation::new())
        .collect();
    let issuer_field = SharedFieldRelation::new();
    let attribute_fields: Vec<_> = (0..attribute_count)
        .map(|_| SharedFieldRelation::new())
        .collect();
    let sha_table_relations = SharedShaTableRelations::new();
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
    let issuer_scalar_z = SharedScalarZRelation::new();
    #[cfg(not(feature = "ec-coprocessor"))]
    let device_scalar_z = statement
        .device_input
        .as_ecdsa()
        .map(|_| SharedScalarZRelation::new());
    let revocation_scalar_z = has_p256_revocation_signature.then(SharedScalarZRelation::new);

    #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
    let mut issuer_p256 = match (
        &proof.issuer_p256_claim,
        &proof.issuer_p256_interaction_claim,
    ) {
        (Some(claim), Some(interaction_claim)) => Some(
            P256Verifier::new(claim.clone(), interaction_claim.clone())
                .with_z_binding(issuer_scalar_z.clone()),
        ),
        (None, None) => None,
        _ => {
            return Err(Error::Verify(
                "mdoc proof carries a partial issuer P-256 claim".to_string(),
            ))
        }
    };
    #[cfg(not(feature = "ec-coprocessor"))]
    let mut device_p256 = match (
        &proof.device_p256_claim,
        &proof.device_p256_interaction_claim,
    ) {
        (Some(claim), Some(interaction_claim)) => Some(
            P256Verifier::new(claim.clone(), interaction_claim.clone())
                .with_preprocessed_namespace("mdoc/device")
                .with_z_binding(
                    device_scalar_z
                        .clone()
                        .expect("device z relation exists for a P-256 device"),
                ),
        ),
        (None, None) => None,
        _ => {
            return Err(Error::Verify(
                "mdoc proof carries a partial device P-256 claim".to_string(),
            ))
        }
    };
    let mut revocation_p256 = match (
        proof.revocation_p256_claim.clone(),
        proof.revocation_p256_interaction_claim.clone(),
        revocation_scalar_z.clone(),
    ) {
        (Some(claim), Some(interaction_claim), Some(revocation_scalar_z)) => {
            let revocation_key = statement
                .ts13_revocation
                .as_ref()
                .and_then(|revocation| revocation.revocation_public_key.as_ecdsa())
                .ok_or_else(|| {
                    Error::Verify(
                        "revocation P-256 proof requires public P-256 revocation inputs"
                            .to_string(),
                    )
                })?;
            if claim.public_inputs.instances.len() != 1
                || !public_instance_key_matches(&claim.public_inputs.instances[0], revocation_key)
            {
                return Err(Error::P256InstanceMismatch);
            }
            Some(
                P256Verifier::new(claim, interaction_claim)
                    .with_preprocessed_namespace("mdoc/ts13/revocation")
                    .with_z_binding(revocation_scalar_z),
            )
        }
        _ => None,
    };
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
    let issuer_sha_base = Sha256Verifier::new(
        proof.issuer_sha_log_n_rows,
        SHA_GROUP_WIDTH,
        proof.issuer_sha_interaction_claim.clone(),
    )
    .with_shared_tables(sha_table_relations.clone());
    // Mirror the prover: no digest handle for ML-DSA issuers.
    let issuer_sha_base = if statement.issuer_input.is_mldsa() {
        issuer_sha_base
    } else {
        issuer_sha_base.with_digest_handle(issuer_digest.clone())
    };
    let mut issuer_sha =
        issuer_sha_base.with_field_handle(issuer_mso_exposure(statement), issuer_field.clone());
    // Hosted ML-DSA verifier (M7): rebuilt from the statement's public input +
    // the proof's claim tree; composed AFTER `issuer_sha` (shared field draw).
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
    let mut issuer_mldsa = match (statement.issuer_input.as_mldsa(), &proof.mldsa) {
        (Some(input), Some(claims)) => Some(
            MlDsaStatementVerifier::hosted(
                input.clone(),
                claims.group_evals.clone(),
                claims.claimed_sums.clone(),
                claims.sib_stream_len,
                claims.sib_squeezed_len,
                issuer_field.clone(),
            )
            .with_instance_namespace(MDOC_ISSUER_MLDSA_NAMESPACE),
        ),
        _ => None,
    };
    // Mirror the prover: no digest handle for ML-DSA devices, field handle on
    // the device relation instead.
    let device_sha_base = Sha256Verifier::new(
        proof.device_sha_log_n_rows,
        SHA_GROUP_WIDTH,
        proof.device_sha_interaction_claim.clone(),
    )
    .with_shared_tables(sha_table_relations.clone());
    let device_sha_base = if let Some(device_digest) = &device_digest {
        device_sha_base.with_digest_handle(device_digest.clone())
    } else {
        device_sha_base
    };
    #[cfg(feature = "ml-dsa")]
    let mut device_sha = if let Some(device_field) = &device_field {
        device_sha_base.with_field_handle(
            device_sig_structure_exposure(statement),
            device_field.clone(),
        )
    } else {
        device_sha_base
    };
    #[cfg(not(feature = "ml-dsa"))]
    let mut device_sha = device_sha_base;
    // Hosted ML-DSA device verifier: rebuilt from the statement's public input
    // + the proof's claim tree; composed AFTER `device_sha` (field draw).
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
    let mut device_mldsa = match (statement.device_input.as_mldsa(), &proof.device_mldsa) {
        (Some(input), Some(claims)) => Some(
            MlDsaStatementVerifier::hosted(
                input.clone(),
                claims.group_evals.clone(),
                claims.claimed_sums.clone(),
                claims.sib_stream_len,
                claims.sib_squeezed_len,
                device_field
                    .clone()
                    .expect("device field relation exists for an ML-DSA device"),
            )
            .with_instance_namespace(MDOC_DEVICE_MLDSA_NAMESPACE),
        ),
        _ => None,
    };
    let mut mso_sha = match (
        proof.mso_sha_log_n_rows,
        proof.mso_sha_interaction_claim.clone(),
        mso_digest.clone(),
    ) {
        (Some(log_n_rows), Some(interaction_claim), Some(mso_digest)) => Some({
            let sha = Sha256Verifier::new(log_n_rows, SHA_GROUP_WIDTH, interaction_claim)
                .with_shared_tables(sha_table_relations.clone())
                .with_digest_handle(mso_digest);
            if let Some(mso_field) = &mso_field {
                sha.with_field_handle(mso_payload_exposure(statement), mso_field.clone())
            } else {
                sha
            }
        }),
        _ => None,
    };
    let mut revocation_sha = match (
        proof.revocation_sha_log_n_rows,
        proof.revocation_sha_interaction_claim.clone(),
    ) {
        (Some(log_n_rows), Some(interaction_claim)) => {
            let sha = Sha256Verifier::new(log_n_rows, SHA_GROUP_WIDTH, interaction_claim)
                .with_shared_tables(sha_table_relations.clone());
            let sha = if let Some(revocation_digest) = &revocation_digest {
                sha.with_digest_handle(revocation_digest.clone())
            } else {
                sha
            };
            Some(
                if let Some(revocation_message_field) = &revocation_message_field {
                    sha.with_field_handle(
                        ts13_revocation_message_exposure(statement),
                        revocation_message_field.clone(),
                    )
                } else {
                    sha
                },
            )
        }
        _ => None,
    };
    // Hosted ML-DSA revocation verifier, private-message mode: the input is
    // rebuilt from the statement's PUBLIC key/signature bytes with 20 ZEROED
    // message bytes — the real id bounds never enter the verifier's inputs,
    // the transcript (only the length is mixed), or the serialized proof.
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
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
                    )
                    .with_instance_namespace(MDOC_REVOCATION_MLDSA_NAMESPACE)
                    .with_private_message()
                },
            )
        }
        None => None,
    };

    let attribute_exposures: Vec<_> = (0..statement.attributes.len())
        .map(|index| attribute_exposure(statement, index))
        .collect();
    let mut attribute_sha = Vec::with_capacity(attribute_count);
    for index in 0..attribute_count {
        attribute_sha.push(
            Sha256Verifier::new(
                proof.attribute_sha_log_n_rows[index],
                SHA_GROUP_WIDTH,
                proof.attribute_sha_interaction_claims[index].clone(),
            )
            .with_shared_tables(sha_table_relations.clone())
            .with_digest_handle(attribute_digests[index].clone())
            .with_field_handle(
                attribute_exposures[index].clone(),
                attribute_fields[index].clone(),
            ),
        );
    }

    #[cfg(all(not(feature = "ec-coprocessor"), feature = "p256"))]
    let mut issuer_bridge = match (
        proof.issuer_bridge_log_size,
        &proof.issuer_p256_claim,
        &proof.issuer_bridge_interaction_claim,
        statement.issuer_input.as_ecdsa(),
    ) {
        (Some(log_size), Some(p256_claim), Some(interaction_claim), Some(_)) => {
            Some(DigestBindVerifier::new(
                log_size,
                p256_claim.public_inputs.instances.len(),
                interaction_claim.clone(),
                issuer_scalar_z,
                issuer_digest,
            ))
        }
        (None, None, None, None) => None,
        _ => {
            return Err(Error::Verify(
                "mdoc proof issuer bridge does not match the statement's issuer arm".to_string(),
            ))
        }
    };
    #[cfg(not(feature = "ec-coprocessor"))]
    let mut device_bridge = match (
        proof.device_bridge_log_size,
        &proof.device_p256_claim,
        &proof.device_bridge_interaction_claim,
        statement.device_input.as_ecdsa(),
    ) {
        (Some(log_size), Some(p256_claim), Some(interaction_claim), Some(_)) => {
            Some(DigestBindVerifier::new(
                log_size,
                p256_claim.public_inputs.instances.len(),
                interaction_claim.clone(),
                device_scalar_z.expect("device z relation exists for a P-256 device"),
                device_digest
                    .clone()
                    .expect("device digest relation exists for a P-256 device"),
            ))
        }
        (None, None, None, None) => None,
        _ => {
            return Err(Error::Verify(
                "mdoc proof device bridge does not match the statement's device arm".to_string(),
            ))
        }
    };
    #[cfg(feature = "ec-coprocessor")]
    let mut device_public_digest_bind = PublicDigestBind::verifier(
        statement
            .device_input
            .expect_ecdsa("ec-coprocessor mdoc verify")?
            .message_hash
            .0,
        device_digest.expect("device digest relation exists on the ec-coprocessor path"),
        proof.device_public_digest_bind_interaction_claim.clone(),
    );
    let mut revocation_bridge = match (
        proof.revocation_bridge_log_size,
        proof.revocation_bridge_interaction_claim.clone(),
        revocation_scalar_z,
        revocation_digest,
    ) {
        (
            Some(log_size),
            Some(interaction_claim),
            Some(revocation_scalar_z),
            Some(revocation_digest),
        ) => Some(DigestBindVerifier::new(
            log_size,
            proof
                .revocation_p256_claim
                .as_ref()
                .map(|claim| claim.public_inputs.instances.len())
                .unwrap_or(0),
            interaction_claim,
            revocation_scalar_z,
            revocation_digest,
        )),
        _ => None,
    };
    let mut mdoc_window_bind = MdocWindowBind::verifier_for_attributes(
        mdoc_window_bind_rows_from(statement, None),
        issuer_field.clone(),
        attribute_fields.clone(),
        attribute_digests.clone(),
        proof.mdoc_window_bind_interaction_claim.clone(),
    );
    let mut mdoc_validity = MdocValidityBind::verifier(
        statement.policy.current_date,
        mdoc_validity_rows_from(statement, None),
        issuer_field.clone(),
        proof.mdoc_validity_interaction_claim.clone(),
    );
    let mut mso_payload_bind = has_revocation_range.then(|| {
        MdocMsoPayloadBind::verifier(
            statement.mso_payload_len,
            issuer_field.clone(),
            mso_field
                .clone()
                .expect("MSO field handle exists when revocation range is set"),
            proof
                .mso_payload_bind_interaction_claim
                .clone()
                .expect("MSO payload bind interaction claim exists when range is set"),
        )
    });
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
    #[cfg(feature = "ec-coprocessor")]
    let mac_state = MdocP4bMacSharedState::default();
    #[cfg(feature = "ec-coprocessor")]
    let mut mdoc_mac = MdocMacBind::verifier(
        mac_state.clone(),
        issuer_digest.clone(),
        issuer_field.clone(),
        proof.mdoc_mac_interaction_claim.clone(),
    );
    #[cfg(feature = "ec-coprocessor")]
    let mut coprocessor = MdocCoprocessorBindingVerifier {
        issuer_input: statement
            .issuer_input
            .expect_ecdsa("ec-coprocessor mdoc verify")?
            .clone(),
        device_input: statement
            .device_input
            .expect_ecdsa("ec-coprocessor mdoc verify")?
            .clone(),
        bundle: proof
            .coprocessor_bundle
            .clone()
            .ok_or(Error::CoprocessorMissing)?,
        mac_state,
        profile: None,
    };
    let mut ts13_revocation_public = statement
        .ts13_revocation
        .clone()
        .map(MdocRevocationPublicBind::new);
    let mut ts13_revocation_range = statement.ts13_revocation_range.as_ref().map(|_| {
        MdocRevocationRangeBind::verifier(
            mso_digest
                .clone()
                .expect("MSO digest handle exists when revocation range is set"),
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

    #[cfg(not(feature = "ec-coprocessor"))]
    let mut modules: Vec<&mut dyn Air> = {
        // Mirror the prover's module order exactly (transcript identity).
        let mut modules: Vec<&mut dyn Air> = vec![&mut sha_tables];
        #[cfg(feature = "p256")]
        if let Some(issuer_p256) = issuer_p256.as_mut() {
            modules.push(issuer_p256);
        }
        modules.push(&mut issuer_sha);
        #[cfg(feature = "ml-dsa")]
        if let Some(issuer_mldsa) = issuer_mldsa.as_mut() {
            modules.push(issuer_mldsa);
        }
        #[cfg(feature = "p256")]
        if let Some(issuer_bridge) = issuer_bridge.as_mut() {
            modules.push(issuer_bridge);
        }
        if let Some(device_p256) = device_p256.as_mut() {
            modules.push(device_p256);
        }
        modules.push(&mut device_sha);
        #[cfg(feature = "ml-dsa")]
        if let Some(device_mldsa) = device_mldsa.as_mut() {
            modules.push(device_mldsa);
        }
        if let Some(device_bridge) = device_bridge.as_mut() {
            modules.push(device_bridge);
        }
        modules
    };
    #[cfg(feature = "ec-coprocessor")]
    let mut modules: Vec<&mut dyn Air> = vec![
        &mut sha_tables,
        &mut issuer_sha,
        &mut device_sha,
        &mut device_public_digest_bind,
    ];
    if let Some(revocation_p256) = revocation_p256.as_mut() {
        modules.push(revocation_p256);
    }
    if let Some(mso_sha) = mso_sha.as_mut() {
        modules.push(mso_sha);
    }
    if let Some(revocation_sha) = revocation_sha.as_mut() {
        modules.push(revocation_sha);
    }
    #[cfg(all(not(feature = "ec-coprocessor"), feature = "ml-dsa"))]
    if let Some(revocation_mldsa) = revocation_mldsa.as_mut() {
        modules.push(revocation_mldsa);
    }
    if let Some(revocation_bridge) = revocation_bridge.as_mut() {
        modules.push(revocation_bridge);
    }
    for sha in &mut attribute_sha {
        modules.push(sha);
    }
    modules.push(&mut mdoc_window_bind);
    modules.push(&mut mdoc_validity);
    if let Some(mso_payload_bind) = mso_payload_bind.as_mut() {
        modules.push(mso_payload_bind);
    }
    if let Some(age) = age.as_mut() {
        modules.push(age);
    }
    if let Some(nat) = nat.as_mut() {
        modules.push(nat);
    }
    if let Some(revocation_public) = ts13_revocation_public.as_mut() {
        modules.push(revocation_public);
    }
    if let Some(revocation_range) = ts13_revocation_range.as_mut() {
        modules.push(revocation_range);
    }
    #[cfg(feature = "ec-coprocessor")]
    modules.push(&mut coprocessor);
    #[cfg(feature = "ec-coprocessor")]
    modules.push(&mut mdoc_mac);
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        air_core::verify_with_expected_preprocessed_root(
            modules.as_mut_slice(),
            &proof.stark_proof,
            expected_preprocessed_root,
        )
    })) {
        Ok(Ok(())) => Ok(MdocCircuitVerifyProfile {
            total: total_start.elapsed(),
            #[cfg(feature = "ec-coprocessor")]
            p4b: coprocessor.profile.take(),
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
    // WO-P3 pow/query rebalance: pow_bits 20 + n_queries 54 keeps 54·2 + 20 =
    // 128-bit security (log_blowup 2), trading ~5 FRI queries (≈135 KB of
    // queried_values) for cheap grinding. The verifier pins this exact config
    // (see verify_mdoc_circuit_with_pcs_config) so an old-config proof is
    // rejected.
    PcsConfig {
        pow_bits: 20,
        fri_config: FriConfig::new(1, 2, 54, 2),
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

#[cfg(test)]
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
