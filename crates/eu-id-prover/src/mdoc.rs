//! Product EUID PID mdoc proof path.
//!
//! This module parses the constrained ISO/IEC 18013-5 PID profile, prepares the
//! mdoc statement/witness, and proves issuer signature, ISO device
//! authentication, MSO digest membership, validity, device-key origin, and the
//! age/nationality predicates in one verifier-facing proof. The legacy nonce
//! module is not part of this path; the device-auth signature binds freshness.

use std::collections::HashMap;

use air_core::relations::{field_id, SharedDigestRelation, SharedFieldRelation};
use air_core::{Air, AirProver, TreeLayout};
use ciborium::value::Value;
use ecdsa::signature::{Signer, Verifier};
use p256::ecdsa::{Signature as P256Signature, SigningKey, VerifyingKey};
use p256::pkcs8::DecodePublicKey;
use p256::EncodedPoint;
use predicates::nat::NationalityPredicate;
use predicates::{AgeRangeCheck, DateOfBirth, PredicateProver, PredicateVerifier};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};
#[cfg(not(feature = "ec-coprocessor"))]
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;
#[cfg(feature = "ec-coprocessor")]
use stwo::core::{air::Component, channel::Blake2sChannel, verifier::VerificationError};
#[cfg(feature = "ec-coprocessor")]
use stwo::prover::backend::simd::SimdBackend;
#[cfg(feature = "ec-coprocessor")]
use stwo::prover::{ComponentProver, TreeBuilder};
#[cfg(feature = "ec-coprocessor")]
use stwo_constraint_framework::{
    preprocessed_columns::PreProcessedColumnId, TraceLocationAllocator,
};
#[cfg(not(feature = "ec-coprocessor"))]
use stwo_p256::components::digest_bind::module::{
    DigestBindInteractionClaim, DigestBindProver, DigestBindVerifier,
};
#[cfg(not(feature = "ec-coprocessor"))]
use stwo_p256::components::digest_bind::SharedScalarZRelation;
#[cfg(not(feature = "ec-coprocessor"))]
use stwo_p256::public_inputs::PublicEcdsaInstance;
use stwo_p256::types::{AffinePoint, EcdsaVerifyInput, Signature, U256};
use stwo_p256::{proof::air::P256Prover, proof::P256ProofDraft};
#[cfg(not(feature = "ec-coprocessor"))]
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

use crate::generator::{Policy, SHA_GROUP_WIDTH};
use crate::mdoc_validity::{
    mdoc_validity_rows, MdocValidityBind, MdocValidityInteractionClaim, MdocValidityRow,
};
use crate::mdoc_window_bind::{
    MdocFieldSource, MdocWindowBind, MdocWindowBindInteractionClaim, MdocWindowBindRow,
};
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
const CBOR_TAG_ENCODED_CBOR: u64 = 24;
const CBOR_TAG_FULL_DATE: u64 = 1004;
const MDOC_ATTRIBUTE_ELEMENT_ID_BASE: u32 = 16;
const MDOC_ATTRIBUTE_VALUE_BASE: u32 = 20;
const MDOC_ATTRIBUTE_DIGEST_BASE: u32 = 24;
const MDOC_ATTRIBUTE_DIGEST_ANCHOR_BASE: u32 = 28;
const MDOC_ATTRIBUTE_VALUE_HEAD_BASE: u32 = 32;
const MDOC_ATTRIBUTE_ELEMENT_ANCHOR_BASE: u32 = 36;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MdocPidRequest {
    pub doctype: String,
    pub namespace: String,
    pub attributes: Vec<MdocRequestedAttribute>,
    pub birth_date_element: String,
    pub nationality_element: String,
    pub session_transcript: Vec<u8>,
    pub trusted_issuer_certificates: Vec<Vec<u8>>,
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
        }
    }

    pub fn with_trusted_issuer_certificates(mut self, certificates: Vec<Vec<u8>>) -> Self {
        self.trusted_issuer_certificates = certificates;
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
    pub issuer_ecdsa_input: EcdsaVerifyInput,
    pub device_ecdsa_input: EcdsaVerifyInput,
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
    InvalidCertificate(&'static str),
    UntrustedIssuerCertificate,
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

    #[cfg(not(feature = "ec-coprocessor"))]
    let issuer_draft = single_p256_draft(statement.issuer_input.clone())?;
    #[cfg(not(feature = "ec-coprocessor"))]
    let device_draft = single_p256_draft(statement.device_input.clone())?;
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
    #[cfg(not(feature = "ec-coprocessor"))]
    let issuer_scalar_z = SharedScalarZRelation::new();
    #[cfg(not(feature = "ec-coprocessor"))]
    let device_scalar_z = SharedScalarZRelation::new();

    let issuer_exposure = issuer_mso_exposure(statement);
    let attribute_exposures: Vec<_> = (0..statement.attributes.len())
        .map(|index| attribute_exposure(statement, index))
        .collect();

    #[cfg(not(feature = "ec-coprocessor"))]
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

    #[cfg(not(feature = "ec-coprocessor"))]
    let issuer_bridge_rows = crate::bridge_rows(&issuer_p256.proof_claim().public_inputs.instances);
    #[cfg(not(feature = "ec-coprocessor"))]
    let issuer_bridge_log = crate::bridge_log_size(issuer_bridge_rows.len());
    #[cfg(not(feature = "ec-coprocessor"))]
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
    let issuer_public_digest_bind =
        PublicDigestBind::new(statement.issuer_input.message_hash.0, issuer_digest.clone());
    #[cfg(feature = "ec-coprocessor")]
    let device_public_digest_bind =
        PublicDigestBind::new(statement.device_input.message_hash.0, device_digest.clone());
    let mdoc_window_bind = MdocWindowBind::new_for_attributes(
        mdoc_window_bind_rows_from(statement, Some(&extracted.issuer_sig_structure)),
        issuer_field.clone(),
        attribute_fields.clone(),
        attribute_digests.clone(),
    );
    let mdoc_validity = MdocValidityBind::new(
        statement.policy.current_date,
        mdoc_validity_rows_from(statement, Some(&extracted.issuer_sig_structure)),
        issuer_field,
    );
    #[cfg(feature = "ec-coprocessor")]
    let coprocessor = MdocCoprocessorBindingProver::new(
        statement.issuer_input.clone(),
        statement.device_input.clone(),
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
        MdocModuleShape {
            name: "mdoc_sha_tables",
            layout: sha_tables.layout(),
        },
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
            layout: attribute_sha[0].layout(),
        },
        MdocModuleShape {
            name: "mdoc_nat_sha",
            layout: attribute_sha[1].layout(),
        },
        MdocModuleShape {
            name: "mdoc_window_bind",
            layout: mdoc_window_bind.layout(),
        },
        MdocModuleShape {
            name: "mdoc_validity",
            layout: mdoc_validity.layout(),
        },
        MdocModuleShape {
            name: "mdoc_age",
            layout: age.layout(),
        },
        MdocModuleShape {
            name: "mdoc_nat",
            layout: nat.layout(),
        },
    ];
    #[cfg(feature = "ec-coprocessor")]
    let shapes = vec![
        MdocModuleShape {
            name: "mdoc_sha_tables",
            layout: sha_tables.layout(),
        },
        MdocModuleShape {
            name: "mdoc_issuer_sha",
            layout: issuer_sha.layout(),
        },
        MdocModuleShape {
            name: "mdoc_issuer_public_digest_bind",
            layout: issuer_public_digest_bind.layout(),
        },
        MdocModuleShape {
            name: "mdoc_device_sha",
            layout: device_sha.layout(),
        },
        MdocModuleShape {
            name: "mdoc_device_public_digest_bind",
            layout: device_public_digest_bind.layout(),
        },
        MdocModuleShape {
            name: "mdoc_birth_sha",
            layout: attribute_sha[0].layout(),
        },
        MdocModuleShape {
            name: "mdoc_nat_sha",
            layout: attribute_sha[1].layout(),
        },
        MdocModuleShape {
            name: "mdoc_window_bind",
            layout: mdoc_window_bind.layout(),
        },
        MdocModuleShape {
            name: "mdoc_validity",
            layout: mdoc_validity.layout(),
        },
        MdocModuleShape {
            name: "mdoc_age",
            layout: age.layout(),
        },
        MdocModuleShape {
            name: "mdoc_nat",
            layout: nat.layout(),
        },
        MdocModuleShape {
            name: "mdoc_coprocessor",
            layout: coprocessor.layout(),
        },
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
    let doc_map = expect_map(&doc, "document")?;
    let doctype = text_field(doc_map, "docType")?.to_string();
    if doctype != request.doctype {
        return Err(MdocError::DoctypeMismatch);
    }

    let issuer_signed = map_field(doc_map, "issuerSigned")?;
    let issuer_auth = parse_cose_sign1(value_field(issuer_signed, "issuerAuth")?)?;
    let issuer_key = issuer_key_from_unprotected(
        expect_map(&issuer_auth.unprotected, "issuerAuth.unprotected")?,
        request,
    )?;
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
    let device_signature = parse_cose_sign1(value_field(device_auth, "deviceSignature")?)?;
    let expected_device_payload =
        device_authentication_bytes(&request.session_transcript, &request.doctype)?;
    if device_signature.payload != expected_device_payload {
        return Err(MdocError::DeviceAuthPayloadMismatch);
    }
    verify_signature(
        &device_key,
        &device_signature.sig_structure,
        &device_signature.signature_bytes,
        "deviceSignature",
    )?;

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
        issuer_ecdsa_input,
        device_ecdsa_input,
    })
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
    FieldExposure::from_preimage_windows_multi(&windows)
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
    rows.extend([
        MdocWindowBindRow::constant(
            field_id::MDOC_DEVICE_KEY_X,
            MdocFieldSource::IssuerMso,
            &statement.device_input.public_key.x.0,
        ),
        MdocWindowBindRow::constant(
            field_id::MDOC_DEVICE_KEY_Y,
            MdocFieldSource::IssuerMso,
            &statement.device_input.public_key.y.0,
        ),
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

fn issuer_key_from_unprotected(
    unprotected: &[(Value, Value)],
    request: &MdocPidRequest,
) -> Result<AffinePoint, MdocError> {
    if let Some(x5chain) = value_int_key(unprotected, 33) {
        return issuer_key_from_x5chain(x5chain, &request.trusted_issuer_certificates);
    }
    parse_cose_key(value_field(unprotected, "issuerKey")?)
}

fn issuer_key_from_x5chain(
    value: &Value,
    trusted_roots: &[Vec<u8>],
) -> Result<AffinePoint, MdocError> {
    let chain = x5chain_certificates(value)?;
    let parsed_chain = chain
        .iter()
        .map(|certificate| parse_x509_certificate(certificate))
        .collect::<Result<Vec<_>, _>>()?;
    for pair in parsed_chain.windows(2) {
        verify_certificate_signature(&pair[0], &pair[1])?;
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
    affine_point_from_spki(parsed_chain[0].spki_der)
}

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
    tbs_der: &'a [u8],
    spki_der: &'a [u8],
    signature_der: &'a [u8],
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
    let signature_der = der_bit_string_bytes(signature, "certificate.signatureValue")?;

    let spki_der = certificate_spki_der(tbs.value)?;
    Ok(ParsedCertificate {
        tbs_der: tbs.full,
        spki_der,
        signature_der,
    })
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
    pub issuer_input: EcdsaVerifyInput,
    pub device_input: EcdsaVerifyInput,
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
    pub policy: Policy,
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
        let mso_device_key_x_anchor = vec![0x21, 0x58, 0x20];
        let mso_device_key_x_anchor_offset = anchor_before_offset(
            &extracted.issuer_sig_structure,
            mso_device_key_x_offset,
            &mso_device_key_x_anchor,
            "device key x anchor offset",
        )?;
        let mso_device_key_y_anchor = vec![0x22, 0x58, 0x20];
        let mso_device_key_y_anchor_offset = anchor_before_offset(
            &extracted.issuer_sig_structure,
            mso_device_key_y_offset,
            &mso_device_key_y_anchor,
            "device key y anchor offset",
        )?;
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
            &full_date_text_bytes(extracted.valid_from),
            "validFrom date offset",
        )?;
        ensure_value_window_with_message(
            &extracted.issuer_sig_structure,
            mso_valid_until_date_offset,
            &full_date_text_bytes(extracted.valid_until),
            "validUntil date offset",
        )?;

        Ok(Self {
            issuer_input: extracted.issuer_ecdsa_input.clone(),
            device_input: extracted.device_ecdsa_input.clone(),
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

#[derive(Clone, Serialize, Deserialize)]
pub struct MdocCircuitProof {
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
    sha_tables_interaction_claim: ShaTablesInteractionClaim,
    #[cfg(not(feature = "ec-coprocessor"))]
    issuer_p256_claim: P256CurrentAirProofClaim,
    #[cfg(not(feature = "ec-coprocessor"))]
    issuer_p256_interaction_claim: P256CurrentAirInteractionClaim,
    #[cfg(not(feature = "ec-coprocessor"))]
    device_p256_claim: P256CurrentAirProofClaim,
    #[cfg(not(feature = "ec-coprocessor"))]
    device_p256_interaction_claim: P256CurrentAirInteractionClaim,
    #[cfg(feature = "ec-coprocessor")]
    issuer_public_digest_bind_interaction_claim: PublicDigestBindInteractionClaim,
    #[cfg(feature = "ec-coprocessor")]
    device_public_digest_bind_interaction_claim: PublicDigestBindInteractionClaim,
    #[cfg(feature = "ec-coprocessor")]
    coprocessor_bundle: Option<eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle>,
    issuer_sha_log_n_rows: u32,
    issuer_sha_interaction_claim: Sha256InteractionClaim,
    device_sha_log_n_rows: u32,
    device_sha_interaction_claim: Sha256InteractionClaim,
    attribute_sha_log_n_rows: Vec<u32>,
    attribute_sha_interaction_claims: Vec<Sha256InteractionClaim>,
    #[cfg(not(feature = "ec-coprocessor"))]
    issuer_bridge_log_size: u32,
    #[cfg(not(feature = "ec-coprocessor"))]
    issuer_bridge_interaction_claim: DigestBindInteractionClaim,
    #[cfg(not(feature = "ec-coprocessor"))]
    device_bridge_log_size: u32,
    #[cfg(not(feature = "ec-coprocessor"))]
    device_bridge_interaction_claim: DigestBindInteractionClaim,
    mdoc_window_bind_interaction_claim: MdocWindowBindInteractionClaim,
    mdoc_validity_interaction_claim: MdocValidityInteractionClaim,
    age_public: Option<predicates::PublicInput>,
    age_claimed_sums: Option<Vec<QM31>>,
    nat_public: Option<predicates::NatPublicInput>,
    nat_claimed_sums: Option<Vec<QM31>>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MdocProofByteBreakdown {
    pub proof_bytes: usize,
    pub stark_proof_bytes: usize,
    pub coprocessor_bundle_bytes: Option<usize>,
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
    #[cfg(feature = "ec-coprocessor")]
    let coprocessor_bundle_bytes = proof.coprocessor_bundle.as_ref().map(bincode_len);
    #[cfg(not(feature = "ec-coprocessor"))]
    let coprocessor_bundle_bytes = None;
    let non_stark_metadata_bytes = proof_bytes
        .saturating_sub(stark_proof_bytes)
        .saturating_sub(coprocessor_bundle_bytes.unwrap_or(0));

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

fn ecdsa_inputs_equal(left: &EcdsaVerifyInput, right: &EcdsaVerifyInput) -> bool {
    left.message_hash.0 == right.message_hash.0
        && left.signature.r.0 == right.signature.r.0
        && left.signature.s.0 == right.signature.s.0
        && left.public_key.x.0 == right.public_key.x.0
        && left.public_key.y.0 == right.public_key.y.0
}

#[cfg(feature = "ec-coprocessor")]
struct MdocCoprocessorBindingProver {
    issuer_input: EcdsaVerifyInput,
    device_input: EcdsaVerifyInput,
    issuer_witness: eu_id_ec_coprocessor::ecdsa::Witness,
    device_witness: eu_id_ec_coprocessor::ecdsa::Witness,
    bundle: Option<eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle>,
}

#[cfg(feature = "ec-coprocessor")]
impl MdocCoprocessorBindingProver {
    fn new(issuer_input: EcdsaVerifyInput, device_input: EcdsaVerifyInput) -> Result<Self, Error> {
        let issuer_witness = crate::ec_coprocessor::generate_witness_from_stwo(&issuer_input)
            .map_err(Error::CoprocessorWitness)?;
        let device_witness = crate::ec_coprocessor::generate_witness_from_stwo(&device_input)
            .map_err(Error::CoprocessorWitness)?;
        Ok(Self {
            issuer_input,
            device_input,
            issuer_witness,
            device_witness,
            bundle: None,
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
        crate::mix_coprocessor_tagged_statements(
            channel,
            &[
                (b"issuer".as_slice(), &self.issuer_input),
                (b"device".as_slice(), &self.device_input),
            ],
        )
        .expect("mdoc coprocessor statements mix");
        let seed = crate::draw_coprocessor_seed(channel);
        let inputs = [self.issuer_input.clone(), self.device_input.clone()];
        let witnesses = [self.issuer_witness.clone(), self.device_witness.clone()];
        let bundle = crate::ec_coprocessor::prove_implemented_circuit_bundle_batch_from_stwo(
            &inputs, &witnesses, seed,
        )
        .expect("mdoc coprocessor bundle proves both checked witnesses");
        crate::mix_coprocessor_rejoin(channel, &bundle).expect("mdoc coprocessor rejoin mixes");
        self.bundle = Some(bundle);
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
        crate::mix_coprocessor_tagged_statements(
            channel,
            &[
                (b"issuer".as_slice(), &self.issuer_input),
                (b"device".as_slice(), &self.device_input),
            ],
        )
        .map_err(VerificationError::InvalidStructure)?;
        let seed = crate::draw_coprocessor_seed(channel);
        let inputs = [self.issuer_input.clone(), self.device_input.clone()];
        crate::ec_coprocessor::verify_implemented_circuit_bundle_batch_from_stwo(
            &inputs,
            &self.bundle,
            seed,
        )
        .map_err(|err| VerificationError::InvalidStructure(format!("{err:?}")))?;
        crate::mix_coprocessor_rejoin(channel, &self.bundle)
            .map_err(VerificationError::InvalidStructure)?;
        Ok(())
    }
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

    #[cfg(not(feature = "ec-coprocessor"))]
    let issuer_draft = single_p256_draft(statement.issuer_input.clone())?;
    #[cfg(not(feature = "ec-coprocessor"))]
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
    #[cfg(not(feature = "ec-coprocessor"))]
    let issuer_scalar_z = SharedScalarZRelation::new();
    #[cfg(not(feature = "ec-coprocessor"))]
    let device_scalar_z = SharedScalarZRelation::new();

    let issuer_exposure = issuer_mso_exposure(statement);
    let attribute_exposures: Vec<_> = (0..statement.attributes.len())
        .map(|index| attribute_exposure(statement, index))
        .collect();

    #[cfg(not(feature = "ec-coprocessor"))]
    let mut issuer_p256 = P256Prover::new(&issuer_draft)
        .map_err(Error::P256Prepare)?
        .with_z_binding(issuer_scalar_z.clone());
    // The `mdoc/device` namespace is REQUIRED, not waste: the hinted-mul schedule
    // preprocessed columns are witness-dependent (measured: 18 of 215 columns —
    // the log-13 schedule set — differ between the issuer and device signatures).
    // Without the namespace the device module would alias onto the issuer's
    // schedule under air-core first-writer-wins tree-0 dedup, binding the wrong
    // constraints. Two genuinely distinct signatures cannot share the schedule.
    #[cfg(not(feature = "ec-coprocessor"))]
    let mut device_p256 = P256Prover::new(&device_draft)
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
    let mut sha_tables =
        ShaTablesProver::new(sha_table_multiplicities, sha_table_relations.clone());
    let mut issuer_sha = Sha256Prover::new(&issuer_sha_witness, shared_sha_log, SHA_GROUP_WIDTH)
        .with_shared_tables(sha_table_relations.clone())
        .with_digest_handle(issuer_digest.clone())
        .with_field_handle(issuer_exposure.clone(), issuer_field.clone());
    let mut device_sha = Sha256Prover::new(&device_sha_witness, shared_sha_log, SHA_GROUP_WIDTH)
        .with_shared_tables(sha_table_relations.clone())
        .with_digest_handle(device_digest.clone());
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

    #[cfg(not(feature = "ec-coprocessor"))]
    let issuer_bridge_rows = crate::bridge_rows(&issuer_p256.proof_claim().public_inputs.instances);
    #[cfg(not(feature = "ec-coprocessor"))]
    let issuer_bridge_log = crate::bridge_log_size(issuer_bridge_rows.len());
    #[cfg(not(feature = "ec-coprocessor"))]
    let mut issuer_bridge = DigestBindProver::new(
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
    let mut device_bridge = DigestBindProver::new(
        device_bridge_rows,
        device_bridge_log,
        device_scalar_z,
        device_digest.clone(),
    );
    #[cfg(feature = "ec-coprocessor")]
    let mut issuer_public_digest_bind =
        PublicDigestBind::new(statement.issuer_input.message_hash.0, issuer_digest.clone());
    #[cfg(feature = "ec-coprocessor")]
    let mut device_public_digest_bind =
        PublicDigestBind::new(statement.device_input.message_hash.0, device_digest.clone());
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
    #[cfg(feature = "ec-coprocessor")]
    let mut coprocessor = MdocCoprocessorBindingProver::new(
        statement.issuer_input.clone(),
        statement.device_input.clone(),
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

    #[cfg(not(feature = "ec-coprocessor"))]
    let config = issuer_p256.pcs_config();
    #[cfg(feature = "ec-coprocessor")]
    let config = crate::coprocessor_bridge_pcs_config();
    let stark_proof = {
        #[cfg(not(feature = "ec-coprocessor"))]
        let mut modules: Vec<&mut dyn AirProver> = vec![
            &mut sha_tables,
            &mut issuer_p256,
            &mut issuer_sha,
            &mut issuer_bridge,
            &mut device_p256,
            &mut device_sha,
            &mut device_bridge,
        ];
        #[cfg(feature = "ec-coprocessor")]
        let mut modules: Vec<&mut dyn AirProver> = vec![
            &mut sha_tables,
            &mut issuer_sha,
            &mut issuer_public_digest_bind,
            &mut device_sha,
            &mut device_public_digest_bind,
        ];
        for sha in &mut attribute_sha {
            modules.push(sha);
        }
        modules.push(&mut mdoc_window_bind);
        modules.push(&mut mdoc_validity);
        if let Some(age) = age.as_mut() {
            modules.push(age);
        }
        if let Some(nat) = nat.as_mut() {
            modules.push(nat);
        }
        #[cfg(feature = "ec-coprocessor")]
        modules.push(&mut coprocessor);
        air_core::prove(modules.as_mut_slice(), config)
            .map_err(|e| Error::Prove(format!("{e:?}")))?
    };
    #[cfg(feature = "ec-coprocessor")]
    let coprocessor_bundle = coprocessor.bundle.take().ok_or(Error::CoprocessorMissing)?;

    Ok(MdocCircuitProof {
        stark_proof,
        sha_tables_interaction_claim: sha_tables.interaction_claim().clone(),
        #[cfg(not(feature = "ec-coprocessor"))]
        issuer_p256_claim: issuer_p256.proof_claim().clone(),
        #[cfg(not(feature = "ec-coprocessor"))]
        issuer_p256_interaction_claim: issuer_p256.interaction_claim().clone(),
        #[cfg(not(feature = "ec-coprocessor"))]
        device_p256_claim: device_p256.proof_claim().clone(),
        #[cfg(not(feature = "ec-coprocessor"))]
        device_p256_interaction_claim: device_p256.interaction_claim().clone(),
        #[cfg(feature = "ec-coprocessor")]
        issuer_public_digest_bind_interaction_claim: issuer_public_digest_bind
            .interaction_claim()
            .clone(),
        #[cfg(feature = "ec-coprocessor")]
        device_public_digest_bind_interaction_claim: device_public_digest_bind
            .interaction_claim()
            .clone(),
        #[cfg(feature = "ec-coprocessor")]
        coprocessor_bundle: Some(coprocessor_bundle),
        issuer_sha_log_n_rows: shared_sha_log,
        issuer_sha_interaction_claim: issuer_sha.interaction_claim().clone(),
        device_sha_log_n_rows: shared_sha_log,
        device_sha_interaction_claim: device_sha.interaction_claim().clone(),
        attribute_sha_log_n_rows: vec![shared_sha_log; attribute_sha.len()],
        attribute_sha_interaction_claims: attribute_sha
            .iter()
            .map(|sha| sha.interaction_claim().clone())
            .collect(),
        #[cfg(not(feature = "ec-coprocessor"))]
        issuer_bridge_log_size: issuer_bridge_log,
        #[cfg(not(feature = "ec-coprocessor"))]
        issuer_bridge_interaction_claim: issuer_bridge.interaction_claim().clone(),
        #[cfg(not(feature = "ec-coprocessor"))]
        device_bridge_log_size: device_bridge_log,
        #[cfg(not(feature = "ec-coprocessor"))]
        device_bridge_interaction_claim: device_bridge.interaction_claim().clone(),
        mdoc_window_bind_interaction_claim: mdoc_window_bind.interaction_claim().clone(),
        mdoc_validity_interaction_claim: mdoc_validity.interaction_claim().clone(),
        age_public: age.as_ref().map(|_| age_public),
        age_claimed_sums: age.as_ref().map(|age| age.claimed_sums()),
        nat_public: nat.as_ref().map(|_| nat_public),
        nat_claimed_sums: nat.as_ref().map(|nat| nat.claimed_sums()),
    })
}

pub fn verify_mdoc_circuit(
    proof: &MdocCircuitProof,
    statement: &MdocCircuitStatement,
) -> Result<(), Error> {
    #[cfg(not(feature = "ec-coprocessor"))]
    if proof.issuer_p256_claim.public_inputs.instances.as_slice()
        != [expected_instance(&statement.issuer_input)]
    {
        return Err(Error::P256InstanceMismatch);
    }
    #[cfg(not(feature = "ec-coprocessor"))]
    if proof.device_p256_claim.public_inputs.instances.as_slice()
        != [expected_instance(&statement.device_input)]
    {
        return Err(Error::P256InstanceMismatch);
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
    let device_digest = SharedDigestRelation::new();
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
    #[cfg(not(feature = "ec-coprocessor"))]
    let issuer_scalar_z = SharedScalarZRelation::new();
    #[cfg(not(feature = "ec-coprocessor"))]
    let device_scalar_z = SharedScalarZRelation::new();

    #[cfg(not(feature = "ec-coprocessor"))]
    let mut issuer_p256 = P256Verifier::new(
        proof.issuer_p256_claim.clone(),
        proof.issuer_p256_interaction_claim.clone(),
    )
    .with_z_binding(issuer_scalar_z.clone());
    #[cfg(not(feature = "ec-coprocessor"))]
    let mut device_p256 = P256Verifier::new(
        proof.device_p256_claim.clone(),
        proof.device_p256_interaction_claim.clone(),
    )
    .with_preprocessed_namespace("mdoc/device")
    .with_z_binding(device_scalar_z.clone());
    #[cfg(not(feature = "ec-coprocessor"))]
    let expected_pcs_config = issuer_p256.expected_pcs_config();
    #[cfg(feature = "ec-coprocessor")]
    let expected_pcs_config = crate::coprocessor_bridge_pcs_config();
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
    let mut issuer_sha = Sha256Verifier::new(
        proof.issuer_sha_log_n_rows,
        SHA_GROUP_WIDTH,
        proof.issuer_sha_interaction_claim.clone(),
    )
    .with_shared_tables(sha_table_relations.clone())
    .with_digest_handle(issuer_digest.clone())
    .with_field_handle(issuer_mso_exposure(statement), issuer_field.clone());
    let mut device_sha = Sha256Verifier::new(
        proof.device_sha_log_n_rows,
        SHA_GROUP_WIDTH,
        proof.device_sha_interaction_claim.clone(),
    )
    .with_shared_tables(sha_table_relations.clone())
    .with_digest_handle(device_digest.clone());

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

    #[cfg(not(feature = "ec-coprocessor"))]
    let mut issuer_bridge = DigestBindVerifier::new(
        proof.issuer_bridge_log_size,
        proof.issuer_bridge_interaction_claim.clone(),
        issuer_scalar_z,
        issuer_digest,
    );
    #[cfg(not(feature = "ec-coprocessor"))]
    let mut device_bridge = DigestBindVerifier::new(
        proof.device_bridge_log_size,
        proof.device_bridge_interaction_claim.clone(),
        device_scalar_z,
        device_digest,
    );
    #[cfg(feature = "ec-coprocessor")]
    let mut issuer_public_digest_bind = PublicDigestBind::verifier(
        statement.issuer_input.message_hash.0,
        issuer_digest,
        proof.issuer_public_digest_bind_interaction_claim.clone(),
    );
    #[cfg(feature = "ec-coprocessor")]
    let mut device_public_digest_bind = PublicDigestBind::verifier(
        statement.device_input.message_hash.0,
        device_digest,
        proof.device_public_digest_bind_interaction_claim.clone(),
    );
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
        issuer_field,
        proof.mdoc_validity_interaction_claim.clone(),
    );
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
    let mut coprocessor = MdocCoprocessorBindingVerifier {
        issuer_input: statement.issuer_input.clone(),
        device_input: statement.device_input.clone(),
        bundle: proof
            .coprocessor_bundle
            .clone()
            .ok_or(Error::CoprocessorMissing)?,
    };

    #[cfg(not(feature = "ec-coprocessor"))]
    let mut modules: Vec<&mut dyn Air> = vec![
        &mut sha_tables,
        &mut issuer_p256,
        &mut issuer_sha,
        &mut issuer_bridge,
        &mut device_p256,
        &mut device_sha,
        &mut device_bridge,
    ];
    #[cfg(feature = "ec-coprocessor")]
    let mut modules: Vec<&mut dyn Air> = vec![
        &mut sha_tables,
        &mut issuer_sha,
        &mut issuer_public_digest_bind,
        &mut device_sha,
        &mut device_public_digest_bind,
    ];
    for sha in &mut attribute_sha {
        modules.push(sha);
    }
    modules.push(&mut mdoc_window_bind);
    modules.push(&mut mdoc_validity);
    if let Some(age) = age.as_mut() {
        modules.push(age);
    }
    if let Some(nat) = nat.as_mut() {
        modules.push(nat);
    }
    #[cfg(feature = "ec-coprocessor")]
    modules.push(&mut coprocessor);
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        air_core::verify(modules.as_mut_slice(), &proof.stark_proof)
    })) {
        Ok(Ok(())) => Ok(()),
        Ok(Err(error)) => Err(Error::Verify(format!("{error:?}"))),
        Err(_) => Err(Error::Verify(
            "malformed mdoc proof panicked during verification".to_string(),
        )),
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
    #[ignore = "slow: proves product mdoc circuit profile"]
    fn shared_sha_table_provider_claim_is_bound() {
        let fixture = demo_mdoc_circuit_fixture();
        let mut proof =
            prove_mdoc_circuit(&fixture.extracted, &fixture.statement).expect("mdoc proves");
        verify_mdoc_circuit(&proof, &fixture.statement).expect("mdoc verifies before tamper");

        proof.sha_tables_interaction_claim.round_split_pack[0].claimed_sum =
            -proof.sha_tables_interaction_claim.round_split_pack[0].claimed_sum;

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

        proof.sha_tables_interaction_claim.round_split_pack.clear();
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

    fn assert_verify_rejects(proof: &MdocCircuitProof, statement: &MdocCircuitStatement) {
        assert!(
            verify_mdoc_circuit(proof, statement).is_err(),
            "tampered mdoc proof unexpectedly verified"
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

        let mut missing_bundle = proof.clone();
        missing_bundle.coprocessor_bundle = None;
        assert!(matches!(
            verify_mdoc_circuit(&missing_bundle, &statement),
            Err(Error::CoprocessorMissing)
        ));

        let mut tampered = proof.clone();
        tampered.coprocessor_bundle =
            Some(tampered_bundle(proof.coprocessor_bundle.as_ref().unwrap()));
        assert_verify_rejects(&tampered, &statement);

        let mut issuer_z_mismatch = statement.clone();
        issuer_z_mismatch.issuer_input.message_hash.0[0] ^= 1;
        assert_verify_rejects(&proof, &issuer_z_mismatch);

        let mut device_z_mismatch = statement.clone();
        device_z_mismatch.device_input.message_hash.0[0] ^= 1;
        assert_verify_rejects(&proof, &device_z_mismatch);

        let mut cross_slot_z = statement.clone();
        std::mem::swap(
            &mut cross_slot_z.issuer_input.message_hash,
            &mut cross_slot_z.device_input.message_hash,
        );
        assert_verify_rejects(&proof, &cross_slot_z);

        let mut cross_signature = statement.clone();
        std::mem::swap(
            &mut cross_signature.issuer_input,
            &mut cross_signature.device_input,
        );
        assert_verify_rejects(&proof, &cross_signature);

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
        assert_verify_rejects(&replayed_identity_bundle, &statement);
    }

    #[test]
    #[ignore = "slow: proves product mdoc circuit with coprocessor bundle"]
    fn mdoc_coprocessor_statement_order_and_rejoin_guards_are_bound() {
        let (proof, statement) = verified_mdoc_proof();
        let bundle = proof.coprocessor_bundle.as_ref().unwrap();

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

        let mut without_rejoin = air_core::Ch::default();
        crate::mix_coprocessor_tagged_statements(
            &mut without_rejoin,
            &[
                (b"issuer".as_slice(), &statement.issuer_input),
                (b"device".as_slice(), &statement.device_input),
            ],
        )
        .expect("mdoc tagged statements mix");
        let _seed = crate::draw_coprocessor_seed(&mut without_rejoin);
        let without_rejoin_next = crate::draw_coprocessor_seed(&mut without_rejoin);

        let mut with_rejoin = air_core::Ch::default();
        crate::mix_coprocessor_tagged_statements(
            &mut with_rejoin,
            &[
                (b"issuer".as_slice(), &statement.issuer_input),
                (b"device".as_slice(), &statement.device_input),
            ],
        )
        .expect("mdoc tagged statements mix");
        let _seed = crate::draw_coprocessor_seed(&mut with_rejoin);
        crate::mix_coprocessor_rejoin(&mut with_rejoin, bundle).expect("mdoc rejoin mixes");
        let with_rejoin_next = crate::draw_coprocessor_seed(&mut with_rejoin);

        assert_ne!(with_rejoin_next, without_rejoin_next);
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
