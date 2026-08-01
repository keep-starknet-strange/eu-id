//! TS13 EUDI PID mdoc proof construction.
//!
//! This module parses the constrained ISO/IEC 18013-5 PID profile, prepares the
//! mdoc statement/witness, and proves issuer signature, ISO device
//! authentication, MSO digest membership, validity, device-key origin, and
//! `age_over_18 = true` in one proof. The device-auth signature binds
//! freshness.

use std::collections::{HashMap, HashSet, VecDeque};
use std::io::Cursor;
use std::sync::{Mutex, OnceLock};

use air_core::relations::{
    DigestBytesRelation, FieldBytesRelation, SharedDigestRelation, SharedFieldRelation,
};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use ciborium::value::Value;
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
use stwo_mldsa::binding::SharedT1CellRelation;
use stwo_mldsa::coeffs::relations::SharedRangeRelation;
use stwo_mldsa::coeffs::tables::SharedRangeTable;
use stwo_mldsa::expand_a::{ExpandABindings, ExpandAClaim, ExpandAProver, ExpandAVerifier};
use stwo_mldsa::private_key_eval::PrivateKeyEvalBindings;
use stwo_mldsa::statement::HOSTED_MSG_FIELD_ID;
use stwo_mldsa::statement::{
    keccak_job_shapes, MlDsaProver as MlDsaStatementProver, MlDsaVerifier as MlDsaStatementVerifier,
};
use stwo_mldsa::stwo_keccak::relations::SharedKeccakRelations;
use stwo_mldsa::stwo_keccak::service::{KeccakServiceProver, KeccakServiceVerifier};
use stwo_mldsa::types::{MlDsaPrivateKeyPublicInput, MlDsaVerifyInput};
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
use crate::mdoc_cbor_stream::{MdocCborInputMode, MdocCborStream, MdocCborStreamInteractionClaim};
use crate::mdoc_private_device_key_bind::{
    MdocPrivateDeviceKeyBind, MdocPrivateDeviceKeyInteractionClaim,
    MDOC_PRIVATE_DEVICE_KEY_ACTIVE_ROWS,
};
use crate::mdoc_private_item_bind::{
    MdocPrivateItemBind, MdocPrivateItemError, MdocPrivateItemFieldIds, MdocPrivateItemHandles,
    MdocPrivateItemInteractionClaim, MdocPrivateItemPrivateInput, MdocPrivateTag24WrapperReason,
};
use crate::mdoc_private_message::{MdocPrivateMessageInteractionClaim, MdocPrivateMessageProvider};
use crate::mdoc_private_mso_bind::{
    MdocPrivateMsoBind, MdocPrivateMsoBindSpec, MdocPrivateMsoBindWitness,
    MdocPrivateMsoInteractionClaim, MdocPrivateMsoShaStreamSpec, SharedMdocDevicePkStartRelation,
    SharedMdocMsoStartRelation,
};
use crate::mdoc_private_mso_validity::{
    MdocPrivateMsoValidity, MdocPrivateMsoValidityInteractionClaim, MdocPrivateMsoValiditySpec,
    SharedMdocMsoValidityBytesRelation,
};
pub use crate::mdoc_value_digests_scan::MsoValueDigestsCanonicalityReason as MdocMsoValueDigestsCanonicalityReason;
use crate::mdoc_value_digests_scan::{
    MdocSelectedValueDigest, MdocValueDigestItemHandles, MdocValueDigestsInteractionClaim,
    MdocValueDigestsScan, MdocValueDigestsScanError, MdocValueDigestsScanHandles,
    MdocValueDigestsScanSpec, MdocValueDigestsScanWitness,
};
use crate::policy::Date;
use crate::ts13_demo::{Ts13PublicContextBind, TS13_DEMO_VERIFICATION_TIMESTAMP_RFC3339_UTC_BYTES};
use crate::Error;

/// ISO/IEC 18013-5:2021 MobileSecurityObject version.
const MDOC_PROFILE_VERSION: &str = "1.0";
/// The document type that the fixture and parser use.
const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const ISSUER_SIGNED_ITEM_KEYS: [&str; 4] =
    ["elementValue", "digestID", "random", "elementIdentifier"];
/// COSE protected header `{1: -49}` (ML-DSA-65,
/// `stwo_mldsa::constants::COSE_ALG_ML_DSA_65`): CBOR `A1 01 38 30`.
pub(crate) const MLDSA_PROTECTED_HEADER: &[u8] = &[0xA1, 0x01, 0x38, 0x30];
pub(crate) const MLDSA44_PROTECTED_HEADER: &[u8] = &[0xA1, 0x01, 0x38, 0x2F];
const CBOR_TAG_ENCODED_CBOR: u64 = 24;
const MDOC_ATTRIBUTE_FIELD_IDS: MdocPrivateItemFieldIds = MdocPrivateItemFieldIds {
    outer_stream: 0x4d49_0000,
    inner_stream: 0x4d49_0001,
    element_identifier: 16,
    element_value: 20,
};
const MDOC_MSO_SHA_STREAM_FIELD_ID: u32 = 0x4d53_0000;
const MDOC_MSO_SHA_LOG_SIZE: u32 = 11;
const MDOC_MSO_SHA_NAMESPACE: &str = "mdoc/mso-sha";
const MDOC_ATTRIBUTE_SHA_NAMESPACE: &str = "mdoc/attribute-sha/0";
const TS13_REVOCATION_MESSAGE_LEN: usize = 20;
/// The verifier keeps only a small working set of canonical tree-0 roots.
/// It adds a root only after successful proof verification.
/// A malformed proof cannot change this cache.
const MDOC_TREE0_ROOT_CACHE_CAPACITY: usize = 16;
/// Instance namespaces separate the hosted ML-DSA roles.
/// The prover and verifier use the same namespaces.
/// Each namespace is part of the transcript.
/// It also prefixes witness-dependent preprocessed column identifiers.
const MDOC_ISSUER_MLDSA_NAMESPACE: &str = "mdoc/issuer";
const MDOC_DEVICE_MLDSA_NAMESPACE: &str = "mdoc/device";
const MDOC_DEVICE_EXPAND_A_NAMESPACE: &str = "mdoc/ts13/device-expand-a";
const MDOC_REVOCATION_MLDSA_NAMESPACE: &str = "mdoc/ts13/revocation";
/// HashIo stream bases separate the hosted ML-DSA roles.
/// All instances share one Keccak-service relation set.
/// Thus, each role uses a unique stream range.
/// Each base is a multiple of [`stwo_mldsa::statement::STREAM_BASE_STRIDE`].
pub(crate) const MDOC_ISSUER_MLDSA_STREAM_BASE: u32 = 0x100;
pub(crate) const MDOC_DEVICE_MLDSA_STREAM_BASE: u32 = 0x200;
pub(crate) const MDOC_REVOCATION_MLDSA_STREAM_BASE: u32 = 0x300;
const MDOC_DEVICE_EXPAND_A_STREAM_BASE: u32 = 0x400;
const _: () = assert!(
    MDOC_ISSUER_MLDSA_STREAM_BASE.is_multiple_of(stwo_mldsa::statement::STREAM_BASE_STRIDE)
        && MDOC_DEVICE_MLDSA_STREAM_BASE.is_multiple_of(stwo_mldsa::statement::STREAM_BASE_STRIDE)
        && MDOC_REVOCATION_MLDSA_STREAM_BASE
            .is_multiple_of(stwo_mldsa::statement::STREAM_BASE_STRIDE)
        && MDOC_DEVICE_EXPAND_A_STREAM_BASE
            .is_multiple_of(stwo_mldsa::statement::STREAM_BASE_STRIDE)
);

pub(crate) fn ts13_demo_mldsa_keccak_job_shapes(
    device_message_len: usize,
) -> Vec<stwo_mldsa::stwo_keccak::sponge::Shape> {
    let mut shapes = keccak_job_shapes(
        TS13_DEMO_ISSUER_MESSAGE_BYTES,
        MDOC_ISSUER_MLDSA_STREAM_BASE,
        false,
    );
    shapes.extend(
        stwo_mldsa::expand_a::shake128_job_shapes(
            stwo_mldsa::profile::ML_DSA_44,
            MDOC_DEVICE_EXPAND_A_STREAM_BASE,
        )
        .expect("fixed TS13 ExpandA stream base is valid"),
    );
    shapes.extend(stwo_mldsa::statement::hosted_private_key_keccak_job_shapes(
        device_message_len,
        MDOC_DEVICE_MLDSA_STREAM_BASE,
    ));
    shapes.extend(keccak_job_shapes(
        TS13_REVOCATION_MESSAGE_LEN,
        MDOC_REVOCATION_MLDSA_STREAM_BASE,
        false,
    ));
    shapes
}

/// List the fixed TS13 module order for the prover and verifier.
/// Each invocation supplies modules with the same roles.
macro_rules! collect_ts13_demo_modules {
    (
        $modules:ident;
        sha_tables = $sha_tables:expr,
        range_tables = $range_tables:expr,
        keccak_service = $keccak_service:expr,
        public_context = $public_context:expr,
        issuer_message = $issuer_message:expr,
        issuer_mldsa = $issuer_mldsa:expr,
        attribute_sha = $attribute_sha:expr,
        mso_sha = $mso_sha:expr,
        item_outer_parser = $item_outer_parser:expr,
        item_inner_parser = $item_inner_parser:expr,
        item_binder = $item_binder:expr,
        mso_binder = $mso_binder:expr,
        mso_validity = $mso_validity:expr,
        value_digests = $value_digests:expr,
        expand_a = $expand_a:expr,
        device_key = $device_key:expr,
        device_mldsa = $device_mldsa:expr,
        revocation_range = $revocation_range:expr,
        revocation_mldsa = $revocation_mldsa:expr,
        revocation_public = $revocation_public:expr $(,)?
    ) => {{
        $modules.push($sha_tables); // 1
        $modules.push($range_tables); // 2
        $modules.push($keccak_service); // 3
        $modules.push($public_context); // 4
        $modules.push($issuer_message); // 5
        $modules.push($issuer_mldsa); // 6
        $modules.push($attribute_sha); // 7
        $modules.push($mso_sha); // 8
        $modules.push($item_outer_parser); // 9: first AIR in logical parser module 9
        $modules.push($item_inner_parser); // 10: second AIR in logical parser module 9
        $modules.push($item_binder); // 11: logical module 10
        $modules.push($mso_binder); // 12: logical module 11
        $modules.push($mso_validity); // 13: logical module 12
        $modules.push($value_digests); // 14: logical module 13
        $modules.push($expand_a); // 15: logical module 14
        $modules.push($device_key); // 16: logical module 15
        $modules.push($device_mldsa); // 17: logical module 16
        $modules.push($revocation_range); // 18: logical module 17
        $modules.push($revocation_mldsa); // 19: logical module 18
        $modules.push($revocation_public); // 20: logical module 19
    }};
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MdocPidRequest {
    pub(crate) session_transcript: Vec<u8>,
}

#[derive(Clone, Debug)]
pub struct ExtractedMdocAttribute {
    pub digest_id: u32,
    pub item: Vec<u8>,
}

impl MdocPidRequest {
    pub fn age_over_18(session_transcript: Vec<u8>) -> Self {
        Self { session_transcript }
    }
}

fn private_issuer_verifier_input(public_key: &[u8]) -> Result<Box<MlDsaVerifyInput>, Error> {
    let decoded_key =
        stwo_mldsa::reference::encoding::pk_decode(stwo_mldsa::profile::ML_DSA_65, public_key)
            .map_err(|error| Error::Verify(format!("mdoc issuer public key decode: {error:?}")))?;
    let zero_signature = stwo_mldsa::reference::encoding::SignatureParts {
        c_tilde: [0; stwo_mldsa::constants::C_TILDE_BYTES],
        z: [[0; stwo_mldsa::constants::N]; stwo_mldsa::constants::L],
        h: [[0; stwo_mldsa::constants::N]; stwo_mldsa::constants::K],
    };
    Ok(Box::new(MlDsaVerifyInput::from_decoded(
        stwo_mldsa::profile::ML_DSA_65,
        &decoded_key,
        &zero_signature,
        [0; 64],
        vec![0; TS13_DEMO_ISSUER_MESSAGE_BYTES],
    )))
}

#[derive(Clone, Debug)]
pub struct ExtractedPidMdoc {
    pub attribute: ExtractedMdocAttribute,
    pub valid_from: (u16, u8, u8),
    pub valid_until: (u16, u8, u8),
    pub mso: Vec<u8>,
    /// The ML-DSA-65 issuer-auth verification input.
    pub issuer_auth_input: Box<MlDsaVerifyInput>,
    /// The ML-DSA-44 device-auth verification input.
    pub device_auth_input: Box<MlDsaVerifyInput>,
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
    InvalidSignature(&'static str),
    UnsupportedCircuitValue(&'static str),
    UnsupportedMsoVersion(String),
    InvalidTdate(&'static str),
    CredentialNotYetValid,
    CredentialExpired,
    SaltTooShort {
        len: usize,
    },
    ValueEqualityMismatch {
        element: String,
    },
    IssuerSignedItemNotCanonical {
        offset: usize,
        reason: MdocIssuerSignedItemCanonicalityReason,
    },
    MsoValueDigestsNotCanonical {
        offset: usize,
        reason: MdocMsoValueDigestsCanonicalityReason,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MdocIssuerSignedItemCanonicalityReason {
    EmptyInput,
    TraceTooLarge { bytes: usize },
    InvalidShaPadding(&'static str),
    TruncatedToken { needed: usize },
    InvalidAdditionalInfo { additional: u8 },
    UnsupportedContainerLength { additional: u8 },
    NonMinimalArgument { argument: u64 },
    InvalidSimpleValue { additional: u8 },
    NestingTooDeep,
    MissingContainer,
    TrailingCbor { input_len: usize },
    IncompleteRoot,
    ExpectedTag24,
    ExpectedTag24ByteString,
    ExpectedTag24ByteStringU8Length { additional: u8 },
    Tag24ByteStringLengthMismatch { declared: usize, actual: usize },
}

fn issuer_signed_item_parser_error(
    error: crate::mdoc_cbor_stream::MdocCborStreamError,
    base_offset: usize,
) -> MdocError {
    use crate::mdoc_cbor_stream::MdocCborStreamError as ParserError;
    use MdocIssuerSignedItemCanonicalityReason as Reason;

    let (relative_offset, reason) = match error {
        ParserError::EmptyInput => (0, Reason::EmptyInput),
        ParserError::TraceTooLarge { bytes } => (0, Reason::TraceTooLarge { bytes }),
        ParserError::InvalidShaPadding(reason) => (0, Reason::InvalidShaPadding(reason)),
        ParserError::TruncatedToken { index, needed } => (index, Reason::TruncatedToken { needed }),
        ParserError::InvalidAdditionalInfo { index, additional } => {
            (index, Reason::InvalidAdditionalInfo { additional })
        }
        ParserError::UnsupportedContainerLength { index, additional } => {
            (index, Reason::UnsupportedContainerLength { additional })
        }
        ParserError::NonMinimalArgument { index, argument } => {
            (index, Reason::NonMinimalArgument { argument })
        }
        ParserError::InvalidSimpleValue { index, additional } => {
            (index, Reason::InvalidSimpleValue { additional })
        }
        ParserError::NestingTooDeep { index } => (index, Reason::NestingTooDeep),
        ParserError::MissingContainer { index } => (index, Reason::MissingContainer),
        ParserError::TrailingCbor {
            root_end,
            input_len,
        } => (root_end, Reason::TrailingCbor { input_len }),
        ParserError::IncompleteRoot => (0, Reason::IncompleteRoot),
    };
    MdocError::IssuerSignedItemNotCanonical {
        offset: base_offset + relative_offset,
        reason,
    }
}

fn map_private_item_prove_error(error: MdocPrivateItemError) -> Error {
    const TAG24_OUTER_PREFIX_LEN: usize = 4;
    match error {
        MdocPrivateItemError::OuterParser(error) => {
            Error::Mdoc(issuer_signed_item_parser_error(error, 0))
        }
        MdocPrivateItemError::InnerParser(error) => Error::Mdoc(issuer_signed_item_parser_error(
            error,
            TAG24_OUTER_PREFIX_LEN,
        )),
        MdocPrivateItemError::InvalidTag24Wrapper { offset, reason } => {
            let reason = match reason {
                MdocPrivateTag24WrapperReason::TruncatedToken { needed } => {
                    MdocIssuerSignedItemCanonicalityReason::TruncatedToken { needed }
                }
                MdocPrivateTag24WrapperReason::ExpectedTag24 => {
                    MdocIssuerSignedItemCanonicalityReason::ExpectedTag24
                }
                MdocPrivateTag24WrapperReason::ExpectedByteString => {
                    MdocIssuerSignedItemCanonicalityReason::ExpectedTag24ByteString
                }
                MdocPrivateTag24WrapperReason::ExpectedU8ByteStringLength { additional } => {
                    MdocIssuerSignedItemCanonicalityReason::ExpectedTag24ByteStringU8Length {
                        additional,
                    }
                }
                MdocPrivateTag24WrapperReason::ByteStringLengthMismatch { declared, actual } => {
                    MdocIssuerSignedItemCanonicalityReason::Tag24ByteStringLengthMismatch {
                        declared,
                        actual,
                    }
                }
            };
            Error::Mdoc(MdocError::IssuerSignedItemNotCanonical { offset, reason })
        }
        other => Error::Prove(format!("private IssuerSignedItem: {other}")),
    }
}

fn map_value_digests_prove_error(error: MdocValueDigestsScanError) -> Error {
    match error {
        MdocValueDigestsScanError::MsoValueDigestsNotCanonical { offset, reason } => {
            Error::Mdoc(MdocError::MsoValueDigestsNotCanonical { offset, reason })
        }
        other => Error::Prove(format!("private valueDigests scanner: {other}")),
    }
}

/// Parse an ML-DSA-65 `issuerAuth` and build the circuit witness.
/// Use FIPS 204 Algorithm 3 in pure mode with an empty context.
fn mldsa_issuer_input(
    issuer_unprotected: &[(Value, Value)],
    issuer_auth: &CoseSign1,
) -> Result<MlDsaVerifyInput, MdocError> {
    let pk = mldsa_issuer_pk_from_unprotected(issuer_unprotected)?;
    let trace = stwo_mldsa::reference::verify::verify_internals(
        stwo_mldsa::profile::ML_DSA_65,
        &pk,
        &issuer_auth.sig_structure,
        &issuer_auth.signature_bytes,
    )
    .map_err(|_| MdocError::InvalidSignature("issuerAuth"))?;
    if !trace.accepted {
        return Err(MdocError::InvalidSignature("issuerAuth"));
    }
    let decoded_pk =
        stwo_mldsa::reference::encoding::pk_decode(stwo_mldsa::profile::ML_DSA_65, &pk)
            .map_err(|_| MdocError::InvalidCoseKey("ML-DSA-65 public key"))?;
    let decoded_sig = stwo_mldsa::reference::encoding::sig_decode(
        stwo_mldsa::profile::ML_DSA_65,
        &issuer_auth.signature_bytes,
    )
    .map_err(|_| MdocError::InvalidSignature("issuerAuth"))?;
    Ok(MlDsaVerifyInput::from_decoded(
        stwo_mldsa::profile::ML_DSA_65,
        &decoded_pk,
        &decoded_sig,
        trace.tr,
        issuer_auth.sig_structure.clone(),
    ))
}

/// Mirror of [`mldsa_issuer_input`] for the device role: native FIPS 204
/// pre-check over the device `Sig_structure`, then the decoded in-circuit
/// input. The verifier fixes this role to ML-DSA-44.
fn mldsa_device_auth_input(
    pk: &[u8],
    device_signature: &CoseSign1,
) -> Result<Box<MlDsaVerifyInput>, MdocError> {
    let profile = stwo_mldsa::profile::ML_DSA_44;
    let trace = stwo_mldsa::reference::verify::verify_internals(
        profile,
        pk,
        &device_signature.sig_structure,
        &device_signature.signature_bytes,
    )
    .map_err(|_| MdocError::InvalidSignature("deviceSignature"))?;
    if !trace.accepted {
        return Err(MdocError::InvalidSignature("deviceSignature"));
    }
    let decoded_pk = stwo_mldsa::reference::encoding::pk_decode(profile, pk)
        .map_err(|_| MdocError::InvalidCoseKey("ML-DSA-44 public key"))?;
    let decoded_sig =
        stwo_mldsa::reference::encoding::sig_decode(profile, &device_signature.signature_bytes)
            .map_err(|_| MdocError::InvalidSignature("deviceSignature"))?;
    let input = MlDsaVerifyInput::from_decoded(
        profile,
        &decoded_pk,
        &decoded_sig,
        trace.tr,
        device_signature.sig_structure.clone(),
    );
    Ok(Box::new(input))
}

pub fn extract_pid_mdoc(
    document: &[u8],
    request: &MdocPidRequest,
) -> Result<ExtractedPidMdoc, MdocError> {
    let doc = decode_value(document)?;
    let doc_map = document_map(&doc)?;
    let doctype = text_field(doc_map, "docType")?;
    if doctype != PID_DOCTYPE {
        return Err(MdocError::DoctypeMismatch);
    }

    let issuer_signed = map_field(doc_map, "issuerSigned")?;
    let issuer_auth = parse_cose_sign1(value_field(issuer_signed, "issuerAuth")?)?;
    let issuer_unprotected = expect_map(&issuer_auth.unprotected, "issuerAuth.unprotected")?;
    let issuer_mldsa_input = mldsa_issuer_input(issuer_unprotected, &issuer_auth)?;

    let mso = parse_mso(&issuer_auth.payload, PID_NAMESPACE)?;
    if mso.version != MDOC_PROFILE_VERSION {
        return Err(MdocError::UnsupportedMsoVersion(mso.version));
    }
    if mso.doc_type != PID_DOCTYPE {
        return Err(MdocError::DoctypeMismatch);
    }

    let namespace_items = namespace_items(issuer_signed, PID_NAMESPACE)?;
    let element_identifier = "age_over_18";
    let item = find_item(namespace_items, element_identifier)?
        .ok_or_else(|| MdocError::ElementMissing(element_identifier.to_string()))?;
    validate_item_digest(
        &mso.value_digests,
        element_identifier,
        item.digest_id,
        &item.bytes,
    )?;
    if encode_value(item.value) != [0xf5] {
        return Err(MdocError::ValueEqualityMismatch {
            element: element_identifier.to_string(),
        });
    }
    let attribute = ExtractedMdocAttribute {
        digest_id: item.digest_id,
        item: item.bytes,
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

    Ok(ExtractedPidMdoc {
        attribute,
        valid_from: mso.valid_from,
        valid_until: mso.valid_until,
        mso: issuer_auth.payload,
        issuer_auth_input: Box::new(issuer_mldsa_input),
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

fn attribute_exposure() -> FieldExposure {
    FieldExposure::from_full_padded_stream(
        MDOC_ATTRIBUTE_FIELD_IDS.outer_stream,
        usize::from(TS13_DEMO_ITEM_PADDED_BYTES),
    )
}

fn mdoc_phase_error(phase: &'static str, message: String) -> Error {
    if phase == "prove" {
        Error::Prove(message)
    } else {
        Error::Verify(message)
    }
}

fn validate_single_mldsa_public_key(
    role: &'static str,
    profile: stwo_mldsa::profile::MlDsaProfile,
    input: &MlDsaVerifyInput,
    phase: &'static str,
) -> Result<(), Error> {
    input
        .validate_public_key(profile)
        .map_err(|message| mdoc_phase_error(phase, format!("mdoc {role} public key: {message}")))
}

fn validate_public_input_shape(
    public: &MdocTs13DemoCircuitPublicInput,
    phase: &'static str,
) -> Result<Date, Error> {
    let fail = |message| mdoc_phase_error(phase, format!("mdoc public shape: {message}"));
    if public.trusted_issuer_public_key.len() != stwo_mldsa::constants::PK_BYTES
        || public.device_cose_sig_structure.is_empty()
        || public.device_cose_sig_structure.len() > TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY
    {
        return Err(fail(
            "public input does not match the fixed TS13 profile".to_string(),
        ));
    }
    let current_date = match utc_date_from_epoch_seconds(public.timestamp_epoch_seconds) {
        Ok(date) => date,
        Err(Error::Verify(message)) => return Err(fail(message)),
        Err(error) => return Err(error),
    };
    Ok(current_date)
}

fn validate_public_issuer_projection(issuer: &MlDsaVerifyInput) -> Result<(), Error> {
    let signature_witness_is_zero = |input: &MlDsaVerifyInput| {
        input.tr.iter().all(|&byte| byte == 0)
            && input.c_tilde.iter().all(|&byte| byte == 0)
            && input
                .z
                .iter()
                .flatten()
                .all(|&coefficient| coefficient == 0)
            && input.hint.iter().flatten().all(|&bit| bit == 0)
    };
    if !signature_witness_is_zero(issuer) || issuer.message.iter().any(|&byte| byte != 0) {
        return Err(Error::Verify(
            "mdoc verifier input contains a private issuer message or signature witness"
                .to_string(),
        ));
    }
    Ok(())
}

fn validate_extracted_profile(
    extracted: &ExtractedPidMdoc,
    public: &MdocTs13DemoCircuitPublicInput,
    current_date: &Date,
) -> Result<(), Error> {
    if extracted.issuer_auth_input.message.len() != TS13_DEMO_ISSUER_MESSAGE_BYTES
        || extracted.mso.len() != TS13_DEMO_MSO_PAYLOAD_BYTES
        || stwo_sha256::native::pad_message(&extracted.attribute.item).len()
            != usize::from(TS13_DEMO_ITEM_PADDED_BYTES)
    {
        return Err(Error::UnsupportedDemoCredentialShape);
    }
    validate_single_mldsa_public_key(
        "issuer",
        stwo_mldsa::profile::ML_DSA_65,
        &extracted.issuer_auth_input,
        "prove",
    )?;
    validate_single_mldsa_public_key(
        "device",
        stwo_mldsa::profile::ML_DSA_44,
        &extracted.device_auth_input,
        "prove",
    )?;
    if extracted
        .issuer_auth_input
        .encode_pk(stwo_mldsa::profile::ML_DSA_65)
        != public.trusted_issuer_public_key
        || extracted.device_auth_input.message != public.device_cose_sig_structure
    {
        return Err(Error::Prove(
            "TS13 demo private witness does not match the public theorem".to_string(),
        ));
    }

    let current_date = date_tuple(*current_date).map_err(Error::Mdoc)?;
    if current_date < extracted.valid_from {
        return Err(Error::Mdoc(MdocError::CredentialNotYetValid));
    }
    if current_date > extracted.valid_until {
        return Err(Error::Mdoc(MdocError::CredentialExpired));
    }
    Ok(())
}

/// Build the prover input for the ML-DSA revocation check.
///
/// The signature and the 20-byte range message are private. The range AIR and
/// the ML-DSA AIR consume the same message relation.
fn ts13_revocation_mldsa_prover_input(
    revocation: &MdocRevocationPublicInputs,
    signature: &MdocRevocationSignature,
    message: Vec<u8>,
) -> Result<Box<MlDsaVerifyInput>, Error> {
    let pk = revocation.revocation_public_key.as_bytes();
    let decoded_pk = stwo_mldsa::reference::encoding::pk_decode(stwo_mldsa::profile::ML_DSA_65, pk)
        .map_err(|error| Error::Prove(format!("TS13 revocation pk decode: {error:?}")))?;
    let decoded_sig = stwo_mldsa::reference::encoding::sig_decode(
        stwo_mldsa::profile::ML_DSA_65,
        signature.as_bytes(),
    )
    .map_err(|error| Error::Prove(format!("TS13 revocation sig decode: {error:?}")))?;
    // `tr` depends only on the public key. The prover and verifier compute the
    // same value without access to the private message.
    let (tr_bytes, _) = stwo_mldsa::reference::sponge::shake256(&[pk], 64);
    let tr: [u8; 64] = tr_bytes
        .try_into()
        .expect("shake256 returns the requested 64 bytes");
    Ok(Box::new(MlDsaVerifyInput::from_decoded(
        stwo_mldsa::profile::ML_DSA_65,
        &decoded_pk,
        &decoded_sig,
        tr,
        message,
    )))
}

/// Build the verifier input for the ML-DSA revocation check.
///
/// The proof commits to the private signature witness. The verifier uses the
/// public key and zero placeholders of the required size.
fn ts13_revocation_mldsa_verifier_input(
    revocation: &MdocRevocationPublicInputs,
    message: Vec<u8>,
) -> Result<Box<MlDsaVerifyInput>, Error> {
    let pk = revocation.revocation_public_key.as_bytes();
    let decoded_pk = stwo_mldsa::reference::encoding::pk_decode(stwo_mldsa::profile::ML_DSA_65, pk)
        .map_err(|error| Error::Verify(format!("TS13 revocation pk decode: {error:?}")))?;
    let zero_signature = stwo_mldsa::reference::encoding::SignatureParts {
        c_tilde: [0; stwo_mldsa::constants::C_TILDE_BYTES],
        z: [[0; stwo_mldsa::constants::N]; stwo_mldsa::constants::L],
        h: [[0; stwo_mldsa::constants::N]; stwo_mldsa::constants::K],
    };
    let (tr_bytes, _) = stwo_mldsa::reference::sponge::shake256(&[pk], 64);
    let tr: [u8; 64] = tr_bytes
        .try_into()
        .expect("shake256 returns the requested 64 bytes");
    Ok(Box::new(MlDsaVerifyInput::from_decoded(
        stwo_mldsa::profile::ML_DSA_65,
        &decoded_pk,
        &zero_signature,
        tr,
        message,
    )))
}

fn decode_value(bytes: &[u8]) -> Result<Value, MdocError> {
    ciborium::de::from_reader(bytes).map_err(|error| MdocError::Cbor(error.to_string()))
}

fn decode_value_exact(bytes: &[u8]) -> Result<Value, MdocError> {
    let mut reader = Cursor::new(bytes);
    let value = ciborium::de::from_reader(&mut reader)
        .map_err(|error| MdocError::Cbor(error.to_string()))?;
    if reader.position() != bytes.len() as u64 {
        return Err(MdocError::Cbor("trailing CBOR data".to_string()));
    }
    Ok(value)
}

fn encode_value(value: Value) -> Vec<u8> {
    let mut out = Vec::new();
    ciborium::ser::into_writer(&value, &mut out).expect("CBOR serialization into Vec");
    out
}

fn parse_cose_sign1(value: &Value) -> Result<CoseSign1, MdocError> {
    parse_cose_sign1_inner(stwo_mldsa::profile::ML_DSA_65, value, None)
}

fn parse_cose_sign1_with_detached_payload(
    value: &Value,
    detached_payload: &[u8],
) -> Result<CoseSign1, MdocError> {
    parse_cose_sign1_inner(
        stwo_mldsa::profile::ML_DSA_44,
        value,
        Some(detached_payload),
    )
}

fn parse_cose_sign1_inner(
    profile: stwo_mldsa::profile::MlDsaProfile,
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
    let expected_header = match profile {
        stwo_mldsa::profile::MlDsaProfile::MlDsa44 => MLDSA44_PROTECTED_HEADER,
        stwo_mldsa::profile::MlDsaProfile::MlDsa65 => MLDSA_PROTECTED_HEADER,
    };
    if protected != expected_header {
        return Err(MdocError::InvalidCoseSign1(match profile {
            stwo_mldsa::profile::MlDsaProfile::MlDsa44 => "protected header must be ML-DSA-44",
            stwo_mldsa::profile::MlDsaProfile::MlDsa65 => "protected header must be ML-DSA-65",
        }));
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
    if signature_bytes.len() != profile.sig_bytes() {
        return Err(MdocError::InvalidCoseSign1(match profile {
            stwo_mldsa::profile::MlDsaProfile::MlDsa44 => "ML-DSA-44 signature length",
            stwo_mldsa::profile::MlDsaProfile::MlDsa65 => "ML-DSA-65 signature length",
        }));
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
    let device_authentication = encode_value(Value::Array(vec![
        "DeviceAuthentication".into(),
        session_transcript,
        doc_type.into(),
        Value::Tag(24, Box::new(Value::Bytes(device_namespaces))),
    ]));
    Ok(encode_value(Value::Tag(
        24,
        Box::new(Value::Bytes(device_authentication)),
    )))
}

fn expected_device_authentication_bytes(request: &MdocPidRequest) -> Result<Vec<u8>, MdocError> {
    device_authentication_bytes(&request.session_transcript, PID_DOCTYPE)
}

fn parse_mso(bytes: &[u8], namespace: &str) -> Result<ParsedMso, MdocError> {
    let value = decode_value_exact(bytes)?;
    let value = match value {
        Value::Tag(CBOR_TAG_ENCODED_CBOR, inner) => {
            let mso_bytes = expect_bytes(&inner, "MobileSecurityObjectBytes")?;
            decode_value_exact(mso_bytes)?
        }
        value => value,
    };
    parse_mso_value(&value, namespace)
}

fn parse_mso_value(value: &Value, namespace: &str) -> Result<ParsedMso, MdocError> {
    let mso = expect_map(value, "MobileSecurityObject")?;
    let version = text_field(mso, "version")?.to_string();
    let doc_type = text_field(mso, "docType")?.to_string();
    let digest_algorithm = text_field(mso, "digestAlgorithm")?;
    if digest_algorithm != "SHA-256" {
        return Err(MdocError::UnsupportedDigestAlgorithm(
            digest_algorithm.to_string(),
        ));
    }

    let value_digests = map_field(mso, "valueDigests")?;
    let namespace_key = Value::Text(namespace.to_string());
    let mut namespace_matches = value_digests
        .iter()
        .filter_map(|(key, value)| (key == &namespace_key).then_some(value));
    let namespace_digests = namespace_matches
        .next()
        .ok_or(MdocError::NamespaceMissing)?;
    if namespace_matches.next().is_some() {
        return Err(MdocError::UnsupportedCircuitValue(
            "duplicate valueDigests namespace",
        ));
    }
    let namespace_digests = expect_map(namespace_digests, "valueDigests namespace")?;
    let mut digests = HashMap::new();
    for (key, value) in namespace_digests {
        let digest_id = expect_u32(key, "digestID")?;
        let digest = expect_digest(value, "elementDigest")?;
        if digests.insert(digest_id, digest).is_some() {
            return Err(MdocError::UnsupportedCircuitValue("duplicate digestID"));
        }
    }

    let device_key_info = map_field(mso, "deviceKeyInfo")?;
    let device_key = parse_device_cose_key(value_field(device_key_info, "deviceKey")?)?;
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
        let item_bytes = issuer_signed_item_bytes(item)?;
        let parsed = parse_issuer_signed_item_bytes(&item_bytes)?;
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

fn parse_issuer_signed_item_bytes(bytes: &[u8]) -> Result<ParsedItem, MdocError> {
    let value = decode_value(bytes)?;
    let Value::Tag(24, inner) = value else {
        return Err(MdocError::WrongType("IssuerSignedItemBytes tag 24"));
    };
    let item_bytes = expect_bytes(&inner, "IssuerSignedItemBytes")?;
    let item_value = decode_value(item_bytes)?;
    let item = expect_map(&item_value, "IssuerSignedItem")?;
    ensure_issuer_signed_item_keys(item)?;
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

/// Require the four unique `IssuerSignedItem` keys in any map order.
fn ensure_issuer_signed_item_keys(item: &[(Value, Value)]) -> Result<(), MdocError> {
    if item.len() != ISSUER_SIGNED_ITEM_KEYS.len() {
        return Err(MdocError::UnsupportedCircuitValue(
            "IssuerSignedItem key set",
        ));
    }
    for expected in ISSUER_SIGNED_ITEM_KEYS {
        let present = item
            .iter()
            .any(|(key, _)| key == &Value::Text(expected.to_string()));
        if !present {
            return Err(MdocError::UnsupportedCircuitValue(
                "IssuerSignedItem key set",
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

/// Parse the MSO ML-DSA-44 AKP `deviceKey`.
fn parse_device_cose_key(value: &Value) -> Result<Vec<u8>, MdocError> {
    let key = expect_map(value, "COSE_Key")?;
    Ok(parse_akp_mldsa_cose_key_for(stwo_mldsa::profile::ML_DSA_44, key)?.to_vec())
}

/// ML-DSA-65 issuer key from the unprotected `issuerKey` COSE_Key: AKP key
/// type (`kty = 7`), `alg = -49`, raw 1952-byte public key in label `-1`.
///
fn mldsa_issuer_pk_from_unprotected(unprotected: &[(Value, Value)]) -> Result<Vec<u8>, MdocError> {
    let key = expect_map(value_field(unprotected, "issuerKey")?, "COSE_Key")?;
    Ok(parse_akp_mldsa_cose_key_for(stwo_mldsa::profile::ML_DSA_65, key)?.to_vec())
}

/// Parse an AKP ML-DSA COSE_Key for a verifier-selected profile.
/// The map must contain `kty = 7`, the profile algorithm, and the exact raw
/// public-key length in label `-1`.
fn parse_akp_mldsa_cose_key_for(
    profile: stwo_mldsa::profile::MlDsaProfile,
    key: &[(Value, Value)],
) -> Result<&[u8], MdocError> {
    let kty = int_field(key, 1, "COSE_Key.kty")?;
    let alg = int_field(key, 3, "COSE_Key.alg")?;
    if kty != i128::from(stwo_mldsa::constants::COSE_KTY_AKP)
        || alg != i128::from(profile.cose_alg())
    {
        return Err(MdocError::InvalidCoseKey(match profile {
            stwo_mldsa::profile::MlDsaProfile::MlDsa44 => "expected ML-DSA-44 AKP key",
            stwo_mldsa::profile::MlDsaProfile::MlDsa65 => "expected ML-DSA-65 AKP key",
        }));
    }
    let pk = bytes_int_field(key, -1, "COSE_Key.pub")?;
    if pk.len() != profile.pk_bytes() {
        return Err(MdocError::InvalidCoseKey(match profile {
            stwo_mldsa::profile::MlDsaProfile::MlDsa44 => "ML-DSA-44 public key length",
            stwo_mldsa::profile::MlDsaProfile::MlDsa65 => "ML-DSA-65 public key length",
        }));
    }
    Ok(pk)
}

/// ML-DSA-65 revocation-authority public key (`pkEncode`, 1,952 bytes).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocRevocationKey(pub Vec<u8>);

impl MdocRevocationKey {
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

/// ML-DSA-65 signature over `LE64(id_lo) ‖ LE64(id_hi) ‖ LE32(epoch)`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocRevocationSignature(pub Vec<u8>);

impl MdocRevocationSignature {
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocRevocationPublicInputs {
    pub revocation_public_key: MdocRevocationKey,
    pub epoch: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct MdocRevocationRangeWitness {
    pub id: u64,
    pub id_lo: u64,
    pub id_hi: u64,
}

pub const TS13_DEMO_ISSUER_MESSAGE_BYTES: usize = 1_894;
pub const TS13_DEMO_MSO_PAYLOAD_BYTES: usize = 1_873;
pub const TS13_DEMO_ITEM_PADDED_BYTES: u16 = 128;
const TS13_DEMO_ATTRIBUTE_SHA_LOG_N_ROWS: u32 = 8;
pub const TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY: usize =
    stwo_mldsa::statement::DEVICE_SIG_STRUCTURE_CAPACITY;

/// Verifier-authoritative inputs for the public-input-unlinkable TS13 demo.
///
/// Credential-selected lengths and the device key are intentionally absent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MdocTs13DemoCircuitPublicInput {
    pub circuit_hash: [u8; 32],
    pub request_context_digest: [u8; 32],
    pub timestamp_epoch_seconds: i64,
    pub verification_timestamp_rfc3339_utc:
        [u8; TS13_DEMO_VERIFICATION_TIMESTAMP_RFC3339_UTC_BYTES],
    pub trusted_issuer_public_key: Vec<u8>,
    pub device_cose_sig_structure: Vec<u8>,
    pub revocation: MdocRevocationPublicInputs,
}

impl MdocTs13DemoCircuitPublicInput {
    fn context_bind(&self) -> Ts13PublicContextBind {
        Ts13PublicContextBind::new(self.request_context_digest, self.circuit_hash)
    }
}

fn utc_date_from_epoch_seconds(timestamp: i64) -> Result<Date, Error> {
    if timestamp < 0 {
        return Err(Error::Verify(
            "TS13 verification timestamp is outside the supported range".to_string(),
        ));
    }
    let days = timestamp / 86_400;
    // Howard Hinnant's civil-from-days transform, with day zero at 1970-01-01.
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let day_of_era = z - era * 146_097;
    let year_of_era =
        (day_of_era - day_of_era / 1_460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
    let mut year = year_of_era + era * 400;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let month_prime = (5 * day_of_year + 2) / 153;
    let day = day_of_year - (153 * month_prime + 2) / 5 + 1;
    let month = month_prime + if month_prime < 10 { 3 } else { -9 };
    year += i64::from(month <= 2);
    if !(2020..=2099).contains(&year) {
        return Err(Error::Verify(
            "TS13 verification timestamp is outside years 2020..=2099".to_string(),
        ));
    }
    Ok(Date {
        year: year as u32,
        month: month as u32,
        day: day as u32,
    })
}

fn date_tuple(date: Date) -> Result<(u16, u8, u8), MdocError> {
    if date.year > 9999 {
        return Err(MdocError::InvalidTdate("verification date"));
    }
    Ok((
        u16::try_from(date.year).map_err(|_| MdocError::InvalidTdate("verification date"))?,
        u8::try_from(date.month).map_err(|_| MdocError::InvalidTdate("verification date"))?,
        u8::try_from(date.day).map_err(|_| MdocError::InvalidTdate("verification date"))?,
    ))
}

/// Public ML-DSA claims for one issuer, device, or revocation role.
///
/// The shared proof contains the STARK.
/// Public fields let negative tests swap role claims.
/// The transcript binds each claim to its role.
#[derive(Clone, Serialize, Deserialize)]
pub struct MdocMlDsaClaims {
    pub group_evals: Vec<QM31>,
    pub claimed_sums: Vec<QM31>,
}

impl MdocMlDsaClaims {
    fn from_prover(prover: &MlDsaStatementProver) -> Self {
        Self {
            group_evals: prover.group_evals().to_vec(),
            claimed_sums: prover.claimed_sums(),
        }
    }

    /// Check the shape before `Claims::from_flat`.
    /// A short vector can cause a panic during claim-tree construction.
    /// This construction occurs outside the verification panic boundary.
    fn has_expected_shape(&self, public_message: bool) -> bool {
        let expected_claimed_sums = if public_message {
            stwo_mldsa::statement::hosted_public_claimed_sums_len()
        } else {
            stwo_mldsa::statement::hosted_claimed_sums_len()
        };
        self.group_evals.len() == stwo_mldsa::statement::n_group_evals()
            && self.claimed_sums.len() == expected_claimed_sums
    }
}

pub(crate) const MDOC_PROOF_SERIALIZED_CLAIM_NAMES: [&str; 19] = [
    "sha_tables_interaction_claim",
    "mldsa",
    "device_mldsa",
    "revocation_mldsa",
    "mldsa_range_table_claimed_sum",
    "keccak_service_claimed_sums",
    "private_issuer_message_interaction_claim",
    "attribute_sha_interaction_claim",
    "mso_sha_interaction_claim",
    "private_mso_bind_interaction_claim",
    "private_item_interaction_claim",
    "value_digests_scan_interaction_claim",
    "private_item_outer_cbor_interaction_claim",
    "private_item_inner_cbor_interaction_claim",
    "ts13_expand_a_claim",
    "ts13_device_key_bind_interaction_claim",
    "ts13_mso_validity_interaction_claim",
    "ts13_revocation_range_interaction_claim",
    "post_interaction_payloads",
];

#[derive(Clone, Serialize, Deserialize)]
pub struct MdocProof {
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
    sha_tables_interaction_claim: ShaTablesInteractionClaim,
    pub mldsa: MdocMlDsaClaims,
    pub device_mldsa: MdocMlDsaClaims,
    pub revocation_mldsa: MdocMlDsaClaims,
    mldsa_range_table_claimed_sum: QM31,
    pub keccak_service_claimed_sums: Vec<QM31>,
    private_issuer_message_interaction_claim: MdocPrivateMessageInteractionClaim,
    attribute_sha_interaction_claim: Sha256InteractionClaim,
    mso_sha_interaction_claim: Sha256InteractionClaim,
    private_mso_bind_interaction_claim: MdocPrivateMsoInteractionClaim,
    private_item_interaction_claim: MdocPrivateItemInteractionClaim,
    value_digests_scan_interaction_claim: MdocValueDigestsInteractionClaim,
    private_item_outer_cbor_interaction_claim: MdocCborStreamInteractionClaim,
    private_item_inner_cbor_interaction_claim: MdocCborStreamInteractionClaim,
    ts13_expand_a_claim: ExpandAClaim,
    ts13_device_key_bind_interaction_claim: MdocPrivateDeviceKeyInteractionClaim,
    ts13_mso_validity_interaction_claim: MdocPrivateMsoValidityInteractionClaim,
    ts13_revocation_range_interaction_claim: MdocRevocationRangeInteractionClaim,
    /// Opaque post-interaction payloads. The Keccak service carries its
    /// round-GKR proof in its module slot.
    pub post_interaction_payloads: Vec<Vec<u8>>,
    /// Prover-side executable geometry for artifact drift tests.
    /// The proof does not contain this value.
    #[serde(skip, default)]
    ts13_demo_circuit_geometry: Option<MdocTs13DemoCircuitGeometry>,
}

impl MdocProof {
    fn serialized_non_stark_field_lengths(&self) -> Vec<(&'static str, usize)> {
        let lengths = [
            bincode_len(&self.sha_tables_interaction_claim),
            bincode_len(&self.mldsa),
            bincode_len(&self.device_mldsa),
            bincode_len(&self.revocation_mldsa),
            bincode_len(&self.mldsa_range_table_claimed_sum),
            bincode_len(&self.keccak_service_claimed_sums),
            bincode_len(&self.private_issuer_message_interaction_claim),
            bincode_len(&self.attribute_sha_interaction_claim),
            bincode_len(&self.mso_sha_interaction_claim),
            bincode_len(&self.private_mso_bind_interaction_claim),
            bincode_len(&self.private_item_interaction_claim),
            bincode_len(&self.value_digests_scan_interaction_claim),
            bincode_len(&self.private_item_outer_cbor_interaction_claim),
            bincode_len(&self.private_item_inner_cbor_interaction_claim),
            bincode_len(&self.ts13_expand_a_claim),
            bincode_len(&self.ts13_device_key_bind_interaction_claim),
            bincode_len(&self.ts13_mso_validity_interaction_claim),
            bincode_len(&self.ts13_revocation_range_interaction_claim),
            bincode_len(&self.post_interaction_payloads),
        ];
        MDOC_PROOF_SERIALIZED_CLAIM_NAMES
            .into_iter()
            .zip(lengths)
            .collect()
    }

    pub fn has_ts13_demo_shape(&self) -> bool {
        use crate::ts13_demo_artifact_constants::{
            TS13_DEMO_FRI_FIRST_HASH_CAP, TS13_DEMO_FRI_FIRST_WITNESS_CAP,
            TS13_DEMO_FRI_INNER_HASH_CAPS, TS13_DEMO_FRI_INNER_WITNESS_CAPS,
            TS13_DEMO_FRI_LAST_LAYER_COEFFICIENT_COUNT, TS13_DEMO_POST_INTERACTION_PAYLOAD_COUNT,
            TS13_DEMO_QUERY_COUNT, TS13_DEMO_SAMPLED_VALUE_LENGTH_HISTOGRAMS,
            TS13_DEMO_TREE_COLUMN_COUNTS, TS13_DEMO_TREE_MERKLE_HASH_CAPS,
        };

        fn length_histogram_matches<T>(columns: &[Vec<T>], expected: &[(usize, usize)]) -> bool {
            expected.iter().map(|(_, count)| count).sum::<usize>() == columns.len()
                && expected.iter().all(|&(length, expected_count)| {
                    columns
                        .iter()
                        .filter(|column| column.len() == length)
                        .count()
                        == expected_count
                })
        }

        let stark = &self.stark_proof.0;
        stark.config == mdoc_ts13_pcs_config()
            && stark.commitments.len() == TS13_DEMO_TREE_COLUMN_COUNTS.len()
            && stark.sampled_values.len() == TS13_DEMO_TREE_COLUMN_COUNTS.len()
            && stark
                .sampled_values
                .iter()
                .zip(TS13_DEMO_SAMPLED_VALUE_LENGTH_HISTOGRAMS)
                .all(|(columns, histogram)| length_histogram_matches(columns, histogram))
            && stark.decommitments.len() == TS13_DEMO_TREE_COLUMN_COUNTS.len()
            && stark
                .decommitments
                .iter()
                .zip(TS13_DEMO_TREE_MERKLE_HASH_CAPS)
                .all(|(decommitment, cap)| decommitment.hash_witness.len() <= cap)
            && stark.queried_values.len() == TS13_DEMO_TREE_COLUMN_COUNTS.len()
            && stark
                .queried_values
                .iter()
                .zip(TS13_DEMO_TREE_COLUMN_COUNTS)
                .all(|(columns, count)| {
                    columns.len() == count
                        && columns
                            .iter()
                            .all(|values| values.len() == TS13_DEMO_QUERY_COUNT)
                })
            && stark.fri_proof.first_layer.fri_witness.len() <= TS13_DEMO_FRI_FIRST_WITNESS_CAP
            && stark.fri_proof.first_layer.decommitment.hash_witness.len()
                <= TS13_DEMO_FRI_FIRST_HASH_CAP
            && stark.fri_proof.inner_layers.len() == TS13_DEMO_FRI_INNER_WITNESS_CAPS.len()
            && stark
                .fri_proof
                .inner_layers
                .iter()
                .zip(TS13_DEMO_FRI_INNER_WITNESS_CAPS)
                .zip(TS13_DEMO_FRI_INNER_HASH_CAPS)
                .all(|((layer, witness_cap), hash_cap)| {
                    layer.fri_witness.len() <= witness_cap
                        && layer.decommitment.hash_witness.len() <= hash_cap
                })
            && stark.fri_proof.last_layer_poly.len() == TS13_DEMO_FRI_LAST_LAYER_COEFFICIENT_COUNT
            && self.post_interaction_payloads.len() == TS13_DEMO_POST_INTERACTION_PAYLOAD_COUNT
            && self
                .post_interaction_payloads
                .iter()
                .enumerate()
                .all(|(index, payload)| {
                    if index == 2 {
                        air_core::gkr::is_ts13_demo_gkr_batch_proof_wire(payload)
                    } else {
                        payload.is_empty()
                    }
                })
            && self.sha_tables_interaction_claim.pairs.len() == 3
            && self.attribute_sha_interaction_claim.range.is_empty()
            && self.mso_sha_interaction_claim.range.is_empty()
            && self.mldsa.has_expected_shape(false)
            && self.device_mldsa.group_evals.len()
                == stwo_mldsa::statement::n_private_key_group_evals()
            && self.device_mldsa.claimed_sums.len()
                == stwo_mldsa::statement::hosted_private_key_claimed_sums_len()
            && self.revocation_mldsa.has_expected_shape(false)
            && self.keccak_service_claimed_sums.len()
                == stwo_mldsa::stwo_keccak::service::service_claimed_sums_len()
    }

    #[doc(hidden)]
    pub fn ts13_demo_circuit_geometry(&self) -> Option<&MdocTs13DemoCircuitGeometry> {
        self.ts13_demo_circuit_geometry.as_ref()
    }
}

/// Values that identify the fixed PCS and its preprocessed tree cache entry.
#[derive(Clone, Debug, Serialize)]
struct MdocTree0CacheKeyMaterial {
    version: u8,
    pcs_log_last_layer_degree_bound: u32,
    pcs_log_blowup_factor: u32,
    pcs_queries: usize,
    pcs_fold_step: u32,
    pcs_pow_bits: u32,
    pcs_lifting_log_size: Option<u32>,
    attribute_sha_log_n_rows: u32,
    device_mldsa_message_bytes: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct MdocTree0CacheKey {
    digest: [u8; 32],
    /// Keep the full cache-key material so that a digest collision is a miss.
    material: Vec<u8>,
}

type MdocTree0Root = air_core::CommitmentRoot;
type MdocTree0RootCache = VecDeque<(MdocTree0CacheKey, MdocTree0Root)>;

static MDOC_TREE0_ROOT_CACHE: OnceLock<Mutex<MdocTree0RootCache>> = OnceLock::new();

fn serialize_mdoc_tree0_cache_key_material(
    material: &MdocTree0CacheKeyMaterial,
) -> Result<Vec<u8>, Error> {
    bincode::serialize(material)
        .map_err(|error| Error::Verify(format!("mdoc tree-0 cache key: {error}")))
}

fn mdoc_tree0_cache_key(
    device_message_len: usize,
    expected_pcs_config: PcsConfig,
) -> Result<MdocTree0CacheKey, Error> {
    let material = MdocTree0CacheKeyMaterial {
        version: 2,
        pcs_log_last_layer_degree_bound: expected_pcs_config.fri_config.log_last_layer_degree_bound,
        pcs_log_blowup_factor: expected_pcs_config.fri_config.log_blowup_factor,
        pcs_queries: expected_pcs_config.fri_config.n_queries,
        pcs_fold_step: expected_pcs_config.fri_config.fold_step,
        pcs_pow_bits: expected_pcs_config.pow_bits,
        pcs_lifting_log_size: expected_pcs_config.lifting_log_size,
        attribute_sha_log_n_rows: TS13_DEMO_ATTRIBUTE_SHA_LOG_N_ROWS,
        device_mldsa_message_bytes: device_message_len,
    };
    let material = serialize_mdoc_tree0_cache_key_material(&material)?;
    Ok(MdocTree0CacheKey {
        digest: Sha256::digest(&material).into(),
        material,
    })
}

fn mdoc_tree0_cached_root(key: &MdocTree0CacheKey) -> Result<Option<MdocTree0Root>, Error> {
    let cache = MDOC_TREE0_ROOT_CACHE.get_or_init(|| Mutex::new(VecDeque::new()));
    let mut entries = cache
        .lock()
        .map_err(|_| Error::Verify("mdoc tree-0 cache lock poisoned".to_string()))?;
    let Some(index) = entries.iter().position(|(candidate, _)| {
        candidate.digest == key.digest && candidate.material == key.material
    }) else {
        return Ok(None);
    };
    let entry = entries
        .remove(index)
        .expect("cache index came from the same deque");
    let root = entry.1;
    entries.push_back(entry);
    Ok(Some(root))
}

fn mdoc_tree0_cache_insert(key: MdocTree0CacheKey, root: MdocTree0Root) -> Result<(), Error> {
    let cache = MDOC_TREE0_ROOT_CACHE.get_or_init(|| Mutex::new(VecDeque::new()));
    let mut entries = cache
        .lock()
        .map_err(|_| Error::Verify("mdoc tree-0 cache lock poisoned".to_string()))?;
    if let Some(index) = entries.iter().position(|(candidate, _)| {
        candidate.digest == key.digest && candidate.material == key.material
    }) {
        entries.remove(index);
    }
    if entries.len() == MDOC_TREE0_ROOT_CACHE_CAPACITY {
        entries.pop_front();
    }
    entries.push_back((key, root));
    Ok(())
}

/// Executable serialization/claim geometry extracted from a real TS13 demo
/// proof. The circuit-artifact drift test compares this view with the
/// generated manifest; it is not part of the verifier's public statement.
#[doc(hidden)]
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocTs13DemoProofShape {
    pub proof_bytes: usize,
    pub stark_proof_bytes: usize,
    pub outer_claims_and_framing_bytes: usize,
    pub serialized_non_stark_field_lengths: Vec<usize>,
    pub fri_log_last_layer_degree_bound: u32,
    pub fri_log_blowup_factor: u32,
    pub fri_query_count: usize,
    pub fri_fold_step: u32,
    pub pow_bits: u32,
    pub lifting_log_size: Option<u32>,
    pub commitment_count: usize,
    pub tree_zero_root: Option<[u8; 32]>,
    pub sampled_values: Vec<Vec<usize>>,
    pub decommitment_hash_counts: Vec<usize>,
    pub queried_values: Vec<Vec<usize>>,
    pub fri_first_layer_witness_count: usize,
    pub fri_first_layer_hash_count: usize,
    pub fri_inner_layers: Vec<MdocFriLayerShape>,
    pub fri_last_layer_coefficient_count: usize,
    pub post_interaction_payload_bytes: Vec<usize>,
    pub sha_table_pair_claim_count: usize,
    pub attribute_sha_range_claim_count: usize,
    pub mso_sha_range_claim_count: Option<usize>,
    pub issuer_mldsa_group_eval_count: Option<usize>,
    pub issuer_mldsa_claimed_sum_count: Option<usize>,
    pub device_mldsa_group_eval_count: Option<usize>,
    pub device_mldsa_claimed_sum_count: Option<usize>,
    pub revocation_mldsa_group_eval_count: Option<usize>,
    pub revocation_mldsa_claimed_sum_count: Option<usize>,
    pub keccak_service_claimed_sum_count: Option<usize>,
    pub private_item_claim_count: usize,
    pub cbor_parser_claim_count: usize,
}

#[doc(hidden)]
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocFriLayerShape {
    pub witness_count: usize,
    pub hash_count: usize,
}

/// Exact prover-constructed AIR/component geometry. This metadata is retained
/// only in memory for circuit-artifact generation and drift tests.
#[doc(hidden)]
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocTs13DemoCircuitGeometry {
    pub committed_preprocessed_ids: Vec<String>,
    pub committed_preprocessed_log_sizes: Vec<u32>,
    pub air_instances: Vec<MdocAirInstanceGeometry>,
}

#[doc(hidden)]
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocAirInstanceGeometry {
    pub preprocessed_log_sizes: Vec<u32>,
    pub trace_log_sizes: Vec<u32>,
    pub interaction_log_sizes: Vec<u32>,
    pub post_interaction_log_sizes: Vec<u32>,
    pub claimed_sum_count: usize,
    pub max_log_size: u32,
    pub max_constraint_log_degree_bound: u32,
    pub components: Vec<MdocComponentGeometry>,
}

#[doc(hidden)]
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocComponentGeometry {
    pub trace_rows: u32,
    pub active_rows: u32,
    pub constraint_count: usize,
    pub max_constraint_log_degree_bound: u32,
    pub trace_log_degree_bounds: Vec<Vec<u32>>,
}

fn capture_ts13_demo_circuit_geometry(
    modules: &[&mut dyn AirProver],
) -> MdocTs13DemoCircuitGeometry {
    const TS13_DEMO_DEVICE_KEY_BIND_AIR_ORDINAL: usize = 15;
    const TS13_DEMO_DEVICE_KEY_BIND_COMPONENT_ORDINAL: usize = 0;

    let mut seen_preprocessed_ids = HashSet::new();
    let mut committed_preprocessed_ids = Vec::new();
    let mut committed_preprocessed_log_sizes = Vec::new();
    for module in modules {
        let ids = module.preprocessed_column_ids();
        let log_sizes = module.layout().preprocessed;
        assert_eq!(
            ids.len(),
            log_sizes.len(),
            "preprocessed ids and layout differ during TS13 artifact capture"
        );
        for (id, log_size) in ids.into_iter().zip(log_sizes) {
            let id_name = format!("{id:?}");
            if seen_preprocessed_ids.insert(id) {
                committed_preprocessed_ids.push(id_name);
                committed_preprocessed_log_sizes.push(log_size);
            }
        }
    }

    MdocTs13DemoCircuitGeometry {
        committed_preprocessed_ids,
        committed_preprocessed_log_sizes,
        air_instances: modules
            .iter()
            .enumerate()
            .map(|(air_ordinal, module)| {
                let layout = module.layout();
                MdocAirInstanceGeometry {
                    preprocessed_log_sizes: layout.preprocessed,
                    trace_log_sizes: layout.trace,
                    interaction_log_sizes: layout.interaction,
                    post_interaction_log_sizes: module.post_interaction_log_sizes(),
                    claimed_sum_count: module.claimed_sums().len(),
                    max_log_size: module.max_log_size(),
                    max_constraint_log_degree_bound: module.max_constraint_log_degree_bound(),
                    components: module
                        .components()
                        .into_iter()
                        .enumerate()
                        .map(|(component_ordinal, component)| {
                            let trace_log_degree_bounds = component
                                .trace_log_degree_bounds()
                                .iter()
                                .cloned()
                                .collect::<Vec<_>>();
                            let trace_rows = trace_log_degree_bounds
                                .iter()
                                .flatten()
                                .copied()
                                .max()
                                .and_then(|log_size| 1_u32.checked_shl(log_size))
                                .expect("TS13 component has a supported non-empty trace layout");
                            MdocComponentGeometry {
                                trace_rows,
                                active_rows: if air_ordinal == TS13_DEMO_DEVICE_KEY_BIND_AIR_ORDINAL
                                    && component_ordinal
                                        == TS13_DEMO_DEVICE_KEY_BIND_COMPONENT_ORDINAL
                                {
                                    MDOC_PRIVATE_DEVICE_KEY_ACTIVE_ROWS as u32
                                } else {
                                    trace_rows
                                },
                                constraint_count: component.n_constraints(),
                                max_constraint_log_degree_bound: component
                                    .max_constraint_log_degree_bound(),
                                trace_log_degree_bounds,
                            }
                        })
                        .collect(),
                }
            })
            .collect(),
    }
}

impl MdocProof {
    /// Return the public proof shape for artifact audits.
    #[doc(hidden)]
    pub fn ts13_demo_proof_shape(&self) -> MdocTs13DemoProofShape {
        let stark = &self.stark_proof.0;
        let mldsa_shape =
            |claims: &MdocMlDsaClaims| (claims.group_evals.len(), claims.claimed_sums.len());
        let issuer = mldsa_shape(&self.mldsa);
        let device = mldsa_shape(&self.device_mldsa);
        let revocation = mldsa_shape(&self.revocation_mldsa);
        let proof_bytes = bincode_len(self);
        let stark_proof_bytes = bincode_len(&self.stark_proof);
        let serialized_non_stark_fields = self.serialized_non_stark_field_lengths();
        let non_stark_field_bytes = serialized_non_stark_fields
            .iter()
            .map(|(_, length)| *length)
            .sum::<usize>();
        assert_eq!(
            proof_bytes,
            stark_proof_bytes + non_stark_field_bytes,
            "serialized proof length must equal the sum of its field lengths"
        );
        let post_interaction_payload_wire_bytes = 8
            + self.post_interaction_payloads.len() * 8
            + self
                .post_interaction_payloads
                .iter()
                .map(Vec::len)
                .sum::<usize>();
        MdocTs13DemoProofShape {
            proof_bytes,
            stark_proof_bytes,
            outer_claims_and_framing_bytes: proof_bytes
                .checked_sub(stark_proof_bytes + post_interaction_payload_wire_bytes)
                .expect("post payloads are contained in the serialized proof"),
            serialized_non_stark_field_lengths: serialized_non_stark_fields
                .into_iter()
                .map(|(_, length)| length)
                .collect(),
            fri_log_last_layer_degree_bound: stark.config.fri_config.log_last_layer_degree_bound,
            fri_log_blowup_factor: stark.config.fri_config.log_blowup_factor,
            fri_query_count: stark.config.fri_config.n_queries,
            fri_fold_step: stark.config.fri_config.fold_step,
            pow_bits: stark.config.pow_bits,
            lifting_log_size: stark.config.lifting_log_size,
            commitment_count: stark.commitments.len(),
            tree_zero_root: stark.commitments.first().map(|root| root.0),
            sampled_values: stark
                .sampled_values
                .iter()
                .map(|columns| columns.iter().map(Vec::len).collect())
                .collect(),
            decommitment_hash_counts: stark
                .decommitments
                .iter()
                .map(|decommitment| decommitment.hash_witness.len())
                .collect(),
            queried_values: stark
                .queried_values
                .iter()
                .map(|columns| columns.iter().map(Vec::len).collect())
                .collect(),
            fri_first_layer_witness_count: stark.fri_proof.first_layer.fri_witness.len(),
            fri_first_layer_hash_count: stark.fri_proof.first_layer.decommitment.hash_witness.len(),
            fri_inner_layers: stark
                .fri_proof
                .inner_layers
                .iter()
                .map(|layer| MdocFriLayerShape {
                    witness_count: layer.fri_witness.len(),
                    hash_count: layer.decommitment.hash_witness.len(),
                })
                .collect(),
            fri_last_layer_coefficient_count: stark.fri_proof.last_layer_poly.len(),
            post_interaction_payload_bytes: self
                .post_interaction_payloads
                .iter()
                .map(Vec::len)
                .collect(),
            sha_table_pair_claim_count: self.sha_tables_interaction_claim.pairs.len(),
            attribute_sha_range_claim_count: self.attribute_sha_interaction_claim.range.len(),
            mso_sha_range_claim_count: Some(self.mso_sha_interaction_claim.range.len()),
            issuer_mldsa_group_eval_count: Some(issuer.0),
            issuer_mldsa_claimed_sum_count: Some(issuer.1),
            device_mldsa_group_eval_count: Some(device.0),
            device_mldsa_claimed_sum_count: Some(device.1),
            revocation_mldsa_group_eval_count: Some(revocation.0),
            revocation_mldsa_claimed_sum_count: Some(revocation.1),
            keccak_service_claimed_sum_count: Some(self.keccak_service_claimed_sums.len()),
            private_item_claim_count: 1,
            cbor_parser_claim_count: 2,
        }
    }
}

fn bincode_len<T: Serialize>(value: &T) -> usize {
    bincode::serialize(value)
        .expect("mdoc proof byte breakdown value serializes")
        .len()
}

pub(crate) fn checked_sha256_padded_len(message_len: usize) -> Option<usize> {
    message_len
        .checked_add(9)?
        .checked_add(stwo_sha256::constants::BLOCK_BYTES - 1)
        .map(|rounded| {
            (rounded / stwo_sha256::constants::BLOCK_BYTES) * stwo_sha256::constants::BLOCK_BYTES
        })
}

fn private_mso_bind_spec(
    verification_date: Date,
    mso_sha_padded_len: usize,
) -> MdocPrivateMsoBindSpec {
    MdocPrivateMsoBindSpec {
        issuer_message_len: TS13_DEMO_ISSUER_MESSAGE_BYTES,
        mso_len: TS13_DEMO_MSO_PAYLOAD_BYTES,
        doc_type: PID_DOCTYPE.to_string(),
        policy_date: verification_date,
        sha_stream: MdocPrivateMsoShaStreamSpec {
            field_id: MDOC_MSO_SHA_STREAM_FIELD_ID,
            padded_len: mso_sha_padded_len,
        },
    }
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
        channel.mix_u64(2);
        for &byte in self.inputs.revocation_public_key.as_bytes() {
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

const MDOC_REVOCATION_RANGE_LOG_SIZE: u32 = LOG_N_LANES;
const REVOCATION_U64_BYTES: usize = 8;
const REVOCATION_RANGE_BYTE_COLS: usize = 5 * REVOCATION_U64_BYTES;
const REVOCATION_RANGE_CARRY_COLS: usize = 2 * REVOCATION_U64_BYTES;
const REVOCATION_RANGE_DIGEST_TAIL_COLS: usize = 32 - REVOCATION_U64_BYTES;

fn revocation_range_bit_byte_indices() -> std::ops::Range<usize> {
    // The range component provides `id_lo || id_hi || epoch` to the hosted
    // revocation signature leg. Provider-side bytes must remain constrained
    // independently of that external consumer. The private SHA digest relation
    // constrains the leading `id` bytes.
    REVOCATION_U64_BYTES..REVOCATION_RANGE_BYTE_COLS
}

fn revocation_range_bit_cols() -> usize {
    revocation_range_bit_byte_indices().len() * 8
}

type MdocRevocationRangeColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type MdocRevocationRangeComponent = FrameworkComponent<MdocRevocationRangeEval>;

fn revocation_range_trace_cols() -> usize {
    REVOCATION_RANGE_BYTE_COLS
        + revocation_range_bit_cols()
        + REVOCATION_RANGE_CARRY_COLS
        + REVOCATION_RANGE_DIGEST_TAIL_COLS
}

#[cfg(test)]
thread_local! {
    static REVOCATION_ENDPOINT_ATTACK: core::cell::Cell<Option<RevocationEndpointAttack>> =
        const { core::cell::Cell::new(None) };
}

#[cfg(test)]
struct RevocationRangeAttackGuard;

#[cfg(test)]
#[derive(Clone, Copy)]
enum RevocationEndpointAttack {
    Lower,
    Upper,
}

#[cfg(test)]
impl Drop for RevocationRangeAttackGuard {
    fn drop(&mut self) {
        REVOCATION_ENDPOINT_ATTACK.with(|attack| attack.set(None));
    }
}

#[cfg(test)]
fn install_revocation_endpoint_attack(
    attack: RevocationEndpointAttack,
) -> RevocationRangeAttackGuard {
    REVOCATION_ENDPOINT_ATTACK.with(|active| active.set(Some(attack)));
    RevocationRangeAttackGuard
}

#[cfg(test)]
fn prover_revocation_range_strictness() -> (bool, bool) {
    REVOCATION_ENDPOINT_ATTACK.with(|attack| match attack.get() {
        Some(RevocationEndpointAttack::Lower) => (false, true),
        Some(RevocationEndpointAttack::Upper) => (true, false),
        None => (true, true),
    })
}

#[cfg(not(test))]
fn prover_revocation_range_strictness() -> (bool, bool) {
    (true, true)
}

struct MdocRevocationRangeBind {
    witness: Option<MdocRevocationRangeWitness>,
    mso_digest: Option<[u8; 32]>,
    epoch: u32,
    strict_comparisons: (bool, bool),
    digest_handle: SharedDigestRelation,
    message_field_handle: SharedFieldRelation,
    blinder_relation: Option<ClaimedSumBlinderRelation>,
    interaction_claim: Option<MdocRevocationRangeInteractionClaim>,
    component: Option<MdocRevocationRangeComponent>,
    blinder_component: Option<FrameworkComponent<ClaimedSumBlinderEval>>,
}

#[derive(Clone)]
struct MdocRevocationRangeEval {
    mso_digest_relation: Box<DigestBytesRelation>,
    message_field_relation: FieldBytesRelation,
    epoch: u32,
    strict_comparisons: (bool, bool),
    blinder_relation: ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct MdocRevocationRangeInteractionClaim {
    claimed_sum: QM31,
    /// Claimed-sum blinder pair. See `claimed_sum_blinder`.
    blinder_v: QM31,
    blinder_m: QM31,
    blinder_claimed_sum: QM31,
}

impl MdocRevocationRangeBind {
    fn prover(
        witness: MdocRevocationRangeWitness,
        mso_digest: [u8; 32],
        digest_handle: SharedDigestRelation,
        epoch: u32,
        message_field_handle: SharedFieldRelation,
    ) -> Self {
        Self {
            witness: Some(witness),
            mso_digest: Some(mso_digest),
            epoch,
            strict_comparisons: prover_revocation_range_strictness(),
            digest_handle,
            message_field_handle,
            blinder_relation: None,
            interaction_claim: None,
            component: None,
            blinder_component: None,
        }
    }

    fn verifier(
        digest_handle: SharedDigestRelation,
        epoch: u32,
        message_field_handle: SharedFieldRelation,
        interaction_claim: MdocRevocationRangeInteractionClaim,
    ) -> Self {
        Self {
            witness: None,
            mso_digest: None,
            epoch,
            strict_comparisons: (true, true),
            digest_handle,
            message_field_handle,
            blinder_relation: None,
            interaction_claim: Some(interaction_claim),
            component: None,
            blinder_component: None,
        }
    }

    fn mso_digest_relation(&self) -> DigestBytesRelation {
        self.digest_handle.get()
    }

    fn message_relation(&self) -> FieldBytesRelation {
        self.message_field_handle.get()
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

fn comparison_carries(lhs: [u8; 8], rhs: [u8; 8], slack: [u8; 8], strict: bool) -> [u8; 8] {
    let mut carry = 0u16;
    std::array::from_fn(|idx| {
        let add_one = u16::from(strict && idx == 0);
        let sum = u16::from(lhs[idx]) + u16::from(slack[idx]) + add_one + carry;
        carry = sum >> 8;
        debug_assert_eq!((sum & 0xff) as u8, rhs[idx]);
        carry as u8
    })
}

fn revocation_range_base_trace(
    witness: &MdocRevocationRangeWitness,
    mso_digest: &[u8; 32],
    strict_comparisons: (bool, bool),
) -> Vec<MdocRevocationRangeColumnEval> {
    let id = witness.id.to_le_bytes();
    let id_lo = witness.id_lo.to_le_bytes();
    let id_hi = witness.id_hi.to_le_bytes();
    let lower_slack = witness
        .id
        .wrapping_sub(witness.id_lo)
        .wrapping_sub(u64::from(strict_comparisons.0))
        .to_le_bytes();
    let upper_slack = witness
        .id_hi
        .wrapping_sub(witness.id)
        .wrapping_sub(u64::from(strict_comparisons.1))
        .to_le_bytes();
    let lower_carries = comparison_carries(id_lo, id, lower_slack, strict_comparisons.0);
    let upper_carries = comparison_carries(id, id_hi, upper_slack, strict_comparisons.1);

    let mut first_row = Vec::with_capacity(revocation_range_trace_cols());
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
    for byte_idx in revocation_range_bit_byte_indices() {
        first_row.extend(
            byte_bits(range_bytes[byte_idx] as u8)
                .into_iter()
                .map(u32::from),
        );
    }
    first_row.extend(lower_carries.into_iter().map(u32::from));
    first_row.extend(upper_carries.into_iter().map(u32::from));
    first_row.extend(
        mso_digest[REVOCATION_U64_BYTES..]
            .iter()
            .map(|&byte| u32::from(byte)),
    );
    debug_assert_eq!(first_row.len(), revocation_range_trace_cols());

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
    strict_comparisons: (bool, bool),
    mso_digest_relation: &DigestBytesRelation,
    epoch: u32,
    message_relation: &FieldBytesRelation,
    blinder_relation: &ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
) -> (Vec<MdocRevocationRangeColumnEval>, QM31) {
    let base = revocation_range_base_trace(witness, mso_digest, strict_comparisons);
    let active = revocation_range_active_column();
    let n_vec_rows = 1usize << (MDOC_REVOCATION_RANGE_LOG_SIZE - LOG_N_LANES);
    let digest_tail_offset =
        REVOCATION_RANGE_BYTE_COLS + revocation_range_bit_cols() + REVOCATION_RANGE_CARRY_COLS;
    // Emit `+m/(z−combine(v))` last.
    // It pairs with the final revocation-message tuple.
    let blinder_num = PackedQM31::broadcast(blinder_m);
    let blinder_den = crate::claimed_sum_blinder::blinder_denominator(blinder_relation, blinder_v);
    let mut logup = LogupTraceGenerator::new(MDOC_REVOCATION_RANGE_LOG_SIZE);
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
                    return (numerator, mso_digest_relation.combine(&values));
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
                    PackedM31::broadcast(M31::from_u32_unchecked(HOSTED_MSG_FIELD_ID)),
                    PackedM31::broadcast(M31::from_u32_unchecked(byte_idx as u32)),
                    value,
                ]);
                (-numerator, denominator)
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

        let values: Vec<E::F> = (0..revocation_range_trace_cols())
            .map(|_| eval.next_trace_mask())
            .collect();
        for value in &values {
            eval.add_constraint((one.clone() - active.clone()) * value.clone());
        }

        // Bit-pin exactly the externally-unpinned bytes (see
        // `revocation_range_bit_byte_indices` for the per-byte exemptions).
        for (slot, byte_idx) in revocation_range_bit_byte_indices().enumerate() {
            let byte = values[byte_idx].clone();
            let bits = &values[REVOCATION_RANGE_BYTE_COLS + slot * 8
                ..REVOCATION_RANGE_BYTE_COLS + (slot + 1) * 8];
            for bit in bits {
                eval.add_constraint(bit.clone() * (bit.clone() - one.clone()));
            }
            eval.add_constraint(active.clone() * (byte - byte_from_bits::<E>(bits)));
        }

        let lower_carries_offset = REVOCATION_RANGE_BYTE_COLS + revocation_range_bit_cols();
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
            let lower_add_one =
                m31_const::<E>(u32::from(self.strict_comparisons.0 && byte_idx == 0));
            let upper_add_one =
                m31_const::<E>(u32::from(self.strict_comparisons.1 && byte_idx == 0));
            eval.add_constraint(
                active.clone()
                    * (id_lo + lower_slack + lower_add_one + lower_carry_in
                        - id.clone()
                        - m31_const::<E>(256) * lower_carry_out),
            );
            eval.add_constraint(
                active.clone()
                    * (id + upper_slack + upper_add_one + upper_carry_in
                        - id_hi
                        - m31_const::<E>(256) * upper_carry_out),
            );
        }
        eval.add_constraint(active.clone() * values[lower_carries_offset + 7].clone());
        eval.add_constraint(active.clone() * values[upper_carries_offset + 7].clone());

        let digest_tail_offset = upper_carries_offset + REVOCATION_U64_BYTES;
        let mut digest_values = Vec::with_capacity(32);
        digest_values.extend(values.iter().take(REVOCATION_U64_BYTES).cloned());
        for byte_idx in 0..REVOCATION_RANGE_DIGEST_TAIL_COLS {
            digest_values.push(values[digest_tail_offset + byte_idx].clone());
        }
        eval.add_to_relation(RelationEntry::new(
            self.mso_digest_relation.as_ref(),
            E::EF::from(active.clone()),
            &digest_values,
        ));
        let field_id = m31_const::<E>(HOSTED_MSG_FIELD_ID);
        for byte_idx in 0..TS13_REVOCATION_MESSAGE_LEN {
            let value = match byte_idx {
                0..=7 => values[REVOCATION_U64_BYTES + byte_idx].clone(),
                8..=15 => values[2 * REVOCATION_U64_BYTES + byte_idx - 8].clone(),
                _ => m31_const::<E>(u32::from(self.epoch.to_le_bytes()[byte_idx - 16])),
            };
            eval.add_to_relation(RelationEntry::new(
                &self.message_field_relation,
                -E::EF::from(active.clone()),
                &[field_id.clone(), m31_const::<E>(byte_idx as u32), value],
            ));
        }
        // Emit the ungated `+m/(z−combine(v))` entry last to
        // match the generator's pairing of the lone message site.
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

impl Air for MdocRevocationRangeBind {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(0x5453_3133_524e_4701);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        // This component is the revocation-message field-byte provider unless
        // an earlier module has populated the shared handle.
        if !self.message_field_handle.is_set() {
            self.message_field_handle
                .set(FieldBytesRelation::draw(channel));
        }
        self.blinder_relation = Some(ClaimedSumBlinderRelation::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        // The digest, 20 message tuples, and blinder are paired in the main
        // component; the blinder counterpart contributes one more column.
        let interaction_cols =
            ((2 + TS13_REVOCATION_MESSAGE_LEN).div_ceil(2) + 1) * SECURE_EXTENSION_DEGREE;
        TreeLayout {
            preprocessed: vec![MDOC_REVOCATION_RANGE_LOG_SIZE],
            trace: vec![MDOC_REVOCATION_RANGE_LOG_SIZE; revocation_range_trace_cols()],
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

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(vec![revocation_range_active_column()])
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
                mso_digest_relation: Box::new(self.mso_digest_relation()),
                message_field_relation: self.message_relation(),
                epoch: self.epoch,
                strict_comparisons: self.strict_comparisons,
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
            self.strict_comparisons,
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
            self.strict_comparisons,
            &self.mso_digest_relation(),
            self.epoch,
            &self.message_relation(),
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

fn prepare_mldsa_role(
    profile: stwo_mldsa::profile::MlDsaProfile,
    mut input: MlDsaVerifyInput,
    witness_error_context: &'static str,
) -> Result<(stwo_mldsa::witness::MlDsaWitness, MlDsaVerifyInput), Error> {
    let native_tr = stwo_mldsa::statement::native_tr(profile, &input);
    debug_assert_eq!(
        input.tr, native_tr,
        "{witness_error_context} tr must already match SHAKE256(pk)"
    );
    input.tr = native_tr;
    let witness = stwo_mldsa::witness::generate_witness(profile, &input)
        .map_err(|error| Error::Prove(format!("{witness_error_context}: {error:?}")))?;
    stwo_mldsa::sampleinball::validate_stream(&witness)
        .map_err(|error| Error::Prove(format!("mldsa SIB resource cap: {error}")))?;
    Ok((witness, input))
}

pub(crate) fn prove_mdoc_ts13_demo_circuit(
    extracted: &ExtractedPidMdoc,
    public: &MdocTs13DemoCircuitPublicInput,
    revocation_range: MdocRevocationRangeWitness,
    revocation_signature: MdocRevocationSignature,
) -> Result<MdocProof, Error> {
    let witness_start = std::time::Instant::now();
    let config = mdoc_ts13_pcs_config();
    let verification_date = validate_public_input_shape(public, "prove")?;
    validate_extracted_profile(extracted, public, &verification_date)?;
    // Issuer, device, and revocation messages are absorbed directly by hosted
    // ML-DSA modules. SHA-256 remains only for ISO mdoc attribute digests.
    let revocation_message = crate::ts13::ts13_revocation_message(
        revocation_range.id_lo,
        revocation_range.id_hi,
        public.revocation.epoch,
    );
    let attribute_sha_witness = compute_sha256_witness(&extracted.attribute.item);
    let mso_sha_witness = compute_sha256_witness(extracted.mso.as_slice());
    let mso_sha_padded_len = mso_sha_witness.padding.padded.len();
    // The attribute SHA uses the fixed public log. Revocation is not a SHA
    // instance. Its range AIR provides the signed message.
    let attribute_digest = SharedDigestRelation::new();
    let mso_digest = SharedDigestRelation::new();
    let mso_stream_field = SharedFieldRelation::new();
    let mso_start_handle = SharedMdocMsoStartRelation::new();
    let device_pk_start_handle = SharedMdocDevicePkStartRelation::new();
    let validity_handle = SharedMdocMsoValidityBytesRelation::new();
    let expand_a_bindings = ExpandABindings::new();
    let t1_handle = SharedT1CellRelation::new();
    // The proof-wide Keccak-service relation handle is drawn once by the
    // service module, consumed by every hosted ML-DSA instance.
    let mldsa_keccak_handle = SharedKeccakRelations::new();
    let mldsa_range_handle = SharedRangeRelation::new();
    let issuer_message_field = SharedFieldRelation::new();
    let revocation_message_field = SharedFieldRelation::new();
    let attribute_field = SharedFieldRelation::new();
    let sha_table_relations = SharedShaTableRelations::new();
    let attribute_exposure = attribute_exposure();

    let sha_table_multiplicities =
        ShaTableMultiplicities::from_consumers(&[&attribute_sha_witness, &mso_sha_witness]);
    let mut sha_tables =
        ShaTablesProver::new(sha_table_multiplicities, sha_table_relations.clone());

    // Witness preparation is pure and Send. Keep the non-Send shared relation
    // handles and MlDsaProver construction on this thread, in fixed role order.
    let issuer_input = extracted.issuer_auth_input.as_ref().clone();
    let device_input = extracted.device_auth_input.as_ref().clone();
    let issuer_message = issuer_input.message.clone();
    let private_mso_spec = private_mso_bind_spec(verification_date, mso_sha_padded_len);
    let private_mso_witness = MdocPrivateMsoBindWitness::from_canonical_issuer_message(
        &private_mso_spec,
        issuer_message.clone(),
        &extracted.mso,
    )
    .map_err(|error| Error::Prove(format!("private MSO binder witness: {error}")))?;
    let private_mso_start = private_mso_witness
        .mso_start(extracted.mso.len())
        .map_err(|error| Error::Prove(format!("private MSO start: {error}")))?;
    let private_device_pk_start = private_mso_witness
        .device_pk_start(&private_mso_spec)
        .map_err(|error| Error::Prove(format!("private device-key start: {error}")))?;
    let private_validity_witness = private_mso_witness
        .validity_witness(&private_mso_spec)
        .map_err(|error| Error::Prove(format!("private MSO validity: {error}")))?;
    let (mut private_mso_bind, private_mso_census) = MdocPrivateMsoBind::prover(
        private_mso_spec,
        private_mso_witness,
        issuer_message_field.clone(),
        mso_stream_field.clone(),
        mso_start_handle.clone(),
        device_pk_start_handle.clone(),
        validity_handle.clone(),
    )
    .map_err(|error| Error::Prove(format!("private MSO binder: {error}")))?;
    let mut ts13_public_context = public.context_bind();
    let expand_a_witness = stwo_mldsa::expand_a::derive_expand_a_witness(
        stwo_mldsa::profile::ML_DSA_44,
        device_input.rho,
    )
    .map_err(|error| Error::Prove(format!("TS13 private ExpandA: {error}")))?;
    let mut ts13_expand_a = ExpandAProver::new(
        stwo_mldsa::profile::ML_DSA_44,
        expand_a_witness,
        MDOC_DEVICE_EXPAND_A_NAMESPACE,
        MDOC_DEVICE_EXPAND_A_STREAM_BASE,
        mldsa_range_handle.clone(),
        mldsa_keccak_handle.clone(),
        expand_a_bindings.clone(),
    )
    .map_err(|error| Error::Prove(format!("TS13 private ExpandA: {error}")))?;
    let (mut ts13_device_key_bind, ts13_device_key_census) = MdocPrivateDeviceKeyBind::prover(
        device_input.encode_pk(stwo_mldsa::profile::ML_DSA_44),
        private_device_pk_start,
        issuer_message.len(),
        issuer_message_field.clone(),
        mldsa_range_handle.clone(),
        expand_a_bindings.rho.clone(),
        t1_handle.clone(),
        device_pk_start_handle.clone(),
    )
    .map_err(|error| Error::Prove(format!("TS13 private device-key bind: {error}")))?;
    if !ts13_device_key_census.has_fixed_demo_shape() {
        return Err(Error::Prove(
            "TS13 private device-key binder geometry differs from the fixed profile".to_string(),
        ));
    }
    let (mut ts13_mso_validity, ts13_validity_range_uses) = MdocPrivateMsoValidity::prover(
        MdocPrivateMsoValiditySpec {
            timestamp_epoch_seconds: public.timestamp_epoch_seconds,
            verification_timestamp_rfc3339_utc: public.verification_timestamp_rfc3339_utc,
        },
        private_validity_witness,
        mldsa_range_handle.clone(),
        validity_handle.clone(),
    )
    .map_err(|error| Error::Prove(format!("TS13 private MSO validity: {error}")))?;

    let private_item_handles = MdocPrivateItemHandles::fresh(attribute_field.clone());
    let padded_item = stwo_sha256::native::pad_message(&extracted.attribute.item);
    let private_item_input = MdocPrivateItemPrivateInput::new(padded_item.clone());
    let mut private_item_bind = MdocPrivateItemBind::new(
        private_item_input,
        MDOC_ATTRIBUTE_FIELD_IDS,
        private_item_handles.clone(),
    )
    .map_err(map_private_item_prove_error)?;
    let mut private_item_outer_parser = MdocCborStream::new(
        padded_item,
        MdocCborInputMode::ShaPadded,
        MDOC_ATTRIBUTE_FIELD_IDS.outer_stream,
        private_item_handles.item_fields.clone(),
        private_item_handles.outer_parsed.clone(),
    )
    .map_err(|error| Error::Prove(format!("IssuerSignedItem outer parser: {error}")))?;
    let mut private_item_inner_parser = MdocCborStream::new(
        private_item_bind.inner_bytes().to_vec(),
        MdocCborInputMode::Raw,
        MDOC_ATTRIBUTE_FIELD_IDS.inner_stream,
        private_item_handles.inner_raw.clone(),
        private_item_handles.inner_parsed.clone(),
    )
    .map_err(|error| Error::Prove(format!("IssuerSignedItem inner parser: {error}")))?;
    let scanner_handles = MdocValueDigestsScanHandles {
        issuer_message: issuer_message_field.clone(),
        mso_start: mso_start_handle.clone(),
        item: MdocValueDigestItemHandles {
            digest_id: private_item_handles.digest_id.clone(),
            digest: attribute_digest.clone(),
        },
    };
    let scanner_spec = MdocValueDigestsScanSpec {
        issuer_message_len: issuer_message.len(),
        mso_len: extracted.mso.len(),
        namespace: PID_NAMESPACE.to_string(),
    };
    let scanner_witness = MdocValueDigestsScanWitness {
        issuer_message: issuer_message.clone(),
        mso_start: private_mso_start,
        selected_digest: MdocSelectedValueDigest {
            digest_id: extracted.attribute.digest_id,
            digest: Sha256::digest(&extracted.attribute.item).into(),
        },
    };
    let (mut value_digests_scan, value_digests_census) =
        MdocValueDigestsScan::prover(scanner_spec, scanner_witness, scanner_handles)
            .map_err(map_value_digests_prove_error)?;
    if private_mso_census.issuer_position_uses.len()
        != value_digests_census.issuer_position_uses.len()
        || ts13_device_key_census.issuer_position_uses.len()
            != private_mso_census.issuer_position_uses.len()
    {
        return Err(Error::Prove(
            "private issuer-message census lengths disagree".to_string(),
        ));
    }
    let ts13_device_key_uses = ts13_device_key_census.issuer_position_uses.as_slice();
    let issuer_position_uses: Vec<u32> = private_mso_census
        .issuer_position_uses
        .into_iter()
        .zip(value_digests_census.issuer_position_uses)
        .enumerate()
        .map(|(index, (mso_uses, scan_uses))| {
            mso_uses
                .checked_add(scan_uses)
                .and_then(|uses| uses.checked_add(ts13_device_key_uses[index]))
                .ok_or_else(|| {
                    Error::Prove(format!(
                        "private issuer message use count overflows at byte {index}"
                    ))
                })
        })
        .collect::<Result<_, _>>()?;
    let mut issuer_message_provider = MdocPrivateMessageProvider::new(
        issuer_message.clone(),
        issuer_position_uses,
        issuer_message_field.clone(),
    )
    .map_err(|error| Error::Prove(format!("private issuer message provider: {error}")))?;
    let revocation_input = ts13_revocation_mldsa_prover_input(
        &public.revocation,
        &revocation_signature,
        revocation_message.to_vec(),
    )?;
    let ((issuer_prepared, device_prepared), revocation_prepared) = rayon::join(
        || {
            rayon::join(
                || {
                    prepare_mldsa_role(
                        stwo_mldsa::profile::ML_DSA_65,
                        issuer_input,
                        "mldsa witness",
                    )
                },
                || {
                    prepare_mldsa_role(
                        stwo_mldsa::profile::ML_DSA_44,
                        device_input,
                        "mldsa device witness",
                    )
                },
            )
        },
        || {
            prepare_mldsa_role(
                stwo_mldsa::profile::ML_DSA_65,
                *revocation_input,
                "mldsa revocation witness",
            )
        },
    );
    // Report preparation errors in issuer, device, then revocation order.
    let issuer_prepared = issuer_prepared?;
    let device_prepared = device_prepared?;
    let revocation_prepared = revocation_prepared?;

    // The issuer Sig_structure is private. Its hosted µ bridge consumes one
    // complete indexed copy from `issuer_message_provider`; only the public
    // message length determines its transcript/layout.
    let mut issuer_mldsa = MlDsaStatementProver::hosted(
        issuer_prepared.0,
        issuer_prepared.1,
        issuer_message_field.clone(),
        mldsa_range_handle.clone(),
        mldsa_keccak_handle.clone(),
    )
    .with_instance_namespace(MDOC_ISSUER_MLDSA_NAMESPACE)
    .with_stream_base(MDOC_ISSUER_MLDSA_STREAM_BASE)
    .with_private_message();
    // Hosted in-circuit ML-DSA device statement in public-message mode.
    let mut device_mldsa = MlDsaStatementProver::hosted_private_key(
        device_prepared.0,
        device_prepared.1,
        issuer_message_field.clone(),
        mldsa_range_handle.clone(),
        mldsa_keccak_handle.clone(),
        PrivateKeyEvalBindings::new(expand_a_bindings.ntt.clone(), t1_handle.clone()),
    )
    .map(|prover| {
        prover
            .with_instance_namespace(MDOC_DEVICE_MLDSA_NAMESPACE)
            .with_stream_base(MDOC_DEVICE_MLDSA_STREAM_BASE)
    })
    .map_err(|error| Error::Prove(format!("TS13 private device ML-DSA: {error}")))?;
    // Hosted in-circuit ML-DSA revocation statement, private-message mode: the
    // prover's input carries the REAL 20-byte message (from the private range
    // witness); only its LENGTH is mixed into the transcript.
    let mut revocation_mldsa = MlDsaStatementProver::hosted(
        revocation_prepared.0,
        revocation_prepared.1,
        revocation_message_field.clone(),
        mldsa_range_handle.clone(),
        mldsa_keccak_handle.clone(),
    )
    .with_instance_namespace(MDOC_REVOCATION_MLDSA_NAMESPACE)
    .with_stream_base(MDOC_REVOCATION_MLDSA_STREAM_BASE)
    .with_private_message();
    let range_uses = vec![
        issuer_mldsa.range_uses().clone(),
        device_mldsa.range_uses().clone(),
        revocation_mldsa.range_uses().clone(),
        ts13_expand_a.range_uses().clone(),
        ts13_device_key_bind.range_uses().clone(),
        ts13_validity_range_uses.clone(),
    ];
    let mut mldsa_range_table = SharedRangeTable::prover(&range_uses, mldsa_range_handle.clone());
    let mut keccak_shapes = Vec::new();
    let mut keccak_streams = Vec::new();
    for (shapes, streams) in [
        issuer_mldsa.keccak_jobs(),
        ts13_expand_a
            .keccak_jobs()
            .map_err(|error| Error::Prove(format!("TS13 private ExpandA jobs: {error}")))?,
        device_mldsa.keccak_jobs(),
        revocation_mldsa.keccak_jobs(),
    ] {
        keccak_shapes.extend(shapes);
        keccak_streams.extend(streams);
    }
    let mut mldsa_keccak_service =
        KeccakServiceProver::new(keccak_shapes, keccak_streams, mldsa_keccak_handle.clone());
    // The fixed-width padded stream uses one namespaced SHA proof instance and
    // its fixed digest bridge.
    let mut attribute_sha =
        Sha256Prover::new(&attribute_sha_witness, TS13_DEMO_ATTRIBUTE_SHA_LOG_N_ROWS)
            .with_instance_namespace(MDOC_ATTRIBUTE_SHA_NAMESPACE)
            .with_digest_handle(attribute_digest.clone())
            .with_field_handle(attribute_exposure, attribute_field.clone())
            .with_shared_tables(sha_table_relations.clone());
    let mut mso_sha = Sha256Prover::new(&mso_sha_witness, MDOC_MSO_SHA_LOG_SIZE)
        .with_instance_namespace(MDOC_MSO_SHA_NAMESPACE)
        .with_digest_handle(mso_digest.clone())
        .with_field_handle(
            FieldExposure::from_full_padded_stream(
                MDOC_MSO_SHA_STREAM_FIELD_ID,
                mso_sha_witness.padding.padded.len(),
            ),
            mso_stream_field.clone(),
        )
        .with_shared_tables(sha_table_relations.clone());

    let mut ts13_revocation_public = MdocRevocationPublicBind::new(public.revocation.clone());
    let mut ts13_revocation_range = MdocRevocationRangeBind::prover(
        revocation_range,
        Sha256::digest(&extracted.mso).into(),
        mso_digest.clone(),
        public.revocation.epoch,
        revocation_message_field.clone(),
    );

    crate::report_prove_timing(
        "eu_id_prover",
        "witness_generation",
        witness_start.elapsed(),
    );

    let (stark_proof, post_interaction_payloads, ts13_demo_circuit_geometry) = {
        let mut modules: Vec<&mut dyn AirProver> = Vec::new();
        collect_ts13_demo_modules!(
            modules;
            sha_tables = &mut sha_tables,
            range_tables = &mut mldsa_range_table,
            keccak_service = &mut mldsa_keccak_service,
            public_context = &mut ts13_public_context,
            issuer_message = &mut issuer_message_provider,
            issuer_mldsa = &mut issuer_mldsa,
            attribute_sha = &mut attribute_sha,
            mso_sha = &mut mso_sha,
            item_outer_parser = &mut private_item_outer_parser,
            item_inner_parser = &mut private_item_inner_parser,
            item_binder = &mut private_item_bind,
            mso_binder = &mut private_mso_bind,
            mso_validity = &mut ts13_mso_validity,
            value_digests = &mut value_digests_scan,
            expand_a = &mut ts13_expand_a,
            device_key = &mut ts13_device_key_bind,
            device_mldsa = &mut device_mldsa,
            revocation_range = &mut ts13_revocation_range,
            revocation_mldsa = &mut revocation_mldsa,
            revocation_public = &mut ts13_revocation_public,
        );
        let (stark_proof, post_interaction_payloads) =
            air_core::prove_with_post_interaction(modules.as_mut_slice(), config)
                .map_err(|e| Error::Prove(format!("{e:?}")))?;
        let geometry = Some(capture_ts13_demo_circuit_geometry(&modules));
        (stark_proof, post_interaction_payloads, geometry)
    };
    Ok(MdocProof {
        stark_proof,
        sha_tables_interaction_claim: sha_tables.interaction_claim().clone(),
        mldsa: MdocMlDsaClaims::from_prover(&issuer_mldsa),
        device_mldsa: MdocMlDsaClaims::from_prover(&device_mldsa),
        revocation_mldsa: MdocMlDsaClaims::from_prover(&revocation_mldsa),
        mldsa_range_table_claimed_sum: mldsa_range_table.claimed_sum(),
        keccak_service_claimed_sums: mldsa_keccak_service.claimed_sums(),
        private_issuer_message_interaction_claim: issuer_message_provider.claim().clone(),
        attribute_sha_interaction_claim: attribute_sha.interaction_claim().clone(),
        mso_sha_interaction_claim: mso_sha.interaction_claim().clone(),
        private_mso_bind_interaction_claim: private_mso_bind.interaction_claim().clone(),
        private_item_interaction_claim: private_item_bind.claim().clone(),
        value_digests_scan_interaction_claim: value_digests_scan.claim().clone(),
        private_item_outer_cbor_interaction_claim: private_item_outer_parser
            .interaction_claim()
            .clone(),
        private_item_inner_cbor_interaction_claim: private_item_inner_parser
            .interaction_claim()
            .clone(),
        ts13_expand_a_claim: ts13_expand_a.claim(),
        ts13_device_key_bind_interaction_claim: ts13_device_key_bind.interaction_claim().clone(),
        ts13_mso_validity_interaction_claim: ts13_mso_validity.interaction_claim().clone(),
        ts13_revocation_range_interaction_claim: ts13_revocation_range.interaction_claim().clone(),
        post_interaction_payloads,
        ts13_demo_circuit_geometry,
    })
}

pub(crate) fn verify_mdoc_ts13_demo_circuit(
    proof: &MdocProof,
    public: &MdocTs13DemoCircuitPublicInput,
) -> Result<(), Error> {
    let expected_pcs_config = mdoc_ts13_pcs_config();
    let verification_date = validate_public_input_shape(public, "verify")?;
    let mut issuer_input = *private_issuer_verifier_input(&public.trusted_issuer_public_key)?;
    validate_single_mldsa_public_key(
        "issuer",
        stwo_mldsa::profile::ML_DSA_65,
        &issuer_input,
        "verify",
    )?;
    validate_public_issuer_projection(&issuer_input)?;
    let issuer_public_message = false;
    if !proof.mldsa.has_expected_shape(issuer_public_message) {
        return Err(Error::Verify(
            "mdoc proof ML-DSA issuer claim tree has the wrong shape".to_string(),
        ));
    }
    if proof.device_mldsa.group_evals.len() != stwo_mldsa::statement::n_private_key_group_evals()
        || proof.device_mldsa.claimed_sums.len()
            != stwo_mldsa::statement::hosted_private_key_claimed_sums_len()
    {
        return Err(Error::Verify(
            "mdoc proof ML-DSA device claim tree has the wrong shape".to_string(),
        ));
    }
    let expected_log = min_log_size(
        usize::from(TS13_DEMO_ITEM_PADDED_BYTES) / stwo_sha256::constants::BLOCK_BYTES,
    );
    if expected_log != TS13_DEMO_ATTRIBUTE_SHA_LOG_N_ROWS {
        return Err(Error::Verify(
            "mdoc attribute SHA schedule does not match the fixed profile".to_string(),
        ));
    }
    let mso_sha_padded_len = checked_sha256_padded_len(TS13_DEMO_MSO_PAYLOAD_BYTES)
        .ok_or_else(|| Error::Verify("mdoc private MSO SHA padded length overflows".to_string()))?;
    let mso_sha_blocks = mso_sha_padded_len / stwo_sha256::constants::BLOCK_BYTES;
    if min_log_size(mso_sha_blocks) != MDOC_MSO_SHA_LOG_SIZE {
        return Err(Error::Verify(
            "mdoc MSO SHA schedule does not match the fixed profile".to_string(),
        ));
    }
    if !proof.revocation_mldsa.has_expected_shape(false) {
        return Err(Error::Verify(
            "mdoc proof ML-DSA revocation claim tree does not match the statement".to_string(),
        ));
    }
    if proof.keccak_service_claimed_sums.len()
        != stwo_mldsa::stwo_keccak::service::service_claimed_sums_len()
    {
        return Err(Error::Verify(
            "mdoc proof Keccak service claims do not match the statement".to_string(),
        ));
    }
    // The Keccak service uses GKR for its round LogUp. Its proof is in
    // `post_interaction_payloads`. Verification gives each module its payload
    // in proof order. `verify_post_interaction` rejects a missing or invalid
    // payload. An empty payload fails GKR decoding.
    let issuer_message_field = SharedFieldRelation::new();
    let revocation_message_field = SharedFieldRelation::new();
    let attribute_digest = SharedDigestRelation::new();
    let mso_digest = SharedDigestRelation::new();
    let mso_stream_field = SharedFieldRelation::new();
    let mso_start_handle = SharedMdocMsoStartRelation::new();
    let device_pk_start_handle = SharedMdocDevicePkStartRelation::new();
    let validity_handle = SharedMdocMsoValidityBytesRelation::new();
    let expand_a_bindings = ExpandABindings::new();
    let t1_handle = SharedT1CellRelation::new();
    // The proof-wide keccak service's relations handle (mirror of the prover).
    let mldsa_keccak_handle = SharedKeccakRelations::new();
    let mldsa_range_handle = SharedRangeRelation::new();
    let attribute_field = SharedFieldRelation::new();
    let sha_table_relations = SharedShaTableRelations::new();
    if proof.stark_proof.config != expected_pcs_config {
        return Err(Error::WeakConfig {
            got: proof.stark_proof.config,
            expected: expected_pcs_config,
        });
    }
    let tree0_cache_key =
        mdoc_tree0_cache_key(public.device_cose_sig_structure.len(), expected_pcs_config)?;
    let cached_preprocessed_root = mdoc_tree0_cached_root(&tree0_cache_key)?;

    let mut sha_tables = ShaTablesVerifier::new(
        proof.sha_tables_interaction_claim.clone(),
        sha_table_relations.clone(),
    );
    let issuer_message_len = issuer_input.message.len();
    let mut issuer_message_provider = MdocPrivateMessageProvider::verifier(
        issuer_message_len,
        issuer_message_field.clone(),
        proof.private_issuer_message_interaction_claim.clone(),
    )
    .map_err(|error| Error::Verify(format!("private issuer message provider: {error}")))?;
    // The verifier knows only the issuer message length. Its zero bytes are
    // layout placeholders; the provider/hosted bridge relation carries the
    // signed private Sig_structure.
    issuer_input.tr =
        stwo_mldsa::statement::native_tr(stwo_mldsa::profile::ML_DSA_65, &issuer_input);
    issuer_input.message.fill(0);
    let issuer_claims = &proof.mldsa;
    let mut issuer_mldsa = MlDsaStatementVerifier::hosted(
        issuer_input,
        issuer_claims.group_evals.clone(),
        issuer_claims.claimed_sums.clone(),
        issuer_message_field.clone(),
        mldsa_range_handle.clone(),
        mldsa_keccak_handle.clone(),
    )
    .with_instance_namespace(MDOC_ISSUER_MLDSA_NAMESPACE)
    .with_stream_base(MDOC_ISSUER_MLDSA_STREAM_BASE)
    .with_private_message();
    let device_input = MlDsaPrivateKeyPublicInput {
        message: public.device_cose_sig_structure.clone(),
    };
    let device_claims = &proof.device_mldsa;
    let mut device_mldsa = MlDsaStatementVerifier::hosted_private_key(
        device_input,
        device_claims.group_evals.clone(),
        device_claims.claimed_sums.clone(),
        issuer_message_field.clone(),
        mldsa_range_handle.clone(),
        mldsa_keccak_handle.clone(),
        PrivateKeyEvalBindings::new(expand_a_bindings.ntt.clone(), t1_handle.clone()),
    )
    .map_err(|error| Error::Verify(format!("TS13 private device ML-DSA: {error}")))?
    .with_instance_namespace(MDOC_DEVICE_MLDSA_NAMESPACE)
    .with_stream_base(MDOC_DEVICE_MLDSA_STREAM_BASE);
    // The verifier rebuilds the revocation input from the public key. It uses
    // zero placeholders for the private signature and the 20-byte message.
    // The bounds are not clear verifier inputs or clear envelope fields. They
    // affect the committed trace and the proof.
    let revocation_claims = &proof.revocation_mldsa;
    let revocation_input = ts13_revocation_mldsa_verifier_input(
        &public.revocation,
        vec![0u8; TS13_REVOCATION_MESSAGE_LEN],
    )?;
    let mut revocation_mldsa = MlDsaStatementVerifier::hosted(
        *revocation_input,
        revocation_claims.group_evals.clone(),
        revocation_claims.claimed_sums.clone(),
        revocation_message_field.clone(),
        mldsa_range_handle.clone(),
        mldsa_keccak_handle.clone(),
    )
    .with_instance_namespace(MDOC_REVOCATION_MLDSA_NAMESPACE)
    .with_stream_base(MDOC_REVOCATION_MLDSA_STREAM_BASE)
    .with_private_message();
    let mut mldsa_range_table = SharedRangeTable::verifier(
        proof.mldsa_range_table_claimed_sum,
        mldsa_range_handle.clone(),
    );
    // Rebuild the Keccak job shapes from public data.
    // Use the fixed issuer, device, and revocation order.
    // The fixed profile and the public device message supply message lengths.
    // Role constants supply stream bases.
    // SIB uses the verifier-fixed cap for each role profile.
    // The proof supplies claimed sums.
    debug_assert_eq!(issuer_message_len, TS13_DEMO_ISSUER_MESSAGE_BYTES);
    debug_assert!(!issuer_public_message);
    let keccak_shapes = ts13_demo_mldsa_keccak_job_shapes(public.device_cose_sig_structure.len());
    let mut mldsa_keccak_service = KeccakServiceVerifier::new(
        keccak_shapes,
        proof.keccak_service_claimed_sums.clone(),
        mldsa_keccak_handle.clone(),
    );

    let mut attribute_sha = Sha256Verifier::new(
        TS13_DEMO_ATTRIBUTE_SHA_LOG_N_ROWS,
        proof.attribute_sha_interaction_claim.clone(),
    )
    .with_instance_namespace(MDOC_ATTRIBUTE_SHA_NAMESPACE)
    .with_digest_handle(attribute_digest.clone())
    .with_field_handle(attribute_exposure(), attribute_field.clone())
    .with_shared_tables(sha_table_relations.clone());
    let mut mso_sha = Sha256Verifier::new(
        MDOC_MSO_SHA_LOG_SIZE,
        proof.mso_sha_interaction_claim.clone(),
    )
    .with_instance_namespace(MDOC_MSO_SHA_NAMESPACE)
    .with_digest_handle(mso_digest.clone())
    .with_field_handle(
        FieldExposure::from_full_padded_stream(MDOC_MSO_SHA_STREAM_FIELD_ID, mso_sha_padded_len),
        mso_stream_field.clone(),
    )
    .with_shared_tables(sha_table_relations.clone());
    let private_mso_spec = private_mso_bind_spec(verification_date, mso_sha_padded_len);
    let mut private_mso_bind = MdocPrivateMsoBind::verifier(
        private_mso_spec,
        issuer_message_field.clone(),
        mso_stream_field.clone(),
        mso_start_handle.clone(),
        device_pk_start_handle.clone(),
        validity_handle.clone(),
        proof.private_mso_bind_interaction_claim.clone(),
    )
    .map_err(|error| Error::Verify(format!("TS13 private MSO bind: {error}")))?;
    let mut ts13_public_context = public.context_bind();
    let mut ts13_expand_a = ExpandAVerifier::new(
        stwo_mldsa::profile::ML_DSA_44,
        proof.ts13_expand_a_claim.clone(),
        MDOC_DEVICE_EXPAND_A_NAMESPACE,
        MDOC_DEVICE_EXPAND_A_STREAM_BASE,
        mldsa_range_handle.clone(),
        mldsa_keccak_handle.clone(),
        expand_a_bindings.clone(),
    )
    .map_err(|error| Error::Verify(format!("TS13 private ExpandA: {error}")))?;
    let mut ts13_device_key_bind = MdocPrivateDeviceKeyBind::verifier(
        issuer_message_len,
        issuer_message_field.clone(),
        mldsa_range_handle.clone(),
        expand_a_bindings.rho.clone(),
        t1_handle.clone(),
        device_pk_start_handle.clone(),
        proof.ts13_device_key_bind_interaction_claim.clone(),
    )
    .map_err(|error| Error::Verify(format!("TS13 private device-key bind: {error}")))?;
    let mut ts13_mso_validity = MdocPrivateMsoValidity::verifier(
        MdocPrivateMsoValiditySpec {
            timestamp_epoch_seconds: public.timestamp_epoch_seconds,
            verification_timestamp_rfc3339_utc: public.verification_timestamp_rfc3339_utc,
        },
        mldsa_range_handle.clone(),
        validity_handle.clone(),
        proof.ts13_mso_validity_interaction_claim.clone(),
    )
    .map_err(|error| Error::Verify(format!("TS13 private MSO validity: {error}")))?;

    let private_item_handles = MdocPrivateItemHandles::fresh(attribute_field.clone());
    let mut private_item_bind = MdocPrivateItemBind::verifier(
        MDOC_ATTRIBUTE_FIELD_IDS,
        private_item_handles.clone(),
        proof.private_item_interaction_claim.clone(),
    );
    let mut private_item_outer_parser = MdocCborStream::verifier(
        MdocCborInputMode::ShaPadded,
        MDOC_ATTRIBUTE_FIELD_IDS.outer_stream,
        private_item_bind.outer_parser_log_size(),
        private_item_handles.item_fields.clone(),
        private_item_handles.outer_parsed.clone(),
        proof.private_item_outer_cbor_interaction_claim.clone(),
    )
    .map_err(|error| Error::Verify(format!("IssuerSignedItem outer parser: {error}")))?;
    let mut private_item_inner_parser = MdocCborStream::verifier(
        MdocCborInputMode::Raw,
        MDOC_ATTRIBUTE_FIELD_IDS.inner_stream,
        private_item_bind.inner_parser_log_size(),
        private_item_handles.inner_raw.clone(),
        private_item_handles.inner_parsed.clone(),
        proof.private_item_inner_cbor_interaction_claim.clone(),
    )
    .map_err(|error| Error::Verify(format!("IssuerSignedItem inner parser: {error}")))?;
    let scanner_handles = MdocValueDigestsScanHandles {
        issuer_message: issuer_message_field.clone(),
        mso_start: mso_start_handle.clone(),
        item: MdocValueDigestItemHandles {
            digest_id: private_item_handles.digest_id.clone(),
            digest: attribute_digest.clone(),
        },
    };
    let scanner_spec = MdocValueDigestsScanSpec {
        issuer_message_len,
        mso_len: TS13_DEMO_MSO_PAYLOAD_BYTES,
        namespace: PID_NAMESPACE.to_string(),
    };
    let mut value_digests_scan = MdocValueDigestsScan::verifier(
        scanner_spec,
        scanner_handles,
        proof.value_digests_scan_interaction_claim.clone(),
    )
    .map_err(|error| Error::Verify(format!("private valueDigests scanner: {error}")))?;
    let mut ts13_revocation_public = MdocRevocationPublicBind::new(public.revocation.clone());
    let mut ts13_revocation_range = MdocRevocationRangeBind::verifier(
        mso_digest.clone(),
        public.revocation.epoch,
        revocation_message_field.clone(),
        proof.ts13_revocation_range_interaction_claim.clone(),
    );

    let mut modules: Vec<&mut dyn Air> = Vec::new();
    collect_ts13_demo_modules!(
        modules;
        sha_tables = &mut sha_tables,
        range_tables = &mut mldsa_range_table,
        keccak_service = &mut mldsa_keccak_service,
        public_context = &mut ts13_public_context,
        issuer_message = &mut issuer_message_provider,
        issuer_mldsa = &mut issuer_mldsa,
        attribute_sha = &mut attribute_sha,
        mso_sha = &mut mso_sha,
        item_outer_parser = &mut private_item_outer_parser,
        item_inner_parser = &mut private_item_inner_parser,
        item_binder = &mut private_item_bind,
        mso_binder = &mut private_mso_bind,
        mso_validity = &mut ts13_mso_validity,
        value_digests = &mut value_digests_scan,
        expand_a = &mut ts13_expand_a,
        device_key = &mut ts13_device_key_bind,
        device_mldsa = &mut device_mldsa,
        revocation_range = &mut ts13_revocation_range,
        revocation_mldsa = &mut revocation_mldsa,
        revocation_public = &mut ts13_revocation_public,
    );
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let expected_preprocessed_root = match cached_preprocessed_root.as_ref() {
            Some(root) => *root,
            None => air_core::compute_canonical_preprocessed_root(
                modules.as_mut_slice(),
                expected_pcs_config,
            )
            .map_err(air_core::VerifyError::Stark)?,
        };
        air_core::verify_with_expected_preprocessed_root_and_payloads(
            modules.as_mut_slice(),
            &proof.stark_proof,
            Some(expected_preprocessed_root),
            &proof.post_interaction_payloads,
        )?;
        Ok(expected_preprocessed_root)
    })) {
        Ok(Ok(expected_preprocessed_root)) => {
            // Soundness/DoS boundary: a miss is memoized only after the whole
            // proof has verified against the verifier-recomputed root.
            if cached_preprocessed_root.is_none() {
                mdoc_tree0_cache_insert(tree0_cache_key, expected_preprocessed_root)?;
            }
            Ok(())
        }
        Ok(Err(air_core::VerifyError::PreprocessedRootMismatch { got, expected })) => {
            Err(Error::PreprocessedRootMismatch { got, expected })
        }
        Ok(Err(error)) => Err(Error::Verify(format!("{error:?}"))),
        Err(_) => Err(Error::Verify(
            "malformed mdoc proof panicked during verification".to_string(),
        )),
    }
}

const TS13_PCS_LOG_BLOWUP_FACTOR: u32 = 2;
const TS13_PCS_QUERIES: usize = 54;
const TS13_PCS_POW_BITS: u32 = 20;
const TS13_PCS_LIFTING_LOG_SIZE: Option<u32> = None;

pub(crate) fn mdoc_ts13_pcs_config() -> PcsConfig {
    // PCS query and proof-of-work label: 54×2 + 20 = 128 bits.
    // This exceeds the 108-bit OODS bound that dominates the TS13 STARK.
    // The verifier pins this configuration and rejects other configurations.
    // TS13 accounts for OODS and binding-hash limits separately.
    PcsConfig {
        pow_bits: TS13_PCS_POW_BITS,
        fri_config: FriConfig::new(1, TS13_PCS_LOG_BLOWUP_FACTOR, TS13_PCS_QUERIES, 2),
        lifting_log_size: TS13_PCS_LIFTING_LOG_SIZE,
    }
}

fn value_field<'a>(map: &'a [(Value, Value)], field: &'static str) -> Result<&'a Value, MdocError> {
    let key = Value::Text(field.to_string());
    let mut matches = map
        .iter()
        .filter_map(|(candidate, value)| (candidate == &key).then_some(value));
    let value = matches.next().ok_or(MdocError::MissingField(field))?;
    if matches.next().is_some() {
        return Err(MdocError::UnsupportedCircuitValue("duplicate text map key"));
    }
    Ok(value)
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
    let mut matches = map.iter().filter_map(|(candidate, value)| {
        value_i128(candidate)
            .ok()
            .filter(|candidate| *candidate == key)
            .map(|_| value)
    });
    let value = matches.next().ok_or(MdocError::MissingField(field))?;
    if matches.next().is_some() {
        return Err(MdocError::UnsupportedCircuitValue(
            "duplicate integer map key",
        ));
    }
    value_i128(value)
}

fn bytes_int_field<'a>(
    map: &'a [(Value, Value)],
    key: i128,
    field: &'static str,
) -> Result<&'a [u8], MdocError> {
    let mut matches = map.iter().filter_map(|(candidate, value)| {
        value_i128(candidate)
            .ok()
            .filter(|candidate| *candidate == key)
            .map(|_| value)
    });
    let value = matches.next().ok_or(MdocError::MissingField(field))?;
    if matches.next().is_some() {
        return Err(MdocError::UnsupportedCircuitValue(
            "duplicate integer map key",
        ));
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    const RHO_BYTES: usize = 32;
    const TR_BYTES: usize = 64;
    const TEST_VERIFY_AT: i64 = 1_798_761_600;
    const TEST_REVOCATION_EPOCH: u32 = 17;
    const TEST_CIRCUIT_HASH: [u8; 32] = crate::ts13_demo_artifact_constants::TS13_DEMO_CIRCUIT_HASH;

    fn committed_cells(layout: &TreeLayout) -> usize {
        layout
            .preprocessed
            .iter()
            .chain(&layout.trace)
            .chain(&layout.interaction)
            .map(|log_size| 1usize << log_size)
            .sum()
    }

    #[test]
    fn tree_zero_cache_key_binds_the_complete_pcs_configuration() {
        let base = mdoc_ts13_pcs_config();
        let base_key = mdoc_tree0_cache_key(TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY, base).unwrap();
        let variants = [
            PcsConfig {
                fri_config: FriConfig::new(
                    2,
                    base.fri_config.log_blowup_factor,
                    base.fri_config.n_queries,
                    base.fri_config.fold_step,
                ),
                ..base
            },
            PcsConfig {
                fri_config: FriConfig::new(
                    base.fri_config.log_last_layer_degree_bound,
                    2,
                    base.fri_config.n_queries,
                    base.fri_config.fold_step,
                ),
                ..base
            },
            PcsConfig {
                fri_config: FriConfig::new(
                    base.fri_config.log_last_layer_degree_bound,
                    base.fri_config.log_blowup_factor,
                    base.fri_config.n_queries + 1,
                    base.fri_config.fold_step,
                ),
                ..base
            },
            PcsConfig {
                fri_config: FriConfig::new(
                    base.fri_config.log_last_layer_degree_bound,
                    base.fri_config.log_blowup_factor,
                    base.fri_config.n_queries,
                    1,
                ),
                ..base
            },
            PcsConfig {
                pow_bits: base.pow_bits + 1,
                ..base
            },
            PcsConfig {
                lifting_log_size: Some(20),
                ..base
            },
        ];
        for variant in variants {
            let key =
                mdoc_tree0_cache_key(TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY, variant).unwrap();
            assert_ne!(key.material, base_key.material);
        }
    }

    #[test]
    fn mixed_profile_keccak_plan_has_exact_role_order_and_163_permutations() {
        const ISSUER_JOBS: std::ops::Range<usize> = 0..3;
        const EXPAND_A_JOBS: std::ops::Range<usize> = 3..19;
        const DEVICE_JOBS: std::ops::Range<usize> = 19..23;
        const REVOCATION_JOBS: std::ops::Range<usize> = 23..26;

        let shapes = ts13_demo_mldsa_keccak_job_shapes(TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY);
        assert_eq!(shapes.len(), 26);
        let jobs = stwo_mldsa::stwo_keccak::sponge_v::JobList::new(shapes);
        let role_permutations: [usize; 4] = [
            jobs.jobs[ISSUER_JOBS]
                .iter()
                .map(|shape| shape.n_perms())
                .sum(),
            jobs.jobs[EXPAND_A_JOBS]
                .iter()
                .map(|shape| shape.n_perms())
                .sum(),
            jobs.jobs[DEVICE_JOBS]
                .iter()
                .map(|shape| shape.n_perms())
                .sum(),
            jobs.jobs[REVOCATION_JOBS]
                .iter()
                .map(|shape| shape.n_perms())
                .sum(),
        ];
        assert_eq!(role_permutations, [27, 96, 27, 13]);
        assert_eq!(jobs.n_perms_total(), 163);

        assert_eq!(
            jobs.jobs[0].absorb_stream_id,
            MDOC_ISSUER_MLDSA_STREAM_BASE + stwo_mldsa::statement::MU_ABSORB
        );
        assert_eq!(
            jobs.jobs[3].absorb_stream_id,
            MDOC_DEVICE_EXPAND_A_STREAM_BASE + 16
        );
        assert_eq!(
            jobs.jobs[19].absorb_stream_id,
            MDOC_DEVICE_MLDSA_STREAM_BASE + stwo_mldsa::statement::TR_ABSORB
        );
        assert_eq!(
            jobs.jobs[23].absorb_stream_id,
            MDOC_REVOCATION_MLDSA_STREAM_BASE + stwo_mldsa::statement::MU_ABSORB
        );
        assert_eq!(
            jobs.jobs[19].message_len,
            stwo_mldsa::profile::ML_DSA_44.pk_bytes()
        );
        assert_eq!(jobs.jobs[19].n_absorb, 10);
        assert_eq!(
            jobs.jobs[20].message_capacity,
            Some(66 + TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY)
        );
        assert_eq!(jobs.jobs[20].n_absorb, 9);
        assert_eq!(
            jobs.jobs[22].message_len,
            stwo_mldsa::profile::ML_DSA_44.c_tilde_bytes()
        );
        assert_eq!(jobs.jobs[22].n_squeeze, 1);
    }

    #[test]
    fn device_cose_profile_rejects_algorithm_and_wire_length_substitution() {
        let detached_payload = b"device authentication";
        let device_sign1 = |protected: &[u8], signature_len: usize| {
            Value::Array(vec![
                Value::Bytes(protected.to_vec()),
                Value::Map(Vec::new()),
                Value::Null,
                Value::Bytes(vec![0; signature_len]),
            ])
        };
        assert!(parse_cose_sign1_with_detached_payload(
            &device_sign1(
                MLDSA44_PROTECTED_HEADER,
                stwo_mldsa::profile::ML_DSA_44.sig_bytes(),
            ),
            detached_payload,
        )
        .is_ok());
        assert!(parse_cose_sign1_with_detached_payload(
            &device_sign1(
                MLDSA_PROTECTED_HEADER,
                stwo_mldsa::profile::ML_DSA_44.sig_bytes(),
            ),
            detached_payload,
        )
        .is_err());
        assert!(parse_cose_sign1_with_detached_payload(
            &device_sign1(
                MLDSA44_PROTECTED_HEADER,
                stwo_mldsa::profile::ML_DSA_65.sig_bytes(),
            ),
            detached_payload,
        )
        .is_err());

        let device_key = |algorithm: i64, public_key_len: usize| {
            Value::Map(vec![
                (
                    Value::from(1),
                    Value::from(stwo_mldsa::constants::COSE_KTY_AKP),
                ),
                (Value::from(3), Value::from(algorithm)),
                (Value::from(-1), Value::Bytes(vec![0; public_key_len])),
            ])
        };
        assert!(parse_device_cose_key(&device_key(
            stwo_mldsa::constants::COSE_ALG_ML_DSA_44,
            stwo_mldsa::profile::ML_DSA_44.pk_bytes(),
        ))
        .is_ok());
        assert!(parse_device_cose_key(&device_key(
            stwo_mldsa::constants::COSE_ALG_ML_DSA_65,
            stwo_mldsa::profile::ML_DSA_44.pk_bytes(),
        ))
        .is_err());
        assert!(parse_device_cose_key(&device_key(
            stwo_mldsa::constants::COSE_ALG_ML_DSA_44,
            stwo_mldsa::profile::ML_DSA_65.pk_bytes(),
        ))
        .is_err());
    }

    fn test_public_input(
        transcript: &[u8],
        issuer_public_key: &[u8],
        revocation_public_key: &[u8],
        zk_system_id: &str,
    ) -> MdocTs13DemoCircuitPublicInput {
        let derived =
            crate::ts13_demo::derive_public_context(crate::ts13_demo::Ts13DemoPublicContextInput {
                circuit_hash: &TEST_CIRCUIT_HASH,
                zk_system_id,
                document_type: PID_DOCTYPE,
                namespace: PID_NAMESPACE,
                element_identifier: "age_over_18",
                expected_value_cbor: &[0xf5],
                timestamp_epoch_seconds: TEST_VERIFY_AT,
                session_transcript: transcript,
                trusted_issuer_public_key: issuer_public_key,
                revocation_public_key,
                revocation_epoch: TEST_REVOCATION_EPOCH,
            })
            .expect("public request context derives");
        MdocTs13DemoCircuitPublicInput {
            circuit_hash: TEST_CIRCUIT_HASH,
            request_context_digest: derived.request_context_digest,
            timestamp_epoch_seconds: TEST_VERIFY_AT,
            verification_timestamp_rfc3339_utc: derived.verification_timestamp_rfc3339_utc,
            trusted_issuer_public_key: issuer_public_key.to_vec(),
            device_cose_sig_structure: derived.device_cose_sig_structure,
            revocation: MdocRevocationPublicInputs {
                revocation_public_key: MdocRevocationKey(revocation_public_key.to_vec()),
                epoch: TEST_REVOCATION_EPOCH,
            },
        }
    }

    fn test_revocation_witness(mso: &[u8]) -> (u64, u64, MdocRevocationSignature) {
        let id = crate::ts13::ts13_mso_derived_revocation_id(mso);
        let id_lo = id.checked_sub(1).expect("fixture revocation ID is nonzero");
        let id_hi = id
            .checked_add(1)
            .expect("fixture revocation ID is not the maximum");
        let (_, signature) = crate::mldsa_test_fixture::mldsa_revocation_fixture(
            id_lo,
            id_hi,
            TEST_REVOCATION_EPOCH,
        );
        (id_lo, id_hi, MdocRevocationSignature(signature))
    }

    fn input(message: Vec<u8>, signature_fill: u8) -> Box<MlDsaVerifyInput> {
        Box::new(MlDsaVerifyInput {
            rho: [7; RHO_BYTES],
            t1: [[0; stwo_mldsa::constants::N]; stwo_mldsa::constants::K],
            tr: [signature_fill; TR_BYTES],
            message,
            c_tilde: [signature_fill; stwo_mldsa::constants::C_TILDE_BYTES],
            z: [[i32::from(signature_fill); stwo_mldsa::constants::N]; stwo_mldsa::constants::L],
            hint: [[signature_fill & 1; stwo_mldsa::constants::N]; stwo_mldsa::constants::K],
        })
    }

    fn shape_public_input() -> MdocTs13DemoCircuitPublicInput {
        MdocTs13DemoCircuitPublicInput {
            circuit_hash: [0x11; 32],
            request_context_digest: [0x22; 32],
            timestamp_epoch_seconds: 1_775_001_600,
            verification_timestamp_rfc3339_utc: *b"2026-04-01T00:00:00Z",
            trusted_issuer_public_key: input(Vec::new(), 0)
                .encode_pk(stwo_mldsa::profile::ML_DSA_65),
            device_cose_sig_structure: vec![0; 64],
            revocation: MdocRevocationPublicInputs {
                revocation_public_key: MdocRevocationKey(vec![0; stwo_mldsa::constants::PK_BYTES]),
                epoch: 17,
            },
        }
    }

    fn item_key_map(order: [usize; 4]) -> Vec<(Value, Value)> {
        order
            .into_iter()
            .map(|index| {
                (
                    Value::Text(ISSUER_SIGNED_ITEM_KEYS[index].to_string()),
                    Value::Null,
                )
            })
            .collect()
    }

    #[test]
    fn issuer_signed_item_key_set_accepts_all_map_orders() {
        let mut accepted = 0;
        for first in 0..4 {
            for second in 0..4 {
                for third in 0..4 {
                    for fourth in 0..4 {
                        let order = [first, second, third, fourth];
                        if order
                            .iter()
                            .enumerate()
                            .any(|(index, value)| order[..index].contains(value))
                        {
                            continue;
                        }
                        ensure_issuer_signed_item_keys(&item_key_map(order))
                            .expect("each map-key permutation is valid");
                        accepted += 1;
                    }
                }
            }
        }
        assert_eq!(accepted, 24);
    }

    #[test]
    fn issuer_signed_item_key_set_rejects_missing_duplicate_and_unknown_keys() {
        let missing = item_key_map([0, 1, 2, 2]);
        let mut unknown = item_key_map([0, 1, 2, 3]);
        unknown[3].0 = Value::Text("unknown".to_string());
        let extra = [
            item_key_map([0, 1, 2, 3]),
            vec![(Value::Text("unknown".to_string()), Value::Null)],
        ]
        .concat();

        for invalid in [missing, unknown, extra] {
            assert!(matches!(
                ensure_issuer_signed_item_keys(&invalid),
                Err(MdocError::UnsupportedCircuitValue(
                    "IssuerSignedItem key set"
                ))
            ));
        }
    }

    #[test]
    fn public_shape_caps_return_typed_errors_without_panicking() {
        type Mutation = fn(&mut MdocTs13DemoCircuitPublicInput);
        let cases: [(&str, Mutation); 4] = [
            ("short issuer key", |public| {
                public.trusted_issuer_public_key.clear()
            }),
            ("zero device message", |public| {
                public.device_cose_sig_structure.clear()
            }),
            ("long device message", |public| {
                public.device_cose_sig_structure =
                    vec![0; TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY + 1]
            }),
            ("unsupported timestamp", |public| {
                public.timestamp_epoch_seconds = -1
            }),
        ];

        validate_public_input_shape(&shape_public_input(), "prove").expect("control prove shape");
        validate_public_input_shape(&shape_public_input(), "verify").expect("control verify shape");
        for phase in ["prove", "verify"] {
            for (name, mutate) in cases {
                let mut public = shape_public_input();
                mutate(&mut public);
                let outcome =
                    std::panic::catch_unwind(|| validate_public_input_shape(&public, phase));
                let error = outcome
                    .unwrap_or_else(|_| panic!("{phase} {name} shape panicked"))
                    .unwrap_err();
                assert!(
                    matches!(
                        (phase, error),
                        ("prove", Error::Prove(_)) | ("verify", Error::Verify(_))
                    ),
                    "{phase} {name} did not return a phase-typed error"
                );
            }
        }
    }

    #[test]
    fn canonical_verifier_reconstructs_zero_private_witnesses() {
        let encoded_key = input(Vec::new(), 0).encode_pk(stwo_mldsa::profile::ML_DSA_65);
        let issuer = private_issuer_verifier_input(&encoded_key).expect("valid issuer key");

        assert_eq!(issuer.message, vec![0; TS13_DEMO_ISSUER_MESSAGE_BYTES]);
        assert_eq!(issuer.tr, [0; 64]);
        assert_eq!(issuer.c_tilde, [0; stwo_mldsa::constants::C_TILDE_BYTES]);
        assert!(issuer
            .z
            .iter()
            .flatten()
            .all(|&coefficient| coefficient == 0));
        assert!(issuer.hint.iter().flatten().all(|&bit| bit == 0));
    }

    #[test]
    fn canonical_verifier_rejects_malformed_issuer_key() {
        let error =
            private_issuer_verifier_input(&[0; 31]).expect_err("short issuer key must fail");
        assert!(matches!(error, Error::Verify(_)));
    }

    #[test]
    fn composed_mso_and_device_key_substitution_rejects() {
        std::thread::Builder::new()
            .name("ts13-device-key-substitution-test".to_string())
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let transcript = openid4vp_session_transcript(b"ts13-demo-device-key-substitution");
                let credential_a =
                    crate::mldsa_test_fixture::mldsa_ts13_credential_a_with_transcript(&transcript);
                let credential_b =
                    crate::mldsa_test_fixture::mldsa_ts13_credential_b_with_transcript(&transcript);
                assert_ne!(credential_a.device_pk, credential_b.device_pk);
                assert_eq!(
                    credential_a.device_sig_structure,
                    credential_b.device_sig_structure
                );

                let request_a = MdocPidRequest::age_over_18(transcript.clone());
                let request_b = MdocPidRequest::age_over_18(transcript.clone());
                let mut hybrid = extract_pid_mdoc(&credential_a.document, &request_a)
                    .expect("first credential extracts");
                let extracted_b = extract_pid_mdoc(&credential_b.document, &request_b)
                    .expect("second credential extracts");
                stwo_mldsa::witness::generate_witness(
                    stwo_mldsa::profile::ML_DSA_44,
                    &extracted_b.device_auth_input,
                )
                .expect("second device signature is valid");
                hybrid.device_auth_input = extracted_b.device_auth_input;

                let public = test_public_input(
                    &transcript,
                    &credential_a.issuer_pk,
                    &credential_a.revocation_pk,
                    "rp-local-demo-device-key-substitution",
                );
                let (id_lo, id_hi, signature) = test_revocation_witness(&credential_a.mso);
                let revocation_range = MdocRevocationRangeWitness {
                    id: crate::ts13::ts13_mso_derived_revocation_id(&credential_a.mso),
                    id_lo,
                    id_hi,
                };

                let proof =
                    prove_mdoc_ts13_demo_circuit(&hybrid, &public, revocation_range, signature)
                        .expect("the substituted device witness builds an adversarial proof");
                verify_mdoc_ts13_demo_circuit(&proof, &public)
                    .expect_err("the substituted device key must fail");
            })
            .expect("large-stack substitution test thread starts")
            .join()
            .expect("large-stack substitution test thread succeeds");
    }

    #[test]
    fn composed_wrong_mso_revocation_id_with_valid_signature_rejects() {
        std::thread::Builder::new()
            .name("ts13-wrong-revocation-id-test".to_string())
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let transcript = openid4vp_session_transcript(b"ts13-wrong-revocation-id");
                let fixture =
                    crate::mldsa_test_fixture::mldsa_ts13_credential_a_with_transcript(&transcript);
                let request = MdocPidRequest::age_over_18(transcript.clone());
                let extracted =
                    extract_pid_mdoc(&fixture.document, &request).expect("credential extracts");
                let actual_id = crate::ts13::ts13_mso_derived_revocation_id(&fixture.mso);
                let wrong_id = if actual_id <= u64::MAX - 3 {
                    actual_id + 2
                } else {
                    actual_id - 2
                };
                let wrong_id_lo = wrong_id - 1;
                let wrong_id_hi = wrong_id + 1;
                assert!(!(wrong_id_lo < actual_id && actual_id < wrong_id_hi));

                let (revocation_pk, signature) =
                    crate::mldsa_test_fixture::mldsa_revocation_fixture(
                        wrong_id_lo,
                        wrong_id_hi,
                        TEST_REVOCATION_EPOCH,
                    );
                assert_eq!(revocation_pk, fixture.revocation_pk);
                let signed_message = crate::ts13::ts13_revocation_message(
                    wrong_id_lo,
                    wrong_id_hi,
                    TEST_REVOCATION_EPOCH,
                );
                let signature_trace = stwo_mldsa::verify_internals(
                    stwo_mldsa::profile::ML_DSA_65,
                    &revocation_pk,
                    &signed_message,
                    &signature,
                )
                .expect("changed endpoints decode");
                assert!(signature_trace.accepted);

                let public = test_public_input(
                    &transcript,
                    &fixture.issuer_pk,
                    &revocation_pk,
                    "rp-local-demo-wrong-revocation-id",
                );
                let revocation_range = MdocRevocationRangeWitness {
                    id: wrong_id,
                    id_lo: wrong_id_lo,
                    id_hi: wrong_id_hi,
                };

                let proof = prove_mdoc_ts13_demo_circuit(
                    &extracted,
                    &public,
                    revocation_range,
                    MdocRevocationSignature(signature),
                )
                .expect("the changed revocation inputs build an adversarial proof");
                let error = verify_mdoc_ts13_demo_circuit(&proof, &public)
                    .expect_err("the wrong MSO-derived revocation ID must fail");
                assert!(matches!(error, Error::Verify(_)));
            })
            .expect("large-stack revocation test thread starts")
            .join()
            .expect("large-stack revocation test thread succeeds");
    }

    #[test]
    fn composed_revocation_endpoint_equalities_fail_air_verification() {
        std::thread::Builder::new()
            .name("ts13-revocation-endpoint-test".to_string())
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let transcript = openid4vp_session_transcript(b"ts13-revocation-endpoints");
                let fixture =
                    crate::mldsa_test_fixture::mldsa_ts13_credential_a_with_transcript(&transcript);
                let request = MdocPidRequest::age_over_18(transcript.clone());
                let extracted =
                    extract_pid_mdoc(&fixture.document, &request).expect("credential extracts");
                let id = crate::ts13::ts13_mso_derived_revocation_id(&fixture.mso);
                let below = id.checked_sub(1).expect("fixture revocation ID is nonzero");
                let above = id
                    .checked_add(1)
                    .expect("fixture revocation ID is not the maximum");
                let public = test_public_input(
                    &transcript,
                    &fixture.issuer_pk,
                    &fixture.revocation_pk,
                    "rp-local-demo-revocation-endpoints",
                );

                let prove_range = |id_lo,
                                   id_hi,
                                   attack: Option<RevocationEndpointAttack>,
                                   label: &str| {
                    let (revocation_pk, signature) =
                        crate::mldsa_test_fixture::mldsa_revocation_fixture(
                            id_lo,
                            id_hi,
                            TEST_REVOCATION_EPOCH,
                        );
                    assert_eq!(revocation_pk, fixture.revocation_pk, "{label}");
                    let signed_message =
                        crate::ts13::ts13_revocation_message(id_lo, id_hi, TEST_REVOCATION_EPOCH);
                    let signature_trace = stwo_mldsa::verify_internals(
                        stwo_mldsa::profile::ML_DSA_65,
                        &revocation_pk,
                        &signed_message,
                        &signature,
                    )
                    .expect("revocation signature decodes");
                    assert!(signature_trace.accepted, "{label}");
                    let _attack = attack.map(install_revocation_endpoint_attack);
                    prove_mdoc_ts13_demo_circuit(
                        &extracted,
                        &public,
                        MdocRevocationRangeWitness { id, id_lo, id_hi },
                        MdocRevocationSignature(signature),
                    )
                    .unwrap_or_else(|error| panic!("{label} proof generation failed: {error:?}"))
                };

                let control = prove_range(below, above, None, "strict control");
                verify_mdoc_ts13_demo_circuit(&control, &public)
                    .expect("strict revocation interval verifies");

                for (label, id_lo, id_hi, attack) in [
                    (
                        "lower endpoint equality",
                        id,
                        above,
                        RevocationEndpointAttack::Lower,
                    ),
                    (
                        "upper endpoint equality",
                        below,
                        id,
                        RevocationEndpointAttack::Upper,
                    ),
                ] {
                    let proof = prove_range(id_lo, id_hi, Some(attack), label);
                    match verify_mdoc_ts13_demo_circuit(&proof, &public)
                        .expect_err("endpoint equality must fail AIR verification")
                    {
                        Error::Verify(message) => {
                            assert!(message.starts_with("Stark("), "{label}: {message}")
                        }
                        error => panic!("{label}: expected a STARK error, got {error:?}"),
                    }
                }
            })
            .expect("large-stack revocation endpoint test thread starts")
            .join()
            .expect("large-stack revocation endpoint test thread succeeds");
    }

    #[test]
    fn issuer_signed_item_parser_errors_preserve_token_and_absolute_offset() {
        let outer = map_private_item_prove_error(MdocPrivateItemError::OuterParser(
            crate::mdoc_cbor_stream::MdocCborStreamError::NonMinimalArgument {
                index: 7,
                argument: 23,
            },
        ));
        assert!(matches!(
            outer,
            Error::Mdoc(MdocError::IssuerSignedItemNotCanonical {
                offset: 7,
                reason: MdocIssuerSignedItemCanonicalityReason::NonMinimalArgument { argument: 23 }
            })
        ));

        let inner = map_private_item_prove_error(MdocPrivateItemError::InnerParser(
            crate::mdoc_cbor_stream::MdocCborStreamError::InvalidAdditionalInfo {
                index: 3,
                additional: 31,
            },
        ));
        assert!(matches!(
            inner,
            Error::Mdoc(MdocError::IssuerSignedItemNotCanonical {
                offset: 7,
                reason: MdocIssuerSignedItemCanonicalityReason::InvalidAdditionalInfo {
                    additional: 31
                }
            })
        ));
    }

    #[test]
    fn tag24_wrapper_errors_map_to_public_token_and_offset_reasons() {
        let cases = [
            (
                0,
                MdocPrivateTag24WrapperReason::ExpectedTag24,
                MdocIssuerSignedItemCanonicalityReason::ExpectedTag24,
            ),
            (
                2,
                MdocPrivateTag24WrapperReason::ExpectedByteString,
                MdocIssuerSignedItemCanonicalityReason::ExpectedTag24ByteString,
            ),
            (
                2,
                MdocPrivateTag24WrapperReason::ExpectedU8ByteStringLength { additional: 25 },
                MdocIssuerSignedItemCanonicalityReason::ExpectedTag24ByteStringU8Length {
                    additional: 25,
                },
            ),
            (
                3,
                MdocPrivateTag24WrapperReason::TruncatedToken { needed: 1 },
                MdocIssuerSignedItemCanonicalityReason::TruncatedToken { needed: 1 },
            ),
            (
                3,
                MdocPrivateTag24WrapperReason::ByteStringLengthMismatch {
                    declared: 12,
                    actual: 11,
                },
                MdocIssuerSignedItemCanonicalityReason::Tag24ByteStringLengthMismatch {
                    declared: 12,
                    actual: 11,
                },
            ),
        ];

        for (expected_offset, private_reason, expected_reason) in cases {
            let mapped = map_private_item_prove_error(MdocPrivateItemError::InvalidTag24Wrapper {
                offset: expected_offset,
                reason: private_reason,
            });
            let Error::Mdoc(MdocError::IssuerSignedItemNotCanonical { offset, reason }) = mapped
            else {
                panic!("wrapper error did not map to the public typed error");
            };
            assert_eq!(offset, expected_offset);
            assert_eq!(reason, expected_reason);
        }
    }

    #[test]
    fn value_digests_canonicality_maps_to_public_offset_and_reason() {
        let mapped =
            map_value_digests_prove_error(MdocValueDigestsScanError::MsoValueDigestsNotCanonical {
                offset: 73,
                reason: MdocMsoValueDigestsCanonicalityReason::Truncated("digest bytes"),
            });
        assert!(matches!(
            mapped,
            Error::Mdoc(MdocError::MsoValueDigestsNotCanonical {
                offset: 73,
                reason: MdocMsoValueDigestsCanonicalityReason::Truncated("digest bytes"),
            })
        ));
    }

    #[test]
    fn revocation_range_uses_the_fixed_private_digest_geometry() {
        let zero = QM31::from(M31::from_u32_unchecked(0));
        let module = MdocRevocationRangeBind::verifier(
            SharedDigestRelation::new(),
            17,
            SharedFieldRelation::new(),
            MdocRevocationRangeInteractionClaim {
                claimed_sum: zero,
                blinder_v: zero,
                blinder_m: zero,
                blinder_claimed_sum: zero,
            },
        );
        let layout = module.layout();

        assert_eq!(revocation_range_trace_cols(), 336);
        assert_eq!(layout.preprocessed, vec![MDOC_REVOCATION_RANGE_LOG_SIZE]);
        assert_eq!(
            layout.trace,
            vec![MDOC_REVOCATION_RANGE_LOG_SIZE; revocation_range_trace_cols()]
        );
        assert_eq!(
            layout.interaction,
            vec![MDOC_REVOCATION_RANGE_LOG_SIZE; 12 * SECURE_EXTENSION_DEGREE]
        );
    }

    #[test]
    fn sha_profile_uses_30_mso_blocks_at_log_11() {
        const BLOCK_BYTES: usize = stwo_sha256::constants::BLOCK_BYTES;
        const MSO_BLOCKS: usize = 30;
        const ITEM_BLOCKS: usize = 2;
        const ITEM_PADDED_BYTES: usize = TS13_DEMO_ITEM_PADDED_BYTES as usize;
        const EXPECTED_MSO_CELLS: usize = 619_600;
        const EXPECTED_ITEM_CELLS: usize = 78_416;
        const EXPECTED_SHARED_TABLE_CELLS: usize = 4_128;
        const EXPECTED_TOTAL_CELLS: usize = 702_144;
        const _: () = assert!(EXPECTED_TOTAL_CELLS <= 1_500_000);

        let mso_bytes = vec![0u8; TS13_DEMO_MSO_PAYLOAD_BYTES];
        let mso_witness = compute_sha256_witness(&mso_bytes);
        assert_eq!(mso_witness.padding.padded.len(), MSO_BLOCKS * BLOCK_BYTES);
        assert_eq!(mso_witness.blocks.len(), MSO_BLOCKS);
        assert_eq!(min_log_size(mso_witness.blocks.len()), 11);
        assert_eq!(MDOC_MSO_SHA_LOG_SIZE, 11);

        let item_bytes = vec![0u8; BLOCK_BYTES];
        let item_witness = compute_sha256_witness(&item_bytes);
        assert_eq!(item_witness.padding.padded.len(), ITEM_PADDED_BYTES);
        assert_eq!(item_witness.blocks.len(), ITEM_BLOCKS);
        assert_eq!(min_log_size(item_witness.blocks.len()), 8);
        assert_eq!(TS13_DEMO_ATTRIBUTE_SHA_LOG_N_ROWS, 8);

        let shared = SharedShaTableRelations::new();
        let mso_sha = Sha256Prover::new(&mso_witness, MDOC_MSO_SHA_LOG_SIZE)
            .with_instance_namespace(MDOC_MSO_SHA_NAMESPACE)
            .with_digest_handle(SharedDigestRelation::new())
            .with_field_handle(
                FieldExposure::from_full_padded_stream(
                    MDOC_MSO_SHA_STREAM_FIELD_ID,
                    mso_witness.padding.padded.len(),
                ),
                SharedFieldRelation::new(),
            )
            .with_shared_tables(shared.clone());
        let item_sha = Sha256Prover::new(&item_witness, TS13_DEMO_ATTRIBUTE_SHA_LOG_N_ROWS)
            .with_instance_namespace(MDOC_ATTRIBUTE_SHA_NAMESPACE)
            .with_digest_handle(SharedDigestRelation::new())
            .with_field_handle(attribute_exposure(), SharedFieldRelation::new())
            .with_shared_tables(shared.clone());
        let tables = ShaTablesProver::new(
            ShaTableMultiplicities::from_consumers(&[&item_witness, &mso_witness]),
            shared,
        );

        let mso_layout = mso_sha.layout();
        assert_eq!(mso_layout.preprocessed, [vec![11; 10], vec![4]].concat());
        assert_eq!(mso_layout.trace, [vec![11; 260], vec![4; 32]].concat());
        assert_eq!(mso_layout.interaction, [vec![11; 32], vec![4; 36]].concat());
        assert_eq!(committed_cells(&mso_layout), EXPECTED_MSO_CELLS);

        let item_cells = committed_cells(&item_sha.layout());
        let table_cells = committed_cells(&tables.layout());
        assert_eq!(item_cells, EXPECTED_ITEM_CELLS);
        assert_eq!(table_cells, EXPECTED_SHARED_TABLE_CELLS);
        let total_cells = committed_cells(&mso_layout) + item_cells + table_cells;
        assert_eq!(total_cells, EXPECTED_TOTAL_CELLS);
        assert!(total_cells <= 1_500_000);
    }
}
