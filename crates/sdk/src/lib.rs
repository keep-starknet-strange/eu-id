//! ML-DSA EU-ID ZK SDK, exposed to Kotlin and Swift through UniFFI.
//!
//! [`prove_identity`] accepts a CBOR PID mdoc plus ML-DSA issuer trust pins and
//! returns a compressed proof envelope. [`verify_identity`] binds that envelope
//! to the verifier's request and verifies the same mdoc proof.

use std::io::{Read, Write};

use bincode::Options;
use bzip2::read::BzDecoder;
use bzip2::write::BzEncoder;
use bzip2::Compression;
use ciborium::value::Value;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

uniffi::setup_scaffolding!();

#[cfg(feature = "demo")]
mod demo;
mod mapping;

#[derive(uniffi::Enum, Clone, Copy, Debug, PartialEq, Eq)]
pub enum PredicateMode {
    Age,
    Nat,
    And,
    Or,
}

impl PredicateMode {
    fn as_token(self) -> &'static str {
        match self {
            Self::Age => "age",
            Self::Nat => "nat",
            Self::And => "and",
            Self::Or => "or",
        }
    }

    fn from_token(token: &str) -> Option<Self> {
        match token {
            "age" => Some(Self::Age),
            "nat" => Some(Self::Nat),
            "and" => Some(Self::And),
            "or" => Some(Self::Or),
            _ => None,
        }
    }

    fn uses_age(self) -> bool {
        matches!(self, Self::Age | Self::And | Self::Or)
    }

    fn uses_nat(self) -> bool {
        matches!(self, Self::Nat | Self::And | Self::Or)
    }
}

#[derive(uniffi::Enum, Clone, Copy, Debug, PartialEq, Eq)]
pub enum NatMode {
    Any,
}

impl NatMode {
    fn as_token(self) -> &'static str {
        match self {
            Self::Any => "any",
        }
    }
}

#[derive(uniffi::Record, Clone, Debug)]
pub struct ZkContract {
    pub system_name: String,
    pub spec_id_pid: String,
    pub pid_namespace: String,
    pub doctype_pid: String,
    pub element_birth_date: String,
    pub element_nationality: String,
    pub param_predicate_mode: String,
    pub param_min_age: String,
    pub param_accepted_countries: String,
    pub param_nat_mode: String,
    pub param_version: String,
    pub param_num_attributes: String,
    pub param_circuit_hash: String,
    pub result_nat_in_set: String,
}

const TS13_SYSTEM_ID: &str = "stwo-euid-v1";
const TS13_LONGFELLOW_SYSTEM_ID: &str = "longfellow-libzk-v1";
const TS13_CREDENTIAL_FORMAT: &str = "mso_mdoc_zk";
const TS13_UNSUPPORTED_JWT_FORMAT: &str = "zk-jwt";
const TS13_DEVICE_AUTH_PROFILE: &str = "iso18013-5";
const TS13_PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const TS13_PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const TS13_MAX_MSO_PAYLOAD_BYTES: u32 = eu_id_prover::ts13::TS13_MAX_MSO_PAYLOAD_BYTES as u32;
const TS13_NUM_ATTRIBUTES: u32 = 1;
const TS13_MAX_ATTRIBUTE_BYTES: u32 = 32;
const TS13_MAX_ATTRIBUTE_ITEM_BYTES: u32 = eu_id_prover::ts13::TS13_MAX_ATTRIBUTE_ITEM_BYTES as u32;
const TS13_MAX_REQUESTED_DIGEST_ID: u32 = eu_id_prover::ts13::TS13_MAX_REQUESTED_DIGEST_ID;
const TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES: u32 =
    eu_id_prover::ts13::TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES as u32;
const TS13_MAX_DEVICE_MLDSA_MESSAGE_BYTES: u32 =
    eu_id_prover::ts13::TS13_MAX_DEVICE_MLDSA_MESSAGE_BYTES as u32;
const TS13_MAX_SESSION_TRANSCRIPT_BYTES: usize = TS13_MAX_DEVICE_MLDSA_MESSAGE_BYTES as usize;
const TS13_MERGED_SHA_SLOT_LOG: u32 = eu_id_prover::ts13::TS13_MERGED_SHA_SLOT_LOG;
const TS13_MERGED_SHA_LOG_N_ROWS: u32 = eu_id_prover::ts13::TS13_MERGED_SHA_LOG_N_ROWS;
const TS13_POTENTIAL_ISSUERS: u32 = 1;
const TS13_REVOCATION_ENABLED: bool = true;
const TS13_REVOCATION_ID_WIDTH_BYTES: u32 = 8;
const ML_DSA_65_PUBLIC_KEY_BYTES: usize = 1_952;
/// Deliberately independent from the product SDK envelope versions. A TS13
/// verifier never accepts a ProductDefault proof as an equality+revocation
/// presentation, or vice versa.
const TS13_ENVELOPE_FORMAT_V2: u16 = 2;

#[derive(uniffi::Enum, Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Ts13DisclosureKind {
    Equality,
    Extension,
}

#[derive(uniffi::Record, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Ts13PresentationRequest {
    pub credential_format: String,
    pub zk_system_id: String,
    pub doctype: String,
    pub namespace: String,
    pub circuit_hash: String,
    pub num_attributes: u32,
    pub max_mso_payload_bytes: u32,
    pub max_attribute_bytes: u32,
    pub max_attribute_item_bytes: u32,
    pub max_requested_digest_id: u32,
    pub max_issuer_mldsa_message_bytes: u32,
    pub max_device_mldsa_message_bytes: u32,
    pub merged_sha_slot_log: u32,
    pub merged_sha_log_n_rows: u32,
    pub potential_issuers: u32,
    pub revocation_enabled: bool,
    pub revocation_id_width_bytes: u32,
    pub device_auth_profile: String,
    pub current_date_epoch_day: i32,
    pub session_transcript: Vec<u8>,
    pub trusted_issuer_hashes: Vec<String>,
    /// FIPS 204 ML-DSA-65 `pkEncode` bytes.
    pub revocation_public_key: Vec<u8>,
    pub revocation_epoch: u32,
}

#[derive(uniffi::Record, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Ts13DisclosedAttribute {
    pub namespace: String,
    pub name: String,
    pub value_cbor: Vec<u8>,
    pub disclosure: Ts13DisclosureKind,
}

#[derive(uniffi::Record, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Ts13ZkDocument {
    pub doc_type: String,
    pub zk_system_id: String,
    pub circuit_hash: String,
    pub request_binding_hash: String,
    pub disclosed_attributes: Vec<Ts13DisclosedAttribute>,
    pub proof: Vec<u8>,
}

/// Prover-only inputs for the TS13 equality profile. The revocation bounds are
/// private and are intentionally not copied into [`Ts13ZkDocument`] or its
/// serialized verifier envelope.
#[derive(uniffi::Record, Clone, Debug)]
pub struct Ts13MdocWitness {
    pub document: Vec<u8>,
    pub trusted_issuer_public_keys: Vec<Vec<u8>>,
    pub revocation_id_lo: u64,
    pub revocation_id_hi: u64,
    pub revocation_signature: Vec<u8>,
}

#[derive(uniffi::Enum, Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MdocRequestProfile {
    ProductDefault,
    Ts13AgeOver18Equality,
}

#[uniffi::export]
pub fn zk_contract_v1() -> ZkContract {
    ZkContract {
        system_name: "stwo-euid-v1".to_string(),
        spec_id_pid: "stwo-euid-pid-v1".to_string(),
        pid_namespace: TS13_PID_NAMESPACE.to_string(),
        doctype_pid: TS13_PID_DOCTYPE.to_string(),
        element_birth_date: "birth_date".to_string(),
        element_nationality: "nationality".to_string(),
        param_predicate_mode: "predicate_mode".to_string(),
        param_min_age: "min_age".to_string(),
        param_accepted_countries: "accepted_countries".to_string(),
        param_nat_mode: "nat_mode".to_string(),
        param_version: "version".to_string(),
        param_num_attributes: "num_attributes".to_string(),
        param_circuit_hash: "circuit_hash".to_string(),
        result_nat_in_set: "nationality_in_set".to_string(),
    }
}

fn hex_sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn cbor_bytes(value: Value) -> Vec<u8> {
    let mut out = Vec::new();
    ciborium::ser::into_writer(&value, &mut out)
        .expect("CBOR serialization of TS13 metadata is infallible");
    out
}

fn ts13_tuple_value(request: &Ts13PresentationRequest) -> Value {
    Value::Map(vec![
        ("system".into(), request.zk_system_id.as_str().into()),
        (
            "credential_format".into(),
            request.credential_format.as_str().into(),
        ),
        ("doctype".into(), request.doctype.as_str().into()),
        ("namespace".into(), request.namespace.as_str().into()),
        ("num_attributes".into(), Value::from(request.num_attributes)),
        (
            "max_mso_payload_bytes".into(),
            Value::from(request.max_mso_payload_bytes),
        ),
        (
            "max_attribute_bytes".into(),
            Value::from(request.max_attribute_bytes),
        ),
        (
            "max_attribute_item_bytes".into(),
            Value::from(request.max_attribute_item_bytes),
        ),
        (
            "max_requested_digest_id".into(),
            Value::from(request.max_requested_digest_id),
        ),
        (
            "max_issuer_mldsa_message_bytes".into(),
            Value::from(request.max_issuer_mldsa_message_bytes),
        ),
        (
            "max_device_mldsa_message_bytes".into(),
            Value::from(request.max_device_mldsa_message_bytes),
        ),
        (
            "merged_sha_slot_log".into(),
            Value::from(request.merged_sha_slot_log),
        ),
        (
            "merged_sha_log_n_rows".into(),
            Value::from(request.merged_sha_log_n_rows),
        ),
        (
            "potential_issuers".into(),
            Value::from(request.potential_issuers),
        ),
        (
            "revocation_enabled".into(),
            Value::Bool(request.revocation_enabled),
        ),
        (
            "revocation_id_width_bytes".into(),
            Value::from(request.revocation_id_width_bytes),
        ),
        (
            "device_auth_profile".into(),
            request.device_auth_profile.as_str().into(),
        ),
    ])
}

fn ts13_request_binding_hash(request: &Ts13PresentationRequest) -> String {
    let value = Value::Map(vec![
        ("tuple".into(), ts13_tuple_value(request)),
        ("circuit_hash".into(), request.circuit_hash.as_str().into()),
        (
            "current_date_epoch_day".into(),
            Value::from(request.current_date_epoch_day),
        ),
        (
            "session_transcript".into(),
            Value::Bytes(request.session_transcript.clone()),
        ),
        (
            "trusted_issuer_hashes".into(),
            Value::Array(
                request
                    .trusted_issuer_hashes
                    .iter()
                    .map(|hash| hash.as_str().into())
                    .collect(),
            ),
        ),
        (
            "revocation_public_key".into(),
            Value::Bytes(request.revocation_public_key.clone()),
        ),
        (
            "revocation_epoch".into(),
            Value::from(request.revocation_epoch),
        ),
    ]);
    hex_sha256(&cbor_bytes(value))
}

#[uniffi::export]
pub fn ts13_default_circuit_hash() -> String {
    eu_id_prover::ts13::ts13_default_circuit_hash()
}

fn ts13_tuple_is_supported(request: &Ts13PresentationRequest) -> bool {
    request.doctype == TS13_PID_DOCTYPE
        && request.namespace == TS13_PID_NAMESPACE
        && request.num_attributes == TS13_NUM_ATTRIBUTES
        && request.max_mso_payload_bytes == TS13_MAX_MSO_PAYLOAD_BYTES
        && request.max_attribute_bytes == TS13_MAX_ATTRIBUTE_BYTES
        && request.max_attribute_item_bytes == TS13_MAX_ATTRIBUTE_ITEM_BYTES
        && request.max_requested_digest_id == TS13_MAX_REQUESTED_DIGEST_ID
        && request.max_issuer_mldsa_message_bytes == TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES
        && request.max_device_mldsa_message_bytes == TS13_MAX_DEVICE_MLDSA_MESSAGE_BYTES
        && request.merged_sha_slot_log == TS13_MERGED_SHA_SLOT_LOG
        && request.merged_sha_log_n_rows == TS13_MERGED_SHA_LOG_N_ROWS
        && request.potential_issuers == TS13_POTENTIAL_ISSUERS
        && request.revocation_enabled == TS13_REVOCATION_ENABLED
        && request.revocation_id_width_bytes == TS13_REVOCATION_ID_WIDTH_BYTES
        && request.device_auth_profile == TS13_DEVICE_AUTH_PROFILE
}

fn is_lower_hex_sha256(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

#[uniffi::export]
pub fn ts13_validate_presentation_request(
    request: &Ts13PresentationRequest,
) -> Result<(), ZkError> {
    if request.credential_format == TS13_UNSUPPORTED_JWT_FORMAT {
        return Err(ZkError::InvalidInput(
            "unsupported zk-jwt TS13 credential format".to_string(),
        ));
    }
    if request.credential_format != TS13_CREDENTIAL_FORMAT {
        return Err(ZkError::InvalidInput(format!(
            "unsupported TS13 credential format: {}",
            request.credential_format
        )));
    }
    if request.zk_system_id != TS13_SYSTEM_ID {
        let message = if request.zk_system_id == TS13_LONGFELLOW_SYSTEM_ID {
            "unsupported system: longfellow-libzk-v1 is libzk-only".to_string()
        } else {
            format!("unsupported zkSystemId: {}", request.zk_system_id)
        };
        return Err(ZkError::InvalidInput(message));
    }
    if !ts13_tuple_is_supported(request) {
        return Err(ZkError::InvalidInput(
            "unsupported TS13 tuple; no circuit_hash lookup entry".to_string(),
        ));
    }
    if request.circuit_hash != ts13_default_circuit_hash() {
        return Err(ZkError::InvalidInput(format!(
            "unknown circuit_hash: {}",
            request.circuit_hash
        )));
    }
    if request.trusted_issuer_hashes.len() != request.potential_issuers as usize
        || request
            .trusted_issuer_hashes
            .iter()
            .any(|hash| !is_lower_hex_sha256(hash))
    {
        return Err(ZkError::InvalidInput(
            "trusted issuer set does not match TS13 tuple".to_string(),
        ));
    }
    if request.revocation_public_key.len() != ML_DSA_65_PUBLIC_KEY_BYTES {
        return Err(ZkError::InvalidInput(format!(
            "ML-DSA-65 revocation public key must be {ML_DSA_65_PUBLIC_KEY_BYTES} bytes"
        )));
    }
    if request.session_transcript.len() > TS13_MAX_SESSION_TRANSCRIPT_BYTES {
        return Err(ZkError::InvalidInput(format!(
            "TS13 session transcript exceeds {TS13_MAX_SESSION_TRANSCRIPT_BYTES} bytes"
        )));
    }
    Ok(())
}

#[uniffi::export]
pub fn ts13_build_zk_document(
    request: Ts13PresentationRequest,
    disclosed_attributes: Vec<Ts13DisclosedAttribute>,
    proof: Vec<u8>,
) -> Result<Ts13ZkDocument, ZkError> {
    ts13_validate_presentation_request(&request)?;
    Ok(Ts13ZkDocument {
        doc_type: request.doctype.clone(),
        zk_system_id: request.zk_system_id.clone(),
        circuit_hash: request.circuit_hash.clone(),
        request_binding_hash: ts13_request_binding_hash(&request),
        disclosed_attributes,
        proof,
    })
}

#[derive(Serialize, Deserialize)]
struct Ts13ProofEnvelope {
    envelope_format: u16,
    request_binding_hash: String,
    mdoc_statement: eu_id_prover::MdocTs13Statement,
    stark_proof: Vec<u8>,
}

fn canonical_ts13_disclosures() -> Vec<Ts13DisclosedAttribute> {
    vec![Ts13DisclosedAttribute {
        namespace: TS13_PID_NAMESPACE.to_string(),
        name: result_age_over(18),
        value_cbor: cbor_bytes(Value::Bool(true)),
        disclosure: Ts13DisclosureKind::Equality,
    }]
}

fn ts13_policy(request: &Ts13PresentationRequest) -> Result<eu_id_prover::Policy, ZkError> {
    Ok(eu_id_prover::Policy {
        current_date: mapping::epoch_day_to_date(request.current_date_epoch_day)?,
        min_age_years: 0,
        accepted_nationalities: Vec::new(),
        accepted_nationalities_alpha2: Vec::new(),
    })
}

fn ts13_mdoc_request(
    request: &Ts13PresentationRequest,
    witness: &Ts13MdocWitness,
) -> eu_id_prover::MdocPidRequest {
    eu_id_prover::MdocPidRequest {
        doctype: request.doctype.clone(),
        namespace: request.namespace.clone(),
        attributes: expected_mdoc_attributes_for_profile(MdocRequestProfile::Ts13AgeOver18Equality),
        birth_date_element: zk_contract_v1().element_birth_date,
        nationality_element: zk_contract_v1().element_nationality,
        session_transcript: request.session_transcript.clone(),
        trusted_mldsa_issuer_public_keys: witness.trusted_issuer_public_keys.clone(),
        device_authentication_profile:
            eu_id_prover::mdoc::MdocDeviceAuthenticationProfile::Iso180135,
    }
}

fn decode_ts13_proof_envelope(proof: &[u8]) -> Result<Ts13ProofEnvelope, ZkError> {
    if proof.len() > MAX_MDOC_ENVELOPE_BYTES {
        return Err(ZkError::Verify(
            "TS13 proof envelope exceeds size limit".to_string(),
        ));
    }
    // Peek only the leading `envelope_format` field: allow trailing bytes here
    // (the rest of the envelope follows it). The full decode below still pins
    // exact consumption via `reject_trailing_bytes`.
    let envelope_format: u16 = bounded_bincode_options(MAX_MDOC_ENVELOPE_BYTES)
        .allow_trailing_bytes()
        .deserialize(proof)
        .map_err(|_| ZkError::Verify("unsupported TS13 envelope format".to_string()))?;
    if envelope_format != TS13_ENVELOPE_FORMAT_V2 {
        return Err(ZkError::Verify(
            "unsupported TS13 envelope format".to_string(),
        ));
    }
    let envelope: Ts13ProofEnvelope = bounded_bincode_options(MAX_MDOC_ENVELOPE_BYTES)
        .reject_trailing_bytes()
        .deserialize(proof)
        .map_err(|_| ZkError::Verify("invalid TS13 proof envelope".to_string()))?;
    if envelope.stark_proof.len() > MAX_COMPRESSED_STARK_PROOF_BYTES {
        return Err(ZkError::Verify(
            "compressed TS13 STARK proof exceeds size limit".to_string(),
        ));
    }
    Ok(envelope)
}

fn ts13_mdoc_statement_matches(
    request: &Ts13PresentationRequest,
    statement: &eu_id_prover::MdocTs13Statement,
) -> Result<bool, ZkError> {
    let expected_attributes =
        expected_mdoc_attributes_for_profile(MdocRequestProfile::Ts13AgeOver18Equality);
    if statement.doctype != request.doctype
        || statement.namespace != request.namespace
        || statement.policy != ts13_policy(request)?
        || statement.requested_digest_id > TS13_MAX_REQUESTED_DIGEST_ID
        || !eu_id_prover::ts13::ts13_requested_item_padded_len_is_supported(
            statement.requested_item_padded_len,
        )
        || statement.attributes.len() != expected_attributes.len()
        || statement
            .attributes
            .iter()
            .zip(expected_attributes.iter())
            .any(|(attribute, expected)| {
                attribute.element_identifier != expected.element_identifier
                    || attribute.mode != expected.mode
            })
    {
        return Ok(false);
    }
    if !request
        .trusted_issuer_hashes
        .iter()
        .any(|trusted| trusted == &hex_sha256(&statement.issuer.public_key))
    {
        return Ok(false);
    }
    let expected_device_hash = eu_id_prover::mdoc::device_authentication_sig_structure_hash(
        &request.session_transcript,
        &request.doctype,
    )
    .map_err(|error| {
        ZkError::InvalidInput(format!(
            "invalid TS13 DeviceAuthentication input: {error:?}"
        ))
    })?;
    if <[u8; 32]>::from(Sha256::digest(&statement.device.message)) != expected_device_hash {
        return Ok(false);
    }
    Ok(statement.revocation.epoch == request.revocation_epoch
        && matches!(
            &statement.revocation.revocation_public_key,
            eu_id_prover::mdoc::MdocRevocationKey::MlDsa(key)
                if key == &request.revocation_public_key
        ))
}

/// Create the dedicated TS13 equality-and-revocation proof envelope.  This
/// does not share the product `prove_identity` request profile or envelope.
#[uniffi::export]
pub fn ts13_prove_zk_document(
    request: Ts13PresentationRequest,
    witness: Ts13MdocWitness,
) -> Result<Ts13ZkDocument, ZkError> {
    ts13_validate_presentation_request(&request)?;
    if witness.trusted_issuer_public_keys.len() != request.potential_issuers as usize
        || witness.trusted_issuer_public_keys.iter().any(|key| {
            key.len() != ML_DSA_65_PUBLIC_KEY_BYTES
                || !request
                    .trusted_issuer_hashes
                    .iter()
                    .any(|trusted| trusted == &hex_sha256(key))
        })
    {
        return Err(ZkError::InvalidInput(
            "TS13 witness issuer keys do not match trusted issuer hashes".to_string(),
        ));
    }
    on_large_stack(move || {
        let policy = ts13_policy(&request)?;
        let mdoc_request = ts13_mdoc_request(&request, &witness);
        let (proof, mdoc_statement) = eu_id_prover::prove_mdoc_with_ts13_revocation(
            &witness.document,
            &mdoc_request,
            policy,
            eu_id_prover::mdoc::MdocRevocationPublicInputs {
                revocation_public_key: eu_id_prover::mdoc::MdocRevocationKey::MlDsa(
                    request.revocation_public_key.clone(),
                ),
                epoch: request.revocation_epoch,
            },
            witness.revocation_id_lo,
            witness.revocation_id_hi,
            eu_id_prover::mdoc::MdocRevocationSignature::MlDsa(
                witness.revocation_signature.clone(),
            ),
        )
        .map_err(map_prover_error)?;
        let stark_proof = bincode::serialize(&proof)
            .map_err(|error| {
                ZkError::Prove(format!("failed to serialize TS13 mdoc proof: {error}"))
            })
            .and_then(|bytes| compress_stark_proof_for_ffi(&bytes))?;
        let request_binding_hash = ts13_request_binding_hash(&request);
        let proof = bincode::serialize(&Ts13ProofEnvelope {
            envelope_format: TS13_ENVELOPE_FORMAT_V2,
            request_binding_hash: request_binding_hash.clone(),
            mdoc_statement,
            stark_proof,
        })
        .map_err(|error| {
            ZkError::Prove(format!("failed to serialize TS13 proof envelope: {error}"))
        })?;
        Ok(Ts13ZkDocument {
            doc_type: request.doctype.clone(),
            zk_system_id: request.zk_system_id.clone(),
            circuit_hash: request.circuit_hash.clone(),
            request_binding_hash,
            disclosed_attributes: canonical_ts13_disclosures(),
            proof,
        })
    })
}

#[uniffi::export]
pub fn ts13_verify_zk_document(
    request: &Ts13PresentationRequest,
    document: &Ts13ZkDocument,
) -> Result<bool, ZkError> {
    if ts13_validate_presentation_request(request).is_err()
        || document.proof.len() > MAX_MDOC_ENVELOPE_BYTES
    {
        return Ok(false);
    }
    if document.doc_type != request.doctype
        || document.zk_system_id != request.zk_system_id
        || document.circuit_hash != request.circuit_hash
        || document.request_binding_hash != ts13_request_binding_hash(request)
        || document.disclosed_attributes != canonical_ts13_disclosures()
    {
        return Ok(false);
    }

    // All caller-controlled variable-length fields are bounded or equal to
    // canonical constants before they are copied onto the large-stack worker.
    let request = request.clone();
    let document = document.clone();
    on_large_stack(move || {
        let Ok(envelope) = decode_ts13_proof_envelope(&document.proof) else {
            return Ok(false);
        };
        if envelope.request_binding_hash != document.request_binding_hash
            || !ts13_mdoc_statement_matches(&request, &envelope.mdoc_statement)?
        {
            return Ok(false);
        }
        let Some(stark_proof) = decompress_stark_proof_from_ffi(&envelope.stark_proof)
            .ok()
            .and_then(|bytes| decode_stark_proof(&bytes))
        else {
            return Ok(false);
        };
        Ok(eu_id_prover::ts13::verify_ts13_age_over_18_circuit(
            &stark_proof,
            &envelope.mdoc_statement,
        )
        .is_ok())
    })
}

pub fn ts13_disclosure_kind(
    attribute: &eu_id_prover::mdoc::MdocRequestedAttribute,
) -> Ts13DisclosureKind {
    match attribute.mode {
        eu_id_prover::mdoc::MdocDisclosureMode::ValueEquality(_) => Ts13DisclosureKind::Equality,
        eu_id_prover::mdoc::MdocDisclosureMode::AgeOver
        | eu_id_prover::mdoc::MdocDisclosureMode::Alpha2Set => Ts13DisclosureKind::Extension,
    }
}

#[uniffi::export]
pub fn sdk_version() -> String {
    env!("CARGO_PKG_VERSION").to_string()
}

#[uniffi::export]
pub fn result_age_over(min_age: u32) -> String {
    format!("age_over_{min_age}")
}

#[uniffi::export]
pub fn predicate_mode_from_token(token: String) -> Option<PredicateMode> {
    PredicateMode::from_token(&token)
}

#[uniffi::export]
pub fn predicate_mode_token(mode: PredicateMode) -> String {
    mode.as_token().to_string()
}

#[uniffi::export]
pub fn predicate_mode_uses_age(mode: PredicateMode) -> bool {
    mode.uses_age()
}

#[uniffi::export]
pub fn predicate_mode_uses_nat(mode: PredicateMode) -> bool {
    mode.uses_nat()
}

#[uniffi::export]
pub fn nat_mode_token(mode: NatMode) -> String {
    mode.as_token().to_string()
}

#[uniffi::export]
pub fn iso_alpha2_to_numeric(alpha2: String) -> Option<u32> {
    celes::Country::from_alpha2(alpha2)
        .ok()
        .map(|country| country.value as u32)
}

/// Which ZK identity system this SDK build implements. Mirrors the linked prover
/// backend (see [`zk_system`]); lets callers pick the right [`IssuerKey`] /
/// [`TrustedIssuers`] variant without a build flag of their own.
#[derive(uniffi::Enum, Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkSystemKind {
    P256,
    MlDsa,
}

/// Issuer trust anchor pinned in a [`ZkPublicStatement`]: P-256 carries the EC
/// public-key coordinates; ML-DSA carries the SHA-256 of the issuer `pkEncode`.
/// The type is identical on both branches; each build only accepts its own variant.
#[derive(uniffi::Enum, Clone, Debug, PartialEq, Eq)]
pub enum IssuerKey {
    P256 { x: Vec<u8>, y: Vec<u8> },
    MlDsa { pk_hash: Vec<u8> },
}

/// Trusted issuers accepted by the prover: P-256 accepts x5chain root
/// certificates; ML-DSA (no PKI) pins raw `pkEncode` values.
#[derive(uniffi::Enum, Clone, Debug)]
pub enum TrustedIssuers {
    Certificates(Vec<Vec<u8>>),
    PublicKeys(Vec<Vec<u8>>),
}

#[derive(uniffi::Record, Clone, Debug, PartialEq, Eq)]
pub struct ZkPublicStatement {
    pub spec_id: String,
    pub version: u32,
    pub doctype: String,
    pub namespace: String,
    /// Issuer trust anchor (P-256 coordinates or ML-DSA `pkEncode` hash).
    pub issuer_key: IssuerKey,
    pub today_epoch_day: i32,
    pub nonce: Vec<u8>,
    pub predicate_mode: PredicateMode,
    pub age_threshold_years: Option<u32>,
    pub accepted_numeric_countries: Option<Vec<u32>>,
    pub nat_mode: NatMode,
}

#[derive(uniffi::Record, Clone, Debug)]
pub struct ZkMdocWitness {
    pub document: Vec<u8>,
    /// Trusted issuers (x5chain certs for P-256, pinned `pkEncode`s for ML-DSA).
    pub trusted_issuers: TrustedIssuers,
}

#[derive(uniffi::Record, Clone, Debug)]
pub struct ZkVerifyResult {
    pub ok: bool,
}

#[derive(uniffi::Error, thiserror::Error, Debug)]
pub enum ZkError {
    #[error("invalid input: {0}")]
    InvalidInput(String),
    #[error("proving failed: {0}")]
    Prove(String),
    #[error("verification failed: {0}")]
    Verify(String),
}

fn validate_product_statement_contract(statement: &ZkPublicStatement) -> Result<(), ZkError> {
    let contract = zk_contract_v1();
    if statement.spec_id != contract.spec_id_pid
        || statement.version != 1
        || statement.doctype != contract.doctype_pid
        || statement.namespace != contract.pid_namespace
    {
        return Err(ZkError::InvalidInput(
            "unsupported product statement contract labels".to_string(),
        ));
    }
    match &statement.issuer_key {
        IssuerKey::MlDsa { pk_hash } => {
            if pk_hash.len() != 32 {
                return Err(ZkError::InvalidInput(
                    "ML-DSA issuer pk_hash must be 32 bytes".to_string(),
                ));
            }
        }
        IssuerKey::P256 { x, y } => {
            if x.len() != 32 || y.len() != 32 {
                return Err(ZkError::InvalidInput(
                    "P-256 issuer key coordinates must be 32 bytes".to_string(),
                ));
            }
        }
    }
    Ok(())
}

fn encode_statement(statement: &ZkPublicStatement) -> Vec<u8> {
    let mut entries: Vec<(Value, Value)> = vec![
        ("v".into(), Value::from(statement.version)),
        ("spec_id".into(), statement.spec_id.as_str().into()),
        ("doctype".into(), statement.doctype.as_str().into()),
        ("namespace".into(), statement.namespace.as_str().into()),
        (
            "issuer_key".into(),
            match &statement.issuer_key {
                IssuerKey::MlDsa { pk_hash } => Value::Map(vec![
                    ("alg".into(), "ML-DSA-65".into()),
                    ("pk_hash".into(), Value::Bytes(pk_hash.clone())),
                ]),
                IssuerKey::P256 { x, y } => Value::Map(vec![
                    ("crv".into(), "P-256".into()),
                    ("x".into(), Value::Bytes(x.clone())),
                    ("y".into(), Value::Bytes(y.clone())),
                ]),
            },
        ),
        ("today".into(), Value::from(statement.today_epoch_day)),
        ("nonce".into(), Value::Bytes(statement.nonce.clone())),
        (
            "predicate_mode".into(),
            statement.predicate_mode.as_token().into(),
        ),
    ];
    if let Some(threshold) = statement.age_threshold_years {
        entries.push((
            "age".into(),
            Value::Map(vec![("threshold_years".into(), Value::from(threshold))]),
        ));
    }
    if let Some(accepted) = &statement.accepted_numeric_countries {
        entries.push((
            "nat".into(),
            Value::Map(vec![
                ("mode".into(), statement.nat_mode.as_token().into()),
                (
                    "accepted".into(),
                    Value::Array(accepted.iter().copied().map(Value::from).collect()),
                ),
            ]),
        ));
    }
    cbor_bytes(Value::Map(entries))
}

#[derive(Serialize, Deserialize)]
struct MdocProofEnvelope {
    envelope_format: u16,
    statement_bytes: Vec<u8>,
    mdoc_statement: eu_id_prover::MdocStatement,
    stark_proof: Vec<u8>,
}

const MDOC_ENVELOPE_FORMAT_V6: u16 = 6;
/// The mobile transport rail is under 1 MiB; this leaves bounded headroom for
/// the public statement and future format framing while rejecting oversized
/// inputs before bincode can allocate from an attacker-controlled length.
const MAX_MDOC_ENVELOPE_BYTES: usize = 1_572_864;
const MAX_COMPRESSED_STARK_PROOF_BYTES: usize = 1_572_864;
const MAX_DECOMPRESSED_STARK_PROOF_BYTES: usize = 16 * 1024 * 1024;

fn bounded_bincode_options(limit: usize) -> impl Options {
    // `bincode::serialize`/`deserialize` use fixed-width integer encoding;
    // retain that wire format while bounding all nested lengths.
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_limit(limit as u64)
}

fn decode_mdoc_proof_envelope(proof: &[u8]) -> Result<MdocProofEnvelope, ZkError> {
    let unsupported = || ZkError::Verify("unsupported envelope format".to_string());
    if proof.len() > MAX_MDOC_ENVELOPE_BYTES {
        return Err(ZkError::Verify(
            "proof envelope exceeds size limit".to_string(),
        ));
    }
    // Peek only the leading `envelope_format` field: allow trailing bytes here
    // (the rest of the envelope follows it). The full decode below still pins
    // exact consumption via `reject_trailing_bytes`.
    let envelope_format: u16 = bounded_bincode_options(MAX_MDOC_ENVELOPE_BYTES)
        .allow_trailing_bytes()
        .deserialize(proof)
        .map_err(|_| unsupported())?;
    if envelope_format != MDOC_ENVELOPE_FORMAT_V6 {
        return Err(unsupported());
    }
    let envelope: MdocProofEnvelope = bounded_bincode_options(MAX_MDOC_ENVELOPE_BYTES)
        .reject_trailing_bytes()
        .deserialize(proof)
        .map_err(|error| ZkError::Verify(format!("invalid proof envelope: {error}")))?;
    debug_assert_eq!(envelope.envelope_format, envelope_format);
    if envelope.stark_proof.len() > MAX_COMPRESSED_STARK_PROOF_BYTES {
        return Err(ZkError::Verify(
            "compressed STARK proof exceeds size limit".to_string(),
        ));
    }
    Ok(envelope)
}

const PROVER_STACK_SIZE: usize = 32 * 1024 * 1024;

fn on_large_stack<T, F>(work: F) -> Result<T, ZkError>
where
    T: Send + 'static,
    F: FnOnce() -> Result<T, ZkError> + Send + 'static,
{
    let handle = std::thread::Builder::new()
        .name("euid-prover".to_string())
        .stack_size(PROVER_STACK_SIZE)
        .spawn(work)
        .map_err(|error| ZkError::Prove(format!("failed to spawn prover thread: {error}")))?;
    handle
        .join()
        .map_err(|_| ZkError::Prove("prover thread panicked".to_string()))?
}

fn map_prover_error(error: eu_id_prover::Error) -> ZkError {
    ZkError::Prove(format!("{error:?}"))
}

fn compress_stark_proof_for_ffi(raw_bincode: &[u8]) -> Result<Vec<u8>, ZkError> {
    let mut encoder = BzEncoder::new(Vec::new(), Compression::best());
    encoder
        .write_all(raw_bincode)
        .map_err(|error| ZkError::Prove(format!("failed to compress proof: {error}")))?;
    encoder
        .finish()
        .map_err(|error| ZkError::Prove(format!("failed to finish proof compression: {error}")))
}

fn decompress_stark_proof_from_ffi(compressed: &[u8]) -> Result<Vec<u8>, ZkError> {
    if compressed.len() > MAX_COMPRESSED_STARK_PROOF_BYTES {
        return Err(ZkError::Verify(
            "compressed STARK proof exceeds size limit".to_string(),
        ));
    }
    let decoder = BzDecoder::new(compressed);
    let mut raw_bincode = Vec::new();
    decoder
        .take((MAX_DECOMPRESSED_STARK_PROOF_BYTES + 1) as u64)
        .read_to_end(&mut raw_bincode)
        .map_err(|error| ZkError::Verify(format!("failed to decompress proof: {error}")))?;
    if raw_bincode.len() > MAX_DECOMPRESSED_STARK_PROOF_BYTES {
        return Err(ZkError::Verify(
            "decompressed STARK proof exceeds size limit".to_string(),
        ));
    }
    Ok(raw_bincode)
}

fn decode_stark_proof(raw_bincode: &[u8]) -> Option<eu_id_prover::MdocProof> {
    bounded_bincode_options(MAX_DECOMPRESSED_STARK_PROOF_BYTES)
        .reject_trailing_bytes()
        .deserialize(raw_bincode)
        .ok()
}

/// The product attribute set is bound to the statement's predicate mode: an
/// age-only presentation must not require the credential to disclose (or even
/// contain) the nationality element, and vice versa. Single-attribute requests
/// are the established shape (the TS13 age-over profile proves one attribute).
fn expected_mdoc_attributes(
    mode: PredicateMode,
) -> Vec<eu_id_prover::mdoc::MdocRequestedAttribute> {
    expected_mdoc_attributes_for_profile(MdocRequestProfile::ProductDefault)
        .into_iter()
        .filter(|attribute| match attribute.mode {
            eu_id_prover::mdoc::MdocDisclosureMode::AgeOver => mode.uses_age(),
            eu_id_prover::mdoc::MdocDisclosureMode::Alpha2Set => mode.uses_nat(),
            _ => true,
        })
        .collect()
}

fn expected_mdoc_attributes_for_profile(
    profile: MdocRequestProfile,
) -> Vec<eu_id_prover::mdoc::MdocRequestedAttribute> {
    let contract = zk_contract_v1();
    match profile {
        MdocRequestProfile::ProductDefault => vec![
            eu_id_prover::mdoc::MdocRequestedAttribute {
                element_identifier: contract.element_birth_date,
                mode: eu_id_prover::mdoc::MdocDisclosureMode::AgeOver,
            },
            eu_id_prover::mdoc::MdocRequestedAttribute {
                element_identifier: contract.element_nationality,
                mode: eu_id_prover::mdoc::MdocDisclosureMode::Alpha2Set,
            },
        ],
        MdocRequestProfile::Ts13AgeOver18Equality => {
            vec![eu_id_prover::mdoc::MdocRequestedAttribute {
                element_identifier: result_age_over(18),
                mode: eu_id_prover::mdoc::MdocDisclosureMode::ValueEquality(vec![0xf5]),
            }]
        }
    }
}

fn mdoc_request(
    statement: &ZkPublicStatement,
    witness: &ZkMdocWitness,
) -> Result<eu_id_prover::MdocPidRequest, ZkError> {
    let trusted_mldsa_issuer_public_keys = match &witness.trusted_issuers {
        TrustedIssuers::PublicKeys(keys) => keys.clone(),
        TrustedIssuers::Certificates(_) => {
            return Err(ZkError::InvalidInput(
                "this build proves ML-DSA; witness needs TrustedIssuers::PublicKeys".to_string(),
            ))
        }
    };
    let contract = zk_contract_v1();
    Ok(eu_id_prover::MdocPidRequest {
        doctype: statement.doctype.clone(),
        namespace: statement.namespace.clone(),
        attributes: expected_mdoc_attributes(statement.predicate_mode),
        birth_date_element: contract.element_birth_date,
        nationality_element: contract.element_nationality,
        session_transcript: statement.nonce.clone(),
        trusted_mldsa_issuer_public_keys,
        device_authentication_profile:
            eu_id_prover::mdoc::MdocDeviceAuthenticationProfile::Iso180135,
    })
}

fn mdoc_statement_matches_public_statement(
    mdoc_statement: &eu_id_prover::MdocStatement,
    statement: &ZkPublicStatement,
) -> Result<bool, ZkError> {
    if mdoc_statement.ts13_revocation.is_some()
        || mdoc_statement.ts13_revocation_range.is_some()
        || mdoc_statement.ts13_revocation_signature.is_some()
    {
        return Ok(false);
    }
    if mdoc_statement.doctype != statement.doctype
        || mdoc_statement.namespace != statement.namespace
    {
        return Ok(false);
    }
    if mdoc_statement.policy != mapping::to_policy(statement)? {
        return Ok(false);
    }
    let expected_issuer_hash: [u8; 32] = match &statement.issuer_key {
        IssuerKey::MlDsa { pk_hash } => pk_hash.as_slice().try_into().map_err(|_| {
            ZkError::InvalidInput("issuer_key ML-DSA pk_hash must be 32 bytes".to_string())
        })?,
        IssuerKey::P256 { .. } => {
            return Err(ZkError::InvalidInput(
                "this build verifies ML-DSA; statement needs IssuerKey::MlDsa".to_string(),
            ))
        }
    };
    let Some(issuer_pk) = eu_id_prover::mdoc::mdoc_statement_issuer_mldsa_pk(mdoc_statement) else {
        return Ok(false);
    };
    if <[u8; 32]>::from(Sha256::digest(issuer_pk)) != expected_issuer_hash {
        return Ok(false);
    }

    let expected_device_hash = eu_id_prover::mdoc::device_authentication_sig_structure_hash(
        &statement.nonce,
        &statement.doctype,
    )
    .map_err(|error| {
        ZkError::InvalidInput(format!("invalid DeviceAuthentication input: {error:?}"))
    })?;
    let Some(device_input) = mdoc_statement.device_input.as_mldsa() else {
        return Ok(false);
    };
    if <[u8; 32]>::from(Sha256::digest(&device_input.message)) != expected_device_hash {
        return Ok(false);
    }

    Ok(mdoc_disclosed_set_matches(
        statement.predicate_mode,
        &mdoc_statement.attributes,
        mdoc_statement.age_attribute_index,
        mdoc_statement.nationality_attribute_index,
    ))
}

fn mdoc_disclosed_set_matches(
    mode: PredicateMode,
    attributes: &[eu_id_prover::mdoc::MdocStatementAttribute],
    age_attribute_index: Option<usize>,
    nationality_attribute_index: Option<usize>,
) -> bool {
    let expected = expected_mdoc_attributes(mode);
    if attributes.len() != expected.len()
        || attributes.iter().zip(&expected).any(|(got, want)| {
            got.element_identifier != want.element_identifier || got.mode != want.mode
        })
    {
        return false;
    }
    age_attribute_index
        == expected.iter().position(|attribute| {
            matches!(
                attribute.mode,
                eu_id_prover::mdoc::MdocDisclosureMode::AgeOver
            )
        })
        && nationality_attribute_index
            == expected.iter().position(|attribute| {
                matches!(
                    attribute.mode,
                    eu_id_prover::mdoc::MdocDisclosureMode::Alpha2Set
                )
            })
}

#[uniffi::export]
pub fn prove_identity(
    statement: ZkPublicStatement,
    witness: ZkMdocWitness,
) -> Result<Vec<u8>, ZkError> {
    on_large_stack(move || {
        validate_product_statement_contract(&statement)?;
        let policy = mapping::to_policy(&statement)?;
        let request = mdoc_request(&statement, &witness)?;
        let (proof, mdoc_statement) = eu_id_prover::prove_mdoc(&witness.document, &request, policy)
            .map_err(map_prover_error)?;
        let stark_proof = bincode::serialize(&proof)
            .map_err(|error| ZkError::Prove(format!("failed to serialize mdoc proof: {error}")))
            .and_then(|bytes| compress_stark_proof_for_ffi(&bytes))?;
        bincode::serialize(&MdocProofEnvelope {
            envelope_format: MDOC_ENVELOPE_FORMAT_V6,
            statement_bytes: encode_statement(&statement),
            mdoc_statement,
            stark_proof,
        })
        .map_err(|error| ZkError::Prove(format!("failed to serialize proof envelope: {error}")))
    })
}

#[uniffi::export]
pub fn verify_identity(
    statement: ZkPublicStatement,
    proof: Vec<u8>,
) -> Result<ZkVerifyResult, ZkError> {
    on_large_stack(move || {
        validate_product_statement_contract(&statement)?;
        let envelope = decode_mdoc_proof_envelope(&proof)?;
        if envelope.statement_bytes != encode_statement(&statement)
            || !mdoc_statement_matches_public_statement(&envelope.mdoc_statement, &statement)?
        {
            return Ok(ZkVerifyResult { ok: false });
        }
        let stark_proof = match decompress_stark_proof_from_ffi(&envelope.stark_proof)
            .ok()
            .and_then(|bytes| decode_stark_proof(&bytes))
        {
            Some(proof) => proof,
            None => return Ok(ZkVerifyResult { ok: false }),
        };
        Ok(ZkVerifyResult {
            ok: eu_id_prover::verify_mdoc(&stark_proof, &envelope.mdoc_statement).is_ok(),
        })
    })
}

/// The ZK identity system this SDK build implements. Reflects the linked prover
/// backend, so it can't disagree with what's compiled — callers use it to pick the
/// P-256 vs ML-DSA path (which [`IssuerKey`] / [`TrustedIssuers`] variant to build)
/// without a build flag of their own.
#[uniffi::export]
pub fn zk_system() -> ZkSystemKind {
    match eu_id_prover::ZK_SYSTEM_KIND {
        eu_id_prover::ZkSystemKind::P256 => ZkSystemKind::P256,
        eu_id_prover::ZkSystemKind::MlDsa => ZkSystemKind::MlDsa,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const PRE_Q12_TS13_CIRCUIT_HASH: &str =
        "05505a1e08264a96a82848baffa8cca3a190c9540dd486834e13a590471b6438";
    const PRE_Q13_TS13_CIRCUIT_HASH: &str =
        "7c50ed055da7745adce107a0e26a0f212ae187afc11805c23098b5a8b3b8735c";
    const PRE_Q14_TS13_CIRCUIT_HASH: &str =
        "0a16c986814462419b3f797e16d176450f8be46435d2b44a306a4862ea74d43c";
    const PRE_Q12_MDOC_ENVELOPE_FORMAT_V2: u16 = 2;
    const PRE_Q13_MDOC_ENVELOPE_FORMAT_V3: u16 = 3;
    const PRE_Q14_MDOC_ENVELOPE_FORMAT_V4: u16 = 4;
    const PRE_S1_MDOC_ENVELOPE_FORMAT_V5: u16 = 5;

    fn sample_statement() -> ZkPublicStatement {
        ZkPublicStatement {
            spec_id: "stwo-euid-pid-v1".to_string(),
            version: 1,
            doctype: TS13_PID_DOCTYPE.to_string(),
            namespace: TS13_PID_NAMESPACE.to_string(),
            issuer_key: IssuerKey::MlDsa {
                pk_hash: vec![0x11; 32],
            },
            today_epoch_day: 20_637,
            nonce: vec![1, 2, 3, 4],
            predicate_mode: PredicateMode::And,
            age_threshold_years: Some(18),
            accepted_numeric_countries: Some(vec![276, 250]),
            nat_mode: NatMode::Any,
        }
    }

    fn ts13_request() -> Ts13PresentationRequest {
        Ts13PresentationRequest {
            credential_format: TS13_CREDENTIAL_FORMAT.to_string(),
            zk_system_id: TS13_SYSTEM_ID.to_string(),
            doctype: TS13_PID_DOCTYPE.to_string(),
            namespace: TS13_PID_NAMESPACE.to_string(),
            circuit_hash: ts13_default_circuit_hash(),
            num_attributes: TS13_NUM_ATTRIBUTES,
            max_mso_payload_bytes: TS13_MAX_MSO_PAYLOAD_BYTES,
            max_attribute_bytes: TS13_MAX_ATTRIBUTE_BYTES,
            max_attribute_item_bytes: TS13_MAX_ATTRIBUTE_ITEM_BYTES,
            max_requested_digest_id: TS13_MAX_REQUESTED_DIGEST_ID,
            max_issuer_mldsa_message_bytes: TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES,
            max_device_mldsa_message_bytes: TS13_MAX_DEVICE_MLDSA_MESSAGE_BYTES,
            merged_sha_slot_log: TS13_MERGED_SHA_SLOT_LOG,
            merged_sha_log_n_rows: TS13_MERGED_SHA_LOG_N_ROWS,
            potential_issuers: TS13_POTENTIAL_ISSUERS,
            revocation_enabled: TS13_REVOCATION_ENABLED,
            revocation_id_width_bytes: TS13_REVOCATION_ID_WIDTH_BYTES,
            device_auth_profile: TS13_DEVICE_AUTH_PROFILE.to_string(),
            current_date_epoch_day: 20_637,
            session_transcript: vec![1, 2, 3, 4],
            trusted_issuer_hashes: vec!["00".repeat(32)],
            revocation_public_key: vec![7; ML_DSA_65_PUBLIC_KEY_BYTES],
            revocation_epoch: 7,
        }
    }

    fn statement_attribute(
        element_identifier: &str,
        mode: eu_id_prover::mdoc::MdocDisclosureMode,
    ) -> eu_id_prover::mdoc::MdocStatementAttribute {
        eu_id_prover::mdoc::MdocStatementAttribute {
            element_identifier: element_identifier.to_string(),
            mode,
            element_identifier_offset: 0,
            element_identifier_anchor_offset: 0,
            element_identifier_anchor: Vec::new(),
            element_value_anchor_offset: 0,
            element_value_anchor: Vec::new(),
            value_offset: 0,
            value: Vec::new(),
            value_head: Vec::new(),
            digest_id: 0,
            mso_digest_offset: 0,
            mso_digest_anchor_offset: 0,
            mso_digest_anchor: Vec::new(),
        }
    }

    #[test]
    fn ts13_legacy_builder_is_not_a_proof_verifier() {
        let request = ts13_request();
        let document = ts13_build_zk_document(request.clone(), Vec::new(), vec![1, 2, 3])
            .expect("valid request builds");
        assert!(!ts13_verify_zk_document(&request, &document).unwrap());

        let mut changed = request;
        changed.revocation_epoch += 1;
        assert!(!ts13_verify_zk_document(&changed, &document).unwrap());
    }

    #[test]
    fn ts13_rejects_non_mldsa_revocation_key_shape() {
        let mut request = ts13_request();
        request.revocation_public_key = vec![0; 64];
        assert!(matches!(
            ts13_validate_presentation_request(&request),
            Err(ZkError::InvalidInput(_))
        ));
    }

    #[test]
    fn ts13_rejects_resource_tuple_drift() {
        let mut request = ts13_request();
        request.max_mso_payload_bytes += 1;
        assert!(matches!(
            ts13_validate_presentation_request(&request),
            Err(ZkError::InvalidInput(message))
                if message == "unsupported TS13 tuple; no circuit_hash lookup entry"
        ));

        let mut request = ts13_request();
        request.merged_sha_slot_log += 1;
        assert!(matches!(
            ts13_validate_presentation_request(&request),
            Err(ZkError::InvalidInput(message))
                if message == "unsupported TS13 tuple; no circuit_hash lookup entry"
        ));

        let mut request = ts13_request();
        request.max_requested_digest_id += 1;
        assert!(matches!(
            ts13_validate_presentation_request(&request),
            Err(ZkError::InvalidInput(message))
                if message == "unsupported TS13 tuple; no circuit_hash lookup entry"
        ));
    }

    #[test]
    fn ts13_rejects_oversized_session_transcript() {
        let mut request = ts13_request();
        request.session_transcript = vec![0; TS13_MAX_SESSION_TRANSCRIPT_BYTES + 1];
        assert!(matches!(
            ts13_validate_presentation_request(&request),
            Err(ZkError::InvalidInput(message))
                if message == format!(
                    "TS13 session transcript exceeds {TS13_MAX_SESSION_TRANSCRIPT_BYTES} bytes"
                )
        ));
    }

    #[test]
    fn ts13_verify_rejects_oversized_document_before_worker_clone() {
        let request = ts13_request();
        let document = ts13_build_zk_document(
            request.clone(),
            canonical_ts13_disclosures(),
            vec![0; MAX_MDOC_ENVELOPE_BYTES + 1],
        )
        .expect("valid request builds");
        assert!(!ts13_verify_zk_document(&request, &document).unwrap());
    }

    #[test]
    fn ts13_rejects_pre_q12_circuit_hash() {
        let mut request = ts13_request();
        request.circuit_hash = PRE_Q12_TS13_CIRCUIT_HASH.to_string();
        assert!(matches!(
            ts13_validate_presentation_request(&request),
            Err(ZkError::InvalidInput(message)) if message.starts_with("unknown circuit_hash:")
        ));
    }

    #[test]
    fn ts13_rejects_pre_q13_circuit_hash() {
        let mut request = ts13_request();
        request.circuit_hash = PRE_Q13_TS13_CIRCUIT_HASH.to_string();
        assert!(matches!(
            ts13_validate_presentation_request(&request),
            Err(ZkError::InvalidInput(message)) if message.starts_with("unknown circuit_hash:")
        ));
    }

    #[test]
    fn ts13_rejects_pre_q14_circuit_hash() {
        let mut request = ts13_request();
        request.circuit_hash = PRE_Q14_TS13_CIRCUIT_HASH.to_string();
        assert!(matches!(
            ts13_validate_presentation_request(&request),
            Err(ZkError::InvalidInput(message)) if message.starts_with("unknown circuit_hash:")
        ));
    }

    #[test]
    fn mdoc_request_forwards_mldsa_trust_pins() {
        let pins = vec![vec![9; ML_DSA_65_PUBLIC_KEY_BYTES]];
        let witness = ZkMdocWitness {
            document: vec![0xa0],
            trusted_issuers: TrustedIssuers::PublicKeys(pins.clone()),
        };
        let request = mdoc_request(&sample_statement(), &witness).unwrap();
        assert_eq!(request.trusted_mldsa_issuer_public_keys, pins);
    }

    #[test]
    fn mdoc_disclosed_set_is_fail_closed() {
        let attributes = vec![
            statement_attribute(
                "birth_date",
                eu_id_prover::mdoc::MdocDisclosureMode::AgeOver,
            ),
            statement_attribute(
                "nationality",
                eu_id_prover::mdoc::MdocDisclosureMode::Alpha2Set,
            ),
        ];
        assert!(mdoc_disclosed_set_matches(
            PredicateMode::And,
            &attributes,
            Some(0),
            Some(1)
        ));
        assert!(!mdoc_disclosed_set_matches(
            PredicateMode::And,
            &attributes,
            None,
            Some(1)
        ));

        let mut substituted = attributes.clone();
        substituted[0].element_identifier = "issue_date".to_string();
        assert!(!mdoc_disclosed_set_matches(
            PredicateMode::And,
            &substituted,
            Some(0),
            Some(1)
        ));

        // Age-only: exactly the birth_date attribute, no nationality index.
        let age_only = vec![statement_attribute(
            "birth_date",
            eu_id_prover::mdoc::MdocDisclosureMode::AgeOver,
        )];
        assert!(mdoc_disclosed_set_matches(
            PredicateMode::Age,
            &age_only,
            Some(0),
            None
        ));
        // Cross-mode confusion stays fail-closed: an age-only statement must
        // not accept a two-attribute proof, nor an And statement a one-attribute
        // proof.
        assert!(!mdoc_disclosed_set_matches(
            PredicateMode::Age,
            &attributes,
            Some(0),
            Some(1)
        ));
        assert!(!mdoc_disclosed_set_matches(
            PredicateMode::And,
            &age_only,
            Some(0),
            None
        ));
    }

    #[test]
    fn expected_attributes_follow_predicate_mode() {
        let modes = [
            (PredicateMode::Age, vec!["birth_date"]),
            (PredicateMode::Nat, vec!["nationality"]),
            (PredicateMode::And, vec!["birth_date", "nationality"]),
        ];
        for (mode, expected) in modes {
            let got: Vec<String> = expected_mdoc_attributes(mode)
                .into_iter()
                .map(|attribute| attribute.element_identifier)
                .collect();
            assert_eq!(got, expected, "mode {mode:?}");
        }
    }

    #[test]
    fn identity_public_api_rejects_malformed_mdoc() {
        let witness = ZkMdocWitness {
            document: Vec::new(),
            trusted_issuers: TrustedIssuers::PublicKeys(Vec::new()),
        };
        assert!(matches!(
            prove_identity(sample_statement(), witness),
            Err(ZkError::Prove(_))
        ));
    }

    #[test]
    fn identity_public_api_rejects_malformed_proof() {
        assert!(matches!(
            verify_identity(sample_statement(), b"not a proof".to_vec()),
            Err(ZkError::Verify(message)) if message == "unsupported envelope format"
        ));
    }

    #[test]
    fn pre_q11_envelope_without_discriminator_rejects_typed() {
        // The old envelope started with `statement_bytes: Vec<u8>`, whose
        // bincode length prefix is deliberately not the supported format
        // (9 != MDOC_ENVELOPE_FORMAT_V6; a length equal to the current format
        // would instead reject at body decode, which the v6 test covers).
        let legacy = bincode::serialize(&(vec![0u8; 9], vec![0u8; 1], vec![0u8; 1])).unwrap();
        assert!(matches!(
            verify_identity(sample_statement(), legacy),
            Err(ZkError::Verify(message)) if message == "unsupported envelope format"
        ));
    }

    #[test]
    fn pre_q12_v2_envelope_rejects_typed_before_body_decode() {
        let legacy = bincode::serialize(&PRE_Q12_MDOC_ENVELOPE_FORMAT_V2).unwrap();
        assert!(matches!(
            verify_identity(sample_statement(), legacy),
            Err(ZkError::Verify(message)) if message == "unsupported envelope format"
        ));
    }

    #[test]
    fn pre_q13_v3_envelope_rejects_typed_before_body_decode() {
        let legacy = bincode::serialize(&PRE_Q13_MDOC_ENVELOPE_FORMAT_V3).unwrap();
        assert!(matches!(
            verify_identity(sample_statement(), legacy),
            Err(ZkError::Verify(message)) if message == "unsupported envelope format"
        ));
    }

    #[test]
    fn pre_q14_v4_envelope_rejects_typed_before_body_decode() {
        let legacy = bincode::serialize(&PRE_Q14_MDOC_ENVELOPE_FORMAT_V4).unwrap();
        assert!(matches!(
            verify_identity(sample_statement(), legacy),
            Err(ZkError::Verify(message)) if message == "unsupported envelope format"
        ));
    }

    #[test]
    fn v6_envelope_discriminator_reaches_body_decode() {
        let incomplete = bincode::serialize(&MDOC_ENVELOPE_FORMAT_V6).unwrap();
        assert!(matches!(
            verify_identity(sample_statement(), incomplete),
            Err(ZkError::Verify(message)) if message.starts_with("invalid proof envelope:")
        ));
    }

    #[test]
    fn pre_s1_v5_envelope_rejects_typed_before_body_decode() {
        let legacy = bincode::serialize(&PRE_S1_MDOC_ENVELOPE_FORMAT_V5).unwrap();
        assert!(matches!(
            verify_identity(sample_statement(), legacy),
            Err(ZkError::Verify(message)) if message == "unsupported envelope format"
        ));
    }

    #[test]
    fn oversized_envelope_rejects_before_decode() {
        let oversized = vec![0u8; MAX_MDOC_ENVELOPE_BYTES + 1];
        assert!(matches!(
            decode_mdoc_proof_envelope(&oversized),
            Err(ZkError::Verify(message)) if message == "proof envelope exceeds size limit"
        ));
    }

    #[test]
    fn oversized_compressed_proof_rejects_before_decompression() {
        let oversized = vec![0u8; MAX_COMPRESSED_STARK_PROOF_BYTES + 1];
        assert!(matches!(
            decompress_stark_proof_from_ffi(&oversized),
            Err(ZkError::Verify(message)) if message == "compressed STARK proof exceeds size limit"
        ));
    }

    #[test]
    fn statement_encoding_is_deterministic_and_mldsa_tagged() {
        let statement = sample_statement();
        let encoded = encode_statement(&statement);
        assert_eq!(encoded, encode_statement(&statement));
        assert!(encoded
            .windows("ML-DSA-65".len())
            .any(|window| window == b"ML-DSA-65"));
    }

    #[test]
    fn transport_compression_round_trips() {
        let raw = b"serialized stark proof bytes";
        let compressed = compress_stark_proof_for_ffi(raw).unwrap();
        assert!(compressed.starts_with(b"BZh"));
        assert_eq!(decompress_stark_proof_from_ffi(&compressed).unwrap(), raw);
    }

    #[test]
    fn public_helpers_remain_stable() {
        for mode in [
            PredicateMode::Age,
            PredicateMode::Nat,
            PredicateMode::And,
            PredicateMode::Or,
        ] {
            let token = predicate_mode_token(mode);
            assert_eq!(predicate_mode_from_token(token), Some(mode));
        }
        assert_eq!(result_age_over(18), "age_over_18");
        assert_eq!(iso_alpha2_to_numeric("GR".to_string()), Some(300));
        assert_eq!(zk_contract_v1().pid_namespace, TS13_PID_NAMESPACE);
        assert_eq!(sdk_version(), env!("CARGO_PKG_VERSION"));
    }
}
