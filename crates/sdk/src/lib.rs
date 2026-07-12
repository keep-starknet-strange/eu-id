//! ML-DSA EU-ID ZK SDK, exposed to Kotlin and Swift through UniFFI.
//!
//! [`prove_mdoc_pid`] accepts a CBOR PID mdoc plus ML-DSA issuer trust pins and
//! returns a compressed proof envelope. [`verify_mdoc_pid`] binds that envelope
//! to the verifier's request and verifies the same mdoc proof.

use std::io::{Read, Write};

use bzip2::read::BzDecoder;
use bzip2::write::BzEncoder;
use bzip2::Compression;
use ciborium::value::Value;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

uniffi::setup_scaffolding!();

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
const TS13_MAX_MDOC_BYTES: u32 = 16_384;
const TS13_NUM_ATTRIBUTES: u32 = 1;
const TS13_MAX_ATTRIBUTE_BYTES: u32 = 32;
const TS13_POTENTIAL_ISSUERS: u32 = 1;
const TS13_REVOCATION_ENABLED: bool = true;
const TS13_REVOCATION_ID_WIDTH_BYTES: u32 = 8;
const ML_DSA_65_PUBLIC_KEY_BYTES: usize = 1_952;

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
    pub preprocessed_root: Vec<u8>,
    pub num_attributes: u32,
    pub max_mdoc_bytes: u32,
    pub max_attribute_bytes: u32,
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
    pub preprocessed_root: Vec<u8>,
    pub request_binding_hash: String,
    pub disclosed_attributes: Vec<Ts13DisclosedAttribute>,
    pub proof: Vec<u8>,
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
        ("max_mdoc_bytes".into(), Value::from(request.max_mdoc_bytes)),
        (
            "max_attribute_bytes".into(),
            Value::from(request.max_attribute_bytes),
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
            "preprocessed_root".into(),
            Value::Bytes(request.preprocessed_root.clone()),
        ),
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

#[uniffi::export]
pub fn ts13_default_preprocessed_root() -> Vec<u8> {
    eu_id_prover::ts13::ts13_default_preprocessed_root().to_vec()
}

fn ts13_tuple_is_supported(request: &Ts13PresentationRequest) -> bool {
    request.doctype == TS13_PID_DOCTYPE
        && request.namespace == TS13_PID_NAMESPACE
        && request.num_attributes == TS13_NUM_ATTRIBUTES
        && request.max_mdoc_bytes == TS13_MAX_MDOC_BYTES
        && request.max_attribute_bytes == TS13_MAX_ATTRIBUTE_BYTES
        && request.potential_issuers == TS13_POTENTIAL_ISSUERS
        && request.revocation_enabled == TS13_REVOCATION_ENABLED
        && request.revocation_id_width_bytes == TS13_REVOCATION_ID_WIDTH_BYTES
        && request.device_auth_profile == TS13_DEVICE_AUTH_PROFILE
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
    if request.preprocessed_root.len() != 32 {
        return Err(ZkError::InvalidInput(
            "preprocessed_root must be 32 bytes".to_string(),
        ));
    }
    if request.trusted_issuer_hashes.len() != request.potential_issuers as usize
        || request.trusted_issuer_hashes.iter().any(String::is_empty)
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
        preprocessed_root: request.preprocessed_root.clone(),
        request_binding_hash: ts13_request_binding_hash(&request),
        disclosed_attributes,
        proof,
    })
}

#[uniffi::export]
pub fn ts13_verify_zk_document(
    request: &Ts13PresentationRequest,
    document: &Ts13ZkDocument,
) -> Result<bool, ZkError> {
    if ts13_validate_presentation_request(request).is_err() {
        return Ok(false);
    }
    Ok(document.doc_type == request.doctype
        && document.zk_system_id == request.zk_system_id
        && document.circuit_hash == request.circuit_hash
        && document.preprocessed_root == request.preprocessed_root
        && document.request_binding_hash == ts13_request_binding_hash(request))
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

#[derive(uniffi::Record, Clone, Debug, PartialEq, Eq)]
pub struct ZkPublicStatement {
    pub spec_id: String,
    pub version: u32,
    pub doctype: String,
    pub namespace: String,
    /// SHA-256 of the trusted issuer's FIPS 204 `pkEncode` bytes.
    pub issuer_public_key_hash: Vec<u8>,
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
    /// Trusted ML-DSA-65 issuer `pkEncode` values.
    pub trusted_issuer_public_keys: Vec<Vec<u8>>,
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

fn encode_statement(statement: &ZkPublicStatement) -> Vec<u8> {
    let mut entries: Vec<(Value, Value)> = vec![
        ("v".into(), Value::from(statement.version)),
        ("spec_id".into(), statement.spec_id.as_str().into()),
        ("doctype".into(), statement.doctype.as_str().into()),
        ("namespace".into(), statement.namespace.as_str().into()),
        (
            "issuer_key".into(),
            Value::Map(vec![
                ("alg".into(), "ML-DSA-65".into()),
                (
                    "pk_hash".into(),
                    Value::Bytes(statement.issuer_public_key_hash.clone()),
                ),
            ]),
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
    statement_bytes: Vec<u8>,
    mdoc_statement: eu_id_prover::MdocStatement,
    stark_proof: Vec<u8>,
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
    let mut decoder = BzDecoder::new(compressed);
    let mut raw_bincode = Vec::new();
    decoder
        .read_to_end(&mut raw_bincode)
        .map_err(|error| ZkError::Verify(format!("failed to decompress proof: {error}")))?;
    Ok(raw_bincode)
}

fn expected_mdoc_attributes() -> Vec<eu_id_prover::mdoc::MdocRequestedAttribute> {
    expected_mdoc_attributes_for_profile(MdocRequestProfile::ProductDefault)
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
) -> eu_id_prover::MdocPidRequest {
    let contract = zk_contract_v1();
    eu_id_prover::MdocPidRequest {
        doctype: statement.doctype.clone(),
        namespace: statement.namespace.clone(),
        attributes: expected_mdoc_attributes(),
        birth_date_element: contract.element_birth_date,
        nationality_element: contract.element_nationality,
        session_transcript: statement.nonce.clone(),
        trusted_mldsa_issuer_public_keys: witness.trusted_issuer_public_keys.clone(),
        device_authentication_profile:
            eu_id_prover::mdoc::MdocDeviceAuthenticationProfile::Iso180135,
    }
}

fn mdoc_statement_matches_public_statement(
    mdoc_statement: &eu_id_prover::MdocStatement,
    statement: &ZkPublicStatement,
) -> Result<bool, ZkError> {
    if mdoc_statement.policy != mapping::to_policy(statement)? {
        return Ok(false);
    }
    let expected_issuer_hash: [u8; 32] = statement
        .issuer_public_key_hash
        .as_slice()
        .try_into()
        .map_err(|_| {
            ZkError::InvalidInput("issuer_public_key_hash must be 32 bytes".to_string())
        })?;
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
        &mdoc_statement.attributes,
        mdoc_statement.age_attribute_index,
        mdoc_statement.nationality_attribute_index,
    ))
}

fn mdoc_disclosed_set_matches(
    attributes: &[eu_id_prover::mdoc::MdocStatementAttribute],
    age_attribute_index: Option<usize>,
    nationality_attribute_index: Option<usize>,
) -> bool {
    let expected = expected_mdoc_attributes();
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
pub fn prove_mdoc_pid(
    statement: ZkPublicStatement,
    witness: ZkMdocWitness,
) -> Result<Vec<u8>, ZkError> {
    on_large_stack(move || {
        let policy = mapping::to_policy(&statement)?;
        let request = mdoc_request(&statement, &witness);
        let (proof, mdoc_statement) = eu_id_prover::prove_mdoc(&witness.document, &request, policy)
            .map_err(map_prover_error)?;
        let stark_proof = bincode::serialize(&proof)
            .map_err(|error| ZkError::Prove(format!("failed to serialize mdoc proof: {error}")))
            .and_then(|bytes| compress_stark_proof_for_ffi(&bytes))?;
        bincode::serialize(&MdocProofEnvelope {
            statement_bytes: encode_statement(&statement),
            mdoc_statement,
            stark_proof,
        })
        .map_err(|error| ZkError::Prove(format!("failed to serialize proof envelope: {error}")))
    })
}

#[uniffi::export]
pub fn verify_mdoc_pid(
    statement: ZkPublicStatement,
    proof: Vec<u8>,
) -> Result<ZkVerifyResult, ZkError> {
    on_large_stack(move || {
        let envelope: MdocProofEnvelope = match bincode::deserialize(&proof) {
            Ok(envelope) => envelope,
            Err(_) => return Ok(ZkVerifyResult { ok: false }),
        };
        if envelope.statement_bytes != encode_statement(&statement)
            || !mdoc_statement_matches_public_statement(&envelope.mdoc_statement, &statement)?
        {
            return Ok(ZkVerifyResult { ok: false });
        }
        let stark_proof = match decompress_stark_proof_from_ffi(&envelope.stark_proof)
            .ok()
            .and_then(|bytes| bincode::deserialize::<eu_id_prover::MdocProof>(&bytes).ok())
        {
            Some(proof) => proof,
            None => return Ok(ZkVerifyResult { ok: false }),
        };
        Ok(ZkVerifyResult {
            ok: eu_id_prover::verify_mdoc(&stark_proof, &envelope.mdoc_statement).is_ok(),
        })
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_statement() -> ZkPublicStatement {
        ZkPublicStatement {
            spec_id: "stwo-euid-pid-v1".to_string(),
            version: 1,
            doctype: TS13_PID_DOCTYPE.to_string(),
            namespace: TS13_PID_NAMESPACE.to_string(),
            issuer_public_key_hash: vec![0x11; 32],
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
            preprocessed_root: ts13_default_preprocessed_root(),
            num_attributes: TS13_NUM_ATTRIBUTES,
            max_mdoc_bytes: TS13_MAX_MDOC_BYTES,
            max_attribute_bytes: TS13_MAX_ATTRIBUTE_BYTES,
            potential_issuers: TS13_POTENTIAL_ISSUERS,
            revocation_enabled: TS13_REVOCATION_ENABLED,
            revocation_id_width_bytes: TS13_REVOCATION_ID_WIDTH_BYTES,
            device_auth_profile: TS13_DEVICE_AUTH_PROFILE.to_string(),
            current_date_epoch_day: 20_637,
            session_transcript: vec![1, 2, 3, 4],
            trusted_issuer_hashes: vec!["issuer-root-sha256".to_string()],
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
    fn ts13_presentation_round_trip_and_policy_binding() {
        let request = ts13_request();
        let document = ts13_build_zk_document(request.clone(), Vec::new(), vec![1, 2, 3])
            .expect("valid request builds");
        assert!(ts13_verify_zk_document(&request, &document).unwrap());

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
    fn mdoc_request_forwards_mldsa_trust_pins() {
        let witness = ZkMdocWitness {
            document: vec![0xa0],
            trusted_issuer_public_keys: vec![vec![9; ML_DSA_65_PUBLIC_KEY_BYTES]],
        };
        let request = mdoc_request(&sample_statement(), &witness);
        assert_eq!(
            request.trusted_mldsa_issuer_public_keys,
            witness.trusted_issuer_public_keys
        );
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
        assert!(mdoc_disclosed_set_matches(&attributes, Some(0), Some(1)));
        assert!(!mdoc_disclosed_set_matches(&attributes, None, Some(1)));

        let mut substituted = attributes;
        substituted[0].element_identifier = "issue_date".to_string();
        assert!(!mdoc_disclosed_set_matches(&substituted, Some(0), Some(1)));
    }

    #[test]
    fn malformed_mdoc_proof_rejects() {
        assert!(
            !verify_mdoc_pid(sample_statement(), b"not a proof".to_vec())
                .unwrap()
                .ok
        );
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
