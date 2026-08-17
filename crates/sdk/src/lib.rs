//! ML-DSA EU-ID ZK SDK, exposed to Kotlin and Swift through UniFFI.
//!
//! ## Entry point
//!
//! [`prove_identity`] accepts one tagged theorem and returns its opaque proof
//! bytes. The TS13 variant runs the canonical public-input-unlinkable identity
//! proof with revocation.
//!
//! ## Product variant
//!
//! The Product variant is interface-compatible only. This branch ships no
//! product circuit, so the Product variant fails closed with
//! [`ZkError::UnsupportedProofSystem`].

use bincode::Options;
use ciborium::value::Value;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

uniffi::setup_scaffolding!();

mod demo;
mod ts13_demo;

pub use ts13_demo::{IdentityError, IdentityStatement, IdentityWitness};

const PROOF_THREAD_STACK_SIZE_BYTES: usize = 2 * 1024 * 1024;
const PROOF_WORKER_STACK_SIZE_BYTES: usize = 16 * 1024 * 1024;
const PROOF_WORKER_COUNT: usize = 6;

fn with_proof_runtime<T, F>(failure: IdentityError, work: F) -> Result<T, IdentityError>
where
    T: Send + 'static,
    F: FnOnce() -> Result<T, IdentityError> + Send + 'static,
{
    let handle = std::thread::Builder::new()
        .name("euid-zk".to_string())
        .stack_size(PROOF_THREAD_STACK_SIZE_BYTES)
        .spawn(move || {
            let pool = rayon::ThreadPoolBuilder::new()
                .num_threads(PROOF_WORKER_COUNT)
                .stack_size(PROOF_WORKER_STACK_SIZE_BYTES)
                .thread_name(|index| format!("euid-zk-worker-{index}"))
                .build()
                .map_err(|_| failure)?;
            pool.install(work)
        })
        .map_err(|_| failure)?;
    handle.join().map_err(|_| failure)?
}

/// Predicate mode of a product theorem: age, nationality, or a combination.
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

/// Nationality predicate mode. `Any` accepts every nationality.
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

/// The ZK contract v1: canonical names for the spec, elements, parameters,
/// and results.
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
const TS13_NUM_ATTRIBUTES: u32 = 1;
const TS13_AGE_THRESHOLD_YEARS: u32 = 18;
const TS13_POTENTIAL_ISSUERS: u32 = 1;
const TS13_REVOCATION_ENABLED: bool = true;
const TS13_REVOCATION_ID_WIDTH_BYTES: u32 = 8;
const ML_DSA_65_PUBLIC_KEY_BYTES: usize = eu_id_prover::ts13_demo::ML_DSA_65_PUBLIC_KEY_BYTES;
const SECONDS_PER_DAY: i64 = 86_400;
/// Compat document envelope over the canonical identity envelope. V3 was the
/// pre-canonicalization circuit; V3 proofs no longer verify anywhere.
const TS13_ENVELOPE_FORMAT_V4: u16 = 4;
/// Bounds the wallet-compatible wrapper while leaving room for the fixed
/// identity envelope, issuer key, and request binding.
const MAX_TS13_DOCUMENT_PROOF_BYTES: usize = 2_097_152;

/// Disclosure kind of a TS13 attribute: equality or extension.
#[derive(uniffi::Enum, Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Ts13DisclosureKind {
    Equality,
    Extension,
}

/// The TS13 presentation request tuple. The circuit-shape numeric fields are
/// kept for wire compatibility; they are pinned transitively by `circuit_hash`
/// (the only binding the canonical verifier checks) and are not re-validated
/// field by field.
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
    pub value_digests_scan_log_size: u32,
    pub value_digests_scan_max_items: u32,
    pub value_digests_scan_preprocessed_cols: u32,
    pub value_digests_scan_trace_cols: u32,
    pub value_digests_scan_relation_sites: u32,
    pub value_digests_scan_interaction_cols: u32,
    pub country_code_dataset: String,
    pub country_code_table_log_size: u32,
    pub country_code_count: u32,
    pub country_code_table_preprocessed_cols: u32,
    pub country_code_table_trace_cols: u32,
    pub country_code_table_interaction_cols: u32,
    pub country_code_table_sha256: Vec<u8>,
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

/// One attribute disclosed in a [`Ts13ZkDocument`].
#[derive(uniffi::Record, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Ts13DisclosedAttribute {
    pub namespace: String,
    pub name: String,
    pub value_cbor: Vec<u8>,
    pub disclosure: Ts13DisclosureKind,
}

/// The ZK document a wallet returns to a verifier: binding hash, disclosed
/// attributes, and proof.
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

/// Returns the ZK contract v1 with the canonical field names.
#[uniffi::export]
pub fn zk_contract_v1() -> ZkContract {
    ZkContract {
        system_name: TS13_SYSTEM_ID.to_string(),
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

fn lower_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn sha256_hex(bytes: &[u8]) -> String {
    lower_hex(&Sha256::digest(bytes))
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
            "value_digests_scan_log_size".into(),
            Value::from(request.value_digests_scan_log_size),
        ),
        (
            "value_digests_scan_max_items".into(),
            Value::from(request.value_digests_scan_max_items),
        ),
        (
            "value_digests_scan_preprocessed_cols".into(),
            Value::from(request.value_digests_scan_preprocessed_cols),
        ),
        (
            "value_digests_scan_trace_cols".into(),
            Value::from(request.value_digests_scan_trace_cols),
        ),
        (
            "value_digests_scan_relation_sites".into(),
            Value::from(request.value_digests_scan_relation_sites),
        ),
        (
            "value_digests_scan_interaction_cols".into(),
            Value::from(request.value_digests_scan_interaction_cols),
        ),
        (
            "country_code_dataset".into(),
            request.country_code_dataset.as_str().into(),
        ),
        (
            "country_code_table_log_size".into(),
            Value::from(request.country_code_table_log_size),
        ),
        (
            "country_code_count".into(),
            Value::from(request.country_code_count),
        ),
        (
            "country_code_table_preprocessed_cols".into(),
            Value::from(request.country_code_table_preprocessed_cols),
        ),
        (
            "country_code_table_trace_cols".into(),
            Value::from(request.country_code_table_trace_cols),
        ),
        (
            "country_code_table_interaction_cols".into(),
            Value::from(request.country_code_table_interaction_cols),
        ),
        (
            "country_code_table_sha256".into(),
            Value::Bytes(request.country_code_table_sha256.clone()),
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
    sha256_hex(&cbor_bytes(value))
}

/// The canonical circuit hash as the lowercase hex string carried in
/// [`Ts13PresentationRequest::circuit_hash`].
#[uniffi::export]
pub fn ts13_default_circuit_hash() -> String {
    lower_hex(&ts13_demo_circuit_hash())
}

/// Raw artifact-derived circuit hash required by [`IdentityStatement`].
#[uniffi::export]
pub fn ts13_demo_circuit_hash() -> Vec<u8> {
    eu_id_prover::ts13_demo_artifact_constants::TS13_DEMO_CIRCUIT_HASH.to_vec()
}

/// Protocol-level tuple fields. The circuit-shape numerics deliberately do not
/// appear here: `circuit_hash` pins the exact circuit, so re-checking shape
/// descriptors against exported constants would only duplicate that binding.
fn ts13_tuple_is_supported(request: &Ts13PresentationRequest) -> bool {
    request.doctype == TS13_PID_DOCTYPE
        && request.namespace == TS13_PID_NAMESPACE
        && request.num_attributes == TS13_NUM_ATTRIBUTES
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

/// Validates a TS13 presentation request against the pinned canonical tuple.
/// Fails closed on any unsupported field.
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
    Ok(())
}

/// Builds a [`Ts13ZkDocument`] from a validated request. Binds the document to
/// the request through `request_binding_hash`.
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

/// Compat wrapper around the canonical identity envelope. The canonical
/// envelope carries no statement (unlinkability). The verifier must check the
/// issuer key against `trusted_issuer_hashes`, so this wrapper carries the
/// issuer key, as the old envelope carried it inside its mdoc statement.
#[derive(Serialize, Deserialize)]
struct Ts13ProofEnvelope {
    envelope_format: u16,
    request_binding_hash: String,
    issuer_public_key: Vec<u8>,
    identity_envelope: Vec<u8>,
}

fn bounded_bincode_options(limit: usize) -> impl Options {
    // `bincode::serialize`/`deserialize` use fixed-width integer encoding;
    // retain that wire format while bounding all nested lengths.
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_limit(limit as u64)
}

fn decode_ts13_proof_envelope(proof: &[u8]) -> Result<Ts13ProofEnvelope, ZkError> {
    if proof.len() > MAX_TS13_DOCUMENT_PROOF_BYTES {
        return Err(ZkError::Verify(
            "TS13 proof envelope exceeds size limit".to_string(),
        ));
    }
    // Decode only the leading `envelope_format` field. Trailing bytes are
    // allowed here because the rest of the envelope follows that field. The
    // full decode below still pins exact consumption via
    // `reject_trailing_bytes`.
    let envelope_format: u16 = bounded_bincode_options(MAX_TS13_DOCUMENT_PROOF_BYTES)
        .allow_trailing_bytes()
        .deserialize(proof)
        .map_err(|_| ZkError::Verify("unsupported TS13 envelope format".to_string()))?;
    if envelope_format != TS13_ENVELOPE_FORMAT_V4 {
        return Err(ZkError::Verify(
            "unsupported TS13 envelope format".to_string(),
        ));
    }
    bounded_bincode_options(MAX_TS13_DOCUMENT_PROOF_BYTES)
        .reject_trailing_bytes()
        .deserialize(proof)
        .map_err(|_| ZkError::Verify("invalid TS13 proof envelope".to_string()))
}

fn canonical_ts13_disclosures() -> Vec<Ts13DisclosedAttribute> {
    vec![Ts13DisclosedAttribute {
        namespace: TS13_PID_NAMESPACE.to_string(),
        name: result_age_over(TS13_AGE_THRESHOLD_YEARS),
        value_cbor: cbor_bytes(Value::Bool(true)),
        disclosure: Ts13DisclosureKind::Equality,
    }]
}

/// Builds the canonical [`IdentityStatement`] that a presentation request pins
/// down, given the issuer public key resolved against `trusted_issuer_hashes`.
fn ts13_identity_statement(
    request: &Ts13PresentationRequest,
    trusted_issuer_public_key: Vec<u8>,
) -> IdentityStatement {
    IdentityStatement {
        circuit_hash: ts13_demo_circuit_hash(),
        zk_system_id: request.zk_system_id.clone(),
        document_type: request.doctype.clone(),
        namespace: request.namespace.clone(),
        element_identifier: result_age_over(TS13_AGE_THRESHOLD_YEARS),
        expected_value_cbor: cbor_bytes(Value::Bool(true)),
        timestamp_epoch_seconds: i64::from(request.current_date_epoch_day) * SECONDS_PER_DAY,
        session_transcript: request.session_transcript.clone(),
        trusted_issuer_public_key,
        revocation_public_key: request.revocation_public_key.clone(),
        revocation_epoch: request.revocation_epoch,
    }
}

fn ts13_witness_issuer_key(
    request: &Ts13PresentationRequest,
    witness: &Ts13MdocWitness,
) -> Result<Vec<u8>, ZkError> {
    if witness.trusted_issuer_public_keys.len() != request.potential_issuers as usize
        || witness.trusted_issuer_public_keys.iter().any(|key| {
            key.len() != ML_DSA_65_PUBLIC_KEY_BYTES
                || !request
                    .trusted_issuer_hashes
                    .iter()
                    .any(|trusted| trusted == &sha256_hex(key))
        })
    {
        return Err(ZkError::InvalidInput(
            "TS13 witness issuer keys do not match trusted issuer hashes".to_string(),
        ));
    }
    Ok(witness.trusted_issuer_public_keys[0].clone())
}

/// Create the dedicated TS13 equality-and-revocation proof envelope through
/// the canonical identity prover.
#[uniffi::export]
pub fn ts13_prove_zk_document(
    request: Ts13PresentationRequest,
    witness: Ts13MdocWitness,
) -> Result<Ts13ZkDocument, ZkError> {
    ts13_validate_presentation_request(&request)?;
    let issuer_public_key = ts13_witness_issuer_key(&request, &witness)?;
    let statement = ts13_identity_statement(&request, issuer_public_key.clone());
    let identity_witness = IdentityWitness {
        document: witness.document,
        revocation_id_lo: witness.revocation_id_lo,
        revocation_id_hi: witness.revocation_id_hi,
        revocation_signature: witness.revocation_signature,
    };
    let identity_envelope = with_proof_runtime(IdentityError::ProofGenerationFailed, move || {
        eu_id_prover::report_prove_runtime_configuration(
            PROOF_THREAD_STACK_SIZE_BYTES,
            PROOF_WORKER_STACK_SIZE_BYTES,
        );
        ts13_demo::prove_identity_inner(&statement, identity_witness)
    })?;
    let request_binding_hash = ts13_request_binding_hash(&request);
    let proof = bincode::serialize(&Ts13ProofEnvelope {
        envelope_format: TS13_ENVELOPE_FORMAT_V4,
        request_binding_hash: request_binding_hash.clone(),
        issuer_public_key,
        identity_envelope,
    })
    .map_err(|error| ZkError::Prove(format!("failed to serialize TS13 proof envelope: {error}")))?;
    if proof.len() > MAX_TS13_DOCUMENT_PROOF_BYTES {
        return Err(ZkError::Prove(
            "TS13 proof envelope exceeds size limit".to_string(),
        ));
    }
    Ok(Ts13ZkDocument {
        doc_type: request.doctype,
        zk_system_id: request.zk_system_id,
        circuit_hash: request.circuit_hash,
        request_binding_hash,
        disclosed_attributes: canonical_ts13_disclosures(),
        proof,
    })
}

fn ts13_document_matches_request(
    request: &Ts13PresentationRequest,
    document: &Ts13ZkDocument,
) -> bool {
    if ts13_validate_presentation_request(request).is_err() {
        return false;
    }
    if document.doc_type != request.doctype
        || document.zk_system_id != request.zk_system_id
        || document.circuit_hash != request.circuit_hash
        || document.request_binding_hash != ts13_request_binding_hash(request)
        || document.disclosed_attributes != canonical_ts13_disclosures()
    {
        return false;
    }
    true
}

/// Verifies a [`Ts13ZkDocument`] against a presentation request. Returns
/// `Ok(false)` when the document does not match the request, the envelope is
/// malformed, the issuer key is not trusted, or the proof does not verify.
#[uniffi::export]
pub fn ts13_verify_zk_document(
    request: &Ts13PresentationRequest,
    document: &Ts13ZkDocument,
) -> Result<bool, ZkError> {
    if !ts13_document_matches_request(request, document) {
        return Ok(false);
    }
    let Ok(envelope) = decode_ts13_proof_envelope(&document.proof) else {
        return Ok(false);
    };
    if envelope.request_binding_hash != document.request_binding_hash
        || !request
            .trusted_issuer_hashes
            .iter()
            .any(|trusted| trusted == &sha256_hex(&envelope.issuer_public_key))
    {
        return Ok(false);
    }
    let statement = ts13_identity_statement(request, envelope.issuer_public_key);
    let verified = with_proof_runtime(IdentityError::ProofVerificationFailed, move || {
        Ok(ts13_demo::verify_identity_inner(&statement, &envelope.identity_envelope).is_ok())
    })?;
    Ok(verified)
}

/// Returns the SDK crate version.
#[uniffi::export]
pub fn sdk_version() -> String {
    env!("CARGO_PKG_VERSION").to_string()
}

/// Returns the canonical element identifier for an age-over predicate.
#[uniffi::export]
pub fn result_age_over(min_age: u32) -> String {
    format!("age_over_{min_age}")
}

/// Parses a predicate-mode token. Returns `None` for unknown tokens.
#[uniffi::export]
pub fn predicate_mode_from_token(token: String) -> Option<PredicateMode> {
    PredicateMode::from_token(&token)
}

/// Returns the wire token of a predicate mode.
#[uniffi::export]
pub fn predicate_mode_token(mode: PredicateMode) -> String {
    mode.as_token().to_string()
}

/// Reports whether the predicate mode evaluates the age predicate.
#[uniffi::export]
pub fn predicate_mode_uses_age(mode: PredicateMode) -> bool {
    mode.uses_age()
}

/// Reports whether the predicate mode evaluates the nationality predicate.
#[uniffi::export]
pub fn predicate_mode_uses_nat(mode: PredicateMode) -> bool {
    mode.uses_nat()
}

/// Returns the wire token of a nationality mode.
#[uniffi::export]
pub fn nat_mode_token(mode: NatMode) -> String {
    mode.as_token().to_string()
}

/// Converts an ISO 3166-1 alpha-2 code to its numeric code. Returns `None`
/// for unknown codes.
#[uniffi::export]
pub fn iso_alpha2_to_numeric(alpha2: String) -> Option<u32> {
    eu_id_prover::iso_alpha2_to_numeric(&alpha2)
}

/// Identifies the ZK identity system this SDK build implements. This build is
/// ML-DSA by construction. The P-256 variant exists only for interface
/// compatibility with callers that switch on the system kind.
#[derive(uniffi::Enum, Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkSystemKind {
    P256,
    MlDsa,
}

/// Issuer trust anchor pinned in a [`ZkPublicStatement`]: P-256 carries the EC
/// public-key coordinates; ML-DSA carries the SHA-256 of the issuer `pkEncode`.
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

/// The result of a successful identity-proof verification.
#[derive(uniffi::Record, Clone, Debug)]
pub struct ZkVerifyResult {
    pub ok: bool,
}

/// SDK errors surfaced over UniFFI. Error messages carry no private data.
#[derive(uniffi::Error, thiserror::Error, Clone, Debug, PartialEq, Eq)]
pub enum ZkError {
    #[error("invalid input: {0}")]
    InvalidInput(String),
    #[error("proving failed: {0}")]
    Prove(String),
    #[error("verification failed: {0}")]
    Verify(String),
    #[error("unsupported proof system")]
    UnsupportedProofSystem,
    #[error("unsupported circuit hash")]
    UnsupportedCircuitHash,
    #[error("unsupported demo credential shape")]
    UnsupportedDemoCredentialShape,
    #[error("malformed session transcript")]
    MalformedSessionTranscript,
    #[error("invalid public context")]
    InvalidPublicContext,
    #[error("invalid private credential")]
    InvalidPrivateCredential,
    #[error("invalid revocation witness")]
    InvalidRevocationWitness,
    #[error("proof generation failed")]
    ProofGenerationFailed,
    #[error("malformed proof envelope")]
    MalformedProofEnvelope,
    #[error("proof context mismatch")]
    ProofContextMismatch,
    #[error("proof verification failed")]
    ProofVerificationFailed,
}

impl From<IdentityError> for ZkError {
    fn from(error: IdentityError) -> Self {
        match error {
            IdentityError::UnsupportedCircuitHash => Self::UnsupportedCircuitHash,
            IdentityError::UnsupportedCredentialShape => Self::UnsupportedDemoCredentialShape,
            IdentityError::MalformedSessionTranscript => Self::MalformedSessionTranscript,
            IdentityError::InvalidPublicContext => Self::InvalidPublicContext,
            IdentityError::InvalidPrivateCredential => Self::InvalidPrivateCredential,
            IdentityError::InvalidRevocationWitness => Self::InvalidRevocationWitness,
            IdentityError::ProofGenerationFailed => Self::ProofGenerationFailed,
            IdentityError::MalformedProofEnvelope => Self::MalformedProofEnvelope,
            IdentityError::ProofVerificationFailed => Self::ProofVerificationFailed,
        }
    }
}

/// Holds the existing product theorem, without any optional TS13 fields.
#[derive(uniffi::Record, Clone, Debug, PartialEq, Eq)]
pub struct ProductPublicStatementV1 {
    pub spec_id: String,
    pub version: u32,
    pub doctype: String,
    pub namespace: String,
    pub issuer_key: IssuerKey,
    pub today_epoch_day: i32,
    pub nonce: Vec<u8>,
    pub predicate_mode: PredicateMode,
    pub age_threshold_years: Option<u32>,
    pub accepted_numeric_countries: Option<Vec<u32>>,
    pub nat_mode: NatMode,
}

/// Holds the existing product mdoc witness, without any optional TS13 fields.
#[derive(uniffi::Record, Clone, Debug)]
pub struct ProductMdocWitnessV1 {
    pub document: Vec<u8>,
    pub trusted_issuers: TrustedIssuers,
}

/// Tagged public statement: the Product V1 theorem or the canonical TS13
/// identity theorem.
#[derive(uniffi::Enum, Clone, Debug)]
pub enum ZkPublicStatement {
    ProductV1(ProductPublicStatementV1),
    Ts13DemoV1(IdentityStatement),
}

/// Tagged witness matching [`ZkPublicStatement`].
#[derive(uniffi::Enum, Clone)]
pub enum ZkMdocWitness {
    ProductV1(ProductMdocWitnessV1),
    Ts13DemoV1(IdentityWitness),
}

/// Prove the theorem selected by the tagged public statement. The TS13 variant
/// runs the full canonical identity proof, revocation included.
#[uniffi::export]
pub fn prove_identity(
    statement: ZkPublicStatement,
    witness: ZkMdocWitness,
) -> Result<Vec<u8>, ZkError> {
    match (statement, witness) {
        (ZkPublicStatement::Ts13DemoV1(statement), ZkMdocWitness::Ts13DemoV1(witness)) => {
            with_proof_runtime(IdentityError::ProofGenerationFailed, move || {
                eu_id_prover::report_prove_runtime_configuration(
                    PROOF_THREAD_STACK_SIZE_BYTES,
                    PROOF_WORKER_STACK_SIZE_BYTES,
                );
                ts13_demo::prove_identity_inner(&statement, witness)
            })
            .map_err(ZkError::from)
        }
        // ponytail: this branch ships no product circuit. The Product variant
        // exists so callers compile. Restoring the product prover is a separate
        // effort.
        (ZkPublicStatement::ProductV1(_), ZkMdocWitness::ProductV1(_)) => {
            Err(ZkError::UnsupportedProofSystem)
        }
        _ => Err(ZkError::UnsupportedProofSystem),
    }
}

/// Verify the theorem selected by the tagged public statement.
#[uniffi::export]
pub fn verify_identity(
    statement: ZkPublicStatement,
    proof: Vec<u8>,
) -> Result<ZkVerifyResult, ZkError> {
    match statement {
        ZkPublicStatement::Ts13DemoV1(statement) => {
            with_proof_runtime(IdentityError::ProofVerificationFailed, move || {
                ts13_demo::verify_identity_inner(&statement, &proof)
            })
            .map(|()| ZkVerifyResult { ok: true })
            .map_err(ZkError::from)
        }
        ZkPublicStatement::ProductV1(_) => Err(ZkError::UnsupportedProofSystem),
    }
}

/// The ZK identity system this SDK build implements. This branch links only
/// the ML-DSA prover.
#[uniffi::export]
pub fn zk_system() -> ZkSystemKind {
    ZkSystemKind::MlDsa
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uses_the_canonical_worker_count() {
        let workers = with_proof_runtime(IdentityError::ProofGenerationFailed, || {
            Ok(rayon::current_num_threads())
        })
        .expect("the canonical proof runtime must start");

        assert_eq!(workers, PROOF_WORKER_COUNT);
    }

    #[test]
    fn predicate_mode_tokens_round_trip() {
        for mode in [
            PredicateMode::Age,
            PredicateMode::Nat,
            PredicateMode::And,
            PredicateMode::Or,
        ] {
            assert_eq!(
                predicate_mode_from_token(predicate_mode_token(mode)),
                Some(mode)
            );
        }
        assert_eq!(predicate_mode_from_token("nope".to_string()), None);
        assert_eq!(nat_mode_token(NatMode::Any), "any");
    }

    #[test]
    fn this_build_is_mldsa() {
        assert_eq!(zk_system(), ZkSystemKind::MlDsa);
    }

    #[test]
    fn default_circuit_hash_is_the_canonical_pin_hex() {
        assert_eq!(ts13_default_circuit_hash().len(), 64);
        assert!(is_lower_hex_sha256(&ts13_default_circuit_hash()));
        assert_eq!(
            ts13_default_circuit_hash(),
            lower_hex(&ts13_demo_circuit_hash())
        );
        assert_eq!(
            ts13_demo_circuit_hash(),
            eu_id_prover::ts13_demo_artifact_constants::TS13_DEMO_CIRCUIT_HASH.to_vec()
        );
    }

    #[test]
    fn product_variant_fails_closed() {
        let statement = ProductPublicStatementV1 {
            spec_id: "stwo-euid-pid-v1".to_string(),
            version: 1,
            doctype: TS13_PID_DOCTYPE.to_string(),
            namespace: TS13_PID_NAMESPACE.to_string(),
            issuer_key: IssuerKey::MlDsa {
                pk_hash: vec![0u8; 32],
            },
            today_epoch_day: 20_000,
            nonce: vec![1, 2, 3],
            predicate_mode: PredicateMode::Age,
            age_threshold_years: Some(18),
            accepted_numeric_countries: None,
            nat_mode: NatMode::Any,
        };
        let witness = ProductMdocWitnessV1 {
            document: vec![0xA0],
            trusted_issuers: TrustedIssuers::PublicKeys(vec![]),
        };
        assert_eq!(
            prove_identity(
                ZkPublicStatement::ProductV1(statement.clone()),
                ZkMdocWitness::ProductV1(witness),
            ),
            Err(ZkError::UnsupportedProofSystem)
        );
        assert!(matches!(
            verify_identity(ZkPublicStatement::ProductV1(statement), vec![0u8; 8]),
            Err(ZkError::UnsupportedProofSystem)
        ));
    }

    #[test]
    fn mismatched_variant_pair_fails_closed() {
        let witness = ZkMdocWitness::Ts13DemoV1(IdentityWitness {
            document: vec![0xA0],
            revocation_id_lo: 0,
            revocation_id_hi: 1,
            revocation_signature: vec![0u8; 4],
        });
        let statement = ProductPublicStatementV1 {
            spec_id: "stwo-euid-pid-v1".to_string(),
            version: 1,
            doctype: TS13_PID_DOCTYPE.to_string(),
            namespace: TS13_PID_NAMESPACE.to_string(),
            issuer_key: IssuerKey::MlDsa {
                pk_hash: vec![0u8; 32],
            },
            today_epoch_day: 20_000,
            nonce: Vec::new(),
            predicate_mode: PredicateMode::Age,
            age_threshold_years: Some(18),
            accepted_numeric_countries: None,
            nat_mode: NatMode::Any,
        };
        assert_eq!(
            prove_identity(ZkPublicStatement::ProductV1(statement), witness),
            Err(ZkError::UnsupportedProofSystem)
        );
    }

    fn supported_request() -> Ts13PresentationRequest {
        Ts13PresentationRequest {
            credential_format: TS13_CREDENTIAL_FORMAT.to_string(),
            zk_system_id: TS13_SYSTEM_ID.to_string(),
            doctype: TS13_PID_DOCTYPE.to_string(),
            namespace: TS13_PID_NAMESPACE.to_string(),
            circuit_hash: ts13_default_circuit_hash(),
            num_attributes: TS13_NUM_ATTRIBUTES,
            max_mso_payload_bytes: 0,
            max_attribute_bytes: 0,
            max_attribute_item_bytes: 0,
            max_requested_digest_id: 0,
            value_digests_scan_log_size: 0,
            value_digests_scan_max_items: 0,
            value_digests_scan_preprocessed_cols: 0,
            value_digests_scan_trace_cols: 0,
            value_digests_scan_relation_sites: 0,
            value_digests_scan_interaction_cols: 0,
            country_code_dataset: String::new(),
            country_code_table_log_size: 0,
            country_code_count: 0,
            country_code_table_preprocessed_cols: 0,
            country_code_table_trace_cols: 0,
            country_code_table_interaction_cols: 0,
            country_code_table_sha256: vec![0u8; 32],
            max_issuer_mldsa_message_bytes: 0,
            max_device_mldsa_message_bytes: 0,
            merged_sha_slot_log: 0,
            merged_sha_log_n_rows: 0,
            potential_issuers: TS13_POTENTIAL_ISSUERS,
            revocation_enabled: TS13_REVOCATION_ENABLED,
            revocation_id_width_bytes: TS13_REVOCATION_ID_WIDTH_BYTES,
            device_auth_profile: TS13_DEVICE_AUTH_PROFILE.to_string(),
            current_date_epoch_day: 20_000,
            session_transcript: vec![0x83, 0xF6, 0xF6, 0x80],
            trusted_issuer_hashes: vec![sha256_hex(b"issuer")],
            revocation_public_key: vec![0u8; ML_DSA_65_PUBLIC_KEY_BYTES],
            revocation_epoch: 17,
        }
    }

    #[test]
    fn validate_rejects_jwt_and_foreign_system_and_stale_hash() {
        let mut request = supported_request();
        assert!(ts13_validate_presentation_request(&request).is_ok());

        request.credential_format = TS13_UNSUPPORTED_JWT_FORMAT.to_string();
        assert!(matches!(
            ts13_validate_presentation_request(&request),
            Err(ZkError::InvalidInput(_))
        ));

        let mut request = supported_request();
        request.zk_system_id = TS13_LONGFELLOW_SYSTEM_ID.to_string();
        assert!(matches!(
            ts13_validate_presentation_request(&request),
            Err(ZkError::InvalidInput(_))
        ));

        let mut request = supported_request();
        request.circuit_hash = sha256_hex(b"stale");
        assert!(matches!(
            ts13_validate_presentation_request(&request),
            Err(ZkError::InvalidInput(_))
        ));
    }

    #[test]
    fn request_binding_hash_is_deterministic_and_input_sensitive() {
        let request = supported_request();
        assert_eq!(
            ts13_request_binding_hash(&request),
            ts13_request_binding_hash(&request)
        );
        let mut changed = request.clone();
        changed.revocation_epoch += 1;
        assert_ne!(
            ts13_request_binding_hash(&request),
            ts13_request_binding_hash(&changed)
        );
    }

    #[test]
    fn build_zk_document_binds_the_request() {
        let request = supported_request();
        let document =
            ts13_build_zk_document(request.clone(), canonical_ts13_disclosures(), vec![1, 2, 3])
                .expect("build");
        assert_eq!(document.doc_type, request.doctype);
        assert_eq!(
            document.request_binding_hash,
            ts13_request_binding_hash(&request)
        );
    }

    #[test]
    fn proof_envelope_size_limit_is_strict() {
        let request = supported_request();
        let request_binding_hash = ts13_request_binding_hash(&request);
        let encoded = bincode::serialize(&Ts13ProofEnvelope {
            envelope_format: TS13_ENVELOPE_FORMAT_V4,
            request_binding_hash: request_binding_hash.clone(),
            issuer_public_key: vec![7; ML_DSA_65_PUBLIC_KEY_BYTES],
            identity_envelope: vec![9; 32],
        })
        .expect("small proof envelope serializes");
        let decoded = decode_ts13_proof_envelope(&encoded).expect("small proof envelope decodes");
        assert_eq!(decoded.request_binding_hash, request_binding_hash);

        let oversized = vec![0; MAX_TS13_DOCUMENT_PROOF_BYTES + 1];
        assert!(matches!(
            decode_ts13_proof_envelope(&oversized),
            Err(ZkError::Verify(_))
        ));

        let document =
            ts13_build_zk_document(request.clone(), canonical_ts13_disclosures(), oversized)
                .expect("document builder leaves proof verification to the verifier");
        assert!(ts13_document_matches_request(&request, &document));
        assert_eq!(ts13_verify_zk_document(&request, &document), Ok(false));
    }
}
