//! EU-ID ZK SDK — the prover/verifier data contract, exposed to Kotlin/Swift via
//! UniFFI.
//!
//! This crate is the *single* place the canonical statement encoding and the
//! prove/verify entry points live (see the integration plan, §5/§6). Both the
//! wallet (prove) and the verifier (verify) call this same code, so the wire
//! format is structurally impossible to drift — there is no second
//! implementation to disagree with.
//!
//! The product API is the mdoc PID path: [`prove_identity`] accepts the full
//! wallet-returned CBOR document plus verifier trust roots, calls
//! `eu_id_prover::prove_mdoc`, and returns a proof envelope that
//! [`verify_identity`] checks through `eu_id_prover::verify_mdoc`.
//!
//! ## What the proof binds (§9.2)
//! `prove_identity` runs the product mdoc prover and returns an
//! [`MdocProofEnvelope`]: the zstd-compressed, bincode-serialized mdoc proof,
//! the verifier-facing mdoc statement, and the canonical-CBOR bytes of the full
//! [`ZkPublicStatement`]. The two layers bind complementary things:
//!
//! - **The mdoc proof** binds the issuer key, policy, session transcript, issuer
//!   and device `(r, s)` signatures, and statement offsets. Attribute digests
//!   and the device key are private witness values bound in-circuit.
//! - **The envelope** binds the SDK contract fields (`nonce` /
//!   `SessionTranscript`, `doctype`, `namespace`, `spec_id`, and `version`) so
//!   verifier-side request drift is rejected before the inner proof is trusted.
//!
//! The combined prover overflows a small default thread stack (`EXC_BAD_ACCESS`
//! on device — see ROADMAP_E2E §7.2), so both entry points run the heavy work on
//! a dedicated large-stack thread the SDK owns; the apps call the UniFFI fn
//! synchronously and do no thread handling of their own.

// One allocator for every prover entry point on-device: mimalloc. See
// eu-id-ffi — same rationale, this crate is its own cdylib link unit.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;
use ciborium::value::Value;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

uniffi::setup_scaffolding!();

// The pure contract↔prover translation layer (§9.1): `to_policy` builds the
// prover's public policy from the UniFFI statement. Wired into the production
// prove/verify bodies below (§9.2).
mod mapping;
// Compile-parity stubs for the ML-DSA-only `demo_*` surface (see demo.rs).
mod demo;

/// Which predicate(s) the statement asserts.
///
/// `Age` / `Nat` activate a single predicate; `And` / `Or` combine both. The
/// corresponding optional fields on [`ZkPublicStatement`] must be present for
/// whichever predicates are active.
#[derive(uniffi::Enum, Clone, Copy, Debug, PartialEq, Eq)]
pub enum PredicateMode {
    Age,
    Nat,
    And,
    Or,
}

impl PredicateMode {
    /// Stable string token used in the canonical CBOR (`predicate_mode`).
    fn as_token(self) -> &'static str {
        match self {
            PredicateMode::Age => "age",
            PredicateMode::Nat => "nat",
            PredicateMode::And => "and",
            PredicateMode::Or => "or",
        }
    }

    /// Inverse of [`PredicateMode::as_token`]. Returns `None` for unknown tokens.
    fn from_token(token: &str) -> Option<PredicateMode> {
        match token {
            "age" => Some(PredicateMode::Age),
            "nat" => Some(PredicateMode::Nat),
            "and" => Some(PredicateMode::And),
            "or" => Some(PredicateMode::Or),
            _ => None,
        }
    }

    fn uses_age(self) -> bool {
        matches!(
            self,
            PredicateMode::Age | PredicateMode::And | PredicateMode::Or
        )
    }

    fn uses_nat(self) -> bool {
        matches!(
            self,
            PredicateMode::Nat | PredicateMode::And | PredicateMode::Or
        )
    }
}

/// Nationality membership mode. Only [`NatMode::Any`] is implemented this
/// iteration (prove ∃ a held nationality ∈ accepted set); `Subset` is reserved
/// for forward-compat — see the plan §0.
#[derive(uniffi::Enum, Clone, Copy, Debug, PartialEq, Eq)]
pub enum NatMode {
    Any,
    // Subset (future)
}

impl NatMode {
    /// Stable string token used in the canonical CBOR (`nat.mode`).
    fn as_token(self) -> &'static str {
        match self {
            NatMode::Any => "any",
        }
    }
}

// ---------------------------------------------------------------------------
// Contract surface — the shared identifiers/keys and small helpers that BOTH
// the wallet and the verifier must agree on. They live here (not duplicated in
// each app) so there is one source of truth. Consumed from Kotlin/Swift via the
// generated bindings.
//
// Note: these include EUDI-mdoc *identifiers* (namespace, element ids, doctype)
// as plain string values. This crate still does not depend on / parse mdoc — the
// credential extraction stays app-side; the apps only read these strings to know
// what to extract.
// ---------------------------------------------------------------------------

/// All shared contract identifiers and `ZkSystemSpec.params` keys, in one place.
/// Fetch once via [`zk_contract_v1`] and reference the fields instead of hardcoding
/// strings in either app.
#[derive(uniffi::Record, Clone, Debug)]
pub struct ZkContract {
    /// Must equal the verifier's requested `ZkSystemSpec.system`.
    pub system_name: String,
    pub spec_id_pid: String,
    pub pid_namespace: String,
    pub doctype_pid: String,
    pub element_birth_date: String,
    pub element_nationality: String,
    // ZkSystemSpec.params keys (the verifier↔wallet contract).
    pub param_predicate_mode: String,
    pub param_min_age: String,
    pub param_accepted_countries: String,
    pub param_nat_mode: String,
    pub param_version: String,
    pub param_num_attributes: String,
    pub param_circuit_hash: String,
    /// Synthetic result claim id for the nationality predicate.
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
    pub revocation_public_key_x: Vec<u8>,
    pub revocation_public_key_y: Vec<u8>,
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

/// The frozen contract constants. Single source of truth for both apps.
#[uniffi::export]
pub fn zk_contract_v1() -> ZkContract {
    ZkContract {
        system_name: "stwo-euid-v1".to_string(),
        spec_id_pid: "stwo-euid-pid-v1".to_string(),
        pid_namespace: "eu.europa.ec.eudi.pid.1".to_string(),
        doctype_pid: "eu.europa.ec.eudi.pid.1".to_string(),
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
            "revocation_public_key_x".into(),
            Value::Bytes(request.revocation_public_key_x.clone()),
        ),
        (
            "revocation_public_key_y".into(),
            Value::Bytes(request.revocation_public_key_y.clone()),
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
        if request.zk_system_id == TS13_LONGFELLOW_SYSTEM_ID {
            return Err(ZkError::InvalidInput(
                "unsupported system: longfellow-libzk-v1 is libzk-only".to_string(),
            ));
        }
        return Err(ZkError::InvalidInput(format!(
            "unsupported zkSystemId: {}",
            request.zk_system_id
        )));
    }
    if !ts13_tuple_is_supported(request) {
        return Err(ZkError::InvalidInput(
            "unsupported TS13 tuple; no circuit_hash lookup entry".to_string(),
        ));
    }
    let expected_hash = ts13_default_circuit_hash();
    if request.circuit_hash != expected_hash {
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
    if request.trusted_issuer_hashes.len() != request.potential_issuers as usize {
        return Err(ZkError::InvalidInput(
            "trusted issuer set does not match TS13 tuple".to_string(),
        ));
    }
    if request
        .trusted_issuer_hashes
        .iter()
        .any(|hash| hash.is_empty())
    {
        return Err(ZkError::InvalidInput(
            "trusted issuer hashes must be non-empty".to_string(),
        ));
    }
    if request.revocation_public_key_x.len() != 32 || request.revocation_public_key_y.len() != 32 {
        return Err(ZkError::InvalidInput(
            "revocation public key coordinates must be 32 bytes".to_string(),
        ));
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

/// The SDK's semantic version — the Cargo crate version, baked in at compile
/// time via `CARGO_PKG_VERSION`. Since the crate inherits its version from the
/// workspace (`version.workspace = true`), this is the same value the published
/// AAR / JVM jar carry, so a consumer can assert the native lib it loaded matches
/// the artifact it depends on.
#[uniffi::export]
pub fn sdk_version() -> String {
    env!("CARGO_PKG_VERSION").to_string()
}

/// The synthetic result claim id for an age predicate, e.g. `age_over_18`.
#[uniffi::export]
pub fn result_age_over(min_age: u32) -> String {
    format!("age_over_{min_age}")
}

/// Construct a [`PredicateMode`] from its canonical token (the value carried in
/// `ZkSystemSpec.params["predicate_mode"]`). Returns `None` for unknown tokens.
///
/// UniFFI exposes this as a top-level function (enums can't carry exported
/// inherent methods), which is the equivalent of `PredicateMode::from(string)`.
#[uniffi::export]
pub fn predicate_mode_from_token(token: String) -> Option<PredicateMode> {
    PredicateMode::from_token(&token)
}

/// The canonical token for a [`PredicateMode`] (inverse of [`predicate_mode_from_token`]).
#[uniffi::export]
pub fn predicate_mode_token(mode: PredicateMode) -> String {
    mode.as_token().to_string()
}

/// Whether the mode activates the age predicate.
#[uniffi::export]
pub fn predicate_mode_uses_age(mode: PredicateMode) -> bool {
    mode.uses_age()
}

/// Whether the mode activates the nationality predicate.
#[uniffi::export]
pub fn predicate_mode_uses_nat(mode: PredicateMode) -> bool {
    mode.uses_nat()
}

/// The canonical token for a [`NatMode`] (`nat.mode`).
#[uniffi::export]
pub fn nat_mode_token(mode: NatMode) -> String {
    mode.as_token().to_string()
}

/// ISO-3166-1 alpha-2 → numeric. Converts an mdoc nationality string (e.g.
/// `"GR"`) into the numeric code the nat circuit and the accepted-set use.
///
/// Backed by the `celes` crate (full ISO 3166-1 coverage, case-insensitive).
/// Returns `None` for an unknown code.
#[uniffi::export]
pub fn iso_alpha2_to_numeric(alpha2: String) -> Option<u32> {
    celes::Country::from_alpha2(alpha2)
        .ok()
        .map(|c| c.value as u32)
}

/// The PUBLIC statement `I` — the instance shared byte-identically between
/// prover and verifier. This is what [`encode_statement`] serializes; the
/// resulting bytes are folded into Fiat-Shamir, so any representation drift
/// fails verification.
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
    /// "Today" as an epoch-day integer (days since 1970-01-01).
    pub today_epoch_day: i32,
    /// Freshness nonce (the mdoc SessionTranscript).
    pub nonce: Vec<u8>,
    pub predicate_mode: PredicateMode,
    /// Present iff the age predicate is active.
    pub age_threshold_years: Option<u32>,
    /// ISO-3166 numeric codes: sorted, unique. Present iff the nat predicate is
    /// active.
    pub accepted_numeric_countries: Option<Vec<u32>>,
    /// Reserved; only [`NatMode::Any`] for now.
    pub nat_mode: NatMode,
}

/// The PRIVATE witness for the production identity proof path.
#[derive(uniffi::Record, Clone, Debug)]
pub struct ZkMdocWitness {
    /// Full CBOR mdoc document returned by the wallet.
    pub document: Vec<u8>,
    /// Trusted issuers (x5chain certs for P-256, pinned `pkEncode`s for ML-DSA).
    pub trusted_issuers: TrustedIssuers,
}

/// The verdict returned by [`verify_identity`].
#[derive(uniffi::Record, Clone, Debug)]
pub struct ZkVerifyResult {
    pub ok: bool,
    // age_ok: Option<bool>, nat_ok: Option<bool>  (future, per-predicate detail)
}

/// Errors surfaced across the FFI boundary.
#[derive(uniffi::Error, thiserror::Error, Debug)]
pub enum ZkError {
    #[error("invalid input: {0}")]
    InvalidInput(String),
    #[error("proving failed: {0}")]
    Prove(String),
    #[error("verification failed: {0}")]
    Verify(String),
}

/// Deterministic-CBOR encoding of the public statement `I` — the SINGLE source
/// of truth, used by both prove and verify (and by both apps).
///
/// Determinism comes from building an explicitly-ordered `Value::Map`: ciborium
/// preserves the insertion order of map entries, and we fix that order here. The
/// optional `age` / `nat` sub-maps appear only when their predicate is active,
/// matching the canonical shape in the plan §2.3.
///
/// This is a free function (not `#[uniffi::export]`ed) because callers only ever
/// need it transitively through prove/verify; exposing it would invite a second
/// caller and undermine the "one encoder" guarantee.
fn encode_statement(s: &ZkPublicStatement) -> Vec<u8> {
    let mut entries: Vec<(Value, Value)> = vec![
        ("v".into(), Value::from(s.version)),
        ("spec_id".into(), s.spec_id.as_str().into()),
        ("doctype".into(), s.doctype.as_str().into()),
        ("namespace".into(), s.namespace.as_str().into()),
        (
            "issuer_key".into(),
            match &s.issuer_key {
                // Byte-identical to the pre-unification encoding — existing proofs still verify.
                IssuerKey::P256 { x, y } => Value::Map(vec![
                    ("crv".into(), "P-256".into()),
                    ("x".into(), Value::Bytes(x.clone())),
                    ("y".into(), Value::Bytes(y.clone())),
                ]),
                IssuerKey::MlDsa { pk_hash } => Value::Map(vec![
                    ("alg".into(), "ML-DSA-65".into()),
                    ("pk_hash".into(), Value::Bytes(pk_hash.clone())),
                ]),
            },
        ),
        ("today".into(), Value::from(s.today_epoch_day)),
        ("nonce".into(), Value::Bytes(s.nonce.clone())),
        ("predicate_mode".into(), s.predicate_mode.as_token().into()),
    ];

    if let Some(threshold) = s.age_threshold_years {
        entries.push((
            "age".into(),
            Value::Map(vec![("threshold_years".into(), Value::from(threshold))]),
        ));
    }

    if let Some(accepted) = &s.accepted_numeric_countries {
        let accepted_arr = accepted.iter().map(|&c| Value::from(c)).collect();
        entries.push((
            "nat".into(),
            Value::Map(vec![
                ("mode".into(), s.nat_mode.as_token().into()),
                ("accepted".into(), Value::Array(accepted_arr)),
            ]),
        ));
    }

    let mut out = Vec::new();
    // Writing into a Vec is infallible; a CBOR serialization error here would be
    // a library bug, not bad input, so we surface it as a panic rather than
    // widening every caller's signature.
    ciborium::ser::into_writer(&Value::Map(entries), &mut out)
        .expect("CBOR serialization of ZkPublicStatement is infallible");
    out
}

#[derive(Serialize, Deserialize)]
struct MdocProofEnvelope {
    statement_bytes: Vec<u8>,
    mdoc_statement: eu_id_prover::MdocStatement,
    stark_proof: Vec<u8>,
}

/// Stack size for the dedicated prover/verifier thread. The combined prover
/// overflows the small default worker-thread stack with `EXC_BAD_ACCESS`; 32 MiB
/// is the headroom the FFI harness established on device (ROADMAP_E2E §7.2).
const PROVER_STACK_SIZE: usize = 32 * 1024 * 1024;

/// Run `work` on a dedicated large-stack thread and join it, returning its
/// result.
///
/// The closure owns everything it touches (the statement / witness are moved
/// in), so the thread is `'static`. A panic inside `work` is caught by `join`
/// and surfaced as [`ZkError::Prove`] — it never unwinds across the UniFFI
/// boundary (requirement: the spawned thread must not unwind across FFI).
fn on_large_stack<T, F>(work: F) -> Result<T, ZkError>
where
    T: Send + 'static,
    F: FnOnce() -> Result<T, ZkError> + Send + 'static,
{
    let handle = std::thread::Builder::new()
        .name("euid-prover".to_string())
        .stack_size(PROVER_STACK_SIZE)
        .spawn(work)
        .map_err(|e| ZkError::Prove(format!("failed to spawn prover thread: {e}")))?;
    match handle.join() {
        Ok(result) => result,
        Err(_) => Err(ZkError::Prove("prover thread panicked".to_string())),
    }
}

/// Map a prover error to the FFI error. A false statement (under-age,
/// nationality not in the accepted set) is rejected at witness generation, so it
/// surfaces here as a failed *prove* — not a panic and not a verify failure.
fn map_prover_error(e: eu_id_prover::Error) -> ZkError {
    use eu_id_prover::Error::*;
    match e {
        // "No honest witness exists" cases: the holder genuinely does not
        // satisfy the predicate, so the prover refuses at witness generation
        // (not a verify failure). Lead with a human explanation — the raw Debug
        // detail (e.g. `NatPrepare(Input(NoMatch))`) is kept for diagnostics.
        AgePrepare(_) => ZkError::Prove(format!(
            "the holder does not satisfy the age predicate (likely under the requested minimum age) [{e:?}]"
        )),
        NatPrepare(_) => ZkError::Prove(format!(
            "the holder's nationality is not in the accepted set [{e:?}]"
        )),
        // Other witness-generation / proving failures (bad signature, internal).
        P256Prepare(_) | SignatureInvalid | Prove(_) | Mdoc(_) | CoprocessorWitness(_) => {
            ZkError::Prove(format!("{e:?}"))
        }
        // Verifier-side rejections (only reachable from the verify path).
        P256InstanceMismatch | IssuerKeyMismatch | AgePolicyMismatch | NatPolicyMismatch
        | WeakConfig { .. } | CoprocessorMissing | CoprocessorInstanceCount { .. }
        | CoprocessorProof(_) | Verify(_) | PreprocessedRootMismatch { .. }
        | ShapeTooLarge { .. } => {
            ZkError::Verify(format!("{e:?}"))
        }
    }
}

/// zstd level for the FFI transport envelope. Measured on the full TS13 N=1
/// proof (4.66 MB): level 12 compresses to 3.95 MB in ~80 ms vs bzip2-9's
/// 4.06 MB in ~390 ms, and decompresses ~8× faster — smaller wire payload AND
/// less prover/verifier wall time. Level 19 saves only ~20 KB more for ~4× the
/// compression time.
const PROOF_ZSTD_LEVEL: i32 = 12;

/// Compress the raw bincode STARK proof for the FFI transport envelope.
fn compress_stark_proof_for_ffi(raw_bincode: &[u8]) -> Result<Vec<u8>, ZkError> {
    zstd::bulk::compress(raw_bincode, PROOF_ZSTD_LEVEL)
        .map_err(|e| ZkError::Prove(format!("failed to compress proof: {e}")))
}

/// Decompress the FFI transport proof payload back to raw bincode bytes.
fn decompress_stark_proof_from_ffi(compressed: &[u8]) -> Result<Vec<u8>, ZkError> {
    zstd::stream::decode_all(compressed)
        .map_err(|e| ZkError::Verify(format!("failed to decompress proof: {e}")))
}

/// The disclosed-attribute set the SDK's mdoc PID path requests, in a fixed
/// order: `birth_date` under `AgeOver`, then `nationality` under `Alpha2Set`.
/// Single source of truth shared by the prove side (to build the request) and
/// the verify side (to pin the envelope statement's disclosed set), so the two
/// cannot drift.
///
/// The set is bound to the statement's predicate mode: an age-only
/// presentation must not require the credential to disclose (or even contain)
/// the nationality element, and vice versa — a selectively-disclosed wallet
/// document carries only the requested elements, so requesting the inactive
/// leg fails extraction with `ElementMissing`.
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
    let trusted_issuer_certificates = match &witness.trusted_issuers {
        TrustedIssuers::Certificates(certs) => certs.clone(),
        TrustedIssuers::PublicKeys(_) => {
            return Err(ZkError::InvalidInput(
                "this build proves P-256; witness needs TrustedIssuers::Certificates".to_string(),
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
        trusted_issuer_certificates,
        trusted_issuer_public_keys: Vec::new(),
        device_authentication_profile:
            eu_id_prover::mdoc::MdocDeviceAuthenticationProfile::Iso180135,
    })
}

fn mdoc_statement_matches_public_statement(
    mdoc_statement: &eu_id_prover::MdocStatement,
    statement: &ZkPublicStatement,
) -> Result<bool, ZkError> {
    let policy = mapping::to_policy(statement)?;
    if mdoc_statement.policy != policy {
        return Ok(false);
    }

    let (issuer_key_x, issuer_key_y) = match &statement.issuer_key {
        IssuerKey::P256 { x, y } => (x, y),
        IssuerKey::MlDsa { .. } => {
            return Err(ZkError::InvalidInput(
                "this build verifies P-256; statement needs IssuerKey::P256".to_string(),
            ))
        }
    };
    let issuer_x: [u8; 32] = issuer_key_x
        .as_slice()
        .try_into()
        .map_err(|_| ZkError::InvalidInput("issuer_key P-256 x must be 32 bytes".to_string()))?;
    let issuer_y: [u8; 32] = issuer_key_y
        .as_slice()
        .try_into()
        .map_err(|_| ZkError::InvalidInput("issuer_key P-256 y must be 32 bytes".to_string()))?;
    if mdoc_statement.issuer_public_key.x.0 != issuer_x
        || mdoc_statement.issuer_public_key.y.0 != issuer_y
    {
        return Ok(false);
    }

    let expected_device_hash = eu_id_prover::mdoc::device_authentication_sig_structure_hash(
        &statement.nonce,
        &statement.doctype,
    )
    .map_err(|e| ZkError::InvalidInput(format!("invalid DeviceAuthentication input: {e:?}")))?;
    if mdoc_statement.device_message_hash.0 != expected_device_hash {
        return Ok(false);
    }

    // Caller-arg binding (mirrors the historical P-256 fix): the disclosed
    // attribute set, predicate-leg activation, element identity, and disclosure
    // modes are all prover-supplied fields of the envelope statement. The policy
    // check above binds only the *values* (min_age, accepted set); it does NOT
    // force the predicate to actually be proven. Pin these fields to the SDK's
    // OWN request so a prover cannot
    //   - drop the age (or nationality) leg by leaving its index `None`, which
    //     makes the circuit gate `proof.age_public == index.map(..)` trivially
    //     pass without the predicate ever being enforced (C1); or
    //   - prove a predicate over the wrong signed element, e.g. `issue_date`
    //     instead of `birth_date` (C2).
    // Fail-closed on ANY divergence from the expected set.
    let expected = expected_mdoc_attributes(statement.predicate_mode);
    if mdoc_statement.attributes.len() != expected.len() {
        return Ok(false);
    }
    for (got, want) in mdoc_statement.attributes.iter().zip(expected.iter()) {
        if got.element_identifier != want.element_identifier || got.mode != want.mode {
            return Ok(false);
        }
    }
    // Each active leg's index must be `Some` and point at the matching
    // disclosed attribute; an inactive leg's index must be `None` (the
    // `position` over the mode-filtered expected set yields exactly that), so
    // cross-mode confusion stays fail-closed in both directions.
    let expected_age_index = expected
        .iter()
        .position(|a| matches!(a.mode, eu_id_prover::mdoc::MdocDisclosureMode::AgeOver));
    let expected_nat_index = expected
        .iter()
        .position(|a| matches!(a.mode, eu_id_prover::mdoc::MdocDisclosureMode::Alpha2Set));
    if mdoc_statement.age_attribute_index != expected_age_index
        || mdoc_statement.nationality_attribute_index != expected_nat_index
    {
        return Ok(false);
    }

    Ok(true)
}

/// Prove an identity presentation from a full CBOR mdoc and trusted issuer
/// roots using [`eu_id_prover::prove_mdoc`].
///
/// The returned envelope binds the caller's complete public statement to the
/// production mdoc proof and runs on the SDK's dedicated large-stack thread.
#[uniffi::export]
pub fn prove_identity(
    statement: ZkPublicStatement,
    witness: ZkMdocWitness,
) -> Result<Vec<u8>, ZkError> {
    on_large_stack(move || {
        let policy = mapping::to_policy(&statement)?;
        let request = mdoc_request(&statement, &witness)?;
        let (proof, mdoc_statement) = eu_id_prover::prove_mdoc(&witness.document, &request, policy)
            .map_err(map_prover_error)?;
        let stark_proof_bincode = bincode::serialize(&proof)
            .map_err(|e| ZkError::Prove(format!("failed to serialize mdoc proof: {e}")))?;
        let stark_proof = compress_stark_proof_for_ffi(&stark_proof_bincode)?;

        let envelope = MdocProofEnvelope {
            statement_bytes: encode_statement(&statement),
            mdoc_statement,
            stark_proof,
        };
        bincode::serialize(&envelope)
            .map_err(|e| ZkError::Prove(format!("failed to serialize mdoc proof envelope: {e}")))
    })
}

/// Verify a production identity proof against the caller's public statement.
///
/// Malformed or mismatched proof bytes fail closed with `ok = false`.
#[uniffi::export]
pub fn verify_identity(
    statement: ZkPublicStatement,
    proof: Vec<u8>,
) -> Result<ZkVerifyResult, ZkError> {
    on_large_stack(move || {
        let envelope: MdocProofEnvelope = match bincode::deserialize(&proof) {
            Ok(envelope) => envelope,
            Err(_) => return Ok(ZkVerifyResult { ok: false }),
        };
        if envelope.statement_bytes != encode_statement(&statement) {
            return Ok(ZkVerifyResult { ok: false });
        }
        if !mdoc_statement_matches_public_statement(&envelope.mdoc_statement, &statement)? {
            return Ok(ZkVerifyResult { ok: false });
        }

        let stark_proof_bincode = match decompress_stark_proof_from_ffi(&envelope.stark_proof) {
            Ok(bytes) => bytes,
            Err(_) => return Ok(ZkVerifyResult { ok: false }),
        };
        let stark_proof: eu_id_prover::MdocProof = match bincode::deserialize(&stark_proof_bincode)
        {
            Ok(stark_proof) => stark_proof,
            Err(_) => return Ok(ZkVerifyResult { ok: false }),
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

    fn ts13_request() -> Ts13PresentationRequest {
        Ts13PresentationRequest {
            credential_format: "mso_mdoc_zk".to_string(),
            zk_system_id: "stwo-euid-v1".to_string(),
            doctype: "eu.europa.ec.eudi.pid.1".to_string(),
            namespace: "eu.europa.ec.eudi.pid.1".to_string(),
            circuit_hash: ts13_default_circuit_hash(),
            preprocessed_root: ts13_default_preprocessed_root(),
            num_attributes: 1,
            max_mdoc_bytes: 16_384,
            max_attribute_bytes: 32,
            potential_issuers: 1,
            revocation_enabled: true,
            revocation_id_width_bytes: 8,
            device_auth_profile: "iso18013-5".to_string(),
            current_date_epoch_day: 20_637,
            session_transcript: vec![1, 2, 3, 4],
            trusted_issuer_hashes: vec!["issuer-root-sha256".to_string()],
            revocation_public_key_x: vec![0x11; 32],
            revocation_public_key_y: vec![0x22; 32],
            revocation_epoch: 42,
        }
    }

    #[test]
    fn ts13_presentation_round_trip() {
        let request = ts13_request();
        let disclosed = vec![Ts13DisclosedAttribute {
            namespace: request.namespace.clone(),
            name: "age_over_18".to_string(),
            value_cbor: vec![0xf5],
            disclosure: Ts13DisclosureKind::Equality,
        }];

        let document =
            ts13_build_zk_document(request.clone(), disclosed.clone(), b"proof".to_vec()).unwrap();

        assert_eq!(document.doc_type, request.doctype);
        assert_eq!(document.zk_system_id, "stwo-euid-v1");
        assert_eq!(document.circuit_hash, request.circuit_hash);
        assert_eq!(document.disclosed_attributes, disclosed);
        assert!(ts13_verify_zk_document(&request, &document).unwrap());
    }

    #[test]
    fn ts13_presentation_rejects_unknown_zk_system_id() {
        let mut request = ts13_request();
        request.zk_system_id = "unknown-zk-system".to_string();

        assert!(matches!(
            ts13_validate_presentation_request(&request),
            Err(ZkError::InvalidInput(message)) if message.contains("zkSystemId")
        ));
    }

    #[test]
    fn ts13_presentation_rejects_longfellow_only_request() {
        let mut request = ts13_request();
        request.zk_system_id = "longfellow-libzk-v1".to_string();

        assert!(matches!(
            ts13_validate_presentation_request(&request),
            Err(ZkError::InvalidInput(message)) if message.contains("libzk-only")
        ));
    }

    #[test]
    fn ts13_presentation_rejects_unknown_circuit_hash() {
        let mut request = ts13_request();
        request.circuit_hash = "00".repeat(32);

        assert!(matches!(
            ts13_validate_presentation_request(&request),
            Err(ZkError::InvalidInput(message)) if message.contains("circuit_hash")
        ));
    }

    #[test]
    fn ts13_presentation_rejects_tuple_mismatch() {
        let request = ts13_request();
        let document =
            ts13_build_zk_document(request.clone(), Vec::new(), b"proof".to_vec()).unwrap();
        let mut other_request = request;
        other_request.max_mdoc_bytes += 1;

        assert!(!ts13_verify_zk_document(&other_request, &document).unwrap());
    }

    #[test]
    fn ts13_presentation_rejects_caller_policy_drift() {
        let request = ts13_request();
        let document =
            ts13_build_zk_document(request.clone(), Vec::new(), b"proof".to_vec()).unwrap();
        let mut other_request = request;
        other_request.current_date_epoch_day += 1;

        assert!(!ts13_verify_zk_document(&other_request, &document).unwrap());
    }

    #[test]
    fn ts13_presentation_rejects_revocation_policy_drift() {
        let request = ts13_request();
        let document =
            ts13_build_zk_document(request.clone(), Vec::new(), b"proof".to_vec()).unwrap();
        let mut other_request = request.clone();
        other_request.revocation_epoch += 1;
        assert!(!ts13_verify_zk_document(&other_request, &document).unwrap());

        let mut other_request = request.clone();
        other_request.revocation_public_key_x[0] ^= 1;
        assert!(!ts13_verify_zk_document(&other_request, &document).unwrap());

        let mut other_request = request;
        other_request
            .trusted_issuer_hashes
            .push("extra".to_string());
        assert!(!ts13_verify_zk_document(&other_request, &document).unwrap());
    }

    #[test]
    fn ts13_presentation_rejects_preprocessed_root_drift() {
        let request = ts13_request();
        let document =
            ts13_build_zk_document(request.clone(), Vec::new(), b"proof".to_vec()).unwrap();
        assert_eq!(document.preprocessed_root, request.preprocessed_root);

        let mut other_request = request;
        other_request.preprocessed_root[0] ^= 1;

        assert!(!ts13_verify_zk_document(&other_request, &document).unwrap());
    }

    #[test]
    fn ts13_presentation_rejects_malformed_preprocessed_root() {
        let mut request = ts13_request();
        request.preprocessed_root.pop();

        assert!(matches!(
            ts13_validate_presentation_request(&request),
            Err(ZkError::InvalidInput(message)) if message.contains("preprocessed_root")
        ));
    }

    #[test]
    fn ts13_presentation_rejects_zk_jwt_unsupported() {
        let mut request = ts13_request();
        request.credential_format = "zk-jwt".to_string();

        assert!(matches!(
            ts13_validate_presentation_request(&request),
            Err(ZkError::InvalidInput(message)) if message.contains("unsupported zk-jwt")
        ));
    }

    #[test]
    fn circuit_hash_sdk_lookup_fail_closed() {
        let mut request = ts13_request();
        request.num_attributes = 2;

        assert!(matches!(
            ts13_validate_presentation_request(&request),
            Err(ZkError::InvalidInput(message)) if message.contains("unsupported TS13 tuple")
        ));
    }

    #[test]
    fn ts13_sdk_labels_extension_predicates() {
        let equality = eu_id_prover::mdoc::MdocRequestedAttribute {
            element_identifier: "age_over_18".to_string(),
            mode: eu_id_prover::mdoc::MdocDisclosureMode::ValueEquality(vec![0xf5]),
        };
        let age_extension = eu_id_prover::mdoc::MdocRequestedAttribute {
            element_identifier: "birth_date".to_string(),
            mode: eu_id_prover::mdoc::MdocDisclosureMode::AgeOver,
        };
        let nat_extension = eu_id_prover::mdoc::MdocRequestedAttribute {
            element_identifier: "nationality".to_string(),
            mode: eu_id_prover::mdoc::MdocDisclosureMode::Alpha2Set,
        };

        assert_eq!(
            ts13_disclosure_kind(&equality),
            Ts13DisclosureKind::Equality
        );
        assert_eq!(
            ts13_disclosure_kind(&age_extension),
            Ts13DisclosureKind::Extension
        );
        assert_eq!(
            ts13_disclosure_kind(&nat_extension),
            Ts13DisclosureKind::Extension
        );
    }

    #[test]
    fn ts13_sdk_value_equality_request_maps_to_prover() {
        let ts13_attrs =
            expected_mdoc_attributes_for_profile(MdocRequestProfile::Ts13AgeOver18Equality);
        assert_eq!(ts13_attrs.len(), 1);
        assert_eq!(ts13_attrs[0].element_identifier, "age_over_18");
        assert!(matches!(
            ts13_attrs[0].mode,
            eu_id_prover::mdoc::MdocDisclosureMode::ValueEquality(ref bytes) if bytes == &vec![0xf5]
        ));

        let default_attrs =
            expected_mdoc_attributes_for_profile(MdocRequestProfile::ProductDefault);
        assert_eq!(default_attrs.len(), 2);
        assert!(default_attrs
            .iter()
            .any(|attr| matches!(attr.mode, eu_id_prover::mdoc::MdocDisclosureMode::AgeOver)));
        assert!(default_attrs
            .iter()
            .all(|attr| attr.element_identifier != "age_over_18"));
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

    fn sample_statement() -> ZkPublicStatement {
        ZkPublicStatement {
            spec_id: "stwo-euid-pid-v1".to_string(),
            version: 1,
            doctype: "eu.europa.ec.eudi.pid.1".to_string(),
            namespace: "eu.europa.ec.eudi.pid.1".to_string(),
            issuer_key: IssuerKey::P256 {
                x: vec![0x11; 32],
                y: vec![0x22; 32],
            },
            today_epoch_day: 7305,
            nonce: vec![0xab, 0xcd, 0xef],
            predicate_mode: PredicateMode::And,
            age_threshold_years: Some(18),
            accepted_numeric_countries: Some(vec![56, 196, 300]),
            nat_mode: NatMode::Any,
        }
    }

    fn honest_mdoc_statement() -> (ZkPublicStatement, eu_id_prover::MdocStatement) {
        let fixture = eu_id_prover::mdoc::demo_mdoc_circuit_fixture();
        let issuer_key = fixture.statement.issuer_input.public_key.clone();
        (
            ZkPublicStatement {
                spec_id: "stwo-euid-pid-v1".to_string(),
                version: 1,
                doctype: "eu.europa.ec.eudi.pid.1".to_string(),
                namespace: "eu.europa.ec.eudi.pid.1".to_string(),
                issuer_key: IssuerKey::P256 {
                    x: issuer_key.x.0.to_vec(),
                    y: issuer_key.y.0.to_vec(),
                },
                today_epoch_day: 20637, // 2026-07-03
                nonce: fixture.request.session_transcript,
                predicate_mode: PredicateMode::And,
                age_threshold_years: Some(18),
                accepted_numeric_countries: Some(vec![276, 250]), // DE, FR
                nat_mode: NatMode::Any,
            },
            eu_id_prover::MdocStatement::from_circuit(&fixture.statement),
        )
    }

    fn canonical_v2_mdoc_sdk_fixture() -> (ZkPublicStatement, ZkMdocWitness) {
        let fixture = eu_id_prover::mdoc::demo_mdoc_circuit_fixture();
        let issuer_key = fixture.statement.issuer_input.public_key.clone();
        (
            ZkPublicStatement {
                spec_id: "stwo-euid-pid-v1".to_string(),
                version: 1,
                doctype: fixture.request.doctype,
                namespace: fixture.request.namespace,
                issuer_key: IssuerKey::P256 {
                    x: issuer_key.x.0.to_vec(),
                    y: issuer_key.y.0.to_vec(),
                },
                today_epoch_day: 20637, // 2026-07-03
                nonce: fixture.request.session_transcript,
                predicate_mode: PredicateMode::And,
                age_threshold_years: Some(fixture.statement.policy.min_age_years),
                accepted_numeric_countries: Some(
                    fixture.statement.policy.accepted_nationalities.clone(),
                ),
                nat_mode: NatMode::Any,
            },
            ZkMdocWitness {
                document: fixture.document,
                trusted_issuers: TrustedIssuers::Certificates(
                    fixture.request.trusted_issuer_certificates,
                ),
            },
        )
    }

    #[test]
    fn mdoc_statement_match_recomputes_phase_e_device_authentication_hash() {
        let (statement, mdoc_statement) = honest_mdoc_statement();
        assert!(mdoc_statement_matches_public_statement(&mdoc_statement, &statement).unwrap());

        let mut changed_transcript = statement.clone();
        changed_transcript.nonce = eu_id_prover::mdoc::openid4vp_session_transcript(b"other");
        assert!(
            !mdoc_statement_matches_public_statement(&mdoc_statement, &changed_transcript).unwrap(),
            "transcript drift must change the expected device-auth hash"
        );

        let mut changed_doctype = statement.clone();
        changed_doctype.doctype = "wrong.doctype".to_string();
        assert!(
            !mdoc_statement_matches_public_statement(&mdoc_statement, &changed_doctype).unwrap(),
            "docType drift must change the expected device-auth hash"
        );
    }

    #[test]
    fn mdoc_public_statement_serialization_omits_private_signature_and_device_key_material() {
        let fixture = eu_id_prover::mdoc::demo_mdoc_circuit_fixture();
        let public = eu_id_prover::MdocStatement::from_circuit(&fixture.statement);
        let encoded = bincode::serialize(&public).expect("public mdoc statement serializes");
        assert!(
            !encoded
                .windows(32)
                .any(|window| window == fixture.statement.issuer_input.message_hash.0),
            "issuer z must not be serialized in the public mdoc statement"
        );
        assert!(
            !encoded
                .windows(32)
                .any(|window| window == fixture.statement.issuer_input.signature.r.0),
            "issuer r must not be serialized in the public mdoc statement"
        );
        assert!(
            !encoded
                .windows(32)
                .any(|window| window == fixture.statement.issuer_input.signature.s.0),
            "issuer s must not be serialized in the public mdoc statement"
        );
        assert!(
            !encoded
                .windows(32)
                .any(|window| window == fixture.statement.device_input.public_key.x.0),
            "device qx must not be serialized in the public mdoc statement"
        );
        assert!(
            !encoded
                .windows(32)
                .any(|window| window == fixture.statement.device_input.public_key.y.0),
            "device qy must not be serialized in the public mdoc statement"
        );
        assert!(
            !encoded
                .windows(32)
                .any(|window| window == fixture.statement.device_input.signature.r.0),
            "device r must not be serialized in the public mdoc statement"
        );
        assert!(
            !encoded
                .windows(32)
                .any(|window| window == fixture.statement.device_input.signature.s.0),
            "device s must not be serialized in the public mdoc statement"
        );
    }

    #[test]
    fn mdoc_verify_rejects_dropped_predicate_leg() {
        // C1: a proof that never proved the age (or nationality) predicate leaves
        // its attribute index `None`; the circuit gate then passes trivially. The
        // SDK guard must reject it even though policy / issuer / device all match.
        let (statement, honest) = honest_mdoc_statement();
        assert!(
            mdoc_statement_matches_public_statement(&honest, &statement).unwrap(),
            "honest And statement (both legs present) must be accepted"
        );

        let mut age_dropped = honest.clone();
        age_dropped.age_attribute_index = None;
        assert!(
            !mdoc_statement_matches_public_statement(&age_dropped, &statement).unwrap(),
            "dropping the age predicate leg (index None) must be rejected"
        );

        let mut nat_dropped = honest.clone();
        nat_dropped.nationality_attribute_index = None;
        assert!(
            !mdoc_statement_matches_public_statement(&nat_dropped, &statement).unwrap(),
            "dropping the nationality predicate leg (index None) must be rejected"
        );
    }

    #[test]
    fn mdoc_verify_rejects_element_substitution() {
        // C2: prove the age predicate over the wrong signed element (e.g.
        // `issue_date` instead of `birth_date`). The disclosed element identity
        // must be pinned to the requested contract element.
        let (statement, honest) = honest_mdoc_statement();
        let age_index = honest
            .age_attribute_index
            .expect("honest statement discloses the age attribute");

        let mut wrong_element = honest.clone();
        wrong_element.attributes[age_index].element_identifier = "issue_date".to_string();
        assert!(
            !mdoc_statement_matches_public_statement(&wrong_element, &statement).unwrap(),
            "age predicate over the wrong element_identifier must be rejected"
        );

        let mut wrong_mode = honest.clone();
        wrong_mode.attributes[age_index].mode =
            eu_id_prover::mdoc::MdocDisclosureMode::ValueEquality(vec![0x01]);
        assert!(
            !mdoc_statement_matches_public_statement(&wrong_mode, &statement).unwrap(),
            "age leg disclosed under the wrong mode must be rejected"
        );
    }

    #[test]
    fn mdoc_verify_rejects_attribute_count_mismatch() {
        // Fail-closed on an unexpected disclosed-attribute count (extra or fewer
        // legs than the SDK's own request).
        let (statement, honest) = honest_mdoc_statement();

        let mut extra = honest.clone();
        let extra_attr = extra.attributes[0].clone();
        extra.attributes.push(extra_attr);
        assert!(
            !mdoc_statement_matches_public_statement(&extra, &statement).unwrap(),
            "an extra disclosed attribute must be rejected"
        );

        let mut truncated = honest.clone();
        truncated.attributes.truncate(1);
        assert!(
            !mdoc_statement_matches_public_statement(&truncated, &statement).unwrap(),
            "a missing disclosed attribute must be rejected"
        );
    }

    #[test]
    #[ignore = "runs the product mdoc STWO prover: reproduces the C1 attack end-to-end"]
    fn mdoc_verify_pid_rejects_c1_dropped_age_predicate_end_to_end() {
        // End-to-end C1: build a genuine issuer-signed proof that discloses ONLY
        // the nationality attribute (age omitted), then present it against a
        // mode=And request that demands the age predicate. Pre-fix this returned
        // ok=true (age never proven); post-fix the SDK guard rejects it.
        let demo = eu_id_prover::mdoc::demo_mdoc_circuit_fixture();
        let issuer_key = demo.statement.issuer_input.public_key.clone();

        // Attacker request: nationality only — no AgeOver leg.
        let nat_only_request = eu_id_prover::MdocPidRequest {
            doctype: demo.request.doctype.clone(),
            namespace: demo.request.namespace.clone(),
            attributes: vec![eu_id_prover::mdoc::MdocRequestedAttribute {
                element_identifier: "nationality".to_string(),
                mode: eu_id_prover::mdoc::MdocDisclosureMode::Alpha2Set,
            }],
            birth_date_element: "birth_date".to_string(),
            nationality_element: "nationality".to_string(),
            session_transcript: demo.request.session_transcript.clone(),
            trusted_issuer_certificates: demo.request.trusted_issuer_certificates.clone(),
            trusted_issuer_public_keys: Vec::new(),
            device_authentication_profile:
                eu_id_prover::mdoc::MdocDeviceAuthenticationProfile::Iso180135,
        };
        // Policy whose min_age matches what the mode=And verifier will demand, so
        // the SDK policy-equality check passes.
        let policy = eu_id_prover::Policy {
            current_date: eu_id_prover::Date {
                year: 2026,
                month: 7,
                day: 3,
            },
            min_age_years: 18,
            accepted_nationalities: vec![276, 250],
            accepted_nationalities_alpha2: vec![*b"DE", *b"FR"],
        };
        let (proof, mdoc_statement) =
            eu_id_prover::prove_mdoc(&demo.document, &nat_only_request, policy)
                .expect("nationality-only mdoc proves");
        assert!(
            mdoc_statement.age_attribute_index.is_none(),
            "attack precondition: age predicate leg absent"
        );

        let stark_proof_bincode = bincode::serialize(&proof).unwrap();
        let stark_proof = compress_stark_proof_for_ffi(&stark_proof_bincode).unwrap();

        let claimed_statement = ZkPublicStatement {
            spec_id: "stwo-euid-pid-v1".to_string(),
            version: 1,
            doctype: demo.request.doctype.clone(),
            namespace: demo.request.namespace.clone(),
            issuer_key: IssuerKey::P256 {
                x: issuer_key.x.0.to_vec(),
                y: issuer_key.y.0.to_vec(),
            },
            today_epoch_day: 20637, // 2026-07-03
            nonce: demo.request.session_transcript.clone(),
            predicate_mode: PredicateMode::And,
            age_threshold_years: Some(18),
            accepted_numeric_countries: Some(vec![276, 250]),
            nat_mode: NatMode::Any,
        };
        let envelope = MdocProofEnvelope {
            statement_bytes: encode_statement(&claimed_statement),
            mdoc_statement,
            stark_proof,
        };
        let proof_bytes = bincode::serialize(&envelope).unwrap();

        assert!(
            !verify_identity(claimed_statement, proof_bytes)
                .expect("verification returns")
                .ok,
            "C1 attack (age predicate never proven) must be rejected end-to-end"
        );
    }

    #[test]
    #[ignore = "runs the product mdoc STWO prover over the canonical v2 fixture"]
    fn identity_public_api_round_trips_canonical_v2_fixture() {
        let (statement, witness) = canonical_v2_mdoc_sdk_fixture();
        let proof = prove_identity(statement.clone(), witness).expect("identity proof builds");
        assert!(
            verify_identity(statement, proof)
                .expect("identity verification returns")
                .ok,
            "canonical v2 fixture must verify through the SDK identity API"
        );
    }

    #[test]
    #[ignore = "runs the product mdoc STWO prover: single-predicate modes end-to-end"]
    fn identity_public_api_round_trips_single_predicate_modes() {
        // Regression for the swapped-looking ElementMissing failures: a
        // nationality-only statement must not request (nor require) the
        // birth_date element, and an age-only statement must not require
        // nationality.
        let (base, witness) = canonical_v2_mdoc_sdk_fixture();

        let mut age_only = base.clone();
        age_only.predicate_mode = PredicateMode::Age;
        age_only.accepted_numeric_countries = None;
        let proof = prove_identity(age_only.clone(), witness.clone()).expect("age-only proves");
        assert!(
            verify_identity(age_only, proof)
                .expect("age-only verification returns")
                .ok,
            "age-only statement must verify through the SDK identity API"
        );

        let mut nat_only = base;
        nat_only.predicate_mode = PredicateMode::Nat;
        nat_only.age_threshold_years = None;
        let proof = prove_identity(nat_only.clone(), witness).expect("nat-only proves");
        assert!(
            verify_identity(nat_only, proof)
                .expect("nat-only verification returns")
                .ok,
            "nat-only statement must verify through the SDK identity API"
        );
    }

    #[test]
    fn encode_statement_is_deterministic() {
        let s = sample_statement();
        assert_eq!(encode_statement(&s), encode_statement(&s));
    }

    #[test]
    fn verify_rejects_a_malformed_proof() {
        // Garbage bytes don't deserialize to an envelope -> fail-closed, no error.
        let s = sample_statement();
        let result = verify_identity(s, b"not a proof envelope".to_vec()).unwrap();
        assert!(!result.ok);
    }

    #[test]
    fn ffi_stark_proof_payload_is_zstd_compressed() {
        let raw_bincode = b"serialized stark proof bytes";
        let compressed = compress_stark_proof_for_ffi(raw_bincode).unwrap();

        assert!(
            compressed.starts_with(&[0x28, 0xB5, 0x2F, 0xFD]),
            "zstd payloads must carry the zstd frame magic, got prefix {:?}",
            &compressed[..compressed.len().min(4)]
        );
        assert_ne!(
            compressed, raw_bincode,
            "FFI transport must not expose raw bincode proof bytes"
        );

        let restored = decompress_stark_proof_from_ffi(&compressed).unwrap();
        assert_eq!(
            restored, raw_bincode,
            "verifier-side decompression must restore the exact bincode bytes"
        );
    }

    #[test]
    fn verify_rejects_statement_envelope_drift() {
        // The envelope binds the *full* statement (incl. nonce). An envelope
        // built for statement A is rejected against statement B before the STARK
        // is even deserialized — this is the anti-replay / doctype binding, and
        // it needs no real proof to exercise.
        let (a, mdoc_statement) = honest_mdoc_statement();
        let mut b = a.clone();
        b.nonce = vec![0xff; 8]; // a fresh session -> different statement bytes

        let envelope = bincode::serialize(&MdocProofEnvelope {
            statement_bytes: encode_statement(&a),
            mdoc_statement,
            stark_proof: b"opaque".to_vec(),
        })
        .unwrap();
        assert!(!verify_identity(b, envelope).unwrap().ok);
    }

    #[test]
    fn verify_rejects_matching_statement_but_corrupt_stark_proof() {
        // Envelope statement matches, but the inner STARK proof is junk -> the
        // STARK deserialization fails and the result is fail-closed.
        let (s, mdoc_statement) = honest_mdoc_statement();
        let envelope = bincode::serialize(&MdocProofEnvelope {
            statement_bytes: encode_statement(&s),
            mdoc_statement,
            stark_proof: b"not a stark proof".to_vec(),
        })
        .unwrap();
        assert!(!verify_identity(s, envelope).unwrap().ok);
    }

    #[test]
    fn verify_rejects_matching_statement_but_compressed_corrupt_stark_proof() {
        // The FFI transport layer may be well-formed zstd while the decompressed
        // bytes are not a valid STARK proof. That still rejects fail-closed.
        let (s, mdoc_statement) = honest_mdoc_statement();
        let compressed_junk = compress_stark_proof_for_ffi(b"not a stark proof").unwrap();
        let envelope = bincode::serialize(&MdocProofEnvelope {
            statement_bytes: encode_statement(&s),
            mdoc_statement,
            stark_proof: compressed_junk,
        })
        .unwrap();
        assert!(!verify_identity(s, envelope).unwrap().ok);
    }

    #[test]
    fn omitted_predicates_drop_their_subkeys() {
        // Age-only statement: the `nat` sub-map must be absent, so its encoding
        // is strictly shorter than the both-predicates one.
        let mut age_only = sample_statement();
        age_only.predicate_mode = PredicateMode::Age;
        age_only.accepted_numeric_countries = None;

        let both = sample_statement();
        assert!(encode_statement(&age_only).len() < encode_statement(&both).len());
    }

    #[test]
    fn predicate_mode_token_round_trips() {
        for mode in [
            PredicateMode::Age,
            PredicateMode::Nat,
            PredicateMode::And,
            PredicateMode::Or,
        ] {
            let token = predicate_mode_token(mode);
            assert_eq!(predicate_mode_from_token(token), Some(mode));
        }
        assert_eq!(predicate_mode_from_token("nope".to_string()), None);
    }

    #[test]
    fn predicate_mode_usage_flags() {
        assert!(predicate_mode_uses_age(PredicateMode::Age));
        assert!(!predicate_mode_uses_nat(PredicateMode::Age));
        assert!(predicate_mode_uses_nat(PredicateMode::Nat));
        assert!(
            predicate_mode_uses_age(PredicateMode::And)
                && predicate_mode_uses_nat(PredicateMode::And)
        );
    }

    #[test]
    fn result_age_over_formats() {
        assert_eq!(result_age_over(18), "age_over_18");
    }

    #[test]
    fn sdk_version_reports_crate_version() {
        // Non-empty and equal to the crate version Cargo compiled in — the same
        // value the workspace owns and the Gradle artifacts publish.
        let v = sdk_version();
        assert!(!v.is_empty());
        assert_eq!(v, env!("CARGO_PKG_VERSION"));
    }

    #[test]
    fn iso_alpha2_lookup_matches_numeric_codes() {
        assert_eq!(iso_alpha2_to_numeric("GR".to_string()), Some(300));
        assert_eq!(iso_alpha2_to_numeric("cy".to_string()), Some(196)); // case-insensitive
        assert_eq!(iso_alpha2_to_numeric("US".to_string()), Some(840)); // full ISO coverage (celes), not just EU
        assert_eq!(iso_alpha2_to_numeric("ZZ".to_string()), None);
    }

    #[test]
    fn contract_exposes_stable_identifiers() {
        let c = zk_contract_v1();
        assert_eq!(c.system_name, "stwo-euid-v1");
        assert_eq!(c.pid_namespace, "eu.europa.ec.eudi.pid.1");
        assert_eq!(c.param_min_age, "min_age");
        assert_eq!(c.result_nat_in_set, "nationality_in_set");
    }
}
