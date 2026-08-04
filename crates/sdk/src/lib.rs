//! Provides the EU-ID ZK data contract to Kotlin and Swift through UniFFI.
//!
//! This crate defines the canonical statement encoding and proof entry points.
//! The wallet and verifier use this code.
//! Thus, they cannot use different wire format implementations.
//!
//! [`prove_identity`] accepts the wallet CBOR document and verifier-authoritative issuer key.
//! It calls `eu_id_prover::prove_mdoc` and returns a proof envelope.
//! [`verify_identity`] checks this envelope with `eu_id_prover::verify_product_mdoc`.
//!
//! In this documentation, “private” identifies a logical witness value, not a public input.
//! It does not claim proof confidentiality.
//! The current composed proof is transparent and is not zero-knowledge.
//!
//! ## What the proof binds
//! `prove_identity` runs the product mdoc prover and returns the sole V8 envelope.
//! The envelope contains only `version = 8` and the compressed proof.
//! The two layers bind complementary data:
//!
//! - **The mdoc proof** binds the issuer key, policy, session transcript, issuer
//!   and device `(r, s)` signatures, canonical CBOR scope, and the
//!   domain-separated request digest. The circuit binds the attribute digests
//!   and device key as logical witness values.
//! - **The SDK verifier** validates the caller's complete public request and
//!   reconstructs every verifier input from it. No proof-carried statement is
//!   accepted as authority. The domain-separated request digest binds product
//!   pins, context, policy, issuer, revocation, and verifier time.
//!
//! The combined prover needs more stack space than a default worker thread.
//! Both entry points use an SDK thread with a large stack.
//! Applications call the UniFFI function synchronously.

// One allocator for every prover entry point on-device: mimalloc. See
// eu-id-ffi — same rationale, this crate is its own cdylib link unit.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;
use std::io::Read;

use bincode::Options;
use ciborium::value::Value;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

uniffi::setup_scaffolding!();

#[cfg(feature = "bench-jni")]
mod android_bench_jni;

// This module builds the prover policy from the UniFFI statement.
mod mapping;

/// Which predicate(s) the statement asserts.
///
/// `Age` / `Nat` activate one predicate. `And` activates both. The
/// corresponding optional fields on [`ZkPublicStatement`] must be present for
/// whichever predicates are active.
#[derive(uniffi::Enum, Clone, Copy, Debug, PartialEq, Eq)]
pub enum PredicateMode {
    Age,
    Nat,
    And,
}

impl PredicateMode {
    /// Stable string token used in the canonical CBOR (`predicate_mode`).
    fn as_token(self) -> &'static str {
        match self {
            PredicateMode::Age => "age",
            PredicateMode::Nat => "nat",
            PredicateMode::And => "and",
        }
    }

    fn uses_age(self) -> bool {
        matches!(self, PredicateMode::Age | PredicateMode::And)
    }

    fn uses_nat(self) -> bool {
        matches!(self, PredicateMode::Nat | PredicateMode::And)
    }
}

const PRODUCT_SPEC_ID: &str = "stwo-euid-pid-v1";
const PRODUCT_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const PRODUCT_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const PRODUCT_BIRTH_DATE_ELEMENT: &str = "birth_date";
const PRODUCT_NATIONALITY_ELEMENT: &str = "nationality";
const NAT_MODE_ANY_TOKEN: &str = "any";

#[uniffi::export]
pub fn product_profile_id() -> String {
    eu_id_prover::product_profile::PRODUCT_PROFILE_ID.to_string()
}

#[uniffi::export]
pub fn product_circuit_hash() -> String {
    eu_id_prover::product_profile::product_circuit_hash()
}

#[uniffi::export]
pub fn product_root_policy_hash() -> Vec<u8> {
    eu_id_prover::product_profile::product_root_policy_hash().to_vec()
}

#[derive(uniffi::Record, Clone, Debug, PartialEq, Eq)]
pub struct ZkPublicStatement {
    pub spec_id: String,
    pub version: u32,
    pub profile_id: String,
    pub circuit_hash: String,
    pub root_policy_hash: Vec<u8>,
    pub doctype: String,
    pub namespace: String,
    /// Required issuer P-256 public-key x-coordinate.
    pub issuer_public_key_x: Vec<u8>,
    /// Required issuer P-256 public-key y-coordinate.
    pub issuer_public_key_y: Vec<u8>,
    /// Verifier time in whole UTC seconds since 1970-01-01T00:00:00Z.
    pub now_epoch_seconds: u64,
    /// Canonical CBOR mdoc SessionTranscript for this presentation.
    pub session_transcript: Vec<u8>,
    pub predicate_mode: PredicateMode,
    /// Present if and only if the age predicate is active.
    pub age_threshold_years: Option<u32>,
    /// Sorted, unique uppercase ISO 3166-1 alpha-2 country codes.
    /// Present if and only if the nationality predicate is
    /// active.
    pub accepted_alpha2_countries: Option<Vec<String>>,
    pub revocation_public_key_x: Vec<u8>,
    pub revocation_public_key_y: Vec<u8>,
    pub revocation_epoch: u32,
}

/// The PRIVATE witness for the production identity proof path.
#[derive(uniffi::Record, Clone, Debug)]
pub struct ZkMdocWitness {
    /// Full CBOR mdoc document returned by the wallet.
    pub document: Vec<u8>,
    pub revocation_id_lo: u64,
    pub revocation_id_hi: u64,
    pub revocation_signature_r: Vec<u8>,
    pub revocation_signature_s: Vec<u8>,
}

/// The verdict returned by [`verify_identity`].
#[derive(uniffi::Record, Clone, Debug)]
pub struct ZkVerifyResult {
    pub ok: bool,
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

/// Build an RFC 8949 deterministic map whose keys are CBOR text strings.
///
/// Deterministic CBOR orders map keys first by the length of their encoded form
/// and then lexicographically by those encoded bytes. For text-only keys this is
/// exactly UTF-8 byte length followed by UTF-8 byte order.
fn canonical_text_map(mut entries: Vec<(Value, Value)>) -> Value {
    entries.sort_by(|(left, _), (right, _)| {
        let (Value::Text(left), Value::Text(right)) = (left, right) else {
            unreachable!("canonical_text_map accepts only text keys");
        };
        left.len()
            .cmp(&right.len())
            .then_with(|| left.as_bytes().cmp(right.as_bytes()))
    });
    Value::Map(entries)
}

/// Encode the public statement as deterministic CBOR (RFC 8949).
///
/// The optional `age` / `nat` sub-maps appear only when their predicate is
/// active.
///
/// This function is private so proving and verification use one encoder.
fn encode_statement(s: &ZkPublicStatement) -> Vec<u8> {
    let mut entries: Vec<(Value, Value)> = vec![
        ("v".into(), Value::from(s.version)),
        ("spec_id".into(), s.spec_id.as_str().into()),
        ("profile_id".into(), s.profile_id.as_str().into()),
        ("circuit_hash".into(), s.circuit_hash.as_str().into()),
        (
            "root_policy_hash".into(),
            Value::Bytes(s.root_policy_hash.clone()),
        ),
        ("doctype".into(), s.doctype.as_str().into()),
        ("namespace".into(), s.namespace.as_str().into()),
        (
            "issuer_key".into(),
            canonical_text_map(vec![
                ("crv".into(), "P-256".into()),
                ("x".into(), Value::Bytes(s.issuer_public_key_x.clone())),
                ("y".into(), Value::Bytes(s.issuer_public_key_y.clone())),
            ]),
        ),
        ("now".into(), Value::from(s.now_epoch_seconds)),
        (
            "session_transcript".into(),
            Value::Bytes(s.session_transcript.clone()),
        ),
        ("predicate_mode".into(), s.predicate_mode.as_token().into()),
        (
            "revocation".into(),
            canonical_text_map(vec![
                ("epoch".into(), Value::from(s.revocation_epoch)),
                (
                    "public_key_x".into(),
                    Value::Bytes(s.revocation_public_key_x.clone()),
                ),
                (
                    "public_key_y".into(),
                    Value::Bytes(s.revocation_public_key_y.clone()),
                ),
            ]),
        ),
    ];

    if let Some(threshold) = s.age_threshold_years {
        entries.push((
            "age".into(),
            canonical_text_map(vec![("threshold_years".into(), Value::from(threshold))]),
        ));
    }

    if let Some(accepted) = &s.accepted_alpha2_countries {
        let accepted_arr = accepted
            .iter()
            .map(|country| Value::Text(country.clone()))
            .collect();
        entries.push((
            "nat".into(),
            canonical_text_map(vec![
                ("mode".into(), NAT_MODE_ANY_TOKEN.into()),
                ("accepted".into(), Value::Array(accepted_arr)),
            ]),
        ));
    }

    let mut out = Vec::new();
    // Writing to a Vec cannot fail.
    // A CBOR serialization error indicates a library defect.
    ciborium::ser::into_writer(&canonical_text_map(entries), &mut out)
        .expect("CBOR serialization of ZkPublicStatement is infallible");
    out
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
struct MdocProofEnvelope {
    version: u16,
    compressed_proof: Vec<u8>,
}

const MDOC_PROOF_ENVELOPE_VERSION: u16 = 8;
const PRODUCT_STATEMENT_VERSION: u32 = 2;
const REQUEST_BINDING_DOMAIN: &[u8] = b"eudi-mdoc-proof-request-v3\0";
const P256_COORDINATE_BYTES: usize = 32;
const MAX_SESSION_TRANSCRIPT_BYTES: usize = 16 * 1024;
const MAX_ACCEPTED_ALPHA2_COUNTRIES: usize = 249;
const MAX_PRODUCT_MDOC_DOCUMENT_BYTES: usize = eu_id_prover::mdoc::PRODUCT_MDOC_CBOR_MAX_BYTES;

/// The measured P-256 proof is about 4 MiB compressed. These caps preserve
/// headroom while bounding proof parsing and decompression.
const MAX_MDOC_PROOF_ENVELOPE_BYTES: usize = 8 * 1024 * 1024;
const MAX_COMPRESSED_STARK_PROOF_BYTES: usize = 6 * 1024 * 1024;
const MAX_DECOMPRESSED_STARK_PROOF_BYTES: usize = 16 * 1024 * 1024;
const MAX_ZSTD_WINDOW_LOG: u32 = 24;
const ZSTD_FRAME_MAGIC: [u8; 4] = [0x28, 0xb5, 0x2f, 0xfd];

fn bounded_bincode_options(limit: usize) -> impl Options {
    // Match the fixed-width encoding used by bincode's v1 convenience
    // functions, but add an explicit aggregate allocation/read bound.
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_limit(limit as u64)
}

fn request_binding(statement: &ZkPublicStatement) -> [u8; 32] {
    let statement_bytes = encode_statement(statement);
    let mut digest = Sha256::new();
    digest.update(REQUEST_BINDING_DOMAIN);
    digest.update((statement_bytes.len() as u64).to_be_bytes());
    digest.update(&statement_bytes);
    digest.finalize().into()
}

fn validate_product_statement_contract(statement: &ZkPublicStatement) -> Result<(), ZkError> {
    if statement.spec_id != PRODUCT_SPEC_ID {
        return Err(ZkError::InvalidInput(format!(
            "unsupported spec_id `{}`; expected `{}`",
            statement.spec_id, PRODUCT_SPEC_ID
        )));
    }
    if statement.version != PRODUCT_STATEMENT_VERSION {
        return Err(ZkError::InvalidInput(format!(
            "unsupported statement version {}; expected {}",
            statement.version, PRODUCT_STATEMENT_VERSION
        )));
    }
    if !eu_id_prover::product_profile::product_profile_pin_is_supported(
        &statement.profile_id,
        &statement.circuit_hash,
        &statement.root_policy_hash,
    ) {
        return Err(ZkError::InvalidInput(
            "unsupported product profile, circuit_hash, or root_policy_hash".to_string(),
        ));
    }
    if statement.doctype != PRODUCT_DOCTYPE {
        return Err(ZkError::InvalidInput(format!(
            "unsupported doctype `{}`; expected `{}`",
            statement.doctype, PRODUCT_DOCTYPE
        )));
    }
    if statement.namespace != PRODUCT_NAMESPACE {
        return Err(ZkError::InvalidInput(format!(
            "unsupported namespace `{}`; expected `{}`",
            statement.namespace, PRODUCT_NAMESPACE
        )));
    }

    if statement.issuer_public_key_x.len() != P256_COORDINATE_BYTES {
        return Err(ZkError::InvalidInput(format!(
            "issuer P-256 public-key x-coordinate must be {P256_COORDINATE_BYTES} bytes"
        )));
    }
    if statement.issuer_public_key_y.len() != P256_COORDINATE_BYTES {
        return Err(ZkError::InvalidInput(format!(
            "issuer P-256 public-key y-coordinate must be {P256_COORDINATE_BYTES} bytes"
        )));
    }
    if eu_id_prover::mdoc::p256_affine_point_from_coordinates(
        &statement.issuer_public_key_x,
        &statement.issuer_public_key_y,
    )
    .is_none()
    {
        return Err(ZkError::InvalidInput(
            "issuer public key is not a valid P-256 point".to_string(),
        ));
    }
    if eu_id_prover::mdoc::p256_affine_point_from_coordinates(
        &statement.revocation_public_key_x,
        &statement.revocation_public_key_y,
    )
    .is_none()
    {
        return Err(ZkError::InvalidInput(
            "revocation_public_key is not a valid P-256 point".to_string(),
        ));
    }
    if statement.now_epoch_seconds == 0
        || statement
            .now_epoch_seconds
            .checked_add(1)
            .and_then(|seconds| eu_id_prover::mdoc::utc_timestamp_from_epoch_seconds(seconds).ok())
            .is_none()
    {
        return Err(ZkError::InvalidInput(
            "now_epoch_seconds is outside the strict-validity range".to_string(),
        ));
    }

    if statement.session_transcript.is_empty() {
        return Err(ZkError::InvalidInput(
            "session transcript must not be empty".to_string(),
        ));
    }
    if statement.session_transcript.len() > MAX_SESSION_TRANSCRIPT_BYTES {
        return Err(ZkError::InvalidInput(format!(
            "session transcript exceeds {MAX_SESSION_TRANSCRIPT_BYTES} bytes"
        )));
    }
    eu_id_prover::mdoc::validate_product_session_transcript_cbor(&statement.session_transcript)
        .map_err(|_| {
            ZkError::InvalidInput(
                "session transcript must be one canonical CBOR SessionTranscript array".to_string(),
            )
        })?;

    let (requires_age, requires_nat) = match statement.predicate_mode {
        PredicateMode::Age => (true, false),
        PredicateMode::Nat => (false, true),
        PredicateMode::And => (true, true),
    };
    if statement.age_threshold_years.is_some() != requires_age {
        return Err(ZkError::InvalidInput(if requires_age {
            "age predicate active but `age_threshold_years` is absent".to_string()
        } else {
            "`age_threshold_years` must be absent when the age predicate is inactive".to_string()
        }));
    }
    if statement.accepted_alpha2_countries.is_some() != requires_nat {
        return Err(ZkError::InvalidInput(if requires_nat {
            "nationality predicate active but `accepted_alpha2_countries` is absent".to_string()
        } else {
            "`accepted_alpha2_countries` must be absent when the nationality predicate is inactive"
                .to_string()
        }));
    }
    if let Some(accepted) = &statement.accepted_alpha2_countries {
        if accepted.len() > MAX_ACCEPTED_ALPHA2_COUNTRIES {
            return Err(ZkError::InvalidInput(format!(
                "accepted nationality set exceeds {MAX_ACCEPTED_ALPHA2_COUNTRIES} entries"
            )));
        }
        if accepted.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(ZkError::InvalidInput(
                "accepted nationality set must be sorted and unique".to_string(),
            ));
        }
    }
    mapping::to_policy(statement)?;
    Ok(())
}

fn validate_product_witness(witness: &ZkMdocWitness) -> Result<(), ZkError> {
    if witness.document.is_empty() {
        return Err(ZkError::InvalidInput(
            "mdoc document must not be empty".to_string(),
        ));
    }
    if witness.document.len() > MAX_PRODUCT_MDOC_DOCUMENT_BYTES {
        return Err(ZkError::InvalidInput(format!(
            "mdoc document exceeds {MAX_PRODUCT_MDOC_DOCUMENT_BYTES} bytes"
        )));
    }
    eu_id_prover::mdoc::validate_product_mdoc_cbor_structure(&witness.document).map_err(
        |error| ZkError::InvalidInput(format!("invalid mdoc CBOR structure: {error:?}")),
    )?;

    Ok(())
}

fn encode_mdoc_proof_envelope(envelope: &MdocProofEnvelope) -> Result<Vec<u8>, bincode::Error> {
    bounded_bincode_options(MAX_MDOC_PROOF_ENVELOPE_BYTES)
        .reject_trailing_bytes()
        .serialize(envelope)
}

fn decode_mdoc_proof_envelope(proof: &[u8]) -> Result<MdocProofEnvelope, ZkError> {
    if proof.len() > MAX_MDOC_PROOF_ENVELOPE_BYTES {
        return Err(ZkError::Verify(
            "proof envelope exceeds size limit".to_string(),
        ));
    }

    let unsupported = || ZkError::Verify("unsupported proof envelope version".to_string());
    let version: u16 = bounded_bincode_options(MAX_MDOC_PROOF_ENVELOPE_BYTES)
        .allow_trailing_bytes()
        .deserialize(proof)
        .map_err(|_| unsupported())?;
    if version != MDOC_PROOF_ENVELOPE_VERSION {
        return Err(unsupported());
    }

    let envelope: MdocProofEnvelope = bounded_bincode_options(MAX_MDOC_PROOF_ENVELOPE_BYTES)
        .reject_trailing_bytes()
        .deserialize(proof)
        .map_err(|error| ZkError::Verify(format!("invalid proof envelope: {error}")))?;
    if envelope.compressed_proof.len() > MAX_COMPRESSED_STARK_PROOF_BYTES {
        return Err(ZkError::Verify(
            "compressed STARK proof exceeds size limit".to_string(),
        ));
    }
    Ok(envelope)
}

/// Stack size for the dedicated prover/verifier thread. The combined prover
/// overflows the small default worker-thread stack with `EXC_BAD_ACCESS`. A 32 MiB
/// stack provides the headroom that the FFI harness established on the device.
const PROVER_STACK_SIZE: usize = 32 * 1024 * 1024;

/// Run `work` on a dedicated large-stack thread and join it, returning its
/// result.
///
/// The closure owns everything it touches, so the thread is `'static`. A panic
/// inside `work` is caught by `join` and mapped to the caller-selected FFI
/// error variant — it never unwinds across the UniFFI boundary.
fn on_large_stack<T, F>(
    role: &'static str,
    thread_error: fn(String) -> ZkError,
    work: F,
) -> Result<T, ZkError>
where
    T: Send + 'static,
    F: FnOnce() -> Result<T, ZkError> + Send + 'static,
{
    let handle = std::thread::Builder::new()
        .name(format!("euid-{role}"))
        .stack_size(PROVER_STACK_SIZE)
        .spawn(work)
        .map_err(|e| thread_error(format!("failed to spawn {role} thread: {e}")))?;
    match handle.join() {
        Ok(result) => result,
        Err(_) => Err(thread_error(format!("{role} thread panicked"))),
    }
}

/// Maps a prover error to an FFI error.
///
/// Witness generation rejects a false predicate statement.
/// Thus, this case reports a proof failure.
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
        // Other witness-generation and proving failures.
        Prove(_)
        | Mdoc(_)
        | RequestBindingMissing
        | Revocation(_)
        | CoprocessorWitness(_) => {
            ZkError::Prove(format!("{e:?}"))
        }
        // Verifier-side rejections (only reachable from the verify path).
        P256InstanceMismatch
        | AgePolicyMismatch
        | NatPolicyMismatch
        | WeakConfig { .. }
        | CoprocessorMissing
        | Verify(_)
        | PreprocessedRootMismatch { .. }
        | ShapeTooLarge { .. } => {
            ZkError::Verify(format!("{e:?}"))
        }
    }
}

/// zstd level for the FFI transport envelope.
///
/// Level 12 balances size and time for the current product proof.
/// Level 19 saves little space and takes about four times longer.
const PROOF_ZSTD_LEVEL: i32 = 12;

/// Compress the raw bincode STARK proof for the FFI transport envelope.
fn compress_stark_proof_for_ffi(raw_bincode: &[u8]) -> Result<Vec<u8>, ZkError> {
    if raw_bincode.len() > MAX_DECOMPRESSED_STARK_PROOF_BYTES {
        return Err(ZkError::Prove(
            "serialized STARK proof exceeds size limit".to_string(),
        ));
    }
    let compressed = zstd::bulk::compress(raw_bincode, PROOF_ZSTD_LEVEL)
        .map_err(|e| ZkError::Prove(format!("failed to compress proof: {e}")))?;
    if compressed.len() > MAX_COMPRESSED_STARK_PROOF_BYTES {
        return Err(ZkError::Prove(
            "compressed STARK proof exceeds size limit".to_string(),
        ));
    }
    Ok(compressed)
}

/// Decompress the FFI transport proof payload back to raw bincode bytes.
fn decompress_stark_proof_from_ffi(compressed: &[u8]) -> Result<Vec<u8>, ZkError> {
    if compressed.len() > MAX_COMPRESSED_STARK_PROOF_BYTES {
        return Err(ZkError::Verify(
            "compressed STARK proof exceeds size limit".to_string(),
        ));
    }
    if !compressed.starts_with(&ZSTD_FRAME_MAGIC) {
        return Err(ZkError::Verify(
            "compressed STARK proof must be one zstd frame".to_string(),
        ));
    }
    let frame_size = zstd::zstd_safe::find_frame_compressed_size(compressed)
        .map_err(|e| ZkError::Verify(format!("invalid compressed STARK proof frame: {e}")))?;
    if frame_size != compressed.len() {
        return Err(ZkError::Verify(
            "compressed STARK proof contains trailing or concatenated frames".to_string(),
        ));
    }
    let mut decoder = zstd::stream::read::Decoder::new(compressed)
        .map_err(|e| ZkError::Verify(format!("failed to initialize proof decompression: {e}")))?;
    decoder
        .window_log_max(MAX_ZSTD_WINDOW_LOG)
        .map_err(|e| ZkError::Verify(format!("failed to limit proof decompression window: {e}")))?;
    let decoder = decoder.single_frame();
    let mut raw_bincode = Vec::new();
    decoder
        .take((MAX_DECOMPRESSED_STARK_PROOF_BYTES + 1) as u64)
        .read_to_end(&mut raw_bincode)
        .map_err(|e| ZkError::Verify(format!("failed to decompress proof: {e}")))?;
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

/// Returns the ordered attribute set for the SDK mdoc PID path.
///
/// `birth_date` under `AgeOver` precedes `nationality` under `Alpha2Set`.
/// The prover and verifier use this function.
///
/// The predicate mode selects the required elements.
/// An age-only presentation does not require nationality.
/// A nationality-only presentation does not require birth date.
/// A wallet document can contain only the requested elements.
fn expected_mdoc_attributes(
    mode: PredicateMode,
) -> Vec<eu_id_prover::mdoc::MdocRequestedAttribute> {
    let mut attributes =
        Vec::with_capacity(usize::from(mode.uses_age()) + usize::from(mode.uses_nat()));
    if mode.uses_age() {
        attributes.push(eu_id_prover::mdoc::MdocRequestedAttribute {
            element_identifier: PRODUCT_BIRTH_DATE_ELEMENT.to_string(),
            mode: eu_id_prover::mdoc::MdocDisclosureMode::AgeOver,
        });
    }
    if mode.uses_nat() {
        attributes.push(eu_id_prover::mdoc::MdocRequestedAttribute {
            element_identifier: PRODUCT_NATIONALITY_ELEMENT.to_string(),
            mode: eu_id_prover::mdoc::MdocDisclosureMode::Alpha2Set,
        });
    }
    attributes
}

fn reconstruct_mdoc_statement(
    statement: &ZkPublicStatement,
) -> Result<eu_id_prover::MdocStatement, ZkError> {
    validate_product_statement_contract(statement)?;
    let issuer_public_key = eu_id_prover::mdoc::p256_affine_point_from_coordinates(
        &statement.issuer_public_key_x,
        &statement.issuer_public_key_y,
    )
    .ok_or_else(|| ZkError::InvalidInput("invalid issuer P-256 public key".to_string()))?;
    let revocation_public_key = eu_id_prover::mdoc::p256_affine_point_from_coordinates(
        &statement.revocation_public_key_x,
        &statement.revocation_public_key_y,
    )
    .ok_or_else(|| ZkError::InvalidInput("invalid revocation P-256 public key".to_string()))?;
    let device_hash = eu_id_prover::mdoc::device_authentication_sig_structure_hash(
        &statement.session_transcript,
        &statement.doctype,
    )
    .map_err(|error| {
        ZkError::InvalidInput(format!("invalid DeviceAuthentication input: {error:?}"))
    })?;
    let device_message_hash = eu_id_prover::mdoc::p256_digest(device_hash);
    let attributes = expected_mdoc_attributes(statement.predicate_mode);

    Ok(eu_id_prover::MdocStatement {
        request_binding: request_binding(statement),
        doctype: statement.doctype.clone(),
        namespace: statement.namespace.clone(),
        issuer_public_key,
        device_message_hash,
        verification_time_epoch_seconds: statement.now_epoch_seconds,
        ts13_revocation: eu_id_prover::mdoc::MdocRevocationPublicInputs {
            revocation_public_key,
            epoch: statement.revocation_epoch,
        },
        attributes,
        policy: mapping::to_policy(statement)?,
    })
}

fn mdoc_request(
    statement: &ZkPublicStatement,
    witness: &ZkMdocWitness,
    public_statement: &eu_id_prover::MdocStatement,
) -> Result<eu_id_prover::MdocPidRequest, ZkError> {
    if witness.revocation_id_lo >= witness.revocation_id_hi {
        return Err(ZkError::InvalidInput(
            "revocation bounds must satisfy id_lo < id_hi".to_string(),
        ));
    }
    let revocation_signature = eu_id_prover::mdoc::p256_signature_from_scalars(
        &witness.revocation_signature_r,
        &witness.revocation_signature_s,
    )
    .ok_or_else(|| ZkError::InvalidInput("invalid revocation P-256 signature".to_string()))?;
    let revocation_public_inputs = public_statement.ts13_revocation.clone();
    Ok(eu_id_prover::MdocPidRequest {
        request_binding: public_statement.request_binding,
        doctype: public_statement.doctype.clone(),
        namespace: public_statement.namespace.clone(),
        attributes: public_statement.attributes.clone(),
        session_transcript: statement.session_transcript.clone(),
        required_issuer_public_key: public_statement.issuer_public_key.clone(),
        verification_time_epoch_seconds: public_statement.verification_time_epoch_seconds,
        revocation: eu_id_prover::MdocRevocationRequest {
            public_inputs: revocation_public_inputs,
            id_lo: witness.revocation_id_lo,
            id_hi: witness.revocation_id_hi,
            signature: revocation_signature,
        },
    })
}

#[cfg(test)]
fn mdoc_statement_matches_public_statement(
    mdoc_statement: &eu_id_prover::MdocStatement,
    statement: &ZkPublicStatement,
) -> Result<bool, ZkError> {
    Ok(mdoc_statement == &reconstruct_mdoc_statement(statement)?)
}

/// Prove an identity presentation from a full CBOR mdoc using
/// [`eu_id_prover::prove_mdoc`]. The verifier-authoritative issuer public key
/// must equal the SubjectPublicKeyInfo key in the signed document's single
/// x5chain leaf.
///
/// The returned envelope binds the caller's complete public statement to the
/// production mdoc proof and runs on the SDK's dedicated large-stack thread.
#[uniffi::export]
pub fn prove_identity(
    statement: ZkPublicStatement,
    witness: ZkMdocWitness,
) -> Result<Vec<u8>, ZkError> {
    on_large_stack("prover", ZkError::Prove, move || {
        let expected_mdoc_statement = reconstruct_mdoc_statement(&statement)?;
        validate_product_witness(&witness)?;
        let policy = expected_mdoc_statement.policy.clone();
        let request = mdoc_request(&statement, &witness, &expected_mdoc_statement)?;
        let document = witness.document;
        let (proof, mdoc_statement) =
            eu_id_prover::prove_mdoc(&document, &request, policy).map_err(map_prover_error)?;
        if mdoc_statement != expected_mdoc_statement {
            return Err(ZkError::Prove(
                "prover returned an mdoc statement outside the requested product profile"
                    .to_string(),
            ));
        }
        let stark_proof_bincode = bincode::serialize(&proof)
            .map_err(|e| ZkError::Prove(format!("failed to serialize mdoc proof: {e}")))?;
        let compressed_proof = compress_stark_proof_for_ffi(&stark_proof_bincode)?;

        let envelope = MdocProofEnvelope {
            version: MDOC_PROOF_ENVELOPE_VERSION,
            compressed_proof,
        };
        encode_mdoc_proof_envelope(&envelope)
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
    on_large_stack("verifier", ZkError::Verify, move || {
        let mdoc_statement = reconstruct_mdoc_statement(&statement)?;
        let envelope = match decode_mdoc_proof_envelope(&proof) {
            Ok(envelope) => envelope,
            Err(_) => return Ok(ZkVerifyResult { ok: false }),
        };
        let stark_proof_bincode = match decompress_stark_proof_from_ffi(&envelope.compressed_proof)
        {
            Ok(bytes) => bytes,
            Err(_) => return Ok(ZkVerifyResult { ok: false }),
        };
        let stark_proof = match decode_stark_proof(&stark_proof_bincode) {
            Some(stark_proof) => stark_proof,
            None => return Ok(ZkVerifyResult { ok: false }),
        };
        Ok(ZkVerifyResult {
            ok: eu_id_prover::verify_product_mdoc(&stark_proof, &mdoc_statement).is_ok(),
        })
    })
}

#[cfg(test)]
mod tests {
    use std::io::Write;

    use super::*;

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
        let fixture = eu_id_prover::mdoc::demo_mdoc_circuit_fixture();
        let issuer_key = fixture.statement.issuer_input.public_key;
        let session_transcript = fixture.request.session_transcript;
        let (revocation, _) =
            eu_id_prover::ts13::demo_ts13_revocation_inputs(&fixture.extracted.mso);
        ZkPublicStatement {
            spec_id: "stwo-euid-pid-v1".to_string(),
            version: PRODUCT_STATEMENT_VERSION,
            profile_id: product_profile_id(),
            circuit_hash: product_circuit_hash(),
            root_policy_hash: product_root_policy_hash(),
            doctype: "eu.europa.ec.eudi.pid.1".to_string(),
            namespace: "eu.europa.ec.eudi.pid.1".to_string(),
            issuer_public_key_x: issuer_key.x.0.to_vec(),
            issuer_public_key_y: issuer_key.y.0.to_vec(),
            now_epoch_seconds: 20_637 * 86_400 + 43_200,
            session_transcript,
            predicate_mode: PredicateMode::And,
            age_threshold_years: Some(18),
            accepted_alpha2_countries: Some(vec![
                "BE".to_string(),
                "CY".to_string(),
                "GR".to_string(),
            ]),
            revocation_public_key_x: revocation.revocation_public_key.x.0.to_vec(),
            revocation_public_key_y: revocation.revocation_public_key.y.0.to_vec(),
            revocation_epoch: revocation.epoch,
        }
    }

    fn honest_mdoc_statement() -> (ZkPublicStatement, eu_id_prover::MdocStatement) {
        let fixture = eu_id_prover::mdoc::demo_mdoc_circuit_fixture();
        let issuer_key = fixture.statement.issuer_input.public_key.clone();
        let (revocation, revocation_witness) =
            eu_id_prover::ts13::demo_ts13_revocation_inputs(&fixture.extracted.mso);
        let statement = ZkPublicStatement {
            spec_id: "stwo-euid-pid-v1".to_string(),
            version: PRODUCT_STATEMENT_VERSION,
            profile_id: product_profile_id(),
            circuit_hash: product_circuit_hash(),
            root_policy_hash: product_root_policy_hash(),
            doctype: "eu.europa.ec.eudi.pid.1".to_string(),
            namespace: "eu.europa.ec.eudi.pid.1".to_string(),
            issuer_public_key_x: issuer_key.x.0.to_vec(),
            issuer_public_key_y: issuer_key.y.0.to_vec(),
            now_epoch_seconds: 20_637 * 86_400 + 43_200,
            session_transcript: fixture.request.session_transcript,
            predicate_mode: PredicateMode::And,
            age_threshold_years: Some(18),
            accepted_alpha2_countries: Some(vec!["DE".to_string(), "FR".to_string()]),
            revocation_public_key_x: revocation.revocation_public_key.x.0.to_vec(),
            revocation_public_key_y: revocation.revocation_public_key.y.0.to_vec(),
            revocation_epoch: revocation.epoch,
        };
        assert_eq!(
            fixture.statement.ts13_revocation,
            eu_id_prover::mdoc::MdocRevocationPublicInputs::from(&revocation)
        );
        assert_eq!(
            fixture.statement.ts13_revocation_range,
            eu_id_prover::mdoc::MdocRevocationRangeWitness {
                id: revocation_witness.id,
                id_lo: revocation_witness.id_lo,
                id_hi: revocation_witness.id_hi,
            }
        );
        assert_eq!(
            fixture.statement.ts13_revocation_signature,
            revocation_witness.signature
        );
        let mut mdoc_statement = eu_id_prover::MdocStatement::from_circuit(&fixture.statement);
        mdoc_statement.request_binding = request_binding(&statement);
        mdoc_statement.policy = mapping::to_policy(&statement).unwrap();
        (statement, mdoc_statement)
    }

    fn canonical_v2_mdoc_sdk_fixture() -> (ZkPublicStatement, ZkMdocWitness) {
        let fixture = eu_id_prover::mdoc::demo_mdoc_circuit_fixture();
        let issuer_key = fixture.statement.issuer_input.public_key.clone();
        let (revocation, revocation_witness) =
            eu_id_prover::ts13::demo_ts13_revocation_inputs(&fixture.extracted.mso);
        let mut accepted_alpha2_countries = fixture
            .statement
            .policy
            .accepted_nationalities
            .iter()
            .map(|country| String::from_utf8(country.to_vec()).expect("fixture alpha-2 is ASCII"))
            .collect::<Vec<_>>();
        accepted_alpha2_countries.sort_unstable();
        accepted_alpha2_countries.dedup();
        (
            ZkPublicStatement {
                spec_id: "stwo-euid-pid-v1".to_string(),
                version: PRODUCT_STATEMENT_VERSION,
                profile_id: product_profile_id(),
                circuit_hash: product_circuit_hash(),
                root_policy_hash: product_root_policy_hash(),
                doctype: fixture.request.doctype,
                namespace: fixture.request.namespace,
                issuer_public_key_x: issuer_key.x.0.to_vec(),
                issuer_public_key_y: issuer_key.y.0.to_vec(),
                now_epoch_seconds: 20_637 * 86_400 + 43_200,
                session_transcript: fixture.request.session_transcript,
                predicate_mode: PredicateMode::And,
                age_threshold_years: Some(fixture.statement.policy.min_age_years),
                accepted_alpha2_countries: Some(accepted_alpha2_countries),
                revocation_public_key_x: revocation.revocation_public_key.x.0.to_vec(),
                revocation_public_key_y: revocation.revocation_public_key.y.0.to_vec(),
                revocation_epoch: revocation.epoch,
            },
            ZkMdocWitness {
                document: fixture.document,
                revocation_id_lo: revocation_witness.id_lo,
                revocation_id_hi: revocation_witness.id_hi,
                revocation_signature_r: revocation_witness.signature.r.0.to_vec(),
                revocation_signature_s: revocation_witness.signature.s.0.to_vec(),
            },
        )
    }

    #[test]
    fn mdoc_statement_match_recomputes_device_authentication_hash() {
        let (statement, mdoc_statement) = honest_mdoc_statement();
        assert!(mdoc_statement_matches_public_statement(&mdoc_statement, &statement).unwrap());

        let mut changed_binding = mdoc_statement.clone();
        changed_binding.request_binding[0] ^= 1;
        assert!(
            !mdoc_statement_matches_public_statement(&changed_binding, &statement).unwrap(),
            "the inner public statement must carry the canonical request binding"
        );

        let mut changed_inner_doctype = mdoc_statement.clone();
        changed_inner_doctype.doctype = "other.doctype".to_string();
        assert!(
            !mdoc_statement_matches_public_statement(&changed_inner_doctype, &statement).unwrap(),
            "the proof statement's docType must exactly match the verifier request"
        );

        let mut changed_inner_namespace = mdoc_statement.clone();
        changed_inner_namespace.namespace = "other.namespace".to_string();
        assert!(
            !mdoc_statement_matches_public_statement(&changed_inner_namespace, &statement).unwrap(),
            "the proof statement's namespace must exactly match the verifier request"
        );

        let mut changed_transcript = statement.clone();
        changed_transcript.session_transcript =
            eu_id_prover::mdoc::openid4vp_session_transcript(b"other");
        assert!(
            !mdoc_statement_matches_public_statement(&mdoc_statement, &changed_transcript).unwrap(),
            "transcript drift must change the expected device-auth hash"
        );

        let mut changed_doctype = statement.clone();
        changed_doctype.doctype = "wrong.doctype".to_string();
        assert!(matches!(
            mdoc_statement_matches_public_statement(&mdoc_statement, &changed_doctype),
            Err(ZkError::InvalidInput(_))
        ));
    }

    #[test]
    fn mdoc_public_statement_serialization_omits_private_signature_and_device_key_material() {
        let fixture = eu_id_prover::mdoc::demo_mdoc_circuit_fixture();
        let public = eu_id_prover::MdocStatement::from_circuit(&fixture.statement);
        let encoded = bincode::serialize(&public).expect("public mdoc statement serializes");
        let birth_date = fixture.extracted.birth_date_binding.0;
        assert!(
            !encoded
                .windows(birth_date.len())
                .any(|window| window == birth_date),
            "raw signed birth date must not be serialized in the public mdoc statement"
        );
        for attribute in &fixture.extracted.extracted_attributes {
            assert!(
                !encoded
                    .windows(attribute.item.len())
                    .any(|window| window == attribute.item),
                "private IssuerSignedItem must not be serialized in the public statement"
            );
        }
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
        // Reject a requested attribute when its semantic proof is inactive.
        let (statement, honest) = honest_mdoc_statement();
        assert!(
            mdoc_statement_matches_public_statement(&honest, &statement).unwrap(),
            "honest And statement (both legs present) must be accepted"
        );

        let mut age_dropped = honest.clone();
        age_dropped.attributes.retain(|attribute| {
            !matches!(
                attribute.mode,
                eu_id_prover::mdoc::MdocDisclosureMode::AgeOver
            )
        });
        assert!(
            !mdoc_statement_matches_public_statement(&age_dropped, &statement).unwrap(),
            "dropping the age predicate semantic binding must be rejected"
        );

        let mut nat_dropped = honest.clone();
        nat_dropped.attributes.retain(|attribute| {
            !matches!(
                attribute.mode,
                eu_id_prover::mdoc::MdocDisclosureMode::Alpha2Set
            )
        });
        assert!(
            !mdoc_statement_matches_public_statement(&nat_dropped, &statement).unwrap(),
            "dropping the nationality predicate semantic binding must be rejected"
        );
    }

    #[test]
    fn mdoc_verify_rejects_revocation_public_input_drift() {
        let (statement, honest) = honest_mdoc_statement();
        assert!(mdoc_statement_matches_public_statement(&honest, &statement).unwrap());

        let mut changed_key = honest.clone();
        changed_key.ts13_revocation.revocation_public_key.x.0[0] ^= 1;
        assert!(
            !mdoc_statement_matches_public_statement(&changed_key, &statement).unwrap(),
            "the product verifier must reject revocation-key drift"
        );

        let mut changed_epoch = honest;
        changed_epoch.ts13_revocation.epoch = changed_epoch
            .ts13_revocation
            .epoch
            .checked_add(1)
            .expect("fixture revocation epoch can increment");
        assert!(
            !mdoc_statement_matches_public_statement(&changed_epoch, &statement).unwrap(),
            "the product verifier must reject revocation-epoch drift"
        );
    }

    #[test]
    fn mdoc_verify_rejects_element_substitution() {
        // C2: prove the age predicate over the wrong signed element (e.g.
        // `issue_date` instead of `birth_date`). The disclosed element identity
        // must be pinned to the requested contract element.
        let (statement, honest) = honest_mdoc_statement();
        let age_index = honest
            .attributes
            .iter()
            .position(|attribute| {
                matches!(
                    attribute.mode,
                    eu_id_prover::mdoc::MdocDisclosureMode::AgeOver
                )
            })
            .expect("honest statement discloses the age attribute");

        let mut wrong_element = honest.clone();
        wrong_element.attributes[age_index].element_identifier = "issue_date".to_string();
        assert!(
            !mdoc_statement_matches_public_statement(&wrong_element, &statement).unwrap(),
            "age predicate over the wrong element_identifier must be rejected"
        );

        let mut wrong_mode = honest.clone();
        wrong_mode.attributes[age_index].mode = eu_id_prover::mdoc::MdocDisclosureMode::Alpha2Set;
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
        // Build a signed proof that discloses only nationality.
        // Reject it when an `And` request also requires age.
        let demo = eu_id_prover::mdoc::demo_mdoc_circuit_fixture();
        let issuer_key = demo.statement.issuer_input.public_key.clone();
        let (revocation, revocation_witness) =
            eu_id_prover::ts13::demo_ts13_revocation_inputs(&demo.extracted.mso);
        let claimed_statement = ZkPublicStatement {
            spec_id: "stwo-euid-pid-v1".to_string(),
            version: PRODUCT_STATEMENT_VERSION,
            profile_id: product_profile_id(),
            circuit_hash: product_circuit_hash(),
            root_policy_hash: product_root_policy_hash(),
            doctype: demo.request.doctype.clone(),
            namespace: demo.request.namespace.clone(),
            issuer_public_key_x: issuer_key.x.0.to_vec(),
            issuer_public_key_y: issuer_key.y.0.to_vec(),
            now_epoch_seconds: 20_637 * 86_400 + 43_200,
            session_transcript: demo.request.session_transcript.clone(),
            predicate_mode: PredicateMode::And,
            age_threshold_years: Some(18),
            accepted_alpha2_countries: Some(vec!["DE".to_string(), "FR".to_string()]),
            revocation_public_key_x: revocation.revocation_public_key.x.0.to_vec(),
            revocation_public_key_y: revocation.revocation_public_key.y.0.to_vec(),
            revocation_epoch: revocation.epoch,
        };
        let expected_request_binding = request_binding(&claimed_statement);

        // Attacker request: nationality only — no AgeOver leg.
        let nat_only_request = eu_id_prover::MdocPidRequest {
            request_binding: expected_request_binding,
            doctype: demo.request.doctype.clone(),
            namespace: demo.request.namespace.clone(),
            attributes: vec![eu_id_prover::mdoc::MdocRequestedAttribute {
                element_identifier: "nationality".to_string(),
                mode: eu_id_prover::mdoc::MdocDisclosureMode::Alpha2Set,
            }],
            session_transcript: demo.request.session_transcript.clone(),
            required_issuer_public_key: issuer_key,
            verification_time_epoch_seconds: claimed_statement.now_epoch_seconds,
            revocation: eu_id_prover::MdocRevocationRequest {
                public_inputs: eu_id_prover::mdoc::MdocRevocationPublicInputs::from(&revocation),
                id_lo: revocation_witness.id_lo,
                id_hi: revocation_witness.id_hi,
                signature: revocation_witness.signature,
            },
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
            accepted_nationalities: vec![*b"DE", *b"FR"],
        };
        let (proof, mdoc_statement) =
            eu_id_prover::prove_mdoc(&demo.document, &nat_only_request, policy)
                .expect("nationality-only mdoc proves");
        assert!(
            !mdoc_statement.attributes.iter().any(|attribute| matches!(
                attribute.mode,
                eu_id_prover::mdoc::MdocDisclosureMode::AgeOver
            )),
            "attack precondition: age predicate leg absent"
        );

        let stark_proof_bincode = bincode::serialize(&proof).unwrap();
        let compressed_proof = compress_stark_proof_for_ffi(&stark_proof_bincode).unwrap();
        let envelope = MdocProofEnvelope {
            version: MDOC_PROOF_ENVELOPE_VERSION,
            compressed_proof,
        };
        let proof_bytes = encode_mdoc_proof_envelope(&envelope).unwrap();

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
        let envelope = decode_mdoc_proof_envelope(&proof).expect("V8 envelope decodes");
        assert_eq!(envelope.version, MDOC_PROOF_ENVELOPE_VERSION);
        assert!(!envelope.compressed_proof.is_empty());
        assert!(
            verify_identity(statement.clone(), proof.clone())
                .expect("identity verification returns")
                .ok,
            "canonical v2 fixture must verify through the SDK identity API"
        );

        let mut changed = statement.clone();
        changed.session_transcript =
            eu_id_prover::mdoc::openid4vp_session_transcript(b"other-session");
        assert!(!verify_identity(changed, proof.clone()).unwrap().ok);

        let mut changed = statement.clone();
        changed.now_epoch_seconds += 1;
        assert!(!verify_identity(changed, proof.clone()).unwrap().ok);

        let mut changed = statement;
        changed.age_threshold_years = Some(changed.age_threshold_years.unwrap() + 1);
        assert!(!verify_identity(changed, proof).unwrap().ok);
    }

    #[test]
    #[ignore = "runs the product mdoc STWO prover: single-predicate modes end-to-end"]
    fn identity_public_api_round_trips_single_predicate_modes() {
        // A nationality-only statement must not request birth date.
        // An age-only statement must not request nationality.
        let (base, witness) = canonical_v2_mdoc_sdk_fixture();

        let mut age_only = base.clone();
        age_only.predicate_mode = PredicateMode::Age;
        age_only.accepted_alpha2_countries = None;
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
    fn encode_statement_uses_rfc8949_deterministic_map_order() {
        let encoded = encode_statement(&sample_statement());
        let decoded: Value =
            ciborium::de::from_reader(encoded.as_slice()).expect("statement CBOR decodes");
        let Value::Map(entries) = decoded else {
            panic!("statement must encode as a CBOR map");
        };
        let keys: Vec<&str> = entries
            .iter()
            .map(|(key, _)| {
                let Value::Text(key) = key else {
                    panic!("statement map keys must be text");
                };
                key.as_str()
            })
            .collect();
        assert_eq!(
            keys,
            [
                "v",
                "age",
                "nat",
                "now",
                "doctype",
                "spec_id",
                "namespace",
                "issuer_key",
                "profile_id",
                "revocation",
                "circuit_hash",
                "predicate_mode",
                "root_policy_hash",
                "session_transcript",
            ]
        );

        let issuer_key = entries
            .iter()
            .find_map(|(key, value)| {
                (key == &Value::Text("issuer_key".to_string())).then_some(value)
            })
            .expect("issuer_key exists");
        let Value::Map(issuer_entries) = issuer_key else {
            panic!("issuer_key must encode as a map");
        };
        let issuer_keys: Vec<&str> = issuer_entries
            .iter()
            .map(|(key, _)| {
                let Value::Text(key) = key else {
                    panic!("issuer-key map keys must be text");
                };
                key.as_str()
            })
            .collect();
        assert_eq!(issuer_keys, ["x", "y", "crv"]);
    }

    #[test]
    fn request_binding_is_deterministic_and_binds_the_complete_contract() {
        let statement = sample_statement();
        let expected = request_binding(&statement);
        assert_eq!(expected, request_binding(&statement));

        let mut variants = Vec::new();
        let mut changed = statement.clone();
        changed.spec_id.push_str("-other");
        variants.push(changed);
        let mut changed = statement.clone();
        changed.version += 1;
        variants.push(changed);
        let mut changed = statement.clone();
        changed.profile_id.push_str("-other");
        variants.push(changed);
        let mut changed = statement.clone();
        changed.circuit_hash.replace_range(..2, "ff");
        variants.push(changed);
        let mut changed = statement.clone();
        changed.root_policy_hash[0] ^= 1;
        variants.push(changed);
        let mut changed = statement.clone();
        changed.doctype.push_str(".other");
        variants.push(changed);
        let mut changed = statement.clone();
        changed.namespace.push_str(".other");
        variants.push(changed);
        let mut changed = statement.clone();
        changed.issuer_public_key_x[0] ^= 1;
        variants.push(changed);
        let mut changed = statement.clone();
        changed.issuer_public_key_y[0] ^= 1;
        variants.push(changed);
        let mut changed = statement.clone();
        changed.now_epoch_seconds += 86_400;
        variants.push(changed);
        let mut changed = statement.clone();
        changed.session_transcript.push(0xff);
        variants.push(changed);
        let mut changed = statement.clone();
        changed.predicate_mode = PredicateMode::Age;
        variants.push(changed);
        let mut changed = statement.clone();
        changed.age_threshold_years = Some(21);
        variants.push(changed);
        let mut changed = statement.clone();
        changed.accepted_alpha2_countries = Some(vec!["BE".to_string(), "CY".to_string()]);
        variants.push(changed);
        let mut changed = statement.clone();
        changed.revocation_public_key_x[0] ^= 1;
        variants.push(changed);
        let mut changed = statement.clone();
        changed.revocation_public_key_y[0] ^= 1;
        variants.push(changed);
        let mut changed = statement.clone();
        changed.revocation_epoch += 1;
        variants.push(changed);

        for variant in variants {
            assert_ne!(
                expected,
                request_binding(&variant),
                "every canonical request field must affect the binding"
            );
        }
    }

    #[test]
    fn product_contract_rejects_every_unsupported_identity_label() {
        let statement = sample_statement();
        validate_product_statement_contract(&statement).unwrap();

        let mut invalid = Vec::new();
        let mut changed = statement.clone();
        changed.spec_id = "other-spec".to_string();
        invalid.push(changed);
        let mut changed = statement.clone();
        changed.version = PRODUCT_STATEMENT_VERSION + 1;
        invalid.push(changed);
        let mut changed = statement.clone();
        changed.doctype = "other.doctype".to_string();
        invalid.push(changed);
        let mut changed = statement;
        changed.namespace = "other.namespace".to_string();
        invalid.push(changed);

        for statement in invalid {
            assert!(matches!(
                validate_product_statement_contract(&statement),
                Err(ZkError::InvalidInput(_))
            ));
        }
    }

    #[test]
    fn product_contract_bounds_and_canonicalizes_public_vectors() {
        let rejects = |statement: ZkPublicStatement| {
            assert!(matches!(
                validate_product_statement_contract(&statement),
                Err(ZkError::InvalidInput(_))
            ));
        };

        let mut changed = sample_statement();
        changed
            .issuer_public_key_x
            .truncate(P256_COORDINATE_BYTES - 1);
        rejects(changed);
        let mut changed = sample_statement();
        changed
            .revocation_public_key_x
            .truncate(P256_COORDINATE_BYTES - 1);
        rejects(changed);
        let mut changed = sample_statement();
        changed.session_transcript.clear();
        rejects(changed);

        let mut changed = sample_statement();
        changed.session_transcript = vec![0; MAX_SESSION_TRANSCRIPT_BYTES + 1];
        rejects(changed);

        let mut changed = sample_statement();
        changed.predicate_mode = PredicateMode::Age;
        changed.accepted_alpha2_countries = None;
        validate_product_statement_contract(&changed).unwrap();
        changed.accepted_alpha2_countries = Some(vec!["BE".to_string(), "CY".to_string()]);
        rejects(changed);

        let mut changed = sample_statement();
        changed.predicate_mode = PredicateMode::Nat;
        changed.age_threshold_years = None;
        validate_product_statement_contract(&changed).unwrap();
        changed.age_threshold_years = Some(18);
        rejects(changed);

        let mut changed = sample_statement();
        changed.accepted_alpha2_countries = Some(vec!["CY".to_string(), "BE".to_string()]);
        rejects(changed);

        let mut changed = sample_statement();
        changed.accepted_alpha2_countries =
            Some(vec!["BE".to_string(), "BE".to_string(), "CY".to_string()]);
        rejects(changed);

        let mut changed = sample_statement();
        changed.accepted_alpha2_countries = Some(vec!["BE".to_string()]);
        validate_product_statement_contract(&changed).unwrap();

        let mut changed = sample_statement();
        changed.accepted_alpha2_countries = Some(Vec::new());
        rejects(changed);

        let mut changed = sample_statement();
        changed.accepted_alpha2_countries = Some(vec!["BE".to_string(), "ZZ".to_string()]);
        rejects(changed);

        let mut changed = sample_statement();
        changed.accepted_alpha2_countries =
            Some(vec!["AA".to_string(); MAX_ACCEPTED_ALPHA2_COUNTRIES + 1]);
        rejects(changed);
    }

    fn bounded_witness(document: Vec<u8>) -> ZkMdocWitness {
        ZkMdocWitness {
            document,
            revocation_id_lo: 0,
            revocation_id_hi: u64::MAX,
            revocation_signature_r: vec![1; P256_COORDINATE_BYTES],
            revocation_signature_s: vec![1; P256_COORDINATE_BYTES],
        }
    }

    #[test]
    fn product_witness_rejects_unbounded_documents() {
        validate_product_witness(&bounded_witness(vec![0x80])).unwrap();

        for witness in [
            bounded_witness(Vec::new()),
            bounded_witness(vec![0; MAX_PRODUCT_MDOC_DOCUMENT_BYTES + 1]),
        ] {
            assert!(matches!(
                validate_product_witness(&witness),
                Err(ZkError::InvalidInput(_))
            ));
        }
    }

    #[test]
    fn product_witness_rejects_malformed_or_deep_cbor_before_decoding() {
        for document in [
            vec![0x9f, 0xff],
            [vec![0x81; 9], vec![0xf6]].concat(),
            vec![0x80, 0x80],
        ] {
            let witness = bounded_witness(document);
            assert!(matches!(
                validate_product_witness(&witness),
                Err(ZkError::InvalidInput(message)) if message.contains("CBOR structure")
            ));
        }
    }

    #[test]
    fn mdoc_request_rejects_malformed_revocation_witness_fields() {
        let statement = sample_statement();
        let public_statement = reconstruct_mdoc_statement(&statement).unwrap();
        let mut witness = bounded_witness(vec![0x80]);
        witness.revocation_id_lo = 1;
        witness.revocation_id_hi = 1;
        assert!(matches!(
            mdoc_request(&statement, &witness, &public_statement),
            Err(ZkError::InvalidInput(message)) if message.contains("revocation bounds")
        ));

        witness.revocation_id_lo = 0;
        witness.revocation_id_hi = 2;
        witness.revocation_signature_r.clear();
        assert!(matches!(
            mdoc_request(&statement, &witness, &public_statement),
            Err(ZkError::InvalidInput(message)) if message.contains("revocation P-256 signature")
        ));
    }

    #[test]
    fn public_entry_points_validate_the_product_contract_before_proof_processing() {
        let mut statement = sample_statement();
        statement.version = PRODUCT_STATEMENT_VERSION + 1;
        let witness = ZkMdocWitness {
            document: Vec::new(),
            revocation_id_lo: 0,
            revocation_id_hi: u64::MAX,
            revocation_signature_r: vec![1; 32],
            revocation_signature_s: vec![1; 32],
        };

        assert!(matches!(
            prove_identity(statement.clone(), witness),
            Err(ZkError::InvalidInput(_))
        ));
        assert!(matches!(
            verify_identity(statement, Vec::new()),
            Err(ZkError::InvalidInput(_))
        ));
    }

    #[test]
    fn public_entry_points_reject_a_noncanonical_session_transcript() {
        let mut statement = sample_statement();
        statement.session_transcript = vec![0x9f, 0xff];
        let witness = ZkMdocWitness {
            document: Vec::new(),
            revocation_id_lo: 0,
            revocation_id_hi: u64::MAX,
            revocation_signature_r: vec![1; 32],
            revocation_signature_s: vec![1; 32],
        };

        assert!(matches!(
            prove_identity(statement.clone(), witness),
            Err(ZkError::InvalidInput(_))
        ));
        assert!(matches!(
            verify_identity(statement, Vec::new()),
            Err(ZkError::InvalidInput(_))
        ));
    }

    #[test]
    fn verify_rejects_a_malformed_proof() {
        // Garbage bytes do not deserialize to an envelope -> fail-closed, no error.
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
    fn decompression_rejects_trailing_bytes_and_additional_frames() {
        let frame = compress_stark_proof_for_ffi(b"first proof").unwrap();
        let second_frame = compress_stark_proof_for_ffi(b"second proof").unwrap();
        let empty_frame = compress_stark_proof_for_ffi(b"").unwrap();
        let skippable_frame = [0x50, 0x2a, 0x4d, 0x18, 0, 0, 0, 0];

        for suffix in [vec![0], second_frame, empty_frame, skippable_frame.to_vec()] {
            let mut input = frame.clone();
            input.extend_from_slice(&suffix);
            assert!(matches!(
                decompress_stark_proof_from_ffi(&input),
                Err(ZkError::Verify(message)) if message.contains("trailing or concatenated")
            ));
        }
    }

    #[test]
    fn envelope_decoder_rejects_wrong_version_and_trailing_bytes() {
        let mut envelope = MdocProofEnvelope {
            version: MDOC_PROOF_ENVELOPE_VERSION - 1,
            compressed_proof: Vec::new(),
        };
        let encoded = encode_mdoc_proof_envelope(&envelope).unwrap();
        assert_eq!(
            encoded,
            bincode::serialize(&envelope).unwrap(),
            "bounded envelope options must remain byte-compatible with bincode v1 fixed-int encoding"
        );
        assert!(decode_mdoc_proof_envelope(&encoded).is_err());

        for version in (0..MDOC_PROOF_ENVELOPE_VERSION).chain([9, u16::MAX]) {
            envelope.version = version;
            let encoded = encode_mdoc_proof_envelope(&envelope).unwrap();
            assert!(matches!(
                decode_mdoc_proof_envelope(&encoded),
                Err(ZkError::Verify(message)) if message == "unsupported proof envelope version"
            ));
        }

        envelope.version = MDOC_PROOF_ENVELOPE_VERSION;
        let mut encoded = encode_mdoc_proof_envelope(&envelope).unwrap();
        encoded.push(0xff);
        assert!(decode_mdoc_proof_envelope(&encoded).is_err());

        let decoded = decode_mdoc_proof_envelope(
            &encode_mdoc_proof_envelope(&envelope).expect("V8 envelope encodes"),
        )
        .expect("V8 envelope decodes");
        assert_eq!(decoded, envelope);
    }

    #[test]
    fn v8_envelope_contains_only_version_and_compressed_proof() {
        let compressed_proof = vec![0xa5; 17];
        let envelope = MdocProofEnvelope {
            version: MDOC_PROOF_ENVELOPE_VERSION,
            compressed_proof: compressed_proof.clone(),
        };
        let encoded = encode_mdoc_proof_envelope(&envelope).unwrap();

        assert_eq!(encoded.len(), 2 + 8 + compressed_proof.len());
        assert_eq!(decode_mdoc_proof_envelope(&encoded).unwrap(), envelope);
    }

    #[test]
    fn envelope_decoder_rejects_oversized_inputs_before_nested_decode() {
        let oversized = vec![0u8; MAX_MDOC_PROOF_ENVELOPE_BYTES + 1];
        assert!(matches!(
            decode_mdoc_proof_envelope(&oversized),
            Err(ZkError::Verify(message)) if message.contains("envelope exceeds")
        ));

        let envelope = MdocProofEnvelope {
            version: MDOC_PROOF_ENVELOPE_VERSION,
            compressed_proof: vec![0u8; MAX_COMPRESSED_STARK_PROOF_BYTES + 1],
        };
        let encoded = encode_mdoc_proof_envelope(&envelope).unwrap();
        assert!(matches!(
            decode_mdoc_proof_envelope(&encoded),
            Err(ZkError::Verify(message)) if message.contains("compressed STARK proof")
        ));
    }

    #[test]
    fn streaming_decompression_rejects_output_past_the_limit() {
        let oversized_raw = vec![0x5a; MAX_DECOMPRESSED_STARK_PROOF_BYTES + 1];
        let compressed = zstd::bulk::compress(&oversized_raw, 1).unwrap();
        assert!(compressed.len() < MAX_COMPRESSED_STARK_PROOF_BYTES);
        assert!(matches!(
            decompress_stark_proof_from_ffi(&compressed),
            Err(ZkError::Verify(message)) if message.contains("decompressed STARK proof")
        ));
    }

    #[test]
    fn streaming_decompression_rejects_frames_with_oversized_windows() {
        let mut encoder =
            zstd::stream::write::Encoder::new(Vec::new(), 1).expect("zstd encoder initializes");
        encoder
            .window_log(MAX_ZSTD_WINDOW_LOG + 1)
            .expect("test encoder accepts a larger window");
        encoder
            .write_all(b"small payload")
            .expect("test payload compresses");
        let compressed = encoder.finish().expect("test frame finishes");

        assert!(matches!(
            decompress_stark_proof_from_ffi(&compressed),
            Err(ZkError::Verify(message)) if message.contains("decompress")
        ));
    }

    #[test]
    fn large_stack_verifier_panics_map_to_verify_errors() {
        let error = on_large_stack::<(), _>("verifier", ZkError::Verify, || {
            panic!("intentional verifier panic")
        })
        .unwrap_err();
        assert!(matches!(
            error,
            ZkError::Verify(message) if message.contains("verifier thread panicked")
        ));
    }

    #[test]
    fn verify_rejects_corrupt_compressed_proof() {
        let statement = sample_statement();
        let envelope = encode_mdoc_proof_envelope(&MdocProofEnvelope {
            version: MDOC_PROOF_ENVELOPE_VERSION,
            compressed_proof: b"not a zstd frame".to_vec(),
        })
        .unwrap();
        assert!(!verify_identity(statement, envelope).unwrap().ok);
    }

    #[test]
    fn verify_rejects_compressed_non_proof_bytes() {
        let statement = sample_statement();
        let compressed_junk = compress_stark_proof_for_ffi(b"not a stark proof").unwrap();
        let envelope = encode_mdoc_proof_envelope(&MdocProofEnvelope {
            version: MDOC_PROOF_ENVELOPE_VERSION,
            compressed_proof: compressed_junk,
        })
        .unwrap();
        assert!(!verify_identity(statement, envelope).unwrap().ok);
    }

    #[test]
    fn omitted_predicates_drop_their_subkeys() {
        // Age-only statement: the `nat` sub-map must be absent, so its encoding
        // is strictly shorter than the both-predicates one.
        let mut age_only = sample_statement();
        age_only.predicate_mode = PredicateMode::Age;
        age_only.accepted_alpha2_countries = None;

        let both = sample_statement();
        assert!(encode_statement(&age_only).len() < encode_statement(&both).len());
    }
}
