//! EU-ID ZK SDK — the prover/verifier data contract, exposed to Kotlin/Swift via
//! UniFFI.
//!
//! This crate is the *single* place the canonical statement encoding and the
//! prove/verify entry points live (see the integration plan, §5/§6). Both the
//! wallet (prove) and the verifier (verify) call this same code, so the wire
//! format is structurally impossible to drift — there is no second
//! implementation to disagree with.
//!
//! Everything here is mdoc-agnostic: callers pass already-extracted raw bytes
//! (issuer key, signature, MSO, item bytes, …) and get back a proof or verdict.
//! No Multipaz / verifier-core types leak in.
//!
//! ## What the proof binds (§9.2)
//! `prove_identity` runs the real STWO combined prover (`eu_id_prover`) over the
//! POC credential and returns a [`ProofEnvelope`]: the bzip2-compressed,
//! bincode-serialized STARK `Proof` **plus** the canonical-CBOR bytes of the
//! full [`ZkPublicStatement`].
//! The two layers bind complementary things:
//!
//! - **The STARK** binds `{ demo issuer key Q, age public input, nat public
//!   input }` — i.e. the age threshold + reference date and the accepted
//!   nationality set, plus (internally) that the signature is over `SHA-256(C)`
//!   and that the DOB / nationality the predicates reason about are the signed
//!   credential's bytes.
//! - **The envelope** binds everything the STARK does *not* cover but the mdoc
//!   contract carries: `nonce` (the `SessionTranscript` freshness / anti-replay
//!   value), `doctype`, `namespace`, `spec_id`, and `version`. `verify_identity`
//!   rejects (fail-closed `ok = false`) if the envelope's statement bytes drift
//!   from the verifier's own [`encode_statement`].
//!
//! This preserves the stub's "the statement survived transport" guarantee on top
//! of the real proof, so freshness / doctype are not silently dropped when the
//! stub body is swapped out.
//!
//! The combined prover overflows a small default thread stack (`EXC_BAD_ACCESS`
//! on device — see ROADMAP_E2E §7.2), so both entry points run the heavy work on
//! a dedicated large-stack thread the SDK owns; the apps call the UniFFI fn
//! synchronously and do no thread handling of their own.

use std::io::{Read, Write};

use bzip2::read::BzDecoder;
use bzip2::write::BzEncoder;
use bzip2::Compression;
use ciborium::value::Value;
use serde::{Deserialize, Serialize};

uniffi::setup_scaffolding!();

// The pure contract↔prover translation layer (§9.1): `to_public_statement` /
// `to_policy` / `to_credential` build the prover's relying-party types from the
// UniFFI contract types. Wired into the real prove/verify bodies below (§9.2).
mod mapping;

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
#[derive(uniffi::Record, Clone, Debug, PartialEq, Eq)]
pub struct ZkPublicStatement {
    pub spec_id: String,
    pub version: u32,
    pub doctype: String,
    pub namespace: String,
    /// P-256 issuer public key coordinates (32 bytes each).
    pub issuer_key_x: Vec<u8>,
    pub issuer_key_y: Vec<u8>,
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

/// The PRIVATE witness `W` — wallet-only, never leaves the device. Only the
/// prove side consumes it. Fields are already-extracted raw mdoc bytes.
#[derive(uniffi::Record, Clone, Debug)]
pub struct ZkWitness {
    /// ECDSA signature components.
    pub issuer_sig_r: Vec<u8>,
    pub issuer_sig_s: Vec<u8>,
    /// The COSE `Sig_structure` that the issuer signed (`hash = SHA256(..)`).
    pub sig_structure: Vec<u8>,
    /// The MSO bytes (carry `valueDigests`).
    pub mso: Vec<u8>,
    /// `IssuerSignedItemBytes` for each attribute.
    pub birth_date_item: Vec<u8>,
    pub nationality_item: Vec<u8>,
    /// The cleartext attribute values.
    pub birth_date: String,
    pub nationalities: Vec<u32>,
    /// Which MSO digest slots the items occupy.
    pub digest_ids: std::collections::HashMap<String, u32>,
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
            Value::Map(vec![
                ("crv".into(), "P-256".into()),
                ("x".into(), Value::Bytes(s.issuer_key_x.clone())),
                ("y".into(), Value::Bytes(s.issuer_key_y.clone())),
            ]),
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

/// The wire format `prove_identity` returns and `verify_identity` consumes: the
/// real STARK proof alongside the full statement it does not itself bind.
///
/// `statement_bytes` is [`encode_statement`] of the *whole* [`ZkPublicStatement`]
/// (incl. `nonce` / `doctype` / `namespace` / `spec_id` / `version`); the
/// verifier rebuilds the same bytes from its own statement and rejects on any
/// drift, so the mdoc freshness / anti-replay nonce is bound even though the
/// STARK only covers `{ Q, age input, nat input }`.
#[derive(Serialize, Deserialize)]
struct ProofEnvelope {
    /// Canonical CBOR of the full public statement (the envelope binding).
    statement_bytes: Vec<u8>,
    /// bzip2-compressed bincode of the `eu_id_prover::Proof` (the STARK binding).
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
        // Witness-generation / proving failures — incl. the "no honest witness
        // exists" cases (under-age DOB, code outside the accepted set, an
        // invalid signature) that the prover rejects before it can prove.
        P256Prepare(_) | AgePrepare(_) | NatPrepare(_) | SignatureInvalid | Prove(_) => {
            ZkError::Prove(format!("{e:?}"))
        }
        // Verifier-side rejections (only reachable from the verify path).
        P256InstanceMismatch | IssuerKeyMismatch | AgePolicyMismatch | NatPolicyMismatch
        | Verify(_) => ZkError::Verify(format!("{e:?}")),
    }
}

/// Compress the raw bincode STARK proof for the FFI transport envelope.
fn compress_stark_proof_for_ffi(raw_bincode: &[u8]) -> Result<Vec<u8>, ZkError> {
    let mut encoder = BzEncoder::new(Vec::new(), Compression::best());
    encoder
        .write_all(raw_bincode)
        .map_err(|e| ZkError::Prove(format!("failed to compress proof: {e}")))?;
    encoder
        .finish()
        .map_err(|e| ZkError::Prove(format!("failed to finish proof compression: {e}")))
}

/// Decompress the FFI transport proof payload back to raw bincode bytes.
fn decompress_stark_proof_from_ffi(compressed: &[u8]) -> Result<Vec<u8>, ZkError> {
    let mut decoder = BzDecoder::new(compressed);
    let mut raw_bincode = Vec::new();
    decoder
        .read_to_end(&mut raw_bincode)
        .map_err(|e| ZkError::Verify(format!("failed to decompress proof: {e}")))?;
    Ok(raw_bincode)
}

/// Prove the public statement holds for the given witness.
///
/// Maps the mdoc-shaped contract to the prover's `Credential` / `Policy` (§9.1),
/// signs with the deterministic [`IssuerKey::demo`] (decision 1 — the real EU
/// issuer key in `statement.issuer_key_x/y` is ignored this iteration), runs the
/// real combined STWO prover, and returns a bincode-serialized [`ProofEnvelope`]
/// (compressed STARK proof + the full statement bytes). Runs on a large-stack
/// thread.
///
/// A false statement (e.g. under-age) cannot be proven and returns
/// [`ZkError::Prove`]; a structurally invalid request returns
/// [`ZkError::InvalidInput`].
#[uniffi::export]
pub fn prove_identity(
    statement: ZkPublicStatement,
    witness: ZkWitness,
) -> Result<Vec<u8>, ZkError> {
    on_large_stack(move || {
        let policy = mapping::to_policy(&statement)?;
        let credential = mapping::to_credential(&witness, &policy)?;
        let issuer = eu_id_prover::IssuerKey::demo();

        let proof = eu_id_prover::prove_identity(&credential, &issuer, &policy)
            .map_err(map_prover_error)?;
        let stark_proof_bincode = bincode::serialize(&proof)
            .map_err(|e| ZkError::Prove(format!("failed to serialize proof: {e}")))?;
        let stark_proof = compress_stark_proof_for_ffi(&stark_proof_bincode)?;

        let envelope = ProofEnvelope {
            // The full statement (incl. nonce / doctype / …) — bound by the
            // envelope, not the STARK.
            statement_bytes: encode_statement(&statement),
            stark_proof,
        };
        bincode::serialize(&envelope)
            .map_err(|e| ZkError::Prove(format!("failed to serialize proof envelope: {e}")))
    })
}

/// Verify a proof against the public statement.
///
/// Deserializes the [`ProofEnvelope`], checks its statement bytes match the
/// verifier's own [`encode_statement`] (the full-statement / anti-replay
/// binding), rebuilds the [`PublicStatement`] via §9.1, and runs the real STARK
/// verifier. `ok` is true iff every layer accepts; any rejection — envelope
/// drift, a malformed proof, or a broken STARK balance — is fail-closed
/// `ok = false`. A structurally invalid *request* returns
/// [`ZkError::InvalidInput`]. Runs on a large-stack thread.
#[uniffi::export]
pub fn verify_identity(
    statement: ZkPublicStatement,
    proof: Vec<u8>,
) -> Result<ZkVerifyResult, ZkError> {
    on_large_stack(move || {
        // A malformed envelope is a rejected proof, not a caller error.
        let envelope: ProofEnvelope = match bincode::deserialize(&proof) {
            Ok(envelope) => envelope,
            Err(_) => return Ok(ZkVerifyResult { ok: false }),
        };

        // Full-statement binding: the envelope must carry the exact statement the
        // verifier expects — this is where `nonce` / `doctype` / `namespace` /
        // `spec_id` / `version` (none of which the STARK covers) are enforced.
        if envelope.statement_bytes != encode_statement(&statement) {
            return Ok(ZkVerifyResult { ok: false });
        }

        // The verifier rebuilds the statement from its own request (decision 1:
        // demo Q, never the supplied issuer key). A structurally invalid request
        // is a caller error; a well-formed-but-wrong one falls through to the
        // STARK check below.
        let public_statement = mapping::to_public_statement(&statement)?;

        let stark_proof_bincode = match decompress_stark_proof_from_ffi(&envelope.stark_proof) {
            Ok(bytes) => bytes,
            Err(_) => return Ok(ZkVerifyResult { ok: false }),
        };

        let stark_proof: eu_id_prover::Proof = match bincode::deserialize(&stark_proof_bincode) {
            Ok(stark_proof) => stark_proof,
            Err(_) => return Ok(ZkVerifyResult { ok: false }),
        };

        Ok(ZkVerifyResult {
            ok: eu_id_prover::verify_identity(&stark_proof, &public_statement).is_ok(),
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
            doctype: "eu.europa.ec.eudi.pid.1".to_string(),
            namespace: "eu.europa.ec.eudi.pid.1".to_string(),
            issuer_key_x: vec![0x11; 32],
            issuer_key_y: vec![0x22; 32],
            today_epoch_day: 7305,
            nonce: vec![0xab, 0xcd, 0xef],
            predicate_mode: PredicateMode::And,
            age_threshold_years: Some(18),
            accepted_numeric_countries: Some(vec![56, 196, 300]),
            nat_mode: NatMode::Any,
        }
    }

    fn sample_witness() -> ZkWitness {
        ZkWitness {
            issuer_sig_r: vec![1; 32],
            issuer_sig_s: vec![2; 32],
            sig_structure: vec![3; 16],
            mso: vec![4; 16],
            birth_date_item: vec![5; 8],
            nationality_item: vec![6; 8],
            birth_date: "1990-01-01".to_string(),
            nationalities: vec![300],
            digest_ids: std::collections::HashMap::new(),
        }
    }

    /// An honest statement: today 2020-01-01, age threshold 18, accepted set
    /// includes the held nationality — provable over [`honest_witness`].
    fn honest_statement(mode: PredicateMode) -> ZkPublicStatement {
        ZkPublicStatement {
            spec_id: "stwo-euid-pid-v1".to_string(),
            version: 1,
            doctype: "eu.europa.ec.eudi.pid.1".to_string(),
            namespace: "eu.europa.ec.eudi.pid.1".to_string(),
            issuer_key_x: vec![0x11; 32],
            issuer_key_y: vec![0x22; 32],
            today_epoch_day: 18262, // 2020-01-01
            nonce: vec![0x01, 0x02, 0x03, 0x04],
            predicate_mode: mode,
            age_threshold_years: Some(18),
            accepted_numeric_countries: Some(vec![276, 250]), // DE, FR
            nat_mode: NatMode::Any,
        }
    }

    /// Born 1990-07-15 (well over 18 on 2020-01-01), holds DE — in the accepted
    /// set above.
    fn honest_witness() -> ZkWitness {
        let mut w = sample_witness();
        w.birth_date = "1990-07-15".to_string();
        w.nationalities = vec![276];
        w
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
    fn ffi_stark_proof_payload_is_bzip2_compressed() {
        let raw_bincode = b"serialized stark proof bytes";
        let compressed = compress_stark_proof_for_ffi(raw_bincode).unwrap();

        assert!(
            compressed.starts_with(b"BZh"),
            "bzip2 payloads must carry the BZh stream header, got prefix {:?}",
            &compressed[..compressed.len().min(3)]
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
        let a = sample_statement();
        let mut b = sample_statement();
        b.nonce = vec![0xff; 8]; // a fresh session -> different statement bytes

        let envelope = bincode::serialize(&ProofEnvelope {
            statement_bytes: encode_statement(&a),
            stark_proof: b"opaque".to_vec(),
        })
        .unwrap();
        assert!(!verify_identity(b, envelope).unwrap().ok);
    }

    #[test]
    fn verify_rejects_matching_statement_but_corrupt_stark_proof() {
        // Envelope statement matches, but the inner STARK proof is junk -> the
        // STARK deserialization fails and the result is fail-closed.
        let s = sample_statement();
        let envelope = bincode::serialize(&ProofEnvelope {
            statement_bytes: encode_statement(&s),
            stark_proof: b"not a stark proof".to_vec(),
        })
        .unwrap();
        assert!(!verify_identity(s, envelope).unwrap().ok);
    }

    #[test]
    fn verify_rejects_matching_statement_but_compressed_corrupt_stark_proof() {
        // The FFI transport layer may be well-formed bzip2 while the decompressed
        // bytes are not a valid STARK proof. That still rejects fail-closed.
        let s = sample_statement();
        let compressed_junk = compress_stark_proof_for_ffi(b"not a stark proof").unwrap();
        let envelope = bincode::serialize(&ProofEnvelope {
            statement_bytes: encode_statement(&s),
            stark_proof: compressed_junk,
        })
        .unwrap();
        assert!(!verify_identity(s, envelope).unwrap().ok);
    }

    // ---- real prover round trips (slow; `cargo test -p sdk --release -- --ignored`) ----

    #[test]
    #[ignore = "runs the real combined STWO prover (~seconds); use --release --ignored"]
    fn real_round_trip_verifies() {
        let s = honest_statement(PredicateMode::And);
        let proof = prove_identity(s.clone(), honest_witness()).unwrap();
        assert!(verify_identity(s, proof).unwrap().ok);
    }

    #[test]
    #[ignore = "runs the real combined STWO prover (~seconds); use --release --ignored"]
    fn real_proof_for_statement_a_rejected_against_b() {
        // A genuine proof for A (threshold 18) must not verify against B
        // (threshold 21) — the policy drives both the envelope bytes and the
        // STARK's age public input, so both layers reject.
        let a = honest_statement(PredicateMode::And);
        let mut b = honest_statement(PredicateMode::And);
        b.age_threshold_years = Some(21);

        let proof_for_a = prove_identity(a, honest_witness()).unwrap();
        assert!(!verify_identity(b, proof_for_a).unwrap().ok);
    }

    #[test]
    #[ignore = "runs the real combined STWO prover (~seconds); use --release --ignored"]
    fn real_proof_rejected_when_only_the_nonce_differs() {
        // The purest anti-replay test: A and B share an identical policy, so the
        // STARK alone would accept the proof against either. They differ ONLY in
        // the freshness `nonce` — which the STARK does not bind. The envelope's
        // full-statement binding is what rejects the replay.
        let a = honest_statement(PredicateMode::And);
        let mut b = honest_statement(PredicateMode::And);
        b.nonce = vec![0xde, 0xad, 0xbe, 0xef]; // a different session

        // Sanity: the only difference is the nonce, so the derived policy (hence
        // everything the STARK binds) is identical — without the envelope, B
        // would accept A's proof.
        assert_eq!(
            mapping::to_policy(&a).unwrap(),
            mapping::to_policy(&b).unwrap()
        );

        let proof_for_a = prove_identity(a.clone(), honest_witness()).unwrap();
        assert!(verify_identity(a, proof_for_a.clone()).unwrap().ok);
        assert!(!verify_identity(b, proof_for_a).unwrap().ok);
    }

    #[test]
    #[ignore = "runs the real combined STWO prover (~seconds); use --release --ignored"]
    fn real_each_predicate_mode_round_trips() {
        for mode in [PredicateMode::Age, PredicateMode::Nat, PredicateMode::And] {
            let s = honest_statement(mode);
            let proof = prove_identity(s.clone(), honest_witness()).unwrap();
            assert!(verify_identity(s, proof).unwrap().ok, "mode {mode:?}");
        }
    }

    #[test]
    #[ignore = "runs the real combined STWO prover (~seconds); use --release --ignored"]
    fn real_under_age_is_an_unprovable_statement() {
        // Born 2015 -> not 18 on 2020-01-01; the age module rejects the witness,
        // so prove fails (a false statement, surfaced as ZkError::Prove) rather
        // than producing a proof that would fail to verify.
        let s = honest_statement(PredicateMode::Age);
        let mut w = honest_witness();
        w.birth_date = "2015-07-15".to_string();
        assert!(matches!(prove_identity(s, w), Err(ZkError::Prove(_))));
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
