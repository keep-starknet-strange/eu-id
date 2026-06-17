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
//! ## Stub status
//! `prove_identity` returns the canonical statement bytes as the "proof" (a
//! deterministic round trip), and `verify_identity` returns `ok = true`. The
//! real STWO proving swaps in behind this exact surface later — §6, §8 N1.

use ciborium::value::Value;

uniffi::setup_scaffolding!();

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

/// Prove the public statement holds for the given witness.
///
/// STUB: returns the canonical statement bytes as the "proof" (deterministic
/// round trip), so the stub verifier can confirm the claims survived transport
/// — the agreed §9 choice.
///
/// TODO(real): build `I`/`W` field elements via the shared map, run the STWO
/// prover, return the serialized `StarkProof`.
#[uniffi::export]
pub fn prove_identity(
    statement: ZkPublicStatement,
    _witness: ZkWitness,
) -> Result<Vec<u8>, ZkError> {
    Ok(encode_statement(&statement))
}

/// Verify a proof against the public statement.
///
/// STUB: `ok` is true iff the proof bytes equal this statement's canonical
/// encoding — i.e. the round trip from [`prove_identity`] survived transport. A
/// caller (e.g. the wallet) can pass deliberately mismatched bytes to exercise
/// the rejection path. TODO(real): re-derive `I` field elements via the shared
/// map and verify the `StarkProof`.
#[uniffi::export]
pub fn verify_identity(
    statement: ZkPublicStatement,
    proof: Vec<u8>,
) -> Result<ZkVerifyResult, ZkError> {
    Ok(ZkVerifyResult {
        ok: proof == encode_statement(&statement),
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

    #[test]
    fn encode_statement_is_deterministic() {
        let s = sample_statement();
        assert_eq!(encode_statement(&s), encode_statement(&s));
    }

    #[test]
    fn stub_prove_returns_canonical_statement_bytes() {
        let s = sample_statement();
        let proof = prove_identity(s.clone(), sample_witness()).unwrap();
        assert_eq!(proof, encode_statement(&s));
    }

    #[test]
    fn stub_verify_accepts_a_matching_proof() {
        // The §9 round trip: prove emits statement bytes, the stub verifier
        // accepts — the end-to-end shape both apps exercise.
        let s = sample_statement();
        let proof = prove_identity(s.clone(), sample_witness()).unwrap();
        let result = verify_identity(s, proof).unwrap();
        assert!(result.ok);
    }

    #[test]
    fn stub_verify_rejects_a_mismatched_proof() {
        // Lets the wallet fake a bad proof to exercise the rejection path.
        let s = sample_statement();
        let result = verify_identity(s, b"not the statement".to_vec()).unwrap();
        assert!(!result.ok);
    }

    #[test]
    fn stub_verify_rejects_proof_for_a_different_statement() {
        // A proof produced for statement A must not verify against statement B.
        let a = sample_statement();
        let mut b = sample_statement();
        b.age_threshold_years = Some(21);

        let proof_for_a = prove_identity(a, sample_witness()).unwrap();
        assert!(!verify_identity(b, proof_for_a).unwrap().ok);
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
}
