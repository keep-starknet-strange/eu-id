//! Frozen native API, core routing, and V4 proof envelope for the unlinkable
//! TS13 demo.

use std::io::Cursor;

use bincode::Options;
use serde::de::DeserializeOwned;
use serde::Serialize;

use crate::{IssuerKey, NatMode, PredicateMode, TrustedIssuers};

const V4_MAGIC: &[u8; 8] = b"EUIDTS13";
const V4_VERSION: u16 = 4;
const V4_HEADER_BYTES: usize = 46;
const V4_CAPACITY_ALIGNMENT: u32 = 65_536;
#[cfg(test)]
const TS13_DEMO_PUBLIC_FIELD_NAMES: [&str; 11] = [
    "circuit_hash",
    "zk_system_id",
    "document_type",
    "namespace",
    "element_identifier",
    "expected_value_cbor",
    "timestamp_epoch_seconds",
    "session_transcript",
    "trusted_issuer_public_key",
    "revocation_public_key",
    "revocation_epoch",
];
#[cfg(test)]
const TS13_DEMO_V4_HEADER_FIELD_NAMES: [&str; 4] =
    ["magic", "envelope_version", "circuit_hash", "body_capacity"];
#[cfg(test)]
const TS13_DEMO_DERIVED_CONTEXT_STATE_FIELD_NAMES: [&str; 6] = [
    "canonical_session_transcript",
    "device_authentication_bytes",
    "device_cose_sig_structure",
    "verification_timestamp_rfc3339_utc",
    "canonical_context_cbor",
    "request_context_digest",
];
// Section 5.1's normative derived circuit values. The derived-context helper
// above also retains deterministic construction intermediates, but those are
// not additional verifier inputs or independent public circuit values.
#[cfg(test)]
const TS13_DEMO_DERIVED_CIRCUIT_VALUE_NAMES: [&str; 6] = [
    "session_transcript_sha256",
    "device_cose_sig_structure",
    "device_cose_sig_structure_length",
    "device_cose_sig_structure_sha256",
    "verification_timestamp_rfc3339_utc",
    "request_context_digest",
];
#[cfg(test)]
const TS13_DEMO_CIRCUIT_PUBLIC_FIELD_NAMES: [&str; 7] = [
    "circuit_hash",
    "request_context_digest",
    "timestamp_epoch_seconds",
    "verification_timestamp_rfc3339_utc",
    "trusted_issuer_public_key",
    "device_cose_sig_structure",
    "revocation",
];
#[cfg(test)]
const TS13_DEMO_REVOCATION_PUBLIC_FIELD_NAMES: [&str; 2] = ["revocation_public_key", "epoch"];
// Universal values are grouped by their normative role because the generated
// artifact owns the exact per-column/per-relation constants within its shape,
// geometry, and cryptographic-parameter manifests.
#[cfg(test)]
const TS13_DEMO_UNIVERSAL_CIRCUIT_CONSTANT_NAMES: [&str; 11] = [
    "context_label",
    "proof_system_name",
    "public_context_transcript_domain",
    "document_type",
    "namespace",
    "element_identifier",
    "expected_value_cbor",
    "credential_shape_manifest",
    "trace_geometry",
    "cryptographic_parameters",
    "device_cose_sig_structure_capacity",
];
#[cfg(test)]
const TS13_DEMO_COMPLETE_CLEAR_PUBLIC_SURFACE: [&str; 32] = [
    "semantic.circuit_hash",
    "semantic.zk_system_id",
    "semantic.document_type",
    "semantic.namespace",
    "semantic.element_identifier",
    "semantic.expected_value_cbor",
    "semantic.timestamp_epoch_seconds",
    "semantic.session_transcript",
    "semantic.trusted_issuer_public_key",
    "semantic.revocation_public_key",
    "semantic.revocation_epoch",
    "derived.session_transcript_sha256",
    "derived.device_cose_sig_structure",
    "derived.device_cose_sig_structure_length",
    "derived.device_cose_sig_structure_sha256",
    "derived.verification_timestamp_rfc3339_utc",
    "derived.request_context_digest",
    "v4_header.magic",
    "v4_header.envelope_version",
    "v4_header.circuit_hash",
    "v4_header.body_capacity",
    "universal.context_label",
    "universal.proof_system_name",
    "universal.public_context_transcript_domain",
    "universal.document_type",
    "universal.namespace",
    "universal.element_identifier",
    "universal.expected_value_cbor",
    "universal.credential_shape_manifest",
    "universal.trace_geometry",
    "universal.cryptographic_parameters",
    "universal.device_cose_sig_structure_capacity",
];

/// Existing product theorem, without any optional TS13 fields.
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

/// Existing product mdoc witness, without any optional TS13 fields.
#[derive(uniffi::Record, Clone, Debug)]
pub struct ProductMdocWitnessV1 {
    pub document: Vec<u8>,
    pub trusted_issuers: TrustedIssuers,
}

/// Exact semantic public statement for the TS13 demo profile.
#[derive(uniffi::Record, Clone, Debug, PartialEq, Eq)]
pub struct Ts13DemoPublicStatementV1 {
    pub circuit_hash: Vec<u8>,
    pub zk_system_id: String,
    pub document_type: String,
    pub namespace: String,
    pub element_identifier: String,
    pub expected_value_cbor: Vec<u8>,
    pub timestamp_epoch_seconds: i64,
    pub session_transcript: Vec<u8>,
    pub trusted_issuer_public_key: Vec<u8>,
    pub revocation_public_key: Vec<u8>,
    pub revocation_epoch: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ValidatedTs13DemoPublicStatementV1 {
    pub(crate) circuit_hash: [u8; 32],
    pub(crate) zk_system_id: String,
    pub(crate) document_type: String,
    pub(crate) namespace: String,
    pub(crate) element_identifier: String,
    pub(crate) expected_value_cbor: Vec<u8>,
    pub(crate) timestamp_epoch_seconds: i64,
    pub(crate) session_transcript: Vec<u8>,
    pub(crate) trusted_issuer_public_key: [u8; eu_id_prover::ts13_demo::ML_DSA_65_PUBLIC_KEY_BYTES],
    pub(crate) revocation_public_key: [u8; eu_id_prover::ts13_demo::ML_DSA_65_PUBLIC_KEY_BYTES],
    pub(crate) revocation_epoch: u32,
}

fn map_context_error(error: eu_id_prover::ts13_demo::Ts13DemoContextError) -> Ts13DemoError {
    match error {
        eu_id_prover::ts13_demo::Ts13DemoContextError::MalformedSessionTranscript => {
            Ts13DemoError::MalformedSessionTranscript
        }
        eu_id_prover::ts13_demo::Ts13DemoContextError::InvalidPublicContext => {
            Ts13DemoError::InvalidPublicContext
        }
    }
}

impl ValidatedTs13DemoPublicStatementV1 {
    pub(crate) fn derive_public_context(
        &self,
    ) -> Result<eu_id_prover::ts13_demo::Ts13DemoDerivedContext, Ts13DemoError> {
        eu_id_prover::ts13_demo::derive_public_context(
            eu_id_prover::ts13_demo::Ts13DemoPublicContextInput {
                circuit_hash: &self.circuit_hash,
                zk_system_id: &self.zk_system_id,
                document_type: &self.document_type,
                namespace: &self.namespace,
                element_identifier: &self.element_identifier,
                expected_value_cbor: &self.expected_value_cbor,
                timestamp_epoch_seconds: self.timestamp_epoch_seconds,
                session_transcript: &self.session_transcript,
                trusted_issuer_public_key: &self.trusted_issuer_public_key,
                revocation_public_key: &self.revocation_public_key,
                revocation_epoch: self.revocation_epoch,
            },
        )
        .map_err(map_context_error)
    }

    fn from_public(
        statement: &Ts13DemoPublicStatementV1,
    ) -> Result<(Self, eu_id_prover::ts13_demo::Ts13DemoDerivedContext), Ts13DemoError> {
        let validated = Self {
            circuit_hash: statement
                .circuit_hash
                .as_slice()
                .try_into()
                .map_err(|_| Ts13DemoError::InvalidPublicContext)?,
            zk_system_id: statement.zk_system_id.clone(),
            document_type: statement.document_type.clone(),
            namespace: statement.namespace.clone(),
            element_identifier: statement.element_identifier.clone(),
            expected_value_cbor: statement.expected_value_cbor.clone(),
            timestamp_epoch_seconds: statement.timestamp_epoch_seconds,
            session_transcript: statement.session_transcript.clone(),
            trusted_issuer_public_key: statement
                .trusted_issuer_public_key
                .as_slice()
                .try_into()
                .map_err(|_| Ts13DemoError::InvalidPublicContext)?,
            revocation_public_key: statement
                .revocation_public_key
                .as_slice()
                .try_into()
                .map_err(|_| Ts13DemoError::InvalidPublicContext)?,
            revocation_epoch: statement.revocation_epoch,
        };
        let derived = validated.derive_public_context()?;
        Ok((validated, derived))
    }
}

impl TryFrom<&Ts13DemoPublicStatementV1> for ValidatedTs13DemoPublicStatementV1 {
    type Error = Ts13DemoError;

    fn try_from(statement: &Ts13DemoPublicStatementV1) -> Result<Self, Self::Error> {
        Self::from_public(statement).map(|(validated, _)| validated)
    }
}

impl Ts13DemoPublicStatementV1 {
    /// Reconstruct every derived public circuit byte from this semantic
    /// statement; no derived value is accepted from a caller or proof.
    pub fn derive_public_context(
        &self,
    ) -> Result<eu_id_prover::ts13_demo::Ts13DemoDerivedContext, Ts13DemoError> {
        ValidatedTs13DemoPublicStatementV1::from_public(self).map(|(_, derived)| derived)
    }
}

/// Exact private witness for the TS13 demo profile.
#[derive(uniffi::Record, Clone)]
pub struct Ts13DemoWitnessV1 {
    pub document: Vec<u8>,
    pub revocation_id_lo: u64,
    pub revocation_id_hi: u64,
    pub revocation_signature: Vec<u8>,
}

/// Tagged public theorem. A product statement cannot be interpreted as TS13.
#[derive(uniffi::Enum, Clone, Debug, PartialEq, Eq)]
pub enum ZkPublicStatement {
    ProductV1(ProductPublicStatementV1),
    Ts13DemoV1(Ts13DemoPublicStatementV1),
}

/// Tagged private witness. Variant matching is checked before proving.
#[derive(uniffi::Enum, Clone)]
pub enum ZkMdocWitness {
    ProductV1(ProductMdocWitnessV1),
    Ts13DemoV1(Ts13DemoWitnessV1),
}

/// Reject mixed theorem/witness profiles before any credential is parsed.
pub fn validate_variant_pair(
    statement: &ZkPublicStatement,
    witness: &ZkMdocWitness,
) -> Result<(), Ts13DemoError> {
    match (statement, witness) {
        (ZkPublicStatement::ProductV1(_), ZkMdocWitness::ProductV1(_))
        | (ZkPublicStatement::Ts13DemoV1(_), ZkMdocWitness::Ts13DemoV1(_)) => Ok(()),
        _ => Err(Ts13DemoError::UnsupportedProofSystem),
    }
}

/// Frozen typed failures. No variant carries private bytes or values.
#[derive(uniffi::Error, Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Ts13DemoError {
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

/// Artifact-injected V4 constants. No provisional hash or capacity is compiled
/// into the SDK by this module.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ts13DemoV4Parameters {
    circuit_hash: [u8; 32],
    proof_body_capacity: u32,
}

impl Ts13DemoV4Parameters {
    pub fn new(circuit_hash: [u8; 32], proof_body_capacity: u32) -> Result<Self, Ts13DemoError> {
        if proof_body_capacity == 0 || proof_body_capacity % V4_CAPACITY_ALIGNMENT != 0 {
            return Err(Ts13DemoError::InvalidPublicContext);
        }
        Ok(Self {
            circuit_hash,
            proof_body_capacity,
        })
    }

    pub const fn circuit_hash(self) -> [u8; 32] {
        self.circuit_hash
    }

    pub const fn proof_body_capacity(self) -> u32 {
        self.proof_body_capacity
    }
}

fn v4_bincode_options(limit: u32) -> impl Options {
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_little_endian()
        .with_limit(u64::from(limit))
}

/// Encode one canonical bincode proof prefix followed by artifact-sized zero
/// padding. The semantic statement is never serialized into V4.
pub fn encode_v4<T: Serialize>(
    parameters: Ts13DemoV4Parameters,
    proof: &T,
) -> Result<Vec<u8>, Ts13DemoError> {
    let prefix = v4_bincode_options(parameters.proof_body_capacity)
        .serialize(proof)
        .map_err(|_| Ts13DemoError::ProofGenerationFailed)?;
    let capacity = parameters.proof_body_capacity as usize;
    if prefix.len() > capacity {
        return Err(Ts13DemoError::ProofGenerationFailed);
    }
    let total_len = V4_HEADER_BYTES
        .checked_add(capacity)
        .ok_or(Ts13DemoError::ProofGenerationFailed)?;
    let mut envelope = vec![0; total_len];
    envelope[..8].copy_from_slice(V4_MAGIC);
    envelope[8..10].copy_from_slice(&V4_VERSION.to_le_bytes());
    envelope[10..42].copy_from_slice(&parameters.circuit_hash);
    envelope[42..46].copy_from_slice(&parameters.proof_body_capacity.to_le_bytes());
    envelope[46..46 + prefix.len()].copy_from_slice(&prefix);
    Ok(envelope)
}

/// Decode exactly one bounded canonical proof prefix and require an all-zero
/// tail. `proof_shape_is_valid` is supplied by the generated circuit artifact
/// layer and must validate every fixed claim/vector length.
pub fn decode_v4<T, F>(
    parameters: Ts13DemoV4Parameters,
    envelope: &[u8],
    proof_shape_is_valid: F,
) -> Result<T, Ts13DemoError>
where
    T: DeserializeOwned + Serialize,
    F: FnOnce(&T) -> bool,
{
    if envelope.len() < V4_HEADER_BYTES
        || &envelope[..8] != V4_MAGIC
        || u16::from_le_bytes(
            envelope[8..10]
                .try_into()
                .map_err(|_| Ts13DemoError::MalformedProofEnvelope)?,
        ) != V4_VERSION
    {
        return Err(Ts13DemoError::MalformedProofEnvelope);
    }

    let encoded_hash: [u8; 32] = envelope[10..42]
        .try_into()
        .map_err(|_| Ts13DemoError::MalformedProofEnvelope)?;
    if encoded_hash != parameters.circuit_hash {
        return Err(Ts13DemoError::UnsupportedCircuitHash);
    }

    let encoded_capacity = u32::from_le_bytes(
        envelope[42..46]
            .try_into()
            .map_err(|_| Ts13DemoError::MalformedProofEnvelope)?,
    );
    if encoded_capacity != parameters.proof_body_capacity {
        return Err(Ts13DemoError::MalformedProofEnvelope);
    }
    let expected_len = V4_HEADER_BYTES
        .checked_add(encoded_capacity as usize)
        .ok_or(Ts13DemoError::MalformedProofEnvelope)?;
    if envelope.len() != expected_len {
        return Err(Ts13DemoError::MalformedProofEnvelope);
    }

    let body = &envelope[V4_HEADER_BYTES..];
    let mut cursor = Cursor::new(body);
    let proof: T = v4_bincode_options(parameters.proof_body_capacity)
        .allow_trailing_bytes()
        .deserialize_from(&mut cursor)
        .map_err(|_| Ts13DemoError::MalformedProofEnvelope)?;
    let consumed = cursor.position() as usize;
    let canonical_prefix = v4_bincode_options(parameters.proof_body_capacity)
        .serialize(&proof)
        .map_err(|_| Ts13DemoError::MalformedProofEnvelope)?;
    if consumed != canonical_prefix.len()
        || body.get(..consumed) != Some(canonical_prefix.as_slice())
        || body[consumed..].iter().any(|&byte| byte != 0)
        || !proof_shape_is_valid(&proof)
    {
        return Err(Ts13DemoError::MalformedProofEnvelope);
    }
    Ok(proof)
}

/// Resolves verifier-authoritative circuit parameters from a generated
/// artifact embedding. Implementations must never derive either value from
/// prover-controlled proof bytes.
pub(crate) trait Ts13DemoArtifactResolver {
    fn resolve(&self, circuit_hash: [u8; 32]) -> Result<Ts13DemoV4Parameters, Ts13DemoError>;
}

/// Compile-time artifact resolver used by the public SDK route.
pub(crate) struct CompiledTs13DemoArtifactResolver;

impl Ts13DemoArtifactResolver for CompiledTs13DemoArtifactResolver {
    fn resolve(&self, circuit_hash: [u8; 32]) -> Result<Ts13DemoV4Parameters, Ts13DemoError> {
        use eu_id_prover::ts13_demo_artifact_constants::{
            TS13_DEMO_CIRCUIT_HASH, TS13_DEMO_PROOF_BODY_CAPACITY,
        };

        if circuit_hash != TS13_DEMO_CIRCUIT_HASH {
            return Err(Ts13DemoError::UnsupportedCircuitHash);
        }
        Ts13DemoV4Parameters::new(TS13_DEMO_CIRCUIT_HASH, TS13_DEMO_PROOF_BODY_CAPACITY)
    }
}

struct PreparedTs13DemoPublicInput {
    parameters: Ts13DemoV4Parameters,
    request: eu_id_prover::MdocPidRequest,
    circuit: eu_id_prover::MdocTs13DemoCircuitPublicInput,
}

fn prepare_public_input<R: Ts13DemoArtifactResolver>(
    statement: &Ts13DemoPublicStatementV1,
    artifact_resolver: &R,
) -> Result<PreparedTs13DemoPublicInput, Ts13DemoError> {
    let (validated, derived) = ValidatedTs13DemoPublicStatementV1::from_public(statement)?;
    if derived.device_cose_sig_structure.len()
        > eu_id_prover::mdoc::TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY
    {
        return Err(Ts13DemoError::InvalidPublicContext);
    }

    let parameters = artifact_resolver.resolve(validated.circuit_hash)?;
    if parameters.circuit_hash() != validated.circuit_hash {
        return Err(Ts13DemoError::UnsupportedCircuitHash);
    }

    let request = eu_id_prover::MdocPidRequest {
        doctype: validated.document_type,
        namespace: validated.namespace,
        attributes: vec![eu_id_prover::mdoc::MdocRequestedAttribute {
            element_identifier: validated.element_identifier,
            mode: eu_id_prover::mdoc::MdocDisclosureMode::ValueEquality(
                validated.expected_value_cbor,
            ),
        }],
        birth_date_element: "birth_date".to_string(),
        nationality_element: "nationality".to_string(),
        session_transcript: derived.canonical_session_transcript,
        trusted_mldsa_issuer_public_keys: vec![validated.trusted_issuer_public_key.to_vec()],
        device_authentication_profile:
            eu_id_prover::mdoc::MdocDeviceAuthenticationProfile::Iso180135,
    };
    let circuit = eu_id_prover::MdocTs13DemoCircuitPublicInput {
        circuit_hash: validated.circuit_hash,
        request_context_digest: derived.request_context_digest,
        timestamp_epoch_seconds: validated.timestamp_epoch_seconds,
        verification_timestamp_rfc3339_utc: derived.verification_timestamp_rfc3339_utc,
        trusted_issuer_public_key: validated.trusted_issuer_public_key.to_vec(),
        device_cose_sig_structure: derived.device_cose_sig_structure,
        revocation: eu_id_prover::mdoc::MdocRevocationPublicInputs {
            revocation_public_key: eu_id_prover::mdoc::MdocRevocationKey::MlDsa(
                validated.revocation_public_key.to_vec(),
            ),
            epoch: validated.revocation_epoch,
        },
    };
    Ok(PreparedTs13DemoPublicInput {
        parameters,
        request,
        circuit,
    })
}

fn map_core_prove_error(error: eu_id_prover::Error) -> Ts13DemoError {
    match error {
        eu_id_prover::Error::UnsupportedDemoCredentialShape => {
            Ts13DemoError::UnsupportedDemoCredentialShape
        }
        eu_id_prover::Error::Mdoc(_)
        | eu_id_prover::Error::AuthInputMismatch
        | eu_id_prover::Error::AgePolicyMismatch
        | eu_id_prover::Error::NatPolicyMismatch => Ts13DemoError::InvalidPrivateCredential,
        _ => Ts13DemoError::ProofGenerationFailed,
    }
}

pub(crate) fn prove_ts13_demo_identity<R: Ts13DemoArtifactResolver>(
    statement: &Ts13DemoPublicStatementV1,
    witness: &Ts13DemoWitnessV1,
    artifact_resolver: &R,
) -> Result<Vec<u8>, Ts13DemoError> {
    let prepared = prepare_public_input(statement, artifact_resolver)?;
    if witness.revocation_id_lo >= witness.revocation_id_hi
        || witness.revocation_signature.len() != eu_id_prover::ts13_demo::ML_DSA_65_SIGNATURE_BYTES
    {
        return Err(Ts13DemoError::InvalidRevocationWitness);
    }
    let proof = eu_id_prover::prove_mdoc_ts13_demo(
        &witness.document,
        &prepared.request,
        &prepared.circuit,
        witness.revocation_id_lo,
        witness.revocation_id_hi,
        eu_id_prover::mdoc::MdocRevocationSignature::MlDsa(witness.revocation_signature.clone()),
    )
    .map_err(map_core_prove_error)?;
    encode_v4(prepared.parameters, &proof)
}

pub(crate) fn verify_ts13_demo_identity<R: Ts13DemoArtifactResolver>(
    statement: &Ts13DemoPublicStatementV1,
    envelope: &[u8],
    artifact_resolver: &R,
) -> Result<(), Ts13DemoError> {
    let prepared = prepare_public_input(statement, artifact_resolver)?;
    let proof: eu_id_prover::MdocProof = decode_v4(
        prepared.parameters,
        envelope,
        |proof: &eu_id_prover::MdocProof| proof.has_ts13_demo_shape(),
    )?;
    eu_id_prover::verify_mdoc_ts13_demo(&proof, &prepared.circuit)
        .map_err(|_| Ts13DemoError::ProofVerificationFailed)
}

#[cfg(test)]
mod tests {
    use serde::{Deserialize, Deserializer, Serializer};

    use super::*;

    const CAPACITY: u32 = 65_536;

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    struct DemoProof {
        claims: Vec<u32>,
        transcript: Vec<u8>,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct CanonicalByte;

    impl Serialize for CanonicalByte {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            serializer.serialize_u8(0)
        }
    }

    impl<'de> Deserialize<'de> for CanonicalByte {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            let _ignored = u8::deserialize(deserializer)?;
            Ok(Self)
        }
    }

    fn parameters() -> Ts13DemoV4Parameters {
        Ts13DemoV4Parameters::new([0x11; 32], CAPACITY).unwrap()
    }

    #[test]
    fn compiled_resolver_pins_generated_hash_and_capacity() {
        use eu_id_prover::ts13_demo_artifact_constants::{
            TS13_DEMO_CIRCUIT_HASH, TS13_DEMO_SHAPE_MANIFEST_SHA256,
            TS13_DEMO_SOUNDNESS_SOURCE_TREE_SHA256,
        };

        let expected_hash = TS13_DEMO_CIRCUIT_HASH;
        assert_ne!(
            expected_hash, [0; 32],
            "the compiled resolver must not accept the bootstrap placeholder"
        );
        assert_ne!(TS13_DEMO_SHAPE_MANIFEST_SHA256, [0; 32]);
        assert_ne!(TS13_DEMO_SOUNDNESS_SOURCE_TREE_SHA256, [0; 32]);
        let parameters = CompiledTs13DemoArtifactResolver
            .resolve(expected_hash)
            .expect("generated circuit is supported");
        assert_eq!(parameters.circuit_hash(), expected_hash);
        assert_eq!(
            parameters.proof_body_capacity(),
            eu_id_prover::ts13_demo_artifact_constants::TS13_DEMO_PROOF_BODY_CAPACITY
        );

        let mut unknown_hash = expected_hash;
        unknown_hash[0] ^= 1;
        assert_eq!(
            CompiledTs13DemoArtifactResolver.resolve(unknown_hash),
            Err(Ts13DemoError::UnsupportedCircuitHash)
        );
    }

    fn sample_ts13_statement() -> Ts13DemoPublicStatementV1 {
        Ts13DemoPublicStatementV1 {
            circuit_hash: vec![0x11; 32],
            zk_system_id: "rp-demo".to_string(),
            document_type: "eu.europa.ec.eudi.pid.1".to_string(),
            namespace: "eu.europa.ec.eudi.pid.1".to_string(),
            element_identifier: "age_over_18".to_string(),
            expected_value_cbor: vec![0xf5],
            timestamp_epoch_seconds: 1_735_689_600,
            session_transcript: vec![0x83, 0xf6, 0xf6, 0x81, 0x01],
            trusted_issuer_public_key: vec![0x22; 1_952],
            revocation_public_key: vec![0x33; 1_952],
            revocation_epoch: 7,
        }
    }

    #[test]
    fn ts13_public_schema_is_exact() {
        use std::collections::BTreeSet;

        let statement = sample_ts13_statement();
        let Ts13DemoPublicStatementV1 {
            circuit_hash: _,
            zk_system_id: _,
            document_type: _,
            namespace: _,
            element_identifier: _,
            expected_value_cbor: _,
            timestamp_epoch_seconds: _,
            session_transcript: _,
            trusted_issuer_public_key: _,
            revocation_public_key: _,
            revocation_epoch: _,
        } = statement;
        assert_eq!(
            TS13_DEMO_PUBLIC_FIELD_NAMES,
            [
                "circuit_hash",
                "zk_system_id",
                "document_type",
                "namespace",
                "element_identifier",
                "expected_value_cbor",
                "timestamp_epoch_seconds",
                "session_transcript",
                "trusted_issuer_public_key",
                "revocation_public_key",
                "revocation_epoch",
            ],
        );

        let qualified_names = [
            ("semantic", TS13_DEMO_PUBLIC_FIELD_NAMES.as_slice()),
            ("derived", TS13_DEMO_DERIVED_CIRCUIT_VALUE_NAMES.as_slice()),
            ("v4_header", TS13_DEMO_V4_HEADER_FIELD_NAMES.as_slice()),
            (
                "universal",
                TS13_DEMO_UNIVERSAL_CIRCUIT_CONSTANT_NAMES.as_slice(),
            ),
        ]
        .into_iter()
        .flat_map(|(surface, names)| names.iter().map(move |name| format!("{surface}.{name}")))
        .collect::<Vec<_>>();
        let complete_surface = qualified_names.iter().cloned().collect::<BTreeSet<_>>();
        assert_eq!(
            complete_surface.len(),
            qualified_names.len(),
            "the four normative public allowlists must be mutually disjoint"
        );
        assert_eq!(
            complete_surface,
            TS13_DEMO_COMPLETE_CLEAR_PUBLIC_SURFACE
                .into_iter()
                .map(str::to_owned)
                .collect::<BTreeSet<_>>(),
            "the four normative allowlists must be the complete clear public surface"
        );
    }

    #[test]
    fn ts13_private_witness_schema_is_exact() {
        let witness = Ts13DemoWitnessV1 {
            document: vec![0xa0],
            revocation_id_lo: 1,
            revocation_id_hi: 3,
            revocation_signature: vec![7],
        };
        let Ts13DemoWitnessV1 {
            document: _,
            revocation_id_lo: _,
            revocation_id_hi: _,
            revocation_signature: _,
        } = witness;
    }

    #[test]
    fn ffi_byte_arrays_validate_into_fixed_internal_fields() {
        let statement = sample_ts13_statement();
        let validated = ValidatedTs13DemoPublicStatementV1::try_from(&statement).unwrap();
        let ValidatedTs13DemoPublicStatementV1 {
            circuit_hash,
            zk_system_id: _,
            document_type: _,
            namespace: _,
            element_identifier: _,
            expected_value_cbor: _,
            timestamp_epoch_seconds: _,
            session_transcript: _,
            trusted_issuer_public_key,
            revocation_public_key,
            revocation_epoch: _,
        } = validated;
        assert_eq!(circuit_hash, [0x11; 32]);
        assert_eq!(trusted_issuer_public_key, [0x22; 1_952]);
        assert_eq!(revocation_public_key, [0x33; 1_952]);

        let assert_invalid_length = |statement: Ts13DemoPublicStatementV1| {
            assert_eq!(
                ValidatedTs13DemoPublicStatementV1::try_from(&statement),
                Err(Ts13DemoError::InvalidPublicContext)
            );
        };
        let mut invalid = sample_ts13_statement();
        invalid.circuit_hash.pop();
        assert_invalid_length(invalid);
        let mut invalid = sample_ts13_statement();
        invalid.circuit_hash.push(0);
        assert_invalid_length(invalid);
        let mut invalid = sample_ts13_statement();
        invalid.trusted_issuer_public_key.pop();
        assert_invalid_length(invalid);
        let mut invalid = sample_ts13_statement();
        invalid.revocation_public_key.push(0);
        assert_invalid_length(invalid);
    }

    #[test]
    fn semantic_statement_derives_context_without_caller_supplied_echoes() {
        let derived = sample_ts13_statement().derive_public_context().unwrap();
        assert_eq!(
            derived.verification_timestamp_rfc3339_utc,
            *b"2025-01-01T00:00:00Z"
        );
        assert_eq!(
            derived.request_context_digest,
            [
                0xc9, 0xec, 0x6e, 0xb1, 0x38, 0xda, 0x43, 0xf3, 0xf2, 0x78, 0x00, 0x0d, 0x9b, 0x8a,
                0x4a, 0xb9, 0x18, 0x89, 0x04, 0xef, 0x53, 0xc1, 0x2f, 0x1d, 0xf5, 0x03, 0xbc, 0xd9,
                0x72, 0xa0, 0x4f, 0xc4,
            ]
        );

        let mut malformed = sample_ts13_statement();
        malformed.session_transcript.push(0);
        assert_eq!(
            malformed.derive_public_context(),
            Err(Ts13DemoError::MalformedSessionTranscript)
        );
    }

    #[test]
    fn ts13_derived_context_typed_state_is_exact() {
        let derived = sample_ts13_statement().derive_public_context().unwrap();
        let eu_id_prover::ts13_demo::Ts13DemoDerivedContext {
            canonical_session_transcript: _,
            device_authentication_bytes: _,
            device_cose_sig_structure: _,
            verification_timestamp_rfc3339_utc: _,
            canonical_context_cbor: _,
            request_context_digest: _,
        } = derived;
        assert_eq!(
            TS13_DEMO_DERIVED_CONTEXT_STATE_FIELD_NAMES,
            [
                "canonical_session_transcript",
                "device_authentication_bytes",
                "device_cose_sig_structure",
                "verification_timestamp_rfc3339_utc",
                "canonical_context_cbor",
                "request_context_digest",
            ]
        );
    }

    #[test]
    fn ts13_circuit_public_schema_is_exact() {
        let input = eu_id_prover::MdocTs13DemoCircuitPublicInput {
            circuit_hash: [0x11; 32],
            request_context_digest: [0x22; 32],
            timestamp_epoch_seconds: 1_735_689_600,
            verification_timestamp_rfc3339_utc: *b"2025-01-01T00:00:00Z",
            trusted_issuer_public_key: vec![0x33; 1_952],
            device_cose_sig_structure: vec![0x44; 64],
            revocation: eu_id_prover::mdoc::MdocRevocationPublicInputs {
                revocation_public_key: eu_id_prover::mdoc::MdocRevocationKey::MlDsa(vec![
                    0x55;
                    1_952
                ]),
                epoch: 7,
            },
        };
        let eu_id_prover::MdocTs13DemoCircuitPublicInput {
            circuit_hash: _,
            request_context_digest: _,
            timestamp_epoch_seconds: _,
            verification_timestamp_rfc3339_utc: _,
            trusted_issuer_public_key: _,
            device_cose_sig_structure: _,
            revocation,
        } = input;
        let eu_id_prover::mdoc::MdocRevocationPublicInputs {
            revocation_public_key: _,
            epoch: _,
        } = revocation;
        assert_eq!(
            TS13_DEMO_CIRCUIT_PUBLIC_FIELD_NAMES,
            [
                "circuit_hash",
                "request_context_digest",
                "timestamp_epoch_seconds",
                "verification_timestamp_rfc3339_utc",
                "trusted_issuer_public_key",
                "device_cose_sig_structure",
                "revocation",
            ]
        );
        assert_eq!(
            TS13_DEMO_REVOCATION_PUBLIC_FIELD_NAMES,
            ["revocation_public_key", "epoch"]
        );
    }

    #[test]
    fn every_mutable_public_context_field_changes_the_digest() {
        let baseline = sample_ts13_statement();
        let baseline_digest = baseline
            .derive_public_context()
            .unwrap()
            .request_context_digest;
        let assert_changes = |changed: Ts13DemoPublicStatementV1| {
            assert_ne!(
                changed
                    .derive_public_context()
                    .unwrap()
                    .request_context_digest,
                baseline_digest
            );
        };

        let mut changed = baseline.clone();
        changed.circuit_hash[0] ^= 1;
        assert_changes(changed);
        let mut changed = baseline.clone();
        changed.zk_system_id.push_str("-other");
        assert_changes(changed);
        let mut changed = baseline.clone();
        changed.timestamp_epoch_seconds += 1;
        assert_changes(changed);
        let mut changed = baseline.clone();
        changed.session_transcript = vec![0x83, 0xf6, 0xf6, 0x81, 0x02];
        assert_changes(changed);
        let mut changed = baseline.clone();
        changed.trusted_issuer_public_key[0] ^= 1;
        assert_changes(changed);
        let mut changed = baseline.clone();
        changed.revocation_public_key[0] ^= 1;
        assert_changes(changed);
        let mut changed = baseline.clone();
        changed.revocation_epoch += 1;
        assert_changes(changed);

        let assert_invalid = |invalid: Ts13DemoPublicStatementV1| {
            assert_eq!(
                invalid.derive_public_context(),
                Err(Ts13DemoError::InvalidPublicContext)
            );
        };
        let mut invalid = baseline.clone();
        invalid.document_type.push_str("-other");
        assert_invalid(invalid);
        let mut invalid = baseline.clone();
        invalid.namespace.push_str("-other");
        assert_invalid(invalid);
        let mut invalid = baseline.clone();
        invalid.element_identifier.push_str("-other");
        assert_invalid(invalid);
        let mut invalid = baseline;
        invalid.expected_value_cbor = vec![0xf4];
        assert_invalid(invalid);
    }

    #[test]
    fn mixed_tagged_variants_reject_before_proving() {
        let product_statement = ZkPublicStatement::ProductV1(ProductPublicStatementV1 {
            spec_id: "stwo-euid-pid-v1".to_string(),
            version: 1,
            doctype: "eu.europa.ec.eudi.pid.1".to_string(),
            namespace: "eu.europa.ec.eudi.pid.1".to_string(),
            issuer_key: IssuerKey::MlDsa {
                pk_hash: vec![0; 32],
            },
            today_epoch_day: 20_637,
            nonce: vec![1],
            predicate_mode: PredicateMode::Age,
            age_threshold_years: Some(18),
            accepted_numeric_countries: None,
            nat_mode: NatMode::Any,
        });
        let ts13_statement = ZkPublicStatement::Ts13DemoV1(sample_ts13_statement());
        let product_witness = ZkMdocWitness::ProductV1(ProductMdocWitnessV1 {
            document: vec![0xa0],
            trusted_issuers: TrustedIssuers::PublicKeys(Vec::new()),
        });
        let ts13_witness = ZkMdocWitness::Ts13DemoV1(Ts13DemoWitnessV1 {
            document: vec![0xa0],
            revocation_id_lo: 1,
            revocation_id_hi: 3,
            revocation_signature: vec![7],
        });

        assert_eq!(
            validate_variant_pair(&product_statement, &product_witness),
            Ok(())
        );
        assert_eq!(
            validate_variant_pair(&ts13_statement, &ts13_witness),
            Ok(())
        );
        assert_eq!(
            validate_variant_pair(&product_statement, &ts13_witness),
            Err(Ts13DemoError::UnsupportedProofSystem)
        );
        assert_eq!(
            validate_variant_pair(&ts13_statement, &product_witness),
            Err(Ts13DemoError::UnsupportedProofSystem)
        );
    }

    #[test]
    fn v4_round_trip_has_exact_header_and_fixed_length() {
        let proof = DemoProof {
            claims: vec![1, 2, 3],
            transcript: vec![9, 8, 7],
        };
        let envelope = encode_v4(parameters(), &proof).unwrap();
        assert_eq!(envelope.len(), 46 + CAPACITY as usize);
        assert_eq!(&envelope[..8], b"EUIDTS13");
        assert_eq!(&envelope[8..10], &4u16.to_le_bytes());
        assert_eq!(&envelope[10..42], &[0x11; 32]);
        assert_eq!(&envelope[42..46], &CAPACITY.to_le_bytes());
        assert_eq!(
            TS13_DEMO_V4_HEADER_FIELD_NAMES,
            ["magic", "envelope_version", "circuit_hash", "body_capacity"]
        );
        assert_eq!(
            decode_v4(parameters(), &envelope, |proof: &DemoProof| {
                proof.claims.len() == 3
            }),
            Ok(proof)
        );
    }

    #[test]
    fn v4_body_codec_is_fixed_int_little_endian() {
        let proof = DemoProof {
            claims: vec![0x0102_0304],
            transcript: vec![0xaa],
        };
        let envelope = encode_v4(parameters(), &proof).unwrap();
        let expected_prefix = [
            1, 0, 0, 0, 0, 0, 0, 0, // claims vector length (u64)
            4, 3, 2, 1, // claims[0] (u32)
            1, 0, 0, 0, 0, 0, 0, 0, // transcript vector length (u64)
            0xaa,
        ];
        assert_eq!(
            &envelope[V4_HEADER_BYTES..V4_HEADER_BYTES + expected_prefix.len()],
            &expected_prefix
        );
        assert!(envelope[V4_HEADER_BYTES + expected_prefix.len()..]
            .iter()
            .all(|byte| *byte == 0));

        let varint_prefix = bincode::DefaultOptions::new()
            .with_varint_encoding()
            .with_little_endian()
            .serialize(&proof)
            .unwrap();
        let mut varint_envelope = vec![0; V4_HEADER_BYTES + CAPACITY as usize];
        varint_envelope[..V4_HEADER_BYTES].copy_from_slice(&envelope[..V4_HEADER_BYTES]);
        varint_envelope[V4_HEADER_BYTES..V4_HEADER_BYTES + varint_prefix.len()]
            .copy_from_slice(&varint_prefix);
        assert_eq!(
            decode_v4(parameters(), &varint_envelope, |_: &DemoProof| true),
            Err(Ts13DemoError::MalformedProofEnvelope)
        );
    }

    #[test]
    fn v4_rejects_every_malformed_clear_surface_and_tail() {
        let proof = DemoProof {
            claims: vec![1, 2, 3],
            transcript: vec![9, 8, 7],
        };
        let valid = encode_v4(parameters(), &proof).unwrap();
        let reject = |envelope: &[u8]| {
            decode_v4(parameters(), envelope, |_: &DemoProof| true)
                .map(|_| ())
                .unwrap_err()
        };

        let mut wrong_magic = valid.clone();
        wrong_magic[0] ^= 1;
        assert_eq!(reject(&wrong_magic), Ts13DemoError::MalformedProofEnvelope);

        let mut wrong_version = valid.clone();
        wrong_version[8..10].copy_from_slice(&3u16.to_le_bytes());
        assert_eq!(
            reject(&wrong_version),
            Ts13DemoError::MalformedProofEnvelope
        );

        let mut wrong_hash = valid.clone();
        wrong_hash[10] ^= 1;
        assert_eq!(reject(&wrong_hash), Ts13DemoError::UnsupportedCircuitHash);

        let mut wrong_capacity = valid.clone();
        wrong_capacity[42..46].copy_from_slice(&(CAPACITY * 2).to_le_bytes());
        assert_eq!(
            reject(&wrong_capacity),
            Ts13DemoError::MalformedProofEnvelope
        );

        let mut truncated = valid.clone();
        truncated.pop();
        assert_eq!(reject(&truncated), Ts13DemoError::MalformedProofEnvelope);

        let mut trailing = valid.clone();
        trailing.push(0);
        assert_eq!(reject(&trailing), Ts13DemoError::MalformedProofEnvelope);

        let mut nonzero_padding = valid;
        *nonzero_padding.last_mut().unwrap() = 1;
        assert_eq!(
            reject(&nonzero_padding),
            Ts13DemoError::MalformedProofEnvelope
        );

        let legacy_v3 = bincode::serialize(&3u16).unwrap();
        assert_eq!(reject(&legacy_v3), Ts13DemoError::MalformedProofEnvelope);
    }

    #[test]
    fn unknown_hash_rejects_before_body_decode() {
        let mut envelope = vec![0xff; 46 + CAPACITY as usize];
        envelope[..8].copy_from_slice(b"EUIDTS13");
        envelope[8..10].copy_from_slice(&4u16.to_le_bytes());
        envelope[10..42].copy_from_slice(&[0x99; 32]);
        envelope[42..46].copy_from_slice(&CAPACITY.to_le_bytes());
        assert_eq!(
            decode_v4(parameters(), &envelope, |_: &DemoProof| true),
            Err(Ts13DemoError::UnsupportedCircuitHash)
        );
    }

    #[test]
    fn v4_rejects_noncanonical_prefix_and_wrong_artifact_shape() {
        let mut noncanonical = encode_v4(parameters(), &CanonicalByte).unwrap();
        noncanonical[V4_HEADER_BYTES] = 1;
        assert_eq!(
            decode_v4(parameters(), &noncanonical, |_: &CanonicalByte| true),
            Err(Ts13DemoError::MalformedProofEnvelope)
        );

        let proof = DemoProof {
            claims: vec![1, 2, 3],
            transcript: vec![9, 8, 7],
        };
        let envelope = encode_v4(parameters(), &proof).unwrap();
        assert_eq!(
            decode_v4(parameters(), &envelope, |_: &DemoProof| false),
            Err(Ts13DemoError::MalformedProofEnvelope)
        );
    }

    #[test]
    fn v4_capacity_is_artifact_injected_and_bounded() {
        assert_eq!(
            Ts13DemoV4Parameters::new([0; 32], 0),
            Err(Ts13DemoError::InvalidPublicContext)
        );
        assert_eq!(
            Ts13DemoV4Parameters::new([0; 32], CAPACITY + 1),
            Err(Ts13DemoError::InvalidPublicContext)
        );

        let oversized = vec![0u8; CAPACITY as usize + 1];
        assert_eq!(
            encode_v4(parameters(), &oversized),
            Err(Ts13DemoError::ProofGenerationFailed)
        );
    }

    #[test]
    fn typed_errors_never_format_private_values() {
        let forbidden = [
            "private-mso-sentinel",
            "revocation-endpoint-sentinel",
            "signature-sentinel",
        ];
        for error in [
            Ts13DemoError::UnsupportedProofSystem,
            Ts13DemoError::UnsupportedCircuitHash,
            Ts13DemoError::UnsupportedDemoCredentialShape,
            Ts13DemoError::MalformedSessionTranscript,
            Ts13DemoError::InvalidPublicContext,
            Ts13DemoError::InvalidPrivateCredential,
            Ts13DemoError::InvalidRevocationWitness,
            Ts13DemoError::ProofGenerationFailed,
            Ts13DemoError::MalformedProofEnvelope,
            Ts13DemoError::ProofContextMismatch,
            Ts13DemoError::ProofVerificationFailed,
        ] {
            let message = error.to_string();
            assert!(forbidden.iter().all(|sentinel| !message.contains(sentinel)));
        }
    }

    #[test]
    fn fixed_credential_shape_error_survives_the_public_boundary() {
        assert_eq!(
            map_core_prove_error(eu_id_prover::Error::UnsupportedDemoCredentialShape),
            Ts13DemoError::UnsupportedDemoCredentialShape
        );
    }
}
