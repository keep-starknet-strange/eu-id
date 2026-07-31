//! TS13 identity types and proof envelope.

use std::io::Cursor;

use bincode::Options;
use serde::de::DeserializeOwned;
use serde::Serialize;

const ENVELOPE_MAGIC: &[u8; 8] = b"EUIDTS13";
const ENVELOPE_VERSION: u16 = 4;
const ENVELOPE_HEADER_BYTES: usize = 46;
const ENVELOPE_CAPACITY_ALIGNMENT: u32 = 65_536;
const PROOF_BODY_CAPACITY: u32 =
    eu_id_prover::ts13_demo_artifact_constants::TS13_DEMO_PROOF_BODY_CAPACITY;

const _: () = assert!(
    PROOF_BODY_CAPACITY != 0 && PROOF_BODY_CAPACITY.is_multiple_of(ENVELOPE_CAPACITY_ALIGNMENT)
);

/// Public values for the TS13 identity proof.
#[derive(uniffi::Record, Clone, Debug, PartialEq, Eq)]
pub struct IdentityStatement {
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

#[derive(Debug, PartialEq, Eq)]
struct FixedPublicFields {
    circuit_hash: [u8; 32],
    trusted_issuer_public_key: [u8; eu_id_prover::ts13_demo::ML_DSA_65_PUBLIC_KEY_BYTES],
    revocation_public_key: [u8; eu_id_prover::ts13_demo::ML_DSA_65_PUBLIC_KEY_BYTES],
}

fn map_context_error(error: eu_id_prover::ts13_demo::Ts13DemoContextError) -> IdentityError {
    match error {
        eu_id_prover::ts13_demo::Ts13DemoContextError::MalformedSessionTranscript => {
            IdentityError::MalformedSessionTranscript
        }
        eu_id_prover::ts13_demo::Ts13DemoContextError::InvalidPublicContext => {
            IdentityError::InvalidPublicContext
        }
    }
}

fn fixed_public_fields(statement: &IdentityStatement) -> Result<FixedPublicFields, IdentityError> {
    Ok(FixedPublicFields {
        circuit_hash: statement
            .circuit_hash
            .as_slice()
            .try_into()
            .map_err(|_| IdentityError::InvalidPublicContext)?,
        trusted_issuer_public_key: statement
            .trusted_issuer_public_key
            .as_slice()
            .try_into()
            .map_err(|_| IdentityError::InvalidPublicContext)?,
        revocation_public_key: statement
            .revocation_public_key
            .as_slice()
            .try_into()
            .map_err(|_| IdentityError::InvalidPublicContext)?,
    })
}

fn derive_public_context(
    statement: &IdentityStatement,
    fixed: &FixedPublicFields,
) -> Result<eu_id_prover::ts13_demo::Ts13DemoDerivedContext, IdentityError> {
    eu_id_prover::ts13_demo::derive_public_context(
        eu_id_prover::ts13_demo::Ts13DemoPublicContextInput {
            circuit_hash: &fixed.circuit_hash,
            zk_system_id: &statement.zk_system_id,
            document_type: &statement.document_type,
            namespace: &statement.namespace,
            element_identifier: &statement.element_identifier,
            expected_value_cbor: &statement.expected_value_cbor,
            timestamp_epoch_seconds: statement.timestamp_epoch_seconds,
            session_transcript: &statement.session_transcript,
            trusted_issuer_public_key: &fixed.trusted_issuer_public_key,
            revocation_public_key: &fixed.revocation_public_key,
            revocation_epoch: statement.revocation_epoch,
        },
    )
    .map_err(map_context_error)
}

impl IdentityStatement {
    #[cfg(test)]
    pub(crate) fn derive_public_context(
        &self,
    ) -> Result<eu_id_prover::ts13_demo::Ts13DemoDerivedContext, IdentityError> {
        derive_public_context(self, &fixed_public_fields(self)?)
    }
}

/// Private values for the TS13 identity proof.
#[derive(uniffi::Record, Clone)]
pub struct IdentityWitness {
    pub document: Vec<u8>,
    pub revocation_id_lo: u64,
    pub revocation_id_hi: u64,
    pub revocation_signature: Vec<u8>,
}

/// Identity-proof errors. These errors do not contain private data.
#[derive(uniffi::Error, Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum IdentityError {
    #[error("unsupported circuit hash")]
    UnsupportedCircuitHash,
    #[error("unsupported credential shape")]
    UnsupportedCredentialShape,
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
    #[error("proof verification failed")]
    ProofVerificationFailed,
}

fn envelope_bincode_options() -> impl Options {
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_little_endian()
        .with_limit(u64::from(PROOF_BODY_CAPACITY))
}

fn encode_envelope(proof: &eu_id_prover::MdocProof) -> Result<Vec<u8>, IdentityError> {
    let prefix = envelope_bincode_options()
        .serialize(proof)
        .map_err(|_| IdentityError::ProofGenerationFailed)?;
    encode_envelope_prefix(&prefix)
}

fn encode_envelope_prefix(prefix: &[u8]) -> Result<Vec<u8>, IdentityError> {
    let capacity = PROOF_BODY_CAPACITY as usize;
    if prefix.len() > capacity {
        return Err(IdentityError::ProofGenerationFailed);
    }
    let total_len = ENVELOPE_HEADER_BYTES
        .checked_add(capacity)
        .ok_or(IdentityError::ProofGenerationFailed)?;
    let mut envelope = vec![0; total_len];
    envelope[..8].copy_from_slice(ENVELOPE_MAGIC);
    envelope[8..10].copy_from_slice(&ENVELOPE_VERSION.to_le_bytes());
    envelope[10..42]
        .copy_from_slice(&eu_id_prover::ts13_demo_artifact_constants::TS13_DEMO_CIRCUIT_HASH);
    envelope[42..46].copy_from_slice(&PROOF_BODY_CAPACITY.to_le_bytes());
    envelope[46..46 + prefix.len()].copy_from_slice(prefix);
    Ok(envelope)
}

fn envelope_body(envelope: &[u8]) -> Result<&[u8], IdentityError> {
    if envelope.len() < ENVELOPE_HEADER_BYTES
        || &envelope[..8] != ENVELOPE_MAGIC
        || u16::from_le_bytes(
            envelope[8..10]
                .try_into()
                .map_err(|_| IdentityError::MalformedProofEnvelope)?,
        ) != ENVELOPE_VERSION
    {
        return Err(IdentityError::MalformedProofEnvelope);
    }

    let encoded_hash: [u8; 32] = envelope[10..42]
        .try_into()
        .map_err(|_| IdentityError::MalformedProofEnvelope)?;
    if encoded_hash != eu_id_prover::ts13_demo_artifact_constants::TS13_DEMO_CIRCUIT_HASH {
        return Err(IdentityError::UnsupportedCircuitHash);
    }

    let encoded_capacity = u32::from_le_bytes(
        envelope[42..46]
            .try_into()
            .map_err(|_| IdentityError::MalformedProofEnvelope)?,
    );
    if encoded_capacity != PROOF_BODY_CAPACITY {
        return Err(IdentityError::MalformedProofEnvelope);
    }
    let expected_len = ENVELOPE_HEADER_BYTES
        .checked_add(encoded_capacity as usize)
        .ok_or(IdentityError::MalformedProofEnvelope)?;
    if envelope.len() != expected_len {
        return Err(IdentityError::MalformedProofEnvelope);
    }
    Ok(&envelope[ENVELOPE_HEADER_BYTES..])
}

fn decode_canonical_body<T>(body: &[u8]) -> Result<T, IdentityError>
where
    T: DeserializeOwned + Serialize,
{
    let mut cursor = Cursor::new(body);
    let value: T = envelope_bincode_options()
        .allow_trailing_bytes()
        .deserialize_from(&mut cursor)
        .map_err(|_| IdentityError::MalformedProofEnvelope)?;
    let consumed = cursor.position() as usize;
    let canonical_prefix = envelope_bincode_options()
        .serialize(&value)
        .map_err(|_| IdentityError::MalformedProofEnvelope)?;
    if consumed != canonical_prefix.len()
        || body.get(..consumed) != Some(canonical_prefix.as_slice())
        || body[consumed..].iter().any(|&byte| byte != 0)
    {
        return Err(IdentityError::MalformedProofEnvelope);
    }
    Ok(value)
}

fn decode_envelope(envelope: &[u8]) -> Result<eu_id_prover::MdocProof, IdentityError> {
    let proof = decode_canonical_body(envelope_body(envelope)?)?;
    if !eu_id_prover::MdocProof::has_ts13_demo_shape(&proof) {
        return Err(IdentityError::MalformedProofEnvelope);
    }
    Ok(proof)
}

fn ensure_supported_circuit_hash(circuit_hash: [u8; 32]) -> Result<(), IdentityError> {
    if circuit_hash != eu_id_prover::ts13_demo_artifact_constants::TS13_DEMO_CIRCUIT_HASH {
        return Err(IdentityError::UnsupportedCircuitHash);
    }
    Ok(())
}

struct PreparedIdentityInput {
    request: eu_id_prover::MdocPidRequest,
    circuit: eu_id_prover::MdocTs13DemoCircuitPublicInput,
}

fn prepare_public_input(
    statement: &IdentityStatement,
) -> Result<PreparedIdentityInput, IdentityError> {
    let fixed = fixed_public_fields(statement)?;
    ensure_supported_circuit_hash(fixed.circuit_hash)?;
    let derived = derive_public_context(statement, &fixed)?;
    eu_id_prover::ts13_demo::ensure_device_cose_sig_structure_capacity(
        &derived.device_cose_sig_structure,
        eu_id_prover::mdoc::TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY as u32,
    )
    .map_err(map_context_error)?;

    let request = eu_id_prover::MdocPidRequest::age_over_18(derived.canonical_session_transcript);
    let circuit = eu_id_prover::MdocTs13DemoCircuitPublicInput {
        circuit_hash: fixed.circuit_hash,
        request_context_digest: derived.request_context_digest,
        timestamp_epoch_seconds: statement.timestamp_epoch_seconds,
        verification_timestamp_rfc3339_utc: derived.verification_timestamp_rfc3339_utc,
        trusted_issuer_public_key: fixed.trusted_issuer_public_key.to_vec(),
        device_cose_sig_structure: derived.device_cose_sig_structure,
        revocation: eu_id_prover::mdoc::MdocRevocationPublicInputs {
            revocation_public_key: eu_id_prover::mdoc::MdocRevocationKey(
                fixed.revocation_public_key.to_vec(),
            ),
            epoch: statement.revocation_epoch,
        },
    };
    Ok(PreparedIdentityInput { request, circuit })
}

fn map_core_prove_error(error: eu_id_prover::Error) -> IdentityError {
    match error {
        eu_id_prover::Error::UnsupportedDemoCredentialShape => {
            IdentityError::UnsupportedCredentialShape
        }
        eu_id_prover::Error::Mdoc(_) => IdentityError::InvalidPrivateCredential,
        _ => IdentityError::ProofGenerationFailed,
    }
}

pub(crate) fn prove_identity_inner(
    statement: &IdentityStatement,
    witness: &IdentityWitness,
) -> Result<Vec<u8>, IdentityError> {
    let prepared = prepare_public_input(statement)?;
    if witness.revocation_id_lo >= witness.revocation_id_hi
        || witness.revocation_signature.len() != eu_id_prover::ts13_demo::ML_DSA_65_SIGNATURE_BYTES
    {
        return Err(IdentityError::InvalidRevocationWitness);
    }
    let proof = eu_id_prover::prove_mdoc_ts13_demo(
        &witness.document,
        &prepared.request,
        &prepared.circuit,
        witness.revocation_id_lo,
        witness.revocation_id_hi,
        eu_id_prover::mdoc::MdocRevocationSignature(witness.revocation_signature.clone()),
    )
    .map_err(map_core_prove_error)?;
    encode_envelope(&proof)
}

pub(crate) fn verify_identity_inner(
    statement: &IdentityStatement,
    envelope: &[u8],
) -> Result<(), IdentityError> {
    let prepared = prepare_public_input(statement)?;
    let proof = decode_envelope(envelope)?;
    eu_id_prover::verify_mdoc_ts13_demo(&proof, &prepared.circuit)
        .map_err(|_| IdentityError::ProofVerificationFailed)
}

#[cfg(test)]
mod tests {
    use serde::{Deserialize, Deserializer, Serializer};

    use super::*;

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

    fn encode_test_envelope<T: Serialize>(value: &T) -> Vec<u8> {
        let prefix = envelope_bincode_options().serialize(value).unwrap();
        encode_envelope_prefix(&prefix).unwrap()
    }

    fn decode_test_envelope<T>(envelope: &[u8]) -> Result<T, IdentityError>
    where
        T: DeserializeOwned + Serialize,
    {
        decode_canonical_body(envelope_body(envelope)?)
    }

    #[test]
    fn compiled_artifact_pins_hash_and_capacity() {
        use eu_id_prover::ts13_demo_artifact_constants::{
            TS13_DEMO_CIRCUIT_HASH, TS13_DEMO_SHAPE_MANIFEST_SHA256,
            TS13_DEMO_SOUNDNESS_SOURCE_TREE_SHA256,
        };

        let expected_hash = TS13_DEMO_CIRCUIT_HASH;
        assert_ne!(
            expected_hash, [0; 32],
            "the compiled artifact must not accept the bootstrap placeholder"
        );
        assert_ne!(TS13_DEMO_SHAPE_MANIFEST_SHA256, [0; 32]);
        assert_ne!(TS13_DEMO_SOUNDNESS_SOURCE_TREE_SHA256, [0; 32]);
        assert_ne!(PROOF_BODY_CAPACITY, 0);
        assert_eq!(PROOF_BODY_CAPACITY % ENVELOPE_CAPACITY_ALIGNMENT, 0);
        ensure_supported_circuit_hash(expected_hash).expect("generated circuit is supported");

        let mut unknown_hash = expected_hash;
        unknown_hash[0] ^= 1;
        assert_eq!(
            ensure_supported_circuit_hash(unknown_hash),
            Err(IdentityError::UnsupportedCircuitHash)
        );
    }

    fn sample_identity_statement() -> IdentityStatement {
        IdentityStatement {
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
        let IdentityStatement {
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
        } = sample_identity_statement();

        let witness = IdentityWitness {
            document: vec![0xa0],
            revocation_id_lo: 1,
            revocation_id_hi: 3,
            revocation_signature: vec![7],
        };
        let IdentityWitness {
            document: _,
            revocation_id_lo: _,
            revocation_id_hi: _,
            revocation_signature: _,
        } = witness;

        let derived = sample_identity_statement().derive_public_context().unwrap();
        let eu_id_prover::ts13_demo::Ts13DemoDerivedContext {
            canonical_session_transcript: _,
            device_authentication_bytes: _,
            device_cose_sig_structure: _,
            verification_timestamp_rfc3339_utc: _,
            canonical_context_cbor: _,
            request_context_digest: _,
        } = derived;

        let circuit_input = eu_id_prover::MdocTs13DemoCircuitPublicInput {
            circuit_hash: [0x11; 32],
            request_context_digest: [0x22; 32],
            timestamp_epoch_seconds: 1_735_689_600,
            verification_timestamp_rfc3339_utc: *b"2025-01-01T00:00:00Z",
            trusted_issuer_public_key: vec![0x33; 1_952],
            device_cose_sig_structure: vec![0x44; 64],
            revocation: eu_id_prover::mdoc::MdocRevocationPublicInputs {
                revocation_public_key: eu_id_prover::mdoc::MdocRevocationKey(vec![0x55; 1_952]),
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
        } = circuit_input;
        let eu_id_prover::mdoc::MdocRevocationPublicInputs {
            revocation_public_key: _,
            epoch: _,
        } = revocation;
    }

    #[test]
    fn ffi_byte_arrays_validate_into_fixed_internal_fields() {
        let statement = sample_identity_statement();
        let fixed = fixed_public_fields(&statement).unwrap();
        let FixedPublicFields {
            circuit_hash,
            trusted_issuer_public_key,
            revocation_public_key,
        } = fixed;
        assert_eq!(circuit_hash, [0x11; 32]);
        assert_eq!(trusted_issuer_public_key, [0x22; 1_952]);
        assert_eq!(revocation_public_key, [0x33; 1_952]);

        let assert_invalid_length = |statement: IdentityStatement| {
            assert_eq!(
                fixed_public_fields(&statement),
                Err(IdentityError::InvalidPublicContext)
            );
        };
        let mut invalid = sample_identity_statement();
        invalid.circuit_hash.pop();
        assert_invalid_length(invalid);
        let mut invalid = sample_identity_statement();
        invalid.circuit_hash.push(0);
        assert_invalid_length(invalid);
        let mut invalid = sample_identity_statement();
        invalid.trusted_issuer_public_key.pop();
        assert_invalid_length(invalid);
        let mut invalid = sample_identity_statement();
        invalid.revocation_public_key.push(0);
        assert_invalid_length(invalid);
    }

    #[test]
    fn semantic_statement_derives_context_without_caller_supplied_echoes() {
        let derived = sample_identity_statement().derive_public_context().unwrap();
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

        let mut malformed = sample_identity_statement();
        malformed.session_transcript.push(0);
        assert_eq!(
            malformed.derive_public_context(),
            Err(IdentityError::MalformedSessionTranscript)
        );
    }

    #[test]
    fn every_mutable_public_context_field_changes_the_digest() {
        let baseline = sample_identity_statement();
        let baseline_digest = baseline
            .derive_public_context()
            .unwrap()
            .request_context_digest;
        let assert_changes = |changed: IdentityStatement| {
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

        let assert_invalid = |invalid: IdentityStatement| {
            assert_eq!(
                invalid.derive_public_context(),
                Err(IdentityError::InvalidPublicContext)
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
    fn envelope_round_trip_has_exact_header_and_fixed_length() {
        let proof = DemoProof {
            claims: vec![1, 2, 3],
            transcript: vec![9, 8, 7],
        };
        let envelope = encode_test_envelope(&proof);
        assert_eq!(
            envelope.len(),
            ENVELOPE_HEADER_BYTES + PROOF_BODY_CAPACITY as usize
        );
        assert_eq!(&envelope[..8], b"EUIDTS13");
        assert_eq!(&envelope[8..10], &4u16.to_le_bytes());
        assert_eq!(
            &envelope[10..42],
            &eu_id_prover::ts13_demo_artifact_constants::TS13_DEMO_CIRCUIT_HASH
        );
        assert_eq!(&envelope[42..46], &PROOF_BODY_CAPACITY.to_le_bytes());
        assert_eq!(decode_test_envelope(&envelope), Ok(proof));
    }

    #[test]
    fn envelope_body_codec_is_fixed_int_little_endian() {
        let proof = DemoProof {
            claims: vec![0x0102_0304],
            transcript: vec![0xaa],
        };
        let envelope = encode_test_envelope(&proof);
        let expected_prefix = [
            1, 0, 0, 0, 0, 0, 0, 0, // claims vector length (u64)
            4, 3, 2, 1, // claims[0] (u32)
            1, 0, 0, 0, 0, 0, 0, 0, // transcript vector length (u64)
            0xaa,
        ];
        assert_eq!(
            &envelope[ENVELOPE_HEADER_BYTES..ENVELOPE_HEADER_BYTES + expected_prefix.len()],
            &expected_prefix
        );
        assert!(envelope[ENVELOPE_HEADER_BYTES + expected_prefix.len()..]
            .iter()
            .all(|byte| *byte == 0));

        let varint_prefix = bincode::DefaultOptions::new()
            .with_varint_encoding()
            .with_little_endian()
            .serialize(&proof)
            .unwrap();
        let mut varint_envelope = vec![0; ENVELOPE_HEADER_BYTES + PROOF_BODY_CAPACITY as usize];
        varint_envelope[..ENVELOPE_HEADER_BYTES]
            .copy_from_slice(&envelope[..ENVELOPE_HEADER_BYTES]);
        varint_envelope[ENVELOPE_HEADER_BYTES..ENVELOPE_HEADER_BYTES + varint_prefix.len()]
            .copy_from_slice(&varint_prefix);
        assert_eq!(
            decode_test_envelope::<DemoProof>(&varint_envelope),
            Err(IdentityError::MalformedProofEnvelope)
        );
    }

    #[test]
    fn envelope_rejects_every_malformed_clear_surface_and_tail() {
        let proof = DemoProof {
            claims: vec![1, 2, 3],
            transcript: vec![9, 8, 7],
        };
        let valid = encode_test_envelope(&proof);
        let reject = |envelope: &[u8]| {
            decode_test_envelope::<DemoProof>(envelope)
                .map(|_| ())
                .unwrap_err()
        };

        let mut wrong_magic = valid.clone();
        wrong_magic[0] ^= 1;
        assert_eq!(reject(&wrong_magic), IdentityError::MalformedProofEnvelope);

        let mut wrong_version = valid.clone();
        wrong_version[8..10].copy_from_slice(&3u16.to_le_bytes());
        assert_eq!(
            reject(&wrong_version),
            IdentityError::MalformedProofEnvelope
        );

        let mut wrong_hash = valid.clone();
        wrong_hash[10] ^= 1;
        assert_eq!(reject(&wrong_hash), IdentityError::UnsupportedCircuitHash);

        let mut wrong_capacity = valid.clone();
        wrong_capacity[42..46]
            .copy_from_slice(&(PROOF_BODY_CAPACITY + ENVELOPE_CAPACITY_ALIGNMENT).to_le_bytes());
        assert_eq!(
            reject(&wrong_capacity),
            IdentityError::MalformedProofEnvelope
        );

        let mut truncated = valid.clone();
        truncated.pop();
        assert_eq!(reject(&truncated), IdentityError::MalformedProofEnvelope);

        let mut trailing = valid.clone();
        trailing.push(0);
        assert_eq!(reject(&trailing), IdentityError::MalformedProofEnvelope);

        let mut nonzero_padding = valid;
        *nonzero_padding.last_mut().unwrap() = 1;
        assert_eq!(
            reject(&nonzero_padding),
            IdentityError::MalformedProofEnvelope
        );

        let invalid_prefix = bincode::serialize(&3u16).unwrap();
        assert_eq!(
            reject(&invalid_prefix),
            IdentityError::MalformedProofEnvelope
        );
    }

    #[test]
    fn unknown_hash_rejects_before_body_decode() {
        let mut envelope = vec![0xff; ENVELOPE_HEADER_BYTES + PROOF_BODY_CAPACITY as usize];
        envelope[..8].copy_from_slice(b"EUIDTS13");
        envelope[8..10].copy_from_slice(&4u16.to_le_bytes());
        envelope[10..42].copy_from_slice(&[0x99; 32]);
        envelope[42..46].copy_from_slice(&PROOF_BODY_CAPACITY.to_le_bytes());
        assert_eq!(
            decode_test_envelope::<DemoProof>(&envelope),
            Err(IdentityError::UnsupportedCircuitHash)
        );
    }

    #[test]
    fn envelope_rejects_noncanonical_prefix() {
        let mut noncanonical = encode_test_envelope(&CanonicalByte);
        noncanonical[ENVELOPE_HEADER_BYTES] = 1;
        assert_eq!(
            decode_test_envelope::<CanonicalByte>(&noncanonical),
            Err(IdentityError::MalformedProofEnvelope)
        );
    }

    #[test]
    fn envelope_rejects_a_body_larger_than_the_artifact_capacity() {
        let oversized = vec![0u8; PROOF_BODY_CAPACITY as usize + 1];
        assert_eq!(
            encode_envelope_prefix(&oversized),
            Err(IdentityError::ProofGenerationFailed)
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
            IdentityError::UnsupportedCircuitHash,
            IdentityError::UnsupportedCredentialShape,
            IdentityError::MalformedSessionTranscript,
            IdentityError::InvalidPublicContext,
            IdentityError::InvalidPrivateCredential,
            IdentityError::InvalidRevocationWitness,
            IdentityError::ProofGenerationFailed,
            IdentityError::MalformedProofEnvelope,
            IdentityError::ProofVerificationFailed,
        ] {
            let message = error.to_string();
            assert!(forbidden.iter().all(|sentinel| !message.contains(sentinel)));
        }
    }

    #[test]
    fn fixed_credential_shape_error_survives_the_public_boundary() {
        assert_eq!(
            map_core_prove_error(eu_id_prover::Error::UnsupportedDemoCredentialShape),
            IdentityError::UnsupportedCredentialShape
        );
    }
}
