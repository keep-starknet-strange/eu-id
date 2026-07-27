use ciborium::value::Value;
use ecdsa::signature::hazmat::PrehashVerifier;
use p256::ecdsa::{Signature as P256Signature, VerifyingKey};
use p256::EncodedPoint;
use sha2::{Digest, Sha256};
use stwo::core::vcs::blake2_hash::Blake2sHash;
use stwo_p256::types::{AffinePoint, Signature};

use crate::mdoc::{
    verify_mdoc_circuit_with_preprocessed_root, ExtractedPidMdoc, MdocCircuitProof,
    MdocCircuitStatement, MdocRevocationPublicInputs,
};

// Published identifiers pin the default `ec-coprocessor` circuit composition.
// The no-default backend is not a published TS13 profile and canonical artifact
// verification there fails closed. Regenerated 2026-07-27 for circuit revision
// 6: the mdoc scope's DFA edge table moves to its own narrow component at the
// edge-count height, letting the semantic walk run at its natural byte-count
// height (masked table claimed sum joins the cyclic claim-mask ring).
// Old hashes:
// 5445c650a6f57d6b...0d4f21e6 (revision 1); a43f41e4745a053a...a3232591
// (revision 2, SHA field exposure from constrained W bit planes 2026-07-13);
// d09852c1343dcf59...2b84fc96 (revision 3, split-pack deletion 2026-07-21);
// b1f58a97cbcffc1b...04252bf3 (revision 4, terminal Range8 checks 2026-07-24);
// 8fbe779f33710584...f386886f (revision 5, in-circuit CBOR scope 2026-07-24).
pub const TS13_PUBLISHED_AGE_OVER_18_CIRCUIT_HASH: &str =
    "ad2f48128677588d08c67fc742cadeeabaceef1f8d33bb38d33045d47a266557";
// Regenerated 2026-07-27 for revision 6. Value is the real
// `commitments[0]` of the published N=1 revocation-enabled age_over_18 mdoc
// proof (captured via ts13_evidence_pack_n1_measurements). Old values:
// 3532fa24129acba9...8583169f (Class-D blinding repin 2026-07-08);
// ba943f9deed4cf5e...55e8a8b7 (P4b coprocessor revocation reroute 2026-07-08);
// bc8ad8a2f9440f66...2a9babcf (split-pack deletion 2026-07-21);
// ea5754a08fdd9ca9...6b7d3c7c (revision 4, terminal Range8 checks 2026-07-24);
// d824fce24daae4c6...7d2e7bae (revision 5, in-circuit CBOR scope 2026-07-24).
// See tasks/p4c-leakage-table.md.
pub const TS13_PUBLISHED_AGE_OVER_18_PREPROCESSED_ROOT: &[u8; 32] =
    b"\xf0\x7c\xc4\x55\xfa\xda\x60\x38\x21\xf3\x9a\x68\x4c\xaa\xdd\xf2\xc4\x40\xb5\xcc\x64\xc4\x34\x0b\x0a\x2a\xdf\x88\x65\x47\x9a\xb9";
pub const TS13_P4C_MIN_BLIND_ROWS: usize = 256;
pub const TS13_P4C_MAX_OPENINGS: usize = 256;
pub const TS13_P4C_MIN_DECOY_MESSAGE_BITS: usize = 512;
pub const TS13_P4C_PER_OPENING_STATISTICAL_BITS: u32 = 64;
pub const TS13_CIRCUIT_REVISION: u32 = 6;
pub const TS13_PCS_LOG_BLOWUP_FACTOR: u32 = 2;
pub const TS13_PCS_QUERIES: u32 = 54;
pub const TS13_PCS_POW_BITS: u32 = 20;
pub const TS13_PCS_FOLD_STEP: u32 = 3;
pub const TS13_STARK_SOUNDNESS_BITS: u32 =
    TS13_PCS_POW_BITS + TS13_PCS_LOG_BLOWUP_FACTOR * TS13_PCS_QUERIES;
pub const TS13_P256_SOUNDNESS_BITS: u32 = 128;
pub const TS13_SHA256_SOUNDNESS_BITS: u32 = 128;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ts13FixedTableFingerprint {
    pub name: &'static str,
    pub digest: [u8; 32],
    pub rationale: &'static str,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ts13CircuitTuple {
    pub system: &'static str,
    pub circuit_revision: u32,
    pub credential_format: &'static str,
    pub doctype: &'static str,
    pub namespace: &'static str,
    pub num_attributes: u32,
    pub max_mdoc_bytes: u32,
    pub max_attribute_bytes: u32,
    pub potential_issuers: u32,
    pub revocation_enabled: bool,
    pub revocation_id_width_bytes: u32,
    pub device_auth_profile: &'static str,
    pub pcs_log_blowup_factor: u32,
    pub pcs_queries: u32,
    pub pcs_pow_bits: u32,
    pub pcs_fold_step: u32,
    pub fixed_table_fingerprints: Vec<Ts13FixedTableFingerprint>,
    pub preprocessed_root: [u8; 32],
    pub composed_soundness_bits: u32,
}

impl Ts13CircuitTuple {
    pub fn published_age_over_18() -> Self {
        Self {
            system: "stwo-euid-v1",
            circuit_revision: TS13_CIRCUIT_REVISION,
            credential_format: "mso_mdoc_zk",
            doctype: "eu.europa.ec.eudi.pid.1",
            namespace: "eu.europa.ec.eudi.pid.1",
            num_attributes: 1,
            max_mdoc_bytes: 16_384,
            max_attribute_bytes: 32,
            potential_issuers: 1,
            revocation_enabled: true,
            revocation_id_width_bytes: 8,
            device_auth_profile: "iso18013-5",
            pcs_log_blowup_factor: TS13_PCS_LOG_BLOWUP_FACTOR,
            pcs_queries: TS13_PCS_QUERIES,
            pcs_pow_bits: TS13_PCS_POW_BITS,
            pcs_fold_step: TS13_PCS_FOLD_STEP,
            fixed_table_fingerprints: ts13_published_fixed_table_fingerprints(),
            preprocessed_root: *TS13_PUBLISHED_AGE_OVER_18_PREPROCESSED_ROOT,
            composed_soundness_bits: ts13_published_soundness_table().composed_soundness_bits(),
        }
    }

    fn canonical_value(&self) -> Value {
        Value::Map(vec![
            ("system".into(), self.system.into()),
            (
                "circuit_revision".into(),
                Value::from(self.circuit_revision),
            ),
            ("credential_format".into(), self.credential_format.into()),
            ("doctype".into(), self.doctype.into()),
            ("namespace".into(), self.namespace.into()),
            ("num_attributes".into(), Value::from(self.num_attributes)),
            ("max_mdoc_bytes".into(), Value::from(self.max_mdoc_bytes)),
            (
                "max_attribute_bytes".into(),
                Value::from(self.max_attribute_bytes),
            ),
            (
                "potential_issuers".into(),
                Value::from(self.potential_issuers),
            ),
            (
                "revocation_enabled".into(),
                Value::Bool(self.revocation_enabled),
            ),
            (
                "revocation_id_width_bytes".into(),
                Value::from(self.revocation_id_width_bytes),
            ),
            (
                "device_auth_profile".into(),
                self.device_auth_profile.into(),
            ),
            (
                "pcs_log_blowup_factor".into(),
                Value::from(self.pcs_log_blowup_factor),
            ),
            ("pcs_queries".into(), Value::from(self.pcs_queries)),
            ("pcs_pow_bits".into(), Value::from(self.pcs_pow_bits)),
            ("pcs_fold_step".into(), Value::from(self.pcs_fold_step)),
            (
                "fixed_table_fingerprints".into(),
                Value::Array(
                    self.fixed_table_fingerprints
                        .iter()
                        .map(|fingerprint| {
                            Value::Map(vec![
                                ("name".into(), fingerprint.name.into()),
                                ("digest".into(), Value::Bytes(fingerprint.digest.to_vec())),
                                ("rationale".into(), fingerprint.rationale.into()),
                            ])
                        })
                        .collect(),
                ),
            ),
            (
                "preprocessed_root".into(),
                Value::Bytes(self.preprocessed_root.to_vec()),
            ),
            (
                "composed_soundness_bits".into(),
                Value::from(self.composed_soundness_bits),
            ),
        ])
    }
}

pub fn ts13_published_fixed_table_fingerprints() -> Vec<Ts13FixedTableFingerprint> {
    vec![Ts13FixedTableFingerprint {
        name: "mdoc_preprocessed_tree",
        digest: *TS13_PUBLISHED_AGE_OVER_18_PREPROCESSED_ROOT,
        rationale: "tree-0 preprocessed commitment root for the published TS13 age_over_18 tuple",
    }]
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ts13SoundnessComponent {
    pub name: &'static str,
    pub bits: u32,
    pub rationale: &'static str,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ts13SoundnessTable {
    pub components: Vec<Ts13SoundnessComponent>,
}

impl Ts13SoundnessTable {
    pub fn composed_soundness_bits(&self) -> u32 {
        self.components
            .iter()
            .map(|component| component.bits)
            .min()
            .unwrap_or(0)
    }
}

pub fn ts13_published_soundness_table() -> Ts13SoundnessTable {
    Ts13SoundnessTable {
        components: vec![
            Ts13SoundnessComponent {
                name: "STARK/FRI",
                bits: TS13_STARK_SOUNDNESS_BITS,
                rationale: "mdoc production PCS: pow_bits + log_blowup_factor * n_queries",
            },
            Ts13SoundnessComponent {
                name: "issuer P-256",
                bits: TS13_P256_SOUNDNESS_BITS,
                rationale: "ES256 issuerAuth over MobileSecurityObjectBytes",
            },
            Ts13SoundnessComponent {
                name: "device P-256",
                bits: TS13_P256_SOUNDNESS_BITS,
                rationale: "ISO DeviceAuthenticationBytes signature",
            },
            Ts13SoundnessComponent {
                name: "revocation P-256",
                bits: TS13_P256_SOUNDNESS_BITS,
                rationale: "sorted-pair revocation authority signature",
            },
            Ts13SoundnessComponent {
                name: "SHA-256 bindings",
                bits: TS13_SHA256_SOUNDNESS_BITS,
                rationale: "MSO, item digest, and revocation-message hash bindings",
            },
        ],
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ts13CircuitPin {
    circuit_hash: String,
    preprocessed_root: [u8; 32],
}

impl Ts13CircuitPin {
    pub fn for_tuple(tuple: &Ts13CircuitTuple, preprocessed_root: [u8; 32]) -> Self {
        Self {
            circuit_hash: ts13_circuit_hash(tuple),
            preprocessed_root,
        }
    }

    pub fn verify(
        &self,
        tuple: &Ts13CircuitTuple,
        preprocessed_root: [u8; 32],
    ) -> Result<(), Ts13CircuitPinError> {
        if self.circuit_hash != ts13_circuit_hash(tuple) {
            return Err(Ts13CircuitPinError::CircuitHashMismatch);
        }
        if self.preprocessed_root != preprocessed_root {
            return Err(Ts13CircuitPinError::PreprocessedRootMismatch);
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ts13CircuitPinError {
    CircuitHashMismatch,
    PreprocessedRootMismatch,
}

pub fn ts13_circuit_hash(tuple: &Ts13CircuitTuple) -> String {
    hex_sha256(&ts13_circuit_tuple_cbor(tuple))
}

pub fn ts13_circuit_tuple_cbor(tuple: &Ts13CircuitTuple) -> Vec<u8> {
    let mut bytes = Vec::new();
    ciborium::ser::into_writer(&tuple.canonical_value(), &mut bytes)
        .expect("CBOR serialization of TS13 circuit tuple is infallible");
    bytes
}

pub fn ts13_default_circuit_tuple_cbor() -> Vec<u8> {
    ts13_circuit_tuple_cbor(&Ts13CircuitTuple::published_age_over_18())
}

fn hex_sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

pub fn ts13_default_circuit_hash() -> String {
    ts13_circuit_hash(&Ts13CircuitTuple::published_age_over_18())
}

pub fn ts13_default_preprocessed_root() -> [u8; 32] {
    *TS13_PUBLISHED_AGE_OVER_18_PREPROCESSED_ROOT
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ts13ZkExposureClassification {
    PublicByDesign,
    PerfectlyMasked,
    StatisticallyMasked,
    RejectedAtTs13Entry,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ts13ZkExposure {
    pub name: &'static str,
    pub classification: Ts13ZkExposureClassification,
    pub rationale: &'static str,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ts13P4cNumericalBound {
    pub independent_decoy_bits: usize,
    pub per_opening_statistical_bits: u32,
    pub max_openings: usize,
    pub union_bound_bits: u32,
}

pub fn ts13_mdoc_zk_exposure_inventory() -> Vec<Ts13ZkExposure> {
    use Ts13ZkExposureClassification::*;

    vec![
        Ts13ZkExposure {
            name: "doctype",
            classification: PublicByDesign,
            rationale: "caller-bound TS13 request field",
        },
        Ts13ZkExposure {
            name: "namespace",
            classification: PublicByDesign,
            rationale: "caller-bound TS13 request field",
        },
        Ts13ZkExposure {
            name: "age_over_18 equality value",
            classification: PublicByDesign,
            rationale: "requested disclosed equality attribute",
        },
        Ts13ZkExposure {
            name: "policy current date",
            classification: PublicByDesign,
            rationale: "caller-bound verifier policy input",
        },
        Ts13ZkExposure {
            name: "session-bound device authentication digest",
            classification: PublicByDesign,
            rationale: "public verifier transcript binding",
        },
        Ts13ZkExposure {
            name: "issuer public key",
            classification: PublicByDesign,
            rationale: "baseline TS13 tuple uses public issuer trust policy",
        },
        Ts13ZkExposure {
            name: "revocation public key and epoch",
            classification: PublicByDesign,
            rationale: "caller-bound revocation statement",
        },
        Ts13ZkExposure {
            name: "revocation ECDSA message hash and signature",
            classification: PerfectlyMasked,
            rationale: "private coprocessor witness rejoined to the authenticated revocation \
                        digest through the fixed-width P4b MAC; only the revocation key and \
                        epoch remain caller-bound public inputs",
        },
        Ts13ZkExposure {
            name: "longfellow-libzk-v1 proof bytes",
            classification: RejectedAtTs13Entry,
            rationale: "that system id denotes Google libzk proofs, not stwo-euid-v1",
        },
        Ts13ZkExposure {
            name: "zk-jwt request format",
            classification: RejectedAtTs13Entry,
            rationale: "unsupported until an SD-JWT tuple is implemented",
        },
        Ts13ZkExposure {
            name: "Class-A blind cells",
            classification: PerfectlyMasked,
            rationale: "field-free blind cells are masked when P4c selector/pin drops are active",
        },
        Ts13ZkExposure {
            name: "Class-D dummy-key multiplicities",
            classification: PerfectlyMasked,
            rationale: "reserved-key blind region with cancelling LogUp pairs under P4c",
        },
        Ts13ZkExposure {
            name: "LogUp claimed sums",
            classification: PerfectlyMasked,
            rationale: "fresh committed per-component masks have private cyclic targets whose \
                        total is zero; a nonzero post-commitment challenge masks every private \
                        sum without serializing the masks",
        },
        Ts13ZkExposure {
            name: "SHA w/a/e decoy bit columns",
            classification: StatisticallyMasked,
            rationale: "fresh decoy SHA message bits drive the Case-2 character-sum bound",
        },
    ]
}

pub fn ts13_p4c_numerical_bound() -> Ts13P4cNumericalBound {
    let union_bound_loss = TS13_P4C_MAX_OPENINGS.ilog2();
    Ts13P4cNumericalBound {
        independent_decoy_bits: TS13_P4C_MIN_DECOY_MESSAGE_BITS,
        per_opening_statistical_bits: TS13_P4C_PER_OPENING_STATISTICAL_BITS,
        max_openings: TS13_P4C_MAX_OPENINGS,
        union_bound_bits: TS13_P4C_PER_OPENING_STATISTICAL_BITS - union_bound_loss,
    }
}

pub fn ts13_p4c_circle_code_rank_check() -> bool {
    vandermonde_has_full_row_rank(TS13_P4C_MAX_OPENINGS, TS13_P4C_MIN_BLIND_ROWS)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ts13RevocationStatement {
    pub revocation_public_key: AffinePoint,
    pub epoch: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ts13RevocationWitness {
    pub id: u64,
    pub id_lo: u64,
    pub id_hi: u64,
    pub epoch: u32,
    pub signature: Signature,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ts13RevocationError {
    DerivedIdMismatch,
    SentinelId,
    Range,
    Epoch,
    InvalidPublicKey,
    InvalidSignatureEncoding,
    InvalidSignature,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ts13MdocProofArtifact {
    pub circuit_hash: String,
    pub preprocessed_root: [u8; 32],
    pub mdoc_proof: Vec<u8>,
    pub revocation_statement: Ts13RevocationStatement,
    pub revocation_witness: Ts13RevocationWitness,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ts13MdocProofArtifactError {
    CircuitHash,
    PreprocessedRoot,
    EmptyProof,
    StatementRevocationMissing,
    StatementRevocationMismatch,
    ProofDecode,
    MdocProof,
    Revocation(Ts13RevocationError),
}

impl Ts13MdocProofArtifact {
    pub fn verify_revocation_binding(
        &self,
        extracted: &ExtractedPidMdoc,
        expected_preprocessed_root: [u8; 32],
    ) -> Result<(), Ts13MdocProofArtifactError> {
        if self.circuit_hash != ts13_default_circuit_hash() {
            return Err(Ts13MdocProofArtifactError::CircuitHash);
        }
        if self.preprocessed_root != expected_preprocessed_root {
            return Err(Ts13MdocProofArtifactError::PreprocessedRoot);
        }
        if self.mdoc_proof.is_empty() {
            return Err(Ts13MdocProofArtifactError::EmptyProof);
        }
        self.revocation_statement
            .verify_witness(extracted, &self.revocation_witness)
            .map_err(Ts13MdocProofArtifactError::Revocation)
    }

    pub fn verify_mdoc_and_revocation(
        &self,
        extracted: &ExtractedPidMdoc,
        statement: &MdocCircuitStatement,
    ) -> Result<(), Ts13MdocProofArtifactError> {
        self.verify_statement_revocation_binding(statement)?;
        let expected_preprocessed_root = ts13_default_preprocessed_root();
        self.verify_revocation_binding(extracted, expected_preprocessed_root)?;
        let proof: MdocCircuitProof = bincode::deserialize(&self.mdoc_proof)
            .map_err(|_| Ts13MdocProofArtifactError::ProofDecode)?;
        verify_mdoc_circuit_with_preprocessed_root(
            &proof,
            statement,
            Blake2sHash(expected_preprocessed_root),
        )
        .map_err(|_| Ts13MdocProofArtifactError::MdocProof)
    }

    fn verify_statement_revocation_binding(
        &self,
        statement: &MdocCircuitStatement,
    ) -> Result<(), Ts13MdocProofArtifactError> {
        let Some(public_inputs) = &statement.ts13_revocation else {
            return Err(Ts13MdocProofArtifactError::StatementRevocationMissing);
        };
        if public_inputs != &MdocRevocationPublicInputs::from(&self.revocation_statement) {
            return Err(Ts13MdocProofArtifactError::StatementRevocationMismatch);
        }
        let Some(range) = &statement.ts13_revocation_range else {
            return Err(Ts13MdocProofArtifactError::StatementRevocationMismatch);
        };
        if range.id != self.revocation_witness.id
            || range.id_lo != self.revocation_witness.id_lo
            || range.id_hi != self.revocation_witness.id_hi
            || statement.ts13_revocation_signature.as_ref()
                != Some(&self.revocation_witness.signature)
        {
            return Err(Ts13MdocProofArtifactError::StatementRevocationMismatch);
        }
        Ok(())
    }
}

impl From<&Ts13RevocationStatement> for MdocRevocationPublicInputs {
    fn from(statement: &Ts13RevocationStatement) -> Self {
        Self {
            revocation_public_key: statement.revocation_public_key.clone(),
            epoch: statement.epoch,
        }
    }
}

impl Ts13RevocationStatement {
    pub fn verify_witness(
        &self,
        extracted: &ExtractedPidMdoc,
        witness: &Ts13RevocationWitness,
    ) -> Result<(), Ts13RevocationError> {
        let derived_id = ts13_mso_derived_revocation_id(&extracted.mso);
        if derived_id == 0 || derived_id == u64::MAX {
            return Err(Ts13RevocationError::SentinelId);
        }
        if witness.id != derived_id {
            return Err(Ts13RevocationError::DerivedIdMismatch);
        }
        if !(witness.id_lo < witness.id && witness.id < witness.id_hi) {
            return Err(Ts13RevocationError::Range);
        }
        if witness.epoch != self.epoch {
            return Err(Ts13RevocationError::Epoch);
        }

        let verifying_key = verifying_key_from_affine(&self.revocation_public_key)?;
        let signature = p256_signature_from_stwo(&witness.signature)?;
        let message_hash =
            ts13_revocation_message_hash(witness.id_lo, witness.id_hi, witness.epoch);
        verifying_key
            .verify_prehash(&message_hash, &signature)
            .map_err(|_| Ts13RevocationError::InvalidSignature)
    }
}

pub fn ts13_mso_derived_revocation_id(mso: &[u8]) -> u64 {
    let digest = Sha256::digest(mso);
    let bytes: [u8; 8] = digest[..8]
        .try_into()
        .expect("SHA-256 digest always has at least eight bytes");
    u64::from_le_bytes(bytes)
}

pub fn ts13_revocation_message_hash(id_lo: u64, id_hi: u64, epoch: u32) -> [u8; 32] {
    let mut message = Vec::with_capacity(20);
    message.extend_from_slice(&id_lo.to_le_bytes());
    message.extend_from_slice(&id_hi.to_le_bytes());
    message.extend_from_slice(&epoch.to_le_bytes());
    Sha256::digest(message).into()
}

fn verifying_key_from_affine(
    public_key: &AffinePoint,
) -> Result<VerifyingKey, Ts13RevocationError> {
    let encoded = EncodedPoint::from_affine_coordinates(
        (&public_key.x.0).into(),
        (&public_key.y.0).into(),
        false,
    );
    VerifyingKey::from_encoded_point(&encoded).map_err(|_| Ts13RevocationError::InvalidPublicKey)
}

fn p256_signature_from_stwo(signature: &Signature) -> Result<P256Signature, Ts13RevocationError> {
    let mut bytes = Vec::with_capacity(64);
    bytes.extend_from_slice(&signature.r.0);
    bytes.extend_from_slice(&signature.s.0);
    P256Signature::from_slice(&bytes).map_err(|_| Ts13RevocationError::InvalidSignatureEncoding)
}

const TS13_RANK_FIELD_MODULUS: u64 = 2_147_483_647;

fn vandermonde_has_full_row_rank(rows: usize, columns: usize) -> bool {
    if rows == 0 || rows > columns || columns >= TS13_RANK_FIELD_MODULUS as usize {
        return false;
    }

    let mut matrix = vec![vec![0u64; columns]; rows];
    for row in 0..rows {
        for col in 0..columns {
            matrix[row][col] = mod_pow((col + 1) as u64, row as u64);
        }
    }
    rank_mod_prime(matrix) == rows
}

fn rank_mod_prime(mut matrix: Vec<Vec<u64>>) -> usize {
    let row_count = matrix.len();
    let column_count = matrix.first().map_or(0, Vec::len);
    let mut rank = 0;

    for column in 0..column_count {
        let Some(pivot) = (rank..row_count).find(|&row| matrix[row][column] != 0) else {
            continue;
        };
        matrix.swap(rank, pivot);
        let inv = mod_inv(matrix[rank][column]);
        for value in &mut matrix[rank][column..] {
            *value = mod_mul(*value, inv);
        }
        for row in 0..row_count {
            if row == rank {
                continue;
            }
            let factor = matrix[row][column];
            if factor == 0 {
                continue;
            }
            for col in column..column_count {
                matrix[row][col] = mod_sub(matrix[row][col], mod_mul(factor, matrix[rank][col]));
            }
        }
        rank += 1;
        if rank == row_count {
            break;
        }
    }

    rank
}

fn mod_pow(mut base: u64, mut exponent: u64) -> u64 {
    let mut acc = 1;
    while exponent > 0 {
        if exponent & 1 == 1 {
            acc = mod_mul(acc, base);
        }
        base = mod_mul(base, base);
        exponent >>= 1;
    }
    acc
}

fn mod_inv(value: u64) -> u64 {
    mod_pow(value, TS13_RANK_FIELD_MODULUS - 2)
}

fn mod_mul(lhs: u64, rhs: u64) -> u64 {
    ((lhs as u128 * rhs as u128) % TS13_RANK_FIELD_MODULUS as u128) as u64
}

fn mod_sub(lhs: u64, rhs: u64) -> u64 {
    (lhs + TS13_RANK_FIELD_MODULUS - rhs) % TS13_RANK_FIELD_MODULUS
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn circuit_hash_golden_matches_canonical_serialization() {
        let tuple = Ts13CircuitTuple::published_age_over_18();

        assert_eq!(
            ts13_circuit_hash(&tuple),
            TS13_PUBLISHED_AGE_OVER_18_CIRCUIT_HASH
        );
    }

    #[test]
    fn circuit_hash_rejects_cross_tuple_proof() {
        let expected = Ts13CircuitTuple::published_age_over_18();
        let mut actual = expected.clone();
        actual.num_attributes += 1;
        let pin = Ts13CircuitPin::for_tuple(&expected, [7u8; 32]);

        assert!(matches!(
            pin.verify(&actual, [7u8; 32]),
            Err(Ts13CircuitPinError::CircuitHashMismatch)
        ));
    }

    #[test]
    fn circuit_hash_rejects_stale_preprocessed_root() {
        let tuple = Ts13CircuitTuple::published_age_over_18();
        let pin = Ts13CircuitPin::for_tuple(&tuple, [7u8; 32]);

        assert!(matches!(
            pin.verify(&tuple, [8u8; 32]),
            Err(Ts13CircuitPinError::PreprocessedRootMismatch)
        ));
    }

    #[test]
    fn circuit_hash_tuple_includes_security_accounting() {
        let tuple = Ts13CircuitTuple::published_age_over_18();
        let soundness = ts13_published_soundness_table();

        assert_eq!(tuple.circuit_revision, 6);
        assert_eq!(tuple.pcs_log_blowup_factor, 2);
        assert_eq!(tuple.pcs_queries, 54);
        assert_eq!(tuple.pcs_pow_bits, 20);
        assert_eq!(tuple.pcs_fold_step, 3);
        assert_eq!(soundness.composed_soundness_bits(), 128);
        assert!(soundness
            .components
            .iter()
            .any(|component| component.name == "STARK/FRI"));
        assert!(soundness
            .components
            .iter()
            .any(|component| component.name == "revocation P-256"));
    }

    #[test]
    fn circuit_hash_tuple_includes_preprocessed_root() {
        let tuple = Ts13CircuitTuple::published_age_over_18();

        assert_eq!(
            tuple.preprocessed_root,
            *TS13_PUBLISHED_AGE_OVER_18_PREPROCESSED_ROOT
        );
        assert!(ts13_circuit_tuple_cbor(&tuple)
            .windows(TS13_PUBLISHED_AGE_OVER_18_PREPROCESSED_ROOT.len())
            .any(|window| window == TS13_PUBLISHED_AGE_OVER_18_PREPROCESSED_ROOT));
    }

    #[test]
    fn circuit_hash_tuple_includes_fixed_table_fingerprints() {
        let tuple = Ts13CircuitTuple::published_age_over_18();

        assert!(
            tuple
                .fixed_table_fingerprints
                .iter()
                .any(|fingerprint| fingerprint.name == "mdoc_preprocessed_tree"),
            "published tuple must name the fixed table/preprocessed tree fingerprint"
        );
        assert!(ts13_circuit_tuple_cbor(&tuple)
            .windows(b"fixed_table_fingerprints".len())
            .any(|window| window == b"fixed_table_fingerprints"));
    }

    #[test]
    fn circuit_hash_exports_exact_tuple_serialization() {
        let tuple = Ts13CircuitTuple::published_age_over_18();
        let bytes = ts13_circuit_tuple_cbor(&tuple);
        let cbor_hex = bytes
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();

        assert!(!bytes.is_empty(), "tuple serialization must be publishable");
        assert_eq!(hex_sha256(&bytes), TS13_PUBLISHED_AGE_OVER_18_CIRCUIT_HASH);
        assert_eq!(bytes, ts13_default_circuit_tuple_cbor());
        println!("ts13_tuple_cbor_hex={cbor_hex}");
        println!(
            "ts13_circuit_hash={}",
            TS13_PUBLISHED_AGE_OVER_18_CIRCUIT_HASH
        );
    }

    #[test]
    fn mdoc_zk_masking_classification_complete() {
        let inventory = ts13_mdoc_zk_exposure_inventory();

        assert!(!inventory.is_empty(), "TS13 ZK inventory must not be empty");
        assert!(
            inventory
                .iter()
                .any(|entry| entry.classification == Ts13ZkExposureClassification::PublicByDesign),
            "inventory must name public-by-design surfaces"
        );
        assert!(
            inventory
                .iter()
                .any(|entry| entry.classification == Ts13ZkExposureClassification::PerfectlyMasked),
            "inventory must name perfectly masked surfaces"
        );
        assert!(
            inventory
                .iter()
                .any(|entry| entry.classification
                    == Ts13ZkExposureClassification::StatisticallyMasked),
            "inventory must name statistically masked surfaces"
        );
        assert!(
            inventory
                .iter()
                .any(|entry| entry.classification
                    == Ts13ZkExposureClassification::RejectedAtTs13Entry),
            "inventory must name fail-closed TS13 entry-point rejections"
        );
        for entry in inventory {
            assert!(!entry.name.is_empty(), "inventory entry has an empty name");
            assert!(
                !entry.rationale.is_empty(),
                "inventory entry {} has no rationale",
                entry.name
            );
        }
    }

    #[test]
    fn mdoc_zk_circle_code_rank_check() {
        assert!(
            ts13_p4c_circle_code_rank_check(),
            "P4c blind-row opening matrix must have full row rank"
        );
        let bound = ts13_p4c_numerical_bound();
        assert_eq!(bound.independent_decoy_bits, 512);
        assert_eq!(bound.per_opening_statistical_bits, 64);
        assert_eq!(bound.max_openings, 256);
        assert!(
            bound.union_bound_bits >= 40,
            "TS13 tuple union bound must remain above 40 bits; got {}",
            bound.union_bound_bits
        );
    }
}
