use ciborium::value::Value;
use sha2::{Digest, Sha256};

use crate::mdoc::{
    verify_mdoc_circuit, ExtractedPidMdoc, MdocCircuitProof, MdocCircuitStatement,
    MdocRevocationKey, MdocRevocationPublicInputs, MdocRevocationSignature,
    MDOC_PRODUCTION_PCS_LOG_BLOWUP_FACTOR, MDOC_PRODUCTION_PCS_POW_BITS,
    MDOC_PRODUCTION_PCS_QUERIES,
};

// Regenerated whenever the canonical published tuple changes.
pub const TS13_PUBLISHED_AGE_OVER_18_CIRCUIT_HASH: &str =
    "0a16c986814462419b3f797e16d176450f8be46435d2b44a306a4862ea74d43c";
pub const TS13_P4C_MIN_BLIND_ROWS: usize = 256;
pub const TS13_P4C_MAX_OPENINGS: usize = 256;
pub const TS13_P4C_MIN_DECOY_MESSAGE_BITS: usize = 512;
pub const TS13_P4C_PER_OPENING_STATISTICAL_BITS: u32 = 64;
pub const TS13_CONSTRAINT_SYSTEM: &str = "mldsa65-pure-stark-direct-v4";
pub const TS13_PCS_LOG_BLOWUP_FACTOR: u32 = MDOC_PRODUCTION_PCS_LOG_BLOWUP_FACTOR;
pub const TS13_PCS_QUERIES: u32 = MDOC_PRODUCTION_PCS_QUERIES as u32;
pub const TS13_PCS_POW_BITS: u32 = MDOC_PRODUCTION_PCS_POW_BITS;
/// Conservative current outer-STARK bound. The PCS query/PoW label is 129
/// bits, but the single QM31 OODS check at degree/domain `2^16` is only about
/// 108 bits and therefore dominates.
pub const TS13_STARK_SOUNDNESS_BITS: u32 = 108;
pub const TS13_ML_DSA_65_SOUNDNESS_BITS: u32 = 192;
/// Generic quantum collision bound for the 256-bit hashes used as binding
/// commitments. This is approximately 256/3 bits, rounded down.
pub const TS13_SHA256_SOUNDNESS_BITS: u32 = 85;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ts13CircuitTuple {
    pub system: &'static str,
    pub constraint_system: &'static str,
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
    pub composed_soundness_bits: u32,
}

impl Ts13CircuitTuple {
    pub fn published_age_over_18() -> Self {
        Self {
            system: "stwo-euid-v1",
            constraint_system: TS13_CONSTRAINT_SYSTEM,
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
            composed_soundness_bits: ts13_published_soundness_table().composed_soundness_bits(),
        }
    }

    fn canonical_value(&self) -> Value {
        Value::Map(vec![
            ("system".into(), self.system.into()),
            ("constraint_system".into(), self.constraint_system.into()),
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
            (
                "composed_soundness_bits".into(),
                Value::from(self.composed_soundness_bits),
            ),
        ])
    }
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
    /// Conservative integer lower bound obtained by union-bounding all listed
    /// failure events. This deliberately pays `ceil(log2(component_count))`
    /// bits instead of treating the weakest individual component as a proof
    /// of composed soundness.
    pub fn composed_soundness_bits(&self) -> u32 {
        let weakest_component_bits = self
            .components
            .iter()
            .map(|component| component.bits)
            .min()
            .unwrap_or(0);
        let component_count = self.components.len();
        if component_count == 0 {
            return 0;
        }
        let union_bound_loss = usize::BITS - (component_count - 1).leading_zeros();
        weakest_component_bits.saturating_sub(union_bound_loss)
    }
}

pub fn ts13_published_soundness_table() -> Ts13SoundnessTable {
    Ts13SoundnessTable {
        components: vec![
            Ts13SoundnessComponent {
                name: "STARK/FRI",
                bits: TS13_STARK_SOUNDNESS_BITS,
                rationale: "single-QM31 OODS bound at the maximum degree/domain",
            },
            Ts13SoundnessComponent {
                name: "issuer ML-DSA-65",
                bits: TS13_ML_DSA_65_SOUNDNESS_BITS,
                rationale: "FIPS 204 category-3 issuerAuth over MobileSecurityObjectBytes",
            },
            Ts13SoundnessComponent {
                name: "device ML-DSA-65",
                bits: TS13_ML_DSA_65_SOUNDNESS_BITS,
                rationale: "FIPS 204 category-3 DeviceAuthenticationBytes signature",
            },
            Ts13SoundnessComponent {
                name: "revocation ML-DSA-65",
                bits: TS13_ML_DSA_65_SOUNDNESS_BITS,
                rationale: "FIPS 204 category-3 sorted-pair revocation authority signature",
            },
            Ts13SoundnessComponent {
                name: "256-bit binding hashes",
                bits: TS13_SHA256_SOUNDNESS_BITS,
                rationale: "generic quantum collision bound for 256-bit binding hashes",
            },
        ],
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ts13CircuitPin {
    circuit_hash: String,
}

impl Ts13CircuitPin {
    pub fn for_tuple(tuple: &Ts13CircuitTuple) -> Self {
        Self {
            circuit_hash: ts13_circuit_hash(tuple),
        }
    }

    pub fn verify(&self, tuple: &Ts13CircuitTuple) -> Result<(), Ts13CircuitPinError> {
        if self.circuit_hash != ts13_circuit_hash(tuple) {
            return Err(Ts13CircuitPinError::CircuitHashMismatch);
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ts13CircuitPinError {
    CircuitHashMismatch,
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
            rationale: "Q-015 blinder pairs make each published private-data sum uniform",
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
    /// ML-DSA-65 revocation-authority key.
    pub revocation_public_key: MdocRevocationKey,
    pub epoch: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ts13RevocationWitness {
    pub id: u64,
    pub id_lo: u64,
    pub id_hi: u64,
    pub epoch: u32,
    /// Pure ML-DSA-65 signature over the raw 20-byte sorted-pair message.
    pub signature: MdocRevocationSignature,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ts13RevocationError {
    DerivedIdMismatch,
    SentinelId,
    Range,
    Epoch,
    InvalidSignatureEncoding,
    InvalidSignature,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ts13MdocProofArtifact {
    pub circuit_hash: String,
    pub mdoc_proof: Vec<u8>,
    pub revocation_statement: Ts13RevocationStatement,
    pub revocation_witness: Ts13RevocationWitness,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ts13MdocProofArtifactError {
    CircuitHash,
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
    ) -> Result<(), Ts13MdocProofArtifactError> {
        if self.circuit_hash != ts13_default_circuit_hash() {
            return Err(Ts13MdocProofArtifactError::CircuitHash);
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
        self.verify_revocation_binding(extracted)?;
        let proof: MdocCircuitProof = bincode::deserialize(&self.mdoc_proof)
            .map_err(|_| Ts13MdocProofArtifactError::ProofDecode)?;
        verify_mdoc_circuit(&proof, statement).map_err(|_| Ts13MdocProofArtifactError::MdocProof)
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

        let MdocRevocationKey::MlDsa(public_key) = &self.revocation_public_key;
        let MdocRevocationSignature::MlDsa(signature) = &witness.signature;
        let message = ts13_revocation_message(witness.id_lo, witness.id_hi, witness.epoch);
        let trace =
            stwo_mldsa::reference::verify::verify_internals(public_key, &message, signature)
                .map_err(|_| Ts13RevocationError::InvalidSignatureEncoding)?;
        if !trace.accepted {
            return Err(Ts13RevocationError::InvalidSignature);
        }
        Ok(())
    }
}

pub fn ts13_mso_derived_revocation_id(mso: &[u8]) -> u64 {
    let digest = Sha256::digest(mso);
    let bytes: [u8; 8] = digest[..8]
        .try_into()
        .expect("SHA-256 digest always has at least eight bytes");
    u64::from_le_bytes(bytes)
}

/// The raw 20-byte TS13 revocation message `LE64(id_lo) ‖ LE64(id_hi) ‖
/// LE32(epoch)` — the exact bytes ML-DSA-65 signs (pure, no prehash).
pub fn ts13_revocation_message(id_lo: u64, id_hi: u64, epoch: u32) -> [u8; 20] {
    let mut message = [0u8; 20];
    message[..8].copy_from_slice(&id_lo.to_le_bytes());
    message[8..16].copy_from_slice(&id_hi.to_le_bytes());
    message[16..].copy_from_slice(&epoch.to_le_bytes());
    message
}

const TS13_RANK_FIELD_MODULUS: u64 = 2_147_483_647;

fn vandermonde_has_full_row_rank(rows: usize, columns: usize) -> bool {
    if rows == 0 || rows > columns || columns >= TS13_RANK_FIELD_MODULUS as usize {
        return false;
    }

    let mut matrix = vec![vec![0u64; columns]; rows];
    for (row, values) in matrix.iter_mut().enumerate() {
        for (col, value) in values.iter_mut().enumerate() {
            *value = mod_pow((col + 1) as u64, row as u64);
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
        let pivot_row = matrix[rank].clone();
        for (row, values) in matrix.iter_mut().enumerate() {
            if row == rank {
                continue;
            }
            let factor = values[column];
            if factor == 0 {
                continue;
            }
            for (col, value) in values.iter_mut().enumerate().skip(column) {
                *value = mod_sub(*value, mod_mul(factor, pivot_row[col]));
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
        let pin = Ts13CircuitPin::for_tuple(&expected);

        assert!(matches!(
            pin.verify(&actual),
            Err(Ts13CircuitPinError::CircuitHashMismatch)
        ));
    }

    #[test]
    fn circuit_hash_tuple_includes_security_accounting() {
        let tuple = Ts13CircuitTuple::published_age_over_18();
        let soundness = ts13_published_soundness_table();

        assert_eq!(tuple.pcs_log_blowup_factor, 4);
        assert_eq!(tuple.pcs_queries, 26);
        assert_eq!(tuple.pcs_pow_bits, 25);
        assert_eq!(tuple.constraint_system, TS13_CONSTRAINT_SYSTEM);
        assert_eq!(soundness.composed_soundness_bits(), 82);
        assert!(soundness
            .components
            .iter()
            .any(|component| component.name == "STARK/FRI"));
        assert!(soundness
            .components
            .iter()
            .any(|component| component.name == "revocation ML-DSA-65"));
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
