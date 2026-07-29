use ciborium::value::Value;
use sha2::{Digest, Sha256};

use crate::mdoc::{
    mdoc_statement_resource_lengths, mdoc_ts13_public_statement_resource_lengths,
    verify_mdoc_ts13_public_statement, ExtractedPidMdoc, MdocCircuitProof, MdocCircuitStatement,
    MdocRevocationKey, MdocRevocationSignature, MdocTs13PublicStatement,
    MDOC_PRODUCTION_PCS_LOG_BLOWUP_FACTOR, MDOC_PRODUCTION_PCS_POW_BITS,
    MDOC_PRODUCTION_PCS_QUERIES,
};

// Regenerated whenever the canonical published tuple changes.
// Repinned for the exact-item CBOR parser/scope and full-padded SHA binding.
pub const TS13_PUBLISHED_AGE_OVER_18_CIRCUIT_HASH: &str =
    "d35d5f25a07a10c9abf96272f81edffa705087f373f4c194a0c250abf2c5d6d6";
pub const TS13_P4C_MIN_BLIND_ROWS: usize = 256;
pub const TS13_P4C_MAX_OPENINGS: usize = 256;
pub const TS13_P4C_MIN_DECOY_MESSAGE_BITS: usize = 512;
pub const TS13_P4C_PER_OPENING_STATISTICAL_BITS: u32 = 64;
pub const TS13_CONSTRAINT_SYSTEM: &str = "mldsa65-pure-stark-direct-v10";
/// The one published equality attribute's canonical IssuerSignedItem is
/// allocated in a three-block SHA slot (256 rows), including padding.
pub const TS13_MAX_ATTRIBUTE_ITEM_BYTES: usize = 183;
/// Published finite range for the credential-stable `IssuerSignedItem.digestID`.
pub const TS13_MAX_REQUESTED_DIGEST_ID: u32 = u16::MAX as u32;
pub const TS13_VALUE_DIGESTS_SCAN_LOG_SIZE: u32 =
    crate::mdoc_value_digests_scan::MDOC_VALUE_DIGESTS_SCAN_LOG_SIZE;
pub const TS13_VALUE_DIGESTS_SCAN_MAX_ITEMS: u32 =
    crate::mdoc_value_digests_scan::MDOC_MAX_VALUE_DIGEST_SCAN_ITEMS as u32;
pub const TS13_VALUE_DIGESTS_SCAN_PREPROCESSED_COLS: u32 =
    crate::mdoc_value_digests_scan::MDOC_VALUE_DIGESTS_SCAN_PREPROCESSED_COLS as u32;
pub const TS13_VALUE_DIGESTS_SCAN_TRACE_COLS: u32 =
    crate::mdoc_value_digests_scan::MDOC_VALUE_DIGESTS_SCAN_TRACE_COLS as u32;
pub const TS13_VALUE_DIGESTS_SCAN_RELATION_SITES: u32 =
    crate::mdoc_value_digests_scan::MDOC_VALUE_DIGESTS_SCAN_RELATION_SITES as u32;
pub const TS13_VALUE_DIGESTS_SCAN_INTERACTION_COLS: u32 =
    crate::mdoc_value_digests_scan::MDOC_VALUE_DIGESTS_SCAN_INTERACTION_COLS as u32;
pub const TS13_COUNTRY_CODE_DATASET: &str = "celes-2.8.2";
pub const TS13_COUNTRY_CODE_TABLE_LOG_SIZE: u32 =
    crate::mdoc_country_code_table::MDOC_COUNTRY_CODE_TABLE_LOG_SIZE;
pub const TS13_COUNTRY_CODE_COUNT: u32 =
    crate::mdoc_country_code_table::MDOC_COUNTRY_CODE_COUNT as u32;
pub const TS13_COUNTRY_CODE_TABLE_PREPROCESSED_COLS: u32 =
    crate::mdoc_country_code_table::MDOC_COUNTRY_CODE_PREPROCESSED_COLS as u32;
pub const TS13_COUNTRY_CODE_TABLE_TRACE_COLS: u32 =
    crate::mdoc_country_code_table::MDOC_COUNTRY_CODE_TRACE_COLS as u32;
pub const TS13_COUNTRY_CODE_TABLE_INTERACTION_COLS: u32 =
    crate::mdoc_country_code_table::MDOC_COUNTRY_CODE_INTERACTION_COLS as u32;
pub const TS13_COUNTRY_CODE_TABLE_SHA256: [u8; 32] =
    crate::mdoc_country_code_table::MDOC_COUNTRY_CODE_TABLE_SHA256;
/// SHA-256-padded size buckets reachable under the 183-byte item cap.
pub const TS13_ALLOWED_REQUESTED_ITEM_PADDED_LENGTHS: [u16; 3] = [64, 128, 192];

pub(crate) fn ts13_requested_digest_id_is_supported(digest_id: u32) -> bool {
    digest_id <= TS13_MAX_REQUESTED_DIGEST_ID
}

pub fn ts13_requested_item_padded_len_is_supported(padded_len: u16) -> bool {
    TS13_ALLOWED_REQUESTED_ITEM_PADDED_LENGTHS.contains(&padded_len)
}
pub const TS13_MERGED_SHA_SLOT_LOG: u32 = 8;
pub const TS13_MERGED_SHA_LOG_N_ROWS: u32 = 8;
/// The signed MSO, not the whole transport document, is the issuer-side
/// resource consumed by the ML-DSA/Keccak statement.
pub const TS13_MAX_MSO_PAYLOAD_BYTES: usize = 4_096;
/// The canonical Signature1 envelope around the MSO is bounded separately
/// because ML-DSA absorbs the full issuer message.
pub const TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES: usize = 4_160;
/// The DeviceAuthentication Sig_structure is also absorbed by ML-DSA.  This
/// cap leaves room for the published session binding without accepting an
/// arbitrary message layout under this circuit pin.
pub const TS13_MAX_DEVICE_MLDSA_MESSAGE_BYTES: usize = 512;
/// Prover-only transport cap. A verifier does not receive the document, so
/// its proof-side analogue is the MSO/item/message contract below.
pub const TS13_MAX_DOCUMENT_BYTES: usize = 16_384;
pub const TS13_PCS_LOG_BLOWUP_FACTOR: u32 = MDOC_PRODUCTION_PCS_LOG_BLOWUP_FACTOR;
pub const TS13_PCS_QUERIES: u32 = MDOC_PRODUCTION_PCS_QUERIES as u32;
pub const TS13_PCS_POW_BITS: u32 = MDOC_PRODUCTION_PCS_POW_BITS;
/// Conservative current outer-STARK bound. The PCS query/PoW label is 128
/// bits (blowup-3 prove-time flip 2026-07-21: 36 queries × 3 + pow 20), but
/// the single QM31 OODS check at degree/domain `2^16` is only about 108 bits
/// and therefore dominates.
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
    pub country_code_dataset: &'static str,
    pub country_code_table_log_size: u32,
    pub country_code_count: u32,
    pub country_code_table_preprocessed_cols: u32,
    pub country_code_table_trace_cols: u32,
    pub country_code_table_interaction_cols: u32,
    pub country_code_table_sha256: [u8; 32],
    pub max_issuer_mldsa_message_bytes: u32,
    pub max_device_mldsa_message_bytes: u32,
    pub merged_sha_slot_log: u32,
    pub merged_sha_log_n_rows: u32,
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
            max_mso_payload_bytes: TS13_MAX_MSO_PAYLOAD_BYTES as u32,
            max_attribute_bytes: 32,
            max_attribute_item_bytes: TS13_MAX_ATTRIBUTE_ITEM_BYTES as u32,
            max_requested_digest_id: TS13_MAX_REQUESTED_DIGEST_ID,
            value_digests_scan_log_size: TS13_VALUE_DIGESTS_SCAN_LOG_SIZE,
            value_digests_scan_max_items: TS13_VALUE_DIGESTS_SCAN_MAX_ITEMS,
            value_digests_scan_preprocessed_cols: TS13_VALUE_DIGESTS_SCAN_PREPROCESSED_COLS,
            value_digests_scan_trace_cols: TS13_VALUE_DIGESTS_SCAN_TRACE_COLS,
            value_digests_scan_relation_sites: TS13_VALUE_DIGESTS_SCAN_RELATION_SITES,
            value_digests_scan_interaction_cols: TS13_VALUE_DIGESTS_SCAN_INTERACTION_COLS,
            country_code_dataset: TS13_COUNTRY_CODE_DATASET,
            country_code_table_log_size: TS13_COUNTRY_CODE_TABLE_LOG_SIZE,
            country_code_count: TS13_COUNTRY_CODE_COUNT,
            country_code_table_preprocessed_cols: TS13_COUNTRY_CODE_TABLE_PREPROCESSED_COLS,
            country_code_table_trace_cols: TS13_COUNTRY_CODE_TABLE_TRACE_COLS,
            country_code_table_interaction_cols: TS13_COUNTRY_CODE_TABLE_INTERACTION_COLS,
            country_code_table_sha256: TS13_COUNTRY_CODE_TABLE_SHA256,
            max_issuer_mldsa_message_bytes: TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES as u32,
            max_device_mldsa_message_bytes: TS13_MAX_DEVICE_MLDSA_MESSAGE_BYTES as u32,
            merged_sha_slot_log: TS13_MERGED_SHA_SLOT_LOG,
            merged_sha_log_n_rows: TS13_MERGED_SHA_LOG_N_ROWS,
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
            (
                "max_mso_payload_bytes".into(),
                Value::from(self.max_mso_payload_bytes),
            ),
            (
                "max_attribute_bytes".into(),
                Value::from(self.max_attribute_bytes),
            ),
            (
                "max_attribute_item_bytes".into(),
                Value::from(self.max_attribute_item_bytes),
            ),
            (
                "max_requested_digest_id".into(),
                Value::from(self.max_requested_digest_id),
            ),
            (
                "value_digests_scan_log_size".into(),
                Value::from(self.value_digests_scan_log_size),
            ),
            (
                "value_digests_scan_max_items".into(),
                Value::from(self.value_digests_scan_max_items),
            ),
            (
                "value_digests_scan_preprocessed_cols".into(),
                Value::from(self.value_digests_scan_preprocessed_cols),
            ),
            (
                "value_digests_scan_trace_cols".into(),
                Value::from(self.value_digests_scan_trace_cols),
            ),
            (
                "value_digests_scan_relation_sites".into(),
                Value::from(self.value_digests_scan_relation_sites),
            ),
            (
                "value_digests_scan_interaction_cols".into(),
                Value::from(self.value_digests_scan_interaction_cols),
            ),
            (
                "country_code_dataset".into(),
                self.country_code_dataset.into(),
            ),
            (
                "country_code_table_log_size".into(),
                Value::from(self.country_code_table_log_size),
            ),
            (
                "country_code_count".into(),
                Value::from(self.country_code_count),
            ),
            (
                "country_code_table_preprocessed_cols".into(),
                Value::from(self.country_code_table_preprocessed_cols),
            ),
            (
                "country_code_table_trace_cols".into(),
                Value::from(self.country_code_table_trace_cols),
            ),
            (
                "country_code_table_interaction_cols".into(),
                Value::from(self.country_code_table_interaction_cols),
            ),
            (
                "country_code_table_sha256".into(),
                Value::Bytes(self.country_code_table_sha256.to_vec()),
            ),
            (
                "max_issuer_mldsa_message_bytes".into(),
                Value::from(self.max_issuer_mldsa_message_bytes),
            ),
            (
                "max_device_mldsa_message_bytes".into(),
                Value::from(self.max_device_mldsa_message_bytes),
            ),
            (
                "merged_sha_slot_log".into(),
                Value::from(self.merged_sha_slot_log),
            ),
            (
                "merged_sha_log_n_rows".into(),
                Value::from(self.merged_sha_log_n_rows),
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
pub enum Ts13MdocVerifierError {
    Statement,
    ResourceCap,
    ProofShape,
    MdocProof,
}

/// Fail-closed verifier for the one published TS13 equality+revocation
/// statement.  All profile and resource checks intentionally happen before
/// the generic verifier constructs tree-0 from proof-controlled layout.
/// `Ok(())` also proves that the private credential validity window contained
/// the verifier-supplied `statement.policy.current_date`; no `valid_today`
/// field, validity date, timestamp, or offset is serialized.
pub fn verify_ts13_age_over_18_circuit(
    proof: &MdocCircuitProof,
    statement: &MdocTs13PublicStatement,
) -> Result<(), Ts13MdocVerifierError> {
    validate_ts13_age_over_18_public_statement(statement)?;
    validate_ts13_age_over_18_proof_shape(proof)?;
    verify_mdoc_ts13_public_statement(proof, statement)
        .map_err(|_| Ts13MdocVerifierError::MdocProof)
}

/// Proving-side resource check. The transport document itself is available
/// only here; verification pins every representation that survives in the
/// statement/proof instead.
pub fn validate_ts13_age_over_18_proving_inputs(
    document: &[u8],
    extracted: &ExtractedPidMdoc,
    statement: &MdocCircuitStatement,
) -> Result<(), Ts13MdocVerifierError> {
    if document.len() > TS13_MAX_DOCUMENT_BYTES
        || extracted.mso.len() > TS13_MAX_MSO_PAYLOAD_BYTES
        || extracted.issuer_sig_structure.len() > TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES
        || extracted.device_sig_structure.len() > TS13_MAX_DEVICE_MLDSA_MESSAGE_BYTES
        || extracted.extracted_attributes.len() != 1
        || extracted.extracted_attributes[0].item.len() > TS13_MAX_ATTRIBUTE_ITEM_BYTES
    {
        return Err(Ts13MdocVerifierError::ResourceCap);
    }
    let actual_item_padded_len = u16::try_from(
        stwo_sha256::native::pad_message(&extracted.extracted_attributes[0].item).len(),
    )
    .map_err(|_| Ts13MdocVerifierError::ResourceCap)?;
    if statement.attributes.len() != 1
        || statement.attributes[0].item_padded_len != actual_item_padded_len
        || !ts13_requested_digest_id_is_supported(extracted.extracted_attributes[0].digest_id)
    {
        return Err(Ts13MdocVerifierError::Statement);
    }
    validate_ts13_age_over_18_proving_statement(statement)
}

fn validate_ts13_age_over_18_proving_statement(
    statement: &MdocCircuitStatement,
) -> Result<(), Ts13MdocVerifierError> {
    if statement.doctype != "eu.europa.ec.eudi.pid.1"
        || statement.namespace != "eu.europa.ec.eudi.pid.1"
        || statement.policy.min_age_years != 0
        || !statement.policy.accepted_nationalities.is_empty()
        || statement.age_attribute_index().is_some()
        || statement.nationality_attribute_index().is_some()
        || statement.attributes.len() != 1
        || statement.attributes[0].element_identifier != "age_over_18"
        || statement.attributes[0].mode
            != crate::mdoc::MdocDisclosureMode::ValueEquality(vec![0xf5])
        || !ts13_requested_item_padded_len_is_supported(statement.attributes[0].item_padded_len)
        || statement.ts13_revocation.is_none()
        || statement.ts13_revocation_signature.is_none()
        || statement.ts13_revocation_range.is_none()
    {
        return Err(Ts13MdocVerifierError::Statement);
    }
    let lengths =
        mdoc_statement_resource_lengths(statement).map_err(|_| Ts13MdocVerifierError::Statement)?;
    if lengths.issuer_mso_payload_bytes > TS13_MAX_MSO_PAYLOAD_BYTES
        || lengths.issuer_message_bytes > TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES
        || lengths.device_message_bytes > TS13_MAX_DEVICE_MLDSA_MESSAGE_BYTES
    {
        return Err(Ts13MdocVerifierError::ResourceCap);
    }
    Ok(())
}

fn validate_ts13_age_over_18_public_statement(
    statement: &MdocTs13PublicStatement,
) -> Result<(), Ts13MdocVerifierError> {
    if statement.doctype != "eu.europa.ec.eudi.pid.1"
        || statement.namespace != "eu.europa.ec.eudi.pid.1"
        || statement.policy.min_age_years != 0
        || !statement.policy.accepted_nationalities.is_empty()
        || statement.attributes.len() != 1
        || statement.attributes[0].element_identifier != "age_over_18"
        || statement.attributes[0].mode
            != crate::mdoc::MdocDisclosureMode::ValueEquality(vec![0xf5])
        || !ts13_requested_item_padded_len_is_supported(statement.requested_item_padded_len)
    {
        return Err(Ts13MdocVerifierError::Statement);
    }
    let lengths = mdoc_ts13_public_statement_resource_lengths(statement)
        .map_err(|_| Ts13MdocVerifierError::Statement)?;
    if lengths.issuer_mso_payload_bytes > TS13_MAX_MSO_PAYLOAD_BYTES
        || lengths.issuer_message_bytes > TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES
        || lengths.device_message_bytes > TS13_MAX_DEVICE_MLDSA_MESSAGE_BYTES
    {
        return Err(Ts13MdocVerifierError::ResourceCap);
    }
    Ok(())
}

fn validate_ts13_age_over_18_proof_shape(
    proof: &MdocCircuitProof,
) -> Result<(), Ts13MdocVerifierError> {
    if proof.merged_sha_layout() != Some((TS13_MERGED_SHA_SLOT_LOG, TS13_MERGED_SHA_LOG_N_ROWS))
        || !proof.has_ts13_mldsa_shape()
    {
        return Err(Ts13MdocVerifierError::ProofShape);
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ts13ZkExposureClassification {
    PublicByDesign,
    /// Public and credential-stable, so repeated presentations are correlatable.
    LinkablePublic,
    /// A private-witness-dependent value is opened without a proof-wide
    /// zero-knowledge polynomial mask.
    UnmaskedPrivateTrace,
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

/// Revocation anonymity note: the public epoch partitions the anonymity set
/// by design. The derived `id`, `id_lo`, `id_hi`, MSO digest, and revocation
/// signature are not clear public statement or transcript inputs. Endpoint
/// indistinguishability remains conditional on Phase-3 proof-wide masking.
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
            name: "issuer Sig_structure and MobileSecurityObject",
            classification: UnmaskedPrivateTrace,
            rationale: "private message provider and MSO binder remove these credential bytes from clear statement/transcript inputs, but Phase 3 proof-wide masking is still absent",
        },
        Ts13ZkExposure {
            name: "device public key",
            classification: LinkablePublic,
            rationale: "ML-DSA verification currently takes the credential-bound device key as a verifier-native public input",
        },
        Ts13ZkExposure {
            name: "requested IssuerSignedItem digestID",
            classification: UnmaskedPrivateTrace,
            rationale: "the private item binder and valueDigests scanner carry the selector only as a private relation tuple; Phase 3 proof-wide masking is still absent",
        },
        Ts13ZkExposure {
            name: "requested IssuerSignedItem padded length",
            classification: LinkablePublic,
            rationale: "the staged verifier publishes the selected item's credential-stable 64-byte SHA-256 size bucket",
        },
        Ts13ZkExposure {
            name: "device authentication Sig_structure",
            classification: PublicByDesign,
            rationale: "the message is derived from the caller-bound session transcript and document type",
        },
        Ts13ZkExposure {
            name: "revocation public key and epoch",
            classification: PublicByDesign,
            rationale: "the authority key is caller-bound and the public epoch deliberately partitions the anonymity set",
        },
        Ts13ZkExposure {
            name: "private revocation id, endpoints, MSO digest, and signature",
            classification: UnmaskedPrivateTrace,
            rationale: "absent from clear public statement and transcript inputs; endpoint indistinguishability still depends on Phase-3 proof-wide masking",
        },
        Ts13ZkExposure {
            name: "private base and interaction trace openings",
            classification: UnmaskedPrivateTrace,
            rationale: "the locked STWO PCS serializes private-witness-dependent OODS and FRI openings without proof-wide trace-polynomial blinding; this profile is not zero knowledge",
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
            classification: UnmaskedPrivateTrace,
            rationale: "local blinder pairs cover selected components only; ML-DSA, Keccak, and other published component sums remain witness-dependent",
        },
        Ts13ZkExposure {
            name: "SHA w/a/e decoy bit columns",
            classification: StatisticallyMasked,
            rationale: "fresh decoy SHA message bits drive the Case-2 character-sum bound",
        },
    ]
}

/// The current locked STWO commitment path opens unblinded private trace
/// polynomials. Local blind cells and claimed-sum masks do not provide a
/// proof-wide zero-knowledge simulator.
pub const fn ts13_profile_is_zero_knowledge() -> bool {
    false
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

    const PRE_PACKED_COEFFS_CONSTRAINT_SYSTEM: &str = "mldsa65-pure-stark-direct-v6";

    fn cbor_has_map_key(value: &Value, expected: &str) -> bool {
        match value {
            Value::Map(entries) => entries.iter().any(|(key, value)| {
                matches!(key, Value::Text(key) if key == expected)
                    || cbor_has_map_key(value, expected)
            }),
            Value::Array(values) => values.iter().any(|value| cbor_has_map_key(value, expected)),
            Value::Tag(_, value) => cbor_has_map_key(value, expected),
            _ => false,
        }
    }

    #[test]
    fn circuit_hash_golden_matches_canonical_serialization() {
        let tuple = Ts13CircuitTuple::published_age_over_18();

        assert_eq!(
            ts13_circuit_hash(&tuple),
            TS13_PUBLISHED_AGE_OVER_18_CIRCUIT_HASH
        );
    }

    #[test]
    fn published_tuple_pins_the_equality_resource_layout() {
        let tuple = Ts13CircuitTuple::published_age_over_18();

        assert_eq!(
            tuple.max_mso_payload_bytes as usize,
            TS13_MAX_MSO_PAYLOAD_BYTES
        );
        assert_eq!(
            tuple.max_attribute_item_bytes as usize,
            TS13_MAX_ATTRIBUTE_ITEM_BYTES
        );
        assert_eq!(tuple.max_requested_digest_id, TS13_MAX_REQUESTED_DIGEST_ID);
        assert_eq!(tuple.value_digests_scan_log_size, 9);
        assert_eq!(tuple.value_digests_scan_max_items, 255);
        assert_eq!(tuple.value_digests_scan_preprocessed_cols, 4);
        assert_eq!(tuple.value_digests_scan_trace_cols, 324);
        assert_eq!(tuple.value_digests_scan_relation_sites, 51);
        assert_eq!(tuple.value_digests_scan_interaction_cols, 108);
        assert_eq!(tuple.country_code_dataset, "celes-2.8.2");
        assert_eq!(tuple.country_code_table_log_size, 9);
        assert_eq!(tuple.country_code_count, 250);
        assert_eq!(tuple.country_code_table_preprocessed_cols, 6);
        assert_eq!(tuple.country_code_table_trace_cols, 1);
        assert_eq!(tuple.country_code_table_interaction_cols, 4);
        assert_eq!(
            tuple.country_code_table_sha256,
            TS13_COUNTRY_CODE_TABLE_SHA256
        );
        assert_eq!(tuple.merged_sha_slot_log, TS13_MERGED_SHA_SLOT_LOG);
        assert_eq!(tuple.merged_sha_log_n_rows, TS13_MERGED_SHA_LOG_N_ROWS);
    }

    #[test]
    fn requested_digest_id_is_bounded_by_the_published_contract() {
        assert!(ts13_requested_digest_id_is_supported(0));
        assert!(ts13_requested_digest_id_is_supported(
            TS13_MAX_REQUESTED_DIGEST_ID
        ));
        assert!(!ts13_requested_digest_id_is_supported(
            TS13_MAX_REQUESTED_DIGEST_ID + 1
        ));
    }

    #[test]
    fn requested_item_padded_len_is_bounded_by_the_published_contract() {
        for padded_len in TS13_ALLOWED_REQUESTED_ITEM_PADDED_LENGTHS {
            assert!(ts13_requested_item_padded_len_is_supported(padded_len));
        }
        for padded_len in [0, 63, 65, 127, 129, 191, 193, u16::MAX] {
            assert!(!ts13_requested_item_padded_len_is_supported(padded_len));
        }
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
    fn packed_coeffs_repin_rejects_previous_identity() {
        let current = Ts13CircuitTuple::published_age_over_18();
        let mut previous = current.clone();
        previous.constraint_system = PRE_PACKED_COEFFS_CONSTRAINT_SYSTEM;
        assert_ne!(
            ts13_circuit_hash(&previous),
            ts13_circuit_hash(&current),
            "the constraint-system identity must remain tuple-bound"
        );

        let current_pin = Ts13CircuitPin::for_tuple(&current);
        assert_eq!(
            current_pin.verify(&previous),
            Err(Ts13CircuitPinError::CircuitHashMismatch)
        );
    }

    #[test]
    fn circuit_hash_tuple_includes_security_accounting() {
        let tuple = Ts13CircuitTuple::published_age_over_18();
        let soundness = ts13_published_soundness_table();

        assert_eq!(tuple.pcs_log_blowup_factor, 3);
        assert_eq!(tuple.pcs_queries, 36);
        assert_eq!(tuple.pcs_pow_bits, 20);
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
            !ts13_profile_is_zero_knowledge(),
            "the profile must remain fail-honest until every private trace is polynomial-masked"
        );
        assert!(
            inventory
                .iter()
                .any(|entry| entry.classification == Ts13ZkExposureClassification::PublicByDesign),
            "inventory must name public-by-design surfaces"
        );
        assert!(
            inventory
                .iter()
                .any(|entry| entry.classification == Ts13ZkExposureClassification::LinkablePublic),
            "inventory must name credential-stable public surfaces"
        );
        assert!(
            inventory.iter().any(|entry| {
                entry.classification == Ts13ZkExposureClassification::UnmaskedPrivateTrace
            }),
            "inventory must name the proof-wide zero-knowledge blocker"
        );
        assert!(inventory.iter().any(|entry| {
            entry.name == "requested IssuerSignedItem digestID"
                && entry.classification == Ts13ZkExposureClassification::UnmaskedPrivateTrace
        }));
        assert!(inventory.iter().any(|entry| {
            entry.name == "requested IssuerSignedItem padded length"
                && entry.classification == Ts13ZkExposureClassification::LinkablePublic
        }));
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
    fn mdoc_zk_revocation_inventory_records_the_anonymity_boundary() {
        let inventory = ts13_mdoc_zk_exposure_inventory();

        assert!(inventory.iter().any(|entry| {
            entry.name == "revocation public key and epoch"
                && entry.classification == Ts13ZkExposureClassification::PublicByDesign
        }));
        assert!(inventory.iter().any(|entry| {
            entry.name == "private revocation id, endpoints, MSO digest, and signature"
                && entry.classification == Ts13ZkExposureClassification::UnmaskedPrivateTrace
        }));
    }

    #[test]
    fn ts13_public_statement_exposes_only_public_revocation_inputs() {
        const EPOCH: u32 = 0xface_b00c;
        let revocation_public_key = vec![0xa7; stwo_mldsa::constants::PK_BYTES];
        let auth = crate::mdoc::MdocMlDsaPublicAuthInput {
            public_key: Vec::new(),
            message_len: 0,
            message: Vec::new(),
        };
        let statement = MdocTs13PublicStatement {
            doctype: "eu.europa.ec.eudi.pid.1".to_string(),
            namespace: "eu.europa.ec.eudi.pid.1".to_string(),
            issuer: auth.clone(),
            device: auth,
            revocation: crate::mdoc::MdocRevocationPublicInputs {
                revocation_public_key: MdocRevocationKey::MlDsa(revocation_public_key),
                epoch: EPOCH,
            },
            mso_payload_len: 1,
            requested_item_padded_len: TS13_ALLOWED_REQUESTED_ITEM_PADDED_LENGTHS[0],
            attributes: Vec::new(),
            policy: crate::policy::Policy {
                current_date: predicates::Date {
                    year: 2026,
                    month: 7,
                    day: 29,
                },
                min_age_years: 18,
                accepted_nationalities: Vec::new(),
            },
        };

        let mut encoded = Vec::new();
        ciborium::ser::into_writer(&statement, &mut encoded)
            .expect("TS13 public statement serializes");
        let decoded: Value =
            ciborium::de::from_reader(encoded.as_slice()).expect("TS13 public statement decodes");
        let restored: MdocTs13PublicStatement =
            ciborium::de::from_reader(encoded.as_slice()).expect("TS13 statement round-trips");

        assert_eq!(restored, statement);
        assert_eq!(restored.revocation.epoch, EPOCH);
        assert_eq!(
            restored.revocation.revocation_public_key,
            statement.revocation.revocation_public_key
        );
        for public_key in ["revocation_public_key", "epoch"] {
            assert!(
                cbor_has_map_key(&decoded, public_key),
                "missing clear public revocation input {public_key}"
            );
        }
        for private_key in ["id", "id_lo", "id_hi", "signature", "mso_digest"] {
            assert!(
                !cbor_has_map_key(&decoded, private_key),
                "private revocation input {private_key} leaked into the public statement"
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
