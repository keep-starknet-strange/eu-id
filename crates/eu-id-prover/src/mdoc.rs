//! Product EUID PID mdoc proof path.
//!
//! This module parses the constrained ISO/IEC 18013-5 PID profile, prepares the
//! mdoc statement/witness, and proves issuer signature, ISO device
//! authentication, MSO digest membership, validity, device-key origin, and the
//! age/nationality predicates in one verifier-facing proof. The legacy nonce
//! module is not part of this path; the device-auth signature binds freshness.

use std::collections::{HashMap, HashSet, VecDeque};
use std::io::Cursor;
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

use air_core::relations::{
    field_id, DigestBytesRelation, FieldBytesRelation, SharedDigestRelation, SharedFieldRelation,
};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use ciborium::value::Value;
use predicates::nat::NationalityPredicate;
use predicates::{AgeRangeCheck, DateOfBirth, PredicateProver, PredicateVerifier};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use sha2::{Digest as _, Sha256};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{QM31, SECURE_EXTENSION_DEGREE};
use stwo::core::fri::FriConfig;
use stwo::core::pcs::PcsConfig;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof::StarkProof;
use stwo::core::utils::{bit_reverse_index, coset_index_to_circle_domain_index};
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;
use stwo::core::{
    air::Component,
    channel::{Blake2sChannel, Channel},
};
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::{
    preprocessed_columns::PreProcessedColumnId, TraceLocationAllocator,
};
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
};
use stwo_mldsa::binding::SharedT1CellRelation;
use stwo_mldsa::coeffs::relations::SharedRangeRelation;
use stwo_mldsa::coeffs::tables::SharedRangeTable;
use stwo_mldsa::expand_a::{
    derive_expand_a_witness, ExpandABindings, ExpandAClaim, ExpandAProver, ExpandAVerifier,
};
use stwo_mldsa::private_key_eval::PrivateKeyEvalBindings;
use stwo_mldsa::statement::HOSTED_MSG_FIELD_ID;
use stwo_mldsa::statement::{
    keccak_job_shapes, MlDsaProver as MlDsaStatementProver, MlDsaVerifier as MlDsaStatementVerifier,
};
use stwo_mldsa::stwo_keccak::relations::SharedKeccakRelations;
use stwo_mldsa::stwo_keccak::service::{KeccakServiceProver, KeccakServiceVerifier};
use stwo_mldsa::types::{MlDsaPrivateKeyPublicInput, MlDsaVerifyInput};
use stwo_sha256::air::{Sha256Prover, Sha256Verifier};
use stwo_sha256::field_exposure::FieldExposure;
use stwo_sha256::interaction::InteractionClaim as Sha256InteractionClaim;
use stwo_sha256::partitions::MAX_ROUND_GROUP_BITS;
use stwo_sha256::relations::SharedShaTableRelations;
use stwo_sha256::shared_tables::{
    ShaTableMultiplicities, ShaTablesInteractionClaim, ShaTablesProver, ShaTablesVerifier,
};
use stwo_sha256::trace::min_log_size;
use stwo_sha256::witness::compute_sha256_witness;

use crate::claimed_sum_blinder::{
    add_blinder_relation_entry, blinder_counter_interaction, random_qm31, ClaimedSumBlinderEval,
    ClaimedSumBlinderRelation,
};
use crate::mdoc_cbor_stream::{MdocCborInputMode, MdocCborStream, MdocCborStreamInteractionClaim};
use crate::mdoc_country_code_table::{MdocCountryCodeTable, SharedMdocCountryCodeRelation};
use crate::mdoc_private_device_key_bind::{
    MdocPrivateDeviceKeyBind, MdocPrivateDeviceKeyInteractionClaim,
    MDOC_PRIVATE_DEVICE_KEY_ACTIVE_ROWS,
};
use crate::mdoc_private_item_bind::{
    MdocPrivateItemBind, MdocPrivateItemError, MdocPrivateItemFieldIds, MdocPrivateItemHandles,
    MdocPrivateItemInteractionClaim, MdocPrivateItemPrivateInput, MdocPrivateItemProfile,
    MdocPrivateItemRequestMode, MdocPrivateTag24WrapperReason,
};
use crate::mdoc_private_message::{MdocPrivateMessageInteractionClaim, MdocPrivateMessageProvider};
use crate::mdoc_private_mso_bind::{
    MdocPrivateMsoBind, MdocPrivateMsoBindSpec, MdocPrivateMsoBindWitness,
    MdocPrivateMsoDeviceKeyMode, MdocPrivateMsoInteractionClaim, MdocPrivateMsoShaStreamSpec,
    MdocPrivateMsoVersion, SharedMdocDevicePkStartRelation, SharedMdocMsoStartRelation,
};
use crate::mdoc_private_mso_validity::{
    MdocPrivateMsoValidityInteractionClaim, MdocPrivateMsoValiditySpec, MdocPrivateMsoValidityV2,
    SharedMdocMsoValidityBytesRelation,
};
#[cfg(feature = "unlink-spikes")]
use crate::mdoc_unlink_spike::{append_dummy_jobs, append_dummy_shapes, MdocUnlinkSpikeIo};
pub use crate::mdoc_value_digests_scan::MsoValueDigestsCanonicalityReason as MdocMsoValueDigestsCanonicalityReason;
use crate::mdoc_value_digests_scan::{
    MdocValueDigestDisclosure, MdocValueDigestItemHandles, MdocValueDigestsInteractionClaim,
    MdocValueDigestsProfile, MdocValueDigestsScan, MdocValueDigestsScanError,
    MdocValueDigestsScanHandles, MdocValueDigestsScanSpec, MdocValueDigestsScanWitness,
};
use crate::mdoc_window_bind::{MdocWindowBind, MdocWindowBindInteractionClaim, MdocWindowBindRow};
use crate::policy::Policy;
use crate::ts13_demo::{
    Ts13PublicContextBindV1, TS13_DEMO_VERIFICATION_TIMESTAMP_RFC3339_UTC_BYTES,
};
use crate::Error;

/// Legacy profile: `elementValue` packed as a fixed-width CBOR `bstr`.
const MDOC_PROFILE_VERSION_V1: &str = "1.0";
/// Profile v2: canonical (RFC 8949 core deterministic) CBOR, text-form values.
const MDOC_PROFILE_VERSION_V2: &str = "2.0";
/// The profile the demo fixture emits and the parser advertises by default.
const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
/// COSE protected header `{1: -49}` (ML-DSA-65,
/// `stwo_mldsa::constants::COSE_ALG_ML_DSA_65`): CBOR `A1 01 38 30`.
pub(crate) const MLDSA_PROTECTED_HEADER: &[u8] = &[0xA1, 0x01, 0x38, 0x30];
const CBOR_TAG_ENCODED_CBOR: u64 = 24;
const CBOR_TAG_FULL_DATE: u64 = 1004;
const MDOC_ATTRIBUTE_ELEMENT_ID_BASE: u32 = 16;
const MDOC_ATTRIBUTE_VALUE_BASE: u32 = 20;
const MDOC_ATTRIBUTE_ITEM_STREAM_BASE: u32 = 0x4d49_0000;
const MDOC_ATTRIBUTE_ITEM_STREAM_STRIDE: u32 = 2;
const MDOC_MSO_SHA_STREAM_FIELD_ID: u32 = 0x4d53_0000;
const MDOC_MSO_SHA_LOG_SIZE: u32 = 13;
const MDOC_MSO_SHA_NAMESPACE: &str = "mdoc/mso-sha";
const TS13_REVOCATION_MESSAGE_LEN: usize = 20;
/// The largest canonical nationality array accepted by the circuit.  Each
/// member occupies exactly three CBOR bytes (`0x62`/`0x42` plus two code
/// bytes), so this fixed bound keeps the selected-member offset auditable.
const MAX_NATIONALITY_MEMBERS: usize = 8;
/// The verifier keeps only a small working set of canonical tree-0 roots.
/// Entries are populated after a full successful proof verification, so an
/// attacker cannot evict useful policy roots with malformed proofs.
const MDOC_TREE0_ROOT_CACHE_CAPACITY: usize = 16;
/// Per-role instance namespaces for hosted ML-DSA modules. Prover and verifier
/// must agree; the namespace is mixed into the transcript (role/domain
/// separation — a device claim tree cannot be replayed against the revocation
/// slot) and prefixes the witness-dependent preprocessed column ids (so two
/// instances cannot alias each other's SIB schedules under tree-0 dedup).
const MDOC_ISSUER_MLDSA_NAMESPACE: &str = "mdoc/issuer";
const MDOC_DEVICE_MLDSA_NAMESPACE: &str = "mdoc/device";
const MDOC_DEVICE_EXPAND_A_NAMESPACE: &str = "mdoc/ts13/device-expand-a";
const MDOC_REVOCATION_MLDSA_NAMESPACE: &str = "mdoc/ts13/revocation";
/// Per-role HashIo stream-id bases for hosted ML-DSA modules (S1): every
/// instance shares the ONE keccak-service relation set, so stream ids must be
/// globally unique. Prover and verifier must agree per role; each base must be
/// a multiple of [`stwo_mldsa::statement::STREAM_BASE_STRIDE`] (0x100/0x200/
/// 0x300 all are).
const MDOC_ISSUER_MLDSA_STREAM_BASE: u32 = 0x100;
const MDOC_DEVICE_MLDSA_STREAM_BASE: u32 = 0x200;
const MDOC_REVOCATION_MLDSA_STREAM_BASE: u32 = 0x300;
const MDOC_DEVICE_EXPAND_A_STREAM_BASE: u32 = 0x400;
const _: () = assert!(
    MDOC_ISSUER_MLDSA_STREAM_BASE.is_multiple_of(stwo_mldsa::statement::STREAM_BASE_STRIDE)
        && MDOC_DEVICE_MLDSA_STREAM_BASE.is_multiple_of(stwo_mldsa::statement::STREAM_BASE_STRIDE)
        && MDOC_REVOCATION_MLDSA_STREAM_BASE
            .is_multiple_of(stwo_mldsa::statement::STREAM_BASE_STRIDE)
);

/// The frozen TS13 module order lives here once and is expanded for both the
/// prover and verifier. The invocation supplies role-equivalent modules; it
/// does not get to choose their ordering.
macro_rules! collect_ts13_demo_modules {
    (
        $modules:ident;
        sha_tables = $sha_tables:expr,
        range_tables = $range_tables:expr,
        keccak_service = $keccak_service:expr,
        public_context = $public_context:expr,
        issuer_message = $issuer_message:expr,
        issuer_mldsa = $issuer_mldsa:expr,
        item_shas = $item_shas:expr,
        mso_sha = $mso_sha:expr,
        item_parsers = $item_parsers:expr,
        item_binders = $item_binders:expr,
        mso_binder = $mso_binder:expr,
        mso_validity = $mso_validity:expr,
        value_digests = $value_digests:expr,
        expand_a = $expand_a:expr,
        device_key = $device_key:expr,
        device_mldsa = $device_mldsa:expr,
        revocation_range = $revocation_range:expr,
        revocation_mldsa = $revocation_mldsa:expr,
        revocation_public = $revocation_public:expr $(,)?
    ) => {{
        $modules.push($sha_tables); // 1
        $modules.push($range_tables); // 2
        $modules.push($keccak_service); // 3
        $modules.push($public_context); // 4
        $modules.push($issuer_message); // 5
        $modules.push($issuer_mldsa); // 6
        for module in $item_shas {
            $modules.push(module); // 7
        }
        $modules.push($mso_sha); // 8
        for module in $item_parsers {
            $modules.push(module); // 9
        }
        for module in $item_binders {
            $modules.push(module); // 10
        }
        $modules.push($mso_binder); // 11
        $modules.push($mso_validity); // 12
        $modules.push($value_digests); // 13
        $modules.push($expand_a); // 14
        $modules.push($device_key); // 15
        $modules.push($device_mldsa); // 16
        $modules.push($revocation_range); // 17
        $modules.push($revocation_mldsa); // 18
        $modules.push($revocation_public); // 19
    }};
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MdocPidRequest {
    pub doctype: String,
    pub namespace: String,
    pub attributes: Vec<MdocRequestedAttribute>,
    pub birth_date_element: String,
    pub nationality_element: String,
    pub session_transcript: Vec<u8>,
    /// ML-DSA-65 issuer trust pins: FIPS 204 `pkEncode` bytes (1,952 each). An
    /// ML-DSA issuer REQUIRES a non-empty pin list and the header AKP key must
    /// be byte-equal to a member — a self-carried key is never a trust decision
    /// (no PQ PKI profile exists yet, so there is no x5chain equivalent).
    pub trusted_mldsa_issuer_public_keys: Vec<Vec<u8>>,
    pub device_authentication_profile: MdocDeviceAuthenticationProfile,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MdocDeviceAuthenticationProfile {
    Iso180135,
    LongfellowLegacy,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MdocDisclosureMode {
    ValueEquality(Vec<u8>),
    AgeOver,
    Alpha2Set,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocRequestedAttribute {
    pub element_identifier: String,
    pub mode: MdocDisclosureMode,
}

#[derive(Clone, Debug)]
pub struct ExtractedMdocAttribute {
    pub request: MdocRequestedAttribute,
    pub digest_id: u32,
    pub item: Vec<u8>,
    pub element_identifier_offset: usize,
    pub value_offset: usize,
    pub value: Vec<u8>,
}

impl MdocPidRequest {
    pub fn eudi_pid(session_transcript: Vec<u8>) -> Self {
        Self {
            doctype: PID_DOCTYPE.to_string(),
            namespace: PID_NAMESPACE.to_string(),
            attributes: vec![
                MdocRequestedAttribute {
                    element_identifier: "birth_date".to_string(),
                    mode: MdocDisclosureMode::AgeOver,
                },
                MdocRequestedAttribute {
                    element_identifier: "nationality".to_string(),
                    mode: MdocDisclosureMode::Alpha2Set,
                },
            ],
            birth_date_element: "birth_date".to_string(),
            nationality_element: "nationality".to_string(),
            session_transcript,
            trusted_mldsa_issuer_public_keys: Vec::new(),
            device_authentication_profile: MdocDeviceAuthenticationProfile::Iso180135,
        }
    }

    /// See [`MdocPidRequest::trusted_mldsa_issuer_public_keys`].
    pub fn with_trusted_mldsa_issuer_public_keys(mut self, public_keys: Vec<Vec<u8>>) -> Self {
        self.trusted_mldsa_issuer_public_keys = public_keys;
        self
    }

    pub fn with_device_authentication_profile(
        mut self,
        profile: MdocDeviceAuthenticationProfile,
    ) -> Self {
        self.device_authentication_profile = profile;
        self
    }

    pub fn disclosed_attributes(&self) -> Vec<MdocRequestedAttribute> {
        self.attributes.clone()
    }
}

fn validate_attribute_shapes<'a>(
    count: usize,
    attributes: impl Iterator<Item = (&'a str, &'a MdocDisclosureMode)>,
) -> Result<(), MdocError> {
    if !(1..=crate::mdoc_window_bind::MDOC_MAX_DISCLOSED_ATTRIBUTES).contains(&count) {
        return Err(MdocError::InvalidAttributeCount { count });
    }
    let mut age_seen = false;
    let mut alpha2_seen = false;
    for (element_identifier, mode) in attributes {
        match mode {
            MdocDisclosureMode::ValueEquality(bytes) => {
                if bytes.len() > 32 {
                    return Err(MdocError::ValueEqualityTooLong {
                        element: element_identifier.to_string(),
                        len: bytes.len(),
                    });
                }
                if element_identifier.len() > 32 {
                    return Err(MdocError::ElementIdentifierTooLong {
                        element: element_identifier.to_string(),
                        len: element_identifier.len(),
                    });
                }
            }
            MdocDisclosureMode::AgeOver => {
                if element_identifier.len() > 32 {
                    return Err(MdocError::ElementIdentifierTooLong {
                        element: element_identifier.to_string(),
                        len: element_identifier.len(),
                    });
                }
                if std::mem::replace(&mut age_seen, true) {
                    return Err(MdocError::DuplicatePredicateMode("AgeOver"));
                }
            }
            MdocDisclosureMode::Alpha2Set => {
                if element_identifier.len() > 32 {
                    return Err(MdocError::ElementIdentifierTooLong {
                        element: element_identifier.to_string(),
                        len: element_identifier.len(),
                    });
                }
                if std::mem::replace(&mut alpha2_seen, true) {
                    return Err(MdocError::DuplicatePredicateMode("Alpha2Set"));
                }
            }
        }
    }
    Ok(())
}

fn validate_requested_attributes(attributes: &[MdocRequestedAttribute]) -> Result<(), MdocError> {
    validate_attribute_shapes(
        attributes.len(),
        attributes
            .iter()
            .map(|attribute| (attribute.element_identifier.as_str(), &attribute.mode)),
    )
}

/// ML-DSA-65 signature-verification input shared by issuer and device roles.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum MdocAuthInput {
    /// Boxed because an `MlDsaVerifyInput` is roughly 20 KiB inline.
    MlDsa(Box<MlDsaVerifyInput>),
    /// Verifier-side TS13 device input. The device public key and signature
    /// are existential circuit witnesses; only the request-derived message is
    /// verifier input.
    MlDsaPrivateKey(MlDsaPrivateKeyPublicInput),
}

/// The issuer-role view of [`MdocAuthInput`] (historical name, kept as alias).
pub type IssuerAuthInput = MdocAuthInput;
/// The device-role view of [`MdocAuthInput`].
pub type DeviceAuthInput = MdocAuthInput;

impl MdocAuthInput {
    pub fn as_mldsa(&self) -> Option<&MlDsaVerifyInput> {
        match self {
            Self::MlDsa(input) => Some(input.as_ref()),
            Self::MlDsaPrivateKey(_) => None,
        }
    }

    fn private_key_public_input(&self) -> Option<&MlDsaPrivateKeyPublicInput> {
        match self {
            Self::MlDsa(_) => None,
            Self::MlDsaPrivateKey(input) => Some(input),
        }
    }

    fn message(&self) -> &[u8] {
        match self {
            Self::MlDsa(input) => &input.message,
            Self::MlDsaPrivateKey(input) => &input.message,
        }
    }

    /// Whether this is an ML-DSA-65 issuer. Always available (returns `false`
    /// when the `ml-dsa` feature is disabled, since the variant cannot exist) so
    /// digest-handle selection compiles in every feature combination.
    pub fn is_mldsa(&self) -> bool {
        true
    }
}

/// Verifier-visible part of an ML-DSA authentication input.
///
/// The signature witness (`c_tilde`, `z`, and `hint`) is intentionally absent.
/// Verification reconstructs canonical zero placeholders because those fields
/// affect neither public-input mixing nor verifier-side layout/evaluations.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocMlDsaPublicAuthInput {
    /// FIPS 204 `pkEncode` bytes.
    pub public_key: Vec<u8>,
    /// Public resource shape of the role's COSE `Sig_structure`.
    pub message_len: u16,
    /// Device authentication carries its verifier-selected public bytes. The
    /// private issuer role carries an empty vector; `message_len` is enough to
    /// reconstruct its zero placeholder for verifier-side layout.
    pub message: Vec<u8>,
}

impl MdocMlDsaPublicAuthInput {
    fn from_circuit(input: &MdocAuthInput, include_message: bool) -> Result<Self, String> {
        let input = input.as_mldsa().ok_or_else(|| {
            "private-key device input cannot be serialized as a public key".to_string()
        })?;
        let message_len = u16::try_from(input.message.len()).map_err(|_| {
            format!(
                "ML-DSA public message length {} exceeds the wire shape",
                input.message.len()
            )
        })?;
        Ok(Self {
            public_key: input.encode_pk(),
            message_len,
            message: if include_message {
                input.message.clone()
            } else {
                Vec::new()
            },
        })
    }

    fn verifier_input(
        &self,
        role: &'static str,
        include_message: bool,
    ) -> Result<MdocAuthInput, Error> {
        let message_len = usize::from(self.message_len);
        let message = if include_message {
            if self.message.len() != message_len {
                return Err(Error::Verify(format!(
                    "mdoc {role} public message length does not match its shape"
                )));
            }
            self.message.clone()
        } else {
            if !self.message.is_empty() {
                return Err(Error::Verify(format!(
                    "mdoc {role} private message bytes are present in the public statement"
                )));
            }
            vec![0; message_len]
        };
        let decoded_pk = stwo_mldsa::reference::encoding::pk_decode(&self.public_key)
            .map_err(|error| Error::Verify(format!("mdoc {role} public key decode: {error:?}")))?;
        let zero_signature = stwo_mldsa::reference::encoding::SignatureParts {
            c_tilde: [0; stwo_mldsa::constants::C_TILDE_BYTES],
            z: [[0; stwo_mldsa::constants::N]; stwo_mldsa::constants::L],
            h: [[0; stwo_mldsa::constants::N]; stwo_mldsa::constants::K],
        };
        Ok(MdocAuthInput::MlDsa(Box::new(
            MlDsaVerifyInput::from_decoded(&decoded_pk, &zero_signature, [0; 64], message),
        )))
    }
}

fn serialize_private_issuer_auth<S>(input: &MdocAuthInput, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    MdocMlDsaPublicAuthInput::from_circuit(input, false)
        .map_err(serde::ser::Error::custom)?
        .serialize(serializer)
}

fn deserialize_private_issuer_auth<'de, D>(deserializer: D) -> Result<MdocAuthInput, D::Error>
where
    D: Deserializer<'de>,
{
    MdocMlDsaPublicAuthInput::deserialize(deserializer)?
        .verifier_input("issuer", false)
        .map_err(|error| serde::de::Error::custom(format!("{error:?}")))
}

fn serialize_public_device_auth<S>(input: &MdocAuthInput, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    MdocMlDsaPublicAuthInput::from_circuit(input, true)
        .map_err(serde::ser::Error::custom)?
        .serialize(serializer)
}

fn deserialize_public_device_auth<'de, D>(deserializer: D) -> Result<MdocAuthInput, D::Error>
where
    D: Deserializer<'de>,
{
    MdocMlDsaPublicAuthInput::deserialize(deserializer)?
        .verifier_input("device", true)
        .map_err(|error| serde::de::Error::custom(format!("{error:?}")))
}

fn auth_inputs_equal(left: &MdocAuthInput, right: &MdocAuthInput) -> bool {
    match (left, right) {
        (MdocAuthInput::MlDsa(l), MdocAuthInput::MlDsa(r)) => l == r,
        (MdocAuthInput::MlDsaPrivateKey(l), MdocAuthInput::MlDsaPrivateKey(r)) => l == r,
        _ => false,
    }
}

#[derive(Clone, Debug)]
pub struct ExtractedPidMdoc {
    pub doctype: String,
    pub namespace: String,
    pub attributes: Vec<MdocRequestedAttribute>,
    pub extracted_attributes: Vec<ExtractedMdocAttribute>,
    pub birth_date: String,
    pub nationalities: Vec<u32>,
    pub birth_date_bytes: [u8; 4],
    pub nationality_bytes: [u8; 2],
    pub birth_date_binding: MdocBirthDateBinding,
    pub nationality_binding: MdocNationalityBinding,
    pub birth_date_value_offset: usize,
    pub nationality_value_offset: usize,
    /// Canonical nationality-array metadata. `None` is a scalar elementValue;
    /// otherwise the selected member is at `nationality_array_index`.
    pub nationality_array_len: Option<u8>,
    pub nationality_array_index: Option<u8>,
    /// All of the holder's parsed nationality entries (one for a scalar value, N for an array).
    /// The `nationality_*` singles above hold the currently-bound entry (default: the first);
    /// [`select_accepted_nationality`] repoints them at the entry that satisfies the accepted set.
    pub nationality_candidates: Vec<ParsedNationalityValue>,
    pub signed_at: (u16, u8, u8),
    pub valid_from: (u16, u8, u8),
    pub valid_until: (u16, u8, u8),
    pub digest_ids: HashMap<String, u32>,
    pub birth_date_item: Vec<u8>,
    pub nationality_item: Vec<u8>,
    pub mso: Vec<u8>,
    pub issuer_sig_structure: Vec<u8>,
    pub device_sig_structure: Vec<u8>,
    /// The issuer-auth verification input (ECDSA or ML-DSA-65). For an ML-DSA
    /// issuer, `issuer_key`/`issuer_signature` above are zeroed placeholders —
    /// the real key/signature live in this enum's `MlDsa` arm.
    pub issuer_auth_input: IssuerAuthInput,
    /// The device-auth verification input (ECDSA or ML-DSA-65). For an ML-DSA
    /// device, `device_key`/`device_signature` above are zeroed placeholders.
    /// Signature schemes are uniform across roles (fail-closed at extraction):
    /// this arm always matches `issuer_auth_input`'s.
    pub device_auth_input: DeviceAuthInput,
}

/// How the `birth_date` element value is encoded in the item preimage. The
/// window bytes exposed to the age predicate differ per encoding: `Packed`
/// exposes the 4 raw big-endian date bytes; `Text` exposes the 10 ASCII bytes
/// of the canonical `YYYY-MM-DD` tstr (profile v2).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MdocBirthDateBinding {
    Packed([u8; 4]),
    Text([u8; 10]),
}

/// How the `nationality` element value is encoded in the item preimage.
/// `Numeric` exposes the 2 raw big-endian country-code bytes; `Alpha2` exposes
/// the 2 ASCII bytes of the ISO 3166-1 alpha-2 code (profile v2).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MdocNationalityBinding {
    Numeric([u8; 2]),
    Alpha2([u8; 2]),
}

fn nationality_member_bytes(binding: &MdocNationalityBinding) -> [u8; 3] {
    match binding {
        MdocNationalityBinding::Numeric(bytes) => [0x42, bytes[0], bytes[1]],
        MdocNationalityBinding::Alpha2(bytes) => [0x62, bytes[0], bytes[1]],
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MdocError {
    Cbor(String),
    MissingField(&'static str),
    WrongType(&'static str),
    DoctypeMismatch,
    NamespaceMissing,
    ElementMissing(String),
    UnsupportedDigestAlgorithm(String),
    ItemDigestMismatch {
        element: String,
        digest_id: u32,
    },
    DeviceAuthPayloadMismatch,
    InvalidCoseKey(&'static str),
    InvalidCoseSign1(&'static str),
    UntrustedIssuerKey,
    InvalidSignature(&'static str),
    InvalidNationality(String),
    UnsupportedCircuitValue(&'static str),
    UnsupportedMsoVersion(String),
    InvalidTdate(&'static str),
    CredentialNotYetValid,
    CredentialExpired,
    SaltTooShort {
        len: usize,
    },
    InvalidAttributeCount {
        count: usize,
    },
    DuplicatePredicateMode(&'static str),
    ValueEqualityTooLong {
        element: String,
        len: usize,
    },
    ElementIdentifierTooLong {
        element: String,
        len: usize,
    },
    ValueEqualityMismatch {
        element: String,
    },
    IssuerSignedItemNotCanonical {
        offset: usize,
        reason: MdocIssuerSignedItemCanonicalityReason,
    },
    MsoValueDigestsNotCanonical {
        offset: usize,
        reason: MdocMsoValueDigestsCanonicalityReason,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MdocIssuerSignedItemCanonicalityReason {
    EmptyInput,
    TraceTooLarge { bytes: usize },
    InvalidShaPadding(&'static str),
    TruncatedToken { needed: usize },
    InvalidAdditionalInfo { additional: u8 },
    UnsupportedContainerLength { additional: u8 },
    NonMinimalArgument { argument: u64 },
    InvalidSimpleValue { additional: u8 },
    NestingTooDeep,
    MissingContainer,
    TrailingCbor { input_len: usize },
    IncompleteRoot,
    ExpectedTag24,
    ExpectedTag24ByteString,
    ExpectedTag24ByteStringU8Length { additional: u8 },
    Tag24ByteStringLengthMismatch { declared: usize, actual: usize },
}

fn issuer_signed_item_parser_error(
    error: crate::mdoc_cbor_stream::MdocCborStreamError,
    base_offset: usize,
) -> MdocError {
    use crate::mdoc_cbor_stream::MdocCborStreamError as ParserError;
    use MdocIssuerSignedItemCanonicalityReason as Reason;

    let (relative_offset, reason) = match error {
        ParserError::EmptyInput => (0, Reason::EmptyInput),
        ParserError::TraceTooLarge { bytes } => (0, Reason::TraceTooLarge { bytes }),
        ParserError::InvalidShaPadding(reason) => (0, Reason::InvalidShaPadding(reason)),
        ParserError::TruncatedToken { index, needed } => (index, Reason::TruncatedToken { needed }),
        ParserError::InvalidAdditionalInfo { index, additional } => {
            (index, Reason::InvalidAdditionalInfo { additional })
        }
        ParserError::UnsupportedContainerLength { index, additional } => {
            (index, Reason::UnsupportedContainerLength { additional })
        }
        ParserError::NonMinimalArgument { index, argument } => {
            (index, Reason::NonMinimalArgument { argument })
        }
        ParserError::InvalidSimpleValue { index, additional } => {
            (index, Reason::InvalidSimpleValue { additional })
        }
        ParserError::NestingTooDeep { index } => (index, Reason::NestingTooDeep),
        ParserError::MissingContainer { index } => (index, Reason::MissingContainer),
        ParserError::TrailingCbor {
            root_end,
            input_len,
        } => (root_end, Reason::TrailingCbor { input_len }),
        ParserError::IncompleteRoot => (0, Reason::IncompleteRoot),
    };
    MdocError::IssuerSignedItemNotCanonical {
        offset: base_offset + relative_offset,
        reason,
    }
}

fn map_private_item_prove_error(index: usize, error: MdocPrivateItemError) -> Error {
    const TAG24_OUTER_PREFIX_LEN: usize = 4;
    match error {
        MdocPrivateItemError::OuterParser(error) => {
            Error::Mdoc(issuer_signed_item_parser_error(error, 0))
        }
        MdocPrivateItemError::InnerParser(error) => Error::Mdoc(issuer_signed_item_parser_error(
            error,
            TAG24_OUTER_PREFIX_LEN,
        )),
        MdocPrivateItemError::InvalidTag24Wrapper { offset, reason } => {
            let reason = match reason {
                MdocPrivateTag24WrapperReason::TruncatedToken { needed } => {
                    MdocIssuerSignedItemCanonicalityReason::TruncatedToken { needed }
                }
                MdocPrivateTag24WrapperReason::ExpectedTag24 => {
                    MdocIssuerSignedItemCanonicalityReason::ExpectedTag24
                }
                MdocPrivateTag24WrapperReason::ExpectedByteString => {
                    MdocIssuerSignedItemCanonicalityReason::ExpectedTag24ByteString
                }
                MdocPrivateTag24WrapperReason::ExpectedU8ByteStringLength { additional } => {
                    MdocIssuerSignedItemCanonicalityReason::ExpectedTag24ByteStringU8Length {
                        additional,
                    }
                }
                MdocPrivateTag24WrapperReason::ByteStringLengthMismatch { declared, actual } => {
                    MdocIssuerSignedItemCanonicalityReason::Tag24ByteStringLengthMismatch {
                        declared,
                        actual,
                    }
                }
            };
            Error::Mdoc(MdocError::IssuerSignedItemNotCanonical { offset, reason })
        }
        other => Error::Prove(format!("private IssuerSignedItem {index}: {other}")),
    }
}

fn map_value_digests_prove_error(error: MdocValueDigestsScanError) -> Error {
    match error {
        MdocValueDigestsScanError::MsoValueDigestsNotCanonical { offset, reason } => {
            Error::Mdoc(MdocError::MsoValueDigestsNotCanonical { offset, reason })
        }
        other => Error::Prove(format!("private valueDigests scanner: {other}")),
    }
}

/// Parse + natively pre-check an ML-DSA-65 issuerAuth (FIPS 204 Algorithm 3,
/// pure mode, empty context) and build the in-circuit witness. Shared by the
/// `p256` and quantum-only extraction shells.
fn mldsa_issuer_input(
    issuer_unprotected: &[(Value, Value)],
    request: &MdocPidRequest,
    issuer_auth: &CoseSign1,
) -> Result<MlDsaVerifyInput, MdocError> {
    let pk = mldsa_issuer_pk_from_unprotected(issuer_unprotected, request)?;
    let trace = stwo_mldsa::reference::verify::verify_internals(
        &pk,
        &issuer_auth.sig_structure,
        &issuer_auth.signature_bytes,
    )
    .map_err(|_| MdocError::InvalidSignature("issuerAuth"))?;
    if !trace.accepted {
        return Err(MdocError::InvalidSignature("issuerAuth"));
    }
    let decoded_pk = stwo_mldsa::reference::encoding::pk_decode(&pk)
        .map_err(|_| MdocError::InvalidCoseKey("ML-DSA-65 public key"))?;
    let decoded_sig = stwo_mldsa::reference::encoding::sig_decode(&issuer_auth.signature_bytes)
        .map_err(|_| MdocError::InvalidSignature("issuerAuth"))?;
    Ok(MlDsaVerifyInput::from_decoded(
        &decoded_pk,
        &decoded_sig,
        trace.tr,
        issuer_auth.sig_structure.clone(),
    ))
}

/// Mirror of [`mldsa_issuer_input`] for the device role: native FIPS 204
/// pre-check over the device `Sig_structure`, then the decoded in-circuit
/// input. Rejects the mixed ML-DSA-device / ES256-issuer row fail-closed.
fn mldsa_device_auth_input(
    pk: &[u8],
    device_signature: &CoseSign1,
) -> Result<MdocAuthInput, MdocError> {
    let trace = stwo_mldsa::reference::verify::verify_internals(
        pk,
        &device_signature.sig_structure,
        &device_signature.signature_bytes,
    )
    .map_err(|_| MdocError::InvalidSignature("deviceSignature"))?;
    if !trace.accepted {
        return Err(MdocError::InvalidSignature("deviceSignature"));
    }
    let decoded_pk = stwo_mldsa::reference::encoding::pk_decode(pk)
        .map_err(|_| MdocError::InvalidCoseKey("ML-DSA-65 public key"))?;
    let decoded_sig =
        stwo_mldsa::reference::encoding::sig_decode(&device_signature.signature_bytes)
            .map_err(|_| MdocError::InvalidSignature("deviceSignature"))?;
    let input = MlDsaVerifyInput::from_decoded(
        &decoded_pk,
        &decoded_sig,
        trace.tr,
        device_signature.sig_structure.clone(),
    );
    Ok(MdocAuthInput::MlDsa(Box::new(input)))
}

pub fn extract_pid_mdoc(
    document: &[u8],
    request: &MdocPidRequest,
) -> Result<ExtractedPidMdoc, MdocError> {
    let requested_attributes = request.disclosed_attributes();
    validate_requested_attributes(&requested_attributes)?;
    let doc = decode_value(document)?;
    let doc_map = document_map(&doc)?;
    let doctype = text_field(doc_map, "docType")?.to_string();
    if doctype != request.doctype {
        return Err(MdocError::DoctypeMismatch);
    }

    let issuer_signed = map_field(doc_map, "issuerSigned")?;
    let issuer_auth = parse_cose_sign1(value_field(issuer_signed, "issuerAuth")?)?;
    let issuer_unprotected = expect_map(&issuer_auth.unprotected, "issuerAuth.unprotected")?;
    let issuer_mldsa_input = mldsa_issuer_input(issuer_unprotected, request, &issuer_auth)?;

    let mso = parse_mso(&issuer_auth.payload, &request.namespace)?;
    if !is_supported_mdoc_profile_version(&mso.version) {
        return Err(MdocError::UnsupportedMsoVersion(mso.version));
    }
    if mso.doc_type != request.doctype {
        return Err(MdocError::DoctypeMismatch);
    }

    let namespace_items = namespace_items(issuer_signed, &request.namespace)?;
    let mut extracted_attributes = Vec::with_capacity(requested_attributes.len());
    for attribute in &requested_attributes {
        let item = find_item(namespace_items, &attribute.element_identifier, &mso.version)?
            .ok_or_else(|| MdocError::ElementMissing(attribute.element_identifier.clone()))?;
        validate_item_digest(
            &mso.value_digests,
            &attribute.element_identifier,
            item.digest_id,
            &item.bytes,
        )?;
        let element_identifier_offset =
            find_subslice(&item.bytes, attribute.element_identifier.as_bytes()).ok_or(
                MdocError::UnsupportedCircuitValue("attribute elementIdentifier offset"),
            )?;
        let value = encode_value(item.value.clone());
        if let MdocDisclosureMode::ValueEquality(expected) = &attribute.mode {
            if &value != expected {
                return Err(MdocError::ValueEqualityMismatch {
                    element: attribute.element_identifier.clone(),
                });
            }
        }
        let value_offset = find_subslice(&item.bytes, &value)
            .ok_or(MdocError::UnsupportedCircuitValue("attribute value offset"))?;
        extracted_attributes.push(ExtractedMdocAttribute {
            request: attribute.clone(),
            digest_id: item.digest_id,
            item: item.bytes,
            element_identifier_offset,
            value_offset,
            value,
        });
    }
    let birth_date_element = requested_attributes.iter().find_map(|attribute| {
        matches!(attribute.mode, MdocDisclosureMode::AgeOver)
            .then_some(attribute.element_identifier.as_str())
    });
    let nationality_element = requested_attributes.iter().find_map(|attribute| {
        matches!(attribute.mode, MdocDisclosureMode::Alpha2Set)
            .then_some(attribute.element_identifier.as_str())
    });
    let birth_date_item = if let Some(element) = birth_date_element {
        Some(
            find_item(namespace_items, element, &mso.version)?
                .ok_or_else(|| MdocError::ElementMissing(element.to_string()))?,
        )
    } else {
        None
    };
    let nationality_item = if let Some(element) = nationality_element {
        Some(
            find_item(namespace_items, element, &mso.version)?
                .ok_or_else(|| MdocError::ElementMissing(element.to_string()))?,
        )
    } else {
        None
    };

    let parsed_birth = if let Some(item) = &birth_date_item {
        validate_item_digest(
            &mso.value_digests,
            birth_date_element.expect("AgeOver element is present"),
            item.digest_id,
            &item.bytes,
        )?;
        parse_birth_date_value(item)?
    } else {
        ParsedBirthDateValue::default()
    };
    let (nationality_candidates, nationality_array_len) = if let Some(item) = &nationality_item {
        validate_item_digest(
            &mso.value_digests,
            nationality_element.expect("Alpha2Set element is present"),
            item.digest_id,
            &item.bytes,
        )?;
        parse_nationality_value(item)?
    } else {
        (Vec::new(), None)
    };
    // Default to the first entry; the policy-aware pick happens later in `select_accepted_nationality`.
    let parsed_nat = nationality_candidates.first().cloned().unwrap_or_default();

    let device_signed = map_field(doc_map, "deviceSigned")?;
    let device_auth = map_field(device_signed, "deviceAuth")?;
    let expected_device_payload = expected_device_authentication_bytes(request)?;
    let device_signature = parse_cose_sign1_with_detached_payload(
        value_field(device_auth, "deviceSignature")?,
        &expected_device_payload,
    )?;
    if device_signature.payload != expected_device_payload {
        return Err(MdocError::DeviceAuthPayloadMismatch);
    }
    let device_auth_input = mldsa_device_auth_input(&mso.device_key, &device_signature)?;

    let mut digest_ids = HashMap::new();
    for attribute in &extracted_attributes {
        digest_ids.insert(
            attribute.request.element_identifier.clone(),
            attribute.digest_id,
        );
    }
    if let (Some(element), Some(item)) = (birth_date_element, &birth_date_item) {
        digest_ids.insert(element.to_string(), item.digest_id);
    }
    if let (Some(element), Some(item)) = (nationality_element, &nationality_item) {
        digest_ids.insert(element.to_string(), item.digest_id);
    }

    let issuer_auth_input = IssuerAuthInput::MlDsa(Box::new(issuer_mldsa_input));

    Ok(ExtractedPidMdoc {
        doctype,
        namespace: request.namespace.clone(),
        attributes: requested_attributes,
        extracted_attributes,
        birth_date: parsed_birth.display,
        nationalities: vec![parsed_nat.numeric],
        birth_date_bytes: parsed_birth.bytes,
        nationality_bytes: parsed_nat.bytes,
        birth_date_binding: parsed_birth.binding,
        nationality_binding: parsed_nat.binding,
        birth_date_value_offset: parsed_birth.offset,
        nationality_value_offset: parsed_nat.offset,
        nationality_array_len,
        nationality_array_index: nationality_array_len.map(|_| 0),
        nationality_candidates,
        signed_at: mso.signed_at,
        valid_from: mso.valid_from,
        valid_until: mso.valid_until,
        digest_ids,
        birth_date_item: birth_date_item.map(|item| item.bytes).unwrap_or_default(),
        nationality_item: nationality_item.map(|item| item.bytes).unwrap_or_default(),
        mso: issuer_auth.payload,
        issuer_sig_structure: issuer_auth.sig_structure,
        device_sig_structure: device_signature.sig_structure,
        issuer_auth_input,
        device_auth_input,
    })
}

fn document_map(value: &Value) -> Result<&[(Value, Value)], MdocError> {
    let map = expect_map(value, "document")?;
    if value_field(map, "docType").is_ok() {
        return Ok(map);
    }
    if let Ok(status) = value_field(map, "status") {
        if value_i128(status)? != 0 {
            return Err(MdocError::WrongType("DeviceResponse.status"));
        }
    }
    let documents = expect_array(value_field(map, "documents")?, "DeviceResponse.documents")?;
    let first_document = documents
        .first()
        .ok_or(MdocError::MissingField("documents"))?;
    expect_map(first_document, "DeviceResponse.documents[0]")
}

#[derive(Clone)]
struct ParsedBirthDateValue {
    display: String,
    bytes: [u8; 4],
    binding: MdocBirthDateBinding,
    offset: usize,
}

impl Default for ParsedBirthDateValue {
    fn default() -> Self {
        Self {
            display: String::new(),
            bytes: [0; 4],
            binding: MdocBirthDateBinding::Text(*b"0000-00-00"),
            offset: 0,
        }
    }
}

#[derive(Clone, Debug)]
pub struct ParsedNationalityValue {
    numeric: u32,
    bytes: [u8; 2],
    binding: MdocNationalityBinding,
    offset: usize,
}

impl Default for ParsedNationalityValue {
    fn default() -> Self {
        Self {
            numeric: 0,
            bytes: [0; 2],
            binding: MdocNationalityBinding::Alpha2([0; 2]),
            offset: 0,
        }
    }
}

#[derive(Clone)]
struct CoseSign1 {
    unprotected: Value,
    payload: Vec<u8>,
    signature_bytes: Vec<u8>,
    sig_structure: Vec<u8>,
}

struct ParsedMso {
    version: String,
    doc_type: String,
    value_digests: HashMap<u32, [u8; 32]>,
    device_key: Vec<u8>,
    signed_at: (u16, u8, u8),
    valid_from: (u16, u8, u8),
    valid_until: (u16, u8, u8),
}

#[derive(Clone)]
struct ParsedItem {
    digest_id: u32,
    element: String,
    value: Value,
    bytes: Vec<u8>,
}

fn parse_birth_date_value(item: &ParsedItem) -> Result<ParsedBirthDateValue, MdocError> {
    match &item.value {
        Value::Text(text) => parse_birth_date_text_value(item, text),
        Value::Tag(CBOR_TAG_FULL_DATE, inner) => {
            let text = expect_text(inner, "birth_date elementValue")?;
            parse_birth_date_text_value(item, text)
        }
        Value::Bytes(bytes) => {
            let raw: [u8; 4] = bytes
                .as_slice()
                .try_into()
                .map_err(|_| MdocError::UnsupportedCircuitValue("birth_date binary length"))?;
            let year = u16::from_be_bytes([raw[0], raw[1]]);
            let month = raw[2];
            let day = raw[3];
            let offset = find_subslice(&item.bytes, &raw).ok_or(
                MdocError::UnsupportedCircuitValue("birth_date binary offset"),
            )?;
            Ok(ParsedBirthDateValue {
                display: format!("{year:04}-{month:02}-{day:02}"),
                bytes: raw,
                binding: MdocBirthDateBinding::Packed(raw),
                offset,
            })
        }
        _ => Err(MdocError::WrongType("birth_date elementValue")),
    }
}

fn parse_birth_date_text_value(
    item: &ParsedItem,
    text: &str,
) -> Result<ParsedBirthDateValue, MdocError> {
    let (year, month, day) = parse_birth_date_text(text)?;
    let value_bytes = text.as_bytes();
    let offset = find_subslice(&item.bytes, value_bytes)
        .ok_or(MdocError::UnsupportedCircuitValue("birth_date text offset"))?;
    Ok(ParsedBirthDateValue {
        display: text.to_string(),
        bytes: [(year >> 8) as u8, (year & 0xFF) as u8, month, day],
        binding: MdocBirthDateBinding::Text(
            value_bytes
                .try_into()
                .map_err(|_| MdocError::UnsupportedCircuitValue("birth_date text length"))?,
        ),
        offset,
    })
}

fn parse_nationality_value(
    item: &ParsedItem,
) -> Result<(Vec<ParsedNationalityValue>, Option<u8>), MdocError> {
    let (values, array_len, array_start): (Vec<&Value>, Option<u8>, Option<usize>) = match &item
        .value
    {
        Value::Array(entries) if (1..=MAX_NATIONALITY_MEMBERS).contains(&entries.len()) => {
            // `item.value` is re-encoded below to locate it in the original
            // IssuerSignedItemBytes. A non-canonical/indefinite array cannot
            // have that exact definite head and is therefore rejected before
            // it reaches the circuit.
            let encoded = encode_value(item.value.clone());
            let start =
                find_subslice(&item.bytes, &encoded).ok_or(MdocError::UnsupportedCircuitValue(
                    "nationality array must use a canonical definite head",
                ))?;
            (
                entries.iter().collect(),
                Some(entries.len() as u8),
                Some(start),
            )
        }
        Value::Array(_) => {
            return Err(MdocError::UnsupportedCircuitValue(
                "nationality array must contain 1..=8 members",
            ))
        }
        other => (vec![other], None, None),
    };
    let mut candidates: Vec<_> = values
        .into_iter()
        .map(|value| parse_one_nationality(item, value))
        .collect::<Result<_, _>>()?;
    if let Some(start) = array_start {
        for (index, candidate) in candidates.iter_mut().enumerate() {
            let member_offset = start + 1 + 3 * index;
            let expected = nationality_member_bytes(&candidate.binding);
            ensure_value_window_with_message(
                &item.bytes,
                member_offset,
                &expected,
                "nationality array member encoding",
            )?;
            candidate.offset = member_offset + 1;
        }
    }
    Ok((candidates, array_len))
}

fn select_nationality_index(candidates: &[ParsedNationalityValue], accepted: &[u32]) -> usize {
    candidates
        .iter()
        .position(|c| accepted.contains(&c.numeric))
        .unwrap_or(0)
}

pub fn select_accepted_nationality(extracted: &mut ExtractedPidMdoc, policy: &Policy) {
    let index = select_nationality_index(
        &extracted.nationality_candidates,
        &policy.accepted_nationalities,
    );
    if let Some(selected) = extracted.nationality_candidates.get(index).cloned() {
        extracted.nationalities = vec![selected.numeric];
        extracted.nationality_bytes = selected.bytes;
        extracted.nationality_binding = selected.binding;
        extracted.nationality_value_offset = selected.offset;
        extracted.nationality_array_index = extracted.nationality_array_len.map(|_| index as u8);
    }
}

fn parse_one_nationality(
    item: &ParsedItem,
    value: &Value,
) -> Result<ParsedNationalityValue, MdocError> {
    match value {
        Value::Text(alpha2) => {
            let numeric = numeric_country(alpha2)?;
            let bytes = [(numeric >> 8) as u8, (numeric & 0xFF) as u8];
            let offset = find_subslice(&item.bytes, alpha2.as_bytes()).ok_or(
                MdocError::UnsupportedCircuitValue("nationality text offset"),
            )?;
            Ok(ParsedNationalityValue {
                numeric,
                bytes,
                binding: MdocNationalityBinding::Alpha2(
                    alpha2.as_bytes().try_into().map_err(|_| {
                        MdocError::UnsupportedCircuitValue("nationality text length")
                    })?,
                ),
                offset,
            })
        }
        Value::Bytes(bytes) => {
            let raw: [u8; 2] = bytes
                .as_slice()
                .try_into()
                .map_err(|_| MdocError::UnsupportedCircuitValue("nationality binary length"))?;
            let numeric = u16::from_be_bytes(raw) as u32;
            let offset = find_subslice(&item.bytes, &raw).ok_or(
                MdocError::UnsupportedCircuitValue("nationality binary offset"),
            )?;
            Ok(ParsedNationalityValue {
                numeric,
                bytes: raw,
                binding: MdocNationalityBinding::Numeric(raw),
                offset,
            })
        }
        _ => Err(MdocError::WrongType("nationality elementValue")),
    }
}

fn parse_birth_date_text(text: &str) -> Result<(u16, u8, u8), MdocError> {
    let bytes = text.as_bytes();
    if bytes.len() != 10 || bytes[4] != b'-' || bytes[7] != b'-' {
        return Err(MdocError::UnsupportedCircuitValue(
            "birth_date text must be YYYY-MM-DD",
        ));
    }
    let year = parse_digits(&bytes[0..4])? as u16;
    let month = parse_digits(&bytes[5..7])? as u8;
    let day = parse_digits(&bytes[8..10])? as u8;
    Ok((year, month, day))
}

fn parse_digits(bytes: &[u8]) -> Result<u32, MdocError> {
    let mut value = 0u32;
    for &byte in bytes {
        if !byte.is_ascii_digit() {
            return Err(MdocError::UnsupportedCircuitValue("non-digit date byte"));
        }
        value = value * 10 + u32::from(byte - b'0');
    }
    Ok(value)
}

fn find_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() {
        return Some(0);
    }
    haystack
        .windows(needle.len())
        .position(|candidate| candidate == needle)
}

fn attribute_exposure(statement: &MdocCircuitStatement, index: usize) -> FieldExposure {
    let attribute = &statement.attributes[index];
    FieldExposure::from_full_padded_stream(
        MdocStatementAttribute::outer_stream_field_id(index),
        usize::from(attribute.item_padded_len),
    )
}

/// Field exposure over the issuer `Sig_structure` preimage: the two 32-byte
/// `valueDigests` windows (D2) and the two 32-byte deviceKey coordinate windows
/// (D3), all consumed by the MSO window-bind component.
fn ts13_revocation_message_bytes(id_lo: u64, id_hi: u64, epoch: u32) -> [u8; 20] {
    let mut bytes = [0u8; TS13_REVOCATION_MESSAGE_LEN];
    bytes[..8].copy_from_slice(&id_lo.to_le_bytes());
    bytes[8..16].copy_from_slice(&id_hi.to_le_bytes());
    bytes[16..].copy_from_slice(&epoch.to_le_bytes());
    bytes
}

fn check_mldsa_extracted_statement_coherence(
    extracted: &ExtractedPidMdoc,
    statement: &MdocCircuitStatement,
) -> Result<(), Error> {
    if extracted.doctype != statement.doctype || extracted.namespace != statement.namespace {
        return Err(Error::Prove(
            "mdoc extracted document scope does not match the statement".to_string(),
        ));
    }
    if extracted.mso.len() != statement.mso_payload_len
        || extracted.extracted_attributes.len() != statement.attributes.len()
    {
        return Err(Error::Prove(
            "mdoc extracted resource shape does not match the statement".to_string(),
        ));
    }
    for (index, (extracted_attribute, statement_attribute)) in extracted
        .extracted_attributes
        .iter()
        .zip(&statement.attributes)
        .enumerate()
    {
        let padded_len = stwo_sha256::native::pad_message(&extracted_attribute.item).len();
        if extracted_attribute.request.element_identifier != statement_attribute.element_identifier
            || extracted_attribute.request.mode != statement_attribute.mode
            || padded_len != usize::from(statement_attribute.item_padded_len)
        {
            return Err(Error::Prove(format!(
                "mdoc extracted attribute {index} does not match the statement"
            )));
        }
    }
    if let Some(input) = statement.issuer_input.as_mldsa() {
        if extracted.issuer_sig_structure != input.message {
            return Err(Error::Prove(
                "mdoc extracted issuer Sig_structure does not match the statement's public ML-DSA message".to_string(),
            ));
        }
    }
    if let Some(input) = statement.device_input.as_mldsa() {
        if extracted.device_sig_structure != input.message {
            return Err(Error::Prove(
                "mdoc extracted device Sig_structure does not match the statement's public ML-DSA message".to_string(),
            ));
        }
    }
    Ok(())
}

/// The revocation range is a prover-only witness.  The verifier reconstructs
/// the presence and layout of its AIR solely from the public key/epoch. The
/// range and signature are prover-only witnesses. Keeping this check central
/// prevents a partially filled proving triple from silently becoming a proof
/// without revocation.
fn validate_ts13_revocation_shape(
    statement: &MdocCircuitStatement,
    require_private_range: bool,
    phase: &'static str,
) -> Result<bool, Error> {
    let fail = |context: &str| {
        let detail = format!("TS13 revocation inputs: {context}");
        if phase == "prove" {
            Error::Prove(detail)
        } else {
            Error::Verify(detail)
        }
    };

    let public = statement.ts13_revocation.is_some();
    let private_range = statement.ts13_revocation_range.is_some();
    let private_signature = statement.ts13_revocation_signature.is_some();
    if require_private_range {
        return match (public, private_range, private_signature) {
            (false, false, false) => Ok(false),
            (true, true, true) => Ok(true),
            (true, false, _) => Err(fail("proving requires the private id range witness")),
            (true, _, false) => Err(fail("proving requires the revocation signature witness")),
            _ => Err(fail(
                "private revocation witnesses require public revocation inputs",
            )),
        };
    }
    match (public, private_range || private_signature) {
        (false, false) => Ok(false),
        (false, true) => Err(fail(
            "private revocation witnesses require public revocation inputs",
        )),
        // Direct in-memory verification may still receive the prover's
        // witnesses. Serialized public statements receive neither; both have
        // the same public layout.
        (true, _) => Ok(true),
    }
}

fn validate_mldsa_public_keys(
    statement: &MdocCircuitStatement,
    phase: &'static str,
) -> Result<(), Error> {
    for (role, input) in [
        ("issuer", statement.issuer_input.as_mldsa()),
        ("device", statement.device_input.as_mldsa()),
    ] {
        if let Some(input) = input {
            input.validate_public_key().map_err(|message| {
                let detail = format!("mdoc {role} public key: {message}");
                if phase == "prove" {
                    Error::Prove(detail)
                } else {
                    Error::Verify(detail)
                }
            })?;
        }
    }
    Ok(())
}

fn mdoc_phase_error(phase: &'static str, message: String) -> Error {
    if phase == "prove" {
        Error::Prove(message)
    } else {
        Error::Verify(message)
    }
}

fn validate_mdoc_statement_shape<'a>(
    phase: &'static str,
    doctype: &str,
    policy: &Policy,
    lengths: MdocStatementResourceLengths,
    max_device_message_bytes: usize,
    attribute_count: usize,
    attributes: impl Iterator<Item = (&'a str, &'a MdocDisclosureMode)>,
) -> Result<(), Error> {
    let fail = |message| mdoc_phase_error(phase, format!("mdoc public shape: {message}"));
    validate_attribute_shapes(attribute_count, attributes)
        .map_err(|error| fail(format!("invalid attributes: {error:?}")))?;

    for (role, length, max) in [
        (
            "issuer message",
            lengths.issuer_message_bytes,
            crate::ts13::TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES,
        ),
        (
            "device message",
            lengths.device_message_bytes,
            max_device_message_bytes,
        ),
        (
            "MSO payload",
            lengths.issuer_mso_payload_bytes,
            crate::ts13::TS13_MAX_MSO_PAYLOAD_BYTES,
        ),
    ] {
        if length == 0 || length > max {
            return Err(fail(format!("{role} length {length} is outside 1..={max}")));
        }
    }
    if doctype.is_empty()
        || doctype.len() > crate::mdoc_private_mso_bind::MDOC_PRIVATE_MSO_MAX_DOC_TYPE_BYTES
    {
        return Err(fail(format!(
            "docType length {} is outside 1..={}",
            doctype.len(),
            crate::mdoc_private_mso_bind::MDOC_PRIVATE_MSO_MAX_DOC_TYPE_BYTES
        )));
    }
    let date = policy.current_date;
    if date.year > 9_999 || !(1..=12).contains(&date.month) || !(1..=31).contains(&date.day) {
        return Err(fail(format!(
            "policy date {}-{}-{} is outside the supported shape",
            date.year, date.month, date.day
        )));
    }
    Ok(())
}

fn validate_mdoc_circuit_statement_shape(
    statement: &MdocCircuitStatement,
    phase: &'static str,
    is_ts13_demo: bool,
) -> Result<(), Error> {
    let lengths = mdoc_statement_resource_lengths(statement)
        .map_err(|error| mdoc_phase_error(phase, format!("mdoc public shape: {error:?}")))?;
    validate_mdoc_statement_shape(
        phase,
        &statement.doctype,
        &statement.policy,
        lengths,
        if is_ts13_demo {
            TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY
        } else {
            crate::ts13::TS13_MAX_DEVICE_MLDSA_MESSAGE_BYTES
        },
        statement.attributes.len(),
        statement
            .attributes
            .iter()
            .map(|attribute| (attribute.element_identifier.as_str(), &attribute.mode)),
    )?;
    for attribute in &statement.attributes {
        if !crate::mdoc_private_item_bind::MDOC_PRIVATE_ITEM_PADDED_BUCKETS
            .contains(&attribute.item_padded_len)
        {
            return Err(mdoc_phase_error(
                phase,
                format!(
                    "mdoc public shape: unsupported item padded length {}",
                    attribute.item_padded_len
                ),
            ));
        }
    }
    Ok(())
}

fn validate_mdoc_ts13_public_statement_shape(
    statement: &MdocTs13PublicStatement,
    phase: &'static str,
) -> Result<(), Error> {
    let lengths = mdoc_ts13_public_statement_resource_lengths(statement)
        .map_err(|error| mdoc_phase_error(phase, format!("mdoc public shape: {error:?}")))?;
    validate_mdoc_statement_shape(
        phase,
        &statement.doctype,
        &statement.policy,
        lengths,
        crate::ts13::TS13_MAX_DEVICE_MLDSA_MESSAGE_BYTES,
        statement.attributes.len(),
        statement
            .attributes
            .iter()
            .map(|attribute| (attribute.element_identifier.as_str(), &attribute.mode)),
    )
}

fn validate_public_auth_projection(statement: &MdocCircuitStatement) -> Result<(), Error> {
    let issuer = statement
        .issuer_input
        .as_mldsa()
        .ok_or_else(|| Error::Verify("mdoc issuer input is not ML-DSA".to_string()))?;
    let signature_witness_is_zero = |input: &MlDsaVerifyInput| {
        input.tr.iter().all(|&byte| byte == 0)
            && input.c_tilde.iter().all(|&byte| byte == 0)
            && input
                .z
                .iter()
                .flatten()
                .all(|&coefficient| coefficient == 0)
            && input.hint.iter().flatten().all(|&bit| bit == 0)
    };
    let device_is_publicly_projected = statement
        .device_input
        .as_mldsa()
        .is_some_and(signature_witness_is_zero)
        || statement.device_input.private_key_public_input().is_some();
    if !signature_witness_is_zero(issuer)
        || !device_is_publicly_projected
        || issuer.message.iter().any(|&byte| byte != 0)
    {
        return Err(Error::Verify(
            "mdoc public statement contains a private issuer message or ML-DSA signature witness"
                .to_string(),
        ));
    }
    Ok(())
}

/// Build the ML-DSA revocation verification input from the statement's public
/// key/signature bytes and the given 20-byte message. The prover passes the
/// REAL message (from the private range witness); the verifier passes 20 zero
/// bytes — the hosted instance runs in private-message mode, which mixes only
/// the message LENGTH into the transcript, and the real bytes flow exclusively
/// through the revocation SHA module's field relation (G6 privacy invariant:
/// `id_lo`/`id_hi` never enter the serialized statement or proof).
fn ts13_revocation_mldsa_input(
    statement: &MdocCircuitStatement,
    message: Vec<u8>,
) -> Result<Option<Box<MlDsaVerifyInput>>, Error> {
    let Some(signature) = statement
        .ts13_revocation_signature
        .as_ref()
        .and_then(|signature| signature.as_mldsa())
    else {
        return Ok(None);
    };
    let revocation = statement.ts13_revocation.as_ref().ok_or_else(|| {
        Error::Prove("TS13 revocation signature requires public revocation inputs".to_string())
    })?;
    let pk = revocation.revocation_public_key.as_mldsa().ok_or_else(|| {
        Error::Prove(
            "TS13 ML-DSA revocation signature requires an ML-DSA revocation key".to_string(),
        )
    })?;
    let decoded_pk = stwo_mldsa::reference::encoding::pk_decode(pk)
        .map_err(|error| Error::Prove(format!("TS13 revocation pk decode: {error:?}")))?;
    let decoded_sig = stwo_mldsa::reference::encoding::sig_decode(signature)
        .map_err(|error| Error::Prove(format!("TS13 revocation sig decode: {error:?}")))?;
    // tr = SHAKE-256(pk, 64 bytes) — a pure function of the PUBLIC key, so
    // both sides recompute it identically without touching the message.
    let (tr_bytes, _) = stwo_mldsa::reference::sponge::shake256(&[pk], 64);
    let tr: [u8; 64] = tr_bytes
        .try_into()
        .expect("shake256 returns the requested 64 bytes");
    Ok(Some(Box::new(MlDsaVerifyInput::from_decoded(
        &decoded_pk,
        &decoded_sig,
        tr,
        message,
    ))))
}

/// Verifier reconstruction of the revocation role. The existential ML-DSA
/// signature witness is carried by the STARK claim tree, not by the public
/// statement, so canonical zero placeholders are sufficient here.
fn ts13_revocation_mldsa_verifier_input(
    statement: &MdocCircuitStatement,
    message: Vec<u8>,
) -> Result<Option<Box<MlDsaVerifyInput>>, Error> {
    let Some(revocation) = statement.ts13_revocation.as_ref() else {
        return Ok(None);
    };
    let pk = revocation.revocation_public_key.as_mldsa().ok_or_else(|| {
        Error::Verify("TS13 ML-DSA revocation proof requires an ML-DSA revocation key".to_string())
    })?;
    let decoded_pk = stwo_mldsa::reference::encoding::pk_decode(pk)
        .map_err(|error| Error::Verify(format!("TS13 revocation pk decode: {error:?}")))?;
    let zero_signature = stwo_mldsa::reference::encoding::SignatureParts {
        c_tilde: [0; stwo_mldsa::constants::C_TILDE_BYTES],
        z: [[0; stwo_mldsa::constants::N]; stwo_mldsa::constants::L],
        h: [[0; stwo_mldsa::constants::N]; stwo_mldsa::constants::K],
    };
    let (tr_bytes, _) = stwo_mldsa::reference::sponge::shake256(&[pk], 64);
    let tr: [u8; 64] = tr_bytes
        .try_into()
        .expect("shake256 returns the requested 64 bytes");
    Ok(Some(Box::new(MlDsaVerifyInput::from_decoded(
        &decoded_pk,
        &zero_signature,
        tr,
        message,
    ))))
}

fn mdoc_window_bind_rows_from(statement: &MdocCircuitStatement) -> Vec<MdocWindowBindRow> {
    // This component is now only the verifier-known semantic sink. The
    // private item binder provides identifier/equality tuples after proving
    // their exact CBOR field positions; no credential offset, anchor, value
    // encoding, or array selector enters this row set.
    let mut rows = Vec::new();
    for (index, attribute) in statement.attributes.iter().enumerate() {
        rows.push(MdocWindowBindRow::constant(
            MdocStatementAttribute::element_field_id(index),
            index,
            attribute.element_identifier.as_bytes(),
        ));
        if let MdocDisclosureMode::ValueEquality(value) = &attribute.mode {
            rows.push(MdocWindowBindRow::constant(
                MdocStatementAttribute::value_field_id(index),
                index,
                value,
            ));
        }
    }
    rows
}

fn nat_public_input_for(statement: &MdocCircuitStatement) -> predicates::NatPublicInput {
    statement.policy.nat_public_input()
}

fn decode_value(bytes: &[u8]) -> Result<Value, MdocError> {
    ciborium::de::from_reader(bytes).map_err(|error| MdocError::Cbor(error.to_string()))
}

fn decode_value_exact(bytes: &[u8]) -> Result<Value, MdocError> {
    let mut reader = Cursor::new(bytes);
    let value = ciborium::de::from_reader(&mut reader)
        .map_err(|error| MdocError::Cbor(error.to_string()))?;
    if reader.position() != bytes.len() as u64 {
        return Err(MdocError::Cbor("trailing CBOR data".to_string()));
    }
    Ok(value)
}

/// Public byte lengths which determine the hosted ML-DSA/Keccak and mdoc-SHA
/// layouts.  Profile verifiers use this instead of trusting legacy serialized
/// offset metadata.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MdocStatementResourceLengths {
    pub issuer_message_bytes: usize,
    pub issuer_mso_payload_bytes: usize,
    pub device_message_bytes: usize,
}

pub fn mdoc_statement_resource_lengths(
    statement: &MdocCircuitStatement,
) -> Result<MdocStatementResourceLengths, Error> {
    let issuer = statement
        .issuer_input
        .as_mldsa()
        .ok_or_else(|| Error::Verify("mdoc statement issuer input is not ML-DSA".to_string()))?;
    Ok(MdocStatementResourceLengths {
        issuer_message_bytes: issuer.message.len(),
        issuer_mso_payload_bytes: statement.mso_payload_len,
        device_message_bytes: statement.device_input.message().len(),
    })
}

pub fn mdoc_ts13_public_statement_resource_lengths(
    statement: &MdocTs13PublicStatement,
) -> Result<MdocStatementResourceLengths, Error> {
    Ok(MdocStatementResourceLengths {
        issuer_message_bytes: usize::from(statement.issuer.message_len),
        issuer_mso_payload_bytes: usize::from(statement.mso_payload_len),
        device_message_bytes: usize::from(statement.device.message_len),
    })
}

fn encode_value(value: Value) -> Vec<u8> {
    let mut out = Vec::new();
    ciborium::ser::into_writer(&value, &mut out).expect("CBOR serialization into Vec");
    out
}

fn parse_cose_sign1(value: &Value) -> Result<CoseSign1, MdocError> {
    parse_cose_sign1_inner(value, None)
}

fn parse_cose_sign1_with_detached_payload(
    value: &Value,
    detached_payload: &[u8],
) -> Result<CoseSign1, MdocError> {
    parse_cose_sign1_inner(value, Some(detached_payload))
}

fn parse_cose_sign1_inner(
    value: &Value,
    detached_payload: Option<&[u8]>,
) -> Result<CoseSign1, MdocError> {
    let Value::Array(items) = value else {
        return Err(MdocError::WrongType("COSE_Sign1"));
    };
    if items.len() != 4 {
        return Err(MdocError::InvalidCoseSign1("expected four-element array"));
    }

    let protected = expect_bytes(&items[0], "COSE_Sign1.protected")?.to_vec();
    if protected != MLDSA_PROTECTED_HEADER {
        return Err(MdocError::InvalidCoseSign1(
            "protected header must be ML-DSA-65",
        ));
    }
    expect_map(&items[1], "COSE_Sign1.unprotected")?;
    let unprotected = items[1].clone();
    let payload = match (&items[2], detached_payload) {
        (Value::Bytes(payload), _) => payload.clone(),
        (Value::Null, Some(detached_payload)) => detached_payload.to_vec(),
        (Value::Null, None) => return Err(MdocError::InvalidCoseSign1("detached payload")),
        _ => return Err(MdocError::WrongType("COSE_Sign1.payload")),
    };
    let signature_bytes = expect_bytes(&items[3], "COSE_Sign1.signature")?.to_vec();
    if signature_bytes.len() != stwo_mldsa::constants::SIG_BYTES {
        return Err(MdocError::InvalidCoseSign1("ML-DSA-65 signature length"));
    }
    let sig_structure = sig_structure(&protected, &payload);

    Ok(CoseSign1 {
        unprotected,
        payload,
        signature_bytes,
        sig_structure,
    })
}

fn sig_structure(protected: &[u8], payload: &[u8]) -> Vec<u8> {
    encode_value(Value::Array(vec![
        "Signature1".into(),
        Value::Bytes(protected.to_vec()),
        Value::Bytes(Vec::new()),
        Value::Bytes(payload.to_vec()),
    ]))
}

pub fn openid4vp_session_transcript(handover_info: &[u8]) -> Vec<u8> {
    encode_value(Value::Array(vec![
        Value::Null,
        Value::Null,
        Value::Array(vec![
            "OpenID4VPHandover".into(),
            Value::Bytes(Sha256::digest(handover_info).to_vec()),
        ]),
    ]))
}

pub fn device_authentication_bytes(
    session_transcript: &[u8],
    doc_type: &str,
) -> Result<Vec<u8>, MdocError> {
    let session_transcript = decode_value(session_transcript)?;
    if !matches!(session_transcript, Value::Array(_)) {
        return Err(MdocError::WrongType("SessionTranscript"));
    }

    let device_namespaces = encode_value(Value::Map(Vec::new()));
    let device_authentication = encode_value(Value::Array(vec![
        "DeviceAuthentication".into(),
        session_transcript,
        doc_type.into(),
        Value::Tag(24, Box::new(Value::Bytes(device_namespaces))),
    ]));
    Ok(encode_value(Value::Tag(
        24,
        Box::new(Value::Bytes(device_authentication)),
    )))
}

fn expected_device_authentication_bytes(request: &MdocPidRequest) -> Result<Vec<u8>, MdocError> {
    match request.device_authentication_profile {
        MdocDeviceAuthenticationProfile::Iso180135 => {
            device_authentication_bytes(&request.session_transcript, &request.doctype)
        }
        MdocDeviceAuthenticationProfile::LongfellowLegacy => {
            longfellow_legacy_device_authentication_bytes(
                &request.session_transcript,
                &request.doctype,
            )
        }
    }
}

fn longfellow_legacy_device_authentication_bytes(
    session_transcript: &[u8],
    doc_type: &str,
) -> Result<Vec<u8>, MdocError> {
    let session_transcript_value = decode_value(session_transcript)?;
    if !matches!(session_transcript_value, Value::Array(_)) {
        return Err(MdocError::WrongType("SessionTranscript"));
    }
    let mut device_authentication = encode_value(Value::Array(vec!["DeviceAuthentication".into()]));
    device_authentication[0] = 0x84;
    device_authentication.extend_from_slice(session_transcript);
    device_authentication.extend_from_slice(&encode_value(Value::Text(doc_type.to_string())));
    device_authentication.extend_from_slice(&encode_value(Value::Tag(
        24,
        Box::new(Value::Bytes(encode_value(Value::Map(Vec::new())))),
    )));
    Ok(encode_value(Value::Tag(
        24,
        Box::new(Value::Bytes(device_authentication)),
    )))
}

pub fn device_authentication_sig_structure_hash(
    session_transcript: &[u8],
    doc_type: &str,
) -> Result<[u8; 32], MdocError> {
    let payload = device_authentication_bytes(session_transcript, doc_type)?;
    Ok(Sha256::digest(sig_structure(MLDSA_PROTECTED_HEADER, &payload)).into())
}

fn parse_mso(bytes: &[u8], namespace: &str) -> Result<ParsedMso, MdocError> {
    let value = decode_value_exact(bytes)?;
    let value = match value {
        Value::Tag(CBOR_TAG_ENCODED_CBOR, inner) => {
            let mso_bytes = expect_bytes(&inner, "MobileSecurityObjectBytes")?;
            decode_value_exact(mso_bytes)?
        }
        value => value,
    };
    parse_mso_value(&value, namespace)
}

fn parse_mso_value(value: &Value, namespace: &str) -> Result<ParsedMso, MdocError> {
    let mso = expect_map(value, "MobileSecurityObject")?;
    let version = text_field(mso, "version")?.to_string();
    let doc_type = text_field(mso, "docType")?.to_string();
    let digest_algorithm = text_field(mso, "digestAlgorithm")?;
    if digest_algorithm != "SHA-256" {
        return Err(MdocError::UnsupportedDigestAlgorithm(
            digest_algorithm.to_string(),
        ));
    }

    let value_digests = map_field(mso, "valueDigests")?;
    let namespace_key = Value::Text(namespace.to_string());
    let mut namespace_matches = value_digests
        .iter()
        .filter_map(|(key, value)| (key == &namespace_key).then_some(value));
    let namespace_digests = namespace_matches
        .next()
        .ok_or(MdocError::NamespaceMissing)?;
    if namespace_matches.next().is_some() {
        return Err(MdocError::UnsupportedCircuitValue(
            "duplicate valueDigests namespace",
        ));
    }
    let namespace_digests = expect_map(namespace_digests, "valueDigests namespace")?;
    let mut digests = HashMap::new();
    for (key, value) in namespace_digests {
        let digest_id = expect_u32(key, "digestID")?;
        let digest = expect_digest(value, "elementDigest")?;
        if digests.insert(digest_id, digest).is_some() {
            return Err(MdocError::UnsupportedCircuitValue("duplicate digestID"));
        }
    }

    let device_key_info = map_field(mso, "deviceKeyInfo")?;
    let device_key = parse_device_cose_key(value_field(device_key_info, "deviceKey")?)?;
    let validity_info = map_field(mso, "validityInfo")?;
    let signed_at = parse_tdate(value_field(validity_info, "signed")?, "validityInfo.signed")?;
    let valid_from = parse_tdate(
        value_field(validity_info, "validFrom")?,
        "validityInfo.validFrom",
    )?;
    let valid_until = parse_tdate(
        value_field(validity_info, "validUntil")?,
        "validityInfo.validUntil",
    )?;

    Ok(ParsedMso {
        version,
        doc_type,
        value_digests: digests,
        device_key,
        signed_at,
        valid_from,
        valid_until,
    })
}

fn parse_tdate(value: &Value, field: &'static str) -> Result<(u16, u8, u8), MdocError> {
    let Value::Tag(0, inner) = value else {
        return Err(MdocError::InvalidTdate(field));
    };
    let text = expect_text(inner, field).map_err(|_| MdocError::InvalidTdate(field))?;
    let bytes = text.as_bytes();
    if bytes.len() != 20
        || bytes[4] != b'-'
        || bytes[7] != b'-'
        || bytes[10] != b'T'
        || bytes[13] != b':'
        || bytes[16] != b':'
        || bytes[19] != b'Z'
    {
        return Err(MdocError::InvalidTdate(field));
    }
    let year = parse_tdate_digits(&bytes[0..4], field)? as u16;
    let month = parse_tdate_digits(&bytes[5..7], field)? as u8;
    let day = parse_tdate_digits(&bytes[8..10], field)? as u8;
    let hour = parse_tdate_digits(&bytes[11..13], field)? as u8;
    let minute = parse_tdate_digits(&bytes[14..16], field)? as u8;
    let second = parse_tdate_digits(&bytes[17..19], field)? as u8;
    if !(1..=12).contains(&month)
        || !(1..=31).contains(&day)
        || hour > 23
        || minute > 59
        || second > 59
    {
        return Err(MdocError::InvalidTdate(field));
    }
    Ok((year, month, day))
}

fn parse_tdate_digits(bytes: &[u8], field: &'static str) -> Result<u32, MdocError> {
    let mut value = 0u32;
    for &byte in bytes {
        if !byte.is_ascii_digit() {
            return Err(MdocError::InvalidTdate(field));
        }
        value = value * 10 + u32::from(byte - b'0');
    }
    Ok(value)
}

fn namespace_items<'a>(
    issuer_signed: &'a [(Value, Value)],
    namespace: &str,
) -> Result<&'a [Value], MdocError> {
    let namespaces = map_field(issuer_signed, "nameSpaces")?;
    let value = namespaces
        .iter()
        .find_map(|(key, value)| (key == &Value::Text(namespace.to_string())).then_some(value))
        .ok_or(MdocError::NamespaceMissing)?;
    let Value::Array(items) = value else {
        return Err(MdocError::WrongType("issuerSigned.nameSpaces namespace"));
    };
    Ok(items)
}

fn find_item(
    items: &[Value],
    element: &str,
    profile_version: &str,
) -> Result<Option<ParsedItem>, MdocError> {
    for item in items {
        let item_bytes = issuer_signed_item_bytes(item)?;
        let parsed = parse_issuer_signed_item_bytes(&item_bytes, profile_version)?;
        if parsed.element == element {
            return Ok(Some(parsed));
        }
    }
    Ok(None)
}

fn issuer_signed_item_bytes(item: &Value) -> Result<Vec<u8>, MdocError> {
    match item {
        Value::Bytes(bytes) => Ok(bytes.clone()),
        Value::Tag(CBOR_TAG_ENCODED_CBOR, inner) => {
            expect_bytes(inner, "IssuerSignedItemBytes")?;
            Ok(encode_value(item.clone()))
        }
        _ => Err(MdocError::WrongType("IssuerSignedItemBytes")),
    }
}

fn parse_issuer_signed_item_bytes(
    bytes: &[u8],
    profile_version: &str,
) -> Result<ParsedItem, MdocError> {
    let value = decode_value(bytes)?;
    let Value::Tag(24, inner) = value else {
        return Err(MdocError::WrongType("IssuerSignedItemBytes tag 24"));
    };
    let item_bytes = expect_bytes(&inner, "IssuerSignedItemBytes")?;
    let item_value = decode_value(item_bytes)?;
    let item = expect_map(&item_value, "IssuerSignedItem")?;
    ensure_issuer_signed_item_key_order(item, profile_version)?;
    let digest_id = u32_field(item, "digestID")?;
    let element = text_field(item, "elementIdentifier")?.to_string();
    let random_len = expect_bytes(value_field(item, "random")?, "random")?.len();
    if random_len < 16 {
        return Err(MdocError::SaltTooShort { len: random_len });
    }
    let value = value_field(item, "elementValue")?.clone();
    Ok(ParsedItem {
        digest_id,
        element,
        value,
        bytes: bytes.to_vec(),
    })
}

/// Require the four `IssuerSignedItem` keys. Profile v1 accepts legacy key
/// ordering; profile v2 requires the RFC 8949 canonical order used by the
/// canonical-CBOR profile.
fn ensure_issuer_signed_item_key_order(
    item: &[(Value, Value)],
    profile_version: &str,
) -> Result<(), MdocError> {
    const KEY_SET: [&str; 4] = ["elementValue", "digestID", "random", "elementIdentifier"];
    const V2_CANONICAL: [&str; 4] = ["random", "digestID", "elementValue", "elementIdentifier"];
    if item.len() != KEY_SET.len() {
        return Err(MdocError::UnsupportedCircuitValue(
            "IssuerSignedItem key set",
        ));
    }
    for expected in KEY_SET {
        let present = item
            .iter()
            .any(|(key, _)| key == &Value::Text(expected.to_string()));
        if !present {
            return Err(MdocError::UnsupportedCircuitValue(
                "IssuerSignedItem key set",
            ));
        }
    }
    if profile_version == MDOC_PROFILE_VERSION_V2 {
        let canonical = item
            .iter()
            .map(|(key, _)| key)
            .zip(V2_CANONICAL)
            .all(|(key, expected)| key == &Value::Text(expected.to_string()));
        if !canonical {
            return Err(MdocError::UnsupportedCircuitValue(
                "IssuerSignedItem canonical key order",
            ));
        }
    }
    Ok(())
}

fn validate_item_digest(
    digests: &HashMap<u32, [u8; 32]>,
    element: &str,
    digest_id: u32,
    item_bytes: &[u8],
) -> Result<(), MdocError> {
    let expected = digests
        .get(&digest_id)
        .ok_or_else(|| MdocError::ItemDigestMismatch {
            element: element.to_string(),
            digest_id,
        })?;
    let actual: [u8; 32] = Sha256::digest(item_bytes).into();
    if &actual != expected {
        return Err(MdocError::ItemDigestMismatch {
            element: element.to_string(),
            digest_id,
        });
    }
    Ok(())
}

/// Parse the MSO ML-DSA-65 AKP `deviceKey`.
fn parse_device_cose_key(value: &Value) -> Result<Vec<u8>, MdocError> {
    let key = expect_map(value, "COSE_Key")?;
    Ok(parse_akp_mldsa_cose_key(key)?.to_vec())
}

/// The FIPS 204 `pkEncode` bytes of the statement's ML-DSA issuer key,
/// recomputed from the PUBLIC `(ρ, t1)` in the statement — never read from the
/// prover-supplied `tr` digest. A relying party binds its issuer trust anchor
/// against this (e.g. the SDK's statement-binding layer compares a pinned
/// SHA-256 of these bytes); `None` for a P-256 issuer statement.
pub fn mdoc_statement_issuer_mldsa_pk(statement: &MdocCircuitStatement) -> Option<Vec<u8>> {
    statement
        .issuer_input
        .as_mldsa()
        .map(|input| stwo_mldsa::reference::encoding::pk_encode(&input.rho, &input.t1))
}

/// ML-DSA-65 issuer key from the unprotected `issuerKey` COSE_Key: AKP key
/// type (`kty = 7`), `alg = -49`, raw 1952-byte public key in label `-1`.
///
/// Trust is FAIL-CLOSED: the request MUST carry a non-empty
/// `trusted_mldsa_issuer_public_keys` pin list and the header key must be
/// byte-equal to a member — the self-carried AKP key is never a trust
/// decision.
fn mldsa_issuer_pk_from_unprotected(
    unprotected: &[(Value, Value)],
    request: &MdocPidRequest,
) -> Result<Vec<u8>, MdocError> {
    let key = expect_map(value_field(unprotected, "issuerKey")?, "COSE_Key")?;
    let pk = parse_akp_mldsa_cose_key(key)?;
    if !request
        .trusted_mldsa_issuer_public_keys
        .iter()
        .any(|trusted| trusted.as_slice() == pk)
    {
        // Also the empty-pin-list case: no pins ⇒ nothing is trusted.
        return Err(MdocError::UntrustedIssuerKey);
    }
    Ok(pk.to_vec())
}

/// Parse an AKP ML-DSA-65 COSE_Key map (`kty = 7`, `alg = -49`, raw 1952-byte
/// public key in label `-1`). Shared by the issuer header key and the MSO
/// `deviceKey` parser.
fn parse_akp_mldsa_cose_key(key: &[(Value, Value)]) -> Result<&[u8], MdocError> {
    let kty = int_field(key, 1, "COSE_Key.kty")?;
    let alg = int_field(key, 3, "COSE_Key.alg")?;
    if kty != i128::from(stwo_mldsa::constants::COSE_KTY_AKP)
        || alg != i128::from(stwo_mldsa::constants::COSE_ALG_ML_DSA_65)
    {
        return Err(MdocError::InvalidCoseKey("expected ML-DSA-65 AKP key"));
    }
    let pk = bytes_int_field(key, -1, "COSE_Key.pub")?;
    if pk.len() != stwo_mldsa::constants::PK_BYTES {
        return Err(MdocError::InvalidCoseKey("ML-DSA-65 public key length"));
    }
    Ok(pk)
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MdocCircuitStatement {
    /// Verifier-selected ISO document scope. The private MSO binder proves
    /// that the issuer-signed payload carries this exact `docType`.
    pub doctype: String,
    pub namespace: String,
    #[serde(
        serialize_with = "serialize_private_issuer_auth",
        deserialize_with = "deserialize_private_issuer_auth"
    )]
    pub issuer_input: IssuerAuthInput,
    /// Device-auth input. Scheme uniformity with `issuer_input` and the
    /// revocation role is enforced fail-closed at prove and verify — a mixed
    /// statement never reaches STARK work.
    #[serde(
        serialize_with = "serialize_public_device_auth",
        deserialize_with = "deserialize_public_device_auth"
    )]
    pub device_input: DeviceAuthInput,
    pub ts13_revocation: Option<MdocRevocationPublicInputs>,
    /// Prover-only private witness.  It is deliberately absent from every
    /// verifier envelope; deserialization supplies `None` for verification.
    #[serde(skip, default)]
    pub ts13_revocation_range: Option<MdocRevocationRangeWitness>,
    /// Prover-only existential signature witness. The verifier reconstructs
    /// the revocation AIR layout from the public key, epoch, and proof claim
    /// shape; it never synthesizes or serializes a signature placeholder.
    #[serde(skip, default)]
    pub ts13_revocation_signature: Option<MdocRevocationSignature>,
    pub attributes: Vec<MdocStatementAttribute>,
    /// Public bounded length of the private issuerAuth payload. All payload
    /// bytes, offsets, validity dates, digest IDs, and item encodings remain
    /// prover-only witnesses.
    pub mso_payload_len: usize,
    pub policy: Policy,
}

/// ML-DSA-65 revocation-authority public key (`pkEncode`, 1,952 bytes).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MdocRevocationKey {
    MlDsa(Vec<u8>),
}

impl MdocRevocationKey {
    pub fn as_mldsa(&self) -> Option<&[u8]> {
        match self {
            Self::MlDsa(pk) => Some(pk),
        }
    }

    pub fn is_mldsa(&self) -> bool {
        true
    }
}

/// ML-DSA-65 signature over `LE64(id_lo) ‖ LE64(id_hi) ‖ LE32(epoch)`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MdocRevocationSignature {
    MlDsa(Vec<u8>),
}

impl MdocRevocationSignature {
    pub fn as_mldsa(&self) -> Option<&[u8]> {
        match self {
            Self::MlDsa(signature) => Some(signature),
        }
    }

    pub fn is_mldsa(&self) -> bool {
        true
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocRevocationPublicInputs {
    pub revocation_public_key: MdocRevocationKey,
    pub epoch: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocRevocationRangeWitness {
    pub id: u64,
    pub id_lo: u64,
    pub id_hi: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MdocStatementAttribute {
    pub element_identifier: String,
    pub mode: MdocDisclosureMode,
    /// SHA-256-padded item bucket. This is the only public item-shape
    /// determinant; the raw item length and every semantic offset stay
    /// private.
    pub item_padded_len: u16,
}

impl MdocStatementAttribute {
    fn outer_stream_field_id(index: usize) -> u32 {
        MDOC_ATTRIBUTE_ITEM_STREAM_BASE + MDOC_ATTRIBUTE_ITEM_STREAM_STRIDE * index as u32
    }

    fn inner_stream_field_id(index: usize) -> u32 {
        Self::outer_stream_field_id(index) + 1
    }

    fn element_field_id(index: usize) -> u32 {
        MDOC_ATTRIBUTE_ELEMENT_ID_BASE + index as u32
    }

    fn value_field_id(index: usize) -> u32 {
        MDOC_ATTRIBUTE_VALUE_BASE + index as u32
    }
}

/// Public verifier statement for the dedicated TS13 equality-and-revocation
/// profile.
///
/// This type deliberately cannot carry credential attribute witnesses,
/// byte-window offsets/anchors, revocation bounds, or ML-DSA signature
/// witnesses. The prover keeps those in [`MdocCircuitStatement`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocTs13PublicStatement {
    pub doctype: String,
    pub namespace: String,
    pub issuer: MdocMlDsaPublicAuthInput,
    pub device: MdocMlDsaPublicAuthInput,
    pub revocation: MdocRevocationPublicInputs,
    /// Public bounded length of the private MobileSecurityObject payload.
    pub mso_payload_len: u16,
    /// Public 64-byte SHA-256 size bucket of the selected IssuerSignedItem.
    pub requested_item_padded_len: u16,
    pub attributes: Vec<MdocRequestedAttribute>,
    pub policy: Policy,
}

impl MdocTs13PublicStatement {
    pub fn from_circuit(statement: &MdocCircuitStatement) -> Result<Self, Error> {
        if statement.ts13_revocation_signature.is_none()
            || statement.ts13_revocation_range.is_none()
        {
            return Err(Error::Prove(
                "TS13 public statement requires a complete revocation witness".to_string(),
            ));
        }
        let revocation = statement.ts13_revocation.clone().ok_or_else(|| {
            Error::Prove("TS13 public statement requires revocation inputs".to_string())
        })?;
        let [requested_attribute] = statement.attributes.as_slice() else {
            return Err(Error::Prove(
                "TS13 public statement requires exactly one attribute".to_string(),
            ));
        };
        let requested_item_padded_len = requested_attribute.item_padded_len;
        let mso_payload_len = u16::try_from(statement.mso_payload_len)
            .map_err(|_| Error::Prove("TS13 MSO payload length is out of range".to_string()))?;
        if !crate::ts13::ts13_requested_item_padded_len_is_supported(requested_item_padded_len) {
            return Err(Error::Prove(
                "TS13 requested item padded length is unsupported".to_string(),
            ));
        }
        Ok(Self {
            doctype: statement.doctype.clone(),
            namespace: statement.namespace.clone(),
            issuer: MdocMlDsaPublicAuthInput::from_circuit(&statement.issuer_input, false)
                .map_err(Error::Prove)?,
            device: MdocMlDsaPublicAuthInput::from_circuit(&statement.device_input, true)
                .map_err(Error::Prove)?,
            revocation,
            mso_payload_len,
            requested_item_padded_len,
            attributes: statement
                .attributes
                .iter()
                .map(|attribute| MdocRequestedAttribute {
                    element_identifier: attribute.element_identifier.clone(),
                    mode: attribute.mode.clone(),
                })
                .collect(),
            policy: statement.policy.clone(),
        })
    }

    fn verifier_circuit_statement(&self) -> Result<MdocCircuitStatement, Error> {
        validate_mdoc_ts13_public_statement_shape(self, "verify")?;
        if !self.issuer.message.is_empty() {
            return Err(Error::Verify(
                "TS13 public statement contains private issuer-message bytes".to_string(),
            ));
        }
        if !crate::ts13::ts13_requested_item_padded_len_is_supported(self.requested_item_padded_len)
        {
            return Err(Error::Verify(
                "TS13 requested item padded length is unsupported".to_string(),
            ));
        }
        let attributes = self
            .attributes
            .iter()
            .map(|attribute| MdocStatementAttribute {
                element_identifier: attribute.element_identifier.clone(),
                mode: attribute.mode.clone(),
                item_padded_len: self.requested_item_padded_len,
            })
            .collect();
        Ok(MdocCircuitStatement {
            doctype: self.doctype.clone(),
            namespace: self.namespace.clone(),
            issuer_input: self.issuer.verifier_input("issuer", false)?,
            device_input: self.device.verifier_input("device", true)?,
            ts13_revocation: Some(self.revocation.clone()),
            ts13_revocation_range: None,
            ts13_revocation_signature: None,
            attributes,
            mso_payload_len: usize::from(self.mso_payload_len),
            policy: self.policy.clone(),
        })
    }
}

pub const TS13_DEMO_ISSUER_MESSAGE_BYTES: usize = 2_534;
pub const TS13_DEMO_MSO_PAYLOAD_BYTES: usize = 2_513;
pub const TS13_DEMO_ITEM_PADDED_BYTES: u16 = 128;
pub const TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY: usize =
    stwo_mldsa::statement::DEVICE_SIG_STRUCTURE_CAPACITY;

/// Verifier-authoritative circuit inputs for the unlinkable TS13 demo.
///
/// Credential-selected lengths and the device key are intentionally absent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MdocTs13DemoCircuitPublicInput {
    pub circuit_hash: [u8; 32],
    pub request_context_digest: [u8; 32],
    pub timestamp_epoch_seconds: i64,
    pub verification_timestamp_rfc3339_utc:
        [u8; TS13_DEMO_VERIFICATION_TIMESTAMP_RFC3339_UTC_BYTES],
    pub trusted_issuer_public_key: Vec<u8>,
    pub device_cose_sig_structure: Vec<u8>,
    pub revocation: MdocRevocationPublicInputs,
}

impl MdocTs13DemoCircuitPublicInput {
    fn context_bind(&self) -> Ts13PublicContextBindV1 {
        Ts13PublicContextBindV1::new(self.request_context_digest, self.circuit_hash)
    }

    pub(crate) fn policy(&self) -> Result<Policy, Error> {
        Ok(Policy {
            current_date: utc_date_from_epoch_seconds(self.timestamp_epoch_seconds)?,
            min_age_years: 18,
            accepted_nationalities: Vec::new(),
        })
    }

    fn verifier_statement(&self) -> Result<MdocCircuitStatement, Error> {
        if self.trusted_issuer_public_key.len() != stwo_mldsa::constants::PK_BYTES {
            return Err(Error::Verify(
                "TS13 trusted issuer public key has the wrong length".to_string(),
            ));
        }
        if self.device_cose_sig_structure.len() > TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY {
            return Err(Error::Verify(
                "TS13 device Sig_structure exceeds the fixed capacity".to_string(),
            ));
        }
        let issuer = MdocMlDsaPublicAuthInput {
            public_key: self.trusted_issuer_public_key.clone(),
            message_len: TS13_DEMO_ISSUER_MESSAGE_BYTES as u16,
            message: Vec::new(),
        }
        .verifier_input("issuer", false)?;
        Ok(MdocCircuitStatement {
            doctype: PID_DOCTYPE.to_string(),
            namespace: PID_NAMESPACE.to_string(),
            issuer_input: issuer,
            device_input: MdocAuthInput::MlDsaPrivateKey(MlDsaPrivateKeyPublicInput {
                message: self.device_cose_sig_structure.clone(),
            }),
            ts13_revocation: Some(self.revocation.clone()),
            ts13_revocation_range: None,
            ts13_revocation_signature: None,
            attributes: vec![MdocStatementAttribute {
                element_identifier: "age_over_18".to_string(),
                mode: MdocDisclosureMode::ValueEquality(vec![0xf5]),
                item_padded_len: TS13_DEMO_ITEM_PADDED_BYTES,
            }],
            mso_payload_len: TS13_DEMO_MSO_PAYLOAD_BYTES,
            policy: self.policy()?,
        })
    }
}

fn utc_date_from_epoch_seconds(timestamp: i64) -> Result<predicates::Date, Error> {
    if timestamp < 0 {
        return Err(Error::Verify(
            "TS13 verification timestamp is outside the supported range".to_string(),
        ));
    }
    let days = timestamp / 86_400;
    // Howard Hinnant's civil-from-days transform, with day zero at 1970-01-01.
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let day_of_era = z - era * 146_097;
    let year_of_era =
        (day_of_era - day_of_era / 1_460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
    let mut year = year_of_era + era * 400;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let month_prime = (5 * day_of_year + 2) / 153;
    let day = day_of_year - (153 * month_prime + 2) / 5 + 1;
    let month = month_prime + if month_prime < 10 { 3 } else { -9 };
    year += i64::from(month <= 2);
    if !(2020..=2099).contains(&year) {
        return Err(Error::Verify(
            "TS13 verification timestamp is outside years 2020..=2099".to_string(),
        ));
    }
    Ok(predicates::Date {
        year: year as u32,
        month: month as u32,
        day: day as u32,
    })
}

impl MdocCircuitStatement {
    /// Position of the age predicate in the ordered public attribute modes.
    pub fn age_attribute_index(&self) -> Option<usize> {
        self.attributes
            .iter()
            .position(|attribute| matches!(attribute.mode, MdocDisclosureMode::AgeOver))
    }

    /// Position of the nationality predicate in the ordered public attribute modes.
    pub fn nationality_attribute_index(&self) -> Option<usize> {
        self.attributes
            .iter()
            .position(|attribute| matches!(attribute.mode, MdocDisclosureMode::Alpha2Set))
    }

    pub fn with_ts13_revocation(mut self, revocation: MdocRevocationPublicInputs) -> Self {
        self.ts13_revocation = Some(revocation);
        self
    }

    pub fn with_ts13_revocation_range(mut self, range: MdocRevocationRangeWitness) -> Self {
        self.ts13_revocation_range = Some(range);
        self
    }

    pub fn with_ts13_revocation_signature(mut self, signature: MdocRevocationSignature) -> Self {
        self.ts13_revocation_signature = Some(signature);
        self
    }

    /// The only verifier-safe view of a proving statement. The issuer message
    /// and every existential ML-DSA witness are zero-projected while retaining
    /// their public lengths and public keys. Credential item/MSO contents are
    /// absent from the statement type itself.
    pub fn into_public_view(mut self) -> Self {
        let scrub_signature_witness = |input: &mut MdocAuthInput, private_message: bool| {
            if let MdocAuthInput::MlDsa(input) = input {
                input.tr = [0; 64];
                input.c_tilde = [0; stwo_mldsa::constants::C_TILDE_BYTES];
                input.z = [[0; stwo_mldsa::constants::N]; stwo_mldsa::constants::L];
                input.hint = [[0; stwo_mldsa::constants::N]; stwo_mldsa::constants::K];
                if private_message {
                    input.message.fill(0);
                }
            }
        };
        // The issuer Sig_structure is a Phase-1 private-message witness.
        // DeviceAuthentication remains verifier-selected public input, but
        // neither role's existential signature witness belongs in the wire
        // statement.
        scrub_signature_witness(&mut self.issuer_input, true);
        scrub_signature_witness(&mut self.device_input, false);
        self.ts13_revocation_range = None;
        self.ts13_revocation_signature = None;
        self
    }

    pub fn from_extracted(extracted: &ExtractedPidMdoc, policy: Policy) -> Result<Self, MdocError> {
        validate_requested_attributes(&extracted.attributes)?;
        let current_date = policy_date_tuple(&policy)?;
        if current_date < extracted.valid_from {
            return Err(MdocError::CredentialNotYetValid);
        }
        if current_date > extracted.valid_until {
            return Err(MdocError::CredentialExpired);
        }

        let mso = parse_mso(&extracted.mso, &extracted.namespace)?;
        if !is_supported_mdoc_profile_version(&mso.version) {
            return Err(MdocError::UnsupportedMsoVersion(mso.version));
        }
        if mso.doc_type != extracted.doctype {
            return Err(MdocError::DoctypeMismatch);
        }
        let mut statement_attributes = Vec::with_capacity(extracted.extracted_attributes.len());
        for attribute in &extracted.extracted_attributes {
            let item_padded_len =
                u16::try_from(stwo_sha256::native::pad_message(&attribute.item).len())
                    .map_err(|_| MdocError::UnsupportedCircuitValue("attribute padded length"))?;
            if !crate::mdoc_private_item_bind::MDOC_PRIVATE_ITEM_PADDED_BUCKETS
                .contains(&item_padded_len)
            {
                return Err(MdocError::UnsupportedCircuitValue(
                    "attribute padded length bucket",
                ));
            }
            statement_attributes.push(MdocStatementAttribute {
                element_identifier: attribute.request.element_identifier.clone(),
                mode: attribute.request.mode.clone(),
                item_padded_len,
            });
        }
        Ok(Self {
            doctype: extracted.doctype.clone(),
            namespace: extracted.namespace.clone(),
            issuer_input: extracted.issuer_auth_input.clone(),
            device_input: extracted.device_auth_input.clone(),
            ts13_revocation: None,
            ts13_revocation_range: None,
            ts13_revocation_signature: None,
            attributes: statement_attributes,
            mso_payload_len: extracted.mso.len(),
            policy,
        })
    }
}

fn ensure_value_window_with_message(
    item: &[u8],
    offset: usize,
    expected: &[u8],
    mismatch_message: &'static str,
) -> Result<(), MdocError> {
    let end = offset
        .checked_add(expected.len())
        .ok_or(MdocError::UnsupportedCircuitValue(mismatch_message))?;
    if item.get(offset..end) != Some(expected) {
        return Err(MdocError::UnsupportedCircuitValue(mismatch_message));
    }
    Ok(())
}

fn policy_date_tuple(policy: &Policy) -> Result<(u16, u8, u8), MdocError> {
    if policy.current_date.year > 9999 {
        return Err(MdocError::InvalidTdate("policy.current_date"));
    }
    Ok((
        u16::try_from(policy.current_date.year)
            .map_err(|_| MdocError::InvalidTdate("policy.current_date"))?,
        u8::try_from(policy.current_date.month)
            .map_err(|_| MdocError::InvalidTdate("policy.current_date"))?,
        u8::try_from(policy.current_date.day)
            .map_err(|_| MdocError::InvalidTdate("policy.current_date"))?,
    ))
}

/// The public claim tree of a hosted in-circuit ML-DSA-65 statement instance —
/// one per role (issuer / device / revocation) — mirroring
/// `stwo_mldsa::statement::MlDsaProof` minus the STARK, which lives in the
/// shared `MdocCircuitProof::stark_proof`.
///
/// Fields are `pub` so negative tests (role-replay claim swaps) can exercise
/// the verifier's rejection paths; soundness never rests on their integrity —
/// the per-role instance namespace is mixed into the transcript, so a claim
/// tree presented in the wrong role slot fails verification.
#[derive(Clone, Serialize, Deserialize)]
pub struct MdocMlDsaClaims {
    pub group_evals: Vec<QM31>,
    pub claimed_sums: Vec<QM31>,
}

impl MdocMlDsaClaims {
    fn from_prover(prover: &MlDsaStatementProver) -> Self {
        Self {
            group_evals: prover.group_evals().to_vec(),
            claimed_sums: prover.claimed_sums(),
        }
    }

    /// Shape-gate BEFORE `Claims::from_flat`: a short vector would panic
    /// inside claim-tree construction (outside the verify catch_unwind),
    /// turning a malformed proof into a crash.
    fn has_expected_shape(&self, public_message: bool) -> bool {
        let expected_claimed_sums = if public_message {
            stwo_mldsa::statement::hosted_public_claimed_sums_len()
        } else {
            stwo_mldsa::statement::hosted_claimed_sums_len()
        };
        self.group_evals.len() == stwo_mldsa::statement::n_group_evals()
            && self.claimed_sums.len() == expected_claimed_sums
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct MdocCircuitProof {
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
    sha_tables_interaction_claim: ShaTablesInteractionClaim,
    pub mldsa: Option<MdocMlDsaClaims>,
    pub device_mldsa: Option<MdocMlDsaClaims>,
    pub revocation_mldsa: Option<MdocMlDsaClaims>,
    pub(crate) mldsa_range_table_claimed_sum: Option<QM31>,
    pub keccak_service_claimed_sums: Option<Vec<QM31>>,
    private_issuer_message_interaction_claim: MdocPrivateMessageInteractionClaim,
    merged_sha_log_n_rows: Option<u32>,
    merged_sha_slot_log: Option<u32>,
    attribute_sha_interaction_claims: Vec<Sha256InteractionClaim>,
    mso_sha_interaction_claim: Option<Sha256InteractionClaim>,
    private_mso_bind_interaction_claim: MdocPrivateMsoInteractionClaim,
    country_code_table_claimed_sum: Option<QM31>,
    private_item_interaction_claims: Vec<MdocPrivateItemInteractionClaim>,
    value_digests_scan_interaction_claim: MdocValueDigestsInteractionClaim,
    mdoc_window_bind_interaction_claim: Option<MdocWindowBindInteractionClaim>,
    mdoc_cbor_interaction_claims: Vec<MdocCborStreamInteractionClaim>,
    ts13_expand_a_claim: Option<ExpandAClaim>,
    ts13_device_key_bind_interaction_claim: Option<MdocPrivateDeviceKeyInteractionClaim>,
    ts13_mso_validity_interaction_claim: Option<MdocPrivateMsoValidityInteractionClaim>,
    ts13_revocation_range_interaction_claim: Option<MdocRevocationRangeInteractionClaim>,
    age_public: Option<predicates::PublicInput>,
    age_claimed_sums: Option<Vec<QM31>>,
    nat_public: Option<predicates::NatPublicInput>,
    nat_claimed_sums: Option<Vec<QM31>>,
    /// Opaque post-interaction payloads; production carries the Keccak
    /// service's round-GKR proof in its module slot.
    pub post_interaction_payloads: Vec<Vec<u8>>,
    /// Prover-side executable geometry for artifact drift tests. It is never
    /// serialized into the proof and is absent after V4 decoding.
    #[serde(skip, default)]
    ts13_demo_circuit_geometry: Option<MdocTs13DemoCircuitGeometry>,
}

impl MdocCircuitProof {
    /// Public shape view for profile verifiers.  The schedule is part of the
    /// transcript and determines tree-0 preprocessing, so callers that pin a
    /// profile must reject a proof before constructing its tree when this is
    /// absent or outside that profile's resource contract.
    pub fn merged_sha_layout(&self) -> Option<(u32, u32)> {
        self.merged_sha_slot_log.zip(self.merged_sha_log_n_rows)
    }

    /// True only when the proof carries the three ML-DSA role claim trees and
    /// the TS13 range claim required by the fully-PQ revocation profile.
    pub fn has_ts13_mldsa_shape(&self) -> bool {
        self.mldsa
            .as_ref()
            .is_some_and(|claims| claims.has_expected_shape(false))
            && self
                .device_mldsa
                .as_ref()
                .is_some_and(|claims| claims.has_expected_shape(true))
            && self
                .revocation_mldsa
                .as_ref()
                .is_some_and(|claims| claims.has_expected_shape(false))
            && self.ts13_revocation_range_interaction_claim.is_some()
            && self.mso_sha_interaction_claim.is_some()
            && self.country_code_table_claimed_sum.is_none()
            && self.attribute_sha_interaction_claims.len() == 1
            && self.private_item_interaction_claims.len() == 1
            && self.mdoc_cbor_interaction_claims.len() == 2
            && self.mldsa_range_table_claimed_sum.is_some()
            && self
                .keccak_service_claimed_sums
                .as_ref()
                .is_some_and(|sums| {
                    sums.len() == stwo_mldsa::stwo_keccak::service::service_claimed_sums_len()
                })
    }

    pub fn has_ts13_demo_shape(&self) -> bool {
        use crate::ts13_demo_artifact_constants::{
            TS13_DEMO_FRI_FIRST_HASH_CAP, TS13_DEMO_FRI_FIRST_WITNESS_CAP,
            TS13_DEMO_FRI_INNER_HASH_CAPS, TS13_DEMO_FRI_INNER_WITNESS_CAPS,
            TS13_DEMO_FRI_LAST_LAYER_COEFFICIENT_COUNT, TS13_DEMO_POST_INTERACTION_PAYLOAD_COUNT,
            TS13_DEMO_QUERY_COUNT, TS13_DEMO_SAMPLED_VALUE_LENGTH_HISTOGRAMS,
            TS13_DEMO_TREE_COLUMN_COUNTS, TS13_DEMO_TREE_MERKLE_HASH_CAPS,
        };

        fn length_histogram_matches<T>(columns: &[Vec<T>], expected: &[(usize, usize)]) -> bool {
            expected.iter().map(|(_, count)| count).sum::<usize>() == columns.len()
                && expected.iter().all(|&(length, expected_count)| {
                    columns
                        .iter()
                        .filter(|column| column.len() == length)
                        .count()
                        == expected_count
                })
        }

        let stark = &self.stark_proof.0;
        self.merged_sha_layout() == Some((8, 8))
            && stark.config == mdoc_production_pcs_config()
            && stark.commitments.len() == TS13_DEMO_TREE_COLUMN_COUNTS.len()
            && stark.sampled_values.len() == TS13_DEMO_TREE_COLUMN_COUNTS.len()
            && stark
                .sampled_values
                .iter()
                .zip(TS13_DEMO_SAMPLED_VALUE_LENGTH_HISTOGRAMS)
                .all(|(columns, histogram)| length_histogram_matches(columns, histogram))
            && stark.decommitments.len() == TS13_DEMO_TREE_COLUMN_COUNTS.len()
            && stark
                .decommitments
                .iter()
                .zip(TS13_DEMO_TREE_MERKLE_HASH_CAPS)
                .all(|(decommitment, cap)| decommitment.hash_witness.len() <= cap)
            && stark.queried_values.len() == TS13_DEMO_TREE_COLUMN_COUNTS.len()
            && stark
                .queried_values
                .iter()
                .zip(TS13_DEMO_TREE_COLUMN_COUNTS)
                .all(|(columns, count)| {
                    columns.len() == count
                        && columns
                            .iter()
                            .all(|values| values.len() == TS13_DEMO_QUERY_COUNT)
                })
            && stark.fri_proof.first_layer.fri_witness.len() <= TS13_DEMO_FRI_FIRST_WITNESS_CAP
            && stark.fri_proof.first_layer.decommitment.hash_witness.len()
                <= TS13_DEMO_FRI_FIRST_HASH_CAP
            && stark.fri_proof.inner_layers.len() == TS13_DEMO_FRI_INNER_WITNESS_CAPS.len()
            && stark
                .fri_proof
                .inner_layers
                .iter()
                .zip(TS13_DEMO_FRI_INNER_WITNESS_CAPS)
                .zip(TS13_DEMO_FRI_INNER_HASH_CAPS)
                .all(|((layer, witness_cap), hash_cap)| {
                    layer.fri_witness.len() <= witness_cap
                        && layer.decommitment.hash_witness.len() <= hash_cap
                })
            && stark.fri_proof.last_layer_poly.len() == TS13_DEMO_FRI_LAST_LAYER_COEFFICIENT_COUNT
            && self.post_interaction_payloads.len() == TS13_DEMO_POST_INTERACTION_PAYLOAD_COUNT
            && self
                .post_interaction_payloads
                .iter()
                .enumerate()
                .all(|(index, payload)| {
                    if index == 2 {
                        air_core::gkr::is_ts13_demo_gkr_batch_proof_wire(payload)
                    } else {
                        payload.is_empty()
                    }
                })
            && self.sha_tables_interaction_claim.pairs.len() == 3
            && self
                .attribute_sha_interaction_claims
                .iter()
                .all(|claim| claim.range.is_empty())
            && self
                .mso_sha_interaction_claim
                .as_ref()
                .is_some_and(|claim| claim.range.is_empty())
            && self
                .mldsa
                .as_ref()
                .is_some_and(|claims| claims.has_expected_shape(false))
            && self.device_mldsa.as_ref().is_some_and(|claims| {
                claims.group_evals.len() == stwo_mldsa::statement::n_private_key_group_evals()
                    && claims.claimed_sums.len()
                        == stwo_mldsa::statement::hosted_private_key_claimed_sums_len()
            })
            && self
                .revocation_mldsa
                .as_ref()
                .is_some_and(|claims| claims.has_expected_shape(false))
            && self.ts13_expand_a_claim.is_some()
            && self.ts13_device_key_bind_interaction_claim.is_some()
            && self.ts13_mso_validity_interaction_claim.is_some()
            && self.ts13_revocation_range_interaction_claim.is_some()
            && self.mso_sha_interaction_claim.is_some()
            && self.country_code_table_claimed_sum.is_none()
            && self.attribute_sha_interaction_claims.len() == 1
            && self.private_item_interaction_claims.len() == 1
            && self.mdoc_cbor_interaction_claims.len() == 2
            && self.mdoc_window_bind_interaction_claim.is_none()
            && self.age_public.is_none()
            && self.age_claimed_sums.is_none()
            && self.nat_public.is_none()
            && self.nat_claimed_sums.is_none()
            && self.mldsa_range_table_claimed_sum.is_some()
            && self
                .keccak_service_claimed_sums
                .as_ref()
                .is_some_and(|sums| {
                    sums.len() == stwo_mldsa::stwo_keccak::service::service_claimed_sums_len()
                })
    }

    #[doc(hidden)]
    pub fn ts13_demo_circuit_geometry(&self) -> Option<&MdocTs13DemoCircuitGeometry> {
        self.ts13_demo_circuit_geometry.as_ref()
    }

    #[doc(hidden)]
    pub fn clear_mldsa_range_table_claimed_sum_for_test(&mut self) {
        self.mldsa_range_table_claimed_sum = None;
    }

    #[doc(hidden)]
    pub fn mldsa_range_table_claimed_sum_mut_for_test(&mut self) -> Option<&mut QM31> {
        self.mldsa_range_table_claimed_sum.as_mut()
    }

    #[doc(hidden)]
    pub fn ts13_expand_a_claim_mut_for_test(&mut self) -> Option<&mut ExpandAClaim> {
        self.ts13_expand_a_claim.as_mut()
    }

    #[doc(hidden)]
    pub fn tamper_ts13_device_key_bind_claimed_sum_for_test(&mut self) -> bool {
        let Some(claim) = self.ts13_device_key_bind_interaction_claim.as_mut() else {
            return false;
        };
        claim.claimed_sum += QM31::from(M31::from_u32_unchecked(1));
        true
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MdocCircuitProveProfile {
    pub total: Duration,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MdocCircuitVerifyProfile {
    pub total: Duration,
    pub tree0_canonical_root: Duration,
    pub stark_verify: Duration,
    pub tree0_cache_hit: bool,
}

#[cfg(feature = "unlink-spikes")]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct MdocUnlinkSpikeConfig {
    dummy_keccak_jobs: usize,
}

#[cfg(feature = "unlink-spikes")]
const UNLINK_SPIKE_DUMMY_JOB_COUNTS: [usize; 3] = [0, 13, 33];

#[cfg(feature = "unlink-spikes")]
fn validate_unlink_spike_dummy_jobs(dummy_keccak_jobs: usize, context: &str) -> Result<(), Error> {
    if UNLINK_SPIKE_DUMMY_JOB_COUNTS.contains(&dummy_keccak_jobs) {
        Ok(())
    } else {
        Err(match context {
            "prove" => Error::Prove(format!(
                "unlinkability Keccak spike dummy job count must be one of {:?}, got {dummy_keccak_jobs}",
                UNLINK_SPIKE_DUMMY_JOB_COUNTS
            )),
            _ => Error::Verify(format!(
                "unlinkability Keccak spike dummy job count must be one of {:?}, got {dummy_keccak_jobs}",
                UNLINK_SPIKE_DUMMY_JOB_COUNTS
            )),
        })
    }
}

#[derive(Clone, Debug, Serialize)]
struct MdocTree0AttributeKey {
    mode: u8,
    element_identifier: Vec<u8>,
    equality_value: Vec<u8>,
    item_padded_len: u16,
}

/// Exact verifier-known determinants of the canonical tree-0 construction.
///
/// The key contains: PCS blowup; merged-SHA slot/row logs; optional revocation
/// module presence; optional country-table presence; ordered attribute
/// modes, identifiers, equality constants, and padded buckets; normalized
/// age/nationality public tables; docType length; and issuer/device public
/// message lengths. Fixed protocol tables, role namespaces, scanner geometry,
/// and the now-constant five-block SIB rail need no key fields.
///
/// The merged-SHA layout fields originate in the proof, but are shape-gated
/// before this key is built and were already used to reconstruct that verifier
/// module before Q13. They do not authorize a root or widen verifier trust.
/// Every stored value is a verifier-recomputed canonical root; an accidentally
/// omitted determinant therefore causes a fail-closed wrong-root rejection
/// (and is caught by the fresh-audit test), never acceptance of a proof root.
/// Signature bytes, keys, public message *contents*, private revocation
/// bounds, claimed sums, and commitments are deliberately absent: none
/// determines preprocessing. The issuer/device public message lengths are
/// included because hosted ML-DSA bridge/sink schedules depend on them.
#[derive(Clone, Debug, Serialize)]
struct MdocTree0CacheKeyMaterial {
    version: u8,
    pcs_log_blowup_factor: u32,
    merged_sha_slot_log: u32,
    merged_sha_log_n_rows: u32,
    has_ts13_revocation: bool,
    has_country_table: bool,
    doctype_len: usize,
    namespace: Vec<u8>,
    issuer_mldsa_message_bytes: usize,
    issuer_mso_payload_bytes: usize,
    device_mldsa_message_bytes: usize,
    attributes: Vec<MdocTree0AttributeKey>,
    age_public: Option<predicates::PublicInput>,
    nat_public: Option<predicates::NatPublicInput>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct MdocTree0CacheKey {
    digest: [u8; 32],
    /// Retaining the bounded, non-secret material makes digest collisions a
    /// cache miss rather than a soundness event.
    material: Vec<u8>,
}

type MdocTree0Root = air_core::CommitmentRoot;
type MdocTree0RootCache = VecDeque<(MdocTree0CacheKey, MdocTree0Root)>;

static MDOC_TREE0_ROOT_CACHE: OnceLock<Mutex<MdocTree0RootCache>> = OnceLock::new();

fn serialize_mdoc_tree0_cache_key_material(
    material: &MdocTree0CacheKeyMaterial,
    #[cfg(feature = "unlink-spikes")] unlink_spike: MdocUnlinkSpikeConfig,
) -> Result<Vec<u8>, Error> {
    let encoded = bincode::serialize(material)
        .map_err(|error| Error::Verify(format!("mdoc tree-0 cache key: {error}")))?;
    #[cfg(feature = "unlink-spikes")]
    let mut encoded = encoded;
    #[cfg(feature = "unlink-spikes")]
    if unlink_spike != MdocUnlinkSpikeConfig::default() {
        const SPIKE_CACHE_KEY_DOMAIN: &[u8] = b"eu-id/unlink-spike/tree0/v1";
        encoded.extend_from_slice(SPIKE_CACHE_KEY_DOMAIN);
        encoded.extend_from_slice(&(unlink_spike.dummy_keccak_jobs as u64).to_le_bytes());
    }
    Ok(encoded)
}

fn mdoc_tree0_cache_key(
    proof: &MdocCircuitProof,
    statement: &MdocCircuitStatement,
    expected_pcs_config: PcsConfig,
    #[cfg(feature = "unlink-spikes")] unlink_spike: MdocUnlinkSpikeConfig,
) -> Result<MdocTree0CacheKey, Error> {
    let issuer_mldsa_message_bytes = statement
        .issuer_input
        .as_mldsa()
        .ok_or_else(|| {
            Error::Verify("mdoc tree-0 cache key issuer input is not ML-DSA".to_string())
        })?
        .message
        .len();
    let private_device_key = statement.device_input.private_key_public_input().is_some();
    let device_mldsa_message_bytes = if private_device_key {
        TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY
    } else {
        statement.device_input.message().len()
    };
    let attributes = statement
        .attributes
        .iter()
        .map(|attribute| {
            let (mode, equality_value) = match &attribute.mode {
                MdocDisclosureMode::ValueEquality(value) => (0, value.clone()),
                MdocDisclosureMode::AgeOver => (1, Vec::new()),
                MdocDisclosureMode::Alpha2Set => (2, Vec::new()),
            };
            MdocTree0AttributeKey {
                mode,
                element_identifier: attribute.element_identifier.as_bytes().to_vec(),
                equality_value,
                item_padded_len: attribute.item_padded_len,
            }
        })
        .collect();
    let material = MdocTree0CacheKeyMaterial {
        version: if private_device_key { 6 } else { 5 },
        pcs_log_blowup_factor: expected_pcs_config.fri_config.log_blowup_factor,
        merged_sha_slot_log: proof
            .merged_sha_slot_log
            .expect("merged SHA slot log shape-gated before cache-key construction"),
        merged_sha_log_n_rows: proof
            .merged_sha_log_n_rows
            .expect("merged SHA row log shape-gated before cache-key construction"),
        has_ts13_revocation: validate_ts13_revocation_shape(statement, false, "verify")?,
        has_country_table: statement.nationality_attribute_index().is_some(),
        doctype_len: statement.doctype.len(),
        namespace: statement.namespace.as_bytes().to_vec(),
        issuer_mldsa_message_bytes,
        issuer_mso_payload_bytes: statement.mso_payload_len,
        device_mldsa_message_bytes,
        attributes,
        age_public: statement
            .age_attribute_index()
            .map(|_| statement.policy.age_public_input()),
        nat_public: statement
            .nationality_attribute_index()
            .map(|_| nat_public_input_for(statement)),
    };
    let material = serialize_mdoc_tree0_cache_key_material(
        &material,
        #[cfg(feature = "unlink-spikes")]
        unlink_spike,
    )?;
    Ok(MdocTree0CacheKey {
        digest: Sha256::digest(&material).into(),
        material,
    })
}

fn mdoc_tree0_cached_root(key: &MdocTree0CacheKey) -> Result<Option<MdocTree0Root>, Error> {
    let cache = MDOC_TREE0_ROOT_CACHE.get_or_init(|| Mutex::new(VecDeque::new()));
    let mut entries = cache
        .lock()
        .map_err(|_| Error::Verify("mdoc tree-0 cache lock poisoned".to_string()))?;
    let Some(index) = entries.iter().position(|(candidate, _)| {
        candidate.digest == key.digest && candidate.material == key.material
    }) else {
        return Ok(None);
    };
    let entry = entries
        .remove(index)
        .expect("cache index came from the same deque");
    let root = entry.1;
    entries.push_back(entry);
    Ok(Some(root))
}

fn mdoc_tree0_cache_insert(key: MdocTree0CacheKey, root: MdocTree0Root) -> Result<(), Error> {
    let cache = MDOC_TREE0_ROOT_CACHE.get_or_init(|| Mutex::new(VecDeque::new()));
    let mut entries = cache
        .lock()
        .map_err(|_| Error::Verify("mdoc tree-0 cache lock poisoned".to_string()))?;
    if let Some(index) = entries.iter().position(|(candidate, _)| {
        candidate.digest == key.digest && candidate.material == key.material
    }) {
        entries.remove(index);
    }
    if entries.len() == MDOC_TREE0_ROOT_CACHE_CAPACITY {
        entries.pop_front();
    }
    entries.push_back((key, root));
    Ok(())
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MdocProofByteBreakdown {
    pub proof_bytes: usize,
    pub stark_proof_bytes: usize,
    /// Everything serialized outside `stark_proof`, including metadata and
    /// post-interaction payloads.
    pub outer_proof_bytes: usize,
    /// Auxiliary post-interaction payloads, including the ML-DSA round-GKR
    /// proof. This is a subset of `outer_proof_bytes`.
    pub post_interaction_payload_bytes: usize,
    pub stark: MdocStarkProofByteBreakdown,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MdocStarkProofByteBreakdown {
    pub config: usize,
    pub commitments: usize,
    pub sampled_values: usize,
    pub decommitments: usize,
    pub queried_values: usize,
    pub proof_of_work: usize,
    pub fri_proof: usize,
}

/// Executable serialization/claim geometry extracted from a real TS13 demo
/// proof. The circuit-artifact drift test compares this view with the
/// generated manifest; it is not part of the verifier's public statement.
#[doc(hidden)]
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocTs13DemoProofShape {
    pub proof_bytes: usize,
    pub stark_proof_bytes: usize,
    pub outer_claims_and_framing_bytes: usize,
    pub commitment_count: usize,
    pub tree_zero_root: Option<[u8; 32]>,
    pub sampled_values: Vec<Vec<usize>>,
    pub decommitment_hash_counts: Vec<usize>,
    pub queried_values: Vec<Vec<usize>>,
    pub fri_first_layer_witness_count: usize,
    pub fri_first_layer_hash_count: usize,
    pub fri_inner_layers: Vec<MdocFriLayerShape>,
    pub fri_last_layer_coefficient_count: usize,
    pub post_interaction_payload_bytes: Vec<usize>,
    pub sha_table_pair_claim_count: usize,
    pub attribute_sha_range_claim_counts: Vec<usize>,
    pub mso_sha_range_claim_count: Option<usize>,
    pub issuer_mldsa_group_eval_count: Option<usize>,
    pub issuer_mldsa_claimed_sum_count: Option<usize>,
    pub device_mldsa_group_eval_count: Option<usize>,
    pub device_mldsa_claimed_sum_count: Option<usize>,
    pub revocation_mldsa_group_eval_count: Option<usize>,
    pub revocation_mldsa_claimed_sum_count: Option<usize>,
    pub keccak_service_claimed_sum_count: Option<usize>,
    pub private_item_claim_count: usize,
    pub cbor_parser_claim_count: usize,
    pub merged_sha_layout: Option<(u32, u32)>,
}

#[doc(hidden)]
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocFriLayerShape {
    pub witness_count: usize,
    pub hash_count: usize,
}

/// Exact prover-constructed Air/component geometry. This metadata is retained
/// only in memory for circuit-artifact generation and drift tests.
#[doc(hidden)]
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocTs13DemoCircuitGeometry {
    pub committed_preprocessed_ids: Vec<String>,
    pub committed_preprocessed_log_sizes: Vec<u32>,
    pub air_instances: Vec<MdocAirInstanceGeometry>,
}

#[doc(hidden)]
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocAirInstanceGeometry {
    pub preprocessed_log_sizes: Vec<u32>,
    pub trace_log_sizes: Vec<u32>,
    pub interaction_log_sizes: Vec<u32>,
    pub post_interaction_log_sizes: Vec<u32>,
    pub max_log_size: u32,
    pub max_constraint_log_degree_bound: u32,
    pub components: Vec<MdocComponentGeometry>,
}

#[doc(hidden)]
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MdocComponentGeometry {
    pub trace_rows: u32,
    pub active_rows: u32,
    pub constraint_count: usize,
    pub max_constraint_log_degree_bound: u32,
    pub trace_log_degree_bounds: Vec<Vec<u32>>,
}

fn capture_ts13_demo_circuit_geometry(
    modules: &[&mut dyn AirProver],
) -> MdocTs13DemoCircuitGeometry {
    const TS13_DEMO_U9_PHYSICAL_AIR_ORDINAL: usize = 15;
    const TS13_DEMO_U9_MAIN_COMPONENT_ORDINAL: usize = 0;

    let mut seen_preprocessed_ids = HashSet::new();
    let mut committed_preprocessed_ids = Vec::new();
    let mut committed_preprocessed_log_sizes = Vec::new();
    for module in modules {
        let ids = module.preprocessed_column_ids();
        let log_sizes = module.layout().preprocessed;
        assert_eq!(
            ids.len(),
            log_sizes.len(),
            "preprocessed ids and layout differ during TS13 artifact capture"
        );
        for (id, log_size) in ids.into_iter().zip(log_sizes) {
            let id_name = format!("{id:?}");
            if seen_preprocessed_ids.insert(id) {
                committed_preprocessed_ids.push(id_name);
                committed_preprocessed_log_sizes.push(log_size);
            }
        }
    }

    MdocTs13DemoCircuitGeometry {
        committed_preprocessed_ids,
        committed_preprocessed_log_sizes,
        air_instances: modules
            .iter()
            .enumerate()
            .map(|(air_ordinal, module)| {
                let layout = module.layout();
                MdocAirInstanceGeometry {
                    preprocessed_log_sizes: layout.preprocessed,
                    trace_log_sizes: layout.trace,
                    interaction_log_sizes: layout.interaction,
                    post_interaction_log_sizes: module.post_interaction_log_sizes(),
                    max_log_size: module.max_log_size(),
                    max_constraint_log_degree_bound: module.max_constraint_log_degree_bound(),
                    components: module
                        .components()
                        .into_iter()
                        .enumerate()
                        .map(|(component_ordinal, component)| {
                            let trace_log_degree_bounds = component
                                .trace_log_degree_bounds()
                                .iter()
                                .cloned()
                                .collect::<Vec<_>>();
                            let trace_rows = trace_log_degree_bounds
                                .iter()
                                .flatten()
                                .copied()
                                .max()
                                .and_then(|log_size| 1_u32.checked_shl(log_size))
                                .expect("TS13 component has a supported non-empty trace layout");
                            MdocComponentGeometry {
                                trace_rows,
                                active_rows: if air_ordinal == TS13_DEMO_U9_PHYSICAL_AIR_ORDINAL
                                    && component_ordinal == TS13_DEMO_U9_MAIN_COMPONENT_ORDINAL
                                {
                                    MDOC_PRIVATE_DEVICE_KEY_ACTIVE_ROWS as u32
                                } else {
                                    trace_rows
                                },
                                constraint_count: component.n_constraints(),
                                max_constraint_log_degree_bound: component
                                    .max_constraint_log_degree_bound(),
                                trace_log_degree_bounds,
                            }
                        })
                        .collect(),
                }
            })
            .collect(),
    }
}

impl MdocCircuitProof {
    /// Return the live, proof-carried shape needed by the deterministic
    /// artifact audit without exposing any private witness value.
    #[doc(hidden)]
    pub fn ts13_demo_proof_shape(&self) -> MdocTs13DemoProofShape {
        let stark = &self.stark_proof.0;
        let mldsa_shape = |claims: &Option<MdocMlDsaClaims>| {
            claims
                .as_ref()
                .map(|claims| (claims.group_evals.len(), claims.claimed_sums.len()))
        };
        let issuer = mldsa_shape(&self.mldsa);
        let device = mldsa_shape(&self.device_mldsa);
        let revocation = mldsa_shape(&self.revocation_mldsa);
        let proof_bytes = bincode_len(self);
        let stark_proof_bytes = bincode_len(&self.stark_proof);
        let post_interaction_payload_wire_bytes = 8
            + self.post_interaction_payloads.len() * 8
            + self
                .post_interaction_payloads
                .iter()
                .map(Vec::len)
                .sum::<usize>();
        MdocTs13DemoProofShape {
            proof_bytes,
            stark_proof_bytes,
            outer_claims_and_framing_bytes: proof_bytes
                .checked_sub(stark_proof_bytes + post_interaction_payload_wire_bytes)
                .expect("post payloads are contained in the serialized proof"),
            commitment_count: stark.commitments.len(),
            tree_zero_root: stark.commitments.first().map(|root| root.0),
            sampled_values: stark
                .sampled_values
                .iter()
                .map(|columns| columns.iter().map(Vec::len).collect())
                .collect(),
            decommitment_hash_counts: stark
                .decommitments
                .iter()
                .map(|decommitment| decommitment.hash_witness.len())
                .collect(),
            queried_values: stark
                .queried_values
                .iter()
                .map(|columns| columns.iter().map(Vec::len).collect())
                .collect(),
            fri_first_layer_witness_count: stark.fri_proof.first_layer.fri_witness.len(),
            fri_first_layer_hash_count: stark.fri_proof.first_layer.decommitment.hash_witness.len(),
            fri_inner_layers: stark
                .fri_proof
                .inner_layers
                .iter()
                .map(|layer| MdocFriLayerShape {
                    witness_count: layer.fri_witness.len(),
                    hash_count: layer.decommitment.hash_witness.len(),
                })
                .collect(),
            fri_last_layer_coefficient_count: stark.fri_proof.last_layer_poly.len(),
            post_interaction_payload_bytes: self
                .post_interaction_payloads
                .iter()
                .map(Vec::len)
                .collect(),
            sha_table_pair_claim_count: self.sha_tables_interaction_claim.pairs.len(),
            attribute_sha_range_claim_counts: self
                .attribute_sha_interaction_claims
                .iter()
                .map(|claim| claim.range.len())
                .collect(),
            mso_sha_range_claim_count: self
                .mso_sha_interaction_claim
                .as_ref()
                .map(|claim| claim.range.len()),
            issuer_mldsa_group_eval_count: issuer.map(|shape| shape.0),
            issuer_mldsa_claimed_sum_count: issuer.map(|shape| shape.1),
            device_mldsa_group_eval_count: device.map(|shape| shape.0),
            device_mldsa_claimed_sum_count: device.map(|shape| shape.1),
            revocation_mldsa_group_eval_count: revocation.map(|shape| shape.0),
            revocation_mldsa_claimed_sum_count: revocation.map(|shape| shape.1),
            keccak_service_claimed_sum_count: self
                .keccak_service_claimed_sums
                .as_ref()
                .map(Vec::len),
            private_item_claim_count: self.private_item_interaction_claims.len(),
            cbor_parser_claim_count: self.mdoc_cbor_interaction_claims.len(),
            merged_sha_layout: self.merged_sha_layout(),
        }
    }
}

pub fn mdoc_proof_byte_breakdown(proof: &MdocCircuitProof) -> MdocProofByteBreakdown {
    let stark = &proof.stark_proof.0;
    let proof_bytes = bincode_len(proof);
    let stark_proof_bytes = bincode_len(&proof.stark_proof);
    let outer_proof_bytes = proof_bytes.saturating_sub(stark_proof_bytes);

    MdocProofByteBreakdown {
        proof_bytes,
        stark_proof_bytes,
        outer_proof_bytes,
        post_interaction_payload_bytes: proof.post_interaction_payloads.iter().map(Vec::len).sum(),
        stark: MdocStarkProofByteBreakdown {
            config: bincode_len(&stark.config),
            commitments: bincode_len(&stark.commitments),
            sampled_values: bincode_len(&stark.sampled_values),
            decommitments: bincode_len(&stark.decommitments),
            queried_values: bincode_len(&stark.queried_values),
            proof_of_work: bincode_len(&stark.proof_of_work),
            fri_proof: bincode_len(&stark.fri_proof),
        },
    }
}

fn bincode_len<T: Serialize>(value: &T) -> usize {
    bincode::serialize(value)
        .expect("mdoc proof byte breakdown value serializes")
        .len()
}

fn sha_params(bytes: &[u8]) -> (stwo_sha256::types::Sha256Witness, u32) {
    let witness = compute_sha256_witness(bytes);
    let log_n_rows = min_log_size(witness.blocks.len());
    (witness, log_n_rows)
}

fn checked_sha256_padded_len(message_len: usize) -> Option<usize> {
    message_len
        .checked_add(9)?
        .checked_add(stwo_sha256::constants::BLOCK_BYTES - 1)
        .map(|rounded| {
            (rounded / stwo_sha256::constants::BLOCK_BYTES) * stwo_sha256::constants::BLOCK_BYTES
        })
}

fn private_mso_bind_spec(
    statement: &MdocCircuitStatement,
    mso_sha_padded_len: Option<usize>,
    private_device_key: bool,
    phase: &'static str,
) -> Result<MdocPrivateMsoBindSpec, Error> {
    let fail = |message: String| {
        if phase == "prove" {
            Error::Prove(message)
        } else {
            Error::Verify(message)
        }
    };
    let issuer = statement
        .issuer_input
        .as_mldsa()
        .ok_or_else(|| fail("private MSO binder issuer input is not ML-DSA".to_string()))?;
    let device_key_mode = if private_device_key {
        MdocPrivateMsoDeviceKeyMode::Ts13PrivateStart
    } else {
        let device = statement
            .device_input
            .as_mldsa()
            .ok_or_else(|| fail("private MSO binder device input is not ML-DSA".to_string()))?;
        MdocPrivateMsoDeviceKeyMode::LegacyPublicExact(device.encode_pk())
    };
    Ok(MdocPrivateMsoBindSpec {
        issuer_message_len: issuer.message.len(),
        mso_len: statement.mso_payload_len,
        doc_type: statement.doctype.clone(),
        device_key_mode,
        policy_date: statement.policy.current_date,
        sha_stream: mso_sha_padded_len.map(|padded_len| MdocPrivateMsoShaStreamSpec {
            field_id: MDOC_MSO_SHA_STREAM_FIELD_ID,
            padded_len,
        }),
    })
}

struct MdocRevocationPublicBind {
    inputs: MdocRevocationPublicInputs,
}

impl MdocRevocationPublicBind {
    fn new(inputs: MdocRevocationPublicInputs) -> Self {
        Self { inputs }
    }
}

impl Air for MdocRevocationPublicBind {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(0x5453_3133_5245_5601);
        // Keep the role/key-kind discriminant for transcript domain separation.
        match &self.inputs.revocation_public_key {
            MdocRevocationKey::MlDsa(pk) => {
                channel.mix_u64(2);
                for &byte in pk {
                    channel.mix_u64(u64::from(byte));
                }
            }
        }
        channel.mix_u64(u64::from(self.inputs.epoch));
    }

    fn draw_relations(&mut self, _channel: &mut Blake2sChannel) {}

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: Vec::new(),
            trace: Vec::new(),
            interaction: Vec::new(),
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        Vec::new()
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        Vec::new()
    }

    fn build_components(&mut self, _allocator: &mut TraceLocationAllocator) {}

    fn components(&self) -> Vec<&dyn Component> {
        Vec::new()
    }
}

impl AirProver for MdocRevocationPublicBind {
    fn max_log_size(&self) -> u32 {
        0
    }

    fn write_preprocessed(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

    fn write_trace(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

    fn write_interaction(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        Vec::new()
    }
}

const MDOC_REVOCATION_RANGE_LOG_SIZE: u32 = LOG_N_LANES;
const REVOCATION_U64_BYTES: usize = 8;
const REVOCATION_RANGE_BYTE_COLS: usize = 5 * REVOCATION_U64_BYTES;
const REVOCATION_RANGE_CARRY_COLS: usize = 2 * REVOCATION_U64_BYTES;
const REVOCATION_RANGE_DIGEST_TAIL_COLS: usize = 32 - REVOCATION_U64_BYTES;

fn revocation_range_bit_byte_indices() -> std::ops::Range<usize> {
    // The range component provides `id_lo || id_hi || epoch` to the hosted
    // revocation signature leg. Provider-side bytes must remain constrained
    // independently of that external consumer. The private SHA digest relation
    // constrains the leading `id` bytes.
    REVOCATION_U64_BYTES..REVOCATION_RANGE_BYTE_COLS
}

fn revocation_range_bit_cols() -> usize {
    revocation_range_bit_byte_indices().len() * 8
}

type MdocRevocationRangeColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type MdocRevocationRangeComponent = FrameworkComponent<MdocRevocationRangeEval>;

fn revocation_range_trace_cols() -> usize {
    REVOCATION_RANGE_BYTE_COLS
        + revocation_range_bit_cols()
        + REVOCATION_RANGE_CARRY_COLS
        + REVOCATION_RANGE_DIGEST_TAIL_COLS
}

struct MdocRevocationRangeBind {
    witness: Option<MdocRevocationRangeWitness>,
    mso_digest: Option<[u8; 32]>,
    epoch: u32,
    digest_handle: SharedDigestRelation,
    message_field_handle: SharedFieldRelation,
    blinder_relation: Option<ClaimedSumBlinderRelation>,
    interaction_claim: Option<MdocRevocationRangeInteractionClaim>,
    component: Option<MdocRevocationRangeComponent>,
    blinder_component: Option<FrameworkComponent<ClaimedSumBlinderEval>>,
}

#[derive(Clone)]
struct MdocRevocationRangeEval {
    mso_digest_relation: Box<DigestBytesRelation>,
    message_field_relation: FieldBytesRelation,
    epoch: u32,
    blinder_relation: ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct MdocRevocationRangeInteractionClaim {
    claimed_sum: QM31,
    /// Q-015 §4b blinder pair (see `claimed_sum_blinder`).
    blinder_v: QM31,
    blinder_m: QM31,
    blinder_claimed_sum: QM31,
}

impl MdocRevocationRangeBind {
    fn prover(
        witness: MdocRevocationRangeWitness,
        mso_digest: [u8; 32],
        digest_handle: SharedDigestRelation,
        epoch: u32,
        message_field_handle: SharedFieldRelation,
    ) -> Self {
        Self {
            witness: Some(witness),
            mso_digest: Some(mso_digest),
            epoch,
            digest_handle,
            message_field_handle,
            blinder_relation: None,
            interaction_claim: None,
            component: None,
            blinder_component: None,
        }
    }

    fn verifier(
        digest_handle: SharedDigestRelation,
        epoch: u32,
        message_field_handle: SharedFieldRelation,
        interaction_claim: MdocRevocationRangeInteractionClaim,
    ) -> Self {
        Self {
            witness: None,
            mso_digest: None,
            epoch,
            digest_handle,
            message_field_handle,
            blinder_relation: None,
            interaction_claim: Some(interaction_claim),
            component: None,
            blinder_component: None,
        }
    }

    fn mso_digest_relation(&self) -> DigestBytesRelation {
        self.digest_handle.get()
    }

    fn message_relation(&self) -> FieldBytesRelation {
        self.message_field_handle.get()
    }

    fn interaction_claim(&self) -> &MdocRevocationRangeInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("mdoc revocation range interaction claim is set")
    }
}

fn revocation_range_active_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: "mdoc/ts13/revocation_range_active".to_string(),
    }
}

fn m31_const<E: EvalAtRow>(value: u32) -> E::F {
    E::F::from(M31::from_u32_unchecked(value))
}

fn mdoc_column_eval(log_size: u32, coset_values: Vec<M31>) -> MdocRevocationRangeColumnEval {
    let mut ordered = vec![M31::from_u32_unchecked(0); 1usize << log_size];
    for (coset_index, value) in coset_values.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        );
        ordered[row] = value;
    }
    CircleEvaluation::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(ordered),
    )
}

fn revocation_range_active_column() -> MdocRevocationRangeColumnEval {
    let mut values = vec![M31::from_u32_unchecked(0); 1usize << MDOC_REVOCATION_RANGE_LOG_SIZE];
    values[0] = M31::from_u32_unchecked(1);
    mdoc_column_eval(MDOC_REVOCATION_RANGE_LOG_SIZE, values)
}

fn byte_bits(byte: u8) -> [u8; 8] {
    std::array::from_fn(|bit| (byte >> bit) & 1)
}

fn comparison_carries(lhs: [u8; 8], rhs: [u8; 8], slack: [u8; 8]) -> [u8; 8] {
    let mut carry = 0u16;
    std::array::from_fn(|idx| {
        let add_one = u16::from(idx == 0);
        let sum = u16::from(lhs[idx]) + u16::from(slack[idx]) + add_one + carry;
        carry = sum >> 8;
        debug_assert_eq!((sum & 0xff) as u8, rhs[idx]);
        carry as u8
    })
}

fn revocation_range_base_trace(
    witness: &MdocRevocationRangeWitness,
    mso_digest: &[u8; 32],
) -> Vec<MdocRevocationRangeColumnEval> {
    let id = witness.id.to_le_bytes();
    let id_lo = witness.id_lo.to_le_bytes();
    let id_hi = witness.id_hi.to_le_bytes();
    let lower_slack = witness
        .id
        .wrapping_sub(witness.id_lo)
        .wrapping_sub(1)
        .to_le_bytes();
    let upper_slack = witness
        .id_hi
        .wrapping_sub(witness.id)
        .wrapping_sub(1)
        .to_le_bytes();
    let lower_carries = comparison_carries(id_lo, id, lower_slack);
    let upper_carries = comparison_carries(id, id_hi, upper_slack);

    let mut first_row = Vec::with_capacity(revocation_range_trace_cols());
    for byte in id
        .into_iter()
        .chain(id_lo)
        .chain(id_hi)
        .chain(lower_slack)
        .chain(upper_slack)
    {
        first_row.push(u32::from(byte));
    }
    let range_bytes = first_row[..REVOCATION_RANGE_BYTE_COLS].to_vec();
    for byte_idx in revocation_range_bit_byte_indices() {
        first_row.extend(
            byte_bits(range_bytes[byte_idx] as u8)
                .into_iter()
                .map(u32::from),
        );
    }
    first_row.extend(lower_carries.into_iter().map(u32::from));
    first_row.extend(upper_carries.into_iter().map(u32::from));
    first_row.extend(
        mso_digest[REVOCATION_U64_BYTES..]
            .iter()
            .map(|&byte| u32::from(byte)),
    );
    debug_assert_eq!(first_row.len(), revocation_range_trace_cols());

    first_row
        .into_iter()
        .map(|value| {
            let mut column = vec![M31::from_u32_unchecked(0); 1 << MDOC_REVOCATION_RANGE_LOG_SIZE];
            column[0] = M31::from_u32_unchecked(value);
            mdoc_column_eval(MDOC_REVOCATION_RANGE_LOG_SIZE, column)
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn revocation_range_interaction_trace(
    witness: &MdocRevocationRangeWitness,
    mso_digest: &[u8; 32],
    mso_digest_relation: &DigestBytesRelation,
    epoch: u32,
    message_relation: &FieldBytesRelation,
    blinder_relation: &ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
) -> (Vec<MdocRevocationRangeColumnEval>, QM31) {
    let base = revocation_range_base_trace(witness, mso_digest);
    let active = revocation_range_active_column();
    let n_vec_rows = 1usize << (MDOC_REVOCATION_RANGE_LOG_SIZE - LOG_N_LANES);
    let digest_tail_offset =
        REVOCATION_RANGE_BYTE_COLS + revocation_range_bit_cols() + REVOCATION_RANGE_CARRY_COLS;
    // Q-015 blinder `+m/(z−combine(v))`, emitted LAST (paired with the lone
    // message site in the TS13 Relation branch, its own column otherwise).
    let blinder_num = PackedQM31::broadcast(blinder_m);
    let blinder_den = crate::claimed_sum_blinder::blinder_denominator(blinder_relation, blinder_v);
    let mut logup = LogupTraceGenerator::new(MDOC_REVOCATION_RANGE_LOG_SIZE);
    let epoch_bytes = epoch.to_le_bytes();
    for first_lookup in (0..=TS13_REVOCATION_MESSAGE_LEN).step_by(2) {
        logup.col_from_fn(|vec_row| {
            let entry = |lookup: usize| {
                let numerator = PackedQM31::from(active.data[vec_row]);
                if lookup == 0 {
                    let mut values = [PackedM31::broadcast(M31::from_u32_unchecked(0)); 32];
                    for byte_idx in 0..REVOCATION_U64_BYTES {
                        values[byte_idx] = base[byte_idx].data[vec_row];
                    }
                    for byte_idx in REVOCATION_U64_BYTES..32 {
                        values[byte_idx] = base
                            [digest_tail_offset + byte_idx - REVOCATION_U64_BYTES]
                            .data[vec_row];
                    }
                    return (numerator, mso_digest_relation.combine(&values));
                }

                let byte_idx = lookup - 1;
                let value = match byte_idx {
                    0..=7 => base[REVOCATION_U64_BYTES + byte_idx].data[vec_row],
                    8..=15 => base[2 * REVOCATION_U64_BYTES + byte_idx - 8].data[vec_row],
                    _ => PackedM31::broadcast(M31::from_u32_unchecked(u32::from(
                        epoch_bytes[byte_idx - 16],
                    ))),
                };
                let denominator: PackedQM31 = message_relation.combine(&[
                    PackedM31::broadcast(M31::from_u32_unchecked(HOSTED_MSG_FIELD_ID)),
                    PackedM31::broadcast(M31::from_u32_unchecked(byte_idx as u32)),
                    value,
                ]);
                (-numerator, denominator)
            };
            let (left_num, left_den) = entry(first_lookup);
            if first_lookup == TS13_REVOCATION_MESSAGE_LEN {
                // Pair the lone last message site with the blinder.
                return (
                    left_num * blinder_den + blinder_num * left_den,
                    left_den * blinder_den,
                );
            }
            let (right_num, right_den) = entry(first_lookup + 1);
            (
                left_num * right_den + right_num * left_den,
                left_den * right_den,
            )
        });
    }
    debug_assert_eq!(n_vec_rows, 1);
    logup.finalize_last()
}

fn byte_from_bits<E: EvalAtRow>(bits: &[E::F]) -> E::F {
    bits.iter()
        .enumerate()
        .fold(m31_const::<E>(0), |acc, (bit, value)| {
            acc + m31_const::<E>(1u32 << bit) * value.clone()
        })
}

impl FrameworkEval for MdocRevocationRangeEval {
    fn log_size(&self) -> u32 {
        MDOC_REVOCATION_RANGE_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        MDOC_REVOCATION_RANGE_LOG_SIZE + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(revocation_range_active_id());
        let one = m31_const::<E>(1);
        eval.add_constraint(active.clone() * (active.clone() - one.clone()));

        let values: Vec<E::F> = (0..revocation_range_trace_cols())
            .map(|_| eval.next_trace_mask())
            .collect();
        for value in &values {
            eval.add_constraint((one.clone() - active.clone()) * value.clone());
        }

        // Bit-pin exactly the externally-unpinned bytes (see
        // `revocation_range_bit_byte_indices` for the per-byte exemptions).
        for (slot, byte_idx) in revocation_range_bit_byte_indices().enumerate() {
            let byte = values[byte_idx].clone();
            let bits = &values[REVOCATION_RANGE_BYTE_COLS + slot * 8
                ..REVOCATION_RANGE_BYTE_COLS + (slot + 1) * 8];
            for bit in bits {
                eval.add_constraint(bit.clone() * (bit.clone() - one.clone()));
            }
            eval.add_constraint(active.clone() * (byte - byte_from_bits::<E>(bits)));
        }

        let lower_carries_offset = REVOCATION_RANGE_BYTE_COLS + revocation_range_bit_cols();
        let upper_carries_offset = lower_carries_offset + REVOCATION_U64_BYTES;
        for carry in &values[lower_carries_offset..upper_carries_offset + REVOCATION_U64_BYTES] {
            eval.add_constraint(carry.clone() * (carry.clone() - one.clone()));
        }

        for byte_idx in 0..REVOCATION_U64_BYTES {
            let id = values[byte_idx].clone();
            let id_lo = values[REVOCATION_U64_BYTES + byte_idx].clone();
            let id_hi = values[2 * REVOCATION_U64_BYTES + byte_idx].clone();
            let lower_slack = values[3 * REVOCATION_U64_BYTES + byte_idx].clone();
            let upper_slack = values[4 * REVOCATION_U64_BYTES + byte_idx].clone();
            let lower_carry_in = if byte_idx == 0 {
                m31_const::<E>(0)
            } else {
                values[lower_carries_offset + byte_idx - 1].clone()
            };
            let lower_carry_out = values[lower_carries_offset + byte_idx].clone();
            let upper_carry_in = if byte_idx == 0 {
                m31_const::<E>(0)
            } else {
                values[upper_carries_offset + byte_idx - 1].clone()
            };
            let upper_carry_out = values[upper_carries_offset + byte_idx].clone();
            let add_one = m31_const::<E>(u32::from(byte_idx == 0));
            eval.add_constraint(
                active.clone()
                    * (id_lo + lower_slack + add_one.clone() + lower_carry_in
                        - id.clone()
                        - m31_const::<E>(256) * lower_carry_out),
            );
            eval.add_constraint(
                active.clone()
                    * (id + upper_slack + add_one + upper_carry_in
                        - id_hi
                        - m31_const::<E>(256) * upper_carry_out),
            );
        }
        eval.add_constraint(active.clone() * values[lower_carries_offset + 7].clone());
        eval.add_constraint(active.clone() * values[upper_carries_offset + 7].clone());

        let digest_tail_offset = upper_carries_offset + REVOCATION_U64_BYTES;
        let mut digest_values = Vec::with_capacity(32);
        digest_values.extend(values.iter().take(REVOCATION_U64_BYTES).cloned());
        for byte_idx in 0..REVOCATION_RANGE_DIGEST_TAIL_COLS {
            digest_values.push(values[digest_tail_offset + byte_idx].clone());
        }
        eval.add_to_relation(RelationEntry::new(
            self.mso_digest_relation.as_ref(),
            E::EF::from(active.clone()),
            &digest_values,
        ));
        let field_id = m31_const::<E>(HOSTED_MSG_FIELD_ID);
        for byte_idx in 0..TS13_REVOCATION_MESSAGE_LEN {
            let value = match byte_idx {
                0..=7 => values[REVOCATION_U64_BYTES + byte_idx].clone(),
                8..=15 => values[2 * REVOCATION_U64_BYTES + byte_idx - 8].clone(),
                _ => m31_const::<E>(u32::from(self.epoch.to_le_bytes()[byte_idx - 16])),
            };
            eval.add_to_relation(RelationEntry::new(
                &self.message_field_relation,
                -E::EF::from(active.clone()),
                &[field_id.clone(), m31_const::<E>(byte_idx as u32), value],
            ));
        }
        // Q-015 blinder `+m/(z−combine(v))`, ungated, emitted LAST to
        // match the generator's pairing of the lone message site.
        add_blinder_relation_entry(
            &mut eval,
            &self.blinder_relation,
            self.blinder_v,
            self.blinder_m,
            false,
        );
        eval.finalize_logup_in_pairs();
        eval
    }
}

impl Air for MdocRevocationRangeBind {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(0x5453_3133_524e_4701);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        // This component is the revocation-message field-byte provider unless
        // an earlier module has populated the shared handle.
        if !self.message_field_handle.is_set() {
            self.message_field_handle
                .set(FieldBytesRelation::draw(channel));
        }
        self.blinder_relation = Some(ClaimedSumBlinderRelation::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        // The digest, 20 message tuples, and blinder are paired in the main
        // component; the blinder counterpart contributes one more column.
        let interaction_cols =
            ((2 + TS13_REVOCATION_MESSAGE_LEN).div_ceil(2) + 1) * SECURE_EXTENSION_DEGREE;
        TreeLayout {
            preprocessed: vec![MDOC_REVOCATION_RANGE_LOG_SIZE],
            trace: vec![MDOC_REVOCATION_RANGE_LOG_SIZE; revocation_range_trace_cols()],
            interaction: vec![MDOC_REVOCATION_RANGE_LOG_SIZE; interaction_cols],
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        let claim = self.interaction_claim();
        vec![claim.claimed_sum, claim.blinder_claimed_sum]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        vec![revocation_range_active_id()]
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(vec![revocation_range_active_column()])
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let claim = self.interaction_claim().clone();
        let blinder_relation = self
            .blinder_relation
            .clone()
            .expect("mdoc revocation range blinder relation drawn before components");
        self.component = Some(MdocRevocationRangeComponent::new(
            allocator,
            MdocRevocationRangeEval {
                mso_digest_relation: Box::new(self.mso_digest_relation()),
                message_field_relation: self.message_relation(),
                epoch: self.epoch,
                blinder_relation: blinder_relation.clone(),
                blinder_v: claim.blinder_v,
                blinder_m: claim.blinder_m,
            },
            claim.claimed_sum,
        ));
        self.blinder_component = Some(FrameworkComponent::new(
            allocator,
            ClaimedSumBlinderEval {
                log_size: MDOC_REVOCATION_RANGE_LOG_SIZE,
                relation: blinder_relation,
                v: claim.blinder_v,
                m: claim.blinder_m,
            },
            claim.blinder_claimed_sum,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![
            self.component
                .as_ref()
                .expect("mdoc revocation range component is built"),
            self.blinder_component
                .as_ref()
                .expect("mdoc revocation range blinder component is built"),
        ]
    }
}

impl AirProver for MdocRevocationRangeBind {
    fn max_log_size(&self) -> u32 {
        MDOC_REVOCATION_RANGE_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        MDOC_REVOCATION_RANGE_LOG_SIZE + 1
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(vec![revocation_range_active_column()]);
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc::MdocRevocationRangeBind",
            &[revocation_range_active_id()],
            &[revocation_range_active_column()],
        )
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(revocation_range_base_trace(
            self.witness
                .as_ref()
                .expect("mdoc revocation range witness is set"),
            self.mso_digest
                .as_ref()
                .expect("mdoc revocation range MSO digest is set"),
        ));
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let blinder_v = random_qm31();
        let blinder_m = random_qm31();
        let blinder_relation = self
            .blinder_relation
            .clone()
            .expect("mdoc revocation range blinder relation drawn before interaction");
        let (trace, claimed_sum) = revocation_range_interaction_trace(
            self.witness
                .as_ref()
                .expect("mdoc revocation range witness is set"),
            self.mso_digest
                .as_ref()
                .expect("mdoc revocation range MSO digest is set"),
            &self.mso_digest_relation(),
            self.epoch,
            &self.message_relation(),
            &blinder_relation,
            blinder_v,
            blinder_m,
        );
        tb.extend_evals(trace);
        let (blinder_trace, blinder_claimed_sum) = blinder_counter_interaction(
            MDOC_REVOCATION_RANGE_LOG_SIZE,
            &blinder_relation,
            blinder_v,
            blinder_m,
        );
        tb.extend_evals(blinder_trace);
        self.interaction_claim = Some(MdocRevocationRangeInteractionClaim {
            claimed_sum,
            blinder_v,
            blinder_m,
            blinder_claimed_sum,
        });
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            self.component
                .as_ref()
                .expect("mdoc revocation range component is built"),
            self.blinder_component
                .as_ref()
                .expect("mdoc revocation range blinder component is built"),
        ]
    }
}

pub fn prove_mdoc_circuit(
    extracted: &ExtractedPidMdoc,
    statement: &MdocCircuitStatement,
) -> Result<MdocCircuitProof, Error> {
    prove_mdoc_circuit_with_pcs_config(extracted, statement, mdoc_production_pcs_config())
}

pub fn prove_mdoc_circuit_with_pcs_config(
    extracted: &ExtractedPidMdoc,
    statement: &MdocCircuitStatement,
    config: PcsConfig,
) -> Result<MdocCircuitProof, Error> {
    prove_mdoc_circuit_inner(extracted, statement, config)
}

fn prove_mdoc_circuit_inner(
    extracted: &ExtractedPidMdoc,
    statement: &MdocCircuitStatement,
    config: PcsConfig,
) -> Result<MdocCircuitProof, Error> {
    prove_mdoc_circuit_inner_impl(
        extracted,
        statement,
        config,
        None,
        #[cfg(feature = "unlink-spikes")]
        MdocUnlinkSpikeConfig::default(),
    )
}

pub fn prove_mdoc_ts13_demo_circuit(
    extracted: &ExtractedPidMdoc,
    statement: &MdocCircuitStatement,
    public: &MdocTs13DemoCircuitPublicInput,
) -> Result<MdocCircuitProof, Error> {
    prove_mdoc_circuit_inner_impl(
        extracted,
        statement,
        mdoc_production_pcs_config(),
        Some(public),
        #[cfg(feature = "unlink-spikes")]
        MdocUnlinkSpikeConfig::default(),
    )
}

/// Unlinkability Phase-0b service-scaling probe. `dummy_keccak_jobs` appends
/// identical 34-byte SHAKE-128/five-squeeze jobs after all production jobs.
#[cfg(feature = "unlink-spikes")]
#[doc(hidden)]
pub fn prove_mdoc_circuit_keccak_scale_spike(
    extracted: &ExtractedPidMdoc,
    statement: &MdocCircuitStatement,
    dummy_keccak_jobs: usize,
) -> Result<MdocCircuitProof, Error> {
    validate_unlink_spike_dummy_jobs(dummy_keccak_jobs, "prove")?;
    prove_mdoc_circuit_inner_impl(
        extracted,
        statement,
        mdoc_production_pcs_config(),
        None,
        MdocUnlinkSpikeConfig { dummy_keccak_jobs },
    )
}

fn prepare_mldsa_role(
    mut input: MlDsaVerifyInput,
    witness_error_context: &'static str,
) -> Result<(stwo_mldsa::witness::MlDsaWitness, MlDsaVerifyInput), Error> {
    let native_tr = stwo_mldsa::statement::native_tr(&input);
    debug_assert_eq!(
        input.tr, native_tr,
        "{witness_error_context} tr must already match SHAKE256(pk)"
    );
    input.tr = native_tr;
    let witness = stwo_mldsa::witness::generate_witness(&input)
        .map_err(|error| Error::Prove(format!("{witness_error_context}: {error:?}")))?;
    stwo_mldsa::sampleinball::validate_stream(&witness)
        .map_err(|error| Error::Prove(format!("mldsa SIB resource cap: {error}")))?;
    Ok((witness, input))
}

fn validate_ts13_demo_proving_shape(
    extracted: &ExtractedPidMdoc,
    statement: &MdocCircuitStatement,
    public: &MdocTs13DemoCircuitPublicInput,
) -> Result<(), Error> {
    let [attribute] = statement.attributes.as_slice() else {
        return Err(Error::UnsupportedDemoCredentialShape);
    };
    if statement.doctype != PID_DOCTYPE
        || statement.namespace != PID_NAMESPACE
        || attribute.element_identifier != "age_over_18"
        || attribute.mode != MdocDisclosureMode::ValueEquality(vec![0xf5])
        || attribute.item_padded_len != TS13_DEMO_ITEM_PADDED_BYTES
        || statement.mso_payload_len != TS13_DEMO_MSO_PAYLOAD_BYTES
        || extracted.issuer_sig_structure.len() != TS13_DEMO_ISSUER_MESSAGE_BYTES
        || extracted.mso.len() != TS13_DEMO_MSO_PAYLOAD_BYTES
        || extracted
            .extracted_attributes
            .first()
            .map(|item| stwo_sha256::native::pad_message(&item.item).len())
            != Some(usize::from(TS13_DEMO_ITEM_PADDED_BYTES))
    {
        return Err(Error::UnsupportedDemoCredentialShape);
    }
    let issuer = statement
        .issuer_input
        .as_mldsa()
        .ok_or_else(|| Error::Prove("TS13 issuer input is not ML-DSA".to_string()))?;
    let device = statement
        .device_input
        .as_mldsa()
        .ok_or_else(|| Error::Prove("TS13 device witness is not ML-DSA".to_string()))?;
    if issuer.encode_pk() != public.trusted_issuer_public_key
        || device.message != public.device_cose_sig_structure
        || statement.ts13_revocation.as_ref() != Some(&public.revocation)
        || statement.policy.current_date
            != utc_date_from_epoch_seconds(public.timestamp_epoch_seconds)
                .map_err(|error| Error::Prove(format!("{error:?}")))?
        || public.device_cose_sig_structure.len() > TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY
    {
        return Err(Error::Prove(
            "TS13 demo private witness does not match the public theorem".to_string(),
        ));
    }
    Ok(())
}

fn prove_mdoc_circuit_inner_impl(
    extracted: &ExtractedPidMdoc,
    statement: &MdocCircuitStatement,
    config: PcsConfig,
    ts13_demo_public: Option<&MdocTs13DemoCircuitPublicInput>,
    #[cfg(feature = "unlink-spikes")] unlink_spike: MdocUnlinkSpikeConfig,
) -> Result<MdocCircuitProof, Error> {
    validate_mdoc_circuit_statement_shape(statement, "prove", ts13_demo_public.is_some())?;
    validate_mldsa_public_keys(statement, "prove")?;
    let has_ts13_revocation = validate_ts13_revocation_shape(statement, true, "prove")?;
    let is_ts13_demo = ts13_demo_public.is_some();
    if let Some(public) = ts13_demo_public {
        validate_ts13_demo_proving_shape(extracted, statement, public)?;
        if !has_ts13_revocation {
            return Err(Error::Prove("TS13 demo requires revocation".to_string()));
        }
    }
    if !auth_inputs_equal(&statement.issuer_input, &extracted.issuer_auth_input)
        || !auth_inputs_equal(&statement.device_input, &extracted.device_auth_input)
    {
        return Err(Error::AuthInputMismatch);
    }
    check_mldsa_extracted_statement_coherence(extracted, statement)?;
    // Issuer, device, and revocation messages are absorbed directly by hosted
    // ML-DSA modules. SHA-256 remains only for ISO mdoc attribute digests.
    let revocation_message = has_ts13_revocation.then(|| {
        let revocation = statement
            .ts13_revocation
            .as_ref()
            .expect("revocation shape was validated");
        let range = statement
            .ts13_revocation_range
            .as_ref()
            .expect("proving revocation shape includes the private range");
        ts13_revocation_message_bytes(range.id_lo, range.id_hi, revocation.epoch)
    });
    let attribute_items: Vec<_> = extracted
        .extracted_attributes
        .iter()
        .map(|attribute| attribute.item.as_slice())
        .collect();
    let attribute_sha_params: Vec<_> = attribute_items
        .iter()
        .map(|item| sha_params(item))
        .collect();
    let mso_sha_witness =
        has_ts13_revocation.then(|| compute_sha256_witness(extracted.mso.as_slice()));
    let mso_sha_padded_len = mso_sha_witness
        .as_ref()
        .map(|witness| witness.padding.padded.len());
    let shared_sha_log = attribute_sha_params
        .iter()
        .map(|(_, log)| *log)
        .max()
        .expect("sha log list is non-empty (attributes are 1..=4)");
    // Fully post-quantum composition: each format-required attribute digest
    // uses one namespaced SHA instance at the shared public log. Revocation is
    // not a SHA instance; its range AIR directly provides the raw signed
    // message.
    let attribute_digests: Vec<_> = (0..attribute_sha_params.len())
        .map(|_| SharedDigestRelation::new())
        .collect();
    let mso_digest = has_ts13_revocation.then(SharedDigestRelation::new);
    let mso_stream_field = has_ts13_revocation.then(SharedFieldRelation::new);
    let mso_start_handle = SharedMdocMsoStartRelation::new();
    let device_pk_start_handle = is_ts13_demo.then(SharedMdocDevicePkStartRelation::new);
    let validity_handle = is_ts13_demo.then(SharedMdocMsoValidityBytesRelation::new);
    let expand_a_bindings = is_ts13_demo.then(ExpandABindings::new);
    let t1_handle = is_ts13_demo.then(SharedT1CellRelation::new);
    let country_code_handle = SharedMdocCountryCodeRelation::new();
    // The proof-wide keccak service's relations handle (S1): drawn ONCE by the
    // service module, consumed by every hosted ML-DSA instance.
    let mldsa_keccak_handle = SharedKeccakRelations::new();
    let mldsa_range_handle = SharedRangeRelation::new();
    let issuer_message_field = SharedFieldRelation::new();
    let revocation_message_field = has_ts13_revocation.then(SharedFieldRelation::new);
    let attribute_fields: Vec<_> = (0..attribute_sha_params.len())
        .map(|_| SharedFieldRelation::new())
        .collect();
    let sha_table_relations = SharedShaTableRelations::new();
    let attribute_exposures: Vec<_> = (0..statement.attributes.len())
        .map(|index| attribute_exposure(statement, index))
        .collect();

    let mut sha_consumers: Vec<_> = attribute_sha_params
        .iter()
        .zip(&attribute_exposures)
        .map(|((witness, _), exposure)| (witness, exposure.clone()))
        .collect();
    if let (Some(witness), Some(padded_len)) = (mso_sha_witness.as_ref(), mso_sha_padded_len) {
        sha_consumers.push((
            witness,
            FieldExposure::from_full_padded_stream(MDOC_MSO_SHA_STREAM_FIELD_ID, padded_len),
        ));
    }
    let sha_table_multiplicities = ShaTableMultiplicities::from_consumers(&sha_consumers);
    let mut sha_tables =
        ShaTablesProver::new(sha_table_multiplicities, sha_table_relations.clone());

    // Witness preparation is pure and Send. Keep the non-Send shared relation
    // handles and MlDsaProver construction on this thread, in fixed role order.
    let issuer_input = statement.issuer_input.as_mldsa().cloned();
    let device_input = statement.device_input.as_mldsa().cloned();
    let issuer_message = issuer_input
        .as_ref()
        .ok_or_else(|| Error::Prove("mdoc issuer input is not ML-DSA".to_string()))?
        .message
        .clone();
    let private_mso_spec =
        private_mso_bind_spec(statement, mso_sha_padded_len, is_ts13_demo, "prove")?;
    let private_mso_version = match parse_mso(&extracted.mso, &statement.namespace)
        .map_err(Error::Mdoc)?
        .version
        .as_str()
    {
        MDOC_PROFILE_VERSION_V1 => MdocPrivateMsoVersion::V1,
        MDOC_PROFILE_VERSION_V2 => MdocPrivateMsoVersion::V2,
        other => {
            return Err(Error::Prove(format!(
                "private MSO binder unsupported version {other}"
            )))
        }
    };
    let private_mso_witness = MdocPrivateMsoBindWitness::from_canonical_issuer_message(
        &private_mso_spec,
        issuer_message.clone(),
        &extracted.mso,
        private_mso_version,
    )
    .map_err(|error| Error::Prove(format!("private MSO binder witness: {error}")))?;
    let private_mso_start = private_mso_witness
        .mso_start(extracted.mso.len())
        .map_err(|error| Error::Prove(format!("private MSO start: {error}")))?;
    let private_device_pk_start = is_ts13_demo
        .then(|| private_mso_witness.device_pk_start(&private_mso_spec))
        .transpose()
        .map_err(|error| Error::Prove(format!("private device-key start: {error}")))?;
    let private_validity_witness = is_ts13_demo
        .then(|| private_mso_witness.validity_witness(&private_mso_spec))
        .transpose()
        .map_err(|error| Error::Prove(format!("private MSO validity: {error}")))?;
    let (mut private_mso_bind, private_mso_census) = MdocPrivateMsoBind::prover(
        private_mso_spec,
        private_mso_witness,
        issuer_message_field.clone(),
        mso_stream_field.clone(),
        Some(mso_start_handle.clone()),
        device_pk_start_handle.clone(),
        validity_handle.clone(),
    )
    .map_err(|error| Error::Prove(format!("private MSO binder: {error}")))?;
    let mut ts13_public_context =
        ts13_demo_public.map(MdocTs13DemoCircuitPublicInput::context_bind);
    let mut ts13_expand_a = if is_ts13_demo {
        let device = device_input
            .as_ref()
            .expect("TS13 demo shape requires a private device witness");
        let witness = derive_expand_a_witness(device.rho)
            .map_err(|error| Error::Prove(format!("TS13 private ExpandA: {error}")))?;
        Some(
            ExpandAProver::new(
                witness,
                MDOC_DEVICE_EXPAND_A_NAMESPACE,
                MDOC_DEVICE_EXPAND_A_STREAM_BASE,
                mldsa_range_handle.clone(),
                mldsa_keccak_handle.clone(),
                expand_a_bindings
                    .clone()
                    .expect("TS13 ExpandA bindings exist"),
            )
            .map_err(|error| Error::Prove(format!("TS13 private ExpandA: {error}")))?,
        )
    } else {
        None
    };
    let (mut ts13_device_key_bind, ts13_device_key_census) = if is_ts13_demo {
        let device = device_input
            .as_ref()
            .expect("TS13 demo shape requires a private device witness");
        let (bind, census) = MdocPrivateDeviceKeyBind::prover(
            device.encode_pk(),
            private_device_pk_start.expect("TS13 private device-key start exists"),
            issuer_message.len(),
            issuer_message_field.clone(),
            mldsa_range_handle.clone(),
            expand_a_bindings
                .as_ref()
                .expect("TS13 ExpandA bindings exist")
                .rho
                .clone(),
            t1_handle.clone().expect("TS13 T1 handle exists"),
            device_pk_start_handle
                .clone()
                .expect("TS13 device-key start handle exists"),
        )
        .map_err(|error| Error::Prove(format!("TS13 private device-key bind: {error}")))?;
        if !census.has_frozen_demo_shape() {
            return Err(Error::Prove(
                "TS13 private device-key binder geometry drifted from the frozen profile"
                    .to_string(),
            ));
        }
        (Some(bind), Some(census))
    } else {
        (None, None)
    };
    let (mut ts13_mso_validity, ts13_validity_range_uses) = if let Some(public) = ts13_demo_public {
        let (validity, uses) = MdocPrivateMsoValidityV2::prover(
            MdocPrivateMsoValiditySpec {
                timestamp_epoch_seconds: public.timestamp_epoch_seconds,
                verification_timestamp_rfc3339_utc: public.verification_timestamp_rfc3339_utc,
            },
            private_validity_witness.expect("TS13 validity witness exists"),
            mldsa_range_handle.clone(),
            validity_handle
                .clone()
                .expect("TS13 validity relation exists"),
        )
        .map_err(|error| Error::Prove(format!("TS13 private MSO validity: {error}")))?;
        (Some(validity), Some(uses))
    } else {
        (None, None)
    };

    let private_item_profile = if is_ts13_demo {
        MdocPrivateItemProfile::Ts13Demo
    } else if has_ts13_revocation {
        MdocPrivateItemProfile::Ts13
    } else {
        MdocPrivateItemProfile::Product
    };
    let value_digests_profile = if has_ts13_revocation {
        MdocValueDigestsProfile::Ts13
    } else {
        MdocValueDigestsProfile::Product
    };
    let mut private_item_handles = Vec::with_capacity(statement.attributes.len());
    let mut private_item_binds = Vec::with_capacity(statement.attributes.len());
    let mut mdoc_cbor_streams = Vec::with_capacity(statement.attributes.len() * 2);
    for (index, (statement_attribute, extracted_attribute)) in statement
        .attributes
        .iter()
        .zip(&extracted.extracted_attributes)
        .enumerate()
    {
        let request_mode = match statement_attribute.mode {
            MdocDisclosureMode::ValueEquality(_) => MdocPrivateItemRequestMode::ValueEquality,
            MdocDisclosureMode::AgeOver => MdocPrivateItemRequestMode::BirthDate,
            MdocDisclosureMode::Alpha2Set => MdocPrivateItemRequestMode::Nationality,
        };
        let field_ids = MdocPrivateItemFieldIds {
            outer_stream: MdocStatementAttribute::outer_stream_field_id(index),
            inner_stream: MdocStatementAttribute::inner_stream_field_id(index),
            element_identifier: MdocStatementAttribute::element_field_id(index),
            element_value: match request_mode {
                MdocPrivateItemRequestMode::ValueEquality => {
                    MdocStatementAttribute::value_field_id(index)
                }
                MdocPrivateItemRequestMode::BirthDate => field_id::DOB,
                MdocPrivateItemRequestMode::Nationality => field_id::NATIONALITY,
            },
        };
        let handles = MdocPrivateItemHandles::fresh(
            attribute_fields[index].clone(),
            country_code_handle.clone(),
        );
        let padded_item = stwo_sha256::native::pad_message(&extracted_attribute.item);
        let private_input = if matches!(request_mode, MdocPrivateItemRequestMode::Nationality) {
            match extracted.nationality_array_index {
                Some(selected_index) => MdocPrivateItemPrivateInput::with_nationality_member(
                    padded_item.clone(),
                    selected_index,
                ),
                None => MdocPrivateItemPrivateInput::new(padded_item.clone()),
            }
        } else {
            MdocPrivateItemPrivateInput::new(padded_item.clone())
        };
        let item_bind = MdocPrivateItemBind::new(
            index,
            private_item_profile,
            private_mso_version,
            request_mode,
            usize::from(statement_attribute.item_padded_len),
            private_input,
            field_ids,
            handles.clone(),
        )
        .map_err(|error| map_private_item_prove_error(index, error))?;
        let outer_parser = MdocCborStream::new(
            padded_item,
            MdocCborInputMode::ShaPadded,
            field_ids.outer_stream,
            handles.item_fields.clone(),
            Some(handles.outer_parsed.clone()),
        )
        .map_err(|error| Error::Prove(format!("IssuerSignedItem {index} outer parser: {error}")))?;
        let inner_parser = MdocCborStream::new(
            item_bind.inner_bytes().to_vec(),
            MdocCborInputMode::Raw,
            field_ids.inner_stream,
            handles.inner_raw.clone(),
            Some(handles.inner_parsed.clone()),
        )
        .map_err(|error| Error::Prove(format!("IssuerSignedItem {index} inner parser: {error}")))?;
        private_item_handles.push(handles);
        private_item_binds.push(item_bind);
        mdoc_cbor_streams.push(outer_parser);
        mdoc_cbor_streams.push(inner_parser);
    }
    let country_code_uses: Vec<_> = private_item_binds
        .iter()
        .filter(|bind| bind.country_code_uses().total_uses() != 0)
        .map(|bind| bind.country_code_uses().clone())
        .collect();
    let mut country_code_table = statement
        .nationality_attribute_index()
        .map(|_| {
            MdocCountryCodeTable::prover(&country_code_uses, country_code_handle.clone())
                .map_err(|error| Error::Prove(format!("country-code table: {error}")))
        })
        .transpose()?;

    let scanner_handles = MdocValueDigestsScanHandles {
        issuer_message: issuer_message_field.clone(),
        mso_start: mso_start_handle.clone(),
        items: private_item_handles
            .iter()
            .zip(&attribute_digests)
            .map(|(item, digest)| MdocValueDigestItemHandles {
                digest_id: item.digest_id.clone(),
                digest: digest.clone(),
            })
            .collect(),
    };
    let scanner_spec = MdocValueDigestsScanSpec {
        issuer_message_len: issuer_message.len(),
        mso_len: extracted.mso.len(),
        namespace: statement.namespace.clone(),
        profile: value_digests_profile,
        attribute_count: statement.attributes.len(),
    };
    let scanner_witness = MdocValueDigestsScanWitness {
        issuer_message: issuer_message.clone(),
        mso_start: private_mso_start,
        version: private_mso_version,
        disclosures: extracted
            .extracted_attributes
            .iter()
            .map(|attribute| MdocValueDigestDisclosure {
                digest_id: attribute.digest_id,
                digest: Sha256::digest(&attribute.item).into(),
            })
            .collect(),
    };
    let (mut value_digests_scan, value_digests_census) =
        MdocValueDigestsScan::prover(scanner_spec, scanner_witness, scanner_handles)
            .map_err(map_value_digests_prove_error)?;
    if private_mso_census.issuer_position_uses.len()
        != value_digests_census.issuer_position_uses.len()
        || ts13_device_key_census.as_ref().is_some_and(|census| {
            census.issuer_position_uses.len() != private_mso_census.issuer_position_uses.len()
        })
    {
        return Err(Error::Prove(
            "private issuer-message census lengths disagree".to_string(),
        ));
    }
    let ts13_device_key_uses = ts13_device_key_census
        .as_ref()
        .map(|census| census.issuer_position_uses.as_slice());
    let issuer_position_uses: Vec<u32> = private_mso_census
        .issuer_position_uses
        .into_iter()
        .zip(value_digests_census.issuer_position_uses)
        .enumerate()
        .map(|(index, (mso_uses, scan_uses))| {
            mso_uses
                .checked_add(scan_uses)
                .and_then(|uses| {
                    uses.checked_add(
                        ts13_device_key_uses
                            .map(|counts| counts[index])
                            .unwrap_or(0),
                    )
                })
                .ok_or_else(|| {
                    Error::Prove(format!(
                        "private issuer message use count overflows at byte {index}"
                    ))
                })
        })
        .collect::<Result<_, _>>()?;
    let mut issuer_message_provider = MdocPrivateMessageProvider::new(
        issuer_message.clone(),
        issuer_position_uses,
        issuer_message_field.clone(),
    )
    .map_err(|error| Error::Prove(format!("private issuer message provider: {error}")))?;
    let revocation_input = revocation_message
        .as_ref()
        .map(|message| ts13_revocation_mldsa_input(statement, message.to_vec()))
        .transpose();
    let ((issuer_prepared, device_prepared), revocation_prepared) = rayon::join(
        || {
            rayon::join(
                || {
                    issuer_input
                        .map(|input| prepare_mldsa_role(input, "mldsa witness"))
                        .transpose()
                },
                || {
                    device_input
                        .map(|input| prepare_mldsa_role(input, "mldsa device witness"))
                        .transpose()
                },
            )
        },
        || {
            revocation_input.and_then(|input| {
                input
                    .flatten()
                    .map(|input| prepare_mldsa_role(*input, "mldsa revocation witness"))
                    .transpose()
            })
        },
    );
    // Preserve the original deterministic error priority even though all three
    // independent preparations run to completion.
    let issuer_prepared = issuer_prepared?;
    let device_prepared = device_prepared?;
    let revocation_prepared = revocation_prepared?;

    // The issuer Sig_structure is private. Its hosted µ bridge consumes one
    // complete indexed copy from `issuer_message_provider`; only the public
    // message length determines its transcript/layout.
    let mut issuer_mldsa = issuer_prepared.map(|(witness, input)| {
        MlDsaStatementProver::hosted(
            witness,
            input,
            issuer_message_field.clone(),
            mldsa_range_handle.clone(),
            mldsa_keccak_handle.clone(),
        )
        .with_instance_namespace(MDOC_ISSUER_MLDSA_NAMESPACE)
        .with_stream_base(MDOC_ISSUER_MLDSA_STREAM_BASE)
        .with_private_message()
    });
    // Hosted in-circuit ML-DSA device statement, public-message mode (S4).
    let mut device_mldsa = device_prepared
        .map(|(witness, input)| {
            let prover = if is_ts13_demo {
                MlDsaStatementProver::hosted_private_key(
                    witness,
                    input,
                    issuer_message_field.clone(),
                    mldsa_range_handle.clone(),
                    mldsa_keccak_handle.clone(),
                    PrivateKeyEvalBindings::new(
                        expand_a_bindings
                            .as_ref()
                            .expect("TS13 ExpandA bindings exist")
                            .ntt
                            .clone(),
                        t1_handle.clone().expect("TS13 T1 handle exists"),
                    ),
                )
                .map_err(|error| Error::Prove(format!("TS13 private device ML-DSA: {error}")))?
            } else {
                MlDsaStatementProver::hosted_public(
                    witness,
                    input,
                    mldsa_range_handle.clone(),
                    mldsa_keccak_handle.clone(),
                )
            };
            Ok::<_, Error>(
                prover
                    .with_instance_namespace(MDOC_DEVICE_MLDSA_NAMESPACE)
                    .with_stream_base(MDOC_DEVICE_MLDSA_STREAM_BASE),
            )
        })
        .transpose()?;
    // Hosted in-circuit ML-DSA revocation statement, private-message mode: the
    // prover's input carries the REAL 20-byte message (from the private range
    // witness); only its LENGTH is mixed into the transcript.
    let mut revocation_mldsa = revocation_prepared.map(|(witness, input)| {
        MlDsaStatementProver::hosted(
            witness,
            input,
            revocation_message_field
                .clone()
                .expect("revocation field relation exists with a revocation signature"),
            mldsa_range_handle.clone(),
            mldsa_keccak_handle.clone(),
        )
        .with_instance_namespace(MDOC_REVOCATION_MLDSA_NAMESPACE)
        .with_stream_base(MDOC_REVOCATION_MLDSA_STREAM_BASE)
        .with_private_message()
    });
    let mut range_uses: Vec<_> = [&issuer_mldsa, &device_mldsa, &revocation_mldsa]
        .into_iter()
        .flatten()
        .map(|prover| prover.range_uses().clone())
        .collect();
    if let Some(expand_a) = ts13_expand_a.as_ref() {
        range_uses.push(expand_a.range_uses().clone());
    }
    if let Some(device_key) = ts13_device_key_bind.as_ref() {
        range_uses.push(device_key.range_uses().clone());
    }
    if let Some(validity_uses) = ts13_validity_range_uses.as_ref() {
        range_uses.push(validity_uses.clone());
    }
    let mut mldsa_range_table = (!range_uses.is_empty())
        .then(|| SharedRangeTable::prover(&range_uses, mldsa_range_handle.clone()));
    // The ONE proof-wide keccak service (S1): built from the concatenated
    // sponge jobs of every present hosted ML-DSA instance, in fixed role order
    // (issuer, device, revocation) — the verifier rebuilds the same list from
    // public data. Present iff any instance is. Composed BEFORE the first
    // instance in module order so its `draw_relations` publishes the shared
    // keccak relations every consumer draws.
    let mut mldsa_keccak_service = {
        let mut shapes = Vec::new();
        let mut streams = Vec::new();
        if let Some(prover) = issuer_mldsa.as_ref() {
            let (job_shapes, job_streams) = prover.keccak_jobs();
            shapes.extend(job_shapes);
            streams.extend(job_streams);
        }
        if let Some(expand_a) = ts13_expand_a.as_ref() {
            let (job_shapes, job_streams) = expand_a
                .keccak_jobs()
                .map_err(|error| Error::Prove(format!("TS13 private ExpandA jobs: {error}")))?;
            shapes.extend(job_shapes);
            streams.extend(job_streams);
        }
        for prover in [&device_mldsa, &revocation_mldsa].into_iter().flatten() {
            let (job_shapes, job_streams) = prover.keccak_jobs();
            shapes.extend(job_shapes);
            streams.extend(job_streams);
        }
        #[cfg(feature = "unlink-spikes")]
        append_dummy_jobs(&mut shapes, &mut streams, unlink_spike.dummy_keccak_jobs);
        (!shapes.is_empty())
            .then(|| KeccakServiceProver::new(shapes, streams, mldsa_keccak_handle.clone()))
    };
    #[cfg(feature = "unlink-spikes")]
    let mut unlink_spike_io = (unlink_spike.dummy_keccak_jobs > 0).then(|| {
        MdocUnlinkSpikeIo::new(unlink_spike.dummy_keccak_jobs, mldsa_keccak_handle.clone())
    });
    // Constant-width padded-stream exposure requires a single-message SHA
    // instance. Keep one namespaced instance per attribute, all at the same
    // public log, while sharing the global tables.
    let merged_sha_log_n_rows = shared_sha_log;
    let mut attribute_shas: Vec<_> = attribute_sha_params
        .iter()
        .zip(&attribute_exposures)
        .enumerate()
        .map(|(index, ((witness, _), exposure))| {
            Sha256Prover::new(witness, shared_sha_log, MAX_ROUND_GROUP_BITS)
                .with_instance_namespace(format!("mdoc/attribute-sha/{index}"))
                .with_digest_handle(attribute_digests[index].clone())
                .with_field_handle(exposure.clone(), attribute_fields[index].clone())
                .with_shared_tables(sha_table_relations.clone())
        })
        .collect();
    let mut mso_sha = mso_sha_witness.as_ref().map(|witness| {
        let padded_len = witness.padding.padded.len();
        Sha256Prover::new(witness, MDOC_MSO_SHA_LOG_SIZE, MAX_ROUND_GROUP_BITS)
            .with_instance_namespace(MDOC_MSO_SHA_NAMESPACE)
            .with_digest_handle(
                mso_digest
                    .clone()
                    .expect("TS13 MSO digest handle exists with its SHA witness"),
            )
            .with_field_handle(
                FieldExposure::from_full_padded_stream(MDOC_MSO_SHA_STREAM_FIELD_ID, padded_len),
                mso_stream_field
                    .clone()
                    .expect("TS13 MSO stream handle exists with its SHA witness"),
            )
            .with_shared_tables(sha_table_relations.clone())
    });

    let mut mdoc_window_bind = MdocWindowBind::new_for_attributes(
        mdoc_window_bind_rows_from(statement),
        attribute_fields.clone(),
    );
    let age_public = statement.policy.age_public_input();
    let nat_public = nat_public_input_for(statement);
    let age_dob = DateOfBirth(predicates::Date {
        year: u32::from(u16::from_be_bytes([
            extracted.birth_date_bytes[0],
            extracted.birth_date_bytes[1],
        ])),
        month: u32::from(extracted.birth_date_bytes[2]),
        day: u32::from(extracted.birth_date_bytes[3]),
    });
    let nat_private = predicates::NatPrivateInput {
        nationalities: extracted.nationalities.clone(),
    };
    let mut age = if let Some(index) = statement.age_attribute_index() {
        let age = AgeRangeCheck::new(PcsConfig::default())
            .prover(&age_public, &age_dob)
            .map_err(Error::AgePrepare)?;
        Some(age.with_dob_binding(attribute_fields[index].clone()))
    } else {
        None
    };
    let mut nat = if let Some(index) = statement.nationality_attribute_index() {
        Some(
            NationalityPredicate::new(PcsConfig::default())
                .prover(&nat_public, &nat_private)
                .map_err(Error::NatPrepare)?
                .with_nat_binding(attribute_fields[index].clone()),
        )
    } else {
        None
    };
    let mut ts13_revocation_public = has_ts13_revocation.then(|| {
        MdocRevocationPublicBind::new(
            statement
                .ts13_revocation
                .clone()
                .expect("revocation shape was validated"),
        )
    });
    let mut ts13_revocation_range = has_ts13_revocation.then(|| {
        let range = statement
            .ts13_revocation_range
            .clone()
            .expect("proving revocation shape includes the private range");
        let mso_digest_bytes: [u8; 32] = Sha256::digest(&extracted.mso).into();
        MdocRevocationRangeBind::prover(
            range,
            mso_digest_bytes,
            mso_digest
                .clone()
                .expect("TS13 MSO digest relation exists with revocation"),
            statement
                .ts13_revocation
                .as_ref()
                .expect("revocation shape was validated")
                .epoch,
            revocation_message_field
                .clone()
                .expect("TS13 revocation message relation exists with revocation"),
        )
    });

    let (stark_proof, post_interaction_payloads, ts13_demo_circuit_geometry) = {
        let mut modules: Vec<&mut dyn AirProver> = Vec::new();
        if is_ts13_demo {
            collect_ts13_demo_modules!(
                modules;
                sha_tables = &mut sha_tables,
                range_tables = mldsa_range_table
                    .as_mut()
                    .expect("TS13 shared range table exists"),
                keccak_service = mldsa_keccak_service
                    .as_mut()
                    .expect("TS13 Keccak service exists"),
                public_context = ts13_public_context
                    .as_mut()
                    .expect("TS13 public context exists"),
                issuer_message = &mut issuer_message_provider,
                issuer_mldsa = issuer_mldsa.as_mut().expect("TS13 issuer ML-DSA exists"),
                item_shas = &mut attribute_shas,
                mso_sha = mso_sha.as_mut().expect("TS13 MSO SHA exists"),
                item_parsers = &mut mdoc_cbor_streams,
                item_binders = &mut private_item_binds,
                mso_binder = &mut private_mso_bind,
                mso_validity = ts13_mso_validity
                    .as_mut()
                    .expect("TS13 exact validity exists"),
                value_digests = &mut value_digests_scan,
                expand_a = ts13_expand_a
                    .as_mut()
                    .expect("TS13 private ExpandA exists"),
                device_key = ts13_device_key_bind
                    .as_mut()
                    .expect("TS13 private device-key binder exists"),
                device_mldsa = device_mldsa
                    .as_mut()
                    .expect("TS13 private device ML-DSA exists"),
                revocation_range = ts13_revocation_range
                    .as_mut()
                    .expect("TS13 revocation range exists"),
                revocation_mldsa = revocation_mldsa
                    .as_mut()
                    .expect("TS13 revocation ML-DSA exists"),
                revocation_public = ts13_revocation_public
                    .as_mut()
                    .expect("TS13 revocation public bind exists"),
            );
        } else {
            modules.push(&mut sha_tables);
            if let Some(range_table) = mldsa_range_table.as_mut() {
                modules.push(range_table);
            }
            if let Some(country_table) = country_code_table.as_mut() {
                modules.push(country_table);
            }
            if let Some(service) = mldsa_keccak_service.as_mut() {
                modules.push(service);
            }
            modules.push(&mut issuer_message_provider);
            #[cfg(feature = "unlink-spikes")]
            if let Some(spike_io) = unlink_spike_io.as_mut() {
                modules.push(spike_io);
            }
            if let Some(issuer) = issuer_mldsa.as_mut() {
                modules.push(issuer);
            }
            if let Some(device) = device_mldsa.as_mut() {
                modules.push(device);
            }
            for attribute_sha in &mut attribute_shas {
                modules.push(attribute_sha);
            }
            if let Some(mso_sha) = mso_sha.as_mut() {
                modules.push(mso_sha);
            }
            for parser in &mut mdoc_cbor_streams {
                modules.push(parser);
            }
            for item_bind in &mut private_item_binds {
                modules.push(item_bind);
            }
            modules.push(&mut private_mso_bind);
            modules.push(&mut value_digests_scan);
            if let Some(revocation_range) = ts13_revocation_range.as_mut() {
                modules.push(revocation_range);
            }
            if let Some(revocation_mldsa) = revocation_mldsa.as_mut() {
                modules.push(revocation_mldsa);
            }
            modules.push(&mut mdoc_window_bind);
            if let Some(age) = age.as_mut() {
                modules.push(age);
            }
            if let Some(nat) = nat.as_mut() {
                modules.push(nat);
            }
            if let Some(revocation_public) = ts13_revocation_public.as_mut() {
                modules.push(revocation_public);
            }
        }
        let (stark_proof, post_interaction_payloads) =
            air_core::prove_with_post_interaction(modules.as_mut_slice(), config)
                .map_err(|e| Error::Prove(format!("{e:?}")))?;
        let geometry = is_ts13_demo.then(|| capture_ts13_demo_circuit_geometry(&modules));
        (stark_proof, post_interaction_payloads, geometry)
    };
    Ok(MdocCircuitProof {
        stark_proof,
        sha_tables_interaction_claim: sha_tables.interaction_claim().clone(),
        mldsa: issuer_mldsa.as_ref().map(MdocMlDsaClaims::from_prover),
        device_mldsa: device_mldsa.as_ref().map(MdocMlDsaClaims::from_prover),
        revocation_mldsa: revocation_mldsa.as_ref().map(MdocMlDsaClaims::from_prover),
        mldsa_range_table_claimed_sum: mldsa_range_table
            .as_ref()
            .map(SharedRangeTable::claimed_sum),
        keccak_service_claimed_sums: mldsa_keccak_service
            .as_ref()
            .map(|service| service.claimed_sums()),
        private_issuer_message_interaction_claim: issuer_message_provider.claim().clone(),
        merged_sha_log_n_rows: Some(merged_sha_log_n_rows),
        merged_sha_slot_log: Some(shared_sha_log),
        attribute_sha_interaction_claims: attribute_shas
            .iter()
            .map(|sha| sha.interaction_claim().clone())
            .collect(),
        mso_sha_interaction_claim: mso_sha.as_ref().map(|sha| sha.interaction_claim().clone()),
        private_mso_bind_interaction_claim: private_mso_bind.interaction_claim().clone(),
        country_code_table_claimed_sum: country_code_table
            .as_ref()
            .map(MdocCountryCodeTable::claimed_sum),
        private_item_interaction_claims: private_item_binds
            .iter()
            .map(|bind| bind.claim().clone())
            .collect(),
        value_digests_scan_interaction_claim: value_digests_scan.claim().clone(),
        mdoc_window_bind_interaction_claim: (!is_ts13_demo)
            .then(|| mdoc_window_bind.interaction_claim().clone()),
        mdoc_cbor_interaction_claims: mdoc_cbor_streams
            .iter()
            .map(|parser| parser.interaction_claim().clone())
            .collect(),
        ts13_expand_a_claim: ts13_expand_a.as_ref().map(ExpandAProver::claim),
        ts13_device_key_bind_interaction_claim: ts13_device_key_bind
            .as_ref()
            .map(|bind| bind.interaction_claim().clone()),
        ts13_mso_validity_interaction_claim: ts13_mso_validity
            .as_ref()
            .map(|validity| validity.interaction_claim().clone()),
        ts13_revocation_range_interaction_claim: ts13_revocation_range
            .as_ref()
            .map(|range| range.interaction_claim().clone()),
        age_public: age.as_ref().map(|_| age_public),
        // Q-015 §4b: no blinder pair on the age/nat predicate sums. The
        // verifier RECOMPUTES these from the public statement (that is the
        // public-binding fix), so a blinder term here would either break the
        // recomputation or have to live in a verifier-recomputed public sum,
        // which the pair rules forbid.
        age_claimed_sums: age.as_ref().map(|age| age.claimed_sums()),
        nat_public: nat.as_ref().map(|_| nat_public),
        nat_claimed_sums: nat.as_ref().map(|nat| nat.claimed_sums()),
        post_interaction_payloads,
        ts13_demo_circuit_geometry,
    })
}

pub fn verify_mdoc_circuit(
    proof: &MdocCircuitProof,
    statement: &MdocCircuitStatement,
) -> Result<(), Error> {
    verify_mdoc_circuit_with_pcs_config(proof, statement, mdoc_production_pcs_config())
}

pub fn verify_mdoc_ts13_public_statement(
    proof: &MdocCircuitProof,
    statement: &MdocTs13PublicStatement,
) -> Result<(), Error> {
    let verifier_statement = statement.verifier_circuit_statement()?;
    verify_mdoc_circuit(proof, &verifier_statement)
}

pub fn verify_mdoc_ts13_demo_circuit(
    proof: &MdocCircuitProof,
    public: &MdocTs13DemoCircuitPublicInput,
) -> Result<(), Error> {
    let statement = public.verifier_statement()?;
    verify_mdoc_circuit_with_pcs_config_profiled_impl_core(
        proof,
        &statement,
        mdoc_production_pcs_config(),
        MdocTree0RootMode::Memoized,
        Some(public),
        #[cfg(feature = "unlink-spikes")]
        MdocUnlinkSpikeConfig::default(),
    )
    .map(|_| ())
}

pub fn verify_mdoc_circuit_with_pcs_config(
    proof: &MdocCircuitProof,
    statement: &MdocCircuitStatement,
    expected_pcs_config: PcsConfig,
) -> Result<(), Error> {
    verify_mdoc_circuit_with_pcs_config_profiled(proof, statement, expected_pcs_config).map(|_| ())
}

pub fn verify_mdoc_circuit_with_pcs_config_profiled(
    proof: &MdocCircuitProof,
    statement: &MdocCircuitStatement,
    expected_pcs_config: PcsConfig,
) -> Result<MdocCircuitVerifyProfile, Error> {
    verify_mdoc_circuit_with_pcs_config_profiled_impl(
        proof,
        statement,
        expected_pcs_config,
        MdocTree0RootMode::Memoized,
    )
}

/// Recompute the canonical tree-0 root and compare it with any memoized value.
/// This is a deliberately slower audit/test path; production verification uses
/// [`verify_mdoc_circuit_with_pcs_config_profiled`].
#[doc(hidden)]
pub fn verify_mdoc_circuit_with_pcs_config_profiled_fresh(
    proof: &MdocCircuitProof,
    statement: &MdocCircuitStatement,
    expected_pcs_config: PcsConfig,
) -> Result<MdocCircuitVerifyProfile, Error> {
    verify_mdoc_circuit_with_pcs_config_profiled_impl(
        proof,
        statement,
        expected_pcs_config,
        MdocTree0RootMode::FreshAudit,
    )
}

/// Fresh verification mirror for [`prove_mdoc_circuit_keccak_scale_spike`].
#[cfg(feature = "unlink-spikes")]
#[doc(hidden)]
pub fn verify_mdoc_circuit_keccak_scale_spike_fresh(
    proof: &MdocCircuitProof,
    statement: &MdocCircuitStatement,
    dummy_keccak_jobs: usize,
) -> Result<MdocCircuitVerifyProfile, Error> {
    validate_unlink_spike_dummy_jobs(dummy_keccak_jobs, "verify")?;
    verify_mdoc_circuit_with_pcs_config_profiled_impl_core(
        proof,
        statement,
        mdoc_production_pcs_config(),
        MdocTree0RootMode::FreshAudit,
        None,
        MdocUnlinkSpikeConfig { dummy_keccak_jobs },
    )
}

#[derive(Clone, Copy)]
enum MdocTree0RootMode {
    Memoized,
    FreshAudit,
}

fn verify_mdoc_circuit_with_pcs_config_profiled_impl(
    proof: &MdocCircuitProof,
    statement: &MdocCircuitStatement,
    expected_pcs_config: PcsConfig,
    tree0_root_mode: MdocTree0RootMode,
) -> Result<MdocCircuitVerifyProfile, Error> {
    verify_mdoc_circuit_with_pcs_config_profiled_impl_core(
        proof,
        statement,
        expected_pcs_config,
        tree0_root_mode,
        None,
        #[cfg(feature = "unlink-spikes")]
        MdocUnlinkSpikeConfig::default(),
    )
}

fn verify_mdoc_circuit_with_pcs_config_profiled_impl_core(
    proof: &MdocCircuitProof,
    statement: &MdocCircuitStatement,
    expected_pcs_config: PcsConfig,
    tree0_root_mode: MdocTree0RootMode,
    ts13_demo_public: Option<&MdocTs13DemoCircuitPublicInput>,
    #[cfg(feature = "unlink-spikes")] unlink_spike: MdocUnlinkSpikeConfig,
) -> Result<MdocCircuitVerifyProfile, Error> {
    let total_start = Instant::now();
    let is_ts13_demo = ts13_demo_public.is_some();
    validate_mdoc_circuit_statement_shape(statement, "verify", is_ts13_demo)?;
    validate_mldsa_public_keys(statement, "verify")?;
    validate_public_auth_projection(statement)?;
    let has_ts13_revocation = validate_ts13_revocation_shape(statement, false, "verify")?;
    if is_ts13_demo && !has_ts13_revocation {
        return Err(Error::Verify(
            "TS13 demo proof is missing revocation".to_string(),
        ));
    }
    let issuer_public_message = false;
    match &proof.mldsa {
        Some(claims) if claims.has_expected_shape(issuer_public_message) => {}
        _ => {
            return Err(Error::Verify(
                "mdoc proof ML-DSA issuer claim tree has the wrong shape".to_string(),
            ))
        }
    }
    match &proof.device_mldsa {
        Some(claims)
            if if is_ts13_demo {
                claims.group_evals.len() == stwo_mldsa::statement::n_private_key_group_evals()
                    && claims.claimed_sums.len()
                        == stwo_mldsa::statement::hosted_private_key_claimed_sums_len()
            } else {
                claims.has_expected_shape(true)
            } => {}
        _ => {
            return Err(Error::Verify(
                "mdoc proof ML-DSA device claim tree has the wrong shape".to_string(),
            ))
        }
    }
    if is_ts13_demo {
        if proof.ts13_expand_a_claim.is_none()
            || proof.ts13_device_key_bind_interaction_claim.is_none()
            || proof.ts13_mso_validity_interaction_claim.is_none()
            || proof.mdoc_window_bind_interaction_claim.is_some()
        {
            return Err(Error::Verify(
                "TS13 demo proof has the wrong private-device claim shape".to_string(),
            ));
        }
    } else if proof.ts13_expand_a_claim.is_some()
        || proof.ts13_device_key_bind_interaction_claim.is_some()
        || proof.ts13_mso_validity_interaction_claim.is_some()
        || proof.mdoc_window_bind_interaction_claim.is_none()
    {
        return Err(Error::Verify(
            "mdoc proof carries claims from a different profile".to_string(),
        ));
    }
    if proof.age_public
        != statement
            .age_attribute_index()
            .map(|_| statement.policy.age_public_input())
    {
        return Err(Error::AgePolicyMismatch);
    }
    if proof.nat_public
        != statement
            .nationality_attribute_index()
            .map(|_| nat_public_input_for(statement))
    {
        return Err(Error::NatPolicyMismatch);
    }

    if proof.ts13_revocation_range_interaction_claim.is_some() != has_ts13_revocation {
        return Err(Error::Verify(
            "mdoc proof revocation layout mismatch".to_string(),
        ));
    }
    if proof.mso_sha_interaction_claim.is_some() != has_ts13_revocation {
        return Err(Error::Verify(
            "mdoc proof private MSO SHA layout mismatch".to_string(),
        ));
    }
    if proof.merged_sha_log_n_rows.is_none()
        || proof.merged_sha_slot_log.is_none()
        || proof.attribute_sha_interaction_claims.len() != statement.attributes.len()
    {
        return Err(Error::Verify(
            "mdoc proof merged SHA layout does not match the statement".to_string(),
        ));
    }
    // Sanity-bound the proof-carried schedule so a malformed proof errors
    // instead of panicking inside the schedule constructors. The values are
    // transcript-mixed and layout-determining, so a lie cannot verify.
    if let (Some(slot_log), Some(log_n_rows)) =
        (proof.merged_sha_slot_log, proof.merged_sha_log_n_rows)
    {
        let expected_log = statement
            .attributes
            .iter()
            .map(|attribute| {
                min_log_size(
                    usize::from(attribute.item_padded_len) / stwo_sha256::constants::BLOCK_BYTES,
                )
            })
            .max()
            .expect("attribute count is shape-gated to be nonzero");
        if slot_log != expected_log || log_n_rows != expected_log {
            return Err(Error::Verify(
                "mdoc proof attribute SHA schedule does not match the statement".to_string(),
            ));
        }
    }
    if proof.private_item_interaction_claims.len() != statement.attributes.len() {
        return Err(Error::Verify(
            "mdoc proof private-item claim shape mismatch".to_string(),
        ));
    }
    if proof.mdoc_cbor_interaction_claims.len() != statement.attributes.len() * 2 {
        return Err(Error::Verify(
            "mdoc proof private-item parser claim shape mismatch".to_string(),
        ));
    }
    if proof.country_code_table_claimed_sum.is_some()
        != statement.nationality_attribute_index().is_some()
    {
        return Err(Error::Verify(
            "mdoc proof country-code table shape mismatch".to_string(),
        ));
    }
    if proof.age_claimed_sums.is_some() != statement.age_attribute_index().is_some()
        || proof.nat_claimed_sums.is_some() != statement.nationality_attribute_index().is_some()
    {
        return Err(Error::Verify(
            "mdoc proof predicate claim shape mismatch".to_string(),
        ));
    }
    match (&proof.revocation_mldsa, has_ts13_revocation) {
        (Some(claims), true) if claims.has_expected_shape(false) => {}
        (None, false) => {}
        _ => {
            return Err(Error::Verify(
                "mdoc proof ML-DSA revocation claim tree does not match the statement".to_string(),
            ))
        }
    }
    let has_mldsa =
        proof.mldsa.is_some() || proof.device_mldsa.is_some() || proof.revocation_mldsa.is_some();
    match (&proof.mldsa_range_table_claimed_sum, has_mldsa) {
        (Some(_), true) | (None, false) => {}
        _ => {
            return Err(Error::Verify(
                "mdoc proof shared ML-DSA range-table claim does not match the statement"
                    .to_string(),
            ))
        }
    }
    match &proof.keccak_service_claimed_sums {
        Some(sums)
            if sums.len() == stwo_mldsa::stwo_keccak::service::service_claimed_sums_len() => {}
        _ => {
            return Err(Error::Verify(
                "mdoc proof keccak service claims do not match the statement".to_string(),
            ))
        }
    }
    // The keccak service's round LogUp is GKR-offloaded: its proof blob rides
    // in `post_interaction_payloads`. The payload-aware verify entry hands each
    // module its slot in prove order; the service `verify_post_interaction`
    // fails closed on a missing/corrupt blob (an empty blob fails GKR decode).
    let issuer_message_field = SharedFieldRelation::new();
    let revocation_message_field = has_ts13_revocation.then(SharedFieldRelation::new);
    let attribute_count = statement.attributes.len();
    let attribute_digests: Vec<_> = (0..attribute_count)
        .map(|_| SharedDigestRelation::new())
        .collect();
    let mso_digest = has_ts13_revocation.then(SharedDigestRelation::new);
    let mso_stream_field = has_ts13_revocation.then(SharedFieldRelation::new);
    let mso_start_handle = SharedMdocMsoStartRelation::new();
    let device_pk_start_handle = is_ts13_demo.then(SharedMdocDevicePkStartRelation::new);
    let validity_handle = is_ts13_demo.then(SharedMdocMsoValidityBytesRelation::new);
    let expand_a_bindings = is_ts13_demo.then(ExpandABindings::new);
    let t1_handle = is_ts13_demo.then(SharedT1CellRelation::new);
    let country_code_handle = SharedMdocCountryCodeRelation::new();
    // The proof-wide keccak service's relations handle (mirror of the prover).
    let mldsa_keccak_handle = SharedKeccakRelations::new();
    let mldsa_range_handle = SharedRangeRelation::new();
    let attribute_fields: Vec<_> = (0..attribute_count)
        .map(|_| SharedFieldRelation::new())
        .collect();
    let sha_table_relations = SharedShaTableRelations::new();
    if proof.stark_proof.config != expected_pcs_config {
        return Err(Error::WeakConfig {
            got: proof.stark_proof.config,
            expected: expected_pcs_config,
        });
    }
    let tree0_cache_key = mdoc_tree0_cache_key(
        proof,
        statement,
        expected_pcs_config,
        #[cfg(feature = "unlink-spikes")]
        unlink_spike,
    )?;
    let cached_preprocessed_root = mdoc_tree0_cached_root(&tree0_cache_key)?;
    let tree0_cache_hit = matches!(tree0_root_mode, MdocTree0RootMode::Memoized)
        && cached_preprocessed_root.is_some();

    let mut sha_tables = ShaTablesVerifier::new(
        proof.sha_tables_interaction_claim.clone(),
        sha_table_relations.clone(),
    );
    let issuer_message_len = statement
        .issuer_input
        .as_mldsa()
        .ok_or_else(|| Error::Verify("mdoc issuer input is not ML-DSA".to_string()))?
        .message
        .len();
    let mut issuer_message_provider = MdocPrivateMessageProvider::verifier(
        issuer_message_len,
        issuer_message_field.clone(),
        proof.private_issuer_message_interaction_claim.clone(),
    )
    .map_err(|error| Error::Verify(format!("private issuer message provider: {error}")))?;
    // The verifier knows only the issuer message length. Its zero bytes are
    // layout placeholders; the provider/hosted bridge relation carries the
    // signed private Sig_structure.
    let mut issuer_mldsa = match (statement.issuer_input.as_mldsa(), &proof.mldsa) {
        (Some(input), Some(claims)) => {
            let mut input = input.clone();
            input.tr = stwo_mldsa::statement::native_tr(&input);
            input.message.fill(0);
            Some(
                MlDsaStatementVerifier::hosted(
                    input,
                    claims.group_evals.clone(),
                    claims.claimed_sums.clone(),
                    issuer_message_field.clone(),
                    mldsa_range_handle.clone(),
                    mldsa_keccak_handle.clone(),
                )
                .with_instance_namespace(MDOC_ISSUER_MLDSA_NAMESPACE)
                .with_stream_base(MDOC_ISSUER_MLDSA_STREAM_BASE)
                .with_private_message(),
            )
        }
        _ => None,
    };
    // Hosted ML-DSA device verifier, public-message mode (S4): rebuilt from
    // the statement's public input + the proof's claim tree.
    let mut device_mldsa = if is_ts13_demo {
        let input = statement
            .device_input
            .private_key_public_input()
            .ok_or_else(|| Error::Verify("TS13 verifier received a device public key".to_string()))?
            .clone();
        let claims = proof
            .device_mldsa
            .as_ref()
            .expect("TS13 device claim shape was checked");
        Some(
            MlDsaStatementVerifier::hosted_private_key(
                input,
                claims.group_evals.clone(),
                claims.claimed_sums.clone(),
                issuer_message_field.clone(),
                mldsa_range_handle.clone(),
                mldsa_keccak_handle.clone(),
                PrivateKeyEvalBindings::new(
                    expand_a_bindings
                        .as_ref()
                        .expect("TS13 ExpandA bindings exist")
                        .ntt
                        .clone(),
                    t1_handle.clone().expect("TS13 T1 handle exists"),
                ),
            )
            .map_err(|error| Error::Verify(format!("TS13 private device ML-DSA: {error}")))?
            .with_instance_namespace(MDOC_DEVICE_MLDSA_NAMESPACE)
            .with_stream_base(MDOC_DEVICE_MLDSA_STREAM_BASE),
        )
    } else {
        match (statement.device_input.as_mldsa(), &proof.device_mldsa) {
            (Some(input), Some(claims)) => {
                let mut input = input.clone();
                input.tr = stwo_mldsa::statement::native_tr(&input);
                Some(
                    MlDsaStatementVerifier::hosted_public(
                        input,
                        claims.group_evals.clone(),
                        claims.claimed_sums.clone(),
                        mldsa_range_handle.clone(),
                        mldsa_keccak_handle.clone(),
                    )
                    .with_instance_namespace(MDOC_DEVICE_MLDSA_NAMESPACE)
                    .with_stream_base(MDOC_DEVICE_MLDSA_STREAM_BASE),
                )
            }
            _ => None,
        }
    };
    // Hosted ML-DSA revocation verifier, private-message mode: the input is
    // rebuilt from the statement's PUBLIC key/signature bytes with 20 ZEROED
    // message bytes — the real id bounds never enter the verifier's inputs,
    // the transcript (only the length is mixed), or the serialized proof.
    let mut revocation_mldsa = match &proof.revocation_mldsa {
        Some(claims) => {
            ts13_revocation_mldsa_verifier_input(statement, vec![0u8; TS13_REVOCATION_MESSAGE_LEN])?
                .map(|input| {
                    MlDsaStatementVerifier::hosted(
                        *input,
                        claims.group_evals.clone(),
                        claims.claimed_sums.clone(),
                        revocation_message_field
                            .clone()
                            .expect("revocation field relation exists with a revocation signature"),
                        mldsa_range_handle.clone(),
                        mldsa_keccak_handle.clone(),
                    )
                    .with_instance_namespace(MDOC_REVOCATION_MLDSA_NAMESPACE)
                    .with_stream_base(MDOC_REVOCATION_MLDSA_STREAM_BASE)
                    .with_private_message()
                })
        }
        None => None,
    };
    let mut mldsa_range_table = proof
        .mldsa_range_table_claimed_sum
        .map(|claim| SharedRangeTable::verifier(claim, mldsa_range_handle.clone()));
    // The proof-wide keccak service verifier (S1): job shapes rebuilt from
    // PUBLIC data only, in the prover's fixed role order (issuer, device,
    // revocation) — message lengths from the statement (the revocation
    // message is the fixed 20-byte private-message window), sib stream
    // stream bases from the role constants. SIB is the fixed five-block
    // protocol resource cap for every role. Claimed sums come from the proof.
    let mut mldsa_keccak_service = proof.keccak_service_claimed_sums.as_ref().map(|sums| {
        let mut shapes = Vec::new();
        if let Some(input) = statement.issuer_input.as_mldsa() {
            shapes.extend(keccak_job_shapes(
                input.message.len(),
                MDOC_ISSUER_MLDSA_STREAM_BASE,
                issuer_public_message,
            ));
        }
        if is_ts13_demo {
            shapes.extend(
                stwo_mldsa::expand_a::shake128_job_shapes(MDOC_DEVICE_EXPAND_A_STREAM_BASE)
                    .expect("frozen TS13 ExpandA stream base is valid"),
            );
            shapes.extend(stwo_mldsa::statement::hosted_private_key_keccak_job_shapes(
                statement.device_input.message().len(),
                MDOC_DEVICE_MLDSA_STREAM_BASE,
            ));
        } else if let Some(input) = statement.device_input.as_mldsa() {
            shapes.extend(keccak_job_shapes(
                input.message.len(),
                MDOC_DEVICE_MLDSA_STREAM_BASE,
                true,
            ));
        }
        if proof.revocation_mldsa.is_some() {
            shapes.extend(keccak_job_shapes(
                TS13_REVOCATION_MESSAGE_LEN,
                MDOC_REVOCATION_MLDSA_STREAM_BASE,
                false,
            ));
        }
        #[cfg(feature = "unlink-spikes")]
        append_dummy_shapes(&mut shapes, unlink_spike.dummy_keccak_jobs);
        KeccakServiceVerifier::new(shapes, sums.clone(), mldsa_keccak_handle.clone())
    });
    #[cfg(feature = "unlink-spikes")]
    let mut unlink_spike_io = (unlink_spike.dummy_keccak_jobs > 0).then(|| {
        MdocUnlinkSpikeIo::new(unlink_spike.dummy_keccak_jobs, mldsa_keccak_handle.clone())
    });

    let attribute_exposures: Vec<_> = (0..statement.attributes.len())
        .map(|index| attribute_exposure(statement, index))
        .collect();
    let attribute_sha_log = proof
        .merged_sha_log_n_rows
        .expect("attribute SHA log shape-gated above");
    let mut attribute_shas: Vec<_> = attribute_exposures
        .iter()
        .enumerate()
        .map(|(index, exposure)| {
            Sha256Verifier::new(
                attribute_sha_log,
                MAX_ROUND_GROUP_BITS,
                proof.attribute_sha_interaction_claims[index].clone(),
            )
            .with_instance_namespace(format!("mdoc/attribute-sha/{index}"))
            .with_digest_handle(attribute_digests[index].clone())
            .with_field_handle(exposure.clone(), attribute_fields[index].clone())
            .with_shared_tables(sha_table_relations.clone())
        })
        .collect();
    let mso_sha_padded_len = has_ts13_revocation
        .then(|| {
            checked_sha256_padded_len(statement.mso_payload_len).ok_or_else(|| {
                Error::Verify("mdoc private MSO SHA padded length overflows".to_string())
            })
        })
        .transpose()?;
    let mut mso_sha = mso_sha_padded_len.map(|padded_len| {
        Sha256Verifier::new(
            MDOC_MSO_SHA_LOG_SIZE,
            MAX_ROUND_GROUP_BITS,
            proof
                .mso_sha_interaction_claim
                .clone()
                .expect("private MSO SHA claim shape-gated above"),
        )
        .with_instance_namespace(MDOC_MSO_SHA_NAMESPACE)
        .with_digest_handle(
            mso_digest
                .clone()
                .expect("TS13 MSO digest handle exists with revocation"),
        )
        .with_field_handle(
            FieldExposure::from_full_padded_stream(MDOC_MSO_SHA_STREAM_FIELD_ID, padded_len),
            mso_stream_field
                .clone()
                .expect("TS13 MSO stream handle exists with revocation"),
        )
        .with_shared_tables(sha_table_relations.clone())
    });
    let private_mso_spec =
        private_mso_bind_spec(statement, mso_sha_padded_len, is_ts13_demo, "verify")?;
    let mut private_mso_bind = MdocPrivateMsoBind::verifier(
        private_mso_spec,
        issuer_message_field.clone(),
        mso_stream_field.clone(),
        Some(mso_start_handle.clone()),
        device_pk_start_handle.clone(),
        validity_handle.clone(),
        proof.private_mso_bind_interaction_claim.clone(),
    )
    .map_err(|error| Error::Verify(format!("TS13 private MSO bind: {error}")))?;
    let mut ts13_public_context =
        ts13_demo_public.map(MdocTs13DemoCircuitPublicInput::context_bind);
    let mut ts13_expand_a = if is_ts13_demo {
        Some(
            ExpandAVerifier::new(
                proof
                    .ts13_expand_a_claim
                    .clone()
                    .expect("TS13 ExpandA claim shape was checked"),
                MDOC_DEVICE_EXPAND_A_NAMESPACE,
                MDOC_DEVICE_EXPAND_A_STREAM_BASE,
                mldsa_range_handle.clone(),
                mldsa_keccak_handle.clone(),
                expand_a_bindings
                    .clone()
                    .expect("TS13 ExpandA bindings exist"),
            )
            .map_err(|error| Error::Verify(format!("TS13 private ExpandA: {error}")))?,
        )
    } else {
        None
    };
    let mut ts13_device_key_bind = if is_ts13_demo {
        Some(
            MdocPrivateDeviceKeyBind::verifier(
                issuer_message_len,
                issuer_message_field.clone(),
                mldsa_range_handle.clone(),
                expand_a_bindings
                    .as_ref()
                    .expect("TS13 ExpandA bindings exist")
                    .rho
                    .clone(),
                t1_handle.clone().expect("TS13 T1 handle exists"),
                device_pk_start_handle
                    .clone()
                    .expect("TS13 device-key start relation exists"),
                proof
                    .ts13_device_key_bind_interaction_claim
                    .clone()
                    .expect("TS13 device-key claim shape was checked"),
            )
            .map_err(|error| Error::Verify(format!("TS13 private device-key bind: {error}")))?,
        )
    } else {
        None
    };
    let mut ts13_mso_validity = if let Some(public) = ts13_demo_public {
        Some(
            MdocPrivateMsoValidityV2::verifier(
                MdocPrivateMsoValiditySpec {
                    timestamp_epoch_seconds: public.timestamp_epoch_seconds,
                    verification_timestamp_rfc3339_utc: public.verification_timestamp_rfc3339_utc,
                },
                mldsa_range_handle.clone(),
                validity_handle
                    .clone()
                    .expect("TS13 validity relation exists"),
                proof
                    .ts13_mso_validity_interaction_claim
                    .clone()
                    .expect("TS13 validity claim shape was checked"),
            )
            .map_err(|error| Error::Verify(format!("TS13 private MSO validity: {error}")))?,
        )
    } else {
        None
    };

    let private_item_profile = if is_ts13_demo {
        MdocPrivateItemProfile::Ts13Demo
    } else if has_ts13_revocation {
        MdocPrivateItemProfile::Ts13
    } else {
        MdocPrivateItemProfile::Product
    };
    let value_digests_profile = if has_ts13_revocation {
        MdocValueDigestsProfile::Ts13
    } else {
        MdocValueDigestsProfile::Product
    };
    let mut private_item_handles = Vec::with_capacity(attribute_count);
    let mut private_item_binds = Vec::with_capacity(attribute_count);
    let mut mdoc_cbor_streams = Vec::with_capacity(attribute_count * 2);
    for (index, attribute) in statement.attributes.iter().enumerate() {
        let request_mode = match attribute.mode {
            MdocDisclosureMode::ValueEquality(_) => MdocPrivateItemRequestMode::ValueEquality,
            MdocDisclosureMode::AgeOver => MdocPrivateItemRequestMode::BirthDate,
            MdocDisclosureMode::Alpha2Set => MdocPrivateItemRequestMode::Nationality,
        };
        let field_ids = MdocPrivateItemFieldIds {
            outer_stream: MdocStatementAttribute::outer_stream_field_id(index),
            inner_stream: MdocStatementAttribute::inner_stream_field_id(index),
            element_identifier: MdocStatementAttribute::element_field_id(index),
            element_value: match request_mode {
                MdocPrivateItemRequestMode::ValueEquality => {
                    MdocStatementAttribute::value_field_id(index)
                }
                MdocPrivateItemRequestMode::BirthDate => field_id::DOB,
                MdocPrivateItemRequestMode::Nationality => field_id::NATIONALITY,
            },
        };
        let handles = MdocPrivateItemHandles::fresh(
            attribute_fields[index].clone(),
            country_code_handle.clone(),
        );
        let item_bind = MdocPrivateItemBind::verifier(
            index,
            private_item_profile,
            request_mode,
            usize::from(attribute.item_padded_len),
            field_ids,
            handles.clone(),
            proof.private_item_interaction_claims[index].clone(),
        )
        .map_err(|error| Error::Verify(format!("private IssuerSignedItem {index}: {error}")))?;
        let outer_parser = MdocCborStream::verifier(
            MdocCborInputMode::ShaPadded,
            field_ids.outer_stream,
            item_bind.outer_parser_log_size(),
            handles.item_fields.clone(),
            Some(handles.outer_parsed.clone()),
            proof.mdoc_cbor_interaction_claims[index * 2].clone(),
        )
        .map_err(|error| {
            Error::Verify(format!("IssuerSignedItem {index} outer parser: {error}"))
        })?;
        let inner_parser = MdocCborStream::verifier(
            MdocCborInputMode::Raw,
            field_ids.inner_stream,
            item_bind.inner_parser_log_size(),
            handles.inner_raw.clone(),
            Some(handles.inner_parsed.clone()),
            proof.mdoc_cbor_interaction_claims[index * 2 + 1].clone(),
        )
        .map_err(|error| {
            Error::Verify(format!("IssuerSignedItem {index} inner parser: {error}"))
        })?;
        private_item_handles.push(handles);
        private_item_binds.push(item_bind);
        mdoc_cbor_streams.push(outer_parser);
        mdoc_cbor_streams.push(inner_parser);
    }
    let scanner_handles = MdocValueDigestsScanHandles {
        issuer_message: issuer_message_field.clone(),
        mso_start: mso_start_handle.clone(),
        items: private_item_handles
            .iter()
            .zip(&attribute_digests)
            .map(|(item, digest)| MdocValueDigestItemHandles {
                digest_id: item.digest_id.clone(),
                digest: digest.clone(),
            })
            .collect(),
    };
    let scanner_spec = MdocValueDigestsScanSpec {
        issuer_message_len,
        mso_len: statement.mso_payload_len,
        namespace: statement.namespace.clone(),
        profile: value_digests_profile,
        attribute_count,
    };
    let mut value_digests_scan = MdocValueDigestsScan::verifier(
        scanner_spec,
        scanner_handles,
        proof.value_digests_scan_interaction_claim.clone(),
    )
    .map_err(|error| Error::Verify(format!("private valueDigests scanner: {error}")))?;
    let mut country_code_table = proof
        .country_code_table_claimed_sum
        .map(|sum| MdocCountryCodeTable::verifier(sum, country_code_handle.clone()));
    let mut mdoc_window_bind = if is_ts13_demo {
        None
    } else {
        Some(MdocWindowBind::verifier_for_attributes(
            mdoc_window_bind_rows_from(statement),
            attribute_fields.clone(),
            proof
                .mdoc_window_bind_interaction_claim
                .clone()
                .ok_or_else(|| {
                    Error::Verify("mdoc proof is missing the semantic window claim".to_string())
                })?,
        ))
    };
    let mut age = if let Some(index) = statement.age_attribute_index() {
        let public = proof.age_public.as_ref().ok_or(Error::AgePolicyMismatch)?;
        let claimed_sums = proof
            .age_claimed_sums
            .as_ref()
            .ok_or(Error::AgePolicyMismatch)?;
        let age = AgeRangeCheck::new(PcsConfig::default())
            .verifier(public, claimed_sums)
            .map_err(Error::AgePrepare)?;
        Some(age.with_dob_binding(attribute_fields[index].clone()))
    } else {
        None
    };
    let mut nat = if let Some(index) = statement.nationality_attribute_index() {
        let public = proof.nat_public.as_ref().ok_or(Error::NatPolicyMismatch)?;
        let claimed_sums = proof
            .nat_claimed_sums
            .as_ref()
            .ok_or(Error::NatPolicyMismatch)?;
        Some(
            NationalityPredicate::new(PcsConfig::default())
                .verifier(public, claimed_sums)
                .map_err(Error::NatPrepare)?
                .with_nat_binding(attribute_fields[index].clone()),
        )
    } else {
        None
    };
    let mut ts13_revocation_public = has_ts13_revocation.then(|| {
        MdocRevocationPublicBind::new(
            statement
                .ts13_revocation
                .clone()
                .expect("revocation shape was validated"),
        )
    });
    let mut ts13_revocation_range = has_ts13_revocation.then(|| {
        MdocRevocationRangeBind::verifier(
            mso_digest
                .clone()
                .expect("TS13 MSO digest relation exists with revocation"),
            statement
                .ts13_revocation
                .as_ref()
                .expect("revocation shape was validated")
                .epoch,
            revocation_message_field
                .clone()
                .expect("TS13 revocation message relation exists with revocation"),
            proof
                .ts13_revocation_range_interaction_claim
                .clone()
                .expect("revocation range interaction claim exists when range is set"),
        )
    });

    let mut modules: Vec<&mut dyn Air> = Vec::new();
    if is_ts13_demo {
        collect_ts13_demo_modules!(
            modules;
            sha_tables = &mut sha_tables,
            range_tables = mldsa_range_table
                .as_mut()
                .expect("TS13 shared range table exists"),
            keccak_service = mldsa_keccak_service
                .as_mut()
                .expect("TS13 Keccak service exists"),
            public_context = ts13_public_context
                .as_mut()
                .expect("TS13 public context exists"),
            issuer_message = &mut issuer_message_provider,
            issuer_mldsa = issuer_mldsa.as_mut().expect("TS13 issuer ML-DSA exists"),
            item_shas = &mut attribute_shas,
            mso_sha = mso_sha.as_mut().expect("TS13 MSO SHA exists"),
            item_parsers = &mut mdoc_cbor_streams,
            item_binders = &mut private_item_binds,
            mso_binder = &mut private_mso_bind,
            mso_validity = ts13_mso_validity
                .as_mut()
                .expect("TS13 exact validity exists"),
            value_digests = &mut value_digests_scan,
            expand_a = ts13_expand_a
                .as_mut()
                .expect("TS13 private ExpandA exists"),
            device_key = ts13_device_key_bind
                .as_mut()
                .expect("TS13 private device-key binder exists"),
            device_mldsa = device_mldsa
                .as_mut()
                .expect("TS13 private device ML-DSA exists"),
            revocation_range = ts13_revocation_range
                .as_mut()
                .expect("TS13 revocation range exists"),
            revocation_mldsa = revocation_mldsa
                .as_mut()
                .expect("TS13 revocation ML-DSA exists"),
            revocation_public = ts13_revocation_public
                .as_mut()
                .expect("TS13 revocation public bind exists"),
        );
    } else {
        modules.push(&mut sha_tables);
        if let Some(range_table) = mldsa_range_table.as_mut() {
            modules.push(range_table);
        }
        if let Some(country_table) = country_code_table.as_mut() {
            modules.push(country_table);
        }
        if let Some(service) = mldsa_keccak_service.as_mut() {
            modules.push(service);
        }
        modules.push(&mut issuer_message_provider);
        #[cfg(feature = "unlink-spikes")]
        if let Some(spike_io) = unlink_spike_io.as_mut() {
            modules.push(spike_io);
        }
        if let Some(issuer) = issuer_mldsa.as_mut() {
            modules.push(issuer);
        }
        if let Some(device) = device_mldsa.as_mut() {
            modules.push(device);
        }
        for attribute_sha in &mut attribute_shas {
            modules.push(attribute_sha);
        }
        if let Some(mso_sha) = mso_sha.as_mut() {
            modules.push(mso_sha);
        }
        for parser in &mut mdoc_cbor_streams {
            modules.push(parser);
        }
        for item_bind in &mut private_item_binds {
            modules.push(item_bind);
        }
        modules.push(&mut private_mso_bind);
        modules.push(&mut value_digests_scan);
        if let Some(revocation_range) = ts13_revocation_range.as_mut() {
            modules.push(revocation_range);
        }
        if let Some(revocation_mldsa) = revocation_mldsa.as_mut() {
            modules.push(revocation_mldsa);
        }
        modules.push(
            mdoc_window_bind
                .as_mut()
                .expect("product semantic window exists"),
        );
        if let Some(age) = age.as_mut() {
            modules.push(age);
        }
        if let Some(nat) = nat.as_mut() {
            modules.push(nat);
        }
        if let Some(revocation_public) = ts13_revocation_public.as_mut() {
            modules.push(revocation_public);
        }
    }
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let tree0_start = Instant::now();
        let expected_preprocessed_root = match tree0_root_mode {
            MdocTree0RootMode::Memoized => match cached_preprocessed_root.as_ref() {
                Some(root) => *root,
                None => air_core::compute_canonical_preprocessed_root(
                    modules.as_mut_slice(),
                    expected_pcs_config,
                )
                .map_err(air_core::VerifyError::Stark)?,
            },
            MdocTree0RootMode::FreshAudit => {
                let fresh = air_core::compute_canonical_preprocessed_root(
                    modules.as_mut_slice(),
                    expected_pcs_config,
                )
                .map_err(air_core::VerifyError::Stark)?;
                if cached_preprocessed_root
                    .as_ref()
                    .is_some_and(|cached| cached != &fresh)
                {
                    return Err(air_core::VerifyError::Stark(
                        stwo::core::verifier::VerificationError::InvalidStructure(
                            "mdoc tree-0 cache drift".to_string(),
                        ),
                    ));
                }
                fresh
            }
        };
        let tree0_canonical_root = tree0_start.elapsed();
        let stark_verify_start = Instant::now();
        air_core::verify_with_expected_preprocessed_root_and_payloads(
            modules.as_mut_slice(),
            &proof.stark_proof,
            Some(expected_preprocessed_root),
            &proof.post_interaction_payloads,
        )?;
        Ok((
            tree0_canonical_root,
            stark_verify_start.elapsed(),
            expected_preprocessed_root,
        ))
    })) {
        Ok(Ok((tree0_canonical_root, stark_verify, expected_preprocessed_root))) => {
            // Soundness/DoS boundary: a miss is memoized only after the whole
            // proof has verified against the verifier-recomputed root.
            if cached_preprocessed_root.is_none() {
                mdoc_tree0_cache_insert(tree0_cache_key, expected_preprocessed_root)?;
            }
            Ok(MdocCircuitVerifyProfile {
                total: total_start.elapsed(),
                tree0_canonical_root,
                stark_verify,
                tree0_cache_hit,
            })
        }
        Ok(Err(air_core::VerifyError::PreprocessedRootMismatch { got, expected })) => {
            Err(Error::PreprocessedRootMismatch { got, expected })
        }
        Ok(Err(error)) => Err(Error::Verify(format!("{error:?}"))),
        Err(_) => Err(Error::Verify(
            "malformed mdoc proof panicked during verification".to_string(),
        )),
    }
}

pub const MDOC_PRODUCTION_PCS_LOG_BLOWUP_FACTOR: u32 = 3;
pub const MDOC_PRODUCTION_PCS_QUERIES: usize = 36;
pub const MDOC_PRODUCTION_PCS_POW_BITS: u32 = 20;

pub fn mdoc_production_pcs_config() -> PcsConfig {
    // Blowup-3 prove-time flip 2026-07-21, rail relaxed to ~1.4MB per Lucas:
    // FRI (1,3,36,2)/pow20 (the Q5 buy-back point) replaces blowup-4/26q/pow25.
    // PCS query/PoW label: 36×3 + 20 = 128 bits (previous schedule 26×4 + 25 =
    // 129); both exceed the 108-bit OODS bound that dominates TS13's STARK
    // component, so composed soundness accounting is unchanged. The verifier
    // pins this exact config (see verify_mdoc_circuit_with_pcs_config) so an
    // old-config proof is rejected. This label is not a whole-system soundness
    // claim; TS13 accounts separately for OODS and binding-hash limits.
    PcsConfig {
        pow_bits: MDOC_PRODUCTION_PCS_POW_BITS,
        fri_config: FriConfig::new(
            1,
            MDOC_PRODUCTION_PCS_LOG_BLOWUP_FACTOR,
            MDOC_PRODUCTION_PCS_QUERIES,
            2,
        ),
        lifting_log_size: None,
    }
}

fn is_supported_mdoc_profile_version(version: &str) -> bool {
    matches!(version, MDOC_PROFILE_VERSION_V1 | MDOC_PROFILE_VERSION_V2)
}

fn numeric_country(alpha2: &str) -> Result<u32, MdocError> {
    celes::Country::from_alpha2(alpha2)
        .map(|country| country.value as u32)
        .map_err(|_| MdocError::InvalidNationality(alpha2.to_string()))
}

fn value_field<'a>(map: &'a [(Value, Value)], field: &'static str) -> Result<&'a Value, MdocError> {
    let key = Value::Text(field.to_string());
    let mut matches = map
        .iter()
        .filter_map(|(candidate, value)| (candidate == &key).then_some(value));
    let value = matches.next().ok_or(MdocError::MissingField(field))?;
    if matches.next().is_some() {
        return Err(MdocError::UnsupportedCircuitValue("duplicate text map key"));
    }
    Ok(value)
}

fn map_field<'a>(
    map: &'a [(Value, Value)],
    field: &'static str,
) -> Result<&'a [(Value, Value)], MdocError> {
    expect_map(value_field(map, field)?, field)
}

fn text_field<'a>(map: &'a [(Value, Value)], field: &'static str) -> Result<&'a str, MdocError> {
    expect_text(value_field(map, field)?, field)
}

fn u32_field(map: &[(Value, Value)], field: &'static str) -> Result<u32, MdocError> {
    expect_u32(value_field(map, field)?, field)
}

fn int_field(map: &[(Value, Value)], key: i128, field: &'static str) -> Result<i128, MdocError> {
    let mut matches = map.iter().filter_map(|(candidate, value)| {
        value_i128(candidate)
            .ok()
            .filter(|candidate| *candidate == key)
            .map(|_| value)
    });
    let value = matches.next().ok_or(MdocError::MissingField(field))?;
    if matches.next().is_some() {
        return Err(MdocError::UnsupportedCircuitValue(
            "duplicate integer map key",
        ));
    }
    value_i128(value)
}

fn bytes_int_field<'a>(
    map: &'a [(Value, Value)],
    key: i128,
    field: &'static str,
) -> Result<&'a [u8], MdocError> {
    let mut matches = map.iter().filter_map(|(candidate, value)| {
        value_i128(candidate)
            .ok()
            .filter(|candidate| *candidate == key)
            .map(|_| value)
    });
    let value = matches.next().ok_or(MdocError::MissingField(field))?;
    if matches.next().is_some() {
        return Err(MdocError::UnsupportedCircuitValue(
            "duplicate integer map key",
        ));
    }
    expect_bytes(value, field)
}

fn expect_map<'a>(
    value: &'a Value,
    field: &'static str,
) -> Result<&'a [(Value, Value)], MdocError> {
    match value {
        Value::Map(entries) => Ok(entries),
        _ => Err(MdocError::WrongType(field)),
    }
}

fn expect_text<'a>(value: &'a Value, field: &'static str) -> Result<&'a str, MdocError> {
    match value {
        Value::Text(text) => Ok(text),
        _ => Err(MdocError::WrongType(field)),
    }
}

fn expect_array<'a>(value: &'a Value, field: &'static str) -> Result<&'a [Value], MdocError> {
    match value {
        Value::Array(items) => Ok(items),
        _ => Err(MdocError::WrongType(field)),
    }
}

fn expect_bytes<'a>(value: &'a Value, field: &'static str) -> Result<&'a [u8], MdocError> {
    match value {
        Value::Bytes(bytes) => Ok(bytes),
        _ => Err(MdocError::WrongType(field)),
    }
}

fn expect_u32(value: &Value, field: &'static str) -> Result<u32, MdocError> {
    let int = value_i128(value)?;
    u32::try_from(int).map_err(|_| MdocError::WrongType(field))
}

fn value_i128(value: &Value) -> Result<i128, MdocError> {
    let Value::Integer(int) = value else {
        return Err(MdocError::WrongType("integer"));
    };
    Ok((*int).into())
}

fn expect_digest(value: &Value, field: &'static str) -> Result<[u8; 32], MdocError> {
    expect_32(expect_bytes(value, field)?, field)
}

fn expect_32(bytes: &[u8], field: &'static str) -> Result<[u8; 32], MdocError> {
    bytes.try_into().map_err(|_| MdocError::WrongType(field))
}

#[cfg(test)]
mod tree0_cache_key_tests {
    use super::*;

    fn material(
        issuer_mldsa_message_bytes: usize,
        device_mldsa_message_bytes: usize,
    ) -> MdocTree0CacheKeyMaterial {
        MdocTree0CacheKeyMaterial {
            version: 5,
            pcs_log_blowup_factor: 3,
            merged_sha_slot_log: 8,
            merged_sha_log_n_rows: 8,
            has_ts13_revocation: true,
            has_country_table: false,
            doctype_len: PID_DOCTYPE.len(),
            namespace: PID_NAMESPACE.as_bytes().to_vec(),
            issuer_mldsa_message_bytes,
            issuer_mso_payload_bytes: 4_096,
            device_mldsa_message_bytes,
            attributes: vec![MdocTree0AttributeKey {
                mode: 0,
                element_identifier: b"age_over_18".to_vec(),
                equality_value: vec![0xf5],
                item_padded_len: 192,
            }],
            age_public: None,
            nat_public: None,
        }
    }

    #[test]
    fn tree0_cache_material_distinguishes_hosted_mldsa_message_lengths() {
        let baseline_material = material(200, 120);
        let baseline = bincode::serialize(&baseline_material).expect("cache material encodes");
        let production = serialize_mdoc_tree0_cache_key_material(
            &baseline_material,
            #[cfg(feature = "unlink-spikes")]
            MdocUnlinkSpikeConfig::default(),
        )
        .expect("production cache material encodes");
        assert_eq!(
            production, baseline,
            "production tree-0 cache key must retain its version-5 byte encoding"
        );
        assert_ne!(
            baseline,
            bincode::serialize(&material(201, 120)).expect("cache material encodes"),
            "issuer ML-DSA message length determines hosted tree-0 preprocessing"
        );
        assert_ne!(
            baseline,
            bincode::serialize(&material(200, 121)).expect("cache material encodes"),
            "device ML-DSA message length determines hosted tree-0 preprocessing"
        );
    }

    #[cfg(feature = "unlink-spikes")]
    #[test]
    fn tree0_cache_material_distinguishes_unlinkability_dummy_job_layout() {
        let baseline = material(200, 120);
        let baseline =
            serialize_mdoc_tree0_cache_key_material(&baseline, MdocUnlinkSpikeConfig::default())
                .expect("cache material encodes");
        let dummy_jobs = serialize_mdoc_tree0_cache_key_material(
            &material(200, 120),
            MdocUnlinkSpikeConfig {
                dummy_keccak_jobs: 13,
            },
        )
        .expect("dummy-job cache material encodes");
        assert_ne!(
            baseline, dummy_jobs,
            "dummy jobs change Keccak service preprocessing"
        );
    }

    #[cfg(feature = "unlink-spikes")]
    #[test]
    fn unlinkability_keccak_spike_accepts_only_workorder_points() {
        for count in UNLINK_SPIKE_DUMMY_JOB_COUNTS {
            assert!(validate_unlink_spike_dummy_jobs(count, "prove").is_ok());
            assert!(validate_unlink_spike_dummy_jobs(count, "verify").is_ok());
        }
        assert!(matches!(
            validate_unlink_spike_dummy_jobs(12, "prove"),
            Err(Error::Prove(_))
        ));
        assert!(matches!(
            validate_unlink_spike_dummy_jobs(34, "verify"),
            Err(Error::Verify(_))
        ));
    }
}

#[cfg(test)]
mod auth_projection_serde_tests {
    use super::*;

    const RHO_BYTES: usize = 32;
    const TR_BYTES: usize = 64;

    #[derive(Serialize, Deserialize)]
    struct ProjectedAuthPair {
        #[serde(
            serialize_with = "serialize_private_issuer_auth",
            deserialize_with = "deserialize_private_issuer_auth"
        )]
        issuer: MdocAuthInput,
        #[serde(
            serialize_with = "serialize_public_device_auth",
            deserialize_with = "deserialize_public_device_auth"
        )]
        device: MdocAuthInput,
    }

    #[derive(Debug, Deserialize)]
    struct ProjectedPrivateIssuer {
        #[serde(deserialize_with = "deserialize_private_issuer_auth")]
        #[serde(rename = "issuer")]
        _issuer: MdocAuthInput,
    }

    fn input(message: Vec<u8>, signature_fill: u8) -> MdocAuthInput {
        MdocAuthInput::MlDsa(Box::new(MlDsaVerifyInput {
            rho: [7; RHO_BYTES],
            t1: [[0; stwo_mldsa::constants::N]; stwo_mldsa::constants::K],
            tr: [signature_fill; TR_BYTES],
            message,
            c_tilde: [signature_fill; stwo_mldsa::constants::C_TILDE_BYTES],
            z: [[i32::from(signature_fill); stwo_mldsa::constants::N]; stwo_mldsa::constants::L],
            hint: [[signature_fill & 1; stwo_mldsa::constants::N]; stwo_mldsa::constants::K],
        }))
    }

    fn equality_attribute() -> MdocStatementAttribute {
        MdocStatementAttribute {
            element_identifier: "family_name".to_string(),
            mode: MdocDisclosureMode::ValueEquality(vec![0xf5]),
            item_padded_len: 64,
        }
    }

    fn shape_statement() -> MdocCircuitStatement {
        MdocCircuitStatement {
            doctype: PID_DOCTYPE.to_string(),
            namespace: PID_NAMESPACE.to_string(),
            issuer_input: input(vec![0; 256], 0),
            device_input: input(vec![0; 64], 0),
            ts13_revocation: None,
            ts13_revocation_range: None,
            ts13_revocation_signature: None,
            attributes: vec![equality_attribute()],
            mso_payload_len: 128,
            policy: Policy {
                current_date: predicates::Date {
                    year: 2026,
                    month: 7,
                    day: 29,
                },
                min_age_years: 18,
                accepted_nationalities: Vec::new(),
            },
        }
    }

    fn set_message_len(input: &mut MdocAuthInput, len: usize) {
        let MdocAuthInput::MlDsa(input) = input else {
            panic!("shape-test helper requires the public-key ML-DSA arm");
        };
        input.message = vec![0; len];
    }

    fn ts13_public_shape_statement() -> MdocTs13PublicStatement {
        let statement = shape_statement();
        MdocTs13PublicStatement {
            doctype: statement.doctype,
            namespace: statement.namespace,
            issuer: MdocMlDsaPublicAuthInput::from_circuit(&statement.issuer_input, false)
                .expect("issuer projection"),
            device: MdocMlDsaPublicAuthInput::from_circuit(&statement.device_input, true)
                .expect("device projection"),
            revocation: MdocRevocationPublicInputs {
                revocation_public_key: MdocRevocationKey::MlDsa(vec![
                    0;
                    stwo_mldsa::constants::PK_BYTES
                ]),
                epoch: 17,
            },
            mso_payload_len: 128,
            requested_item_padded_len: 64,
            attributes: vec![MdocRequestedAttribute {
                element_identifier: "family_name".to_string(),
                mode: MdocDisclosureMode::ValueEquality(vec![0xf5]),
            }],
            policy: statement.policy,
        }
    }

    fn contains_run(haystack: &[u8], needle: &[u8]) -> bool {
        !needle.is_empty()
            && haystack
                .windows(needle.len())
                .any(|window| window == needle)
    }

    #[test]
    fn circuit_shape_caps_return_typed_errors_without_panicking() {
        type Mutation = fn(&mut MdocCircuitStatement);
        let cases: [(&str, Mutation); 11] = [
            ("zero attributes", |statement| statement.attributes.clear()),
            ("five attributes", |statement| {
                statement.attributes = vec![
                    equality_attribute();
                    crate::mdoc_window_bind::MDOC_MAX_DISCLOSED_ATTRIBUTES
                        + 1
                ]
            }),
            ("long identifier", |statement| {
                statement.attributes[0].element_identifier = "x".repeat(33)
            }),
            ("long equality mode", |statement| {
                statement.attributes[0].mode = MdocDisclosureMode::ValueEquality(vec![0; 33])
            }),
            ("unsupported item bucket", |statement| {
                statement.attributes[0].item_padded_len = 65
            }),
            ("zero issuer message", |statement| {
                set_message_len(&mut statement.issuer_input, 0)
            }),
            ("long issuer message", |statement| {
                set_message_len(
                    &mut statement.issuer_input,
                    crate::ts13::TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES + 1,
                )
            }),
            ("zero device message", |statement| {
                set_message_len(&mut statement.device_input, 0)
            }),
            ("long device message", |statement| {
                set_message_len(
                    &mut statement.device_input,
                    crate::ts13::TS13_MAX_DEVICE_MLDSA_MESSAGE_BYTES + 1,
                )
            }),
            ("zero MSO", |statement| statement.mso_payload_len = 0),
            ("long MSO", |statement| {
                statement.mso_payload_len = crate::ts13::TS13_MAX_MSO_PAYLOAD_BYTES + 1
            }),
        ];

        validate_mdoc_circuit_statement_shape(&shape_statement(), "prove", false)
            .expect("control prove shape");
        validate_mdoc_circuit_statement_shape(&shape_statement(), "verify", false)
            .expect("control verify shape");
        for phase in ["prove", "verify"] {
            for (name, mutate) in cases {
                let mut statement = shape_statement();
                mutate(&mut statement);
                let outcome = std::panic::catch_unwind(|| {
                    validate_mdoc_circuit_statement_shape(&statement, phase, false)
                });
                let error = outcome
                    .unwrap_or_else(|_| panic!("{phase} {name} shape panicked"))
                    .unwrap_err();
                assert!(
                    matches!(
                        (phase, error),
                        ("prove", Error::Prove(_)) | ("verify", Error::Verify(_))
                    ),
                    "{phase} {name} did not return a phase-typed error"
                );
            }
        }
    }

    #[test]
    fn ts13_public_reconstruction_checks_resource_caps_before_allocating() {
        type Mutation = fn(&mut MdocTs13PublicStatement);
        let cases: [(&str, Mutation); 8] = [
            ("zero attributes", |statement| statement.attributes.clear()),
            ("five attributes", |statement| {
                statement.attributes = vec![
                    statement.attributes[0].clone();
                    crate::mdoc_window_bind::MDOC_MAX_DISCLOSED_ATTRIBUTES
                        + 1
                ]
            }),
            ("long equality", |statement| {
                statement.attributes[0].mode = MdocDisclosureMode::ValueEquality(vec![0; 33])
            }),
            ("zero issuer message", |statement| {
                statement.issuer.message_len = 0
            }),
            ("long issuer message", |statement| {
                statement.issuer.message_len =
                    (crate::ts13::TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES + 1) as u16
            }),
            ("zero device message", |statement| {
                statement.device.message_len = 0
            }),
            ("long device message", |statement| {
                statement.device.message_len =
                    (crate::ts13::TS13_MAX_DEVICE_MLDSA_MESSAGE_BYTES + 1) as u16
            }),
            ("zero MSO", |statement| statement.mso_payload_len = 0),
        ];

        ts13_public_shape_statement()
            .verifier_circuit_statement()
            .expect("control public statement reconstructs");
        for (name, mutate) in cases {
            let mut statement = ts13_public_shape_statement();
            mutate(&mut statement);
            let outcome = std::panic::catch_unwind(|| statement.verifier_circuit_statement());
            let error = outcome
                .unwrap_or_else(|_| panic!("{name} public reconstruction panicked"))
                .unwrap_err();
            assert!(
                matches!(error, Error::Verify(_)),
                "{name} did not return a verify error"
            );
        }

        let mut statement = ts13_public_shape_statement();
        statement.mso_payload_len = (crate::ts13::TS13_MAX_MSO_PAYLOAD_BYTES + 1) as u16;
        let outcome = std::panic::catch_unwind(|| statement.verifier_circuit_statement());
        assert!(matches!(
            outcome.expect("long MSO public reconstruction must not panic"),
            Err(Error::Verify(_))
        ));
    }

    #[test]
    fn auth_projection_round_trip_scrubs_private_issuer_and_signature_witnesses() {
        let issuer_message = b"private issuer Sig_structure sentinel".to_vec();
        let device_message = b"public DeviceAuthentication sentinel".to_vec();
        let pair = ProjectedAuthPair {
            issuer: input(issuer_message.clone(), 0xa5),
            device: input(device_message.clone(), 0x5a),
        };

        let encoded = bincode::serialize(&pair).expect("auth projection serializes");
        assert!(!contains_run(&encoded, &issuer_message));
        assert!(contains_run(&encoded, &device_message));
        assert!(
            !contains_run(&encoded, &[0xa5; stwo_mldsa::constants::C_TILDE_BYTES]),
            "issuer signature witness leaked through its public projection"
        );
        assert!(
            !contains_run(&encoded, &[0x5a; stwo_mldsa::constants::C_TILDE_BYTES]),
            "device signature witness leaked through its public projection"
        );

        let restored: ProjectedAuthPair =
            bincode::deserialize(&encoded).expect("auth projection deserializes");
        let restored_issuer = restored.issuer.as_mldsa().expect("issuer ML-DSA");
        let restored_device = restored.device.as_mldsa().expect("device ML-DSA");
        assert_eq!(restored_issuer.message, vec![0; issuer_message.len()]);
        assert_eq!(restored_device.message, device_message);
        assert_eq!(
            restored_issuer.c_tilde,
            [0; stwo_mldsa::constants::C_TILDE_BYTES]
        );
        assert_eq!(
            restored_device.c_tilde,
            [0; stwo_mldsa::constants::C_TILDE_BYTES]
        );
    }

    #[test]
    fn private_issuer_projection_rejects_serialized_message_bytes() {
        #[derive(Serialize)]
        struct MalformedPrivateIssuer {
            issuer: MdocMlDsaPublicAuthInput,
        }

        let malformed = MalformedPrivateIssuer {
            issuer: MdocMlDsaPublicAuthInput {
                public_key: input(Vec::new(), 0).as_mldsa().expect("ML-DSA").encode_pk(),
                message_len: 1,
                message: vec![42],
            },
        };
        let encoded = bincode::serialize(&malformed).expect("malformed projection serializes");
        let error = bincode::deserialize::<ProjectedPrivateIssuer>(&encoded)
            .expect_err("private issuer bytes must reject");
        assert!(
            error.to_string().contains("private message bytes"),
            "unexpected malformed private issuer error: {error}"
        );
    }

    #[test]
    fn issuer_signed_item_parser_errors_preserve_token_and_absolute_offset() {
        let outer = map_private_item_prove_error(
            0,
            MdocPrivateItemError::OuterParser(
                crate::mdoc_cbor_stream::MdocCborStreamError::NonMinimalArgument {
                    index: 7,
                    argument: 23,
                },
            ),
        );
        assert!(matches!(
            outer,
            Error::Mdoc(MdocError::IssuerSignedItemNotCanonical {
                offset: 7,
                reason: MdocIssuerSignedItemCanonicalityReason::NonMinimalArgument { argument: 23 }
            })
        ));

        let inner = map_private_item_prove_error(
            0,
            MdocPrivateItemError::InnerParser(
                crate::mdoc_cbor_stream::MdocCborStreamError::InvalidAdditionalInfo {
                    index: 3,
                    additional: 31,
                },
            ),
        );
        assert!(matches!(
            inner,
            Error::Mdoc(MdocError::IssuerSignedItemNotCanonical {
                offset: 7,
                reason: MdocIssuerSignedItemCanonicalityReason::InvalidAdditionalInfo {
                    additional: 31
                }
            })
        ));
    }

    #[test]
    fn tag24_wrapper_errors_map_to_public_token_and_offset_reasons() {
        let cases = [
            (
                0,
                MdocPrivateTag24WrapperReason::ExpectedTag24,
                MdocIssuerSignedItemCanonicalityReason::ExpectedTag24,
            ),
            (
                2,
                MdocPrivateTag24WrapperReason::ExpectedByteString,
                MdocIssuerSignedItemCanonicalityReason::ExpectedTag24ByteString,
            ),
            (
                2,
                MdocPrivateTag24WrapperReason::ExpectedU8ByteStringLength { additional: 25 },
                MdocIssuerSignedItemCanonicalityReason::ExpectedTag24ByteStringU8Length {
                    additional: 25,
                },
            ),
            (
                3,
                MdocPrivateTag24WrapperReason::TruncatedToken { needed: 1 },
                MdocIssuerSignedItemCanonicalityReason::TruncatedToken { needed: 1 },
            ),
            (
                3,
                MdocPrivateTag24WrapperReason::ByteStringLengthMismatch {
                    declared: 12,
                    actual: 11,
                },
                MdocIssuerSignedItemCanonicalityReason::Tag24ByteStringLengthMismatch {
                    declared: 12,
                    actual: 11,
                },
            ),
        ];

        for (expected_offset, private_reason, expected_reason) in cases {
            let mapped = map_private_item_prove_error(
                0,
                MdocPrivateItemError::InvalidTag24Wrapper {
                    offset: expected_offset,
                    reason: private_reason,
                },
            );
            let Error::Mdoc(MdocError::IssuerSignedItemNotCanonical { offset, reason }) = mapped
            else {
                panic!("wrapper error did not map to the public typed error");
            };
            assert_eq!(offset, expected_offset);
            assert_eq!(reason, expected_reason);
        }
    }

    #[test]
    fn value_digests_canonicality_maps_to_public_offset_and_reason() {
        let mapped =
            map_value_digests_prove_error(MdocValueDigestsScanError::MsoValueDigestsNotCanonical {
                offset: 73,
                reason: MdocMsoValueDigestsCanonicalityReason::Truncated("digest bytes"),
            });
        assert!(matches!(
            mapped,
            Error::Mdoc(MdocError::MsoValueDigestsNotCanonical {
                offset: 73,
                reason: MdocMsoValueDigestsCanonicalityReason::Truncated("digest bytes"),
            })
        ));
    }

    #[test]
    fn full_statement_round_trip_scrubs_all_signature_and_revocation_witnesses() {
        const PRIVATE_SIGNATURE_SENTINEL: u8 = 0xee;
        const PRIVATE_RANGE_ID_SENTINEL: u8 = 0xd1;
        const PRIVATE_RANGE_LO_SENTINEL: u8 = 0xd2;
        const PRIVATE_RANGE_HI_SENTINEL: u8 = 0xd3;
        let issuer_message = b"private full-statement issuer sentinel".to_vec();
        let device_message = b"public full-statement device message".to_vec();
        let statement = MdocCircuitStatement {
            doctype: PID_DOCTYPE.to_string(),
            namespace: PID_NAMESPACE.to_string(),
            issuer_input: input(issuer_message.clone(), 0xa5),
            device_input: input(device_message.clone(), 0x5a),
            ts13_revocation: Some(MdocRevocationPublicInputs {
                revocation_public_key: MdocRevocationKey::MlDsa(vec![
                    0x11;
                    stwo_mldsa::constants::PK_BYTES
                ]),
                epoch: 17,
            }),
            ts13_revocation_range: Some(MdocRevocationRangeWitness {
                id: u64::from_le_bytes([PRIVATE_RANGE_ID_SENTINEL; 8]),
                id_lo: u64::from_le_bytes([PRIVATE_RANGE_LO_SENTINEL; 8]),
                id_hi: u64::from_le_bytes([PRIVATE_RANGE_HI_SENTINEL; 8]),
            }),
            ts13_revocation_signature: Some(MdocRevocationSignature::MlDsa(vec![
                PRIVATE_SIGNATURE_SENTINEL;
                96
            ])),
            attributes: Vec::new(),
            mso_payload_len: 128,
            policy: Policy {
                current_date: predicates::Date {
                    year: 2026,
                    month: 7,
                    day: 29,
                },
                min_age_years: 18,
                accepted_nationalities: vec![276],
            },
        };

        let encoded = bincode::serialize(&statement).expect("full statement serializes");
        assert!(!contains_run(&encoded, &issuer_message));
        assert!(contains_run(&encoded, &device_message));
        assert!(
            !contains_run(&encoded, &[PRIVATE_SIGNATURE_SENTINEL; 96]),
            "revocation signature witness leaked through the full statement"
        );
        for sentinel in [
            PRIVATE_RANGE_ID_SENTINEL,
            PRIVATE_RANGE_LO_SENTINEL,
            PRIVATE_RANGE_HI_SENTINEL,
        ] {
            assert!(
                !contains_run(&encoded, &[sentinel; 8]),
                "revocation range witness leaked through the full statement"
            );
        }

        let restored: MdocCircuitStatement =
            bincode::deserialize(&encoded).expect("full statement deserializes");
        assert!(restored.ts13_revocation_range.is_none());
        assert!(restored.ts13_revocation_signature.is_none());
        assert_eq!(
            restored
                .issuer_input
                .as_mldsa()
                .expect("issuer ML-DSA")
                .message,
            vec![0; issuer_message.len()]
        );
        assert_eq!(
            restored
                .device_input
                .as_mldsa()
                .expect("device ML-DSA")
                .message,
            device_message
        );
    }

    #[test]
    fn public_view_contains_only_the_phase1_statement_shape() {
        let mut statement = shape_statement();
        statement.attributes[0] = MdocStatementAttribute {
            element_identifier: "age_over_18".to_string(),
            mode: MdocDisclosureMode::ValueEquality(vec![0xf5]),
            item_padded_len: 192,
        };
        statement.mso_payload_len = 3_137;
        statement.ts13_revocation = Some(MdocRevocationPublicInputs {
            revocation_public_key: MdocRevocationKey::MlDsa(vec![
                0x11;
                stwo_mldsa::constants::PK_BYTES
            ]),
            epoch: 17,
        });
        statement.ts13_revocation_range = Some(MdocRevocationRangeWitness {
            id: 29,
            id_lo: 23,
            id_hi: 31,
        });
        statement.ts13_revocation_signature = Some(MdocRevocationSignature::MlDsa(vec![0xee; 96]));

        let public =
            MdocTs13PublicStatement::from_circuit(&statement).expect("TS13 projection succeeds");
        assert_eq!(public.requested_item_padded_len, 192);
        assert_eq!(public.mso_payload_len, 3_137);
        assert_eq!(public.attributes.len(), 1);

        let projected = statement.into_public_view();
        assert!(projected.ts13_revocation.is_some());
        assert!(projected.ts13_revocation_range.is_none());
        assert!(projected.ts13_revocation_signature.is_none());
        assert_eq!(projected.attributes[0].item_padded_len, 192);
        assert_eq!(projected.mso_payload_len, 3_137);

        let mut encoded = Vec::new();
        ciborium::ser::into_writer(&public, &mut encoded).expect("public statement serializes");
        let value: Value =
            ciborium::de::from_reader(encoded.as_slice()).expect("public statement is CBOR");
        let Value::Map(entries) = value else {
            panic!("public statement must serialize as a map");
        };
        let keys: Vec<_> = entries
            .iter()
            .filter_map(|(key, _)| match key {
                Value::Text(key) => Some(key.as_str()),
                _ => None,
            })
            .collect();
        for private_key in [
            "requested_digest_id",
            "valid_today",
            "mso_payload_offset",
            "birth_date_value_offset",
            "nationality_value_offset",
        ] {
            assert!(
                !keys.contains(&private_key),
                "private/credential-stable key {private_key} leaked"
            );
        }
    }

    #[test]
    fn ts13_public_verifier_statement_does_not_synthesize_revocation_signature() {
        let issuer_input = input(b"private issuer message".to_vec(), 0xa5);
        let device_input = input(b"public device message".to_vec(), 0x5a);
        let public = MdocTs13PublicStatement {
            doctype: PID_DOCTYPE.to_string(),
            namespace: PID_NAMESPACE.to_string(),
            issuer: MdocMlDsaPublicAuthInput::from_circuit(&issuer_input, false)
                .expect("issuer public projection"),
            device: MdocMlDsaPublicAuthInput::from_circuit(&device_input, true)
                .expect("device public projection"),
            revocation: MdocRevocationPublicInputs {
                revocation_public_key: MdocRevocationKey::MlDsa(vec![
                    0;
                    stwo_mldsa::constants::PK_BYTES
                ]),
                epoch: 17,
            },
            mso_payload_len: 128,
            requested_item_padded_len: 64,
            attributes: vec![MdocRequestedAttribute {
                element_identifier: "family_name".to_string(),
                mode: MdocDisclosureMode::ValueEquality(vec![0x61, b'A']),
            }],
            policy: Policy {
                current_date: predicates::Date {
                    year: 2026,
                    month: 7,
                    day: 29,
                },
                min_age_years: 18,
                accepted_nationalities: Vec::new(),
            },
        };

        let verifier = public
            .verifier_circuit_statement()
            .expect("public TS13 statement reconstructs");
        assert!(verifier.ts13_revocation_signature.is_none());
        assert!(verifier.ts13_revocation_range.is_none());
        validate_public_auth_projection(&verifier).expect("reconstructed statement is public-only");
    }

    #[test]
    fn revocation_range_uses_the_fixed_private_digest_geometry() {
        let zero = QM31::from(M31::from_u32_unchecked(0));
        let module = MdocRevocationRangeBind::verifier(
            SharedDigestRelation::new(),
            17,
            SharedFieldRelation::new(),
            MdocRevocationRangeInteractionClaim {
                claimed_sum: zero,
                blinder_v: zero,
                blinder_m: zero,
                blinder_claimed_sum: zero,
            },
        );
        let layout = module.layout();

        assert_eq!(revocation_range_trace_cols(), 336);
        assert_eq!(layout.preprocessed, vec![MDOC_REVOCATION_RANGE_LOG_SIZE]);
        assert_eq!(
            layout.trace,
            vec![MDOC_REVOCATION_RANGE_LOG_SIZE; revocation_range_trace_cols()]
        );
        assert_eq!(
            layout.interaction,
            vec![MDOC_REVOCATION_RANGE_LOG_SIZE; 12 * SECURE_EXTENSION_DEGREE]
        );
    }
}
