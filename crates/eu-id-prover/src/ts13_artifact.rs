//! Deterministic circuit identity generator for the canonical TS13 demo.
//!
//! `src/bin/ts13_demo_artifact.rs` compiles this module.
//! The JSON input has no defaults. The composed prover supplies the geometry.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Write as _};
use std::fs;
use std::io;
use std::path::{Component, Path, PathBuf};
use std::process::Command;

use ciborium::value::Value;
use serde::de::{self, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use sha2::{Digest as _, Sha256};

pub const ARTIFACT_PATH: &str = "artifacts/ts13-demo-v1/circuit-artifact-v1.cbor";
pub const SHAPE_MANIFEST_PATH: &str = "artifacts/ts13-demo-v1/shape-manifest.cbor";
pub const HASH_EMBED_PATH: &str = "crates/eu-id-prover/src/generated/ts13_demo_artifact.rs";
pub const GENERATION_INPUT_PATH: &str = "artifacts/ts13-demo-v1/generation-input-v1.json";
pub const NORMATIVE_SPEC_PATH: &str = "docs/ts13-unlinkable-age18-demo-spec.md";

/// Prove and return live circuit geometry for artifact maintenance.
///
/// This Rust-only diagnostic is not part of the UniFFI API.
#[doc(hidden)]
pub fn prove_live_ts13_demo(
    document: &[u8],
    request: &crate::MdocPidRequest,
    public: &crate::MdocTs13DemoCircuitPublicInput,
    id_lo: u64,
    id_hi: u64,
    signature: crate::mdoc::MdocRevocationSignature,
) -> Result<(crate::MdocProof, crate::mdoc::MdocTs13DemoCircuitGeometry), crate::Error> {
    crate::prove_mdoc_ts13_demo_for_artifact(document, request, public, id_lo, id_hi, signature)
}

/// Generated files that the soundness source-tree digest omits.
///
/// The scanner also omits Cargo `target` directories. It does not use
/// `.gitignore`, wildcards, suffixes, or caller exclusions.
pub const GENERATED_RECURSION_EXCLUSIONS: [&str; 3] =
    [SHAPE_MANIFEST_PATH, ARTIFACT_PATH, HASH_EMBED_PATH];

pub const SOURCE_PACKAGE_ROOTS: [&str; 6] = [
    "crates/air-core",
    "crates/stwo-sha256",
    "crates/stwo-keccak",
    "crates/stwo-mldsa",
    "crates/eu-id-prover",
    "crates/sdk",
];

const SHARED_KECCAK_SERVICE_MODULE: &str = "shared_keccak_service";

pub const CANONICAL_MODULE_ORDER: [&str; 19] = [
    "shared_sha256_tables",
    "shared_mldsa_range_tables",
    SHARED_KECCAK_SERVICE_MODULE,
    "ts13_public_context_bind",
    "private_issuer_message_provider",
    "issuer_private_message_mldsa",
    "requested_item_sha256",
    "private_mso_sha256",
    "private_item_cbor_parsers",
    "private_item_binder",
    "private_mso_binder",
    "mdoc_private_mso_validity",
    "private_value_digests_scanner",
    "private_expand_a",
    "private_device_key_binder",
    "private_device_mldsa",
    "private_revocation_range",
    "private_revocation_mldsa",
    "public_revocation_key_epoch_bind",
];

const CANONICAL_MERKLE_TREE_ORDER: [&str; 5] = [
    "tree_0_preprocessed",
    "tree_1_trace",
    "tree_2_interaction",
    "tree_3_post_interaction",
    "tree_4_composition",
];

const PROFILE_ID: &str = "ts13-pid-age-over-18-unlinkable-demo-v1";
const PROOF_SYSTEM_ID: &str = "stwo-euid-ts13-demo-v1";
const CONSTRAINT_SYSTEM_VERSION: &str = "ts13-unlinkable-air-v1";
const ARTIFACT_SCHEMA_VERSION: u64 = 3;
const SHAPE_SCHEMA_VERSION: u64 = 3;
const ENVELOPE_VERSION: u64 = 4;
const ENVELOPE_HEADER_BYTES: u64 = 46;
const ENVELOPE_CAPACITY_ALIGNMENT: u64 = 65_536;
const CANONICAL_DIGEST_IDENTIFIER_INTEGER_WIDTHS: [u8; 3] = [1, 2, 3];
const CANONICAL_REQUEST_CONTEXT_CORPUS_SHA256: &str =
    "2ba3208731e3eb7b67ef54e0683f28dcb81d1b3811c0d2a1ce1d187ee9c3d77c";
const CANONICAL_GENERATION_INPUT_SHA256: &str =
    "9e789af403f9c570d81a8e004e4c78bb4012dd87d16f5d99620c11c059074454";
const CANONICAL_EUDI_ARF_COMMIT: &str = "230cd75d9c243e6b4c7b35f3f2bf73f9dff20cdc";
const CANONICAL_OBSERVED_MAX_DEVICE_COSE_SIG_STRUCTURE_BYTES: u32 = 456;
const CANONICAL_RELATION_COUNT: usize = 69;
const CANONICAL_RELATION_USE_COUNT: usize = 240;
const CANONICAL_KECCAK_POST_INTERACTION_COLUMN_COUNT: u32 = 24;
const RESERVED_TRANSCRIPT_RELATION_NAMES: [&str; 1] = ["r07_keccak_round"];
const CANONICAL_PUBLIC_MIX_COUNT: usize = 20;
const CANONICAL_CHALLENGE_ENTRY_COUNT: usize = 78;
const CANONICAL_RAW_MLDSA_CHALLENGE_COUNT: usize = 9;
const CANONICAL_EXPAND_A_JOB_COUNT: usize = stwo_mldsa::profile::ML_DSA_65.matrix_polys();
const CANONICAL_HASH_STREAM_COUNT: usize = CANONICAL_EXPAND_A_JOB_COUNT + 10;
const CANONICAL_STREAM_ID_COUNT: usize = CANONICAL_HASH_STREAM_COUNT * 2 + 3;
const CANONICAL_RANGE_TABLE_COUNT: usize = 26;
const CANONICAL_DEVICE_KEY_BIND_ACTIVE_ROWS: usize =
    crate::mdoc_private_device_key_bind::MDOC_PRIVATE_DEVICE_KEY_ACTIVE_ROWS;
const CANONICAL_DEVICE_PUBLIC_KEY_BYTES: usize = stwo_mldsa::profile::ML_DSA_65.pk_bytes();
const CANONICAL_SERIALIZED_CLAIM_NAMES: [&str; 19] = crate::mdoc::MDOC_PROOF_SERIALIZED_CLAIM_NAMES;
const OUTER_CBOR_PUBLIC_MIX_ENCODING: &str = "mix_u64(domain,mode=outer,stream_id,log_size)";
const INNER_CBOR_PUBLIC_MIX_ENCODING: &str = "mix_u64(domain,mode=inner,stream_id,log_size)";
const MSO_BIND_PUBLIC_MIX_ENCODING: &str = "mix_u64(domain,version,issuer_message_len,mso_len,\
payload_anchor_len,row_count,preprocessed_cols,trace_cols,interaction_cols,doc_type_len,\
each_doc_type_byte,private_device_key_mode,public_key_len,sha_field_id,sha_padded_len)";
const ITEM_BIND_PUBLIC_MIX_ENCODING: &str = "mix_u64(domain,version,transcript_tag,\
attribute_index=0,padded_item_bytes=128,log_size,outer_parser_log_size,inner_parser_log_size,\
max_random_bytes,element_identifier_len,element_value_len,digest_id_max,outer_stream_field_id,\
inner_stream_field_id,element_identifier_field_id,element_value_field_id,main_relation_sites)";
const MSO_VALIDITY_PUBLIC_MIX_ENCODING: &str = "mix_u64(domain,version,\
verification_timestamp_epoch_seconds); mix_u64(each verification_timestamp_rfc3339_utc byte in \
order); mix_u64(preprocessed_cols,trace_cols,interaction_cols)";
const VALUE_DIGESTS_PUBLIC_MIX_ENCODING: &str = "mix_u64(domain,version,transcript_tag,\
issuer_message_len,mso_len,selected_attribute_count=1,namespace_len,each_namespace_byte,log_size,\
max_scan_items,max_namespace_bytes,preprocessed_cols,trace_cols,relation_sites,interaction_cols,\
digest_id_max)";
const KECCAK_PUBLIC_MIX_ENCODING: &str = "mix_u64(job_count,service_log_size); for each of 40 jobs mix mode,rate,message_len,n_squeeze,absorb_stream,squeeze_stream,perm_id_base; device-mu additionally mixes CAPACITY_TAG,1090";
const KECCAK_PUBLIC_MIX_FIXED_LENGTH: u32 = 2_272;
const CLAIM_MIX_ORDER: &str = "After tree 1, mix claims in physical AIR order. ML-DSA roles mix group_evals before claimed_sums.";
const TRANSCRIPT_PHASE_ORDER: &str = "Mix the PCS configuration and commit tree0. Mix 20 AIR public statements and commit tree1. Draw the secure fields in challengeOrder. Mix claims in physical AIR order and commit tree2. Run the shared_keccak_service GKR post-interaction and commit tree3. Then calculate the composition polynomial and FRI.";
const KECCAK_JOB_ORDER: &str = "issuer_mu,issuer_ct,issuer_sib,expand_a_00..expand_a_29,device_tr,device_mu,device_ct,device_sib,revocation_mu,revocation_ct,revocation_sib";
const HASH_STREAM_ID_SEMANTICS: &str = "HashStreamV1.streamId is the absorb stream ID. `streamIds` also contains the separate squeeze stream IDs.";
const CANONICAL_BUILTIN_CONSTANT_NAMES: [&str; 40] = [
    "cbor.device_key_info_prefix",
    "context.domain",
    "context.public_mix_domain",
    "device_key_binding.active_rows",
    "device_key_binding.public_key_bytes",
    "device_key_binding.rho_rows",
    "envelope.magic",
    "expand_a.accepted_coefficients_per_polynomial",
    "expand_a.candidate_bits",
    "expand_a.jobs",
    "expand_a.modulus_q",
    "expand_a.squeeze_blocks_per_job",
    "privacy.claim",
    "private_key_evaluation.a_evaluation_count",
    "private_key_evaluation.coefficient_evaluation_count",
    "private_key_evaluation.inverse_ntt_normalizer",
    "private_key_evaluation.radix",
    "private_key_evaluation.scaled_t1_factor",
    "private_key_evaluation.t1_evaluation_count",
    "private_key_evaluation.t1_hi_bits",
    "private_key_evaluation.t1_lo_bits",
    "profile.device_authentication",
    "profile.device_authentication_profile",
    "profile.disclosed_attributes",
    "profile.document_type",
    "profile.element",
    "profile.expected_cbor_hex",
    "profile.format",
    "profile.hash",
    "profile.issuer_authentication",
    "profile.namespace",
    "profile.revocation_authentication",
    "profile.revocation_mandatory",
    "profile.timestamp_precision",
    "profile.trusted_issuer_count",
    "spec.eudi_arf_commit",
    "spec.eudi_arf_ts13_path",
    "spec.normative_document_sha256",
    "validity.maximum_year",
    "validity.minimum_year",
];
const CANONICAL_IMPLEMENTATION_CONSTANT_NAMES: [&str; 38] = [
    "impl.air_instance_count",
    "impl.cargo_feature_scope",
    "impl.challenge.raw_mldsa_secure_field_draws",
    "impl.challenge.relation_instances",
    "impl.challenge.relation_secure_field_draws",
    "impl.challenge.total_secure_field_draws",
    "impl.component_count",
    "impl.device_sig_structure_capacity_bytes",
    "impl.digest_identifier_integer_widths",
    "impl.eval_at_rs_public_cancellation",
    "impl.expand_a_job_count",
    "impl.hash_job_count",
    "impl.hash_stream_record_stream_id_semantics",
    "impl.issuer_cose_sig_structure_bytes",
    "impl.keccak.job_order",
    "impl.keccak_service_claimed_sum_count",
    "impl.logical_module_count",
    "impl.mldsa.device_claimed_sum_count",
    "impl.mldsa.device_group_eval_count",
    "impl.mldsa.issuer_claimed_sum_count",
    "impl.mldsa.issuer_group_eval_count",
    "impl.mldsa.revocation_claimed_sum_count",
    "impl.mldsa.revocation_group_eval_count",
    "impl.mso_payload_bytes",
    "impl.outer_claim_bytes_excluding_stark_and_post_payloads",
    "impl.padded_issuer_signed_item_bytes",
    "impl.post_interaction_nonempty_payload_bytes",
    "impl.post_interaction_payload_vector_wire_bytes",
    "impl.relation_tuple_counts_semantics",
    "impl.serialized_claim_bytes_excluding_stark",
    "impl.stream_base.device_mldsa",
    "impl.stream_base.expand_a",
    "impl.stream_base.issuer_mldsa",
    "impl.stream_base.revocation_mldsa",
    "impl.transcript.claim_mix_order",
    "impl.transcript.global_claimed_sum_count",
    "impl.transcript.phase_order",
    "impl.tuple_scalar_semantics",
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GenerationMode {
    Write,
    Check,
}

#[derive(Debug)]
pub enum ArtifactError {
    Io {
        action: &'static str,
        path: PathBuf,
        source: io::Error,
    },
    Json {
        path: PathBuf,
        source: serde_json::Error,
    },
    InvalidInput(String),
    Cbor(String),
    Command {
        program: &'static str,
        detail: String,
    },
    Drift(Vec<PathBuf>),
}

impl fmt::Display for ArtifactError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io {
                action,
                path,
                source,
            } => write!(formatter, "cannot {action} {}: {source}", path.display()),
            Self::Json { path, source } => {
                write!(
                    formatter,
                    "invalid generation input {}: {source}",
                    path.display()
                )
            }
            Self::InvalidInput(detail) => write!(formatter, "invalid generation input: {detail}"),
            Self::Cbor(detail) => write!(formatter, "canonical CBOR encoding failed: {detail}"),
            Self::Command { program, detail } => {
                write!(formatter, "{program} metadata command failed: {detail}")
            }
            Self::Drift(paths) => {
                write!(formatter, "generated artifact drift:")?;
                for path in paths {
                    write!(formatter, " {}", path.display())?;
                }
                Ok(())
            }
        }
    }
}

impl std::error::Error for ArtifactError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io { source, .. } => Some(source),
            Self::Json { source, .. } => Some(source),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Digest32([u8; 32]);

impl Digest32 {
    fn of(bytes: &[u8]) -> Self {
        Self(Sha256::digest(bytes).into())
    }
}

impl fmt::Display for Digest32 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in self.0 {
            write!(formatter, "{byte:02x}")?;
        }
        Ok(())
    }
}

impl Serialize for Digest32 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        if serializer.is_human_readable() {
            serializer.serialize_str(&self.to_string())
        } else {
            serializer.serialize_bytes(&self.0)
        }
    }
}

impl<'de> Deserialize<'de> for Digest32 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        if deserializer.is_human_readable() {
            let encoded = String::deserialize(deserializer)?;
            let bytes = decode_hex(&encoded).map_err(de::Error::custom)?;
            let bytes: [u8; 32] = bytes
                .try_into()
                .map_err(|_| de::Error::custom("SHA-256 digest must contain 32 bytes"))?;
            Ok(Self(bytes))
        } else {
            deserializer.deserialize_bytes(Digest32Visitor)
        }
    }
}

struct Digest32Visitor;

impl<'de> Visitor<'de> for Digest32Visitor {
    type Value = Digest32;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a 32-byte SHA-256 digest")
    }

    fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        let value = value
            .try_into()
            .map_err(|_| E::custom("SHA-256 digest must contain 32 bytes"))?;
        Ok(Digest32(value))
    }

    fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let mut value = [0_u8; 32];
        for byte in &mut value {
            *byte = sequence
                .next_element()?
                .ok_or_else(|| de::Error::custom("SHA-256 digest is too short"))?;
        }
        if sequence.next_element::<u8>()?.is_some() {
            return Err(de::Error::custom("SHA-256 digest is too long"));
        }
        Ok(Digest32(value))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct HexBytes(Vec<u8>);

impl Serialize for HexBytes {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        if serializer.is_human_readable() {
            let mut encoded = String::with_capacity(self.0.len() * 2);
            for byte in &self.0 {
                write!(encoded, "{byte:02x}").map_err(serde::ser::Error::custom)?;
            }
            serializer.serialize_str(&encoded)
        } else {
            serializer.serialize_bytes(&self.0)
        }
    }
}

impl<'de> Deserialize<'de> for HexBytes {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        if deserializer.is_human_readable() {
            String::deserialize(deserializer)
                .and_then(|value| decode_hex(&value).map(Self).map_err(de::Error::custom))
        } else {
            Vec::<u8>::deserialize(deserializer).map(Self)
        }
    }
}

fn decode_hex(encoded: &str) -> Result<Vec<u8>, &'static str> {
    if !encoded.len().is_multiple_of(2) {
        return Err("hex value must have an even number of digits");
    }
    encoded
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            let high = hex_nibble(pair[0])?;
            let low = hex_nibble(pair[1])?;
            Ok((high << 4) | low)
        })
        .collect()
}

fn hex_nibble(value: u8) -> Result<u8, &'static str> {
    match value {
        b'0'..=b'9' => Ok(value - b'0'),
        b'a'..=b'f' => Ok(value - b'a' + 10),
        b'A'..=b'F' => Ok(value - b'A' + 10),
        _ => Err("hex value contains a non-hexadecimal character"),
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct GenerationInputV1 {
    credential_shape: CredentialShapeV1,
    request_context_corpus: RequestContextCorpusV1,
    modules: Vec<ModuleLayoutV1>,
    relations: Vec<RelationLayoutV1>,
    transcript: TranscriptLayoutV1,
    serialized_claims: Vec<SerializedClaimV1>,
    stream_ids: Vec<NamedU64V1>,
    hash_streams: Vec<HashStreamV1>,
    range_tables: Vec<RangeTableV1>,
    relation_tuple_counts: Vec<NamedU64V1>,
    implementation_constants: Vec<ArtifactConstantV1>,
    tree_zero: TreeZeroV1,
    proof_system: ProofSystemV1,
    enabled_cargo_features: Vec<PackageFeaturesV1>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct CredentialShapeV1 {
    issuer_cose_sig_structure_bytes: u32,
    mso_payload_bytes: u32,
    padded_issuer_signed_item_bytes: u32,
    digest_identifier_integer_widths: Vec<u8>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RequestContextCorpusV1 {
    corpus_sha256: Digest32,
    observed_max_device_cose_sig_structure_bytes: u32,
    device_sig_structure_capacity: u32,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ModuleLayoutV1 {
    name: String,
    air_instances: Vec<AirInstanceLayoutV1>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct AirInstanceLayoutV1 {
    columns: AirColumnLayoutV1,
    claimed_sum_count: u32,
    max_log_size: u32,
    max_constraint_log_degree_bound: u32,
    components: Vec<AirComponentLayoutV1>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct AirComponentLayoutV1 {
    name: String,
    trace_rows: u32,
    constraint_count: u32,
    max_constraint_log_degree_bound: u32,
    trace_mask_column_counts: Vec<u32>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct AirColumnLayoutV1 {
    preprocessed_m31_log_sizes: Vec<u32>,
    trace_m31_log_sizes: Vec<u32>,
    interaction_m31_log_sizes: Vec<u32>,
    post_interaction_m31_log_sizes: Vec<u32>,
}

impl AirColumnLayoutV1 {
    fn all(&self) -> impl Iterator<Item = (&'static str, &u32)> {
        self.preprocessed_m31_log_sizes
            .iter()
            .map(|log_size| ("preprocessed", log_size))
            .chain(
                self.trace_m31_log_sizes
                    .iter()
                    .map(|log_size| ("trace", log_size)),
            )
            .chain(
                self.interaction_m31_log_sizes
                    .iter()
                    .map(|log_size| ("interaction", log_size)),
            )
            .chain(
                self.post_interaction_m31_log_sizes
                    .iter()
                    .map(|log_size| ("post_interaction", log_size)),
            )
    }

    fn counts(&self) -> Result<ColumnCountsV1, ArtifactError> {
        Ok(ColumnCountsV1 {
            preprocessed: checked_column_count(&self.preprocessed_m31_log_sizes)?,
            trace: checked_column_count(&self.trace_m31_log_sizes)?,
            interaction: checked_column_count(&self.interaction_m31_log_sizes)?,
            post_interaction: checked_column_count(&self.post_interaction_m31_log_sizes)?,
        })
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
enum ColumnScalarV1 {
    Bit,
    U8,
    U16,
    U32,
    M31,
    Qm31,
    SecureField,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RelationLayoutV1 {
    name: String,
    challenge_owner_module: String,
    tuple: Vec<RelationFieldV1>,
    uses: Vec<RelationUseV1>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RelationFieldV1 {
    name: String,
    scalar: ColumnScalarV1,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RelationUseV1 {
    module: String,
    component: String,
    sign: RelationSignV1,
    multiplicity: String,
}

#[derive(Clone, Copy, Debug, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
enum RelationSignV1 {
    Positive,
    Negative,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct TranscriptLayoutV1 {
    public_mix_order: Vec<TranscriptEntryV1>,
    challenge_order: Vec<TranscriptEntryV1>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct TranscriptEntryV1 {
    owner_module: String,
    name: String,
    encoding: String,
    fixed_length: Option<u32>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SerializedClaimV1 {
    name: String,
    encoding: String,
    fixed_length: u32,
    fixed_vector_lengths: Vec<NamedU64V1>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct NamedU64V1 {
    name: String,
    value: u64,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct HashStreamV1 {
    name: String,
    stream_id: u64,
    hash_function: String,
    domain_separator: HexBytes,
    job_count: u32,
    input_capacity_bytes: u32,
    output_bytes: u32,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RangeTableV1 {
    name: String,
    value_kind: String,
    bit_width: u8,
    log_size: u32,
    active_rows: u32,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ArtifactConstantV1 {
    name: String,
    value: ConstantValueV1,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "kind", content = "value", rename_all = "snake_case")]
enum ConstantValueV1 {
    Unsigned(u64),
    Signed(i64),
    Text(String),
    Bytes(HexBytes),
    UnsignedVector(Vec<u64>),
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct TreeZeroV1 {
    derivation: String,
    hash: String,
    preprocessed_column_order: Vec<String>,
    committed_column_log_sizes: Vec<u32>,
    root: Digest32,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ProofSystemV1 {
    field: String,
    field_modulus: u64,
    secure_extension_field: String,
    secure_extension_degree: u32,
    pcs: String,
    commitment_hash: String,
    merkle_hash: String,
    fri_log_last_layer_degree_bound: u32,
    fri_log_blowup_factor: u32,
    fri_query_count: u32,
    fri_fold_step: u32,
    pow_bits: u32,
    lifting_log_size: Option<u32>,
    merkle_trees: Vec<MerkleTreeParametersV1>,
    fri_layers: Vec<FriLayerParametersV1>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct MerkleTreeParametersV1 {
    name: String,
    depth: u32,
    digest_bytes: u32,
    maximum_opened_columns: u32,
    sampled_value_length_histogram: Vec<ValueCountV1>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ValueCountV1 {
    value: u32,
    count: u32,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct FriLayerParametersV1 {
    input_log_size: u32,
    output_log_size: u32,
    merkle_depth: u32,
    maximum_opened_values: u32,
}

#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "snake_case")]
enum ProofBoundSectionV1 {
    ProofHeader,
    Commitments,
    Queries,
    MerkleDecommitments,
    FriLayers,
    Claims,
    ColumnValues,
    PostInteractionPayloads,
    Pow,
    SerializationOverhead,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ProofBoundTermV1 {
    section: ProofBoundSectionV1,
    name: String,
    maximum_item_count: u64,
    maximum_serialized_bytes_per_item: u64,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct PackageFeaturesV1 {
    package: String,
    features: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct ShapeManifestV1 {
    schema_version: u64,
    profile: &'static str,
    credential_shape: CredentialShapeV1,
    request_context_corpus: RequestContextCorpusV1,
    modules: Vec<ShapeModuleV1>,
    air_instances: Vec<ShapeAirInstanceV1>,
    components: Vec<ShapeComponentV1>,
    stream_ids: Vec<NamedU64V1>,
    hash_streams: Vec<HashStreamV1>,
    range_tables: Vec<RangeTableV1>,
    relation_tuple_counts: Vec<NamedU64V1>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct ShapeModuleV1 {
    module_ordinal: u32,
    module: String,
    air_instance_count: u32,
    component_count: u32,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct ShapeAirInstanceV1 {
    module_ordinal: u32,
    module: String,
    air_instance_ordinal: u32,
    columns: ColumnCountsV1,
    column_log_sizes: AirColumnLayoutV1,
    claimed_sum_count: u32,
    max_log_size: u32,
    max_constraint_log_degree_bound: u32,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct ShapeComponentV1 {
    module_ordinal: u32,
    module: String,
    component_ordinal: u32,
    air_instance_ordinal: u32,
    component: String,
    trace_rows: u32,
    constraint_count: u32,
    max_constraint_log_degree_bound: u32,
    trace_mask_column_counts: Vec<u32>,
}

#[derive(Clone, Copy, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct ColumnCountsV1 {
    preprocessed: u32,
    trace: u32,
    interaction: u32,
    post_interaction: u32,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct CircuitArtifactV1 {
    schema_version: u64,
    profile: &'static str,
    proof_system_id: &'static str,
    constraint_system_version: &'static str,
    module_order: Vec<String>,
    modules: Vec<ModuleLayoutV1>,
    relations: Vec<RelationLayoutV1>,
    transcript: TranscriptLayoutV1,
    serialized_claims: Vec<SerializedClaimV1>,
    hash_streams: Vec<HashStreamV1>,
    range_tables: Vec<RangeTableV1>,
    constants: Vec<ArtifactConstantV1>,
    shape_manifest_sha256: Digest32,
    tree_zero: TreeZeroV1,
    proof_system: ProofSystemV1,
    proof_serialization: ProofSerializationV1,
    enabled_cargo_features: Vec<PackageFeaturesV1>,
    build_identity: BuildIdentityV1,
    soundness_source_tree: SoundnessSourceIdentityV1,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct ProofSerializationV1 {
    proof_codec: &'static str,
    envelope_magic: HexBytes,
    envelope_version: u64,
    envelope_header_bytes: u64,
    capacity_alignment_bytes: u64,
    bound_terms: Vec<ProofBoundTermV1>,
    deterministic_worst_case_bytes: u64,
    proof_body_capacity: u32,
    padding: &'static str,
    compression: &'static str,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct BuildIdentityV1 {
    cargo_lock_sha256: Digest32,
    rust_toolchain: RustToolchainV1,
    git: GitMetadataV1,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct RustToolchainV1 {
    channel: String,
    rust_toolchain_file_sha256: Digest32,
    rustc_release: String,
    rustc_commit_hash: String,
    rustc_commit_date: String,
    llvm_version: String,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct GitMetadataV1 {
    repository_kind: &'static str,
    object_format: String,
    source_commit_scope: &'static str,
    soundness_source_commit: String,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct SoundnessSourceIdentityV1 {
    algorithm: &'static str,
    workspace_files: Vec<String>,
    package_roots: Vec<String>,
    cargo_build_directory_name: &'static str,
    generated_recursive_exclusions: Vec<String>,
    manifest_sha256: Digest32,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct SourceTreeManifestV1 {
    schema_version: u64,
    workspace_files: Vec<String>,
    package_roots: Vec<String>,
    cargo_build_directory_name: &'static str,
    generated_recursive_exclusions: Vec<String>,
    files: Vec<SourceFileEntryV1>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct SourceFileEntryV1 {
    path: String,
    sha256: Digest32,
}

#[derive(Clone, Debug)]
struct GenerationEnvironmentV1 {
    cargo_lock_sha256: Digest32,
    enabled_cargo_features: Vec<PackageFeaturesV1>,
    rust_toolchain: RustToolchainV1,
    git: GitMetadataV1,
    source_manifest: SourceTreeManifestV1,
    source_manifest_sha256: Digest32,
}

#[derive(Clone, Debug)]
struct GeneratedOutputs {
    shape_manifest: Vec<u8>,
    artifact: Vec<u8>,
    hash_embedding: Vec<u8>,
    circuit_hash: Digest32,
    proof_body_capacity: u32,
}

#[derive(Clone, Debug)]
pub struct GenerationResult {
    pub circuit_hash: Digest32,
    pub proof_body_capacity: u32,
}

fn io_error(action: &'static str, path: &Path, source: io::Error) -> ArtifactError {
    ArtifactError::Io {
        action,
        path: path.to_owned(),
        source,
    }
}

fn read(path: &Path) -> Result<Vec<u8>, ArtifactError> {
    fs::read(path).map_err(|source| io_error("read", path, source))
}

fn checked_name_list<'a>(
    kind: &str,
    names: impl IntoIterator<Item = &'a str>,
) -> Result<(), ArtifactError> {
    let mut previous = None;
    for name in names {
        if name.is_empty() {
            return Err(ArtifactError::InvalidInput(format!(
                "{kind} contains an empty name"
            )));
        }
        if let Some(previous) = previous {
            if previous >= name {
                return Err(ArtifactError::InvalidInput(format!(
                    "{kind} names must be strictly sorted; {previous:?} precedes {name:?}"
                )));
            }
        }
        previous = Some(name);
    }
    Ok(())
}

impl GenerationInputV1 {
    fn validate(&self) -> Result<(), ArtifactError> {
        if self.credential_shape.issuer_cose_sig_structure_bytes
            != crate::mdoc::TS13_DEMO_ISSUER_MESSAGE_BYTES as u32
            || self.credential_shape.mso_payload_bytes
                != crate::mdoc::TS13_DEMO_MSO_PAYLOAD_BYTES as u32
            || self.credential_shape.padded_issuer_signed_item_bytes
                != u32::from(crate::mdoc::TS13_DEMO_ITEM_PADDED_BYTES)
            || self.credential_shape.digest_identifier_integer_widths
                != CANONICAL_DIGEST_IDENTIFIER_INTEGER_WIDTHS
        {
            return Err(ArtifactError::InvalidInput(
                "credential shape does not match the canonical A/B fixtures".to_owned(),
            ));
        }
        if self.request_context_corpus.corpus_sha256.to_string()
            != CANONICAL_REQUEST_CONTEXT_CORPUS_SHA256
            || self
                .request_context_corpus
                .observed_max_device_cose_sig_structure_bytes
                != CANONICAL_OBSERVED_MAX_DEVICE_COSE_SIG_STRUCTURE_BYTES
            || self.request_context_corpus.device_sig_structure_capacity
                != crate::mdoc::TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY as u32
        {
            return Err(ArtifactError::InvalidInput(
                "request-context corpus does not match the canonical corpus measurement".to_owned(),
            ));
        }

        let with_margin = self
            .request_context_corpus
            .observed_max_device_cose_sig_structure_bytes
            .checked_add(128)
            .ok_or_else(|| {
                ArtifactError::InvalidInput("request-context capacity margin overflows".to_owned())
            })?;
        let expected_capacity = with_margin.checked_next_power_of_two().ok_or_else(|| {
            ArtifactError::InvalidInput("request-context capacity exceeds u32".to_owned())
        })?;
        if self.request_context_corpus.device_sig_structure_capacity != expected_capacity {
            return Err(ArtifactError::InvalidInput(format!(
                "device Sig_structure capacity must be next_power_of_two(max + 128): expected \
                 {expected_capacity}, got {}",
                self.request_context_corpus.device_sig_structure_capacity
            )));
        }

        let module_names: Vec<_> = self
            .modules
            .iter()
            .map(|module| module.name.as_str())
            .collect();
        if module_names != CANONICAL_MODULE_ORDER {
            return Err(ArtifactError::InvalidInput(format!(
                "module order must be exactly {:?}",
                CANONICAL_MODULE_ORDER
            )));
        }
        let air_instance_count = self.modules.iter().try_fold(0_u32, |sum, module| {
            let count = u32::try_from(module.air_instances.len()).map_err(|_| {
                ArtifactError::InvalidInput("AIR instance count exceeds u32".to_owned())
            })?;
            sum.checked_add(count).ok_or_else(|| {
                ArtifactError::InvalidInput("AIR instance count exceeds u32".to_owned())
            })
        })?;
        if air_instance_count != 20 {
            return Err(ArtifactError::InvalidInput(format!(
                "the 19 logical module slots must expand to exactly 20 AIR instances, got \
                 {air_instance_count}"
            )));
        }

        let mut component_names = BTreeSet::new();
        for module in &self.modules {
            if module.air_instances.is_empty() {
                return Err(ArtifactError::InvalidInput(format!(
                    "module {:?} has no AIR instances",
                    module.name
                )));
            }
            for air in &module.air_instances {
                let max_column_log_size = air.columns.all().map(|(_, log_size)| *log_size).max();
                if let Some(max_column_log_size) = max_column_log_size {
                    if max_column_log_size >= u32::BITS {
                        return Err(ArtifactError::InvalidInput(format!(
                            "module {:?} has an unsupported column log size",
                            module.name
                        )));
                    }
                } else if air.max_log_size != 0 {
                    return Err(ArtifactError::InvalidInput(format!(
                        "zero-column AIR in module {:?} must have max log size zero",
                        module.name
                    )));
                }
                if air.max_constraint_log_degree_bound == 0 {
                    return Err(ArtifactError::InvalidInput(format!(
                        "module {:?} has a zero constraint-degree bound",
                        module.name
                    )));
                }
                for (tree, log_sizes) in [
                    ("preprocessed", &air.columns.preprocessed_m31_log_sizes),
                    ("trace", &air.columns.trace_m31_log_sizes),
                    ("interaction", &air.columns.interaction_m31_log_sizes),
                    (
                        "post_interaction",
                        &air.columns.post_interaction_m31_log_sizes,
                    ),
                ] {
                    if log_sizes.iter().any(|&log_size| log_size >= u32::BITS) {
                        return Err(ArtifactError::InvalidInput(format!(
                            "module {:?} has an invalid ordered {tree} M31 column log size",
                            module.name
                        )));
                    }
                }
                for component in &air.components {
                    if component.name.is_empty()
                        || !component_names.insert(component.name.as_str())
                        || component.constraint_count == 0
                        || component.max_constraint_log_degree_bound == 0
                        || component.trace_rows == 0
                        || !component.trace_rows.is_power_of_two()
                        || component.trace_mask_column_counts.is_empty()
                        || component.trace_mask_column_counts.len() > 4
                    {
                        return Err(ArtifactError::InvalidInput(format!(
                            "AIR component names and constraint/mask geometry must be complete and \
                             globally unique: {:?}",
                            component.name
                        )));
                    }
                }
            }
        }
        let public_context = &self.modules[3];
        if public_context.air_instances.len() != 1
            || !public_context.air_instances[0].components.is_empty()
        {
            return Err(ArtifactError::InvalidInput(
                "Ts13PublicContextBind must be exactly one zero-component AIR instance".to_owned(),
            ));
        }
        let item_parsers = &self.modules[8];
        if item_parsers.air_instances.len() != 2 {
            return Err(ArtifactError::InvalidInput(
                "the private item parser slot must contain its outer and inner AIR instances"
                    .to_owned(),
            ));
        }
        if self.modules[14].air_instances.len() != 1 {
            return Err(ArtifactError::InvalidInput(
                "the private device-key binder must be one AIR instance".to_owned(),
            ));
        }
        if self.modules[15].air_instances.len() != 1 {
            return Err(ArtifactError::InvalidInput(
                "private-device ML-DSA must be one contiguous AIR instance".to_owned(),
            ));
        }
        let public_revocation = &self.modules[18];
        if public_revocation.air_instances.len() != 1
            || !public_revocation.air_instances[0].components.is_empty()
        {
            return Err(ArtifactError::InvalidInput(
                "the public revocation binder must be exactly one zero-component AIR instance"
                    .to_owned(),
            ));
        }
        for module in &self.modules {
            let post_interaction_columns =
                module.air_instances.iter().try_fold(0_u32, |sum, air| {
                    sum.checked_add(checked_column_count(
                        &air.columns.post_interaction_m31_log_sizes,
                    )?)
                    .ok_or_else(|| {
                        ArtifactError::InvalidInput(
                            "post-interaction column count exceeds u32".to_owned(),
                        )
                    })
                })?;
            let expected = if module.name == SHARED_KECCAK_SERVICE_MODULE {
                CANONICAL_KECCAK_POST_INTERACTION_COLUMN_COUNT
            } else {
                0
            };
            if post_interaction_columns != expected {
                return Err(ArtifactError::InvalidInput(format!(
                    "module {:?} must declare exactly {expected} physical post-interaction columns",
                    module.name
                )));
            }
        }

        let modules: BTreeSet<_> = self
            .modules
            .iter()
            .map(|module| module.name.as_str())
            .collect();
        let mut relations = BTreeSet::new();
        for relation in &self.relations {
            if relation.name.is_empty()
                || !relations.insert(relation.name.as_str())
                || !modules.contains(relation.challenge_owner_module.as_str())
                || relation.tuple.is_empty()
            {
                return Err(ArtifactError::InvalidInput(format!(
                    "relation {:?} has an invalid name, owner, tuple, or use list",
                    relation.name
                )));
            }
            for relation_use in &relation.uses {
                if !modules.contains(relation_use.module.as_str())
                    || !component_names.contains(relation_use.component.as_str())
                    || relation_use.multiplicity.is_empty()
                {
                    return Err(ArtifactError::InvalidInput(format!(
                        "relation {:?} has an invalid use",
                        relation.name
                    )));
                }
                let component_module = self
                    .modules
                    .iter()
                    .find(|module| {
                        module
                            .air_instances
                            .iter()
                            .flat_map(|air| &air.components)
                            .any(|component| component.name == relation_use.component)
                    })
                    .map(|module| module.name.as_str());
                if component_module != Some(relation_use.module.as_str()) {
                    return Err(ArtifactError::InvalidInput(format!(
                        "relation {:?} assigns component {:?} to the wrong module",
                        relation.name, relation_use.component
                    )));
                }
            }
        }
        let reserved_transcript_relations = self
            .relations
            .iter()
            .filter(|relation| relation.uses.is_empty())
            .map(|relation| relation.name.as_str())
            .collect::<Vec<_>>();
        if reserved_transcript_relations != RESERVED_TRANSCRIPT_RELATION_NAMES {
            return Err(ArtifactError::InvalidInput(format!(
                "relations without uses must be exactly {:?}",
                RESERVED_TRANSCRIPT_RELATION_NAMES
            )));
        }
        let relation_use_count = self.relations.iter().try_fold(0_usize, |sum, relation| {
            sum.checked_add(relation.uses.len()).ok_or_else(|| {
                ArtifactError::InvalidInput("relation use count exceeds usize".to_owned())
            })
        })?;
        if self.relations.len() != CANONICAL_RELATION_COUNT
            || relation_use_count != CANONICAL_RELATION_USE_COUNT
        {
            return Err(ArtifactError::InvalidInput(format!(
                "the canonical profile must contain exactly {CANONICAL_RELATION_COUNT} relations and \
                 {CANONICAL_RELATION_USE_COUNT} uses, got {} and {relation_use_count}",
                self.relations.len()
            )));
        }
        for (relation_name, use_ordinal, expected) in canonical_relation_multiplicities()? {
            let actual = self
                .relations
                .iter()
                .find(|relation| relation.name == relation_name)
                .and_then(|relation| relation.uses.get(use_ordinal))
                .map(|relation_use| relation_use.multiplicity.as_str());
            if actual != Some(expected.as_str()) {
                return Err(ArtifactError::InvalidInput(format!(
                    "relation {relation_name:?} use {use_ordinal} has stale multiplicity metadata"
                )));
            }
        }
        for (name, expected_fields) in [
            (
                "r41_private_digest_id",
                &[
                    "encoding_len",
                    "encoded_byte_0",
                    "encoded_byte_1",
                    "encoded_byte_2",
                    "encoded_byte_3",
                    "encoded_byte_4",
                    "digest_id_lo16",
                    "digest_id_hi16",
                ][..],
            ),
            ("r44_private_mso_start", &["mso_start"][..]),
        ] {
            let relation = self
                .relations
                .iter()
                .find(|relation| relation.name == name)
                .ok_or_else(|| {
                    ArtifactError::InvalidInput(format!(
                        "the canonical relation {name:?} is missing"
                    ))
                })?;
            if relation
                .tuple
                .iter()
                .map(|field| field.name.as_str())
                .ne(expected_fields.iter().copied())
                || relation
                    .tuple
                    .iter()
                    .any(|field| !matches!(field.scalar, ColumnScalarV1::M31))
            {
                return Err(ArtifactError::InvalidInput(format!(
                    "relation {name:?} differs from the canonical schema"
                )));
            }
        }
        checked_name_list(
            "relation",
            self.relations.iter().map(|relation| relation.name.as_str()),
        )?;

        for (kind, entries) in [
            ("public mix", &self.transcript.public_mix_order),
            ("challenge", &self.transcript.challenge_order),
        ] {
            if entries.is_empty() {
                return Err(ArtifactError::InvalidInput(format!(
                    "{kind} order cannot be empty"
                )));
            }
            for entry in entries {
                if !modules.contains(entry.owner_module.as_str())
                    || entry.name.is_empty()
                    || entry.encoding.is_empty()
                {
                    return Err(ArtifactError::InvalidInput(format!(
                        "{kind} entry is incomplete or has an unknown owner"
                    )));
                }
            }
        }
        if self.transcript.public_mix_order.len() != CANONICAL_PUBLIC_MIX_COUNT
            || self.transcript.challenge_order.len() != CANONICAL_CHALLENGE_ENTRY_COUNT
        {
            return Err(ArtifactError::InvalidInput(format!(
                "the canonical transcript must contain exactly {CANONICAL_PUBLIC_MIX_COUNT} public \
                mixes and {CANONICAL_CHALLENGE_ENTRY_COUNT} challenge entries"
            )));
        }
        for (ordinal, name, encoding, fixed_length) in [
            (
                2,
                "p02_shared_keccak_job_list",
                KECCAK_PUBLIC_MIX_ENCODING,
                KECCAK_PUBLIC_MIX_FIXED_LENGTH,
            ),
            (
                8,
                "p08_outer_private_item_cbor_parser",
                OUTER_CBOR_PUBLIC_MIX_ENCODING,
                32,
            ),
            (
                9,
                "p09_inner_private_item_cbor_parser",
                INNER_CBOR_PUBLIC_MIX_ENCODING,
                32,
            ),
            (
                10,
                "p10_private_item_binder",
                ITEM_BIND_PUBLIC_MIX_ENCODING,
                136,
            ),
            (
                11,
                "p11_private_mso_binder",
                MSO_BIND_PUBLIC_MIX_ENCODING,
                296,
            ),
            (
                12,
                "p12_mdoc_private_mso_validity",
                MSO_VALIDITY_PUBLIC_MIX_ENCODING,
                208,
            ),
            (
                13,
                "p13_private_value_digests_scanner",
                VALUE_DIGESTS_PUBLIC_MIX_ENCODING,
                304,
            ),
        ] {
            let entry = &self.transcript.public_mix_order[ordinal];
            if entry.name != name
                || entry.encoding != encoding
                || entry.fixed_length != Some(fixed_length)
            {
                return Err(ArtifactError::InvalidInput(format!(
                    "public mix {name:?} differs from the canonical transcript"
                )));
            }
        }
        let expected_public_mix_owners = self
            .modules
            .iter()
            .flat_map(|module| module.air_instances.iter().map(|_| module.name.as_str()))
            .collect::<Vec<_>>();
        if self
            .transcript
            .public_mix_order
            .iter()
            .zip(expected_public_mix_owners)
            .enumerate()
            .any(|(ordinal, (entry, owner))| {
                entry.owner_module != owner || !entry.name.starts_with(&format!("p{ordinal:02}_"))
            })
        {
            return Err(ArtifactError::InvalidInput(
                "public mixes must follow the exact physical AIR order".to_owned(),
            ));
        }
        if self
            .transcript
            .challenge_order
            .iter()
            .enumerate()
            .any(|(ordinal, entry)| !entry.name.starts_with(&format!("c{ordinal:03}_")))
        {
            return Err(ArtifactError::InvalidInput(
                "challenge entries must carry their exact transcript ordinal".to_owned(),
            ));
        }
        let mut relation_challenge_count = 0_usize;
        for relation in &self.relations {
            let suffix = format!("_{}", relation.name);
            let mut matches = self
                .transcript
                .challenge_order
                .iter()
                .filter(|entry| entry.name.ends_with(&suffix));
            let Some(entry) = matches.next() else {
                return Err(ArtifactError::InvalidInput(format!(
                    "relation {:?} has no transcript challenge",
                    relation.name
                )));
            };
            if matches.next().is_some()
                || entry.owner_module != relation.challenge_owner_module
                || entry.fixed_length != Some(32)
            {
                return Err(ArtifactError::InvalidInput(format!(
                    "relation {:?} must have exactly one 32-byte challenge owned by {:?}",
                    relation.name, relation.challenge_owner_module
                )));
            }
            relation_challenge_count += 1;
        }
        let raw_challenges = self
            .transcript
            .challenge_order
            .len()
            .checked_sub(relation_challenge_count)
            .ok_or_else(|| {
                ArtifactError::InvalidInput(
                    "relation challenge count exceeds transcript length".to_owned(),
                )
            })?;
        if raw_challenges != CANONICAL_RAW_MLDSA_CHALLENGE_COUNT {
            return Err(ArtifactError::InvalidInput(format!(
                "the canonical transcript must contain exactly \
                 {CANONICAL_RAW_MLDSA_CHALLENGE_COUNT} raw ML-DSA challenges, got {raw_challenges}"
            )));
        }
        let relation_secure_field_draws =
            relation_challenge_count.checked_mul(2).ok_or_else(|| {
                ArtifactError::InvalidInput(
                    "relation secure-field draw count exceeds usize".to_owned(),
                )
            })?;
        let total_secure_field_draws = relation_secure_field_draws
            .checked_add(raw_challenges)
            .ok_or_else(|| {
                ArtifactError::InvalidInput(
                    "total secure-field draw count exceeds usize".to_owned(),
                )
            })?;
        checked_name_list(
            "challenge",
            self.transcript
                .challenge_order
                .iter()
                .map(|entry| entry.name.as_str()),
        )?;

        if self
            .serialized_claims
            .iter()
            .map(|claim| claim.name.as_str())
            .collect::<Vec<_>>()
            != CANONICAL_SERIALIZED_CLAIM_NAMES
        {
            return Err(ArtifactError::InvalidInput(
                "serialized claim order differs from MdocProof".to_owned(),
            ));
        }
        let mut claim_names = BTreeSet::new();
        for claim in &self.serialized_claims {
            if claim.name.is_empty()
                || !claim_names.insert(claim.name.as_str())
                || claim.encoding.is_empty()
                || claim.fixed_length == 0
            {
                return Err(ArtifactError::InvalidInput(
                    "serialized claims require a unique name, encoding, and fixed byte length"
                        .to_owned(),
                ));
            }
            checked_name_list(
                "claim fixed-vector",
                claim
                    .fixed_vector_lengths
                    .iter()
                    .map(|entry| entry.name.as_str()),
            )?;
        }
        checked_named_values("stream ID", &self.stream_ids)?;
        let hash_shapes = canonical_hash_stream_shapes()?;
        if self.stream_ids != canonical_stream_ids(&hash_shapes)? {
            return Err(ArtifactError::InvalidInput(format!(
                "the canonical profile must contain the exact {CANONICAL_STREAM_ID_COUNT} named \
                 stream IDs"
            )));
        }
        checked_name_list(
            "hash stream",
            self.hash_streams.iter().map(|stream| stream.name.as_str()),
        )?;
        let declared_stream_ids = self
            .stream_ids
            .iter()
            .map(|entry| entry.value)
            .collect::<BTreeSet<_>>();
        if self.hash_streams.len() != CANONICAL_HASH_STREAM_COUNT
            || self
                .hash_streams
                .iter()
                .map(|stream| stream.stream_id)
                .collect::<BTreeSet<_>>()
                .len()
                != self.hash_streams.len()
        {
            return Err(ArtifactError::InvalidInput(
                "hash streams require the exact count and unique stream IDs".to_owned(),
            ));
        }
        for stream in &self.hash_streams {
            let shape = hash_shapes.get(&stream.name).ok_or_else(|| {
                ArtifactError::InvalidInput(format!(
                    "hash stream {:?} has no canonical job shape",
                    stream.name
                ))
            })?;
            let (hash_function, input_capacity_bytes, output_bytes) = hash_stream_geometry(*shape)?;
            if stream.stream_id != u64::from(shape.absorb_stream_id)
                || stream.hash_function != hash_function
                || stream.domain_separator.0 != [0x1f]
                || stream.job_count != 1
                || stream.input_capacity_bytes != input_capacity_bytes
                || stream.output_bytes != output_bytes
                || !declared_stream_ids.contains(&stream.stream_id)
            {
                return Err(ArtifactError::InvalidInput(format!(
                    "hash stream {:?} differs from its live circuit job shape",
                    stream.name
                )));
            }
        }
        checked_name_list(
            "range table",
            self.range_tables.iter().map(|table| table.name.as_str()),
        )?;
        if self.range_tables.len() != CANONICAL_RANGE_TABLE_COUNT
            || self.range_tables.iter().any(|table| {
                table.value_kind.is_empty()
                    || table.bit_width == 0
                    || table.bit_width > 31
                    || table.log_size >= u32::BITS
                    || table.active_rows > (1_u32 << table.log_size)
            })
        {
            return Err(ArtifactError::InvalidInput(
                "range tables require sorted unique names and valid bit/log/row geometry"
                    .to_owned(),
            ));
        }
        checked_named_values("relation tuple count", &self.relation_tuple_counts)?;
        if self.relation_tuple_counts.len() != self.relations.len()
            || self
                .relation_tuple_counts
                .iter()
                .zip(&self.relations)
                .any(|(count, relation)| {
                    count.name != relation.name || count.value != relation.tuple.len() as u64
                })
        {
            return Err(ArtifactError::InvalidInput(
                "relation tuple counts must exactly match every ordered relation schema".to_owned(),
            ));
        }
        checked_name_list(
            "implementation constant",
            self.implementation_constants
                .iter()
                .map(|constant| constant.name.as_str()),
        )?;
        let implementation_constant_names = self
            .implementation_constants
            .iter()
            .map(|constant| constant.name.as_str())
            .collect::<Vec<_>>();
        if implementation_constant_names != CANONICAL_IMPLEMENTATION_CONSTANT_NAMES {
            return Err(ArtifactError::InvalidInput(
                "implementation constants differ from the canonical allowlist".to_owned(),
            ));
        }
        let digest_widths = self
            .implementation_constants
            .iter()
            .find(|constant| constant.name == "impl.digest_identifier_integer_widths")
            .expect("the canonical allowlist contains digest identifier widths");
        let ConstantValueV1::UnsignedVector(digest_widths) = &digest_widths.value else {
            return Err(ArtifactError::InvalidInput(
                "digest identifier widths must be an unsigned vector".to_owned(),
            ));
        };
        if !digest_widths
            .iter()
            .copied()
            .eq(CANONICAL_DIGEST_IDENTIFIER_INTEGER_WIDTHS.map(u64::from))
        {
            return Err(ArtifactError::InvalidInput(
                "digest identifier widths differ from the canonical profile".to_owned(),
            ));
        }
        for (name, expected) in [
            ("impl.air_instance_count", u64::from(air_instance_count)),
            ("impl.component_count", component_names.len() as u64),
            (
                "impl.expand_a_job_count",
                CANONICAL_EXPAND_A_JOB_COUNT as u64,
            ),
            ("impl.hash_job_count", CANONICAL_HASH_STREAM_COUNT as u64),
            (
                "impl.keccak_service_claimed_sum_count",
                stwo_keccak::service::service_claimed_sums_len() as u64,
            ),
            (
                "impl.mldsa.device_claimed_sum_count",
                stwo_mldsa::statement::hosted_private_key_claimed_sums_len() as u64,
            ),
            (
                "impl.mldsa.device_group_eval_count",
                stwo_mldsa::statement::n_private_key_group_evals() as u64,
            ),
            (
                "impl.mldsa.issuer_claimed_sum_count",
                stwo_mldsa::statement::hosted_claimed_sums_len() as u64,
            ),
            (
                "impl.mldsa.issuer_group_eval_count",
                stwo_mldsa::statement::n_group_evals() as u64,
            ),
            (
                "impl.mldsa.revocation_claimed_sum_count",
                stwo_mldsa::statement::hosted_claimed_sums_len() as u64,
            ),
            (
                "impl.mldsa.revocation_group_eval_count",
                stwo_mldsa::statement::n_group_evals() as u64,
            ),
            (
                "impl.issuer_cose_sig_structure_bytes",
                u64::from(self.credential_shape.issuer_cose_sig_structure_bytes),
            ),
            (
                "impl.mso_payload_bytes",
                u64::from(self.credential_shape.mso_payload_bytes),
            ),
            (
                "impl.padded_issuer_signed_item_bytes",
                u64::from(self.credential_shape.padded_issuer_signed_item_bytes),
            ),
            (
                "impl.challenge.raw_mldsa_secure_field_draws",
                raw_challenges as u64,
            ),
            (
                "impl.challenge.relation_instances",
                relation_challenge_count as u64,
            ),
            (
                "impl.challenge.relation_secure_field_draws",
                relation_secure_field_draws as u64,
            ),
            (
                "impl.challenge.total_secure_field_draws",
                total_secure_field_draws as u64,
            ),
        ] {
            if implementation_unsigned(&self.implementation_constants, name)? != expected {
                return Err(ArtifactError::InvalidInput(format!(
                    "implementation constant {name:?} differs from its typed source"
                )));
            }
        }
        let claimed_sum_count = self
            .modules
            .iter()
            .flat_map(|module| &module.air_instances)
            .try_fold(0_u64, |sum, air| {
                sum.checked_add(u64::from(air.claimed_sum_count))
                    .ok_or_else(|| {
                        ArtifactError::InvalidInput(
                            "global claimed-sum count exceeds u64".to_owned(),
                        )
                    })
            })?;
        if implementation_unsigned(
            &self.implementation_constants,
            "impl.transcript.global_claimed_sum_count",
        )? != claimed_sum_count
            || implementation_text(
                &self.implementation_constants,
                "impl.transcript.claim_mix_order",
            )? != CLAIM_MIX_ORDER
            || implementation_text(
                &self.implementation_constants,
                "impl.transcript.phase_order",
            )? != TRANSCRIPT_PHASE_ORDER
            || implementation_text(&self.implementation_constants, "impl.keccak.job_order")?
                != KECCAK_JOB_ORDER
            || implementation_text(
                &self.implementation_constants,
                "impl.hash_stream_record_stream_id_semantics",
            )? != HASH_STREAM_ID_SEMANTICS
        {
            return Err(ArtifactError::InvalidInput(
                "transcript or hash-job descriptions differ from typed geometry".to_owned(),
            ));
        }

        let tree_column_counts = expected_tree_column_counts(self)?;
        if self.tree_zero.derivation.is_empty()
            || self.tree_zero.hash != "Blake2s-256"
            || self.tree_zero.preprocessed_column_order.len() != tree_column_counts[0] as usize
            || self
                .tree_zero
                .preprocessed_column_order
                .iter()
                .collect::<BTreeSet<_>>()
                .len()
                != self.tree_zero.preprocessed_column_order.len()
            || self.tree_zero.committed_column_log_sizes.len() != tree_column_counts[0] as usize
            || self
                .tree_zero
                .committed_column_log_sizes
                .iter()
                .any(|&log_size| log_size >= u32::BITS)
        {
            return Err(ArtifactError::InvalidInput(format!(
                "tree zero must carry the exact {}-column deduplicated order and log geometry",
                tree_column_counts[0]
            )));
        }
        let security_bits = self
            .proof_system
            .fri_query_count
            .checked_mul(self.proof_system.fri_log_blowup_factor)
            .and_then(|bits| bits.checked_add(self.proof_system.pow_bits))
            .ok_or_else(|| {
                ArtifactError::InvalidInput("PCS security label exceeds u32".to_owned())
            })?;
        if self.proof_system.field != "M31"
            || self.proof_system.field_modulus != 2_147_483_647
            || self.proof_system.secure_extension_field != "QM31"
            || self.proof_system.secure_extension_degree != 4
            || self.proof_system.pcs != "CirclePcs"
            || self.proof_system.commitment_hash != "Blake2s-256"
            || self.proof_system.merkle_hash != "Blake2s-256"
            || self.proof_system.fri_log_last_layer_degree_bound != 1
            || !(1..=16).contains(&self.proof_system.fri_log_blowup_factor)
            || self.proof_system.fri_query_count == 0
            || self.proof_system.fri_fold_step != 2
            || self.proof_system.pow_bits > 32
            || security_bits < 128
        {
            return Err(ArtifactError::InvalidInput(
                "proof-system field, hash, FRI shape, or 128-bit PCS label is invalid".to_owned(),
            ));
        }
        let executable_pcs = crate::mdoc::mdoc_ts13_pcs_config();
        if self.proof_system.fri_log_last_layer_degree_bound
            != executable_pcs.fri_config.log_last_layer_degree_bound
            || self.proof_system.fri_log_blowup_factor
                != executable_pcs.fri_config.log_blowup_factor
            || usize::try_from(self.proof_system.fri_query_count).ok()
                != Some(executable_pcs.fri_config.n_queries)
            || self.proof_system.fri_fold_step != executable_pcs.fri_config.fold_step
            || self.proof_system.pow_bits != executable_pcs.pow_bits
            || self.proof_system.lifting_log_size != executable_pcs.lifting_log_size
        {
            return Err(ArtifactError::InvalidInput(
                "artifact PCS configuration differs from the executable verifier".to_owned(),
            ));
        }
        checked_name_list(
            "Merkle tree",
            self.proof_system
                .merkle_trees
                .iter()
                .map(|tree| tree.name.as_str()),
        )?;
        let merkle_tree_names = self
            .proof_system
            .merkle_trees
            .iter()
            .map(|tree| tree.name.as_str())
            .collect::<Vec<_>>();
        if merkle_tree_names != CANONICAL_MERKLE_TREE_ORDER {
            return Err(ArtifactError::InvalidInput(format!(
                "Merkle-tree order must be exactly {CANONICAL_MERKLE_TREE_ORDER:?}"
            )));
        }
        let tree_depths = expected_tree_depths(self)?;
        let fri_input_log_size = self.proof_system.lifting_log_size.unwrap_or(tree_depths[4]);
        let fri_layers = expected_fri_layers(&self.proof_system, fri_input_log_size)?;
        if self.proof_system.merkle_trees.len() != 5
            || self
                .proof_system
                .merkle_trees
                .iter()
                .zip(tree_depths)
                .zip(tree_column_counts)
                .any(|((tree, depth), columns)| {
                    tree.depth != depth
                        || tree.digest_bytes != 32
                        || u64::from(tree.maximum_opened_columns) != columns
                        || tree.sampled_value_length_histogram.is_empty()
                        || tree
                            .sampled_value_length_histogram
                            .iter()
                            .map(|entry| u64::from(entry.count))
                            .sum::<u64>()
                            != columns
                        || tree
                            .sampled_value_length_histogram
                            .iter()
                            .any(|entry| entry.value == 0 || entry.count == 0)
                        || tree
                            .sampled_value_length_histogram
                            .windows(2)
                            .any(|pair| pair[0].value >= pair[1].value)
                })
            || self.proof_system.fri_layers != fri_layers
        {
            return Err(ArtifactError::InvalidInput(
                "Merkle-tree or FRI-layer geometry differs from the typed circuit and PCS"
                    .to_owned(),
            ));
        }
        validate_proof_bound(&ts13_demo_proof_bound_terms(self)?)?;

        let expected_packages: Vec<_> = SOURCE_PACKAGE_ROOTS
            .iter()
            .map(|root| root.trim_start_matches("crates/"))
            .collect();
        let actual_packages: Vec<_> = self
            .enabled_cargo_features
            .iter()
            .map(|package| package.package.as_str())
            .collect();
        if actual_packages != expected_packages {
            return Err(ArtifactError::InvalidInput(format!(
                "enabled feature sets must list exactly {expected_packages:?}"
            )));
        }
        for package in &self.enabled_cargo_features {
            checked_name_list("Cargo feature", package.features.iter().map(String::as_str))?;
        }
        Ok(())
    }

    fn shape_manifest(&self) -> Result<ShapeManifestV1, ArtifactError> {
        let modules = self
            .modules
            .iter()
            .enumerate()
            .map(|(module_ordinal, module)| {
                Ok(ShapeModuleV1 {
                    module_ordinal: u32::try_from(module_ordinal).map_err(|_| {
                        ArtifactError::InvalidInput("module ordinal exceeds u32".to_owned())
                    })?,
                    module: module.name.clone(),
                    air_instance_count: u32::try_from(module.air_instances.len()).map_err(
                        |_| {
                            ArtifactError::InvalidInput("AIR instance count exceeds u32".to_owned())
                        },
                    )?,
                    component_count: u32::try_from(
                        module
                            .air_instances
                            .iter()
                            .map(|air| air.components.len())
                            .sum::<usize>(),
                    )
                    .map_err(|_| {
                        ArtifactError::InvalidInput("component count exceeds u32".to_owned())
                    })?,
                })
            })
            .collect::<Result<Vec<_>, ArtifactError>>()?;
        let mut air_instances = Vec::new();
        let mut components = Vec::new();
        for (module_ordinal, module) in self.modules.iter().enumerate() {
            let module_ordinal = u32::try_from(module_ordinal).map_err(|_| {
                ArtifactError::InvalidInput("module ordinal exceeds u32".to_owned())
            })?;
            let mut component_ordinal = 0_u32;
            for (air_instance_ordinal, air) in module.air_instances.iter().enumerate() {
                let air_instance_ordinal = u32::try_from(air_instance_ordinal).map_err(|_| {
                    ArtifactError::InvalidInput("AIR instance ordinal exceeds u32".to_owned())
                })?;
                air_instances.push(ShapeAirInstanceV1 {
                    module_ordinal,
                    module: module.name.clone(),
                    air_instance_ordinal,
                    columns: air.columns.counts()?,
                    column_log_sizes: air.columns.clone(),
                    claimed_sum_count: air.claimed_sum_count,
                    max_log_size: air.max_log_size,
                    max_constraint_log_degree_bound: air.max_constraint_log_degree_bound,
                });
                for component in &air.components {
                    components.push(ShapeComponentV1 {
                        module_ordinal,
                        module: module.name.clone(),
                        component_ordinal,
                        air_instance_ordinal,
                        component: component.name.clone(),
                        trace_rows: component.trace_rows,
                        constraint_count: component.constraint_count,
                        max_constraint_log_degree_bound: component.max_constraint_log_degree_bound,
                        trace_mask_column_counts: component.trace_mask_column_counts.clone(),
                    });
                    component_ordinal = component_ordinal.checked_add(1).ok_or_else(|| {
                        ArtifactError::InvalidInput("component ordinal exceeds u32".to_owned())
                    })?;
                }
            }
        }
        Ok(ShapeManifestV1 {
            schema_version: SHAPE_SCHEMA_VERSION,
            profile: PROFILE_ID,
            credential_shape: self.credential_shape.clone(),
            request_context_corpus: self.request_context_corpus.clone(),
            modules,
            air_instances,
            components,
            stream_ids: self.stream_ids.clone(),
            hash_streams: self.hash_streams.clone(),
            range_tables: self.range_tables.clone(),
            relation_tuple_counts: self.relation_tuple_counts.clone(),
        })
    }
}

fn checked_column_count(log_sizes: &[u32]) -> Result<u32, ArtifactError> {
    u32::try_from(log_sizes.len())
        .map_err(|_| ArtifactError::InvalidInput("AIR column count exceeds u32".to_owned()))
}

fn checked_named_values(kind: &str, values: &[NamedU64V1]) -> Result<(), ArtifactError> {
    if values.is_empty() {
        return Err(ArtifactError::InvalidInput(format!(
            "{kind} list cannot be empty"
        )));
    }
    checked_name_list(kind, values.iter().map(|entry| entry.name.as_str()))
}

fn implementation_unsigned(
    constants: &[ArtifactConstantV1],
    name: &str,
) -> Result<u64, ArtifactError> {
    let constant = constants
        .iter()
        .find(|constant| constant.name == name)
        .ok_or_else(|| ArtifactError::InvalidInput(format!("missing constant {name:?}")))?;
    let ConstantValueV1::Unsigned(value) = constant.value else {
        return Err(ArtifactError::InvalidInput(format!(
            "constant {name:?} must be unsigned"
        )));
    };
    Ok(value)
}

fn implementation_text<'a>(
    constants: &'a [ArtifactConstantV1],
    name: &str,
) -> Result<&'a str, ArtifactError> {
    let constant = constants
        .iter()
        .find(|constant| constant.name == name)
        .ok_or_else(|| ArtifactError::InvalidInput(format!("missing constant {name:?}")))?;
    let ConstantValueV1::Text(value) = &constant.value else {
        return Err(ArtifactError::InvalidInput(format!(
            "constant {name:?} must be text"
        )));
    };
    Ok(value)
}

fn expected_tree_column_counts(input: &GenerationInputV1) -> Result<[u64; 5], ArtifactError> {
    let air_instances = input
        .modules
        .iter()
        .flat_map(|module| &module.air_instances)
        .collect::<Vec<_>>();
    let count = |value: usize| {
        u64::try_from(value)
            .map_err(|_| ArtifactError::InvalidInput("tree column count exceeds u64".to_owned()))
    };
    let sum_columns = |select: fn(&AirColumnLayoutV1) -> &[u32]| {
        air_instances.iter().try_fold(0_u64, |total, air| {
            total
                .checked_add(count(select(&air.columns).len())?)
                .ok_or_else(|| {
                    ArtifactError::InvalidInput("tree column count exceeds u64".to_owned())
                })
        })
    };
    let composition_split = composition_log_split(input)?;
    let composition_columns = 1_u64
        .checked_shl(composition_split)
        .and_then(|parts| parts.checked_mul(u64::from(input.proof_system.secure_extension_degree)))
        .ok_or_else(|| {
            ArtifactError::InvalidInput("composition column count exceeds u64".to_owned())
        })?;
    Ok([
        count(input.tree_zero.committed_column_log_sizes.len())?,
        sum_columns(|columns| &columns.trace_m31_log_sizes)?,
        sum_columns(|columns| &columns.interaction_m31_log_sizes)?,
        sum_columns(|columns| &columns.post_interaction_m31_log_sizes)?,
        composition_columns,
    ])
}

fn composition_log_split(input: &GenerationInputV1) -> Result<u32, ArtifactError> {
    input
        .modules
        .iter()
        .flat_map(|module| &module.air_instances)
        .flat_map(|air| &air.components)
        .map(|component| {
            if component.trace_rows == 0 {
                return Err(ArtifactError::InvalidInput(
                    "composition component has no trace rows".to_owned(),
                ));
            }
            Ok(component
                .max_constraint_log_degree_bound
                .saturating_sub(component.trace_rows.ilog2()))
        })
        .try_fold(1, |maximum, split| split.map(|split| maximum.max(split)))
}

fn composition_evaluation_log_size(input: &GenerationInputV1) -> Result<u32, ArtifactError> {
    let maximum_trace_log_size = input
        .modules
        .iter()
        .flat_map(|module| &module.air_instances)
        .flat_map(|air| &air.components)
        .map(|component| {
            if component.trace_rows == 0 {
                return Err(ArtifactError::InvalidInput(
                    "composition component has no trace rows".to_owned(),
                ));
            }
            Ok(component.trace_rows.ilog2())
        })
        .try_fold(None, |maximum, log_size| {
            log_size
                .map(|log_size| Some(maximum.map_or(log_size, |value: u32| value.max(log_size))))
        })?
        .ok_or_else(|| ArtifactError::InvalidInput("circuit has no AIR components".to_owned()))?;
    maximum_trace_log_size
        .checked_add(composition_log_split(input)?)
        .ok_or_else(|| {
            ArtifactError::InvalidInput("composition evaluation log size exceeds u32".to_owned())
        })
}

fn expected_tree_depths(input: &GenerationInputV1) -> Result<[u32; 5], ArtifactError> {
    let maximum = |logs: Vec<u32>, tree: &str| {
        logs.into_iter()
            .max()
            .ok_or_else(|| ArtifactError::InvalidInput(format!("{tree} has no committed columns")))
    };
    let air_instances = input
        .modules
        .iter()
        .flat_map(|module| &module.air_instances)
        .collect::<Vec<_>>();
    let base_logs = [
        maximum(
            input.tree_zero.committed_column_log_sizes.clone(),
            "preprocessed tree",
        )?,
        maximum(
            air_instances
                .iter()
                .flat_map(|air| air.columns.trace_m31_log_sizes.iter().copied())
                .collect(),
            "trace tree",
        )?,
        maximum(
            air_instances
                .iter()
                .flat_map(|air| air.columns.interaction_m31_log_sizes.iter().copied())
                .collect(),
            "interaction tree",
        )?,
        maximum(
            air_instances
                .iter()
                .flat_map(|air| air.columns.post_interaction_m31_log_sizes.iter().copied())
                .collect(),
            "post-interaction tree",
        )?,
        maximum(
            air_instances.iter().map(|air| air.max_log_size).collect(),
            "composition tree",
        )?,
    ];
    if let Some(lifting_log_size) = input.proof_system.lifting_log_size {
        let mut minimum_lifting_log_size = composition_evaluation_log_size(input)?;
        for base_log in base_logs {
            let minimum = base_log
                .checked_add(input.proof_system.fri_log_blowup_factor)
                .ok_or_else(|| ArtifactError::InvalidInput("tree depth exceeds u32".to_owned()))?;
            minimum_lifting_log_size = minimum_lifting_log_size.max(minimum);
        }
        if lifting_log_size < minimum_lifting_log_size {
            return Err(ArtifactError::InvalidInput(format!(
                "lifting log size {lifting_log_size} is below the required interpolation or \
                 commitment domain {minimum_lifting_log_size}"
            )));
        }
        return Ok([lifting_log_size; 5]);
    }
    let mut depths = [0; 5];
    for (depth, base_log) in depths.iter_mut().zip(base_logs) {
        *depth = base_log
            .checked_add(input.proof_system.fri_log_blowup_factor)
            .ok_or_else(|| ArtifactError::InvalidInput("tree depth exceeds u32".to_owned()))?;
    }
    Ok(depths)
}

fn expected_fri_layers(
    proof_system: &ProofSystemV1,
    first_input_log_size: u32,
) -> Result<Vec<FriLayerParametersV1>, ArtifactError> {
    let last_input_log_size = proof_system
        .fri_log_last_layer_degree_bound
        .checked_add(proof_system.fri_log_blowup_factor)
        .ok_or_else(|| ArtifactError::InvalidInput("FRI last-layer log exceeds u32".to_owned()))?;
    if proof_system.fri_fold_step == 0 || first_input_log_size <= last_input_log_size {
        return Err(ArtifactError::InvalidInput(
            "FRI requires a positive fold step and at least one layer".to_owned(),
        ));
    }
    let mut input_log_size = first_input_log_size;
    let mut layers = Vec::new();
    while input_log_size > last_input_log_size {
        let step = proof_system
            .fri_fold_step
            .min(input_log_size - last_input_log_size);
        let output_log_size = input_log_size - step;
        let merkle_depth = if step > 1 && input_log_size >= 2 {
            input_log_size - 2
        } else {
            input_log_size
        };
        let opened_per_query = 1_u32
            .checked_shl(step)
            .and_then(|value| value.checked_sub(1))
            .ok_or_else(|| ArtifactError::InvalidInput("FRI fold step exceeds u32".to_owned()))?;
        let maximum_opened_values = proof_system
            .fri_query_count
            .checked_mul(opened_per_query)
            .ok_or_else(|| {
                ArtifactError::InvalidInput("FRI witness bound exceeds u32".to_owned())
            })?;
        layers.push(FriLayerParametersV1 {
            input_log_size,
            output_log_size,
            merkle_depth,
            maximum_opened_values,
        });
        input_log_size = output_log_size;
    }
    Ok(layers)
}

fn ts13_demo_proof_bound_terms(
    input: &GenerationInputV1,
) -> Result<Vec<ProofBoundTermV1>, ArtifactError> {
    let trees = &input.proof_system.merkle_trees;
    let query_count = u64::from(input.proof_system.fri_query_count);
    let committed_columns = trees.iter().try_fold(0_u64, |sum, tree| {
        sum.checked_add(u64::from(tree.maximum_opened_columns))
            .ok_or_else(|| ArtifactError::InvalidInput("tree column total exceeds u64".to_owned()))
    })?;
    let queried_base_fields = committed_columns.checked_mul(query_count).ok_or_else(|| {
        ArtifactError::InvalidInput("queried base-field bound exceeds u64".to_owned())
    })?;
    let tree_hashes = trees.iter().try_fold(0_u64, |sum, tree| {
        let hashes = u64::from(tree.depth)
            .checked_mul(query_count)
            .ok_or_else(|| {
                ArtifactError::InvalidInput("Merkle hash bound exceeds u64".to_owned())
            })?;
        sum.checked_add(hashes)
            .ok_or_else(|| ArtifactError::InvalidInput("Merkle hash bound exceeds u64".to_owned()))
    })?;
    let fri_hashes = input
        .proof_system
        .fri_layers
        .iter()
        .try_fold(0_u64, |sum, layer| {
            let hashes = u64::from(layer.merkle_depth)
                .checked_mul(query_count)
                .ok_or_else(|| {
                    ArtifactError::InvalidInput("FRI hash bound exceeds u64".to_owned())
                })?;
            sum.checked_add(hashes)
                .ok_or_else(|| ArtifactError::InvalidInput("FRI hash bound exceeds u64".to_owned()))
        })?;
    let fri_witnesses = input
        .proof_system
        .fri_layers
        .iter()
        .try_fold(0_u64, |sum, layer| {
            sum.checked_add(u64::from(layer.maximum_opened_values))
                .ok_or_else(|| {
                    ArtifactError::InvalidInput("FRI witness bound exceeds u64".to_owned())
                })
        })?;
    let sampled_secure_fields = trees.iter().try_fold(0_u64, |tree_sum, tree| {
        let tree_fields =
            tree.sampled_value_length_histogram
                .iter()
                .try_fold(0_u64, |sum, entry| {
                    let fields = u64::from(entry.value)
                        .checked_mul(u64::from(entry.count))
                        .ok_or_else(|| {
                            ArtifactError::InvalidInput(
                                "sampled secure-field bound exceeds u64".to_owned(),
                            )
                        })?;
                    sum.checked_add(fields).ok_or_else(|| {
                        ArtifactError::InvalidInput(
                            "sampled secure-field bound exceeds u64".to_owned(),
                        )
                    })
                })?;
        tree_sum.checked_add(tree_fields).ok_or_else(|| {
            ArtifactError::InvalidInput("sampled secure-field bound exceeds u64".to_owned())
        })
    })?;
    let outer_claim_bytes = input
        .serialized_claims
        .iter()
        .filter(|claim| claim.name != "post_interaction_payloads")
        .try_fold(0_u64, |sum, claim| {
            sum.checked_add(u64::from(claim.fixed_length))
                .ok_or_else(|| {
                    ArtifactError::InvalidInput("outer claim bound exceeds u64".to_owned())
                })
        })?;
    let tree_count = u64::try_from(trees.len())
        .map_err(|_| ArtifactError::InvalidInput("tree count exceeds u64".to_owned()))?;
    let fri_layer_count = u64::try_from(input.proof_system.fri_layers.len())
        .map_err(|_| ArtifactError::InvalidInput("FRI layer count exceeds u64".to_owned()))?;
    let air_count = u64::try_from(
        input
            .modules
            .iter()
            .map(|module| module.air_instances.len())
            .sum::<usize>(),
    )
    .map_err(|_| ArtifactError::InvalidInput("AIR count exceeds u64".to_owned()))?;
    let tree_vector_framing = 8_u64
        .checked_add(tree_count.checked_mul(8).ok_or_else(|| {
            ArtifactError::InvalidInput("tree vector framing exceeds u64".to_owned())
        })?)
        .and_then(|bytes| bytes.checked_add(committed_columns.checked_mul(8)?))
        .ok_or_else(|| ArtifactError::InvalidInput("tree vector framing exceeds u64".to_owned()))?;
    let tree_decommitment_framing = 8_u64
        .checked_add(tree_count.checked_mul(8).ok_or_else(|| {
            ArtifactError::InvalidInput("tree decommitment framing exceeds u64".to_owned())
        })?)
        .ok_or_else(|| {
            ArtifactError::InvalidInput("tree decommitment framing exceeds u64".to_owned())
        })?;
    let fri_vector_framing = 20_u64
        .checked_add(fri_layer_count.checked_mul(16).ok_or_else(|| {
            ArtifactError::InvalidInput("FRI vector framing exceeds u64".to_owned())
        })?)
        .ok_or_else(|| ArtifactError::InvalidInput("FRI vector framing exceeds u64".to_owned()))?;
    let post_payload_framing = 8_u64
        .checked_add(air_count.checked_mul(8).ok_or_else(|| {
            ArtifactError::InvalidInput("post-payload framing exceeds u64".to_owned())
        })?)
        .ok_or_else(|| {
            ArtifactError::InvalidInput("post-payload framing exceeds u64".to_owned())
        })?;
    let last_layer_coefficients = 1_u64
        .checked_shl(input.proof_system.fri_log_last_layer_degree_bound)
        .ok_or_else(|| {
            ArtifactError::InvalidInput("FRI last-layer coefficient count exceeds u64".to_owned())
        })?;
    let pcs_config_bytes = 28 + 4 * u64::from(input.proof_system.lifting_log_size.is_some());
    let terms = vec![
        ProofBoundTermV1 {
            section: ProofBoundSectionV1::ProofHeader,
            name: "pcs_config".to_owned(),
            maximum_item_count: 1,
            maximum_serialized_bytes_per_item: pcs_config_bytes,
        },
        ProofBoundTermV1 {
            section: ProofBoundSectionV1::Commitments,
            name: "blake2s_roots".to_owned(),
            maximum_item_count: tree_count,
            maximum_serialized_bytes_per_item: 32,
        },
        ProofBoundTermV1 {
            section: ProofBoundSectionV1::Commitments,
            name: "vector_length".to_owned(),
            maximum_item_count: 1,
            maximum_serialized_bytes_per_item: 8,
        },
        ProofBoundTermV1 {
            section: ProofBoundSectionV1::Queries,
            name: "base_field_vector_framing".to_owned(),
            maximum_item_count: 1,
            maximum_serialized_bytes_per_item: tree_vector_framing,
        },
        ProofBoundTermV1 {
            section: ProofBoundSectionV1::MerkleDecommitments,
            name: "hash_witnesses".to_owned(),
            maximum_item_count: tree_hashes,
            maximum_serialized_bytes_per_item: 32,
        },
        ProofBoundTermV1 {
            section: ProofBoundSectionV1::MerkleDecommitments,
            name: "vector_framing".to_owned(),
            maximum_item_count: 1,
            maximum_serialized_bytes_per_item: tree_decommitment_framing,
        },
        ProofBoundTermV1 {
            section: ProofBoundSectionV1::FriLayers,
            name: "commitments".to_owned(),
            maximum_item_count: fri_layer_count,
            maximum_serialized_bytes_per_item: 32,
        },
        ProofBoundTermV1 {
            section: ProofBoundSectionV1::FriLayers,
            name: "hash_witnesses".to_owned(),
            maximum_item_count: fri_hashes,
            maximum_serialized_bytes_per_item: 32,
        },
        ProofBoundTermV1 {
            section: ProofBoundSectionV1::FriLayers,
            name: "last_layer_coefficients".to_owned(),
            maximum_item_count: last_layer_coefficients,
            maximum_serialized_bytes_per_item: 16,
        },
        ProofBoundTermV1 {
            section: ProofBoundSectionV1::FriLayers,
            name: "secure_field_witnesses".to_owned(),
            maximum_item_count: fri_witnesses,
            maximum_serialized_bytes_per_item: 16,
        },
        ProofBoundTermV1 {
            section: ProofBoundSectionV1::FriLayers,
            name: "vector_framing".to_owned(),
            maximum_item_count: 1,
            maximum_serialized_bytes_per_item: fri_vector_framing,
        },
        ProofBoundTermV1 {
            section: ProofBoundSectionV1::Claims,
            name: "fixed_outer_claims_and_framing".to_owned(),
            maximum_item_count: 1,
            maximum_serialized_bytes_per_item: outer_claim_bytes,
        },
        ProofBoundTermV1 {
            section: ProofBoundSectionV1::ColumnValues,
            name: "queried_base_fields".to_owned(),
            maximum_item_count: queried_base_fields,
            maximum_serialized_bytes_per_item: 4,
        },
        ProofBoundTermV1 {
            section: ProofBoundSectionV1::ColumnValues,
            name: "sampled_secure_fields".to_owned(),
            maximum_item_count: sampled_secure_fields,
            maximum_serialized_bytes_per_item: 16,
        },
        ProofBoundTermV1 {
            section: ProofBoundSectionV1::ColumnValues,
            name: "sampled_vector_framing".to_owned(),
            maximum_item_count: 1,
            maximum_serialized_bytes_per_item: tree_vector_framing,
        },
        ProofBoundTermV1 {
            section: ProofBoundSectionV1::PostInteractionPayloads,
            name: "keccak_round_gkr".to_owned(),
            maximum_item_count: 1,
            maximum_serialized_bytes_per_item: air_core::gkr::TS13_DEMO_GKR_MAX_PAYLOAD_BYTES
                as u64,
        },
        ProofBoundTermV1 {
            section: ProofBoundSectionV1::Pow,
            name: "nonce".to_owned(),
            maximum_item_count: 1,
            maximum_serialized_bytes_per_item: 8,
        },
        ProofBoundTermV1 {
            section: ProofBoundSectionV1::SerializationOverhead,
            name: "post_payload_vector_framing".to_owned(),
            maximum_item_count: 1,
            maximum_serialized_bytes_per_item: post_payload_framing,
        },
    ];
    validate_proof_bound(&terms)?;
    Ok(terms)
}

fn validate_proof_bound(terms: &[ProofBoundTermV1]) -> Result<(), ArtifactError> {
    let required = [
        ProofBoundSectionV1::ProofHeader,
        ProofBoundSectionV1::Commitments,
        ProofBoundSectionV1::Queries,
        ProofBoundSectionV1::MerkleDecommitments,
        ProofBoundSectionV1::FriLayers,
        ProofBoundSectionV1::Claims,
        ProofBoundSectionV1::ColumnValues,
        ProofBoundSectionV1::PostInteractionPayloads,
        ProofBoundSectionV1::Pow,
        ProofBoundSectionV1::SerializationOverhead,
    ];
    let present: BTreeSet<_> = terms.iter().map(|term| term.section).collect();
    if present != BTreeSet::from(required) {
        return Err(ArtifactError::InvalidInput(
            "proof serialization bound must cover header, commitments, queries, Merkle \
             decommitments, FRI layers, claims, column values, post-interaction payloads, PoW, \
             and serialization overhead"
                .to_owned(),
        ));
    }
    if terms.iter().any(|term| {
        term.name.is_empty()
            || term.maximum_item_count == 0
            || term.maximum_serialized_bytes_per_item == 0
    }) {
        return Err(ArtifactError::InvalidInput(
            "proof serialization bound terms must have non-zero counts and byte sizes".to_owned(),
        ));
    }
    if terms.windows(2).any(|pair| {
        (pair[0].section, pair[0].name.as_str()) >= (pair[1].section, pair[1].name.as_str())
    }) {
        return Err(ArtifactError::InvalidInput(
            "proof serialization bound terms must be strictly sorted by section and name"
                .to_owned(),
        ));
    }
    Ok(())
}

fn deterministic_proof_bound(terms: &[ProofBoundTermV1]) -> Result<(u64, u32), ArtifactError> {
    let worst_case = terms.iter().try_fold(0_u64, |sum, term| {
        let bytes = term
            .maximum_item_count
            .checked_mul(term.maximum_serialized_bytes_per_item)
            .ok_or_else(|| {
                ArtifactError::InvalidInput("proof serialization term overflows u64".to_owned())
            })?;
        sum.checked_add(bytes).ok_or_else(|| {
            ArtifactError::InvalidInput("proof serialization bound overflows u64".to_owned())
        })
    })?;
    let capacity = worst_case
        .checked_add(ENVELOPE_CAPACITY_ALIGNMENT - 1)
        .map(|value| value / ENVELOPE_CAPACITY_ALIGNMENT * ENVELOPE_CAPACITY_ALIGNMENT)
        .ok_or_else(|| ArtifactError::InvalidInput("proof capacity overflows u64".to_owned()))?;
    if !capacity.is_multiple_of(ENVELOPE_CAPACITY_ALIGNMENT) {
        return Err(ArtifactError::InvalidInput(
            "proof capacity does not meet the independent alignment rail".to_owned(),
        ));
    }
    let capacity = u32::try_from(capacity).map_err(|_| {
        ArtifactError::InvalidInput(
            "envelope capacity does not fit its u32 header field".to_owned(),
        )
    })?;
    Ok((worst_case, capacity))
}

fn builtin_constants(normative_spec_digest: Digest32) -> Vec<ArtifactConstantV1> {
    let mut constants = vec![
        constant_bytes(
            "cbor.device_key_info_prefix",
            &[
                0x6d, 0x64, 0x65, 0x76, 0x69, 0x63, 0x65, 0x4b, 0x65, 0x79, 0x49, 0x6e, 0x66, 0x6f,
                0xa1, 0x69, 0x64, 0x65, 0x76, 0x69, 0x63, 0x65, 0x4b, 0x65, 0x79, 0xa3, 0x01, 0x07,
                0x03, 0x38, 0x30, 0x20, 0x59, 0x07, 0xa0,
            ],
        ),
        constant_text("context.domain", "EUDI-TS13-DEMO-CONTEXT-V1"),
        constant_text("context.public_mix_domain", "EUDI-TS13-PUBLIC-CONTEXT-V1"),
        constant_unsigned("profile.disclosed_attributes", 1),
        constant_text("profile.document_type", "eu.europa.ec.eudi.pid.1"),
        constant_text("profile.element", "age_over_18"),
        constant_text("profile.expected_cbor_hex", "f5"),
        constant_text("profile.format", "mso_mdoc_zk"),
        constant_text("profile.hash", "SHA-256"),
        constant_text("profile.issuer_authentication", "FIPS-204-ML-DSA-65"),
        constant_text("profile.device_authentication", "FIPS-204-ML-DSA-65"),
        constant_text("profile.revocation_authentication", "FIPS-204-ML-DSA-65"),
        constant_text(
            "profile.device_authentication_profile",
            "ISO-18013-5-DeviceAuthentication",
        ),
        constant_text("profile.namespace", "eu.europa.ec.eudi.pid.1"),
        constant_unsigned("profile.trusted_issuer_count", 1),
        constant_unsigned("profile.revocation_mandatory", 1),
        constant_text("profile.timestamp_precision", "UTC-whole-Unix-second"),
        constant_text(
            "privacy.claim",
            "public-input unlinkable; transcript zero knowledge pending",
        ),
        constant_text("spec.eudi_arf_commit", CANONICAL_EUDI_ARF_COMMIT),
        constant_text(
            "spec.eudi_arf_ts13_path",
            "docs/technical-specifications/ts13-zksnarks.md",
        ),
        constant_bytes("spec.normative_document_sha256", &normative_spec_digest.0),
        constant_unsigned("expand_a.accepted_coefficients_per_polynomial", 256),
        constant_unsigned("expand_a.candidate_bits", 23),
        constant_unsigned("expand_a.jobs", CANONICAL_EXPAND_A_JOB_COUNT as u64),
        constant_unsigned("expand_a.modulus_q", 8_380_417),
        constant_unsigned("expand_a.squeeze_blocks_per_job", 6),
        constant_unsigned("private_key_evaluation.a_evaluation_count", 30),
        constant_unsigned("private_key_evaluation.coefficient_evaluation_count", 30),
        constant_unsigned("private_key_evaluation.inverse_ntt_normalizer", 8_347_681),
        constant_unsigned("private_key_evaluation.radix", 512),
        constant_unsigned("private_key_evaluation.scaled_t1_factor", 1 << 13),
        constant_unsigned("private_key_evaluation.t1_evaluation_count", 6),
        constant_unsigned("private_key_evaluation.t1_hi_bits", 1),
        constant_unsigned("private_key_evaluation.t1_lo_bits", 9),
        constant_unsigned(
            "device_key_binding.active_rows",
            CANONICAL_DEVICE_KEY_BIND_ACTIVE_ROWS as u64,
        ),
        constant_unsigned(
            "device_key_binding.public_key_bytes",
            CANONICAL_DEVICE_PUBLIC_KEY_BYTES as u64,
        ),
        constant_unsigned("device_key_binding.rho_rows", 32),
        constant_unsigned("validity.maximum_year", 2099),
        constant_unsigned("validity.minimum_year", 2020),
        constant_bytes("envelope.magic", b"EUIDTS13"),
    ];
    constants.sort_by(|left, right| left.name.cmp(&right.name));
    constants
}

fn constant_unsigned(name: &str, value: u64) -> ArtifactConstantV1 {
    ArtifactConstantV1 {
        name: name.to_owned(),
        value: ConstantValueV1::Unsigned(value),
    }
}

fn constant_text(name: &str, value: &str) -> ArtifactConstantV1 {
    ArtifactConstantV1 {
        name: name.to_owned(),
        value: ConstantValueV1::Text(value.to_owned()),
    }
}

fn constant_bytes(name: &str, value: &[u8]) -> ArtifactConstantV1 {
    ArtifactConstantV1 {
        name: name.to_owned(),
        value: ConstantValueV1::Bytes(HexBytes(value.to_vec())),
    }
}

fn canonical_cbor<T: Serialize>(value: &T) -> Result<Vec<u8>, ArtifactError> {
    let value = Value::serialized(value).map_err(|error| ArtifactError::Cbor(error.to_string()))?;
    let mut encoded = Vec::new();
    encode_canonical_value(&value, &mut encoded)?;
    Ok(encoded)
}

fn encode_canonical_value(value: &Value, encoded: &mut Vec<u8>) -> Result<(), ArtifactError> {
    match value {
        Value::Integer(integer) => {
            let integer = i128::from(*integer);
            if integer >= 0 {
                push_argument(encoded, 0, integer as u64);
            } else {
                push_argument(encoded, 1, (-1 - integer) as u64);
            }
        }
        Value::Bytes(bytes) => {
            push_argument(encoded, 2, usize_to_u64(bytes.len())?);
            encoded.extend_from_slice(bytes);
        }
        Value::Text(text) => {
            push_argument(encoded, 3, usize_to_u64(text.len())?);
            encoded.extend_from_slice(text.as_bytes());
        }
        Value::Array(items) => {
            push_argument(encoded, 4, usize_to_u64(items.len())?);
            for item in items {
                encode_canonical_value(item, encoded)?;
            }
        }
        Value::Map(entries) => {
            let mut canonical_entries = Vec::with_capacity(entries.len());
            for (key, item) in entries {
                let mut encoded_key = Vec::new();
                encode_canonical_value(key, &mut encoded_key)?;
                canonical_entries.push((encoded_key, item));
            }
            canonical_entries.sort_by(|left, right| {
                left.0
                    .len()
                    .cmp(&right.0.len())
                    .then_with(|| left.0.cmp(&right.0))
            });
            if canonical_entries
                .windows(2)
                .any(|pair| pair[0].0 == pair[1].0)
            {
                return Err(ArtifactError::Cbor(
                    "map contains duplicate canonical keys".to_owned(),
                ));
            }
            push_argument(encoded, 5, usize_to_u64(canonical_entries.len())?);
            for (key, item) in canonical_entries {
                encoded.extend_from_slice(&key);
                encode_canonical_value(item, encoded)?;
            }
        }
        Value::Tag(tag, item) => {
            push_argument(encoded, 6, *tag);
            encode_canonical_value(item, encoded)?;
        }
        Value::Bool(false) => encoded.push(0xf4),
        Value::Bool(true) => encoded.push(0xf5),
        Value::Null => encoded.push(0xf6),
        Value::Float(_) => {
            return Err(ArtifactError::Cbor(
                "floating-point values are forbidden in circuit artifacts".to_owned(),
            ));
        }
        _ => {
            return Err(ArtifactError::Cbor(
                "unsupported CBOR value in circuit artifact".to_owned(),
            ));
        }
    }
    Ok(())
}

fn usize_to_u64(value: usize) -> Result<u64, ArtifactError> {
    u64::try_from(value).map_err(|_| ArtifactError::Cbor("container length exceeds u64".to_owned()))
}

fn push_argument(encoded: &mut Vec<u8>, major: u8, value: u64) {
    let prefix = major << 5;
    match value {
        0..=23 => encoded.push(prefix | value as u8),
        24..=0xff => encoded.extend_from_slice(&[prefix | 24, value as u8]),
        0x100..=0xffff => {
            encoded.push(prefix | 25);
            encoded.extend_from_slice(&(value as u16).to_be_bytes());
        }
        0x1_0000..=0xffff_ffff => {
            encoded.push(prefix | 26);
            encoded.extend_from_slice(&(value as u32).to_be_bytes());
        }
        _ => {
            encoded.push(prefix | 27);
            encoded.extend_from_slice(&value.to_be_bytes());
        }
    }
}

fn normalized_relative_path(path: &Path) -> Result<String, ArtifactError> {
    let mut normalized = String::new();
    for component in path.components() {
        let Component::Normal(component) = component else {
            return Err(ArtifactError::InvalidInput(format!(
                "source path is not a normalized relative path: {}",
                path.display()
            )));
        };
        let component = component.to_str().ok_or_else(|| {
            ArtifactError::InvalidInput(format!(
                "source path is not valid UTF-8: {}",
                path.display()
            ))
        })?;
        if !normalized.is_empty() {
            normalized.push('/');
        }
        normalized.push_str(component);
    }
    Ok(normalized)
}

fn is_generated_exclusion(path: &str) -> bool {
    GENERATED_RECURSION_EXCLUSIONS.contains(&path)
}

fn is_target_directory(path: &Path) -> bool {
    path.file_name().is_some_and(|name| name == "target")
}

fn collect_directory_files(
    workspace: &Path,
    directory: &Path,
    files: &mut Vec<SourceFileEntryV1>,
) -> Result<(), ArtifactError> {
    let entries = fs::read_dir(directory).map_err(|source| io_error("list", directory, source))?;
    for entry in entries {
        let entry = entry.map_err(|source| io_error("list", directory, source))?;
        let path = entry.path();
        let file_type = entry
            .file_type()
            .map_err(|source| io_error("inspect", &path, source))?;
        if file_type.is_dir() {
            if !is_target_directory(&path) {
                collect_directory_files(workspace, &path, files)?;
            }
        } else if file_type.is_file() {
            let relative = path.strip_prefix(workspace).map_err(|_| {
                ArtifactError::InvalidInput(format!(
                    "source file escaped workspace: {}",
                    path.display()
                ))
            })?;
            let relative = normalized_relative_path(relative)?;
            if !is_generated_exclusion(&relative) {
                files.push(SourceFileEntryV1 {
                    path: relative,
                    sha256: Digest32::of(&read(&path)?),
                });
            }
        } else {
            return Err(ArtifactError::InvalidInput(format!(
                "source tree contains a non-regular file: {}",
                path.display()
            )));
        }
    }
    Ok(())
}

fn collect_source_tree(workspace: &Path) -> Result<SourceTreeManifestV1, ArtifactError> {
    let cargo_toml = workspace.join("Cargo.toml");
    let normative_spec = workspace.join(NORMATIVE_SPEC_PATH);
    let mut files = vec![
        SourceFileEntryV1 {
            path: "Cargo.toml".to_owned(),
            sha256: Digest32::of(&read(&cargo_toml)?),
        },
        SourceFileEntryV1 {
            path: NORMATIVE_SPEC_PATH.to_owned(),
            sha256: Digest32::of(&read(&normative_spec)?),
        },
    ];
    for root in SOURCE_PACKAGE_ROOTS {
        collect_directory_files(workspace, &workspace.join(root), &mut files)?;
    }
    files.sort_by(|left, right| left.path.cmp(&right.path));
    if files.windows(2).any(|pair| pair[0].path == pair[1].path) {
        return Err(ArtifactError::InvalidInput(
            "soundness source tree contains duplicate paths".to_owned(),
        ));
    }
    Ok(SourceTreeManifestV1 {
        schema_version: 1,
        workspace_files: vec!["Cargo.toml".to_owned(), NORMATIVE_SPEC_PATH.to_owned()],
        package_roots: SOURCE_PACKAGE_ROOTS
            .iter()
            .map(|path| (*path).to_owned())
            .collect(),
        cargo_build_directory_name: "target",
        generated_recursive_exclusions: GENERATED_RECURSION_EXCLUSIONS
            .iter()
            .map(|path| (*path).to_owned())
            .collect(),
        files,
    })
}

fn command_output(
    program: &'static str,
    arguments: &[&str],
    workspace: &Path,
) -> Result<Vec<u8>, ArtifactError> {
    let output = Command::new(program)
        .args(arguments)
        .current_dir(workspace)
        .output()
        .map_err(|source| ArtifactError::Command {
            program,
            detail: source.to_string(),
        })?;
    if !output.status.success() {
        return Err(ArtifactError::Command {
            program,
            detail: String::from_utf8_lossy(&output.stderr).trim().to_owned(),
        });
    }
    Ok(output.stdout)
}

fn resolved_source_package_features(
    workspace: &Path,
) -> Result<Vec<PackageFeaturesV1>, ArtifactError> {
    let output = command_output(
        "cargo",
        &["metadata", "--format-version", "1", "--locked"],
        workspace,
    )?;
    let metadata: serde_json::Value = serde_json::from_slice(&output).map_err(|error| {
        ArtifactError::InvalidInput(format!("cargo metadata is not valid JSON: {error}"))
    })?;
    let packages = metadata
        .get("packages")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| ArtifactError::InvalidInput("cargo metadata omitted packages".to_owned()))?;
    let nodes = metadata
        .get("resolve")
        .and_then(|resolve| resolve.get("nodes"))
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| {
            ArtifactError::InvalidInput("cargo metadata omitted resolved nodes".to_owned())
        })?;

    SOURCE_PACKAGE_ROOTS
        .iter()
        .map(|root| {
            let expected_manifest = fs::canonicalize(workspace.join(root).join("Cargo.toml"))
                .map_err(|source| {
                    io_error(
                        "canonicalize",
                        &workspace.join(root).join("Cargo.toml"),
                        source,
                    )
                })?;
            let package = packages
                .iter()
                .find(|package| {
                    package
                        .get("manifest_path")
                        .and_then(serde_json::Value::as_str)
                        .and_then(|path| fs::canonicalize(path).ok())
                        .as_ref()
                        == Some(&expected_manifest)
                })
                .ok_or_else(|| {
                    ArtifactError::InvalidInput(format!(
                        "cargo metadata omitted source package {root:?}"
                    ))
                })?;
            let id = package
                .get("id")
                .and_then(serde_json::Value::as_str)
                .ok_or_else(|| {
                    ArtifactError::InvalidInput(format!(
                        "cargo metadata package {root:?} omitted its ID"
                    ))
                })?;
            let name = package
                .get("name")
                .and_then(serde_json::Value::as_str)
                .ok_or_else(|| {
                    ArtifactError::InvalidInput(format!(
                        "cargo metadata package {root:?} omitted its name"
                    ))
                })?;
            let node = nodes
                .iter()
                .find(|node| node.get("id").and_then(serde_json::Value::as_str) == Some(id))
                .ok_or_else(|| {
                    ArtifactError::InvalidInput(format!(
                        "cargo metadata omitted resolved features for {name:?}"
                    ))
                })?;
            let mut features = node
                .get("features")
                .and_then(serde_json::Value::as_array)
                .ok_or_else(|| {
                    ArtifactError::InvalidInput(format!(
                        "cargo metadata package {name:?} omitted features"
                    ))
                })?
                .iter()
                .map(|feature| {
                    feature.as_str().map(str::to_owned).ok_or_else(|| {
                        ArtifactError::InvalidInput(format!(
                            "cargo metadata package {name:?} has a non-string feature"
                        ))
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            features.sort();
            if features.windows(2).any(|pair| pair[0] == pair[1]) {
                return Err(ArtifactError::InvalidInput(format!(
                    "cargo metadata package {name:?} has duplicate features"
                )));
            }
            Ok(PackageFeaturesV1 {
                package: name.to_owned(),
                features,
            })
        })
        .collect()
}

fn git_path_arguments(prefix: &[&'static str]) -> Vec<&'static str> {
    let mut arguments = prefix.to_vec();
    arguments.push("--");
    arguments.push("Cargo.toml");
    arguments.push(NORMATIVE_SPEC_PATH);
    arguments.extend(SOURCE_PACKAGE_ROOTS);
    arguments.push(":(exclude)artifacts/ts13-demo-v1/shape-manifest.cbor");
    arguments.push(":(exclude)artifacts/ts13-demo-v1/circuit-artifact-v1.cbor");
    arguments.push(":(exclude)crates/eu-id-prover/src/generated/ts13_demo_artifact.rs");
    arguments
}

fn checked_git_source_paths(
    workspace: &Path,
    manifest: &SourceTreeManifestV1,
) -> Result<(), ArtifactError> {
    let arguments = git_path_arguments(&["ls-files", "-z", "--cached"]);
    let output = command_output("git", &arguments, workspace)?;
    let mut tracked: Vec<String> = output
        .split(|byte| *byte == 0)
        .filter(|path| !path.is_empty())
        .map(|path| {
            std::str::from_utf8(path).map(str::to_owned).map_err(|_| {
                ArtifactError::InvalidInput(
                    "git returned a non-UTF-8 soundness source path".to_owned(),
                )
            })
        })
        .collect::<Result<_, _>>()?;
    tracked.retain(|path| {
        !Path::new(path)
            .components()
            .any(|component| component.as_os_str() == "target")
            && !is_generated_exclusion(path)
    });
    tracked.sort();
    let manifest_paths: Vec<_> = manifest
        .files
        .iter()
        .map(|file| file.path.clone())
        .collect();
    if tracked != manifest_paths {
        let tracked: BTreeSet<_> = tracked.into_iter().collect();
        let manifest: BTreeSet<_> = manifest_paths.into_iter().collect();
        let untracked: Vec<_> = manifest.difference(&tracked).take(5).cloned().collect();
        let missing: Vec<_> = tracked.difference(&manifest).take(5).cloned().collect();
        return Err(ArtifactError::InvalidInput(format!(
            "soundness source paths must exactly match checked-in files; untracked {untracked:?}, \
             missing {missing:?}"
        )));
    }
    Ok(())
}

fn checked_git_source_clean(workspace: &Path) -> Result<(), ArtifactError> {
    let arguments =
        git_path_arguments(&["status", "--porcelain=v1", "-z", "--untracked-files=all"]);
    let output = command_output("git", &arguments, workspace)?;
    if output.is_empty() {
        Ok(())
    } else {
        Err(ArtifactError::InvalidInput(
            "soundness source files are dirty; commit them before generating an artifact"
                .to_owned(),
        ))
    }
}

fn git_metadata(workspace: &Path) -> Result<GitMetadataV1, ArtifactError> {
    let object_format = command_output("git", &["rev-parse", "--show-object-format"], workspace)?;
    let object_format = String::from_utf8(object_format)
        .map_err(|_| ArtifactError::InvalidInput("git object format is not UTF-8".to_owned()))?
        .trim()
        .to_owned();
    let arguments = git_path_arguments(&["log", "-1", "--format=%H"]);
    let source_commit = command_output("git", &arguments, workspace)?;
    let source_commit = String::from_utf8(source_commit)
        .map_err(|_| ArtifactError::InvalidInput("git source commit is not UTF-8".to_owned()))?
        .trim()
        .to_owned();
    if object_format.is_empty() || source_commit.is_empty() {
        return Err(ArtifactError::InvalidInput(
            "git object format and soundness source commit are required".to_owned(),
        ));
    }
    Ok(GitMetadataV1 {
        repository_kind: "git",
        object_format,
        source_commit_scope: "latest commit touching the closed soundness source allowlist",
        soundness_source_commit: source_commit,
    })
}

fn toolchain_metadata(workspace: &Path) -> Result<RustToolchainV1, ArtifactError> {
    let toolchain_path = workspace.join("rust-toolchain.toml");
    let toolchain_bytes = read(&toolchain_path)?;
    let toolchain_text = std::str::from_utf8(&toolchain_bytes).map_err(|_| {
        ArtifactError::InvalidInput("rust-toolchain.toml is not valid UTF-8".to_owned())
    })?;
    let channel = toolchain_text
        .lines()
        .find_map(|line| {
            line.trim()
                .strip_prefix("channel")
                .and_then(|rest| rest.trim().strip_prefix('='))
                .map(str::trim)
                .and_then(|value| value.strip_prefix('"'))
                .and_then(|value| value.strip_suffix('"'))
        })
        .ok_or_else(|| {
            ArtifactError::InvalidInput("rust-toolchain.toml has no quoted channel".to_owned())
        })?
        .to_owned();

    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_owned());
    let output = Command::new(&rustc)
        .arg("--version")
        .arg("--verbose")
        .current_dir(workspace)
        .output()
        .map_err(|source| ArtifactError::Command {
            program: "rustc",
            detail: source.to_string(),
        })?;
    if !output.status.success() {
        return Err(ArtifactError::Command {
            program: "rustc",
            detail: String::from_utf8_lossy(&output.stderr).trim().to_owned(),
        });
    }
    let version = String::from_utf8(output.stdout)
        .map_err(|_| ArtifactError::InvalidInput("rustc -Vv output is not UTF-8".to_owned()))?;
    let fields: BTreeMap<_, _> = version
        .lines()
        .filter_map(|line| line.split_once(':'))
        .map(|(key, value)| (key.trim(), value.trim()))
        .collect();
    let required = |name| {
        fields
            .get(name)
            .map(|value| (*value).to_owned())
            .ok_or_else(|| ArtifactError::InvalidInput(format!("rustc -Vv omitted {name:?}")))
    };
    Ok(RustToolchainV1 {
        channel,
        rust_toolchain_file_sha256: Digest32::of(&toolchain_bytes),
        rustc_release: required("release")?,
        rustc_commit_hash: required("commit-hash")?,
        rustc_commit_date: required("commit-date")?,
        llvm_version: required("LLVM version")?,
    })
}

fn generation_environment(workspace: &Path) -> Result<GenerationEnvironmentV1, ArtifactError> {
    let source_manifest = collect_source_tree(workspace)?;
    checked_git_source_paths(workspace, &source_manifest)?;
    checked_git_source_clean(workspace)?;
    let source_manifest_sha256 = Digest32::of(&canonical_cbor(&source_manifest)?);
    Ok(GenerationEnvironmentV1 {
        cargo_lock_sha256: Digest32::of(&read(&workspace.join("Cargo.lock"))?),
        enabled_cargo_features: resolved_source_package_features(workspace)?,
        rust_toolchain: toolchain_metadata(workspace)?,
        git: git_metadata(workspace)?,
        source_manifest,
        source_manifest_sha256,
    })
}

fn source_file_digest(
    manifest: &SourceTreeManifestV1,
    path: &str,
) -> Result<Digest32, ArtifactError> {
    manifest
        .files
        .iter()
        .find(|file| file.path == path)
        .map(|file| file.sha256)
        .ok_or_else(|| {
            ArtifactError::InvalidInput(format!(
                "soundness source manifest omitted required file {path:?}"
            ))
        })
}

fn build_outputs(
    input: &GenerationInputV1,
    environment: GenerationEnvironmentV1,
) -> Result<GeneratedOutputs, ArtifactError> {
    input.validate()?;
    if input.enabled_cargo_features != environment.enabled_cargo_features {
        return Err(ArtifactError::InvalidInput(format!(
            "declared Cargo features differ from the resolved build: declared {:?}, resolved {:?}",
            input.enabled_cargo_features, environment.enabled_cargo_features
        )));
    }
    let shape_manifest = canonical_cbor(&input.shape_manifest()?)?;
    let shape_manifest_sha256 = Digest32::of(&shape_manifest);
    let proof_serialization_bound = ts13_demo_proof_bound_terms(input)?;
    let (worst_case, proof_body_capacity) = deterministic_proof_bound(&proof_serialization_bound)?;

    let normative_spec_digest =
        source_file_digest(&environment.source_manifest, NORMATIVE_SPEC_PATH)?;
    let mut constants = builtin_constants(normative_spec_digest);
    if constants
        .iter()
        .map(|constant| constant.name.as_str())
        .collect::<Vec<_>>()
        != CANONICAL_BUILTIN_CONSTANT_NAMES
    {
        return Err(ArtifactError::InvalidInput(
            "built-in constants differ from the canonical allowlist".to_owned(),
        ));
    }
    constants.extend(input.implementation_constants.clone());
    constants.sort_by(|left, right| left.name.cmp(&right.name));
    if constants
        .windows(2)
        .any(|pair| pair[0].name == pair[1].name)
    {
        return Err(ArtifactError::InvalidInput(
            "built-in and implementation constant names overlap".to_owned(),
        ));
    }

    let source_manifest = environment.source_manifest;
    let artifact = CircuitArtifactV1 {
        schema_version: ARTIFACT_SCHEMA_VERSION,
        profile: PROFILE_ID,
        proof_system_id: PROOF_SYSTEM_ID,
        constraint_system_version: CONSTRAINT_SYSTEM_VERSION,
        module_order: CANONICAL_MODULE_ORDER
            .iter()
            .map(|name| (*name).to_owned())
            .collect(),
        modules: input.modules.clone(),
        relations: input.relations.clone(),
        transcript: input.transcript.clone(),
        serialized_claims: input.serialized_claims.clone(),
        hash_streams: input.hash_streams.clone(),
        range_tables: input.range_tables.clone(),
        constants,
        shape_manifest_sha256,
        tree_zero: input.tree_zero.clone(),
        proof_system: input.proof_system.clone(),
        proof_serialization: ProofSerializationV1 {
            proof_codec: "bincode-1-fixed-int-little-endian",
            envelope_magic: HexBytes(b"EUIDTS13".to_vec()),
            envelope_version: ENVELOPE_VERSION,
            envelope_header_bytes: ENVELOPE_HEADER_BYTES,
            capacity_alignment_bytes: ENVELOPE_CAPACITY_ALIGNMENT,
            bound_terms: proof_serialization_bound,
            deterministic_worst_case_bytes: worst_case,
            proof_body_capacity,
            padding: "zero bytes to exact capacity; no encoded used length",
            compression: "forbidden",
        },
        enabled_cargo_features: input.enabled_cargo_features.clone(),
        build_identity: BuildIdentityV1 {
            cargo_lock_sha256: environment.cargo_lock_sha256,
            rust_toolchain: environment.rust_toolchain,
            git: environment.git,
        },
        soundness_source_tree: SoundnessSourceIdentityV1 {
            algorithm: "SHA-256(canonical-CBOR(sorted relative path,SHA-256(file bytes)) manifest)",
            workspace_files: source_manifest.workspace_files,
            package_roots: source_manifest.package_roots,
            cargo_build_directory_name: source_manifest.cargo_build_directory_name,
            generated_recursive_exclusions: source_manifest.generated_recursive_exclusions,
            manifest_sha256: environment.source_manifest_sha256,
        },
    };
    let artifact = canonical_cbor(&artifact)?;
    let circuit_hash = Digest32::of(&artifact);
    let hash_embedding = render_hash_embedding(
        circuit_hash,
        shape_manifest_sha256,
        environment.source_manifest_sha256,
        proof_body_capacity,
        input,
    );
    Ok(GeneratedOutputs {
        shape_manifest,
        artifact,
        hash_embedding: hash_embedding.into_bytes(),
        circuit_hash,
        proof_body_capacity,
    })
}

fn render_digest_array(output: &mut String, name: &str, digest: Digest32) {
    writeln!(output, "pub const {name}: [u8; 32] = [").expect("writing to String cannot fail");
    for chunk in digest.0.chunks(16) {
        output.push_str("    ");
        for (index, byte) in chunk.iter().enumerate() {
            if index != 0 {
                output.push(' ');
            }
            write!(output, "0x{byte:02x},").expect("writing to String cannot fail");
        }
        output.push('\n');
    }
    output.push_str("];\n");
}

fn render_usize_array(
    output: &mut String,
    name: &str,
    length: usize,
    values: impl IntoIterator<Item = u64>,
) {
    write!(output, "pub const {name}: [usize; {length}] = [")
        .expect("writing to String cannot fail");
    let values = values.into_iter().collect::<Vec<_>>();
    for (index, value) in values.iter().enumerate() {
        if index != 0 {
            output.push_str(", ");
        }
        write!(output, "{value}").expect("writing to String cannot fail");
    }
    output.push_str("];\n");
}

fn render_hash_embedding(
    circuit_hash: Digest32,
    shape_manifest_sha256: Digest32,
    source_manifest_sha256: Digest32,
    proof_body_capacity: u32,
    input: &GenerationInputV1,
) -> String {
    let mut output = String::from(
        "// @generated by `ts13_demo_artifact`; do not edit.\n\
         // This path is the only in-tree circuit-identity recursion exclusion.\n\n",
    );
    render_digest_array(&mut output, "TS13_DEMO_CIRCUIT_HASH", circuit_hash);
    output.push('\n');
    render_digest_array(
        &mut output,
        "TS13_DEMO_SHAPE_MANIFEST_SHA256",
        shape_manifest_sha256,
    );
    output.push('\n');
    render_digest_array(
        &mut output,
        "TS13_DEMO_SOUNDNESS_SOURCE_TREE_SHA256",
        source_manifest_sha256,
    );
    writeln!(
        output,
        "\npub const TS13_DEMO_PROOF_BODY_CAPACITY: u32 = {proof_body_capacity};"
    )
    .expect("writing to String cannot fail");
    let query_count = input.proof_system.fri_query_count as usize;
    writeln!(
        output,
        "pub const TS13_DEMO_QUERY_COUNT: usize = {query_count};"
    )
    .expect("writing to String cannot fail");

    render_usize_array(
        &mut output,
        "TS13_DEMO_TREE_COLUMN_COUNTS",
        5,
        input
            .proof_system
            .merkle_trees
            .iter()
            .map(|tree| u64::from(tree.maximum_opened_columns)),
    );
    render_usize_array(
        &mut output,
        "TS13_DEMO_TREE_MERKLE_HASH_CAPS",
        5,
        input
            .proof_system
            .merkle_trees
            .iter()
            .map(|tree| u64::from(input.proof_system.fri_query_count) * u64::from(tree.depth)),
    );

    output.push_str(
        "pub const TS13_DEMO_SAMPLED_VALUE_LENGTH_HISTOGRAMS: \
         [&[(usize, usize)]; 5] = [\n",
    );
    for tree in &input.proof_system.merkle_trees {
        if tree.sampled_value_length_histogram.len() <= 2 {
            output.push_str("    &[");
            for (index, entry) in tree.sampled_value_length_histogram.iter().enumerate() {
                if index != 0 {
                    output.push_str(", ");
                }
                write!(output, "({}, {})", entry.value, entry.count)
                    .expect("writing to String cannot fail");
            }
            output.push_str("],\n");
        } else {
            output.push_str("    &[\n");
            for entry in &tree.sampled_value_length_histogram {
                writeln!(output, "        ({}, {}),", entry.value, entry.count)
                    .expect("writing to String cannot fail");
            }
            output.push_str("    ],\n");
        }
    }
    output.push_str("];\n");

    let first_fri_layer = &input.proof_system.fri_layers[0];
    writeln!(
        output,
        "pub const TS13_DEMO_FRI_FIRST_WITNESS_CAP: usize = {};",
        first_fri_layer.maximum_opened_values
    )
    .expect("writing to String cannot fail");
    writeln!(
        output,
        "pub const TS13_DEMO_FRI_FIRST_HASH_CAP: usize = {};",
        u64::from(input.proof_system.fri_query_count) * u64::from(first_fri_layer.merkle_depth)
    )
    .expect("writing to String cannot fail");
    render_usize_array(
        &mut output,
        "TS13_DEMO_FRI_INNER_WITNESS_CAPS",
        input.proof_system.fri_layers.len() - 1,
        input.proof_system.fri_layers[1..]
            .iter()
            .map(|layer| u64::from(layer.maximum_opened_values)),
    );
    render_usize_array(
        &mut output,
        "TS13_DEMO_FRI_INNER_HASH_CAPS",
        input.proof_system.fri_layers.len() - 1,
        input.proof_system.fri_layers[1..].iter().map(|layer| {
            u64::from(input.proof_system.fri_query_count) * u64::from(layer.merkle_depth)
        }),
    );
    writeln!(
        output,
        "pub const TS13_DEMO_FRI_LAST_LAYER_COEFFICIENT_COUNT: usize = {};",
        1_usize << input.proof_system.fri_log_last_layer_degree_bound
    )
    .expect("writing to String cannot fail");
    writeln!(
        output,
        "pub const TS13_DEMO_POST_INTERACTION_PAYLOAD_COUNT: usize = {};",
        input
            .modules
            .iter()
            .map(|module| module.air_instances.len())
            .sum::<usize>()
    )
    .expect("writing to String cannot fail");
    output
}

fn output_paths(workspace: &Path) -> [(PathBuf, &'static str); 3] {
    [
        (workspace.join(SHAPE_MANIFEST_PATH), SHAPE_MANIFEST_PATH),
        (workspace.join(ARTIFACT_PATH), ARTIFACT_PATH),
        (workspace.join(HASH_EMBED_PATH), HASH_EMBED_PATH),
    ]
}

fn write_atomic(path: &Path, bytes: &[u8]) -> Result<(), ArtifactError> {
    let parent = path.parent().ok_or_else(|| {
        ArtifactError::InvalidInput(format!("output path has no parent: {}", path.display()))
    })?;
    fs::create_dir_all(parent).map_err(|source| io_error("create directory", parent, source))?;
    let temporary = parent.join(format!(
        ".{}.{}.tmp",
        path.file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("ts13-artifact"),
        std::process::id()
    ));
    fs::write(&temporary, bytes).map_err(|source| io_error("write", &temporary, source))?;
    fs::rename(&temporary, path).map_err(|source| io_error("replace", path, source))
}

fn apply_outputs(
    workspace: &Path,
    outputs: &GeneratedOutputs,
    mode: GenerationMode,
) -> Result<(), ArtifactError> {
    let bytes = [
        outputs.shape_manifest.as_slice(),
        outputs.artifact.as_slice(),
        outputs.hash_embedding.as_slice(),
    ];
    let paths = output_paths(workspace);
    match mode {
        GenerationMode::Write => {
            for ((path, _), bytes) in paths.iter().zip(bytes) {
                write_atomic(path, bytes)?;
            }
            Ok(())
        }
        GenerationMode::Check => {
            let mut drift = Vec::new();
            for ((path, relative), expected) in paths.iter().zip(bytes) {
                match fs::read(path) {
                    Ok(actual) if actual == expected => {}
                    _ => drift.push(PathBuf::from(relative)),
                }
            }
            if drift.is_empty() {
                Ok(())
            } else {
                Err(ArtifactError::Drift(drift))
            }
        }
    }
}

fn validate_generation_input_digest(input_bytes: &[u8]) -> Result<(), ArtifactError> {
    let input_digest = Digest32::of(input_bytes);
    if input_digest.to_string() != CANONICAL_GENERATION_INPUT_SHA256 {
        return Err(ArtifactError::InvalidInput(format!(
            "generation input SHA-256 {input_digest} differs from the audited source pin \
             {CANONICAL_GENERATION_INPUT_SHA256}"
        )));
    }
    Ok(())
}

pub fn generate_from_json(
    workspace: &Path,
    input_path: &Path,
    mode: GenerationMode,
) -> Result<GenerationResult, ArtifactError> {
    let workspace =
        fs::canonicalize(workspace).map_err(|source| io_error("resolve", workspace, source))?;
    let input_path = if input_path.is_absolute() {
        input_path.to_owned()
    } else {
        workspace.join(input_path)
    };
    let input_bytes = read(&input_path)?;
    validate_generation_input_digest(&input_bytes)?;
    let input = serde_json::from_slice::<GenerationInputV1>(&input_bytes).map_err(|source| {
        ArtifactError::Json {
            path: input_path,
            source,
        }
    })?;
    let outputs = build_outputs(&input, generation_environment(&workspace)?)?;
    apply_outputs(&workspace, &outputs, mode)?;
    Ok(GenerationResult {
        circuit_hash: outputs.circuit_hash,
        proof_body_capacity: outputs.proof_body_capacity,
    })
}

fn set_named_value(values: &mut [NamedU64V1], name: &str, value: u64) -> Result<(), ArtifactError> {
    let entry = values
        .iter_mut()
        .find(|entry| entry.name == name)
        .ok_or_else(|| ArtifactError::InvalidInput(format!("missing value {name:?}")))?;
    entry.value = value;
    Ok(())
}

fn set_implementation_unsigned(
    input: &mut GenerationInputV1,
    name: &str,
    value: u64,
) -> Result<(), ArtifactError> {
    let constant = input
        .implementation_constants
        .iter_mut()
        .find(|constant| constant.name == name)
        .ok_or_else(|| ArtifactError::InvalidInput(format!("missing constant {name:?}")))?;
    constant.value = ConstantValueV1::Unsigned(value);
    Ok(())
}

fn set_implementation_text(
    input: &mut GenerationInputV1,
    name: &str,
    value: &str,
) -> Result<(), ArtifactError> {
    let constant = input
        .implementation_constants
        .iter_mut()
        .find(|constant| constant.name == name)
        .ok_or_else(|| ArtifactError::InvalidInput(format!("missing constant {name:?}")))?;
    constant.value = ConstantValueV1::Text(value.to_owned());
    Ok(())
}

fn required_shape_count(value: Option<usize>, name: &str) -> Result<u64, ArtifactError> {
    value
        .map(|value| value as u64)
        .ok_or_else(|| ArtifactError::InvalidInput(format!("live proof omitted {name}")))
}

fn canonical_hash_stream_shapes(
) -> Result<BTreeMap<String, stwo_keccak::sponge::Shape>, ArtifactError> {
    use stwo_mldsa::profile::ML_DSA_65;

    let mut names = ["issuer_mu_job", "issuer_ct_job", "issuer_sib_job"]
        .into_iter()
        .map(str::to_owned)
        .collect::<Vec<_>>();
    names.extend((0..ML_DSA_65.matrix_polys()).map(|ordinal| format!("expand_a_{ordinal:02}_job")));
    names.extend(
        [
            "device_tr_job",
            "device_mu_job",
            "device_ct_job",
            "device_sib_job",
            "revocation_mu_job",
            "revocation_ct_job",
            "revocation_sib_job",
        ]
        .into_iter()
        .map(str::to_owned),
    );
    let live_shapes = crate::mdoc::ts13_demo_mldsa_keccak_job_shapes(
        crate::mdoc::TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY,
    );
    if names.len() != live_shapes.len() || names.len() != CANONICAL_HASH_STREAM_COUNT {
        return Err(ArtifactError::InvalidInput(format!(
            "canonical circuit has {} named jobs and {} live jobs instead of \
             {CANONICAL_HASH_STREAM_COUNT}",
            names.len(),
            live_shapes.len()
        )));
    }
    let mut shapes = BTreeMap::new();
    for (name, shape) in names.into_iter().zip(live_shapes) {
        if shapes.insert(name, shape).is_some() {
            return Err(ArtifactError::InvalidInput(
                "canonical hash jobs reuse a name".to_owned(),
            ));
        }
    }
    Ok(shapes)
}

fn canonical_stream_ids(
    hash_shapes: &BTreeMap<String, stwo_keccak::sponge::Shape>,
) -> Result<Vec<NamedU64V1>, ArtifactError> {
    let mut stream_ids = BTreeMap::new();
    let mut insert = |name: String, value: u64| {
        if stream_ids.insert(name, value).is_some() {
            return Err(ArtifactError::InvalidInput(
                "canonical stream ID names are not unique".to_owned(),
            ));
        }
        Ok(())
    };
    for (job_name, shape) in hash_shapes {
        let prefix = job_name.strip_suffix("_job").ok_or_else(|| {
            ArtifactError::InvalidInput(format!(
                "canonical hash job {job_name:?} has no job suffix"
            ))
        })?;
        insert(
            format!("{prefix}_absorb"),
            u64::from(shape.absorb_stream_id),
        )?;
        insert(
            format!("{prefix}_squeeze"),
            u64::from(shape.squeeze_stream_id),
        )?;
    }
    for (name, value) in [
        (
            "issuer_w1_source",
            crate::mdoc::MDOC_ISSUER_MLDSA_STREAM_BASE,
        ),
        (
            "device_w1_source",
            crate::mdoc::MDOC_DEVICE_MLDSA_STREAM_BASE,
        ),
        (
            "revocation_w1_source",
            crate::mdoc::MDOC_REVOCATION_MLDSA_STREAM_BASE,
        ),
    ] {
        insert(name.to_owned(), u64::from(value))?;
    }
    if stream_ids.len() != CANONICAL_STREAM_ID_COUNT {
        return Err(ArtifactError::InvalidInput(format!(
            "canonical circuit has {} named stream IDs instead of {CANONICAL_STREAM_ID_COUNT}",
            stream_ids.len()
        )));
    }
    Ok(stream_ids
        .into_iter()
        .map(|(name, value)| NamedU64V1 { name, value })
        .collect())
}

fn hash_stream_geometry(
    shape: stwo_keccak::sponge::Shape,
) -> Result<(&'static str, u32, u32), ArtifactError> {
    use stwo_keccak::sponge::XofMode;

    let hash_function = match shape.xof_mode {
        XofMode::Shake256 => "SHAKE-256",
        XofMode::Shake128 => "SHAKE-128",
    };
    let input_capacity_bytes = u32::try_from(shape.geometry_message_len())
        .map_err(|_| ArtifactError::InvalidInput("hash input capacity exceeds u32".to_owned()))?;
    let output_bytes = u32::try_from(shape.output_len())
        .map_err(|_| ArtifactError::InvalidInput("hash output length exceeds u32".to_owned()))?;
    Ok((hash_function, input_capacity_bytes, output_bytes))
}

fn canonical_relation_multiplicities() -> Result<Vec<(&'static str, usize, String)>, ArtifactError>
{
    use stwo_mldsa::{constants::N, profile::ML_DSA_65};

    let mso_padded_len =
        crate::mdoc::checked_sha256_padded_len(crate::mdoc::TS13_DEMO_MSO_PAYLOAD_BYTES)
            .ok_or_else(|| {
                ArtifactError::InvalidInput("MSO SHA-256 padded length exceeds usize".to_owned())
            })?;
    Ok(vec![
        (
            "r37_private_mso_field_bytes",
            0,
            format!(
                "-gate_input at four bytes per input-word row for all {mso_padded_len} padded \
                 stream bytes"
            ),
        ),
        (
            "r52_expand_a_ntt_cell",
            0,
            format!(
                "+accept ({}*{N} stage-zero coefficients)",
                ML_DSA_65.matrix_polys()
            ),
        ),
        (
            "r53_private_t1_cell",
            0,
            format!("-t1_row ({}*{N} coefficients)", ML_DSA_65.k()),
        ),
        (
            "r53_private_t1_cell",
            1,
            format!("+active ({}*{N} coefficients)", ML_DSA_65.k()),
        ),
    ])
}

fn set_relation_use_multiplicity(
    input: &mut GenerationInputV1,
    relation_name: &str,
    use_ordinal: usize,
    multiplicity: String,
) -> Result<(), ArtifactError> {
    let relation = input
        .relations
        .iter_mut()
        .find(|relation| relation.name == relation_name)
        .ok_or_else(|| {
            ArtifactError::InvalidInput(format!("missing relation {relation_name:?}"))
        })?;
    let relation_use = relation.uses.get_mut(use_ordinal).ok_or_else(|| {
        ArtifactError::InvalidInput(format!(
            "relation {relation_name:?} has no use {use_ordinal}"
        ))
    })?;
    relation_use.multiplicity = multiplicity;
    Ok(())
}

fn refresh_canonical_profile_semantics(input: &mut GenerationInputV1) -> Result<(), ArtifactError> {
    input.credential_shape.issuer_cose_sig_structure_bytes =
        crate::mdoc::TS13_DEMO_ISSUER_MESSAGE_BYTES as u32;
    input.credential_shape.mso_payload_bytes = crate::mdoc::TS13_DEMO_MSO_PAYLOAD_BYTES as u32;
    input.credential_shape.padded_issuer_signed_item_bytes =
        u32::from(crate::mdoc::TS13_DEMO_ITEM_PADDED_BYTES);
    input.request_context_corpus.device_sig_structure_capacity =
        crate::mdoc::TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY as u32;

    let hash_shapes = canonical_hash_stream_shapes()?;
    input.stream_ids = canonical_stream_ids(&hash_shapes)?;
    input.hash_streams = hash_shapes
        .iter()
        .map(|(name, shape)| {
            let (hash_function, input_capacity_bytes, output_bytes) = hash_stream_geometry(*shape)?;
            Ok(HashStreamV1 {
                name: name.clone(),
                stream_id: u64::from(shape.absorb_stream_id),
                hash_function: hash_function.to_owned(),
                domain_separator: HexBytes(vec![0x1f]),
                job_count: 1,
                input_capacity_bytes,
                output_bytes,
            })
        })
        .collect::<Result<Vec<_>, ArtifactError>>()?;
    if input.stream_ids.len() != CANONICAL_STREAM_ID_COUNT
        || input.hash_streams.len() != CANONICAL_HASH_STREAM_COUNT
    {
        return Err(ArtifactError::InvalidInput(format!(
            "canonical stream normalization did not produce {CANONICAL_STREAM_ID_COUNT} IDs and \
             {CANONICAL_HASH_STREAM_COUNT} jobs"
        )));
    }

    input
        .relations
        .iter_mut()
        .find(|relation| relation.name == RESERVED_TRANSCRIPT_RELATION_NAMES[0])
        .ok_or_else(|| {
            ArtifactError::InvalidInput(format!(
                "missing reserved transcript relation {:?}",
                RESERVED_TRANSCRIPT_RELATION_NAMES[0]
            ))
        })?
        .uses
        .clear();

    for (relation_name, use_ordinal, multiplicity) in canonical_relation_multiplicities()? {
        set_relation_use_multiplicity(input, relation_name, use_ordinal, multiplicity)?;
    }

    for (name, encoding, fixed_length) in [
        (
            "p02_shared_keccak_job_list",
            KECCAK_PUBLIC_MIX_ENCODING,
            Some(KECCAK_PUBLIC_MIX_FIXED_LENGTH),
        ),
        (
            "p05_issuer_private_message_mldsa",
            "mix_u64(profile_tag,namespace_len,namespace_bytes,rho[32],t1[6][256],tr[64],private_message_len,stream_base); private message bytes omitted",
            Some(13_176),
        ),
        (
            "p14_private_expand_a",
            "mix_u64(domain_tag,profile_tag,namespace_len,namespace_bytes,stream_base,max_squeeze_blocks,matrix_polys)",
            Some(248),
        ),
        (
            "p16_private_device_mldsa",
            "mix_u64(profile_tag,namespace_len,namespace_bytes,HOSTED_PRIVATE_KEY_MODE_TAG,message_len,public_message_bytes,stream_base)",
            None,
        ),
        (
            "p18_private_revocation_mldsa",
            "mix_u64(profile_tag,namespace_len,namespace_bytes,rho[32],t1[6][256],tr[64],private_message_len,stream_base); private message bytes omitted",
            Some(13_248),
        ),
    ] {
        let entry = input
            .transcript
            .public_mix_order
            .iter_mut()
            .find(|entry| entry.name == name)
            .ok_or_else(|| ArtifactError::InvalidInput(format!("missing public mix {name:?}")))?;
        entry.encoding = encoding.to_owned();
        entry.fixed_length = fixed_length;
    }

    set_implementation_unsigned(
        input,
        "impl.expand_a_job_count",
        CANONICAL_EXPAND_A_JOB_COUNT as u64,
    )?;
    set_implementation_unsigned(
        input,
        "impl.hash_job_count",
        CANONICAL_HASH_STREAM_COUNT as u64,
    )?;
    set_implementation_unsigned(
        input,
        "impl.issuer_cose_sig_structure_bytes",
        crate::mdoc::TS13_DEMO_ISSUER_MESSAGE_BYTES as u64,
    )?;
    set_implementation_unsigned(
        input,
        "impl.mso_payload_bytes",
        crate::mdoc::TS13_DEMO_MSO_PAYLOAD_BYTES as u64,
    )?;
    set_implementation_text(input, "impl.keccak.job_order", KECCAK_JOB_ORDER)?;
    set_implementation_text(
        input,
        "impl.hash_stream_record_stream_id_semantics",
        HASH_STREAM_ID_SEMANTICS,
    )?;
    set_implementation_unsigned(
        input,
        "impl.challenge.raw_mldsa_secure_field_draws",
        CANONICAL_RAW_MLDSA_CHALLENGE_COUNT as u64,
    )?;
    set_implementation_unsigned(
        input,
        "impl.challenge.relation_instances",
        CANONICAL_RELATION_COUNT as u64,
    )?;
    set_implementation_unsigned(
        input,
        "impl.challenge.relation_secure_field_draws",
        (CANONICAL_RELATION_COUNT * 2) as u64,
    )?;
    set_implementation_unsigned(
        input,
        "impl.challenge.total_secure_field_draws",
        (CANONICAL_RELATION_COUNT * 2 + CANONICAL_RAW_MLDSA_CHALLENGE_COUNT) as u64,
    )?;
    set_implementation_text(input, "impl.transcript.claim_mix_order", CLAIM_MIX_ORDER)?;
    set_implementation_text(input, "impl.transcript.phase_order", TRANSCRIPT_PHASE_ORDER)?;
    Ok(())
}

fn set_claim_vector(
    input: &mut GenerationInputV1,
    claim_name: &str,
    vector_name: &str,
    value: u64,
) -> Result<(), ArtifactError> {
    let claim = input
        .serialized_claims
        .iter_mut()
        .find(|claim| claim.name == claim_name)
        .ok_or_else(|| ArtifactError::InvalidInput(format!("missing claim {claim_name:?}")))?;
    set_named_value(&mut claim.fixed_vector_lengths, vector_name, value)
}

fn refresh_air_geometry(
    input: &mut GenerationInputV1,
    geometry: &crate::mdoc::MdocTs13DemoCircuitGeometry,
) -> Result<(), ArtifactError> {
    let declared_air_count = input
        .modules
        .iter()
        .map(|module| module.air_instances.len())
        .sum::<usize>();
    if declared_air_count != geometry.air_instances.len() {
        return Err(ArtifactError::InvalidInput(format!(
            "cannot refresh a different AIR skeleton: input {declared_air_count}, live {}",
            geometry.air_instances.len()
        )));
    }
    let mut air_ordinal = 0;
    for module in &mut input.modules {
        for air in &mut module.air_instances {
            let live = &geometry.air_instances[air_ordinal];
            if air.components.len() != live.components.len() {
                return Err(ArtifactError::InvalidInput(format!(
                    "cannot refresh a different component skeleton at AIR {air_ordinal}"
                )));
            }
            air.columns.preprocessed_m31_log_sizes = live.preprocessed_log_sizes.clone();
            air.columns.trace_m31_log_sizes = live.trace_log_sizes.clone();
            air.columns.interaction_m31_log_sizes = live.interaction_log_sizes.clone();
            air.columns.post_interaction_m31_log_sizes = live.post_interaction_log_sizes.clone();
            air.claimed_sum_count = u32::try_from(live.claimed_sum_count).map_err(|_| {
                ArtifactError::InvalidInput("AIR claimed-sum count exceeds u32".to_owned())
            })?;
            air.max_log_size = live.max_log_size;
            air.max_constraint_log_degree_bound = live.max_constraint_log_degree_bound;
            for (component, live) in air.components.iter_mut().zip(&live.components) {
                component.trace_rows = live.trace_rows;
                component.constraint_count =
                    u32::try_from(live.constraint_count).map_err(|_| {
                        ArtifactError::InvalidInput(
                            "component constraint count exceeds u32".to_owned(),
                        )
                    })?;
                component.max_constraint_log_degree_bound = live.max_constraint_log_degree_bound;
                component.trace_mask_column_counts = live
                    .trace_log_degree_bounds
                    .iter()
                    .map(|tree| {
                        u32::try_from(tree.len()).map_err(|_| {
                            ArtifactError::InvalidInput(
                                "component mask column count exceeds u32".to_owned(),
                            )
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
            }
            air_ordinal += 1;
        }
    }
    input.tree_zero.preprocessed_column_order = geometry.committed_preprocessed_ids.clone();
    input.tree_zero.committed_column_log_sizes = geometry.committed_preprocessed_log_sizes.clone();
    Ok(())
}

fn refresh_claim_geometry(
    input: &mut GenerationInputV1,
    proof: &crate::mdoc::MdocTs13DemoProofShape,
) -> Result<(u64, u64, u64), ArtifactError> {
    if input.serialized_claims.len() != proof.serialized_non_stark_field_lengths.len() {
        return Err(ArtifactError::InvalidInput(
            "cannot refresh a different serialized-claim skeleton".to_owned(),
        ));
    }
    for (claim, &length) in input
        .serialized_claims
        .iter_mut()
        .zip(&proof.serialized_non_stark_field_lengths)
    {
        claim.fixed_length = u32::try_from(length).map_err(|_| {
            ArtifactError::InvalidInput("serialized claim length exceeds u32".to_owned())
        })?;
    }
    set_claim_vector(
        input,
        "sha_tables_interaction_claim",
        "pairs",
        proof.sha_table_pair_claim_count as u64,
    )?;
    for (claim, group_evals, claimed_sums, group_evals_constant, claimed_sums_constant) in [
        (
            "mldsa",
            proof.issuer_mldsa_group_eval_count,
            proof.issuer_mldsa_claimed_sum_count,
            "impl.mldsa.issuer_group_eval_count",
            "impl.mldsa.issuer_claimed_sum_count",
        ),
        (
            "device_mldsa",
            proof.device_mldsa_group_eval_count,
            proof.device_mldsa_claimed_sum_count,
            "impl.mldsa.device_group_eval_count",
            "impl.mldsa.device_claimed_sum_count",
        ),
        (
            "revocation_mldsa",
            proof.revocation_mldsa_group_eval_count,
            proof.revocation_mldsa_claimed_sum_count,
            "impl.mldsa.revocation_group_eval_count",
            "impl.mldsa.revocation_claimed_sum_count",
        ),
    ] {
        let group_evals = required_shape_count(group_evals, "ML-DSA group-evaluation count")?;
        let claimed_sums = required_shape_count(claimed_sums, "ML-DSA claimed-sum count")?;
        set_claim_vector(input, claim, "group_evals", group_evals)?;
        set_claim_vector(input, claim, "claimed_sums", claimed_sums)?;
        set_implementation_unsigned(input, group_evals_constant, group_evals)?;
        set_implementation_unsigned(input, claimed_sums_constant, claimed_sums)?;
    }
    let keccak_claimed_sums = required_shape_count(
        proof.keccak_service_claimed_sum_count,
        "Keccak claimed-sum count",
    )?;
    set_claim_vector(
        input,
        "keccak_service_claimed_sums",
        "claimed_sums",
        keccak_claimed_sums,
    )?;
    set_implementation_unsigned(
        input,
        "impl.keccak_service_claimed_sum_count",
        keccak_claimed_sums,
    )?;
    set_claim_vector(
        input,
        "attribute_sha_interaction_claim",
        "range",
        proof.attribute_sha_range_claim_count as u64,
    )?;
    set_claim_vector(
        input,
        "mso_sha_interaction_claim",
        "range",
        required_shape_count(proof.mso_sha_range_claim_count, "MSO SHA range count")?,
    )?;

    let payload_count = proof.post_interaction_payload_bytes.len() as u64;
    let nonempty_payloads = proof
        .post_interaction_payload_bytes
        .iter()
        .filter(|&&bytes| bytes != 0)
        .count() as u64;
    let payload_bytes = proof
        .post_interaction_payload_bytes
        .iter()
        .try_fold(0_u64, |sum, &bytes| sum.checked_add(bytes as u64))
        .ok_or_else(|| ArtifactError::InvalidInput("post payload bytes exceed u64".to_owned()))?;
    for (name, value) in [
        ("nonempty_payloads", nonempty_payloads),
        ("payload_bytes", payload_bytes),
        ("payload_count", payload_count),
    ] {
        set_claim_vector(input, "post_interaction_payloads", name, value)?;
    }
    let serialized_claim_bytes = proof
        .serialized_non_stark_field_lengths
        .iter()
        .try_fold(0_u64, |sum, &bytes| sum.checked_add(bytes as u64))
        .ok_or_else(|| ArtifactError::InvalidInput("serialized claims exceed u64".to_owned()))?;
    let post_payload_wire_bytes = 8 + payload_count * 8 + payload_bytes;
    if serialized_claim_bytes
        != proof.outer_claims_and_framing_bytes as u64 + post_payload_wire_bytes
    {
        return Err(ArtifactError::InvalidInput(
            "live serialized claim totals are internally inconsistent".to_owned(),
        ));
    }
    Ok((
        payload_bytes,
        post_payload_wire_bytes,
        serialized_claim_bytes,
    ))
}

fn refresh_pcs_geometry(
    input: &mut GenerationInputV1,
    proof: &crate::mdoc::MdocTs13DemoProofShape,
) -> Result<(), ArtifactError> {
    input.proof_system.fri_log_last_layer_degree_bound = proof.fri_log_last_layer_degree_bound;
    input.proof_system.fri_log_blowup_factor = proof.fri_log_blowup_factor;
    input.proof_system.fri_query_count = u32::try_from(proof.fri_query_count)
        .map_err(|_| ArtifactError::InvalidInput("FRI query count exceeds u32".to_owned()))?;
    input.proof_system.fri_fold_step = proof.fri_fold_step;
    input.proof_system.pow_bits = proof.pow_bits;
    input.proof_system.lifting_log_size = proof.lifting_log_size;
    if input.proof_system.merkle_trees.len() != CANONICAL_MERKLE_TREE_ORDER.len()
        || proof.sampled_values.len() != CANONICAL_MERKLE_TREE_ORDER.len()
    {
        return Err(ArtifactError::InvalidInput(
            "live proof must contain the five canonical commitment trees".to_owned(),
        ));
    }
    let tree_depths = expected_tree_depths(input)?;
    for ((tree, sampled_columns), depth) in input
        .proof_system
        .merkle_trees
        .iter_mut()
        .zip(&proof.sampled_values)
        .zip(tree_depths)
    {
        tree.depth = depth;
        tree.maximum_opened_columns = u32::try_from(sampled_columns.len()).map_err(|_| {
            ArtifactError::InvalidInput("sampled column count exceeds u32".to_owned())
        })?;
        let mut histogram = BTreeMap::<u32, u32>::new();
        for &length in sampled_columns {
            let length = u32::try_from(length).map_err(|_| {
                ArtifactError::InvalidInput("sampled value length exceeds u32".to_owned())
            })?;
            *histogram.entry(length).or_default() += 1;
        }
        tree.sampled_value_length_histogram = histogram
            .into_iter()
            .map(|(value, count)| ValueCountV1 { value, count })
            .collect();
    }
    let fri_input_log_size = input
        .proof_system
        .lifting_log_size
        .unwrap_or(tree_depths[4]);
    input.proof_system.fri_layers = expected_fri_layers(&input.proof_system, fri_input_log_size)?;
    if proof.fri_inner_layers.len() + 1 != input.proof_system.fri_layers.len() {
        return Err(ArtifactError::InvalidInput(format!(
            "live FRI layer count differs: proof {}, derived {}",
            proof.fri_inner_layers.len() + 1,
            input.proof_system.fri_layers.len()
        )));
    }
    Ok(())
}

fn refresh_live_profile_input(
    input: &mut GenerationInputV1,
    geometry: &crate::mdoc::MdocTs13DemoCircuitGeometry,
    proof: &crate::mdoc::MdocTs13DemoProofShape,
) -> Result<(), ArtifactError> {
    refresh_air_geometry(input, geometry)?;
    input.tree_zero.root = Digest32(proof.tree_zero_root.ok_or_else(|| {
        ArtifactError::InvalidInput("live proof has no tree-zero commitment".to_owned())
    })?);
    let (payload_bytes, post_payload_wire_bytes, serialized_claim_bytes) =
        refresh_claim_geometry(input, proof)?;
    refresh_pcs_geometry(input, proof)?;
    let component_count = geometry
        .air_instances
        .iter()
        .map(|air| air.components.len())
        .sum::<usize>() as u64;
    let claimed_sum_count = geometry.air_instances.iter().try_fold(0_u64, |sum, air| {
        sum.checked_add(air.claimed_sum_count as u64)
            .ok_or_else(|| {
                ArtifactError::InvalidInput("global claimed-sum count exceeds u64".to_owned())
            })
    })?;
    for (name, value) in [
        (
            "impl.air_instance_count",
            geometry.air_instances.len() as u64,
        ),
        ("impl.component_count", component_count),
        (
            "impl.outer_claim_bytes_excluding_stark_and_post_payloads",
            proof.outer_claims_and_framing_bytes as u64,
        ),
        (
            "impl.post_interaction_nonempty_payload_bytes",
            payload_bytes,
        ),
        (
            "impl.post_interaction_payload_vector_wire_bytes",
            post_payload_wire_bytes,
        ),
        (
            "impl.serialized_claim_bytes_excluding_stark",
            serialized_claim_bytes,
        ),
        (
            "impl.transcript.global_claimed_sum_count",
            claimed_sum_count,
        ),
    ] {
        set_implementation_unsigned(input, name, value)?;
    }
    Ok(())
}

/// Render canonical generation input from one verified composed proof.
#[doc(hidden)]
pub fn render_refreshed_live_ts13_demo_input(
    input_json: &[u8],
    geometry: &crate::mdoc::MdocTs13DemoCircuitGeometry,
    proof: &crate::mdoc::MdocTs13DemoProofShape,
) -> Result<Vec<u8>, ArtifactError> {
    let mut input = serde_json::from_slice::<GenerationInputV1>(input_json).map_err(|error| {
        ArtifactError::InvalidInput(format!("live artifact input is not valid JSON: {error}"))
    })?;
    refresh_canonical_profile_semantics(&mut input)?;
    refresh_live_profile_input(&mut input, geometry, proof)?;
    input.validate()?;
    validate_live_profile_input(&input, geometry, proof)?;
    let mut rendered = serde_json::to_vec_pretty(&input).map_err(|error| {
        ArtifactError::InvalidInput(format!("cannot render generation input: {error}"))
    })?;
    rendered.push(b'\n');
    Ok(rendered)
}

/// Atomically replace the checked-in generation input with live verified geometry.
#[doc(hidden)]
pub fn refresh_live_ts13_demo_generation_input(
    workspace: &Path,
    geometry: &crate::mdoc::MdocTs13DemoCircuitGeometry,
    proof: &crate::mdoc::MdocTs13DemoProofShape,
) -> Result<(), ArtifactError> {
    let path = workspace.join(GENERATION_INPUT_PATH);
    let current = read(&path)?;
    let rendered = render_refreshed_live_ts13_demo_input(&current, geometry, proof)?;
    write_atomic(&path, &rendered)
}

/// Compare artifact input with geometry from a composed TS13 demo proof.
///
/// This CI check compares dimensions. It does not compare witness values.
#[doc(hidden)]
pub fn validate_live_ts13_demo_profile(
    input_json: &[u8],
    geometry: &crate::mdoc::MdocTs13DemoCircuitGeometry,
    proof: &crate::mdoc::MdocTs13DemoProofShape,
) -> Result<(), ArtifactError> {
    let input = serde_json::from_slice::<GenerationInputV1>(input_json).map_err(|error| {
        ArtifactError::InvalidInput(format!("live artifact input is not valid JSON: {error}"))
    })?;
    input.validate()?;
    let sampled_secure_fields = proof
        .sampled_values
        .iter()
        .flatten()
        .copied()
        .sum::<usize>();
    let proof_bound_terms = ts13_demo_proof_bound_terms(&input)?;
    let (proof_worst_case, _) = deterministic_proof_bound(&proof_bound_terms)?;
    let declared_sampled_secure_fields = input
        .proof_system
        .merkle_trees
        .iter()
        .flat_map(|tree| &tree.sampled_value_length_histogram)
        .map(|entry| entry.value as usize * entry.count as usize)
        .sum::<usize>();
    let declared_outer_claim_bytes = input
        .serialized_claims
        .iter()
        .filter(|claim| claim.name != "post_interaction_payloads")
        .map(|claim| claim.fixed_length as usize)
        .sum::<usize>();
    if sampled_secure_fields != declared_sampled_secure_fields
        || proof.outer_claims_and_framing_bytes != declared_outer_claim_bytes
        || proof.proof_bytes > proof_worst_case as usize
    {
        return Err(ArtifactError::InvalidInput(
            "live proof differs from the canonical serialization aggregates".to_owned(),
        ));
    }
    validate_live_profile_input(&input, geometry, proof)
}

fn validate_live_profile_input(
    input: &GenerationInputV1,
    geometry: &crate::mdoc::MdocTs13DemoCircuitGeometry,
    proof: &crate::mdoc::MdocTs13DemoProofShape,
) -> Result<(), ArtifactError> {
    fn value_histogram(values: &[usize]) -> BTreeMap<u32, u32> {
        let mut counts = BTreeMap::new();
        for &value in values {
            *counts.entry(value as u32).or_insert(0) += 1;
        }
        counts
    }

    fn declared_value_histogram(groups: &[ValueCountV1]) -> BTreeMap<u32, u32> {
        groups
            .iter()
            .map(|group| (group.value, group.count))
            .collect()
    }

    let declared_airs = input
        .modules
        .iter()
        .flat_map(|module| {
            module
                .air_instances
                .iter()
                .enumerate()
                .map(move |(air_instance_ordinal, air)| {
                    (module.name.as_str(), air_instance_ordinal, air)
                })
        })
        .collect::<Vec<_>>();
    let pcs_shape_matches = proof.fri_log_last_layer_degree_bound
        == input.proof_system.fri_log_last_layer_degree_bound
        && proof.fri_log_blowup_factor == input.proof_system.fri_log_blowup_factor
        && proof.fri_query_count == input.proof_system.fri_query_count as usize
        && proof.fri_fold_step == input.proof_system.fri_fold_step
        && proof.pow_bits == input.proof_system.pow_bits
        && proof.lifting_log_size == input.proof_system.lifting_log_size;
    if !pcs_shape_matches {
        return Err(ArtifactError::InvalidInput(
            "live PCS configuration differs from the artifact input".to_owned(),
        ));
    }
    if input
        .serialized_claims
        .iter()
        .map(|claim| claim.fixed_length as usize)
        .collect::<Vec<_>>()
        != proof.serialized_non_stark_field_lengths
    {
        return Err(ArtifactError::InvalidInput(
            "live serialized field lengths differ from the artifact input".to_owned(),
        ));
    }
    if declared_airs.len() != geometry.air_instances.len() {
        return Err(ArtifactError::InvalidInput(format!(
            "live AIR count differs: artifact {}, prover {}",
            declared_airs.len(),
            geometry.air_instances.len()
        )));
    }
    for (ordinal, ((_, _, declared), live)) in declared_airs
        .iter()
        .zip(&geometry.air_instances)
        .enumerate()
    {
        let layouts_match = [
            (
                &declared.columns.preprocessed_m31_log_sizes,
                &live.preprocessed_log_sizes,
            ),
            (&declared.columns.trace_m31_log_sizes, &live.trace_log_sizes),
            (
                &declared.columns.interaction_m31_log_sizes,
                &live.interaction_log_sizes,
            ),
            (
                &declared.columns.post_interaction_m31_log_sizes,
                &live.post_interaction_log_sizes,
            ),
        ]
        .into_iter()
        .all(|(expected, actual)| expected == actual);
        if !layouts_match
            || declared.claimed_sum_count as usize != live.claimed_sum_count
            || declared.max_log_size != live.max_log_size
            || declared.max_constraint_log_degree_bound != live.max_constraint_log_degree_bound
            || declared.components.len() != live.components.len()
            || declared
                .components
                .iter()
                .zip(&live.components)
                .any(|(expected, actual)| {
                    expected.trace_rows != actual.trace_rows
                        || expected.constraint_count as usize != actual.constraint_count
                        || expected.max_constraint_log_degree_bound
                            != actual.max_constraint_log_degree_bound
                        || expected.trace_mask_column_counts
                            != actual
                                .trace_log_degree_bounds
                                .iter()
                                .map(|tree| tree.len() as u32)
                                .collect::<Vec<_>>()
                })
        {
            return Err(ArtifactError::InvalidInput(format!(
                "live AIR geometry differs at physical ordinal {ordinal}"
            )));
        }
    }

    if input.tree_zero.preprocessed_column_order != geometry.committed_preprocessed_ids
        || input.tree_zero.committed_column_log_sizes != geometry.committed_preprocessed_log_sizes
    {
        return Err(ArtifactError::InvalidInput(
            "live first-writer tree-zero order or log geometry differs".to_owned(),
        ));
    }

    let expected_tree_columns = input
        .proof_system
        .merkle_trees
        .iter()
        .map(|tree| tree.maximum_opened_columns as usize)
        .collect::<Vec<_>>();
    let sampled_tree_columns = proof
        .sampled_values
        .iter()
        .map(Vec::len)
        .collect::<Vec<_>>();
    let queried_tree_columns = proof
        .queried_values
        .iter()
        .map(Vec::len)
        .collect::<Vec<_>>();
    let query_count = input.proof_system.fri_query_count as usize;
    let sampled_value_histograms_match = proof.sampled_values.len()
        == input.proof_system.merkle_trees.len()
        && proof
            .sampled_values
            .iter()
            .zip(&input.proof_system.merkle_trees)
            .all(|(live, expected)| {
                value_histogram(live)
                    == declared_value_histogram(&expected.sampled_value_length_histogram)
            });
    let queried_value_count = proof.queried_values.iter().flatten().next().copied();
    let queried_value_shape_matches = queried_value_count.is_some_and(|count| {
        count > 0
            && count <= query_count
            && proof
                .queried_values
                .iter()
                .flatten()
                .all(|&candidate| candidate == count)
    });
    let decommitment_shape_matches = proof.decommitment_hash_counts.len()
        == input.proof_system.merkle_trees.len()
        && proof
            .decommitment_hash_counts
            .iter()
            .zip(&input.proof_system.merkle_trees)
            .all(|(&count, tree)| count <= query_count * tree.depth as usize);
    let fri_shape_matches =
        input
            .proof_system
            .fri_layers
            .split_first()
            .is_some_and(|(first, inner)| {
                proof.fri_first_layer_witness_count <= first.maximum_opened_values as usize
                    && proof.fri_first_layer_hash_count <= query_count * first.merkle_depth as usize
                    && proof.fri_inner_layers.len() == inner.len()
                    && proof
                        .fri_inner_layers
                        .iter()
                        .zip(inner)
                        .all(|(live, expected)| {
                            live.witness_count <= expected.maximum_opened_values as usize
                                && live.hash_count <= query_count * expected.merkle_depth as usize
                        })
            });
    let expected_last_layer_coefficients = 1_usize
        .checked_shl(input.proof_system.fri_log_last_layer_degree_bound)
        .ok_or_else(|| {
            ArtifactError::InvalidInput("FRI last-layer coefficient count exceeds usize".to_owned())
        })?;
    if proof.commitment_count != input.proof_system.merkle_trees.len()
        || proof.tree_zero_root != Some(input.tree_zero.root.0)
        || sampled_tree_columns != expected_tree_columns
        || queried_tree_columns != expected_tree_columns
        || !sampled_value_histograms_match
        || !queried_value_shape_matches
        || !decommitment_shape_matches
        || !fri_shape_matches
        || proof.fri_last_layer_coefficient_count != expected_last_layer_coefficients
        || proof.post_interaction_payload_bytes.len() != declared_airs.len()
        || proof
            .post_interaction_payload_bytes
            .iter()
            .zip(&declared_airs)
            .any(|(&bytes, &(module_name, air_instance_ordinal, _))| {
                if module_name == SHARED_KECCAK_SERVICE_MODULE && air_instance_ordinal == 0 {
                    bytes > air_core::gkr::TS13_DEMO_GKR_MAX_PAYLOAD_BYTES
                } else {
                    bytes != 0
                }
            })
        || proof.sha_table_pair_claim_count != 3
        || proof.attribute_sha_range_claim_count != 0
        || proof.mso_sha_range_claim_count != Some(0)
        || proof.issuer_mldsa_group_eval_count != Some(stwo_mldsa::statement::n_group_evals())
        || proof.issuer_mldsa_claimed_sum_count
            != Some(stwo_mldsa::statement::hosted_claimed_sums_len())
        || proof.device_mldsa_group_eval_count
            != Some(stwo_mldsa::statement::n_private_key_group_evals())
        || proof.device_mldsa_claimed_sum_count
            != Some(stwo_mldsa::statement::hosted_private_key_claimed_sums_len())
        || proof.revocation_mldsa_group_eval_count != Some(stwo_mldsa::statement::n_group_evals())
        || proof.revocation_mldsa_claimed_sum_count
            != Some(stwo_mldsa::statement::hosted_claimed_sums_len())
        || proof.keccak_service_claimed_sum_count
            != Some(stwo_keccak::service::service_claimed_sums_len())
        || proof.private_item_claim_count != 1
        || proof.cbor_parser_claim_count != 2
    {
        return Err(ArtifactError::InvalidInput(
            "live proof claim, tree, payload, or serialization geometry differs".to_owned(),
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

    fn temporary_directory(name: &str) -> PathBuf {
        let suffix = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "eu-id-ts13-artifact-{name}-{}-{suffix}",
            std::process::id()
        ));
        fs::create_dir(&path).expect("temporary directory is unique");
        path
    }

    fn write_fixture(path: &Path, bytes: &[u8]) {
        fs::create_dir_all(path.parent().expect("fixture path has a parent"))
            .expect("fixture parent is writable");
        fs::write(path, bytes).expect("fixture is writable");
    }

    fn source_workspace() -> PathBuf {
        let workspace = temporary_directory("source");
        write_fixture(&workspace.join("Cargo.toml"), b"[workspace]\n");
        write_fixture(
            &workspace.join(NORMATIVE_SPEC_PATH),
            include_bytes!("../../../docs/ts13-unlinkable-age18-demo-spec.md"),
        );
        for root in SOURCE_PACKAGE_ROOTS {
            write_fixture(
                &workspace.join(root).join("src/lib.rs"),
                format!("// {root}\n").as_bytes(),
            );
        }
        workspace
    }

    fn minimal_input() -> GenerationInputV1 {
        let modules = CANONICAL_MODULE_ORDER
            .iter()
            .map(|name| ModuleLayoutV1 {
                name: (*name).to_owned(),
                air_instances: (0..if *name == "private_item_cbor_parsers" {
                    2
                } else {
                    1
                })
                    .map(|air_instance_ordinal| {
                        let zero_component = matches!(
                            *name,
                            "ts13_public_context_bind" | "public_revocation_key_epoch_bind"
                        );
                        let max_log_size = if *name == "private_device_key_binder" {
                            9
                        } else if zero_component {
                            0
                        } else {
                            1
                        };
                        AirInstanceLayoutV1 {
                            columns: AirColumnLayoutV1 {
                                preprocessed_m31_log_sizes: Vec::new(),
                                trace_m31_log_sizes: (!zero_component)
                                    .then_some(max_log_size)
                                    .into_iter()
                                    .collect(),
                                interaction_m31_log_sizes: Vec::new(),
                                post_interaction_m31_log_sizes: (*name
                                    == SHARED_KECCAK_SERVICE_MODULE
                                    && air_instance_ordinal == 0)
                                    .then_some(vec![
                                        1;
                                        CANONICAL_KECCAK_POST_INTERACTION_COLUMN_COUNT
                                            as usize
                                    ])
                                    .unwrap_or_default(),
                            },
                            claimed_sum_count: if zero_component { 0 } else { 1 },
                            max_log_size,
                            max_constraint_log_degree_bound: max_log_size + 1,
                            components: (!zero_component)
                                .then_some(AirComponentLayoutV1 {
                                    name: format!("{name}_component_{air_instance_ordinal}"),
                                    trace_rows: 1_u32 << max_log_size,
                                    constraint_count: 1,
                                    max_constraint_log_degree_bound: max_log_size + 1,
                                    trace_mask_column_counts: vec![0, 1],
                                })
                                .into_iter()
                                .collect(),
                        }
                    })
                    .collect(),
            })
            .collect::<Vec<_>>();
        let first_component = modules[0].air_instances[0].components[0].name.clone();
        let corpus_sha256: [u8; 32] = decode_hex(CANONICAL_REQUEST_CONTEXT_CORPUS_SHA256)
            .expect("canonical corpus digest is hex")
            .try_into()
            .expect("canonical corpus digest is 32 bytes");
        GenerationInputV1 {
            credential_shape: CredentialShapeV1 {
                issuer_cose_sig_structure_bytes: crate::mdoc::TS13_DEMO_ISSUER_MESSAGE_BYTES as u32,
                mso_payload_bytes: crate::mdoc::TS13_DEMO_MSO_PAYLOAD_BYTES as u32,
                padded_issuer_signed_item_bytes: u32::from(
                    crate::mdoc::TS13_DEMO_ITEM_PADDED_BYTES,
                ),
                digest_identifier_integer_widths: CANONICAL_DIGEST_IDENTIFIER_INTEGER_WIDTHS
                    .to_vec(),
            },
            request_context_corpus: RequestContextCorpusV1 {
                corpus_sha256: Digest32(corpus_sha256),
                observed_max_device_cose_sig_structure_bytes:
                    CANONICAL_OBSERVED_MAX_DEVICE_COSE_SIG_STRUCTURE_BYTES,
                device_sig_structure_capacity: crate::mdoc::TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY
                    as u32,
            },
            modules,
            relations: vec![RelationLayoutV1 {
                name: "FixtureRelation".to_owned(),
                challenge_owner_module: CANONICAL_MODULE_ORDER[0].to_owned(),
                tuple: vec![RelationFieldV1 {
                    name: "value".to_owned(),
                    scalar: ColumnScalarV1::M31,
                }],
                uses: vec![RelationUseV1 {
                    module: CANONICAL_MODULE_ORDER[0].to_owned(),
                    component: first_component,
                    sign: RelationSignV1::Positive,
                    multiplicity: "1".to_owned(),
                }],
            }],
            transcript: TranscriptLayoutV1 {
                public_mix_order: vec![TranscriptEntryV1 {
                    owner_module: CANONICAL_MODULE_ORDER[3].to_owned(),
                    name: "public_context".to_owned(),
                    encoding: "bytes".to_owned(),
                    fixed_length: Some(96),
                }],
                challenge_order: vec![TranscriptEntryV1 {
                    owner_module: CANONICAL_MODULE_ORDER[0].to_owned(),
                    name: "lookup".to_owned(),
                    encoding: "secure_field".to_owned(),
                    fixed_length: Some(16),
                }],
            },
            serialized_claims: vec![SerializedClaimV1 {
                name: "fixture_claim".to_owned(),
                encoding: "bincode-fixed-int-le".to_owned(),
                fixed_length: 32,
                fixed_vector_lengths: vec![NamedU64V1 {
                    name: "values".to_owned(),
                    value: 4,
                }],
            }],
            stream_ids: vec![NamedU64V1 {
                name: "fixture".to_owned(),
                value: 1,
            }],
            hash_streams: vec![HashStreamV1 {
                name: "fixture".to_owned(),
                stream_id: 1,
                hash_function: "SHAKE-256".to_owned(),
                domain_separator: HexBytes(vec![0x01]),
                job_count: 1,
                input_capacity_bytes: 64,
                output_bytes: 64,
            }],
            range_tables: vec![RangeTableV1 {
                name: "rc8".to_owned(),
                value_kind: "unsigned".to_owned(),
                bit_width: 8,
                log_size: 8,
                active_rows: 256,
            }],
            relation_tuple_counts: vec![NamedU64V1 {
                name: "fixture".to_owned(),
                value: 1,
            }],
            implementation_constants: vec![ArtifactConstantV1 {
                name: "impl.fixture".to_owned(),
                value: ConstantValueV1::Unsigned(7),
            }],
            tree_zero: TreeZeroV1 {
                derivation: "fixture".to_owned(),
                hash: "Blake2s-256".to_owned(),
                preprocessed_column_order: vec!["fixture_0".to_owned()],
                committed_column_log_sizes: vec![1],
                root: Digest32([2; 32]),
            },
            proof_system: ProofSystemV1 {
                field: "M31".to_owned(),
                field_modulus: 2_147_483_647,
                secure_extension_field: "QM31".to_owned(),
                secure_extension_degree: 4,
                pcs: "CirclePcs".to_owned(),
                commitment_hash: "Blake2s-256".to_owned(),
                merkle_hash: "Blake2s-256".to_owned(),
                fri_log_last_layer_degree_bound: 1,
                fri_log_blowup_factor: 3,
                fri_query_count: 36,
                fri_fold_step: 2,
                pow_bits: 20,
                lifting_log_size: None,
                merkle_trees: CANONICAL_MERKLE_TREE_ORDER
                    .iter()
                    .enumerate()
                    .map(|(index, name)| {
                        let columns = [1, 18, 0, 8, 8][index];
                        MerkleTreeParametersV1 {
                            name: (*name).to_owned(),
                            depth: 4,
                            digest_bytes: 32,
                            maximum_opened_columns: columns,
                            sampled_value_length_histogram: vec![ValueCountV1 {
                                value: 1,
                                count: columns,
                            }],
                        }
                    })
                    .collect(),
                fri_layers: vec![FriLayerParametersV1 {
                    input_log_size: 4,
                    output_log_size: 3,
                    merkle_depth: 4,
                    maximum_opened_values: 36,
                }],
            },
            enabled_cargo_features: SOURCE_PACKAGE_ROOTS
                .iter()
                .map(|root| PackageFeaturesV1 {
                    package: root.trim_start_matches("crates/").to_owned(),
                    features: Vec::new(),
                })
                .collect(),
        }
    }

    fn sample_input() -> GenerationInputV1 {
        serde_json::from_slice(include_bytes!(
            "../../../artifacts/ts13-demo-v1/generation-input-v1.json"
        ))
        .expect("committed generation input is valid JSON")
    }

    fn sample_environment() -> GenerationEnvironmentV1 {
        let source_manifest = SourceTreeManifestV1 {
            schema_version: 1,
            workspace_files: vec!["Cargo.toml".to_owned(), NORMATIVE_SPEC_PATH.to_owned()],
            package_roots: SOURCE_PACKAGE_ROOTS
                .iter()
                .map(|root| (*root).to_owned())
                .collect(),
            cargo_build_directory_name: "target",
            generated_recursive_exclusions: GENERATED_RECURSION_EXCLUSIONS
                .iter()
                .map(|path| (*path).to_owned())
                .collect(),
            files: vec![
                SourceFileEntryV1 {
                    path: "Cargo.toml".to_owned(),
                    sha256: Digest32([3; 32]),
                },
                SourceFileEntryV1 {
                    path: NORMATIVE_SPEC_PATH.to_owned(),
                    sha256: Digest32::of(include_bytes!(
                        "../../../docs/ts13-unlinkable-age18-demo-spec.md"
                    )),
                },
            ],
        };
        GenerationEnvironmentV1 {
            cargo_lock_sha256: Digest32([4; 32]),
            enabled_cargo_features: sample_input().enabled_cargo_features,
            rust_toolchain: RustToolchainV1 {
                channel: "nightly-fixture".to_owned(),
                rust_toolchain_file_sha256: Digest32([5; 32]),
                rustc_release: "1.99.0-nightly".to_owned(),
                rustc_commit_hash: "fixture".to_owned(),
                rustc_commit_date: "2026-01-01".to_owned(),
                llvm_version: "21.0.0".to_owned(),
            },
            git: GitMetadataV1 {
                repository_kind: "git",
                object_format: "sha1".to_owned(),
                source_commit_scope: "latest commit touching the closed soundness source allowlist",
                soundness_source_commit: "0000000000000000000000000000000000000000".to_owned(),
            },
            source_manifest_sha256: Digest32::of(
                &canonical_cbor(&source_manifest).expect("fixture source manifest encodes"),
            ),
            source_manifest,
        }
    }

    #[test]
    fn canonical_cbor_is_deterministic_and_sorts_map_keys() {
        let left = Value::Map(vec![
            (Value::Text("aa".to_owned()), Value::Integer(2.into())),
            (Value::Text("b".to_owned()), Value::Integer(1.into())),
        ]);
        let right = Value::Map(vec![
            (Value::Text("b".to_owned()), Value::Integer(1.into())),
            (Value::Text("aa".to_owned()), Value::Integer(2.into())),
        ]);
        let left = canonical_cbor(&left).expect("left map encodes");
        let right = canonical_cbor(&right).expect("right map encodes");
        assert_eq!(left, right);
        assert_eq!(left, vec![0xa2, 0x61, b'b', 0x01, 0x62, b'a', b'a', 0x02]);

        let first = build_outputs(&sample_input(), sample_environment()).expect("fixture builds");
        let second =
            build_outputs(&sample_input(), sample_environment()).expect("fixture rebuilds");
        assert_eq!(first.shape_manifest, second.shape_manifest);
        assert_eq!(first.artifact, second.artifact);
        assert_eq!(first.hash_embedding, second.hash_embedding);
        let hash_embedding =
            std::str::from_utf8(&first.hash_embedding).expect("generated Rust is UTF-8");
        assert!(
            hash_embedding.lines().all(|line| !line.ends_with(' ')),
            "generated Rust must not contain trailing whitespace"
        );
        assert_eq!(first.circuit_hash, second.circuit_hash);
        let (worst_case_bytes, aligned_capacity) =
            deterministic_proof_bound(&ts13_demo_proof_bound_terms(&sample_input()).unwrap())
                .unwrap();
        let aligned_capacity_bytes = u64::from(aligned_capacity);
        assert!(worst_case_bytes <= aligned_capacity_bytes);
        assert_eq!(aligned_capacity_bytes % ENVELOPE_CAPACITY_ALIGNMENT, 0);
        assert!(aligned_capacity_bytes - worst_case_bytes < ENVELOPE_CAPACITY_ALIGNMENT);
        assert_eq!(first.proof_body_capacity, aligned_capacity);

        let decoded: Value =
            ciborium::de::from_reader(first.artifact.as_slice()).expect("artifact decodes");
        let Value::Map(fields) = decoded else {
            panic!("artifact must be a CBOR map");
        };
        let shape_digest = fields
            .iter()
            .find_map(|(key, value)| {
                (key == &Value::Text("shapeManifestSha256".to_owned())).then_some(value)
            })
            .expect("artifact carries the shape digest");
        assert!(matches!(shape_digest, Value::Bytes(bytes) if bytes.len() == 32));
    }

    #[test]
    fn recursive_exclusion_allowlist_is_closed_and_exact() {
        assert_eq!(
            GENERATED_RECURSION_EXCLUSIONS,
            [
                "artifacts/ts13-demo-v1/shape-manifest.cbor",
                "artifacts/ts13-demo-v1/circuit-artifact-v1.cbor",
                "crates/eu-id-prover/src/generated/ts13_demo_artifact.rs",
            ]
        );
        for path in GENERATED_RECURSION_EXCLUSIONS {
            assert!(is_generated_exclusion(path));
            assert!(!is_generated_exclusion(&format!("{path}.bak")));
            assert!(!is_generated_exclusion(
                Path::new("nested")
                    .join(path)
                    .to_str()
                    .expect("fixture path is UTF-8")
            ));
        }

        let workspace = source_workspace();
        write_fixture(
            &workspace.join(HASH_EMBED_PATH),
            b"excluded generated embedding",
        );
        write_fixture(
            &workspace
                .join("crates/eu-id-prover/src/generated")
                .join("ts13_demo_artifact.rs.bak"),
            b"included near miss",
        );
        let manifest = collect_source_tree(&workspace).expect("source tree is collected");
        let paths: BTreeSet<_> = manifest
            .files
            .iter()
            .map(|file| file.path.as_str())
            .collect();
        assert!(!paths.contains(HASH_EMBED_PATH));
        assert!(paths.contains("crates/eu-id-prover/src/generated/ts13_demo_artifact.rs.bak"));
        fs::remove_dir_all(workspace).expect("temporary workspace is removable");
    }

    #[test]
    fn soundness_source_digest_changes_when_source_bytes_change() {
        let workspace = source_workspace();
        let before = collect_source_tree(&workspace).expect("initial source tree is collected");
        let before = Digest32::of(&canonical_cbor(&before).expect("initial manifest encodes"));
        write_fixture(
            &workspace.join("crates/stwo-mldsa/src/lib.rs"),
            b"// changed soundness source\n",
        );
        let after = collect_source_tree(&workspace).expect("changed source tree is collected");
        let after = Digest32::of(&canonical_cbor(&after).expect("changed manifest encodes"));
        assert_ne!(before, after);
        fs::remove_dir_all(workspace).expect("temporary workspace is removable");
    }

    #[test]
    fn normative_spec_bytes_change_the_circuit_hash() {
        let input = sample_input();
        let first_environment = sample_environment();
        let mut second_environment = first_environment.clone();
        let specification = second_environment
            .source_manifest
            .files
            .iter_mut()
            .find(|file| file.path == NORMATIVE_SPEC_PATH)
            .expect("fixture provenance contains the normative specification");
        specification.sha256.0[0] ^= 1;
        second_environment.source_manifest_sha256 = Digest32::of(
            &canonical_cbor(&second_environment.source_manifest)
                .expect("changed source manifest encodes"),
        );
        let first = build_outputs(&input, first_environment).expect("first artifact builds");
        let second = build_outputs(&input, second_environment).expect("second artifact builds");
        assert_ne!(first.circuit_hash, second.circuit_hash);
    }

    #[test]
    fn derived_fri_geometry_uses_packed_leaf_depth_and_lifting() {
        let mut input = sample_input();
        input.proof_system.fri_log_blowup_factor = 3;
        input.proof_system.fri_query_count = 36;
        input.proof_system.pow_bits = 20;
        input.proof_system.lifting_log_size = None;
        let layers = expected_fri_layers(&input.proof_system, 19).expect("FRI geometry derives");
        assert_eq!(layers.last().expect("FRI has layers").input_log_size, 5);
        assert_eq!(layers.last().expect("FRI has layers").output_log_size, 4);
        assert_eq!(layers.last().expect("FRI has layers").merkle_depth, 5);
        assert_eq!(
            layers.last().expect("FRI has layers").maximum_opened_values,
            36
        );

        input.proof_system.lifting_log_size = Some(20);
        assert_eq!(expected_tree_depths(&input).unwrap(), [20; 5]);
        let lifted = expected_fri_layers(&input.proof_system, 20).unwrap();
        assert_eq!(lifted.first().unwrap().input_log_size, 20);

        input.proof_system.fri_log_blowup_factor = 1;
        input.proof_system.lifting_log_size = Some(17);
        assert!(expected_tree_depths(&input).is_err());
        input.proof_system.lifting_log_size = Some(18);
        assert_eq!(expected_tree_depths(&input).unwrap(), [18; 5]);
    }

    #[test]
    fn canonical_profile_semantic_refresh_is_idempotent() {
        const EXPECTED_ISSUER_MU_INPUT_BYTES: u32 = 2_600;

        let mut input = sample_input();
        refresh_canonical_profile_semantics(&mut input).expect("first refresh succeeds");
        let first = serde_json::to_vec(&input).expect("first refresh serializes");
        refresh_canonical_profile_semantics(&mut input).expect("second refresh succeeds");
        assert_eq!(first, serde_json::to_vec(&input).unwrap());
        assert_eq!(CANONICAL_EXPAND_A_JOB_COUNT, 30);
        assert_eq!(CANONICAL_HASH_STREAM_COUNT, 40);
        assert_eq!(CANONICAL_STREAM_ID_COUNT, 83);
        assert_eq!(input.stream_ids.len(), 83);
        assert_eq!(input.hash_streams.len(), 40);
        assert!(
            input
                .hash_streams
                .iter()
                .any(|stream| stream.name == "expand_a_29_job"),
            "the ML-DSA-65 matrix requires all 30 ExpandA jobs"
        );
        assert_eq!(
            input.stream_ids,
            canonical_stream_ids(
                &canonical_hash_stream_shapes().expect("canonical hash shapes derive")
            )
            .expect("canonical stream IDs derive")
        );
        assert_eq!(
            input
                .hash_streams
                .iter()
                .find(|stream| stream.name == "issuer_mu_job")
                .expect("issuer mu job is present")
                .input_capacity_bytes,
            EXPECTED_ISSUER_MU_INPUT_BYTES
        );
        for (relation_name, use_ordinal, expected) in
            canonical_relation_multiplicities().expect("canonical multiplicities derive")
        {
            assert_eq!(
                input
                    .relations
                    .iter()
                    .find(|relation| relation.name == relation_name)
                    .and_then(|relation| relation.uses.get(use_ordinal))
                    .map(|relation_use| relation_use.multiplicity.as_str()),
                Some(expected.as_str())
            );
        }
        let shapes = canonical_hash_stream_shapes().expect("canonical hash shapes derive");
        assert_eq!(
            shapes
                .get("device_mu_job")
                .expect("device mu job is present")
                .message_capacity,
            Some(1_090)
        );
        assert_eq!(
            KECCAK_PUBLIC_MIX_FIXED_LENGTH,
            ((2 + CANONICAL_HASH_STREAM_COUNT * 7 + 2) * std::mem::size_of::<u64>()) as u32
        );
    }

    #[test]
    fn canonical_device_constants_select_mldsa_65() {
        let constants = builtin_constants(Digest32([0; 32]));
        let value = |name: &str| {
            &constants
                .iter()
                .find(|constant| constant.name == name)
                .unwrap_or_else(|| panic!("missing built-in constant {name}"))
                .value
        };
        assert!(matches!(
            value("profile.device_authentication"),
            ConstantValueV1::Text(profile) if profile == "FIPS-204-ML-DSA-65"
        ));
        assert!(matches!(
            value("cbor.device_key_info_prefix"),
            ConstantValueV1::Bytes(bytes)
                if bytes.0.ends_with(&[0x03, 0x38, 0x30, 0x20, 0x59, 0x07, 0xa0])
        ));
        for (name, expected) in [
            ("expand_a.jobs", 30),
            ("device_key_binding.active_rows", 416),
            ("device_key_binding.public_key_bytes", 1_952),
        ] {
            assert!(matches!(
                value(name),
                ConstantValueV1::Unsigned(actual) if *actual == expected
            ));
        }
    }

    #[test]
    fn canonical_gkr_bound_matches_the_sound_carrier() {
        assert_eq!(air_core::gkr::TS13_DEMO_GKR_MAX_PAYLOAD_BYTES, 21_368);
        let terms = ts13_demo_proof_bound_terms(&sample_input()).expect("proof bound derives");
        assert_eq!(
            terms
                .iter()
                .find(|term| term.name == "keccak_round_gkr")
                .expect("GKR proof-bound term is present")
                .maximum_serialized_bytes_per_item,
            21_368
        );
    }

    #[test]
    fn committed_generation_input_is_schema_valid() {
        let input = sample_input();
        input
            .validate()
            .expect("committed generation input matches the canonical profile");
    }

    #[test]
    fn artifact_generation_input_bytes_are_source_pinned() {
        let input = include_bytes!("../../../artifacts/ts13-demo-v1/generation-input-v1.json");
        assert_eq!(
            Digest32::of(input).to_string(),
            CANONICAL_GENERATION_INPUT_SHA256
        );
        validate_generation_input_digest(input).expect("committed generation input is pinned");

        let mut drifted = input.to_vec();
        let byte = drifted
            .iter_mut()
            .find(|byte| **byte == b' ')
            .expect("formatted input contains whitespace");
        *byte = b'\t';
        assert!(
            validate_generation_input_digest(&drifted).is_err(),
            "even valid JSON byte drift requires a reviewed source-pin update"
        );
    }

    #[test]
    fn reserved_transcript_relation_allowlist_is_exact() {
        assert_eq!(RESERVED_TRANSCRIPT_RELATION_NAMES, ["r07_keccak_round"]);
        let input = sample_input();
        assert_eq!(
            input
                .relations
                .iter()
                .filter(|relation| relation.uses.is_empty())
                .map(|relation| relation.name.as_str())
                .collect::<Vec<_>>(),
            RESERVED_TRANSCRIPT_RELATION_NAMES
        );
    }

    #[test]
    fn canonical_generation_input_rejects_census_and_cross_list_drift() {
        assert!(
            minimal_input().validate().is_err(),
            "a shape-only skeleton is not the canonical circuit"
        );

        let mut drifted = sample_input();
        drifted.relations[0].uses.pop();
        assert!(
            drifted.validate().is_err(),
            "the exact 251-use census is mandatory"
        );

        let mut drifted = sample_input();
        let reserved = drifted
            .relations
            .iter()
            .position(|relation| relation.name == "r07_keccak_round")
            .expect("the reserved relation is present");
        let active = drifted
            .relations
            .iter()
            .position(|relation| relation.name == "r08_keccak_xor3")
            .expect("the active relation is present");
        drifted.relations[reserved].uses = drifted.relations[active].uses.clone();
        drifted.relations[active].uses.clear();
        assert!(
            drifted.validate().is_err(),
            "the reserved relation allowlist cannot move or grow"
        );

        let mut drifted = sample_input();
        drifted.transcript.challenge_order[0].owner_module = CANONICAL_MODULE_ORDER[1].to_owned();
        assert!(
            drifted.validate().is_err(),
            "each relation challenge is owned by its exact module"
        );

        let mut drifted = sample_input();
        drifted.relation_tuple_counts[0].value += 1;
        assert!(
            drifted.validate().is_err(),
            "tuple-count metadata must equal the relation schema"
        );

        let mut drifted = sample_input();
        drifted
            .relations
            .iter_mut()
            .find(|relation| relation.name == "r44_private_mso_start")
            .expect("the canonical relation is present")
            .tuple[0]
            .name = "unexpected".to_owned();
        assert!(
            drifted.validate().is_err(),
            "fixed-path relation schemas must be exact"
        );

        let mut drifted = sample_input();
        drifted.transcript.public_mix_order[11]
            .encoding
            .push_str(",unexpected");
        assert!(
            drifted.validate().is_err(),
            "fixed-path public transcript metadata must be exact"
        );

        let mut drifted = sample_input();
        drifted.hash_streams[0].stream_id = u64::MAX;
        assert!(
            drifted.validate().is_err(),
            "every hash stream must reference a declared stream ID"
        );

        let mut drifted = sample_input();
        let issuer_ct_id = drifted
            .hash_streams
            .iter()
            .find(|stream| stream.name == "issuer_ct_job")
            .expect("issuer c-tilde job is present")
            .stream_id;
        let device_ct_id = drifted
            .hash_streams
            .iter()
            .find(|stream| stream.name == "device_ct_job")
            .expect("device c-tilde job is present")
            .stream_id;
        drifted
            .hash_streams
            .iter_mut()
            .find(|stream| stream.name == "issuer_ct_job")
            .expect("issuer c-tilde job is present")
            .stream_id = device_ct_id;
        drifted
            .hash_streams
            .iter_mut()
            .find(|stream| stream.name == "device_ct_job")
            .expect("device c-tilde job is present")
            .stream_id = issuer_ct_id;
        assert!(
            drifted.validate().is_err(),
            "same-geometry hash jobs must keep their semantic stream IDs"
        );

        let mut drifted = sample_input();
        drifted
            .stream_ids
            .iter_mut()
            .find(|entry| entry.name == "issuer_mu_squeeze")
            .expect("issuer mu squeeze stream is present")
            .value += 10_000;
        assert!(
            drifted.validate().is_err(),
            "each named squeeze stream must keep its canonical ID"
        );

        let mut drifted = sample_input();
        let blowup = drifted.proof_system.fri_log_blowup_factor;
        let minimum_queries = 96u32.div_ceil(blowup);
        drifted.proof_system.fri_query_count =
            if drifted.proof_system.fri_query_count == minimum_queries {
                minimum_queries + 1
            } else {
                minimum_queries
            };
        drifted.proof_system.pow_bits = 128 - drifted.proof_system.fri_query_count * blowup;
        let error = drifted
            .validate()
            .expect_err("an alternate 128-bit PCS label must reject");
        assert!(
            error
                .to_string()
                .contains("differs from the executable verifier"),
            "the executable PCS pin must reject before derived-geometry checks: {error}"
        );

        let mut drifted = sample_input();
        drifted
            .hash_streams
            .iter_mut()
            .find(|stream| stream.name == "issuer_mu_job")
            .expect("issuer mu job is present")
            .input_capacity_bytes += 1;
        assert!(
            drifted.validate().is_err(),
            "each hash stream must match its live circuit job shape"
        );

        for (relation_name, use_ordinal, _) in
            canonical_relation_multiplicities().expect("canonical multiplicities derive")
        {
            let mut drifted = sample_input();
            drifted
                .relations
                .iter_mut()
                .find(|relation| relation.name == relation_name)
                .expect("canonical relation is present")
                .uses[use_ordinal]
                .multiplicity
                .push_str(" stale");
            assert!(
                drifted.validate().is_err(),
                "relation {relation_name} use {use_ordinal} must reject stale multiplicity metadata"
            );
        }

        let mut drifted = sample_input();
        drifted.implementation_constants.pop();
        assert!(
            drifted.validate().is_err(),
            "the implementation-constant allowlist is exact"
        );

        let mut drifted = sample_input();
        let digest_widths = drifted
            .implementation_constants
            .iter_mut()
            .find(|constant| constant.name == "impl.digest_identifier_integer_widths")
            .expect("the canonical constant is present");
        digest_widths.value = ConstantValueV1::UnsignedVector(vec![1, 2]);
        assert!(
            drifted.validate().is_err(),
            "digest identifier widths must remain canonical"
        );

        let mut environment = sample_environment();
        environment.enabled_cargo_features[0]
            .features
            .push("unexpected".to_owned());
        assert!(
            build_outputs(&sample_input(), environment).is_err(),
            "resolved Cargo-feature drift must reject artifact generation"
        );
    }

    #[test]
    fn check_mode_reports_every_drifted_output() {
        let workspace = temporary_directory("drift");
        let outputs = build_outputs(&sample_input(), sample_environment()).expect("fixture builds");
        apply_outputs(&workspace, &outputs, GenerationMode::Write).expect("outputs are written");
        apply_outputs(&workspace, &outputs, GenerationMode::Check).expect("outputs match");
        write_fixture(&workspace.join(ARTIFACT_PATH), b"drift");
        write_fixture(&workspace.join(HASH_EMBED_PATH), b"drift");
        let error = apply_outputs(&workspace, &outputs, GenerationMode::Check)
            .expect_err("drift must fail");
        let ArtifactError::Drift(paths) = error else {
            panic!("unexpected error: {error}");
        };
        assert_eq!(
            paths,
            vec![PathBuf::from(ARTIFACT_PATH), PathBuf::from(HASH_EMBED_PATH)]
        );
        fs::remove_dir_all(workspace).expect("temporary workspace is removable");
    }

    #[test]
    fn checked_in_artifact_matches_the_committed_soundness_source() {
        let workspace = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .canonicalize()
            .expect("workspace root resolves");
        generate_from_json(
            &workspace,
            Path::new("artifacts/ts13-demo-v1/generation-input-v1.json"),
            GenerationMode::Check,
        )
        .expect("committed TS13 artifact has no source, shape, or embedding drift");
    }
}
