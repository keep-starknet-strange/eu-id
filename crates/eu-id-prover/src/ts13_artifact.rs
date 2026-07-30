//! Deterministic circuit identity generator for the frozen TS13 demo profile.
//!
//! This module is compiled by `src/bin/ts13_demo_artifact.rs`. Its JSON input
//! deliberately has no defaults: final circuit geometry must be supplied by
//! the composed prover rather than guessed here.

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

/// The only generated files omitted from the soundness source-tree digest.
///
/// `target/` directories are separately recognized as Cargo build output.
/// No `.gitignore`, wildcard, suffix, or caller-provided exclusion is used.
pub const GENERATED_RECURSION_EXCLUSIONS: [&str; 3] =
    [SHAPE_MANIFEST_PATH, ARTIFACT_PATH, HASH_EMBED_PATH];

pub const SOURCE_PACKAGE_ROOTS: [&str; 7] = [
    "crates/air-core",
    "crates/predicates",
    "crates/stwo-sha256",
    "crates/stwo-keccak",
    "crates/stwo-mldsa",
    "crates/eu-id-prover",
    "crates/sdk",
];

pub const FROZEN_MODULE_ORDER: [&str; 19] = [
    "shared_sha256_tables",
    "shared_mldsa_range_tables",
    "shared_keccak_service",
    "ts13_public_context_bind_v1",
    "private_issuer_message_provider",
    "issuer_private_message_mldsa",
    "requested_item_sha256",
    "private_mso_sha256",
    "private_item_cbor_parsers",
    "private_item_binder",
    "private_mso_binder",
    "mdoc_private_mso_validity_v2",
    "private_value_digests_scanner",
    "u5_private_expand_a",
    "u9_private_device_key_binder",
    "private_device_mldsa_u6_u7",
    "private_revocation_range",
    "private_revocation_mldsa",
    "public_revocation_key_epoch_bind",
];

const PROFILE_ID: &str = "ts13-pid-age-over-18-unlinkable-demo-v1";
const PROOF_SYSTEM_ID: &str = "stwo-euid-ts13-demo-v1";
const CONSTRAINT_SYSTEM_VERSION: &str = "ts13-unlinkable-air-v1";
const ARTIFACT_SCHEMA_VERSION: u64 = 1;
const SHAPE_SCHEMA_VERSION: u64 = 1;
const V4_ENVELOPE_VERSION: u64 = 4;
const V4_HEADER_BYTES: u64 = 46;
const V4_CAPACITY_ALIGNMENT: u64 = 65_536;

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
pub struct HexBytes(Vec<u8>);

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
pub struct GenerationInputV1 {
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
    proof_serialization_bound: Vec<ProofBoundTermV1>,
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
    components: Vec<AirComponentLayoutV1>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct AirComponentLayoutV1 {
    name: String,
    active_rows: u32,
    constraint_log_degree_bound: u32,
    columns: ColumnTreesV1,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ColumnTreesV1 {
    preprocessed: Vec<ColumnSchemaV1>,
    base: Vec<ColumnSchemaV1>,
    extension: Vec<ColumnSchemaV1>,
    interaction: Vec<ColumnSchemaV1>,
}

impl ColumnTreesV1 {
    fn all(&self) -> impl Iterator<Item = (&'static str, &ColumnSchemaV1)> {
        self.preprocessed
            .iter()
            .map(|column| ("preprocessed", column))
            .chain(self.base.iter().map(|column| ("base", column)))
            .chain(self.extension.iter().map(|column| ("extension", column)))
            .chain(
                self.interaction
                    .iter()
                    .map(|column| ("interaction", column)),
            )
    }

    fn counts(&self) -> Result<ColumnCountsV1, ArtifactError> {
        Ok(ColumnCountsV1 {
            preprocessed: sum_column_counts(&self.preprocessed)?,
            base: sum_column_counts(&self.base)?,
            extension: sum_column_counts(&self.extension)?,
            interaction: sum_column_counts(&self.interaction)?,
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
struct ColumnSchemaV1 {
    name: String,
    scalar: ColumnScalarV1,
    count: u32,
    log_size: u32,
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

#[derive(Clone, Debug, Deserialize, Serialize)]
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
}

#[derive(Clone, Debug, Deserialize, Serialize)]
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
    Pow,
    SerializationOverhead,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ProofBoundTermV1 {
    section: ProofBoundSectionV1,
    name: String,
    maximum_item_count: u64,
    maximum_serialized_bytes_per_item: u64,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
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
    components: Vec<ShapeComponentV1>,
    stream_ids: Vec<NamedU64V1>,
    hash_streams: Vec<HashStreamV1>,
    range_tables: Vec<RangeTableV1>,
    relation_tuple_counts: Vec<NamedU64V1>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct ShapeComponentV1 {
    module_ordinal: u32,
    module: String,
    component_ordinal: u32,
    component: String,
    active_rows: u32,
    constraint_log_degree_bound: u32,
    column_counts: ColumnCountsV1,
}

#[derive(Clone, Copy, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct ColumnCountsV1 {
    preprocessed: u32,
    base: u32,
    extension: u32,
    interaction: u32,
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
        if self.credential_shape.issuer_cose_sig_structure_bytes == 0
            || self.credential_shape.mso_payload_bytes == 0
            || self.credential_shape.padded_issuer_signed_item_bytes == 0
        {
            return Err(ArtifactError::InvalidInput(
                "credential byte lengths must be non-zero".to_owned(),
            ));
        }
        let widths = &self.credential_shape.digest_identifier_integer_widths;
        if widths.is_empty()
            || widths.windows(2).any(|pair| pair[0] >= pair[1])
            || widths.contains(&0)
        {
            return Err(ArtifactError::InvalidInput(
                "digest identifier integer widths must be non-zero, sorted, and unique".to_owned(),
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
        if module_names != FROZEN_MODULE_ORDER {
            return Err(ArtifactError::InvalidInput(format!(
                "module order must be exactly {:?}",
                FROZEN_MODULE_ORDER
            )));
        }

        let mut component_names = BTreeSet::new();
        for module in &self.modules {
            if module.components.is_empty() {
                return Err(ArtifactError::InvalidInput(format!(
                    "module {:?} has no AIR components",
                    module.name
                )));
            }
            for component in &module.components {
                if component.name.is_empty() || !component_names.insert(component.name.as_str()) {
                    return Err(ArtifactError::InvalidInput(format!(
                        "AIR component names must be non-empty and globally unique: {:?}",
                        component.name
                    )));
                }
                let max_log_size = component
                    .columns
                    .all()
                    .map(|(_, column)| column.log_size)
                    .max();
                if let Some(max_log_size) = max_log_size {
                    if max_log_size >= u32::BITS {
                        return Err(ArtifactError::InvalidInput(format!(
                            "component {:?} has unsupported log size {max_log_size}",
                            component.name
                        )));
                    }
                    if component.active_rows > (1_u32 << max_log_size) {
                        return Err(ArtifactError::InvalidInput(format!(
                            "component {:?} active rows exceed its largest trace",
                            component.name
                        )));
                    }
                } else if component.active_rows != 0 {
                    return Err(ArtifactError::InvalidInput(format!(
                        "zero-column component {:?} must have zero active rows",
                        component.name
                    )));
                }
                let mut column_names = BTreeSet::new();
                for (tree, column) in component.columns.all() {
                    if column.name.is_empty()
                        || column.count == 0
                        || !column_names.insert((tree, column.name.as_str()))
                    {
                        return Err(ArtifactError::InvalidInput(format!(
                            "component {:?} has an invalid or duplicate {tree} column group {:?}",
                            component.name, column.name
                        )));
                    }
                }
            }
        }
        let public_context = &self.modules[3];
        if public_context.components.len() != 1
            || public_context.components[0].active_rows != 0
            || public_context.components[0].columns.all().next().is_some()
        {
            return Err(ArtifactError::InvalidInput(
                "Ts13PublicContextBindV1 must be exactly one zero-column component".to_owned(),
            ));
        }
        let u9 = &self.modules[14];
        if u9.components.len() != 1 || u9.components[0].active_rows != 416 {
            return Err(ArtifactError::InvalidInput(
                "U9 must be exactly one component with 416 active rows".to_owned(),
            ));
        }
        if self.modules[15].components.len() != 1 {
            return Err(ArtifactError::InvalidInput(
                "U6 and U7 must be one contiguous private-device ML-DSA AIR component".to_owned(),
            ));
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
                || relation.uses.is_empty()
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
                            .components
                            .iter()
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

        if self.serialized_claims.is_empty() {
            return Err(ArtifactError::InvalidInput(
                "serialized claim order cannot be empty".to_owned(),
            ));
        }
        for claim in &self.serialized_claims {
            if claim.name.is_empty() || claim.encoding.is_empty() || claim.fixed_length == 0 {
                return Err(ArtifactError::InvalidInput(
                    "serialized claims require a name, encoding, and fixed byte length".to_owned(),
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
        checked_name_list(
            "hash stream",
            self.hash_streams.iter().map(|stream| stream.name.as_str()),
        )?;
        if self.hash_streams.is_empty()
            || self.hash_streams.iter().any(|stream| {
                stream.hash_function.is_empty()
                    || stream.job_count == 0
                    || stream.input_capacity_bytes == 0
                    || stream.output_bytes == 0
            })
            || self
                .hash_streams
                .iter()
                .map(|stream| stream.stream_id)
                .collect::<BTreeSet<_>>()
                .len()
                != self.hash_streams.len()
        {
            return Err(ArtifactError::InvalidInput(
                "hash streams require sorted unique names and IDs plus complete non-zero geometry"
                    .to_owned(),
            ));
        }
        checked_name_list(
            "range table",
            self.range_tables.iter().map(|table| table.name.as_str()),
        )?;
        if self.range_tables.is_empty()
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
        checked_name_list(
            "implementation constant",
            self.implementation_constants
                .iter()
                .map(|constant| constant.name.as_str()),
        )?;
        if self
            .implementation_constants
            .iter()
            .any(|constant| !constant.name.starts_with("impl."))
        {
            return Err(ArtifactError::InvalidInput(
                "implementation constant names must start with \"impl.\"".to_owned(),
            ));
        }

        if self.tree_zero.derivation.is_empty()
            || self.tree_zero.hash.is_empty()
            || self.tree_zero.preprocessed_column_order.is_empty()
        {
            return Err(ArtifactError::InvalidInput(
                "tree-zero derivation, hash, and preprocessed order are required".to_owned(),
            ));
        }
        if self.proof_system.field.is_empty()
            || self.proof_system.secure_extension_field.is_empty()
            || self.proof_system.pcs.is_empty()
            || self.proof_system.commitment_hash.is_empty()
            || self.proof_system.merkle_hash.is_empty()
            || self.proof_system.field_modulus == 0
            || self.proof_system.secure_extension_degree == 0
            || self.proof_system.fri_query_count == 0
            || self.proof_system.merkle_trees.is_empty()
            || self.proof_system.fri_layers.is_empty()
        {
            return Err(ArtifactError::InvalidInput(
                "proof-system field, PCS, hash, FRI, query, and extension parameters are required"
                    .to_owned(),
            ));
        }
        checked_name_list(
            "Merkle tree",
            self.proof_system
                .merkle_trees
                .iter()
                .map(|tree| tree.name.as_str()),
        )?;
        if self.proof_system.merkle_trees.iter().any(|tree| {
            tree.depth == 0 || tree.digest_bytes == 0 || tree.maximum_opened_columns == 0
        }) || self.proof_system.fri_layers.iter().any(|layer| {
            layer.input_log_size <= layer.output_log_size
                || layer.merkle_depth == 0
                || layer.maximum_opened_values == 0
        }) {
            return Err(ArtifactError::InvalidInput(
                "Merkle-tree depths and FRI-layer maxima must be explicit and non-zero".to_owned(),
            ));
        }
        validate_proof_bound(&self.proof_serialization_bound)?;

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
        let mut components = Vec::new();
        for (module_ordinal, module) in self.modules.iter().enumerate() {
            for (component_ordinal, component) in module.components.iter().enumerate() {
                components.push(ShapeComponentV1 {
                    module_ordinal: u32::try_from(module_ordinal).map_err(|_| {
                        ArtifactError::InvalidInput("module ordinal exceeds u32".to_owned())
                    })?,
                    module: module.name.clone(),
                    component_ordinal: u32::try_from(component_ordinal).map_err(|_| {
                        ArtifactError::InvalidInput("component ordinal exceeds u32".to_owned())
                    })?,
                    component: component.name.clone(),
                    active_rows: component.active_rows,
                    constraint_log_degree_bound: component.constraint_log_degree_bound,
                    column_counts: component.columns.counts()?,
                });
            }
        }
        Ok(ShapeManifestV1 {
            schema_version: SHAPE_SCHEMA_VERSION,
            profile: PROFILE_ID,
            credential_shape: self.credential_shape.clone(),
            request_context_corpus: self.request_context_corpus.clone(),
            components,
            stream_ids: self.stream_ids.clone(),
            hash_streams: self.hash_streams.clone(),
            range_tables: self.range_tables.clone(),
            relation_tuple_counts: self.relation_tuple_counts.clone(),
        })
    }
}

fn checked_named_values(kind: &str, values: &[NamedU64V1]) -> Result<(), ArtifactError> {
    if values.is_empty() {
        return Err(ArtifactError::InvalidInput(format!(
            "{kind} list cannot be empty"
        )));
    }
    checked_name_list(kind, values.iter().map(|entry| entry.name.as_str()))
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
        ProofBoundSectionV1::Pow,
        ProofBoundSectionV1::SerializationOverhead,
    ];
    let present: BTreeSet<_> = terms.iter().map(|term| term.section).collect();
    if present != BTreeSet::from(required) {
        return Err(ArtifactError::InvalidInput(
            "proof serialization bound must cover header, commitments, queries, Merkle \
             decommitments, FRI layers, claims, column values, PoW, and serialization overhead"
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

fn sum_column_counts(columns: &[ColumnSchemaV1]) -> Result<u32, ArtifactError> {
    columns.iter().try_fold(0_u32, |sum, column| {
        sum.checked_add(column.count).ok_or_else(|| {
            ArtifactError::InvalidInput("component column count exceeds u32".to_owned())
        })
    })
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
        .checked_add(V4_CAPACITY_ALIGNMENT - 1)
        .map(|value| value / V4_CAPACITY_ALIGNMENT * V4_CAPACITY_ALIGNMENT)
        .ok_or_else(|| ArtifactError::InvalidInput("proof capacity overflows u64".to_owned()))?;
    let capacity = u32::try_from(capacity).map_err(|_| {
        ArtifactError::InvalidInput("V4 capacity does not fit its u32 header field".to_owned())
    })?;
    Ok((worst_case, capacity))
}

fn builtin_constants() -> Vec<ArtifactConstantV1> {
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
        constant_unsigned("profile.potential_issuers", 1),
        constant_unsigned("profile.revocation_mandatory", 1),
        constant_text("profile.timestamp_precision", "UTC-whole-Unix-second"),
        constant_unsigned("u5.accepted_coefficients_per_polynomial", 256),
        constant_unsigned("u5.candidate_bits", 23),
        constant_unsigned("u5.expand_a_jobs", 30),
        constant_unsigned("u5.modulus_q", 8_380_417),
        constant_unsigned("u5.squeeze_blocks_per_job", 6),
        constant_unsigned("u6.a_evaluation_count", 30),
        constant_unsigned("u6.coefficient_evaluation_count", 30),
        constant_unsigned("u6.inverse_ntt_normalizer", 8_347_681),
        constant_unsigned("u6.radix", 512),
        constant_unsigned("u6.scaled_t1_factor", 1 << 13),
        constant_unsigned("u6.t1_evaluation_count", 6),
        constant_unsigned("u6.t1_hi_bits", 1),
        constant_unsigned("u6.t1_lo_bits", 9),
        constant_unsigned("u9.active_rows", 416),
        constant_unsigned("u9.device_public_key_bytes", 1_952),
        constant_unsigned("u9.rho_rows", 32),
        constant_unsigned("validity.maximum_year", 2099),
        constant_unsigned("validity.minimum_year", 2020),
        constant_bytes("v4.magic", b"EUIDTS13"),
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
    let mut files = vec![SourceFileEntryV1 {
        path: "Cargo.toml".to_owned(),
        sha256: Digest32::of(&read(&cargo_toml)?),
    }];
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
        workspace_files: vec!["Cargo.toml".to_owned()],
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

fn git_path_arguments(prefix: &[&'static str]) -> Vec<&'static str> {
    let mut arguments = prefix.to_vec();
    arguments.push("--");
    arguments.push("Cargo.toml");
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
    let source_manifest_sha256 = Digest32::of(&canonical_cbor(&source_manifest)?);
    Ok(GenerationEnvironmentV1 {
        cargo_lock_sha256: Digest32::of(&read(&workspace.join("Cargo.lock"))?),
        rust_toolchain: toolchain_metadata(workspace)?,
        git: git_metadata(workspace)?,
        source_manifest,
        source_manifest_sha256,
    })
}

fn build_outputs(
    input: &GenerationInputV1,
    environment: GenerationEnvironmentV1,
) -> Result<GeneratedOutputs, ArtifactError> {
    input.validate()?;
    let shape_manifest = canonical_cbor(&input.shape_manifest()?)?;
    let shape_manifest_sha256 = Digest32::of(&shape_manifest);
    let (worst_case, proof_body_capacity) =
        deterministic_proof_bound(&input.proof_serialization_bound)?;

    let mut constants = builtin_constants();
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
        module_order: FROZEN_MODULE_ORDER
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
            envelope_version: V4_ENVELOPE_VERSION,
            envelope_header_bytes: V4_HEADER_BYTES,
            capacity_alignment_bytes: V4_CAPACITY_ALIGNMENT,
            bound_terms: input.proof_serialization_bound.clone(),
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
    for chunk in digest.0.chunks(8) {
        output.push_str("    ");
        for byte in chunk {
            write!(output, "0x{byte:02x}, ").expect("writing to String cannot fail");
        }
        output.push('\n');
    }
    output.push_str("];\n");
}

fn render_hash_embedding(
    circuit_hash: Digest32,
    shape_manifest_sha256: Digest32,
    source_manifest_sha256: Digest32,
    proof_body_capacity: u32,
) -> String {
    let mut output = String::from(
        "// @generated by `ts13_demo_artifact`; do not edit.\n\
         // This exact path is the sole in-tree circuit-identity recursion exclusion.\n\n",
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
        for root in SOURCE_PACKAGE_ROOTS {
            write_fixture(
                &workspace.join(root).join("src/lib.rs"),
                format!("// {root}\n").as_bytes(),
            );
        }
        workspace
    }

    fn sample_input() -> GenerationInputV1 {
        let modules = FROZEN_MODULE_ORDER
            .iter()
            .map(|name| ModuleLayoutV1 {
                name: (*name).to_owned(),
                components: vec![AirComponentLayoutV1 {
                    name: format!("{name}_component"),
                    active_rows: match *name {
                        "ts13_public_context_bind_v1" => 0,
                        "u9_private_device_key_binder" => 416,
                        _ => 1,
                    },
                    constraint_log_degree_bound: 1,
                    columns: if *name == "ts13_public_context_bind_v1" {
                        ColumnTreesV1 {
                            preprocessed: Vec::new(),
                            base: Vec::new(),
                            extension: Vec::new(),
                            interaction: Vec::new(),
                        }
                    } else {
                        ColumnTreesV1 {
                            preprocessed: Vec::new(),
                            base: vec![ColumnSchemaV1 {
                                name: "value".to_owned(),
                                scalar: ColumnScalarV1::M31,
                                count: 1,
                                log_size: if *name == "u9_private_device_key_binder" {
                                    9
                                } else {
                                    1
                                },
                            }],
                            extension: Vec::new(),
                            interaction: Vec::new(),
                        }
                    },
                }],
            })
            .collect::<Vec<_>>();
        let first_component = modules[0].components[0].name.clone();
        GenerationInputV1 {
            credential_shape: CredentialShapeV1 {
                issuer_cose_sig_structure_bytes: 128,
                mso_payload_bytes: 2_048,
                padded_issuer_signed_item_bytes: 256,
                digest_identifier_integer_widths: vec![1, 2],
            },
            request_context_corpus: RequestContextCorpusV1 {
                corpus_sha256: Digest32([1; 32]),
                observed_max_device_cose_sig_structure_bytes: 300,
                device_sig_structure_capacity: 512,
            },
            modules,
            relations: vec![RelationLayoutV1 {
                name: "FixtureRelation".to_owned(),
                challenge_owner_module: FROZEN_MODULE_ORDER[0].to_owned(),
                tuple: vec![RelationFieldV1 {
                    name: "value".to_owned(),
                    scalar: ColumnScalarV1::M31,
                }],
                uses: vec![RelationUseV1 {
                    module: FROZEN_MODULE_ORDER[0].to_owned(),
                    component: first_component,
                    sign: RelationSignV1::Positive,
                    multiplicity: "1".to_owned(),
                }],
            }],
            transcript: TranscriptLayoutV1 {
                public_mix_order: vec![TranscriptEntryV1 {
                    owner_module: FROZEN_MODULE_ORDER[3].to_owned(),
                    name: "public_context".to_owned(),
                    encoding: "bytes".to_owned(),
                    fixed_length: Some(96),
                }],
                challenge_order: vec![TranscriptEntryV1 {
                    owner_module: FROZEN_MODULE_ORDER[0].to_owned(),
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
                preprocessed_column_order: vec!["fixture".to_owned()],
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
                merkle_trees: vec![MerkleTreeParametersV1 {
                    name: "tree0".to_owned(),
                    depth: 9,
                    digest_bytes: 32,
                    maximum_opened_columns: 1,
                }],
                fri_layers: vec![FriLayerParametersV1 {
                    input_log_size: 12,
                    output_log_size: 10,
                    merkle_depth: 10,
                    maximum_opened_values: 2,
                }],
            },
            proof_serialization_bound: [
                ProofBoundSectionV1::ProofHeader,
                ProofBoundSectionV1::Commitments,
                ProofBoundSectionV1::Queries,
                ProofBoundSectionV1::MerkleDecommitments,
                ProofBoundSectionV1::FriLayers,
                ProofBoundSectionV1::Claims,
                ProofBoundSectionV1::ColumnValues,
                ProofBoundSectionV1::Pow,
                ProofBoundSectionV1::SerializationOverhead,
            ]
            .into_iter()
            .enumerate()
            .map(|(index, section)| ProofBoundTermV1 {
                section,
                name: format!("term_{index}"),
                maximum_item_count: 1,
                maximum_serialized_bytes_per_item: 8,
            })
            .collect(),
            enabled_cargo_features: SOURCE_PACKAGE_ROOTS
                .iter()
                .map(|root| PackageFeaturesV1 {
                    package: root.trim_start_matches("crates/").to_owned(),
                    features: Vec::new(),
                })
                .collect(),
        }
    }

    fn sample_environment() -> GenerationEnvironmentV1 {
        let source_manifest = SourceTreeManifestV1 {
            schema_version: 1,
            workspace_files: vec!["Cargo.toml".to_owned()],
            package_roots: SOURCE_PACKAGE_ROOTS
                .iter()
                .map(|root| (*root).to_owned())
                .collect(),
            cargo_build_directory_name: "target",
            generated_recursive_exclusions: GENERATED_RECURSION_EXCLUSIONS
                .iter()
                .map(|path| (*path).to_owned())
                .collect(),
            files: vec![SourceFileEntryV1 {
                path: "Cargo.toml".to_owned(),
                sha256: Digest32([3; 32]),
            }],
        };
        GenerationEnvironmentV1 {
            cargo_lock_sha256: Digest32([4; 32]),
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
        assert_eq!(first.circuit_hash, second.circuit_hash);
        assert_eq!(first.proof_body_capacity, 65_536);

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
}
