//! Combines one or more proving modules into a single STARK proof.
//!
//! Each circuit implements [`Air`] and [`AirProver`]. A module does not own the
//! channel or the commitment scheme. It only contributes columns and components
//! to shared commitment trees. The orchestrator functions [`prove`] and
//! [`verify`] own the transcript and drive every module through the same four
//! phases:
//!
//! 0. preprocessed tables
//! 1. main witness + multiplicity columns
//! 2. interaction (LogUp) columns
//! 3. component assembly + the single `prove`/`verify` call
//!
//! Proving a single circuit is just `prove(&mut [&mut module])`.
//!
//! ## Hash choice
//!
//! Each combined proof uses one channel and one commitment scheme.
//! Thus, all modules use one hash.
//! The [`Mc`], [`Ch`], and [`Hasher`] aliases define this hash.
//! Module-level generic parameters cannot select different hashes.
//! Change these aliases to select another hash.

pub mod claim_mask;
pub mod relations;

use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher as _};
use std::sync::{Mutex, OnceLock};

use num_traits::Zero;
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo::core::vcs_lifted::MerkleHasherLifted;
use stwo::core::verifier::{verify as stark_verify, VerificationError};
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::{CircleEvaluation, PolyOps};
use stwo::prover::poly::twiddles::TwiddleTree;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{
    prove as stark_prove, CommitmentSchemeProver, ComponentProver, ProvingError, TreeBuilder,
};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::TraceLocationAllocator;

/// The Merkle channel (i.e. the hash) that binds the whole proof. Every module
/// commits its trees and draws its challenges against this one type.
pub type Mc = Blake2sMerkleChannel;

/// The Fiat-Shamir channel modules mix their public statement and relations
/// into. Must stay equal to `<Mc as MerkleChannel>::C`.
pub type Ch = Blake2sChannel;

/// The hasher carried inside the emitted [`StarkProof`] (`Mc::H`).
pub type Hasher = Blake2sMerkleHasher;

/// The commitment-root type carried in `StarkProof::commitments` (a Blake2s
/// Merkle root under the current [`Hasher`] alias).
pub type CommitmentRoot = <Hasher as MerkleHasherLifted>::Hash;

pub type PreprocessedColumnEval = CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreprocessedColumnFingerprint {
    pub id: PreProcessedColumnId,
    pub module: &'static str,
    pub log_size: u32,
    pub hash: u64,
}

static TWIDDLE_CACHE: OnceLock<Mutex<HashMap<u32, &'static TwiddleTree<SimdBackend>>>> =
    OnceLock::new();

fn cached_twiddles(twiddle_log_size: u32) -> &'static TwiddleTree<SimdBackend> {
    let cache = TWIDDLE_CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    // A panic can poison this lock. One malformed proof must not block later
    // proof operations. The map is consistent between operations.
    let mut cache = cache
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    if let Some(twiddles) = cache.get(&twiddle_log_size) {
        return twiddles;
    }
    let twiddles = Box::leak(Box::new(SimdBackend::precompute_twiddles(
        CanonicCoset::new(twiddle_log_size)
            .circle_domain()
            .half_coset,
    )));
    cache.insert(twiddle_log_size, twiddles);
    twiddles
}

fn unique_preprocessed_ids(
    ids: impl IntoIterator<Item = PreProcessedColumnId>,
) -> Vec<PreProcessedColumnId> {
    let mut seen = HashSet::new();
    let mut unique = Vec::new();
    for id in ids {
        if seen.insert(id.clone()) {
            unique.push(id);
        }
    }
    unique
}

fn select_first_preprocessed_ids(
    module_ids: &[Vec<PreProcessedColumnId>],
) -> (Vec<PreProcessedColumnId>, Vec<Vec<PreProcessedColumnId>>) {
    let mut seen = HashSet::new();
    let mut unique = Vec::new();
    let mut selected_by_module = Vec::with_capacity(module_ids.len());

    for ids in module_ids {
        let mut selected = Vec::new();
        for id in ids {
            if seen.insert(id.clone()) {
                unique.push(id.clone());
                selected.push(id.clone());
            }
        }
        selected_by_module.push(selected);
    }

    (unique, selected_by_module)
}

pub fn fingerprint_preprocessed_columns(
    module: &'static str,
    ids: &[PreProcessedColumnId],
    columns: &[PreprocessedColumnEval],
) -> Vec<PreprocessedColumnFingerprint> {
    assert_eq!(
        ids.len(),
        columns.len(),
        "{module} preprocessed ids and columns must have the same length"
    );

    ids.iter()
        .zip(columns)
        .map(|(id, column)| {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            column.domain.log_size().hash(&mut hasher);
            column.values.length.hash(&mut hasher);
            for value in column.values.as_slice() {
                value.0.hash(&mut hasher);
            }
            PreprocessedColumnFingerprint {
                id: id.clone(),
                module,
                log_size: column.domain.log_size(),
                hash: hasher.finish(),
            }
        })
        .collect()
}

fn assert_preprocessed_id_content_invariant(modules: &mut [&mut dyn AirProver]) {
    let mut seen = HashMap::<PreProcessedColumnId, PreprocessedColumnFingerprint>::new();

    for module in modules.iter_mut() {
        for fingerprint in module.preprocessed_column_fingerprints() {
            match seen.get(&fingerprint.id) {
                Some(first)
                    if first.log_size != fingerprint.log_size || first.hash != fingerprint.hash =>
                {
                    panic!(
                        "preprocessed column id '{}' has different content in modules '{}' and '{}'",
                        fingerprint.id.id, first.module, fingerprint.module
                    );
                }
                Some(_) => {}
                None => {
                    seen.insert(fingerprint.id.clone(), fingerprint);
                }
            }
        }
    }
}

fn unique_preprocessed_layout(
    module_specs: impl IntoIterator<Item = (Vec<PreProcessedColumnId>, Vec<u32>)>,
) -> Vec<u32> {
    let mut seen = HashSet::new();
    let mut layout = Vec::new();

    for (ids, sizes) in module_specs {
        assert_eq!(
            ids.len(),
            sizes.len(),
            "preprocessed ids and layout sizes must have the same length"
        );
        for (id, size) in ids.into_iter().zip(sizes) {
            if seen.insert(id) {
                layout.push(size);
            }
        }
    }

    layout
}

/// The per-tree column log-sizes a module contributes, in commit order.
///
/// The verifier uses this to commit against the proof's commitments without
/// rebuilding any trace.
pub struct TreeLayout {
    pub preprocessed: Vec<u32>,
    pub trace: Vec<u32>,
    pub interaction: Vec<u32>,
}

/// Defines the module operations that the prover and verifier use.
///
/// A module binds public input, draws relations, declares its layout, exposes
/// claimed LogUp sums, and assembles AIR components.
pub trait Air {
    /// Reject malformed proof-carried module metadata before it can influence
    /// layouts, transcript mixing, or the global LogUp balance. Implementations
    /// with variable-length serialized claims must enforce their exact
    /// component cardinality here.
    fn validate_structure(&self) -> Result<(), VerificationError> {
        Ok(())
    }

    /// Bind this module's public statement to the shared transcript.
    fn mix_public(&self, channel: &mut Ch);

    /// Draw this module's lookup relations from the shared channel and stash
    /// them for the interaction phase and component assembly.
    fn draw_relations(&mut self, channel: &mut Ch);

    /// Column log-sizes per tree, in commit order.
    fn layout(&self) -> TreeLayout;

    /// The module's claimed LogUp sums whose total enters the global balance.
    /// The orchestrator sums these across all modules and rejects unless the
    /// total is zero. For most modules these are the per-component sums. A
    /// module whose balance also folds in public-input provider terms (P256)
    /// returns those terms here too.
    fn claimed_sums(&self) -> Vec<QM31>;

    /// Mix this module's claimed-sum commitment into the transcript, just before
    /// the interaction tree is committed. The default mixes [`Air::claimed_sums`]
    /// as one flat felt slice. A module whose standalone transcript mixed a
    /// richer structure (P256 mixes per-component claims plus u64 counts) can
    /// override to reproduce it exactly. Must match between prove and verify.
    fn mix_claimed_sums(&self, channel: &mut Ch) {
        channel.mix_felts(&self.claimed_sums());
    }

    /// The preprocessed column ids this module contributes to tree 0, in commit
    /// order. The orchestrator concatenates these across all modules to seed the
    /// single shared [`TraceLocationAllocator`] before building components.
    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId>;

    /// Reconstruct this module's trusted tree-0 columns in the same order as
    /// [`Air::preprocessed_column_ids`]. Production verification commits these
    /// verifier-derived values and pins the proof to that root.
    ///
    /// The default fails closed. A module without preprocessed columns returns
    /// an empty vector.
    ///
    /// A module with preprocessed columns must override this method.
    /// Otherwise, [`compute_canonical_preprocessed_root`] returns `Err`.
    ///
    /// A module with witness-dependent preprocessed columns cannot reconstruct
    /// its tree-0 root from public data and must use an independently pinned
    /// root or fail closed.
    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<PreprocessedColumnEval>, VerificationError> {
        if self.preprocessed_column_ids().is_empty() {
            Ok(Vec::new())
        } else {
            Err(VerificationError::InvalidStructure(
                "module cannot reconstruct its preprocessed columns".into(),
            ))
        }
    }

    /// Build and store this module's AIR components with the shared allocator.
    ///
    /// Call this once in module order. Draw relations and seed the allocator
    /// first. A module owns its components. It lends them through
    /// [`Air::components`] and [`AirProver::prover_components`]. This matches
    /// Stwo's borrowed-component API and avoids rebuilding components.
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator);

    /// Borrow the built verifier-side components, in commit order. Call only
    /// after [`Air::build_components`].
    fn components(&self) -> Vec<&dyn Component>;

    /// Optional post-interaction tree column log-sizes. Feature-gated lookup
    /// arguments use this for MLE tie-back traces committed after tree 2.
    fn post_interaction_log_sizes(&self) -> Vec<u32> {
        Vec::new()
    }

    /// Optional verifier-side post-interaction transcript work, replayed after
    /// tree 2 is committed and before the post-interaction tree is committed.
    fn verify_post_interaction(&mut self, _channel: &mut Ch) -> Result<(), VerificationError> {
        Ok(())
    }
}

/// The prover-only extension: a module that holds a witness and can write its
/// actual columns into the shared commitment trees.
pub trait AirProver: Air {
    /// Largest trace log-size this module uses. The orchestrator takes the max
    /// over all modules to size the FRI twiddles.
    fn max_log_size(&self) -> u32;

    /// Largest constraint-evaluation log-degree this module needs the twiddle
    /// domain to cover. The orchestrator takes the max over all modules and adds
    /// the FRI blow-up to size the precomputed twiddles (unless the config pins
    /// an explicit `lifting_log_size`).
    ///
    /// For a trace of size `2^n`, a degree-`d` constraint has a quotient degree
    /// bounded by `(d - 1) * 2^n`. The default — `max_log_size() + 1` — covers
    /// constraints through degree three. Modules with higher-degree constraints
    /// (including SHA-256 and P-256 ECDSA) override this with the largest bound
    /// declared by their components.
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.max_log_size() + 1
    }

    /// Whether the commitment scheme must retain committed polynomials in
    /// coefficient form (`set_store_polynomials_coefficients`). Off by default.
    /// The P256 module turns it on for its lifting path. If any module in a
    /// `prove` call needs it, the orchestrator enables it for the whole proof.
    fn store_polynomial_coefficients(&self) -> bool {
        false
    }

    /// Appends preprocessed columns to the shared tree.
    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, Mc>);

    /// Fingerprint preprocessed column content before tree-0 dedup. Equal
    /// preprocessed IDs must imply equal fixed-column content. Otherwise
    /// first-writer-wins tree assembly aliases one module's constraints to
    /// another module's table.
    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        let ids = self.preprocessed_column_ids();
        assert!(
            ids.is_empty(),
            "AirProver with preprocessed columns must expose preprocessed fingerprints"
        );
        Vec::new()
    }

    /// Appends only the selected preprocessed columns.
    ///
    /// An earlier module can already contain deterministic columns with the same IDs.
    fn write_selected_preprocessed(
        &mut self,
        tb: &mut TreeBuilder<SimdBackend, Mc>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        assert_eq!(
            selected_ids,
            self.preprocessed_column_ids().as_slice(),
            "module does not support partial preprocessed writes"
        );
        self.write_preprocessed(tb);
    }

    /// Appends witness and multiplicity columns to the shared tree.
    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, Mc>);

    /// Builds and appends interaction columns from the relation challenges.
    ///
    /// The method also stores this module's claimed sums for [`Air::claimed_sums`].
    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, Mc>);

    /// Optional prover-side post-interaction transcript work, run after tree 2
    /// is committed. Any proof messages mixed here are bound to all
    /// committed GKR inputs: trace/multiplicity columns, relation randomness,
    /// claimed sums, and interaction columns.
    fn prove_post_interaction(&mut self, _channel: &mut Ch) {}

    /// Appends optional post-interaction tie-back columns.
    fn write_post_interaction(&mut self, _tb: &mut TreeBuilder<SimdBackend, Mc>) {}

    /// Borrow the built prover-side components, in commit order. Call only
    /// after [`Air::build_components`].
    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>>;
}

/// Drive every module through the four phases against one shared channel and one
/// shared commitment scheme, producing a single STARK proof.
pub fn prove(
    modules: &mut [&mut dyn AirProver],
    config: PcsConfig,
) -> Result<StarkProof<Hasher>, ProvingError> {
    // Size the twiddles to the largest constraint-evaluation domain any module
    // needs, plus the FRI blow-up — unless the config pins an explicit lifting
    // size. With the default (degree-2) bound this is `max_log_size + 1 +
    // log_blowup`, matching the standalone provers.
    let max_constraint_log_degree_bound = modules
        .iter()
        .map(|m| m.max_constraint_log_degree_bound())
        .max()
        .expect("at least one module");
    let twiddle_log_size = config
        .lifting_log_size
        .unwrap_or(max_constraint_log_degree_bound + config.fri_config.log_blowup_factor);

    let twiddles = cached_twiddles(twiddle_log_size);

    let channel = &mut Ch::default();
    config.mix_into(channel);

    let mut commitment_scheme = CommitmentSchemeProver::<SimdBackend, Mc>::new(config, twiddles);
    // If any module needs committed polynomials kept in coefficient form (the
    // P256 lifting path), enable it for the shared scheme.
    if modules.iter().any(|m| m.store_polynomial_coefficients()) {
        commitment_scheme.set_store_polynomials_coefficients();
    }

    // Tree 0: deterministic preprocessed columns, committed once per id.
    assert_preprocessed_id_content_invariant(modules);
    let module_preprocessed_ids: Vec<Vec<PreProcessedColumnId>> = modules
        .iter()
        .map(|m| m.preprocessed_column_ids())
        .collect();
    let (preprocessed_ids, selected_preprocessed_ids) =
        select_first_preprocessed_ids(&module_preprocessed_ids);
    let mut tb = commitment_scheme.tree_builder();
    for (module, selected_ids) in modules.iter_mut().zip(&selected_preprocessed_ids) {
        module.write_selected_preprocessed(&mut tb, selected_ids);
    }
    tb.commit(channel);

    for m in modules.iter() {
        m.mix_public(channel);
    }

    // Tree 1: every module's witness + multiplicity columns.
    let mut tb = commitment_scheme.tree_builder();
    for m in modules.iter_mut() {
        m.write_trace(&mut tb);
    }
    tb.commit(channel);

    for m in modules.iter_mut() {
        m.draw_relations(channel);
    }

    // Tree 2: every module's interaction columns. Claimed sums are mixed before
    // the commit, matching the standalone transcript order.
    let mut tb = commitment_scheme.tree_builder();
    for m in modules.iter_mut() {
        m.write_interaction(&mut tb);
    }
    for m in modules.iter() {
        m.mix_claimed_sums(channel);
    }
    tb.commit(channel);

    // Optional transcript block after tree 2. GKR lookup proofs use this block.
    // Trees 1 and 2 already commit their inputs and relation draws.
    // MLE tie-back columns follow the GKR proof messages.
    // The verifier uses the same Fiat-Shamir order.
    for m in modules.iter_mut() {
        m.prove_post_interaction(channel);
    }
    if modules
        .iter()
        .any(|m| !m.post_interaction_log_sizes().is_empty())
    {
        let mut tb = commitment_scheme.tree_builder();
        for m in modules.iter_mut() {
            m.write_post_interaction(&mut tb);
        }
        tb.commit(channel);
    }

    // Build every module's components with one shared allocator.
    // Seed it with unique preprocessed column IDs. A repeated deterministic table
    // resolves to the first matching ID. This keeps the static allocator defined
    // for repeated modules.
    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&preprocessed_ids);
    for m in modules.iter_mut() {
        m.build_components(&mut allocator);
    }
    let component_refs: Vec<&dyn ComponentProver<SimdBackend>> =
        modules.iter().flat_map(|m| m.prover_components()).collect();
    let proof = stark_prove::<SimdBackend, Mc>(&component_refs, channel, commitment_scheme)?;
    Ok(proof)
}

/// Errors from [`verify_with_expected_preprocessed_root`].
#[derive(Debug)]
pub enum VerifyError {
    /// The proof's tree-0 (preprocessed) commitment root does not equal the
    /// verifier-derived expected root. Rejected fail-closed, before any
    /// transcript or STARK work — a forged preprocessed table (range table,
    /// schedule, constant column) never reaches the STARK verifier.
    PreprocessedRootMismatch {
        /// The tree-0 root embedded in the proof (`proof.commitments[0]`).
        got: CommitmentRoot,
        /// The root the verifier derived independently.
        expected: CommitmentRoot,
    },
    /// The underlying STARK verifier rejected the proof.
    Stark(VerificationError),
}

impl From<VerificationError> for VerifyError {
    fn from(error: VerificationError) -> Self {
        Self::Stark(error)
    }
}

/// Shape key for the preprocessed-root cache.
///
/// The key contains the deduplicated `(column id, log_size)` list in tree-0
/// commit order. It also contains the FRI blowup factor.
/// The Merkle root depends on this factor because it commits the LDE.
/// The cache stores the full key and does not hash it.
type PreprocessedShapeKey = (Vec<(String, u32)>, u32);

static PREPROCESSED_ROOT_CACHE: OnceLock<Mutex<HashMap<PreprocessedShapeKey, CommitmentRoot>>> =
    OnceLock::new();

/// Computes the expected tree-0 commitment root for a module set.
///
/// This function uses the same tree-0 path as [`prove`].
/// It deduplicates preprocessed IDs in first-writer order.
/// Then, it commits the selected columns with a new commitment scheme.
/// Production verifiers use trusted module data to compute this root.
/// They pass the result to [`verify_with_expected_preprocessed_root`].
///
/// A process-global map caches one root for each shape.
/// A shape contains ordered unique `(id, log_size)` entries and the FRI blowup.
/// The cache assumes that each preprocessed column ID determines its content.
/// [`prove`] enforces the same invariant.
/// Call this function only with trusted verifier modules.
///
/// # Soundness
///
/// This root pin is the soundness anchor for tree 0.
/// The Blake2s Merkle root binds each preprocessed column.
/// It binds the column content, order, and size.
/// `PreprocessedColumnFingerprint` is only a development deduplication guard.
/// It uses a 64-bit `DefaultHasher` and is not a soundness pin.
pub fn compute_preprocessed_root(
    modules: &mut [&mut dyn AirProver],
    config: PcsConfig,
) -> CommitmentRoot {
    let module_preprocessed_ids: Vec<Vec<PreProcessedColumnId>> = modules
        .iter()
        .map(|m| m.preprocessed_column_ids())
        .collect();
    let module_preprocessed_sizes: Vec<Vec<u32>> =
        modules.iter().map(|m| m.layout().preprocessed).collect();

    // The shape key mirrors the tree-0 dedup: unique (id, log_size) in commit
    // order. Module identity is positional — the ordered list pins it.
    let mut seen = HashSet::new();
    let mut unique_columns = Vec::new();
    for (ids, sizes) in module_preprocessed_ids
        .iter()
        .zip(&module_preprocessed_sizes)
    {
        assert_eq!(
            ids.len(),
            sizes.len(),
            "preprocessed ids and layout sizes must have the same length"
        );
        for (id, size) in ids.iter().zip(sizes) {
            if seen.insert(id.clone()) {
                unique_columns.push((id.id.clone(), *size));
            }
        }
    }
    let key: PreprocessedShapeKey = (unique_columns, config.fri_config.log_blowup_factor);

    let cache = PREPROCESSED_ROOT_CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    if let Some(root) = cache
        .lock()
        .expect("preprocessed root cache poisoned")
        .get(&key)
    {
        return *root;
    }

    let root = compute_preprocessed_root_uncached(modules, config);

    cache
        .lock()
        .expect("preprocessed root cache poisoned")
        .insert(key, root);
    root
}

/// [`compute_preprocessed_root`] without the per-shape cache: every call
/// rebuilds and commits tree 0.
///
/// Use this function when a column ID does not determine its content.
///
/// P256 hinted-multiplication schedule columns reuse one ID across witnesses,
/// while their content depends on the signature. The cached function would
/// return the first witness root for later witnesses and cause a fail-closed
/// completeness error.
/// Use the cached function only when the [`prove`] ID-to-content invariant holds.
pub fn compute_preprocessed_root_uncached(
    modules: &mut [&mut dyn AirProver],
    config: PcsConfig,
) -> CommitmentRoot {
    let module_preprocessed_ids: Vec<Vec<PreProcessedColumnId>> = modules
        .iter()
        .map(|m| m.preprocessed_column_ids())
        .collect();

    // Exactly the prove()-side tree-0 path: interpolate + blow up + Merkle
    // commit the deduplicated preprocessed columns. The twiddles only need to
    // cover the largest committed LDE domain (tree 0 is the only tree built).
    let max_preprocessed_log_size = modules
        .iter()
        .flat_map(|m| m.layout().preprocessed)
        .max()
        .unwrap_or(0);
    let twiddles = cached_twiddles(max_preprocessed_log_size + config.fri_config.log_blowup_factor);
    let channel = &mut Ch::default();
    config.mix_into(channel);
    let mut commitment_scheme = CommitmentSchemeProver::<SimdBackend, Mc>::new(config, twiddles);
    let (_, selected_preprocessed_ids) = select_first_preprocessed_ids(&module_preprocessed_ids);
    let mut tb = commitment_scheme.tree_builder();
    for (module, selected_ids) in modules.iter_mut().zip(&selected_preprocessed_ids) {
        module.write_selected_preprocessed(&mut tb, selected_ids);
    }
    tb.commit(channel);
    commitment_scheme.roots()[0]
}

/// Maximum preprocessed column log size for one module.
///
/// [`compute_canonical_preprocessed_root`] checks this limit before it allocates
/// the twiddle table. Production modules remain well below this limit.
/// The SHA Maj/Ch table has log size 18 at the production width.
///
/// Doubled range and split tables have log size 17.
/// Typical SHA selectors have log size 15.
/// The P256 and binding modules are smaller.
/// This limit prevents an untrusted shape from forcing a large tree-0 rebuild.
pub const MAX_CANONICAL_PREPROCESSED_LOG_SIZE: u32 = 25;

/// Reconstruct and commit tree 0 from verifier-side canonical module data.
/// Columns use the same first-writer-wins deduplication order as [`prove`]. No
/// witness value or prover-supplied commitment enters this computation.
pub fn compute_canonical_preprocessed_root(
    modules: &mut [&mut dyn Air],
    config: PcsConfig,
) -> Result<CommitmentRoot, VerificationError> {
    for module in modules.iter() {
        module.validate_structure()?;
    }
    let max_preprocessed_log_size = modules
        .iter()
        .flat_map(|module| module.layout().preprocessed)
        .max()
        .unwrap_or(0);
    // Check the limit before twiddle or LDE allocation.
    // An untrusted module log size controls the twiddle table and each rebuilt
    // column. An unlimited value could exhaust verifier memory.
    if max_preprocessed_log_size > MAX_CANONICAL_PREPROCESSED_LOG_SIZE {
        return Err(VerificationError::InvalidStructure(format!(
            "preprocessed log size {max_preprocessed_log_size} exceeds the canonical maximum \
             {MAX_CANONICAL_PREPROCESSED_LOG_SIZE}"
        )));
    }
    let twiddles = cached_twiddles(max_preprocessed_log_size + config.fri_config.log_blowup_factor);
    let channel = &mut Ch::default();
    config.mix_into(channel);
    let mut commitment_scheme = CommitmentSchemeProver::<SimdBackend, Mc>::new(config, twiddles);
    let mut tree_builder = commitment_scheme.tree_builder();
    let mut seen = HashSet::new();

    for module in modules.iter_mut() {
        let ids = module.preprocessed_column_ids();
        let log_sizes = module.layout().preprocessed;
        let columns = module.canonical_preprocessed_columns()?;
        if ids.len() != columns.len() || ids.len() != log_sizes.len() {
            return Err(VerificationError::InvalidStructure(
                "canonical preprocessed ids, columns, and layout differ in length".into(),
            ));
        }
        let mut selected = Vec::new();
        for ((id, column), log_size) in ids.into_iter().zip(columns).zip(log_sizes) {
            if column.domain.log_size() != log_size {
                return Err(VerificationError::InvalidStructure(
                    "canonical preprocessed column has the wrong log size".into(),
                ));
            }
            if seen.insert(id) {
                selected.push(column);
            }
        }
        tree_builder.extend_evals(selected);
    }
    tree_builder.commit(channel);
    Ok(commitment_scheme.roots()[0])
}

/// Re-derive the transcript for every module and verify the single STARK proof.
///
/// Equivalent to [`verify_with_expected_preprocessed_root`] with `None`: the
/// tree-0 root is absorbed from the proof without a content check. Production
/// callers must independently reconstruct or pin the root via the pinned entry
/// point.
pub fn verify(
    modules: &mut [&mut dyn Air],
    proof: &StarkProof<Hasher>,
) -> Result<(), VerificationError> {
    verify_with_expected_preprocessed_root(modules, proof, None).map_err(|error| match error {
        VerifyError::Stark(error) => error,
        VerifyError::PreprocessedRootMismatch { .. } => {
            unreachable!("no expected root was supplied")
        }
    })
}

/// [`verify`], with the tree-0 (preprocessed) commitment root pinned.
///
/// With `Some(expected)`, the proof tree-0 root must equal `expected`.
/// The function checks this value before it absorbs the root.
/// A forged preprocessed tree causes [`VerifyError::PreprocessedRootMismatch`].
/// Callers obtain `expected` from trusted module data or a pinned profile value.
///
/// # Soundness
///
/// This pin is the tree-0 soundness anchor: the Blake2s Merkle root binds the
/// contents, order, and sizes of every preprocessed column cryptographically.
/// The prover-side 64-bit `DefaultHasher` fingerprint guard
/// (`PreprocessedColumnFingerprint`) does not provide a soundness pin.
/// Do not substitute it for this check.
/// Use `None` only for shape tests that do not pin tree 0.
pub fn verify_with_expected_preprocessed_root(
    modules: &mut [&mut dyn Air],
    proof: &StarkProof<Hasher>,
    expected_preprocessed_root: Option<CommitmentRoot>,
) -> Result<(), VerifyError> {
    for module in modules.iter() {
        module.validate_structure()?;
    }
    if let Some(expected) = expected_preprocessed_root {
        let got = proof.commitments[0];
        if got != expected {
            return Err(VerifyError::PreprocessedRootMismatch { got, expected });
        }
    }

    let config = proof.config;
    let channel = &mut Ch::default();
    config.mix_into(channel);

    let commitment_scheme = &mut CommitmentSchemeVerifier::<Mc>::new(config);

    // Tree 0: deterministic preprocessed columns, committed once per id.
    let preprocessed_sizes = unique_preprocessed_layout(
        modules
            .iter()
            .map(|m| (m.preprocessed_column_ids(), m.layout().preprocessed)),
    );
    commitment_scheme.commit(proof.commitments[0], &preprocessed_sizes, channel);

    for m in modules.iter() {
        m.mix_public(channel);
    }

    // Tree 1: witness + multiplicity columns of every module.
    let trace_sizes: Vec<u32> = modules.iter().flat_map(|m| m.layout().trace).collect();
    commitment_scheme.commit(proof.commitments[1], &trace_sizes, channel);

    for m in modules.iter_mut() {
        m.draw_relations(channel);
    }

    // Global LogUp balance: every yield (+) must be matched by a require (-)
    // across all modules.
    let claimed_sums: Vec<QM31> = modules.iter().flat_map(|m| m.claimed_sums()).collect();
    if claimed_sums.iter().fold(QM31::zero(), |acc, &s| acc + s) != QM31::zero() {
        return Err(
            VerificationError::InvalidStructure("LogUp claimed sums do not cancel".into()).into(),
        );
    }

    for m in modules.iter() {
        m.mix_claimed_sums(channel);
    }

    // Tree 2: interaction columns of every module.
    let interaction_sizes: Vec<u32> = modules
        .iter()
        .flat_map(|m| m.layout().interaction)
        .collect();
    commitment_scheme.commit(proof.commitments[2], &interaction_sizes, channel);

    for m in modules.iter_mut() {
        m.verify_post_interaction(channel)?;
    }
    let post_interaction_sizes: Vec<u32> = modules
        .iter()
        .flat_map(|m| m.post_interaction_log_sizes())
        .collect();
    if !post_interaction_sizes.is_empty() {
        commitment_scheme.commit(proof.commitments[3], &post_interaction_sizes, channel);
    }

    // Build every module's components with the prover's shared allocator seed.
    // Then collect borrowed component references for verification.
    let preprocessed_ids =
        unique_preprocessed_ids(modules.iter().flat_map(|m| m.preprocessed_column_ids()));
    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&preprocessed_ids);
    for m in modules.iter_mut() {
        m.build_components(&mut allocator);
    }
    let component_refs: Vec<&dyn Component> = modules.iter().flat_map(|m| m.components()).collect();

    Ok(stark_verify(
        &component_refs,
        channel,
        commitment_scheme,
        proof.clone(),
    )?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use stwo::core::fields::m31::M31;
    use stwo::prover::backend::simd::column::BaseColumn;

    struct FingerprintOnlyProver {
        module: &'static str,
        id: PreProcessedColumnId,
        column: PreprocessedColumnEval,
    }

    impl FingerprintOnlyProver {
        fn new(module: &'static str, id: &str, values: &[u32]) -> Self {
            let log_size = values.len().ilog2();
            assert_eq!(1usize << log_size, values.len());
            let domain = CanonicCoset::new(log_size).circle_domain();
            let column = CircleEvaluation::new(
                domain,
                BaseColumn::from_iter(values.iter().copied().map(M31::from_u32_unchecked)),
            );
            Self {
                module,
                id: PreProcessedColumnId { id: id.to_string() },
                column,
            }
        }
    }

    impl Air for FingerprintOnlyProver {
        fn mix_public(&self, _channel: &mut Ch) {}

        fn draw_relations(&mut self, _channel: &mut Ch) {}

        fn layout(&self) -> TreeLayout {
            TreeLayout {
                preprocessed: vec![self.column.domain.log_size()],
                trace: Vec::new(),
                interaction: Vec::new(),
            }
        }

        fn claimed_sums(&self) -> Vec<QM31> {
            Vec::new()
        }

        fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
            vec![self.id.clone()]
        }

        fn build_components(&mut self, _allocator: &mut TraceLocationAllocator) {}

        fn components(&self) -> Vec<&dyn Component> {
            Vec::new()
        }
    }

    impl AirProver for FingerprintOnlyProver {
        fn max_log_size(&self) -> u32 {
            self.column.domain.log_size()
        }

        fn write_preprocessed(&mut self, _tb: &mut TreeBuilder<SimdBackend, Mc>) {
            unreachable!("invariant tests do not commit columns")
        }

        fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
            fingerprint_preprocessed_columns(
                self.module,
                std::slice::from_ref(&self.id),
                std::slice::from_ref(&self.column),
            )
        }

        fn write_trace(&mut self, _tb: &mut TreeBuilder<SimdBackend, Mc>) {}

        fn write_interaction(&mut self, _tb: &mut TreeBuilder<SimdBackend, Mc>) {}

        fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
            Vec::new()
        }
    }

    #[test]
    fn preprocessed_invariant_accepts_duplicate_id_with_equal_content() {
        let mut first = FingerprintOnlyProver::new("first", "shared", &[1, 2]);
        let mut second = FingerprintOnlyProver::new("second", "shared", &[1, 2]);
        assert_preprocessed_id_content_invariant(&mut [&mut first, &mut second]);
    }

    #[test]
    fn preprocessed_invariant_rejects_duplicate_id_with_different_content() {
        let mut first = FingerprintOnlyProver::new("first", "shared", &[1, 2]);
        let mut second = FingerprintOnlyProver::new("second", "shared", &[1, 3]);

        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            assert_preprocessed_id_content_invariant(&mut [&mut first, &mut second]);
        }))
        .expect_err("duplicate id with different content must panic");
        let message = panic
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| panic.downcast_ref::<&str>().copied())
            .expect("panic has a string message");
        assert!(message.contains("shared"));
        assert!(message.contains("first"));
        assert!(message.contains("second"));
    }

    /// A module that only reports a preprocessed layout log-size — no columns are
    /// ever allocated. Used to prove the shape cap fires *before*
    /// [`compute_canonical_preprocessed_root`] tries to build a tree that large.
    struct ShapeOnlyModule {
        preprocessed_log_size: u32,
    }

    struct InvalidShapeModule;

    impl Air for InvalidShapeModule {
        fn validate_structure(&self) -> Result<(), VerificationError> {
            Err(VerificationError::InvalidStructure(
                "malformed module metadata".to_string(),
            ))
        }

        fn mix_public(&self, _channel: &mut Ch) {}
        fn draw_relations(&mut self, _channel: &mut Ch) {}
        fn layout(&self) -> TreeLayout {
            panic!("layout must not be read before structural validation")
        }
        fn claimed_sums(&self) -> Vec<QM31> {
            panic!("claims must not be read before structural validation")
        }
        fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
            panic!("ids must not be read before structural validation")
        }
        fn build_components(&mut self, _allocator: &mut TraceLocationAllocator) {}
        fn components(&self) -> Vec<&dyn Component> {
            Vec::new()
        }
    }

    impl Air for ShapeOnlyModule {
        fn mix_public(&self, _channel: &mut Ch) {}
        fn draw_relations(&mut self, _channel: &mut Ch) {}
        fn layout(&self) -> TreeLayout {
            TreeLayout {
                preprocessed: vec![self.preprocessed_log_size],
                trace: Vec::new(),
                interaction: Vec::new(),
            }
        }
        fn claimed_sums(&self) -> Vec<QM31> {
            Vec::new()
        }
        fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
            vec![PreProcessedColumnId {
                id: "shape_only".to_string(),
            }]
        }
        fn build_components(&mut self, _allocator: &mut TraceLocationAllocator) {}
        fn components(&self) -> Vec<&dyn Component> {
            Vec::new()
        }
    }

    #[test]
    fn canonical_root_fails_closed_without_reconstruct_override() {
        // Confirm that canonical verification rejects a module without a column
        // reconstruction method. The function must return an error without panic.
        let mut module = ShapeOnlyModule {
            preprocessed_log_size: 4,
        };
        let error = compute_canonical_preprocessed_root(&mut [&mut module], PcsConfig::default())
            .expect_err("a module without a reconstruct override must fail closed");
        match error {
            VerificationError::InvalidStructure(message) => {
                assert!(
                    message.contains("cannot reconstruct"),
                    "unexpected message: {message}"
                );
            }
            other => panic!("expected InvalidStructure, got {other:?}"),
        }
    }

    #[test]
    fn canonical_root_rejects_module_structure_before_reading_layout() {
        let mut module = InvalidShapeModule;
        let error = compute_canonical_preprocessed_root(&mut [&mut module], PcsConfig::default())
            .expect_err("malformed module metadata must reject");
        assert!(matches!(
            error,
            VerificationError::InvalidStructure(message)
                if message == "malformed module metadata"
        ));
    }

    #[test]
    fn canonical_root_rejects_oversized_preprocessed_shape() {
        // Reject an oversized shape before twiddle allocation.
        // A late check would exhaust memory.
        let mut module = ShapeOnlyModule {
            preprocessed_log_size: MAX_CANONICAL_PREPROCESSED_LOG_SIZE + 1,
        };
        let error = compute_canonical_preprocessed_root(&mut [&mut module], PcsConfig::default())
            .expect_err("an oversized preprocessed shape must be rejected");
        match error {
            VerificationError::InvalidStructure(message) => {
                assert!(
                    message.contains("exceeds the canonical maximum"),
                    "unexpected message: {message}"
                );
            }
            other => panic!("expected InvalidStructure, got {other:?}"),
        }
    }

    use stwo::prover::backend::simd::qm31::PackedQM31;
    use stwo_constraint_framework::{
        relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
        RelationEntry,
    };

    relation!(TableRelation, 1);

    /// Minimal provable fixture for the preprocessed-root pin: one preprocessed
    /// "table" column and one trace column constrained equal to it. A doctored
    /// prover that alters a table cell (and its matching trace cell) satisfies
    /// every constraint — exactly the F-ROOT attack the root pin must reject.
    /// The zero-numerator logup entry only gives the module a real interaction
    /// column (the shared STARK requires a non-degenerate tree structure). It
    /// contributes nothing to any sum.
    #[derive(Clone)]
    struct TableEval {
        log_size: u32,
        id: PreProcessedColumnId,
        relation: TableRelation,
    }

    impl FrameworkEval for TableEval {
        fn log_size(&self) -> u32 {
            self.log_size
        }

        fn max_constraint_log_degree_bound(&self) -> u32 {
            self.log_size + 1
        }

        fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
            let table = eval.get_preprocessed_column(self.id.clone());
            let value = eval.next_trace_mask();
            eval.add_constraint(value.clone() - table);
            eval.add_to_relation(RelationEntry::new(&self.relation, E::EF::zero(), &[value]));
            eval.finalize_logup();
            eval
        }
    }

    struct TableModule {
        id: PreProcessedColumnId,
        log_size: u32,
        values: Vec<M31>,
        relation: Option<TableRelation>,
        component: Option<FrameworkComponent<TableEval>>,
    }

    impl TableModule {
        /// `tweak` alters one table cell — the doctored (F-ROOT attacking)
        /// prover, whose trace matches its forged table so constraints hold.
        fn new(id: &str, log_size: u32, tweak: Option<(usize, u32)>) -> Self {
            let mut values: Vec<M31> = (0..1u32 << log_size).map(M31::from_u32_unchecked).collect();
            if let Some((index, value)) = tweak {
                values[index] = M31::from_u32_unchecked(value);
            }
            Self {
                id: PreProcessedColumnId { id: id.to_string() },
                log_size,
                values,
                relation: None,
                component: None,
            }
        }

        fn column(&self) -> PreprocessedColumnEval {
            CircleEvaluation::new(
                CanonicCoset::new(self.log_size).circle_domain(),
                BaseColumn::from_iter(self.values.iter().copied()),
            )
        }
    }

    impl Air for TableModule {
        fn mix_public(&self, _channel: &mut Ch) {}

        fn draw_relations(&mut self, channel: &mut Ch) {
            self.relation = Some(TableRelation::draw(channel));
        }

        fn layout(&self) -> TreeLayout {
            TreeLayout {
                preprocessed: vec![self.log_size],
                trace: vec![self.log_size],
                interaction: vec![self.log_size; 4],
            }
        }

        fn claimed_sums(&self) -> Vec<QM31> {
            Vec::new()
        }

        fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
            vec![self.id.clone()]
        }

        fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
            self.component = Some(FrameworkComponent::new(
                allocator,
                TableEval {
                    log_size: self.log_size,
                    id: self.id.clone(),
                    relation: self.relation.clone().expect("relation is drawn"),
                },
                QM31::zero(),
            ));
        }

        fn components(&self) -> Vec<&dyn Component> {
            vec![self.component.as_ref().expect("component is built")]
        }
    }

    impl AirProver for TableModule {
        fn max_log_size(&self) -> u32 {
            self.log_size
        }

        fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, Mc>) {
            tb.extend_evals(vec![self.column()]);
        }

        fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
            fingerprint_preprocessed_columns(
                "table",
                std::slice::from_ref(&self.id),
                &[self.column()],
            )
        }

        fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, Mc>) {
            // The trace equals the (possibly forged) table, so the equality
            // constraint holds for honest and doctored provers alike.
            tb.extend_evals(vec![self.column()]);
        }

        fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, Mc>) {
            let relation = self.relation.clone().expect("relation is drawn");
            let column = self.column();
            let mut logup = LogupTraceGenerator::new(self.log_size);
            logup.col_from_fn(|vec_row| {
                (
                    PackedQM31::zero(),
                    relation.combine(&[column.data[vec_row]]),
                )
            });
            let (trace, claimed_sum) = logup.finalize_last();
            assert_eq!(claimed_sum, QM31::zero());
            tb.extend_evals(trace);
        }

        fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
            vec![self.component.as_ref().expect("component is built")]
        }
    }

    const TABLE_LOG_SIZE: u32 = 4;

    fn honest_provers() -> (TableModule, TableModule) {
        (
            TableModule::new("froot/a", TABLE_LOG_SIZE, None),
            TableModule::new("froot/b", TABLE_LOG_SIZE, None),
        )
    }

    fn honest_root() -> CommitmentRoot {
        let (mut a, mut b) = honest_provers();
        compute_preprocessed_root(&mut [&mut a, &mut b], PcsConfig::default())
    }

    fn prove_tables(a: &mut TableModule, b: &mut TableModule) -> StarkProof<Hasher> {
        prove(&mut [&mut *a, &mut *b], PcsConfig::default()).expect("table fixture proves")
    }

    fn verify_tables_pinned(
        proof: &StarkProof<Hasher>,
        expected_root: Option<CommitmentRoot>,
    ) -> Result<(), VerifyError> {
        let (mut a, mut b) = honest_provers();
        verify_with_expected_preprocessed_root(&mut [&mut a, &mut b], proof, expected_root)
    }

    /// Confirms that unpinned and pinned verification accept an honest proof.
    /// The pinned check uses an independently computed root.
    #[test]
    fn preprocessed_root_pin_accepts_honest_proof() {
        let (mut a, mut b) = honest_provers();
        let proof = prove_tables(&mut a, &mut b);

        let (mut va, mut vb) = honest_provers();
        verify(&mut [&mut va, &mut vb], &proof).expect("unpinned verify accepts");
        verify_tables_pinned(&proof, None).expect("None pin keeps the old behavior");
        verify_tables_pinned(&proof, Some(honest_root())).expect("pinned verify accepts");
    }

    /// A doctored proof whose tree-0 root field is tampered is rejected with
    /// `PreprocessedRootMismatch` before any STARK work.
    #[test]
    fn preprocessed_root_pin_rejects_tampered_commitment() {
        let (mut a, mut b) = honest_provers();
        let mut proof = prove_tables(&mut a, &mut b);
        proof.0.commitments[0].0[0] ^= 1;

        match verify_tables_pinned(&proof, Some(honest_root())) {
            Err(VerifyError::PreprocessedRootMismatch { got, expected }) => {
                assert_eq!(got, proof.0.commitments[0]);
                assert_eq!(expected, honest_root());
            }
            other => panic!("expected PreprocessedRootMismatch, got {other:?}"),
        }
    }

    /// THE F-ROOT attack: a doctored prover alters one preprocessed table cell
    /// (and its matching trace cell) and commits honestly over the forged data.
    /// Every constraint holds, so the unpinned verifier accepts the forged
    /// table — the audited gap. The root pin closes it.
    #[test]
    fn preprocessed_root_pin_closes_the_froot_attack() {
        let mut evil_a = TableModule::new("froot/a", TABLE_LOG_SIZE, Some((7, 999)));
        let mut evil_b = TableModule::new("froot/b", TABLE_LOG_SIZE, None);
        let forged_proof = prove_tables(&mut evil_a, &mut evil_b);

        // Without the pin the forged table verifies: the verifier derives only
        // the layout, never the content. This is the F-ROOT finding.
        let (mut va, mut vb) = honest_provers();
        verify(&mut [&mut va, &mut vb], &forged_proof)
            .expect("unpinned verify accepts the forged table (the F-ROOT gap)");

        // With the pin the forged tree-0 root differs from the derived one.
        match verify_tables_pinned(&forged_proof, Some(honest_root())) {
            Err(VerifyError::PreprocessedRootMismatch { got, expected }) => {
                assert_ne!(got, expected);
            }
            other => panic!("expected PreprocessedRootMismatch, got {other:?}"),
        }
    }

    /// Shape-key discrimination: different shapes get different cache entries
    /// and different roots, and shape A's root rejects a proof at shape B.
    #[test]
    fn preprocessed_root_cache_discriminates_shapes() {
        let root_a = honest_root();

        // Same ids, larger tables — a different shape, and a different root.
        let taller = || {
            (
                TableModule::new("froot/a", TABLE_LOG_SIZE + 1, None),
                TableModule::new("froot/b", TABLE_LOG_SIZE + 1, None),
            )
        };
        let (mut ta, mut tb_) = taller();
        let root_b = compute_preprocessed_root(&mut [&mut ta, &mut tb_], PcsConfig::default());
        assert_ne!(root_a, root_b, "distinct shapes must yield distinct roots");

        // The cache returns stable per-shape roots on a second computation.
        let (mut ta2, mut tb2) = taller();
        assert_eq!(
            compute_preprocessed_root(&mut [&mut ta2, &mut tb2], PcsConfig::default()),
            root_b
        );

        // A proof at shape B never matches shape A's root.
        let (mut pa, mut pb) = taller();
        let proof_b = prove_tables(&mut pa, &mut pb);
        let (mut va, mut vb) = taller();
        match verify_with_expected_preprocessed_root(
            &mut [&mut va, &mut vb],
            &proof_b,
            Some(root_a),
        ) {
            Err(VerifyError::PreprocessedRootMismatch { got, expected }) => {
                assert_eq!(got, root_b);
                assert_eq!(expected, root_a);
            }
            other => panic!("expected PreprocessedRootMismatch, got {other:?}"),
        }
    }
}
