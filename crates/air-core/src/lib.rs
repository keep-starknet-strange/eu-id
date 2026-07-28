//! Combines one or more proving modules into a single STARK proof.
//!
//! Each circuit implements [`Air`] and [`AirProver`]. A module does NOT own the
//! channel or the commitment scheme; it only contributes columns and components
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
//! A single combined proof has exactly one channel and one commitment scheme,
//! so every module must agree on one hash. That choice lives here once, behind
//! the [`Mc`]/[`Ch`]/[`Hasher`] aliases, rather than as a generic parameter
//! threaded through every module: genericity at the module level buys nothing
//! when all modules in a `prove` call must use the identical channel anyway.
//! Switching the system to a different (e.g. Stwo-friendly) hash is a one-line
//! change to these aliases.

pub mod gkr;
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
    let mut cache = cache.lock().expect("twiddle cache poisoned");
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

/// Process-cached FFT twiddles covering circle domains up to `2^log_size`.
/// Exposed for modules that build post-interaction (tree-3) components which
/// interpolate/evaluate polynomials outside the orchestrator's own tree, e.g.
/// the keccak_round GKR tie-back's `MleEvalProverComponent`.
pub fn twiddles(log_size: u32) -> &'static TwiddleTree<SimdBackend> {
    cached_twiddles(log_size)
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

/// What both the prover and the verifier need from a module: bind the public
/// input, draw the module's lookup relations, declare its column layout, expose
/// its claimed LogUp sums, and assemble its AIR components.
pub trait Air {
    /// Bind this module's public statement to the shared transcript.
    fn mix_public(&self, channel: &mut Ch);

    /// Draw this module's lookup relations from the shared channel and stash
    /// them for the interaction phase and component assembly.
    fn draw_relations(&mut self, channel: &mut Ch);

    /// Column log-sizes per tree, in commit order.
    fn layout(&self) -> TreeLayout;

    /// The module's claimed LogUp sums whose total enters the global balance.
    /// The orchestrator sums these across all modules and rejects unless the
    /// total is zero. For most modules these are the per-component sums; a
    /// module whose balance also folds in public-input/provider terms returns
    /// those terms here too.
    fn claimed_sums(&self) -> Vec<QM31>;

    /// Mix this module's claimed-sum commitment into the transcript, just before
    /// the interaction tree is committed. The default mixes [`Air::claimed_sums`]
    /// as one flat felt slice. A module whose standalone transcript mixed a
    /// richer structure (for example per-component claims plus native counts) can
    /// override to reproduce it exactly. Must match between prove and verify.
    fn mix_claimed_sums(&self, channel: &mut Ch) {
        channel.mix_felts(&self.claimed_sums());
    }

    /// The preprocessed column ids this module contributes to tree 0, in commit
    /// order. The orchestrator concatenates these across all modules to seed the
    /// single shared [`TraceLocationAllocator`] before building components.
    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId>;

    /// Canonical tree-0 columns in the same order as
    /// [`Air::preprocessed_column_ids`]. Production verification uses these
    /// verifier-side values to reconstruct commitment 0 instead of trusting a
    /// caller-supplied root.
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

    /// Build this module's AIR components against the shared allocator and stash
    /// them. Called once, in module order, after relations are drawn and the
    /// allocator is seeded. A module owns its components and lends them out via
    /// [`Air::components`] / [`AirProver::prover_components`] — matching Stwo's
    /// borrowed-component prove/verify API and avoiding any rebuild.
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

    /// Hand this module the opaque post-interaction payload the prover emitted
    /// for it (a serialized GKR proof, typically). Called by the orchestrator
    /// once, before [`Air::verify_post_interaction`], only on the
    /// payload-carrying verify path. Modules that offload a LogUp into GKR stash
    /// the bytes here and deserialize them in `verify_post_interaction`; modules
    /// without a payload ignore it.
    fn load_post_interaction_payload(&mut self, _payload: &[u8]) {}
}

/// The prover-only extension: a module that holds a witness and can write its
/// actual columns into the shared commitment trees.
pub trait AirProver: Air {
    /// Largest trace log-size this module uses; the orchestrator takes the max
    /// over all modules to size the FRI twiddles.
    fn max_log_size(&self) -> u32;

    /// Largest constraint-evaluation log-degree this module needs the twiddle
    /// domain to cover. The orchestrator takes the max over all modules and adds
    /// the FRI blow-up to size the precomputed twiddles (unless the config pins
    /// an explicit `lifting_log_size`).
    ///
    /// The default — `max_log_size() + 1` — is exactly the domain a degree-2 AIR
    /// needs, which is what the predicate and SHA modules use. A module with
    /// higher-degree constraints overrides this with the real bound computed
    /// from its components.
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.max_log_size() + 1
    }

    /// Whether the commitment scheme must retain committed polynomials in
    /// coefficient form (`set_store_polynomials_coefficients`). Off by default;
    /// modules that need coefficient-form openings turn it on. If any module in a
    /// `prove` call needs it, the orchestrator enables it for the whole proof.
    fn store_polynomial_coefficients(&self) -> bool {
        false
    }

    /// Phase 0 — append preprocessed columns to the shared tree.
    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, Mc>);

    /// Fingerprint preprocessed column content before tree-0 dedup. Equal
    /// preprocessed IDs must imply equal fixed-column content; otherwise
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

    /// Phase 0 variant used when another earlier module already committed some
    /// deterministic preprocessed columns with the same IDs.
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

    /// Phase 1 — append main witness + multiplicity columns to the shared tree.
    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, Mc>);

    /// Phase 2 — build the interaction (LogUp) columns from the drawn relations,
    /// append them, and stash this module's claimed sums (read back via
    /// [`Air::claimed_sums`]).
    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, Mc>);

    /// Optional prover-side post-interaction transcript work, run after tree 2
    /// is committed. Any proof messages mixed here are therefore bound to all
    /// committed GKR inputs: trace/multiplicity columns, relation randomness,
    /// claimed sums, and interaction columns.
    fn prove_post_interaction(&mut self, _channel: &mut Ch) {}

    /// Optional phase 3 — append post-interaction tie-back columns.
    fn write_post_interaction(&mut self, _tb: &mut TreeBuilder<SimdBackend, Mc>) {}

    /// Hand the orchestrator this module's opaque post-interaction payload — the
    /// serialized GKR proof produced during [`AirProver::prove_post_interaction`]
    /// — to travel beside the [`StarkProof`]. Called once, after
    /// `prove_post_interaction`. The default (no offload) returns an empty
    /// payload, which the orchestrator treats as "no GKR proof for this module".
    fn take_post_interaction_payload(&mut self) -> Vec<u8> {
        Vec::new()
    }

    /// Borrow the built prover-side components, in commit order. Call only
    /// after [`Air::build_components`].
    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>>;
}

/// Drive every module through the four phases against one shared channel and one
/// shared commitment scheme, producing a single STARK proof.
///
/// Convenience wrapper over [`prove_with_post_interaction`] for the common case
/// of modules that emit no GKR payload. Panics (debug) if any module actually
/// produced one — such a module must be proven via
/// [`prove_with_post_interaction`] so its blob reaches the verifier.
pub fn prove(
    modules: &mut [&mut dyn AirProver],
    config: PcsConfig,
) -> Result<StarkProof<Hasher>, ProvingError> {
    let (proof, payloads) = prove_with_post_interaction(modules, config)?;
    debug_assert!(
        payloads.iter().all(Vec::is_empty),
        "a module emitted a GKR post-interaction payload; use prove_with_post_interaction"
    );
    Ok(proof)
}

fn report_prove_phase(timing: bool, name: &str, t_last: &mut std::time::Instant) {
    if timing {
        eprintln!("air-core prove phase {name}: {:?}", t_last.elapsed());
        *t_last = std::time::Instant::now();
    }
}

fn dump_shape_census_if_requested(modules: &[&mut dyn AirProver]) {
    if std::env::var_os("AIR_CORE_SHAPE_DUMP").is_none() {
        return;
    }
    for (index, module) in modules.iter().enumerate() {
        let layout = module.layout();
        for (tree, sizes) in [
            ("preprocessed", &layout.preprocessed),
            ("trace", &layout.trace),
            ("interaction", &layout.interaction),
        ] {
            let mut hist = std::collections::BTreeMap::<u32, usize>::new();
            for &s in sizes.iter() {
                *hist.entry(s).or_insert(0) += 1;
            }
            let cells: u64 = sizes.iter().map(|&s| 1u64 << s).sum();
            eprintln!(
                "air-core shape module={index} tree={tree} cols={} cells={cells} hist={hist:?}",
                sizes.len()
            );
        }
    }
}

/// [`prove`], additionally returning each module's opaque post-interaction
/// payload (a serialized GKR proof, or empty). The payloads are indexed by
/// module position and must be handed back — in the same order — to
/// [`verify_with_expected_preprocessed_root_and_payloads`].
pub fn prove_with_post_interaction(
    modules: &mut [&mut dyn AirProver],
    config: PcsConfig,
) -> Result<(StarkProof<Hasher>, Vec<Vec<u8>>), ProvingError> {
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

    let timing = std::env::var_os("AIR_CORE_PROVE_TIMING").is_some();
    let t_start = std::time::Instant::now();
    let mut t_last = t_start;
    dump_shape_census_if_requested(modules);

    let twiddles = cached_twiddles(twiddle_log_size);
    report_prove_phase(timing, "twiddles", &mut t_last);

    let channel = &mut Ch::default();
    config.mix_into(channel);

    let mut commitment_scheme = CommitmentSchemeProver::<SimdBackend, Mc>::new(config, twiddles);
    // If any module needs committed polynomials kept in coefficient form,
    // enable it for the shared scheme.
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
    report_prove_phase(timing, "tree0-write", &mut t_last);
    tb.commit(channel);
    report_prove_phase(timing, "tree0-commit", &mut t_last);

    for m in modules.iter() {
        m.mix_public(channel);
    }

    // Tree 1: every module's witness + multiplicity columns.
    let mut tb = commitment_scheme.tree_builder();
    for m in modules.iter_mut() {
        m.write_trace(&mut tb);
    }
    report_prove_phase(timing, "tree1-write", &mut t_last);
    tb.commit(channel);
    report_prove_phase(timing, "tree1-commit", &mut t_last);

    for m in modules.iter_mut() {
        m.draw_relations(channel);
    }

    // Tree 2: every module's interaction columns. Claimed sums are mixed before
    // the commit, matching the standalone transcript order.
    let mut tb = commitment_scheme.tree_builder();
    for m in modules.iter_mut() {
        m.write_interaction(&mut tb);
    }
    report_prove_phase(timing, "tree2-write", &mut t_last);
    for m in modules.iter() {
        m.mix_claimed_sums(channel);
    }
    tb.commit(channel);
    report_prove_phase(timing, "tree2-commit", &mut t_last);

    // Optional post-tree-2 transcript block. GKR lookup proofs live here:
    // their inputs are already committed (trees 1/2 plus relation draws), and
    // any MLE-eval tie-back columns are committed immediately after the GKR
    // proof messages so the verifier replays the same Fiat-Shamir order.
    for m in modules.iter_mut() {
        m.prove_post_interaction(channel);
    }
    // Collect the opaque per-module GKR payloads now that they have been
    // produced and mixed into the channel. Order matches module order, so the
    // verifier can redistribute them positionally.
    let post_interaction_payloads: Vec<Vec<u8>> = modules
        .iter_mut()
        .map(|m| m.take_post_interaction_payload())
        .collect();
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

    // Build every module's components against one shared allocator seeded with
    // unique preprocessed column ids. Repeated deterministic tables resolve to
    // the first matching id here so the constraint framework's static allocator
    // stays well-defined for repeated modules.
    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&preprocessed_ids);
    for m in modules.iter_mut() {
        m.build_components(&mut allocator);
    }
    let component_refs: Vec<&dyn ComponentProver<SimdBackend>> =
        modules.iter().flat_map(|m| m.prover_components()).collect();
    report_prove_phase(timing, "build-components", &mut t_last);
    let result = stark_prove::<SimdBackend, Mc>(&component_refs, channel, commitment_scheme);
    report_prove_phase(timing, "stark-prove(composition+FRI+open)", &mut t_last);
    if timing {
        eprintln!("air-core prove TOTAL: {:?}", t_start.elapsed());
    }
    result.map(|proof| (proof, post_interaction_payloads))
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

/// Shape key for the preprocessed-root cache: the deduplicated `(column id,
/// log_size)` list in tree-0 commit order, plus the FRI blow-up factor (the
/// Merkle tree commits the blown-up LDE, so the root depends on it). The full
/// key is stored — no key hashing — so cache hits are exact by construction,
/// with no collision surface at all (strictly stronger than hashing the list).
#[cfg(test)]
type PreprocessedShapeKey = (Vec<(String, u32)>, u32);

#[cfg(test)]
static PREPROCESSED_ROOT_CACHE: OnceLock<Mutex<HashMap<PreprocessedShapeKey, CommitmentRoot>>> =
    OnceLock::new();

/// Compute the expected tree-0 (preprocessed) commitment root for a module set,
/// by running exactly the [`prove`]-side tree-0 path: dedup the preprocessed ids
/// first-writer-wins, write the selected columns into a fresh commitment
/// scheme, and commit. Production verifiers compute this once (from their own
/// trusted module constructions — never from prover-supplied data) and pass it
/// to [`verify_with_expected_preprocessed_root`].
///
/// Roots are cached per shape (ordered unique `(id, log_size)` list + FRI
/// blow-up) in a process-global map, so repeated verifies at one shape pay the
/// rebuild once. The cache trusts that a preprocessed column id determines its
/// content — the same invariant [`prove`] enforces via
/// `assert_preprocessed_id_content_invariant` — so only feed this function
/// verifier-side (trusted) module constructions.
///
/// # Soundness
///
/// This root pin is the soundness anchor for tree 0: the Blake2s Merkle root
/// cryptographically binds the contents, order, and sizes of every preprocessed
/// column at once. The prover-side `PreprocessedColumnFingerprint` guard uses a
/// 64-bit `DefaultHasher` and is **NOT** a soundness pin — it is a dev-time
/// dedup guard only. Do not downgrade this pin to that fingerprint.
#[cfg(test)]
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
/// Required whenever a preprocessed column's CONTENT is not determined by its
/// id — e.g. a dynamic preprocessed schedule whose content changes across
/// witnesses while reusing one id. The cached
/// variant would return the first witness's root for every later one (a
/// fail-closed completeness bug, not a soundness one — but a bug). Use the
/// cached variant only where the id→content invariant of [`prove`] holds
/// across every call in the process.
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

/// Reconstruct and commit tree 0 from verifier-side canonical module data.
/// Columns are deduplicated with the exact first-writer-wins ordering used by
/// [`prove`]. No witness values or prover-supplied root enter this path.
pub fn compute_canonical_preprocessed_root(
    modules: &mut [&mut dyn Air],
    config: PcsConfig,
) -> Result<CommitmentRoot, VerificationError> {
    let max_preprocessed_log_size = modules
        .iter()
        .flat_map(|module| module.layout().preprocessed)
        .max()
        .unwrap_or(0);
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
/// callers must pin the root via the pinned entry point — see the F-ROOT
/// finding (tasks/audits/2026-07-05-backend-soundness.md).
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
/// On `Some(expected)`, the proof's `commitments[0]` must equal `expected` —
/// checked BEFORE the root is absorbed into the transcript, so a forged
/// preprocessed tree (range tables, schedules, constants) is rejected
/// fail-closed with [`VerifyError::PreprocessedRootMismatch`]. Callers obtain
/// `expected` from [`compute_preprocessed_root`] over their own trusted module
/// constructions (or from a pinned per-profile constant generated the same
/// way), never from the proof.
///
/// # Soundness
///
/// This pin is the tree-0 soundness anchor: the Blake2s Merkle root binds the
/// contents, order, and sizes of every preprocessed column cryptographically.
/// The prover-side 64-bit `DefaultHasher` fingerprint guard
/// (`PreprocessedColumnFingerprint`) is NOT a soundness pin and must never be
/// substituted for this check. On `None`, the legacy unpinned behavior is kept
/// for shape-exploratory tests only.
pub fn verify_with_expected_preprocessed_root(
    modules: &mut [&mut dyn Air],
    proof: &StarkProof<Hasher>,
    expected_preprocessed_root: Option<CommitmentRoot>,
) -> Result<(), VerifyError> {
    verify_with_expected_preprocessed_root_and_payloads(
        modules,
        proof,
        expected_preprocessed_root,
        &[],
    )
}

/// [`verify_with_expected_preprocessed_root`], additionally threading the
/// per-module post-interaction payloads produced by
/// [`prove_with_post_interaction`]. Each non-empty payload is handed to its
/// module (positional, same order as prove) via
/// [`Air::load_post_interaction_payload`] before the module's
/// [`Air::verify_post_interaction`] runs — that is where a GKR-offloading module
/// replays its proof against the shared channel.
///
/// `post_interaction_payloads` is either empty (no module offloads anything) or
/// exactly one entry per module. Any other length is rejected fail-closed.
pub fn verify_with_expected_preprocessed_root_and_payloads(
    modules: &mut [&mut dyn Air],
    proof: &StarkProof<Hasher>,
    expected_preprocessed_root: Option<CommitmentRoot>,
    post_interaction_payloads: &[Vec<u8>],
) -> Result<(), VerifyError> {
    if !post_interaction_payloads.is_empty() && post_interaction_payloads.len() != modules.len() {
        return Err(VerificationError::InvalidStructure(
            "post-interaction payload count does not match module count".into(),
        )
        .into());
    }
    validate_proof_layout_arity(modules, proof)?;
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

    // Hand each module its opaque payload (if any) before it replays its GKR
    // proof against the shared channel in `verify_post_interaction`.
    if !post_interaction_payloads.is_empty() {
        for (m, payload) in modules.iter_mut().zip(post_interaction_payloads) {
            m.load_post_interaction_payload(payload);
        }
    }
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

    // Build every module's components against one shared allocator (same seeding
    // as the prover), then collect the borrowed component refs to verify.
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

/// Reject malformed commitment-tree arities before entering Stwo verification.
///
/// Stwo's point evaluator assumes that the proof and verifier layouts agree;
/// an arity mismatch can panic while a LogUp evaluator is live and trigger a
/// second panic from its drop guard. Validate the cheap, public proof shape at
/// the air-core boundary so malformed proofs return a typed error instead.
fn validate_proof_layout_arity(
    modules: &[&mut dyn Air],
    proof: &StarkProof<Hasher>,
) -> Result<(), VerificationError> {
    let mut seen_preprocessed = HashSet::new();
    let mut preprocessed = Vec::new();
    for (module_index, module) in modules.iter().enumerate() {
        let ids = module.preprocessed_column_ids();
        let sizes = module.layout().preprocessed;
        if ids.len() != sizes.len() {
            return Err(VerificationError::InvalidStructure(format!(
                "proof layout arity mismatch: module={module_index} tree=preprocessed field=declared_layout expected={} got={}",
                ids.len(),
                sizes.len()
            )));
        }
        for (id, size) in ids.into_iter().zip(sizes) {
            if seen_preprocessed.insert(id) {
                preprocessed.push(size);
            }
        }
    }
    let trace = modules.iter().flat_map(|m| m.layout().trace).collect();
    let interaction = modules
        .iter()
        .flat_map(|m| m.layout().interaction)
        .collect();
    let post_interaction = modules
        .iter()
        .flat_map(|m| m.post_interaction_log_sizes())
        .collect::<Vec<_>>();

    let mut module_trees = vec![
        ("preprocessed", preprocessed),
        ("trace", trace),
        ("interaction", interaction),
    ];
    if !post_interaction.is_empty() {
        module_trees.push(("post-interaction", post_interaction));
    }

    // Stwo appends one composition tree after the module-owned trees.
    let expected_tree_count = module_trees.len() + 1;
    for (field, got) in [
        ("commitments", proof.commitments.len()),
        ("sampled_values", proof.sampled_values.len()),
        ("decommitments", proof.decommitments.len()),
        ("queried_values", proof.queried_values.len()),
    ] {
        if got != expected_tree_count {
            return Err(VerificationError::InvalidStructure(format!(
                "proof layout arity mismatch: module=aggregate tree=all field={field} expected={expected_tree_count} got={got}"
            )));
        }
    }

    for (tree_index, (tree, expected_layout)) in module_trees.iter().enumerate() {
        let expected = expected_layout.len();
        for (field, got) in [
            ("sampled_values", proof.sampled_values[tree_index].len()),
            ("queried_values", proof.queried_values[tree_index].len()),
        ] {
            if got != expected {
                return Err(VerificationError::InvalidStructure(format!(
                    "proof layout arity mismatch: module=aggregate tree={tree} field={field} expected={expected} got={got}"
                )));
            }
        }
    }

    let composition_index = module_trees.len();
    let expected_composition = proof.sampled_values[composition_index].len();
    let got_composition = proof.queried_values[composition_index].len();
    if got_composition != expected_composition {
        return Err(VerificationError::InvalidStructure(format!(
            "proof layout arity mismatch: module=stwo tree=composition field=queried_values expected={expected_composition} got={got_composition}"
        )));
    }

    Ok(())
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
    /// column (the shared STARK requires a non-degenerate tree structure); it
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

    /// Back-compat + happy path: the unpinned `verify` and a `None` pin keep the
    /// old behavior, and the pinned verify accepts the honest proof against the
    /// independently recomputed root.
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

    #[test]
    fn proof_layout_arity_mismatch_is_a_typed_error() {
        let (mut a, mut b) = honest_provers();
        let mut proof = prove_tables(&mut a, &mut b);
        proof.0.sampled_values[2]
            .pop()
            .expect("fixture has interaction columns");
        proof.0.queried_values[2]
            .pop()
            .expect("fixture has interaction columns");

        // Keep the outer catch as an abort detector: before the arity gate, a
        // mismatched proof could panic while a LogUp drop guard was live.
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            verify_tables_pinned(&proof, Some(honest_root()))
        }));
        match result {
            Ok(Err(VerifyError::Stark(VerificationError::InvalidStructure(message)))) => {
                assert!(message.contains("tree=interaction"), "{message}");
                assert!(message.contains("expected=8"), "{message}");
                assert!(message.contains("got=7"), "{message}");
            }
            other => panic!("expected typed interaction-arity error, got {other:?}"),
        }
    }

    #[test]
    fn composition_layout_arity_mismatch_is_a_typed_error() {
        let (mut a, mut b) = honest_provers();
        let mut proof = prove_tables(&mut a, &mut b);
        proof
            .0
            .queried_values
            .last_mut()
            .expect("fixture has a composition tree")
            .pop()
            .expect("composition tree has columns");

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            verify_tables_pinned(&proof, Some(honest_root()))
        }));
        match result {
            Ok(Err(VerifyError::Stark(VerificationError::InvalidStructure(message)))) => {
                assert!(message.contains("tree=composition"), "{message}");
            }
            other => panic!("expected typed composition-arity error, got {other:?}"),
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

    // ------------------------------------------------------------------
    // W1: end-to-end GKR transport through prove/verify with a toy module.
    // ------------------------------------------------------------------

    use num_traits::One;
    use stwo::core::fields::qm31::SecureField;
    use stwo::prover::backend::CpuBackend;
    use stwo::prover::lookups::gkr_prover::{prove_batch, Layer};
    use stwo::prover::lookups::gkr_verifier::{partially_verify_batch, Gate};
    use stwo::prover::lookups::mle::Mle;

    use crate::gkr::{decode_gkr_batch_proof, encode_gkr_batch_proof};

    fn grand_product(values: &[SecureField]) -> SecureField {
        values
            .iter()
            .copied()
            .fold(SecureField::one(), |acc, v| acc * v)
    }

    /// Toy module that carries a trivial one-column STARK (so `air_core::prove`
    /// has real components to open) and, on the side, a GKR grand-product proof
    /// over a private input layer whose product equals a public `claim`.
    ///
    /// This is the W1 plumbing fixture: it exercises the opaque payload
    /// transport and the post-tree-2 Fiat-Shamir binding, without the MLE-eval
    /// tie-back (W2/W3) — so the verifier binds the GKR *output* claim to the
    /// public value directly and trusts the input-layer eval claims.
    struct GkrToyModule {
        id: PreProcessedColumnId,
        log_size: u32,
        relation: Option<TableRelation>,
        component: Option<FrameworkComponent<TableEval>>,
        /// Prover-only witness: the GKR input layer.
        values: Vec<SecureField>,
        /// Public grand-product claim, mixed into the transcript by both sides.
        claim: SecureField,
        /// Prover: filled in `prove_post_interaction`. Verifier: loaded via
        /// `load_post_interaction_payload`.
        gkr_blob: Vec<u8>,
    }

    impl GkrToyModule {
        fn prover(values: Vec<SecureField>) -> Self {
            let claim = grand_product(&values);
            Self::with_claim(values, claim)
        }

        /// A prover that announces a `claim` that need not match its values —
        /// used to drive the wrong-claim negative.
        fn with_claim(values: Vec<SecureField>, claim: SecureField) -> Self {
            Self {
                id: PreProcessedColumnId {
                    id: "gkr_toy".to_string(),
                },
                log_size: 4,
                relation: None,
                component: None,
                values,
                claim,
                gkr_blob: Vec::new(),
            }
        }

        fn verifier(claim: SecureField) -> Self {
            Self::with_claim(Vec::new(), claim)
        }

        fn column(&self) -> PreprocessedColumnEval {
            CircleEvaluation::new(
                CanonicCoset::new(self.log_size).circle_domain(),
                BaseColumn::from_iter((0..1u32 << self.log_size).map(M31::from_u32_unchecked)),
            )
        }
    }

    impl Air for GkrToyModule {
        fn mix_public(&self, channel: &mut Ch) {
            channel.mix_felts(&[self.claim]);
        }

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

        fn load_post_interaction_payload(&mut self, payload: &[u8]) {
            self.gkr_blob = payload.to_vec();
        }

        fn verify_post_interaction(&mut self, channel: &mut Ch) -> Result<(), VerificationError> {
            let proof = decode_gkr_batch_proof(&self.gkr_blob).map_err(|e| {
                VerificationError::InvalidStructure(format!("GKR blob decode failed: {e}"))
            })?;
            // Bind the output claim to the public value BEFORE replaying, so a
            // proof of a different product is rejected even if internally valid.
            let output = proof
                .output_claims_by_instance
                .first()
                .and_then(|c| c.first())
                .copied()
                .ok_or_else(|| {
                    VerificationError::InvalidStructure("GKR proof has no output claim".into())
                })?;
            if output != self.claim {
                return Err(VerificationError::InvalidStructure(
                    "GKR output claim does not match public claim".into(),
                ));
            }
            // Replay against the shared channel: this is the Fiat-Shamir binding
            // to trees 1/2 and the drawn relations. A tampered blob desyncs here.
            partially_verify_batch(vec![Gate::GrandProduct], &proof, channel).map_err(|e| {
                VerificationError::InvalidStructure(format!("GKR verify failed: {e}"))
            })?;
            Ok(())
        }
    }

    impl AirProver for GkrToyModule {
        fn max_log_size(&self) -> u32 {
            self.log_size
        }

        fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, Mc>) {
            tb.extend_evals(vec![self.column()]);
        }

        fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
            fingerprint_preprocessed_columns(
                "gkr_toy",
                std::slice::from_ref(&self.id),
                &[self.column()],
            )
        }

        fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, Mc>) {
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

        fn prove_post_interaction(&mut self, channel: &mut Ch) {
            let layer =
                Layer::GrandProduct(Mle::<CpuBackend, SecureField>::new(self.values.clone()));
            let (proof, _artifact) = prove_batch(channel, vec![layer]);
            self.gkr_blob = encode_gkr_batch_proof(&proof);
        }

        fn take_post_interaction_payload(&mut self) -> Vec<u8> {
            std::mem::take(&mut self.gkr_blob)
        }

        fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
            vec![self.component.as_ref().expect("component is built")]
        }
    }

    #[test]
    fn gkr_transport_round_trips_and_verifies() {
        let values: Vec<SecureField> = (1u32..=16).map(SecureField::from).collect();
        let mut prover = GkrToyModule::prover(values.clone());
        let claim = prover.claim;

        let (proof, payloads) =
            prove_with_post_interaction(&mut [&mut prover], PcsConfig::default())
                .expect("toy GKR proves");
        assert_eq!(payloads.len(), 1);
        assert!(
            !payloads[0].is_empty(),
            "GKR blob must travel in the payload"
        );

        let mut verifier = GkrToyModule::verifier(claim);
        verify_with_expected_preprocessed_root_and_payloads(
            &mut [&mut verifier],
            &proof,
            None,
            &payloads,
        )
        .expect("toy GKR verifies against matching payload");
    }

    #[test]
    fn gkr_transport_rejects_corrupted_blob() {
        let values: Vec<SecureField> = (1u32..=16).map(SecureField::from).collect();
        let mut prover = GkrToyModule::prover(values);
        let claim = prover.claim;

        let (proof, mut payloads) =
            prove_with_post_interaction(&mut [&mut prover], PcsConfig::default())
                .expect("toy GKR proves");
        // Flip a byte deep inside the sumcheck data (past the length prefixes).
        let mid = payloads[0].len() / 2;
        payloads[0][mid] ^= 0xff;

        let mut verifier = GkrToyModule::verifier(claim);
        let result = verify_with_expected_preprocessed_root_and_payloads(
            &mut [&mut verifier],
            &proof,
            None,
            &payloads,
        );
        assert!(result.is_err(), "corrupted GKR blob must be rejected");
    }

    #[test]
    fn gkr_transport_rejects_wrong_claim() {
        // Both sides agree on the public claim `wrong_claim` (so the transcript
        // stays in sync), but it does not equal the true grand product the GKR
        // proof attests to. Only the output-claim binding in
        // `verify_post_interaction` catches the mismatch — isolating it from
        // any transcript divergence.
        let values: Vec<SecureField> = (1u32..=16).map(SecureField::from).collect();
        let true_product = grand_product(&values);
        let wrong_claim = true_product + SecureField::one();
        let mut prover = GkrToyModule::with_claim(values, wrong_claim);

        let (proof, payloads) =
            prove_with_post_interaction(&mut [&mut prover], PcsConfig::default())
                .expect("toy GKR proves");

        let mut verifier = GkrToyModule::verifier(wrong_claim);
        let result = verify_with_expected_preprocessed_root_and_payloads(
            &mut [&mut verifier],
            &proof,
            None,
            &payloads,
        );
        assert!(
            result.is_err(),
            "GKR proof of a different product must be rejected"
        );
    }
}
