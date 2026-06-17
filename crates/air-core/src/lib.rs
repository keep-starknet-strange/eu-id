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

pub mod relations;

use num_traits::Zero;
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo::core::verifier::{verify as stark_verify, VerificationError};
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::PolyOps;
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

    /// Build this module's AIR components against the shared allocator and stash
    /// them. Called once, in module order, after relations are drawn and the
    /// allocator is seeded. A module owns its components and lends them out via
    /// [`Air::components`] / [`AirProver::prover_components`] — matching Stwo's
    /// borrowed-component prove/verify API and avoiding any rebuild.
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator);

    /// Borrow the built verifier-side components, in commit order. Call only
    /// after [`Air::build_components`].
    fn components(&self) -> Vec<&dyn Component>;
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
    /// higher-degree constraints (the P256 ECDSA AIR) overrides this with the
    /// real bound computed from its components.
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.max_log_size() + 1
    }

    /// Whether the commitment scheme must retain committed polynomials in
    /// coefficient form (`set_store_polynomials_coefficients`). Off by default;
    /// the P256 module turns it on for its lifting path. If any module in a
    /// `prove` call needs it, the orchestrator enables it for the whole proof.
    fn store_polynomial_coefficients(&self) -> bool {
        false
    }

    /// Phase 0 — append preprocessed columns to the shared tree.
    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, Mc>);

    /// Phase 1 — append main witness + multiplicity columns to the shared tree.
    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, Mc>);

    /// Phase 2 — build the interaction (LogUp) columns from the drawn relations,
    /// append them, and stash this module's claimed sums (read back via
    /// [`Air::claimed_sums`]).
    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, Mc>);

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

    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(twiddle_log_size)
            .circle_domain()
            .half_coset,
    );

    let channel = &mut Ch::default();
    config.mix_into(channel);

    let mut commitment_scheme = CommitmentSchemeProver::<SimdBackend, Mc>::new(config, &twiddles);
    // If any module needs committed polynomials kept in coefficient form (the
    // P256 lifting path), enable it for the shared scheme.
    if modules.iter().any(|m| m.store_polynomial_coefficients()) {
        commitment_scheme.set_store_polynomials_coefficients();
    }

    // Tree 0: every module's preprocessed columns.
    let mut tb = commitment_scheme.tree_builder();
    for m in modules.iter_mut() {
        m.write_preprocessed(&mut tb);
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

    // Build every module's components against one shared allocator seeded with
    // the concatenated preprocessed column ids (commit order), then collect the
    // borrowed prover-component refs for the single prove call.
    let preprocessed_ids: Vec<PreProcessedColumnId> = modules
        .iter()
        .flat_map(|m| m.preprocessed_column_ids())
        .collect();
    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&preprocessed_ids);
    for m in modules.iter_mut() {
        m.build_components(&mut allocator);
    }
    let component_refs: Vec<&dyn ComponentProver<SimdBackend>> =
        modules.iter().flat_map(|m| m.prover_components()).collect();

    stark_prove::<SimdBackend, Mc>(&component_refs, channel, commitment_scheme)
}

/// Re-derive the transcript for every module and verify the single STARK proof.
pub fn verify(
    modules: &mut [&mut dyn Air],
    proof: &StarkProof<Hasher>,
) -> Result<(), VerificationError> {
    let config = proof.config;
    let channel = &mut Ch::default();
    config.mix_into(channel);

    let commitment_scheme = &mut CommitmentSchemeVerifier::<Mc>::new(config);

    // Tree 0: preprocessed columns of every module.
    let preprocessed_sizes: Vec<u32> = modules
        .iter()
        .flat_map(|m| m.layout().preprocessed)
        .collect();
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
        return Err(VerificationError::InvalidStructure(
            "LogUp claimed sums do not cancel".into(),
        ));
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

    // Build every module's components against one shared allocator (same seeding
    // as the prover), then collect the borrowed component refs to verify.
    let preprocessed_ids: Vec<PreProcessedColumnId> = modules
        .iter()
        .flat_map(|m| m.preprocessed_column_ids())
        .collect();
    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&preprocessed_ids);
    for m in modules.iter_mut() {
        m.build_components(&mut allocator);
    }
    let component_refs: Vec<&dyn Component> = modules.iter().flat_map(|m| m.components()).collect();

    stark_verify(&component_refs, channel, commitment_scheme, proof.clone())
}
