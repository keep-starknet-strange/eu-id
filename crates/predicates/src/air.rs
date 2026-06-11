//! Combines one or more proving modules into a single STARK proof.
//!
//! Each predicate (and, later, the SHA and P256 provers) implements [`Air`] and
//! [`AirProver`]. A module does NOT own the channel or the commitment scheme; it
//! only contributes columns and components to shared commitment trees. The
//! orchestrator functions [`prove`] and [`verify`] own the transcript and drive
//! every module through the same four phases:
//!
//! 0. preprocessed tables
//! 1. main witness + multiplicity columns
//! 2. interaction (LogUp) columns
//! 3. component assembly + the single `prove`/`verify` call
//!
//! Proving a single predicate is just `prove(&mut [&mut module])`

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
    fn mix_public(&self, channel: &mut Blake2sChannel);

    /// Draw this module's lookup relations from the shared channel and stash
    /// them for the interaction phase and component assembly.
    fn draw_relations(&mut self, channel: &mut Blake2sChannel);

    /// Column log-sizes per tree, in commit order.
    fn layout(&self) -> TreeLayout;

    /// The module's claimed LogUp sums, in the same order its components expect.
    /// On the verifier side these come from the proof; on the prover side they
    /// are filled in by [`AirProver::write_interaction`].
    fn claimed_sums(&self) -> Vec<QM31>;

    /// Build the verifier-side components (needs relations + claimed sums).
    fn components(&self) -> Vec<Box<dyn Component>>;
}

/// The prover-only extension: a module that holds a witness and can write its
/// actual columns into the shared commitment trees.
pub trait AirProver: Air {
    /// Largest trace log-size this module uses; the orchestrator takes the max
    /// over all modules to size the FRI twiddles.
    fn max_log_size(&self) -> u32;

    /// Phase 0 — append preprocessed columns to the shared tree.
    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>);

    /// Phase 1 — append main witness + multiplicity columns to the shared tree.
    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>);

    /// Phase 2 — build the interaction (LogUp) columns from the drawn relations,
    /// append them, and stash this module's claimed sums (read back via
    /// [`Air::claimed_sums`]).
    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>);

    /// Build the prover-side components (needs relations + claimed sums).
    fn prover_components(&self) -> Vec<Box<dyn ComponentProver<SimdBackend>>>;
}

/// Drive every module through the four phases against one shared channel and one
/// shared commitment scheme, producing a single STARK proof.
pub(crate) fn prove(
    modules: &mut [&mut dyn AirProver],
    config: PcsConfig,
) -> Result<StarkProof<Blake2sMerkleHasher>, ProvingError> {
    let max_log_size = modules
        .iter()
        .map(|m| m.max_log_size())
        .max()
        .expect("at least one module");

    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(max_log_size + 1 + config.fri_config.log_blowup_factor)
            .circle_domain()
            .half_coset,
    );

    let channel = &mut Blake2sChannel::default();
    config.mix_into(channel);

    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

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
    let claimed_sums: Vec<QM31> = modules.iter().flat_map(|m| m.claimed_sums()).collect();
    channel.mix_felts(&claimed_sums);
    tb.commit(channel);

    let components: Vec<Box<dyn ComponentProver<SimdBackend>>> =
        modules.iter().flat_map(|m| m.prover_components()).collect();
    let component_refs: Vec<&dyn ComponentProver<SimdBackend>> =
        components.iter().map(|c| c.as_ref()).collect();

    stark_prove::<SimdBackend, Blake2sMerkleChannel>(&component_refs, channel, commitment_scheme)
}

/// Re-derive the transcript for every module and verify the single STARK proof.
pub(crate) fn verify(
    modules: &mut [&mut dyn Air],
    proof: &StarkProof<Blake2sMerkleHasher>,
) -> Result<(), VerificationError> {
    let config = proof.config;
    let channel = &mut Blake2sChannel::default();
    config.mix_into(channel);

    let commitment_scheme = &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);

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

    let claimed_sums: Vec<QM31> = modules.iter().flat_map(|m| m.claimed_sums()).collect();
    channel.mix_felts(&claimed_sums);

    // Global LogUp balance: every yield (+) must be matched by a require (-)
    // across all modules.
    if claimed_sums.iter().fold(QM31::zero(), |acc, &s| acc + s) != QM31::zero() {
        return Err(VerificationError::InvalidStructure(
            "LogUp claimed sums do not cancel".into(),
        ));
    }

    // Tree 2: interaction columns of every module.
    let interaction_sizes: Vec<u32> = modules
        .iter()
        .flat_map(|m| m.layout().interaction)
        .collect();
    commitment_scheme.commit(proof.commitments[2], &interaction_sizes, channel);

    let components: Vec<Box<dyn Component>> = modules.iter().flat_map(|m| m.components()).collect();
    let component_refs: Vec<&dyn Component> = components.iter().map(|c| c.as_ref()).collect();

    stark_verify(&component_refs, channel, commitment_scheme, proof.clone())
}
