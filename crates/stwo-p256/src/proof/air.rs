//! Wraps the monolithic P256 ECDSA AIR as an [`air_core`] proving module.
//!
//! [`P256Prover`] holds a draft and contributes every column across the four
//! phases the standalone [`super::P256ProofDraft::prove_current_air_monolithic`]
//! ran inline; [`P256Verifier`] holds the proof's claims and rebuilds the same
//! components on the verify side. Both delegate to the existing
//! `gen_current_air_*` trace generators and [`super::P256CurrentAirComponents`],
//! so there is no duplicated proving logic — only the wiring into the shared
//! channel and commitment scheme that [`air_core::prove`] / [`air_core::verify`]
//! own.
//!
//! This module is a child of `proof`, so it reaches that module's private
//! claim/relations/component types and trace generators via `super::`.
//!
//! ## Deviations the orchestrator absorbs
//!
//! - **Constraint-degree FRI sizing.** P256's constraints exceed degree 2, so
//!   it reports its real [`AirProver::max_constraint_log_degree_bound`]; the
//!   orchestrator sizes twiddles from it.
//! - **Constraint-degree FRI sizing.** P256 sizes the lifting domain from its
//!   real component bounds, but it does not need to retain committed
//!   polynomials in coefficient form during ordinary proving.
//! - **Provider-inclusive balance + structured transcript mix.** P256's global
//!   balance is `lookup_sum` (component sums *plus* public-input provider
//!   terms), returned from [`Air::claimed_sums`]; its transcript mix is the
//!   structured [`super::P256CurrentAirInteractionClaim::mix_into`], reproduced
//!   via [`Air::mix_claimed_sums`].

use air_core::{Air, AirProver, TreeLayout};
use stwo::core::air::Component;
use stwo::core::channel::Blake2sChannel;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo::core::ColumnVec;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::TraceLocationAllocator;

use crate::components::digest_bind::{
    scalar_z_provider_claimed_sum, ScalarZRelation, SharedScalarZRelation,
};
use crate::public_inputs::PublicEcdsaInstance;
use crate::scalar::scalar_mod_mul::columns::M31ColumnEval;

use super::{
    p256_stark_monolithic_profile_config, P256CurrentAirBaseTrace, P256CurrentAirComponents,
    P256CurrentAirInteractionClaim, P256CurrentAirProof, P256CurrentAirProofClaim,
    P256CurrentAirRelations, P256ProofDraft, P256ProofError,
};

/// Prove a P256 ECDSA AIR through the shared orchestrator. Thin wrapper that
/// drives [`P256Prover`] (one module) and packs the result into the same
/// [`P256CurrentAirProof`] shape the monolithic path produced.
pub fn prove_current_air(
    draft: &P256ProofDraft,
) -> Result<P256CurrentAirProof<Blake2sMerkleHasher>, P256ProofError> {
    let mut prover = P256Prover::new(draft)?;
    let config = p256_stark_monolithic_profile_config(prover.max_constraint_bound);
    let stark_proof = air_core::prove(&mut [&mut prover], config)
        .map_err(|error| P256ProofError::ProofLayer(error.to_string()))?;

    Ok(P256CurrentAirProof {
        claim: prover.proof_claim,
        interaction_claim: prover
            .interaction_claim
            .expect("interaction claim is set during proving"),
        stark_proof,
    })
}

/// Verify a P256 ECDSA AIR proof through the shared orchestrator. Keeps the
/// monolithic verifier's caller-binding, public-key-canonicality, and
/// config-pinning gates, then delegates the STARK verification.
pub fn verify_current_air(
    proof: P256CurrentAirProof<Blake2sMerkleHasher>,
    expected_instances: &[PublicEcdsaInstance<M31>],
) -> Result<(), P256ProofError> {
    let P256CurrentAirProof {
        claim,
        interaction_claim,
        stark_proof,
    } = proof;

    // Bind the proof to the caller's expected statement (see the monolithic
    // verifier's O1 note): `Ok(())` must mean "this `(z, r, s, pub)` verifies",
    // not "some signature the prover embedded verifies".
    if claim.public_inputs.instances.as_slice() != expected_instances {
        return Err(P256ProofError::PublicInstanceMismatch);
    }
    // Public-key canonicality gate: reject non-canonical coordinate
    // representatives before any proof work.
    for (index, instance) in claim.public_inputs.instances.iter().enumerate() {
        if let Some(field) = instance.non_canonical_public_key_field() {
            return Err(P256ProofError::NonCanonicalPublicKey { index, field });
        }
    }
    // Pin the PCS config: the verifier must not inherit a weakened FRI/grinding
    // setting from the prover-supplied `stark_proof.config`.
    let ids = claim.preprocessed_column_ids();
    let expected_config =
        p256_stark_monolithic_profile_config(claim.max_constraint_log_degree_bound(&ids));
    if stark_proof.config != expected_config {
        return Err(P256ProofError::ProofLayer(format!(
            "proof PCS config {:?} does not match the pinned verifier config {:?}",
            stark_proof.config, expected_config
        )));
    }

    let mut verifier = P256Verifier::new(claim, interaction_claim);
    air_core::verify(&mut [&mut verifier], &stark_proof)
        .map_err(|error| P256ProofError::ProofLayer(error.to_string()))
}

/// Prover-side module: built from a draft, owns its traces and components.
pub struct P256Prover<'a> {
    draft: &'a P256ProofDraft,
    proof_claim: P256CurrentAirProofClaim,
    ids: Vec<PreProcessedColumnId>,
    max_constraint_bound: u32,
    preprocessed: Option<ColumnVec<M31ColumnEval>>,
    base: Option<P256CurrentAirBaseTrace>,
    relations: Option<P256CurrentAirRelations>,
    interaction_claim: Option<P256CurrentAirInteractionClaim>,
    components: Option<P256CurrentAirComponents>,
    /// Cross-module `z` binding: when set, the module additionally draws a
    /// [`ScalarZRelation`], shares it through [`Self::scalar_z_handle`], and folds
    /// an analytic `−1/combine(sig_id, z)` provider term into its claimed sum —
    /// the counterpart the digest-bind bridge consumes. Off for a standalone
    /// P256 proof, leaving its transcript and balance unchanged.
    bind_z: bool,
    scalar_z_handle: Option<SharedScalarZRelation>,
    scalar_z: Option<ScalarZRelation>,
}

/// P-256 proof metadata and trace columns materialized before the module is
/// wired to cross-module relation handles.
pub struct PreparedP256Prover<'a> {
    draft: &'a P256ProofDraft,
    proof_claim: P256CurrentAirProofClaim,
    ids: Vec<PreProcessedColumnId>,
    max_constraint_bound: u32,
    preprocessed: ColumnVec<M31ColumnEval>,
    base: P256CurrentAirBaseTrace,
}

pub struct P256InteractionJob<'a> {
    draft: &'a P256ProofDraft,
    base: &'a P256CurrentAirBaseTrace,
    relations: &'a P256CurrentAirRelations,
}

pub struct PreparedP256Interaction {
    columns: ColumnVec<M31ColumnEval>,
    claim: P256CurrentAirInteractionClaim,
}

impl P256InteractionJob<'_> {
    pub fn materialize(self) -> Result<PreparedP256Interaction, P256ProofError> {
        let (columns, claim) = self
            .draft
            .gen_current_air_interaction_trace(self.base, self.relations)?;
        Ok(PreparedP256Interaction { columns, claim })
    }
}

impl<'a> P256Prover<'a> {
    pub fn prepare(draft: &'a P256ProofDraft) -> Result<PreparedP256Prover<'a>, P256ProofError> {
        let proof_claim = P256CurrentAirProofClaim::from_claim(&draft.claim);
        let ids = proof_claim.preprocessed_column_ids();
        let max_constraint_bound = proof_claim.max_constraint_log_degree_bound(&ids);
        // The fallible trace generation happens up front so the wrapper can
        // surface it; the in-phase `write_*` methods only move the prepared
        // evaluations into the shared trees.
        let preprocessed = draft.gen_current_air_preprocessed_trace(&proof_claim, &ids)?;
        let base = draft.gen_current_air_base_trace(&proof_claim)?;
        Ok(PreparedP256Prover {
            draft,
            proof_claim,
            ids,
            max_constraint_bound,
            preprocessed,
            base,
        })
    }

    pub fn new(draft: &'a P256ProofDraft) -> Result<Self, P256ProofError> {
        Self::prepare(draft).map(Self::from_prepared)
    }

    pub fn from_prepared(prepared: PreparedP256Prover<'a>) -> Self {
        Self {
            draft: prepared.draft,
            proof_claim: prepared.proof_claim,
            ids: prepared.ids,
            max_constraint_bound: prepared.max_constraint_bound,
            preprocessed: Some(prepared.preprocessed),
            base: Some(prepared.base),
            relations: None,
            interaction_claim: None,
            components: None,
            bind_z: false,
            scalar_z_handle: None,
            scalar_z: None,
        }
    }

    /// Enable the cross-module `z` binding: the module draws and shares a
    /// [`ScalarZRelation`] through `handle` and yields the analytic
    /// `(sig_id, z)` provider term. Set this iff the composed proof includes the
    /// digest-bind bridge that consumes the same relation; the matching
    /// [`P256Verifier`] must be built with [`P256Verifier::with_z_binding`].
    pub fn with_z_binding(mut self, handle: SharedScalarZRelation) -> Self {
        self.bind_z = true;
        self.scalar_z_handle = Some(handle);
        self
    }

    /// The PCS config this circuit is calibrated for. A combined proof that
    /// includes the P256 module should drive the whole proof with this config
    /// (it is the security-calibrated one); `lifting_log_size` is `None`, so the
    /// orchestrator still sizes twiddles from the max constraint bound across
    /// all modules.
    pub fn pcs_config(&self) -> PcsConfig {
        p256_stark_monolithic_profile_config(self.max_constraint_bound)
    }

    /// The proof claim, for packing into a combined proof and reconstructing the
    /// verifier module.
    pub fn proof_claim(&self) -> &P256CurrentAirProofClaim {
        &self.proof_claim
    }

    /// The aggregate interaction claim produced during proving. Read back after
    /// [`air_core::prove`] to pack the combined proof. Panics if called before
    /// the interaction phase has run.
    pub fn interaction_claim(&self) -> &P256CurrentAirInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("interaction claim is set during the interaction phase")
    }

    fn relations(&self) -> &P256CurrentAirRelations {
        self.relations
            .as_ref()
            .expect("relations are drawn before they are used")
    }

    fn built_components(&self) -> &P256CurrentAirComponents {
        self.components
            .as_ref()
            .expect("components are built before they are borrowed")
    }

    pub fn interaction_job(&self) -> P256InteractionJob<'_> {
        P256InteractionJob {
            draft: self.draft,
            base: self.base.as_ref().expect("base trace present"),
            relations: self
                .relations
                .as_ref()
                .expect("relations are drawn before the interaction phase"),
        }
    }

    pub fn write_prepared_interaction(
        &mut self,
        tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>,
        prepared: PreparedP256Interaction,
    ) {
        tb.extend_evals(prepared.columns);
        self.interaction_claim = Some(prepared.claim);
    }
}

impl Air for P256Prover<'_> {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        self.proof_claim.mix_into(channel);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.relations = Some(P256CurrentAirRelations::draw(channel));
        // Drawn after the module's own relations (so the existing transcript is
        // unperturbed) and shared with the bridge module that consumes it.
        if self.bind_z {
            let scalar_z = ScalarZRelation::draw(channel);
            self.scalar_z_handle
                .as_ref()
                .expect("scalar_z handle set by with_z_binding")
                .set(scalar_z.clone());
            self.scalar_z = Some(scalar_z);
        }
    }

    fn layout(&self) -> TreeLayout {
        layout(
            &self.proof_claim,
            &self.ids,
            self.interaction_claim.as_ref(),
        )
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        // The whole `lookup_sum` (component sums plus public-input provider
        // terms) as one balance entry; the orchestrator rejects unless it is
        // zero, matching the monolithic verifier's `lookup_sum == 0` gate. When
        // the `z` binding is on, add the analytic `(sig_id, z)` provider term the
        // bridge consumes.
        let mut sum = self
            .interaction_claim()
            .lookup_sum(&self.proof_claim.public_inputs.instances, self.relations());
        if self.bind_z {
            sum += scalar_z_provider_claimed_sum(
                &self.proof_claim.public_inputs.instances,
                self.scalar_z.as_ref().expect("scalar_z drawn when bind_z"),
            );
        }
        vec![sum]
    }

    fn mix_claimed_sums(&self, channel: &mut Blake2sChannel) {
        self.interaction_claim().mix_into(channel);
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        self.ids.clone()
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(P256CurrentAirComponents::new(
            allocator,
            &self.proof_claim,
            self.interaction_claim(),
            self.relations(),
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built_components().components()
    }
}

impl AirProver for P256Prover<'_> {
    fn max_log_size(&self) -> u32 {
        // Unused by the orchestrator for P256 (it sizes from
        // `max_constraint_log_degree_bound`); reported for trait completeness.
        self.max_constraint_bound
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.max_constraint_bound
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let preprocessed = self
            .preprocessed
            .take()
            .expect("preprocessed trace generated in P256Prover::new");
        tb.extend_evals(preprocessed);
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let base = self
            .base
            .as_mut()
            .expect("base trace generated in P256Prover::new");
        // Move out the committed columns; the rest of `base` feeds the
        // interaction phase (matching the monolithic `std::mem::take`).
        let base_columns = std::mem::take(&mut base.columns);
        tb.extend_evals(base_columns);
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let prepared = self
            .interaction_job()
            .materialize()
            .expect("interaction trace generates for a validated draft");
        self.write_prepared_interaction(tb, prepared);
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        self.built_components().component_provers()
    }
}

/// Verifier-side module: built from the proof's claim and interaction claim.
pub struct P256Verifier {
    proof_claim: P256CurrentAirProofClaim,
    ids: Vec<PreProcessedColumnId>,
    interaction_claim: P256CurrentAirInteractionClaim,
    relations: Option<P256CurrentAirRelations>,
    components: Option<P256CurrentAirComponents>,
    bind_z: bool,
    scalar_z_handle: Option<SharedScalarZRelation>,
    scalar_z: Option<ScalarZRelation>,
}

impl P256Verifier {
    pub fn new(
        proof_claim: P256CurrentAirProofClaim,
        interaction_claim: P256CurrentAirInteractionClaim,
    ) -> Self {
        let ids = proof_claim.preprocessed_column_ids();
        Self {
            proof_claim,
            ids,
            interaction_claim,
            relations: None,
            components: None,
            bind_z: false,
            scalar_z_handle: None,
            scalar_z: None,
        }
    }

    /// The PCS config this proof must have been produced under — the verifier-side
    /// counterpart of [`P256Prover::pcs_config`]. A combined proof that embeds the
    /// P256 module inherits this config for the whole STARK, so the combined
    /// verifier pins the proof-supplied config against this value (the standalone
    /// `verify_current_air` does the same). This stops a malicious prover from
    /// submitting a weakened FRI/grinding setting.
    pub fn expected_pcs_config(&self) -> PcsConfig {
        p256_stark_monolithic_profile_config(
            self.proof_claim.max_constraint_log_degree_bound(&self.ids),
        )
    }

    /// Match a [`P256Prover::with_z_binding`] proof: draw and share the same
    /// [`ScalarZRelation`] and fold the analytic provider term into the balance.
    /// Must be set iff the prover set it.
    pub fn with_z_binding(mut self, handle: SharedScalarZRelation) -> Self {
        self.bind_z = true;
        self.scalar_z_handle = Some(handle);
        self
    }

    fn relations(&self) -> &P256CurrentAirRelations {
        self.relations
            .as_ref()
            .expect("relations are drawn before they are used")
    }

    fn built_components(&self) -> &P256CurrentAirComponents {
        self.components
            .as_ref()
            .expect("components are built before they are borrowed")
    }
}

impl Air for P256Verifier {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        self.proof_claim.mix_into(channel);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.relations = Some(P256CurrentAirRelations::draw(channel));
        if self.bind_z {
            let scalar_z = ScalarZRelation::draw(channel);
            self.scalar_z_handle
                .as_ref()
                .expect("scalar_z handle set by with_z_binding")
                .set(scalar_z.clone());
            self.scalar_z = Some(scalar_z);
        }
    }

    fn layout(&self) -> TreeLayout {
        layout(&self.proof_claim, &self.ids, Some(&self.interaction_claim))
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        let mut sum = self
            .interaction_claim
            .lookup_sum(&self.proof_claim.public_inputs.instances, self.relations());
        if self.bind_z {
            sum += scalar_z_provider_claimed_sum(
                &self.proof_claim.public_inputs.instances,
                self.scalar_z.as_ref().expect("scalar_z drawn when bind_z"),
            );
        }
        vec![sum]
    }

    fn mix_claimed_sums(&self, channel: &mut Blake2sChannel) {
        self.interaction_claim.mix_into(channel);
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        self.ids.clone()
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(P256CurrentAirComponents::new(
            allocator,
            &self.proof_claim,
            &self.interaction_claim,
            self.relations(),
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built_components().components()
    }
}

/// Per-tree column log-sizes. Tree 0/1 sizes are independent of the interaction
/// claim and relations; tree 2's column count depends on the interaction claim
/// but not relation values, so dummy relations suffice for sizing (matching the
/// monolithic verifier's use of dummy bounds for the early trees).
fn layout(
    proof_claim: &P256CurrentAirProofClaim,
    ids: &[PreProcessedColumnId],
    interaction_claim: Option<&P256CurrentAirInteractionClaim>,
) -> TreeLayout {
    let owned;
    let interaction_claim = match interaction_claim {
        Some(claim) => claim,
        None => {
            owned = P256CurrentAirInteractionClaim::zero_for_claim(proof_claim);
            &owned
        }
    };
    let bounds = proof_claim.trace_log_degree_bounds(
        ids,
        interaction_claim,
        &P256CurrentAirRelations::dummy(),
    );
    TreeLayout {
        preprocessed: bounds[0].clone(),
        trace: bounds[1].clone(),
        interaction: bounds[2].clone(),
    }
}
