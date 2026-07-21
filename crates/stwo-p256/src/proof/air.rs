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
//! - **Stored polynomial coefficients.** P256 needs the lifting path, so it
//!   returns `true` from [`AirProver::store_polynomial_coefficients`].
//! - **Provider-inclusive balance + structured transcript mix.** P256's global
//!   balance is `lookup_sum` (component sums *plus* public-input provider
//!   terms), returned from [`Air::claimed_sums`]; its transcript mix is the
//!   structured [`super::P256CurrentAirInteractionClaim::mix_into`], reproduced
//!   via [`Air::mix_claimed_sums`].

use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
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
use crate::components::hinted_mul::air::namespace_hinted_mul_schedule_ids;
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
    verify_current_air_with_preprocessed_root(proof, expected_instances, None)
}

/// Compute the expected tree-0 (preprocessed) commitment root for a draft, by
/// running exactly the prover's tree-0 path over [`P256Prover`]. A relying
/// party derives the draft from its OWN expected statement
/// (`P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints` is a
/// deterministic function of the inputs) — never from the proof — and passes
/// the result to [`verify_current_air_with_preprocessed_root`].
///
/// Uses the UNCACHED computation deliberately: the hinted-mul schedule
/// preprocessed columns are witness-dependent but keep one column id across
/// witnesses, so the id-keyed cache in `air_core::compute_preprocessed_root`
/// would return the first witness's root for every later one.
pub fn current_air_preprocessed_root(
    draft: &P256ProofDraft,
) -> Result<air_core::CommitmentRoot, P256ProofError> {
    let mut prover = P256Prover::new(draft)?;
    let config = p256_stark_monolithic_profile_config(prover.max_constraint_bound);
    Ok(air_core::compute_preprocessed_root_uncached(
        &mut [&mut prover],
        config,
    ))
}

/// [`verify_current_air`], with the tree-0 (preprocessed) commitment root
/// pinned — the F-ROOT fix. On `Some(expected)`, the proof's
/// `stark_proof.commitments[0]` must equal `expected`, checked fail-closed
/// BEFORE the root is absorbed into the transcript, so a forged preprocessed
/// tree (range tables, hinted-mul schedules, constants) is rejected up front
/// with [`P256ProofError::PreprocessedRootMismatch`]. Callers obtain
/// `expected` from [`current_air_preprocessed_root`] over their own trusted
/// statement, never from the proof. `None` keeps the legacy unpinned behavior
/// for self-proving tests only.
pub fn verify_current_air_with_preprocessed_root(
    proof: P256CurrentAirProof<Blake2sMerkleHasher>,
    expected_instances: &[PublicEcdsaInstance<M31>],
    expected_preprocessed_root: Option<air_core::CommitmentRoot>,
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
    air_core::verify_with_expected_preprocessed_root(
        &mut [&mut verifier],
        &stark_proof,
        expected_preprocessed_root,
    )
    .map_err(|error| match error {
        air_core::VerifyError::PreprocessedRootMismatch { got, expected } => {
            P256ProofError::PreprocessedRootMismatch {
                got: format!("{got:?}"),
                expected: format!("{expected:?}"),
            }
        }
        air_core::VerifyError::Stark(error) => P256ProofError::ProofLayer(error.to_string()),
    })
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
    hinted_mul_preprocessed_namespace: Option<String>,
}

/// Send-only Stage-1 task input for preparing P-256 preprocessed/base columns.
pub struct P256ColumnTask<'a> {
    draft: &'a P256ProofDraft,
}

/// Prepared P-256 preprocessed/base columns returned by [`P256ColumnTask`].
pub struct P256PreparedColumns {
    proof_claim: P256CurrentAirProofClaim,
    ids: Vec<PreProcessedColumnId>,
    max_constraint_bound: u32,
    preprocessed: ColumnVec<M31ColumnEval>,
    base: P256CurrentAirBaseTrace,
}

impl<'a> P256ColumnTask<'a> {
    pub fn new(draft: &'a P256ProofDraft) -> Self {
        Self { draft }
    }

    pub fn run(self) -> Result<P256PreparedColumns, P256ProofError> {
        let proof_claim = P256CurrentAirProofClaim::from_claim(&self.draft.claim);
        let ids = proof_claim.preprocessed_column_ids();
        let max_constraint_bound = proof_claim.max_constraint_log_degree_bound(&ids);
        let preprocessed = self
            .draft
            .gen_current_air_preprocessed_trace(&proof_claim, &ids)?;
        let base = self.draft.gen_current_air_base_trace(&proof_claim)?;
        Ok(P256PreparedColumns {
            proof_claim,
            ids,
            max_constraint_bound,
            preprocessed,
            base,
        })
    }
}

impl<'a> P256Prover<'a> {
    pub fn new(draft: &'a P256ProofDraft) -> Result<Self, P256ProofError> {
        Ok(Self::from_prepared(
            draft,
            P256ColumnTask::new(draft).run()?,
        ))
    }

    pub fn from_prepared(draft: &'a P256ProofDraft, prepared: P256PreparedColumns) -> Self {
        Self {
            draft,
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
            hinted_mul_preprocessed_namespace: None,
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

    /// Prefix this module's preprocessed column ids so multiple P-256 modules
    /// with witness-dependent hinted-mul schedule columns do not alias in a
    /// shared `air_core::prove` preprocessed tree. The verifier must apply the
    /// same namespace before building components.
    pub fn with_preprocessed_namespace(mut self, namespace: &str) -> Self {
        self.ids = namespace_hinted_mul_schedule_ids(Some(namespace), self.ids);
        self.hinted_mul_preprocessed_namespace = Some(namespace.to_string());
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
            self.hinted_mul_preprocessed_namespace.as_deref(),
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
        self.components = Some(
            P256CurrentAirComponents::new_with_hinted_mul_preprocessed_namespace(
                allocator,
                &self.proof_claim,
                self.interaction_claim(),
                self.relations(),
                self.hinted_mul_preprocessed_namespace.as_deref(),
            ),
        );
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

    fn store_polynomial_coefficients(&self) -> bool {
        true
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let ids = self.ids.clone();
        self.write_selected_preprocessed(tb, &ids);
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "stwo_p256::P256Prover",
            &self.ids,
            self.preprocessed
                .as_ref()
                .expect("preprocessed trace generated in P256Prover::new"),
        )
    }

    fn write_selected_preprocessed(
        &mut self,
        tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        let preprocessed = self
            .preprocessed
            .take()
            .expect("preprocessed trace generated in P256Prover::new");
        if selected_ids == self.ids.as_slice() {
            tb.extend_evals(preprocessed);
            return;
        }

        let selected = selected_ids
            .iter()
            .map(|selected_id| {
                self.ids
                    .iter()
                    .zip(&preprocessed)
                    .find_map(|(id, column)| (id == selected_id).then(|| column.clone()))
                    .unwrap_or_else(|| {
                        panic!(
                            "selected preprocessed column {} is not owned by this P256 module",
                            selected_id.id
                        )
                    })
            })
            .collect();
        tb.extend_evals(selected);
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
        let base = self.base.as_ref().expect("base trace present");
        let relations = self
            .relations
            .as_ref()
            .expect("relations are drawn before the interaction phase");
        let (interaction, interaction_claim) = self
            .draft
            .gen_current_air_interaction_trace(base, relations)
            .expect("interaction trace generates for a validated draft");
        tb.extend_evals(interaction);
        self.interaction_claim = Some(interaction_claim);
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
    hinted_mul_preprocessed_namespace: Option<String>,
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
            hinted_mul_preprocessed_namespace: None,
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
            self.proof_claim
                .max_constraint_log_degree_bound_with_hinted_mul_preprocessed_namespace(
                    &self.ids,
                    self.hinted_mul_preprocessed_namespace.as_deref(),
                ),
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

    /// Match [`P256Prover::with_preprocessed_namespace`].
    pub fn with_preprocessed_namespace(mut self, namespace: &str) -> Self {
        self.ids = namespace_hinted_mul_schedule_ids(Some(namespace), self.ids);
        self.hinted_mul_preprocessed_namespace = Some(namespace.to_string());
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
        layout(
            &self.proof_claim,
            &self.ids,
            Some(&self.interaction_claim),
            self.hinted_mul_preprocessed_namespace.as_deref(),
        )
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

    // NOTE: `P256Verifier` deliberately does NOT override
    // `Air::canonical_preprocessed_columns`. Its preprocessed tree includes the
    // legacy hinted-mul scalar-multiplication schedule, which is
    // witness-dependent and cannot be reconstructed from public data alone. The
    // trait default therefore returns `Err`, so every production verify path
    // that runs `air_core::compute_canonical_preprocessed_root` over a module set
    // containing this module fails closed. This is by design: the classical
    // (non-`ec-coprocessor`) build cannot be canonically verified — the
    // `ec-coprocessor` build proves the ECDSA statement in-circuit instead of
    // reconstructing this schedule. See the trait-default doc in `air-core`.

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(
            P256CurrentAirComponents::new_with_hinted_mul_preprocessed_namespace(
                allocator,
                &self.proof_claim,
                &self.interaction_claim,
                self.relations(),
                self.hinted_mul_preprocessed_namespace.as_deref(),
            ),
        );
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
    hinted_mul_preprocessed_namespace: Option<&str>,
) -> TreeLayout {
    let owned;
    let interaction_claim = match interaction_claim {
        Some(claim) => claim,
        None => {
            owned = P256CurrentAirInteractionClaim::zero_for_claim(proof_claim);
            &owned
        }
    };
    let bounds = proof_claim.trace_log_degree_bounds_with_hinted_mul_preprocessed_namespace(
        ids,
        interaction_claim,
        &P256CurrentAirRelations::dummy(),
        hinted_mul_preprocessed_namespace,
    );
    TreeLayout {
        preprocessed: bounds[0].clone(),
        trace: bounds[1].clone(),
        interaction: bounds[2].clone(),
    }
}
