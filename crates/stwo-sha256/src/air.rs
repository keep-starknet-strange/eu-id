//! Wraps the SHA-256 AIR as an [`air_core`] proving module.
//!
//! [`Sha256Prover`] holds the witness and contributes each prover column.
//! [`Sha256Verifier`] holds the public size data and the claimed sums. Both
//! modules process the preprocessed tables, base trace, producer
//! multiplicities, interaction trace, and component assembly through
//! [`air_core::prove`] and [`air_core::verify`].
//!
//! The orchestrator mixes [`Air::claimed_sums`] as one flat slice in component
//! order. Prove and verify use the same order. See [`flatten_claimed_sums`].

use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::{QM31, SECURE_EXTENSION_DEGREE};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::core::verifier::VerificationError;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{FrameworkComponent, TraceLocationAllocator};

use crate::components::{
    all_preprocessed_column_ids_ns, consumer_preprocessed_column_ids_ns, range_log_size,
    RangeKEval, Sha256Relations, RANGE_TABLES,
};
use crate::constraints::{Sha256Eval, LOGUP_BATCH};
use crate::digest_bridge::{
    digest_bridge_lookups, DigestBridgeEval, DIGEST_BRIDGE_BASE_COLS, DIGEST_BRIDGE_LOG_SIZE,
};
use crate::field_exposure::FieldExposure;
use crate::interaction::{
    generate_consumer_interaction_trace, generate_interaction_trace, sha_lookups_per_row,
    InteractionClaim,
};
use crate::multiplicities::range_k_multiplicities;
use crate::preprocessed::{generate_preprocessed_trace, preprocessed_log_sizes};
use crate::relations::SharedShaTableRelations;
use crate::trace::Layout;
use crate::types::Sha256Witness;

/// Column log sizes per tree, shared by the prover and verifier.
///
/// The sizes depend only on `log_n_rows` and the enabled providers. They do
/// not depend on the witness.
fn layout(
    log_n_rows: u32,
    expose_digest: bool,
    field_exposure: &FieldExposure,
    shared_tables: bool,
) -> TreeLayout {
    TreeLayout {
        preprocessed: if shared_tables {
            consumer_preprocessed_log_sizes(log_n_rows)
        } else {
            preprocessed_log_sizes(log_n_rows)
        },
        trace: base_trace_log_sizes(log_n_rows, field_exposure.n_columns(), !shared_tables),
        interaction: interaction_trace_log_sizes(
            log_n_rows,
            expose_digest,
            field_exposure,
            !shared_tables,
        ),
    }
}

/// Flatten the per-component claims into one slice in component (commit) order
/// — the order [`Sha256Components`] adds them and the order the orchestrator
/// mixes and balances. Equals [`InteractionClaim::total`] when summed.
pub fn flatten_claimed_sums(claim: &InteractionClaim) -> Vec<QM31> {
    let mut out = Vec::new();
    out.push(claim.sha256.claimed_sum);
    out.push(claim.digest_bridge.claimed_sum);
    out.extend(claim.range.iter().map(|c| c.claimed_sum));
    out
}

/// Prover-side module: built from the witness and the public size surface.
pub struct Sha256Prover<'a> {
    witness: &'a Sha256Witness,
    log_n_rows: u32,
    instance_namespace: String,
    expose_digest: bool,
    digest_handle: Option<air_core::relations::SharedDigestRelation>,
    field_exposure: FieldExposure,
    field_handle: Option<air_core::relations::SharedFieldRelation>,
    shared_tables: Option<SharedShaTableRelations>,
    preprocessed: Option<Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>>,
    base: Option<Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>>,
    relations: Option<Sha256Relations>,
    interaction_claim: Option<InteractionClaim>,
    components: Option<Sha256Components>,
}

impl<'a> Sha256Prover<'a> {
    pub fn new(witness: &'a Sha256Witness, log_n_rows: u32) -> Self {
        Self {
            witness,
            log_n_rows,
            instance_namespace: String::new(),
            expose_digest: false,
            digest_handle: None,
            field_exposure: FieldExposure::empty(),
            field_handle: None,
            shared_tables: None,
            preprocessed: None,
            base: None,
            relations: None,
            interaction_claim: None,
            components: None,
        }
    }

    /// Enable the cross-component digest provider: the module yields
    /// the final-block digest on the `Sha256Digest` channel, so a composed
    /// consumer (the ML-DSA digest binding) can require it. This leaves the SHA
    /// module's claimed sum non-zero on its own — it cancels only against the
    /// consumer's require — so it is **off by default**, keeping a standalone
    /// SHA proof self-balancing. The flag is mixed into the transcript
    /// ([`Stmt0`]) so prover and verifier agree, and must be set identically
    /// on the matching [`Sha256Verifier`].
    pub fn with_digest_provider(mut self) -> Self {
        self.expose_digest = true;
        self
    }

    /// As [`Self::with_digest_provider`], plus **share** the drawn
    /// `Sha256Digest` relation through `handle` so a sibling module consumes it
    /// over the identical `LookupElements`.
    /// The handle is populated during [`Air::draw_relations`].
    pub fn with_digest_handle(mut self, handle: air_core::relations::SharedDigestRelation) -> Self {
        self.expose_digest = true;
        self.digest_handle = Some(handle);
        self
    }

    /// Enable the padded-stream provider. The module yields each constrained
    /// message byte on the `Sha256Field` channel. Like
    /// [`Self::with_digest_provider`], this
    /// leaves the module's claimed sum non-zero until a consumer cancels it, so
    /// it is off by default. The exposure shape is mixed into the transcript
    /// ([`Stmt0`]) and must be set identically on the matching
    /// [`Sha256Verifier`]. Use [`Self::with_field_handle`] to also share the
    /// drawn relation with the consumer module.
    pub fn with_field_provider(mut self, exposure: FieldExposure) -> Self {
        self.field_exposure = exposure;
        self
    }

    /// As [`Self::with_field_provider`], plus **share** the drawn `Sha256Field`
    /// relation through `handle` so a sibling module consumes it over the
    /// identical `LookupElements`. The handle is populated during
    /// [`Air::draw_relations`].
    pub fn with_field_handle(
        mut self,
        exposure: FieldExposure,
        handle: air_core::relations::SharedFieldRelation,
    ) -> Self {
        self.field_exposure = exposure;
        self.field_handle = Some(handle);
        self
    }

    pub fn with_shared_tables(mut self, shared: SharedShaTableRelations) -> Self {
        self.shared_tables = Some(shared);
        self
    }

    /// Namespace the witness-independent preprocessed IDs and public
    /// transcript. An empty namespace uses the canonical unnamespaced IDs and
    /// adds no namespace transcript fields. Prover and verifier must use the
    /// same value.
    pub fn with_instance_namespace(mut self, namespace: impl Into<String>) -> Self {
        self.instance_namespace = namespace.into();
        self
    }

    /// Test-only hook: commit `base` verbatim instead of the
    /// witness-derived generator's output. Adversarial tests use this to
    /// plant an illegal cell (e.g. `is_last_block` outside its true row, or
    /// an enabler prefix that isn't block-aligned) and drive the *real*
    /// STARK prove/verify pipeline against it — `tests/constraint_negative.rs`'s
    /// hand-rolled evaluator no-ops `add_to_relation`, so it can't exercise
    /// a mutation whose only consequence surfaces through a relation (the
    /// digest LogUp) or through trace/interaction-trace inconsistency. The
    /// interaction trace is still generated from `witness` (this hook does
    /// not intercept it), so a mutated `base` that changes what a relation
    /// should have yielded is exactly the class of bug this exists to catch.
    /// `base` must match [`build_base_trace`]'s shape (same `witness`,
    /// `log_n_rows`, `field_exposure`, and shared-tables mode this builder
    /// will otherwise use) — this does not re-validate that.
    #[doc(hidden)]
    pub fn with_base(
        mut self,
        base: Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    ) -> Self {
        self.base = Some(base);
        self
    }

    fn uses_shared_tables(&self) -> bool {
        self.shared_tables.is_some()
    }

    fn built_components(&self) -> &Sha256Components {
        self.components
            .as_ref()
            .expect("components are built before they are borrowed")
    }

    /// The aggregate claim produced during the interaction phase. The caller
    /// reads it back after [`air_core::prove`] to stamp the proof. Panics if
    /// called before the interaction phase has run.
    pub fn interaction_claim(&self) -> &InteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("interaction claim is set during the interaction phase")
    }

    fn relations(&self) -> &Sha256Relations {
        self.relations
            .as_ref()
            .expect("relations are drawn before they are used")
    }
}

impl Air for Sha256Prover<'_> {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        Stmt0::new(
            self.log_n_rows,
            self.expose_digest,
            &self.field_exposure,
            self.uses_shared_tables(),
        )
        .mix_into(channel);
        mix_instance_namespace(channel, &self.instance_namespace);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let relations = if let Some(shared) = &self.shared_tables {
            Sha256Relations::draw_with_shared_tables(channel, shared)
        } else {
            Sha256Relations::draw(channel)
        };
        // Share the drawn digest / field relations with the consumer modules, if
        // composed.
        if let Some(handle) = &self.digest_handle {
            handle.set(relations.digest.digest.clone());
        }
        if let Some(handle) = &self.field_handle {
            handle.set(relations.field.field.clone());
        }
        self.relations = Some(relations);
    }

    fn layout(&self) -> TreeLayout {
        layout(
            self.log_n_rows,
            self.expose_digest,
            &self.field_exposure,
            self.uses_shared_tables(),
        )
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        flatten_claimed_sums(self.interaction_claim())
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        if self.uses_shared_tables() {
            consumer_preprocessed_column_ids_ns(&self.instance_namespace)
        } else {
            all_preprocessed_column_ids_ns(&self.instance_namespace)
        }
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, VerificationError> {
        Ok(generated_preprocessed_for_ids(
            self.log_n_rows,
            &self.instance_namespace,
            &self.preprocessed_column_ids(),
        ))
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(Sha256Components::new(
            allocator,
            self.interaction_claim(),
            self.relations(),
            self.log_n_rows,
            self.expose_digest,
            &self.field_exposure,
            !self.uses_shared_tables(),
            &self.instance_namespace,
            None,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built_components().components()
    }
}

impl AirProver for Sha256Prover<'_> {
    fn max_log_size(&self) -> u32 {
        let table_max = if self.uses_shared_tables() {
            DIGEST_BRIDGE_LOG_SIZE
        } else {
            range_log_size(crate::components::RangeKind::Range8)
        };
        table_max.max(self.log_n_rows)
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // The batch-4 LogUp finalizer gives the `Sha256Eval` consumer a
        // degree-excess of 2 (`log_n_rows + 2`, D ≤ 5 — see
        // `constraints::LOGUP_BATCH`), which raises the proof-wide
        // `composition_log_split` to 2: the composition polynomial lives at
        // `max_trace_log_size + 2`. Report `max_log_size() + 2` — not the
        // default `+ 1` — so the orchestrator's twiddles cover it.
        self.max_log_size() + 2
    }

    fn store_polynomial_coefficients(&self) -> bool {
        true
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let ids = self.preprocessed_column_ids();
        let preprocessed = match self.preprocessed.take() {
            Some(evals) if !self.uses_shared_tables() => evals,
            Some(evals) => {
                let full_ids = all_preprocessed_column_ids_ns(&self.instance_namespace);
                ids.iter()
                    .map(|selected_id| {
                        full_ids
                            .iter()
                            .zip(&evals)
                            .find_map(|(id, column)| (id == selected_id).then(|| column.clone()))
                            .unwrap_or_else(|| {
                                panic!(
                                    "selected preprocessed column {} is not owned by this SHA-256 module",
                                    selected_id.id
                                )
                            })
                    })
                    .collect()
            }
            None => generated_preprocessed_for_ids(self.log_n_rows, &self.instance_namespace, &ids),
        };
        tb.extend_evals(preprocessed);
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        // Fingerprint exactly what `write_preprocessed` will commit: the caller-provided
        // evals when set, otherwise the (cached) generated trace. Do not `take` — the
        // evals must still be available for the later `write_preprocessed` call.
        let ids = self.preprocessed_column_ids();
        match &self.preprocessed {
            Some(evals) if !self.uses_shared_tables() => {
                fingerprint_preprocessed_columns("stwo_sha256::Sha256Prover", &ids, evals)
            }
            Some(evals) => {
                let full_ids = all_preprocessed_column_ids_ns(&self.instance_namespace);
                let selected: Vec<_> = ids
                    .iter()
                    .map(|selected_id| {
                        full_ids
                            .iter()
                            .zip(evals)
                            .find_map(|(id, column)| (id == selected_id).then(|| column.clone()))
                            .unwrap_or_else(|| {
                                panic!(
                                    "selected preprocessed column {} is not owned by this SHA-256 module",
                                    selected_id.id
                                )
                            })
                    })
                    .collect();
                fingerprint_preprocessed_columns("stwo_sha256::Sha256Prover", &ids, &selected)
            }
            None => {
                let evals =
                    generated_preprocessed_for_ids(self.log_n_rows, &self.instance_namespace, &ids);
                fingerprint_preprocessed_columns("stwo_sha256::Sha256Prover", &ids, &evals)
            }
        }
    }

    fn write_selected_preprocessed(
        &mut self,
        tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        // Partial-write support for cross-instance dedup: when several SHA modules
        // share one composition (e.g. the mdoc circuit's four instances), the
        // orchestrator commits each preprocessed column once and asks later
        // instances for only their non-duplicate subset — possibly none.
        let ids = self.preprocessed_column_ids();
        let preprocessed = match self.preprocessed.take() {
            Some(evals) if !self.uses_shared_tables() => evals,
            Some(evals) => {
                let full_ids = all_preprocessed_column_ids_ns(&self.instance_namespace);
                ids.iter()
                    .map(|selected_id| {
                        full_ids
                            .iter()
                            .zip(&evals)
                            .find_map(|(id, column)| (id == selected_id).then(|| column.clone()))
                            .unwrap_or_else(|| {
                                panic!(
                                    "selected preprocessed column {} is not owned by this SHA-256 module",
                                    selected_id.id
                                )
                            })
                    })
                    .collect()
            }
            None => generated_preprocessed_for_ids(self.log_n_rows, &self.instance_namespace, &ids),
        };
        if selected_ids == ids.as_slice() {
            tb.extend_evals(preprocessed);
            return;
        }
        let selected: Vec<_> = selected_ids
            .iter()
            .map(|selected_id| {
                ids.iter()
                    .zip(&preprocessed)
                    .find_map(|(id, column)| (id == selected_id).then(|| column.clone()))
                    .unwrap_or_else(|| {
                        panic!(
                            "selected preprocessed column {} is not owned by this SHA-256 module",
                            selected_id.id
                        )
                    })
            })
            .collect();
        tb.extend_evals(selected);
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let base = self.base.take().unwrap_or_else(|| {
            build_base_trace(
                self.witness,
                self.log_n_rows,
                &self.field_exposure,
                !self.uses_shared_tables(),
            )
        });
        tb.extend_evals(base);
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let (interaction_evals, interaction_claim) = if self.uses_shared_tables() {
            generate_consumer_interaction_trace(
                self.relations(),
                self.witness,
                self.log_n_rows,
                self.expose_digest,
                &self.field_exposure,
            )
        } else {
            generate_interaction_trace(
                self.relations(),
                self.witness,
                self.log_n_rows,
                self.expose_digest,
                &self.field_exposure,
            )
        };
        tb.extend_evals(interaction_evals);
        self.interaction_claim = Some(interaction_claim);
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        self.built_components().component_provers()
    }
}

/// Verifier-side module: built from the public size surface and the proof's
/// aggregate claim. It has no witness and only implements [`Air`].
pub struct Sha256Verifier {
    log_n_rows: u32,
    instance_namespace: String,
    expose_digest: bool,
    digest_handle: Option<air_core::relations::SharedDigestRelation>,
    field_exposure: FieldExposure,
    field_handle: Option<air_core::relations::SharedFieldRelation>,
    shared_tables: Option<SharedShaTableRelations>,
    interaction_claim: InteractionClaim,
    relations: Option<Sha256Relations>,
    components: Option<Sha256Components>,
}

impl Sha256Verifier {
    pub fn new(log_n_rows: u32, interaction_claim: InteractionClaim) -> Self {
        Self {
            log_n_rows,
            instance_namespace: String::new(),
            expose_digest: false,
            digest_handle: None,
            field_exposure: FieldExposure::empty(),
            field_handle: None,
            shared_tables: None,
            interaction_claim,
            relations: None,
            components: None,
        }
    }

    /// Match a [`Sha256Prover::with_digest_provider`] proof: reconstruct the
    /// verifier with the digest provider active so the interaction-column
    /// layout and the mixed [`Stmt0`] flag agree with the prover's transcript.
    /// Must be set iff the prover set it.
    pub fn with_digest_provider(mut self) -> Self {
        self.expose_digest = true;
        self
    }

    /// Match a [`Sha256Prover::with_digest_handle`] proof: share the drawn
    /// digest relation with the consumer module through `handle`.
    pub fn with_digest_handle(mut self, handle: air_core::relations::SharedDigestRelation) -> Self {
        self.expose_digest = true;
        self.digest_handle = Some(handle);
        self
    }

    /// Match a [`Sha256Prover::with_field_provider`] proof: reconstruct the
    /// verifier with the **same** field exposure so the trace/interaction
    /// layout and the mixed [`Stmt0`] shape agree with the prover's transcript.
    /// Must be set identically to the prover's exposure.
    pub fn with_field_provider(mut self, exposure: FieldExposure) -> Self {
        self.field_exposure = exposure;
        self
    }

    /// Match a [`Sha256Prover::with_field_handle`] proof: share the drawn field
    /// relation with the consumer module through `handle`.
    pub fn with_field_handle(
        mut self,
        exposure: FieldExposure,
        handle: air_core::relations::SharedFieldRelation,
    ) -> Self {
        self.field_exposure = exposure;
        self.field_handle = Some(handle);
        self
    }

    pub fn with_shared_tables(mut self, shared: SharedShaTableRelations) -> Self {
        self.shared_tables = Some(shared);
        self
    }

    /// Match [`Sha256Prover::with_instance_namespace`]. An empty value selects
    /// the canonical unnamespaced instance.
    pub fn with_instance_namespace(mut self, namespace: impl Into<String>) -> Self {
        self.instance_namespace = namespace.into();
        self
    }

    fn uses_shared_tables(&self) -> bool {
        self.shared_tables.is_some()
    }

    fn relations(&self) -> &Sha256Relations {
        self.relations
            .as_ref()
            .expect("relations are drawn before they are used")
    }

    fn built_components(&self) -> &Sha256Components {
        self.components
            .as_ref()
            .expect("components are built before they are borrowed")
    }
}

impl Air for Sha256Verifier {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        Stmt0::new(
            self.log_n_rows,
            self.expose_digest,
            &self.field_exposure,
            self.uses_shared_tables(),
        )
        .mix_into(channel);
        mix_instance_namespace(channel, &self.instance_namespace);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let relations = if let Some(shared) = &self.shared_tables {
            Sha256Relations::draw_with_shared_tables(channel, shared)
        } else {
            Sha256Relations::draw(channel)
        };
        if let Some(handle) = &self.digest_handle {
            handle.set(relations.digest.digest.clone());
        }
        if let Some(handle) = &self.field_handle {
            handle.set(relations.field.field.clone());
        }
        self.relations = Some(relations);
    }

    fn layout(&self) -> TreeLayout {
        layout(
            self.log_n_rows,
            self.expose_digest,
            &self.field_exposure,
            self.uses_shared_tables(),
        )
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        flatten_claimed_sums(&self.interaction_claim)
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        if self.uses_shared_tables() {
            consumer_preprocessed_column_ids_ns(&self.instance_namespace)
        } else {
            all_preprocessed_column_ids_ns(&self.instance_namespace)
        }
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, VerificationError> {
        Ok(generated_preprocessed_for_ids(
            self.log_n_rows,
            &self.instance_namespace,
            &self.preprocessed_column_ids(),
        ))
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(Sha256Components::new(
            allocator,
            &self.interaction_claim,
            self.relations(),
            self.log_n_rows,
            self.expose_digest,
            &self.field_exposure,
            !self.uses_shared_tables(),
            &self.instance_namespace,
            None,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built_components().components()
    }
}

// ---------------------------------------------------------------------------
// Trace and component mechanics
// ---------------------------------------------------------------------------

/// Per-proof "statement 0": fixes the component log-size surface so the
/// channel state agrees on both sides.
const FULL_PADDED_STREAM_TRANSCRIPT_TAG: u64 = 0x5348_4153_5452_4541; // "SHASTREA"
const INSTANCE_NAMESPACE_TRANSCRIPT_TAG: u64 = 0x5348_4149_4e53_544e; // "SHAINSTN"
const TRANSCRIPT_GROUP_WIDTH: u64 = 6;

fn mix_instance_namespace(channel: &mut Blake2sChannel, instance_namespace: &str) {
    if instance_namespace.is_empty() {
        return;
    }
    channel.mix_u64(INSTANCE_NAMESPACE_TRANSCRIPT_TAG);
    channel.mix_u64(instance_namespace.len() as u64);
    for &byte in instance_namespace.as_bytes() {
        channel.mix_u64(u64::from(byte));
    }
}

struct Stmt0 {
    log_n_rows: u32,
    /// Whether the cross-component digest provider is active. The transcript
    /// binds the digest relation topology and its claim.
    expose_digest: bool,
    n_field_columns: u32,
    n_field_yields: u32,
    binds_full_padded_message: bool,
    /// Complete padded-stream provider configuration.
    full_padded_stream: Option<(u32, u64)>,
    /// Whether a sibling module supplies the fixed SHA table providers. A
    /// standalone instance adds no flag.
    shared_tables: bool,
}
impl Stmt0 {
    fn new(
        log_n_rows: u32,
        expose_digest: bool,
        field_exposure: &FieldExposure,
        shared_tables: bool,
    ) -> Self {
        Self {
            log_n_rows,
            expose_digest,
            n_field_columns: field_exposure.n_columns() as u32,
            n_field_yields: field_exposure.n_yields() as u32,
            binds_full_padded_message: !field_exposure.is_empty(),
            full_padded_stream: field_exposure
                .full_padded_stream()
                .map(|(field_id, padded_len)| (field_id, padded_len as u64)),
            shared_tables,
        }
    }

    fn mix_into(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(self.log_n_rows as u64);
        // Keep this fixed slot for compatibility with the canonical transcript.
        channel.mix_u64(TRANSCRIPT_GROUP_WIDTH);
        channel.mix_u64(u64::from(self.expose_digest));
        channel.mix_u64(u64::from(self.n_field_columns));
        channel.mix_u64(u64::from(self.n_field_yields));
        channel.mix_u64(u64::from(self.binds_full_padded_message));
        if let Some((field_id, padded_len)) = self.full_padded_stream {
            channel.mix_u64(FULL_PADDED_STREAM_TRANSCRIPT_TAG);
            channel.mix_u64(field_id as u64);
            channel.mix_u64(padded_len);
        }
        if self.shared_tables {
            channel.mix_u64(1);
        }
    }
}

/// Pack a `Vec<u32>` multiplicity vector into a SIMD `BaseColumn`-backed
/// `CircleEvaluation` at the given `log_size`. The vector's length must
/// equal `1 << log_size`.
fn mult_col_to_eval(
    mults: &[u32],
    log_size: u32,
) -> CircleEvaluation<SimdBackend, BaseField, BitReversedOrder> {
    debug_assert_eq!(mults.len(), 1usize << log_size);
    let domain = CanonicCoset::new(log_size).circle_domain();
    let col: BaseColumn = mults.iter().map(|&m| BaseField::from(m)).collect();
    CircleEvaluation::new(domain, col)
}

/// Build the base trace in component order: the `Sha256Eval` columns, the
/// fixed digest bridge, and one producer multiplicity column per range table.
///
/// `pub` (rather than crate-private) so adversarial tests can build a base
/// trace, mutate a specific cell, and feed it back through
/// [`Sha256Prover::with_base`].
pub fn build_base_trace(
    witness: &Sha256Witness,
    log_n_rows: u32,
    field_exposure: &FieldExposure,
    include_table_providers: bool,
) -> Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let mut base_trace: Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> =
        Vec::new();

    let sha_main =
        crate::trace::generate_trace_base_columns_with_fields(witness, log_n_rows, field_exposure);
    debug_assert_eq!(
        sha_main.len(),
        Layout::total_cols_with_fields(field_exposure.n_columns())
    );
    let sha_domain = CanonicCoset::new(log_n_rows).circle_domain();
    for col in sha_main {
        base_trace.push(CircleEvaluation::new(sha_domain, col));
    }

    let bridge_domain = CanonicCoset::new(DIGEST_BRIDGE_LOG_SIZE).circle_domain();
    for col in crate::digest_bridge::generate_digest_bridge_trace(witness) {
        base_trace.push(CircleEvaluation::new(bridge_domain, col));
    }

    if !include_table_providers {
        return base_trace;
    }
    // Multiplicity columns — same order as `Sha256Components::component_provers`.
    for &kind in RANGE_TABLES {
        let mults = range_k_multiplicities(witness, kind);
        base_trace.push(mult_col_to_eval(&mults, range_log_size(kind)));
    }

    base_trace
}

/// Return each base-trace log size in commit order. The order is the main SHA
/// trace, the fixed digest bridge, and the range-table producer columns.
fn base_trace_log_sizes(
    log_n_rows: u32,
    n_field_cols: usize,
    include_table_providers: bool,
) -> Vec<u32> {
    // Base columns + the dynamic credential-field byte tail, all at the
    // trace's `log_n_rows`. Empty exposure leaves this at `Layout::TOTAL_COLS`.
    let mut out = vec![log_n_rows; Layout::total_cols_with_fields(n_field_cols)];
    out.extend(std::iter::repeat_n(
        DIGEST_BRIDGE_LOG_SIZE,
        DIGEST_BRIDGE_BASE_COLS,
    ));
    if !include_table_providers {
        return out;
    }
    // 4 range mults, each at its own `range_log_size(kind)`.
    for &kind in RANGE_TABLES {
        out.push(range_log_size(kind));
    }
    out
}

/// log_sizes of every interaction-trace column in commit order. Each
/// component's column count is `ceil(n_lookups / batch)` — batch 4
/// ([`LOGUP_BATCH`]) for the `Sha256Eval` consumer, pairs for the
/// single-lookup producers. We infer the count from the structural firing
/// rule (matching the `interaction::sha256_interaction` derivation).
fn interaction_trace_log_sizes(
    log_n_rows: u32,
    expose_digest: bool,
    field_exposure: &FieldExposure,
    include_table_providers: bool,
) -> Vec<u32> {
    let mut out = Vec::new();

    // Each SecureField interaction column expands to SECURE_EXTENSION_DEGREE = 4
    // base-field columns at the same log_size.
    const EXT: usize = SECURE_EXTENSION_DEGREE;

    // Main SHA consumer, then the fixed 16-row digest bridge.
    let sha_cols = num_batched_cols(sha_lookups_per_row(field_exposure), LOGUP_BATCH);
    out.extend(std::iter::repeat_n(log_n_rows, sha_cols * EXT));
    let bridge_cols = num_batched_cols(digest_bridge_lookups(expose_digest), LOGUP_BATCH);
    out.extend(std::iter::repeat_n(
        DIGEST_BRIDGE_LOG_SIZE,
        bridge_cols * EXT,
    ));
    if !include_table_providers {
        return out;
    }
    // 4 Range_k producers: 1 lookup each, at the kind's own log_size.
    for &kind in RANGE_TABLES {
        out.extend(std::iter::repeat_n(
            range_log_size(kind),
            num_batched_cols(1, 2) * EXT,
        ));
    }
    out
}

fn consumer_preprocessed_log_sizes(log_n_rows: u32) -> Vec<u32> {
    let mut out: Vec<_> = std::iter::repeat_n(log_n_rows, 10).collect();
    out.push(DIGEST_BRIDGE_LOG_SIZE);
    out
}

fn generated_preprocessed_for_ids(
    log_n_rows: u32,
    instance_namespace: &str,
    selected_ids: &[PreProcessedColumnId],
) -> Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let (evals, _generated_ids, _log_sizes) = generate_preprocessed_trace(log_n_rows);
    let ids = all_preprocessed_column_ids_ns(instance_namespace);
    selected_ids
        .iter()
        .map(|selected_id| {
            ids.iter()
                .zip(&evals)
                .find_map(|(id, column)| (id == selected_id).then(|| column.clone()))
                .unwrap_or_else(|| {
                    panic!(
                        "selected preprocessed column {} is not owned by this SHA-256 module",
                        selected_id.id
                    )
                })
        })
        .collect()
}

/// Number of interaction columns produced by `n_lookups` lookups batched
/// `batch` fractions per column: `ceil(n_lookups / batch)`.
#[inline]
const fn num_batched_cols(n_lookups: usize, batch: usize) -> usize {
    n_lookups.div_ceil(batch)
}

/// Aggregate of every `FrameworkComponent` in the proof, in commit order.
struct Sha256Components {
    sha256: FrameworkComponent<Sha256Eval>,
    digest_bridge: FrameworkComponent<DigestBridgeEval>,
    range: Vec<FrameworkComponent<RangeKEval>>,
}

impl Sha256Components {
    #[allow(clippy::too_many_arguments)]
    fn new(
        allocator: &mut TraceLocationAllocator,
        claim: &InteractionClaim,
        relations: &Sha256Relations,
        log_n_rows: u32,
        expose_digest: bool,
        field_exposure: &FieldExposure,
        include_table_providers: bool,
        instance_namespace: &str,
        claim_mask_beta: Option<QM31>,
    ) -> Self {
        // The shared TraceLocationAllocator (seeded by the orchestrator with
        // every module's `preprocessed_column_ids` in commit order) runs the
        // same component order on prover and verifier; each FrameworkComponent
        // claims its slice of preprocessed columns as it is built.
        let sha256 = FrameworkComponent::new(
            allocator,
            Sha256Eval {
                log_size: log_n_rows,
                relations: relations.clone(),
                field_exposure: field_exposure.clone(),
                instance_namespace: instance_namespace.to_string(),
                claim_mask_beta,
            },
            claim.sha256.claimed_sum,
        );

        let digest_bridge = FrameworkComponent::new(
            allocator,
            DigestBridgeEval {
                relations: relations.clone(),
                expose_digest,
                instance_namespace: instance_namespace.to_string(),
            },
            claim.digest_bridge.claimed_sum,
        );

        let mut range = Vec::with_capacity(RANGE_TABLES.len());
        if include_table_providers {
            for (i, &kind) in RANGE_TABLES.iter().enumerate() {
                range.push(FrameworkComponent::new(
                    allocator,
                    RangeKEval {
                        log_size: range_log_size(kind),
                        kind,
                        relations: relations.clone(),
                        shared_tables: false,
                    },
                    claim.range[i].claimed_sum,
                ));
            }
        }

        Self {
            sha256,
            digest_bridge,
            range,
        }
    }

    /// Borrow every component as `dyn Component`, in commit order — the
    /// verifier-side surface the orchestrator consumes.
    fn components(&self) -> Vec<&dyn Component> {
        let mut out: Vec<&dyn Component> = Vec::new();
        out.push(&self.sha256);
        out.push(&self.digest_bridge);
        out.extend(self.range.iter().map(|c| c as &dyn Component));
        out
    }

    /// Borrow every component as `dyn ComponentProver`, in commit order — the
    /// prover-side surface the orchestrator consumes.
    fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        let mut out: Vec<&dyn ComponentProver<SimdBackend>> = Vec::new();
        out.push(&self.sha256);
        out.push(&self.digest_bridge);
        out.extend(
            self.range
                .iter()
                .map(|c| c as &dyn ComponentProver<SimdBackend>),
        );
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn transcript_relations_ns(
        exposure: &FieldExposure,
        instance_namespace: &str,
    ) -> Sha256Relations {
        let mut channel = Blake2sChannel::default();
        Stmt0::new(13, false, exposure, false).mix_into(&mut channel);
        mix_instance_namespace(&mut channel, instance_namespace);
        Sha256Relations::draw(&mut channel)
    }

    fn transcript_relations(exposure: &FieldExposure) -> Sha256Relations {
        transcript_relations_ns(exposure, "")
    }

    #[test]
    fn full_padded_stream_layout_is_fixed_across_padded_lengths() {
        let one_block = FieldExposure::from_full_padded_stream(77, 64);
        let sixty_five_blocks = FieldExposure::from_full_padded_stream(77, 65 * 64);
        let first = layout(13, false, &one_block, false);
        let second = layout(13, false, &sixty_five_blocks, false);

        assert_eq!(first.preprocessed, second.preprocessed);
        assert_eq!(first.trace, second.trace);
        assert_eq!(first.interaction, second.interaction);
        assert_eq!(
            first.trace.len(),
            Layout::TOTAL_COLS
                + 1
                + crate::constants::DIGEST_BYTES
                + crate::components::RANGE_TABLES.len()
        );
        assert_eq!(
            crate::interaction::sha_lookups_per_row(&one_block),
            crate::interaction::SHA_LOOKUPS_PER_ROW_BASE
                + crate::field_exposure::FULL_PADDED_STREAM_SITES_PER_ROW,
        );
    }

    #[test]
    fn full_padded_stream_transcript_binds_mode_field_and_length() {
        let base = FieldExposure::from_full_padded_stream(77, 64);
        let same = FieldExposure::from_full_padded_stream(77, 64);
        let different_field = FieldExposure::from_full_padded_stream(78, 64);
        let different_length = FieldExposure::from_full_padded_stream(77, 128);

        assert_eq!(transcript_relations(&base), transcript_relations(&same));
        assert_ne!(
            transcript_relations(&base),
            transcript_relations(&different_field)
        );
        assert_ne!(
            transcript_relations(&base),
            transcript_relations(&different_length)
        );

        let stmt = Stmt0::new(13, false, &base, false);
        assert_eq!(stmt.full_padded_stream, Some((77, 64)));
    }

    #[test]
    fn empty_instance_namespace_preserves_unnamespaced_transcript_challenge() {
        let exposure = FieldExposure::empty();
        let mut expected_channel = Blake2sChannel::default();
        expected_channel.mix_u64(13);
        expected_channel.mix_u64(TRANSCRIPT_GROUP_WIDTH);
        expected_channel.mix_u64(0);
        expected_channel.mix_u64(0);
        expected_channel.mix_u64(0);
        expected_channel.mix_u64(0);
        let expected_relations = Sha256Relations::draw(&mut expected_channel);

        let witness = crate::witness::compute_sha256_witness(b"default-instance");
        let prover = Sha256Prover::new(&witness, 13);
        let mut default_channel = Blake2sChannel::default();
        prover.mix_public(&mut default_channel);
        assert_eq!(
            Sha256Relations::draw(&mut default_channel),
            expected_relations,
            "default namespace must not add a transcript element"
        );
        assert_eq!(
            prover.preprocessed_column_ids(),
            crate::components::all_preprocessed_column_ids(),
            "default constructor must use the canonical unnamespaced ID vector"
        );
        assert_ne!(
            transcript_relations_ns(&exposure, "mdoc/mso-sha"),
            expected_relations
        );
        assert_ne!(
            transcript_relations_ns(&exposure, "mdoc/mso-sha"),
            transcript_relations_ns(&exposure, "mdoc/mso-sha-2")
        );
    }

    #[test]
    fn namespaced_preprocessed_columns_are_witness_independent() {
        let first_witness = crate::witness::compute_sha256_witness(b"credential-a");
        let second_witness = crate::witness::compute_sha256_witness(b"credential-b");
        let exposure = FieldExposure::from_full_padded_stream(77, 64);
        let mut first = Sha256Prover::new(&first_witness, 13)
            .with_field_provider(exposure.clone())
            .with_instance_namespace("mdoc/mso-sha");
        let mut second = Sha256Prover::new(&second_witness, 13)
            .with_field_provider(exposure)
            .with_instance_namespace("mdoc/mso-sha");

        assert_eq!(
            first.preprocessed_column_fingerprints(),
            second.preprocessed_column_fingerprints()
        );
        assert_eq!(
            first
                .canonical_preprocessed_columns()
                .expect("first canonical tree-zero columns")
                .len(),
            first.preprocessed_column_ids().len()
        );
    }
}
