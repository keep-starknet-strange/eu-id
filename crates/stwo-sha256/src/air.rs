//! Wraps the SHA-256 AIR as an [`air_core`] proving module.
//!
//! [`Sha256Prover`] holds the witness and contributes every column (prover
//! side); [`Sha256Verifier`] holds only the public size surface and the
//! claimed sums from the proof (verifier side). Both drive the same four
//! phases the standalone prover used to run inline — preprocessed lookup
//! tables, base trace + producer multiplicities, per-component interaction
//! trace, and component assembly — but now against the shared channel and
//! commitment scheme [`air_core::prove`]/[`air_core::verify`] own.
//!
//! Transcript order is unchanged from the old standalone path except for the
//! claimed-sum mix: the orchestrator mixes every module's [`Air::claimed_sums`]
//! as one flat slice (see [`flatten_claimed_sums`]) rather than each
//! component's sum individually. Both `air_core::prove` and `air_core::verify`
//! mix identically, so the round trip is self-consistent.

use air_core::claim_mask::{ClaimMaskTrace, SharedClaimMaskChallenge, CLAIM_MASK_TRACE_COLUMNS};
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
    all_preprocessed_column_ids, consumer_preprocessed_column_ids, range_log_size, RangeKEval,
    Sha256Relations, RANGE_TABLES,
};
use crate::constraints::{Sha256Eval, LOGUP_BATCH};
use crate::field_exposure::FieldExposure;
use crate::interaction::{
    generate_consumer_interaction_trace, generate_interaction_trace, sha_lookups_per_row,
    InteractionClaim,
};
use crate::multiplicities::range_k_multiplicities;
use crate::preprocessed::{generate_preprocessed_trace, preprocessed_log_sizes, LOG_SIZE_16};
use crate::relations::SharedShaTableRelations;
use crate::trace::Layout;
use crate::types::Sha256Witness;

/// Column log-sizes per tree, shared by prover and verifier — they depend
/// only on the public size surface (`log_n_rows`, `group_width`), never on the
/// witness.
fn layout(
    log_n_rows: u32,
    group_width: u32,
    expose_digest: bool,
    field_exposure: &FieldExposure,
    shared_tables: bool,
) -> TreeLayout {
    TreeLayout {
        preprocessed: if shared_tables {
            consumer_preprocessed_log_sizes(log_n_rows)
        } else {
            preprocessed_log_sizes(group_width, log_n_rows)
        },
        trace: base_trace_log_sizes(
            log_n_rows,
            group_width,
            field_exposure.n_columns(),
            !shared_tables,
        ),
        interaction: interaction_trace_log_sizes(
            log_n_rows,
            group_width,
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
    out.extend(claim.range.iter().map(|c| c.claimed_sum));
    out
}

/// Prover-side module: built from the witness and the public size surface.
pub struct Sha256Prover<'a> {
    witness: &'a Sha256Witness,
    log_n_rows: u32,
    group_width: u32,
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
    pub fn new(witness: &'a Sha256Witness, log_n_rows: u32, group_width: u32) -> Self {
        Self {
            witness,
            log_n_rows,
            group_width,
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

    /// Enable the credential-field provider: the module yields the given
    /// byte windows on the `Sha256Field` channel so predicate consumers
    /// can require them. Like [`Self::with_digest_provider`] this
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
    /// relation through `handle` so the predicate modules consume it over the
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
            self.group_width,
            self.expose_digest,
            &self.field_exposure,
            self.uses_shared_tables(),
        )
        .mix_into(channel);
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
            self.group_width,
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
            consumer_preprocessed_column_ids()
        } else {
            all_preprocessed_column_ids()
        }
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(Sha256Components::new(
            allocator,
            self.interaction_claim(),
            self.relations(),
            self.log_n_rows,
            self.group_width,
            self.expose_digest,
            &self.field_exposure,
            !self.uses_shared_tables(),
            &None,
            None,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built_components().components()
    }
}

impl AirProver for Sha256Prover<'_> {
    fn max_log_size(&self) -> u32 {
        let _ = self.group_width;
        LOG_SIZE_16.max(self.log_n_rows)
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
                let full_ids = all_preprocessed_column_ids();
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
            None => generated_preprocessed_for_ids(self.group_width, self.log_n_rows, &ids),
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
                let full_ids = all_preprocessed_column_ids();
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
                let evals = generated_preprocessed_for_ids(self.group_width, self.log_n_rows, &ids);
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
                let full_ids = all_preprocessed_column_ids();
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
            None => generated_preprocessed_for_ids(self.group_width, self.log_n_rows, &ids),
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
                self.group_width,
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
                self.group_width,
                self.expose_digest,
                &self.field_exposure,
            )
        } else {
            generate_interaction_trace(
                self.relations(),
                self.witness,
                self.log_n_rows,
                self.group_width,
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
    group_width: u32,
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
    pub fn new(log_n_rows: u32, group_width: u32, interaction_claim: InteractionClaim) -> Self {
        Self {
            log_n_rows,
            group_width,
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
            self.group_width,
            self.expose_digest,
            &self.field_exposure,
            self.uses_shared_tables(),
        )
        .mix_into(channel);
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
            self.group_width,
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
            consumer_preprocessed_column_ids()
        } else {
            all_preprocessed_column_ids()
        }
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(Sha256Components::new(
            allocator,
            &self.interaction_claim,
            self.relations(),
            self.log_n_rows,
            self.group_width,
            self.expose_digest,
            &self.field_exposure,
            !self.uses_shared_tables(),
            &None,
            None,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built_components().components()
    }
}

// ---------------------------------------------------------------------------
// Trace + component mechanics (moved verbatim from `stark.rs`)
// ---------------------------------------------------------------------------

/// Per-proof "statement 0": fixes the component log-size surface so the
/// channel state agrees on both sides.
struct Stmt0 {
    log_n_rows: u32,
    group_width: u32,
    /// Whether the cross-component digest provider is active. Mixed into the
    /// transcript so the prover and verifier agree on the lookup count (and
    /// hence the interaction-column layout); a mismatch reshapes the
    /// interaction tree and the verifier rejects.
    expose_digest: bool,
    /// Credential-field exposure shape — `(byte columns, yields)`. Mixed for the
    /// same reason as `expose_digest`: the column count sets the base-trace
    /// width and the yield count sets the consumer's interaction-column count,
    /// so a prover/verifier disagreement reshapes the trees and the verifier
    /// rejects.
    n_field_columns: u32,
    n_field_yields: u32,
    binds_full_padded_message: bool,
    /// Whether fixed SHA table providers are supplied by a sibling module.
    /// Only the enabled case is mixed so the legacy standalone transcript
    /// remains byte-identical.
    shared_tables: bool,
}
impl Stmt0 {
    fn new(
        log_n_rows: u32,
        group_width: u32,
        expose_digest: bool,
        field_exposure: &FieldExposure,
        shared_tables: bool,
    ) -> Self {
        Self {
            log_n_rows,
            group_width,
            expose_digest,
            n_field_columns: field_exposure.n_columns() as u32,
            n_field_yields: field_exposure.n_yields() as u32,
            binds_full_padded_message: field_exposure.binds_full_padded_message(),
            shared_tables,
        }
    }

    fn mix_into(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(self.log_n_rows as u64);
        channel.mix_u64(self.group_width as u64);
        channel.mix_u64(u64::from(self.expose_digest));
        channel.mix_u64(u64::from(self.n_field_columns));
        channel.mix_u64(u64::from(self.n_field_yields));
        channel.mix_u64(u64::from(self.binds_full_padded_message));
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

/// Build the base trace: the `Sha256Eval` columns first
/// (`TOTAL_COLS` × `log_n_rows`), then one producer multiplicity column per
/// table, in `component_provers` order.
fn build_base_trace(
    witness: &Sha256Witness,
    log_n_rows: u32,
    group_width: u32,
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

    let _ = group_width;
    if !include_table_providers {
        return base_trace;
    }
    // Multiplicity columns — same order as `Sha256Components::component_provers`.
    for &kind in RANGE_TABLES {
        let mults = range_k_multiplicities(witness, kind, field_exposure);
        base_trace.push(mult_col_to_eval(&mults, range_log_size(kind)));
    }

    base_trace
}

/// log_sizes of every base-trace column in commit order. The Sha256Eval
/// block first (`TOTAL_COLS` × `log_n_rows`), then one mult col per
/// producer component.
fn base_trace_log_sizes(
    log_n_rows: u32,
    group_width: u32,
    n_field_cols: usize,
    include_table_providers: bool,
) -> Vec<u32> {
    // Base columns + the dynamic credential-field byte tail, all at the
    // trace's `log_n_rows`. Empty exposure leaves this at `Layout::TOTAL_COLS`.
    let mut out = vec![log_n_rows; Layout::total_cols_with_fields(n_field_cols)];
    let _ = group_width;
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
    group_width: u32,
    expose_digest: bool,
    field_exposure: &FieldExposure,
    include_table_providers: bool,
) -> Vec<u32> {
    let mut out = Vec::new();

    // Each SecureField interaction column expands to SECURE_EXTENSION_DEGREE = 4
    // base-field columns at the same log_size.
    const EXT: usize = SECURE_EXTENSION_DEGREE;

    // Sha256Eval consumer: `sha_lookups_per_row(expose_digest, field_exposure)`
    // lookup sites per row (W=6 hybrid: 58, plus the digest yield when that provider
    // is on, plus the field provider's one `Range8` byte range-check per
    // exposed byte column and one yield per exposed window byte) → `ceil(n/4)`
    // batch-4 columns. Sized at log_n_rows. See `interaction::sha256_interaction`
    // for the per-row site breakdown.
    let sha_cols = num_batched_cols(
        sha_lookups_per_row(expose_digest, field_exposure),
        LOGUP_BATCH,
    );
    out.extend(std::iter::repeat_n(log_n_rows, sha_cols * EXT));
    let _ = group_width;
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
    std::iter::repeat_n(log_n_rows, 10).collect()
}

fn generated_preprocessed_for_ids(
    group_width: u32,
    log_n_rows: u32,
    selected_ids: &[PreProcessedColumnId],
) -> Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let (evals, ids, _log_sizes) = generate_preprocessed_trace(group_width, log_n_rows);
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
    range: Vec<FrameworkComponent<RangeKEval>>, // 4
}

impl Sha256Components {
    #[allow(clippy::too_many_arguments)]
    fn new(
        allocator: &mut TraceLocationAllocator,
        claim: &InteractionClaim,
        relations: &Sha256Relations,
        log_n_rows: u32,
        group_width: u32,
        expose_digest: bool,
        field_exposure: &FieldExposure,
        include_table_providers: bool,
        multi: &Option<crate::constraints::MultiSlotEval>,
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
                expose_digest,
                field_exposure: field_exposure.clone(),
                multi: multi.clone(),
                claim_mask_beta,
            },
            claim.sha256.claimed_sum,
        );

        let _ = group_width;
        let mut range = Vec::with_capacity(4);
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

        Self { sha256, range }
    }

    /// Borrow every component as `dyn Component`, in commit order — the
    /// verifier-side surface the orchestrator consumes.
    fn components(&self) -> Vec<&dyn Component> {
        let mut out: Vec<&dyn Component> = Vec::new();
        out.push(&self.sha256);
        out.extend(self.range.iter().map(|c| c as &dyn Component));
        out
    }

    /// Borrow every component as `dyn ComponentProver`, in commit order — the
    /// prover-side surface the orchestrator consumes.
    fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        let mut out: Vec<&dyn ComponentProver<SimdBackend>> = Vec::new();
        out.push(&self.sha256);
        out.extend(
            self.range
                .iter()
                .map(|c| c as &dyn ComponentProver<SimdBackend>),
        );
        out
    }
}

// ---------------------------------------------------------------------------
// Multi-message (slot-scheduled) merged consumer — S8
// ---------------------------------------------------------------------------

/// Per-slot shared-relation handles of a multi-slot consumer: the same
/// handles the per-instance `with_digest_handle` / `with_field_handle`
/// builders take, one pair per slot. `None` handles leave the drawn
/// relation module-internal (a slot that exposes nothing draws its pair
/// anyway, keeping the transcript shape schedule-determined).
#[derive(Clone, Default)]
pub struct SlotHandles {
    pub digest: Option<air_core::relations::SharedDigestRelation>,
    pub field: Option<air_core::relations::SharedFieldRelation>,
}

/// Transcript surface of a multi-slot merged SHA-256 consumer: the schedule
/// and every slot's exposure shape. A prover/verifier disagreement reshapes
/// the trees and the verifier rejects.
struct Stmt0Multi<'a> {
    log_n_rows: u32,
    config: &'a crate::slots::MultiSlotConfig,
}

impl Stmt0Multi<'_> {
    fn mix_into(&self, channel: &mut Blake2sChannel) {
        // Domain-separate from the single-instance `Stmt0` surface.
        channel.mix_u64(0x5348414d554c5449); // "SHAMULTI"
        channel.mix_u64(self.log_n_rows as u64);
        channel.mix_u64(self.config.slot_log as u64);
        channel.mix_u64(self.config.n_slots() as u64);
        for spec in &self.config.slots {
            channel.mix_u64(u64::from(spec.expose_digest));
            channel.mix_u64(spec.field_exposure.n_columns() as u64);
            channel.mix_u64(spec.field_exposure.n_yields() as u64);
            channel.mix_u64(u64::from(spec.field_exposure.binds_full_padded_message()));
        }
    }
}

/// Column log-sizes of the multi-slot consumer. Preprocessed:
/// `slot_starts + 9 cyclic + n_slots slot_sel`, all at `log_n_rows`.
fn multi_layout(
    log_n_rows: u32,
    config: &crate::slots::MultiSlotConfig,
    claim_masked: bool,
) -> TreeLayout {
    const EXT: usize = SECURE_EXTENSION_DEGREE;
    let sha_cols = num_batched_cols(
        crate::interaction::sha_multi_lookups_per_row_with_mask(config, claim_masked),
        LOGUP_BATCH,
    );
    TreeLayout {
        preprocessed: vec![log_n_rows; 10 + config.n_slots()],
        trace: vec![
            log_n_rows;
            Layout::TOTAL_COLS
                + config.n_field_columns()
                + usize::from(claim_masked) * CLAIM_MASK_TRACE_COLUMNS
        ],
        interaction: vec![log_n_rows; sha_cols * EXT],
    }
}

/// Prover-side multi-slot merged module. Shared-tables consumer ONLY (the
/// quantum composition's `ShaTablesProver` supplies the fixed tables); the
/// single-message `Sha256Prover` is untouched by multi-slot support.
pub struct Sha256MultiProver<'a> {
    witnesses: Vec<&'a Sha256Witness>,
    log_n_rows: u32,
    config: crate::slots::MultiSlotConfig,
    handles: Vec<SlotHandles>,
    shared_tables: SharedShaTableRelations,
    relations: Option<Sha256Relations>,
    slot_relations: Option<Vec<crate::relations::SlotIoRelations>>,
    interaction_claim: Option<InteractionClaim>,
    claim_mask: Option<ClaimMaskTrace>,
    claim_mask_challenge: Option<SharedClaimMaskChallenge>,
    components: Option<Sha256Components>,
}

impl<'a> Sha256MultiProver<'a> {
    pub fn new(
        witnesses: Vec<&'a Sha256Witness>,
        log_n_rows: u32,
        config: crate::slots::MultiSlotConfig,
        shared_tables: SharedShaTableRelations,
    ) -> Self {
        assert_eq!(witnesses.len(), config.n_slots(), "one witness per slot");
        assert!(
            log_n_rows >= config.min_log_n_rows(),
            "log_n_rows {log_n_rows} cannot hold the slot schedule"
        );
        for (s, witness) in witnesses.iter().enumerate() {
            assert!(
                witness.blocks.len() * crate::trace::ROWS_PER_BLOCK < config.slot_rows(),
                "slot {s} message exceeds its capacity"
            );
        }
        let handles = vec![SlotHandles::default(); config.n_slots()];
        Self {
            witnesses,
            log_n_rows,
            config,
            handles,
            shared_tables,
            relations: None,
            slot_relations: None,
            interaction_claim: None,
            claim_mask: None,
            claim_mask_challenge: None,
            components: None,
        }
    }

    /// Share slot `s`'s drawn digest relation with its consumer module.
    pub fn with_slot_digest_handle(
        mut self,
        s: usize,
        handle: air_core::relations::SharedDigestRelation,
    ) -> Self {
        assert!(
            self.config.slots[s].expose_digest,
            "slot {s} does not expose a digest"
        );
        self.handles[s].digest = Some(handle);
        self
    }

    /// Share slot `s`'s drawn field relation with its consumer modules.
    pub fn with_slot_field_handle(
        mut self,
        s: usize,
        handle: air_core::relations::SharedFieldRelation,
    ) -> Self {
        assert!(
            !self.config.slots[s].field_exposure.is_empty(),
            "slot {s} has no field exposure"
        );
        self.handles[s].field = Some(handle);
        self
    }

    pub fn interaction_claim(&self) -> &InteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("interaction claim is set during the interaction phase")
    }

    pub fn ordered_claim_mask_log_sizes(&self) -> Vec<u32> {
        vec![self.log_n_rows]
    }

    pub fn with_claim_mask(
        mut self,
        trace: ClaimMaskTrace,
        challenge: SharedClaimMaskChallenge,
    ) -> Self {
        assert_eq!(trace.log_size(), self.log_n_rows);
        self.claim_mask = Some(trace);
        self.claim_mask_challenge = Some(challenge);
        self
    }

    fn claim_mask_beta(&self) -> Option<QM31> {
        self.claim_mask_challenge
            .as_ref()
            .map(|shared| shared.require().expect("claim-mask anchor drawn last"))
    }

    fn built_components(&self) -> &Sha256Components {
        self.components
            .as_ref()
            .expect("components are built before they are borrowed")
    }

    fn multi_eval(&self) -> Option<crate::constraints::MultiSlotEval> {
        Some(crate::constraints::MultiSlotEval {
            config: self.config.clone(),
            relations: self
                .slot_relations
                .clone()
                .expect("slot relations are drawn before components are built"),
        })
    }
}

fn set_slot_handles(handles: &[SlotHandles], slot_relations: &[crate::relations::SlotIoRelations]) {
    for (handle, relations) in handles.iter().zip(slot_relations) {
        if let Some(digest) = &handle.digest {
            digest.set(relations.digest.digest.clone());
        }
        if let Some(field) = &handle.field {
            field.set(relations.field.field.clone());
        }
    }
}

impl Air for Sha256MultiProver<'_> {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        Stmt0Multi {
            log_n_rows: self.log_n_rows,
            config: &self.config,
        }
        .mix_into(channel);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let (relations, slot_relations) = Sha256Relations::draw_multi_with_shared_tables(
            channel,
            &self.shared_tables,
            self.config.n_slots(),
        );
        set_slot_handles(&self.handles, &slot_relations);
        self.relations = Some(relations);
        self.slot_relations = Some(slot_relations);
    }

    fn layout(&self) -> TreeLayout {
        multi_layout(
            self.log_n_rows,
            &self.config,
            self.claim_mask_challenge.is_some(),
        )
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        flatten_claimed_sums(self.interaction_claim())
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        crate::components::multi_consumer_preprocessed_column_ids(
            self.log_n_rows,
            self.config.slot_log,
            self.config.n_slots(),
        )
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, VerificationError> {
        Ok(
            crate::preprocessed::generate_multi_consumer_preprocessed_trace(
                self.log_n_rows,
                &self.config,
            )
            .0,
        )
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let multi = self.multi_eval();
        self.components = Some(Sha256Components::new(
            allocator,
            self.interaction_claim(),
            self.relations
                .as_ref()
                .expect("relations are drawn before components are built"),
            self.log_n_rows,
            crate::partitions::MAX_ROUND_GROUP_BITS,
            false,
            &FieldExposure::empty(),
            false,
            &multi,
            self.claim_mask_beta(),
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built_components().components()
    }
}

impl AirProver for Sha256MultiProver<'_> {
    fn max_log_size(&self) -> u32 {
        LOG_SIZE_16.max(self.log_n_rows)
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Batch-4 LogUp finalizer ⇒ degree-excess 2, as the single-message
        // consumer (see `Sha256Prover::max_constraint_log_degree_bound`).
        self.max_log_size() + 2
    }

    fn store_polynomial_coefficients(&self) -> bool {
        true
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let (evals, _ids, _log_sizes) =
            crate::preprocessed::generate_multi_consumer_preprocessed_trace(
                self.log_n_rows,
                &self.config,
            );
        tb.extend_evals(evals);
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        let (evals, ids, _log_sizes) =
            crate::preprocessed::generate_multi_consumer_preprocessed_trace(
                self.log_n_rows,
                &self.config,
            );
        fingerprint_preprocessed_columns("stwo_sha256::Sha256MultiProver", &ids, &evals)
    }

    fn write_selected_preprocessed(
        &mut self,
        tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        let (evals, ids, _log_sizes) =
            crate::preprocessed::generate_multi_consumer_preprocessed_trace(
                self.log_n_rows,
                &self.config,
            );
        if selected_ids == ids.as_slice() {
            tb.extend_evals(evals);
            return;
        }
        let selected: Vec<_> = selected_ids
            .iter()
            .map(|selected_id| {
                ids.iter()
                    .zip(&evals)
                    .find_map(|(id, column)| (id == selected_id).then(|| column.clone()))
                    .unwrap_or_else(|| {
                        panic!(
                            "selected preprocessed column {} is not owned by this multi-slot SHA-256 module",
                            selected_id.id
                        )
                    })
            })
            .collect();
        tb.extend_evals(selected);
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let base = crate::trace::generate_multi_trace_base_columns(
            &self.witnesses,
            self.log_n_rows,
            &self.config,
        );
        let domain = CanonicCoset::new(self.log_n_rows).circle_domain();
        let evals: Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> = base
            .into_iter()
            .map(|col| CircleEvaluation::new(domain, col))
            .collect();
        tb.extend_evals(evals);
        if let Some(mask) = &self.claim_mask {
            tb.extend_evals(mask.columns().to_vec());
        }
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let generated =
            if let (Some(mask), Some(beta)) = (self.claim_mask.as_ref(), self.claim_mask_beta()) {
                crate::interaction::generate_multi_consumer_interaction_trace_with_claim_mask(
                    self.relations
                        .as_ref()
                        .expect("relations are drawn before the interaction phase"),
                    self.slot_relations
                        .as_ref()
                        .expect("slot relations are drawn before the interaction phase"),
                    &self.witnesses,
                    self.log_n_rows,
                    &self.config,
                    mask,
                    beta,
                )
            } else {
                crate::interaction::generate_multi_consumer_interaction_trace(
                    self.relations
                        .as_ref()
                        .expect("relations are drawn before the interaction phase"),
                    self.slot_relations
                        .as_ref()
                        .expect("slot relations are drawn before the interaction phase"),
                    &self.witnesses,
                    self.log_n_rows,
                    &self.config,
                )
            };
        let (interaction_evals, interaction_claim) = generated;
        tb.extend_evals(interaction_evals);
        self.interaction_claim = Some(interaction_claim);
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        self.built_components().component_provers()
    }
}

/// Verifier-side multi-slot merged module: public schedule + the proof's
/// claim. Must be configured identically to the prover (same schedule, same
/// per-slot exposures, same handles) or the transcript/layout diverges and
/// verification rejects.
pub struct Sha256MultiVerifier {
    log_n_rows: u32,
    config: crate::slots::MultiSlotConfig,
    handles: Vec<SlotHandles>,
    shared_tables: SharedShaTableRelations,
    interaction_claim: InteractionClaim,
    relations: Option<Sha256Relations>,
    slot_relations: Option<Vec<crate::relations::SlotIoRelations>>,
    claim_mask_challenge: Option<SharedClaimMaskChallenge>,
    components: Option<Sha256Components>,
}

impl Sha256MultiVerifier {
    pub fn new(
        log_n_rows: u32,
        config: crate::slots::MultiSlotConfig,
        shared_tables: SharedShaTableRelations,
        interaction_claim: InteractionClaim,
    ) -> Self {
        assert!(
            log_n_rows >= config.min_log_n_rows(),
            "log_n_rows {log_n_rows} cannot hold the slot schedule"
        );
        let handles = vec![SlotHandles::default(); config.n_slots()];
        Self {
            log_n_rows,
            config,
            handles,
            shared_tables,
            interaction_claim,
            relations: None,
            slot_relations: None,
            claim_mask_challenge: None,
            components: None,
        }
    }

    /// Match a [`Sha256MultiProver::with_slot_digest_handle`] proof.
    pub fn with_slot_digest_handle(
        mut self,
        s: usize,
        handle: air_core::relations::SharedDigestRelation,
    ) -> Self {
        assert!(
            self.config.slots[s].expose_digest,
            "slot {s} does not expose a digest"
        );
        self.handles[s].digest = Some(handle);
        self
    }

    /// Match a [`Sha256MultiProver::with_slot_field_handle`] proof.
    pub fn with_slot_field_handle(
        mut self,
        s: usize,
        handle: air_core::relations::SharedFieldRelation,
    ) -> Self {
        assert!(
            !self.config.slots[s].field_exposure.is_empty(),
            "slot {s} has no field exposure"
        );
        self.handles[s].field = Some(handle);
        self
    }

    pub fn ordered_claim_mask_log_sizes(&self) -> Vec<u32> {
        vec![self.log_n_rows]
    }

    pub fn with_claim_mask(mut self, challenge: SharedClaimMaskChallenge) -> Self {
        self.claim_mask_challenge = Some(challenge);
        self
    }

    fn claim_mask_beta(&self) -> Option<QM31> {
        self.claim_mask_challenge
            .as_ref()
            .map(|shared| shared.require().expect("claim-mask anchor drawn last"))
    }

    fn built_components(&self) -> &Sha256Components {
        self.components
            .as_ref()
            .expect("components are built before they are borrowed")
    }
}

impl Air for Sha256MultiVerifier {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        Stmt0Multi {
            log_n_rows: self.log_n_rows,
            config: &self.config,
        }
        .mix_into(channel);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let (relations, slot_relations) = Sha256Relations::draw_multi_with_shared_tables(
            channel,
            &self.shared_tables,
            self.config.n_slots(),
        );
        set_slot_handles(&self.handles, &slot_relations);
        self.relations = Some(relations);
        self.slot_relations = Some(slot_relations);
    }

    fn layout(&self) -> TreeLayout {
        multi_layout(
            self.log_n_rows,
            &self.config,
            self.claim_mask_challenge.is_some(),
        )
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        flatten_claimed_sums(&self.interaction_claim)
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        crate::components::multi_consumer_preprocessed_column_ids(
            self.log_n_rows,
            self.config.slot_log,
            self.config.n_slots(),
        )
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, VerificationError> {
        Ok(
            crate::preprocessed::generate_multi_consumer_preprocessed_trace(
                self.log_n_rows,
                &self.config,
            )
            .0,
        )
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let multi = Some(crate::constraints::MultiSlotEval {
            config: self.config.clone(),
            relations: self
                .slot_relations
                .clone()
                .expect("slot relations are drawn before components are built"),
        });
        self.components = Some(Sha256Components::new(
            allocator,
            &self.interaction_claim,
            self.relations
                .as_ref()
                .expect("relations are drawn before components are built"),
            self.log_n_rows,
            crate::partitions::MAX_ROUND_GROUP_BITS,
            false,
            &FieldExposure::empty(),
            false,
            &multi,
            self.claim_mask_beta(),
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built_components().components()
    }
}
