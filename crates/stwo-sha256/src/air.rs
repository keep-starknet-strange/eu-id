//! Wraps the SHA-256 AIR as an [`air_core`] proving module.
//!
//! [`Sha256Prover`] holds the witness and contributes every prover column.
//! [`Sha256Verifier`] holds the public size values and proof claim sums.
//! Both types prepare lookup tables, base trace columns, producer counts,
//! interaction trace columns, and components.
//! [`air_core::prove`] and [`air_core::verify`] own the shared channel and
//! commitment scheme.
//!
//! The shared path preserves the standalone transcript order.
//! The claim sum mix is the only exception.
//! The orchestrator mixes each module claim as one flat slice.
//! See [`flatten_claimed_sums`].
//! The prover and verifier use the same mix.

use air_core::claim_mask::{
    ClaimMaskTrace, SharedClaimMaskChallenge, CLAIM_MASK_MIN_LOG_SIZE, CLAIM_MASK_TRACE_COLUMNS,
};
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

use crate::claim_mask::{validate_claim_masks, ShaClaimMaskConfigError};
use crate::components::{
    all_preprocessed_column_ids, consumer_preprocessed_column_ids, range_log_size, RangeKEval,
    Sha256Relations, RANGE_TABLES,
};
use crate::constraints::Sha256Eval;
use crate::field_exposure::FieldExposure;
use crate::interaction::{
    generate_consumer_interaction_trace, generate_interaction_trace,
    generate_interaction_trace_with_claim_masks, sha_lookups_per_row, InteractionClaim,
};
use crate::multiplicities::range_k_multiplicities;
use crate::preprocessed::{
    generate_preprocessed_trace, generate_preprocessed_trace_with_range_min,
    preprocessed_log_sizes, preprocessed_log_sizes_with_range_min, LOG_SIZE_16,
};
use crate::relations::SharedShaTableRelations;
use crate::trace::Layout;
use crate::types::Sha256Witness;

pub const SHA_LOCAL_RANGE_CLAIM_COUNT: usize = RANGE_TABLES.len();

/// Column log-sizes per tree, shared by prover and verifier — they depend
/// only on the public size surface, never on the witness.
fn layout(
    log_n_rows: u32,
    expose_digest: bool,
    field_exposure: &FieldExposure,
    shared_tables: bool,
    claim_masked: bool,
) -> TreeLayout {
    TreeLayout {
        preprocessed: if shared_tables {
            consumer_preprocessed_log_sizes(log_n_rows)
        } else if claim_masked {
            preprocessed_log_sizes_with_range_min(log_n_rows, CLAIM_MASK_MIN_LOG_SIZE)
        } else {
            preprocessed_log_sizes(log_n_rows)
        },
        trace: base_trace_log_sizes(
            log_n_rows,
            field_exposure.n_columns(),
            !shared_tables,
            claim_masked,
        ),
        interaction: interaction_trace_log_sizes(
            log_n_rows,
            expose_digest,
            field_exposure,
            !shared_tables,
            claim_masked,
        ),
    }
}

/// Flatten the per-component claims into one slice in component (commit) order
/// — the order `Sha256Components` adds them and the order the orchestrator
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
    claim_masks: Option<Vec<ClaimMaskTrace>>,
    claim_mask_challenge: Option<SharedClaimMaskChallenge>,
}

/// Send-only Stage-1 task input for preparing SHA preprocessed/base columns.
pub struct Sha256ColumnTask<'a> {
    witness: &'a Sha256Witness,
    log_n_rows: u32,
    field_exposure: FieldExposure,
}

/// Prepared SHA preprocessed/base columns returned by [`Sha256ColumnTask`].
pub struct Sha256PreparedColumns {
    preprocessed: Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    base: Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
}

impl<'a> Sha256ColumnTask<'a> {
    pub fn new(witness: &'a Sha256Witness, log_n_rows: u32, field_exposure: FieldExposure) -> Self {
        Self {
            witness,
            log_n_rows,
            field_exposure,
        }
    }

    pub fn run(self) -> Sha256PreparedColumns {
        let (preprocessed, _ids, _log_sizes) = generate_preprocessed_trace(self.log_n_rows);
        let base = build_base_trace(self.witness, self.log_n_rows, &self.field_exposure, true, 0);
        Sha256PreparedColumns { preprocessed, base }
    }
}

impl<'a> Sha256Prover<'a> {
    pub fn new(witness: &'a Sha256Witness, log_n_rows: u32) -> Self {
        Self {
            witness,
            log_n_rows,
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
            claim_masks: None,
            claim_mask_challenge: None,
        }
    }

    pub fn new_with_prepared(
        witness: &'a Sha256Witness,
        log_n_rows: u32,
        field_exposure: FieldExposure,
        prepared: Sha256PreparedColumns,
    ) -> Self {
        let mut prover = Self::new(witness, log_n_rows);
        prover.field_exposure = field_exposure;
        prover.preprocessed = Some(prepared.preprocessed);
        prover.base = Some(prepared.base);
        prover
    }

    /// Enable the cross-component digest provider.
    ///
    /// The module yields the final digest on the `Sha256Digest` channel.
    /// A composed consumer can then require the digest.
    /// The standalone claim sum stays nonzero without that consumer.
    /// The default configuration keeps this provider off.
    /// `Stmt0` binds the flag to the transcript.
    /// The matching [`Sha256Verifier`] must use the same value.
    pub fn with_digest_provider(mut self) -> Self {
        self.expose_digest = true;
        self
    }

    /// As [`Self::with_digest_provider`], plus **share** the drawn
    /// `Sha256Digest` relation through `handle` so a sibling module (the P256
    /// digest-bind bridge) consumes it over the identical `LookupElements`.
    /// [`Air::draw_relations`] stores the relation in the handle.
    pub fn with_digest_handle(mut self, handle: air_core::relations::SharedDigestRelation) -> Self {
        self.expose_digest = true;
        self.digest_handle = Some(handle);
        self
    }

    /// Enable the credential-field provider: the module yields the given
    /// byte windows on the `Sha256Field` channel so predicate consumers
    /// can require them. Like [`Self::with_digest_provider`] this
    /// leaves the module's claimed sum nonzero until a consumer cancels it.
    /// The default configuration keeps it off. `Stmt0` mixes the exposure
    /// shape into the transcript. Configure the matching [`Sha256Verifier`]
    /// with the same shape. [`Self::with_field_handle`] also shares the
    /// relation with the consumer module.
    pub fn with_field_provider(mut self, exposure: FieldExposure) -> Self {
        self.field_exposure = exposure;
        self
    }

    /// As [`Self::with_field_provider`], plus **share** the drawn `Sha256Field`
    /// relation through `handle` so the predicate modules consume it over the
    /// identical `LookupElements`. [`Air::draw_relations`] stores the relation
    /// in the handle.
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
        assert!(
            self.claim_masks.is_none(),
            "configure shared SHA tables before supplying ordered claim masks"
        );
        self.shared_tables = Some(shared);
        self
    }

    fn uses_shared_tables(&self) -> bool {
        self.shared_tables.is_some()
    }

    fn local_range_min_log_size(&self) -> u32 {
        if self.claim_masks.is_some() && !self.uses_shared_tables() {
            CLAIM_MASK_MIN_LOG_SIZE
        } else {
            0
        }
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

    /// Claim-bearing component log sizes in exact component/serialization
    /// order. This is the order in which the caller must take masks from the
    /// global zero-sum ring.
    pub fn ordered_claim_mask_log_sizes(&self) -> Vec<u32> {
        let mut sizes = vec![self.log_n_rows];
        if !self.uses_shared_tables() {
            sizes.extend(
                RANGE_TABLES
                    .iter()
                    .map(|&kind| range_log_size(kind).max(CLAIM_MASK_MIN_LOG_SIZE)),
            );
        }
        sizes
    }

    /// Enable private claimed sums for the main SHA component and every local
    /// range provider owned by this module.
    pub fn with_claim_masks(
        mut self,
        traces: Vec<ClaimMaskTrace>,
        challenge: SharedClaimMaskChallenge,
    ) -> Result<Self, ShaClaimMaskConfigError> {
        validate_claim_masks(&self.ordered_claim_mask_log_sizes(), &traces)?;
        self.claim_masks = Some(traces);
        self.claim_mask_challenge = Some(challenge);
        Ok(self)
    }

    fn claim_mask_beta(&self) -> Option<QM31> {
        self.claim_mask_challenge.as_ref().map(|shared| {
            shared
                .require()
                .expect("claim-mask challenge anchor must follow all masked SHA modules")
        })
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
            self.claim_masks.is_some(),
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
            self.expose_digest,
            &self.field_exposure,
            self.uses_shared_tables(),
            self.claim_masks.is_some(),
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

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(generated_preprocessed_for_ids(
            self.log_n_rows,
            &self.preprocessed_column_ids(),
            self.local_range_min_log_size(),
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
            self.claim_mask_beta(),
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built_components().components()
    }
}

impl AirProver for Sha256Prover<'_> {
    fn max_log_size(&self) -> u32 {
        LOG_SIZE_16.max(self.log_n_rows)
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // The fixed Range_8 table needs log 16 + 1. The main SHA evaluator batches
        // four LogUp fractions. Its degree-five recurrence needs log_n_rows + 2.
        // Keep the owner bound equal to the largest component bound.
        // max_log_size() + 1 is insufficient when log_n_rows >= 16.
        (LOG_SIZE_16 + 1).max(self.log_n_rows + 2)
    }

    fn store_polynomial_coefficients(&self) -> bool {
        true
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let ids = self.preprocessed_column_ids();
        let range_min_log_size = self.local_range_min_log_size();
        let preprocessed = match self.preprocessed.take() {
            Some(_) if range_min_log_size != 0 => {
                generated_preprocessed_for_ids(self.log_n_rows, &ids, range_min_log_size)
            }
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
            None => generated_preprocessed_for_ids(self.log_n_rows, &ids, range_min_log_size),
        };
        tb.extend_evals(preprocessed);
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        // Fingerprint exactly what `write_preprocessed` will commit: the caller-provided
        // evals when set, otherwise the (cached) generated trace. Do not `take` — the
        // evals must still be available for the later `write_preprocessed` call.
        let ids = self.preprocessed_column_ids();
        let range_min_log_size = self.local_range_min_log_size();
        match &self.preprocessed {
            Some(_) if range_min_log_size != 0 => {
                let evals =
                    generated_preprocessed_for_ids(self.log_n_rows, &ids, range_min_log_size);
                fingerprint_preprocessed_columns("stwo_sha256::Sha256Prover", &ids, &evals)
            }
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
                let evals =
                    generated_preprocessed_for_ids(self.log_n_rows, &ids, range_min_log_size);
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
        let range_min_log_size = self.local_range_min_log_size();
        let preprocessed = match self.preprocessed.take() {
            Some(_) if range_min_log_size != 0 => {
                generated_preprocessed_for_ids(self.log_n_rows, &ids, range_min_log_size)
            }
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
            None => generated_preprocessed_for_ids(self.log_n_rows, &ids, range_min_log_size),
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
        let include_table_providers = !self.uses_shared_tables();
        let range_min_log_size = self.local_range_min_log_size();
        let main_columns = Layout::total_cols_with_fields(self.field_exposure.n_columns());
        let mut base = match self.base.take() {
            Some(prepared)
                if range_min_log_size == 0
                    && include_table_providers
                    && prepared.len() == main_columns + RANGE_TABLES.len() =>
            {
                prepared
            }
            Some(mut prepared) => {
                assert!(
                    prepared.len() >= main_columns,
                    "prepared SHA trace is missing main component columns"
                );
                prepared.truncate(main_columns);
                if include_table_providers {
                    for &kind in RANGE_TABLES {
                        let log_size = range_log_size(kind).max(range_min_log_size);
                        let mut mults = range_k_multiplicities(self.witness, kind);
                        mults.resize(1usize << log_size, 0);
                        prepared.push(mult_col_to_eval(&mults, log_size));
                    }
                }
                prepared
            }
            None => build_base_trace(
                self.witness,
                self.log_n_rows,
                &self.field_exposure,
                include_table_providers,
                range_min_log_size,
            ),
        };

        if let Some(masks) = &self.claim_masks {
            let mut masked =
                Vec::with_capacity(base.len() + masks.len() * CLAIM_MASK_TRACE_COLUMNS);
            masked.extend(base.drain(..main_columns));
            masked.extend(masks[0].columns().iter().cloned());
            if include_table_providers {
                for (index, multiplicity) in base.into_iter().enumerate() {
                    masked.push(multiplicity);
                    masked.extend(masks[index + 1].columns().iter().cloned());
                }
            }
            tb.extend_evals(masked);
        } else {
            tb.extend_evals(base);
        }
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let (interaction_evals, interaction_claim) = if let Some(masks) = &self.claim_masks {
            generate_interaction_trace_with_claim_masks(
                self.relations(),
                self.witness,
                self.log_n_rows,
                self.expose_digest,
                &self.field_exposure,
                !self.uses_shared_tables(),
                masks,
                self.claim_mask_beta()
                    .expect("enabled SHA claim masks have a shared challenge"),
            )
        } else if self.uses_shared_tables() {
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
    expose_digest: bool,
    digest_handle: Option<air_core::relations::SharedDigestRelation>,
    field_exposure: FieldExposure,
    field_handle: Option<air_core::relations::SharedFieldRelation>,
    shared_tables: Option<SharedShaTableRelations>,
    interaction_claim: InteractionClaim,
    relations: Option<Sha256Relations>,
    components: Option<Sha256Components>,
    claim_mask_challenge: Option<SharedClaimMaskChallenge>,
}

impl Sha256Verifier {
    pub fn new(log_n_rows: u32, interaction_claim: InteractionClaim) -> Self {
        Self {
            log_n_rows,
            expose_digest: false,
            digest_handle: None,
            field_exposure: FieldExposure::empty(),
            field_handle: None,
            shared_tables: None,
            interaction_claim,
            relations: None,
            components: None,
            claim_mask_challenge: None,
        }
    }

    /// Match a [`Sha256Prover::with_digest_provider`] proof.
    ///
    /// This method enables the digest provider and its interaction columns.
    /// It also sets the mixed `Stmt0` flag.
    /// Use it exactly when the prover uses the provider.
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

    /// Match a [`Sha256Prover::with_field_provider`] proof.
    ///
    /// Use the same field exposure as the prover.
    /// The exposure controls the trace layout and the mixed `Stmt0` shape.
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

    /// Claim-bearing component log sizes in exact component/serialization
    /// order.
    pub fn ordered_claim_mask_log_sizes(&self) -> Vec<u32> {
        let mut sizes = vec![self.log_n_rows];
        if !self.uses_shared_tables() {
            sizes.extend(
                RANGE_TABLES
                    .iter()
                    .map(|&kind| range_log_size(kind).max(CLAIM_MASK_MIN_LOG_SIZE)),
            );
        }
        sizes
    }

    /// Configure the verifier for a prover that masks all SHA-owned claims.
    pub fn with_claim_masks(mut self, challenge: SharedClaimMaskChallenge) -> Self {
        self.claim_mask_challenge = Some(challenge);
        self
    }

    fn claim_mask_beta(&self) -> Option<QM31> {
        self.claim_mask_challenge.as_ref().map(|shared| {
            shared
                .require()
                .expect("claim-mask challenge anchor must follow all masked SHA modules")
        })
    }

    fn uses_shared_tables(&self) -> bool {
        self.shared_tables.is_some()
    }

    fn local_range_min_log_size(&self) -> u32 {
        if self.claim_mask_challenge.is_some() && !self.uses_shared_tables() {
            CLAIM_MASK_MIN_LOG_SIZE
        } else {
            0
        }
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
    fn validate_structure(&self) -> Result<(), VerificationError> {
        let expected = if self.uses_shared_tables() {
            0
        } else {
            SHA_LOCAL_RANGE_CLAIM_COUNT
        };
        if self.interaction_claim.range.len() != expected {
            return Err(VerificationError::InvalidStructure(format!(
                "SHA range claim count is {}, expected {expected}",
                self.interaction_claim.range.len(),
            )));
        }
        Ok(())
    }

    fn mix_public(&self, channel: &mut Blake2sChannel) {
        Stmt0::new(
            self.log_n_rows,
            self.expose_digest,
            &self.field_exposure,
            self.uses_shared_tables(),
            self.claim_mask_challenge.is_some(),
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
            self.expose_digest,
            &self.field_exposure,
            self.uses_shared_tables(),
            self.claim_mask_challenge.is_some(),
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

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(generated_preprocessed_for_ids(
            self.log_n_rows,
            &self.preprocessed_column_ids(),
            self.local_range_min_log_size(),
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
            self.claim_mask_beta(),
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
    /// Whether the cross-component digest provider is active. Mixed into the
    /// transcript so the prover and verifier agree on the lookup count (and
    /// hence the interaction-column layout). A mismatch reshapes the
    /// interaction tree and the verifier rejects.
    expose_digest: bool,
    /// Credential field shape as `(auxiliary columns, yields)`.
    /// The column count sets the base trace width.
    /// The yield count sets the consumer interaction width.
    /// A prover and verifier mismatch changes the trees and causes rejection.
    n_field_columns: u32,
    n_field_yields: u32,
    /// Whether a sibling module supplies the fixed SHA table providers.
    /// Mix only the active case to keep the standalone transcript unchanged.
    shared_tables: bool,
    /// Whether every claim-bearing component carries four private mask columns.
    claim_masked: bool,
}
impl Stmt0 {
    fn new(
        log_n_rows: u32,
        expose_digest: bool,
        field_exposure: &FieldExposure,
        shared_tables: bool,
        claim_masked: bool,
    ) -> Self {
        Self {
            log_n_rows,
            expose_digest,
            n_field_columns: field_exposure.n_columns() as u32,
            n_field_yields: field_exposure.n_yields() as u32,
            shared_tables,
            claim_masked,
        }
    }

    fn mix_into(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(self.log_n_rows as u64);
        channel.mix_u64(u64::from(self.expose_digest));
        channel.mix_u64(u64::from(self.n_field_columns));
        channel.mix_u64(u64::from(self.n_field_yields));
        if self.shared_tables {
            channel.mix_u64(1);
        }
        if self.claim_masked {
            channel.mix_u64(0x434c_4149_4d4d_4153);
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

/// Build the base trace.
///
/// Put the `Sha256Eval` columns first. Then add one producer multiplicity
/// column for each table in `component_provers` order.
fn build_base_trace(
    witness: &Sha256Witness,
    log_n_rows: u32,
    field_exposure: &FieldExposure,
    include_table_providers: bool,
    range_min_log_size: u32,
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

    if !include_table_providers {
        return base_trace;
    }
    // Multiplicity columns — same order as `Sha256Components::component_provers`.
    for &kind in RANGE_TABLES {
        let log_size = range_log_size(kind).max(range_min_log_size);
        let mut mults = range_k_multiplicities(witness, kind);
        mults.resize(1usize << log_size, 0);
        base_trace.push(mult_col_to_eval(&mults, log_size));
    }

    base_trace
}

/// log_sizes of every base-trace column in commit order. The Sha256Eval
/// block first (`TOTAL_COLS` × `log_n_rows`), then one mult col per
/// producer component.
fn base_trace_log_sizes(
    log_n_rows: u32,
    n_field_cols: usize,
    include_table_providers: bool,
    claim_masked: bool,
) -> Vec<u32> {
    // Base columns + the dynamic multi-block field selector auxiliaries, all
    // at the trace's `log_n_rows`. Empty and single-block exposures leave this
    // at `Layout::TOTAL_COLS`.
    let mut out = vec![log_n_rows; Layout::total_cols_with_fields(n_field_cols)];
    if claim_masked {
        out.extend(std::iter::repeat_n(log_n_rows, CLAIM_MASK_TRACE_COLUMNS));
    }
    if !include_table_providers {
        return out;
    }
    // 4 range mults, each at its own `range_log_size(kind)`.
    for &kind in RANGE_TABLES {
        let log_size = if claim_masked {
            range_log_size(kind).max(CLAIM_MASK_MIN_LOG_SIZE)
        } else {
            range_log_size(kind)
        };
        out.push(log_size);
        if claim_masked {
            out.extend(std::iter::repeat_n(log_size, CLAIM_MASK_TRACE_COLUMNS));
        }
    }
    out
}

/// log_sizes of every interaction-trace column in commit order. The
/// `Sha256Eval` consumer batches `SHA_CONSUMER_LOGUP_BATCH` fractions per
/// column (`ceil(n_lookups / batch)`). The single-fraction producers keep
/// pair batching (`num_paired_cols`). We infer the count from the structural
/// firing rule (matching the `interaction::sha256_interaction` derivation).
fn interaction_trace_log_sizes(
    log_n_rows: u32,
    expose_digest: bool,
    field_exposure: &FieldExposure,
    include_table_providers: bool,
    claim_masked: bool,
) -> Vec<u32> {
    let mut out = Vec::new();

    // Each SecureField interaction column contains
    // SECURE_EXTENSION_DEGREE = 4 base-field columns at the same log_size.
    const EXT: usize = SECURE_EXTENSION_DEGREE;

    // The Sha256Eval consumer has 42 range checks per row.
    // It adds one lookup for an enabled digest provider.
    // It also adds one lookup for each exposed window byte.
    // Batch these sites in columns at `log_n_rows`.
    // Virtual W-bit field expressions do not add range lookups.
    // See `interaction::sha256_interaction`.
    let sha_cols = (sha_lookups_per_row(expose_digest, field_exposure) + usize::from(claim_masked))
        .div_ceil(crate::interaction::SHA_CONSUMER_LOGUP_BATCH);
    out.extend(std::iter::repeat_n(log_n_rows, sha_cols * EXT));
    if !include_table_providers {
        return out;
    }
    // 4 Range_k producers: 1 lookup each, at the kind's own log_size.
    for &kind in RANGE_TABLES {
        let log_size = if claim_masked {
            range_log_size(kind).max(CLAIM_MASK_MIN_LOG_SIZE)
        } else {
            range_log_size(kind)
        };
        out.extend(std::iter::repeat_n(
            log_size,
            num_paired_cols(1 + usize::from(claim_masked)) * EXT,
        ));
    }
    out
}

fn consumer_preprocessed_log_sizes(log_n_rows: u32) -> Vec<u32> {
    std::iter::repeat_n(log_n_rows, 10).collect()
}

fn generated_preprocessed_for_ids(
    log_n_rows: u32,
    selected_ids: &[PreProcessedColumnId],
    range_min_log_size: u32,
) -> Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let (evals, ids, _log_sizes) = if range_min_log_size == 0 {
        generate_preprocessed_trace(log_n_rows)
    } else {
        generate_preprocessed_trace_with_range_min(log_n_rows, range_min_log_size)
    };
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

/// Number of interaction columns produced by `n_lookups` lookups under
/// pair-batching: `ceil(n_lookups / 2)`.
#[inline]
const fn num_paired_cols(n_lookups: usize) -> usize {
    n_lookups.div_ceil(2)
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
        expose_digest: bool,
        field_exposure: &FieldExposure,
        include_table_providers: bool,
        claim_mask_beta: Option<QM31>,
    ) -> Self {
        // The shared TraceLocationAllocator (seeded by the orchestrator with
        // every module's `preprocessed_column_ids` in commit order) runs the
        // same component order on prover and verifier. Each FrameworkComponent
        // claims its slice of preprocessed columns as it is built.
        let sha256 = FrameworkComponent::new(
            allocator,
            Sha256Eval {
                log_size: log_n_rows,
                relations: relations.clone(),
                expose_digest,
                field_exposure: field_exposure.clone(),
                claim_mask_beta,
            },
            claim.sha256.claimed_sum,
        );

        let mut range = Vec::with_capacity(4);
        if include_table_providers {
            for (i, &kind) in RANGE_TABLES.iter().enumerate() {
                let log_size = if claim_mask_beta.is_some() {
                    range_log_size(kind).max(CLAIM_MASK_MIN_LOG_SIZE)
                } else {
                    range_log_size(kind)
                };
                range.push(FrameworkComponent::new(
                    allocator,
                    RangeKEval {
                        log_size,
                        kind,
                        relations: relations.clone(),
                        shared_tables: false,
                        claim_mask_beta,
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
