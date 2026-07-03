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

use air_core::{Air, AirProver, TreeLayout};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::{QM31, SECURE_EXTENSION_DEGREE};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{FrameworkComponent, TraceLocationAllocator};

use crate::components::{
    all_preprocessed_column_ids, range_log_size, MajChEval, RangeKEval, RoundSplitPackEval,
    Sha256Relations, SigmaDecodeEval, SigmaSplitPackEval, Xor8Eval, DECODE_TABLES, RANGE_TABLES,
    ROUND_SPLIT_TABLES, SIGMA_SPLIT_TABLES,
};
use crate::constraints::Sha256Eval;
use crate::field_exposure::FieldExposure;
use crate::interaction::{generate_interaction_trace, sha_lookups_per_row, InteractionClaim};
use crate::multiplicities::{
    decode_multiplicities, maj_ch_multiplicities, range_k_multiplicities,
    round_split_pack_multiplicities, sigma_split_pack_multiplicities, xor_8_multiplicities,
};
use crate::preprocessed::{
    generate_preprocessed_trace, maj_ch_log_size, preprocessed_log_sizes, LOG_SIZE_16,
};
use crate::trace::Layout;
use crate::types::Sha256Witness;

type Sha256ColumnEval = CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>;

/// SHA trace columns materialized before the module is wired to shared relation
/// handles.
pub struct PreparedSha256Traces {
    preprocessed: Vec<Sha256ColumnEval>,
    base: Vec<Sha256ColumnEval>,
}

pub struct Sha256InteractionJob<'a> {
    relations: &'a Sha256Relations,
    witness: &'a Sha256Witness,
    log_n_rows: u32,
    group_width: u32,
    expose_digest: bool,
    field_exposure: &'a FieldExposure,
}

pub struct PreparedSha256Interaction {
    columns: Vec<Sha256ColumnEval>,
    claim: InteractionClaim,
}

impl Sha256InteractionJob<'_> {
    pub fn materialize(self) -> PreparedSha256Interaction {
        let (columns, claim) = generate_interaction_trace(
            self.relations,
            self.witness,
            self.log_n_rows,
            self.group_width,
            self.expose_digest,
            self.field_exposure,
        );
        PreparedSha256Interaction { columns, claim }
    }
}

/// Column log-sizes per tree, shared by prover and verifier — they depend
/// only on the public size surface (`log_n_rows`, `group_width`), never on the
/// witness.
fn layout(
    log_n_rows: u32,
    group_width: u32,
    expose_digest: bool,
    field_exposure: &FieldExposure,
) -> TreeLayout {
    TreeLayout {
        preprocessed: preprocessed_log_sizes(group_width, log_n_rows),
        trace: base_trace_log_sizes(log_n_rows, group_width, field_exposure.n_columns()),
        interaction: interaction_trace_log_sizes(
            log_n_rows,
            group_width,
            expose_digest,
            field_exposure,
        ),
    }
}

/// Flatten the per-component claims into one slice in component (commit) order
/// — the order [`Sha256Components`] adds them and the order the orchestrator
/// mixes and balances. Equals [`InteractionClaim::total`] when summed.
pub fn flatten_claimed_sums(claim: &InteractionClaim) -> Vec<QM31> {
    let mut out = Vec::new();
    out.push(claim.sha256.claimed_sum);
    out.extend(claim.decode.iter().map(|c| c.claimed_sum));
    out.push(claim.maj_ch.claimed_sum);
    out.push(claim.xor_8.claimed_sum);
    out.extend(claim.round_split_pack.iter().map(|c| c.claimed_sum));
    out.extend(claim.sigma_split_pack.iter().map(|c| c.claimed_sum));
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
    relations: Option<Sha256Relations>,
    interaction_claim: Option<InteractionClaim>,
    components: Option<Sha256Components>,
    preprocessed: Option<Vec<Sha256ColumnEval>>,
    base: Option<Vec<Sha256ColumnEval>>,
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
            relations: None,
            interaction_claim: None,
            components: None,
            preprocessed: None,
            base: None,
        }
    }

    pub fn prepare_traces(
        witness: &Sha256Witness,
        log_n_rows: u32,
        group_width: u32,
        field_exposure: &FieldExposure,
    ) -> PreparedSha256Traces {
        let (preprocessed, _ids, _log_sizes) = generate_preprocessed_trace(group_width, log_n_rows);
        let base = build_base_trace(witness, log_n_rows, group_width, field_exposure);
        PreparedSha256Traces { preprocessed, base }
    }

    pub fn with_prepared_traces(mut self, prepared: PreparedSha256Traces) -> Self {
        self.preprocessed = Some(prepared.preprocessed);
        self.base = Some(prepared.base);
        self
    }

    /// Enable the cross-component digest provider: the module yields
    /// the final-block digest on the `Sha256Digest` channel, so a composed
    /// consumer (the P256 `z` binding) can require it. This leaves the SHA
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
    /// `Sha256Digest` relation through `handle` so a sibling module (the P256
    /// digest-bind bridge) consumes it over the identical `LookupElements`.
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

    pub fn interaction_job(&self) -> Sha256InteractionJob<'_> {
        Sha256InteractionJob {
            relations: self.relations(),
            witness: self.witness,
            log_n_rows: self.log_n_rows,
            group_width: self.group_width,
            expose_digest: self.expose_digest,
            field_exposure: &self.field_exposure,
        }
    }

    pub fn write_prepared_interaction(
        &mut self,
        tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>,
        prepared: PreparedSha256Interaction,
    ) {
        tb.extend_evals(prepared.columns);
        self.interaction_claim = Some(prepared.claim);
    }
}

impl Air for Sha256Prover<'_> {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        Stmt0::new(
            self.log_n_rows,
            self.group_width,
            self.expose_digest,
            &self.field_exposure,
        )
        .mix_into(channel);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let relations = Sha256Relations::draw(channel);
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
        )
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        flatten_claimed_sums(self.interaction_claim())
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        all_preprocessed_column_ids()
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
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built_components().components()
    }
}

impl AirProver for Sha256Prover<'_> {
    fn max_log_size(&self) -> u32 {
        // The packed Maj/Ch table (`3W` rows) is the largest committed domain;
        // it dominates `LOG_SIZE_16` and the trace's own `log_n_rows`.
        maj_ch_log_size(self.group_width)
            .max(LOG_SIZE_16)
            .max(self.log_n_rows)
    }

    fn store_polynomial_coefficients(&self) -> bool {
        true
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let preprocessed = self.preprocessed.take().unwrap_or_else(|| {
            let (preprocessed_evals, _ids, _log_sizes) =
                generate_preprocessed_trace(self.group_width, self.log_n_rows);
            preprocessed_evals
        });
        tb.extend_evals(preprocessed);
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let base = self.base.take().unwrap_or_else(|| {
            build_base_trace(
                self.witness,
                self.log_n_rows,
                self.group_width,
                &self.field_exposure,
            )
        });
        tb.extend_evals(base);
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let prepared = self.interaction_job().materialize();
        self.write_prepared_interaction(tb, prepared);
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
        )
        .mix_into(channel);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let relations = Sha256Relations::draw(channel);
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
        )
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        flatten_claimed_sums(&self.interaction_claim)
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        all_preprocessed_column_ids()
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
}
impl Stmt0 {
    fn new(
        log_n_rows: u32,
        group_width: u32,
        expose_digest: bool,
        field_exposure: &FieldExposure,
    ) -> Self {
        Self {
            log_n_rows,
            group_width,
            expose_digest,
            n_field_columns: field_exposure.n_columns() as u32,
            n_field_yields: field_exposure.n_yields() as u32,
        }
    }

    fn mix_into(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(self.log_n_rows as u64);
        channel.mix_u64(self.group_width as u64);
        channel.mix_u64(u64::from(self.expose_digest));
        channel.mix_u64(u64::from(self.n_field_columns));
        channel.mix_u64(u64::from(self.n_field_yields));
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

    // Multiplicity columns — same order as `Sha256Components::component_provers`.
    for &(f, h) in DECODE_TABLES {
        let mults = decode_multiplicities(witness, f, h);
        base_trace.push(mult_col_to_eval(&mults, LOG_SIZE_16));
    }
    {
        let mc = maj_ch_multiplicities(witness, group_width);
        let log_size = maj_ch_log_size(group_width);
        base_trace.push(mult_col_to_eval(&mc.maj, log_size));
        base_trace.push(mult_col_to_eval(&mc.ch, log_size));
    }
    {
        let mults = xor_8_multiplicities(witness);
        base_trace.push(mult_col_to_eval(&mults, LOG_SIZE_16));
    }
    for &(p, h) in ROUND_SPLIT_TABLES {
        let mults = round_split_pack_multiplicities(witness, p, h);
        base_trace.push(mult_col_to_eval(&mults, LOG_SIZE_16));
    }
    for &(p, h) in SIGMA_SPLIT_TABLES {
        let mults = sigma_split_pack_multiplicities(witness, p, h);
        base_trace.push(mult_col_to_eval(&mults, LOG_SIZE_16));
    }
    for &kind in RANGE_TABLES {
        let mults = range_k_multiplicities(witness, kind, field_exposure);
        base_trace.push(mult_col_to_eval(&mults, range_log_size(kind)));
    }

    base_trace
}

/// log_sizes of every base-trace column in commit order. The Sha256Eval
/// block first (`TOTAL_COLS` × `log_n_rows`), then one mult col per
/// producer component.
fn base_trace_log_sizes(log_n_rows: u32, group_width: u32, n_field_cols: usize) -> Vec<u32> {
    // Base columns + the dynamic credential-field byte tail, all at the
    // trace's `log_n_rows`. Empty exposure leaves this at `Layout::TOTAL_COLS`.
    let mut out = vec![log_n_rows; Layout::total_cols_with_fields(n_field_cols)];
    // 8 decode mults, each at log_size 16.
    out.extend(std::iter::repeat_n(LOG_SIZE_16, DECODE_TABLES.len()));
    // 2 Maj/Ch mults, each at log_size 3W.
    out.extend(std::iter::repeat_n(maj_ch_log_size(group_width), 2));
    // xor_8 mult.
    out.push(LOG_SIZE_16);
    // 4 round + 4 σ split-pack mults.
    out.extend(std::iter::repeat_n(LOG_SIZE_16, ROUND_SPLIT_TABLES.len()));
    out.extend(std::iter::repeat_n(LOG_SIZE_16, SIGMA_SPLIT_TABLES.len()));
    // 4 range mults, each at its own `range_log_size(kind)`.
    for &kind in RANGE_TABLES {
        out.push(range_log_size(kind));
    }
    out
}

/// log_sizes of every interaction-trace column in commit order. Each
/// component's column count is `(n_lookups + 1) / 2`. We infer the count
/// from the structural firing rule (matching the
/// `interaction::sha256_interaction` derivation).
fn interaction_trace_log_sizes(
    log_n_rows: u32,
    group_width: u32,
    expose_digest: bool,
    field_exposure: &FieldExposure,
) -> Vec<u32> {
    let mut out = Vec::new();

    // Each SecureField interaction column expands to SECURE_EXTENSION_DEGREE = 4
    // base-field columns at the same log_size.
    const EXT: usize = SECURE_EXTENSION_DEGREE;

    // Sha256Eval consumer: `sha_lookups_per_row(expose_digest, field_exposure)`
    // lookup sites per row (W=6: 106, plus the digest yield when that provider
    // is on, plus the field provider's two `Range16` byte range-checks per
    // exposed byte column and one yield per exposed window byte) → `ceil(n/2)`
    // paired columns. Sized at log_n_rows. See `interaction::sha256_interaction`
    // for the per-row site breakdown.
    let sha_cols = num_paired_cols(sha_lookups_per_row(expose_digest, field_exposure));
    out.extend(std::iter::repeat_n(log_n_rows, sha_cols * EXT));
    // 8 decode producers: 1 lookup each → 1 column each at log_size 16.
    for _ in DECODE_TABLES {
        out.extend(std::iter::repeat_n(LOG_SIZE_16, num_paired_cols(1) * EXT));
    }
    // Maj/Ch: 2 lookups → 1 paired column at log_size 3W.
    out.extend(std::iter::repeat_n(
        maj_ch_log_size(group_width),
        num_paired_cols(2) * EXT,
    ));
    // xor_8: 1 lookup → 1 column at log_size 16. Under the GKR spike this
    // producer-side LogUp column is replaced by the side GKR argument.
    #[cfg(not(feature = "gkr-spike"))]
    out.extend(std::iter::repeat_n(LOG_SIZE_16, num_paired_cols(1) * EXT));
    // 4 round split-pack: 1 lookup each.
    for _ in ROUND_SPLIT_TABLES {
        out.extend(std::iter::repeat_n(LOG_SIZE_16, num_paired_cols(1) * EXT));
    }
    // 4 σ split-pack: 1 lookup each.
    for _ in SIGMA_SPLIT_TABLES {
        out.extend(std::iter::repeat_n(LOG_SIZE_16, num_paired_cols(1) * EXT));
    }
    // 4 Range_k producers: 1 lookup each, at the kind's own log_size.
    for &kind in RANGE_TABLES {
        out.extend(std::iter::repeat_n(
            range_log_size(kind),
            num_paired_cols(1) * EXT,
        ));
    }
    out
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
    decode: Vec<FrameworkComponent<SigmaDecodeEval>>, // 8
    maj_ch: FrameworkComponent<MajChEval>,
    xor_8: FrameworkComponent<Xor8Eval>,
    round_split_pack: Vec<FrameworkComponent<RoundSplitPackEval>>, // 4
    sigma_split_pack: Vec<FrameworkComponent<SigmaSplitPackEval>>, // 4
    range: Vec<FrameworkComponent<RangeKEval>>,                    // 4
}

impl Sha256Components {
    fn new(
        allocator: &mut TraceLocationAllocator,
        claim: &InteractionClaim,
        relations: &Sha256Relations,
        log_n_rows: u32,
        group_width: u32,
        expose_digest: bool,
        field_exposure: &FieldExposure,
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
            },
            claim.sha256.claimed_sum,
        );

        let mut decode = Vec::with_capacity(8);
        for (i, &(f, h)) in DECODE_TABLES.iter().enumerate() {
            decode.push(FrameworkComponent::new(
                allocator,
                SigmaDecodeEval {
                    log_size: LOG_SIZE_16,
                    f,
                    half: h,
                    relations: relations.clone(),
                },
                claim.decode[i].claimed_sum,
            ));
        }
        let maj_ch = FrameworkComponent::new(
            allocator,
            MajChEval {
                log_size: maj_ch_log_size(group_width),
                relations: relations.clone(),
            },
            claim.maj_ch.claimed_sum,
        );
        let xor_8 = FrameworkComponent::new(
            allocator,
            Xor8Eval {
                log_size: LOG_SIZE_16,
                relations: relations.clone(),
            },
            claim.xor_8.claimed_sum,
        );
        let mut round_split_pack = Vec::with_capacity(4);
        for (i, &(p, h)) in ROUND_SPLIT_TABLES.iter().enumerate() {
            round_split_pack.push(FrameworkComponent::new(
                allocator,
                RoundSplitPackEval {
                    log_size: LOG_SIZE_16,
                    partition: p,
                    half: h,
                    relations: relations.clone(),
                },
                claim.round_split_pack[i].claimed_sum,
            ));
        }
        let mut sigma_split_pack = Vec::with_capacity(4);
        for (i, &(p, h)) in SIGMA_SPLIT_TABLES.iter().enumerate() {
            sigma_split_pack.push(FrameworkComponent::new(
                allocator,
                SigmaSplitPackEval {
                    log_size: LOG_SIZE_16,
                    partition: p,
                    half: h,
                    relations: relations.clone(),
                },
                claim.sigma_split_pack[i].claimed_sum,
            ));
        }
        let mut range = Vec::with_capacity(4);
        for (i, &kind) in RANGE_TABLES.iter().enumerate() {
            range.push(FrameworkComponent::new(
                allocator,
                RangeKEval {
                    log_size: range_log_size(kind),
                    kind,
                    relations: relations.clone(),
                },
                claim.range[i].claimed_sum,
            ));
        }

        Self {
            sha256,
            decode,
            maj_ch,
            xor_8,
            round_split_pack,
            sigma_split_pack,
            range,
        }
    }

    /// Borrow every component as `dyn Component`, in commit order — the
    /// verifier-side surface the orchestrator consumes.
    fn components(&self) -> Vec<&dyn Component> {
        let mut out: Vec<&dyn Component> = Vec::new();
        out.push(&self.sha256);
        out.extend(self.decode.iter().map(|c| c as &dyn Component));
        out.push(&self.maj_ch);
        out.push(&self.xor_8);
        out.extend(self.round_split_pack.iter().map(|c| c as &dyn Component));
        out.extend(self.sigma_split_pack.iter().map(|c| c as &dyn Component));
        out.extend(self.range.iter().map(|c| c as &dyn Component));
        out
    }

    /// Borrow every component as `dyn ComponentProver`, in commit order — the
    /// prover-side surface the orchestrator consumes.
    fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        let mut out: Vec<&dyn ComponentProver<SimdBackend>> = Vec::new();
        out.push(&self.sha256);
        out.extend(
            self.decode
                .iter()
                .map(|c| c as &dyn ComponentProver<SimdBackend>),
        );
        out.push(&self.maj_ch);
        out.push(&self.xor_8);
        out.extend(
            self.round_split_pack
                .iter()
                .map(|c| c as &dyn ComponentProver<SimdBackend>),
        );
        out.extend(
            self.sigma_split_pack
                .iter()
                .map(|c| c as &dyn ComponentProver<SimdBackend>),
        );
        out.extend(
            self.range
                .iter()
                .map(|c| c as &dyn ComponentProver<SimdBackend>),
        );
        out
    }
}
