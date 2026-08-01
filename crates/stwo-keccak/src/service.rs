//! `KeccakService` provides the shared Keccak components for a composed proof.
//!
//! An air-core module pair ([`KeccakServiceProver`] impl `Air`+`AirProver`,
//! [`KeccakServiceVerifier`] impl `Air`) owns these items once per proof:
//!
//! 1. the job-list sponge ([`crate::sponge_v`]) for every SHAKE-128/256
//!    sponge job of every hosted instance, one row per permutation;
//! 2. the 25-row Keccak carrier and its fixed schedule table;
//! 3. the nine spread lookup tables ([`crate::tables_air`]);
//! 4. the [`KeccakRelations`] draw, published to consumer modules through a
//!    [`SharedKeccakRelations`] handle (the `SharedFieldRelation` mechanism).
//!
//! ## Fixed component commit order (positional across every method)
//!
//! ```text
//! 1. sponge_v   2. carrier   3. schedule table   4. tables ×9
//! ```
//!
//! Consumers (stwo-mldsa bridges/prefix/sinks/decomp/sib) emit HashIo tuples
//! against the shared relations; stream ids must be globally unique per
//! instance (the host assigns per-instance stream-id bases). The service mixes
//! every job shape into the transcript; the schedule preprocessed ids embed a
//! digest of the full job list.

use stwo::core::air::Component;
use stwo::core::channel::Blake2sChannel;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::verifier::VerificationError;
use stwo::prover::backend::simd::m31::PackedM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::lookups::mle::Mle;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::mle_eval::{
    build_trace as build_tieback_trace, MleEvalProverComponent, MleEvalVerifierComponent,
};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{FrameworkComponent, TraceLocationAllocator};

use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};

use crate::carrier;
use crate::constants::N_BYTES_IN_STATE;
use crate::keccak;
use crate::relations::{KeccakRelations, SharedKeccakRelations};
use crate::round_gkr::{self, RoundCoeffOracle, RoundGkrProver, RoundTieBack};
use crate::sponge::Shape;
use crate::sponge_v::{self, JobList, SpongeVRun};
use crate::tables_air::{self, TableKind, TableMultiplicities};

/// The shared commitment-tree index of the post-interaction tie-back trace.
const POST_INTERACTION_TREE: usize = 3;

/// The exact `claimed_sums` length the service contributes:
/// `[sponge_v, carrier, schedule, tables ×9]`.
pub fn service_claimed_sums_len() -> usize {
    3 + TableKind::ALL.len()
}

fn round_log_size(n_perms_total: usize) -> u32 {
    ((n_perms_total * carrier::ROWS_PER_PERMUTATION) as u32)
        .next_power_of_two()
        .ilog2()
        .max(stwo::prover::backend::simd::m31::LOG_N_LANES)
}

pub type TraceCol = CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>;

/// The carrier witness and its round-derived table multiplicities.
pub struct PermWitness {
    pub carrier_claim: carrier::Claim,
    pub carrier_trace: Vec<TraceCol>,
    pub carrier_data: Option<carrier::InteractionData>,
    pub table_mult: TableMultiplicities,
}

/// Build the carrier trace for all permutation requests.
pub fn build_perm_witness(perm_inputs: &[[PackedM31; N_BYTES_IN_STATE + 1]]) -> PermWitness {
    let boundaries = keccak::generate_boundary_witness(perm_inputs);
    let witness = carrier::generate(&boundaries);
    let table_mult =
        TableMultiplicities::from_carrier_round(&witness.interaction.round, boundaries.n_perms);

    PermWitness {
        carrier_claim: witness.claim,
        carrier_trace: witness.trace,
        carrier_data: Some(witness.interaction),
        table_mult,
    }
}

// =============================================================================
// Shared shape/claims plumbing.
// =============================================================================

#[derive(Clone, Default)]
struct ServiceClaims {
    sponge: SecureField,
    carrier: SecureField,
    schedule: SecureField,
    tables: Vec<SecureField>,
}

impl ServiceClaims {
    fn ordered(&self) -> Vec<SecureField> {
        let mut v = vec![self.sponge, self.carrier, self.schedule];
        v.extend(self.tables.iter().copied());
        v
    }
    fn from_flat(flat: &[SecureField]) -> Self {
        assert_eq!(
            flat.len(),
            service_claimed_sums_len(),
            "service claimed sums length"
        );
        Self {
            sponge: flat[0],
            carrier: flat[1],
            schedule: flat[2],
            tables: flat[3..].to_vec(),
        }
    }
}

/// The prover and verifier forms of the carrier GKR tie-back component.
/// `MleEval` component over the δ-folded coeff column.
enum TieBack {
    Prover(Box<MleEvalProverComponent<'static, RoundCoeffOracle>>),
    Verifier(Box<MleEvalVerifierComponent<RoundCoeffOracle>>),
}

struct Built {
    sponge: sponge_v::Component,
    carrier: carrier::Component,
    schedule: carrier::ScheduleTableComponent,
    tables: Vec<tables_air::Component>,
    tie_back: TieBack,
}

impl Built {
    fn ordered(&self) -> Vec<&dyn Component> {
        let mut out: Vec<&dyn Component> = vec![&self.sponge, &self.carrier, &self.schedule];
        out.extend(self.tables.iter().map(|c| c as &dyn Component));
        out.push(match &self.tie_back {
            TieBack::Prover(c) => c.as_ref() as &dyn Component,
            TieBack::Verifier(c) => c.as_ref() as &dyn Component,
        });
        out
    }
    fn ordered_prover(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        let mut out: Vec<&dyn ComponentProver<SimdBackend>> =
            vec![&self.sponge, &self.carrier, &self.schedule];
        out.extend(
            self.tables
                .iter()
                .map(|c| c as &dyn ComponentProver<SimdBackend>),
        );
        match &self.tie_back {
            TieBack::Prover(c) => out.push(c.as_ref() as &dyn ComponentProver<SimdBackend>),
            TieBack::Verifier(_) => unreachable!("prover components on a verifier-built service"),
        }
        out
    }
}

fn preprocessed_ids(jobs: &JobList) -> Vec<PreProcessedColumnId> {
    let mut ids = sponge_v::schedule_ids(jobs);
    ids.extend(carrier::schedule_table_ids());
    ids.extend(tables_air::all_preprocessed_column_ids());
    ids
}

fn preprocessed_sizes(jobs: &JobList) -> Vec<u32> {
    let mut sizes = vec![jobs.log_size(); jobs.n_schedule_cols()];
    sizes.extend(vec![
        carrier::SCHEDULE_TABLE_LOG_SIZE;
        carrier::N_SCHEDULE_TABLE_PREPROCESSED
    ]);
    sizes.extend(tables_air::all_preprocessed_log_sizes());
    sizes
}

fn gen_preprocessed(jobs: &JobList) -> Vec<air_core::PreprocessedColumnEval> {
    let mut cols = sponge_v::gen_schedule_preprocessed(jobs);
    cols.extend(carrier::generate_schedule_table_preprocessed());
    cols.extend(tables_air::generate_preprocessed_trace());
    cols
}

fn layout_for(jobs: &JobList) -> TreeLayout {
    let ls = jobs.log_size();
    let n = jobs.n_perms_total();
    let carrier_log_size = round_log_size(n);

    let mut trace = vec![ls; jobs.n_base_cols()];
    trace.extend(vec![carrier_log_size; carrier::N_COLUMNS]);
    trace.extend(vec![
        carrier::SCHEDULE_TABLE_LOG_SIZE;
        carrier::N_SCHEDULE_TABLE_TRACE
    ]);
    for kind in TableKind::ALL {
        for _ in 0..kind.n_relations() {
            trace.push(kind.log_size());
        }
    }

    let mut interaction = vec![ls; sponge_v::n_interaction_cols(jobs)];
    interaction.extend(vec![
        carrier::SCHEDULE_TABLE_LOG_SIZE;
        carrier::N_SCHEDULE_TABLE_INTERACTION
    ]);
    for kind in TableKind::ALL {
        for _ in 0..stwo::core::fields::qm31::SECURE_EXTENSION_DEGREE {
            interaction.push(kind.log_size());
        }
    }

    TreeLayout {
        preprocessed: preprocessed_sizes(jobs),
        trace,
        interaction,
    }
}

/// Return the committed service layout for diagnostics and geometry tests.
pub fn debug_layout(shapes: Vec<Shape>) -> TreeLayout {
    layout_for(&JobList::new(shapes))
}

/// Build the base components and the tie-back oracle over the carrier's trace
/// locations. The caller adds the prover or verifier tie-back component.
fn build_base_components(
    allocator: &mut TraceLocationAllocator,
    jobs: &JobList,
    relations: &KeccakRelations,
    claims: &ServiceClaims,
    tie_back: &RoundTieBack,
) -> (
    sponge_v::Component,
    carrier::Component,
    carrier::ScheduleTableComponent,
    Vec<tables_air::Component>,
    RoundCoeffOracle,
) {
    let n = jobs.n_perms_total();
    let sponge = FrameworkComponent::new(
        allocator,
        sponge_v::Eval {
            jobs: jobs.clone(),
            relations: relations.clone(),
        },
        claims.sponge,
    );
    let carrier = FrameworkComponent::new(
        allocator,
        carrier::Eval {
            claim: carrier::Claim { n_perms: n },
        },
        claims.carrier,
    );
    let schedule = FrameworkComponent::new(
        allocator,
        carrier::ScheduleTableEval {
            n_perms: n,
            relations: relations.clone(),
        },
        claims.schedule,
    );
    let tables = TableKind::ALL
        .iter()
        .enumerate()
        .map(|(idx, kind)| {
            FrameworkComponent::new(
                allocator,
                tables_air::Eval {
                    log_size: kind.log_size(),
                    kind: *kind,
                    relations: relations.clone(),
                },
                claims.tables[idx],
            )
        })
        .collect();
    let oracle = RoundCoeffOracle {
        locations: carrier.trace_locations().to_vec(),
        relations: relations.clone(),
        log_size: round_log_size(n),
        delta: tie_back.delta,
        eq_ws: tie_back.eq_ws.clone(),
        n_perms: n,
    };
    (sponge, carrier, schedule, tables, oracle)
}

fn write_selected(
    tb: &mut TreeBuilder<SimdBackend, air_core::Mc>,
    jobs: &JobList,
    selected_ids: &[PreProcessedColumnId],
) {
    let ids = preprocessed_ids(jobs);
    let cols = gen_preprocessed(jobs);
    assert_eq!(
        ids.len(),
        cols.len(),
        "service preprocessed ids/cols mismatch"
    );
    let selected: std::collections::HashSet<PreProcessedColumnId> =
        selected_ids.iter().cloned().collect();
    let mut emitted = std::collections::HashSet::new();
    let (picked_ids, picked_cols): (Vec<_>, Vec<_>) = ids
        .into_iter()
        .zip(cols)
        .filter(|(id, _)| selected.contains(id) && emitted.insert(id.clone()))
        .unzip();
    assert_eq!(
        picked_ids.as_slice(),
        selected_ids,
        "selected preprocessed ids must be this module's ids filtered first-writer-wins"
    );
    tb.extend_evals(picked_cols);
}

// =============================================================================
// Prover.
// =============================================================================

pub struct KeccakServiceProver {
    jobs: JobList,
    handle: SharedKeccakRelations,
    run: SpongeVRun,
    perm: PermWitness,
    relations: Option<KeccakRelations>,
    claims: ServiceClaims,
    built: Option<Built>,
    /// Round GKR state for each prover step:
    /// `write_interaction` creates `round_gkr`;
    /// `prove_post_interaction` creates `gkr_blob`, `tie_back`, and `coeff_mle`;
    /// `write_post_interaction` commits the tie-back trace;
    /// `build_components` gives `coeff_mle` to the MleEval component.
    round_gkr: Option<RoundGkrProver>,
    tie_back: Option<RoundTieBack>,
    gkr_blob: Vec<u8>,
    coeff_mle: Option<Mle<SimdBackend, SecureField>>,
}

impl KeccakServiceProver {
    /// Build the service from job shapes + their witness byte streams.
    /// The service ignores `shapes[i]`'s `perm_id_base` and sets the global
    /// perm-id plan cumulatively over the concatenated list. Stream ids must
    /// already be globally unique across instances (host responsibility).
    pub fn new(shapes: Vec<Shape>, messages: Vec<Vec<u8>>, handle: SharedKeccakRelations) -> Self {
        let jobs = JobList::new(shapes);
        // Duplicate stream ids across jobs would let two jobs' HashIo bytes
        // alias; fail closed at construction.
        let mut seen = std::collections::HashSet::new();
        for s in &jobs.jobs {
            assert!(
                seen.insert(s.absorb_stream_id),
                "duplicate absorb stream id {}",
                s.absorb_stream_id
            );
            assert!(
                seen.insert(s.squeeze_stream_id),
                "duplicate squeeze stream id {}",
                s.squeeze_stream_id
            );
        }
        if std::env::var_os("KECCAK_PERMS_DUMP").is_some() {
            eprintln!(
                "keccak-service n_jobs={} n_perms_total={} round_log_size={}",
                jobs.jobs.len(),
                jobs.n_perms_total(),
                round_log_size(jobs.n_perms_total())
            );
        }
        let run = sponge_v::generate_jobs(&jobs, &messages);
        let mut perm = build_perm_witness(&run.perm_inputs);
        perm.table_mult.add_sponge(&run.xor, &run.conv);
        Self {
            jobs,
            handle,
            run,
            perm,
            relations: None,
            claims: ServiceClaims::default(),
            built: None,
            round_gkr: None,
            tie_back: None,
            gkr_blob: Vec::new(),
            coeff_mle: None,
        }
    }

    /// The per-job full squeeze outputs (`shape.rate() · n_squeeze` each).
    pub fn job_outputs(&self) -> &[Vec<u8>] {
        &self.run.outputs
    }
    /// The stamped job list (cumulative perm-id bases).
    pub fn jobs(&self) -> &JobList {
        &self.jobs
    }
    /// The ordered claimed sums (`[sponge_v, carrier, schedule, tables ×9]`).
    pub fn claimed_sums(&self) -> Vec<SecureField> {
        self.claims.ordered()
    }

    /// Test-only tamper hook: mutate the sponge run's row data before proving.
    /// The base trace AND the sponge interaction trace are generated from this
    /// data while the carrier and table witnesses stay unchanged. Negative
    /// tests use this hook to build a lying sponge.
    #[doc(hidden)]
    pub fn run_mut(&mut self) -> &mut SpongeVRun {
        &mut self.run
    }

    /// Test-only tamper hook for the carrier trace or its separate GKR source.
    /// Negative tests use it to check the MLE tie-back and endpoint links.
    #[doc(hidden)]
    pub fn perm_mut(&mut self) -> &mut PermWitness {
        &mut self.perm
    }

    fn relations(&self) -> &KeccakRelations {
        self.relations.as_ref().expect("relations drawn")
    }
}

impl Air for KeccakServiceProver {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        self.jobs.mix_into(channel);
    }
    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let relations = KeccakRelations::draw(channel);
        let data = self
            .perm
            .carrier_data
            .take()
            .expect("carrier interaction data is available once");
        self.round_gkr = Some(RoundGkrProver::new(&relations, &data));
        self.handle.set(relations.clone());
        self.relations = Some(relations);
    }
    fn layout(&self) -> TreeLayout {
        layout_for(&self.jobs)
    }
    fn claimed_sums(&self) -> Vec<SecureField> {
        self.claims.ordered()
    }
    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_ids(&self.jobs)
    }
    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, VerificationError> {
        Ok(gen_preprocessed(&self.jobs))
    }
    fn post_interaction_log_sizes(&self) -> Vec<u32> {
        vec![round_log_size(self.jobs.n_perms_total()); round_gkr::N_TIEBACK_COLUMNS]
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let rel = self.relations().clone();
        let tie_back = self.tie_back.as_ref().expect("prove_post_interaction ran");
        let (sponge, carrier, schedule, tables, oracle) =
            build_base_components(allocator, &self.jobs, &rel, &self.claims, tie_back);
        let mle = self.coeff_mle.take().expect("coeff column built");
        // Twiddles must cover the quotient eval domain `log_size +
        // composition_log_split` (≤ +2 here from the batch-4 logup components);
        // +4 leaves headroom and the tree is process-cached.
        let twiddles = air_core::twiddles(round_log_size(self.jobs.n_perms_total()) + 4);
        let tie_back_component = MleEvalProverComponent::generate(
            allocator,
            oracle,
            &tie_back.r_row,
            mle,
            tie_back.mle_claim,
            twiddles,
            POST_INTERACTION_TREE,
        );
        self.built = Some(Built {
            sponge,
            carrier,
            schedule,
            tables,
            tie_back: TieBack::Prover(Box::new(tie_back_component)),
        });
    }
    fn components(&self) -> Vec<&dyn Component> {
        self.built.as_ref().expect("built").ordered()
    }
}

impl AirProver for KeccakServiceProver {
    fn max_log_size(&self) -> u32 {
        let n = self.jobs.n_perms_total();
        self.jobs
            .log_size()
            .max(round_log_size(n))
            .max(TableKind::Dense.log_size())
    }
    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(gen_preprocessed(&self.jobs));
    }
    fn write_selected_preprocessed(
        &mut self,
        tb: &mut TreeBuilder<SimdBackend, air_core::Mc>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        write_selected(tb, &self.jobs, selected_ids);
    }
    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "stwo_keccak::KeccakService",
            &preprocessed_ids(&self.jobs),
            &gen_preprocessed(&self.jobs),
        )
    }
    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let mut evals = sponge_v::generate_base_trace(&self.run);
        evals.extend(std::mem::take(&mut self.perm.carrier_trace));
        evals.extend(carrier::generate_schedule_multiplicity(
            self.jobs.n_perms_total(),
        ));
        evals.extend(tables_air::generate_trace(&self.perm.table_mult));
        tb.extend_evals(evals);
    }
    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let rel = self.relations().clone();
        let mut evals = Vec::new();
        let (sponge_ic, sponge_tr) = sponge_v::generate_interaction_trace(&rel, &self.run);
        evals.extend(sponge_tr);
        let (schedule_ic, schedule_trace) =
            carrier::generate_schedule_interaction(&rel, self.jobs.n_perms_total());
        evals.extend(schedule_trace);
        let carrier_claimed_sum = self
            .round_gkr
            .as_ref()
            .expect("carrier GKR was built after relation draw")
            .claimed_sum();
        let (tables_ic, tables_tr) =
            tables_air::generate_interaction_trace(&rel, &self.perm.table_mult);
        evals.extend(tables_tr);
        tb.extend_evals(evals);
        self.claims = ServiceClaims {
            sponge: sponge_ic.claimed_sum,
            carrier: carrier_claimed_sum,
            schedule: schedule_ic.claimed_sum,
            tables: tables_ic.claimed_sums,
        };
    }
    fn prove_post_interaction(&mut self, channel: &mut air_core::Ch) {
        let (blob, tie_back, coeff_mle) = self
            .round_gkr
            .take()
            .expect("write_interaction ran")
            .prove(channel);
        self.gkr_blob = blob;
        self.tie_back = Some(tie_back);
        self.coeff_mle = Some(coeff_mle);
    }
    fn take_post_interaction_payload(&mut self) -> Vec<u8> {
        std::mem::take(&mut self.gkr_blob)
    }
    fn write_post_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let tie_back = self.tie_back.as_ref().expect("prove_post_interaction ran");
        let mle = self.coeff_mle.as_ref().expect("coeff column built");
        tb.extend_evals(build_tieback_trace(
            mle,
            &tie_back.r_row,
            tie_back.mle_claim,
        ));
    }
    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        self.built.as_ref().expect("built").ordered_prover()
    }
}

// =============================================================================
// Verifier.
// =============================================================================

pub struct KeccakServiceVerifier {
    jobs: JobList,
    handle: SharedKeccakRelations,
    claims: ServiceClaims,
    relations: Option<KeccakRelations>,
    built: Option<Built>,
    /// The prover's opaque GKR payload (round LogUp offload), handed over by
    /// the orchestrator before `verify_post_interaction`. Empty ⇒ reject.
    gkr_blob: Vec<u8>,
    tie_back: Option<RoundTieBack>,
}

impl KeccakServiceVerifier {
    /// Reconstruct the service from public job shapes and claimed sums.
    pub fn new(
        shapes: Vec<Shape>,
        claimed_sums: Vec<SecureField>,
        handle: SharedKeccakRelations,
    ) -> Self {
        Self {
            jobs: JobList::new(shapes),
            handle,
            claims: ServiceClaims::from_flat(&claimed_sums),
            relations: None,
            built: None,
            gkr_blob: Vec::new(),
            tie_back: None,
        }
    }

    fn relations(&self) -> &KeccakRelations {
        self.relations.as_ref().expect("relations drawn")
    }
}

impl Air for KeccakServiceVerifier {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        self.jobs.mix_into(channel);
    }
    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let relations = KeccakRelations::draw(channel);
        self.handle.set(relations.clone());
        self.relations = Some(relations);
    }
    fn layout(&self) -> TreeLayout {
        layout_for(&self.jobs)
    }
    fn claimed_sums(&self) -> Vec<SecureField> {
        self.claims.ordered()
    }
    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_ids(&self.jobs)
    }
    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, VerificationError> {
        Ok(gen_preprocessed(&self.jobs))
    }
    fn post_interaction_log_sizes(&self) -> Vec<u32> {
        vec![round_log_size(self.jobs.n_perms_total()); round_gkr::N_TIEBACK_COLUMNS]
    }
    fn load_post_interaction_payload(&mut self, payload: &[u8]) {
        self.gkr_blob = payload.to_vec();
    }
    fn verify_post_interaction(
        &mut self,
        channel: &mut air_core::Ch,
    ) -> Result<(), VerificationError> {
        // Fail-closed: a missing payload is an empty blob, which fails decode.
        let tie_back = round_gkr::verify_round_gkr(
            &self.gkr_blob,
            self.claims.carrier,
            round_log_size(self.jobs.n_perms_total()),
            channel,
        )?;
        self.tie_back = Some(tie_back);
        Ok(())
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let rel = self.relations().clone();
        let tie_back = self.tie_back.as_ref().expect("verify_post_interaction ran");
        let (sponge, carrier, schedule, tables, oracle) =
            build_base_components(allocator, &self.jobs, &rel, &self.claims, tie_back);
        let tie_back_component = MleEvalVerifierComponent::new(
            allocator,
            oracle,
            &tie_back.r_row,
            tie_back.mle_claim,
            POST_INTERACTION_TREE,
        );
        self.built = Some(Built {
            sponge,
            carrier,
            schedule,
            tables,
            tie_back: TieBack::Verifier(Box::new(tie_back_component)),
        });
    }
    fn components(&self) -> Vec<&dyn Component> {
        self.built.as_ref().expect("built").ordered()
    }
}
