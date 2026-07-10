//! `KeccakService` — the ONE keccak side of a composed proof (S1).
//!
//! An air-core module pair ([`KeccakServiceProver`] impl `Air`+`AirProver`,
//! [`KeccakServiceVerifier`] impl `Air`) that owns, exactly once per proof:
//!
//! 1. the rotated job-list sponge ([`crate::sponge_v`]) — every SHAKE-256
//!    sponge job of every hosted instance, one row per permutation;
//! 2. the `keccak` permutation component and the `keccak_round` component;
//! 3. the nine spread lookup tables ([`crate::tables_air`]);
//! 4. the [`KeccakRelations`] draw, published to consumer modules through a
//!    [`SharedKeccakRelations`] handle (the `SharedFieldRelation` mechanism).
//!
//! ## Fixed component commit order (positional across every method)
//!
//! ```text
//! 1. sponge_v   2. keccak   3. keccak_round   4. tables ×9
//! ```
//!
//! Consumers (stwo-mldsa bridges/prefix/sinks/decomp/sib) emit HashIo tuples
//! against the shared relations; stream ids must be globally unique per
//! instance (the host assigns per-instance stream-id bases). The service mixes
//! every job shape into the transcript; the schedule preprocessed ids embed a
//! digest of the full job list (I-5).

use stwo::core::air::Component;
use stwo::core::channel::Blake2sChannel;
use stwo::core::fields::qm31::SecureField;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{FrameworkComponent, TraceLocationAllocator};

use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};

use crate::keccak;
use crate::keccak_round;
use crate::relations::{KeccakRelations, SharedKeccakRelations};
use crate::sponge::Shape;
use crate::sponge_v::{self, JobList, SpongeVRun};
use crate::stark::{build_perm_witness, PermWitness};
use crate::tables_air::{self, TableKind};

/// The exact `claimed_sums` length the service contributes:
/// `[sponge_v, keccak, round, tables ×9]`.
pub fn service_claimed_sums_len() -> usize {
    3 + TableKind::ALL.len()
}

fn keccak_log_size(n_perms_total: usize) -> u32 {
    (n_perms_total as u32)
        .next_power_of_two()
        .ilog2()
        .max(stwo::prover::backend::simd::m31::LOG_N_LANES)
}
fn round_log_size(n_perms_total: usize) -> u32 {
    ((n_perms_total * crate::constants::N_ROUNDS) as u32)
        .next_power_of_two()
        .ilog2()
        .max(stwo::prover::backend::simd::m31::LOG_N_LANES)
}

// =============================================================================
// Shared shape/claims plumbing.
// =============================================================================

#[derive(Clone, Default)]
struct ServiceClaims {
    sponge: SecureField,
    keccak: SecureField,
    round: SecureField,
    tables: Vec<SecureField>,
}

impl ServiceClaims {
    fn ordered(&self) -> Vec<SecureField> {
        let mut v = vec![self.sponge, self.keccak, self.round];
        v.extend(self.tables.iter().copied());
        v
    }
    fn from_flat(flat: &[SecureField]) -> Self {
        assert_eq!(flat.len(), service_claimed_sums_len(), "service claimed sums length");
        Self {
            sponge: flat[0],
            keccak: flat[1],
            round: flat[2],
            tables: flat[3..].to_vec(),
        }
    }
}

struct Built {
    sponge: sponge_v::Component,
    keccak: keccak::Component,
    round: keccak_round::Component,
    tables: Vec<tables_air::Component>,
}

impl Built {
    fn ordered(&self) -> Vec<&dyn Component> {
        let mut out: Vec<&dyn Component> = vec![&self.sponge, &self.keccak, &self.round];
        out.extend(self.tables.iter().map(|c| c as &dyn Component));
        out
    }
    fn ordered_prover(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        let mut out: Vec<&dyn ComponentProver<SimdBackend>> =
            vec![&self.sponge, &self.keccak, &self.round];
        out.extend(self.tables.iter().map(|c| c as &dyn ComponentProver<SimdBackend>));
        out
    }
}

fn preprocessed_ids(jobs: &JobList) -> Vec<PreProcessedColumnId> {
    let mut ids = sponge_v::schedule_ids(jobs);
    ids.extend(tables_air::all_preprocessed_column_ids());
    ids
}

fn preprocessed_sizes(jobs: &JobList) -> Vec<u32> {
    let mut sizes = vec![jobs.log_size(); sponge_v::N_SCHEDULE_COLS];
    sizes.extend(tables_air::all_preprocessed_log_sizes());
    sizes
}

fn gen_preprocessed(jobs: &JobList) -> Vec<air_core::PreprocessedColumnEval> {
    let mut cols = sponge_v::gen_schedule_preprocessed(jobs);
    cols.extend(tables_air::generate_preprocessed_trace());
    cols
}

fn layout_for(jobs: &JobList) -> TreeLayout {
    let ls = jobs.log_size();
    let n = jobs.n_perms_total();
    let keccak_claim = keccak::Claim { log_size: keccak_log_size(n) };
    let round_claim = keccak_round::Claim { log_size: round_log_size(n) };

    let mut trace = vec![ls; sponge_v::N_BASE_COLS];
    trace.extend(keccak_claim.log_sizes()[1].clone());
    trace.extend(round_claim.log_sizes()[1].clone());
    for kind in TableKind::ALL {
        for _ in 0..kind.n_relations() {
            trace.push(kind.log_size());
        }
    }

    let mut interaction = vec![ls; sponge_v::N_INTERACTION_COLS];
    interaction.extend(keccak_claim.log_sizes()[2].clone());
    interaction.extend(round_claim.log_sizes()[2].clone());
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

fn build_components(
    allocator: &mut TraceLocationAllocator,
    jobs: &JobList,
    relations: &KeccakRelations,
    claims: &ServiceClaims,
) -> Built {
    let n = jobs.n_perms_total();
    let sponge = FrameworkComponent::new(
        allocator,
        sponge_v::Eval { jobs: jobs.clone(), relations: relations.clone() },
        claims.sponge,
    );
    let keccak = FrameworkComponent::new(
        allocator,
        keccak::Eval {
            claim: keccak::Claim { log_size: keccak_log_size(n) },
            relations: relations.clone(),
        },
        claims.keccak,
    );
    let round = FrameworkComponent::new(
        allocator,
        keccak_round::Eval {
            claim: keccak_round::Claim { log_size: round_log_size(n) },
            relations: relations.clone(),
        },
        claims.round,
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
    Built { sponge, keccak, round, tables }
}

fn write_selected(
    tb: &mut TreeBuilder<SimdBackend, air_core::Mc>,
    jobs: &JobList,
    selected_ids: &[PreProcessedColumnId],
) {
    let ids = preprocessed_ids(jobs);
    let cols = gen_preprocessed(jobs);
    assert_eq!(ids.len(), cols.len(), "service preprocessed ids/cols mismatch");
    let selected: std::collections::HashSet<&PreProcessedColumnId> = selected_ids.iter().collect();
    let (picked_ids, picked_cols): (Vec<_>, Vec<_>) = ids
        .into_iter()
        .zip(cols)
        .filter(|(id, _)| selected.contains(id))
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
}

impl KeccakServiceProver {
    /// Build the service from job shapes + their witness byte streams.
    /// `shapes[i]`'s `perm_id_base` is ignored — the service stamps the global
    /// perm-id plan cumulatively over the concatenated list. Stream ids must
    /// already be globally unique across instances (host responsibility).
    pub fn new(
        shapes: Vec<Shape>,
        messages: Vec<Vec<u8>>,
        handle: SharedKeccakRelations,
    ) -> Self {
        let jobs = JobList::new(shapes);
        // Duplicate stream ids across jobs would let two jobs' HashIo bytes
        // alias; fail closed at construction.
        let mut seen = std::collections::HashSet::new();
        for s in &jobs.jobs {
            assert!(seen.insert(s.absorb_stream_id), "duplicate absorb stream id {}", s.absorb_stream_id);
            assert!(seen.insert(s.squeeze_stream_id), "duplicate squeeze stream id {}", s.squeeze_stream_id);
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
        }
    }

    /// The per-job full squeeze outputs (`136 · n_squeeze` bytes each).
    pub fn job_outputs(&self) -> &[Vec<u8>] {
        &self.run.outputs
    }
    /// The stamped job list (cumulative perm-id bases).
    pub fn jobs(&self) -> &JobList {
        &self.jobs
    }
    /// The ordered claimed sums (`[sponge_v, keccak, round, tables ×9]`).
    pub fn claimed_sums(&self) -> Vec<SecureField> {
        self.claims.ordered()
    }

    /// Test-only tamper hook: mutate the sponge run's row data before proving.
    /// The base trace AND the sponge interaction trace are generated from this
    /// data, while the keccak/round/table witnesses stay honest — exactly the
    /// adversarial "lying sponge" configuration the negative tests exercise.
    #[doc(hidden)]
    pub fn run_mut(&mut self) -> &mut SpongeVRun {
        &mut self.run
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
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let rel = self.relations().clone();
        self.built = Some(build_components(allocator, &self.jobs, &rel, &self.claims));
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
            .max(keccak_log_size(n))
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
        evals.extend(std::mem::take(&mut self.perm.keccak_trace));
        evals.extend(std::mem::take(&mut self.perm.round_trace));
        evals.extend(tables_air::generate_trace(&self.perm.table_mult));
        tb.extend_evals(evals);
    }
    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let rel = self.relations().clone();
        let mut evals = Vec::new();
        let (sponge_ic, sponge_tr) = sponge_v::generate_interaction_trace(&rel, &self.run);
        evals.extend(sponge_tr);
        let (keccak_ic, keccak_tr) = keccak::generate_interaction_trace(&rel, &self.perm.keccak_data);
        evals.extend(keccak_tr);
        let (round_ic, round_tr) =
            keccak_round::generate_interaction_trace(&rel, &self.perm.round_data);
        evals.extend(round_tr);
        let (tables_ic, tables_tr) =
            tables_air::generate_interaction_trace(&rel, &self.perm.table_mult);
        evals.extend(tables_tr);
        tb.extend_evals(evals);
        self.claims = ServiceClaims {
            sponge: sponge_ic.claimed_sum,
            keccak: keccak_ic.claimed_sum,
            round: round_ic.claimed_sum,
            tables: tables_ic.claimed_sums,
        };
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
}

impl KeccakServiceVerifier {
    /// Reconstruct the service from the PUBLIC job shapes + the proof's claimed
    /// sums (`[sponge_v, keccak, round, tables ×9]`).
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
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let rel = self.relations().clone();
        self.built = Some(build_components(allocator, &self.jobs, &rel, &self.claims));
    }
    fn components(&self) -> Vec<&dyn Component> {
        self.built.as_ref().expect("built").ordered()
    }
}
