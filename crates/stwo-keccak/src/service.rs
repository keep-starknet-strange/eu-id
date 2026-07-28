//! `KeccakService` — the ONE keccak side of a composed proof (S1).
//!
//! An air-core module pair ([`KeccakServiceProver`] impl `Air`+`AirProver`,
//! [`KeccakServiceVerifier`] impl `Air`) that owns, exactly once per proof:
//!
//! 1. the rotated job-list sponge ([`crate::sponge_v`]) — every SHAKE-128/256
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

use num_traits::Zero;
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

use crate::constants::N_BYTES_IN_STATE;
use crate::keccak;
use crate::keccak_round;
use crate::relations::{KeccakRelations, SharedKeccakRelations};
use crate::round_gkr::{self, RoundCoeffOracle, RoundGkrProver, RoundTieBack};
use crate::sponge::Shape;
use crate::sponge_v::{self, JobList, SpongeVRun};
use crate::tables_air::{self, TableKind, TableMultiplicities};

/// The shared commitment-tree index of the post-interaction tie-back trace.
const POST_INTERACTION_TREE: usize = 3;

/// The exact `claimed_sums` length the service contributes:
/// `[sponge_v, keccak, round, tables ×9]`.
pub fn service_claimed_sums_len() -> usize {
    3 + TableKind::ALL.len()
}

fn round_log_size(n_perms_total: usize) -> u32 {
    ((n_perms_total * crate::constants::N_ROUNDS) as u32)
        .next_power_of_two()
        .ilog2()
        .max(stwo::prover::backend::simd::m31::LOG_N_LANES)
}

pub type TraceCol = CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>;

/// The keccak + keccak_round witness for a set of permutation requests, plus
/// the round-derived table multiplicities.
pub struct PermWitness {
    pub keccak_claim: keccak::Claim,
    pub keccak_trace: Vec<TraceCol>,
    pub keccak_data: keccak::InteractionClaimData,
    pub round_claim: keccak_round::Claim,
    pub round_trace: Vec<TraceCol>,
    pub round_data: keccak_round::InteractionClaimData,
    pub table_mult: TableMultiplicities,
}

/// Build the keccak permutation prover + round prover traces for `perm_inputs`
/// (concatenated across any number of sponge jobs).
pub fn build_perm_witness(perm_inputs: &[[PackedM31; N_BYTES_IN_STATE + 1]]) -> PermWitness {
    let (keccak_claim, keccak_trace, keccak_data) = keccak::Claim::generate_trace(perm_inputs);

    let mut round_instances: Vec<([u8; N_BYTES_IN_STATE], u32, u32)> = Vec::new();
    for prow in perm_inputs {
        let mut state = [0u8; N_BYTES_IN_STATE];
        for i in 0..N_BYTES_IN_STATE {
            state[i] = crate::utils::unspread_u32(prow[i].to_array()[0].0) as u8;
        }
        let perm_id = prow[N_BYTES_IN_STATE].to_array()[0].0;
        for round in 0..crate::constants::N_ROUNDS {
            round_instances.push((state, round as u32, perm_id));
            let mut sp: [PackedM31; N_BYTES_IN_STATE] = std::array::from_fn(|i| {
                PackedM31::from(stwo::core::fields::m31::M31::from(state[i] as u32))
            });
            crate::utils::keccak_f1600_round(&mut sp, round);
            for i in 0..N_BYTES_IN_STATE {
                state[i] = sp[i].to_array()[0].0 as u8;
            }
        }
    }
    let n_rounds = round_instances.len();
    let round_inputs = pack_round_instances(&round_instances);
    let (round_claim, round_ct, round_data) =
        keccak_round::Claim::generate_trace(round_inputs, n_rounds);

    let table_mult = TableMultiplicities::from_round(&round_data);

    PermWitness {
        keccak_claim,
        keccak_trace,
        keccak_data,
        round_claim,
        round_trace: round_ct.to_evals().into_iter().collect(),
        round_data,
        table_mult,
    }
}

/// Pack per-lane `(state, round_idx, perm_id)` instances into
/// `[state|round|perm_id]` vec-rows, `N_LANES` distinct instances per row.
fn pack_round_instances(
    instances: &[([u8; N_BYTES_IN_STATE], u32, u32)],
) -> Vec<[PackedM31; N_BYTES_IN_STATE + 2]> {
    use stwo::core::fields::m31::M31;
    use stwo::prover::backend::simd::m31::N_LANES;

    let n_vec_rows = instances.len().div_ceil(N_LANES);
    let mut rows = Vec::with_capacity(n_vec_rows);
    for vr in 0..n_vec_rows {
        let mut row = [PackedM31::zero(); N_BYTES_IN_STATE + 2];
        let mut state_lanes = [[M31::from(0u32); N_LANES]; N_BYTES_IN_STATE];
        let mut round_lanes = [M31::from(0u32); N_LANES];
        let mut perm_id_lanes = [M31::from(0u32); N_LANES];
        for lane in 0..N_LANES {
            let idx = vr * N_LANES + lane;
            if idx >= instances.len() {
                break;
            }
            let (state, round, perm_id) = &instances[idx];
            for i in 0..N_BYTES_IN_STATE {
                state_lanes[i][lane] = M31::from(crate::utils::spread_u32(state[i] as u32));
            }
            round_lanes[lane] = M31::from(*round);
            perm_id_lanes[lane] = M31::from(*perm_id);
        }
        for i in 0..N_BYTES_IN_STATE {
            row[i] = PackedM31::from_array(state_lanes[i]);
        }
        row[N_BYTES_IN_STATE] = PackedM31::from_array(round_lanes);
        row[N_BYTES_IN_STATE + 1] = PackedM31::from_array(perm_id_lanes);
        rows.push(row);
    }
    rows
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
        assert_eq!(
            flat.len(),
            service_claimed_sums_len(),
            "service claimed sums length"
        );
        Self {
            sponge: flat[0],
            keccak: flat[1],
            round: flat[2],
            tables: flat[3..].to_vec(),
        }
    }
}

/// The round GKR tie-back component — prover and verifier flavors of the
/// `MleEval` component over the δ-folded coeff column.
enum TieBack {
    Prover(Box<MleEvalProverComponent<'static, RoundCoeffOracle>>),
    Verifier(Box<MleEvalVerifierComponent<RoundCoeffOracle>>),
}

struct Built {
    sponge: sponge_v::Component,
    keccak: keccak::Component,
    round: keccak_round::Component,
    tables: Vec<tables_air::Component>,
    tie_back: TieBack,
}

impl Built {
    fn ordered(&self) -> Vec<&dyn Component> {
        let mut out: Vec<&dyn Component> = vec![&self.sponge, &self.keccak, &self.round];
        out.extend(self.tables.iter().map(|c| c as &dyn Component));
        out.push(match &self.tie_back {
            TieBack::Prover(c) => c.as_ref() as &dyn Component,
            TieBack::Verifier(c) => c.as_ref() as &dyn Component,
        });
        out
    }
    fn ordered_prover(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        let mut out: Vec<&dyn ComponentProver<SimdBackend>> =
            vec![&self.sponge, &self.keccak, &self.round];
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
    ids.extend(keccak::schedule_ids(jobs.n_perms_total()));
    ids.extend(tables_air::all_preprocessed_column_ids());
    ids
}

fn preprocessed_sizes(jobs: &JobList) -> Vec<u32> {
    let keccak_claim = keccak::Claim {
        n_perms: jobs.n_perms_total(),
    };
    let mut sizes = vec![jobs.log_size(); sponge_v::N_SCHEDULE_COLS];
    sizes.extend(vec![keccak_claim.log_size(); keccak::N_SCHEDULE_COLS]);
    sizes.extend(tables_air::all_preprocessed_log_sizes());
    sizes
}

fn gen_preprocessed(jobs: &JobList) -> Vec<air_core::PreprocessedColumnEval> {
    let mut cols = sponge_v::gen_schedule_preprocessed(jobs);
    cols.extend(keccak::gen_schedule_preprocessed(jobs.n_perms_total()));
    cols.extend(tables_air::generate_preprocessed_trace());
    cols
}

fn layout_for(jobs: &JobList) -> TreeLayout {
    let ls = jobs.log_size();
    let n = jobs.n_perms_total();
    let keccak_claim = keccak::Claim { n_perms: n };
    let round_claim = keccak_round::Claim {
        log_size: round_log_size(n),
    };

    let mut trace = vec![ls; sponge_v::N_BASE_COLS];
    trace.extend(keccak_claim.log_sizes()[1].clone());
    trace.extend(round_claim.log_sizes()[1].clone());
    for kind in TableKind::ALL {
        for _ in 0..kind.n_relations() {
            trace.push(kind.log_size());
        }
    }

    // The round's LogUp is GKR-offloaded: NO round interaction columns; its
    // tie-back trace lives in the post-interaction tree instead.
    let _ = &round_claim;
    let mut interaction = vec![ls; sponge_v::N_INTERACTION_COLS];
    interaction.extend(keccak_claim.log_sizes()[2].clone());
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

/// Build the four framework components (the tie-back component is added per
/// side, prover vs verifier) and the tie-back oracle over the round
/// component's freshly-allocated trace locations.
fn build_base_components(
    allocator: &mut TraceLocationAllocator,
    jobs: &JobList,
    relations: &KeccakRelations,
    claims: &ServiceClaims,
    tie_back: &RoundTieBack,
) -> (
    sponge_v::Component,
    keccak::Component,
    keccak_round::Component,
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
    let keccak = FrameworkComponent::new(
        allocator,
        keccak::Eval {
            claim: keccak::Claim { n_perms: n },
            relations: relations.clone(),
        },
        claims.keccak,
    );
    let round = FrameworkComponent::new(
        allocator,
        keccak_round::Eval {
            claim: keccak_round::Claim {
                log_size: round_log_size(n),
            },
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
    let oracle = RoundCoeffOracle {
        locations: round.trace_locations().to_vec(),
        relations: relations.clone(),
        log_size: round_log_size(n),
        delta: tie_back.delta,
        eq_ws: tie_back.eq_ws.clone(),
    };
    (sponge, keccak, round, tables, oracle)
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
    /// Round GKR offload state, staged phase by phase:
    /// `write_interaction` → `round_gkr` (fractions + claimed sum);
    /// `prove_post_interaction` → `gkr_blob` + `tie_back` + `coeff_mle`;
    /// `write_post_interaction` commits the tie-back trace;
    /// `build_components` consumes `coeff_mle` into the MleEval component.
    round_gkr: Option<RoundGkrProver>,
    tie_back: Option<RoundTieBack>,
    gkr_blob: Vec<u8>,
    coeff_mle: Option<Mle<SimdBackend, SecureField>>,
}

impl KeccakServiceProver {
    /// Build the service from job shapes + their witness byte streams.
    /// `shapes[i]`'s `perm_id_base` is ignored — the service stamps the global
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

    /// Test-only tamper hook: mutate the permutation witness (round base trace
    /// or round lookup data) before proving. Lets the adversarial tests desync
    /// the committed round base columns from the GKR fraction multiset (the
    /// configuration the MLE-eval tie-back must reject) or tamper a chain-link
    /// tuple against the honest keccak component.
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
        let (sponge, keccak, round, tables, oracle) =
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
            keccak,
            round,
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
            .max(keccak::Claim { n_perms: n }.log_size())
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
        let (keccak_ic, keccak_tr) =
            keccak::generate_interaction_trace(&rel, &self.perm.keccak_data);
        evals.extend(keccak_tr);
        // The round emits NO interaction columns: its fraction multiset is
        // GKR-proven post tree-2 and tied back in the post-interaction tree.
        // Its claimed sum (the exact multiset sum) still occupies the same
        // slot in the global LogUp balance.
        let round_gkr = RoundGkrProver::new(&rel, &self.perm.round_data);
        let (tables_ic, tables_tr) =
            tables_air::generate_interaction_trace(&rel, &self.perm.table_mult);
        evals.extend(tables_tr);
        tb.extend_evals(evals);
        self.claims = ServiceClaims {
            sponge: sponge_ic.claimed_sum,
            keccak: keccak_ic.claimed_sum,
            round: round_gkr.claimed_sum(),
            tables: tables_ic.claimed_sums,
        };
        self.round_gkr = Some(round_gkr);
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
            self.claims.round,
            round_log_size(self.jobs.n_perms_total()),
            channel,
        )?;
        self.tie_back = Some(tie_back);
        Ok(())
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let rel = self.relations().clone();
        let tie_back = self.tie_back.as_ref().expect("verify_post_interaction ran");
        let (sponge, keccak, round, tables, oracle) =
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
            keccak,
            round,
            tables,
            tie_back: TieBack::Verifier(Box::new(tie_back_component)),
        });
    }
    fn components(&self) -> Vec<&dyn Component> {
        self.built.as_ref().expect("built").ordered()
    }
}
