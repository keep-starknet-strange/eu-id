//! Shared Keccak components for a composed proof.
//!
//! The service owns one vertical sponge, the XOR and conversion lookup tables,
//! one layered Keccak proof, and two MLE components that bind that proof to the
//! committed sponge input and output columns. Consumers use the shared
//! [`KeccakRelations`] handle for their HashIo tuples.
//!
//! The component order is fixed:
//!
//! 1. sponge;
//! 2. XOR table;
//! 3. conversion table;
//! 4. output source tie-back;
//! 5. input source tie-back.

use stwo::core::air::Component;
use stwo::core::channel::Blake2sChannel;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::SecureField;
use stwo::core::verifier::VerificationError;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::Column;
use stwo::prover::lookups::mle::Mle;
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
use crate::layered_gkr::{
    self, LayeredKeccakProver, SourceOpening, SourceTieBack, SpongeSourceOracle,
};
use crate::relations::{KeccakRelations, SharedKeccakRelations};
use crate::sponge::Shape;
use crate::sponge_v::{self, JobList, SpongeVRun};
use crate::tables_air::{self, TableKind, TableMultiplicities};
use crate::utils::circle_row_to_coset;

const POST_INTERACTION_TREE: usize = 3;
const N_TABLES: usize = 2;

/// The service contributes the sponge, XOR-table, and conversion-table sums.
pub const fn service_claimed_sums_len() -> usize {
    1 + N_TABLES
}

#[derive(Clone, Default)]
struct ServiceClaims {
    sponge: SecureField,
    tables: [SecureField; N_TABLES],
}

impl ServiceClaims {
    fn ordered(&self) -> Vec<SecureField> {
        let mut claims = Vec::with_capacity(service_claimed_sums_len());
        claims.push(self.sponge);
        claims.extend(self.tables);
        claims
    }

    fn from_flat(flat: &[SecureField]) -> Self {
        assert_eq!(
            flat.len(),
            service_claimed_sums_len(),
            "service claimed sums length"
        );
        Self {
            sponge: flat[0],
            tables: [flat[1], flat[2]],
        }
    }
}

struct PendingTieBack {
    row_point: Vec<SecureField>,
    slot_point: Vec<SecureField>,
    claim: SecureField,
    mle: Option<Mle<SimdBackend, SecureField>>,
}

impl From<SourceTieBack> for PendingTieBack {
    fn from(source: SourceTieBack) -> Self {
        Self {
            row_point: source.row_point,
            slot_point: source.slot_point,
            claim: source.claim,
            mle: Some(source.mle),
        }
    }
}

enum TieBack {
    Prover(Box<MleEvalProverComponent<'static, SpongeSourceOracle>>),
    Verifier(Box<MleEvalVerifierComponent<SpongeSourceOracle>>),
}

struct Built {
    sponge: sponge_v::Component,
    tables: Vec<tables_air::Component>,
    tie_backs: [TieBack; 2],
}

impl Built {
    fn ordered(&self) -> Vec<&dyn Component> {
        let mut components: Vec<&dyn Component> = Vec::with_capacity(5);
        components.push(&self.sponge);
        components.extend(self.tables.iter().map(|table| table as &dyn Component));
        components.extend(self.tie_backs.iter().map(|tie_back| match tie_back {
            TieBack::Prover(component) => component.as_ref() as &dyn Component,
            TieBack::Verifier(component) => component.as_ref() as &dyn Component,
        }));
        components
    }

    fn ordered_prover(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        let mut components: Vec<&dyn ComponentProver<SimdBackend>> = Vec::with_capacity(5);
        components.push(&self.sponge);
        components.extend(
            self.tables
                .iter()
                .map(|table| table as &dyn ComponentProver<SimdBackend>),
        );
        for tie_back in &self.tie_backs {
            match tie_back {
                TieBack::Prover(component) => {
                    components.push(component.as_ref() as &dyn ComponentProver<SimdBackend>);
                }
                TieBack::Verifier(_) => {
                    unreachable!("prover components requested from verifier service")
                }
            }
        }
        components
    }
}

fn preprocessed_ids(jobs: &JobList) -> Vec<PreProcessedColumnId> {
    let mut ids = sponge_v::schedule_ids(jobs);
    ids.extend(tables_air::all_preprocessed_column_ids());
    ids
}

fn preprocessed_sizes(jobs: &JobList) -> Vec<u32> {
    let mut sizes = vec![jobs.log_size(); jobs.n_schedule_cols()];
    sizes.extend(tables_air::all_preprocessed_log_sizes());
    sizes
}

fn gen_preprocessed(jobs: &JobList) -> Vec<air_core::PreprocessedColumnEval> {
    let mut columns = sponge_v::gen_schedule_preprocessed(jobs);
    columns.extend(tables_air::generate_preprocessed_trace());
    columns
}

fn layout_for(jobs: &JobList) -> TreeLayout {
    let log_size = jobs.log_size();
    let mut trace = vec![log_size; jobs.n_base_cols()];
    trace.extend(TableKind::ALL.map(|kind| kind.log_size()));

    let mut interaction = vec![log_size; sponge_v::n_interaction_cols(jobs)];
    for kind in TableKind::ALL {
        interaction.extend([kind.log_size(); stwo::core::fields::qm31::SECURE_EXTENSION_DEGREE]);
    }

    TreeLayout {
        preprocessed: preprocessed_sizes(jobs),
        trace,
        interaction,
    }
}

/// Return the committed service layout for geometry and artifact checks.
pub fn debug_layout(shapes: Vec<Shape>) -> TreeLayout {
    layout_for(&JobList::new(shapes))
}

fn build_base_components(
    allocator: &mut TraceLocationAllocator,
    jobs: &JobList,
    relations: &KeccakRelations,
    claims: &ServiceClaims,
) -> (sponge_v::Component, Vec<tables_air::Component>) {
    let sponge = FrameworkComponent::new(
        allocator,
        sponge_v::Eval {
            jobs: jobs.clone(),
            relations: relations.clone(),
        },
        claims.sponge,
    );
    let tables = TableKind::ALL
        .iter()
        .enumerate()
        .map(|(index, kind)| {
            FrameworkComponent::new(
                allocator,
                tables_air::Eval {
                    log_size: kind.log_size(),
                    kind: *kind,
                    relations: relations.clone(),
                },
                claims.tables[index],
            )
        })
        .collect();
    (sponge, tables)
}

fn write_selected(
    tree: &mut TreeBuilder<SimdBackend, air_core::Mc>,
    jobs: &JobList,
    selected_ids: &[PreProcessedColumnId],
) {
    let ids = preprocessed_ids(jobs);
    let columns = gen_preprocessed(jobs);
    assert_eq!(ids.len(), columns.len(), "preprocessed ID/column mismatch");
    let selected: std::collections::HashSet<PreProcessedColumnId> =
        selected_ids.iter().cloned().collect();
    let mut emitted = std::collections::HashSet::new();
    let (picked_ids, picked_columns): (Vec<_>, Vec<_>) = ids
        .into_iter()
        .zip(columns)
        .filter(|(id, _)| selected.contains(id) && emitted.insert(id.clone()))
        .unzip();
    assert_eq!(
        picked_ids.as_slice(),
        selected_ids,
        "selected preprocessed IDs must follow first-writer order"
    );
    tree.extend_evals(picked_columns);
}

#[derive(Clone, Copy)]
struct RawColumnMutation {
    column: usize,
    coset_row: usize,
    delta: M31,
}

fn mutate_coset_cell(column: &mut crate::utils::ColEval, coset_row: usize, delta: M31) {
    let log_size = column.values.len().ilog2();
    let domain_row = circle_row_to_coset(log_size)
        .into_iter()
        .position(|row| row == coset_row)
        .expect("raw-column mutation row exists");
    column.values.as_mut_slice()[domain_row] += delta;
}

pub struct KeccakServiceProver {
    jobs: JobList,
    handle: SharedKeccakRelations,
    run: SpongeVRun,
    table_mult: TableMultiplicities,
    relations: Option<KeccakRelations>,
    claims: ServiceClaims,
    built: Option<Built>,
    layered: Option<LayeredKeccakProver>,
    tie_backs: Option<[PendingTieBack; 2]>,
    payload: Vec<u8>,
    raw_column_mutations: Vec<RawColumnMutation>,
}

impl KeccakServiceProver {
    /// Build one service for the complete canonical Keccak job list.
    pub fn new(shapes: Vec<Shape>, messages: Vec<Vec<u8>>, handle: SharedKeccakRelations) -> Self {
        let jobs = JobList::new(shapes);
        let mut stream_ids = std::collections::HashSet::new();
        for shape in &jobs.jobs {
            assert!(
                stream_ids.insert(shape.absorb_stream_id),
                "duplicate absorb stream ID {}",
                shape.absorb_stream_id
            );
            assert!(
                stream_ids.insert(shape.squeeze_stream_id),
                "duplicate squeeze stream ID {}",
                shape.squeeze_stream_id
            );
        }

        let run = sponge_v::generate_jobs(&jobs, &messages);
        let table_mult = TableMultiplicities::from_sponge(&run.xor, &run.conv);
        let layered = LayeredKeccakProver::new(&jobs, &run);
        if std::env::var_os("KECCAK_PERMS_DUMP").is_some() {
            eprintln!(
                "keccak-service n_jobs={} n_perms_total={} p_log={}",
                jobs.jobs.len(),
                jobs.n_perms_total(),
                jobs.log_size()
            );
        }

        Self {
            jobs,
            handle,
            run,
            table_mult,
            relations: None,
            claims: ServiceClaims::default(),
            built: None,
            layered: Some(layered),
            tie_backs: None,
            payload: Vec::new(),
            raw_column_mutations: Vec::new(),
        }
    }

    pub fn job_outputs(&self) -> &[Vec<u8>] {
        &self.run.outputs
    }

    pub fn claimed_sums(&self) -> Vec<SecureField> {
        self.claims.ordered()
    }

    /// Mutate committed sponge data in adversarial tests.
    #[doc(hidden)]
    pub fn run_mut(&mut self) -> &mut SpongeVRun {
        &mut self.run
    }

    /// Mutate the independent layered witness in adversarial tests.
    #[doc(hidden)]
    pub fn layered_mut(&mut self) -> &mut LayeredKeccakProver {
        self.layered.as_mut().expect("layered prover is available")
    }

    /// Add 256 to the low nibble and subtract 1 from the high nibble.
    /// This keeps `low + 256 * high` unchanged.
    #[doc(hidden)]
    pub fn tamper_input_nibble_pair(&mut self, coset_row: usize, byte: usize) {
        assert!(coset_row < self.jobs.n_perms_total());
        assert!(byte < N_BYTES_IN_STATE);
        let low_column = self.jobs.input_nibble_col_start() + 2 * byte;
        self.raw_column_mutations.extend([
            RawColumnMutation {
                column: low_column,
                coset_row,
                delta: M31::from(layered_gkr::NIBBLE_PAIR_RADIX),
            },
            RawColumnMutation {
                column: low_column + 1,
                coset_row,
                delta: -M31::from(1u32),
            },
        ]);
        self.layered_mut().tamper_input_nibble_pair(coset_row, byte);
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
        vec![self.jobs.log_size(); layered_gkr::N_TIEBACK_COLUMNS]
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let relations = self.relations().clone();
        let (sponge, tables) =
            build_base_components(allocator, &self.jobs, &relations, &self.claims);
        let locations = sponge.trace_locations().to_vec();
        let [output, input] = self
            .tie_backs
            .as_mut()
            .expect("layered proof was generated");
        let output_oracle =
            SpongeSourceOracle::output(locations.clone(), &self.jobs, output.slot_point.clone());
        let input_oracle =
            SpongeSourceOracle::input(locations, &self.jobs, input.slot_point.clone());
        let twiddles = air_core::twiddles(self.jobs.log_size() + 4);
        let output_component = MleEvalProverComponent::generate(
            allocator,
            output_oracle,
            &output.row_point,
            output.mle.take().expect("output source MLE is available"),
            output.claim,
            twiddles,
            POST_INTERACTION_TREE,
        );
        let input_component = MleEvalProverComponent::generate(
            allocator,
            input_oracle,
            &input.row_point,
            input.mle.take().expect("input source MLE is available"),
            input.claim,
            twiddles,
            POST_INTERACTION_TREE,
        );
        self.built = Some(Built {
            sponge,
            tables,
            tie_backs: [
                TieBack::Prover(Box::new(output_component)),
                TieBack::Prover(Box::new(input_component)),
            ],
        });
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built.as_ref().expect("components built").ordered()
    }
}

impl AirProver for KeccakServiceProver {
    fn max_log_size(&self) -> u32 {
        self.jobs.log_size().max(TableKind::Xor3.log_size())
    }

    fn write_preprocessed(&mut self, tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tree.extend_evals(gen_preprocessed(&self.jobs));
    }

    fn write_selected_preprocessed(
        &mut self,
        tree: &mut TreeBuilder<SimdBackend, air_core::Mc>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        write_selected(tree, &self.jobs, selected_ids);
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "stwo_keccak::KeccakService",
            &preprocessed_ids(&self.jobs),
            &gen_preprocessed(&self.jobs),
        )
    }

    fn write_trace(&mut self, tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let mut columns = sponge_v::generate_base_trace(&self.run);
        for mutation in self.raw_column_mutations.iter().copied() {
            mutate_coset_cell(
                &mut columns[mutation.column],
                mutation.coset_row,
                mutation.delta,
            );
        }
        columns.extend(tables_air::generate_trace(&self.table_mult));
        tree.extend_evals(columns);
    }

    fn write_interaction(&mut self, tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let relations = self.relations().clone();
        let (sponge_claim, mut columns) =
            sponge_v::generate_interaction_trace(&relations, &self.run);
        let (table_claims, table_columns) =
            tables_air::generate_interaction_trace(&relations, &self.table_mult);
        columns.extend(table_columns);
        tree.extend_evals(columns);
        self.claims = ServiceClaims {
            sponge: sponge_claim.claimed_sum,
            tables: table_claims
                .claimed_sums
                .try_into()
                .expect("exactly two table claims"),
        };
    }

    fn prove_post_interaction(&mut self, channel: &mut air_core::Ch) {
        let proof = self
            .layered
            .take()
            .expect("layered prover is available once")
            .prove(channel);
        self.payload = proof.payload;
        self.tie_backs = Some([proof.output.into(), proof.input.into()]);
    }

    fn take_post_interaction_payload(&mut self) -> Vec<u8> {
        std::mem::take(&mut self.payload)
    }

    fn write_post_interaction(&mut self, tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        for source in self
            .tie_backs
            .as_ref()
            .expect("layered proof was generated")
        {
            tree.extend_evals(build_tieback_trace(
                source.mle.as_ref().expect("source MLE is available"),
                &source.row_point,
                source.claim,
            ));
        }
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        self.built
            .as_ref()
            .expect("components built")
            .ordered_prover()
    }
}

pub struct KeccakServiceVerifier {
    jobs: JobList,
    handle: SharedKeccakRelations,
    claims: ServiceClaims,
    relations: Option<KeccakRelations>,
    built: Option<Built>,
    payload: Vec<u8>,
    openings: Option<[SourceOpening; 2]>,
}

impl KeccakServiceVerifier {
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
            payload: Vec::new(),
            openings: None,
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
        vec![self.jobs.log_size(); layered_gkr::N_TIEBACK_COLUMNS]
    }

    fn load_post_interaction_payload(&mut self, payload: &[u8]) {
        self.payload = payload.to_vec();
    }

    fn verify_post_interaction(
        &mut self,
        channel: &mut air_core::Ch,
    ) -> Result<(), VerificationError> {
        let verified = layered_gkr::verify_layered_keccak(&self.payload, &self.jobs, channel)?;
        self.openings = Some([verified.output, verified.input]);
        Ok(())
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let relations = self.relations().clone();
        let (sponge, tables) =
            build_base_components(allocator, &self.jobs, &relations, &self.claims);
        let locations = sponge.trace_locations().to_vec();
        let [output, input] = self.openings.as_ref().expect("layered proof was verified");
        let output_oracle =
            SpongeSourceOracle::output(locations.clone(), &self.jobs, output.slot_point.clone());
        let input_oracle =
            SpongeSourceOracle::input(locations, &self.jobs, input.slot_point.clone());
        let output_component = MleEvalVerifierComponent::new(
            allocator,
            output_oracle,
            &output.row_point,
            output.claim,
            POST_INTERACTION_TREE,
        );
        let input_component = MleEvalVerifierComponent::new(
            allocator,
            input_oracle,
            &input.row_point,
            input.claim,
            POST_INTERACTION_TREE,
        );
        self.built = Some(Built {
            sponge,
            tables,
            tie_backs: [
                TieBack::Verifier(Box::new(output_component)),
                TieBack::Verifier(Box::new(input_component)),
            ],
        });
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built.as_ref().expect("components built").ordered()
    }
}
