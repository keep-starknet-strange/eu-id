//! Tests for the vertical job-list sponge and `KeccakService`.
//!
//! The tests cover one job, multiple jobs, padding edges, multiple squeeze
//! blocks, job-boundary isolation, and adversarial trace changes.
//!
//! Run one test harness thread and 12 Rayon workers:
//! `RAYON_NUM_THREADS=12 cargo test -p stwo-keccak --release --test service
//! -- --test-threads=1`.

use num_traits::{One, Zero};
use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::{Shake128, Shake256};

use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{SecureField, QM31, SECURE_EXTENSION_DEGREE};
use stwo::core::fri::FriConfig;
use stwo::core::pcs::PcsConfig;
use stwo::core::pcs::TreeVec;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES, N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::Column;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    assert_constraints_on_trace, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator,
    Relation, RelationEntry, TraceLocationAllocator,
};

use air_core::{Air, AirProver, PreprocessedColumnFingerprint, TreeLayout};

use stwo_keccak::constants::{
    IOTA_RC, IOTA_RC_BYTE_INDICES, N_BYTES_IN_STATE, N_BYTES_IN_U64, N_ROUNDS,
};
use stwo_keccak::keccak;
use stwo_keccak::keccak_round::{N_XOR3_C, N_XOR3_THETA_APPLY};
use stwo_keccak::relations::{HashIoRelation, KeccakRelations, SharedKeccakRelations};
use stwo_keccak::service::{
    service_claimed_sums_len, CarrierShardWitness, KeccakServiceProver, KeccakServiceVerifier,
    PermWitness,
};
use stwo_keccak::sponge::Shape;
use stwo_keccak::sponge_v::{
    gen_schedule_preprocessed, generate_base_trace, generate_interaction_trace, generate_jobs,
    schedule_ids, Eval as SpongeEval, JobList, SpongeVRun,
};
use stwo_keccak::tables::{build_conv_table, build_dense_table};
use stwo_keccak::tables_air::TableMultiplicities;
use stwo_keccak::utils::{col_eval, spread_u32, unspread_u32, ColEval, SPREAD_MAX};

// =====================================================================
// Test io-closer module: yields every job's absorb bytes (+) and requires
// the expected squeeze bytes (−) against the SHARED HashIo relation, closing
// the balance the sponge opens (the standalone io_provider, service-shaped).
// =====================================================================

#[derive(Clone, Copy)]
struct IoEntry {
    stream: u32,
    pos: u32,
    byte: u8,
    /// `true` = yield (+), `false` = require (−).
    positive: bool,
}

#[derive(Clone)]
struct IoCloserEval {
    entries: Vec<IoEntry>,
    hash_io: HashIoRelation,
}

impl FrameworkEval for IoCloserEval {
    fn log_size(&self) -> u32 {
        LOG_N_LANES
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        LOG_N_LANES + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let enabler = eval.next_trace_mask();
        let one = E::F::from(M31::one());
        eval.add_constraint(enabler.clone() * (one - enabler.clone()));
        let en = E::EF::from(enabler);
        for e in &self.entries {
            let sign = if e.positive { en.clone() } else { -en.clone() };
            eval.add_to_relation(RelationEntry::new(
                &self.hash_io,
                sign,
                &[
                    E::F::from(M31::from(e.stream)),
                    E::F::from(M31::from(e.pos)),
                    E::F::from(M31::from(e.byte as u32)),
                ],
            ));
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

struct IoCloser {
    entries: Vec<IoEntry>,
    handle: SharedKeccakRelations,
    hash_io: Option<HashIoRelation>,
    claimed: SecureField,
    component: Option<FrameworkComponent<IoCloserEval>>,
}

impl IoCloser {
    fn new(entries: Vec<IoEntry>, handle: SharedKeccakRelations) -> Self {
        Self {
            entries,
            handle,
            hash_io: None,
            claimed: SecureField::zero(),
            component: None,
        }
    }
    fn interaction(&self, hash_io: &HashIoRelation) -> (Vec<ColEval>, SecureField) {
        let zero = SecureField::zero();
        let one = SecureField::one();
        let mut gen = LogupTraceGenerator::new(LOG_N_LANES);
        let fracs: Vec<(PackedQM31, PackedQM31)> = self
            .entries
            .iter()
            .map(|e| {
                let tuple = [
                    M31::from(e.stream),
                    M31::from(e.pos),
                    M31::from(e.byte as u32),
                ];
                let d: SecureField = hash_io.combine(&tuple);
                let mut n = [zero; N_LANES];
                let mut dl = [one; N_LANES];
                n[0] = if e.positive { one } else { -one };
                dl[0] = d;
                (PackedQM31::from_array(n), PackedQM31::from_array(dl))
            })
            .collect();
        let mut i = 0;
        while i + 2 <= fracs.len() {
            let mut col = gen.new_col();
            let (n0, d0) = fracs[i];
            let (n1, d1) = fracs[i + 1];
            col.write_frac(0, n0 * d1 + n1 * d0, d0 * d1);
            col.finalize_col();
            i += 2;
        }
        if i < fracs.len() {
            let mut col = gen.new_col();
            let (n, d) = fracs[i];
            col.write_frac(0, n, d);
            col.finalize_col();
        }
        gen.finalize_last()
    }
    fn n_interaction_cols(&self) -> usize {
        self.entries.len().div_ceil(2) * SECURE_EXTENSION_DEGREE
    }
}

fn lane0_enabler_col() -> Vec<ColEval> {
    let rows = 1usize << LOG_N_LANES;
    let mut enabler = vec![M31::zero(); rows];
    enabler[0] = M31::one();
    vec![col_eval(LOG_N_LANES, enabler)]
}

impl Air for IoCloser {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(self.entries.len() as u64);
        for e in &self.entries {
            channel.mix_u64(e.stream as u64);
            channel.mix_u64(e.pos as u64);
            channel.mix_u64(e.byte as u64);
            channel.mix_u64(e.positive as u64);
        }
    }
    fn draw_relations(&mut self, _channel: &mut Blake2sChannel) {
        // Composed AFTER the service: read the shared handle, draw nothing.
        let hash_io = self.handle.get().hash_io;
        let (_, sum) = self.interaction(&hash_io);
        self.claimed = sum;
        self.hash_io = Some(hash_io);
    }
    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: Vec::new(),
            trace: vec![LOG_N_LANES],
            interaction: vec![LOG_N_LANES; self.n_interaction_cols()],
        }
    }
    fn claimed_sums(&self) -> Vec<SecureField> {
        vec![self.claimed]
    }
    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        Vec::new()
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.component = Some(FrameworkComponent::new(
            allocator,
            IoCloserEval {
                entries: self.entries.clone(),
                hash_io: self.hash_io.clone().expect("drawn"),
            },
            self.claimed,
        ));
    }
    fn components(&self) -> Vec<&dyn Component> {
        vec![self.component.as_ref().expect("built")]
    }
}

impl AirProver for IoCloser {
    fn max_log_size(&self) -> u32 {
        LOG_N_LANES
    }
    fn write_preprocessed(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}
    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        Vec::new()
    }
    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(lane0_enabler_col());
    }
    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let (trace, sum) = self.interaction(self.hash_io.as_ref().expect("drawn"));
        debug_assert_eq!(sum, self.claimed);
        tb.extend_evals(trace);
    }
    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![self.component.as_ref().expect("built")]
    }
}

// =====================================================================
// Fixture helpers.
// =====================================================================

const ALTERNATE_IOTA_ROUND: usize = 1;
const ALTERNATE_IOTA_RC: u64 = 0;

fn set_packed_lane(cell: &mut PackedM31, lane: usize, value: M31) {
    let mut values = cell.to_array();
    values[lane] = value;
    *cell = PackedM31::from_array(values);
}

fn packed_lane(cell: PackedM31, lane: usize) -> M31 {
    cell.to_array()[lane]
}

fn round_state(
    input: &[u8; N_BYTES_IN_STATE],
    round: usize,
    round_constant: u64,
) -> [u8; N_BYTES_IN_STATE] {
    let mut packed: [PackedM31; N_BYTES_IN_STATE] =
        std::array::from_fn(|index| PackedM31::from(M31::from(input[index] as u32)));
    stwo_keccak::utils::keccak_f1600_round(&mut packed, round);
    let mut output = std::array::from_fn(|index| packed[index].to_array()[0].0 as u8);
    let delta = IOTA_RC[round] ^ round_constant;
    for (byte, delta_byte) in output[..N_BYTES_IN_U64].iter_mut().zip(delta.to_le_bytes()) {
        *byte ^= delta_byte;
    }
    output
}

fn set_carrier_coset_cell(column: &mut ColEval, coset_row: usize, value: M31) {
    let log_size = column.values.len().ilog2();
    let domain_row = stwo_keccak::utils::circle_row_to_coset(log_size)
        .into_iter()
        .position(|row| row == coset_row)
        .expect("carrier coset row exists");
    column.values.as_mut_slice()[domain_row] = value;
}

fn carrier_coset_cell(column: &ColEval, coset_row: usize) -> M31 {
    let log_size = column.values.len().ilog2();
    let domain_row = stwo_keccak::utils::circle_row_to_coset(log_size)
        .into_iter()
        .position(|row| row == coset_row)
        .expect("carrier coset row exists");
    column.values.at(domain_row)
}

fn rotate_carrier_coset_column(column: &mut ColEval) {
    let n_rows = column.values.len();
    let log_size = n_rows.ilog2();
    let row_to_coset = stwo_keccak::utils::circle_row_to_coset(log_size);
    let mut coset_to_row = vec![0; n_rows];
    for (row, coset) in row_to_coset.iter().copied().enumerate() {
        coset_to_row[coset] = row;
    }
    let original = column.values.to_cpu();
    for (row, coset) in row_to_coset.into_iter().enumerate() {
        let source_coset = (coset + n_rows - 1) % n_rows;
        column.values.set(row, original[coset_to_row[source_coset]]);
    }
}

/// Build a coherent permutation with one wrong Iota constant. The carrier,
/// GKR leaves, table counts, sponge output, and all later rounds agree. Only
/// the verifier-fixed 25-position schedule has the official constant.
fn install_alternate_iota_witness(run: &mut SpongeVRun) -> PermWitness {
    assert_eq!(run.jobs.n_perms_total(), 1);
    let shape = &run.jobs.jobs[0];
    let rate = shape.rate();
    let perm_id = run.perm_inputs[0][N_BYTES_IN_STATE].to_array()[0];
    let mut state =
        std::array::from_fn(|index| unspread_u32(run.perm_inputs[0][index].to_array()[0].0) as u8);
    let mut states = Vec::with_capacity(N_ROUNDS + 1);
    states.push(state);
    for (round, official_constant) in IOTA_RC.iter().copied().enumerate().take(N_ROUNDS) {
        state = round_state(
            &state,
            round,
            if round == ALTERNATE_IOTA_ROUND {
                ALTERNATE_IOTA_RC
            } else {
                official_constant
            },
        );
        states.push(state);
    }

    run.rows[0].post = state;
    run.rows[0].squeeze_byte.fill(0);
    run.rows[0].squeeze_byte[..rate].copy_from_slice(&state[..rate]);
    run.outputs[0] = state[..rate].to_vec();
    run.conv.truncate(rate);
    run.conv.extend(state[..rate].iter().map(|byte| {
        [
            PackedM31::from(M31::from(*byte as u32)),
            PackedM31::from(M31::from(spread_u32(*byte as u32))),
        ]
    }));

    let boundary_data = keccak::BoundaryWitness {
        n_perms: 1,
        rows: states
            .iter()
            .map(|state| keccak::BoundaryRow {
                perm_id,
                state: std::array::from_fn(|index| M31::from(spread_u32(state[index] as u32))),
            })
            .collect(),
    };
    let mut carrier_witness = stwo_keccak::carrier::generate(&boundary_data, 0);
    let position = ALTERNATE_IOTA_ROUND + 1;
    let vector_row = position / N_LANES;
    let lane = position % N_LANES;

    // The carrier only commits the 4 nonzero-capable Iota byte lanes
    // (`IOTA_RC_BYTE_INDICES`); the other 4 are inlined as a zero literal in
    // the AIR and have no column to tamper. Each of those is 0 in both the
    // official and alternate constant here, so skipping them changes nothing.
    for (column, byte) in IOTA_RC_BYTE_INDICES.into_iter().enumerate() {
        let official = M31::from(spread_u32(
            IOTA_RC[ALTERNATE_IOTA_ROUND].to_le_bytes()[byte] as u32,
        ));
        let alternate = M31::from(spread_u32(ALTERNATE_IOTA_RC.to_le_bytes()[byte] as u32));
        set_carrier_coset_cell(
            &mut carrier_witness.trace[stwo_keccak::carrier::ROUND_CONSTANT_COLUMN_START + column],
            position,
            alternate,
        );
        set_carrier_coset_cell(
            &mut carrier_witness.interaction.trace_mut()
                [stwo_keccak::carrier::ROUND_CONSTANT_COLUMN_START + column],
            position,
            alternate,
        );
        let key = &mut carrier_witness.round.lookup_data.xor3[N_XOR3_C + N_XOR3_THETA_APPLY + byte]
            [vector_row][0];
        let changed_key = packed_lane(*key, lane) - official + alternate;
        set_packed_lane(key, lane, changed_key);
    }

    let mut table_mult =
        TableMultiplicities::from_carrier_round(&carrier_witness.round, boundary_data.n_perms);
    table_mult.add_sponge(&run.xor, &run.conv);
    PermWitness {
        shards: vec![CarrierShardWitness {
            carrier_claim: carrier_witness.claim,
            carrier_trace: carrier_witness.trace,
            carrier_data: Some(carrier_witness.interaction),
        }],
        table_mult,
    }
}

fn shapes_for(messages: &[Vec<u8>], n_squeezes: &[usize]) -> Vec<Shape> {
    messages
        .iter()
        .zip(n_squeezes)
        .enumerate()
        .map(|(i, (m, &sq))| Shape::new(m.len(), sq, (10 + 2 * i) as u32, (11 + 2 * i) as u32))
        .collect()
}

fn shake256_ref(message: &[u8], out_len: usize) -> Vec<u8> {
    let mut h = Shake256::default();
    h.update(message);
    let mut r = h.finalize_xof();
    let mut out = vec![0u8; out_len];
    r.read(&mut out);
    out
}

fn shake128_ref(message: &[u8], out_len: usize) -> Vec<u8> {
    let mut h = Shake128::default();
    h.update(message);
    let mut r = h.finalize_xof();
    let mut out = vec![0u8; out_len];
    r.read(&mut out);
    out
}

fn closer_entries(shapes: &[Shape], messages: &[Vec<u8>], outputs: &[Vec<u8>]) -> Vec<IoEntry> {
    let mut entries = Vec::new();
    for ((shape, msg), out) in shapes.iter().zip(messages).zip(outputs) {
        for (pos, &b) in msg.iter().enumerate() {
            entries.push(IoEntry {
                stream: shape.absorb_stream_id,
                pos: pos as u32,
                byte: b,
                positive: true, // provider yields; the sponge consumes (−)
            });
        }
        for (pos, &b) in out.iter().enumerate() {
            entries.push(IoEntry {
                stream: shape.squeeze_stream_id,
                pos: pos as u32,
                byte: b,
                positive: false, // pin the sponge's yields to the expected bytes
            });
        }
    }
    entries
}

struct ProvedJobs {
    shapes: Vec<Shape>,
    messages: Vec<Vec<u8>>,
    outputs: Vec<Vec<u8>>,
    service_claims: Vec<SecureField>,
    proof: stwo::core::proof::StarkProof<air_core::Hasher>,
    /// Per-module opaque post-interaction payloads (the service's round-GKR blob).
    payloads: Vec<Vec<u8>>,
}

/// Batch-four round LogUp constraints have log-degree excess two.
fn pcs_config() -> PcsConfig {
    PcsConfig {
        fri_config: FriConfig::new(0, 2, 3, 1),
        ..PcsConfig::default()
    }
}

/// Prove `[service(jobs), io_closer]`, optionally tampering the sponge run
/// (base + sponge interaction data) before any tree is committed.
fn prove_jobs(
    messages: Vec<Vec<u8>>,
    n_squeezes: Vec<usize>,
    tamper: Option<&dyn Fn(&mut SpongeVRun)>,
) -> ProvedJobs {
    prove_jobs_full(messages, n_squeezes, tamper, None, pcs_config())
}

/// [`prove_jobs`] with a permutation-witness tamper hook (round base trace /
/// round lookup data) and an explicit PCS config.
fn prove_jobs_full(
    messages: Vec<Vec<u8>>,
    n_squeezes: Vec<usize>,
    tamper: Option<&dyn Fn(&mut SpongeVRun)>,
    perm_tamper: Option<&dyn Fn(&mut PermWitness)>,
    config: PcsConfig,
) -> ProvedJobs {
    let shapes = shapes_for(&messages, &n_squeezes);
    prove_shapes_full(shapes, messages, tamper, perm_tamper, config)
}

fn prove_shapes_full(
    shapes: Vec<Shape>,
    messages: Vec<Vec<u8>>,
    tamper: Option<&dyn Fn(&mut SpongeVRun)>,
    perm_tamper: Option<&dyn Fn(&mut PermWitness)>,
    config: PcsConfig,
) -> ProvedJobs {
    let handle = SharedKeccakRelations::new();
    let mut service = KeccakServiceProver::new(shapes.clone(), messages.clone(), handle.clone());
    let outputs = service.job_outputs().to_vec();
    if let Some(t) = tamper {
        t(service.run_mut());
    }
    if let Some(t) = perm_tamper {
        t(service.perm_mut());
    }
    let mut closer = IoCloser::new(closer_entries(&shapes, &messages, &outputs), handle);
    let (proof, payloads) =
        air_core::prove_with_post_interaction(&mut [&mut service, &mut closer], config)
            .expect("prove");
    ProvedJobs {
        shapes,
        messages,
        outputs,
        service_claims: service.claimed_sums(),
        proof,
        payloads,
    }
}

fn verify_jobs(p: &ProvedJobs, closer_msgs: &[Vec<u8>]) -> Result<(), air_core::VerifyError> {
    verify_jobs_with_payloads(p, closer_msgs, &p.payloads)
}

fn verify_jobs_with_payloads(
    p: &ProvedJobs,
    closer_msgs: &[Vec<u8>],
    payloads: &[Vec<u8>],
) -> Result<(), air_core::VerifyError> {
    let handle = SharedKeccakRelations::new();
    let mut service =
        KeccakServiceVerifier::new(p.shapes.clone(), p.service_claims.clone(), handle.clone());
    let mut closer = IoCloser::new(closer_entries(&p.shapes, closer_msgs, &p.outputs), handle);
    air_core::verify_with_expected_preprocessed_root_and_payloads(
        &mut [&mut service, &mut closer],
        &p.proof,
        None,
        payloads,
    )
}

fn m1(v: u32) -> M31 {
    M31::from(v)
}

/// A tampered configuration is REJECTED if proving fails/panics or verify errs.
fn rejected(
    messages: Vec<Vec<u8>>,
    n_squeezes: Vec<usize>,
    tamper: &dyn Fn(&mut SpongeVRun),
) -> bool {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let p = prove_jobs(messages.clone(), n_squeezes, Some(tamper));
        verify_jobs(&p, &messages).is_err()
    }))
    .unwrap_or(true)
}

/// A permutation-witness tamper is rejected whether the prover's local
/// constraint check fails early or the verifier rejects the produced proof.
fn perm_rejected(
    messages: Vec<Vec<u8>>,
    n_squeezes: Vec<usize>,
    tamper: &dyn Fn(&mut PermWitness),
) -> bool {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let p = prove_jobs_full(
            messages.clone(),
            n_squeezes,
            None,
            Some(tamper),
            pcs_config(),
        );
        verify_jobs(&p, &messages).is_err()
    }))
    .unwrap_or(true)
}

// =====================================================================
// Positive gates.
// =====================================================================

#[test]
fn single_job_proves_and_matches_sha3() {
    let msg = (0..300u32).map(|i| (i * 7 + 3) as u8).collect::<Vec<u8>>();
    let p = prove_jobs(vec![msg.clone()], vec![1], None);
    assert_eq!(
        p.outputs[0],
        shake256_ref(&msg, 136),
        "rotated sponge output != sha3"
    );
    verify_jobs(&p, &p.messages.clone()).expect("single-job verify");
}

#[test]
fn fixed_capacity_geometry_and_tree_zero_ignore_actual_length() {
    const CAPACITY: usize = 1_024;
    const LENGTHS: [usize; 4] = [130, 303, 456, CAPACITY];

    let shape = |len| Shape::with_message_capacity(len, CAPACITY, 1, 10, 11).unwrap();
    let assert_columns_equal = |actual: &[ColEval], expected: &[ColEval], label: &str| {
        assert_eq!(actual.len(), expected.len(), "{label}: column count");
        for (column_index, (actual, expected)) in actual.iter().zip(expected).enumerate() {
            assert_eq!(
                actual.domain.log_size(),
                expected.domain.log_size(),
                "{label}: column {column_index} log size"
            );
            assert_eq!(
                actual.values.len(),
                expected.values.len(),
                "{label}: column {column_index} row count"
            );
            for row in 0..actual.values.len() {
                assert_eq!(
                    actual.values.at(row),
                    expected.values.at(row),
                    "{label}: column {column_index}, row {row}"
                );
            }
        }
    };
    let baseline_jobs = JobList::new([shape(LENGTHS[0])]);
    let baseline_layout = {
        let mut verifier = KeccakServiceVerifier::new(
            vec![shape(LENGTHS[0])],
            vec![SecureField::zero(); service_claimed_sums_len()],
            SharedKeccakRelations::new(),
        );
        (
            verifier.layout(),
            verifier.preprocessed_column_ids(),
            verifier
                .canonical_preprocessed_columns()
                .expect("baseline canonical preprocessed columns"),
            air_core::compute_canonical_preprocessed_root(&mut [&mut verifier], pcs_config())
                .expect("baseline canonical preprocessed root"),
        )
    };

    for len in LENGTHS {
        let jobs = JobList::new([shape(len)]);
        assert_eq!(jobs.shape_digest(), baseline_jobs.shape_digest());
        assert_eq!(jobs.n_perms_total(), baseline_jobs.n_perms_total());
        assert_eq!(schedule_ids(&jobs), schedule_ids(&baseline_jobs));
        assert_columns_equal(
            &gen_schedule_preprocessed(&jobs),
            &gen_schedule_preprocessed(&baseline_jobs),
            &format!("actual length {len} changed capacity-only schedule bytes"),
        );

        let mut verifier = KeccakServiceVerifier::new(
            vec![shape(len)],
            vec![SecureField::zero(); service_claimed_sums_len()],
            SharedKeccakRelations::new(),
        );
        let layout = verifier.layout();
        assert_eq!(layout.preprocessed, baseline_layout.0.preprocessed);
        assert_eq!(layout.trace, baseline_layout.0.trace);
        assert_eq!(layout.interaction, baseline_layout.0.interaction);
        assert_eq!(verifier.preprocessed_column_ids(), baseline_layout.1);
        assert_columns_equal(
            &verifier
                .canonical_preprocessed_columns()
                .expect("canonical preprocessed columns"),
            &baseline_layout.2,
            &format!("actual length {len} changed canonical preprocessed bytes"),
        );
        assert_eq!(
            air_core::compute_canonical_preprocessed_root(&mut [&mut verifier], pcs_config())
                .expect("canonical preprocessed root"),
            baseline_layout.3,
            "actual length {len} changed tree zero"
        );
    }

    let mut short_channel = Blake2sChannel::default();
    let mut long_channel = Blake2sChannel::default();
    JobList::new([shape(130)]).mix_into(&mut short_channel);
    JobList::new([shape(456)]).mix_into(&mut long_channel);
    assert_ne!(
        short_channel.draw_secure_felt(),
        long_channel.draw_secure_felt(),
        "actual public length must remain transcript-bound"
    );
}

#[test]
fn canonical_n261_carrier_shards_are_pinned() {
    const N_PERMUTATIONS: usize = 261;
    const CAPACITY_PERMUTATIONS: usize = 256;
    const SHAKE256_RATE: usize = 136;
    const EXPECTED_SCHEDULE_COLUMNS: usize = 16;
    const EXPECTED_CARRIER_AND_TIEBACK_CELLS: usize = 6_083_584;
    const EXPECTED_SERVICE_CELLS: usize = 7_532_960;

    let capacity_bytes = (CAPACITY_PERMUTATIONS - 1) * SHAKE256_RATE;
    let mut shapes = vec![Shape::with_message_capacity(0, capacity_bytes, 1, 1, 2)
        .expect("valid fixed-capacity shape")];
    for remainder in 16..21 {
        let stream = 10 + 2 * remainder as u32;
        shapes.push(Shape::new(remainder, 1, stream, stream + 1));
    }

    let jobs = JobList::new(shapes.clone());
    assert_eq!(jobs.n_perms_total(), N_PERMUTATIONS);
    assert_eq!(jobs.log_size(), 9);
    assert_eq!(jobs.n_schedule_cols(), EXPECTED_SCHEDULE_COLUMNS);
    assert_eq!(jobs.n_base_cols(), 1_042);
    assert_eq!(stwo_keccak::sponge_v::n_interaction_cols(&jobs), 848);

    let carrier_claims = stwo_keccak::service::carrier_shard_claims(N_PERMUTATIONS);
    assert_eq!(carrier_claims.len(), 3);
    assert_eq!(
        carrier_claims
            .iter()
            .map(|claim| (claim.perm_id_base, claim.n_perms, claim.log_size()))
            .collect::<Vec<_>>(),
        [(0, 163, 12), (163, 81, 11), (244, 17, 9)]
    );
    assert_eq!(
        N_PERMUTATIONS * stwo_keccak::carrier::ROWS_PER_PERMUTATION,
        6_525
    );
    assert_eq!(stwo_keccak::carrier::N_COLUMNS, 906);
    assert_eq!(stwo_keccak::carrier::N_TOTAL_LOOKUPS, 899);
    assert_eq!(stwo_keccak::round_gkr::LOG_SLOTS, 10);
    assert_eq!(stwo_keccak::round_gkr::N_TIEBACK_COLUMNS, 8);
    assert_eq!(
        carrier_claims
            .iter()
            .map(|claim| stwo_keccak::round_gkr::LOG_SLOTS + claim.log_size())
            .collect::<Vec<_>>(),
        [22, 21, 19]
    );

    let layout = stwo_keccak::service::debug_layout(shapes);
    let committed_cells = |logs: &[u32]| {
        logs.iter()
            .map(|&log_size| 1usize << log_size)
            .sum::<usize>()
    };
    let carrier_rows = carrier_claims
        .iter()
        .map(|claim| 1usize << claim.log_size())
        .sum::<usize>();
    let tieback_cells = stwo_keccak::round_gkr::N_TIEBACK_COLUMNS * carrier_rows;
    let carrier_cells = stwo_keccak::carrier::N_COLUMNS * carrier_rows;
    assert_eq!(
        carrier_cells + tieback_cells,
        EXPECTED_CARRIER_AND_TIEBACK_CELLS
    );
    assert_eq!(
        (stwo_keccak::carrier::N_SCHEDULE_TABLE_PREPROCESSED
            + stwo_keccak::carrier::N_SCHEDULE_TABLE_TRACE
            + stwo_keccak::carrier::N_SCHEDULE_TABLE_INTERACTION)
            << stwo_keccak::carrier::SCHEDULE_TABLE_LOG_SIZE,
        416
    );
    let service_cells = committed_cells(&layout.preprocessed)
        + committed_cells(&layout.trace)
        + committed_cells(&layout.interaction)
        + tieback_cells;
    assert_eq!(service_cells, EXPECTED_SERVICE_CELLS);
    assert_eq!(
        service_cells - EXPECTED_CARRIER_AND_TIEBACK_CELLS,
        1_449_376
    );
}

#[test]
fn carrier_witness_generator_supports_n261() {
    const N_PERMUTATIONS: usize = 261;
    const EXPECTED_SHARDS: [(usize, usize, u32); 3] = [(0, 163, 12), (163, 81, 11), (244, 17, 9)];

    let mut inputs = vec![[PackedM31::zero(); N_BYTES_IN_STATE + 1]; N_PERMUTATIONS];
    for (permutation, input) in inputs.iter_mut().enumerate() {
        input[N_BYTES_IN_STATE] = PackedM31::from(M31::from(permutation as u32));
    }
    let witness = stwo_keccak::service::build_perm_witness(&inputs);
    assert_eq!(witness.shards.len(), EXPECTED_SHARDS.len());
    for (shard, (perm_id_base, n_perms, log_size)) in
        witness.shards.into_iter().zip(EXPECTED_SHARDS)
    {
        assert_eq!(shard.carrier_claim.perm_id_base, perm_id_base);
        assert_eq!(shard.carrier_claim.n_perms, n_perms);
        assert_eq!(shard.carrier_claim.log_size(), log_size);
        assert_eq!(shard.carrier_trace.len(), stwo_keccak::carrier::N_COLUMNS);
        assert!(shard
            .carrier_trace
            .iter()
            .all(|column| column.domain.log_size() == log_size));
        let data = shard.carrier_data.expect("carrier GKR source");
        assert_eq!(data.log_size, log_size);
        assert_eq!(data.n_perms, n_perms);
        assert_eq!(data.perm_id_base, perm_id_base);
    }
}

#[test]
fn carrier_shard_planner_boundaries_are_pinned() {
    let cases: &[(usize, &[(usize, usize, u32)])] = &[
        (1, &[(0, 1, 5)]),
        (163, &[(0, 163, 12)]),
        (164, &[(0, 163, 12), (163, 1, 5)]),
        (244, &[(0, 163, 12), (163, 81, 11)]),
        (245, &[(0, 163, 12), (163, 81, 11), (244, 1, 5)]),
        (252, &[(0, 163, 12), (163, 81, 11), (244, 8, 8)]),
        (261, &[(0, 163, 12), (163, 81, 11), (244, 17, 9)]),
    ];

    for &(n_perms, expected) in cases {
        let actual = stwo_keccak::service::carrier_shard_claims(n_perms)
            .into_iter()
            .map(|claim| (claim.perm_id_base, claim.n_perms, claim.log_size()))
            .collect::<Vec<_>>();
        assert_eq!(
            actual, expected,
            "unexpected plan for {n_perms} permutations"
        );
    }
}

#[test]
fn nonzero_carrier_shard_base_is_constrained() {
    const PERMUTATION_COLUMN: usize = 3;
    const PERM_ID_BASE: usize = 163;
    const N_PERMUTATIONS: usize = 2;

    let mut inputs = vec![[PackedM31::zero(); N_BYTES_IN_STATE + 1]; N_PERMUTATIONS];
    for (permutation, input) in inputs.iter_mut().enumerate() {
        input[N_BYTES_IN_STATE] = PackedM31::from(M31::from((PERM_ID_BASE + permutation) as u32));
    }
    let boundaries = keccak::generate_boundary_witness(&inputs);
    let mut witness = stwo_keccak::carrier::generate(&boundaries, PERM_ID_BASE);
    let claim = witness.claim;
    let assert_trace = |trace: &[ColEval]| {
        let trace = TreeVec::new(vec![
            Vec::new(),
            trace.iter().map(|column| column.to_cpu().values).collect(),
            Vec::new(),
        ]);
        let trace = trace.as_cols_ref();
        let eval = stwo_keccak::carrier::Eval { claim };
        assert_constraints_on_trace(
            &trace,
            eval.log_size(),
            |row| {
                eval.evaluate(row);
            },
            SecureField::zero(),
        );
    };

    assert_trace(&witness.trace);
    set_carrier_coset_cell(
        &mut witness.trace[PERMUTATION_COLUMN],
        0,
        M31::from((PERM_ID_BASE - 1) as u32),
    );
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            assert_trace(&witness.trace);
        }))
        .is_err(),
        "the first row must be pinned to the shard's public permutation base"
    );
}

#[test]
fn fixed_capacity_hashes_actual_prefix_and_canonicalizes_unused_rows() {
    const CAPACITY: usize = 1_024;
    let mut canonical_unused_post = None;

    for len in [130usize, 303, 456, CAPACITY] {
        let message = (0..len)
            .map(|i| (i as u8).wrapping_mul(29).wrapping_add(7))
            .collect::<Vec<_>>();
        let jobs = JobList::new([Shape::with_message_capacity(len, CAPACITY, 1, 10, 11).unwrap()]);
        let run = generate_jobs(&jobs, std::slice::from_ref(&message));
        assert_eq!(run.outputs[0], shake256_ref(&message, 136));
        assert_eq!(run.rows.len(), (CAPACITY + 1).div_ceil(136));

        let actual_rows = (len + 1).div_ceil(136);
        assert!(run.rows[..actual_rows].iter().all(|row| row.absorb_active));
        assert!(run.rows[actual_rows - 1].squeeze_active);
        for (row_index, row) in run.rows.iter().enumerate().skip(actual_rows) {
            assert!(!row.absorb_active);
            assert!(!row.squeeze_active);
            assert_eq!(row.block_byte, [0; stwo_keccak::sponge_v::MAX_RATE]);
            assert_eq!(row.new_rate, [0; stwo_keccak::sponge_v::MAX_RATE]);
            assert_eq!(row.squeeze_byte, [0; stwo_keccak::sponge_v::MAX_RATE]);
            let expected = canonical_unused_post.get_or_insert(row.post);
            assert_eq!(&row.post, expected, "unused row must prove Keccak-f(0)");
            assert!(run.perm_inputs[row_index][..200]
                .iter()
                .all(|value| value.to_array().iter().all(|lane| *lane == M31::zero())));
        }
    }
}

#[test]
fn fixed_capacity_job_proves_and_over_capacity_rejects() {
    const CAPACITY: usize = 1_024;
    let message = (0..303u32)
        .map(|i| i.wrapping_mul(17).wrapping_add(9) as u8)
        .collect::<Vec<_>>();
    let shape = Shape::with_message_capacity(message.len(), CAPACITY, 1, 10, 11).unwrap();
    let fixed_before = vec![0x31; 50];
    let fixed_after = vec![0x72; 200];
    let shapes = vec![
        Shape::new(fixed_before.len(), 1, 8, 9),
        shape,
        Shape::new(fixed_after.len(), 2, 12, 13),
    ];
    let messages = vec![fixed_before, message.clone(), fixed_after];
    let jobs = JobList::new(shapes.clone());
    let mut run = generate_jobs(&jobs, &messages);
    let relations = KeccakRelations::dummy();
    let (interaction_claim, interaction) = generate_interaction_trace(&relations, &run);
    let trace = TreeVec::new(vec![
        gen_schedule_preprocessed(&jobs),
        generate_base_trace(&run),
        interaction,
    ]);
    let trace = trace.as_ref().map_cols(|column| column.to_cpu().values);
    let trace = trace.as_cols_ref();
    let eval = SpongeEval {
        jobs: jobs.clone(),
        relations: relations.clone(),
    };
    assert_constraints_on_trace(
        &trace,
        eval.log_size(),
        |row| {
            eval.evaluate(row);
        },
        interaction_claim.claimed_sum,
    );

    let tamper_rejects = |run: &SpongeVRun| {
        let tampered_relations = relations.clone();
        let (tampered_claim, tampered_interaction) =
            generate_interaction_trace(&tampered_relations, run);
        let tampered_trace = TreeVec::new(vec![
            gen_schedule_preprocessed(&jobs),
            generate_base_trace(run),
            tampered_interaction,
        ]);
        let tampered_trace = tampered_trace
            .as_ref()
            .map_cols(|column| column.to_cpu().values);
        let tampered_trace = tampered_trace.as_cols_ref();
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let eval = SpongeEval {
                jobs: jobs.clone(),
                relations: tampered_relations,
            };
            assert_constraints_on_trace(
                &tampered_trace,
                eval.log_size(),
                |row| {
                    eval.evaluate(row);
                },
                tampered_claim.claimed_sum,
            );
        }))
        .is_err()
    };

    let capacity_start = shapes[0].n_perms();
    let first_unused = capacity_start + shape.actual_n_absorb();
    run.rows[first_unused].block_byte[0] = 1;
    assert!(
        tamper_rejects(&run),
        "a nonzero inactive capacity byte must violate the canonical-zero constraint"
    );
    run.rows[first_unused].block_byte[0] = 0;
    run.rows[capacity_start].block_byte[stwo_keccak::constants::N_BYTES_IN_RATE] = 1;
    assert!(
        tamper_rejects(&run),
        "a nonzero byte outside the SHAKE-256 rate must violate canonical zero"
    );
    run.rows[capacity_start].block_byte[stwo_keccak::constants::N_BYTES_IN_RATE] = 0;
    run.rows[capacity_start].absorb_active = false;
    assert!(
        tamper_rejects(&run),
        "the first allocated row must remain in the actual absorb prefix"
    );
    run.rows[capacity_start].absorb_active = true;
    run.rows[capacity_start].squeeze_active = true;
    assert!(
        tamper_rejects(&run),
        "the squeeze selector must identify only the final actual absorb row"
    );
    run.rows[capacity_start].squeeze_active = false;
    let pad_row = capacity_start + shape.actual_n_absorb() - 1;
    let pad_start = shape.message_len % stwo_keccak::constants::N_BYTES_IN_RATE;
    run.rows[pad_row].pad_gate[pad_start] = 0;
    assert!(
        tamper_rejects(&run),
        "the committed pad suffix must start at the public actual length"
    );

    let proof = prove_shapes_full(shapes, messages.clone(), None, None, pcs_config());
    assert_eq!(proof.outputs[1], shake256_ref(&message, 136));
    verify_jobs(&proof, &messages).expect("fixed-capacity service verify");

    assert!(matches!(
        Shape::with_message_capacity(CAPACITY + 1, CAPACITY, 1, 10, 11),
        Err(stwo_keccak::sponge::ShapeError::MessageExceedsCapacity { .. })
    ));
    assert!(matches!(
        Shape::with_message_capacity(1, CAPACITY, 2, 10, 11),
        Err(stwo_keccak::sponge::ShapeError::CapacityModeRequiresOneSqueeze { .. })
    ));
}

#[test]
fn shake128_job_proves_and_matches_sha3() {
    let msg = (0..400u32)
        .map(|i| (i.wrapping_mul(19) + 7) as u8)
        .collect::<Vec<u8>>();
    let shapes = vec![Shape::shake128(msg.len(), 2, 10, 11)];
    let p = prove_shapes_full(shapes, vec![msg.clone()], None, None, pcs_config());
    assert_eq!(p.outputs[0], shake128_ref(&msg, 2 * 168));
    verify_jobs(&p, &[msg]).expect("SHAKE-128 verify");
}

/// FIPS 202 SHAKE-256 cases: empty input, final-byte fuse, block-boundary
/// padding, spillover, an ML-DSA µ-sized input, and a long squeeze.
#[test]
fn shake256_kat_matrix_on_service_path() {
    for (name, msg, n_squeeze) in [
        ("empty", Vec::new(), 1usize),
        ("one-block-135", vec![0xA5u8; 135], 1),
        ("block-boundary-136", vec![0x5Au8; 136], 1),
        ("partial-block-137", vec![0x11u8; 137], 1),
        (
            "multi-block-mu-shape",
            (0..1536u32)
                .map(|i| (i.wrapping_mul(31) & 0xFF) as u8)
                .collect(),
            1,
        ),
        ("long-squeeze", b"squeeze me across many blocks".to_vec(), 5),
    ] {
        let p = prove_jobs(vec![msg.clone()], vec![n_squeeze], None);
        assert_eq!(
            p.outputs[0],
            shake256_ref(&msg, n_squeeze * 136),
            "{name}: service output != sha3"
        );
        verify_jobs(&p, &[msg]).unwrap_or_else(|e| panic!("{name}: verify failed: {e:?}"));
    }
}

#[test]
fn mixed_shake128_shake256_job_list_proves() {
    let messages = vec![
        vec![0x11; 135],
        vec![0x22; 167],
        (0..300u32).map(|i| (i * 31) as u8).collect(),
        vec![0x44; 168],
    ];
    let shapes = vec![
        Shape::new(messages[0].len(), 1, 10, 11),
        Shape::shake128(messages[1].len(), 2, 12, 13),
        Shape::new(messages[2].len(), 2, 14, 15),
        Shape::shake128(messages[3].len(), 1, 16, 17),
    ];
    assert_ne!(
        JobList::new([Shape::new(32, 1, 20, 21)]).shape_digest(),
        JobList::new([Shape::shake128(32, 1, 20, 21)]).shape_digest(),
        "job-list digest must bind the XOF mode and rate"
    );
    let p = prove_shapes_full(shapes, messages.clone(), None, None, pcs_config());
    assert_eq!(p.outputs[0], shake256_ref(&messages[0], 136));
    assert_eq!(p.outputs[1], shake128_ref(&messages[1], 2 * 168));
    assert_eq!(p.outputs[2], shake256_ref(&messages[2], 2 * 136));
    assert_eq!(p.outputs[3], shake128_ref(&messages[3], 168));
    verify_jobs(&p, &messages).expect("mixed SHAKE service verify");
}

#[test]
fn verifier_xof_mode_mismatch_rejects() {
    let msg = vec![0x5a; 32];
    let mut p = prove_jobs(vec![msg.clone()], vec![1], None);
    p.shapes[0] = Shape::shake128(32, 1, 10, 11);
    assert!(
        verify_jobs(&p, &[msg]).is_err(),
        "the public transcript and schedule root must bind the XOF mode"
    );
}

/// Multi-job list covering the pad edge shapes: `L mod 136 = 135` (0x9F fused
/// pad byte), `L mod 136 = 0` (an all-pad final block), a plain multi-block
/// message, and a multi-squeeze job. Also the job-boundary isolation gate: two
/// identical messages under different stream ids must both equal the sha3
/// reference. A chaining leak across the job boundary would change the second.
#[test]
fn multi_job_list_proves_with_isolated_boundaries() {
    let m135 = vec![0x11u8; 135];
    let m136 = vec![0x22u8; 136];
    let m300 = (0..300u32)
        .map(|i| (i as u8).wrapping_mul(31))
        .collect::<Vec<u8>>();
    let m_dup = vec![0xAAu8; 200];
    let messages = vec![m135, m136, m300, m_dup.clone(), m_dup.clone()];
    let n_squeezes = vec![1usize, 1, 1, 2, 2];
    let p = prove_jobs(messages.clone(), n_squeezes.clone(), None);
    for ((msg, out), sq) in messages.iter().zip(&p.outputs).zip(&n_squeezes) {
        assert_eq!(
            out,
            &shake256_ref(msg, 136 * sq),
            "job output != sha3 reference"
        );
    }
    // Boundary isolation: the duplicate jobs (different position in the row
    // concatenation, different neighbors) produce identical outputs.
    assert_eq!(
        p.outputs[3], p.outputs[4],
        "job outputs must not depend on neighbors"
    );
    verify_jobs(&p, &messages).expect("multi-job verify");
}

// =====================================================================
// Adversarial trace changes.
// =====================================================================

/// Change one new-rate spread byte consistently in the base
/// trace and the sponge's own logup data) → the xor3 tuple matches no dense
/// table row → LogUp unbalanced → reject.
#[test]
fn tampered_new_rate_rejects() {
    let messages = vec![vec![0x5Au8; 300]]; // 3 absorb perms → rows 1,2 have xor
    assert!(rejected(messages, vec![1], &|run| {
        run.rows[1].new_rate[5] ^= 1;
    }));
}

/// Change one post byte so the sponge output requirement no longer
/// matches the keccak component's OUT yield → LogUp unbalanced → reject.
#[test]
fn tampered_post_rejects() {
    let messages = vec![vec![0x33u8; 300]];
    assert!(rejected(messages, vec![1], &|run| {
        run.rows[0].post[17] ^= 1;
    }));
}

/// pad10*1: a non-canonical pad byte in the last block violates the
/// preprocessed-gated pad constraint (and the io/xor bindings) → reject.
#[test]
fn noncanonical_pad_byte_rejects() {
    let messages = vec![vec![0x77u8; 300]]; // f = 300 % 136 = 28: pad at 28..136
    assert!(rejected(messages, vec![1], &|run| {
        // Flip a zero pad position in the final absorb block (row 2, byte 100).
        run.rows[2].block_byte[100] ^= 0x40;
    }));
}

/// Make the HashIo producer yield a different byte from the
/// sponge absorbed → global LogUp unbalanced → reject (the hosted-mode swap
/// soundness, re-run against the rotated sponge).
#[test]
fn producer_message_byte_mismatch_rejects() {
    let msg = vec![0x44u8; 300];
    let p = prove_jobs(vec![msg.clone()], vec![1], None);
    let mut tampered = msg.clone();
    tampered[10] ^= 1;
    assert!(
        verify_jobs(&p, &[tampered]).is_err(),
        "tampered producer byte must break the HashIo balance"
    );
}

/// Squeeze binding: a consumer requiring a wrong squeeze byte must reject.
#[test]
fn wrong_squeeze_byte_rejects() {
    let msg = vec![0x88u8; 50];
    let mut p = prove_jobs(vec![msg.clone()], vec![1], None);
    p.outputs[0][7] ^= 1; // the verify-side closer now requires a wrong byte
    assert!(verify_jobs(&p, &[msg]).is_err());
}

/// A tampered service claimed sum must be rejected by the component-local
/// claimed-sum checks, not hidden by the global cancellation.
#[test]
fn service_claimed_sum_tamper_rejects() {
    let msg = vec![0x89u8; 50];
    let mut p = prove_jobs(vec![msg.clone()], vec![1], None);
    p.service_claims[0] += SecureField::one();
    assert!(verify_jobs(&p, &[msg]).is_err());
}

/// A tampered committed preprocessed root must reject before any claimed
/// service output is accepted.
#[test]
fn service_preprocessed_root_tamper_rejects() {
    let msg = vec![0x8au8; 50];
    let mut p = prove_jobs(vec![msg.clone()], vec![1], None);
    verify_jobs(&p, std::slice::from_ref(&msg)).expect("control verify");
    p.proof.0.commitments[0].0[0] ^= 1;
    assert!(verify_jobs(&p, &[msg]).is_err());
}

/// A non-spread value smuggled into a spread-output column cannot collide with
/// the genuine dense-table row used by the service's xor path.
#[test]
fn non_spread_value_in_spread_column_has_no_dense_row() {
    let rel = KeccakRelations::dummy();
    let table = build_dense_table();
    let key = spread_u32(0xAB) + spread_u32(0xCD) + spread_u32(0x37);
    let [tk, honest_out] = table[key as usize];
    assert_eq!(tk, key);
    let bad_out = honest_out | 0b11;
    assert!(
        bad_out > SPREAD_MAX || (bad_out & 0b10) != 0,
        "bad_out is non-spread"
    );

    let honest: QM31 = <_ as Relation<M31, QM31>>::combine(&rel.xor3, &[m1(key), m1(honest_out)]);
    let tampered: QM31 = <_ as Relation<M31, QM31>>::combine(&rel.xor3, &[m1(key), m1(bad_out)]);
    assert_ne!(honest, tampered);
    assert_ne!(honest_out, bad_out);
}

/// A wrong byte↔spread conversion at the HashIo boundary cannot collide with
/// the conv table row used by the service.
#[test]
fn wrong_conv_at_hashio_boundary_has_no_conv_row() {
    let rel = KeccakRelations::dummy();
    let conv = build_conv_table();
    let byte = 0x5Au32;
    let [tb, true_spread] = conv[byte as usize];
    assert_eq!(tb, byte);
    assert_eq!(true_spread, spread_u32(byte));
    let wrong_spread = spread_u32(byte ^ 0x01);
    assert_ne!(true_spread, wrong_spread);

    let honest: QM31 = <_ as Relation<M31, QM31>>::combine(&rel.conv, &[m1(byte), m1(true_spread)]);
    let tampered: QM31 =
        <_ as Relation<M31, QM31>>::combine(&rel.conv, &[m1(byte), m1(wrong_spread)]);
    assert_ne!(honest, tampered);
}

// =====================================================================
// Adversarial tests for the round LogUp-to-GKR path.
// =====================================================================

/// A complete service witness for a nonstandard intermediate Iota constant
/// must fail against the verifier-pinned FIPS 202 schedule. The sponge output,
/// all 25 carrier states, all 24 round rows, table multiplicities, and the
/// output closer use the same nonstandard permutation.
#[test]
fn coherent_alternate_iota_schedule_rejects() {
    let message = vec![0x5au8; 32];
    let shapes = shapes_for(std::slice::from_ref(&message), &[1]);
    let handle = SharedKeccakRelations::new();
    let mut service =
        KeccakServiceProver::new(shapes.clone(), vec![message.clone()], handle.clone());
    let official_output = service.job_outputs()[0].clone();
    let alternate_perm = install_alternate_iota_witness(service.run_mut());
    *service.perm_mut() = alternate_perm;
    let outputs = service.job_outputs().to_vec();
    assert_ne!(outputs[0], official_output);
    assert_ne!(outputs[0], shake256_ref(&message, outputs[0].len()));

    let mut closer = IoCloser::new(
        closer_entries(&shapes, std::slice::from_ref(&message), &outputs),
        handle,
    );
    let (proof, payloads) =
        air_core::prove_with_post_interaction(&mut [&mut service, &mut closer], pcs_config())
            .expect("coherent alternate-Iota witness should reach verification");
    let proved = ProvedJobs {
        shapes,
        messages: vec![message.clone()],
        outputs,
        service_claims: service.claimed_sums(),
        proof,
        payloads,
    };
    assert!(
        verify_jobs(&proved, &[message]).is_err(),
        "the fixed round schedule must reject a coherent alternate-Iota witness"
    );
}

/// Skip the prover-side coeff-poly-vs-oracle completeness self-check so the
/// adversarial provers below can produce their desynchronized proofs; the
/// verifier must then reject them independently.
fn skip_prover_oracle_self_check() {
    std::env::set_var("STWO_MLE_EVAL_SKIP_ORACLE_CONSISTENCY", "1");
}

/// A corrupted GKR payload blob must be rejected (decode failure or
/// Fiat-Shamir replay desynchronization both fail closed).
#[test]
fn corrupted_gkr_payload_rejects() {
    let msg = vec![0x21u8; 300];
    let p = prove_jobs(vec![msg.clone()], vec![1], None);
    assert!(!p.payloads[0].is_empty(), "service must emit a GKR blob");

    let mut corrupted = p.payloads.clone();
    let mid = corrupted[0].len() / 2;
    corrupted[0][mid] ^= 0xff;
    assert!(verify_jobs_with_payloads(&p, &p.messages, &corrupted).is_err());

    let mut truncated = p.payloads.clone();
    truncated[0].truncate(4);
    assert!(verify_jobs_with_payloads(&p, &p.messages, &truncated).is_err());
}

/// With no payloads, the service's round LogUp is unproven and verification
/// must fail closed.
#[test]
fn missing_gkr_payload_rejects() {
    let msg = vec![0x22u8; 300];
    let p = prove_jobs(vec![msg.clone()], vec![1], None);
    assert!(verify_jobs_with_payloads(&p, &p.messages, &[]).is_err());
}

/// A structurally valid GKR proof from another proof with the same job shape
/// must desynchronize the shared-channel replay.
#[test]
fn gkr_claim_swapped_between_proofs_rejects() {
    let msg_a = vec![0x31u8; 300];
    let msg_b = vec![0x32u8; 300];
    let a = prove_jobs(vec![msg_a], vec![1], None);
    let b = prove_jobs(vec![msg_b], vec![1], None);

    assert!(verify_jobs_with_payloads(&a, &a.messages, &b.payloads).is_err());
    assert!(verify_jobs_with_payloads(&b, &b.messages, &a.payloads).is_err());
}

/// ExpandA contributes 30 SHAKE-128 jobs to this service. A changed committed
/// carrier cell must break the GKR tie-back.
#[test]
fn tampered_expand_a_round_base_cell_rejects() {
    const EXPAND_A_POLYS: usize = 30;
    const EXPAND_A_SQUEEZE_BLOCKS: usize = 8;
    const STREAM_BASE: u32 = 1_000;

    skip_prover_oracle_self_check();
    let rho = [0x5au8; 32];
    let messages = (0..EXPAND_A_POLYS)
        .map(|poly| {
            let row = poly / 5;
            let col = poly % 5;
            [rho.as_slice(), &[col as u8, row as u8]].concat()
        })
        .collect::<Vec<_>>();
    let shapes = messages
        .iter()
        .enumerate()
        .map(|(poly, msg)| {
            Shape::shake128(
                msg.len(),
                EXPAND_A_SQUEEZE_BLOCKS,
                STREAM_BASE + 2 * poly as u32,
                STREAM_BASE + 2 * poly as u32 + 1,
            )
        })
        .collect();
    let p = prove_shapes_full(
        shapes,
        messages.clone(),
        None,
        Some(&|perm| {
            use stwo::prover::backend::Column;
            let col = &mut perm.shards[0].carrier_trace[20];
            let value = col.values.at(0);
            col.values.set(0, value + M31::one());
        }),
        pcs_config(),
    );
    assert!(verify_jobs(&p, &messages).is_err());
}

/// A cross-permutation carrier-state swap must break the row-wise tie-back.
#[test]
fn cross_permutation_carrier_state_swap_rejects() {
    let msg = vec![0x3fu8; 300]; // three Keccak permutations
    assert!(perm_rejected(vec![msg], vec![1], &|perm| {
        let first = N_ROUNDS;
        let second = stwo_keccak::carrier::ROWS_PER_PERMUTATION + N_ROUNDS;
        let trace = perm.shards[0]
            .carrier_data
            .as_mut()
            .expect("carrier GKR data")
            .trace_mut();
        let column = &mut trace[stwo_keccak::carrier::CARRIER_COLUMN_START];
        let first_value = carrier_coset_cell(column, first);
        let second_value = carrier_coset_cell(column, second);
        set_carrier_coset_cell(column, first, second_value);
        set_carrier_coset_cell(column, second, first_value);
    }));
}

/// Swap two committed positions and the matching GKR schedule data. The
/// schedule multiset stays unchanged, but the recurrence must reject.
#[test]
fn reordered_carrier_positions_reject() {
    let msg = vec![0x40u8; 300];
    assert!(perm_rejected(vec![msg], vec![1], &|perm| {
        set_carrier_coset_cell(&mut perm.shards[0].carrier_trace[4], 1, M31::from(2u32));
        set_carrier_coset_cell(&mut perm.shards[0].carrier_trace[4], 2, M31::from(1u32));
        let trace = perm.shards[0]
            .carrier_data
            .as_mut()
            .expect("carrier GKR data")
            .trace_mut();
        set_carrier_coset_cell(&mut trace[4], 1, M31::from(2u32));
        set_carrier_coset_cell(&mut trace[4], 2, M31::from(1u32));
    }));
}

/// Tamper the endpoint GKR data while the committed carrier stays honest.
#[test]
fn tampered_carrier_endpoint_source_rejects() {
    skip_prover_oracle_self_check();
    let msg = vec![0x41u8; 300];
    let p = prove_jobs_full(
        vec![msg.clone()],
        vec![1],
        None,
        Some(&|perm| {
            let trace = perm.shards[0]
                .carrier_data
                .as_mut()
                .expect("carrier GKR data")
                .trace_mut();
            let column = &mut trace[stwo_keccak::carrier::CARRIER_COLUMN_START];
            let value = carrier_coset_cell(column, 0);
            set_carrier_coset_cell(column, 0, value + M31::one());
        }),
        pcs_config(),
    );
    assert!(verify_jobs(&p, &[msg]).is_err());
}

/// The adversary shifts claimed-sum mass between the carrier and schedule slots.
/// Component-level direct LogUp claims must reject even though the global sum
/// is preserved.
#[test]
fn forged_carrier_claim_with_compensating_slot_rejects() {
    let msg = vec![0x42u8; 300];
    let mut p = prove_jobs(vec![msg.clone()], vec![1], None);
    // claims = [sponge, carrier, schedule, tables×9]. Keep the total unchanged.
    p.service_claims[1] += SecureField::one();
    p.service_claims[2] -= SecureField::one();
    assert!(verify_jobs(&p, &[msg]).is_err());
}

/// Tampered committed base cell with honest GKR fractions and claimed sums
/// must be rejected by the MLE-eval tie-back.
#[test]
fn tampered_carrier_base_cell_rejects() {
    skip_prover_oracle_self_check();
    let msg = vec![0x43u8; 300];
    let p = prove_jobs_full(
        vec![msg.clone()],
        vec![1],
        None,
        Some(&|perm| {
            use stwo::prover::backend::Column;
            let col = &mut perm.shards[0].carrier_trace[20];
            let value = col.values.at(0);
            col.values.set(0, value + M31::one());
        }),
        pcs_config(),
    );
    assert!(verify_jobs(&p, &[msg]).is_err());
}

/// The end marker closes the active chain after the last final row.
#[test]
fn missing_carrier_end_marker_rejects() {
    const END_COLUMN: usize = 5;

    let msg = vec![0x45u8; 300];
    assert!(perm_rejected(vec![msg], vec![1], &|perm| {
        let shard = &mut perm.shards[0];
        let end_row = shard.carrier_claim.n_perms * stwo_keccak::carrier::ROWS_PER_PERMUTATION;
        set_carrier_coset_cell(&mut shard.carrier_trace[END_COLUMN], end_row, M31::zero());
    }));
}

/// The first row of each block must remain the input endpoint row.
#[test]
fn missing_carrier_header_role_rejects() {
    const HEADER_COLUMN: usize = 0;

    let msg = vec![0x46u8; 300];
    assert!(perm_rejected(vec![msg], vec![1], &|perm| {
        set_carrier_coset_cell(
            &mut perm.shards[0].carrier_trace[HEADER_COLUMN],
            0,
            M31::zero(),
        );
        let trace = perm.shards[0]
            .carrier_data
            .as_mut()
            .expect("carrier GKR data")
            .trace_mut();
        set_carrier_coset_cell(&mut trace[HEADER_COLUMN], 0, M31::zero());
    }));
}

/// A row swap in the independent GKR source must fail the MLE tie-back.
#[test]
fn row_swapped_gkr_source_column_rejects() {
    skip_prover_oracle_self_check();
    let msg = vec![0x44u8; 300];
    let p = prove_jobs_full(
        vec![msg.clone()],
        vec![1],
        None,
        Some(&|perm| {
            let trace = perm.shards[0]
                .carrier_data
                .as_mut()
                .expect("carrier GKR data")
                .trace_mut();
            let column = &mut trace[20];
            let first = carrier_coset_cell(column, 0);
            let second = carrier_coset_cell(column, 1);
            set_carrier_coset_cell(column, 0, second);
            set_carrier_coset_cell(column, 1, first);
        }),
        pcs_config(),
    );
    assert!(verify_jobs(&p, &[msg]).is_err());
}

/// A logical row rotation preserves every GKR fraction multiset. The MLE
/// tie-back must still reject because the committed carrier does not rotate.
#[test]
fn cyclically_rotated_gkr_source_rejects() {
    skip_prover_oracle_self_check();
    let msg = vec![0x49u8; 300];
    let p = prove_jobs_full(
        vec![msg.clone()],
        vec![1],
        None,
        Some(&|perm| {
            let trace = perm.shards[0]
                .carrier_data
                .as_mut()
                .expect("carrier GKR data")
                .trace_mut();
            assert_eq!(trace.len(), stwo_keccak::carrier::N_COLUMNS);
            for column in trace {
                rotate_carrier_coset_column(column);
            }
        }),
        pcs_config(),
    );
    assert!(verify_jobs(&p, &[msg]).is_err());
}

/// The GKR tie-back works with `log_blowup = 4`.
#[test]
fn gkr_offload_proves_with_blowup_4_subdomain_mode() {
    let msg = vec![0x51u8; 300];
    let config = PcsConfig {
        fri_config: FriConfig::new(1, 4, 3, 2),
        ..PcsConfig::default()
    };
    let p = prove_jobs_full(vec![msg.clone()], vec![1], None, None, config);
    verify_jobs(&p, &[msg]).expect("blowup-4 SubDomain verify");
}
