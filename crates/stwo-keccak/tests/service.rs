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
use stwo::core::fields::m31::{M31, P as M31_MODULUS};
use stwo::core::fields::qm31::{SecureField, QM31, SECURE_EXTENSION_DEGREE};
use stwo::core::fri::FriConfig;
use stwo::core::pcs::PcsConfig;
use stwo::core::pcs::TreeVec;
use stwo::prover::backend::simd::m31::{LOG_N_LANES, N_LANES};
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

use stwo_keccak::constants::{N_BYTES_IN_RATE, N_BYTES_IN_STATE, N_ROUNDS};
use stwo_keccak::layered_gkr::{
    is_canonical_payload, payload_byte_count, payload_field_count, LayeredKeccakProver,
    N_TIEBACK_COLUMNS, PRODUCT_PAYLOAD_BYTES, PRODUCT_P_LOG,
};
use stwo_keccak::relations::{HashIoRelation, KeccakRelations, SharedKeccakRelations};
use stwo_keccak::service::{service_claimed_sums_len, KeccakServiceProver, KeccakServiceVerifier};
use stwo_keccak::sponge::Shape;
use stwo_keccak::sponge_v::{
    gen_schedule_preprocessed, generate_base_trace, generate_interaction_trace, generate_jobs,
    schedule_ids, Eval as SpongeEval, JobList, SpongeVRun, N_ABSORB_COLS,
};
use stwo_keccak::tables::{build_conv_table, build_xor3_table};
use stwo_keccak::utils::{col_eval, spread_u32, ColEval, SPREAD_MAX};

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
    service_components: usize,
    proof: stwo::core::proof::StarkProof<air_core::Hasher>,
    /// Per-module opaque post-interaction payloads.
    payloads: Vec<Vec<u8>>,
}

/// Batch-four sponge LogUp constraints have log-degree excess two.
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

/// [`prove_jobs`] with a layered-witness tamper hook and an explicit PCS config.
fn prove_jobs_full(
    messages: Vec<Vec<u8>>,
    n_squeezes: Vec<usize>,
    tamper: Option<&dyn Fn(&mut SpongeVRun)>,
    layered_tamper: Option<&dyn Fn(&mut LayeredKeccakProver)>,
    config: PcsConfig,
) -> ProvedJobs {
    let shapes = shapes_for(&messages, &n_squeezes);
    prove_shapes_full(shapes, messages, tamper, layered_tamper, config)
}

fn prove_shapes_full(
    shapes: Vec<Shape>,
    messages: Vec<Vec<u8>>,
    tamper: Option<&dyn Fn(&mut SpongeVRun)>,
    layered_tamper: Option<&dyn Fn(&mut LayeredKeccakProver)>,
    config: PcsConfig,
) -> ProvedJobs {
    let handle = SharedKeccakRelations::new();
    let mut service = KeccakServiceProver::new(shapes.clone(), messages.clone(), handle.clone());
    let outputs = service.job_outputs().to_vec();
    if let Some(t) = tamper {
        t(service.run_mut());
    }
    if let Some(t) = layered_tamper {
        t(service.layered_mut());
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
        service_components: service.components().len(),
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

/// A layered-witness tamper is rejected by proving or verification.
fn layered_rejected(
    messages: Vec<Vec<u8>>,
    n_squeezes: Vec<usize>,
    tamper: &dyn Fn(&mut LayeredKeccakProver),
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

static SOURCE_MLE_ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// Build an invalid source-MLE proof without the prover-side oracle check.
/// The verifier must still reject the proof.
fn prove_with_desynchronized_source(
    messages: Vec<Vec<u8>>,
    n_squeezes: Vec<usize>,
    tamper: &dyn Fn(&mut LayeredKeccakProver),
) -> ProvedJobs {
    const SKIP_ORACLE_CHECK: &str = "STWO_MLE_EVAL_SKIP_ORACLE_CONSISTENCY";

    let _lock = SOURCE_MLE_ENV_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let previous = std::env::var_os(SKIP_ORACLE_CHECK);
    std::env::set_var(SKIP_ORACLE_CHECK, "1");
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_jobs_full(messages, n_squeezes, None, Some(tamper), pcs_config())
    }));
    if let Some(previous) = previous {
        std::env::set_var(SKIP_ORACLE_CHECK, previous);
    } else {
        std::env::remove_var(SKIP_ORACLE_CHECK);
    }
    match result {
        Ok(proof) => proof,
        Err(payload) => std::panic::resume_unwind(payload),
    }
}

fn physical_permutation_row(p_log: u32, logical_row: usize) -> usize {
    stwo_keccak::utils::circle_row_to_coset(p_log)
        .into_iter()
        .position(|coset| coset == logical_row)
        .expect("logical permutation row exists")
}

fn layered_payload_sections(p_log: u32) -> Vec<(String, usize)> {
    const FIXED_SECTIONS: usize = 3;
    const SECTIONS_PER_ROUND: usize = 6;
    const STATE_LOCAL_LOG: usize = 11;
    const PARITY_LOCAL_LOG: usize = 9;
    const NIBBLE_LOCAL_LOG: usize = 9;
    const CHI_COEFFICIENTS: usize = 6;
    const THETA_COEFFICIENTS: usize = 5;
    const PARITY_COEFFICIENTS: usize = 7;
    const EXTRACTION_COEFFICIENTS: usize = 18;
    const CHI_TERMINALS: usize = 3;
    const THETA_TERMINALS: usize = 3;
    const PARITY_TERMINALS: usize = 5;

    let p_log = p_log as usize;
    let mut cursor = 0;
    let mut sections = vec![("output claim".to_owned(), cursor)];
    cursor += 1;
    for round in (0..N_ROUNDS).rev() {
        for (name, sumcheck_fields, terminal_fields) in [
            (
                "chi",
                (p_log + STATE_LOCAL_LOG) * CHI_COEFFICIENTS,
                CHI_TERMINALS,
            ),
            (
                "theta",
                (p_log + STATE_LOCAL_LOG) * THETA_COEFFICIENTS,
                THETA_TERMINALS,
            ),
            (
                "parity",
                (p_log + PARITY_LOCAL_LOG) * PARITY_COEFFICIENTS,
                PARITY_TERMINALS,
            ),
        ] {
            sections.push((format!("round {round} {name} sumcheck"), cursor));
            cursor += sumcheck_fields;
            sections.push((format!("round {round} {name} terminals"), cursor));
            cursor += terminal_fields;
        }
    }
    sections.push(("extraction sumcheck".to_owned(), cursor));
    cursor += (p_log + NIBBLE_LOCAL_LOG) * EXTRACTION_COEFFICIENTS;
    sections.push(("extraction terminal".to_owned(), cursor));
    cursor += 1;
    assert_eq!(cursor, payload_field_count(p_log as u32));
    assert_eq!(
        sections.len(),
        FIXED_SECTIONS + N_ROUNDS * SECTIONS_PER_ROUND
    );
    sections
}

// =====================================================================
// Positive gates.
// =====================================================================

#[test]
fn single_job_proves_and_matches_sha3() {
    let msg = (0..300u32).map(|i| (i * 7 + 3) as u8).collect::<Vec<u8>>();
    let p = prove_jobs(vec![msg.clone()], vec![1], None);
    assert_eq!(p.service_claims.len(), 3);
    assert_eq!(p.service_components, 5);
    assert_eq!(p.payloads[0].len(), payload_byte_count(LOG_N_LANES));
    assert_eq!(
        p.outputs[0],
        shake256_ref(&msg, 136),
        "service output != SHAKE-256"
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
fn canonical_n261_layered_geometry_is_pinned() {
    const N_PERMUTATIONS: usize = 261;
    const CAPACITY_PERMUTATIONS: usize = 256;
    const SHAKE256_RATE: usize = 136;
    const EXPECTED_SCHEDULE_COLUMNS: usize = 16;

    let capacity_bytes = (CAPACITY_PERMUTATIONS - 1) * SHAKE256_RATE;
    let mut shapes = vec![Shape::with_message_capacity(0, capacity_bytes, 1, 1, 2)
        .expect("valid fixed-capacity shape")];
    for remainder in 16..21 {
        let stream = 10 + 2 * remainder as u32;
        shapes.push(Shape::new(remainder, 1, stream, stream + 1));
    }

    let jobs = JobList::new(shapes.clone());
    assert_eq!(jobs.n_perms_total(), N_PERMUTATIONS);
    assert_eq!(jobs.log_size(), PRODUCT_P_LOG);
    assert_eq!(jobs.n_schedule_cols(), EXPECTED_SCHEDULE_COLUMNS);
    assert_eq!(jobs.n_base_cols(), 1_314);
    assert_eq!(stwo_keccak::sponge_v::n_interaction_cols(&jobs), 752);
    assert_eq!(service_claimed_sums_len(), 3);
    assert_eq!(N_TIEBACK_COLUMNS, 16);
    assert_eq!(payload_byte_count(jobs.log_size()), PRODUCT_PAYLOAD_BYTES);
    assert_eq!(PRODUCT_PAYLOAD_BYTES, 142_304);

    let layout = stwo_keccak::service::debug_layout(shapes.clone());
    assert_eq!(
        layout.preprocessed,
        [vec![9; 16], vec![16; 2], vec![8; 2]].concat()
    );
    assert_eq!(layout.trace, [vec![9; 1_314], vec![16], vec![8]].concat());
    assert_eq!(
        layout.interaction,
        [vec![9; 752], vec![16; 4], vec![8; 4]].concat()
    );
    let committed_cells = layout
        .preprocessed
        .iter()
        .chain(&layout.trace)
        .chain(&layout.interaction)
        .map(|&log_size| 1usize << log_size)
        .sum::<usize>()
        + N_TIEBACK_COLUMNS * (1usize << PRODUCT_P_LOG);
    assert_eq!(committed_cells, 1_534_720);

    let verifier = KeccakServiceVerifier::new(
        shapes,
        vec![SecureField::zero(); service_claimed_sums_len()],
        SharedKeccakRelations::new(),
    );
    assert_eq!(verifier.post_interaction_log_sizes(), vec![9; 16]);
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
        for row in run.rows.iter().skip(actual_rows) {
            assert!(!row.absorb_active);
            assert!(!row.squeeze_active);
            assert_eq!(row.block_byte, [0; N_ABSORB_COLS]);
            assert_eq!(row.new_rate, [0; N_ABSORB_COLS]);
            assert_eq!(row.squeeze_byte, [0; stwo_keccak::sponge_v::MAX_RATE]);
            assert_eq!(row.input, [0; N_BYTES_IN_STATE]);
            let expected = canonical_unused_post.get_or_insert(row.post);
            assert_eq!(&row.post, expected, "unused row must prove Keccak-f(0)");
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
    run.rows[capacity_start].squeeze_byte[N_BYTES_IN_RATE] = 1;
    assert!(
        tamper_rejects(&run),
        "a nonzero squeeze byte outside the SHAKE-256 rate must violate canonical zero"
    );
    run.rows[capacity_start].squeeze_byte[N_BYTES_IN_RATE] = 0;
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
    let msg = (0..N_BYTES_IN_RATE as u32)
        .map(|i| (i.wrapping_mul(19) + 7) as u8)
        .collect::<Vec<u8>>();
    let shapes = vec![Shape::shake128(msg.len(), 2, 10, 11)];
    let p = prove_shapes_full(shapes, vec![msg.clone()], None, None, pcs_config());
    assert_eq!(p.outputs[0], shake128_ref(&msg, 2 * 168));
    verify_jobs(&p, &[msg]).expect("SHAKE-128 verify");
}

#[test]
fn shake128_rejects_a_137_byte_message() {
    assert!(std::panic::catch_unwind(|| Shape::shake128(N_BYTES_IN_RATE + 1, 1, 10, 11)).is_err());
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
        vec![0x22; 34],
        (0..300u32).map(|i| (i * 31) as u8).collect(),
        vec![0x44; N_BYTES_IN_RATE],
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

/// A committed input change must not alter the independent layered source.
#[test]
fn committed_input_source_mutation_rejects() {
    let messages = vec![vec![0x32u8; 300]];
    assert!(rejected(messages, vec![1], &|run| {
        run.rows[0].input[17] ^= 1;
    }));
}

/// A committed output change must not alter the independent layered source.
#[test]
fn committed_output_source_mutation_rejects() {
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
/// sponge absorbed → global LogUp unbalanced → reject.
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

/// A non-spread value cannot collide with the genuine XOR-table row.
#[test]
fn non_spread_value_has_no_xor_table_row() {
    let rel = KeccakRelations::dummy();
    let table = build_xor3_table();
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
// Layered proof and source tie-back tests.
// =====================================================================

#[test]
fn layered_payload_codec_rejects_malformed_wire() {
    let msg = vec![0x21u8; 300];
    let p = prove_jobs(vec![msg.clone()], vec![1], None);
    let p_log = JobList::new(p.shapes.clone()).log_size();
    let honest = &p.payloads[0];
    assert_eq!(honest.len(), payload_byte_count(p_log));
    assert!(is_canonical_payload(honest, p_log));

    const FIELD_BYTES: usize = SECURE_EXTENSION_DEGREE * size_of::<u32>();
    for (section, field) in layered_payload_sections(p_log) {
        let mut payloads = p.payloads.clone();
        let byte = field * FIELD_BYTES;
        let raw = u32::from_le_bytes(
            payloads[0][byte..byte + size_of::<u32>()]
                .try_into()
                .expect("one M31 limb"),
        );
        let changed = if raw == 0 { 1 } else { raw - 1 };
        payloads[0][byte..byte + size_of::<u32>()].copy_from_slice(&changed.to_le_bytes());
        assert!(
            is_canonical_payload(&payloads[0], p_log),
            "{section}: mutation must remain canonical"
        );
        assert!(
            verify_jobs_with_payloads(&p, &p.messages, &payloads).is_err(),
            "{section}: canonical mutation must reject"
        );
    }

    let mut truncated = p.payloads.clone();
    truncated[0].pop();
    assert!(!is_canonical_payload(&truncated[0], p_log));
    assert!(verify_jobs_with_payloads(&p, &p.messages, &truncated).is_err());

    let mut trailing = p.payloads.clone();
    trailing[0].push(0);
    assert!(!is_canonical_payload(&trailing[0], p_log));
    assert!(verify_jobs_with_payloads(&p, &p.messages, &trailing).is_err());

    let mut noncanonical = p.payloads.clone();
    noncanonical[0][..4].copy_from_slice(&M31_MODULUS.to_le_bytes());
    assert!(!is_canonical_payload(&noncanonical[0], p_log));
    assert!(verify_jobs_with_payloads(&p, &p.messages, &noncanonical).is_err());
}

#[test]
fn missing_layered_payload_rejects() {
    let msg = vec![0x22u8; 300];
    let p = prove_jobs(vec![msg], vec![1], None);
    let mut payloads = p.payloads.clone();
    payloads[0].clear();
    assert!(verify_jobs_with_payloads(&p, &p.messages, &payloads).is_err());
}

#[test]
fn same_shape_layered_payload_swap_rejects() {
    let a = prove_jobs(vec![vec![0x31u8; 300]], vec![1], None);
    let b = prove_jobs(vec![vec![0x32u8; 300]], vec![1], None);
    assert_eq!(a.shapes, b.shapes);
    assert_eq!(a.payloads[0].len(), b.payloads[0].len());
    assert!(verify_jobs_with_payloads(&a, &a.messages, &b.payloads).is_err());
    assert!(verify_jobs_with_payloads(&b, &b.messages, &a.payloads).is_err());
}

#[test]
fn output_source_mle_mutation_reaches_verifier_and_rejects() {
    let msg = vec![0x41u8; 300];
    let p = prove_with_desynchronized_source(vec![msg.clone()], vec![1], &|layered| {
        layered.perturb_source_mle_value(true, 0)
    });
    assert!(
        verify_jobs(&p, &[msg]).is_err(),
        "the verifier must reject the desynchronized output source MLE"
    );
}

#[test]
fn input_source_mle_mutation_reaches_verifier_and_rejects() {
    let msg = vec![0x43u8; 300];
    let p = prove_with_desynchronized_source(vec![msg.clone()], vec![1], &|layered| {
        layered.perturb_source_mle_value(false, 0)
    });
    assert!(
        verify_jobs(&p, &[msg]).is_err(),
        "the verifier must reject the desynchronized input source MLE"
    );
}

#[test]
fn claim_neutral_cross_permutation_source_swaps_reach_verifier_and_reject() {
    let msg = (0..300u32)
        .map(|index| index.wrapping_mul(29).wrapping_add(7) as u8)
        .collect::<Vec<_>>();
    let p_log = JobList::new(shapes_for(std::slice::from_ref(&msg), &[1])).log_size();
    let first = physical_permutation_row(p_log, 0);
    let second = physical_permutation_row(p_log, 1);

    for output in [false, true] {
        let p = prove_with_desynchronized_source(vec![msg.clone()], vec![1], &|layered| {
            layered.swap_source_mle_rows(output, first, second)
        });
        assert!(
            verify_jobs(&p, std::slice::from_ref(&msg)).is_err(),
            "the verifier must reject the claim-neutral {} source-row swap",
            if output { "output" } else { "input" }
        );
    }
}

#[test]
fn balanced_permutation_row_swap_reaches_verifier_and_rejects() {
    let msg = (0..300u32)
        .map(|index| index.wrapping_mul(31).wrapping_add(11) as u8)
        .collect::<Vec<_>>();
    let p_log = JobList::new(shapes_for(std::slice::from_ref(&msg), &[1])).log_size();
    let first = physical_permutation_row(p_log, 0);
    let second = physical_permutation_row(p_log, 1);
    let p = prove_with_desynchronized_source(vec![msg.clone()], vec![1], &|layered| {
        layered.swap_permutation_rows(first, second)
    });
    assert!(
        verify_jobs(&p, &[msg]).is_err(),
        "the source tie-backs must reject a coherent whole-permutation swap"
    );
}

#[test]
fn internal_layered_state_mutation_rejects() {
    let msg = vec![0x44u8; 300];
    let storage_row = stwo_keccak::utils::circle_row_to_coset(LOG_N_LANES)
        .into_iter()
        .position(|coset| coset == 0)
        .expect("first permutation storage row");
    assert!(layered_rejected(vec![msg], vec![1], &|layered| {
        layered.flip_state_bit(12, storage_row, 7, 31);
    }));
}

#[test]
fn compensating_service_claim_mutation_rejects() {
    let msg = vec![0x42u8; 300];
    let mut p = prove_jobs(vec![msg.clone()], vec![1], None);
    assert_eq!(p.service_claims.len(), 3);
    p.service_claims[1] += SecureField::one();
    p.service_claims[2] -= SecureField::one();
    assert!(verify_jobs(&p, &[msg]).is_err());
}

/// Both source tie-backs work with `log_blowup = 4`.
#[test]
fn layered_proof_works_with_blowup_4_subdomain_mode() {
    let msg = vec![0x51u8; 300];
    let config = PcsConfig {
        fri_config: FriConfig::new(1, 4, 3, 2),
        ..PcsConfig::default()
    };
    let p = prove_jobs_full(vec![msg.clone()], vec![1], None, None, config);
    verify_jobs(&p, &[msg]).expect("blowup-4 SubDomain verify");
}
