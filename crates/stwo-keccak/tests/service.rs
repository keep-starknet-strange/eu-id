//! S1 gate tests for the rotated job-list sponge + `KeccakService` module:
//! single job, multi job (incl. pad edge shapes and multi-squeeze),
//! job-boundary isolation, and the design doc's adversarial rows
//! (tampered new_rate / post / pad byte / producer byte).
//!
//! Run single-threaded: `RAYON_NUM_THREADS=1 cargo test -p stwo-keccak
//! --release --test service -- --test-threads=1`.

use num_traits::{One, Zero};
use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::Shake256;

use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::core::fri::FriConfig;
use stwo::core::pcs::PcsConfig;
use stwo::prover::backend::simd::m31::{LOG_N_LANES, N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    TraceLocationAllocator,
};

use air_core::{Air, AirProver, PreprocessedColumnFingerprint, TreeLayout};

use stwo_keccak::relations::{HashIoRelation, SharedKeccakRelations};
use stwo_keccak::service::{KeccakServiceProver, KeccakServiceVerifier};
use stwo_keccak::sponge::Shape;
use stwo_keccak::sponge_v::SpongeVRun;
use stwo_keccak::utils::{col_eval, ColEval};

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
}

/// Batch-4 logup constraints have log-degree excess 2, so proving needs
/// `log_blowup >= 2` (production uses 3).
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
    let shapes = shapes_for(&messages, &n_squeezes);
    let handle = SharedKeccakRelations::new();
    let mut service = KeccakServiceProver::new(shapes.clone(), messages.clone(), handle.clone());
    let outputs = service.job_outputs().to_vec();
    if let Some(t) = tamper {
        t(service.run_mut());
    }
    let mut closer = IoCloser::new(closer_entries(&shapes, &messages, &outputs), handle);
    let proof = air_core::prove(&mut [&mut service, &mut closer], pcs_config()).expect("prove");
    ProvedJobs {
        shapes,
        messages,
        outputs,
        service_claims: service.claimed_sums(),
        proof,
    }
}

fn verify_jobs(p: &ProvedJobs, closer_msgs: &[Vec<u8>]) -> Result<(), air_core::VerifyError> {
    let handle = SharedKeccakRelations::new();
    let mut service =
        KeccakServiceVerifier::new(p.shapes.clone(), p.service_claims.clone(), handle.clone());
    let mut closer = IoCloser::new(closer_entries(&p.shapes, closer_msgs, &p.outputs), handle);
    air_core::verify_with_expected_preprocessed_root(
        &mut [&mut service, &mut closer],
        &p.proof,
        None,
    )
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

/// Multi-job list covering the pad edge shapes: `L mod 136 = 135` (0x9F fused
/// pad byte), `L mod 136 = 0` (an all-pad final block), a plain multi-block
/// message, and a multi-squeeze job. Also the job-boundary isolation gate: two
/// identical messages under different stream ids must both equal the sha3
/// reference — any chaining leak across the job seam would corrupt the second.
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
// Adversarial rows (design doc S1 gate).
// =====================================================================

/// I-2 xor path: tamper one new_rate spread byte (consistently in the base
/// trace and the sponge's own logup data) → the xor3 tuple matches no dense
/// table row → LogUp unbalanced → reject.
#[test]
fn tampered_new_rate_rejects() {
    let messages = vec![vec![0x5Au8; 300]]; // 3 absorb perms → rows 1,2 have xor
    assert!(rejected(messages, vec![1], &|run| {
        run.rows[1].new_rate[5] ^= 1;
    }));
}

/// I-2 state chain: tamper one post byte → the sponge's OUT require no longer
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

/// I-4 message binding: the HashIo producer yields a DIFFERENT byte than the
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
