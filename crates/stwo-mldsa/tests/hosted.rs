//! M7 Phase-A acceptance: the HOSTED `stwo-mldsa` statement composed with a
//! throwaway host module that yields the ML-DSA message bytes under a SHARED
//! `air_core::relations::FieldBytesRelation` (the mdoc issuer-SHA swap point).
//!
//! Positive: a two-module proof `[field_producer, hosted_mldsa]` proves+verifies,
//! with NO standalone `msglink` component. Negative: tampering ONE message byte
//! on the producer side (so the yielded bytes differ from what the µ-absorb
//! bridge requires) makes the global LogUp unbalanced → verify rejects. This
//! proves the MsgLink→shared-FieldBytes swap is sound and actually binds.
//!
//! Run single-threaded (proofs must not run concurrently):
//! `RUST_MIN_STACK=536870912 cargo test -p stwo-mldsa --release --test hosted \
//!   -- --test-threads=1`.

use ml_dsa::signature::{Keypair, Signer, Verifier};
use ml_dsa::{EncodedSignature, EncodedVerifyingKey, MlDsa65, SigningKey};

use stwo::core::air::Component;
use stwo::core::channel::Blake2sChannel;
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::PcsConfig;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    TraceLocationAllocator,
};

use num_traits::Zero;

use air_core::relations::{FieldBytesRelation, SharedFieldRelation};
use air_core::{Air, AirProver, PreprocessedColumnFingerprint, TreeLayout};

use stwo::prover::backend::simd::m31::{LOG_N_LANES, N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;

use stwo_keccak::relations::SharedKeccakRelations;
use stwo_keccak::service::{KeccakServiceProver, KeccakServiceVerifier};
use stwo_mldsa::air_util::{col_eval, m31, ColEval};
use stwo_mldsa::reference::encoding::{pk_decode, sig_decode};
use stwo_mldsa::reference::sponge::shake256;
use stwo_mldsa::statement::{
    keccak_job_shapes, MlDsaProof, MlDsaProver, MlDsaVerifier, HOSTED_MSG_FIELD_ID,
    STREAM_BASE_STRIDE,
};
use stwo_mldsa::witness::generate_witness;
use stwo_mldsa::MlDsaVerifyInput;

// =====================================================================
// Throwaway host module: a FieldExposure-style producer yielding the whole
// message under the SHARED FieldBytesRelation at HOSTED_MSG_FIELD_ID.
// =====================================================================

/// Single packed row, lane-0 enabler; one relation entry per message byte.
/// Mirrors `stwo_mldsa::msglink::MsgLinkEval` but yields on the shared
/// `FieldBytesRelation` (the host's SHA field-exposure stand-in).
#[derive(Clone)]
struct FieldProducerEval {
    bytes: Vec<u8>,
    field: FieldBytesRelation,
}

impl FrameworkEval for FieldProducerEval {
    fn log_size(&self) -> u32 {
        LOG_N_LANES
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        LOG_N_LANES + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let enabler = eval.next_trace_mask();
        let one = E::F::from(m31(1));
        eval.add_constraint(enabler.clone() * (one - enabler.clone()));
        // (−enabler): match the stwo-sha256 field-provider sign convention
        // (provider −, consuming bridge +).
        let en = -E::EF::from(enabler);
        for (i, &b) in self.bytes.iter().enumerate() {
            eval.add_to_relation(RelationEntry::new(
                &self.field,
                en.clone(),
                &[
                    E::F::from(m31(HOSTED_MSG_FIELD_ID)),
                    E::F::from(m31(i as u32)),
                    E::F::from(m31(b as u32)),
                ],
            ));
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

/// The host module: draws the shared field relation, sets the handle, and yields
/// the message bytes. Composed FIRST so its `draw_relations` populates the handle
/// before the hosted mldsa module reads it.
struct FieldProducer {
    bytes: Vec<u8>,
    handle: SharedFieldRelation,
    field: Option<FieldBytesRelation>,
    claimed_sum: SecureField,
    component: Option<FrameworkComponent<FieldProducerEval>>,
}

impl FieldProducer {
    fn new(bytes: Vec<u8>, handle: SharedFieldRelation) -> Self {
        Self { bytes, handle, field: None, claimed_sum: SecureField::zero(), component: None }
    }
    fn field(&self) -> FieldBytesRelation {
        self.field.clone().expect("relation drawn")
    }
}

fn producer_base_trace() -> Vec<ColEval> {
    let rows = 1usize << LOG_N_LANES;
    let mut enabler = vec![m31(0); rows];
    enabler[0] = m31(1);
    vec![col_eval(LOG_N_LANES, enabler)]
}

/// One `−enabler / combine(tuple)` fraction per byte, paired two-per-column
/// (msglink pattern, sign flipped to the stwo-sha256 provider convention).
fn producer_interaction(bytes: &[u8], field: &FieldBytesRelation) -> (Vec<ColEval>, SecureField) {
    use stwo::prover::backend::simd::m31::PackedM31;
    let mut gen = LogupTraceGenerator::new(LOG_N_LANES);
    let mut en_lanes = [m31(0); N_LANES];
    en_lanes[0] = m31(1);
    let en = -PackedQM31::from(PackedM31::from_array(en_lanes));
    let fracs: Vec<(PackedQM31, PackedQM31)> = bytes
        .iter()
        .enumerate()
        .map(|(i, &b)| {
            let tuple = [
                PackedM31::from(m31(HOSTED_MSG_FIELD_ID)),
                PackedM31::from(m31(i as u32)),
                PackedM31::from(m31(b as u32)),
            ];
            (en, field.combine(&tuple))
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

fn producer_interaction_cols(msg_len: usize) -> usize {
    use stwo::core::fields::qm31::SECURE_EXTENSION_DEGREE;
    msg_len.div_ceil(2) * SECURE_EXTENSION_DEGREE
}

impl Air for FieldProducer {
    fn mix_public(&self, _channel: &mut Blake2sChannel) {}
    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let field = FieldBytesRelation::draw(channel);
        self.handle.set(field.clone());
        // Compute the claimed sum now (both prove and verify run draw_relations
        // identically), so the verifier reconstructs the same value with no
        // witness beyond the public producer bytes.
        let (_, sum) = producer_interaction(&self.bytes, &field);
        self.claimed_sum = sum;
        self.field = Some(field);
    }
    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: Vec::new(),
            trace: vec![LOG_N_LANES],
            interaction: vec![LOG_N_LANES; producer_interaction_cols(self.bytes.len())],
        }
    }
    fn claimed_sums(&self) -> Vec<SecureField> {
        vec![self.claimed_sum]
    }
    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        Vec::new()
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.component = Some(FrameworkComponent::new(
            allocator,
            FieldProducerEval { bytes: self.bytes.clone(), field: self.field() },
            self.claimed_sum,
        ));
    }
    fn components(&self) -> Vec<&dyn Component> {
        vec![self.component.as_ref().expect("built")]
    }
}

impl AirProver for FieldProducer {
    fn max_log_size(&self) -> u32 {
        LOG_N_LANES
    }
    fn write_preprocessed(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}
    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        Vec::new()
    }
    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(producer_base_trace());
    }
    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let (trace, sum) = producer_interaction(&self.bytes, &self.field());
        debug_assert_eq!(sum, self.claimed_sum, "producer sum drifted from draw_relations");
        tb.extend_evals(trace);
    }
    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![self.component.as_ref().expect("built")]
    }
}

// =====================================================================
// Fixture (model: composed.rs).
// =====================================================================

fn oracle_input(seed: u64, msg: &[u8]) -> MlDsaVerifyInput {
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};
    let mut rng = StdRng::seed_from_u64(seed);
    let mut sk_seed = [0u8; 32];
    rng.fill(&mut sk_seed);
    let sk = SigningKey::<MlDsa65>::from_seed(&sk_seed.into());
    let vk = sk.verifying_key();
    let sig = sk.sign(msg);
    assert!(vk.verify(msg, &sig).is_ok(), "oracle self-check");
    let vk_bytes: EncodedVerifyingKey<MlDsa65> = vk.encode();
    let sig_bytes: EncodedSignature<MlDsa65> = sig.encode();
    let pk = pk_decode(vk_bytes.as_slice()).expect("pk_decode");
    let sp = sig_decode(sig_bytes.as_slice()).expect("sig_decode");
    let (tr_vec, _) = shake256(&[vk_bytes.as_slice()], 64);
    let mut tr = [0u8; 64];
    tr.copy_from_slice(&tr_vec);
    MlDsaVerifyInput::from_decoded(&pk, &sp, tr, msg.to_vec())
}

/// Prove the hosted statement: `[keccak_service, field_producer(producer_bytes),
/// hosted_mldsa]`. `producer_bytes` is what the HOST yields (honest = the
/// message; tamper it to simulate a mismatched issuer preimage).
fn prove_hosted(seed: u64, msg: &[u8], producer_bytes: Vec<u8>) -> MlDsaProof {
    let input = oracle_input(seed, msg);
    let witness = generate_witness(&input).expect("witness");

    let handle = SharedFieldRelation::new();
    let keccak_handle = SharedKeccakRelations::new();
    let mut producer = FieldProducer::new(producer_bytes, handle.clone());
    let mut mldsa = MlDsaProver::hosted(witness, input.clone(), handle, keccak_handle.clone());
    let (job_shapes, job_streams) = mldsa.keccak_jobs();
    let mut service = KeccakServiceProver::new(job_shapes, job_streams, keccak_handle);

    let stark_proof = air_core::prove(
        &mut [&mut service, &mut producer, &mut mldsa],
        PcsConfig::default(),
    )
    .expect("prove");

    MlDsaProof {
        input,
        group_evals: mldsa.group_evals().to_vec(),
        claimed_sums: mldsa.claimed_sums(),
        sib_stream_len: mldsa.sib_stream_len(),
        sib_squeezed_len: mldsa.sib_squeezed_len(),
        service_claimed_sums: service.claimed_sums(),
        stark_proof,
    }
}

/// Verify a hosted proof by reconstructing `[keccak_service, field_producer,
/// hosted_mldsa]`.
fn verify_hosted(
    proof: &MlDsaProof,
    producer_bytes: Vec<u8>,
) -> Result<(), stwo::core::verifier::VerificationError> {
    let handle = SharedFieldRelation::new();
    let keccak_handle = SharedKeccakRelations::new();
    // The producer recomputes its claimed sum in draw_relations from the public
    // bytes, so the same FieldProducer serves verification with no witness.
    let mut producer = FieldProducer::new(producer_bytes, handle.clone());
    let mut service = KeccakServiceVerifier::new(
        keccak_job_shapes(proof.input.message.len(), proof.sib_stream_len, 0),
        proof.service_claimed_sums.clone(),
        keccak_handle.clone(),
    );
    let mut mldsa = MlDsaVerifier::hosted(
        proof.input.clone(),
        proof.group_evals.clone(),
        proof.claimed_sums.clone(),
        proof.sib_stream_len,
        proof.sib_squeezed_len,
        handle,
        keccak_handle,
    );
    air_core::verify(
        &mut [&mut service, &mut producer, &mut mldsa],
        &proof.stark_proof,
    )
}

// =====================================================================
// Tests.
// =====================================================================

#[test]
fn hosted_proves_and_verifies() {
    let msg = b"m7-phase-a-hosted-swap: the message bytes come from the host".to_vec();
    let proof = prove_hosted(4242, &msg, msg.clone());
    verify_hosted(&proof, msg.clone()).expect("hosted verify");
}

#[test]
fn hosted_tampered_message_byte_rejects() {
    let msg = b"m7-phase-a-hosted-swap: the message bytes come from the host".to_vec();
    let proof = prove_hosted(4242, &msg, msg.clone());
    // The prover committed the honest proof. Now verify against a producer that
    // yields a DIFFERENT byte 0: the µ-absorb bridge requires the honest bytes,
    // the producer yields a tampered one → global LogUp unbalanced → reject.
    let mut tampered = msg.clone();
    tampered[0] ^= 0x01;
    assert!(
        verify_hosted(&proof, tampered).is_err(),
        "tampered producer bytes must break the swap balance"
    );
}

// =====================================================================
// Multi-instance hosting (device + revocation prerequisite): two hosted
// ML-DSA modules in ONE proof, disjoint instance namespaces, one of them
// in private-message mode.
// =====================================================================

/// The claims one hosted instance contributes to the host's proof struct.
struct InstanceClaims {
    input: MlDsaVerifyInput,
    group_evals: Vec<SecureField>,
    claimed_sums: Vec<SecureField>,
    sib_stream_len: usize,
    sib_squeezed_len: usize,
}

/// Prove `[keccak_service(jobs a+b), producer_a, mldsa_a(ns_a, base 0),
/// producer_b, mldsa_b(ns_b, base 16, private-msg)]`. The ONE service hosts
/// both instances' sponge jobs; the stream bases keep their HashIo ids
/// disjoint under the single shared relation set.
fn prove_two_hosted(
    seed_a: u64,
    msg_a: &[u8],
    ns_a: &str,
    seed_b: u64,
    msg_b: &[u8],
    ns_b: &str,
) -> (
    InstanceClaims,
    InstanceClaims,
    Vec<SecureField>,
    stwo::core::proof::StarkProof<air_core::Hasher>,
) {
    let input_a = oracle_input(seed_a, msg_a);
    let input_b = oracle_input(seed_b, msg_b);
    let witness_a = generate_witness(&input_a).expect("witness a");
    let witness_b = generate_witness(&input_b).expect("witness b");

    let handle_a = SharedFieldRelation::new();
    let handle_b = SharedFieldRelation::new();
    let keccak_handle = SharedKeccakRelations::new();
    let mut producer_a = FieldProducer::new(msg_a.to_vec(), handle_a.clone());
    let mut producer_b = FieldProducer::new(msg_b.to_vec(), handle_b.clone());
    let mut mldsa_a = MlDsaProver::hosted(witness_a, input_a.clone(), handle_a, keccak_handle.clone())
        .with_instance_namespace(ns_a);
    let mut mldsa_b = MlDsaProver::hosted(witness_b, input_b.clone(), handle_b, keccak_handle.clone())
        .with_instance_namespace(ns_b)
        .with_stream_base(STREAM_BASE_STRIDE)
        .with_private_message();

    let (shapes_a, streams_a) = mldsa_a.keccak_jobs();
    let (shapes_b, streams_b) = mldsa_b.keccak_jobs();
    let mut service = KeccakServiceProver::new(
        [shapes_a, shapes_b].concat(),
        [streams_a, streams_b].concat(),
        keccak_handle,
    );

    let stark_proof = air_core::prove(
        &mut [&mut service, &mut producer_a, &mut mldsa_a, &mut producer_b, &mut mldsa_b],
        PcsConfig::default(),
    )
    .expect("two-instance prove");

    let claims = |m: &MlDsaProver, input: &MlDsaVerifyInput| InstanceClaims {
        input: input.clone(),
        group_evals: m.group_evals().to_vec(),
        claimed_sums: m.claimed_sums(),
        sib_stream_len: m.sib_stream_len(),
        sib_squeezed_len: m.sib_squeezed_len(),
    };
    (
        claims(&mldsa_a, &input_a),
        claims(&mldsa_b, &input_b),
        service.claimed_sums(),
        stark_proof,
    )
}

/// Verify the two-instance composition. Instance B runs in private-message
/// mode: its verifier-side input carries ZEROED message bytes (only the length
/// is real) — the bytes reach the µ absorption exclusively through producer_b.
#[allow(clippy::too_many_arguments)]
fn verify_two_hosted(
    a: &InstanceClaims,
    ns_a: &str,
    b: &InstanceClaims,
    ns_b: &str,
    service_claimed_sums: Vec<SecureField>,
    producer_a_bytes: Vec<u8>,
    producer_b_bytes: Vec<u8>,
    stark_proof: &stwo::core::proof::StarkProof<air_core::Hasher>,
) -> Result<(), stwo::core::verifier::VerificationError> {
    let handle_a = SharedFieldRelation::new();
    let handle_b = SharedFieldRelation::new();
    let keccak_handle = SharedKeccakRelations::new();
    let mut producer_a = FieldProducer::new(producer_a_bytes, handle_a.clone());
    let mut producer_b = FieldProducer::new(producer_b_bytes, handle_b.clone());
    let job_shapes = [
        keccak_job_shapes(a.input.message.len(), a.sib_stream_len, 0),
        keccak_job_shapes(b.input.message.len(), b.sib_stream_len, STREAM_BASE_STRIDE),
    ]
    .concat();
    let mut service =
        KeccakServiceVerifier::new(job_shapes, service_claimed_sums, keccak_handle.clone());
    let mut mldsa_a = MlDsaVerifier::hosted(
        a.input.clone(),
        a.group_evals.clone(),
        a.claimed_sums.clone(),
        a.sib_stream_len,
        a.sib_squeezed_len,
        handle_a,
        keccak_handle.clone(),
    )
    .with_instance_namespace(ns_a);
    let mut zeroed_b = b.input.clone();
    zeroed_b.message = vec![0u8; b.input.message.len()];
    let mut mldsa_b = MlDsaVerifier::hosted(
        zeroed_b,
        b.group_evals.clone(),
        b.claimed_sums.clone(),
        b.sib_stream_len,
        b.sib_squeezed_len,
        handle_b,
        keccak_handle,
    )
    .with_instance_namespace(ns_b)
    .with_stream_base(STREAM_BASE_STRIDE)
    .with_private_message();
    air_core::verify(
        &mut [&mut service, &mut producer_a, &mut mldsa_a, &mut producer_b, &mut mldsa_b],
        stark_proof,
    )
}

#[test]
fn two_namespaced_hosted_instances_prove_and_verify() {
    // Different message LENGTHS on purpose: the bridge/sink preprocessed
    // columns are shape-dependent, so this exercises disjoint ids end to end.
    let msg_a = b"instance-a: the issuer-style public message".to_vec();
    let msg_b = b"instance-b-private".to_vec();
    let (a, b, svc, proof) = prove_two_hosted(111, &msg_a, "test/a", 222, &msg_b, "test/b");
    verify_two_hosted(&a, "test/a", &b, "test/b", svc, msg_a, msg_b, &proof)
        .expect("two-instance verify");
}

#[test]
fn two_hosted_instances_swapped_claims_reject() {
    // Same message LENGTH so the swap is not rejected trivially on shape: the
    // role separation must come from the namespaced transcript + inputs.
    let msg_a = b"same-length-message-aaaaaaaa".to_vec();
    let msg_b = b"same-length-message-bbbbbbbb".to_vec();
    let (a, b, svc, proof) = prove_two_hosted(111, &msg_a, "test/a", 222, &msg_b, "test/b");
    // Present A's claim tree in B's slot and vice versa (inputs stay put).
    let swapped_a = InstanceClaims {
        input: a.input.clone(),
        group_evals: b.group_evals.clone(),
        claimed_sums: b.claimed_sums.clone(),
        sib_stream_len: b.sib_stream_len,
        sib_squeezed_len: b.sib_squeezed_len,
    };
    let swapped_b = InstanceClaims {
        input: b.input.clone(),
        group_evals: a.group_evals.clone(),
        claimed_sums: a.claimed_sums.clone(),
        sib_stream_len: a.sib_stream_len,
        sib_squeezed_len: a.sib_squeezed_len,
    };
    assert!(
        verify_two_hosted(&swapped_a, "test/a", &swapped_b, "test/b", svc, msg_a, msg_b, &proof)
            .is_err(),
        "cross-instance claim replay must reject"
    );
}

/// Two instances under the SAME namespace with different witnesses collide on
/// the witness-dependent SIB schedule ids; the air-core preprocessed
/// fingerprint invariant must catch this fail-closed at prove time. This is
/// the regression documenting that the namespace is load-bearing.
#[test]
#[should_panic(expected = "has different content in modules")]
fn two_instances_same_namespace_panics_on_preprocessed_collision() {
    let msg_a = b"same-length-message-aaaaaaaa".to_vec();
    let msg_b = b"same-length-message-bbbbbbbb".to_vec();
    let _ = prove_two_hosted(111, &msg_a, "test/dup", 222, &msg_b, "test/dup");
}
