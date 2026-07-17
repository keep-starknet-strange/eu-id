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
use stwo::core::fri::FriConfig;
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
use stwo_mldsa::coeffs::relations::SharedRangeRelation;
use stwo_mldsa::coeffs::tables::SharedRangeTable;
use stwo_mldsa::reference::encoding::{pk_decode, sig_decode};
use stwo_mldsa::reference::sponge::shake256;
use stwo_mldsa::statement::{
    hosted_public_claimed_sums_len, keccak_job_shapes, MlDsaProver, MlDsaVerifier,
    HOSTED_MSG_FIELD_ID, STREAM_BASE_STRIDE,
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
        Self {
            bytes,
            handle,
            field: None,
            claimed_sum: SecureField::zero(),
            component: None,
        }
    }
    fn field(&self) -> FieldBytesRelation {
        self.field.clone().expect("relation drawn")
    }
}

/// The direct Keccak round AIR uses batch-four LogUp, so blowup two suffices.
fn pcs_config() -> PcsConfig {
    PcsConfig {
        pow_bits: 10,
        fri_config: FriConfig::new(0, 2, 3, 1),
        lifting_log_size: None,
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
            FieldProducerEval {
                bytes: self.bytes.clone(),
                field: self.field(),
            },
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
        debug_assert_eq!(
            sum, self.claimed_sum,
            "producer sum drifted from draw_relations"
        );
        tb.extend_evals(trace);
    }
    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![self.component.as_ref().expect("built")]
    }
}

// =====================================================================
// Fixture (model: composed.rs).
// =====================================================================

#[derive(Clone)]
struct HostedProof {
    input: MlDsaVerifyInput,
    group_evals: Vec<SecureField>,
    claimed_sums: Vec<SecureField>,
    range_table_claimed_sum: SecureField,
    service_claimed_sums: Vec<SecureField>,
    post_interaction_payloads: Vec<Vec<u8>>,
    stark_proof: stwo::core::proof::StarkProof<air_core::Hasher>,
}

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

/// Prove the hosted statement: `[range_table, keccak_service,
/// field_producer(producer_bytes), hosted_mldsa]`. `producer_bytes` is what the
/// HOST yields (honest = the message; tamper it to simulate a mismatched issuer
/// preimage).
fn prove_hosted(seed: u64, msg: &[u8], producer_bytes: Vec<u8>) -> HostedProof {
    let input = oracle_input(seed, msg);
    let witness = generate_witness(&input).expect("witness");

    let handle = SharedFieldRelation::new();
    let keccak_handle = SharedKeccakRelations::new();
    let range_handle = SharedRangeRelation::new();
    let mut producer = FieldProducer::new(producer_bytes, handle.clone());
    let mut mldsa = MlDsaProver::hosted(
        witness,
        input.clone(),
        handle,
        range_handle.clone(),
        keccak_handle.clone(),
    );
    let mut range_table = SharedRangeTable::prover(&[mldsa.range_uses().clone()], range_handle);
    let (job_shapes, job_streams) = mldsa.keccak_jobs();
    let mut service = KeccakServiceProver::new(job_shapes, job_streams, keccak_handle);

    let (stark_proof, post_interaction_payloads) = air_core::prove_with_post_interaction(
        &mut [&mut range_table, &mut service, &mut producer, &mut mldsa],
        pcs_config(),
    )
    .expect("prove");

    HostedProof {
        input,
        group_evals: mldsa.group_evals().to_vec(),
        claimed_sums: mldsa.claimed_sums(),
        range_table_claimed_sum: range_table.claimed_sum(),
        service_claimed_sums: service.claimed_sums(),
        post_interaction_payloads,
        stark_proof,
    }
}

/// Verify a hosted proof by reconstructing `[range_table, keccak_service,
/// field_producer, hosted_mldsa]`.
fn verify_hosted(
    proof: &HostedProof,
    producer_bytes: Vec<u8>,
) -> Result<(), stwo::core::verifier::VerificationError> {
    let handle = SharedFieldRelation::new();
    let keccak_handle = SharedKeccakRelations::new();
    let range_handle = SharedRangeRelation::new();
    // The producer recomputes its claimed sum in draw_relations from the public
    // bytes, so the same FieldProducer serves verification with no witness.
    let mut producer = FieldProducer::new(producer_bytes, handle.clone());
    let mut service = KeccakServiceVerifier::new(
        keccak_job_shapes(proof.input.message.len(), 0, false),
        proof.service_claimed_sums.clone(),
        keccak_handle.clone(),
    );
    let mut range_table =
        SharedRangeTable::verifier(proof.range_table_claimed_sum, range_handle.clone());
    let mut mldsa = MlDsaVerifier::hosted(
        proof.input.clone(),
        proof.group_evals.clone(),
        proof.claimed_sums.clone(),
        handle,
        range_handle,
        keccak_handle,
    );
    air_core::verify_with_expected_preprocessed_root_and_payloads(
        &mut [&mut range_table, &mut service, &mut producer, &mut mldsa],
        &proof.stark_proof,
        None,
        &proof.post_interaction_payloads,
    )
    .map_err(|e| match e {
        air_core::VerifyError::Stark(e) => e,
        air_core::VerifyError::PreprocessedRootMismatch { .. } => unreachable!("no root pinned"),
    })
}

fn prove_hosted_public(seed: u64, msg: &[u8]) -> HostedProof {
    let input = oracle_input(seed, msg);
    let witness = generate_witness(&input).expect("witness");
    let keccak_handle = SharedKeccakRelations::new();
    let range_handle = SharedRangeRelation::new();
    let mut mldsa =
        MlDsaProver::hosted_public(witness, input, range_handle.clone(), keccak_handle.clone());
    let mut range_table = SharedRangeTable::prover(&[mldsa.range_uses().clone()], range_handle);
    let (job_shapes, job_streams) = mldsa.keccak_jobs();
    assert_eq!(job_shapes.len(), 2, "native-µ mode keeps only c̃ and SIB");
    let mut service = KeccakServiceProver::new(job_shapes, job_streams, keccak_handle);
    let (stark_proof, post_interaction_payloads) = air_core::prove_with_post_interaction(
        &mut [&mut range_table, &mut service, &mut mldsa],
        pcs_config(),
    )
    .expect("hosted-public prove");
    let claimed_sums = mldsa.claimed_sums();
    assert_eq!(claimed_sums.len(), hosted_public_claimed_sums_len());
    HostedProof {
        input: mldsa.input().clone(),
        group_evals: mldsa.group_evals().to_vec(),
        claimed_sums,
        range_table_claimed_sum: range_table.claimed_sum(),
        service_claimed_sums: service.claimed_sums(),
        post_interaction_payloads,
        stark_proof,
    }
}

fn verify_hosted_public(
    proof: &HostedProof,
) -> Result<(), stwo::core::verifier::VerificationError> {
    let keccak_handle = SharedKeccakRelations::new();
    let range_handle = SharedRangeRelation::new();
    let mut service = KeccakServiceVerifier::new(
        keccak_job_shapes(proof.input.message.len(), 0, true),
        proof.service_claimed_sums.clone(),
        keccak_handle.clone(),
    );
    let mut range_table =
        SharedRangeTable::verifier(proof.range_table_claimed_sum, range_handle.clone());
    let mut mldsa = MlDsaVerifier::hosted_public(
        proof.input.clone(),
        proof.group_evals.clone(),
        proof.claimed_sums.clone(),
        range_handle,
        keccak_handle,
    );
    air_core::verify_with_expected_preprocessed_root_and_payloads(
        &mut [&mut range_table, &mut service, &mut mldsa],
        &proof.stark_proof,
        None,
        &proof.post_interaction_payloads,
    )
    .map_err(|error| match error {
        air_core::VerifyError::Stark(error) => error,
        air_core::VerifyError::PreprocessedRootMismatch { .. } => unreachable!("no root pinned"),
    })
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
fn hosted_public_native_mu_proves_and_verifies() {
    let msg = b"issuer/device public message uses verifier-native mu".to_vec();
    let proof = prove_hosted_public(4244, &msg);
    verify_hosted_public(&proof).expect("hosted-public verify");
}

#[test]
fn hosted_public_message_tamper_rejects_native_mu_prefix() {
    let msg = b"issuer/device public message native mu tamper".to_vec();
    let mut proof = prove_hosted_public(4245, &msg);
    proof.input.message[0] ^= 1;
    assert!(
        verify_hosted_public(&proof).is_err(),
        "tampered public message must change verifier-native µ and reject"
    );
}

#[test]
fn hosted_public_native_mu_mismatch_returns_error_not_panic() {
    let msg = b"native mu mismatch is an AIR rejection".to_vec();
    let mut input = oracle_input(4247, &msg);
    let witness = generate_witness(&input).expect("honest witness");
    input.message[0] ^= 1;

    let handle = SharedKeccakRelations::new();
    let range_handle = SharedRangeRelation::new();
    let mut mldsa =
        MlDsaProver::hosted_public(witness, input, range_handle.clone(), handle.clone());
    let mut range_table = SharedRangeTable::prover(&[mldsa.range_uses().clone()], range_handle);
    let (job_shapes, job_streams) = mldsa.keccak_jobs();
    let mut service = KeccakServiceProver::new(job_shapes, job_streams, handle);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        air_core::prove_with_post_interaction(
            &mut [&mut range_table, &mut service, &mut mldsa],
            pcs_config(),
        )
    }));
    let (stark_proof, post_interaction_payloads) = result
        .expect("native µ mismatch must not panic")
        .expect("prover may commit the inconsistent trace; verifier rejects it");
    let proof = HostedProof {
        input: mldsa.input().clone(),
        group_evals: mldsa.group_evals().to_vec(),
        claimed_sums: mldsa.claimed_sums(),
        range_table_claimed_sum: range_table.claimed_sum(),
        service_claimed_sums: service.claimed_sums(),
        post_interaction_payloads,
        stark_proof,
    };
    assert!(verify_hosted_public(&proof).is_err());
}

#[test]
fn hosted_missing_round_gkr_payload_rejects() {
    let msg = b"hosted proof must carry the round GKR payload".to_vec();
    let mut proof = prove_hosted(4242, &msg, msg.clone());
    proof.post_interaction_payloads.clear();
    let result =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| verify_hosted(&proof, msg)));
    assert!(
        matches!(result, Ok(Err(_))),
        "missing hosted round-GKR payload must return an error, not panic"
    );
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

#[test]
fn hosted_carried_tr_is_overwritten_before_use() {
    let msg = b"hosted carried tr is compatibility data only".to_vec();
    let mut proof = prove_hosted(4243, &msg, msg.clone());
    proof.input.tr[0] ^= 1;
    verify_hosted(&proof, msg).expect("carried tr must not influence verification");
}

#[test]
fn hosted_public_key_tamper_recomputes_tr_and_rejects() {
    let msg = b"hosted native tr remains bound to the public key".to_vec();
    let mut proof = prove_hosted(4246, &msg, msg.clone());
    proof.input.rho[0] ^= 1;
    assert!(verify_hosted(&proof, msg).is_err());
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
}

struct TwoHostedProof {
    a: InstanceClaims,
    b: InstanceClaims,
    service_claimed_sums: Vec<SecureField>,
    range_table_claimed_sum: SecureField,
    post_interaction_payloads: Vec<Vec<u8>>,
    stark_proof: stwo::core::proof::StarkProof<air_core::Hasher>,
}

/// Prove `[range_table(uses a+b), keccak_service(jobs a+b), producer_a,
/// mldsa_a(ns_a, base 0), producer_b, mldsa_b(ns_b, base 16, private-msg)]`.
/// The ONE service and ONE range table host both instances; the stream bases
/// keep their HashIo ids disjoint under the single shared relation set.
fn prove_two_hosted(
    seed_a: u64,
    msg_a: &[u8],
    ns_a: &str,
    seed_b: u64,
    msg_b: &[u8],
    ns_b: &str,
) -> TwoHostedProof {
    let input_a = oracle_input(seed_a, msg_a);
    let input_b = oracle_input(seed_b, msg_b);
    let witness_a = generate_witness(&input_a).expect("witness a");
    let witness_b = generate_witness(&input_b).expect("witness b");

    let handle_a = SharedFieldRelation::new();
    let handle_b = SharedFieldRelation::new();
    let keccak_handle = SharedKeccakRelations::new();
    let range_handle = SharedRangeRelation::new();
    let mut producer_a = FieldProducer::new(msg_a.to_vec(), handle_a.clone());
    let mut producer_b = FieldProducer::new(msg_b.to_vec(), handle_b.clone());
    let mut mldsa_a = MlDsaProver::hosted(
        witness_a,
        input_a.clone(),
        handle_a,
        range_handle.clone(),
        keccak_handle.clone(),
    )
    .with_instance_namespace(ns_a);
    let mut mldsa_b = MlDsaProver::hosted(
        witness_b,
        input_b.clone(),
        handle_b,
        range_handle.clone(),
        keccak_handle.clone(),
    )
    .with_instance_namespace(ns_b)
    .with_stream_base(STREAM_BASE_STRIDE)
    .with_private_message();
    let mut range_table = SharedRangeTable::prover(
        &[mldsa_a.range_uses().clone(), mldsa_b.range_uses().clone()],
        range_handle,
    );

    let (shapes_a, streams_a) = mldsa_a.keccak_jobs();
    let (shapes_b, streams_b) = mldsa_b.keccak_jobs();
    let mut service = KeccakServiceProver::new(
        [shapes_a, shapes_b].concat(),
        [streams_a, streams_b].concat(),
        keccak_handle,
    );

    let (stark_proof, post_interaction_payloads) = air_core::prove_with_post_interaction(
        &mut [
            &mut range_table,
            &mut service,
            &mut producer_a,
            &mut mldsa_a,
            &mut producer_b,
            &mut mldsa_b,
        ],
        pcs_config(),
    )
    .expect("two-instance prove");

    let claims = |m: &MlDsaProver, input: &MlDsaVerifyInput| InstanceClaims {
        input: input.clone(),
        group_evals: m.group_evals().to_vec(),
        claimed_sums: m.claimed_sums(),
    };
    TwoHostedProof {
        a: claims(&mldsa_a, &input_a),
        b: claims(&mldsa_b, &input_b),
        service_claimed_sums: service.claimed_sums(),
        range_table_claimed_sum: range_table.claimed_sum(),
        post_interaction_payloads,
        stark_proof,
    }
}

/// Verify the two-instance composition. Instance B runs in private-message
/// mode: its verifier-side input carries ZEROED message bytes (only the length
/// is real) — the bytes reach the µ absorption exclusively through producer_b.
fn verify_two_hosted(
    a: &InstanceClaims,
    ns_a: &str,
    b: &InstanceClaims,
    ns_b: &str,
    proof: &TwoHostedProof,
    producer_a_bytes: Vec<u8>,
    producer_b_bytes: Vec<u8>,
) -> Result<(), stwo::core::verifier::VerificationError> {
    let handle_a = SharedFieldRelation::new();
    let handle_b = SharedFieldRelation::new();
    let keccak_handle = SharedKeccakRelations::new();
    let range_handle = SharedRangeRelation::new();
    let mut producer_a = FieldProducer::new(producer_a_bytes, handle_a.clone());
    let mut producer_b = FieldProducer::new(producer_b_bytes, handle_b.clone());
    let job_shapes = [
        keccak_job_shapes(a.input.message.len(), 0, false),
        keccak_job_shapes(b.input.message.len(), STREAM_BASE_STRIDE, false),
    ]
    .concat();
    let mut service = KeccakServiceVerifier::new(
        job_shapes,
        proof.service_claimed_sums.clone(),
        keccak_handle.clone(),
    );
    let mut range_table =
        SharedRangeTable::verifier(proof.range_table_claimed_sum, range_handle.clone());
    let mut mldsa_a = MlDsaVerifier::hosted(
        a.input.clone(),
        a.group_evals.clone(),
        a.claimed_sums.clone(),
        handle_a,
        range_handle.clone(),
        keccak_handle.clone(),
    )
    .with_instance_namespace(ns_a);
    let mut zeroed_b = b.input.clone();
    zeroed_b.message = vec![0u8; b.input.message.len()];
    let mut mldsa_b = MlDsaVerifier::hosted(
        zeroed_b,
        b.group_evals.clone(),
        b.claimed_sums.clone(),
        handle_b,
        range_handle,
        keccak_handle,
    )
    .with_instance_namespace(ns_b)
    .with_stream_base(STREAM_BASE_STRIDE)
    .with_private_message();
    air_core::verify_with_expected_preprocessed_root_and_payloads(
        &mut [
            &mut range_table,
            &mut service,
            &mut producer_a,
            &mut mldsa_a,
            &mut producer_b,
            &mut mldsa_b,
        ],
        &proof.stark_proof,
        None,
        &proof.post_interaction_payloads,
    )
    .map_err(|e| match e {
        air_core::VerifyError::Stark(e) => e,
        air_core::VerifyError::PreprocessedRootMismatch { .. } => unreachable!("no root pinned"),
    })
}

#[test]
fn two_namespaced_hosted_instances_prove_and_verify() {
    // Different message LENGTHS on purpose: the bridge/sink preprocessed
    // columns are shape-dependent, so this exercises disjoint ids end to end.
    let msg_a = b"instance-a: the issuer-style public message".to_vec();
    let msg_b = b"instance-b-private".to_vec();
    let proof = prove_two_hosted(111, &msg_a, "test/a", 222, &msg_b, "test/b");
    verify_two_hosted(&proof.a, "test/a", &proof.b, "test/b", &proof, msg_a, msg_b)
        .expect("two-instance verify");
}

#[test]
fn two_hosted_instances_swapped_claims_reject() {
    // Same message LENGTH so the swap is not rejected trivially on shape: the
    // role separation must come from the namespaced transcript + inputs.
    let msg_a = b"same-length-message-aaaaaaaa".to_vec();
    let msg_b = b"same-length-message-bbbbbbbb".to_vec();
    let proof = prove_two_hosted(111, &msg_a, "test/a", 222, &msg_b, "test/b");
    // Present A's claim tree in B's slot and vice versa (inputs stay put).
    let swapped_a = InstanceClaims {
        input: proof.a.input.clone(),
        group_evals: proof.b.group_evals.clone(),
        claimed_sums: proof.b.claimed_sums.clone(),
    };
    let swapped_b = InstanceClaims {
        input: proof.b.input.clone(),
        group_evals: proof.a.group_evals.clone(),
        claimed_sums: proof.a.claimed_sums.clone(),
    };
    assert!(
        verify_two_hosted(&swapped_a, "test/a", &swapped_b, "test/b", &proof, msg_a, msg_b)
            .is_err(),
        "cross-instance claim replay must reject"
    );
}

/// A-706: the old same-namespace collision negative guarded witness-dependent
/// SIB schedules. Q13 made those schedules static, so identical-content
/// preprocessed ids now deduplicate soundly and the pair proves and verifies.
/// The generic differing-content panic remains covered directly by
/// `air_core::tests::preprocessed_invariant_rejects_duplicate_id_with_different_content`.
#[test]
fn two_instances_same_namespace_share_static_preprocessed() {
    let msg_a = b"same-length-message-aaaaaaaa".to_vec();
    let msg_b = b"same-length-message-bbbbbbbb".to_vec();
    let proof = prove_two_hosted(111, &msg_a, "test/dup", 222, &msg_b, "test/dup");
    verify_two_hosted(
        &proof.a, "test/dup", &proof.b, "test/dup", &proof, msg_a, msg_b,
    )
    .expect("same-namespace static preprocessing deduplicates");
}
