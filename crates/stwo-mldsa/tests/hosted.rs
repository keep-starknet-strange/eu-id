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

use stwo_mldsa::air_util::{col_eval, m31, ColEval};
use stwo_mldsa::reference::encoding::{pk_decode, sig_decode};
use stwo_mldsa::reference::sponge::shake256;
use stwo_mldsa::statement::{
    MlDsaProof, MlDsaProver, MlDsaVerifier, HOSTED_MSG_FIELD_ID,
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

/// Prove the hosted statement: `[field_producer(producer_bytes), hosted_mldsa]`.
/// `producer_bytes` is what the HOST yields (honest = the message; tamper it to
/// simulate a mismatched issuer preimage).
fn prove_hosted(seed: u64, msg: &[u8], producer_bytes: Vec<u8>) -> MlDsaProof {
    let input = oracle_input(seed, msg);
    let witness = generate_witness(&input).expect("witness");

    let handle = SharedFieldRelation::new();
    let mut producer = FieldProducer::new(producer_bytes, handle.clone());
    let mut mldsa = MlDsaProver::hosted(witness, input.clone(), handle);

    let stark_proof =
        air_core::prove(&mut [&mut producer, &mut mldsa], PcsConfig::default()).expect("prove");

    MlDsaProof {
        input,
        group_evals: mldsa.group_evals().to_vec(),
        claimed_sums: mldsa.claimed_sums(),
        sib_stream_len: mldsa.sib_stream_len(),
        sib_squeezed_len: mldsa.sib_squeezed_len(),
        stark_proof,
    }
}

/// Verify a hosted proof by reconstructing `[field_producer, hosted_mldsa]`.
fn verify_hosted(
    proof: &MlDsaProof,
    producer_bytes: Vec<u8>,
) -> Result<(), stwo::core::verifier::VerificationError> {
    let handle = SharedFieldRelation::new();
    // The producer recomputes its claimed sum in draw_relations from the public
    // bytes, so the same FieldProducer serves verification with no witness.
    let mut producer = FieldProducer::new(producer_bytes, handle.clone());
    let mut mldsa = MlDsaVerifier::hosted(
        proof.input.clone(),
        proof.group_evals.clone(),
        proof.claimed_sums.clone(),
        proof.sib_stream_len,
        proof.sib_squeezed_len,
        handle,
    );
    air_core::verify(&mut [&mut producer, &mut mldsa], &proof.stark_proof)
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
