//! Per-stage proving primitives shared by the combined-prover laptop benchmarks.
//!
//! A single [`PipelineWitness`] — built from an honest fixture credential
//! *outside* the measured window — supplies every stage's inputs: the P256 proof
//! draft, the SHA-256 witness, and the age / nationality predicate inputs. This
//! module is the **one** definition of "how each component proves and verifies":
//! a `prove_*` (returning the typed proof), a `verify_*`, and a `*_proof_bytes`
//! per stage. Both consumers funnel through these — the criterion timing bench
//! (`identity_bench.rs`) via the [`Stage`] closure table below, and the
//! peak-memory + JSON report driver (`examples/bench_report.rs`) by calling the
//! free functions directly, in an order that keeps each stage's peak memory
//! isolated.
//!
//! Every stage times **only the STARK proving**: the witnesses and the P256
//! draft are built once, in setup, which is the honest way to attribute
//! per-component cost (the draft generation common to every stage is not
//! double-counted). The end-to-end relying-party `prove_identity` wall-clock —
//! which additionally builds the witness + draft and signs — is measured
//! separately by the report driver, and is the figure the on-device harness
//! reproduces.
//!
//! Standalone SHA size note: `Sha256Proof` is not itself serde-serializable, so
//! its reported size is the underlying STARK proof (the FRI proof + Merkle
//! commitments — the overwhelming bulk); the small witness-derived metadata is
//! excluded.

// Each consumer (the bench, the report driver) uses a subset of this module.
#![allow(dead_code)]

use std::hint::black_box;

use eu_id_prover::generator::PipelineWitness;
use eu_id_prover::{prove as prove_pipeline_inner, verify as verify_pipeline_inner, Proof};

use predicates::nat::types::Proof as NatProof;
use predicates::nat::NationalityPredicate;
use predicates::{AgeRangeCheck, AgeRangeCheckProof};

use stwo::core::fields::m31::M31;
use stwo::core::pcs::PcsConfig;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;

use stwo_p256::proof::air::{prove_current_air, verify_current_air};
use stwo_p256::proof::{P256CurrentAirProof, P256ProofDraft};
use stwo_p256::public_inputs::PublicEcdsaInstance;

use stwo_sha256::stark::{
    prove_sha256_from_witness, verify_sha256_proof, ProverConfig, Sha256Proof,
};

type P256Proof = P256CurrentAirProof<Blake2sMerkleHasher>;
type Instances = Vec<PublicEcdsaInstance<M31>>;

/// The P256 draft carried by the witness (every honest fixture has one).
fn draft(w: &PipelineWitness) -> &P256ProofDraft {
    w.p256_draft
        .as_ref()
        .expect("benchmark fixtures are honest credentials with a valid P256 draft")
}

/// A self-consistent holder nonce draft: the demo device key signing the demo
/// nonce. Built outside the measured window, like the credential draft.
fn nonce_draft() -> P256ProofDraft {
    P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![
        eu_id_prover::fixtures::demo_nonce_statement().ecdsa_input(),
    ])
    .expect("demo nonce builds a proof draft")
}

// ---- P256 ECDSA (the cost driver) -----------------------------------------

pub fn prove_p256(w: &PipelineWitness) -> P256Proof {
    prove_current_air(draft(w)).expect("p256 proves")
}

pub fn p256_instances(proof: &P256Proof) -> Instances {
    proof.claim.public_inputs.instances.clone()
}

pub fn verify_p256(proof: &P256Proof, instances: &[PublicEcdsaInstance<M31>]) {
    // `verify_current_air` consumes the proof; clone for repeatable timing. The
    // clone (a memcpy of the few-MB proof) is sub-millisecond against a
    // tens-of-ms verify, so it does not distort the measurement.
    verify_current_air(proof.clone(), instances).expect("p256 verifies");
}

pub fn p256_proof_bytes(proof: &P256Proof) -> usize {
    bincode::serialize(&(&proof.claim, &proof.interaction_claim, &proof.stark_proof))
        .map(|b| b.len())
        .unwrap_or(0)
}

// ---- SHA-256 ---------------------------------------------------------------

/// The SHA prover config matching the witness the combined proof runs (same row
/// count and group width), so the standalone SHA stage measures the very
/// component that runs inside `pipeline`.
fn sha_config(w: &PipelineWitness) -> ProverConfig {
    ProverConfig {
        log_n_rows: w.sha_log_n_rows,
        group_width: w.sha_group_width,
        pcs_config: PcsConfig::default(),
    }
}

pub fn prove_sha(w: &PipelineWitness) -> Sha256Proof {
    prove_sha256_from_witness(&w.sha_witness, &sha_config(w)).expect("sha proves")
}

pub fn verify_sha(proof: &Sha256Proof) {
    verify_sha256_proof(proof).expect("sha verifies");
}

pub fn sha_proof_bytes(proof: &Sha256Proof) -> usize {
    bincode::serialize(&proof.stark_proof)
        .map(|b| b.len())
        .unwrap_or(0)
}

// ---- Age predicate (range-check strategy, the combined-proof canonical) ----

pub fn prove_age(w: &PipelineWitness) -> AgeRangeCheckProof {
    AgeRangeCheck::new(PcsConfig::default())
        .prove(&w.age_public, &w.age_dob)
        .expect("age proves")
}

pub fn verify_age(proof: &AgeRangeCheckProof) {
    AgeRangeCheck::new(PcsConfig::default())
        .verify(proof)
        .expect("age verifies");
}

pub fn age_proof_bytes(proof: &AgeRangeCheckProof) -> usize {
    bincode::serialize(proof).map(|b| b.len()).unwrap_or(0)
}

// ---- Nationality predicate -------------------------------------------------

pub fn prove_nat(w: &PipelineWitness) -> NatProof {
    NationalityPredicate::new(PcsConfig::default())
        .prove(&w.nat_public, &w.nat_private)
        .expect("nat proves")
}

pub fn verify_nat(proof: &NatProof) {
    NationalityPredicate::new(PcsConfig::default())
        .verify(proof)
        .expect("nat verifies");
}

pub fn nat_proof_bytes(proof: &NatProof) -> usize {
    bincode::serialize(proof).map(|b| b.len()).unwrap_or(0)
}

// ---- Full combined pipeline (P256 + SHA + bridge + age + nat) --------------

pub fn prove_pipeline(w: &PipelineWitness) -> Proof {
    prove_pipeline_inner(
        draft(w),
        &nonce_draft(),
        &w.sha_witness,
        w.sha_log_n_rows,
        w.sha_group_width,
        &w.age_public,
        &w.age_dob,
        &w.nat_public,
        &w.nat_private,
    )
    .expect("pipeline proves")
}

pub fn pipeline_instances(proof: &Proof) -> Instances {
    proof.p256_instances().to_vec()
}

/// The nonce module's proven instances — bound in full (`z` included).
pub fn pipeline_nonce_instances(proof: &Proof) -> Instances {
    proof.nonce_p256_instances().to_vec()
}

pub fn verify_pipeline(
    proof: &Proof,
    instances: &[PublicEcdsaInstance<M31>],
    nonce_instances: &[PublicEcdsaInstance<M31>],
) {
    verify_pipeline_inner(proof, instances, nonce_instances).expect("pipeline verifies");
}

pub fn pipeline_proof_bytes(proof: &Proof) -> usize {
    bincode::serialize(proof).map(|b| b.len()).unwrap_or(0)
}

// ---- Criterion stage table -------------------------------------------------

/// One benchmark stage for the criterion harness: a label, a `prove` thunk, a
/// `verify` thunk (over a proof generated once at construction), and that
/// proof's serialized size.
pub struct Stage<'a> {
    pub name: &'static str,
    pub prove: Box<dyn Fn() + 'a>,
    pub verify: Box<dyn Fn() + 'a>,
    pub proof_bytes: usize,
}

/// Build all five stages from a pipeline witness, for the criterion timing
/// bench. Each stage pre-proves once (for its verify thunk + size); the
/// retained proofs do not affect timing. The report driver does **not** use this
/// — it measures each stage in isolation so retained proofs cannot pollute its
/// peak-memory numbers.
pub fn stages(w: &PipelineWitness) -> Vec<Stage<'_>> {
    let p256 = prove_p256(w);
    let p256_inst = p256_instances(&p256);
    let p256_bytes = p256_proof_bytes(&p256);

    let sha = prove_sha(w);
    let sha_bytes = sha_proof_bytes(&sha);

    let age = prove_age(w);
    let age_bytes = age_proof_bytes(&age);

    let nat = prove_nat(w);
    let nat_bytes = nat_proof_bytes(&nat);

    let pipeline = prove_pipeline(w);
    let pipeline_inst = pipeline_instances(&pipeline);
    let pipeline_nonce_inst = pipeline_nonce_instances(&pipeline);
    let pipeline_bytes = pipeline_proof_bytes(&pipeline);

    vec![
        Stage {
            name: "p256",
            prove: Box::new(move || {
                black_box(prove_p256(w));
            }),
            verify: Box::new(move || verify_p256(&p256, &p256_inst)),
            proof_bytes: p256_bytes,
        },
        Stage {
            name: "sha",
            prove: Box::new(move || {
                black_box(prove_sha(w));
            }),
            verify: Box::new(move || verify_sha(&sha)),
            proof_bytes: sha_bytes,
        },
        Stage {
            name: "age",
            prove: Box::new(move || {
                black_box(prove_age(w));
            }),
            verify: Box::new(move || verify_age(&age)),
            proof_bytes: age_bytes,
        },
        Stage {
            name: "nat",
            prove: Box::new(move || {
                black_box(prove_nat(w));
            }),
            verify: Box::new(move || verify_nat(&nat)),
            proof_bytes: nat_bytes,
        },
        Stage {
            name: "pipeline",
            prove: Box::new(move || {
                black_box(prove_pipeline(w));
            }),
            verify: Box::new(move || {
                verify_pipeline(&pipeline, &pipeline_inst, &pipeline_nonce_inst)
            }),
            proof_bytes: pipeline_bytes,
        },
    ]
}
