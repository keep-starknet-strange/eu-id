//! Exact-iteration perf probe for the FULL published TS13 tuple: N=1
//! age_over_18 value-equality mdoc with in-STARK sorted-pair revocation
//! (revocation SHA + range module + third coprocessor ECDSA).
//!
//! Mirrors `mdoc_perf_probe` (which measures the revocation-OFF demo circuit)
//! so the two reports are directly comparable. `BENCH_ITERS` controls the
//! sample count; medians are reported.

// Match the production (SDK/FFI) allocator so probe numbers are honest.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use std::hint::black_box;
use std::time::{Duration, Instant};

use ciborium::value::Value;
use ecdsa::signature::hazmat::PrehashSigner;
use eu_id_prover::mdoc::{
    demo_mdoc_circuit_fixture_with_attributes, mdoc_proof_byte_breakdown, prove_mdoc_circuit,
    verify_mdoc_circuit_with_preprocessed_root, MdocDisclosureMode, MdocRequestedAttribute,
    MdocRevocationRangeWitness,
};
use eu_id_prover::ts13::{
    ts13_mso_derived_revocation_id, ts13_revocation_message_hash, Ts13RevocationStatement,
    Ts13RevocationWitness,
};
use p256::ecdsa::{Signature as P256Signature, SigningKey};
use serde::Serialize;
use stwo_p256::types::{AffinePoint, Signature, U256};

#[derive(Serialize)]
struct Report {
    circuit: &'static str,
    rayon_num_threads: Option<String>,
    iters: usize,
    proof_bytes: usize,
    prove_ms_median: u128,
    prove_ms_all: Vec<u128>,
    verify_ms_median: u128,
    byte_breakdown: eu_id_prover::mdoc::MdocProofByteBreakdown,
    p4b_prove_profile: Option<String>,
    p4b_verify_profile: Option<String>,
}

fn median(times: &mut [Duration]) -> u128 {
    times.sort();
    times[times.len() / 2].as_millis()
}

fn main() {
    let iters = std::env::var("BENCH_ITERS")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(5)
        .max(1);

    // N=1 value-equality request over age_over_18 — the published TS13 tuple.
    let mut value_bytes = Vec::new();
    ciborium::ser::into_writer(&Value::Bool(true), &mut value_bytes)
        .expect("age_over_18 value encodes");
    let fixture = demo_mdoc_circuit_fixture_with_attributes(vec![MdocRequestedAttribute {
        element_identifier: "age_over_18".to_string(),
        mode: MdocDisclosureMode::ValueEquality(value_bytes),
    }]);

    // Sorted-pair revocation witness for the MSO-derived id, exactly as in
    // `ts13_evidence_pack_n1_measurements`.
    let signing_key = SigningKey::from_bytes((&[33u8; 32]).into()).expect("revocation key");
    let encoded = signing_key.verifying_key().to_encoded_point(false);
    let x: [u8; 32] = encoded.x().expect("x")[..].try_into().expect("x len");
    let y: [u8; 32] = encoded.y().expect("y")[..].try_into().expect("y len");
    let revocation_statement = Ts13RevocationStatement {
        revocation_public_key: AffinePoint {
            x: U256(x),
            y: U256(y),
        },
        epoch: 51,
    };
    let id = ts13_mso_derived_revocation_id(&fixture.extracted.mso);
    let (id_lo, id_hi) = (id.saturating_sub(1), id.saturating_add(1));
    let message_hash = ts13_revocation_message_hash(id_lo, id_hi, revocation_statement.epoch);
    let pair_signature: P256Signature = signing_key
        .sign_prehash(&message_hash)
        .expect("revocation prehash signs");
    let r: [u8; 32] = pair_signature.r().to_bytes().into();
    let s: [u8; 32] = pair_signature.s().to_bytes().into();
    let revocation_witness = Ts13RevocationWitness {
        id,
        id_lo,
        id_hi,
        epoch: revocation_statement.epoch,
        signature: Signature {
            r: U256(r),
            s: U256(s),
        },
    };
    let statement = fixture
        .statement
        .clone()
        .with_ts13_revocation((&revocation_statement).into())
        .with_ts13_revocation_range(MdocRevocationRangeWitness {
            id: revocation_witness.id,
            id_lo: revocation_witness.id_lo,
            id_hi: revocation_witness.id_hi,
        })
        .with_ts13_revocation_signature(revocation_witness.signature.clone());

    let mut prove_times = Vec::with_capacity(iters);
    let mut proof = None;
    for _ in 0..iters {
        let start = Instant::now();
        let next =
            prove_mdoc_circuit(&fixture.extracted, &statement).expect("TS13 N=1 circuit proves");
        prove_times.push(start.elapsed());
        black_box(&next);
        proof = Some(next);
    }
    let proof = proof.expect("at least one proof iteration ran");
    let p4b_prove_profile = proof.p4b_prove_profile().map(|p| format!("{p:?}"));
    let proof_bincode = bincode::serialize(&proof).expect("TS13 mdoc proof serializes");
    // Optional raw-proof dump for wire-compression experiments.
    if let Ok(path) = std::env::var("BENCH_DUMP_PROOF") {
        std::fs::write(&path, &proof_bincode).expect("proof dump writes");
    }
    let proof_bytes = proof_bincode.len();

    let mut verify_times = Vec::with_capacity(iters);
    for _ in 0..iters {
        let start = Instant::now();
        verify_mdoc_circuit_with_preprocessed_root(
            &proof,
            &statement,
            proof.stark_proof.commitments[0],
        )
        .expect("TS13 N=1 circuit verifies");
        verify_times.push(start.elapsed());
    }

    let report = Report {
        circuit: "ts13_n1_age_over_18_revocation",
        rayon_num_threads: std::env::var("RAYON_NUM_THREADS").ok(),
        iters,
        proof_bytes,
        prove_ms_median: median(&mut prove_times.clone()),
        prove_ms_all: prove_times.iter().map(Duration::as_millis).collect(),
        verify_ms_median: median(&mut verify_times),
        byte_breakdown: mdoc_proof_byte_breakdown(&proof),
        p4b_prove_profile,
        p4b_verify_profile: None,
    };
    println!("{}", serde_json::to_string_pretty(&report).unwrap());
}
