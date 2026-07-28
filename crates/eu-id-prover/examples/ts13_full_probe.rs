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
use eu_id_prover::mdoc::{
    demo_mdoc_circuit_fixture_with_attributes, mdoc_proof_byte_breakdown, prove_mdoc_circuit,
    MdocCircuitProof, MdocDisclosureMode, MdocPublicStatement, MdocRequestedAttribute,
    MdocRevocationRangeWitness,
};
use eu_id_prover::ts13::{
    demo_ts13_revocation_inputs, ts13_default_root_policy_hash, verify_ts13_mdoc_public_statement,
    verify_ts13_no_revocation_ablation_public_statement,
};
use serde::Serialize;

const PROOF_ZSTD_LEVEL: i32 = 12;

#[derive(Serialize)]
struct Report {
    circuit: &'static str,
    benchmark_scope: &'static str,
    verification_root_source: &'static str,
    rayon_num_threads: Option<String>,
    iters: usize,
    proof_bytes: usize,
    proof_zstd12_bytes: usize,
    zstd12_ratio: f64,
    compress_us_median: u128,
    decode_us_median: u128,
    prove_ms_median: u128,
    prove_ms_all: Vec<u128>,
    verify_ms_median: u128,
    wire_verify_ms_median: u128,
    preprocessed_root: String,
    root_policy_hash: String,
    byte_breakdown: eu_id_prover::mdoc::MdocProofByteBreakdown,
    p4b_prove_profile: Option<String>,
    p4b_verify_profile: Option<String>,
}

fn median(times: &mut [Duration]) -> u128 {
    times.sort();
    times[times.len() / 2].as_millis()
}

fn median_us(times: &mut [Duration]) -> u128 {
    times.sort();
    times[times.len() / 2].as_micros()
}

fn hex_bytes(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn verify_benchmark_proof(
    proof: &MdocCircuitProof,
    statement: &MdocPublicStatement,
    revocation_enabled: bool,
) -> Result<(), eu_id_prover::Error> {
    if revocation_enabled {
        verify_ts13_mdoc_public_statement(proof, statement)
    } else {
        verify_ts13_no_revocation_ablation_public_statement(proof, statement)
    }
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
    let (revocation_statement, revocation_witness) =
        demo_ts13_revocation_inputs(&fixture.extracted.mso);
    // TS13_REVOCATION=0 proves the identical N=1 statement without the
    // revocation relations, isolating their cost.
    let revocation_enabled = std::env::var("TS13_REVOCATION").as_deref() != Ok("0");
    let statement = if revocation_enabled {
        fixture
            .statement
            .clone()
            .with_ts13_revocation((&revocation_statement).into())
            .with_ts13_revocation_range(MdocRevocationRangeWitness {
                id: revocation_witness.id,
                id_lo: revocation_witness.id_lo,
                id_hi: revocation_witness.id_hi,
            })
            .with_ts13_revocation_signature(revocation_witness.signature.clone())
    } else {
        fixture.statement.clone()
    };
    let public_statement = MdocPublicStatement::from_circuit(&statement);

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
    #[cfg(feature = "ec-coprocessor")]
    let p4b_prove_profile = proof.p4b_prove_profile().map(|p| format!("{p:?}"));
    #[cfg(not(feature = "ec-coprocessor"))]
    let p4b_prove_profile = None;
    let proof_bincode = bincode::serialize(&proof).expect("TS13 mdoc proof serializes");
    // Optional raw-proof dump for wire-compression experiments.
    if let Ok(path) = std::env::var("BENCH_DUMP_PROOF") {
        std::fs::write(&path, &proof_bincode).expect("proof dump writes");
    }
    let proof_bytes = proof_bincode.len();
    let actual_preprocessed_root = proof.stark_proof.commitments[0];
    let root_policy_hash = ts13_default_root_policy_hash();

    let mut compress_times = Vec::with_capacity(iters);
    let mut compressed_proof = None;
    for _ in 0..iters {
        let start = Instant::now();
        let next = zstd::bulk::compress(&proof_bincode, PROOF_ZSTD_LEVEL)
            .expect("TS13 proof zstd compression succeeds");
        compress_times.push(start.elapsed());
        black_box(&next);
        compressed_proof = Some(next);
    }
    let compressed_proof = compressed_proof.expect("at least one compression iteration ran");

    let mut decode_times = Vec::with_capacity(iters);
    for _ in 0..iters {
        let start = Instant::now();
        let raw = zstd::bulk::decompress(&compressed_proof, proof_bytes)
            .expect("TS13 proof zstd decompression succeeds");
        let decoded: MdocCircuitProof =
            bincode::deserialize(&raw).expect("TS13 proof bincode deserializes");
        decode_times.push(start.elapsed());
        black_box(decoded);
    }

    let mut verify_times = Vec::with_capacity(iters);
    for _ in 0..iters {
        let start = Instant::now();
        verify_benchmark_proof(&proof, &public_statement, revocation_enabled)
            .expect("TS13 N=1 circuit verifies under the bounded canonical root policy");
        verify_times.push(start.elapsed());
    }

    let mut wire_verify_times = Vec::with_capacity(iters);
    for _ in 0..iters {
        let start = Instant::now();
        let raw = zstd::bulk::decompress(&compressed_proof, proof_bytes)
            .expect("TS13 proof zstd decompression succeeds");
        let decoded: MdocCircuitProof =
            bincode::deserialize(&raw).expect("TS13 proof bincode deserializes");
        verify_benchmark_proof(&decoded, &public_statement, revocation_enabled)
            .expect("decoded TS13 N=1 circuit verifies under the bounded canonical root policy");
        wire_verify_times.push(start.elapsed());
    }

    let report = Report {
        circuit: if revocation_enabled {
            "ts13_n1_age_over_18_revocation"
        } else {
            "ts13_n1_age_over_18_no_revocation"
        },
        benchmark_scope: "synthetic_preextracted_circuit_core",
        verification_root_source:
            "canonical_reconstruction_from_public_statement_and_bounded_proof_shape",
        rayon_num_threads: std::env::var("RAYON_NUM_THREADS").ok(),
        iters,
        proof_bytes,
        proof_zstd12_bytes: compressed_proof.len(),
        zstd12_ratio: compressed_proof.len() as f64 / proof_bytes as f64,
        compress_us_median: median_us(&mut compress_times),
        decode_us_median: median_us(&mut decode_times),
        prove_ms_median: median(&mut prove_times.clone()),
        prove_ms_all: prove_times.iter().map(Duration::as_millis).collect(),
        verify_ms_median: median(&mut verify_times),
        wire_verify_ms_median: median(&mut wire_verify_times),
        preprocessed_root: hex_bytes(&actual_preprocessed_root.0),
        root_policy_hash: hex_bytes(&root_policy_hash),
        byte_breakdown: mdoc_proof_byte_breakdown(&proof),
        p4b_prove_profile,
        p4b_verify_profile: None,
    };
    println!("{}", serde_json::to_string_pretty(&report).unwrap());
}
