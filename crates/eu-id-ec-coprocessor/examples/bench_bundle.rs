use std::time::{Duration, Instant};

use ecdsa::signature::Signer;
use eu_id_ec_coprocessor::ecdsa::{
    generate_witness, implemented_circuit_family_labels,
    prove_implemented_circuit_bundle_unchecked_profiled,
    verify_implemented_circuit_bundle_profiled, EcdsaInput, ImplementedCircuitBundle,
    ImplementedCircuitProveProfile, ImplementedCircuitVerifyProfile,
};
#[cfg(feature = "count-ops")]
use eu_id_ec_coprocessor::field::{fp_add_count, fp_mul_count, reset_fp_mul_count};
use p256::ecdsa::{Signature, SigningKey};
use sha2::{Digest as _, Sha256};

const RUNS: usize = 5;
const BENCH_SEED: [u8; 32] = [7u8; 32];

fn main() {
    let input = signed_input();
    let mut samples = Vec::with_capacity(RUNS);

    for _ in 0..RUNS {
        samples.push(run_once(&input));
    }

    samples.sort_by_key(|sample| sample.total);
    let median = &samples[RUNS / 2];
    let summary = BundleShape::from_bundle(&median.bundle);

    println!("s4_lite_bundle_bench runs={RUNS}");
    println!("witness_ms={:.3}", ms(median.witness));
    println!("prove_ms={:.3}", ms(median.prove));
    println!("serialize_ms={:.3}", ms(median.serialize));
    println!("verify_ms={:.3}", ms(median.verify));
    println!("total_ms={:.3}", ms(median.total));
    println!("bundle_bytes={}", median.bundle_bytes);
    println!(
        "prove_witness_check_ms={:.3} prove_circuit_build_ms={:.3} prove_ligero_row_encode_ms={:.3} prove_ligero_merkle_ms={:.3}",
        ms(median.prove_profile.witness_check),
        ms(median.prove_profile.circuit_build),
        ms(median.prove_profile.ligero_row_encode),
        ms(median.prove_profile.ligero_merkle_build),
    );
    println!(
        "prove_ligero_proximity_ms={:.3} prove_ligero_openings_ms={:.3} prove_sumcheck_ms={:.3} ligero_rows={} committed_values={} committed_nonzero_values={} max_row_nonzero_values={}",
        ms(median.prove_profile.ligero_proximity_claim),
        ms(median.prove_profile.ligero_openings),
        ms(median.prove_profile.sumcheck),
        median.prove_profile.ligero_rows,
        median.prove_profile.committed_values,
        median.prove_profile.committed_nonzero_values,
        median.prove_profile.max_row_nonzero_values,
    );
    println!(
        "verify_setup_ms={:.3} verify_ligero_proximity_ms={:.3} verify_systematic_reconstruct_ms={:.3} verify_sumcheck_ms={:.3} verify_input_claims_ms={:.3} verify_consistency_ms={:.3}",
        ms(median.verify_profile.setup),
        ms(median.verify_profile.ligero_proximity),
        ms(median.verify_profile.systematic_reconstruct),
        ms(median.verify_profile.sumcheck),
        ms(median.verify_profile.input_claims),
        ms(median.verify_profile.consistency),
    );
    let labels = implemented_circuit_family_labels().expect("static implemented circuits build");
    println!(
        "prove_sumcheck_by_family_ms={}",
        family_timings(&labels, &median.prove_profile.sumcheck_by_family)
    );
    println!(
        "verify_sumcheck_by_family_ms={}",
        family_timings(&labels, &median.verify_profile.sumcheck_by_family)
    );
    println!(
        "sumcheck_rounds_total={} sumcheck_rounds_max_per_layer={}",
        summary.sumcheck_rounds_total, summary.sumcheck_rounds_max_per_layer
    );
    println!(
        "ligero_systematic_columns={} ligero_proximity_columns={} ligero_combined_row_felts={}",
        summary.systematic_columns, summary.proximity_columns, summary.combined_row_felts
    );
    #[cfg(feature = "count-ops")]
    println!(
        "field_muls_witness={} field_muls_prove={} field_muls_serialize={} field_muls_verify={}",
        median.witness_muls, median.prove_muls, median.serialize_muls, median.verify_muls
    );
    #[cfg(feature = "count-ops")]
    println!(
        "field_adds_witness={} field_adds_prove={} field_adds_serialize={} field_adds_verify={}",
        median.witness_adds, median.prove_adds, median.serialize_adds, median.verify_adds
    );
}

struct Sample {
    witness: Duration,
    prove: Duration,
    serialize: Duration,
    verify: Duration,
    total: Duration,
    bundle_bytes: usize,
    bundle: ImplementedCircuitBundle,
    prove_profile: ImplementedCircuitProveProfile,
    verify_profile: ImplementedCircuitVerifyProfile,
    #[cfg(feature = "count-ops")]
    witness_muls: u64,
    #[cfg(feature = "count-ops")]
    witness_adds: u64,
    #[cfg(feature = "count-ops")]
    prove_muls: u64,
    #[cfg(feature = "count-ops")]
    prove_adds: u64,
    #[cfg(feature = "count-ops")]
    serialize_muls: u64,
    #[cfg(feature = "count-ops")]
    serialize_adds: u64,
    #[cfg(feature = "count-ops")]
    verify_muls: u64,
    #[cfg(feature = "count-ops")]
    verify_adds: u64,
}

fn run_once(input: &EcdsaInput) -> Sample {
    let total_start = Instant::now();

    let start = Instant::now();
    #[cfg(feature = "count-ops")]
    reset_fp_mul_count();
    let witness = generate_witness(input).expect("signed fixture generates a witness");
    let witness_duration = start.elapsed();
    #[cfg(feature = "count-ops")]
    let witness_muls = fp_mul_count();
    #[cfg(feature = "count-ops")]
    let witness_adds = fp_add_count();

    let start = Instant::now();
    #[cfg(feature = "count-ops")]
    reset_fp_mul_count();
    let (bundle, prove_profile) =
        prove_implemented_circuit_bundle_unchecked_profiled(input, &witness, BENCH_SEED)
            .expect("bundle proof accepts fixture");
    let prove_duration = start.elapsed();
    #[cfg(feature = "count-ops")]
    let prove_muls = fp_mul_count();
    #[cfg(feature = "count-ops")]
    let prove_adds = fp_add_count();

    let start = Instant::now();
    #[cfg(feature = "count-ops")]
    reset_fp_mul_count();
    let serialized = bincode::serialize(&bundle).expect("bundle serializes");
    let serialize_duration = start.elapsed();
    #[cfg(feature = "count-ops")]
    let serialize_muls = fp_mul_count();
    #[cfg(feature = "count-ops")]
    let serialize_adds = fp_add_count();

    let start = Instant::now();
    #[cfg(feature = "count-ops")]
    reset_fp_mul_count();
    let (_, verify_profile) =
        verify_implemented_circuit_bundle_profiled(input, &bundle, BENCH_SEED)
            .expect("bundle verifies");
    let verify_duration = start.elapsed();
    #[cfg(feature = "count-ops")]
    let verify_muls = fp_mul_count();
    #[cfg(feature = "count-ops")]
    let verify_adds = fp_add_count();

    Sample {
        witness: witness_duration,
        prove: prove_duration,
        serialize: serialize_duration,
        verify: verify_duration,
        total: total_start.elapsed(),
        bundle_bytes: serialized.len(),
        bundle,
        prove_profile,
        verify_profile,
        #[cfg(feature = "count-ops")]
        witness_muls,
        #[cfg(feature = "count-ops")]
        witness_adds,
        #[cfg(feature = "count-ops")]
        prove_muls,
        #[cfg(feature = "count-ops")]
        prove_adds,
        #[cfg(feature = "count-ops")]
        serialize_muls,
        #[cfg(feature = "count-ops")]
        serialize_adds,
        #[cfg(feature = "count-ops")]
        verify_muls,
        #[cfg(feature = "count-ops")]
        verify_adds,
    }
}

struct BundleShape {
    sumcheck_rounds_total: usize,
    sumcheck_rounds_max_per_layer: usize,
    systematic_columns: usize,
    proximity_columns: usize,
    combined_row_felts: usize,
}

impl BundleShape {
    fn from_bundle(bundle: &ImplementedCircuitBundle) -> Self {
        let mut sumcheck_rounds_total = 0;
        let mut sumcheck_rounds_max_per_layer = 0;
        let systematic_columns = bundle.openings.len();
        let proximity_columns = bundle.proximity_openings.len();
        let combined_row_felts = bundle.proximity_claim.combined_row.len();

        for entry in &bundle.entries {
            for layer in &entry.proof.layers {
                sumcheck_rounds_total += layer.rounds.len();
                sumcheck_rounds_max_per_layer =
                    sumcheck_rounds_max_per_layer.max(layer.rounds.len());
            }
        }

        Self {
            sumcheck_rounds_total,
            sumcheck_rounds_max_per_layer,
            systematic_columns,
            proximity_columns,
            combined_row_felts,
        }
    }
}

fn family_timings(labels: &[&'static [u8]], timings: &[Duration]) -> String {
    labels
        .iter()
        .zip(timings)
        .map(|(label, timing)| {
            format!(
                "{}:{:.3}",
                std::str::from_utf8(label).expect("labels are ASCII"),
                ms(*timing)
            )
        })
        .collect::<Vec<_>>()
        .join(",")
}

fn signed_input() -> EcdsaInput {
    let signing_key = SigningKey::from_bytes((&[7u8; 32]).into()).unwrap();
    let message = b"eu-id s4 bench bundle";
    let digest: [u8; 32] = Sha256::digest(message).into();
    let signature: Signature = signing_key.sign(message);
    let public_key = signing_key.verifying_key().to_encoded_point(false);
    let mut qx = [0u8; 32];
    let mut qy = [0u8; 32];
    qx.copy_from_slice(public_key.x().unwrap());
    qy.copy_from_slice(public_key.y().unwrap());

    EcdsaInput {
        z: digest,
        r: signature.r().to_bytes().into(),
        s: signature.s().to_bytes().into(),
        qx,
        qy,
    }
}

fn ms(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1_000.0
}
