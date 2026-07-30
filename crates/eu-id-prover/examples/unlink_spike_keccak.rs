//! WO-U0b: Keccak-service scaling spike.

mod unlink_spike_support;

#[derive(Clone, Copy)]
struct Point {
    label: u32,
    dummy_jobs: usize,
}

fn main() {
    let point = parse_point();
    unlink_spike_support::run_on_prover_pool("unlink-spike-keccak", move || run(point));
}

fn parse_point() -> Point {
    let mut args = std::env::args().skip(1);
    let value = match (args.next().as_deref(), args.next(), args.next()) {
        (Some("--point"), Some(value), None) => value,
        _ => panic!("usage: unlink_spike_keccak --point 37|100|202"),
    };
    match value.as_str() {
        "37" => Point {
            label: 37,
            dummy_jobs: 0,
        },
        "100" => Point {
            label: 100,
            dummy_jobs: 13,
        },
        "202" => Point {
            label: 202,
            dummy_jobs: 33,
        },
        _ => panic!("--point must be 37, 100, or 202"),
    }
}

fn run(point: Point) {
    use eu_id_prover::mdoc::{
        prove_mdoc_circuit_keccak_scale_spike, verify_mdoc_circuit,
        verify_mdoc_circuit_keccak_scale_spike_fresh,
    };

    let fixture = unlink_spike_support::fixture();
    let actual_permutations =
        unlink_spike_support::keccak_permutations_with_dummy_jobs(point.dummy_jobs);
    let mismatched_dummy_jobs = match point.dummy_jobs {
        0 => 13,
        13 => 33,
        33 => 13,
        _ => unreachable!("point parser permits only work-order dummy-job counts"),
    };
    let measurement = unlink_spike_support::measure(
        &fixture,
        |extracted, statement| {
            prove_mdoc_circuit_keccak_scale_spike(extracted, statement, point.dummy_jobs)
        },
        |proof, statement| {
            verify_mdoc_circuit_keccak_scale_spike_fresh(proof, statement, point.dummy_jobs)
        },
        |proof, statement| {
            if point.dummy_jobs == 0 {
                assert!(
                    verify_mdoc_circuit(proof, statement).is_ok(),
                    "zero-job spike proof must equal the production protocol shape"
                );
            }
            verify_mdoc_circuit_keccak_scale_spike_fresh(proof, statement, mismatched_dummy_jobs)
                .is_err()
        },
    );

    println!(
        "UNLINK_SPIKE_KECCAK zero_knowledge=false rayon_threads={} rayon_worker_stack_bytes={} point={} actual_perms={} dummy_jobs={} round_log_size={} keccak_scale_{}_prove_ms={} keccak_scale_{}_verify_ms={} keccak_scale_{}_proof_bytes={} keccak_scale_{}_bzip2_wire_bytes={} fresh_tree0_ms={} fresh_stark_verify_ms={}",
        rayon::current_num_threads(),
        unlink_spike_support::PROVER_WORKER_STACK_BYTES,
        point.label,
        actual_permutations,
        point.dummy_jobs,
        unlink_spike_support::round_log_size(actual_permutations),
        point.label,
        measurement.prove_ms,
        point.label,
        measurement.verify_ms,
        point.label,
        measurement.raw_proof_bytes,
        point.label,
        measurement.bzip2_wire_bytes,
        measurement.tree0_ms,
        measurement.stark_verify_ms,
    );
}
