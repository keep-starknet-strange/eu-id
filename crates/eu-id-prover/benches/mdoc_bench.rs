//! Laptop criterion benchmark for the isolated mdoc prover.
//!
//! Times prove and verify for the full isolated mdoc STARK over the deterministic
//! EUID mdoc profile-v1 fixture. The fixture is built once outside the measured
//! window, matching `identity_bench`.

use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};
use eu_id_prover::mdoc::{demo_mdoc_circuit_fixture, prove_mdoc_circuit, verify_mdoc_circuit};

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn bench_mdoc(c: &mut Criterion) {
    let fixture = demo_mdoc_circuit_fixture();
    let prove_selected = should_register("mdoc", "prove");
    let verify_selected = should_register("mdoc", "verify");
    if !prove_selected && !verify_selected {
        return;
    }

    let mut group = c.benchmark_group("mdoc");
    group.sample_size(10);
    group.warm_up_time(Duration::from_millis(500));

    if prove_selected {
        group.bench_function("prove", |b| {
            b.iter(|| {
                prove_mdoc_circuit(&fixture.extracted, &fixture.statement)
                    .expect("mdoc circuit proves")
            })
        });
    }

    if verify_selected {
        let proof = prove_mdoc_circuit(&fixture.extracted, &fixture.statement)
            .expect("mdoc circuit proves");
        let proof_bytes = bincode::serialize(&proof)
            .map(|bytes| bytes.len())
            .unwrap_or(0);
        group.bench_function("verify", |b| {
            b.iter(|| verify_mdoc_circuit(&proof, &fixture.statement).expect("mdoc verifies"))
        });
        println!(
            "[mdoc] proof size: {} bytes ({:.1} KiB)",
            proof_bytes,
            proof_bytes as f64 / 1024.0,
        );
    }

    group.finish();
}

criterion_group!(benches, bench_mdoc);
criterion_main!(benches);

fn should_register(group: &str, bench: &str) -> bool {
    let full_name = format!("{group}/{bench}");
    let filters: Vec<String> = std::env::args()
        .skip(1)
        .filter(|arg| arg != "--bench" && !arg.starts_with('-'))
        .collect();
    filters.is_empty()
        || filters
            .iter()
            .any(|filter| full_name.contains(filter) || filter.contains(&full_name))
}
