//! Laptop criterion benchmark for the combined identity prover.
//!
//! Times prove and verify for each standalone component — P256 ECDSA, SHA-256,
//! the age predicate, the nationality predicate — and for the full combined
//! STARK (`pipeline`), so the per-stage breakdown and the P256-vs-combined
//! comparison fall straight out of the report. The stage definitions are shared
//! with the peak-memory + JSON report driver (`examples/bench_report.rs`) via
//! `common/stages.rs`, so both measure the identical proving paths.
//!
//! All inputs (witnesses, the P256 draft) are built once, outside the measured
//! window, so each benchmark times only the STARK prove / verify.
//!
//! ```bash
//! cargo bench -p eu-id-prover                       # single-threaded (baseline)
//! cargo bench -p eu-id-prover --features parallel   # Stwo rayon paths on
//! ```

use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};
use eu_id_prover::generator::IssuerKey;
use eu_id_prover::{fixtures, prove_identity};

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[path = "common/stages.rs"]
mod stages;

fn bench_identity(c: &mut Criterion) {
    // One honest over-18 credential drives every stage. Proving cost is
    // independent of the credential's values, so a single fixture is enough.
    let fixture = fixtures::valid_over_18();
    let witness = fixture.pipeline_witness();

    bench_stage(
        c,
        "sha",
        || {
            stages::prove_sha(&witness);
        },
        || {
            let proof = stages::prove_sha(&witness);
            let proof_bytes = stages::sha_proof_bytes(&proof);
            (move || stages::verify_sha(&proof), proof_bytes)
        },
    );

    bench_stage(
        c,
        "p256",
        || {
            stages::prove_p256(&witness);
        },
        || {
            let proof = stages::prove_p256(&witness);
            let instances = stages::p256_instances(&proof);
            let proof_bytes = stages::p256_proof_bytes(&proof);
            (move || stages::verify_p256(&proof, &instances), proof_bytes)
        },
    );

    bench_stage(
        c,
        "age",
        || {
            stages::prove_age(&witness);
        },
        || {
            let proof = stages::prove_age(&witness);
            let proof_bytes = stages::age_proof_bytes(&proof);
            (move || stages::verify_age(&proof), proof_bytes)
        },
    );

    bench_stage(
        c,
        "nat",
        || {
            stages::prove_nat(&witness);
        },
        || {
            let proof = stages::prove_nat(&witness);
            let proof_bytes = stages::nat_proof_bytes(&proof);
            (move || stages::verify_nat(&proof), proof_bytes)
        },
    );

    bench_stage(
        c,
        "pipeline",
        || {
            stages::prove_pipeline(&witness);
        },
        || {
            let proof = stages::prove_pipeline(&witness);
            let instances = stages::pipeline_instances(&proof);
            let proof_bytes = stages::pipeline_proof_bytes(&proof);
            (
                move || stages::verify_pipeline(&proof, &instances),
                proof_bytes,
            )
        },
    );

    if should_register("identity_e2e", "prove_identity") {
        let mut group = c.benchmark_group("identity_e2e");
        group.sample_size(10);
        group.warm_up_time(Duration::from_millis(500));
        let issuer = IssuerKey::demo();
        group.bench_function("prove_identity", |b| {
            b.iter(|| {
                prove_identity(&fixture.signed.credential, &issuer, &fixture.policy)
                    .expect("identity proof generates")
            })
        });
        group.finish();
    }
}

criterion_group!(benches, bench_identity);
criterion_main!(benches);

fn bench_stage<P, V, VF>(c: &mut Criterion, name: &'static str, prove: P, verify_factory: VF)
where
    P: Fn(),
    V: Fn(),
    VF: FnOnce() -> (V, usize),
{
    let prove_selected = should_register(name, "prove");
    let verify_selected = should_register(name, "verify");
    if !prove_selected && !verify_selected {
        return;
    }

    let mut group = c.benchmark_group(name);
    group.sample_size(10);
    group.warm_up_time(Duration::from_millis(500));

    if prove_selected {
        group.bench_function("prove", |b| b.iter(&prove));
    }

    if verify_selected {
        let (verify, proof_bytes) = verify_factory();
        group.bench_function("verify", |b| b.iter(&verify));
        println!(
            "[{name}] proof size: {} bytes ({:.1} KiB)",
            proof_bytes,
            proof_bytes as f64 / 1024.0,
        );
    }

    group.finish();
}

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
