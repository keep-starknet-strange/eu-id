use criterion::{criterion_group, criterion_main, Criterion};

#[path = "common/harness.rs"]
mod harness;

#[path = "common/age.rs"]
mod age;

fn bench_all(c: &mut Criterion) {
    harness::run_bench(c, &age::bit_decomposition_case());
    harness::run_bench(c, &age::range_check_case());
}

criterion_group!(benches, bench_all);
criterion_main!(benches);
