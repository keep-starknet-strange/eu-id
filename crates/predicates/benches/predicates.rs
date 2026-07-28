use criterion::{criterion_group, criterion_main, Criterion};

#[path = "common/harness.rs"]
mod harness;

#[path = "common/age.rs"]
mod age;

#[path = "common/nat.rs"]
mod nat;

fn bench_all(c: &mut Criterion) {
    harness::run_bench(c, &age::range_check_case());
    harness::run_nat_bench(c, &nat::greek_in_schengen_case());
}

criterion_group!(benches, bench_all);
criterion_main!(benches);
