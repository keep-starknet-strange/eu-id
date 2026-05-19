use criterion::{criterion_group, criterion_main, Criterion};

#[path = "common/harness.rs"]
mod harness;

#[path = "common/age.rs"]
mod age;

use age::AgeBitDecomposition;
use harness::run_bench;

fn bench_all(c: &mut Criterion) {
    run_bench(c, &AgeBitDecomposition::new());
}

criterion_group!(benches, bench_all);
criterion_main!(benches);
