use criterion::{criterion_group, criterion_main};

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[path = "common/longfellow_equiv.rs"]
mod longfellow_equiv;

criterion_group!(benches, longfellow_equiv::bench_longfellow_equiv);
criterion_main!(benches);
