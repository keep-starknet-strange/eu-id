use criterion::Criterion;
use predicates::{Predicate, StarkPredicate};
use serde::Serialize;

pub trait BenchCase {
    type P: StarkPredicate;

    fn name(&self) -> &'static str;
    fn predicate(&self) -> &Self::P;
    fn public_input(&self) -> &<Self::P as Predicate>::PublicInput;
    fn private_input(&self) -> &<Self::P as Predicate>::PrivateInput;
}

pub fn run_bench<C>(c: &mut Criterion, case: &C)
where
    C: BenchCase,
    <C::P as StarkPredicate>::Proof: Serialize,
    <C::P as Predicate>::Error: std::fmt::Debug,
{
    let mut group = c.benchmark_group(case.name());

    group.bench_function("prove", |b| {
        b.iter(|| {
            case.predicate()
                .prove(case.public_input(), case.private_input())
                .unwrap()
        })
    });

    let proof = case
        .predicate()
        .prove(case.public_input(), case.private_input())
        .unwrap();

    group.bench_function("verify", |b| {
        b.iter(|| case.predicate().verify(&proof).unwrap())
    });

    let proof_bytes = bincode::serialize(&proof).unwrap();
    println!(
        "\n[{}] proof size: {} bytes ({:.1} KB)\n",
        case.name(),
        proof_bytes.len(),
        proof_bytes.len() as f64 / 1024.0,
    );

    group.finish();
}
