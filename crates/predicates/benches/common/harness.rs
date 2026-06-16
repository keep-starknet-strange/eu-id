use criterion::Criterion;
use predicates::{age, AgeCheckStrategy, AgeProof, DateOfBirth, PublicInput};

pub struct BenchCase {
    pub name: &'static str,
    pub strategy: AgeCheckStrategy,
    pub public: PublicInput,
    pub dob: DateOfBirth,
}

pub fn run_bench(c: &mut Criterion, case: &BenchCase) {
    let mut group = c.benchmark_group(case.name);

    group.bench_function("prove", |b| {
        b.iter(|| age::prove(&case.public, &case.dob, case.strategy).unwrap())
    });

    let proof = age::prove(&case.public, &case.dob, case.strategy).unwrap();

    group.bench_function("verify", |b| b.iter(|| age::verify(&proof).unwrap()));

    let proof_bytes = match &proof {
        AgeProof::BitDecomposition(p) => bincode::serialize(p).unwrap(),
        AgeProof::RangeCheck(p) => bincode::serialize(p).unwrap(),
    };
    println!(
        "\n[{}] proof size: {} bytes ({:.1} KB)\n",
        case.name,
        proof_bytes.len(),
        proof_bytes.len() as f64 / 1024.0,
    );

    group.finish();
}
