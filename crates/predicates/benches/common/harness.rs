use criterion::Criterion;
use predicates::age::strategy::AgeCheckStrategy;
use predicates::nat::NationalityPredicate;
use predicates::{AgeRangeCheck, DateOfBirth, NatPrivateInput, NatPublicInput, PublicInput};
use stwo::core::pcs::PcsConfig;

pub struct BenchCase {
    pub name: &'static str,
    pub strategy: AgeCheckStrategy,
    pub public: PublicInput,
    pub dob: DateOfBirth,
}

pub fn run_bench(c: &mut Criterion, case: &BenchCase) {
    let mut group = c.benchmark_group(case.name);

    let proof_bytes = match case.strategy {
        AgeCheckStrategy::RangeCheck => {
            group.bench_function("prove", |b| {
                b.iter(|| {
                    AgeRangeCheck::new(PcsConfig::default())
                        .prove(&case.public, &case.dob)
                        .unwrap()
                })
            });
            let proof = AgeRangeCheck::new(PcsConfig::default())
                .prove(&case.public, &case.dob)
                .unwrap();
            group.bench_function("verify", |b| {
                b.iter(|| {
                    AgeRangeCheck::new(PcsConfig::default())
                        .verify(&proof)
                        .unwrap()
                })
            });
            bincode::serialize(&proof).unwrap()
        }
    };

    println!(
        "\n[{}] proof size: {} bytes ({:.1} KB)\n",
        case.name,
        proof_bytes.len(),
        proof_bytes.len() as f64 / 1024.0,
    );

    group.finish();
}

pub struct NatBenchCase {
    pub name: &'static str,
    pub public: NatPublicInput,
    pub private: NatPrivateInput,
}

pub fn run_nat_bench(c: &mut Criterion, case: &NatBenchCase) {
    let mut group = c.benchmark_group(case.name);

    group.bench_function("prove", |b| {
        b.iter(|| {
            NationalityPredicate::new(PcsConfig::default())
                .prove(&case.public, &case.private)
                .unwrap()
        })
    });

    let proof = NationalityPredicate::new(PcsConfig::default())
        .prove(&case.public, &case.private)
        .unwrap();

    group.bench_function("verify", |b| {
        b.iter(|| {
            NationalityPredicate::new(PcsConfig::default())
                .verify(&proof)
                .unwrap()
        })
    });

    let proof_bytes = bincode::serialize(&proof).unwrap();
    println!(
        "\n[{}] proof size: {} bytes ({:.1} KB)\n",
        case.name,
        proof_bytes.len(),
        proof_bytes.len() as f64 / 1024.0,
    );

    group.finish();
}
