//! Laptop criterion benchmark for the isolated mdoc prover.
//!
//! Times prove and verify for the full isolated mdoc STARK over the deterministic
//! EUID mdoc profile-v2 fixture. The fixture is built once outside the measured
//! window, matching `identity_bench`.

use std::time::Duration;

use ciborium::value::Value;
use criterion::{criterion_group, criterion_main, Criterion};
use eu_id_prover::mdoc::{
    demo_mdoc_circuit_fixture_with_attributes, prove_mdoc_circuit, verify_mdoc_circuit,
    MdocDisclosureMode, MdocRequestedAttribute,
};

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn bench_mdoc(c: &mut Criterion) {
    let variants = mdoc_variants();
    let any_selected = variants.iter().any(|(name, _)| {
        should_register("mdoc/prove", name) || should_register("mdoc/verify", name)
    });
    if !any_selected {
        return;
    }

    let mut prove_group = c.benchmark_group("mdoc/prove");
    prove_group.sample_size(10);
    prove_group.warm_up_time(Duration::from_millis(500));
    for (name, fixture) in &variants {
        if should_register("mdoc/prove", name) {
            prove_group.bench_function(*name, |b| {
                b.iter(|| {
                    prove_mdoc_circuit(&fixture.extracted, &fixture.statement)
                        .expect("mdoc circuit proves")
                })
            });
        }
    }
    prove_group.finish();

    let mut verify_group = c.benchmark_group("mdoc/verify");
    verify_group.sample_size(10);
    verify_group.warm_up_time(Duration::from_millis(500));
    for (name, fixture) in &variants {
        if !should_register("mdoc/verify", name) {
            continue;
        }
        let proof = prove_mdoc_circuit(&fixture.extracted, &fixture.statement)
            .expect("mdoc circuit proves");
        let proof_bytes = bincode::serialize(&proof)
            .map(|bytes| bytes.len())
            .unwrap_or(0);
        verify_group.bench_function(*name, |b| {
            b.iter(|| verify_mdoc_circuit(&proof, &fixture.statement).expect("mdoc verifies"))
        });
        println!(
            "[mdoc/{name}] proof size: {} bytes ({:.1} KiB)",
            proof_bytes,
            proof_bytes as f64 / 1024.0,
        );
    }
    verify_group.finish();
}

criterion_group!(benches, bench_mdoc);
criterion_main!(benches);

fn mdoc_variants() -> Vec<(&'static str, eu_id_prover::mdoc::DemoMdocCircuitFixture)> {
    vec![
        (
            "N1",
            demo_mdoc_circuit_fixture_with_attributes(vec![MdocRequestedAttribute {
                element_identifier: "age_over_18".to_string(),
                mode: MdocDisclosureMode::ValueEquality(cbor(Value::Bool(true))),
            }]),
        ),
        (
            "N2",
            demo_mdoc_circuit_fixture_with_attributes(vec![
                MdocRequestedAttribute {
                    element_identifier: "birth_date".to_string(),
                    mode: MdocDisclosureMode::AgeOver,
                },
                MdocRequestedAttribute {
                    element_identifier: "nationality".to_string(),
                    mode: MdocDisclosureMode::Alpha2Set,
                },
            ]),
        ),
        (
            "N3",
            demo_mdoc_circuit_fixture_with_attributes(vec![
                MdocRequestedAttribute {
                    element_identifier: "birth_date".to_string(),
                    mode: MdocDisclosureMode::AgeOver,
                },
                MdocRequestedAttribute {
                    element_identifier: "nationality".to_string(),
                    mode: MdocDisclosureMode::Alpha2Set,
                },
                MdocRequestedAttribute {
                    element_identifier: "family_name".to_string(),
                    mode: MdocDisclosureMode::ValueEquality(cbor("Mustermann".into())),
                },
            ]),
        ),
        (
            "N4",
            demo_mdoc_circuit_fixture_with_attributes(vec![
                MdocRequestedAttribute {
                    element_identifier: "birth_date".to_string(),
                    mode: MdocDisclosureMode::AgeOver,
                },
                MdocRequestedAttribute {
                    element_identifier: "nationality".to_string(),
                    mode: MdocDisclosureMode::Alpha2Set,
                },
                MdocRequestedAttribute {
                    element_identifier: "family_name".to_string(),
                    mode: MdocDisclosureMode::ValueEquality(cbor("Mustermann".into())),
                },
                MdocRequestedAttribute {
                    element_identifier: "age_over_18".to_string(),
                    mode: MdocDisclosureMode::ValueEquality(cbor(Value::Bool(true))),
                },
            ]),
        ),
    ]
}

fn cbor(value: Value) -> Vec<u8> {
    let mut out = Vec::new();
    ciborium::ser::into_writer(&value, &mut out).expect("bench cbor serializes");
    out
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
