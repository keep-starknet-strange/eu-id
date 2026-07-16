//! Laptop criterion benchmark for the isolated mdoc prover.
//!
//! Times prove and verify for the full isolated mdoc STARK over the deterministic
//! EUID mdoc profile-v2 fixture. The fixture is built once outside the measured
//! window, matching `identity_bench`.

use std::time::Duration;

use ciborium::value::Value;
use criterion::{criterion_group, criterion_main, Criterion};
use eu_id_prover::mdoc::{
    demo_mdoc_circuit_fixture_with_attributes, extract_pid_mdoc, mdoc_longfellow_parity_pcs_config,
    mdoc_production_pcs_config, prove_mdoc_circuit_with_pcs_config,
    verify_mdoc_circuit_with_pcs_config, ExtractedPidMdoc, MdocCircuitStatement,
    MdocDeviceAuthenticationProfile, MdocDisclosureMode, MdocPidRequest, MdocRequestedAttribute,
};
use eu_id_prover::{Date, Policy};
use stwo::core::pcs::PcsConfig;
use stwo_p256::types::{AffinePoint, U256};

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn bench_mdoc(c: &mut Criterion) {
    let cases = mdoc_cases();
    let any_selected = cases.iter().any(|case| {
        should_register("mdoc/prove", case.name) || should_register("mdoc/verify", case.name)
    });
    if !any_selected {
        return;
    }

    let mut prove_group = c.benchmark_group("mdoc/prove");
    prove_group.sample_size(10);
    prove_group.warm_up_time(Duration::from_millis(500));
    for case in &cases {
        if should_register("mdoc/prove", case.name) {
            prove_group.bench_function(case.name, |b| {
                b.iter(|| {
                    prove_mdoc_circuit_with_pcs_config(
                        &case.extracted,
                        &case.statement,
                        case.config,
                    )
                    .expect("mdoc circuit proves")
                })
            });
        }
    }
    prove_group.finish();

    let mut verify_group = c.benchmark_group("mdoc/verify");
    verify_group.sample_size(10);
    verify_group.warm_up_time(Duration::from_millis(500));
    for case in &cases {
        if !should_register("mdoc/verify", case.name) {
            continue;
        }
        let proof =
            prove_mdoc_circuit_with_pcs_config(&case.extracted, &case.statement, case.config)
                .expect("mdoc circuit proves");
        let proof_bytes = bincode::serialize(&proof)
            .map(|bytes| bytes.len())
            .unwrap_or(0);
        verify_group.bench_function(case.name, |b| {
            b.iter(|| {
                verify_mdoc_circuit_with_pcs_config(&proof, &case.statement, case.config)
                    .expect("mdoc verifies")
            })
        });
        println!(
            "[mdoc/{}] security_bits={} proof size: {} bytes ({:.1} KiB)",
            case.name,
            case.config.security_bits(),
            proof_bytes,
            proof_bytes as f64 / 1024.0,
        );
    }
    verify_group.finish();
}

criterion_group!(benches, bench_mdoc);
criterion_main!(benches);

struct MdocBenchCase {
    name: &'static str,
    extracted: ExtractedPidMdoc,
    statement: MdocCircuitStatement,
    config: PcsConfig,
}

fn mdoc_cases() -> Vec<MdocBenchCase> {
    let prod = mdoc_production_pcs_config();
    let parity = mdoc_longfellow_parity_pcs_config();
    let mut cases = vec![
        demo_case(
            "N1",
            vec![MdocRequestedAttribute {
                element_identifier: "age_over_18".to_string(),
                mode: MdocDisclosureMode::ValueEquality(cbor(Value::Bool(true))),
            }],
            prod,
        ),
        demo_case(
            "N2",
            vec![
                MdocRequestedAttribute {
                    element_identifier: "birth_date".to_string(),
                    mode: MdocDisclosureMode::AgeOver,
                },
                MdocRequestedAttribute {
                    element_identifier: "nationality".to_string(),
                    mode: MdocDisclosureMode::Alpha2Set,
                },
            ],
            prod,
        ),
        demo_case(
            "N3",
            vec![
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
            ],
            prod,
        ),
        demo_case(
            "N4",
            vec![
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
            ],
            prod,
        ),
    ];
    cases.extend(longfellow_cases(prod, parity));
    cases
}

fn demo_case(
    name: &'static str,
    attributes: Vec<MdocRequestedAttribute>,
    config: PcsConfig,
) -> MdocBenchCase {
    let fixture = demo_mdoc_circuit_fixture_with_attributes(attributes);
    MdocBenchCase {
        name,
        extracted: fixture.extracted,
        statement: fixture.statement,
        config,
    }
}

fn longfellow_cases(prod: PcsConfig, parity: PcsConfig) -> Vec<MdocBenchCase> {
    let mdl_n1 = vec![MdocRequestedAttribute {
        element_identifier: "age_over_18".to_string(),
        mode: MdocDisclosureMode::ValueEquality(cbor(Value::Bool(true))),
    }];
    let mdl_n2 = vec![
        MdocRequestedAttribute {
            element_identifier: "age_over_18".to_string(),
            mode: MdocDisclosureMode::ValueEquality(cbor(Value::Bool(true))),
        },
        MdocRequestedAttribute {
            element_identifier: "birth_date".to_string(),
            mode: MdocDisclosureMode::AgeOver,
        },
    ];
    let euav_n1 = vec![MdocRequestedAttribute {
        element_identifier: "age_over_18".to_string(),
        mode: MdocDisclosureMode::ValueEquality(cbor(Value::Bool(true))),
    }];
    vec![
        longfellow_case(
            "longfellow_mdl3_N1_prod128",
            longfellow_mdl3(),
            mdl_n1.clone(),
            prod,
        ),
        longfellow_case(
            "longfellow_mdl3_N1_parity110",
            longfellow_mdl3(),
            mdl_n1,
            parity,
        ),
        longfellow_case(
            "longfellow_mdl3_N2_prod128",
            longfellow_mdl3(),
            mdl_n2.clone(),
            prod,
        ),
        longfellow_case(
            "longfellow_mdl3_N2_parity110",
            longfellow_mdl3(),
            mdl_n2,
            parity,
        ),
        longfellow_case(
            "longfellow_euav11_N1_prod128",
            longfellow_euav11(),
            euav_n1.clone(),
            prod,
        ),
        longfellow_case(
            "longfellow_euav11_N1_parity110",
            longfellow_euav11(),
            euav_n1,
            parity,
        ),
    ]
}

struct LongfellowVector {
    mdoc: &'static [u8],
    transcript: &'static [u8],
    issuer_pk_json: &'static str,
    now: &'static str,
    doctype: &'static str,
    namespace: &'static str,
}

fn longfellow_mdl3() -> LongfellowVector {
    LongfellowVector {
        mdoc: include_bytes!("../tests/vectors/longfellow_mdl3/mdoc.cbor"),
        transcript: include_bytes!("../tests/vectors/longfellow_mdl3/transcript.bin"),
        issuer_pk_json: include_str!("../tests/vectors/longfellow_mdl3/issuer_pk.json"),
        now: include_str!("../tests/vectors/longfellow_mdl3/now.txt"),
        doctype: "org.iso.18013.5.1.mDL",
        namespace: "org.iso.18013.5.1",
    }
}

fn longfellow_euav11() -> LongfellowVector {
    LongfellowVector {
        mdoc: include_bytes!("../tests/vectors/longfellow_euav11/mdoc.cbor"),
        transcript: include_bytes!("../tests/vectors/longfellow_euav11/transcript.bin"),
        issuer_pk_json: include_str!("../tests/vectors/longfellow_euav11/issuer_pk.json"),
        now: include_str!("../tests/vectors/longfellow_euav11/now.txt"),
        doctype: "eu.europa.ec.av.1",
        namespace: "eu.europa.ec.av.1",
    }
}

fn longfellow_case(
    name: &'static str,
    vector: LongfellowVector,
    attributes: Vec<MdocRequestedAttribute>,
    config: PcsConfig,
) -> MdocBenchCase {
    let request = MdocPidRequest {
        doctype: vector.doctype.to_string(),
        namespace: vector.namespace.to_string(),
        attributes,
        birth_date_element: "birth_date".to_string(),
        nationality_element: "nationality".to_string(),
        session_transcript: vector.transcript.to_vec(),
        trusted_issuer_certificates: Vec::new(),
        trusted_issuer_public_keys: vec![longfellow_issuer_public_key(vector.issuer_pk_json)],
        device_authentication_profile: MdocDeviceAuthenticationProfile::LongfellowLegacy,
    };
    let extracted = extract_pid_mdoc(vector.mdoc, &request).expect("Longfellow vector extracts");
    let statement = MdocCircuitStatement::from_extracted(&extracted, policy_from_now(vector.now))
        .expect("Longfellow statement builds");
    MdocBenchCase {
        name,
        extracted,
        statement,
        config,
    }
}

fn cbor(value: Value) -> Vec<u8> {
    let mut out = Vec::new();
    ciborium::ser::into_writer(&value, &mut out).expect("bench cbor serializes");
    out
}

fn longfellow_issuer_public_key(json: &str) -> AffinePoint {
    let value: serde_json::Value = serde_json::from_str(json).expect("issuer_pk.json parses");
    AffinePoint {
        x: U256(hex_32(value["x"].as_str().expect("issuer x hex"))),
        y: U256(hex_32(value["y"].as_str().expect("issuer y hex"))),
    }
}

fn hex_32(hex: &str) -> [u8; 32] {
    let hex = hex.strip_prefix("0x").unwrap_or(hex);
    assert_eq!(hex.len(), 64, "expected 32-byte hex string");
    let mut out = [0u8; 32];
    for (index, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&hex[index * 2..index * 2 + 2], 16).expect("hex byte parses");
    }
    out
}

fn policy_from_now(now: &str) -> Policy {
    let bytes = now.trim().as_bytes();
    Policy {
        current_date: Date {
            year: std::str::from_utf8(&bytes[0..4])
                .expect("year utf8")
                .parse()
                .expect("year parses"),
            month: std::str::from_utf8(&bytes[5..7])
                .expect("month utf8")
                .parse()
                .expect("month parses"),
            day: std::str::from_utf8(&bytes[8..10])
                .expect("day utf8")
                .parse()
                .expect("day parses"),
        },
        min_age_years: 18,
        accepted_nationalities: Vec::new(),
        accepted_nationalities_alpha2: Vec::new(),
    }
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
