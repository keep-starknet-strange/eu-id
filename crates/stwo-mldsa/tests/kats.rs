//! NIST ACVP ML-DSA-65 sigVer known-answer tests.
//!
//! Vendored subset: `tests/vectors/mldsa65_sigver.json` (ACVP-Server master
//! `15c0f3d`, ML-DSA-sigVer-FIPS204, group 3 = external + pure). See the
//! sibling `README.md` for provenance. Every case's `testPassed` must equal our
//! reference's verdict — both the valid cases (accept) and the invalid ones
//! (reject: mutated z / c̃ / hint / message).
//!
//! The file is vendored, so these tests do not use the network.

use serde::Deserialize;
use stwo_mldsa::profile::ML_DSA_65;
use stwo_mldsa::reference::verify::verify_internals_with_context;

#[derive(Deserialize)]
struct Vectors {
    cases: Vec<Case>,
}

#[derive(Deserialize)]
struct Case {
    #[serde(rename = "tcId")]
    tc_id: u32,
    pk: String,
    message: String,
    #[serde(default)]
    context: String,
    signature: String,
    #[serde(rename = "testPassed")]
    test_passed: bool,
    #[serde(default)]
    reason: String,
}

fn hex(s: &str) -> Vec<u8> {
    hex::decode(s).expect("valid hex in ACVP vector")
}

#[test]
fn acvp_ml_dsa_65_sigver_matches_reference() {
    let raw = include_str!("vectors/mldsa65_sigver.json");
    let vectors: Vectors = serde_json::from_str(raw).expect("parse vendored ACVP JSON");

    let total = vectors.cases.len();
    let mut valid = 0usize;
    let mut invalid = 0usize;

    for case in &vectors.cases {
        let pk = hex(&case.pk);
        let msg = hex(&case.message);
        let ctx = hex(&case.context);
        let sig = hex(&case.signature);

        // A well-formed signature that fails to verify → verdict `false`; a
        // malformed one → decode error, which is also a reject for ACVP.
        let verdict = match verify_internals_with_context(ML_DSA_65, &pk, &msg, &ctx, &sig) {
            Ok(trace) => trace.accepted,
            Err(_) => false,
        };

        assert_eq!(
            verdict, case.test_passed,
            "tcId {} ({}): reference verdict {} != ACVP expected {}",
            case.tc_id, case.reason, verdict, case.test_passed
        );

        if case.test_passed {
            valid += 1;
        } else {
            invalid += 1;
        }
    }

    assert_eq!(total, valid + invalid);
    assert!(
        valid > 0 && invalid > 0,
        "need both valid and invalid cases"
    );
    eprintln!(
        "ACVP ML-DSA-65 sigVer: {total} cases ({valid} valid, {invalid} invalid) all matched"
    );
}
