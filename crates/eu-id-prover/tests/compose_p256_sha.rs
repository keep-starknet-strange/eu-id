//! Combined-proof **composition & calendar-boundary** tests.
//!
//! Drives the P256 ECDSA module, the SHA-256 module, the digest-bind bridge, and
//! the age + nationality predicate modules through one STARK proof and checks the
//! positive paths: that all five modules compose into a single verifying proof,
//! and that the calendar edges the bound age module reasons about (turning
//! exactly 18 on the reference date, a leap-day birth) verify.
//!
//! The systematic negative suite — one test per mutation class (digest mismatch,
//! DOB/nationality binding breaks, tampered signature, wrong issuer key,
//! under-age, nationality outside the set) — lives in `tests/e2e_soundness.rs`.
//!
//! Marked `#[ignore]` — a real STARK prove/verify dominated by P256 is slow; run
//! with `--release --ignored`.

use eu_id_prover::credential::Credential;
use eu_id_prover::generator::{sign_credential, IssuerKey};
use eu_id_prover::{fixtures, prove, verify, Error, PipelineWitness, Proof};
use std::time::Instant;

/// Drive a pipeline witness through the five-module combined prover.
fn prove_pipeline(pw: &PipelineWitness) -> Result<Proof, Error> {
    let draft = pw
        .p256_draft
        .as_ref()
        .expect("a valid signature builds a P256 draft");
    prove(
        draft,
        &pw.sha_witness,
        pw.sha_log_n_rows,
        pw.sha_group_width,
        &pw.age_public,
        &pw.age_dob,
        &pw.nat_public,
        &pw.nat_private,
    )
}

#[test]
#[ignore = "WO-1.6 diagnostic: proves the same witness twice and prints cache warm-up timing"]
fn wo_1_6_repeated_prove_timing() {
    let pw = fixtures::valid_over_18().pipeline_witness();
    assert!(pw.check_consistency().all_ok());

    let first_start = Instant::now();
    let first = prove_pipeline(&pw).expect("first proof generates");
    let first_ms = first_start.elapsed().as_secs_f64() * 1000.0;

    let second_start = Instant::now();
    let second = prove_pipeline(&pw).expect("second proof generates");
    let second_ms = second_start.elapsed().as_secs_f64() * 1000.0;

    let first_bytes = bincode::serialize(&first).expect("first proof serializes");
    let second_bytes = bincode::serialize(&second).expect("second proof serializes");
    assert_eq!(first_bytes, second_bytes, "cached proof bytes must match");

    eprintln!(
        "WO-1.6 repeated prove timing: first_ms={first_ms:.3} second_ms={second_ms:.3} delta_ms={:.3}",
        first_ms - second_ms
    );
}

#[test]
#[ignore = "WO-1.6 diagnostic: proves twice to assert cache byte identity"]
fn wo_1_6_repeated_prove_bytes_identical() {
    let pw = fixtures::valid_over_18().pipeline_witness();
    assert!(pw.check_consistency().all_ok());

    let first = prove_pipeline(&pw).expect("first proof generates");
    let second = prove_pipeline(&pw).expect("second proof generates");

    let first_bytes = bincode::serialize(&first).expect("first proof serializes");
    let second_bytes = bincode::serialize(&second).expect("second proof serializes");
    assert_eq!(first_bytes, second_bytes, "cached proof bytes must match");
}

#[test]
#[ignore = "WO-1.2 diagnostic: proves serial task path and default fan-out path to assert byte identity"]
fn wo_1_2_trace_fanout_proof_bytes_identical() {
    let pw = fixtures::valid_over_18().pipeline_witness();
    assert!(pw.check_consistency().all_ok());

    std::env::set_var("EU_ID_DISABLE_TRACE_FANOUT", "1");
    let serial = prove_pipeline(&pw).expect("serial task path proof generates");
    std::env::remove_var("EU_ID_DISABLE_TRACE_FANOUT");

    let parallel = prove_pipeline(&pw).expect("default fan-out proof generates");

    let serial_bytes = bincode::serialize(&serial).expect("serial proof serializes");
    let parallel_bytes = bincode::serialize(&parallel).expect("parallel proof serializes");
    assert_eq!(
        serial_bytes, parallel_bytes,
        "trace fan-out must preserve proof bytes"
    );
}

/// The honest end-to-end witness: a signed credential whose holder is over 18 and
/// whose nationality is accepted. Drives all five modules — P256, SHA-256, the
/// digest bridge, the **credential-bound** age module, and nationality — and
/// verifies. The age binding holds (the date of birth the module clears against
/// the threshold is the credential's signed DOB), and the digest binds, so the
/// global LogUp balance cancels.
#[test]
#[ignore = "slow: full P256 + SHA + bridge + predicates STARK prove/verify; run with --release --ignored"]
fn composes_all_modules_for_an_honest_credential() {
    let pw = fixtures::valid_over_18().pipeline_witness();
    assert!(
        pw.check_consistency().all_ok(),
        "fixture witness must be self-consistent"
    );

    let proof = prove_pipeline(&pw).expect("five-module proof generates");

    let expected = proof.p256_instances().to_vec();
    verify(&proof, &expected).expect("five-module bound proof verifies");

    // Caller-argument binding: a mismatched expected statement is rejected.
    assert!(
        verify(&proof, &[]).is_err(),
        "an empty expected statement must be rejected",
    );
}

/// Boundary case through the bound path: a holder who turns exactly 18 on the
/// reference date (born 2008-06-17, cutoff 2008-06-17, DOB == cutoff is accepted).
/// The age binding holds and the proof verifies.
#[test]
#[ignore = "slow: full P256 + SHA + bridge + predicates STARK prove/verify; run with --release --ignored"]
fn binds_exactly_18_credential() {
    let pw = fixtures::valid_exactly_18().pipeline_witness();
    let proof = prove_pipeline(&pw).expect("exactly-18 proof generates");
    let expected = proof.p256_instances().to_vec();
    verify(&proof, &expected).expect("exactly-18 bound proof verifies");
}

/// Boundary case through the bound path: a leap-day date of birth (born
/// 2000-02-29 — 2000 is a leap year, so Feb 29 exists). Exercises the calendar /
/// valid-day path of the bound age module; the binding holds and the proof
/// verifies. 2000-02-29 reconciles to DOB bytes `[0x07, 0xD0, 0x02, 0x1D]`.
#[test]
#[ignore = "slow: full P256 + SHA + bridge + predicates STARK prove/verify; run with --release --ignored"]
fn binds_leap_year_credential() {
    let credential = Credential::new(2000, 2, 29, 276);
    let signed = sign_credential(&credential, &IssuerKey::demo());
    let pw = PipelineWitness::build(signed, fixtures::demo_policy());
    assert!(
        pw.check_consistency().all_ok(),
        "leap-year credential witness must be self-consistent"
    );

    let proof = prove_pipeline(&pw).expect("leap-year proof generates");
    let expected = proof.p256_instances().to_vec();
    verify(&proof, &expected).expect("leap-year bound proof verifies");
}
