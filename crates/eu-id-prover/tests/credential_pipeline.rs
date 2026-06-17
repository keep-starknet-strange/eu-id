//! End-to-end exercise of the credential format + native witness generator,
//! driven through the crate's **public** surface — the same way every later
//! binding task (and the soundness suite) will consume the oracle.
//!
//! The fast tests run the draft-free path so they stay in CI. One `#[ignore]`
//! test composes the full witness (including the P256 draft) for the valid
//! fixtures; run it with `--release --ignored`.

use eu_id_prover::credential::{Credential, CREDENTIAL_LEN, DOB_WINDOW, NATIONALITY_WINDOW};
use eu_id_prover::fixtures;
use eu_id_prover::generator::{sign_credential, IssuerKey, PipelineWitness};

#[test]
fn every_fixture_matches_its_declared_expectation() {
    for f in fixtures::all() {
        let report = f.pipeline_witness_lite().check_consistency();
        assert_eq!(
            report.crypto_ok(),
            f.expectation.crypto_consistent,
            "fixture `{}`: crypto consistency mismatch ({report:?})",
            f.name
        );
        assert_eq!(
            report.bindings_ok(),
            f.expectation.binding_consistent,
            "fixture `{}`: binding consistency mismatch ({report:?})",
            f.name
        );
    }
}

#[test]
fn consistency_covers_crypto_and_binding_not_the_statements() {
    // `check_consistency` validates only that the crypto checks out and the
    // predicate attributes match the signed bytes — NOT whether the age/nat
    // statements are true (that is the proof's job). So `under_18` and
    // `wrong_nationality` are self-consistent here even though they must not
    // ultimately verify; only `tampered_dob_bytes` (binding) and
    // `bad_signature` (crypto) fail consistency.
    let consistent: Vec<&str> = fixtures::all()
        .iter()
        .filter(|f| f.pipeline_witness_lite().check_consistency().all_ok())
        .map(|f| f.name)
        .collect();
    assert_eq!(
        consistent,
        vec![
            "valid_over_18",
            "valid_exactly_18",
            "under_18",
            "wrong_nationality"
        ]
    );

    // The fully bound proof, by contrast, should accept only the two valid ones.
    let should_verify: Vec<&str> = fixtures::all()
        .iter()
        .filter(|f| f.expectation.should_verify())
        .map(|f| f.name)
        .collect();
    assert_eq!(should_verify, vec!["valid_over_18", "valid_exactly_18"]);
}

#[test]
fn generator_round_trips_an_arbitrary_credential() {
    // The public API can sign and validate any credential, not just fixtures.
    let cred = Credential::new(1990, 12, 31, 380); // IT
    let signed = sign_credential(&cred, &IssuerKey::demo());
    let policy = fixtures::demo_policy();
    let pw = PipelineWitness::build_lite(signed, policy);

    let report = pw.check_consistency();
    assert!(
        report.crypto_ok(),
        "freshly signed credential is sound: {report:?}"
    );
    assert!(report.bindings_ok());

    // The signed bytes expose the documented field windows.
    let dob = &pw.signed.message[DOB_WINDOW];
    assert_eq!(dob, &[0x07, 0xC6, 12, 31]); // 1990 = 0x07C6
    let nat = &pw.signed.message[NATIONALITY_WINDOW];
    assert_eq!(u16::from(nat[0]) * 256 + u16::from(nat[1]), 380);
    assert_eq!(pw.signed.message.len(), CREDENTIAL_LEN);
}

#[test]
#[ignore = "slow in debug: builds full P256 drafts; run with --release --ignored"]
fn valid_fixtures_compose_a_full_pipeline_witness() {
    for f in [fixtures::valid_over_18(), fixtures::valid_exactly_18()] {
        let pw = f.pipeline_witness();
        assert!(
            pw.p256_draft.is_some(),
            "fixture `{}` must compose a P256 draft",
            f.name
        );
        assert!(
            pw.check_consistency().all_ok(),
            "fixture `{}` consistent",
            f.name
        );
    }
}
