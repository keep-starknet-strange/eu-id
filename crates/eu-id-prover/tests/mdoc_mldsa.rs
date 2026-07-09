//! M7 — end-to-end ML-DSA-65-issued mdoc proving.
//!
//! The issuerAuth `COSE_Sign1` carries COSE alg `-49` (ML-DSA-65) and an AKP
//! issuer key; `extract_pid_mdoc` dispatches to the stwo-mldsa native
//! pre-check and the composition hosts the in-circuit ML-DSA statement in
//! place of the issuer P-256 draft (the device signature stays P-256).
//!
//! The hosted composition lives in the in-STARK (non-`ec-coprocessor`) build;
//! under `ec-coprocessor` an ML-DSA issuer is rejected with a clear error
//! (device-only P4b bundle pending — tasks/mldsa-todo.md M7). Run with:
//! `cargo test -p eu-id-prover --no-default-features --release --test mdoc_mldsa -- --test-threads=1`
//!
//! NOTE: heavy proofs must not run concurrently in one process (known
//! stwo-mldsa constraint) — always pass `--test-threads=1`.
#![cfg(feature = "ml-dsa")]

use eu_id_prover::generator::Policy;
use eu_id_prover::mdoc::{
    extract_pid_mdoc, openid4vp_session_transcript, ExtractedPidMdoc, MdocCircuitStatement,
    MdocPidRequest,
};

#[path = "mldsa_fixture.rs"]
mod mldsa_fixture;

fn demo_policy() -> Policy {
    Policy {
        current_date: predicates::Date {
            year: 2026,
            month: 7,
            day: 3,
        },
        min_age_years: 18,
        accepted_nationalities: vec![276, 250],
        accepted_nationalities_alpha2: vec![*b"DE", *b"FR"],
    }
}

fn mldsa_extracted_and_statement() -> (ExtractedPidMdoc, MdocCircuitStatement) {
    mldsa_extracted_and_statement_for(b"session-transcript-123")
}

/// Build the extract + statement for a specific session-transcript nonce. A
/// different nonce ⇒ different `Sig_structure` (the transcript is in the signed
/// MSO/DeviceAuth) ⇒ a distinct ML-DSA signature ⇒ a different SIB
/// rejection-sampling squeeze length — the axis the tree-0 cache key does NOT
/// see.
fn mldsa_extracted_and_statement_for(nonce: &[u8]) -> (ExtractedPidMdoc, MdocCircuitStatement) {
    let session_transcript = openid4vp_session_transcript(nonce);
    let fixture = mldsa_fixture::mldsa_pid_fixture_with_transcript(&session_transcript);
    let request = MdocPidRequest::eudi_pid(session_transcript);
    let extracted = extract_pid_mdoc(&fixture.document, &request).expect("ML-DSA mdoc extracts");
    let statement =
        MdocCircuitStatement::from_extracted(&extracted, demo_policy()).expect("statement builds");
    (extracted, statement)
}

#[test]
fn mldsa_mdoc_extracts_with_mldsa_issuer_arm() {
    let (extracted, statement) = mldsa_extracted_and_statement();
    let input = extracted
        .issuer_auth_input
        .as_mldsa()
        .expect("issuer arm is ML-DSA");
    assert_eq!(input.message, extracted.issuer_sig_structure);
    assert!(statement.issuer_input.as_mldsa().is_some());
    // Device auth stays P-256.
    assert_ne!(extracted.device_ecdsa_input.public_key.x.0, [0u8; 32]);
}

/// Wrong issuer public key (a bit flipped inside the AKP key carried by the
/// document): the native FIPS 204 pre-check must reject at extraction.
#[test]
fn mldsa_mdoc_wrong_issuer_pk_rejects_at_extraction() {
    let session_transcript = openid4vp_session_transcript(b"session-transcript-123");
    let fixture = mldsa_fixture::mldsa_pid_fixture();
    let request = MdocPidRequest::eudi_pid(session_transcript);
    // Locate the 1952-byte issuer pk inside the document and flip one byte.
    let offset = fixture
        .document
        .windows(fixture.issuer_pk.len())
        .position(|window| window == fixture.issuer_pk.as_slice())
        .expect("issuer pk embedded in document");
    let mut tampered = fixture.document.clone();
    tampered[offset] ^= 0x01;
    let err = extract_pid_mdoc(&tampered, &request).expect_err("wrong issuer pk rejects");
    assert!(
        format!("{err:?}").contains("InvalidSignature"),
        "unexpected error: {err:?}"
    );
}

#[cfg(feature = "ec-coprocessor")]
mod coprocessor_mode {
    use super::*;
    use eu_id_prover::mdoc::prove_mdoc_circuit;

    /// Under `ec-coprocessor`, an ML-DSA issuer is rejected with a clear error
    /// (the P4b bundle is a fixed two-ECDSA MAC format; device-only pending).
    #[test]
    fn mldsa_issuer_rejected_with_coprocessor_feature() {
        let (extracted, statement) = mldsa_extracted_and_statement();
        let err = match prove_mdoc_circuit(&extracted, &statement) {
            Err(err) => err,
            Ok(_) => panic!("ML-DSA issuer must be rejected under ec-coprocessor"),
        };
        assert!(
            format!("{err:?}").contains("ML-DSA"),
            "unexpected error: {err:?}"
        );
    }
}

#[cfg(not(feature = "ec-coprocessor"))]
mod hosted_mode {
    use super::*;
    use eu_id_prover::mdoc::{
        mdoc_expected_preprocessed_root, mdoc_production_pcs_config, mdoc_proof_byte_breakdown,
        prove_mdoc_circuit, verify_mdoc_circuit,
        verify_mdoc_circuit_with_pcs_config_and_preprocessed_root,
    };
    use eu_id_prover::Error;
    use std::time::Instant;

    /// e2e: an ML-DSA-65-issued mdoc proves and verifies through the shared
    /// STARK, and the proof (with its ML-DSA claim tree) round-trips bincode.
    /// Prints the measured numbers for the M7 log.
    #[test]
    fn mldsa_mdoc_proves_and_verifies_end_to_end() {
        let (extracted, statement) = mldsa_extracted_and_statement();

        let prove_start = Instant::now();
        let proof = prove_mdoc_circuit(&extracted, &statement).expect("ML-DSA mdoc proves");
        let prove_time = prove_start.elapsed();

        let verify_start = Instant::now();
        verify_mdoc_circuit(&proof, &statement).expect("ML-DSA mdoc verifies");
        let verify_time = verify_start.elapsed();

        let breakdown = mdoc_proof_byte_breakdown(&proof);
        println!(
            "M7 NUMBERS mldsa-mdoc: prove = {prove_time:?}, verify = {verify_time:?}, \
             proof bytes = {}, stark bytes = {}",
            breakdown.proof_bytes, breakdown.stark_proof_bytes
        );

        // Bincode round-trip (the ML-DSA claim tree serializes losslessly).
        let bytes = bincode::serialize(&proof).expect("proof serializes");
        let restored: eu_id_prover::mdoc::MdocCircuitProof =
            bincode::deserialize(&bytes).expect("proof deserializes");
        verify_mdoc_circuit(&restored, &statement).expect("round-tripped proof verifies");
    }

    /// SHA↔SHAKE byte tamper: the SHA pass proves a preimage that differs in
    /// one byte from the message the ML-DSA statement absorbs. The shared
    /// field-relation LogUp must not balance → verification rejects.
    #[test]
    fn mldsa_mdoc_sha_shake_byte_tamper_rejects() {
        let (mut extracted, statement) = mldsa_extracted_and_statement();
        // Offset 2 lies inside the `"Signature1"` tstr — before the payload,
        // outside every statement window, so ONLY the whole-message exposure
        // (the SHA↔SHAKE link) sees the difference.
        extracted.issuer_sig_structure[2] ^= 0x01;

        let rejected = match prove_mdoc_circuit(&extracted, &statement) {
            Err(_) => true,
            Ok(proof) => verify_mdoc_circuit(&proof, &statement).is_err(),
        };
        assert!(rejected, "tampered SHA-side Sig_structure byte must reject");
    }

    /// The F-ROOT pin on the hosted ML-DSA mdoc path: the verifier derives the
    /// expected tree-0 (preprocessed) root independently via
    /// `mdoc_expected_preprocessed_root` and pins it. The honest proof verifies
    /// against the derived root (control); a tampered pin is rejected with
    /// `PreprocessedRootMismatch` — at the ROOT check, before the STARK work.
    #[test]
    fn mldsa_mdoc_pins_the_preprocessed_root() {
        let (extracted, statement) = mldsa_extracted_and_statement();
        let config = mdoc_production_pcs_config();
        let proof = prove_mdoc_circuit(&extracted, &statement).expect("ML-DSA mdoc proves");

        // Control: the verifier's own derivation of the tree-0 root (from the
        // public statement + witness, never from the proof) accepts the honest
        // proof.
        let expected_root = mdoc_expected_preprocessed_root(&extracted, &statement, config)
            .expect("expected preprocessed root computes");
        verify_mdoc_circuit_with_pcs_config_and_preprocessed_root(&proof, &statement, config, expected_root)
            .expect("honest proof verifies against the derived preprocessed root");

        // Negative: a pin that does NOT match the proof's tree-0 root is
        // rejected fail-closed, specifically at the root check — not as a
        // generic constraint failure.
        let mut wrong_root = expected_root;
        wrong_root.0[0] ^= 1;
        assert!(
            matches!(
                verify_mdoc_circuit_with_pcs_config_and_preprocessed_root(
                    &proof,
                    &statement,
                    config,
                    wrong_root,
                ),
                Err(Error::PreprocessedRootMismatch { .. })
            ),
            "a mismatched preprocessed root must be rejected before the STARK check",
        );
    }

    /// Cache-collision regression: two DISTINCT ML-DSA mdoc statements (built
    /// from different session transcripts ⇒ different signatures ⇒ different SIB
    /// squeeze stream lengths) share the same padded `sib_log_size` — and thus
    /// the same tree-0 preprocessed shape key. Each proof must verify under its
    /// OWN derived pin. With the CACHED root variant the second derivation would
    /// return the first's root and one proof would fail `PreprocessedRootMismatch`;
    /// `mdoc_expected_preprocessed_root` uses the uncached variant, so both pass.
    #[test]
    fn mldsa_mdoc_pin_is_per_signature_not_cached() {
        let config = mdoc_production_pcs_config();
        let (extracted_a, statement_a) = mldsa_extracted_and_statement_for(b"nonce-A");
        let (extracted_b, statement_b) = mldsa_extracted_and_statement_for(b"nonce-B");

        let proof_a = prove_mdoc_circuit(&extracted_a, &statement_a).expect("proof A proves");
        let proof_b = prove_mdoc_circuit(&extracted_b, &statement_b).expect("proof B proves");

        // Derive each pin (this is where a cache keyed only on shape would alias
        // B's root onto A's).
        let root_a = mdoc_expected_preprocessed_root(&extracted_a, &statement_a, config)
            .expect("root A computes");
        let root_b = mdoc_expected_preprocessed_root(&extracted_b, &statement_b, config)
            .expect("root B computes");

        verify_mdoc_circuit_with_pcs_config_and_preprocessed_root(&proof_a, &statement_a, config, root_a)
            .expect("proof A verifies under its own pin");
        verify_mdoc_circuit_with_pcs_config_and_preprocessed_root(&proof_b, &statement_b, config, root_b)
            .expect("proof B verifies under its own pin");
    }

    /// Cross-mode confusion: an ML-DSA proof presented against a P-256
    /// (ECDSA) statement must be rejected. Needs both issuer schemes compiled in
    /// (it builds a P-256 demo fixture alongside the ML-DSA one).
    #[cfg(feature = "p256")]
    #[test]
    fn mldsa_proof_against_ecdsa_statement_rejects() {
        use eu_id_prover::mdoc::{demo_mdoc_circuit_fixture, IssuerAuthInput};
        let (extracted, statement) = mldsa_extracted_and_statement();
        let proof = prove_mdoc_circuit(&extracted, &statement).expect("ML-DSA mdoc proves");

        let p256 = demo_mdoc_circuit_fixture();
        assert!(matches!(
            p256.statement.issuer_input,
            IssuerAuthInput::Ecdsa(_)
        ));
        verify_mdoc_circuit(&proof, &p256.statement)
            .expect_err("ML-DSA proof must not verify against an ECDSA statement");

        // And the converse arm mismatch: the ML-DSA statement rejects a proof
        // whose issuer claims are P-256-shaped (proved on the P-256 fixture).
        let p256_proof =
            prove_mdoc_circuit(&p256.extracted, &p256.statement).expect("P-256 mdoc proves");
        verify_mdoc_circuit(&p256_proof, &statement)
            .expect_err("ECDSA proof must not verify against an ML-DSA statement");
    }

    /// CM-3 same-arm malformed claim tree: an ML-DSA proof produced for one
    /// statement is presented against a DIFFERENT ML-DSA statement. Both use the
    /// ML-DSA issuer arm, so this is not the cross-arm mismatch of
    /// `mldsa_proof_against_ecdsa_statement_rejects`; the proof's ML-DSA claim
    /// tree (group evals + claimed sums + SIB shape) is bound to statement A's
    /// public input, so verifying it under statement B must reject — the
    /// claim-tree / public-binding gate, not just the arm selector.
    #[test]
    fn mldsa_malformed_claim_tree_rejects() {
        let (extracted_a, statement_a) = mldsa_extracted_and_statement_for(b"claim-tree-A");
        let (_extracted_b, statement_b) = mldsa_extracted_and_statement_for(b"claim-tree-B");

        let proof_a = prove_mdoc_circuit(&extracted_a, &statement_a).expect("proof A proves");
        // Control: proof A verifies against its own statement.
        verify_mdoc_circuit(&proof_a, &statement_a).expect("control: A verifies under A");
        // Negative: proof A's ML-DSA claim tree is bound to statement A; under
        // statement B the public-input mixing + claim binding no longer match.
        verify_mdoc_circuit(&proof_a, &statement_b)
            .expect_err("ML-DSA proof A must not verify against a different ML-DSA statement B");
    }

    /// ZK/A1 smoke (S5 §5, the weakest — "smoke" — obligation): two DISTINCT
    /// ML-DSA credentials satisfying the SAME policy both prove and verify, and
    /// their proofs share the same public-statement component shape (claimed-sum
    /// arity + ML-DSA group-eval count). This is a STRUCTURAL indistinguishability
    /// check, NOT a statistical zero-knowledge claim — ML-DSA proving here is not
    /// yet randomized, so it does not certify unlinkability, only that the public
    /// surface does not vary with the private credential in shape.
    #[test]
    fn mldsa_two_credentials_same_policy_smoke() {
        let (extracted_a, statement_a) = mldsa_extracted_and_statement_for(b"zk-smoke-A");
        let (extracted_b, statement_b) = mldsa_extracted_and_statement_for(b"zk-smoke-B");
        // Same policy on both (the helper uses `demo_policy()` for both).
        assert_eq!(
            statement_a.policy, statement_b.policy,
            "smoke precondition: both credentials under one policy"
        );

        let proof_a = prove_mdoc_circuit(&extracted_a, &statement_a).expect("A proves");
        let proof_b = prove_mdoc_circuit(&extracted_b, &statement_b).expect("B proves");
        verify_mdoc_circuit(&proof_a, &statement_a).expect("A verifies");
        verify_mdoc_circuit(&proof_b, &statement_b).expect("B verifies");

        // Public shape (component/claim arity) must not leak which credential.
        let bd_a = mdoc_proof_byte_breakdown(&proof_a);
        let bd_b = mdoc_proof_byte_breakdown(&proof_b);
        assert_eq!(
            bd_a.stark.commitments, bd_b.stark.commitments,
            "smoke: commitment-tree shape must not vary with the credential"
        );
    }
}
