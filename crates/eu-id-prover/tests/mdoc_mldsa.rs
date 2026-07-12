//! End-to-end ML-DSA-65 mdoc proving (issuer + device + TS13 revocation).
//!
//! The fully post-quantum mode is UNIFORM: the issuerAuth COSE_Sign1 carries
//! COSE alg `-49` with an AKP issuer key, the MSO `deviceKey` is an AKP
//! COSE_Key with a pure ML-DSA-65 `deviceSignature`, and the optional TS13
//! revocation authority signs the raw 20-byte message with ML-DSA-65 (no
//! prehash; the message stays private via the hosted module's private-message
//! mode).
//!
//! Run with: `RAYON_NUM_THREADS=1 cargo test -p eu-id-prover --release \
//!    --test mdoc_mldsa -- --test-threads=1`
//!
//! NOTE: heavy proofs must not run concurrently in one process (known
//! stwo-mldsa constraint) — always pass `--test-threads=1`.

use eu_id_prover::mdoc::{
    extract_pid_mdoc, openid4vp_session_transcript, ExtractedPidMdoc, MdocCircuitStatement,
    MdocError, MdocPidRequest, MdocRevocationKey, MdocRevocationPublicInputs,
    MdocRevocationRangeWitness, MdocRevocationSignature,
};
use eu_id_prover::ts13::{
    ts13_mso_derived_revocation_id, Ts13RevocationError, Ts13RevocationStatement,
    Ts13RevocationWitness,
};
use eu_id_prover::Policy;

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

/// The fully-PQ fixture + a request pinning ITS issuer key (D5: an ML-DSA
/// issuer requires a non-empty byte-equal pin list).
fn full_pq_fixture_and_request_for(
    nonce: &[u8],
) -> (mldsa_fixture::MldsaFullPqFixture, MdocPidRequest) {
    let session_transcript = openid4vp_session_transcript(nonce);
    let fixture = mldsa_fixture::mldsa_full_pq_fixture_with_transcript(&session_transcript);
    let request = MdocPidRequest::eudi_pid(session_transcript)
        .with_trusted_mldsa_issuer_public_keys(vec![fixture.issuer_pk.clone()]);
    (fixture, request)
}

fn full_pq_extracted_and_statement_for(nonce: &[u8]) -> (ExtractedPidMdoc, MdocCircuitStatement) {
    let (fixture, request) = full_pq_fixture_and_request_for(nonce);
    let extracted = extract_pid_mdoc(&fixture.document, &request).expect("fully-PQ mdoc extracts");
    let statement =
        MdocCircuitStatement::from_extracted(&extracted, demo_policy()).expect("statement builds");
    (extracted, statement)
}

fn full_pq_extracted_and_statement() -> (ExtractedPidMdoc, MdocCircuitStatement) {
    full_pq_extracted_and_statement_for(b"session-transcript-123")
}

/// Distinctive private bound offset (G6): the id_lo/id_hi LE-byte patterns
/// derived from it cannot collide with unrelated proof bytes by accident.
const DISTINCTIVE_BOUND_OFFSET: u64 = 0x1122_3344_5566_7788;

/// The revocation triple for the fully-PQ statement: derived id, distinctive
/// private bounds, and the deterministic ML-DSA revocation-authority
/// signature over the raw 20-byte message.
fn mldsa_revocation_parts(extracted: &ExtractedPidMdoc) -> (u64, u64, u64, u32, Vec<u8>, Vec<u8>) {
    let id = ts13_mso_derived_revocation_id(&extracted.mso);
    assert!(
        id > DISTINCTIVE_BOUND_OFFSET && id < u64::MAX - DISTINCTIVE_BOUND_OFFSET,
        "fixture-derived id supports the distinctive bounds"
    );
    let id_lo = id - DISTINCTIVE_BOUND_OFFSET;
    let id_hi = id + DISTINCTIVE_BOUND_OFFSET;
    let epoch = 7u32;
    let (pk, sig) = mldsa_fixture::mldsa_revocation_fixture(id_lo, id_hi, epoch);
    (id, id_lo, id_hi, epoch, pk, sig)
}

fn with_mldsa_revocation(
    statement: MdocCircuitStatement,
    extracted: &ExtractedPidMdoc,
) -> (MdocCircuitStatement, u64, u64) {
    let (id, id_lo, id_hi, epoch, pk, sig) = mldsa_revocation_parts(extracted);
    (
        statement
            .with_ts13_revocation(MdocRevocationPublicInputs {
                revocation_public_key: MdocRevocationKey::MlDsa(pk),
                epoch,
            })
            .with_ts13_revocation_range(MdocRevocationRangeWitness { id, id_lo, id_hi })
            .with_ts13_revocation_signature(MdocRevocationSignature::MlDsa(sig)),
        id_lo,
        id_hi,
    )
}

// =====================================================================
// Extraction-level positives and fail-closed negatives (G1, D5).
// =====================================================================

#[test]
fn full_pq_mdoc_extracts_with_mldsa_issuer_and_device_arms() {
    let (extracted, statement) = full_pq_extracted_and_statement();
    let issuer = extracted
        .issuer_auth_input
        .as_mldsa()
        .expect("issuer arm is ML-DSA");
    assert_eq!(issuer.message, extracted.issuer_sig_structure);
    let device = extracted
        .device_auth_input
        .as_mldsa()
        .expect("device arm is ML-DSA");
    assert_eq!(device.message, extracted.device_sig_structure);
    assert!(statement.issuer_input.is_mldsa());
    assert!(statement.device_input.is_mldsa());
}

/// D5: an ML-DSA issuer REQUIRES a non-empty pin list whose member is
/// byte-equal to the header AKP key. A self-carried key is never a trust decision.
#[test]
fn mldsa_issuer_trust_pins_fail_closed() {
    let (fixture, request) = full_pq_fixture_and_request_for(b"session-transcript-123");

    // No pins → reject.
    let no_pins = request
        .clone()
        .with_trusted_mldsa_issuer_public_keys(Vec::new());
    assert!(matches!(
        extract_pid_mdoc(&fixture.document, &no_pins),
        Err(MdocError::UntrustedIssuerKey)
    ));

    // Wrong pin (one byte off) → reject.
    let mut wrong_pk = fixture.issuer_pk.clone();
    wrong_pk[0] ^= 0x01;
    let wrong_pin = request
        .clone()
        .with_trusted_mldsa_issuer_public_keys(vec![wrong_pk]);
    assert!(matches!(
        extract_pid_mdoc(&fixture.document, &wrong_pin),
        Err(MdocError::UntrustedIssuerKey)
    ));

    // Control: the correct pin extracts.
    extract_pid_mdoc(&fixture.document, &request).expect("pinned issuer extracts");
}

/// Per-role tamper negatives at extraction (G1): a flipped issuer-signature
/// byte and a flipped device-signature byte must both reject natively.
#[test]
fn full_pq_signature_tampers_reject_at_extraction() {
    let (fixture, request) = full_pq_fixture_and_request_for(b"session-transcript-123");

    let tamper = |needle: &[u8]| {
        let offset = fixture
            .document
            .windows(needle.len())
            .position(|window| window == needle)
            .expect("signature embedded in document");
        let mut tampered = fixture.document.clone();
        // Flip a byte inside the z region (past the 48-byte c̃).
        tampered[offset + stwo_mldsa::constants::C_TILDE_BYTES + 200] ^= 0x01;
        tampered
    };

    let issuer_tampered = tamper(&fixture.issuer_signature);
    assert!(matches!(
        extract_pid_mdoc(&issuer_tampered, &request),
        Err(MdocError::InvalidSignature("issuerAuth"))
    ));

    let device_tampered = tamper(&fixture.device_signature);
    assert!(matches!(
        extract_pid_mdoc(&device_tampered, &request),
        Err(MdocError::InvalidSignature("deviceSignature"))
    ));
}

// =====================================================================
// TS13 revocation, native path (G6): ML-DSA arm of `verify_witness`.
// =====================================================================

#[test]
fn ts13_mldsa_revocation_native_positive_and_negatives() {
    let (extracted, _) = full_pq_extracted_and_statement();
    let (id, id_lo, id_hi, epoch, pk, sig) = mldsa_revocation_parts(&extracted);

    let statement = Ts13RevocationStatement {
        revocation_public_key: MdocRevocationKey::MlDsa(pk.clone()),
        epoch,
    };
    let witness = |id_lo, id_hi, epoch, sig: &[u8]| Ts13RevocationWitness {
        id,
        id_lo,
        id_hi,
        epoch,
        signature: MdocRevocationSignature::MlDsa(sig.to_vec()),
    };

    // Control.
    statement
        .verify_witness(&extracted, &witness(id_lo, id_hi, epoch, &sig))
        .expect("honest ML-DSA revocation witness verifies");

    // Out-of-range id (id == id_lo) → Range.
    assert_eq!(
        statement.verify_witness(&extracted, &witness(id, id_hi, epoch, &sig)),
        Err(Ts13RevocationError::Range)
    );

    // Wrong epoch → Epoch (statement/witness disagree).
    assert_eq!(
        statement.verify_witness(&extracted, &witness(id_lo, id_hi, epoch + 1, &sig)),
        Err(Ts13RevocationError::Epoch)
    );

    // Tampered bounds under the honest signature → pure ML-DSA over the raw
    // 20 bytes rejects (no prehash to hide behind).
    assert_eq!(
        statement.verify_witness(&extracted, &witness(id_lo + 1, id_hi, epoch, &sig)),
        Err(Ts13RevocationError::InvalidSignature)
    );

    // Tampered signature → reject.
    let mut bad_sig = sig.clone();
    bad_sig[stwo_mldsa::constants::C_TILDE_BYTES + 200] ^= 0x01;
    assert_eq!(
        statement.verify_witness(&extracted, &witness(id_lo, id_hi, epoch, &bad_sig)),
        Err(Ts13RevocationError::InvalidSignature)
    );
}

mod quantum_only {
    use super::*;
    use eu_id_prover::mdoc::{
        mdoc_expected_preprocessed_root, mdoc_production_pcs_config, mdoc_proof_byte_breakdown,
        prove_mdoc_circuit, verify_mdoc_circuit,
        verify_mdoc_circuit_with_pcs_config_and_preprocessed_root,
    };
    use eu_id_prover::Error;
    use std::time::Instant;

    /// A device-key ↔ MSO binding violation rejects at prove entry.
    #[test]
    fn full_pq_statement_binding_tamper_rejects_at_prove() {
        let (extracted, statement) = full_pq_extracted_and_statement();

        // D2: statement + extracted whose device key is NOT the MSO deviceKey
        // (the issuer's own input replayed into the device slot) → the
        // canonical byte-equality binding rejects at prove, before any STARK.
        let mut extracted_swapped = extracted.clone();
        extracted_swapped.device_auth_input = extracted.issuer_auth_input.clone();
        let mut statement_swapped = statement.clone();
        statement_swapped.device_input = statement.issuer_input.clone();
        let err = match prove_mdoc_circuit(&extracted_swapped, &statement_swapped) {
            Err(err) => err,
            Ok(_) => panic!("device-key binding tamper must reject at prove"),
        };
        assert!(
            format!("{err:?}").contains("device-key MSO binding"),
            "unexpected error: {err:?}"
        );
    }

    /// G2 + G3 + G5 + G6 in one proving pass: the fully post-quantum e2e —
    /// ML-DSA issuer + device + revocation (three hosted instances) proves and
    /// verifies; the proof round-trips bincode; role-replayed claim trees
    /// reject; the D2 binding rejects on the verify side; and the serialized
    /// verifier statement + proof contain no private id-bound bytes.
    #[test]
    fn full_pq_mdoc_proves_and_verifies_with_revocation_end_to_end() {
        let (extracted, statement) = full_pq_extracted_and_statement();
        let (statement, id_lo, id_hi) = with_mldsa_revocation(statement, &extracted);

        let prove_start = Instant::now();
        let proof = prove_mdoc_circuit(&extracted, &statement).expect("fully-PQ mdoc proves");
        let prove_time = prove_start.elapsed();

        let verify_start = Instant::now();
        verify_mdoc_circuit(&proof, &statement).expect("fully-PQ mdoc verifies");
        let verify_time = verify_start.elapsed();

        let breakdown = mdoc_proof_byte_breakdown(&proof);
        println!(
            "PQ NUMBERS full-pq-mdoc(issuer+device+revocation): prove = {prove_time:?}, \
             verify = {verify_time:?}, proof bytes = {}, stark bytes = {}",
            breakdown.proof_bytes, breakdown.stark_proof_bytes
        );

        // Bincode round-trip.
        let proof_bytes = bincode::serialize(&proof).expect("proof serializes");
        let restored: eu_id_prover::mdoc::MdocCircuitProof =
            bincode::deserialize(&proof_bytes).expect("proof deserializes");
        verify_mdoc_circuit(&restored, &statement).expect("round-tripped proof verifies");

        // The VERIFIER-side statement does not need the real range values:
        // zeroed bounds verify identically (the range facts are proven
        // in-STARK; the verifier only keys off presence).
        let mut verifier_statement = statement.clone();
        verifier_statement.ts13_revocation_range = Some(MdocRevocationRangeWitness {
            id: 0,
            id_lo: 0,
            id_hi: 0,
        });
        verify_mdoc_circuit(&proof, &verifier_statement)
            .expect("verifier statement with zeroed range verifies");

        // G6 privacy: the raw id_lo/id_hi LE-byte patterns are absent from the
        // serialized proof AND the serialized verifier statement.
        let statement_bytes =
            bincode::serialize(&verifier_statement).expect("statement serializes");
        for (name, pattern) in [
            ("id_lo", id_lo.to_le_bytes()),
            ("id_hi", id_hi.to_le_bytes()),
        ] {
            for (blob_name, blob) in [("proof", &proof_bytes), ("statement", &statement_bytes)] {
                assert!(
                    !blob.windows(pattern.len()).any(|window| window == pattern),
                    "{name} bytes leaked into the serialized {blob_name}"
                );
            }
        }

        // G3 role replay: device ↔ revocation claim-tree swap rejects (the
        // per-role instance namespaces diverge the transcript).
        let mut device_revocation_swap = proof.clone();
        std::mem::swap(
            &mut device_revocation_swap.device_mldsa,
            &mut device_revocation_swap.revocation_mldsa,
        );
        verify_mdoc_circuit(&device_revocation_swap, &statement)
            .expect_err("device/revocation claim swap must reject");

        // G3 role replay: issuer ↔ device claim-tree swap rejects.
        let mut issuer_device_swap = proof.clone();
        std::mem::swap(
            &mut issuer_device_swap.mldsa,
            &mut issuer_device_swap.device_mldsa,
        );
        verify_mdoc_circuit(&issuer_device_swap, &statement)
            .expect_err("issuer/device claim swap must reject");

        // G5 verify side: a statement whose device key does not match the MSO
        // deviceKey (issuer input replayed into the device slot) rejects at
        // the D2 binding check, before the STARK.
        let mut binding_tamper = statement.clone();
        binding_tamper.device_input = statement.issuer_input.clone();
        let err = verify_mdoc_circuit(&proof, &binding_tamper)
            .expect_err("device-key binding tamper rejects at verify");
        assert!(
            format!("{err:?}").contains("device-key MSO binding"),
            "unexpected error: {err:?}"
        );

        // G6: a tampered PUBLIC revocation KEY byte in the statement diverges
        // the rebuilt verifier input (ρ/t1/tr are transcript-mixed and drive
        // the verifier-native fold) → reject. NOTE: the SIGNATURE bytes are
        // deliberately NOT verify-bound — c̃/z/hint are private witness in the
        // hosted design (the statement proves "∃ valid signature under this
        // key over this message"); the tampered-signature negative lives at
        // the native layer (`ts13_mldsa_revocation_native_positive_and_negatives`)
        // and at prove (an invalid witness cannot satisfy the constraints).
        let mut revocation_key_tamper = statement.clone();
        match &mut revocation_key_tamper
            .ts13_revocation
            .as_mut()
            .expect("statement carries revocation inputs")
            .revocation_public_key
        {
            MdocRevocationKey::MlDsa(pk) => pk[0] ^= 0x01,
        }
        verify_mdoc_circuit(&proof, &revocation_key_tamper)
            .expect_err("tampered revocation public key must reject");
    }

    /// Direct-provider tamper: change one private bound byte without replacing
    /// the revocation signature. The range AIR then provides a different raw
    /// message than the hosted ML-DSA witness can authenticate, so proving or
    /// verification must reject.
    #[test]
    fn mldsa_revocation_provider_message_tamper_rejects() {
        let (extracted, statement) = full_pq_extracted_and_statement();
        let (mut statement, _, _) = with_mldsa_revocation(statement, &extracted);
        statement
            .ts13_revocation_range
            .as_mut()
            .expect("revocation range")
            .id_lo += 1;

        let rejected = match prove_mdoc_circuit(&extracted, &statement) {
            Err(_) => true,
            Ok(proof) => verify_mdoc_circuit(&proof, &statement).is_err(),
        };
        assert!(rejected, "tampered direct-provider message must reject");
    }

    /// S4 statement-side message tamper: flip one PUBLIC issuer-message byte
    /// in the statement AFTER proving. The public-message producer's
    /// preprocessed content (content-hash ids, root-pinned) and the FS-mixed
    /// message diverge from the proof's transcript → verify must reject.
    #[test]
    fn mldsa_mdoc_statement_message_tamper_rejects() {
        let (extracted, statement) = full_pq_extracted_and_statement();
        let proof = prove_mdoc_circuit(&extracted, &statement).expect("honest prove");
        let mut tampered = statement.clone();
        use eu_id_prover::mdoc::IssuerAuthInput;
        match &mut tampered.issuer_input {
            IssuerAuthInput::MlDsa(input) => input.message[2] ^= 0x01,
        }
        verify_mdoc_circuit(&proof, &tampered)
            .expect_err("tampered statement issuer message must reject");
    }

    /// The F-ROOT pin on the fully-PQ mdoc path: the verifier derives the
    /// expected tree-0 (preprocessed) root independently and pins it; a
    /// tampered pin is rejected with `PreprocessedRootMismatch` before the
    /// STARK work (G7 companion).
    #[test]
    fn mldsa_mdoc_pins_the_preprocessed_root() {
        let (extracted, statement) = full_pq_extracted_and_statement();
        let config = mdoc_production_pcs_config();
        let proof = prove_mdoc_circuit(&extracted, &statement).expect("fully-PQ mdoc proves");

        let expected_root = mdoc_expected_preprocessed_root(&extracted, &statement, config)
            .expect("expected preprocessed root computes");
        verify_mdoc_circuit_with_pcs_config_and_preprocessed_root(
            &proof,
            &statement,
            config,
            expected_root,
        )
        .expect("honest proof verifies against the derived preprocessed root");

        let mut wrong_root = expected_root;
        wrong_root.0[0] ^= 1;
        assert!(
            matches!(
                verify_mdoc_circuit_with_pcs_config_and_preprocessed_root(
                    &proof, &statement, config, wrong_root,
                ),
                Err(Error::PreprocessedRootMismatch { .. })
            ),
            "a mismatched preprocessed root must be rejected before the STARK check",
        );
    }

    /// Cache-collision regression (G7): two DISTINCT fully-PQ statements
    /// (different session transcripts ⇒ different signatures ⇒ different SIB
    /// squeeze lengths across BOTH the issuer and device instances) share the
    /// same padded shape key; each proof must verify under its OWN derived pin.
    #[test]
    fn mldsa_mdoc_pin_is_per_signature_not_cached() {
        let config = mdoc_production_pcs_config();
        let (extracted_a, statement_a) = full_pq_extracted_and_statement_for(b"nonce-A");
        let (extracted_b, statement_b) = full_pq_extracted_and_statement_for(b"nonce-B");

        let proof_a = prove_mdoc_circuit(&extracted_a, &statement_a).expect("proof A proves");
        let proof_b = prove_mdoc_circuit(&extracted_b, &statement_b).expect("proof B proves");

        let root_a = mdoc_expected_preprocessed_root(&extracted_a, &statement_a, config)
            .expect("root A computes");
        let root_b = mdoc_expected_preprocessed_root(&extracted_b, &statement_b, config)
            .expect("root B computes");

        verify_mdoc_circuit_with_pcs_config_and_preprocessed_root(
            &proof_a,
            &statement_a,
            config,
            root_a,
        )
        .expect("proof A verifies under its own pin");
        verify_mdoc_circuit_with_pcs_config_and_preprocessed_root(
            &proof_b,
            &statement_b,
            config,
            root_b,
        )
        .expect("proof B verifies under its own pin");
    }

    /// CM-3 same-arm malformed claim tree: a fully-PQ proof produced for one
    /// statement is presented against a DIFFERENT fully-PQ statement. The
    /// claim trees are bound to statement A's public inputs, so verifying
    /// under statement B must reject. Extended for S1: a malformed keccak
    /// SERVICE claim vector (missing / truncated / value-tampered) rejects.
    #[test]
    fn mldsa_malformed_claim_tree_rejects() {
        let (extracted_a, statement_a) = full_pq_extracted_and_statement_for(b"claim-tree-A");
        let (_extracted_b, statement_b) = full_pq_extracted_and_statement_for(b"claim-tree-B");

        let proof_a = prove_mdoc_circuit(&extracted_a, &statement_a).expect("proof A proves");
        verify_mdoc_circuit(&proof_a, &statement_a).expect("control: A verifies under A");
        verify_mdoc_circuit(&proof_a, &statement_b)
            .expect_err("proof A must not verify against a different statement B");

        // S1 service claims, presence gate: an ML-DSA statement whose proof
        // carries NO service claim vector rejects at the shape gate.
        let mut missing_service = proof_a.clone();
        missing_service.keccak_service_claimed_sums = None;
        verify_mdoc_circuit(&missing_service, &statement_a)
            .expect_err("missing keccak service claim vector must reject");

        // S1 service claims, length gate: a truncated vector rejects BEFORE
        // construction (no panic path).
        let mut short_service = proof_a.clone();
        short_service
            .keccak_service_claimed_sums
            .as_mut()
            .expect("proof carries service claims")
            .pop();
        verify_mdoc_circuit(&short_service, &statement_a)
            .expect_err("truncated keccak service claim vector must reject");

        // S1 service claims, value tamper: swapping two claimed sums keeps the
        // shape but diverges the transcript / LogUp total → STARK reject.
        let mut tampered_service = proof_a.clone();
        tampered_service
            .keccak_service_claimed_sums
            .as_mut()
            .expect("proof carries service claims")
            .swap(0, 1);
        verify_mdoc_circuit(&tampered_service, &statement_a)
            .expect_err("tampered keccak service claimed sums must reject");
    }

    /// ZK/A1 smoke: two DISTINCT fully-PQ credentials satisfying the SAME
    /// policy both prove and verify with the same public-statement component
    /// shape. Structural indistinguishability only — not a statistical ZK
    /// claim.
    #[test]
    fn mldsa_two_credentials_same_policy_smoke() {
        let (extracted_a, statement_a) = full_pq_extracted_and_statement_for(b"zk-smoke-A");
        let (extracted_b, statement_b) = full_pq_extracted_and_statement_for(b"zk-smoke-B");
        assert_eq!(
            statement_a.policy, statement_b.policy,
            "smoke precondition: both credentials under one policy"
        );

        let proof_a = prove_mdoc_circuit(&extracted_a, &statement_a).expect("A proves");
        let proof_b = prove_mdoc_circuit(&extracted_b, &statement_b).expect("B proves");
        verify_mdoc_circuit(&proof_a, &statement_a).expect("A verifies");
        verify_mdoc_circuit(&proof_b, &statement_b).expect("B verifies");

        let bd_a = mdoc_proof_byte_breakdown(&proof_a);
        let bd_b = mdoc_proof_byte_breakdown(&proof_b);
        assert_eq!(
            bd_a.stark.commitments, bd_b.stark.commitments,
            "smoke: commitment-tree shape must not vary with the credential"
        );
    }
}
