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
    extract_pid_mdoc, openid4vp_session_transcript, ExtractedPidMdoc, MdocAuthInput,
    MdocCircuitStatement, MdocError, MdocPidRequest, MdocRevocationKey, MdocRevocationPublicInputs,
    MdocRevocationRangeWitness, MdocRevocationSignature,
};
use eu_id_prover::ts13::{
    ts13_default_circuit_hash, ts13_mso_derived_revocation_id, Ts13MdocProofArtifact,
    Ts13RevocationError, Ts13RevocationStatement, Ts13RevocationWitness,
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
        mdoc_production_pcs_config, mdoc_proof_byte_breakdown, prove_mdoc_circuit,
        verify_mdoc_circuit, verify_mdoc_circuit_with_pcs_config_profiled,
        verify_mdoc_circuit_with_pcs_config_profiled_fresh,
    };
    use std::time::Instant;
    use stwo::core::fields::{m31::M31, qm31::QM31};

    fn sib_consumed_len(input: &stwo_mldsa::types::MlDsaVerifyInput) -> usize {
        let stream = stwo_mldsa::reference::sample_in_ball::sample_in_ball(&input.c_tilde)
            .transcript
            .squeezed;
        let mut position = 8;
        for i in (stwo_mldsa::constants::N - stwo_mldsa::constants::TAU)..stwo_mldsa::constants::N {
            loop {
                let byte = stream[position];
                position += 1;
                if usize::from(byte) <= i {
                    break;
                }
            }
        }
        position
    }

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

    /// Age-only presentation (the SDK's PredicateMode::Age): the request
    /// carries ONLY the birth_date/AgeOver attribute and the policy has no
    /// accepted nationalities. The credential still contains nationality —
    /// it simply is not requested. Regression for the SDK bug where age-only
    /// statements unconditionally demanded the nationality element
    /// (ElementMissing on credentials/disclosures without it).
    #[test]
    fn age_only_mdoc_proves_and_verifies() {
        let session_transcript = openid4vp_session_transcript(b"age-only-session");
        let fixture =
            mldsa_fixture::mldsa_full_pq_fixture_with_transcript(&session_transcript);
        let mut request = MdocPidRequest::eudi_pid(session_transcript)
            .with_trusted_mldsa_issuer_public_keys(vec![fixture.issuer_pk.clone()]);
        request.attributes = vec![eu_id_prover::mdoc::MdocRequestedAttribute {
            element_identifier: "birth_date".to_string(),
            mode: eu_id_prover::mdoc::MdocDisclosureMode::AgeOver,
        }];
        let extracted =
            extract_pid_mdoc(&fixture.document, &request).expect("age-only mdoc extracts");
        let policy = Policy {
            accepted_nationalities: Vec::new(),
            accepted_nationalities_alpha2: Vec::new(),
            ..demo_policy()
        };
        let statement = MdocCircuitStatement::from_extracted(&extracted, policy)
            .expect("age-only statement builds");
        let proof =
            prove_mdoc_circuit(&extracted, &statement).expect("age-only mdoc proves");
        verify_mdoc_circuit(&proof, &statement).expect("age-only mdoc verifies");
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

        // Q14 soundness spine: drift one hosted instance's coeffs/use-side
        // accounting while leaving the single summed range-table claim intact.
        // The proof-wide LogUp balance must reject the joint mismatch.
        let mut range_use_tamper = proof.clone();
        range_use_tamper
            .mldsa
            .as_mut()
            .expect("issuer ML-DSA claims")
            .claimed_sums[0] += QM31::from(M31::from_u32_unchecked(1));
        let error = verify_mdoc_circuit(&range_use_tamper, &statement)
            .expect_err("one-instance range-use accounting drift must reject");
        assert!(
            format!("{error:?}").contains("LogUp claimed sums do not cancel"),
            "unexpected joint-balance rejection: {error:?}"
        );

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

        // The TS13 artifact carries no tree-0 authority; verification derives
        // the canonical commitment internally from the public statement.
        let revocation_public = statement
            .ts13_revocation
            .as_ref()
            .expect("statement carries revocation public inputs");
        let revocation_range = statement
            .ts13_revocation_range
            .as_ref()
            .expect("statement carries revocation range");
        let artifact = Ts13MdocProofArtifact {
            circuit_hash: ts13_default_circuit_hash(),
            mdoc_proof: proof_bytes.clone(),
            revocation_statement: Ts13RevocationStatement {
                revocation_public_key: revocation_public.revocation_public_key.clone(),
                epoch: revocation_public.epoch,
            },
            revocation_witness: Ts13RevocationWitness {
                id: revocation_range.id,
                id_lo: revocation_range.id_lo,
                id_hi: revocation_range.id_hi,
                epoch: revocation_public.epoch,
                signature: statement
                    .ts13_revocation_signature
                    .clone()
                    .expect("statement carries revocation signature"),
            },
        };
        artifact
            .verify_mdoc_and_revocation(&extracted, &statement)
            .expect("TS13 artifact verifies with internal tree-0 reconstruction");

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

        // Q11: each hosted role binds verifier-native ExpandA(ρ) and t1 to
        // the transcript-mixed public key. Statement-side mutations reject.
        for tamper_t1 in [false, true] {
            let mut tampered = statement.clone();
            let eu_id_prover::mdoc::MdocAuthInput::MlDsa(input) = &mut tampered.issuer_input;
            if tamper_t1 {
                input.t1[0][0] ^= 1;
            } else {
                input.rho[0] ^= 1;
            }
            verify_mdoc_circuit(&proof, &tampered).expect_err("tampered issuer rho/t1 must reject");
        }
        for tamper_t1 in [false, true] {
            let mut tampered = statement.clone();
            let eu_id_prover::mdoc::MdocAuthInput::MlDsa(input) = &mut tampered.device_input;
            if tamper_t1 {
                input.t1[0][0] ^= 1;
            } else {
                input.rho[0] ^= 1;
            }
            verify_mdoc_circuit(&proof, &tampered).expect_err("tampered device rho/t1 must reject");
        }
        for tamper_t1 in [false, true] {
            let mut tampered = statement.clone();
            let MdocRevocationKey::MlDsa(pk) = &mut tampered
                .ts13_revocation
                .as_mut()
                .expect("statement carries revocation inputs")
                .revocation_public_key;
            if tamper_t1 {
                let decoded = stwo_mldsa::reference::encoding::pk_decode(pk).unwrap();
                let mut t1 = decoded.t1;
                t1[0][0] ^= 1;
                *pk = stwo_mldsa::reference::encoding::pk_encode(&decoded.rho, &t1);
            } else {
                pk[0] ^= 1;
            }
            verify_mdoc_circuit(&proof, &tampered)
                .expect_err("tampered revocation rho/t1 must reject");
        }

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

    #[test]
    fn legacy_coeffs_interaction_arity_rejects_without_panicking() {
        const LEGACY_COEFFS_INTERACTION_COLUMN_DELTA: usize = 3 * (56 - 20);

        let (extracted, statement) = full_pq_extracted_and_statement();
        let (statement, _, _) = with_mldsa_revocation(statement, &extracted);
        let mut proof = prove_mdoc_circuit(&extracted, &statement).expect("fully-PQ mdoc proves");
        let expected_interaction_columns = proof.stark_proof.0.sampled_values[2].len();
        let legacy_interaction_columns =
            expected_interaction_columns + LEGACY_COEFFS_INTERACTION_COLUMN_DELTA;

        let sampled_filler = proof.stark_proof.0.sampled_values[2]
            .last()
            .expect("interaction tree has sampled columns")
            .clone();
        let queried_filler = proof.stark_proof.0.queried_values[2]
            .last()
            .expect("interaction tree has queried columns")
            .clone();
        proof.stark_proof.0.sampled_values[2].extend(std::iter::repeat_n(
            sampled_filler,
            LEGACY_COEFFS_INTERACTION_COLUMN_DELTA,
        ));
        proof.stark_proof.0.queried_values[2].extend(std::iter::repeat_n(
            queried_filler,
            LEGACY_COEFFS_INTERACTION_COLUMN_DELTA,
        ));

        // Keep the outer catch as an abort detector: without the air-core
        // arity gate, the engine panic plus LogUp drop panic aborts here.
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            verify_mdoc_circuit(&proof, &statement)
        }));
        match result {
            Ok(Err(eu_id_prover::Error::Verify(message))) => {
                assert!(message.contains("tree=interaction"), "{message}");
                assert!(
                    message.contains(&format!("expected={expected_interaction_columns}")),
                    "{message}"
                );
                assert!(
                    message.contains(&format!("got={legacy_interaction_columns}")),
                    "{message}"
                );
            }
            other => panic!("expected typed legacy-layout rejection, got {other:?}"),
        }
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

    /// Q12 statement-side M′ tamper: flip one PUBLIC issuer/device message byte
    /// after proving. Since pure-mode `M′ = 0x00 || 0x00 || M`, the
    /// verifier-native µ and the FS-mixed message diverge from the proof.
    #[test]
    fn mldsa_mdoc_statement_message_tampers_reject() {
        let (extracted, statement) = full_pq_extracted_and_statement();
        let proof = prove_mdoc_circuit(&extracted, &statement).expect("honest prove");

        let mut issuer_tampered = statement.clone();
        match &mut issuer_tampered.issuer_input {
            MdocAuthInput::MlDsa(input) => input.message[2] ^= 0x01,
        }
        verify_mdoc_circuit(&proof, &issuer_tampered)
            .expect_err("tampered statement issuer M′ must reject");

        let mut device_tampered = statement;
        match &mut device_tampered.device_input {
            MdocAuthInput::MlDsa(input) => input.message[2] ^= 0x01,
        }
        verify_mdoc_circuit(&proof, &device_tampered)
            .expect_err("tampered statement device M′ must reject");
    }

    /// A forged proof root is rejected before and after memoization. A failed
    /// cold verification must not populate the cache, and a non-canonical
    /// decoded public key is rejected without accepting any artifact root as
    /// authority.
    #[test]
    fn mldsa_mdoc_reconstructs_tree0_and_gates_public_shape() {
        let (extracted, mut statement) = full_pq_extracted_and_statement();
        // Give this test a unique valid policy key so its first lookup is cold
        // regardless of the rest of this process-global-cache test binary.
        statement.policy.accepted_nationalities_alpha2.push(*b"PL");
        let proof = prove_mdoc_circuit(&extracted, &statement).expect("fully-PQ mdoc proves");

        let mut forged_root = proof.clone();
        forged_root.stark_proof.0.commitments[0].0[0] ^= 1;
        verify_mdoc_circuit(&forged_root, &statement)
            .expect_err("a forged tree-0 commitment must reject cold");
        let cold = verify_mdoc_circuit_with_pcs_config_profiled(
            &proof,
            &statement,
            mdoc_production_pcs_config(),
        )
        .expect("honest proof verifies after failed cold tamper");
        assert!(
            !cold.tree0_cache_hit,
            "a failed verification must not populate the root cache"
        );
        verify_mdoc_circuit(&forged_root, &statement)
            .expect_err("a forged tree-0 commitment must also reject warm");
        let warm = verify_mdoc_circuit_with_pcs_config_profiled(
            &proof,
            &statement,
            mdoc_production_pcs_config(),
        )
        .expect("honest proof verifies warm");
        assert!(warm.tree0_cache_hit);

        let mut noncanonical_t1 = statement.clone();
        let eu_id_prover::mdoc::IssuerAuthInput::MlDsa(input) = &mut noncanonical_t1.issuer_input;
        input.t1[0][0] = stwo_mldsa::types::T1_COEFFICIENT_BOUND;
        verify_mdoc_circuit(&proof, &noncanonical_t1)
            .expect_err("a non-canonical public t1 must reject at verify entry");
        assert!(
            prove_mdoc_circuit(&extracted, &noncanonical_t1).is_err(),
            "a non-canonical public t1 must reject at prove entry"
        );
    }

    /// Q13 regression: signature-dependent rejection history cannot affect
    /// tree 0. Distinct real signatures with different SIB consumption share
    /// one canonical root and warm cache entry; a changed RP policy gets a
    /// distinct root/cache miss, and the fresh audit path agrees with cache.
    #[test]
    fn mldsa_mdoc_tree0_is_signature_independent_and_policy_cached() {
        let (extracted_a, mut statement_a) = full_pq_extracted_and_statement_for(b"nonce-A");
        let (extracted_b, mut statement_b) = full_pq_extracted_and_statement_for(b"nonce-B");
        statement_a
            .policy
            .accepted_nationalities_alpha2
            .push(*b"ES");
        statement_b.policy = statement_a.policy.clone();

        let consumed_a = [
            sib_consumed_len(
                statement_a
                    .issuer_input
                    .as_mldsa()
                    .expect("issuer A is ML-DSA"),
            ),
            sib_consumed_len(
                statement_a
                    .device_input
                    .as_mldsa()
                    .expect("device A is ML-DSA"),
            ),
        ];
        let consumed_b = [
            sib_consumed_len(
                statement_b
                    .issuer_input
                    .as_mldsa()
                    .expect("issuer B is ML-DSA"),
            ),
            sib_consumed_len(
                statement_b
                    .device_input
                    .as_mldsa()
                    .expect("device B is ML-DSA"),
            ),
        ];
        assert_ne!(
            consumed_a, consumed_b,
            "test vectors must exercise distinct rejection histories"
        );

        let proof_a = prove_mdoc_circuit(&extracted_a, &statement_a).expect("proof A proves");
        let proof_b = prove_mdoc_circuit(&extracted_b, &statement_b).expect("proof B proves");

        assert_eq!(
            proof_a.stark_proof.commitments[0], proof_b.stark_proof.commitments[0],
            "SIB rejection history must not affect canonical preprocessing"
        );
        let cold = verify_mdoc_circuit_with_pcs_config_profiled(
            &proof_a,
            &statement_a,
            mdoc_production_pcs_config(),
        )
        .expect("proof A verifies cold");
        assert!(!cold.tree0_cache_hit);
        let warm = verify_mdoc_circuit_with_pcs_config_profiled(
            &proof_b,
            &statement_b,
            mdoc_production_pcs_config(),
        )
        .expect("proof B verifies through the same policy entry");
        assert!(warm.tree0_cache_hit);
        let fresh = verify_mdoc_circuit_with_pcs_config_profiled_fresh(
            &proof_b,
            &statement_b,
            mdoc_production_pcs_config(),
        )
        .expect("fresh canonical root agrees with the memoized root");
        assert!(!fresh.tree0_cache_hit);

        let mut statement_c = statement_b.clone();
        statement_c
            .policy
            .accepted_nationalities_alpha2
            .push(*b"IT");
        let proof_c = prove_mdoc_circuit(&extracted_b, &statement_c).expect("proof C proves");
        assert_ne!(
            proof_a.stark_proof.commitments[0], proof_c.stark_proof.commitments[0],
            "a different RP policy must produce a different canonical root"
        );
        let other_policy = verify_mdoc_circuit_with_pcs_config_profiled(
            &proof_c,
            &statement_c,
            mdoc_production_pcs_config(),
        )
        .expect("different policy verifies after its own recomputation");
        assert!(!other_policy.tree0_cache_hit);
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

        let mut tampered_group_eval = proof_a.clone();
        tampered_group_eval
            .mldsa
            .as_mut()
            .expect("issuer claims")
            .group_evals[0] += stwo::core::fields::qm31::SecureField::from(
            stwo::core::fields::m31::M31::from_u32_unchecked(1),
        );
        verify_mdoc_circuit(&tampered_group_eval, &statement_a)
            .expect_err("tampered coefficient evaluation must reject");

        let mut short_group_evals = proof_a.clone();
        short_group_evals
            .mldsa
            .as_mut()
            .expect("issuer claims")
            .group_evals
            .pop();
        verify_mdoc_circuit(&short_group_evals, &statement_a)
            .expect_err("malformed coefficient-eval shape must reject before construction");

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
