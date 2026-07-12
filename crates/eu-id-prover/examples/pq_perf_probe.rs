//! Full-PQ mdoc perf probe — the S3 campaign's executable perf gate.
//!
//! Builds the fully post-quantum credential (ML-DSA issuer + device + TS13
//! revocation), extracts, proves ONCE, verifies ONCE, and prints one
//! machine-readable line plus the serde_json proof byte breakdown.
//!
//! Run (the campaign's iron measurement):
//! ```sh
//! AIR_CORE_PROVE_TIMING=1 RAYON_NUM_THREADS=1 cargo run --release \
//!   -p eu-id-prover --example pq_perf_probe \
//!   --no-default-features --features "p256,ml-dsa"
//! ```

#[cfg(not(feature = "ec-coprocessor"))]
#[allow(dead_code)]
#[path = "../tests/mldsa_fixture.rs"]
mod mldsa_fixture;

#[cfg(feature = "ec-coprocessor")]
fn main() {
    eprintln!(
        "pq_perf_probe requires the hosted (non-ec-coprocessor) build: \
         --no-default-features --features \"p256,ml-dsa\""
    );
    std::process::exit(1);
}

#[cfg(not(feature = "ec-coprocessor"))]
fn main() {
    use std::time::Instant;

    use eu_id_prover::mdoc::{
        extract_pid_mdoc, mdoc_proof_byte_breakdown, openid4vp_session_transcript,
        prove_mdoc_circuit, verify_mdoc_circuit, MdocCircuitStatement, MdocPidRequest,
        MdocRevocationKey, MdocRevocationPublicInputs, MdocRevocationRangeWitness,
        MdocRevocationSignature,
    };
    use eu_id_prover::ts13::ts13_mso_derived_revocation_id;
    use eu_id_prover::Policy;

    let policy = Policy {
        current_date: predicates::Date {
            year: 2026,
            month: 7,
            day: 3,
        },
        min_age_years: 18,
        accepted_nationalities: vec![276, 250],
        accepted_nationalities_alpha2: vec![*b"DE", *b"FR"],
    };

    // Fully-PQ credential: ML-DSA issuer + device + revocation (mirrors the
    // `full_pq_mdoc_proves_and_verifies_with_revocation_end_to_end` fixture).
    let session_transcript = openid4vp_session_transcript(b"session-transcript-123");
    let fixture = mldsa_fixture::mldsa_full_pq_fixture_with_transcript(&session_transcript);
    let request = MdocPidRequest::eudi_pid(session_transcript)
        .with_trusted_mldsa_issuer_public_keys(vec![fixture.issuer_pk.clone()]);
    let extracted = extract_pid_mdoc(&fixture.document, &request).expect("fully-PQ mdoc extracts");
    let statement =
        MdocCircuitStatement::from_extracted(&extracted, policy).expect("statement builds");

    const BOUND_OFFSET: u64 = 0x1122_3344_5566_7788;
    let id = ts13_mso_derived_revocation_id(&extracted.mso);
    let (id_lo, id_hi) = (id - BOUND_OFFSET, id + BOUND_OFFSET);
    let epoch = 7u32;
    let (pk, sig) = mldsa_fixture::mldsa_revocation_fixture(id_lo, id_hi, epoch);
    let statement = statement
        .with_ts13_revocation(MdocRevocationPublicInputs {
            revocation_public_key: MdocRevocationKey::MlDsa(pk),
            epoch,
        })
        .with_ts13_revocation_range(MdocRevocationRangeWitness { id, id_lo, id_hi })
        .with_ts13_revocation_signature(MdocRevocationSignature::MlDsa(sig));

    let prove_start = Instant::now();
    let proof = prove_mdoc_circuit(&extracted, &statement).expect("fully-PQ mdoc proves");
    let prove_ms = prove_start.elapsed().as_millis();

    let verify_start = Instant::now();
    verify_mdoc_circuit(&proof, &statement).expect("fully-PQ mdoc verifies");
    let verify_ms = verify_start.elapsed().as_millis();

    let breakdown = mdoc_proof_byte_breakdown(&proof);
    std::fs::write("/tmp/pq_proof.bin", bincode::serialize(&proof).unwrap()).unwrap();
    println!(
        "PQ_PERF_PROBE prove_ms={prove_ms} verify_ms={verify_ms} proof_bytes={}",
        breakdown.proof_bytes
    );
    println!(
        "{}",
        serde_json::to_string(&breakdown).expect("byte breakdown serializes")
    );
}
