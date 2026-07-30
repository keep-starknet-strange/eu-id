//! End-to-end SDK timing probe for the dedicated TS13 equality profile.
//!
//! The input is deterministic RustCrypto ML-DSA-65 conformance/demo data. It
//! is not a credential issued by a deployed PQ issuer. Timings include the
//! fixed-capacity V4 envelope, but not network or disk I/O.

#[allow(dead_code)]
#[path = "../../eu-id-prover/tests/mldsa_fixture.rs"]
mod mldsa_fixture;

use std::time::Instant;

use euid_zk_sdk::{
    prove_identity, ts13_demo_circuit_hash, verify_identity, Ts13DemoPublicStatementV1,
    Ts13DemoWitnessV1, ZkMdocWitness, ZkPublicStatement,
};

const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const DISTINCTIVE_BOUND_OFFSET: u64 = 0x1122_3344_5566_7788;
const VERIFICATION_TIMESTAMP_EPOCH_SECONDS: i64 = 20_637 * 86_400;
const REVOCATION_EPOCH: u32 = 7;

fn main() {
    let iterations = parse_iterations();
    std::thread::Builder::new()
        .name("ts13-sdk-perf-probe".to_string())
        .stack_size(32 * 1024 * 1024)
        .spawn(move || run(iterations))
        .expect("SDK TS13 probe worker starts")
        .join()
        .expect("SDK TS13 probe worker does not panic");
}

fn parse_iterations() -> usize {
    let mut args = std::env::args().skip(1);
    match (args.next().as_deref(), args.next()) {
        (None, None) => 1,
        (Some("--iterations" | "-n"), Some(value)) => value
            .parse::<usize>()
            .ok()
            .filter(|iterations| *iterations > 0)
            .expect("--iterations must be a positive integer"),
        _ => panic!("usage: ts13_sdk_perf_probe [--iterations N]"),
    }
}

fn median(values: &mut [u128]) -> u128 {
    values.sort_unstable();
    values[values.len() / 2]
}

fn identity_statement(
    session_transcript: Vec<u8>,
    issuer_public_key: &[u8],
    revocation_public_key: Vec<u8>,
) -> ZkPublicStatement {
    ZkPublicStatement::Ts13DemoV1(Ts13DemoPublicStatementV1 {
        circuit_hash: ts13_demo_circuit_hash(),
        zk_system_id: "rp-local-perf-probe".to_string(),
        document_type: PID_DOCTYPE.to_string(),
        namespace: PID_NAMESPACE.to_string(),
        element_identifier: "age_over_18".to_string(),
        expected_value_cbor: vec![0xf5],
        timestamp_epoch_seconds: VERIFICATION_TIMESTAMP_EPOCH_SECONDS,
        session_transcript,
        trusted_issuer_public_key: issuer_public_key.to_vec(),
        revocation_public_key,
        revocation_epoch: REVOCATION_EPOCH,
    })
}

fn run(iterations: usize) {
    let session_transcript =
        eu_id_prover::mdoc::openid4vp_session_transcript(b"sdk-ts13-perf-equality-session");
    let fixture = mldsa_fixture::mldsa_realistic_pid_fixture_with_age_over_18(&session_transcript);
    let extraction_request = eu_id_prover::MdocPidRequest {
        doctype: PID_DOCTYPE.to_string(),
        namespace: PID_NAMESPACE.to_string(),
        attributes: vec![eu_id_prover::mdoc::MdocRequestedAttribute {
            element_identifier: "age_over_18".to_string(),
            mode: eu_id_prover::mdoc::MdocDisclosureMode::ValueEquality(vec![0xf5]),
        }],
        birth_date_element: "birth_date".to_string(),
        nationality_element: "nationality".to_string(),
        session_transcript: session_transcript.clone(),
        trusted_mldsa_issuer_public_keys: vec![fixture.issuer_pk.clone()],
        device_authentication_profile:
            eu_id_prover::mdoc::MdocDeviceAuthenticationProfile::Iso180135,
    };
    let extracted = eu_id_prover::mdoc::extract_pid_mdoc(&fixture.document, &extraction_request)
        .expect("deterministic TS13 fixture extracts");
    let id = eu_id_prover::ts13::ts13_mso_derived_revocation_id(&extracted.mso);
    let id_lo = id
        .checked_sub(DISTINCTIVE_BOUND_OFFSET)
        .expect("fixture revocation id is above selected bound offset");
    let id_hi = id
        .checked_add(DISTINCTIVE_BOUND_OFFSET)
        .expect("fixture revocation id is below selected bound offset");
    let (_, revocation_signature) =
        mldsa_fixture::mldsa_revocation_fixture(id_lo, id_hi, REVOCATION_EPOCH);
    let statement = identity_statement(
        session_transcript,
        &fixture.issuer_pk,
        fixture.revocation_pk.clone(),
    );
    println!(
        "TS13_SDK_FIXTURE document_bytes={} issuer_sig_structure_bytes={} mso_payload_bytes={} device_sig_structure_bytes={} requested_item_bytes={}",
        fixture.document.len(),
        fixture.issuer_sig_structure.len(),
        extracted.mso.len(),
        fixture.device_sig_structure.len(),
        extracted.extracted_attributes[0].item.len(),
    );

    let mut prove_ms = Vec::with_capacity(iterations);
    let mut verify_ms = Vec::with_capacity(iterations);
    let mut proof_envelope_bytes = Vec::with_capacity(iterations);
    let mut first_verify_ms = None;
    let mut final_proof_envelope_bytes = 0usize;
    let mut final_proof_body_capacity = 0usize;

    for _ in 0..iterations {
        let prove_start = Instant::now();
        let identity_proof = prove_identity(
            statement.clone(),
            ZkMdocWitness::Ts13DemoV1(Ts13DemoWitnessV1 {
                document: fixture.document.clone(),
                revocation_id_lo: id_lo,
                revocation_id_hi: id_hi,
                revocation_signature: revocation_signature.clone(),
            }),
        )
        .expect("SDK identity TS13 equality proof builds");
        prove_ms.push(prove_start.elapsed().as_millis());

        assert_eq!(&identity_proof[..8], b"EUIDTS13");
        final_proof_body_capacity =
            u32::from_le_bytes(identity_proof[42..46].try_into().unwrap()) as usize;
        assert_eq!(identity_proof.len(), 46 + final_proof_body_capacity);
        proof_envelope_bytes.push(identity_proof.len() as u128);
        final_proof_envelope_bytes = identity_proof.len();

        let verify_start = Instant::now();
        assert!(
            verify_identity(statement.clone(), identity_proof)
                .expect("SDK identity TS13 verification runs")
                .ok,
            "SDK identity TS13 equality envelope verifies"
        );
        let elapsed = verify_start.elapsed().as_millis();
        first_verify_ms.get_or_insert(elapsed);
        verify_ms.push(elapsed);
    }

    println!(
        "TS13_SDK_PERF_PROBE privacy_claim=public-input_unlinkable_transcript_zero_knowledge_pending fixture=deterministic_rustcrypto_mldsa65_realistic_7_attribute_pid_demo_not_deployed_credential verify_scope=first_verification_is_tree0_cache_miss_after_prover_warmed_process iterations={iterations} rayon_threads={} prove_identity_ms={} verify_identity_first_ms={} verify_identity_median_ms={} final_v4_envelope_bytes={final_proof_envelope_bytes} final_v4_body_capacity={final_proof_body_capacity} v4_envelope_median_bytes={} fixture_document_bytes={} fixture_issuer_sig_structure_bytes={} fixture_device_sig_structure_bytes={} session_transcript_bytes={}",
        rayon::current_num_threads(),
        median(&mut prove_ms),
        first_verify_ms.expect("at least one probe iteration"),
        median(&mut verify_ms),
        median(&mut proof_envelope_bytes),
        fixture.document.len(),
        fixture.issuer_sig_structure.len(),
        fixture.device_sig_structure.len(),
        extraction_request.session_transcript.len(),
    );
}
