//! End-to-end SDK timing probe for the dedicated TS13 equality profile.
//!
//! The input is deterministic RustCrypto ML-DSA-65 conformance/demo data. It
//! is not a credential issued by a deployed PQ issuer. Timings include the
//! public SDK envelope and its Bzip2 transport payload, but not network or
//! disk I/O.

#[allow(dead_code)]
#[path = "../../eu-id-prover/tests/mldsa_fixture.rs"]
mod mldsa_fixture;

use std::time::Instant;

use euid_zk_sdk::{
    ts13_default_circuit_hash, ts13_prove_zk_document, ts13_verify_zk_document, Ts13MdocWitness,
    Ts13PresentationRequest,
};
use serde::Deserialize;
use sha2::{Digest, Sha256};

const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const DISTINCTIVE_BOUND_OFFSET: u64 = 0x1122_3344_5566_7788;

/// Mirror only the private SDK envelope layout so the probe can report its
/// compressed inner `MdocProof` separately from the surrounding public
/// metadata.
#[derive(Deserialize)]
struct Ts13ProofEnvelopeForProbe {
    #[allow(dead_code)]
    envelope_format: u16,
    #[allow(dead_code)]
    request_binding_hash: String,
    #[allow(dead_code)]
    mdoc_statement: eu_id_prover::MdocTs13Statement,
    compressed_mdoc_proof: Vec<u8>,
}

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

fn hex_sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn ts13_request(
    session_transcript: Vec<u8>,
    issuer_public_key: &[u8],
    revocation_public_key: Vec<u8>,
) -> Ts13PresentationRequest {
    Ts13PresentationRequest {
        credential_format: "mso_mdoc_zk".to_string(),
        zk_system_id: "stwo-euid-v1".to_string(),
        doctype: PID_DOCTYPE.to_string(),
        namespace: PID_NAMESPACE.to_string(),
        circuit_hash: ts13_default_circuit_hash(),
        num_attributes: 1,
        max_mso_payload_bytes: eu_id_prover::ts13::TS13_MAX_MSO_PAYLOAD_BYTES as u32,
        max_attribute_bytes: 32,
        max_attribute_item_bytes: eu_id_prover::ts13::TS13_MAX_ATTRIBUTE_ITEM_BYTES as u32,
        max_requested_digest_id: eu_id_prover::ts13::TS13_MAX_REQUESTED_DIGEST_ID,
        max_issuer_mldsa_message_bytes: eu_id_prover::ts13::TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES
            as u32,
        max_device_mldsa_message_bytes: eu_id_prover::ts13::TS13_MAX_DEVICE_MLDSA_MESSAGE_BYTES
            as u32,
        merged_sha_slot_log: eu_id_prover::ts13::TS13_MERGED_SHA_SLOT_LOG,
        merged_sha_log_n_rows: eu_id_prover::ts13::TS13_MERGED_SHA_LOG_N_ROWS,
        potential_issuers: 1,
        revocation_enabled: true,
        revocation_id_width_bytes: 8,
        device_auth_profile: "iso18013-5".to_string(),
        current_date_epoch_day: 20_637,
        session_transcript,
        trusted_issuer_hashes: vec![hex_sha256(issuer_public_key)],
        revocation_public_key,
        revocation_epoch: 7,
    }
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
    let (_, revocation_signature) = mldsa_fixture::mldsa_revocation_fixture(id_lo, id_hi, 7);
    let request = ts13_request(
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
    let mut document_wire_bytes = Vec::with_capacity(iterations);
    let mut proof_envelope_bytes = Vec::with_capacity(iterations);
    let mut compressed_inner_proof_bytes = Vec::with_capacity(iterations);
    let mut proof_envelope_metadata_bytes = Vec::with_capacity(iterations);
    let mut first_verify_ms = None;
    let mut final_document_wire_bytes = 0usize;
    let mut final_proof_envelope_bytes = 0usize;
    let mut final_compressed_inner_proof_bytes = 0usize;
    let mut final_proof_envelope_metadata_bytes = 0usize;

    for _ in 0..iterations {
        let prove_start = Instant::now();
        let document = ts13_prove_zk_document(
            request.clone(),
            Ts13MdocWitness {
                document: fixture.document.clone(),
                trusted_issuer_public_keys: vec![fixture.issuer_pk.clone()],
                revocation_id_lo: id_lo,
                revocation_id_hi: id_hi,
                revocation_signature: revocation_signature.clone(),
            },
        )
        .expect("SDK TS13 equality proof builds");
        prove_ms.push(prove_start.elapsed().as_millis());

        let envelope: Ts13ProofEnvelopeForProbe =
            bincode::deserialize(&document.proof).expect("SDK TS13 envelope decodes");
        let serialized_document =
            bincode::serialize(&document).expect("complete SDK TS13 document serializes");
        let metadata_bytes = document.proof.len() - envelope.compressed_mdoc_proof.len();
        document_wire_bytes.push(serialized_document.len() as u128);
        proof_envelope_bytes.push(document.proof.len() as u128);
        compressed_inner_proof_bytes.push(envelope.compressed_mdoc_proof.len() as u128);
        proof_envelope_metadata_bytes.push(metadata_bytes as u128);
        final_document_wire_bytes = serialized_document.len();
        final_proof_envelope_bytes = document.proof.len();
        final_compressed_inner_proof_bytes = envelope.compressed_mdoc_proof.len();
        final_proof_envelope_metadata_bytes = metadata_bytes;

        let verify_start = Instant::now();
        assert!(
            ts13_verify_zk_document(&request, &document).expect("SDK TS13 verification runs"),
            "SDK TS13 equality envelope verifies"
        );
        let elapsed = verify_start.elapsed().as_millis();
        first_verify_ms.get_or_insert(elapsed);
        verify_ms.push(elapsed);
    }

    println!(
        "TS13_SDK_PERF_PROBE zero_knowledge=false fixture=deterministic_rustcrypto_mldsa65_realistic_7_attribute_pid_demo_not_deployed_credential verify_scope=first_verification_is_tree0_cache_miss_after_prover_warmed_process iterations={iterations} rayon_threads={} sdk_prove_median_ms={} sdk_verify_first_ms={} sdk_verify_median_ms={} final_document_wire_bytes={final_document_wire_bytes} final_proof_envelope_bytes={final_proof_envelope_bytes} final_compressed_inner_mdoc_proof_bytes={final_compressed_inner_proof_bytes} final_proof_envelope_public_metadata_bytes={final_proof_envelope_metadata_bytes} document_wire_median_bytes={} proof_envelope_median_bytes={} compressed_inner_mdoc_proof_median_bytes={} proof_envelope_public_metadata_median_bytes={} fixture_document_bytes={} fixture_issuer_sig_structure_bytes={} fixture_device_sig_structure_bytes={} session_transcript_bytes={}",
        rayon::current_num_threads(),
        median(&mut prove_ms),
        first_verify_ms.expect("at least one probe iteration"),
        median(&mut verify_ms),
        median(&mut document_wire_bytes),
        median(&mut proof_envelope_bytes),
        median(&mut compressed_inner_proof_bytes),
        median(&mut proof_envelope_metadata_bytes),
        fixture.document.len(),
        fixture.issuer_sig_structure.len(),
        fixture.device_sig_structure.len(),
        extraction_request.session_transcript.len(),
    );
}
