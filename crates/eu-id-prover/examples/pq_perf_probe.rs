//! Full-PQ mdoc perf probe — the S3 campaign's executable perf gate.
//!
//! Builds the fully post-quantum credential (ML-DSA issuer + device + TS13
//! revocation), extracts, proves, forces a fresh tree-0 verification, and
//! reports in-process core timings plus Bzip2 transport measurements. It does
//! not measure document parsing, network transport, or disk I/O.
//!
//! Run (the campaign's iron measurement):
//! ```sh
//! AIR_CORE_PROVE_TIMING=1 RAYON_NUM_THREADS=1 cargo run --release \
//!   -p eu-id-prover --example pq_perf_probe
//! ```

#[allow(dead_code)]
#[path = "../tests/mldsa_fixture.rs"]
mod mldsa_fixture;

const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";

fn main() {
    let iterations = parse_iterations();
    std::thread::Builder::new()
        .name("pq-perf-probe".to_string())
        .stack_size(32 * 1024 * 1024)
        .spawn(move || run(iterations))
        .expect("PQ perf probe worker starts")
        .join()
        .expect("PQ perf probe worker does not panic");
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
        _ => panic!("usage: pq_perf_probe [--iterations N]"),
    }
}

fn median(values: &mut [u128]) -> u128 {
    values.sort_unstable();
    values[values.len() / 2]
}

fn run(iterations: usize) {
    use std::io::{Read, Write};
    use std::time::Instant;

    use bzip2::read::BzDecoder;
    use bzip2::write::BzEncoder;
    use bzip2::Compression;

    use eu_id_prover::mdoc::{
        extract_pid_mdoc, mdoc_proof_byte_breakdown, openid4vp_session_transcript,
        prove_mdoc_circuit, verify_mdoc_circuit_with_pcs_config_profiled_fresh,
        MdocCircuitStatement, MdocDeviceAuthenticationProfile, MdocDisclosureMode, MdocPidRequest,
        MdocRequestedAttribute, MdocRevocationKey, MdocRevocationPublicInputs,
        MdocRevocationRangeWitness, MdocRevocationSignature,
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
    };

    // Fully-PQ TS13 credential: ML-DSA issuer + device + revocation with the
    // profile's single value-equality disclosure.
    let session_transcript = openid4vp_session_transcript(b"session-transcript-123");
    let fixture = mldsa_fixture::mldsa_realistic_pid_fixture_with_age_over_18(&session_transcript);
    let request = MdocPidRequest {
        doctype: PID_DOCTYPE.to_string(),
        namespace: PID_NAMESPACE.to_string(),
        attributes: vec![MdocRequestedAttribute {
            element_identifier: "age_over_18".to_string(),
            mode: MdocDisclosureMode::ValueEquality(vec![0xf5]),
        }],
        birth_date_element: "birth_date".to_string(),
        nationality_element: "nationality".to_string(),
        session_transcript,
        trusted_mldsa_issuer_public_keys: vec![fixture.issuer_pk.clone()],
        device_authentication_profile: MdocDeviceAuthenticationProfile::Iso180135,
    };
    let extracted = extract_pid_mdoc(&fixture.document, &request).expect("fully-PQ mdoc extracts");
    let revocation_sha_rows = stwo_sha256::native::pad_message(&extracted.mso).len();
    let revocation_sha_blocks = revocation_sha_rows / stwo_sha256::constants::BLOCK_BYTES;
    let attribute_loads: Vec<_> = extracted
        .extracted_attributes
        .iter()
        .map(|attribute| {
            let message_bytes = attribute.item.len();
            let padded_blocks = (message_bytes + 1 + 8).div_ceil(64);
            (
                attribute.request.element_identifier.as_str(),
                message_bytes,
                padded_blocks,
            )
        })
        .collect();
    println!(
        "PQ_ATTRIBUTE_LOADS {}",
        serde_json::to_string(&attribute_loads).expect("attribute loads serialize")
    );
    let statement =
        MdocCircuitStatement::from_extracted(&extracted, policy).expect("statement builds");

    const PREFERRED_BOUND_OFFSET: u64 = 0x1122_3344_5566_7788;
    let id = ts13_mso_derived_revocation_id(&extracted.mso);
    let bound_offset = PREFERRED_BOUND_OFFSET.min(id / 2).min((u64::MAX - id) / 2);
    assert!(
        bound_offset > 0,
        "fixture-derived id supports strict bounds"
    );
    let (id_lo, id_hi) = (id - bound_offset, id + bound_offset);
    let epoch = 7u32;
    let (pk, sig) = mldsa_fixture::mldsa_revocation_fixture(id_lo, id_hi, epoch);
    let statement = statement
        .with_ts13_revocation(MdocRevocationPublicInputs {
            revocation_public_key: MdocRevocationKey::MlDsa(pk),
            epoch,
        })
        .with_ts13_revocation_range(MdocRevocationRangeWitness { id, id_lo, id_hi })
        .with_ts13_revocation_signature(MdocRevocationSignature::MlDsa(sig));
    let verifier_statement = statement.clone().into_public_view();

    let rayon_threads = rayon::current_num_threads();
    let mut prove_ms = Vec::with_capacity(iterations);
    let mut fresh_verify_ms = Vec::with_capacity(iterations);
    let mut fresh_tree0_root_ms = Vec::with_capacity(iterations);
    let mut fresh_stark_verify_ms = Vec::with_capacity(iterations);
    let mut bzip2_compress_ms = Vec::with_capacity(iterations);
    let mut bzip2_decompress_ms = Vec::with_capacity(iterations);
    let mut raw_proof_bytes = Vec::with_capacity(iterations);
    let mut bzip2_wire_bytes = Vec::with_capacity(iterations);
    let mut breakdown = None;

    for _ in 0..iterations {
        let prove_start = Instant::now();
        let proof = prove_mdoc_circuit(&extracted, &statement).expect("fully-PQ mdoc proves");
        prove_ms.push(prove_start.elapsed().as_millis());

        let raw = bincode::serialize(&proof).expect("proof serializes");
        let compress_start = Instant::now();
        let mut encoder = BzEncoder::new(Vec::new(), Compression::best());
        encoder.write_all(&raw).expect("proof compresses");
        let wire = encoder.finish().expect("proof compression completes");
        bzip2_compress_ms.push(compress_start.elapsed().as_millis());
        let decompress_start = Instant::now();
        let mut decoded = Vec::new();
        BzDecoder::new(wire.as_slice())
            .read_to_end(&mut decoded)
            .expect("proof decompresses");
        bzip2_decompress_ms.push(decompress_start.elapsed().as_millis());
        assert_eq!(decoded, raw, "Bzip2 wire round trip");
        raw_proof_bytes.push(raw.len() as u128);
        bzip2_wire_bytes.push(wire.len() as u128);

        let fresh_verify_profile = verify_mdoc_circuit_with_pcs_config_profiled_fresh(
            &proof,
            &verifier_statement,
            eu_id_prover::mdoc::mdoc_production_pcs_config(),
        )
        .expect("fully-PQ mdoc verifies with a forced-fresh tree-0 root");
        assert!(
            !fresh_verify_profile.tree0_cache_hit,
            "forced-fresh verification must not use tree-0 cache"
        );
        fresh_verify_ms.push(fresh_verify_profile.total.as_millis());
        fresh_tree0_root_ms.push(fresh_verify_profile.tree0_canonical_root.as_millis());
        fresh_stark_verify_ms.push(fresh_verify_profile.stark_verify.as_millis());
        breakdown = Some(mdoc_proof_byte_breakdown(&proof));
    }

    println!(
        "PQ_PERF_PROBE zero_knowledge=false scope=in_process_core iterations={iterations} rayon_threads={rayon_threads} phase1_prove_ms={} phase1_verify_ms={} phase1_proof_bytes={} phase1_revocation_sha_rows={revocation_sha_rows} phase1_revocation_sha_blocks={revocation_sha_blocks} fresh_tree0_root_median_ms={} fresh_stark_verify_median_ms={} bzip2_compress_median_ms={} bzip2_decompress_median_ms={} bzip2_wire_median_bytes={}",
        median(&mut prove_ms),
        median(&mut fresh_verify_ms),
        median(&mut raw_proof_bytes),
        median(&mut fresh_tree0_root_ms),
        median(&mut fresh_stark_verify_ms),
        median(&mut bzip2_compress_ms),
        median(&mut bzip2_decompress_ms),
        median(&mut bzip2_wire_bytes),
    );
    println!(
        "{}",
        serde_json::to_string(&breakdown.expect("at least one probe iteration"))
            .expect("byte breakdown serializes")
    );
}
