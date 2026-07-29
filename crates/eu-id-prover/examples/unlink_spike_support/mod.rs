#[allow(dead_code)]
#[path = "../../tests/mldsa_fixture.rs"]
mod mldsa_fixture;

use std::io::{Read, Write};
use std::time::Instant;

use bzip2::read::BzDecoder;
use bzip2::write::BzEncoder;
use bzip2::Compression;

use eu_id_prover::mdoc::{
    extract_pid_mdoc, mdoc_proof_byte_breakdown, openid4vp_session_transcript, ExtractedPidMdoc,
    MdocCircuitProof, MdocCircuitStatement, MdocCircuitVerifyProfile, MdocPidRequest,
    MdocRevocationKey, MdocRevocationPublicInputs, MdocRevocationRangeWitness,
    MdocRevocationSignature,
};
use eu_id_prover::ts13::ts13_mso_derived_revocation_id;
use eu_id_prover::Policy;

pub const BASELINE_KECCAK_PERMUTATIONS: usize = 37;
#[allow(dead_code)] // The shared support module is compiled once per example.
pub const DUMMY_JOB_KECCAK_PERMUTATIONS: usize = 5;
pub const PROVER_WORKER_STACK_BYTES: usize = 32 * 1024 * 1024;

pub fn run_on_prover_pool<T: Send>(thread_name: &'static str, run: impl FnOnce() -> T + Send) -> T {
    rayon::ThreadPoolBuilder::new()
        .stack_size(PROVER_WORKER_STACK_BYTES)
        .thread_name(move |index| format!("{thread_name}-{index}"))
        .build()
        .expect("unlinkability spike Rayon pool starts")
        .install(run)
}

pub struct ProbeFixture {
    pub extracted: ExtractedPidMdoc,
    pub statement: MdocCircuitStatement,
}

pub struct Measurement {
    pub prove_ms: u128,
    pub verify_ms: u128,
    pub tree0_ms: u128,
    pub stark_verify_ms: u128,
    pub raw_proof_bytes: usize,
    pub bzip2_wire_bytes: usize,
}

pub fn fixture() -> ProbeFixture {
    let policy = Policy {
        current_date: predicates::Date {
            year: 2026,
            month: 7,
            day: 3,
        },
        min_age_years: 18,
        accepted_nationalities: vec![276, 250],
    };
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
    let (pk, signature) = mldsa_fixture::mldsa_revocation_fixture(id_lo, id_hi, epoch);
    let statement = statement
        .with_ts13_revocation(MdocRevocationPublicInputs {
            revocation_public_key: MdocRevocationKey::MlDsa(pk),
            epoch,
        })
        .with_ts13_revocation_range(MdocRevocationRangeWitness { id, id_lo, id_hi })
        .with_ts13_revocation_signature(MdocRevocationSignature::MlDsa(signature));

    ProbeFixture {
        extracted,
        statement,
    }
}

pub fn measure(
    fixture: &ProbeFixture,
    prove: impl FnOnce(
        &ExtractedPidMdoc,
        &MdocCircuitStatement,
    ) -> Result<MdocCircuitProof, eu_id_prover::Error>,
    verify: impl FnOnce(
        &MdocCircuitProof,
        &MdocCircuitStatement,
    ) -> Result<MdocCircuitVerifyProfile, eu_id_prover::Error>,
    reject_mismatch: impl FnOnce(&MdocCircuitProof, &MdocCircuitStatement) -> bool,
) -> Measurement {
    let prove_start = Instant::now();
    let proof = prove(&fixture.extracted, &fixture.statement).expect("unlinkability spike proves");
    let prove_ms = prove_start.elapsed().as_millis();

    let raw = bincode::serialize(&proof).expect("proof serializes");
    let mut encoder = BzEncoder::new(Vec::new(), Compression::best());
    encoder.write_all(&raw).expect("proof compresses");
    let wire = encoder.finish().expect("proof compression completes");
    let mut decoded = Vec::new();
    BzDecoder::new(wire.as_slice())
        .read_to_end(&mut decoded)
        .expect("proof decompresses");
    assert_eq!(decoded, raw, "Bzip2 wire round trip");
    let decoded_proof: MdocCircuitProof =
        bincode::deserialize(&decoded).expect("wire proof deserializes");

    let verifier_statement = fixture.statement.clone().into_public_view();
    let profile =
        verify(&decoded_proof, &verifier_statement).expect("unlinkability spike verifies");
    assert!(
        reject_mismatch(&decoded_proof, &verifier_statement),
        "unlinkability spike mismatch must fail closed"
    );
    assert!(
        !profile.tree0_cache_hit,
        "spike verification must force a fresh tree-0 root"
    );
    println!(
        "{}",
        serde_json::to_string(&mdoc_proof_byte_breakdown(&decoded_proof))
            .expect("byte breakdown serializes")
    );

    Measurement {
        prove_ms,
        verify_ms: profile.total.as_millis(),
        tree0_ms: profile.tree0_canonical_root.as_millis(),
        stark_verify_ms: profile.stark_verify.as_millis(),
        raw_proof_bytes: raw.len(),
        bzip2_wire_bytes: wire.len(),
    }
}

pub fn round_log_size(permutations: usize) -> u32 {
    ((permutations * 24) as u32)
        .next_power_of_two()
        .ilog2()
        .max(stwo::prover::backend::simd::m31::LOG_N_LANES)
}

#[allow(dead_code)] // Used by the Keccak probe, not the µ probe.
pub fn keccak_permutations_with_dummy_jobs(dummy_jobs: usize) -> usize {
    BASELINE_KECCAK_PERMUTATIONS + dummy_jobs * DUMMY_JOB_KECCAK_PERMUTATIONS
}
