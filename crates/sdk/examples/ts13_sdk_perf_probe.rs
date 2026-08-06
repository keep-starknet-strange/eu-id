//! End-to-end timing probe for the canonical TS13 identity API.
//!
//! The deterministic data uses ML-DSA-65 for all signatures.
//! It is not a deployed credential.
//! Timings include the fixed-capacity proof envelope, but not network or disk I/O.

#[allow(dead_code)]
#[path = "../../eu-id-prover/tests/support/mldsa_fixture.rs"]
mod mldsa_fixture;

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::time::Instant;

use euid_zk_sdk::{
    prove_identity, verify_identity, IdentityStatement, IdentityWitness, ZkMdocWitness,
    ZkPublicStatement,
};

const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const DISTINCTIVE_BOUND_OFFSET: u64 = 0x1122_3344_5566_7788;
const VERIFICATION_TIMESTAMP_EPOCH_SECONDS: i64 = 20_637 * 86_400;
const REVOCATION_EPOCH: u32 = 7;
const FIXTURE_NAME: &str = "deterministic-rustcrypto-mldsa65-all-roles-realistic-7-attribute-pid-demo-not-deployed-credential";

struct Config {
    iterations: usize,
    fixture_out: Option<PathBuf>,
}

#[derive(Debug, thiserror::Error)]
enum FixtureWriteError {
    #[error("cannot serialize the mobile fixture")]
    Serialize(#[from] serde_json::Error),
    #[error("cannot write the mobile fixture to {path}")]
    Write {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
}

fn main() {
    run(parse_config());
}

fn parse_config() -> Config {
    let mut args = std::env::args().skip(1);
    let mut config = Config {
        iterations: 1,
        fixture_out: None,
    };
    while let Some(argument) = args.next() {
        match argument.as_str() {
            "--iterations" | "-n" => {
                let value = args.next().expect("--iterations requires a value");
                config.iterations = value
                    .parse::<usize>()
                    .ok()
                    .filter(|iterations| *iterations > 0)
                    .expect("--iterations must be a positive integer");
            }
            "--fixture-out" => {
                let path = args.next().expect("--fixture-out requires a path");
                assert!(config.fixture_out.is_none(), "--fixture-out was repeated");
                config.fixture_out = Some(PathBuf::from(path));
            }
            _ => panic!("usage: ts13_sdk_perf_probe [--iterations N] [--fixture-out PATH]"),
        }
    }
    config
}

fn median(values: &mut [u128]) -> u128 {
    values.sort_unstable();
    values[values.len() / 2]
}

fn identity_statement(
    session_transcript: Vec<u8>,
    issuer_public_key: &[u8],
    revocation_public_key: Vec<u8>,
) -> IdentityStatement {
    IdentityStatement {
        circuit_hash: eu_id_prover::ts13_demo_artifact_constants::TS13_DEMO_CIRCUIT_HASH.to_vec(),
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
    }
}

fn lower_hex(bytes: &[u8]) -> String {
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(&mut output, "{byte:02x}").expect("writing to a String cannot fail");
    }
    output
}

fn write_mobile_fixture(
    path: &Path,
    statement: &IdentityStatement,
    witness: &IdentityWitness,
) -> Result<(), FixtureWriteError> {
    let fixture = serde_json::json!({
        "byteEncoding": "lowercase-hex",
        "fixture": FIXTURE_NAME,
        "kotlinPackage": "com.kss.euid.zk.sdk",
        "privacyClaim": "public-input unlinkable; transcript zero knowledge pending",
        "profile": "ts13-pid-age-over-18-unlinkable-demo-v1",
        "proofSystem": "stwo-euid-ts13-demo-v1",
        "proveApi": "proveIdentity",
        "schema": "euid-ts13-mobile-fixture-v1",
        "statement": {
            "circuitHash": lower_hex(&statement.circuit_hash),
            "documentType": statement.document_type,
            "elementIdentifier": statement.element_identifier,
            "expectedValueCbor": lower_hex(&statement.expected_value_cbor),
            "namespace": statement.namespace,
            "revocationEpoch": statement.revocation_epoch,
            "revocationPublicKey": lower_hex(&statement.revocation_public_key),
            "sessionTranscript": lower_hex(&statement.session_transcript),
            "timestampEpochSeconds": statement.timestamp_epoch_seconds,
            "trustedIssuerPublicKey": lower_hex(&statement.trusted_issuer_public_key),
            "zkSystemId": statement.zk_system_id,
        },
        "statementType": "IdentityStatement",
        "u64Encoding": "decimal-string",
        "verifyApi": "verifyIdentity",
        "witness": {
            "document": lower_hex(&witness.document),
            "revocationIdHi": witness.revocation_id_hi.to_string(),
            "revocationIdLo": witness.revocation_id_lo.to_string(),
            "revocationSignature": lower_hex(&witness.revocation_signature),
        },
        "witnessType": "IdentityWitness",
    });
    let mut encoded = serde_json::to_vec_pretty(&fixture)?;
    encoded.push(b'\n');
    std::fs::write(path, encoded).map_err(|source| FixtureWriteError::Write {
        path: path.to_path_buf(),
        source,
    })
}

fn run(config: Config) {
    let Config {
        iterations,
        fixture_out,
    } = config;
    let session_transcript =
        eu_id_prover::mdoc::openid4vp_session_transcript(b"sdk-ts13-perf-equality-session");
    let fixture = mldsa_fixture::mldsa_realistic_pid_fixture_with_age_over_18(&session_transcript);
    let extraction_request = eu_id_prover::MdocPidRequest::age_over_18(session_transcript.clone());
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
    let witness = IdentityWitness {
        document: fixture.document.clone(),
        revocation_id_lo: id_lo,
        revocation_id_hi: id_hi,
        revocation_signature,
    };
    println!(
        "TS13_SDK_FIXTURE document_bytes={} issuer_sig_structure_bytes={} mso_payload_bytes={} device_sig_structure_bytes={} requested_item_bytes={}",
        fixture.document.len(),
        fixture.issuer_sig_structure.len(),
        extracted.mso.len(),
        fixture.device_sig_structure.len(),
        extracted.attribute.item.len(),
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
            ZkPublicStatement::Ts13DemoV1(statement.clone()),
            ZkMdocWitness::Ts13DemoV1(witness.clone()),
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
        verify_identity(
            ZkPublicStatement::Ts13DemoV1(statement.clone()),
            identity_proof,
        )
        .expect("SDK identity TS13 equality envelope verifies");
        let elapsed = verify_start.elapsed().as_millis();
        first_verify_ms.get_or_insert(elapsed);
        verify_ms.push(elapsed);
    }

    println!(
        "TS13_SDK_PERF_PROBE privacy_claim=public-input_unlinkable_transcript_zero_knowledge_pending fixture={FIXTURE_NAME} verify_scope=first_verification_is_tree0_cache_miss_after_prover_warmed_process iterations={iterations} prove_identity_ms={} verify_identity_first_ms={} verify_identity_median_ms={} final_envelope_bytes={final_proof_envelope_bytes} final_body_capacity={final_proof_body_capacity} envelope_median_bytes={} fixture_document_bytes={} fixture_issuer_sig_structure_bytes={} fixture_device_sig_structure_bytes={} session_transcript_bytes={}",
        median(&mut prove_ms),
        first_verify_ms.expect("at least one probe iteration"),
        median(&mut verify_ms),
        median(&mut proof_envelope_bytes),
        fixture.document.len(),
        fixture.issuer_sig_structure.len(),
        fixture.device_sig_structure.len(),
        statement.session_transcript.len(),
    );

    if let Some(path) = fixture_out {
        write_mobile_fixture(&path, &statement, &witness)
            .unwrap_or_else(|error| panic!("{error}: {error:?}"));
        println!("TS13_MOBILE_FIXTURE path={}", path.display());
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn lower_hex_is_canonical() {
        assert_eq!(super::lower_hex(&[0, 1, 0xab, 0xff]), "0001abff");
    }
}
