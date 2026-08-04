//! Sole release/LTO measurement harness for the exact `prove_identity` and
//! `verify_identity` application API.
//!
//! `EUID_PROBE_MODE` selects `roundtrip`, `prove`, or `verify`.
//! `EUID_PROOF_OUT` writes the last proof made by `roundtrip` or `prove`.
//! `EUID_PROOF_IN` supplies a proof to `verify`.
//! `BENCH_ITERS` must be odd and at least three. It defaults to nine.

// No #[global_allocator] here: the SDK crate itself installs mimalloc, so the
// example inherits the production allocator.

use std::{fmt::Write as _, fs, path::PathBuf, time::Instant};

use euid_zk_sdk::{
    product_circuit_hash, product_profile_id, product_root_policy_hash, prove_identity,
    verify_identity, PredicateMode, ZkMdocWitness, ZkPublicStatement,
};
use sha2::{Digest, Sha256};

fn hex(bytes: &[u8]) -> String {
    bytes.iter().fold(
        String::with_capacity(bytes.len() * 2),
        |mut output, byte| {
            write!(output, "{byte:02x}").expect("writing to a String cannot fail");
            output
        },
    )
}

fn envelope_sha256(envelope: &[u8]) -> String {
    hex(&Sha256::digest(envelope))
}

fn envelope_version(envelope: &[u8]) -> Option<u16> {
    let prefix: [u8; 2] = envelope.get(..2)?.try_into().ok()?;
    Some(u16::from_le_bytes(prefix))
}

fn raw_stark_proof(envelope: &[u8]) -> Option<Vec<u8>> {
    const HEADER_BYTES: usize = 2 + 8;
    const MAX_RAW_PROOF_BYTES: usize = 16 * 1024 * 1024;

    if envelope_version(envelope)? != 8 {
        return None;
    }
    let compressed_len = u64::from_le_bytes(envelope.get(2..HEADER_BYTES)?.try_into().ok()?);
    let compressed_len = usize::try_from(compressed_len).ok()?;
    let compressed = envelope.get(HEADER_BYTES..)?;
    if compressed.len() != compressed_len {
        return None;
    }
    zstd::bulk::decompress(compressed, MAX_RAW_PROOF_BYTES).ok()
}

fn fixture() -> (ZkPublicStatement, ZkMdocWitness) {
    let fixture = eu_id_prover::mdoc::demo_mdoc_circuit_fixture();
    let issuer_key = fixture.statement.issuer_input.public_key.clone();
    let (revocation, revocation_witness) =
        eu_id_prover::ts13::demo_ts13_revocation_inputs(&fixture.extracted.mso);
    let mut accepted_alpha2_countries = fixture
        .statement
        .policy
        .accepted_nationalities
        .iter()
        .map(|country| String::from_utf8(country.to_vec()).expect("fixture alpha-2 is ASCII"))
        .collect::<Vec<_>>();
    accepted_alpha2_countries.sort_unstable();
    accepted_alpha2_countries.dedup();
    (
        ZkPublicStatement {
            spec_id: "stwo-euid-pid-v1".to_string(),
            version: 2,
            profile_id: product_profile_id(),
            circuit_hash: product_circuit_hash(),
            root_policy_hash: product_root_policy_hash(),
            doctype: fixture.request.doctype,
            namespace: fixture.request.namespace,
            issuer_public_key_x: issuer_key.x.0.to_vec(),
            issuer_public_key_y: issuer_key.y.0.to_vec(),
            now_epoch_seconds: 20_637 * 86_400 + 43_200,
            session_transcript: fixture.request.session_transcript,
            predicate_mode: PredicateMode::And,
            age_threshold_years: Some(fixture.statement.policy.min_age_years),
            accepted_alpha2_countries: Some(accepted_alpha2_countries),
            revocation_public_key_x: revocation.revocation_public_key.x.0.to_vec(),
            revocation_public_key_y: revocation.revocation_public_key.y.0.to_vec(),
            revocation_epoch: revocation.epoch,
        },
        ZkMdocWitness {
            document: fixture.document,
            revocation_id_lo: revocation_witness.id_lo,
            revocation_id_hi: revocation_witness.id_hi,
            revocation_signature_r: revocation_witness.signature.r.0.to_vec(),
            revocation_signature_s: revocation_witness.signature.s.0.to_vec(),
        },
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProbeMode {
    Roundtrip,
    Prove,
    Verify,
}

impl ProbeMode {
    fn from_environment() -> Self {
        match std::env::var("EUID_PROBE_MODE").as_deref() {
            Ok("prove") => Self::Prove,
            Ok("verify") => Self::Verify,
            Ok("roundtrip") | Err(_) => Self::Roundtrip,
            Ok(value) => panic!("unsupported EUID_PROBE_MODE `{value}`"),
        }
    }

    fn as_str(self) -> &'static str {
        match self {
            Self::Roundtrip => "roundtrip",
            Self::Prove => "prove",
            Self::Verify => "verify",
        }
    }
}

fn benchmark_iterations() -> usize {
    let iterations = std::env::var("BENCH_ITERS")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(9);
    assert!(
        iterations >= 3 && iterations % 2 == 1,
        "BENCH_ITERS must be odd and at least three"
    );
    iterations
}

fn proof_path(variable: &str) -> Option<PathBuf> {
    std::env::var_os(variable).map(PathBuf::from)
}

fn main() {
    let mode = ProbeMode::from_environment();
    let iters = benchmark_iterations();
    let (statement, witness) = fixture();
    let statement_version = statement.version;

    let mut prove_ms = Vec::new();
    let mut envelope_bytes = Vec::new();
    let mut envelope_sha256_all = Vec::new();
    let mut proof = if mode == ProbeMode::Verify {
        let path = proof_path("EUID_PROOF_IN")
            .expect("EUID_PROOF_IN is required when EUID_PROBE_MODE=verify");
        fs::read(&path)
            .unwrap_or_else(|error| panic!("failed to read proof from {}: {error}", path.display()))
    } else {
        Vec::new()
    };

    if mode != ProbeMode::Verify {
        for _ in 0..iters {
            let (s, w) = (statement.clone(), witness.clone());
            let start = Instant::now();
            proof = prove_identity(s, w).expect("identity proof builds");
            prove_ms.push(start.elapsed().as_millis());
            envelope_bytes.push(proof.len());
            envelope_sha256_all.push(envelope_sha256(&proof));
        }
        if let Some(path) = proof_path("EUID_PROOF_OUT") {
            fs::write(&path, &proof).unwrap_or_else(|error| {
                panic!("failed to write proof to {}: {error}", path.display())
            });
        }
    } else {
        envelope_bytes.push(proof.len());
        envelope_sha256_all.push(envelope_sha256(&proof));
    }

    let mut verify_ms = Vec::new();
    if mode != ProbeMode::Prove {
        for _ in 0..iters {
            let (s, p) = (statement.clone(), proof.clone());
            let start = Instant::now();
            let result = verify_identity(s, p).expect("verify returns");
            verify_ms.push(start.elapsed().as_millis());
            assert!(result.ok, "identity proof must verify");
        }
    }

    let raw_proof = raw_stark_proof(&proof).expect("V8 envelope contains one bounded zstd proof");
    let dob = b"1990-07-15";
    let dob_ascii_in_compressed_proof = proof.windows(dob.len()).any(|window| window == dob);
    let dob_ascii_in_raw_proof = raw_proof.windows(dob.len()).any(|window| window == dob);
    let rayon_num_threads = std::env::var("RAYON_NUM_THREADS")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .map_or_else(|| "null".to_string(), |value| value.to_string());
    let envelope_version =
        envelope_version(&proof).map_or_else(|| "null".to_string(), |value| value.to_string());

    println!(
        "{{\"api\":\"proveIdentity/verifyIdentity\",\"mode\":\"{}\",\"rayon_num_threads\":{rayon_num_threads},\"iters\":{iters},\"envelope_version\":{envelope_version},\"statement_version\":{statement_version},\"profile_id\":\"{}\",\"circuit_hash\":\"{}\",\"root_policy_hash\":\"{}\",\"envelope_bytes_all\":{envelope_bytes:?},\"envelope_sha256_all\":{envelope_sha256_all:?},\"raw_proof_bytes\":{},\"prove_ms_all\":{prove_ms:?},\"verify_ms_all\":{verify_ms:?},\"dob_ascii_in_compressed_proof\":{dob_ascii_in_compressed_proof},\"dob_ascii_in_raw_proof\":{dob_ascii_in_raw_proof}}}",
        mode.as_str(),
        product_profile_id(),
        product_circuit_hash(),
        hex(&product_root_policy_hash()),
        raw_proof.len(),
    );
}
