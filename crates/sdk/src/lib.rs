//! Native API for the public-input-unlinkable TS13 identity proof.

mod ts13_demo;

pub use ts13_demo::{IdentityError, IdentityStatement, IdentityWitness};

uniffi::setup_scaffolding!();

const PROOF_THREAD_STACK_SIZE_BYTES: usize = 2 * 1024 * 1024;
const PROOF_WORKER_STACK_SIZE_BYTES: usize = 16 * 1024 * 1024;
const PROOF_WORKER_COUNT: usize = 6;

fn with_proof_runtime<T, F>(failure: IdentityError, work: F) -> Result<T, IdentityError>
where
    T: Send + 'static,
    F: FnOnce() -> Result<T, IdentityError> + Send + 'static,
{
    let handle = std::thread::Builder::new()
        .name("euid-zk".to_string())
        .stack_size(PROOF_THREAD_STACK_SIZE_BYTES)
        .spawn(move || {
            let pool = rayon::ThreadPoolBuilder::new()
                .num_threads(PROOF_WORKER_COUNT)
                .stack_size(PROOF_WORKER_STACK_SIZE_BYTES)
                .thread_name(|index| format!("euid-zk-worker-{index}"))
                .build()
                .map_err(|_| failure)?;
            pool.install(work)
        })
        .map_err(|_| failure)?;
    handle.join().map_err(|_| failure)?
}

/// Create the canonical TS13 identity proof.
#[uniffi::export]
pub fn prove_identity(
    statement: IdentityStatement,
    witness: IdentityWitness,
) -> Result<Vec<u8>, IdentityError> {
    with_proof_runtime(IdentityError::ProofGenerationFailed, move || {
        eu_id_prover::report_prove_runtime_configuration(
            PROOF_THREAD_STACK_SIZE_BYTES,
            PROOF_WORKER_STACK_SIZE_BYTES,
        );
        ts13_demo::prove_identity_inner(&statement, &witness)
    })
}

/// Verify the TS13 identity proof against the complete public statement.
#[uniffi::export]
pub fn verify_identity(statement: IdentityStatement, proof: Vec<u8>) -> Result<(), IdentityError> {
    with_proof_runtime(IdentityError::ProofVerificationFailed, move || {
        ts13_demo::verify_identity_inner(&statement, &proof)
    })
}

#[cfg(test)]
#[allow(dead_code)]
#[path = "../../eu-id-prover/tests/support/mldsa_fixture.rs"]
mod mldsa_fixture;

#[cfg(test)]
mod tests {
    use super::*;

    const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
    const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
    const VERIFY_AT_EPOCH_SECONDS: i64 = 1_798_761_600;
    const REVOCATION_EPOCH: u32 = 17;

    fn identity_statement(
        session_transcript: Vec<u8>,
        issuer_public_key: Vec<u8>,
        revocation_public_key: Vec<u8>,
    ) -> IdentityStatement {
        IdentityStatement {
            circuit_hash: eu_id_prover::ts13_demo_artifact_constants::TS13_DEMO_CIRCUIT_HASH
                .to_vec(),
            zk_system_id: "rp-off-domain-nibble-negative".to_string(),
            document_type: PID_DOCTYPE.to_string(),
            namespace: PID_NAMESPACE.to_string(),
            element_identifier: "age_over_18".to_string(),
            expected_value_cbor: vec![0xf5],
            timestamp_epoch_seconds: VERIFY_AT_EPOCH_SECONDS,
            session_transcript,
            trusted_issuer_public_key: issuer_public_key,
            revocation_public_key,
            revocation_epoch: REVOCATION_EPOCH,
        }
    }

    #[test]
    fn uses_the_canonical_worker_count() {
        let workers = with_proof_runtime(IdentityError::ProofGenerationFailed, || {
            Ok(rayon::current_num_threads())
        })
        .expect("the canonical proof runtime must start");

        assert_eq!(workers, PROOF_WORKER_COUNT);
    }

    #[test]
    fn verify_identity_rejects_recomposition_neutral_off_domain_keccak_nibbles() {
        let transcript = eu_id_prover::mdoc::openid4vp_session_transcript(
            b"ts13-recomposition-neutral-off-domain-nibble",
        );
        let fixture = mldsa_fixture::mldsa_ts13_credential_a_with_transcript(&transcript);
        let statement = identity_statement(
            transcript,
            fixture.issuer_pk.clone(),
            fixture.revocation_pk.clone(),
        );
        let revocation_id = eu_id_prover::ts13::ts13_mso_derived_revocation_id(&fixture.mso);
        let bound_offset = 0x1122_3344_5566_7788u64
            .min(revocation_id / 2)
            .min((u64::MAX - revocation_id) / 2);
        assert!(bound_offset > 0);
        let revocation_id_lo = revocation_id - bound_offset;
        let revocation_id_hi = revocation_id + bound_offset;
        let (_, revocation_signature) = mldsa_fixture::mldsa_revocation_fixture(
            revocation_id_lo,
            revocation_id_hi,
            REVOCATION_EPOCH,
        );
        let witness = IdentityWitness {
            document: fixture.document,
            revocation_id_lo,
            revocation_id_hi,
            revocation_signature,
        };
        let prover_statement = statement.clone();
        let proof = with_proof_runtime(IdentityError::ProofGenerationFailed, move || {
            let _attack = eu_id_prover::mdoc::install_ts13_keccak_input_nibble_attack();
            ts13_demo::prove_identity_inner(&prover_statement, &witness)
        })
        .expect("the malicious prover must emit an encoded identity proof");

        assert_eq!(
            verify_identity(statement, proof),
            Err(IdentityError::ProofVerificationFailed),
            "verifyIdentity must reject the committed off-domain nibble pair"
        );
    }
}
