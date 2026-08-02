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
        ts13_demo::prove_identity_inner(&statement, witness)
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
mod tests {
    use super::*;

    #[test]
    fn uses_the_canonical_worker_count() {
        let workers = with_proof_runtime(IdentityError::ProofGenerationFailed, || {
            Ok(rayon::current_num_threads())
        })
        .expect("the canonical proof runtime must start");

        assert_eq!(workers, PROOF_WORKER_COUNT);
    }
}
