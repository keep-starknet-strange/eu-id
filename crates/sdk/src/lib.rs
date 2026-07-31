//! Native API for the public-input-unlinkable TS13 identity proof.

mod ts13_demo;

pub use ts13_demo::{IdentityError, IdentityStatement, IdentityWitness};

uniffi::setup_scaffolding!();

const PROOF_STACK_SIZE: usize = 64 * 1024 * 1024;

fn with_proof_stack<T, F>(failure: IdentityError, work: F) -> Result<T, IdentityError>
where
    T: Send + 'static,
    F: FnOnce() -> Result<T, IdentityError> + Send + 'static,
{
    let handle = std::thread::Builder::new()
        .name("euid-zk".to_string())
        .stack_size(PROOF_STACK_SIZE)
        .spawn(move || {
            let pool = rayon::ThreadPoolBuilder::new()
                .stack_size(PROOF_STACK_SIZE)
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
    with_proof_stack(IdentityError::ProofGenerationFailed, move || {
        ts13_demo::prove_identity_inner(&statement, &witness)
    })
}

/// Verify the TS13 identity proof against the complete public statement.
#[uniffi::export]
pub fn verify_identity(statement: IdentityStatement, proof: Vec<u8>) -> Result<(), IdentityError> {
    with_proof_stack(IdentityError::ProofVerificationFailed, move || {
        ts13_demo::verify_identity_inner(&statement, &proof)
    })
}
