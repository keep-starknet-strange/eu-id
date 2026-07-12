//! Quantum-safe EU identity prover.
//!
//! The product path parses an ISO mdoc PID, proves its ML-DSA-65 issuer,
//! device, and optional revocation signatures, and binds the hidden attributes
//! to the verifier's age and nationality policy in one STARK proof.

pub(crate) mod claimed_sum_blinder;
pub mod mdoc;
mod mdoc_validity;
mod mdoc_window_bind;
pub mod policy;
mod public_digest_bind;
pub mod ts13;

use stwo::core::pcs::PcsConfig;

pub use mdoc::{
    MdocCircuitProof as MdocProof, MdocCircuitStatement as MdocStatement, MdocPidRequest,
};
pub use policy::Policy;
pub use predicates::{all_nationality_codes, Date};

/// Build and prove the product mdoc circuit from the document, verifier
/// request, and public policy.
pub fn prove_mdoc(
    document: &[u8],
    request: &MdocPidRequest,
    policy: Policy,
) -> Result<(MdocProof, MdocStatement), Error> {
    let extracted = mdoc::extract_pid_mdoc(document, request).map_err(Error::Mdoc)?;
    let statement =
        mdoc::MdocCircuitStatement::from_extracted(&extracted, policy).map_err(Error::Mdoc)?;
    let proof = mdoc::prove_mdoc_circuit(&extracted, &statement)?;
    Ok((proof, statement))
}

/// Verify a product mdoc proof against its public statement.
pub fn verify_mdoc(proof: &MdocProof, statement: &MdocStatement) -> Result<(), Error> {
    mdoc::verify_mdoc_circuit(proof, statement)
}

/// Errors from preparing, proving, or verifying a quantum-safe mdoc proof.
#[derive(Debug)]
pub enum Error {
    AgePrepare(predicates::Error),
    NatPrepare(predicates::NatError),
    Mdoc(mdoc::MdocError),
    Prove(String),
    Verify(String),
    AuthInputMismatch,
    AgePolicyMismatch,
    NatPolicyMismatch,
    WeakConfig {
        got: PcsConfig,
        expected: PcsConfig,
    },
    PreprocessedRootMismatch {
        got: air_core::CommitmentRoot,
        expected: air_core::CommitmentRoot,
    },
}
