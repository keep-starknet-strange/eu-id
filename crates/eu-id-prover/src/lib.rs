//! Quantum-safe EU identity prover.
//!
//! The product path parses an ISO mdoc PID, proves its ML-DSA-65 issuer,
//! device, and optional revocation signatures, and binds the hidden attributes
//! to the verifier's age and nationality policy in one STARK proof.

pub(crate) mod claimed_sum_blinder;
pub mod mdoc;
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

/// Which ZK identity system a prover build implements. Both variants exist on
/// every branch so the type is shared-shape; each build hardwires [`ZK_SYSTEM_KIND`]
/// to the one it actually links. The SDK forwards it as `zk_system()`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkSystemKind {
    P256,
    MlDsa,
}

/// This build proves/verifies ML-DSA-65 issuer & device signatures.
pub const ZK_SYSTEM_KIND: ZkSystemKind = ZkSystemKind::MlDsa;

/// Build and prove the product mdoc circuit from the document, verifier
/// request, and public policy.
pub fn prove_mdoc(
    document: &[u8],
    request: &MdocPidRequest,
    policy: Policy,
) -> Result<(MdocProof, MdocStatement), Error> {
    let mut extracted = mdoc::extract_pid_mdoc(document, request).map_err(Error::Mdoc)?;

    // In case of multi-nationality users, before offloading to the circuit, the prover selects
    // a nationality from the accepted set
    mdoc::select_accepted_nationality(&mut extracted, &policy);

    let statement =
        mdoc::MdocCircuitStatement::from_extracted(&extracted, policy).map_err(Error::Mdoc)?;
    let proof = mdoc::prove_mdoc_circuit(&extracted, &statement)?;
    Ok((proof, statement))
}

/// Prove the TS13 profile with a private revocation range witness.  The range
/// never leaves this proving call: `MdocCircuitStatement` skips it during
/// serialization and the verifier reconstructs the active layout from the
/// public revocation key/epoch and signature.
pub fn prove_mdoc_with_ts13_revocation(
    document: &[u8],
    request: &MdocPidRequest,
    policy: Policy,
    revocation: mdoc::MdocRevocationPublicInputs,
    id_lo: u64,
    id_hi: u64,
    signature: mdoc::MdocRevocationSignature,
) -> Result<(MdocProof, MdocStatement), Error> {
    let mut extracted = mdoc::extract_pid_mdoc(document, request).map_err(Error::Mdoc)?;
    mdoc::select_accepted_nationality(&mut extracted, &policy);
    let id = ts13::ts13_mso_derived_revocation_id(&extracted.mso);
    let statement = mdoc::MdocCircuitStatement::from_extracted(&extracted, policy)
        .map_err(Error::Mdoc)?
        .with_ts13_revocation(revocation)
        .with_ts13_revocation_range(mdoc::MdocRevocationRangeWitness { id, id_lo, id_hi })
        .with_ts13_revocation_signature(signature);
    let proof = mdoc::prove_mdoc_circuit(&extracted, &statement)?;
    Ok((proof, statement))
}

/// Verify a product mdoc proof against its public statement. Tree-0 is
/// reconstructed canonically inside the verifier; no artifact root is trusted.
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
