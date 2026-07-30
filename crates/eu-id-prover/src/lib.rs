//! Quantum-safe EU identity prover.
//!
//! The product path parses an ISO mdoc PID, proves its ML-DSA-65 issuer,
//! and device signatures, and binds the hidden attributes to the verifier's
//! age and nationality policy in one STARK proof. Revocation-bearing proofs
//! use the dedicated TS13 path.

pub(crate) mod claimed_sum_blinder;
pub mod mdoc;
mod mdoc_cbor_stream;
mod mdoc_country_code_table;
mod mdoc_private_device_key_bind;
mod mdoc_private_item_bind;
mod mdoc_private_message;
mod mdoc_private_mso_bind;
mod mdoc_private_mso_validity;
#[cfg(test)]
mod mdoc_real_vectors;
#[cfg(feature = "unlink-spikes")]
mod mdoc_unlink_spike;
mod mdoc_value_digests_scan;
mod mdoc_window_bind;
pub mod policy;
pub mod ts13;
#[doc(hidden)]
pub mod ts13_artifact;
pub mod ts13_demo;
#[doc(hidden)]
pub mod ts13_demo_artifact_constants {
    include!("generated/ts13_demo_artifact.rs");
}

use stwo::core::pcs::PcsConfig;

pub use mdoc::{
    MdocCircuitProof as MdocProof, MdocCircuitStatement as MdocStatement, MdocPidRequest,
    MdocTs13DemoCircuitPublicInput, MdocTs13PublicStatement as MdocTs13Statement,
};
pub use policy::{iso_alpha2_to_numeric, Policy};
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
    // Never hand the prover's statement to a verifier: `into_public_view`
    // scrubs private issuer/authentication and revocation witnesses while
    // retaining only verifier-known shape and policy.
    Ok((proof, statement.into_public_view()))
}

/// Prove the TS13 profile with a private revocation range witness.  The range
/// never leaves this proving call: `MdocCircuitStatement` skips it during
/// serialization and the verifier reconstructs the active layout from the
/// public revocation key/epoch plus the proof's fixed claim shape.
pub fn prove_mdoc_with_ts13_revocation(
    document: &[u8],
    request: &MdocPidRequest,
    policy: Policy,
    revocation: mdoc::MdocRevocationPublicInputs,
    id_lo: u64,
    id_hi: u64,
    signature: mdoc::MdocRevocationSignature,
) -> Result<(MdocProof, MdocTs13Statement), Error> {
    if document.len() > ts13::TS13_MAX_DOCUMENT_BYTES {
        return Err(Error::Prove(
            "TS13 document exceeds published resource cap".to_string(),
        ));
    }
    let mut extracted = mdoc::extract_pid_mdoc(document, request).map_err(Error::Mdoc)?;
    mdoc::select_accepted_nationality(&mut extracted, &policy);
    let id = ts13::ts13_mso_derived_revocation_id(&extracted.mso);
    let statement = mdoc::MdocCircuitStatement::from_extracted(&extracted, policy)
        .map_err(Error::Mdoc)?
        .with_ts13_revocation(revocation)
        .with_ts13_revocation_range(mdoc::MdocRevocationRangeWitness { id, id_lo, id_hi })
        .with_ts13_revocation_signature(signature);
    ts13::validate_ts13_age_over_18_proving_inputs(document, &extracted, &statement)
        .map_err(|error| Error::Prove(format!("TS13 published resource contract: {error:?}")))?;
    let proof = mdoc::prove_mdoc_circuit(&extracted, &statement)?;
    let public_statement = mdoc::MdocTs13PublicStatement::from_circuit(&statement)?;
    Ok((proof, public_statement))
}

/// Prove the fixed unlinkable TS13 age-over-18 demo theorem.
///
/// The returned proof contains no serialized semantic statement. The SDK
/// places it in the fixed-capacity V4 envelope.
pub fn prove_mdoc_ts13_demo(
    document: &[u8],
    request: &MdocPidRequest,
    public: &MdocTs13DemoCircuitPublicInput,
    id_lo: u64,
    id_hi: u64,
    signature: mdoc::MdocRevocationSignature,
) -> Result<MdocProof, Error> {
    if request.doctype != "eu.europa.ec.eudi.pid.1"
        || request.namespace != "eu.europa.ec.eudi.pid.1"
        || request.attributes
            != [mdoc::MdocRequestedAttribute {
                element_identifier: "age_over_18".to_string(),
                mode: mdoc::MdocDisclosureMode::ValueEquality(vec![0xf5]),
            }]
        || request.trusted_mldsa_issuer_public_keys != [public.trusted_issuer_public_key.clone()]
        || request.device_authentication_profile != mdoc::MdocDeviceAuthenticationProfile::Iso180135
    {
        return Err(Error::Prove(
            "TS13 demo request does not match the fixed profile".to_string(),
        ));
    }
    if document.len() > ts13::TS13_MAX_DOCUMENT_BYTES {
        return Err(Error::UnsupportedDemoCredentialShape);
    }
    let extracted = mdoc::extract_pid_mdoc(document, request).map_err(Error::Mdoc)?;
    if extracted.device_sig_structure != public.device_cose_sig_structure {
        return Err(Error::Prove(
            "TS13 device authentication does not match the public request".to_string(),
        ));
    }
    let id = ts13::ts13_mso_derived_revocation_id(&extracted.mso);
    let statement = mdoc::MdocCircuitStatement::from_extracted(&extracted, public.policy()?)
        .map_err(Error::Mdoc)?
        .with_ts13_revocation(public.revocation.clone())
        .with_ts13_revocation_range(mdoc::MdocRevocationRangeWitness { id, id_lo, id_hi })
        .with_ts13_revocation_signature(signature);
    mdoc::prove_mdoc_ts13_demo_circuit(&extracted, &statement, public)
}

pub fn verify_mdoc_ts13_demo(
    proof: &MdocProof,
    public: &MdocTs13DemoCircuitPublicInput,
) -> Result<(), Error> {
    mdoc::verify_mdoc_ts13_demo_circuit(proof, public)
}

/// Verify a product mdoc proof against its public statement. Tree-0 is
/// reconstructed canonically inside the verifier; no artifact root is trusted.
/// Success proves that the private credential validity window contained the
/// verifier-supplied policy date; no separate validity output is serialized.
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
    UnsupportedDemoCredentialShape,
    WeakConfig {
        got: PcsConfig,
        expected: PcsConfig,
    },
    PreprocessedRootMismatch {
        got: air_core::CommitmentRoot,
        expected: air_core::CommitmentRoot,
    },
}
