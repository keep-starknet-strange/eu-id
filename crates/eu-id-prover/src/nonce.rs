//! Standalone nonce-signature proof.
//!
//! This is the smallest holder-presence milestone: prove a P-256 device key
//! signed `SHA-256(domain || nonce)`. The origin of the device key remains a
//! public/host-validated boundary until the mdoc device-key binding lands.
//!
//! The nonce signature is *also* folded into the primary monolithic identity
//! proof as a second (non-z-bound) P-256 module — see [`crate::prove_identity`].
//! This module keeps only the small standalone proof and the shared
//! [`NonceSignatureStatement`] both paths verify against.

use serde::{Deserialize, Serialize};

use sha2::{Digest as _, Sha256};
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;
use stwo_p256::ecdsa::ecdsa_verify;
use stwo_p256::proof::air::{
    current_air_preprocessed_root, prove_current_air, verify_current_air_with_preprocessed_root,
};
use stwo_p256::proof::{
    P256CurrentAirInteractionClaim, P256CurrentAirProof, P256CurrentAirProofClaim, P256ProofDraft,
    P256ProofError,
};
use stwo_p256::public_inputs::PublicEcdsaInputClaim;
use stwo_p256::types::{AffinePoint, EcdsaVerifyInput, Signature, U256};

use crate::Error;

const NONCE_SIGNATURE_DOMAIN: &[u8] = b"EU-ID nonce signature v1\0";

/// The verifier-facing nonce signature statement.
///
/// `device_key` is currently a public trust boundary: this proof shows that key
/// signed the nonce message, not that the key came from a particular mdoc.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NonceSignatureStatement {
    pub device_key: AffinePoint,
    pub nonce: Vec<u8>,
    pub signature: Signature,
}

impl NonceSignatureStatement {
    pub fn message_hash_for_nonce(nonce: &[u8]) -> U256 {
        U256(Sha256::digest(nonce_signature_message(nonce)).into())
    }

    /// The ECDSA verification input the nonce signature proves over. Public: the
    /// verifier recomputes it from the nonce host-side and binds the folded P-256
    /// module (or the standalone proof) against it in full — `z` included.
    pub fn ecdsa_input(&self) -> EcdsaVerifyInput {
        EcdsaVerifyInput {
            message_hash: Self::message_hash_for_nonce(&self.nonce),
            signature: self.signature.clone(),
            public_key: self.device_key.clone(),
        }
    }
}

/// Domain-separated bytes signed by the device key for nonce proofs.
pub fn nonce_signature_message(nonce: &[u8]) -> Vec<u8> {
    let mut message = Vec::with_capacity(NONCE_SIGNATURE_DOMAIN.len() + nonce.len());
    message.extend_from_slice(NONCE_SIGNATURE_DOMAIN);
    message.extend_from_slice(nonce);
    message
}

/// A single P-256 STARK proof for the nonce signature statement.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NonceSignatureProof {
    p256_claim: P256CurrentAirProofClaim,
    p256_interaction_claim: P256CurrentAirInteractionClaim,
    stark_proof: StarkProof<Blake2sMerkleHasher>,
}

impl From<P256CurrentAirProof<Blake2sMerkleHasher>> for NonceSignatureProof {
    fn from(proof: P256CurrentAirProof<Blake2sMerkleHasher>) -> Self {
        Self {
            p256_claim: proof.claim,
            p256_interaction_claim: proof.interaction_claim,
            stark_proof: proof.stark_proof,
        }
    }
}

impl From<NonceSignatureProof> for P256CurrentAirProof<Blake2sMerkleHasher> {
    fn from(proof: NonceSignatureProof) -> Self {
        Self {
            claim: proof.p256_claim,
            interaction_claim: proof.p256_interaction_claim,
            stark_proof: proof.stark_proof,
        }
    }
}

/// Prove that `statement.device_key` signed `SHA-256(domain || nonce)`.
pub fn prove_nonce_signature(
    statement: &NonceSignatureStatement,
) -> Result<NonceSignatureProof, Error> {
    let input = statement.ecdsa_input();
    if !ecdsa_verify(&input) {
        return Err(Error::SignatureInvalid);
    }

    let draft = P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![input])
        .map_err(Error::P256Prepare)?;
    let proof = prove_current_air(&draft).map_err(Error::P256Prepare)?;
    Ok(proof.into())
}

/// Verify a nonce-signature proof against the caller's expected nonce statement.
///
/// The tree-0 (preprocessed) root is NOT pinned here — the F-ROOT legacy
/// behavior. Production callers use
/// [`verify_nonce_signature_with_preprocessed_root`] with a root from
/// [`nonce_expected_preprocessed_root`].
pub fn verify_nonce_signature(
    proof: &NonceSignatureProof,
    statement: &NonceSignatureStatement,
) -> Result<(), Error> {
    verify_nonce_signature_impl(proof, statement, None)
}

/// Compute the expected tree-0 (preprocessed) commitment root for a nonce
/// statement, from the statement alone: rebuild the P-256 draft the prover
/// builds (`from_inputs_with_arbitrary_fake_glv_hints` is a deterministic
/// function of the ECDSA input) and run exactly the prover's tree-0 commit
/// path. Never derived from the proof. Pass the result to
/// [`verify_nonce_signature_with_preprocessed_root`].
///
/// The computation is uncached: the hinted-mul schedule preprocessed columns
/// follow the signature, so each statement pays a fresh tree-0 rebuild.
pub fn nonce_expected_preprocessed_root(
    statement: &NonceSignatureStatement,
) -> Result<air_core::CommitmentRoot, Error> {
    let input = statement.ecdsa_input();
    if !ecdsa_verify(&input) {
        return Err(Error::SignatureInvalid);
    }
    let draft = P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![input])
        .map_err(Error::P256Prepare)?;
    current_air_preprocessed_root(&draft).map_err(Error::P256Prepare)
}

/// [`verify_nonce_signature`], with the tree-0 (preprocessed) commitment root
/// pinned — the F-ROOT fix. A proof carrying a forged preprocessed tree
/// (range tables, hinted-mul schedules, constants) is rejected fail-closed
/// with [`Error::PreprocessedRootMismatch`] before the STARK check.
pub fn verify_nonce_signature_with_preprocessed_root(
    proof: &NonceSignatureProof,
    statement: &NonceSignatureStatement,
    expected_preprocessed_root: air_core::CommitmentRoot,
) -> Result<(), Error> {
    verify_nonce_signature_impl(proof, statement, Some(expected_preprocessed_root))
}

fn verify_nonce_signature_impl(
    proof: &NonceSignatureProof,
    statement: &NonceSignatureStatement,
    expected_preprocessed_root: Option<air_core::CommitmentRoot>,
) -> Result<(), Error> {
    let got_root = proof.stark_proof.commitments[0];
    let expected = PublicEcdsaInputClaim::from_inputs(&[statement.ecdsa_input()]);
    verify_current_air_with_preprocessed_root(
        proof.clone().into(),
        &expected.instances,
        expected_preprocessed_root,
    )
    .map_err(|error| match error {
        P256ProofError::PublicInstanceMismatch => Error::P256InstanceMismatch,
        P256ProofError::PreprocessedRootMismatch { .. } => Error::PreprocessedRootMismatch {
            got: got_root,
            // The mismatch arm can only fire when a pin was supplied.
            expected: expected_preprocessed_root
                .expect("root mismatch requires a supplied expected root"),
        },
        other => Error::Verify(format!("{other:?}")),
    })
}
