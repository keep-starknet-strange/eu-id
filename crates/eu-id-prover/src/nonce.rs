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
use stwo_p256::proof::air::{prove_current_air, verify_current_air};
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
pub fn verify_nonce_signature(
    proof: &NonceSignatureProof,
    statement: &NonceSignatureStatement,
) -> Result<(), Error> {
    let expected = PublicEcdsaInputClaim::from_inputs(&[statement.ecdsa_input()]);
    verify_current_air(proof.clone().into(), &expected.instances).map_err(|error| match error {
        P256ProofError::PublicInstanceMismatch => Error::P256InstanceMismatch,
        other => Error::Verify(format!("{other:?}")),
    })
}
