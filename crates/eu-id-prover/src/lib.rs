//! End-to-end `eu-id` prover: composes the per-circuit `air_core` modules into
//! a single STARK proof.
//!
//! This is the standalone library the FFI will eventually wrap. Today it
//! establishes the **multi-module pipeline**: it drives the P256 ECDSA module
//! and the SHA-256 module through one [`air_core::prove`] call — one channel,
//! one commitment scheme, one proof — and verifies the global LogUp balance.
//!
//! ## Not yet bound
//!
//! The composition here is **not yet cross-bound**: P256 and SHA are each
//! internally balanced (their claimed sums net to zero on their own), so the
//! global balance holds as `0 + 0 == 0`. The proof therefore attests "some
//! ECDSA signature verifies" **and**, separately, "some message hashes to some
//! digest" — with *no link* between the signature's message hash and the digest
//! SHA computed.
//!
//! Welding them is the next step: a cross-module LogUp relation where SHA
//! *yields* its digest and P256 *requires* it as the ECDSA message hash, so the
//! global balance only cancels when the signature is verified over the hash SHA
//! actually computed. Until that relation exists, treat this as orchestration
//! scaffolding, not a meaningful identity proof.

use stwo::core::fields::m31::M31;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;

use stwo_p256::proof::air::{P256Prover, P256Verifier};
use stwo_p256::proof::{P256CurrentAirInteractionClaim, P256CurrentAirProofClaim, P256ProofDraft};
use stwo_p256::public_inputs::PublicEcdsaInstance;

use stwo_sha256::air::{Sha256Prover, Sha256Verifier};
use stwo_sha256::interaction::InteractionClaim as Sha256InteractionClaim;
use stwo_sha256::types::Sha256Witness;

/// A single STARK proof over the composed P256 + SHA modules, plus the public
/// claims the verifier needs to reconstruct each module. (Unbound — see the
/// crate docs.)
pub struct Proof {
    /// The one shared STARK proof.
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
    // P256 module reconstruction data.
    p256_claim: P256CurrentAirProofClaim,
    p256_interaction_claim: P256CurrentAirInteractionClaim,
    // SHA module reconstruction data.
    sha_log_n_rows: u32,
    sha_group_width: u32,
    sha_interaction_claim: Sha256InteractionClaim,
}

impl Proof {
    /// The public ECDSA instances the P256 module proves over. A relying party
    /// must compare these against the statement it intended to verify (the
    /// caller-argument binding); [`verify`] takes that statement explicitly.
    pub fn p256_instances(&self) -> &[PublicEcdsaInstance<M31>] {
        &self.p256_claim.public_inputs.instances
    }
}

/// Errors from composing or verifying the combined proof.
#[derive(Debug)]
pub enum Error {
    /// P256 draft preparation (trace generation) failed.
    P256Prepare(stwo_p256::proof::P256ProofError),
    /// The shared STARK prover failed.
    Prove(String),
    /// The verifier's expected ECDSA statement does not match the proof.
    P256InstanceMismatch,
    /// The shared STARK verifier rejected the proof (includes a broken global
    /// LogUp balance).
    Verify(String),
}

/// Prove the identity statement as **one** STARK proof.
///
/// Today the statement is the P256 ECDSA module plus the SHA-256 module; the
/// predicate modules (age, nationality) join the same call as they are wired
/// in. All modules are driven through a single [`air_core::prove`] against one
/// channel and commitment scheme. The proof is governed by P256's
/// (security-calibrated) PCS config; the orchestrator sizes twiddles from the
/// largest module constraint bound and enables the lifting path P256 needs. The
/// composition is unbound (see crate docs).
pub fn prove(
    p256_draft: &P256ProofDraft,
    sha_witness: &Sha256Witness,
    sha_log_n_rows: u32,
    sha_group_width: u32,
) -> Result<Proof, Error> {
    let mut p256 = P256Prover::new(p256_draft).map_err(Error::P256Prepare)?;
    let mut sha = Sha256Prover::new(sha_witness, sha_log_n_rows, sha_group_width);
    let config = p256.pcs_config();

    // Module order is load-bearing: it fixes the transcript and the tree-column
    // / preprocessed-id concatenation. The verifier must use the same order.
    let stark_proof = {
        let mut modules: [&mut dyn air_core::AirProver; 2] = [&mut p256, &mut sha];
        air_core::prove(&mut modules, config).map_err(|e| Error::Prove(format!("{e:?}")))?
    };

    Ok(Proof {
        stark_proof,
        p256_claim: p256.proof_claim().clone(),
        p256_interaction_claim: p256.interaction_claim().clone(),
        sha_log_n_rows,
        sha_group_width,
        sha_interaction_claim: sha.interaction_claim().clone(),
    })
}

/// Verify a [`Proof`], binding the P256 module to the caller's expected
/// ECDSA statement.
pub fn verify(
    proof: &Proof,
    expected_instances: &[PublicEcdsaInstance<M31>],
) -> Result<(), Error> {
    // Caller-argument binding for the P256 statement (the same gate the P256
    // standalone wrapper enforces).
    if proof.p256_claim.public_inputs.instances.as_slice() != expected_instances {
        return Err(Error::P256InstanceMismatch);
    }

    let mut p256 = P256Verifier::new(
        proof.p256_claim.clone(),
        proof.p256_interaction_claim.clone(),
    );
    let mut sha = Sha256Verifier::new(
        proof.sha_log_n_rows,
        proof.sha_group_width,
        proof.sha_interaction_claim.clone(),
    );

    // Same module order as the prover.
    let mut modules: [&mut dyn air_core::Air; 2] = [&mut p256, &mut sha];
    air_core::verify(&mut modules, &proof.stark_proof).map_err(|e| Error::Verify(format!("{e:?}")))
}
