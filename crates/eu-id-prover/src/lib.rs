//! End-to-end `eu-id` prover: composes the per-circuit `air_core` modules into
//! a single STARK proof.
//!
//! This is the standalone library the FFI will eventually wrap. It drives the
//! P256 ECDSA module, the SHA-256 module, and the **digest-bind bridge** through
//! one [`air_core::prove`] call — one channel, one commitment scheme, one proof —
//! and verifies the global LogUp balance.
//!
//! ## Cross-bound: the signature is over the hash of this preimage
//!
//! The composition is **cross-bound** for the P256↔SHA half (`docs/ROADMAP_E2E`
//! §6.3). SHA yields its final-block digest; the bridge requires those 32 bytes
//! as the ECDSA message hash `z` (reconciling SHA's 16-bit limbs against P256's
//! 13-bit limbs at the byte level), and an analytic provider ties the bridge's
//! `z` to the proven ECDSA `z`. So the global balance cancels **only** when the
//! signed digest equals `SHA-256(C)` — a malicious prover cannot sign one
//! message and hash another.
//!
//! Because `z` is now proven equal to `SHA-256(C)`, it is an **internal** bound
//! value on this path: [`verify`] checks the issuer key `Q` and the signature
//! `(r, s)` against the caller's statement but **not** `z`. (Binding the
//! predicate attributes — age, nationality — to the same credential bytes is the
//! remaining glue, §6.6/§6.7; the full policy-shaped public-input contract is
//! §6.8.)
//!
//! ## Credential format & witness oracle
//!
//! [`credential`] defines the simplified POC credential `C` (the frozen
//! byte-offset contract every binding relation keys off), [`generator`] is the
//! native signer + composed [`generator::PipelineWitness`] cross-checked against
//! `sha2` / the `p256` crate, and [`fixtures`] is the deterministic catalogue of
//! valid and adversarial witnesses the binding tasks diff against.

pub mod credential;
pub mod fixtures;
pub mod generator;

pub use credential::Credential;
pub use generator::{IssuerKey, PipelineWitness, Policy, SignedCredential};

use air_core::relations::SharedDigestRelation;
use air_core::{Air, AirProver};
use stwo::core::fields::m31::M31;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;

use stwo_p256::components::digest_bind::module::{
    DigestBindInteractionClaim, DigestBindProver, DigestBindVerifier,
};
use stwo_p256::components::digest_bind::witness::DigestBindRow;
use stwo_p256::components::digest_bind::SharedScalarZRelation;
use stwo_p256::proof::air::{P256Prover, P256Verifier};
use stwo_p256::proof::{P256CurrentAirInteractionClaim, P256CurrentAirProofClaim, P256ProofDraft};
use stwo_p256::public_inputs::PublicEcdsaInstance;

use stwo_sha256::air::{Sha256Prover, Sha256Verifier};
use stwo_sha256::interaction::InteractionClaim as Sha256InteractionClaim;
use stwo_sha256::types::Sha256Witness;

/// A single STARK proof over the composed P256 + SHA + digest-bind modules, plus
/// the public claims the verifier needs to reconstruct each module.
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
    // Digest-bind bridge reconstruction data.
    bridge_log_size: u32,
    bridge_interaction_claim: DigestBindInteractionClaim,
}

impl Proof {
    /// The public ECDSA instances the P256 module proves over. A relying party
    /// compares the issuer key and signature against the statement it intended;
    /// the message hash `z` is **not** part of that comparison (it is proven
    /// equal to `SHA-256(C)`). [`verify`] takes the expected statement
    /// explicitly.
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
    /// The verifier's expected ECDSA statement (issuer key + signature) does not
    /// match the proof.
    P256InstanceMismatch,
    /// The shared STARK verifier rejected the proof (includes a broken global
    /// LogUp balance — e.g. the signed digest does not equal `SHA-256(C)`).
    Verify(String),
}

/// Bridge trace size: enough rows for one active row per ECDSA instance, at the
/// SIMD minimum of `2^4 = 16` rows.
fn bridge_log_size(n_instances: usize) -> u32 {
    let needed = (n_instances.max(1) as u32)
        .next_power_of_two()
        .trailing_zeros();
    needed.max(4)
}

/// Per-instance `(sig_id, z)` rows the bridge binds, sourced from the proven
/// public instances.
fn bridge_rows(instances: &[PublicEcdsaInstance<M31>]) -> Vec<DigestBindRow> {
    instances
        .iter()
        .map(|instance| DigestBindRow {
            sig_id: instance.sig_id,
            z: instance.z.clone(),
        })
        .collect()
}

/// Prove the identity statement as **one** cross-bound STARK proof.
///
/// Drives the P256 ECDSA module, the SHA-256 module, and the digest-bind bridge
/// through a single [`air_core::prove`] against one channel and commitment
/// scheme. The proof is governed by P256's (security-calibrated) PCS config; the
/// orchestrator sizes twiddles from the largest module constraint bound and
/// enables the lifting path P256 needs. The SHA digest is bound to the ECDSA `z`
/// (see the crate docs); the predicate modules join this call as they are wired.
pub fn prove(
    p256_draft: &P256ProofDraft,
    sha_witness: &Sha256Witness,
    sha_log_n_rows: u32,
    sha_group_width: u32,
) -> Result<Proof, Error> {
    let scalar_z_handle = SharedScalarZRelation::new();
    let digest_handle = SharedDigestRelation::new();

    let mut p256 = P256Prover::new(p256_draft)
        .map_err(Error::P256Prepare)?
        .with_z_binding(scalar_z_handle.clone());
    let mut sha = Sha256Prover::new(sha_witness, sha_log_n_rows, sha_group_width)
        .with_digest_handle(digest_handle.clone());

    let instances = p256.proof_claim().public_inputs.instances.clone();
    let rows = bridge_rows(&instances);
    let bridge_log = bridge_log_size(rows.len());
    let mut bridge = DigestBindProver::new(rows, bridge_log, scalar_z_handle, digest_handle);

    let config = p256.pcs_config();

    // Module order is load-bearing: it fixes the transcript, the tree-column /
    // preprocessed-id concatenation, and the order the shared relations are
    // drawn (P256 draws ScalarZ, SHA draws the digest, the bridge reads both).
    // The verifier must use the same order.
    let stark_proof = {
        let mut modules: [&mut dyn AirProver; 3] = [&mut p256, &mut sha, &mut bridge];
        air_core::prove(&mut modules, config).map_err(|e| Error::Prove(format!("{e:?}")))?
    };

    Ok(Proof {
        stark_proof,
        p256_claim: p256.proof_claim().clone(),
        p256_interaction_claim: p256.interaction_claim().clone(),
        sha_log_n_rows,
        sha_group_width,
        sha_interaction_claim: sha.interaction_claim().clone(),
        bridge_log_size: bridge_log,
        bridge_interaction_claim: bridge.interaction_claim().clone(),
    })
}

/// Whether the proof's instances match the caller's expected statement, **except
/// `z`** — the message hash is proven equal to `SHA-256(C)` by the digest
/// binding, so the relying party supplies only the issuer key `Q = (pub_x,
/// pub_y)` and the signature `(r, s)`, never `z`.
fn instances_match_ignoring_z(
    proof: &[PublicEcdsaInstance<M31>],
    expected: &[PublicEcdsaInstance<M31>],
) -> bool {
    proof.len() == expected.len()
        && proof.iter().zip(expected).all(|(p, e)| {
            p.sig_id == e.sig_id
                && p.r == e.r
                && p.s == e.s
                && p.pub_x == e.pub_x
                && p.pub_y == e.pub_y
        })
}

/// Verify a [`Proof`], binding the P256 module to the caller's expected ECDSA
/// statement (issuer key + signature, **not** `z`).
pub fn verify(proof: &Proof, expected_instances: &[PublicEcdsaInstance<M31>]) -> Result<(), Error> {
    // Caller-argument binding for the P256 statement, minus `z` (internally
    // bound to the SHA digest).
    if !instances_match_ignoring_z(
        &proof.p256_claim.public_inputs.instances,
        expected_instances,
    ) {
        return Err(Error::P256InstanceMismatch);
    }

    let scalar_z_handle = SharedScalarZRelation::new();
    let digest_handle = SharedDigestRelation::new();

    let mut p256 = P256Verifier::new(
        proof.p256_claim.clone(),
        proof.p256_interaction_claim.clone(),
    )
    .with_z_binding(scalar_z_handle.clone());
    let mut sha = Sha256Verifier::new(
        proof.sha_log_n_rows,
        proof.sha_group_width,
        proof.sha_interaction_claim.clone(),
    )
    .with_digest_handle(digest_handle.clone());
    let mut bridge = DigestBindVerifier::new(
        proof.bridge_log_size,
        proof.bridge_interaction_claim.clone(),
        scalar_z_handle,
        digest_handle,
    );

    // Same module order as the prover.
    let mut modules: [&mut dyn Air; 3] = [&mut p256, &mut sha, &mut bridge];
    air_core::verify(&mut modules, &proof.stark_proof).map_err(|e| Error::Verify(format!("{e:?}")))
}
