//! End-to-end `eu-id` prover: composes the per-circuit `air_core` modules into
//! a single STARK proof.
//!
//! This is the standalone library the FFI will eventually wrap. It drives the
//! P256 ECDSA module, the SHA-256 module, the **digest-bind bridge**, and the
//! **age** and **nationality** predicate modules through one [`air_core::prove`]
//! call — one channel, one commitment scheme, one proof — and verifies the
//! global LogUp balance.
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
//! `(r, s)` against the caller's statement but **not** `z`.
//!
//! ## Predicates: age credential-bound, nationality pending
//!
//! The age and nationality modules are both part of the composed proof: the age
//! module proves the date of birth it holds clears the policy threshold, and the
//! nationality module proves its private code is in the accepted set.
//!
//! **Age is now credential-bound** (`docs/ROADMAP_E2E` §6.6). SHA exposes the
//! DOB byte window of the preimage `C` on a shared field channel; the age module
//! *requires* exactly those bytes and reconciles them against the packed
//! `(year, month, day)` it reasons about (big-endian recomposition). So the
//! global balance cancels **only** when the date of birth the age module clears
//! against the threshold is the one encoded in the signed credential — a prover
//! can no longer attest age from a date `C` does not contain.
//!
//! **Nationality is not yet bound** (§6.7): its private code is still
//! free-floating, so the nat module's LogUp sub-balance nets to zero on its own
//! and it composes without perturbing the global balance. Binding it (and the
//! full policy-shaped public-input contract a relying party checks against) is
//! the remaining glue tracked in the integration roadmap.
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

use air_core::relations::{field_id, SharedDigestRelation, SharedFieldRelation};
use air_core::{Air, AirProver};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;

use predicates::nat::NationalityPredicate;
use predicates::{
    AgeRangeCheck, DateOfBirth, NatPrivateInput, NatPublicInput, PredicateProver,
    PredicateVerifier, PublicInput as AgePublicInput,
};

use stwo_p256::components::digest_bind::module::{
    DigestBindInteractionClaim, DigestBindProver, DigestBindVerifier,
};
use stwo_p256::components::digest_bind::witness::DigestBindRow;
use stwo_p256::components::digest_bind::SharedScalarZRelation;
use stwo_p256::proof::air::{P256Prover, P256Verifier};
use stwo_p256::proof::{P256CurrentAirInteractionClaim, P256CurrentAirProofClaim, P256ProofDraft};
use stwo_p256::public_inputs::PublicEcdsaInstance;

use stwo_sha256::air::{Sha256Prover, Sha256Verifier};
use stwo_sha256::field_exposure::FieldExposure;
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
    // Age module reconstruction data (range-check strategy): the public input and
    // the six claimed LogUp sums the verifier rebuilds the module from.
    age_public: AgePublicInput,
    age_claimed_sums: Vec<QM31>,
    // Nationality module reconstruction data: the public input (accepted set) and
    // its two claimed LogUp sums.
    nat_public: NatPublicInput,
    nat_claimed_sums: Vec<QM31>,
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
    /// Age predicate preparation (input validation or witness generation) failed.
    AgePrepare(predicates::Error),
    /// Nationality predicate preparation (input validation or witness generation)
    /// failed.
    NatPrepare(predicates::NatError),
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

/// The SHA field-exposure spec for the §6.6 age binding: expose **only** the
/// credential's DOB byte window. SHA yields these four bytes on the shared
/// `Sha256Field` channel and the age module requires them. The nationality
/// window is added in §6.7 (with its nat consumer); exposing a window with no
/// consumer would leave the global balance non-zero, so the exposure is kept in
/// lock-step with the wired consumers. Prover and verifier must build the
/// identical spec (it is mixed into the SHA transcript).
fn dob_exposure() -> FieldExposure {
    FieldExposure::from_preimage_windows(&[(
        field_id::DOB,
        credential::DOB_WINDOW.start,
        credential::DOB_WINDOW.end - credential::DOB_WINDOW.start,
    )])
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

/// Prove the identity statement as **one** STARK proof over five modules.
///
/// Drives the P256 ECDSA module, the SHA-256 module, the digest-bind bridge, and
/// the age and nationality predicate modules through a single [`air_core::prove`]
/// against one channel and commitment scheme. The proof is governed by P256's
/// (security-calibrated) PCS config; the orchestrator sizes twiddles from the
/// largest module constraint bound (P256's) and enables the lifting path P256
/// needs. The predicate modules are plain degree-2 / Blake2s `air_core` modules,
/// so they compose under that config with no friction. The SHA digest is bound
/// to the ECDSA `z` (see the crate docs); the predicate statements are proven but
/// **not yet** bound to the credential bytes, so each nets to zero internally.
//
// Scaffolding takes each module's witness loosely. The relying-party-facing API
// (a later task) collapses these into one credential + policy and supersedes
// this signature, so the argument count is intentional here.
#[allow(clippy::too_many_arguments)]
pub fn prove(
    p256_draft: &P256ProofDraft,
    sha_witness: &Sha256Witness,
    sha_log_n_rows: u32,
    sha_group_width: u32,
    age_public: &AgePublicInput,
    age_dob: &DateOfBirth,
    nat_public: &NatPublicInput,
    nat_private: &NatPrivateInput,
) -> Result<Proof, Error> {
    let scalar_z_handle = SharedScalarZRelation::new();
    let digest_handle = SharedDigestRelation::new();
    let field_handle = SharedFieldRelation::new();

    let mut p256 = P256Prover::new(p256_draft)
        .map_err(Error::P256Prepare)?
        .with_z_binding(scalar_z_handle.clone());
    // SHA both yields its digest (P256↔SHA bridge, §6.3) and exposes the DOB
    // byte window (age↔credential bridge, §6.6) on the shared field channel.
    let mut sha = Sha256Prover::new(sha_witness, sha_log_n_rows, sha_group_width)
        .with_digest_handle(digest_handle.clone())
        .with_field_handle(dob_exposure(), field_handle.clone());

    let instances = p256.proof_claim().public_inputs.instances.clone();
    let rows = bridge_rows(&instances);
    let bridge_log = bridge_log_size(rows.len());
    let mut bridge = DigestBindProver::new(rows, bridge_log, scalar_z_handle, digest_handle);

    // The predicate modules. `range_check` is the canonical age strategy for the
    // combined proof (the standalone default); the bit-decomposition strategy
    // stays available standalone for benchmarking. The wrapper's `PcsConfig` is
    // unused by `prover()` — only the input validation and witness generation it
    // performs matter; the shared orchestrator config below governs the proof.
    //
    // The age module is **credential-bound** (§6.6): `with_dob_binding` makes it
    // require the DOB bytes SHA yields, so the date of birth it proves ≥ the
    // threshold is provably the signed credential's — a prover can no longer
    // attest age from a date the credential does not contain. (Nationality is
    // bound in §6.7; until then nat nets to zero internally.)
    let mut age = AgeRangeCheck::new(PcsConfig::default())
        .prover(age_public, age_dob)
        .map_err(Error::AgePrepare)?
        .with_dob_binding(field_handle.clone());
    let mut nat = NationalityPredicate::new(PcsConfig::default())
        .prover(nat_public, nat_private)
        .map_err(Error::NatPrepare)?;

    let config = p256.pcs_config();

    // Module order is load-bearing: it fixes the transcript, the tree-column /
    // preprocessed-id concatenation, and the order the shared relations are
    // drawn. P256 draws ScalarZ, SHA draws the digest, the bridge reads both, so
    // the bridge must follow its two producers. Age and nat share no relation
    // with the others (they are not yet credential-bound), so they append after
    // the binding cluster. Their preprocessed-id namespaces are disjoint from the
    // rest — age uses `age/...` and the generic `range_check_[0, N]` delta tables,
    // nat uses `nat/...`; neither aliases SHA's `sha256_range_*`, P256's
    // `p256_*`, or the bridge's `digest_bind_*` ids in the shared allocator. The
    // verifier must use this same order.
    let stark_proof = {
        let mut modules: [&mut dyn AirProver; 5] =
            [&mut p256, &mut sha, &mut bridge, &mut age, &mut nat];
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
        // Claimed sums are populated by the modules' interaction phase during the
        // `prove` call above (the slice borrow has been released here).
        age_public: *age_public,
        age_claimed_sums: age.claimed_sums(),
        nat_public: nat_public.clone(),
        nat_claimed_sums: nat.claimed_sums(),
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
    let field_handle = SharedFieldRelation::new();

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
    .with_digest_handle(digest_handle.clone())
    .with_field_handle(dob_exposure(), field_handle.clone());
    let mut bridge = DigestBindVerifier::new(
        proof.bridge_log_size,
        proof.bridge_interaction_claim.clone(),
        scalar_z_handle,
        digest_handle,
    );

    // Rebuild the predicate verifier modules from the public input and claimed
    // sums carried in the proof, with the same canonical strategy the prover
    // used (`range_check` for age). The age module is credential-bound (§6.6),
    // so it reads the same shared field channel to reconstruct its require terms.
    let mut age = AgeRangeCheck::new(PcsConfig::default())
        .verifier(&proof.age_public, &proof.age_claimed_sums)
        .map_err(Error::AgePrepare)?
        .with_dob_binding(field_handle.clone());
    let mut nat = NationalityPredicate::new(PcsConfig::default())
        .verifier(&proof.nat_public, &proof.nat_claimed_sums)
        .map_err(Error::NatPrepare)?;

    // Same module order as the prover.
    let mut modules: [&mut dyn Air; 5] = [&mut p256, &mut sha, &mut bridge, &mut age, &mut nat];
    air_core::verify(&mut modules, &proof.stark_proof).map_err(|e| Error::Verify(format!("{e:?}")))
}
