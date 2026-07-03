//! End-to-end `eu-id` prover: composes the per-circuit `air_core` modules into
//! a single STARK proof.
//!
//! This is the standalone library the `eu-id-ffi` C-ABI surface wraps. It drives the
//! P256 ECDSA module, the SHA-256 module, the **digest-bind bridge**, and the
//! **age** and **nationality** predicate modules through one [`air_core::prove`]
//! call — one channel, one commitment scheme, one proof — and verifies the
//! global LogUp balance.
//!
//! ## Cross-bound: the signature is over the hash of this preimage
//!
//! The composition is **cross-bound** for the P256↔SHA half. SHA yields its
//! final-block digest; the bridge requires those 32 bytes
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
//! ## Predicates: both credential-bound
//!
//! The age and nationality modules are both part of the composed proof: the age
//! module proves the date of birth it holds clears the policy threshold, and the
//! nationality module proves its private code is in the accepted set. Both are
//! now bound to the signed credential bytes.
//!
//! **Age is credential-bound.** SHA exposes the DOB
//! byte window of the preimage `C` on a shared field channel; the age module
//! *requires* exactly those bytes and reconciles them against the packed
//! `(year, month, day)` it reasons about (big-endian recomposition). So the
//! global balance cancels **only** when the date of birth the age module clears
//! against the threshold is the one encoded in the signed credential — a prover
//! can no longer attest age from a date `C` does not contain.
//!
//! **Nationality is credential-bound**, the same way: SHA exposes the
//! nationality byte window of `C` on the same field channel, and the nat module
//! *requires* those two bytes and reconciles them against the packed `code` it
//! proves set-membership for (`code = code_hi · 256 + code_lo`). So the balance
//! cancels **only** when the nationality the nat module clears against the
//! accepted set is the one encoded in the signed credential — a prover can no
//! longer prove membership for a code `C` does not contain.
//!
//! ## Relying-party API & public statement
//!
//! [`prove_identity`] takes a credential, the issuer signing key, and a
//! [`Policy`] (reference date, age threshold, accepted set), signs the
//! credential, and returns one bound [`Proof`]. [`verify_identity`] checks that
//! proof against a [`PublicStatement`] — exactly `{ issuer key Q, current date,
//! age threshold, accepted nationality set }`. The date of birth, the
//! nationality, and the digest `z` are **proven equal to the credential's**, not
//! supplied. Caller-argument binding rejects the proof unless its public values
//! match the caller's statement: the issuer key `Q` against the ECDSA instance's
//! public-key limbs, and the policy against the age / nationality public inputs.
//!
//! **Issuer key / trust anchor.** `Q` is a public input the verifier checks
//! against an issuer it already trusts (out of band). Binding `Q` to a committed
//! issuer registry *in-circuit* (a trust anchor over `Q` / `H(Q)`) is a
//! deliberate non-goal for the MVP and is deferred.
//!
//! The lower-level [`prove`] / [`verify`] take each module's witness / expected
//! ECDSA instances explicitly; they are the composition primitives the
//! credential API is built on, and the surface the negative-test suite forges
//! deliberately inconsistent witnesses against.
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
#[cfg(test)]
mod shape_dump;

pub use credential::Credential;
pub use generator::{IssuerKey, PipelineWitness, Policy, SignedCredential};
// `Policy::current_date` is a `predicates::Date`; re-export it so a relying
// party (e.g. the FFI benchmark harness) can build a `Policy` — and thus a
// `PublicStatement` — without depending on `predicates` directly.
pub use predicates::Date;
// The universal accepted-nationality set (every assigned ISO-3166-1 numeric
// code). A relying party that needs to neutralize the nationality predicate —
// e.g. the SDK contract mapping for an age-only request — builds its accepted
// set from this without depending on `predicates` directly.
pub use predicates::all_nationality_codes;

use serde::{Deserialize, Serialize};

use air_core::relations::{field_id, SharedDigestRelation, SharedFieldRelation};
use air_core::{Air, AirProver};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::PolyOps;
use stwo::prover::{prove as stark_prove, CommitmentSchemeProver, ComponentProver, ProvingError};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::TraceLocationAllocator;

use predicates::age::strategy::range_check::air::RangeCheckProver;
use predicates::nat::air::NatProver;
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
use stwo_p256::limbs::P256M31BigInt;
use stwo_p256::proof::air::{P256ColumnTask, P256Prover, P256Verifier};
use stwo_p256::proof::{P256CurrentAirInteractionClaim, P256CurrentAirProofClaim, P256ProofDraft};
use stwo_p256::public_inputs::PublicEcdsaInstance;
// Re-exported: `AffinePoint` is the type of `PublicStatement::issuer_key`, so a
// relying party needs it in scope to build a statement.
pub use stwo_p256::types::AffinePoint;

use stwo_sha256::air::{Sha256ColumnTask, Sha256Prover, Sha256Verifier};
use stwo_sha256::field_exposure::FieldExposure;
#[cfg(feature = "gkr-spike")]
use stwo_sha256::gkr_spike::Xor8GkrProofWire;
use stwo_sha256::interaction::InteractionClaim as Sha256InteractionClaim;
use stwo_sha256::types::Sha256Witness;

/// A single STARK proof over the composed P256 + SHA + digest-bind modules, plus
/// the public claims the verifier needs to reconstruct each module.
///
/// Serde-serializable end to end (the per-module claim trees derive serde), so
/// the `eu-id` CLI can write a proof in one process and verify it in another.
#[derive(Serialize, Deserialize)]
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
    #[cfg(feature = "gkr-spike")]
    sha_xor_8_gkr_proof: Xor8GkrProofWire,
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
    /// The proof's issuer public key does not match the statement's `Q`.
    IssuerKeyMismatch,
    /// The proof's age public input (reference date / threshold) does not match
    /// the statement's policy.
    AgePolicyMismatch,
    /// The proof's accepted-nationality set does not match the statement's
    /// policy.
    NatPolicyMismatch,
    /// A freshly signed credential did not yield a natively-verifying ECDSA
    /// witness (no proof draft) — should not happen for a well-formed issuer key.
    SignatureInvalid,
    /// The shared STARK verifier rejected the proof (includes a broken global
    /// LogUp balance — e.g. the signed digest does not equal `SHA-256(C)`).
    Verify(String),
    /// The feature-gated SHA `xor_8` GKR output claims did not cancel.
    #[cfg(feature = "gkr-spike")]
    ShaXor8GkrUnbalanced,
    /// The feature-gated SHA `xor_8` side GKR proof was malformed or rejected.
    #[cfg(feature = "gkr-spike")]
    ShaXor8GkrRejected(String),
    /// The proof was produced under a PCS config that does not match the pinned
    /// security profile (e.g. a prover-weakened FRI/grinding setting). Rejected
    /// before the STARK check, so a low-query proof cannot be inherited.
    WeakConfig {
        /// The config embedded in the proof.
        got: PcsConfig,
        /// The pinned config the combined proof must be produced under.
        expected: PcsConfig,
    },
}

/// The relying party's public statement — the only thing [`verify_identity`]
/// checks a [`Proof`] against. Exactly `{ issuer key Q, current date, age
/// threshold, accepted nationality set }`: the date of birth, the nationality,
/// and the digest `z` are proven equal to the signed credential's, never
/// supplied here.
#[derive(Clone, Debug)]
pub struct PublicStatement {
    /// The issuer public key `Q` the credential must be signed under. The
    /// verifier trusts this key out of band; an in-circuit trust anchor over a
    /// committed issuer set is deferred.
    pub issuer_key: AffinePoint,
    /// The verifier policy: reference date, minimum age, and accepted
    /// nationality set. Maps directly to the age / nationality public inputs.
    pub policy: Policy,
}

impl PublicStatement {
    /// Build a statement from a trusted issuer key and a policy.
    pub fn new(issuer_key: AffinePoint, policy: Policy) -> Self {
        Self { issuer_key, policy }
    }
}

/// Bridge trace size: enough rows for one active row per ECDSA instance, at the
/// SIMD minimum of `2^4 = 16` rows.
fn bridge_log_size(n_instances: usize) -> u32 {
    let needed = (n_instances.max(1) as u32)
        .next_power_of_two()
        .trailing_zeros();
    needed.max(4)
}

/// The SHA field-exposure spec for the credential bindings: expose the DOB byte
/// window (for the age consumer) **and** the nationality byte window (for the nat
/// consumer). SHA yields these six bytes on the shared `Sha256Field` channel and
/// the age + nat modules require them — four DOB bytes by age, two nationality
/// bytes by nat. Exposing a window with no consumer would leave the global
/// balance non-zero, so the exposure stays in lock-step with the wired
/// consumers; both are now wired. Prover and verifier must build the identical
/// spec (it is mixed into the SHA transcript).
fn credential_exposure() -> FieldExposure {
    FieldExposure::from_preimage_windows(&[
        (
            field_id::DOB,
            credential::DOB_WINDOW.start,
            credential::DOB_WINDOW.end - credential::DOB_WINDOW.start,
        ),
        (
            field_id::NATIONALITY,
            credential::NATIONALITY_WINDOW.start,
            credential::NATIONALITY_WINDOW.end - credential::NATIONALITY_WINDOW.start,
        ),
    ])
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
/// to the ECDSA `z`, and the age / nationality predicates are bound to the
/// credential's signed DOB / nationality bytes (see the crate docs).
//
// This is the lower-level composition primitive: it takes each module's witness
// explicitly. The relying-party-facing `prove_identity` collapses these into one
// credential + policy and is built on top; the explicit form stays public so the
// negative-test suite can compose deliberately inconsistent witnesses (e.g. hash
// one message but sign another). The argument count is intentional.
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
    prove_with_column_breakdown(
        p256_draft,
        sha_witness,
        sha_log_n_rows,
        sha_group_width,
        age_public,
        age_dob,
        nat_public,
        nat_private,
    )
    .map(|(proof, _)| proof)
}

/// The committed-column counts a single module contributes to each commitment
/// tree, captured from its [`air_core::TreeLayout`].
///
/// The proof-size byte-breakdown instrumentation (`examples/bench_report`)
/// uses these to attribute the width-linear proof streams — `queried_values` and
/// the OODS `sampled_values` — to modules by committed-column count. These are
/// the same per-tree column sizes the verifier commits against, so the
/// attribution matches the committed columns exactly.
#[derive(Clone, Debug)]
pub struct ModuleColumns {
    /// Module label, in commit order (`p256`, `sha`, `bridge`, `age`, `nat`).
    pub name: &'static str,
    /// Columns in tree 0 (preprocessed).
    pub preprocessed: usize,
    /// Columns in tree 1 (main trace + multiplicities).
    pub trace: usize,
    /// Columns in tree 2 (interaction / LogUp).
    pub interaction: usize,
}

impl ModuleColumns {
    fn of(name: &'static str, layout: &air_core::TreeLayout) -> Self {
        Self {
            name,
            preprocessed: layout.preprocessed.len(),
            trace: layout.trace.len(),
            interaction: layout.interaction.len(),
        }
    }

    /// Total committed columns across the three module-owned trees: preprocessed,
    /// trace, and interaction. The composition / quotient tree is shared and not
    /// attributed to any single module.
    pub fn total(&self) -> usize {
        self.preprocessed + self.trace + self.interaction
    }
}

struct PreparedProofModules<'a> {
    p256: P256Prover<'a>,
    sha: Sha256Prover<'a>,
    bridge: DigestBindProver,
    age: RangeCheckProver,
    nat: NatProver,
    sha_log_n_rows: u32,
    sha_group_width: u32,
    bridge_log: u32,
    age_public: &'a AgePublicInput,
    nat_public: &'a NatPublicInput,
}

#[allow(clippy::too_many_arguments)]
fn prepare_proof_modules<'a>(
    p256_draft: &'a P256ProofDraft,
    sha_witness: &'a Sha256Witness,
    sha_log_n_rows: u32,
    sha_group_width: u32,
    age_public: &'a AgePublicInput,
    age_dob: &DateOfBirth,
    nat_public: &'a NatPublicInput,
    nat_private: &NatPrivateInput,
) -> Result<PreparedProofModules<'a>, Error> {
    let scalar_z_handle = SharedScalarZRelation::new();
    let digest_handle = SharedDigestRelation::new();
    let field_handle = SharedFieldRelation::new();

    let field_exposure = credential_exposure();
    let (p256_prepared, sha_prepared) =
        if std::env::var("EU_ID_DISABLE_TRACE_FANOUT").ok().as_deref() == Some("1")
            || rayon::current_num_threads() == 1
        {
            (
                P256ColumnTask::new(p256_draft).run(),
                Sha256ColumnTask::new(
                    sha_witness,
                    sha_log_n_rows,
                    sha_group_width,
                    field_exposure.clone(),
                )
                .run(),
            )
        } else {
            rayon::join(
                || P256ColumnTask::new(p256_draft).run(),
                || {
                    Sha256ColumnTask::new(
                        sha_witness,
                        sha_log_n_rows,
                        sha_group_width,
                        field_exposure.clone(),
                    )
                    .run()
                },
            )
        };

    let p256 = P256Prover::from_prepared(p256_draft, p256_prepared.map_err(Error::P256Prepare)?)
        .with_z_binding(scalar_z_handle.clone());
    // SHA both yields its digest (P256↔SHA bridge) and exposes the DOB +
    // nationality byte windows (age/nat↔credential bridges) on the
    // shared field channel.
    let sha = Sha256Prover::new_with_prepared(
        sha_witness,
        sha_log_n_rows,
        sha_group_width,
        field_exposure.clone(),
        sha_prepared,
    )
    .with_digest_handle(digest_handle.clone())
    .with_field_handle(field_exposure, field_handle.clone());

    let instances = p256.proof_claim().public_inputs.instances.clone();
    let rows = bridge_rows(&instances);
    let bridge_log = bridge_log_size(rows.len());
    let bridge = DigestBindProver::new(rows, bridge_log, scalar_z_handle, digest_handle);

    // The predicate modules. `range_check` is the canonical age strategy for the
    // combined proof (the standalone default); the bit-decomposition strategy
    // stays available standalone for benchmarking. The wrapper's `PcsConfig` is
    // unused by `prover()` — only the input validation and witness generation it
    // performs matter; the shared orchestrator config below governs the proof.
    //
    // Both predicate modules are **credential-bound**. `with_dob_binding`
    // makes age require the DOB bytes SHA yields, so the date of birth it proves
    // ≥ the threshold is provably the signed credential's; `with_nat_binding`
    // makes nat require the nationality bytes SHA yields, so the code it
    // proves ∈ the accepted set is provably the signed credential's. A prover can
    // no longer attest age from a date — or membership from a code — the
    // credential does not contain.
    let age = AgeRangeCheck::new(PcsConfig::default())
        .prover(age_public, age_dob)
        .map_err(Error::AgePrepare)?
        .with_dob_binding(field_handle.clone());
    let nat = NationalityPredicate::new(PcsConfig::default())
        .prover(nat_public, nat_private)
        .map_err(Error::NatPrepare)?
        .with_nat_binding(field_handle.clone());

    Ok(PreparedProofModules {
        p256,
        sha,
        bridge,
        age,
        nat,
        sha_log_n_rows,
        sha_group_width,
        bridge_log,
        age_public,
        nat_public,
    })
}

fn prove_prepared_with_config(
    mut prepared: PreparedProofModules<'_>,
    config: PcsConfig,
) -> Result<(Proof, Vec<ModuleColumns>), Error> {
    let PreparedProofModules {
        ref mut p256,
        ref mut sha,
        ref mut bridge,
        ref mut age,
        ref mut nat,
        sha_log_n_rows,
        sha_group_width,
        bridge_log,
        age_public,
        nat_public,
    } = prepared;

    // Capture each module's committed-column counts before the modules are
    // borrowed into the prove slice. `layout()` is available right after
    // construction (the verifier reads it pre-build too), and these are the same
    // per-tree sizes committed below — the byte-breakdown attributes the
    // width-linear streams by them.
    let column_breakdown = vec![
        ModuleColumns::of("p256", &p256.layout()),
        ModuleColumns::of("sha", &sha.layout()),
        ModuleColumns::of("bridge", &bridge.layout()),
        ModuleColumns::of("age", &age.layout()),
        ModuleColumns::of("nat", &nat.layout()),
    ];

    // Module order is load-bearing: it fixes the transcript, the tree-column /
    // preprocessed-id concatenation, and the order the shared relations are
    // drawn. P256 draws ScalarZ, SHA draws the digest + the credential-field
    // relation, the bridge reads ScalarZ + the digest, and age + nat read the
    // field relation — so every consumer follows SHA (and the bridge follows its
    // two producers). Age and nat append after the binding cluster.
    //
    // The credential bindings ride the cross-module `Sha256Field` LogUp channel
    // (drawn from the transcript), not a preprocessed column, so they add no
    // preprocessed id and cannot collide with one. The preprocessed-id namespaces
    // stay disjoint — age uses `age/...` and the generic `range_check_[0, N]`
    // delta tables, nat uses `nat/...` (incl. the accepted-set `nat/acceptable/...`
    // column); neither aliases SHA's `sha256_range_*`, P256's `p256_*`, or the
    // bridge's `digest_bind_*` ids in the shared allocator. The verifier must use
    // this same order.
    let stark_proof = {
        let mut modules: [&mut dyn AirProver; 5] = [p256, sha, bridge, age, nat];
        air_core::prove(&mut modules, config).map_err(|e| Error::Prove(format!("{e:?}")))?
    };
    #[cfg(feature = "gkr-spike")]
    let sha_xor_8_gkr_proof = sha.xor_8_gkr_proof().clone();

    let proof = Proof {
        stark_proof,
        p256_claim: p256.proof_claim().clone(),
        p256_interaction_claim: p256.interaction_claim().clone(),
        sha_log_n_rows,
        sha_group_width,
        sha_interaction_claim: sha.interaction_claim().clone(),
        #[cfg(feature = "gkr-spike")]
        sha_xor_8_gkr_proof,
        bridge_log_size: bridge_log,
        bridge_interaction_claim: bridge.interaction_claim().clone(),
        // Claimed sums are populated by the modules' interaction phase during the
        // `prove` call above (the slice borrow has been released here).
        age_public: *age_public,
        age_claimed_sums: age.claimed_sums(),
        nat_public: nat_public.clone(),
        nat_claimed_sums: nat.claimed_sums(),
    };
    Ok((proof, column_breakdown))
}

/// Like [`prove`], but also returns each module's committed-column counts in
/// commit order — the per-module attribution input for the proof-size
/// byte-breakdown. The counts come from the **same** module instances that
/// produce the proof, so they cannot drift from what was committed.
#[allow(clippy::too_many_arguments)]
pub fn prove_with_column_breakdown(
    p256_draft: &P256ProofDraft,
    sha_witness: &Sha256Witness,
    sha_log_n_rows: u32,
    sha_group_width: u32,
    age_public: &AgePublicInput,
    age_dob: &DateOfBirth,
    nat_public: &NatPublicInput,
    nat_private: &NatPrivateInput,
) -> Result<(Proof, Vec<ModuleColumns>), Error> {
    let prepared = prepare_proof_modules(
        p256_draft,
        sha_witness,
        sha_log_n_rows,
        sha_group_width,
        age_public,
        age_dob,
        nat_public,
        nat_private,
    )?;
    let config = prepared.p256.pcs_config();
    prove_prepared_with_config(prepared, config)
}

/// FRI-sweep harness only (WO-3.3). Production config changes remain sanctioned-change-only (HANDOVER rule).
#[cfg(feature = "fri-sweep")]
#[allow(clippy::too_many_arguments)]
pub fn prove_with_column_breakdown_and_config(
    p256_draft: &P256ProofDraft,
    sha_witness: &Sha256Witness,
    sha_log_n_rows: u32,
    sha_group_width: u32,
    age_public: &AgePublicInput,
    age_dob: &DateOfBirth,
    nat_public: &NatPublicInput,
    nat_private: &NatPrivateInput,
    config: PcsConfig,
) -> Result<(Proof, Vec<ModuleColumns>), Error> {
    let prepared = prepare_proof_modules(
        p256_draft,
        sha_witness,
        sha_log_n_rows,
        sha_group_width,
        age_public,
        age_dob,
        nat_public,
        nat_private,
    )?;
    prove_prepared_with_config(prepared, config)
}

/// FRI-sweep harness only (WO-3.3/WO-3.1). Production verification remains pinned to P256's sanctioned config.
#[cfg(feature = "fri-sweep")]
pub fn verify_with_config(
    proof: &Proof,
    expected_instances: &[PublicEcdsaInstance<M31>],
    config: PcsConfig,
) -> Result<(), Error> {
    if !instances_match_ignoring_z(
        &proof.p256_claim.public_inputs.instances,
        expected_instances,
    ) {
        return Err(Error::P256InstanceMismatch);
    }
    verify_stark_with_config(proof, Some(config))
}

/// Prove an identity statement from a credential, an issuer signing key, and a
/// policy — the relying-party-facing entry point.
///
/// Signs `credential` with `issuer` (real ES256, so `z = SHA-256(C)`), composes
/// the pipeline witness, and drives all five modules through [`prove`]. The
/// returned [`Proof`] is bound: `z == SHA-256(C)`, and the date of birth /
/// nationality the predicates reason about are the credential's signed bytes.
/// Proving a false statement fails here — e.g. an under-age date of birth is
/// rejected by the age module's witness generation ([`Error::AgePrepare`]).
///
/// Pair the returned proof with [`verify_identity`] against a [`PublicStatement`]
/// built from the issuer's *public* key and the same policy.
pub fn prove_identity(
    credential: &Credential,
    issuer: &IssuerKey,
    policy: &Policy,
) -> Result<Proof, Error> {
    let signed = generator::sign_credential(credential, issuer);
    let witness = PipelineWitness::build(signed, policy.clone());
    let draft = witness.p256_draft.as_ref().ok_or(Error::SignatureInvalid)?;
    prove(
        draft,
        &witness.sha_witness,
        witness.sha_log_n_rows,
        witness.sha_group_width,
        &witness.age_public,
        &witness.age_dob,
        &witness.nat_public,
        &witness.nat_private,
    )
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
///
/// This is the lower-level verify against an explicit ECDSA instance list.
/// Relying parties should prefer [`verify_identity`], which checks the small
/// public statement `{ Q, policy }` instead.
pub fn verify(proof: &Proof, expected_instances: &[PublicEcdsaInstance<M31>]) -> Result<(), Error> {
    // Caller-argument binding for the P256 statement, minus `z` (internally
    // bound to the SHA digest).
    if !instances_match_ignoring_z(
        &proof.p256_claim.public_inputs.instances,
        expected_instances,
    ) {
        return Err(Error::P256InstanceMismatch);
    }
    verify_stark(proof)
}

/// Verify a [`Proof`] against a relying party's [`PublicStatement`] — the
/// credential-API counterpart of [`prove_identity`].
///
/// Caller-argument binding for the full statement: the issuer key `Q` against the
/// ECDSA instance's public-key limbs, the reference date + threshold against the
/// age public input, and the accepted set against the nationality public input.
/// `z`, the date of birth, and the nationality are not supplied — they are proven
/// equal to the credential's. Then checks the shared STARK (the global LogUp
/// balance). Returns `Ok(())` iff every check passes.
pub fn verify_identity(proof: &Proof, statement: &PublicStatement) -> Result<(), Error> {
    // Issuer key: every ECDSA instance's public-key limbs must equal `Q`. The
    // MVP proves a single signature, so there is exactly one instance; an empty
    // instance list never satisfies a concrete issuer.
    let expected_pub_x = P256M31BigInt::from_u256(&statement.issuer_key.x);
    let expected_pub_y = P256M31BigInt::from_u256(&statement.issuer_key.y);
    let instances = &proof.p256_claim.public_inputs.instances;
    if instances.is_empty()
        || !instances
            .iter()
            .all(|i| i.pub_x == expected_pub_x && i.pub_y == expected_pub_y)
    {
        return Err(Error::IssuerKeyMismatch);
    }

    // Policy: the proven age / nationality public inputs must equal the policy's.
    // Both sides build them from the policy the same way, so equality holds iff
    // the reference date, threshold, and normalized accepted set all match.
    if proof.age_public != statement.policy.age_public_input() {
        return Err(Error::AgePolicyMismatch);
    }
    if proof.nat_public != statement.policy.nat_public_input() {
        return Err(Error::NatPolicyMismatch);
    }

    verify_stark(proof)
}

/// Rebuild the five verifier modules from the proof and check the shared STARK
/// (the global LogUp balance). The caller does any public-input / statement
/// binding *first*: both [`verify`] and [`verify_identity`] bind, then delegate
/// here.
fn verify_stark(proof: &Proof) -> Result<(), Error> {
    verify_stark_with_config(proof, None)
}

fn verify_stark_with_config(
    proof: &Proof,
    expected_config_override: Option<PcsConfig>,
) -> Result<(), Error> {
    let scalar_z_handle = SharedScalarZRelation::new();
    let digest_handle = SharedDigestRelation::new();
    let field_handle = SharedFieldRelation::new();

    let mut p256 = P256Verifier::new(
        proof.p256_claim.clone(),
        proof.p256_interaction_claim.clone(),
    )
    .with_z_binding(scalar_z_handle.clone());
    let sha = Sha256Verifier::new(
        proof.sha_log_n_rows,
        proof.sha_group_width,
        proof.sha_interaction_claim.clone(),
    );
    #[cfg(feature = "gkr-spike")]
    let sha = sha.with_xor_8_gkr_proof(proof.sha_xor_8_gkr_proof.clone());
    let mut sha = sha
        .with_digest_handle(digest_handle.clone())
        .with_field_handle(credential_exposure(), field_handle.clone());
    let mut bridge = DigestBindVerifier::new(
        proof.bridge_log_size,
        proof.bridge_interaction_claim.clone(),
        scalar_z_handle,
        digest_handle,
    );

    // Rebuild the predicate verifier modules from the public input and claimed
    // sums carried in the proof, with the same canonical strategy the prover
    // used (`range_check` for age). Both modules are credential-bound, so each
    // reads the same shared field channel to reconstruct its require terms.
    let mut age = AgeRangeCheck::new(PcsConfig::default())
        .verifier(&proof.age_public, &proof.age_claimed_sums)
        .map_err(Error::AgePrepare)?
        .with_dob_binding(field_handle.clone());
    let mut nat = NationalityPredicate::new(PcsConfig::default())
        .verifier(&proof.nat_public, &proof.nat_claimed_sums)
        .map_err(Error::NatPrepare)?
        .with_nat_binding(field_handle.clone());

    // Pin the PCS config. The combined proof inherits the P256 module's
    // security-calibrated config (`prove` drives the whole STARK with
    // `p256.pcs_config()`), and the config is prover-supplied inside
    // `proof.stark_proof`. Reject a weakened FRI/grinding setting outright rather
    // than inherit it — the standalone P256 verifier (`verify_current_air`) does
    // the same. Checked before the STARK verification so a low-query proof never
    // reaches it.
    let expected_config = expected_config_override.unwrap_or_else(|| p256.expected_pcs_config());
    if proof.stark_proof.config != expected_config {
        return Err(Error::WeakConfig {
            got: proof.stark_proof.config,
            expected: expected_config,
        });
    }

    // Same module order as the prover.
    let mut modules: [&mut dyn Air; 5] = [&mut p256, &mut sha, &mut bridge, &mut age, &mut nat];
    air_core::verify(&mut modules, &proof.stark_proof).map_err(|e| Error::Verify(format!("{e:?}")))
}
