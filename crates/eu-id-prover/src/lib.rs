//! End-to-end `eu-id` prover.
//!
//! The product path is the ISO mdoc API: [`prove_mdoc`] parses a PID mdoc,
//! checks the verifier request and host-side trust material, builds the public
//! mdoc statement, and proves it; [`verify_mdoc`] verifies that proof against
//! the statement. The mdoc path uses ISO device authentication for freshness, so
//! it does not include the legacy nonce module.
//!
//! The older [`prove_identity`] / [`verify_identity`] API is retained as the
//! 11-byte proof-of-concept path for parity benchmarks and regression tests. It
//! composes the per-circuit `air_core` modules into a single STARK proof and
//! still includes the nonce P-256 module described below.
//!
//! This is the standalone library the `eu-id-ffi` C-ABI surface wraps. The POC
//! identity path drives
//! the credential P256 ECDSA module, a second **nonce** P256 ECDSA module (the
//! holder-presence device-key signature), the SHA-256 module, the **digest-bind
//! bridge**, and the **age** and **nationality** predicate modules through one
//! [`air_core::prove`] call — one channel, one commitment scheme, one proof —
//! and verifies the global LogUp balance.
//!
//! ## Holder presence: the nonce P-256 module
//!
//! Alongside the credential signature, the proof carries a second P-256 module
//! proving the holder's device key signed `SHA-256(domain || nonce)` (see
//! [`nonce`]). It is folded into the same STARK with its own preprocessed
//! namespace and no z-binding, so a single proof attests both "this credential
//! was issued to me" and "I am present now, signing this fresh nonce". The
//! verifier binds it in full (including `z`, recomputed from the public nonce)
//! against [`PublicStatement::nonce`].
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
//! ## Legacy POC API & public statement
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
pub mod mdoc;
#[cfg(feature = "ec-coprocessor")]
pub(crate) mod mdoc_mac;
mod mdoc_validity;
mod mdoc_window_bind;
pub mod nonce;
#[cfg(feature = "ec-coprocessor")]
mod public_digest_bind;
#[cfg(test)]
mod shape_dump;

pub use credential::Credential;
pub use generator::{IssuerKey, PipelineWitness, Policy, SignedCredential};
#[cfg(not(feature = "ec-coprocessor"))]
pub use mdoc::{
    MdocCircuitProof as MdocProof, MdocCircuitStatement as MdocStatement, MdocPidRequest,
};
#[cfg(feature = "ec-coprocessor")]
pub use mdoc::{
    MdocCircuitProof as MdocProof, MdocPidRequest, MdocPublicStatement as MdocStatement,
};
pub use nonce::{
    nonce_expected_preprocessed_root, nonce_signature_message, prove_nonce_signature,
    verify_nonce_signature, verify_nonce_signature_with_preprocessed_root, NonceSignatureProof,
    NonceSignatureStatement,
};
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

/// Build and prove the product mdoc circuit from the full document, verifier
/// request, and public policy. Returns both the proof and verifier statement.
pub fn prove_mdoc(
    document: &[u8],
    request: &MdocPidRequest,
    policy: Policy,
) -> Result<(MdocProof, MdocStatement), Error> {
    let extracted = mdoc::extract_pid_mdoc(document, request).map_err(Error::Mdoc)?;
    let statement =
        mdoc::MdocCircuitStatement::from_extracted(&extracted, policy).map_err(Error::Mdoc)?;
    let proof = mdoc::prove_mdoc_circuit(&extracted, &statement)?;
    #[cfg(feature = "ec-coprocessor")]
    {
        Ok((proof, MdocStatement::from_circuit(&statement)))
    }
    #[cfg(not(feature = "ec-coprocessor"))]
    {
        Ok((proof, statement))
    }
}

/// Verify a product mdoc proof against its public mdoc statement.
pub fn verify_mdoc(proof: &MdocProof, statement: &MdocStatement) -> Result<(), Error> {
    #[cfg(feature = "ec-coprocessor")]
    {
        mdoc::verify_mdoc_public_statement(proof, statement)
    }
    #[cfg(not(feature = "ec-coprocessor"))]
    {
        mdoc::verify_mdoc_circuit(proof, statement)
    }
}

#[cfg(not(feature = "ec-coprocessor"))]
const NONCE_P256_PREPROCESSED_NAMESPACE: &str = "nonce_p256";

use air_core::relations::{field_id, SharedDigestRelation, SharedFieldRelation};
use air_core::{Air, AirProver};
#[cfg(feature = "ec-coprocessor")]
use blake2::{Blake2s256, Digest as BlakeDigest};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
#[cfg(feature = "ec-coprocessor")]
use stwo::core::fri::FriConfig;
use stwo::core::pcs::PcsConfig;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;
#[cfg(feature = "ec-coprocessor")]
use stwo::core::{air::Component, channel::Channel, verifier::VerificationError};
#[cfg(feature = "ec-coprocessor")]
use stwo::prover::backend::simd::SimdBackend;
#[cfg(feature = "ec-coprocessor")]
use stwo::prover::{ComponentProver, TreeBuilder};
#[cfg(feature = "ec-coprocessor")]
use stwo_constraint_framework::TraceLocationAllocator;

use predicates::age::strategy::range_check::air::RangeCheckProver;
use predicates::nat::air::NatProver;
use predicates::nat::NationalityPredicate;
use predicates::{
    AgeRangeCheck, DateOfBirth, NatPrivateInput, NatPublicInput, PredicateProver,
    PredicateVerifier, PublicInput as AgePublicInput,
};

#[cfg(not(feature = "ec-coprocessor"))]
use stwo_p256::components::digest_bind::module::{
    DigestBindInteractionClaim, DigestBindProver, DigestBindVerifier,
};
#[cfg(any(not(feature = "ec-coprocessor"), test))]
use stwo_p256::components::digest_bind::witness::DigestBindRow;
#[cfg(not(feature = "ec-coprocessor"))]
use stwo_p256::components::digest_bind::SharedScalarZRelation;
use stwo_p256::ecdsa::ecdsa_verify;
use stwo_p256::limbs::P256M31BigInt;
#[cfg(not(feature = "ec-coprocessor"))]
use stwo_p256::proof::air::{P256ColumnTask, P256Prover, P256Verifier};
use stwo_p256::proof::P256ProofDraft;
#[cfg(not(feature = "ec-coprocessor"))]
use stwo_p256::proof::{P256CurrentAirInteractionClaim, P256CurrentAirProofClaim};
use stwo_p256::public_inputs::PublicEcdsaInstance;
// Re-exported: `AffinePoint` is the type of `PublicStatement::issuer_key`, so a
// relying party needs it in scope to build a statement.
pub use stwo_p256::types::AffinePoint;

#[cfg(feature = "ec-coprocessor")]
use crate::public_digest_bind::{PublicDigestBind, PublicDigestBindInteractionClaim};

#[cfg(feature = "ec-coprocessor")]
pub mod ec_coprocessor {
    use eu_id_ec_coprocessor::ecdsa::{
        ecdsa_statement_transcript_segments, generate_witness, implemented_circuit_family_labels,
        implemented_circuit_gate_count, implemented_circuit_transcript_shapes,
        prove_implemented_circuit_bundle, prove_implemented_circuit_bundle_batch,
        prove_implemented_circuit_bundle_batch_with_projection, prove_implemented_circuit_proofs,
        verify_implemented_circuit_bundle, verify_implemented_circuit_bundle_batch,
        verify_implemented_circuit_bundle_batch_with_projection, verify_implemented_circuit_proofs,
        verify_implemented_circuits, verify_witness, CircuitTranscriptShape,
        EcdsaInput as S4EcdsaInput, EcdsaPublicProjection as S4EcdsaPublicProjection,
        ImplementedCircuitBundle, ImplementedCircuitProofError, ImplementedCircuitProofs, Witness,
        WitnessError,
    };
    use eu_id_ec_coprocessor::sumcheck::InputClaims;
    use eu_id_ec_coprocessor::{CircuitError, TranscriptSeed};
    use stwo::core::fields::m31::M31;
    use stwo_p256::public_inputs::PublicEcdsaInstance;
    use stwo_p256::types::EcdsaVerifyInput;

    pub fn input_from_stwo(input: &EcdsaVerifyInput) -> S4EcdsaInput {
        S4EcdsaInput {
            z: input.message_hash.0,
            r: input.signature.r.0,
            s: input.signature.s.0,
            qx: input.public_key.x.0,
            qy: input.public_key.y.0,
        }
    }

    pub fn full_projection_from_stwo(input: &EcdsaVerifyInput) -> S4EcdsaPublicProjection {
        S4EcdsaPublicProjection::full(&input_from_stwo(input))
    }

    pub fn issuer_key_projection_from_stwo(input: &EcdsaVerifyInput) -> S4EcdsaPublicProjection {
        S4EcdsaPublicProjection::issuer_key_only(input.public_key.x.0, input.public_key.y.0)
    }

    pub fn message_hash_projection_from_stwo(input: &EcdsaVerifyInput) -> S4EcdsaPublicProjection {
        S4EcdsaPublicProjection::message_hash_only(input.message_hash.0)
    }

    pub fn generate_witness_from_stwo(input: &EcdsaVerifyInput) -> Result<Witness, WitnessError> {
        generate_witness(&input_from_stwo(input))
    }

    pub fn verify_witness_from_stwo(
        input: &EcdsaVerifyInput,
        witness: &Witness,
    ) -> Result<(), WitnessError> {
        verify_witness(&input_from_stwo(input), witness)
    }

    pub fn verify_implemented_circuits_from_stwo(
        input: &EcdsaVerifyInput,
        witness: &Witness,
    ) -> Result<(), WitnessError> {
        verify_implemented_circuits(&input_from_stwo(input), witness)
    }

    pub fn prove_implemented_circuit_proofs_from_stwo(
        input: &EcdsaVerifyInput,
        witness: &Witness,
        commitment_root: [u8; 32],
        transcript_seed: TranscriptSeed,
    ) -> Result<ImplementedCircuitProofs, ImplementedCircuitProofError> {
        prove_implemented_circuit_proofs(
            &input_from_stwo(input),
            witness,
            commitment_root,
            transcript_seed,
        )
    }

    pub fn verify_implemented_circuit_proofs_from_stwo(
        proofs: &ImplementedCircuitProofs,
        commitment_root: [u8; 32],
        transcript_seed: TranscriptSeed,
    ) -> Result<Vec<InputClaims>, ImplementedCircuitProofError> {
        verify_implemented_circuit_proofs(proofs, commitment_root, transcript_seed)
    }

    pub fn implemented_circuit_family_labels_from_stwo() -> Result<Vec<&'static [u8]>, CircuitError>
    {
        implemented_circuit_family_labels()
    }

    pub fn implemented_circuit_gate_count_from_stwo() -> Result<usize, CircuitError> {
        implemented_circuit_gate_count()
    }

    pub fn implemented_circuit_transcript_shapes_from_stwo(
    ) -> Result<Vec<CircuitTranscriptShape>, CircuitError> {
        implemented_circuit_transcript_shapes()
    }

    pub fn statement_transcript_segments_from_stwo(
        input: &EcdsaVerifyInput,
    ) -> Result<Vec<Vec<u8>>, WitnessError> {
        ecdsa_statement_transcript_segments(&input_from_stwo(input))
    }

    pub fn public_projection_transcript_segments(
        projection: &S4EcdsaPublicProjection,
    ) -> Vec<Vec<u8>> {
        eu_id_ec_coprocessor::ecdsa::ecdsa_public_projection_transcript_segments(projection)
    }

    pub fn prove_implemented_circuit_bundle_from_stwo(
        input: &EcdsaVerifyInput,
        witness: &Witness,
        transcript_seed: TranscriptSeed,
    ) -> Result<ImplementedCircuitBundle, ImplementedCircuitProofError> {
        prove_implemented_circuit_bundle(&input_from_stwo(input), witness, transcript_seed)
    }

    pub fn prove_implemented_circuit_bundle_batch_from_stwo(
        inputs: &[EcdsaVerifyInput],
        witnesses: &[Witness],
        transcript_seed: TranscriptSeed,
    ) -> Result<ImplementedCircuitBundle, ImplementedCircuitProofError> {
        let inputs = inputs.iter().map(input_from_stwo).collect::<Vec<_>>();
        prove_implemented_circuit_bundle_batch(&inputs, witnesses, transcript_seed)
    }

    pub fn prove_implemented_circuit_bundle_batch_with_projection_from_stwo(
        inputs: &[EcdsaVerifyInput],
        projections: &[S4EcdsaPublicProjection],
        witnesses: &[Witness],
        transcript_seed: TranscriptSeed,
    ) -> Result<ImplementedCircuitBundle, ImplementedCircuitProofError> {
        let inputs = inputs.iter().map(input_from_stwo).collect::<Vec<_>>();
        prove_implemented_circuit_bundle_batch_with_projection(
            &inputs,
            projections,
            witnesses,
            transcript_seed,
        )
    }

    pub fn prove_mdoc_p4b_circuit_bundle_from_stwo(
        issuer_input: &EcdsaVerifyInput,
        issuer_projection: &S4EcdsaPublicProjection,
        issuer_witness: &Witness,
        device_input: &EcdsaVerifyInput,
        device_projection: &S4EcdsaPublicProjection,
        device_witness: &Witness,
        mac_key_shares: &eu_id_ec_coprocessor::ecdsa::MdocP4bMacKeyShares,
        transcript_seed: TranscriptSeed,
    ) -> Result<ImplementedCircuitBundle, ImplementedCircuitProofError> {
        eu_id_ec_coprocessor::ecdsa::prove_mdoc_p4b_circuit_bundle(
            &input_from_stwo(issuer_input),
            issuer_projection,
            issuer_witness,
            &input_from_stwo(device_input),
            device_projection,
            device_witness,
            mac_key_shares,
            transcript_seed,
        )
    }

    pub fn prove_mdoc_p4b_circuit_bundle_from_stwo_profiled(
        issuer_input: &EcdsaVerifyInput,
        issuer_projection: &S4EcdsaPublicProjection,
        issuer_witness: &Witness,
        device_input: &EcdsaVerifyInput,
        device_projection: &S4EcdsaPublicProjection,
        device_witness: &Witness,
        mac_key_shares: &eu_id_ec_coprocessor::ecdsa::MdocP4bMacKeyShares,
        transcript_seed: TranscriptSeed,
    ) -> Result<
        (
            ImplementedCircuitBundle,
            eu_id_ec_coprocessor::ecdsa::MdocP4bProveProfile,
        ),
        ImplementedCircuitProofError,
    > {
        eu_id_ec_coprocessor::ecdsa::prove_mdoc_p4b_circuit_bundle_profiled(
            &input_from_stwo(issuer_input),
            issuer_projection,
            issuer_witness,
            &input_from_stwo(device_input),
            device_projection,
            device_witness,
            mac_key_shares,
            transcript_seed,
        )
    }

    pub fn verify_mdoc_p4b_circuit_bundle_from_stwo(
        issuer_projection: &S4EcdsaPublicProjection,
        device_projection: &S4EcdsaPublicProjection,
        bundle: &ImplementedCircuitBundle,
        transcript_seed: TranscriptSeed,
    ) -> Result<(), ImplementedCircuitProofError> {
        eu_id_ec_coprocessor::ecdsa::verify_mdoc_p4b_circuit_bundle(
            issuer_projection,
            device_projection,
            bundle,
            transcript_seed,
        )
    }

    pub fn verify_mdoc_p4b_circuit_bundle_from_stwo_profiled(
        issuer_projection: &S4EcdsaPublicProjection,
        device_projection: &S4EcdsaPublicProjection,
        bundle: &ImplementedCircuitBundle,
        transcript_seed: TranscriptSeed,
    ) -> Result<eu_id_ec_coprocessor::ecdsa::MdocP4bVerifyProfile, ImplementedCircuitProofError>
    {
        eu_id_ec_coprocessor::ecdsa::verify_mdoc_p4b_circuit_bundle_profiled(
            issuer_projection,
            device_projection,
            bundle,
            transcript_seed,
        )
    }

    pub fn mdoc_p4b_av_from_bundle(
        bundle: &ImplementedCircuitBundle,
        transcript_seed: TranscriptSeed,
    ) -> eu_id_ec_coprocessor::mac::Gf128 {
        eu_id_ec_coprocessor::ecdsa::mdoc_p4b_av_from_root(transcript_seed, bundle.root)
    }

    pub fn verify_implemented_circuit_bundle_from_stwo(
        input: &EcdsaVerifyInput,
        bundle: &ImplementedCircuitBundle,
        transcript_seed: TranscriptSeed,
    ) -> Result<Vec<InputClaims>, ImplementedCircuitProofError> {
        verify_implemented_circuit_bundle(&input_from_stwo(input), bundle, transcript_seed)
    }

    pub fn verify_implemented_circuit_bundle_batch_from_stwo(
        inputs: &[EcdsaVerifyInput],
        bundle: &ImplementedCircuitBundle,
        transcript_seed: TranscriptSeed,
    ) -> Result<Vec<Vec<InputClaims>>, ImplementedCircuitProofError> {
        let inputs = inputs.iter().map(input_from_stwo).collect::<Vec<_>>();
        verify_implemented_circuit_bundle_batch(&inputs, bundle, transcript_seed)
    }

    pub fn verify_implemented_circuit_bundle_batch_with_projection_from_stwo(
        projections: &[S4EcdsaPublicProjection],
        bundle: &ImplementedCircuitBundle,
        transcript_seed: TranscriptSeed,
    ) -> Result<Vec<Vec<InputClaims>>, ImplementedCircuitProofError> {
        verify_implemented_circuit_bundle_batch_with_projection(
            projections,
            bundle,
            transcript_seed,
        )
    }

    pub fn verify_implemented_circuit_bundle_from_public_instance(
        instance: &PublicEcdsaInstance<M31>,
        bundle: &ImplementedCircuitBundle,
        transcript_seed: TranscriptSeed,
    ) -> Result<Vec<InputClaims>, ImplementedCircuitProofError> {
        let input = S4EcdsaInput {
            z: instance.z.to_u256().0,
            r: instance.r.to_u256().0,
            s: instance.s.to_u256().0,
            qx: instance.pub_x.to_u256().0,
            qy: instance.pub_y.to_u256().0,
        };
        verify_implemented_circuit_bundle(&input, bundle, transcript_seed)
    }
}

use stwo_sha256::air::{Sha256ColumnTask, Sha256Prover, Sha256Verifier};
use stwo_sha256::field_exposure::FieldExposure;
use stwo_sha256::interaction::InteractionClaim as Sha256InteractionClaim;
use stwo_sha256::types::Sha256Witness;

#[cfg(feature = "ec-coprocessor")]
#[derive(Clone, Serialize, Deserialize)]
struct CoprocessorBundles {
    signatures: eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle,
}

/// A single STARK proof over the composed P256 + SHA + digest-bind modules, plus
/// the public claims the verifier needs to reconstruct each module.
///
/// Serde-serializable end to end (the per-module claim trees derive serde), so
/// the `eu-id` CLI can write a proof in one process and verify it in another.
#[derive(Serialize, Deserialize)]
pub struct Proof {
    /// The one shared STARK proof.
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
    // Credential P256 module reconstruction data.
    #[cfg(feature = "ec-coprocessor")]
    coprocessor_bundles: Option<CoprocessorBundles>,
    #[cfg(feature = "ec-coprocessor")]
    credential_instances: Vec<PublicEcdsaInstance<M31>>,
    #[cfg(not(feature = "ec-coprocessor"))]
    p256_claim: P256CurrentAirProofClaim,
    #[cfg(not(feature = "ec-coprocessor"))]
    p256_interaction_claim: P256CurrentAirInteractionClaim,
    // Nonce P256 module reconstruction data (the holder device-key signature).
    // Feature-off proves this as a P256 AIR module; feature-on verifies it in the
    // EC coprocessor and carries only the public instance for statement binding.
    #[cfg(feature = "ec-coprocessor")]
    nonce_instances: Vec<PublicEcdsaInstance<M31>>,
    #[cfg(not(feature = "ec-coprocessor"))]
    nonce_p256_claim: P256CurrentAirProofClaim,
    #[cfg(not(feature = "ec-coprocessor"))]
    nonce_p256_interaction_claim: P256CurrentAirInteractionClaim,
    // SHA module reconstruction data.
    sha_log_n_rows: u32,
    sha_group_width: u32,
    sha_interaction_claim: Sha256InteractionClaim,
    // Digest-bind bridge reconstruction data.
    #[cfg(not(feature = "ec-coprocessor"))]
    bridge_log_size: u32,
    #[cfg(not(feature = "ec-coprocessor"))]
    bridge_interaction_claim: DigestBindInteractionClaim,
    #[cfg(feature = "ec-coprocessor")]
    public_digest_bind_interaction_claim: PublicDigestBindInteractionClaim,
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
        #[cfg(feature = "ec-coprocessor")]
        {
            &self.credential_instances
        }
        #[cfg(not(feature = "ec-coprocessor"))]
        {
            &self.p256_claim.public_inputs.instances
        }
    }

    /// The public ECDSA instances the nonce P256 module proves over — the holder
    /// device-key signature. Unlike the credential instances, these are bound in
    /// full (`z` included). [`verify`] takes the expected nonce statement
    /// explicitly.
    pub fn nonce_p256_instances(&self) -> &[PublicEcdsaInstance<M31>] {
        #[cfg(feature = "ec-coprocessor")]
        {
            &self.nonce_instances
        }
        #[cfg(not(feature = "ec-coprocessor"))]
        {
            &self.nonce_p256_claim.public_inputs.instances
        }
    }

    #[cfg(feature = "ec-coprocessor")]
    pub fn coprocessor_bundle(
        &self,
    ) -> Option<&eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle> {
        self.coprocessor_bundles
            .as_ref()
            .map(|bundles| &bundles.signatures)
    }

    #[cfg(feature = "ec-coprocessor")]
    pub fn nonce_coprocessor_bundle(
        &self,
    ) -> Option<&eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle> {
        self.coprocessor_bundles
            .as_ref()
            .map(|bundles| &bundles.signatures)
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
    /// mdoc extraction or statement construction failed before proving.
    Mdoc(mdoc::MdocError),
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
    #[cfg(feature = "ec-coprocessor")]
    /// The feature-gated EC coprocessor payload is missing from a relying-party
    /// proof.
    CoprocessorMissing,
    #[cfg(feature = "ec-coprocessor")]
    /// The current S4-lite coprocessor payload binds one ECDSA instance.
    CoprocessorInstanceCount { actual: usize },
    #[cfg(feature = "ec-coprocessor")]
    /// S4-lite witness generation failed for the existing P256 input.
    CoprocessorWitness(eu_id_ec_coprocessor::ecdsa::WitnessError),
    #[cfg(feature = "ec-coprocessor")]
    /// S4-lite proof generation or verification failed.
    CoprocessorProof(eu_id_ec_coprocessor::ecdsa::ImplementedCircuitProofError),
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
    /// The proof's tree-0 (preprocessed) commitment root does not match the
    /// verifier-derived expected root — a forged preprocessed tree (range
    /// tables, schedules, constants; the F-ROOT finding). Rejected before the
    /// STARK check. The Blake2s root pin is the tree-0 soundness anchor; the
    /// prover-side 64-bit `DefaultHasher` fingerprint guard is not.
    PreprocessedRootMismatch {
        /// The tree-0 root embedded in the proof.
        got: air_core::CommitmentRoot,
        /// The root the verifier derived independently.
        expected: air_core::CommitmentRoot,
    },
}

/// The relying party's public statement — the only thing [`verify_identity`]
/// checks a [`Proof`] against. `{ issuer key Q, current date, age threshold,
/// accepted nationality set, holder nonce signature }`: the date of birth, the
/// nationality, and the credential digest `z` are proven equal to the signed
/// credential's, never supplied here. The nonce signature *is* supplied — the
/// verifier recomputes its `z` from the public nonce and binds the nonce P-256
/// module against the full instance.
#[derive(Clone, Debug)]
pub struct PublicStatement {
    /// The issuer public key `Q` the credential must be signed under. The
    /// verifier trusts this key out of band; an in-circuit trust anchor over a
    /// committed issuer set is deferred.
    pub issuer_key: AffinePoint,
    /// The verifier policy: reference date, minimum age, and accepted
    /// nationality set. Maps directly to the age / nationality public inputs.
    pub policy: Policy,
    /// The holder-presence nonce signature: the device key, the fresh nonce, and
    /// the signature over `SHA-256(domain || nonce)`. The verifier recomputes the
    /// message hash `z` from the nonce and binds the nonce P-256 module against
    /// the full instance (`z` included).
    pub nonce: NonceSignatureStatement,
}

impl PublicStatement {
    /// Build a statement from a trusted issuer key, a policy, and the holder's
    /// nonce signature.
    pub fn new(issuer_key: AffinePoint, policy: Policy, nonce: NonceSignatureStatement) -> Self {
        Self {
            issuer_key,
            policy,
            nonce,
        }
    }
}

/// Bridge trace size: enough rows for one active row per ECDSA instance, at the
/// SIMD minimum of `2^4 = 16` rows.
#[cfg(any(not(feature = "ec-coprocessor"), test))]
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
#[cfg(any(not(feature = "ec-coprocessor"), test))]
fn bridge_rows(instances: &[PublicEcdsaInstance<M31>]) -> Vec<DigestBindRow> {
    instances
        .iter()
        .map(|instance| DigestBindRow {
            sig_id: instance.sig_id,
            z: instance.z.clone(),
        })
        .collect()
}

#[cfg(feature = "ec-coprocessor")]
fn coprocessor_bridge_pcs_config() -> PcsConfig {
    // Match stwo-p256's sanctioned monolithic profile without constructing a
    // P256 AIR module on the feature path. The coprocessor removes both P256
    // AIRs, but the shared proof keeps the same 128-bit FRI/Pow split until an
    // architect-approved profile change says otherwise.
    PcsConfig {
        pow_bits: 10,
        fri_config: FriConfig::new(1, 2, 59, 2),
        lifting_log_size: None,
    }
}

#[cfg(all(test, feature = "ec-coprocessor"))]
#[derive(Clone, Debug, PartialEq, Eq)]
struct CoprocessorForkJoinDigests {
    post_statement: [u8; 32],
    post_seed: [u8; 32],
    post_rejoin: [u8; 32],
}

#[cfg(feature = "ec-coprocessor")]
fn mix_channel_bytes(channel: &mut air_core::Ch, bytes: &[u8]) {
    channel.mix_u64(bytes.len() as u64);
    let mut words = Vec::with_capacity(bytes.len().div_ceil(4));
    for chunk in bytes.chunks(4) {
        let mut word = [0u8; 4];
        word[..chunk.len()].copy_from_slice(chunk);
        words.push(u32::from_le_bytes(word));
    }
    channel.mix_u32s(&words);
}

#[cfg(feature = "ec-coprocessor")]
fn draw_coprocessor_seed(channel: &mut air_core::Ch) -> eu_id_ec_coprocessor::TranscriptSeed {
    let words = channel.draw_u32s();
    assert_eq!(words.len(), 8, "Blake2s channel draws 32 bytes");
    let mut seed = [0u8; 32];
    for (chunk, word) in seed.chunks_exact_mut(4).zip(words) {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    seed
}

#[cfg(all(test, feature = "ec-coprocessor"))]
fn channel_digest(channel: &air_core::Ch) -> [u8; 32] {
    channel.digest().0
}

#[cfg(feature = "ec-coprocessor")]
fn mix_coprocessor_statements(
    channel: &mut air_core::Ch,
    inputs: &[&stwo_p256::types::EcdsaVerifyInput],
) -> Result<(), String> {
    match inputs {
        [credential, nonce] => mix_coprocessor_tagged_statements(
            channel,
            &[
                (b"credential".as_slice(), *credential),
                (b"nonce".as_slice(), *nonce),
            ],
        ),
        _ => {
            let tagged: Vec<_> = inputs
                .iter()
                .map(|input| (b"extra".as_slice(), *input))
                .collect();
            mix_coprocessor_tagged_statements(channel, &tagged)
        }
    }
}

#[cfg(feature = "ec-coprocessor")]
fn mix_coprocessor_tagged_statements(
    channel: &mut air_core::Ch,
    tagged_inputs: &[(&[u8], &stwo_p256::types::EcdsaVerifyInput)],
) -> Result<(), String> {
    mix_channel_bytes(channel, b"eu-id-ec-coproc-v1");
    mix_channel_bytes(channel, b"s4-ecdsa-circuit-shape-v1");
    let shapes = ec_coprocessor::implemented_circuit_transcript_shapes_from_stwo()
        .map_err(|err| format!("{err:?}"))?;
    channel.mix_u64(shapes.len() as u64);
    for shape in shapes {
        mix_channel_bytes(channel, shape.label);
        channel.mix_u64(shape.layers.len() as u64);
        for (out_log_size, next_log_size) in shape.layers {
            channel.mix_u64(out_log_size as u64);
            channel.mix_u64(next_log_size as u64);
        }
    }

    mix_channel_bytes(channel, b"eu-id-ec-coproc-statements-v2");
    channel.mix_u64(tagged_inputs.len() as u64);
    for (tag, input) in tagged_inputs {
        mix_channel_bytes(channel, tag);
        for segment in ec_coprocessor::statement_transcript_segments_from_stwo(input)
            .map_err(|err| format!("{err:?}"))?
        {
            mix_channel_bytes(channel, &segment);
        }
    }
    Ok(())
}

#[cfg(feature = "ec-coprocessor")]
fn mix_coprocessor_tagged_projections(
    channel: &mut air_core::Ch,
    tagged_projections: &[(&[u8], &eu_id_ec_coprocessor::ecdsa::EcdsaPublicProjection)],
) -> Result<(), String> {
    mix_channel_bytes(channel, b"eu-id-ec-coproc-v1");
    mix_channel_bytes(channel, b"s4-ecdsa-circuit-shape-v1");
    let shapes = ec_coprocessor::implemented_circuit_transcript_shapes_from_stwo()
        .map_err(|err| format!("{err:?}"))?;
    channel.mix_u64(shapes.len() as u64);
    for shape in shapes {
        mix_channel_bytes(channel, shape.label);
        channel.mix_u64(shape.layers.len() as u64);
        for (out_log_size, next_log_size) in shape.layers {
            channel.mix_u64(out_log_size as u64);
            channel.mix_u64(next_log_size as u64);
        }
    }

    mix_channel_bytes(channel, b"eu-id-ec-coproc-public-projections-v1");
    channel.mix_u64(tagged_projections.len() as u64);
    for (tag, projection) in tagged_projections {
        mix_channel_bytes(channel, tag);
        for segment in ec_coprocessor::public_projection_transcript_segments(projection) {
            mix_channel_bytes(channel, &segment);
        }
    }
    Ok(())
}

#[cfg(feature = "ec-coprocessor")]
fn coprocessor_bundle_hash(
    bundle: &eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle,
) -> Result<[u8; 32], String> {
    let bytes = bincode::serialize(bundle).map_err(|err| err.to_string())?;
    let digest = Blake2s256::digest(bytes);
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    Ok(out)
}

#[cfg(feature = "ec-coprocessor")]
fn mix_coprocessor_rejoin(
    channel: &mut air_core::Ch,
    bundle: &eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle,
) -> Result<(), String> {
    let hash = coprocessor_bundle_hash(bundle)?;
    mix_channel_bytes(channel, b"eu-id-ec-coproc-rejoin-v1");
    mix_channel_bytes(channel, &hash);
    Ok(())
}

#[cfg(feature = "ec-coprocessor")]
struct CoprocessorBindingProver {
    credential_input: stwo_p256::types::EcdsaVerifyInput,
    nonce_input: stwo_p256::types::EcdsaVerifyInput,
    credential_witness: eu_id_ec_coprocessor::ecdsa::Witness,
    nonce_witness: eu_id_ec_coprocessor::ecdsa::Witness,
    bundles: Option<CoprocessorBundles>,
    #[cfg(test)]
    digests: Option<CoprocessorForkJoinDigests>,
}

#[cfg(feature = "ec-coprocessor")]
impl CoprocessorBindingProver {
    fn new(
        credential_input: stwo_p256::types::EcdsaVerifyInput,
        nonce_input: stwo_p256::types::EcdsaVerifyInput,
    ) -> Result<Self, Error> {
        let credential_witness = ec_coprocessor::generate_witness_from_stwo(&credential_input)
            .map_err(Error::CoprocessorWitness)?;
        let nonce_witness = ec_coprocessor::generate_witness_from_stwo(&nonce_input)
            .map_err(Error::CoprocessorWitness)?;
        Ok(Self {
            credential_input,
            nonce_input,
            credential_witness,
            nonce_witness,
            bundles: None,
            #[cfg(test)]
            digests: None,
        })
    }
}

#[cfg(feature = "ec-coprocessor")]
impl Air for CoprocessorBindingProver {
    fn mix_public(&self, _channel: &mut air_core::Ch) {}

    fn draw_relations(&mut self, _channel: &mut air_core::Ch) {}

    fn layout(&self) -> air_core::TreeLayout {
        air_core::TreeLayout {
            preprocessed: Vec::new(),
            trace: Vec::new(),
            interaction: Vec::new(),
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        Vec::new()
    }

    fn preprocessed_column_ids(
        &self,
    ) -> Vec<stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId> {
        Vec::new()
    }

    fn build_components(&mut self, _allocator: &mut TraceLocationAllocator) {}

    fn components(&self) -> Vec<&dyn Component> {
        Vec::new()
    }
}

#[cfg(feature = "ec-coprocessor")]
impl AirProver for CoprocessorBindingProver {
    fn max_log_size(&self) -> u32 {
        0
    }

    fn write_preprocessed(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

    fn write_trace(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

    fn write_interaction(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

    fn prove_post_interaction(&mut self, channel: &mut air_core::Ch) {
        mix_coprocessor_statements(channel, &[&self.credential_input, &self.nonce_input])
            .expect("coprocessor statements mix");
        #[cfg(test)]
        let post_statement = channel_digest(channel);
        let seed = draw_coprocessor_seed(channel);
        #[cfg(test)]
        let post_seed = seed;
        let inputs = [self.credential_input.clone(), self.nonce_input.clone()];
        let witnesses = [self.credential_witness.clone(), self.nonce_witness.clone()];
        let signatures = ec_coprocessor::prove_implemented_circuit_bundle_batch_from_stwo(
            &inputs, &witnesses, seed,
        )
        .expect("coprocessor bundle proves both checked witnesses");
        let bundles = CoprocessorBundles { signatures };
        mix_coprocessor_rejoin(channel, &bundles.signatures).expect("coprocessor rejoin mixes");
        #[cfg(test)]
        let post_rejoin = channel_digest(channel);
        self.bundles = Some(bundles);
        #[cfg(test)]
        {
            self.digests = Some(CoprocessorForkJoinDigests {
                post_statement,
                post_seed,
                post_rejoin,
            });
        }
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        Vec::new()
    }
}

#[cfg(feature = "ec-coprocessor")]
struct CoprocessorBindingVerifier {
    credential_input: stwo_p256::types::EcdsaVerifyInput,
    nonce_input: stwo_p256::types::EcdsaVerifyInput,
    bundles: CoprocessorBundles,
    #[cfg(test)]
    digests: Option<CoprocessorForkJoinDigests>,
}

#[cfg(feature = "ec-coprocessor")]
impl CoprocessorBindingVerifier {
    fn new(
        credential_instances: &[PublicEcdsaInstance<M31>],
        nonce_instances: &[PublicEcdsaInstance<M31>],
        bundles: CoprocessorBundles,
    ) -> Result<Self, Error> {
        if credential_instances.len() != 1 {
            return Err(Error::CoprocessorInstanceCount {
                actual: credential_instances.len(),
            });
        }
        if nonce_instances.len() != 1 {
            return Err(Error::CoprocessorInstanceCount {
                actual: nonce_instances.len(),
            });
        }
        let credential = &credential_instances[0];
        let nonce = &nonce_instances[0];
        Ok(Self {
            credential_input: stwo_p256::types::EcdsaVerifyInput {
                message_hash: stwo_p256::types::U256(credential.z.to_u256().0),
                signature: stwo_p256::types::Signature {
                    r: stwo_p256::types::U256(credential.r.to_u256().0),
                    s: stwo_p256::types::U256(credential.s.to_u256().0),
                },
                public_key: AffinePoint {
                    x: stwo_p256::types::U256(credential.pub_x.to_u256().0),
                    y: stwo_p256::types::U256(credential.pub_y.to_u256().0),
                },
            },
            nonce_input: stwo_p256::types::EcdsaVerifyInput {
                message_hash: stwo_p256::types::U256(nonce.z.to_u256().0),
                signature: stwo_p256::types::Signature {
                    r: stwo_p256::types::U256(nonce.r.to_u256().0),
                    s: stwo_p256::types::U256(nonce.s.to_u256().0),
                },
                public_key: AffinePoint {
                    x: stwo_p256::types::U256(nonce.pub_x.to_u256().0),
                    y: stwo_p256::types::U256(nonce.pub_y.to_u256().0),
                },
            },
            bundles,
            #[cfg(test)]
            digests: None,
        })
    }
}

#[cfg(feature = "ec-coprocessor")]
impl Air for CoprocessorBindingVerifier {
    fn mix_public(&self, _channel: &mut air_core::Ch) {}

    fn draw_relations(&mut self, _channel: &mut air_core::Ch) {}

    fn layout(&self) -> air_core::TreeLayout {
        air_core::TreeLayout {
            preprocessed: Vec::new(),
            trace: Vec::new(),
            interaction: Vec::new(),
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        Vec::new()
    }

    fn preprocessed_column_ids(
        &self,
    ) -> Vec<stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId> {
        Vec::new()
    }

    fn build_components(&mut self, _allocator: &mut TraceLocationAllocator) {}

    fn components(&self) -> Vec<&dyn Component> {
        Vec::new()
    }

    fn verify_post_interaction(
        &mut self,
        channel: &mut air_core::Ch,
    ) -> Result<(), VerificationError> {
        mix_coprocessor_statements(channel, &[&self.credential_input, &self.nonce_input])
            .map_err(VerificationError::InvalidStructure)?;
        #[cfg(test)]
        let post_statement = channel_digest(channel);
        let seed = draw_coprocessor_seed(channel);
        #[cfg(test)]
        let post_seed = seed;
        let inputs = [self.credential_input.clone(), self.nonce_input.clone()];
        ec_coprocessor::verify_implemented_circuit_bundle_batch_from_stwo(
            &inputs,
            &self.bundles.signatures,
            seed,
        )
        .map_err(|err| VerificationError::InvalidStructure(format!("{err:?}")))?;
        mix_coprocessor_rejoin(channel, &self.bundles.signatures)
            .map_err(VerificationError::InvalidStructure)?;
        #[cfg(test)]
        let post_rejoin = channel_digest(channel);
        #[cfg(test)]
        {
            self.digests = Some(CoprocessorForkJoinDigests {
                post_statement,
                post_seed,
                post_rejoin,
            });
        }
        Ok(())
    }
}

/// Prove the identity statement as **one** STARK proof over six modules.
///
/// Drives the credential P256 ECDSA module, the nonce P256 ECDSA module, the
/// SHA-256 module, the digest-bind bridge, and the age and nationality predicate
/// modules through a single [`air_core::prove`]
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
    nonce_p256_draft: &P256ProofDraft,
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
        nonce_p256_draft,
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
    /// Module label, in commit order (`p256`, `nonce_p256`, `sha`, `bridge`,
    /// `age`, `nat`).
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
    #[cfg(not(feature = "ec-coprocessor"))]
    p256: P256Prover<'a>,
    #[cfg(not(feature = "ec-coprocessor"))]
    nonce_p256: P256Prover<'a>,
    sha: Sha256Prover<'a>,
    #[cfg(not(feature = "ec-coprocessor"))]
    bridge: DigestBindProver,
    #[cfg(feature = "ec-coprocessor")]
    public_digest_bind: PublicDigestBind,
    #[cfg(feature = "ec-coprocessor")]
    coprocessor: CoprocessorBindingProver,
    #[cfg(feature = "ec-coprocessor")]
    credential_instances: Vec<PublicEcdsaInstance<M31>>,
    #[cfg(feature = "ec-coprocessor")]
    nonce_instances: Vec<PublicEcdsaInstance<M31>>,
    age: RangeCheckProver,
    nat: NatProver,
    sha_log_n_rows: u32,
    sha_group_width: u32,
    #[cfg(not(feature = "ec-coprocessor"))]
    bridge_log: u32,
    age_public: &'a AgePublicInput,
    nat_public: &'a NatPublicInput,
}

#[allow(clippy::too_many_arguments)]
fn prepare_proof_modules<'a>(
    p256_draft: &'a P256ProofDraft,
    nonce_p256_draft: &'a P256ProofDraft,
    sha_witness: &'a Sha256Witness,
    sha_log_n_rows: u32,
    sha_group_width: u32,
    age_public: &'a AgePublicInput,
    age_dob: &DateOfBirth,
    nat_public: &'a NatPublicInput,
    nat_private: &NatPrivateInput,
) -> Result<PreparedProofModules<'a>, Error> {
    #[cfg(not(feature = "ec-coprocessor"))]
    let scalar_z_handle = SharedScalarZRelation::new();
    let digest_handle = SharedDigestRelation::new();
    let field_handle = SharedFieldRelation::new();

    let field_exposure = credential_exposure();

    #[cfg(not(feature = "ec-coprocessor"))]
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

    #[cfg(feature = "ec-coprocessor")]
    let sha_prepared = Sha256ColumnTask::new(
        sha_witness,
        sha_log_n_rows,
        sha_group_width,
        field_exposure.clone(),
    )
    .run();

    #[cfg(not(feature = "ec-coprocessor"))]
    let p256 = P256Prover::from_prepared(p256_draft, p256_prepared.map_err(Error::P256Prepare)?)
        .with_z_binding(scalar_z_handle.clone());
    // The nonce (holder-presence) P256 module: no z-binding — its `z` is a public
    // value the verifier recomputes from the nonce. It still needs a
    // preprocessed namespace because hinted-mul schedule columns are
    // witness-dependent and may differ from the credential signature.
    #[cfg(not(feature = "ec-coprocessor"))]
    let nonce_p256 = P256Prover::new(nonce_p256_draft)
        .map_err(Error::P256Prepare)?
        .with_preprocessed_namespace(NONCE_P256_PREPROCESSED_NAMESPACE);
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

    #[cfg(not(feature = "ec-coprocessor"))]
    let (bridge, bridge_log) = {
        let instances = p256.proof_claim().public_inputs.instances.clone();
        let rows = bridge_rows(&instances);
        let bridge_log = bridge_log_size(rows.len());
        let bridge = DigestBindProver::new(rows, bridge_log, scalar_z_handle, digest_handle);
        (bridge, bridge_log)
    };

    #[cfg(feature = "ec-coprocessor")]
    let (credential_instances, nonce_instances, public_digest_bind, coprocessor) = {
        let credential_instances = p256_draft.claim.public_inputs.instances.clone();
        let nonce_instances = nonce_p256_draft.claim.public_inputs.instances.clone();
        if credential_instances.len() != 1 || p256_draft.inputs.len() != 1 {
            return Err(Error::CoprocessorInstanceCount {
                actual: credential_instances.len(),
            });
        }
        if nonce_instances.len() != 1 || nonce_p256_draft.inputs.len() != 1 {
            return Err(Error::CoprocessorInstanceCount {
                actual: nonce_instances.len(),
            });
        }
        let public_z = p256_draft.inputs[0].message_hash.0;
        let public_digest_bind = PublicDigestBind::new(public_z, digest_handle);
        let coprocessor = CoprocessorBindingProver::new(
            p256_draft.inputs[0].clone(),
            nonce_p256_draft.inputs[0].clone(),
        )?;
        (
            credential_instances,
            nonce_instances,
            public_digest_bind,
            coprocessor,
        )
    };

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
        #[cfg(not(feature = "ec-coprocessor"))]
        p256,
        #[cfg(not(feature = "ec-coprocessor"))]
        nonce_p256,
        sha,
        #[cfg(not(feature = "ec-coprocessor"))]
        bridge,
        #[cfg(feature = "ec-coprocessor")]
        public_digest_bind,
        #[cfg(feature = "ec-coprocessor")]
        coprocessor,
        #[cfg(feature = "ec-coprocessor")]
        credential_instances,
        #[cfg(feature = "ec-coprocessor")]
        nonce_instances,
        age,
        nat,
        sha_log_n_rows,
        sha_group_width,
        #[cfg(not(feature = "ec-coprocessor"))]
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
        #[cfg(not(feature = "ec-coprocessor"))]
        ref mut p256,
        #[cfg(not(feature = "ec-coprocessor"))]
        ref mut nonce_p256,
        ref mut sha,
        #[cfg(not(feature = "ec-coprocessor"))]
        ref mut bridge,
        #[cfg(feature = "ec-coprocessor")]
        ref mut public_digest_bind,
        #[cfg(feature = "ec-coprocessor")]
        ref mut coprocessor,
        #[cfg(feature = "ec-coprocessor")]
        ref credential_instances,
        #[cfg(feature = "ec-coprocessor")]
        ref nonce_instances,
        ref mut age,
        ref mut nat,
        sha_log_n_rows,
        sha_group_width,
        #[cfg(not(feature = "ec-coprocessor"))]
        bridge_log,
        age_public,
        nat_public,
    } = prepared;

    // Capture each module's committed-column counts before the modules are
    // borrowed into the prove slice. `layout()` is available right after
    // construction (the verifier reads it pre-build too), and these are the same
    // per-tree sizes committed below — the byte-breakdown attributes the
    // width-linear streams by them.
    #[cfg(not(feature = "ec-coprocessor"))]
    let column_breakdown = vec![
        ModuleColumns::of("p256", &p256.layout()),
        ModuleColumns::of("nonce_p256", &nonce_p256.layout()),
        ModuleColumns::of("sha", &sha.layout()),
        ModuleColumns::of("bridge", &bridge.layout()),
        ModuleColumns::of("age", &age.layout()),
        ModuleColumns::of("nat", &nat.layout()),
    ];
    #[cfg(feature = "ec-coprocessor")]
    let column_breakdown = vec![
        ModuleColumns::of("sha", &sha.layout()),
        ModuleColumns::of("public_digest_bind", &public_digest_bind.layout()),
        ModuleColumns::of("age", &age.layout()),
        ModuleColumns::of("nat", &nat.layout()),
        ModuleColumns::of("coprocessor", &coprocessor.layout()),
    ];

    // Module order is load-bearing: it fixes the transcript, the tree-column /
    // preprocessed-id concatenation, and the order the shared relations are
    // drawn. The credential P256 draws ScalarZ, SHA draws the digest + the
    // credential-field relation, the bridge reads ScalarZ + the digest, and age +
    // nat read the field relation — so every consumer follows SHA (and the bridge
    // follows its two producers). The nonce P256 module sits right after the
    // credential P256 module and draws none of the shared relations (no
    // z-binding); age and nat append after the binding cluster.
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
        #[cfg(not(feature = "ec-coprocessor"))]
        let mut modules: [&mut dyn AirProver; 6] = [p256, nonce_p256, sha, bridge, age, nat];
        #[cfg(feature = "ec-coprocessor")]
        let mut modules: [&mut dyn AirProver; 5] = [sha, public_digest_bind, age, nat, coprocessor];
        air_core::prove(&mut modules, config).map_err(|e| Error::Prove(format!("{e:?}")))?
    };
    #[cfg(feature = "ec-coprocessor")]
    let coprocessor_bundles = coprocessor
        .bundles
        .take()
        .ok_or(Error::CoprocessorMissing)?;
    let proof = Proof {
        stark_proof,
        #[cfg(feature = "ec-coprocessor")]
        coprocessor_bundles: Some(coprocessor_bundles),
        #[cfg(feature = "ec-coprocessor")]
        credential_instances: credential_instances.clone(),
        #[cfg(feature = "ec-coprocessor")]
        nonce_instances: nonce_instances.clone(),
        #[cfg(not(feature = "ec-coprocessor"))]
        p256_claim: p256.proof_claim().clone(),
        #[cfg(not(feature = "ec-coprocessor"))]
        p256_interaction_claim: p256.interaction_claim().clone(),
        #[cfg(not(feature = "ec-coprocessor"))]
        nonce_p256_claim: nonce_p256.proof_claim().clone(),
        #[cfg(not(feature = "ec-coprocessor"))]
        nonce_p256_interaction_claim: nonce_p256.interaction_claim().clone(),
        sha_log_n_rows,
        sha_group_width,
        sha_interaction_claim: sha.interaction_claim().clone(),
        #[cfg(not(feature = "ec-coprocessor"))]
        bridge_log_size: bridge_log,
        #[cfg(not(feature = "ec-coprocessor"))]
        bridge_interaction_claim: bridge.interaction_claim().clone(),
        #[cfg(feature = "ec-coprocessor")]
        public_digest_bind_interaction_claim: public_digest_bind.interaction_claim().clone(),
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
    nonce_p256_draft: &P256ProofDraft,
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
        nonce_p256_draft,
        sha_witness,
        sha_log_n_rows,
        sha_group_width,
        age_public,
        age_dob,
        nat_public,
        nat_private,
    )?;
    #[cfg(not(feature = "ec-coprocessor"))]
    let config = prepared.p256.pcs_config();
    #[cfg(feature = "ec-coprocessor")]
    let config = coprocessor_bridge_pcs_config();
    prove_prepared_with_config(prepared, config)
}

/// FRI-sweep harness only (WO-3.3). Production config changes remain sanctioned-change-only (HANDOVER rule).
#[cfg(feature = "fri-sweep")]
#[allow(clippy::too_many_arguments)]
pub fn prove_with_column_breakdown_and_config(
    p256_draft: &P256ProofDraft,
    nonce_p256_draft: &P256ProofDraft,
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
        nonce_p256_draft,
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
    expected_nonce_instances: &[PublicEcdsaInstance<M31>],
    config: PcsConfig,
) -> Result<(), Error> {
    if !instances_match_ignoring_z(proof.p256_instances(), expected_instances) {
        return Err(Error::P256InstanceMismatch);
    }
    if proof.nonce_p256_instances() != expected_nonce_instances {
        return Err(Error::P256InstanceMismatch);
    }
    verify_stark_with_config(proof, Some(config), None)
}

/// Prove an identity statement from a credential, an issuer signing key, and a
/// policy — the relying-party-facing entry point.
///
/// Signs `credential` with `issuer` (real ES256, so `z = SHA-256(C)`), composes
/// the pipeline witness, prechecks + drafts the holder `nonce` signature, and
/// drives all six modules through [`prove`]. The
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
    nonce: &NonceSignatureStatement,
) -> Result<Proof, Error> {
    let signed = generator::sign_credential(credential, issuer);
    let witness = PipelineWitness::build(signed, policy.clone());
    let draft = witness.p256_draft.as_ref().ok_or(Error::SignatureInvalid)?;

    // The holder-presence nonce signature: prechecked natively (so a bad device
    // signature is rejected here, not deep in trace generation) then drafted as a
    // second P256 module.
    let nonce_input = nonce.ecdsa_input();
    if !ecdsa_verify(&nonce_input) {
        return Err(Error::SignatureInvalid);
    }
    let nonce_draft = P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![nonce_input])
        .map_err(Error::P256Prepare)?;

    prove(
        draft,
        &nonce_draft,
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

/// Verify a [`Proof`], binding the credential P256 module to the caller's
/// expected ECDSA statement (issuer key + signature, **not** `z`) and the nonce
/// P256 module to `expected_nonce_instances` (full equality, `z` included).
///
/// This is the lower-level verify against explicit ECDSA instance lists.
/// Relying parties should prefer [`verify_identity`], which checks the small
/// public statement `{ Q, policy, nonce }` instead.
pub fn verify(
    proof: &Proof,
    expected_instances: &[PublicEcdsaInstance<M31>],
    expected_nonce_instances: &[PublicEcdsaInstance<M31>],
) -> Result<(), Error> {
    // Caller-argument binding for the credential P256 statement, minus `z`
    // (internally bound to the SHA digest).
    if !instances_match_ignoring_z(proof.p256_instances(), expected_instances) {
        return Err(Error::P256InstanceMismatch);
    }
    // The nonce P256 statement is bound in FULL — `z` included — because the
    // holder's message hash is a public value the verifier recomputes from the
    // nonce, not an internally proven digest.
    if proof.nonce_p256_instances() != expected_nonce_instances {
        return Err(Error::P256InstanceMismatch);
    }
    verify_stark(proof)
}

/// Verify a [`Proof`] against a relying party's [`PublicStatement`] — the
/// credential-API counterpart of [`prove_identity`].
///
/// Caller-argument binding for the full statement: the issuer key `Q` against the
/// ECDSA instance's public-key limbs, the reference date + threshold against the
/// age public input, the accepted set against the nationality public input, and
/// the holder nonce signature against the nonce P256 module's instance (full
/// equality, including the `z` the verifier recomputes from the nonce). The
/// credential `z`, the date of birth, and the nationality are not supplied — they
/// are proven equal to the credential's. Then checks the shared STARK (the global
/// LogUp balance). Returns `Ok(())` iff every check passes.
///
/// The tree-0 (preprocessed) root is NOT pinned here — the F-ROOT legacy
/// behavior. A single tier-1 profile constant is impossible today: the
/// tree-0 shape follows the caller's policy and predicate mode (the SDK
/// legitimately verifies age-only / nat-only / varying-policy proofs, each
/// with its own root), and the verifier cannot rebuild the prover modules
/// from the statement alone. Callers that know their full profile pin via
/// [`verify_identity_with_preprocessed_root`] with a root from
/// [`identity_expected_preprocessed_root`]; tier-1 default pinning lands
/// once the deployment's message-size / policy envelope is normalized
/// (tasks/froot-pinning-design.md, Tier 1).
pub fn verify_identity(proof: &Proof, statement: &PublicStatement) -> Result<(), Error> {
    verify_identity_impl(proof, statement, None)
}

/// [`verify_identity`], with the tree-0 (preprocessed) commitment root pinned —
/// the F-ROOT fix. The caller supplies the expected root, computed once via
/// [`identity_expected_preprocessed_root`] (or a per-profile constant generated
/// the same way) — never taken from the proof. A proof carrying a forged
/// preprocessed tree (range tables, schedules, constants) is rejected with
/// [`Error::PreprocessedRootMismatch`] before the STARK check.
///
/// # Soundness
///
/// The Blake2s root pin is the tree-0 soundness anchor: it binds the contents,
/// order, and sizes of every preprocessed column cryptographically. The
/// prover-side 64-bit `DefaultHasher` fingerprint guard is NOT a soundness pin;
/// do not downgrade this check to it.
pub fn verify_identity_with_preprocessed_root(
    proof: &Proof,
    statement: &PublicStatement,
    expected_preprocessed_root: air_core::CommitmentRoot,
) -> Result<(), Error> {
    verify_identity_impl(proof, statement, Some(expected_preprocessed_root))
}

fn verify_identity_impl(
    proof: &Proof,
    statement: &PublicStatement,
    expected_preprocessed_root: Option<air_core::CommitmentRoot>,
) -> Result<(), Error> {
    // Issuer key: every ECDSA instance's public-key limbs must equal `Q`. The
    // MVP proves a single signature, so there is exactly one instance; an empty
    // instance list never satisfies a concrete issuer.
    let expected_pub_x = P256M31BigInt::from_u256(&statement.issuer_key.x);
    let expected_pub_y = P256M31BigInt::from_u256(&statement.issuer_key.y);
    let instances = proof.p256_instances();
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

    // Holder nonce signature: the nonce P256 module must prove exactly the
    // instance the verifier reconstructs from the public nonce — including `z`,
    // recomputed host-side as `SHA-256(domain || nonce)`. There is exactly one
    // instance; any other length or value is a mismatch.
    let expected_nonce = [PublicEcdsaInstance::from_input(
        0,
        &statement.nonce.ecdsa_input(),
    )];
    if proof.nonce_p256_instances() != expected_nonce {
        return Err(Error::P256InstanceMismatch);
    }
    verify_stark_with_config(proof, None, expected_preprocessed_root)
}

/// Compute the expected tree-0 (preprocessed) commitment root for the identity
/// pipeline, by constructing the same prover-side modules [`prove_identity`]
/// uses and running exactly the prover's tree-0 commit path
/// ([`air_core::compute_preprocessed_root`]). Pass the result to
/// [`verify_identity_with_preprocessed_root`]; roots are cached per shape, so
/// repeated verifies in one process pay the rebuild once.
///
/// Under the default `ec-coprocessor` feature every preprocessed column is a
/// deterministic function of the pipeline shape (SHA log-rows, policy tables),
/// so any sample credential of the deployed shape yields the profile's root —
/// suitable for generating a pinned per-profile constant. In the legacy
/// (non-coprocessor) build the P256 hinted-mul schedule preprocessed columns
/// depend on the signature, so the computed root pins that specific witness's
/// schedule, not a deployment-wide constant.
///
/// # Soundness
///
/// This root — not the prover-side 64-bit `DefaultHasher` column fingerprint —
/// is the tree-0 soundness pin. Do not downgrade the pin to the fingerprint.
pub fn identity_expected_preprocessed_root(
    credential: &Credential,
    issuer: &IssuerKey,
    policy: &Policy,
    nonce: &NonceSignatureStatement,
) -> Result<air_core::CommitmentRoot, Error> {
    let signed = generator::sign_credential(credential, issuer);
    let witness = PipelineWitness::build(signed, policy.clone());
    let draft = witness.p256_draft.as_ref().ok_or(Error::SignatureInvalid)?;

    let nonce_input = nonce.ecdsa_input();
    if !ecdsa_verify(&nonce_input) {
        return Err(Error::SignatureInvalid);
    }
    let nonce_draft = P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![nonce_input])
        .map_err(Error::P256Prepare)?;

    let mut prepared = prepare_proof_modules(
        draft,
        &nonce_draft,
        &witness.sha_witness,
        witness.sha_log_n_rows,
        witness.sha_group_width,
        &witness.age_public,
        &witness.age_dob,
        &witness.nat_public,
        &witness.nat_private,
    )?;
    #[cfg(not(feature = "ec-coprocessor"))]
    let config = prepared.p256.pcs_config();
    #[cfg(feature = "ec-coprocessor")]
    let config = coprocessor_bridge_pcs_config();

    // Same module order as `prove` — the tree-0 dedup and commit order match.
    #[cfg(not(feature = "ec-coprocessor"))]
    let mut modules: [&mut dyn AirProver; 6] = [
        &mut prepared.p256,
        &mut prepared.nonce_p256,
        &mut prepared.sha,
        &mut prepared.bridge,
        &mut prepared.age,
        &mut prepared.nat,
    ];
    #[cfg(feature = "ec-coprocessor")]
    let mut modules: [&mut dyn AirProver; 5] = [
        &mut prepared.sha,
        &mut prepared.public_digest_bind,
        &mut prepared.age,
        &mut prepared.nat,
        &mut prepared.coprocessor,
    ];
    Ok(air_core::compute_preprocessed_root(&mut modules, config))
}

/// Rebuild the six verifier modules from the proof and check the shared STARK
/// (the global LogUp balance). The caller does any public-input / statement
/// binding *first*: both [`verify`] and [`verify_identity`] bind, then delegate
/// here.
fn verify_stark(proof: &Proof) -> Result<(), Error> {
    verify_stark_with_config(proof, None, None)
}

fn verify_stark_with_config(
    proof: &Proof,
    expected_config_override: Option<PcsConfig>,
    expected_preprocessed_root: Option<air_core::CommitmentRoot>,
) -> Result<(), Error> {
    #[cfg(not(feature = "ec-coprocessor"))]
    let scalar_z_handle = SharedScalarZRelation::new();
    let digest_handle = SharedDigestRelation::new();
    let field_handle = SharedFieldRelation::new();

    #[cfg(not(feature = "ec-coprocessor"))]
    let mut p256 = P256Verifier::new(
        proof.p256_claim.clone(),
        proof.p256_interaction_claim.clone(),
    )
    .with_z_binding(scalar_z_handle.clone());
    // The nonce (holder-presence) P256 module — no z-binding, mirroring the
    // prover. Feature-on verifies this statement through the coprocessor, so no
    // P256 verifier module is reconstructed.
    #[cfg(not(feature = "ec-coprocessor"))]
    let mut nonce_p256 = P256Verifier::new(
        proof.nonce_p256_claim.clone(),
        proof.nonce_p256_interaction_claim.clone(),
    )
    .with_preprocessed_namespace(NONCE_P256_PREPROCESSED_NAMESPACE);
    let sha = Sha256Verifier::new(
        proof.sha_log_n_rows,
        proof.sha_group_width,
        proof.sha_interaction_claim.clone(),
    );
    let mut sha = sha
        .with_digest_handle(digest_handle.clone())
        .with_field_handle(credential_exposure(), field_handle.clone());
    #[cfg(not(feature = "ec-coprocessor"))]
    let mut bridge = DigestBindVerifier::new(
        proof.bridge_log_size,
        proof.bridge_interaction_claim.clone(),
        scalar_z_handle,
        digest_handle,
    );
    #[cfg(feature = "ec-coprocessor")]
    let mut public_digest_bind = {
        let instances = proof.p256_instances();
        if instances.len() != 1 {
            return Err(Error::CoprocessorInstanceCount {
                actual: instances.len(),
            });
        }
        PublicDigestBind::verifier(
            instances[0].z.to_u256().0,
            digest_handle,
            proof.public_digest_bind_interaction_claim.clone(),
        )
    };
    #[cfg(feature = "ec-coprocessor")]
    let mut coprocessor = CoprocessorBindingVerifier::new(
        proof.p256_instances(),
        proof.nonce_p256_instances(),
        proof
            .coprocessor_bundles
            .clone()
            .ok_or(Error::CoprocessorMissing)?,
    )?;

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
    #[cfg(not(feature = "ec-coprocessor"))]
    let expected_pcs_config = p256.expected_pcs_config();
    #[cfg(feature = "ec-coprocessor")]
    let expected_pcs_config = coprocessor_bridge_pcs_config();
    let expected_config = expected_config_override.unwrap_or(expected_pcs_config);
    if proof.stark_proof.config != expected_config {
        return Err(Error::WeakConfig {
            got: proof.stark_proof.config,
            expected: expected_config,
        });
    }
    // The nonce module must expect the same PCS config as the credential module —
    // otherwise the two P256 modules disagree on the shared proof's security
    // profile.
    #[cfg(not(feature = "ec-coprocessor"))]
    if nonce_p256.expected_pcs_config() != p256.expected_pcs_config() {
        return Err(Error::Verify(
            "nonce P-256 module uses a different verifier PCS config".to_string(),
        ));
    }

    // Same module order as the prover.
    #[cfg(not(feature = "ec-coprocessor"))]
    let mut modules: [&mut dyn Air; 6] = [
        &mut p256,
        &mut nonce_p256,
        &mut sha,
        &mut bridge,
        &mut age,
        &mut nat,
    ];
    #[cfg(feature = "ec-coprocessor")]
    let mut modules: [&mut dyn Air; 5] = [
        &mut sha,
        &mut public_digest_bind,
        &mut age,
        &mut nat,
        &mut coprocessor,
    ];
    air_core::verify_with_expected_preprocessed_root(
        &mut modules,
        &proof.stark_proof,
        expected_preprocessed_root,
    )
    .map_err(|e| match e {
        air_core::VerifyError::PreprocessedRootMismatch { got, expected } => {
            Error::PreprocessedRootMismatch { got, expected }
        }
        air_core::VerifyError::Stark(e) => Error::Verify(format!("{e:?}")),
    })
}

#[cfg(all(test, feature = "ec-coprocessor"))]
mod ec_coprocessor_tests {
    use crate::credential::Credential;
    use crate::ec_coprocessor::{
        generate_witness_from_stwo, implemented_circuit_family_labels_from_stwo,
        implemented_circuit_gate_count_from_stwo, prove_implemented_circuit_bundle_from_stwo,
        prove_implemented_circuit_proofs_from_stwo, verify_implemented_circuit_bundle_from_stwo,
        verify_implemented_circuit_proofs_from_stwo, verify_implemented_circuits_from_stwo,
        verify_witness_from_stwo,
    };
    use crate::generator::{sign_credential, IssuerKey};
    use crate::{
        channel_digest, coprocessor_bundle_hash, draw_coprocessor_seed, mix_coprocessor_rejoin,
        mix_coprocessor_statements, CoprocessorBindingProver, CoprocessorBindingVerifier,
        CoprocessorBundles, CoprocessorForkJoinDigests,
    };
    use crate::{fixtures, prove_identity, verify, verify_identity, Error, Proof, PublicStatement};
    use air_core::{Air, AirProver};
    use stwo::core::channel::Channel;
    use stwo_p256::public_inputs::PublicEcdsaInstance;

    const TEST_SEED: [u8; 32] = [5u8; 32];

    #[test]
    fn feature_gated_s4_witness_adapter_accepts_real_signed_input() {
        let credential = Credential::new(2000, 1, 1, 276);
        let signed = sign_credential(&credential, &IssuerKey::demo());

        let witness = generate_witness_from_stwo(&signed.ecdsa_input).unwrap();

        verify_witness_from_stwo(&signed.ecdsa_input, &witness).unwrap();
        verify_implemented_circuits_from_stwo(&signed.ecdsa_input, &witness).unwrap();
        let proofs = prove_implemented_circuit_proofs_from_stwo(
            &signed.ecdsa_input,
            &witness,
            [5u8; 32],
            TEST_SEED,
        )
        .unwrap();
        let claims =
            verify_implemented_circuit_proofs_from_stwo(&proofs, [5u8; 32], TEST_SEED).unwrap();
        assert_eq!(
            claims.len(),
            implemented_circuit_family_labels_from_stwo().unwrap().len()
        );
        assert!(implemented_circuit_gate_count_from_stwo().unwrap() <= 35_000);
    }

    #[test]
    #[ignore = "full S4-lite bundle proves every implemented ECDSA circuit"]
    fn feature_gated_s4_bundle_adapter_accepts_real_signed_input() {
        let credential = Credential::new(2000, 1, 1, 276);
        let signed = sign_credential(&credential, &IssuerKey::demo());
        let witness = generate_witness_from_stwo(&signed.ecdsa_input).unwrap();

        let bundle =
            prove_implemented_circuit_bundle_from_stwo(&signed.ecdsa_input, &witness, TEST_SEED)
                .unwrap();

        let claims =
            verify_implemented_circuit_bundle_from_stwo(&signed.ecdsa_input, &bundle, TEST_SEED)
                .unwrap();
        assert_eq!(
            claims.len(),
            implemented_circuit_family_labels_from_stwo().unwrap().len()
        );
    }

    #[test]
    #[ignore = "full S4-lite bundle proves every implemented ECDSA circuit"]
    fn feature_gated_s4_bundle_adapter_rejects_wrong_caller_input() {
        let credential = Credential::new(2000, 1, 1, 276);
        let signed = sign_credential(&credential, &IssuerKey::demo());
        let witness = generate_witness_from_stwo(&signed.ecdsa_input).unwrap();
        let bundle =
            prove_implemented_circuit_bundle_from_stwo(&signed.ecdsa_input, &witness, TEST_SEED)
                .unwrap();

        let other_credential = Credential::new(1999, 12, 31, 250);
        let other_signed = sign_credential(&other_credential, &IssuerKey::demo());

        assert!(verify_implemented_circuit_bundle_from_stwo(
            &other_signed.ecdsa_input,
            &bundle,
            TEST_SEED
        )
        .is_err());
    }

    fn transcript_prefix(channel: &mut air_core::Ch) {
        channel.mix_u64(0x4d315f7072656669);
    }

    fn swapped_statement_order_digests(
        credential_input: &stwo_p256::types::EcdsaVerifyInput,
        nonce_input: &stwo_p256::types::EcdsaVerifyInput,
        bundle: &eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle,
    ) -> CoprocessorForkJoinDigests {
        let mut channel = air_core::Ch::default();
        transcript_prefix(&mut channel);
        mix_coprocessor_statements(&mut channel, &[nonce_input, credential_input]).unwrap();
        let post_statement = channel_digest(&channel);
        let post_seed = draw_coprocessor_seed(&mut channel);
        mix_coprocessor_rejoin(&mut channel, bundle).unwrap();
        let post_rejoin = channel_digest(&channel);
        CoprocessorForkJoinDigests {
            post_statement,
            post_seed,
            post_rejoin,
        }
    }

    fn rejoin_digest_for_bundle(
        bundle: &eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle,
    ) -> [u8; 32] {
        let mut channel = air_core::Ch::default();
        transcript_prefix(&mut channel);
        mix_coprocessor_rejoin(&mut channel, bundle).unwrap();
        channel_digest(&channel)
    }

    #[test]
    #[ignore = "full S4-lite bundle proves every implemented ECDSA circuit"]
    fn feature_gated_coprocessor_fork_join_digests_match_prover_and_verifier() {
        let credential = Credential::new(2000, 1, 1, 276);
        let signed = sign_credential(&credential, &IssuerKey::demo());
        let nonce_input = fixtures::demo_nonce_statement().ecdsa_input();
        let mut prover =
            CoprocessorBindingProver::new(signed.ecdsa_input.clone(), nonce_input.clone()).unwrap();
        let mut prover_channel = air_core::Ch::default();
        transcript_prefix(&mut prover_channel);

        prover.prove_post_interaction(&mut prover_channel);
        let bundles = prover.bundles.clone().unwrap();
        let bundle = bundles.signatures.clone();
        let prover_digests = prover.digests.clone().unwrap();

        let instance = PublicEcdsaInstance::from_input(0, &signed.ecdsa_input);
        let nonce_instance = PublicEcdsaInstance::from_input(0, &nonce_input);
        let mut verifier =
            CoprocessorBindingVerifier::new(&[instance], &[nonce_instance], bundles).unwrap();
        let mut verifier_channel = air_core::Ch::default();
        transcript_prefix(&mut verifier_channel);

        verifier
            .verify_post_interaction(&mut verifier_channel)
            .unwrap();
        let verifier_digests = verifier.digests.clone().unwrap();

        assert_eq!(prover_digests, verifier_digests);
        assert_ne!(
            swapped_statement_order_digests(&signed.ecdsa_input, &nonce_input, &bundle),
            prover_digests
        );
    }

    #[test]
    #[ignore = "full S4-lite bundle proves every implemented ECDSA circuit"]
    fn feature_gated_coprocessor_rejoin_changes_next_stark_challenge() {
        let credential = Credential::new(2000, 1, 1, 276);
        let signed = sign_credential(&credential, &IssuerKey::demo());
        let nonce_input = fixtures::demo_nonce_statement().ecdsa_input();
        let mut prover =
            CoprocessorBindingProver::new(signed.ecdsa_input.clone(), nonce_input.clone()).unwrap();
        let mut with_rejoin = air_core::Ch::default();
        transcript_prefix(&mut with_rejoin);
        prover.prove_post_interaction(&mut with_rejoin);
        let with_rejoin_next = draw_coprocessor_seed(&mut with_rejoin);

        let mut without_rejoin = air_core::Ch::default();
        transcript_prefix(&mut without_rejoin);
        mix_coprocessor_statements(&mut without_rejoin, &[&signed.ecdsa_input, &nonce_input])
            .unwrap();
        let _seed = draw_coprocessor_seed(&mut without_rejoin);
        let without_rejoin_next = draw_coprocessor_seed(&mut without_rejoin);

        assert_ne!(with_rejoin_next, without_rejoin_next);
    }

    #[test]
    #[ignore = "full S4-lite bundle proves every implemented ECDSA circuit"]
    fn feature_gated_coprocessor_rejoin_digest_changes_on_bundle_byte_tamper() {
        let credential = Credential::new(2000, 1, 1, 276);
        let signed = sign_credential(&credential, &IssuerKey::demo());
        let nonce_input = fixtures::demo_nonce_statement().ecdsa_input();
        let mut prover =
            CoprocessorBindingProver::new(signed.ecdsa_input.clone(), nonce_input).unwrap();
        let mut channel = air_core::Ch::default();
        transcript_prefix(&mut channel);
        prover.prove_post_interaction(&mut channel);
        let bundle = prover.bundles.clone().unwrap().signatures;

        let mut bundle_bytes = bincode::serialize(&bundle).unwrap();
        let mut tampered_bundle = None;
        for index in (0..bundle_bytes.len()).rev() {
            bundle_bytes[index] ^= 1;
            if let Ok(bundle) = bincode::deserialize(&bundle_bytes) {
                tampered_bundle = Some(bundle);
                break;
            }
            bundle_bytes[index] ^= 1;
        }
        let tampered_bundle: eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle =
            tampered_bundle.expect("one serialized bundle byte can be tampered");

        assert_ne!(
            rejoin_digest_for_bundle(&bundle),
            rejoin_digest_for_bundle(&tampered_bundle)
        );
    }

    #[test]
    fn feature_gated_prove_identity_carries_serialized_coprocessor_bundle() {
        let fixture = fixtures::valid_over_18();
        let issuer = IssuerKey::demo();
        let nonce = fixtures::demo_nonce_statement();

        let proof =
            prove_identity(&fixture.signed.credential, &issuer, &fixture.policy, &nonce).unwrap();
        assert!(proof.coprocessor_bundle().is_some());
        assert!(proof.nonce_coprocessor_bundle().is_some());

        let bytes = bincode::serialize(&proof).unwrap();
        let mut restored: Proof = bincode::deserialize(&bytes).unwrap();
        assert!(restored.coprocessor_bundle().is_some());
        assert!(restored.nonce_coprocessor_bundle().is_some());

        let statement = PublicStatement::new(issuer.public_key(), fixture.policy.clone(), nonce);
        verify_identity(&restored, &statement).unwrap();

        let original_bundle = restored.coprocessor_bundle().unwrap().clone();
        let original_hash = coprocessor_bundle_hash(&original_bundle).unwrap();
        let mut bundle_bytes = bincode::serialize(&original_bundle).unwrap();
        let mut tampered_bundle = None;
        for index in (0..bundle_bytes.len()).rev() {
            bundle_bytes[index] ^= 1;
            if let Ok(bundle) = bincode::deserialize(&bundle_bytes) {
                tampered_bundle = Some(bundle);
                break;
            }
            bundle_bytes[index] ^= 1;
        }
        let tampered_bundle: eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle =
            tampered_bundle.expect("one serialized bundle byte can be tampered");
        assert_ne!(
            coprocessor_bundle_hash(&tampered_bundle).unwrap(),
            original_hash
        );
        restored.coprocessor_bundles = Some(CoprocessorBundles {
            signatures: tampered_bundle,
        });
        assert!(matches!(
            verify_identity(&restored, &statement),
            Err(Error::Verify(_))
        ));
    }

    #[test]
    fn feature_gated_verify_rejects_missing_coprocessor_bundle() {
        let fixture = fixtures::valid_over_18();
        let issuer = IssuerKey::demo();
        let nonce = fixtures::demo_nonce_statement();
        let mut proof =
            prove_identity(&fixture.signed.credential, &issuer, &fixture.policy, &nonce).unwrap();
        let expected = proof.p256_instances().to_vec();
        let expected_nonce = [PublicEcdsaInstance::from_input(0, &nonce.ecdsa_input())];

        proof.coprocessor_bundles = None;

        assert!(matches!(
            verify(&proof, &expected, &expected_nonce),
            Err(Error::CoprocessorMissing)
        ));
    }

    #[test]
    fn feature_gated_verify_rejects_cross_signature_swap_before_stark() {
        let fixture = fixtures::valid_over_18();
        let issuer = IssuerKey::demo();
        let nonce = fixtures::demo_nonce_statement();
        let mut proof =
            prove_identity(&fixture.signed.credential, &issuer, &fixture.policy, &nonce).unwrap();
        let statement = PublicStatement::new(issuer.public_key(), fixture.policy.clone(), nonce);

        std::mem::swap(&mut proof.credential_instances, &mut proof.nonce_instances);

        assert!(matches!(
            verify_identity(&proof, &statement),
            Err(Error::IssuerKeyMismatch) | Err(Error::P256InstanceMismatch)
        ));
    }
}
