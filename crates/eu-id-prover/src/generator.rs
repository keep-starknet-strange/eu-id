//! Native (out-of-circuit) credential generator and the composed
//! pipeline-witness it produces.
//!
//! This is the ground-truth oracle for the whole integration effort. Given a
//! credential, an issuer signing key, and a verifier policy it:
//!
//! 1. encodes the credential to its frozen bytes `C` ([`crate::credential`]),
//! 2. signs it with real ES256 (`sha2` + the `p256` crate) — emitting
//!    `z = SHA-256(C)`, an ECDSA signature `(r, s)`, and the issuer key `Q`,
//! 3. composes the per-module witnesses — the SHA-256 witness over `C`, the
//!    P256 proof draft over `(z, r, s, Q)`, and the age / nationality predicate
//!    inputs — into one [`PipelineWitness`], and
//! 4. cross-checks the result against independent reference oracles
//!    ([`PipelineWitness::check_consistency`]).
//!
//! Built before any binding so each later binding task can diff its trace
//! against a trusted witness rather than a guess.

// The signing oracle and pipeline witness are P-256 constructs; only `Policy`
// and `SHA_GROUP_WIDTH` are scheme-neutral (the mdoc path consumes them), so
// everything classical lives behind the `p256` feature.
#[cfg(feature = "p256")]
use ecdsa::signature::{Signer, Verifier};
#[cfg(feature = "p256")]
use p256::ecdsa::{Signature as P256Signature, SigningKey, VerifyingKey};
use serde::{Deserialize, Serialize};
#[cfg(feature = "p256")]
use sha2::{Digest as _, Sha256};

use predicates::{Date, NatPublicInput, PublicInput as AgePublicInput};
#[cfg(feature = "p256")]
use predicates::{DateOfBirth, NatPrivateInput};

#[cfg(feature = "p256")]
use stwo_p256::ecdsa::ecdsa_verify;
#[cfg(feature = "p256")]
use stwo_p256::proof::P256ProofDraft;
#[cfg(feature = "p256")]
use stwo_p256::types::{AffinePoint, EcdsaVerifyInput, Signature, U256};

#[cfg(feature = "p256")]
use stwo_sha256::trace::min_log_size;
#[cfg(feature = "p256")]
use stwo_sha256::types::Sha256Witness;
#[cfg(feature = "p256")]
use stwo_sha256::witness::compute_sha256_witness;

#[cfg(feature = "p256")]
use crate::credential::Credential;

/// SHA-256 round-group width fed to the SHA module. `MAX_ROUND_GROUP_BITS = 6`
/// is the minimum of the legal range `[6, MAX_GROUP_WIDTH]` and the smallest
/// Maj/Ch table (`2^18` rows). Benchmarking showed `6` roughly halves the
/// combined prove time and cuts peak memory ~3.5× versus the earlier `7`
/// (`2^21` rows) — with SHA the dominant component at `7` but P256 the dominant
/// component at `6` — and the full soundness suite passes either way, so the
/// combined proof uses the cheaper `6`.
pub const SHA_GROUP_WIDTH: u32 = 6;

/// Deterministic demo issuer seed. A fixed seed keeps `Q` (and therefore every
/// fixture's public statement) reproducible across runs. Not a real key —
/// this is a POC oracle.
#[cfg(feature = "p256")]
pub const DEMO_ISSUER_SEED: [u8; 32] = [7u8; 32];

/// An issuer's ECDSA-P256 signing key. Wraps the `p256` crate so the rest of
/// the pipeline never touches it directly.
#[cfg(feature = "p256")]
pub struct IssuerKey {
    signing_key: SigningKey,
}

#[cfg(feature = "p256")]
impl IssuerKey {
    /// Build an issuer key from a 32-byte scalar seed. Panics if the seed is not
    /// a valid P-256 scalar (zero or ≥ n) — callers use fixed, known-good seeds.
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        let signing_key = SigningKey::from_bytes(seed.into()).expect("valid P-256 signing key");
        Self { signing_key }
    }

    /// The deterministic demo issuer ([`DEMO_ISSUER_SEED`]).
    pub fn demo() -> Self {
        Self::from_seed(&DEMO_ISSUER_SEED)
    }

    /// The issuer public key `Q` as a P-256 affine point (the verifier's anchor).
    pub fn public_key(&self) -> AffinePoint {
        let encoded = self.signing_key.verifying_key().to_encoded_point(false);
        let x: [u8; 32] = encoded.x().expect("x coordinate")[..]
            .try_into()
            .expect("x is 32 bytes");
        let y: [u8; 32] = encoded.y().expect("y coordinate")[..]
            .try_into()
            .expect("y is 32 bytes");
        AffinePoint {
            x: U256(x),
            y: U256(y),
        }
    }
}

/// A credential together with its issuer signature — everything the issuer
/// emits. `message` is the signed preimage `C`; `digest` is `z = SHA-256(C)`;
/// `ecdsa_input` is the `(z, r, s, Q)` tuple the P256 module ingests.
#[derive(Clone, Debug)]
#[cfg(feature = "p256")]
pub struct SignedCredential {
    pub credential: Credential,
    /// The signed preimage `C` (== `credential.encode()`).
    pub message: Vec<u8>,
    /// `z = SHA-256(C)`, 32 big-endian bytes.
    pub digest: [u8; 32],
    /// The ECDSA tuple `(z, r, s, Q)` as the P256 module consumes it.
    pub ecdsa_input: EcdsaVerifyInput,
}

#[cfg(feature = "p256")]
impl SignedCredential {
    /// The issuer public key `Q`.
    pub fn issuer_key(&self) -> &AffinePoint {
        &self.ecdsa_input.public_key
    }

    /// The signature `(r, s)`.
    pub fn signature(&self) -> &Signature {
        &self.ecdsa_input.signature
    }

    /// Corrupt the signature by flipping the low bit of `s`. The signature stays
    /// a well-formed scalar (nonzero, `< n`) but no longer verifies — used to
    /// build the `bad_signature` oracle fixture.
    pub fn corrupt_signature(&mut self) {
        self.ecdsa_input.signature.s.0[31] ^= 1;
    }
}

/// Sign a credential with an issuer key, producing the [`SignedCredential`].
///
/// Real ES256: the `p256` crate hashes `C` with SHA-256 internally and signs the
/// digest, so the resulting `(r, s)` verifies against `z = SHA-256(C)`.
#[cfg(feature = "p256")]
pub fn sign_credential(credential: &Credential, issuer: &IssuerKey) -> SignedCredential {
    let message = credential.encode().to_vec();
    let digest: [u8; 32] = Sha256::digest(&message).into();
    let signature: P256Signature = issuer.signing_key.sign(&message);

    let r_bytes: [u8; 32] = signature.r().to_bytes().into();
    let s_bytes: [u8; 32] = signature.s().to_bytes().into();

    let ecdsa_input = EcdsaVerifyInput {
        message_hash: U256(digest),
        signature: Signature {
            r: U256(r_bytes),
            s: U256(s_bytes),
        },
        public_key: issuer.public_key(),
    };

    SignedCredential {
        credential: *credential,
        message,
        digest,
        ecdsa_input,
    }
}

/// The relying party's public policy — exactly the statement the combined
/// verifier will check against. The date of birth, the nationality, and the
/// digest are *proven*, never supplied.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Policy {
    /// Reference "today" the age check is evaluated against.
    pub current_date: Date,
    /// Minimum age in years (the PRD headline is 18).
    pub min_age_years: u32,
    /// Accepted nationality set (ISO-3166-1 numeric codes). Used by the POC /
    /// profile-v1 numeric nationality path.
    pub accepted_nationalities: Vec<u32>,
    /// Accepted nationality set as ISO 3166-1 alpha-2 ASCII codes. Used by the
    /// profile-v2 text path, where the exposed window carries the two ASCII
    /// bytes directly. Empty for the numeric path.
    pub accepted_nationalities_alpha2: Vec<[u8; 2]>,
}

impl Policy {
    /// The age predicate's public input for this policy.
    pub fn age_public_input(&self) -> AgePublicInput {
        AgePublicInput::new(self.current_date, self.min_age_years)
    }

    /// The nationality predicate's public input for this policy (numeric path).
    pub fn nat_public_input(&self) -> NatPublicInput {
        NatPublicInput::new(self.accepted_nationalities.clone())
    }

    /// The nationality predicate's public input over ISO 3166-1 alpha-2 codes,
    /// each packed as `256*b0 + b1` (profile-v2 text path).
    pub fn nat_alpha2_public_input(&self) -> NatPublicInput {
        NatPublicInput::new_alpha2(
            self.accepted_nationalities_alpha2
                .iter()
                .map(|code| u32::from(u16::from_be_bytes(*code)))
                .collect(),
        )
    }

    /// The cutoff date a date of birth must be on-or-before to satisfy the age
    /// check (`current` shifted back `min_age_years`).
    pub fn age_cutoff(&self) -> Date {
        self.age_public_input().cutoff_date()
    }
}

/// The complete, self-consistent witness for the whole pipeline, assembled from
/// a signed credential + policy. This is the struct every later binding task
/// diffs against.
///
/// The per-module pieces are the SHA-256 witness over `C`, the P256 proof draft
/// over `(z, r, s, Q)`, and the age / nationality predicate inputs. The age DOB
/// and nationality code are held explicitly (rather than always re-derived from
/// the credential) so a deliberately *inconsistent* witness can be built — that
/// is exactly the credential↔predicate mismatch the `tampered_dob_bytes`
/// fixture models and a later binding relation must reject.
#[cfg(feature = "p256")]
pub struct PipelineWitness {
    /// The signed credential (`C`, `z`, `(r, s)`, `Q`).
    pub signed: SignedCredential,
    /// The verifier policy this witness is built against.
    pub policy: Policy,

    /// SHA-256 module witness over `C`.
    pub sha_witness: Sha256Witness,
    /// `log_2` row count to size the SHA trace at (from the block count).
    pub sha_log_n_rows: u32,
    /// SHA round-group width ([`SHA_GROUP_WIDTH`]).
    pub sha_group_width: u32,

    /// P256 module proof draft over `(z, r, s, Q)`. `None` when the signature
    /// does not natively verify (a bad signature has no meaningful draft to
    /// compose — see the `bad_signature` fixture).
    pub p256_draft: Option<P256ProofDraft>,

    /// Age predicate public input (derived from the policy).
    pub age_public: AgePublicInput,
    /// Date of birth the age module reasons about. Equal to the credential's DOB
    /// in an honest witness.
    pub age_dob: DateOfBirth,

    /// Nationality predicate public input (derived from the policy).
    pub nat_public: NatPublicInput,
    /// Private nationality the nat module reasons about. Holds the credential's
    /// code in an honest witness.
    pub nat_private: NatPrivateInput,
}

#[cfg(feature = "p256")]
impl PipelineWitness {
    /// Compose an **honest** pipeline witness: the age DOB and nationality code
    /// are taken from the signed credential, so the result is binding-consistent.
    /// Includes the (heavier) P256 draft.
    pub fn build(signed: SignedCredential, policy: Policy) -> Self {
        let (age_dob, nat_code) = credential_attributes(&signed.credential);
        Self::compose(signed, policy, age_dob, nat_code, true)
    }

    /// As [`build`](Self::build) but skips the P256 draft (`p256_draft = None`).
    /// For fast crypto/binding checks that do not need the EC trace.
    pub fn build_lite(signed: SignedCredential, policy: Policy) -> Self {
        let (age_dob, nat_code) = credential_attributes(&signed.credential);
        Self::compose(signed, policy, age_dob, nat_code, false)
    }

    /// Compose a witness with the predicate attributes injected independently of
    /// the credential bytes. Use to model a credential↔predicate mismatch.
    pub fn build_with_attributes(
        signed: SignedCredential,
        policy: Policy,
        age_dob: DateOfBirth,
        nat_code: u32,
    ) -> Self {
        Self::compose(signed, policy, age_dob, nat_code, true)
    }

    /// As [`build_with_attributes`](Self::build_with_attributes) but skips the
    /// P256 draft.
    pub fn build_with_attributes_lite(
        signed: SignedCredential,
        policy: Policy,
        age_dob: DateOfBirth,
        nat_code: u32,
    ) -> Self {
        Self::compose(signed, policy, age_dob, nat_code, false)
    }

    fn compose(
        signed: SignedCredential,
        policy: Policy,
        age_dob: DateOfBirth,
        nat_code: u32,
        with_draft: bool,
    ) -> Self {
        let sha_witness = compute_sha256_witness(&signed.message);
        let sha_log_n_rows = min_log_size(sha_witness.blocks.len());

        // Only build a draft for a natively-verifying signature: the draft
        // builder is designed for valid signatures, and a bad signature's draft
        // would never prove anyway.
        let p256_draft = if with_draft && ecdsa_verify(&signed.ecdsa_input) {
            P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![signed
                .ecdsa_input
                .clone()])
            .ok()
        } else {
            None
        };

        let age_public = policy.age_public_input();
        let nat_public = policy.nat_public_input();
        let nat_private = NatPrivateInput {
            nationalities: vec![nat_code],
        };

        Self {
            signed,
            policy,
            sha_witness,
            sha_log_n_rows,
            sha_group_width: SHA_GROUP_WIDTH,
            p256_draft,
            age_public,
            age_dob,
            nat_public,
            nat_private,
        }
    }

    /// Cross-check this witness against independent reference oracles — `sha2`
    /// and the `p256` crate (external), plus the in-repo native SHA and ECDSA
    /// references. Returns which invariants hold; an honest witness has
    /// [`ConsistencyReport::all_ok`].
    ///
    /// This validates *self-consistency* (the crypto checks out and the
    /// predicate attributes match the signed bytes), **not** the truth of the
    /// statements (whether the holder is ≥ 18, whether the nationality is
    /// accepted) — those are what the proof enforces.
    pub fn check_consistency(&self) -> ConsistencyReport {
        let credential = &self.signed.credential;
        let message: &[u8] = &self.signed.message;

        // Encoding: the bytes round-trip to the credential.
        let encoding_ok = message == credential.encode().as_slice()
            && Credential::decode(message) == Ok(*credential);

        // Digest: external `sha2`, the in-repo native reference, the SHA witness,
        // and the ECDSA input's `z` all agree with the stored digest.
        let sha2_digest: [u8; 32] = Sha256::digest(message).into();
        let native_digest = stwo_sha256::native::hash(message).0;
        let sha_digest_ok = sha2_digest == self.signed.digest
            && native_digest == self.signed.digest
            && self.sha_witness.digest.0 == self.signed.digest
            && self.signed.ecdsa_input.message_hash.0 == self.signed.digest;

        // ECDSA: the external `p256` verifier (over the message) and the in-repo
        // native verifier (over `z`) both accept.
        let ecdsa_ok = self.verify_with_p256_crate() && ecdsa_verify(&self.signed.ecdsa_input);

        // Binding: the predicate attributes match the credential's bytes.
        let age_dob_matches_credential = self.age_dob.0 == credential_dob(credential);
        let nat_code_matches_credential =
            self.nat_private.nationalities == vec![u32::from(credential.nationality)];

        ConsistencyReport {
            encoding_ok,
            sha_digest_ok,
            ecdsa_ok,
            age_dob_matches_credential,
            nat_code_matches_credential,
        }
    }

    /// Independent verification through the `p256` crate, reconstructed purely
    /// from the stored public values (`Q`, `r`, `s`) — not the signing key.
    fn verify_with_p256_crate(&self) -> bool {
        let q = self.signed.issuer_key();
        let mut sec1 = [0u8; 65];
        sec1[0] = 0x04;
        sec1[1..33].copy_from_slice(&q.x.0);
        sec1[33..65].copy_from_slice(&q.y.0);

        let mut rs = [0u8; 64];
        rs[..32].copy_from_slice(&self.signed.signature().r.0);
        rs[32..].copy_from_slice(&self.signed.signature().s.0);

        match (
            VerifyingKey::from_sec1_bytes(&sec1),
            P256Signature::from_slice(&rs),
        ) {
            (Ok(vk), Ok(sig)) => vk.verify(&self.signed.message, &sig).is_ok(),
            _ => false,
        }
    }
}

/// A breakdown of which self-consistency invariants a [`PipelineWitness`] holds.
/// An honest witness has every field `true` ([`Self::all_ok`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg(feature = "p256")]
pub struct ConsistencyReport {
    /// `C` round-trips through encode/decode to the same credential.
    pub encoding_ok: bool,
    /// `sha2`, the native reference, the SHA witness, and the ECDSA `z` all
    /// equal the stored digest.
    pub sha_digest_ok: bool,
    /// Both the `p256` crate and the native verifier accept `(z, r, s, Q)`.
    pub ecdsa_ok: bool,
    /// The age module's DOB equals the credential's DOB bytes.
    pub age_dob_matches_credential: bool,
    /// The nat module's code equals the credential's nationality bytes.
    pub nat_code_matches_credential: bool,
}

#[cfg(feature = "p256")]
impl ConsistencyReport {
    /// True iff every invariant holds.
    pub fn all_ok(&self) -> bool {
        self.encoding_ok
            && self.sha_digest_ok
            && self.ecdsa_ok
            && self.age_dob_matches_credential
            && self.nat_code_matches_credential
    }

    /// True iff the cryptographic invariants hold (encoding, digest, ECDSA),
    /// regardless of the credential↔predicate bindings.
    pub fn crypto_ok(&self) -> bool {
        self.encoding_ok && self.sha_digest_ok && self.ecdsa_ok
    }

    /// True iff both credential↔predicate bindings hold.
    pub fn bindings_ok(&self) -> bool {
        self.age_dob_matches_credential && self.nat_code_matches_credential
    }
}

/// The credential's DOB as a predicate [`Date`].
#[cfg(feature = "p256")]
pub(crate) fn credential_dob(c: &Credential) -> Date {
    Date {
        year: u32::from(c.birth_year),
        month: u32::from(c.birth_month),
        day: u32::from(c.birth_day),
    }
}

/// The credential's `(DateOfBirth, nationality code)` predicate attributes.
#[cfg(feature = "p256")]
fn credential_attributes(c: &Credential) -> (DateOfBirth, u32) {
    (DateOfBirth(credential_dob(c)), u32::from(c.nationality))
}

#[cfg(all(test, feature = "p256"))]
mod tests {
    use super::*;

    fn demo_policy() -> Policy {
        Policy {
            current_date: Date {
                year: 2026,
                month: 6,
                day: 17,
            },
            min_age_years: 18,
            accepted_nationalities: vec![276, 250, 380, 724],
            accepted_nationalities_alpha2: Vec::new(),
        }
    }

    #[test]
    fn signs_a_credential_that_verifies_natively_and_externally() {
        let cred = Credential::new(2000, 1, 1, 276);
        let signed = sign_credential(&cred, &IssuerKey::demo());

        // Native verifier accepts.
        assert!(ecdsa_verify(&signed.ecdsa_input));
        // z is SHA-256(C).
        assert_eq!(
            signed.digest,
            <[u8; 32]>::from(Sha256::digest(&signed.message))
        );
        assert_eq!(signed.message, cred.encode());
    }

    #[test]
    fn honest_witness_is_fully_consistent_lite() {
        let cred = Credential::new(2000, 1, 1, 276);
        let signed = sign_credential(&cred, &IssuerKey::demo());
        let pw = PipelineWitness::build_lite(signed, demo_policy());

        let report = pw.check_consistency();
        assert!(
            report.all_ok(),
            "honest witness must be consistent: {report:?}"
        );
    }

    #[test]
    fn injected_dob_mismatch_breaks_only_the_binding() {
        let cred = Credential::new(2010, 1, 1, 276); // real DOB
        let signed = sign_credential(&cred, &IssuerKey::demo());
        let lying_dob = DateOfBirth(Date {
            year: 2000,
            month: 1,
            day: 1,
        });
        let pw = PipelineWitness::build_with_attributes_lite(signed, demo_policy(), lying_dob, 276);

        let report = pw.check_consistency();
        assert!(report.crypto_ok(), "crypto still sound: {report:?}");
        assert!(!report.age_dob_matches_credential, "binding must be broken");
        assert!(!report.all_ok());
    }

    #[test]
    fn corrupt_signature_breaks_crypto_consistency() {
        let cred = Credential::new(2000, 1, 1, 276);
        let mut signed = sign_credential(&cred, &IssuerKey::demo());
        signed.corrupt_signature();
        assert!(!ecdsa_verify(&signed.ecdsa_input));

        let pw = PipelineWitness::build_lite(signed, demo_policy());
        let report = pw.check_consistency();
        assert!(!report.ecdsa_ok, "corrupt signature must fail ecdsa check");
        assert!(report.bindings_ok(), "bindings still hold: {report:?}");
    }

    #[test]
    fn build_includes_p256_draft_for_valid_signature() {
        let cred = Credential::new(2000, 1, 1, 276);
        let signed = sign_credential(&cred, &IssuerKey::demo());
        let pw = PipelineWitness::build(signed, demo_policy());
        assert!(pw.p256_draft.is_some(), "valid signature composes a draft");
        assert!(pw.check_consistency().all_ok());
    }
}
