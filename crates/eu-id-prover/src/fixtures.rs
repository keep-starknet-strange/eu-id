//! Deterministic credential fixtures — the oracle's catalogue of cases.
//!
//! Seven fixtures, each isolating exactly one property so a later binding task
//! can pin down which relation a regression broke:
//!
//! | fixture                      | crypto | binding | age ≥ 18 | nat ∈ set | verifies |
//! |------------------------------|:------:|:-------:|:--------:|:---------:|:--------:|
//! | `valid_over_18`              |   ✓    |    ✓    |    ✓     |     ✓     |    ✓     |
//! | `valid_exactly_18`           |   ✓    |    ✓    |    ✓     |     ✓     |    ✓     |
//! | `under_18`                   |   ✓    |    ✓    |    ✗     |     ✓     |    ✗     |
//! | `wrong_nationality`          |   ✓    |    ✓    |    ✓     |     ✗     |    ✗     |
//! | `tampered_dob_bytes`         |   ✓    |    ✗    |    ✓*    |     ✓     |    ✗     |
//! | `tampered_nationality_bytes` |   ✓    |    ✗    |    ✓     |     ✓*    |    ✗     |
//! | `bad_signature`              |   ✗    |    ✓    |    ✓     |     ✓     |    ✗     |
//!
//! The two tampered fixtures (*) are the credential↔predicate attacks. In
//! `tampered_dob_bytes` a real under-18 credential is signed but the age module
//! is fed an over-18 date of birth; in `tampered_nationality_bytes` a credential
//! for one nationality is signed but the nat module is fed a different (still
//! accepted) code. Each time the signature and the predicate sub-statement both
//! "pass" — only the binding is broken, which is exactly what the
//! age↔credential / nationality↔credential relations must catch.
//!
//! Every fixture declares its [`Expectation`]; [`Fixture::actual_expectation`]
//! recomputes it from the witness + reference oracles, and the tests assert the
//! two agree, so the catalogue can never silently drift from reality.

use predicates::{Date, DateOfBirth};

use crate::credential::Credential;
use crate::generator::{
    credential_dob, sign_credential, IssuerKey, PipelineWitness, Policy, SignedCredential,
};

/// What the combined bound proof should conclude about a fixture, broken out by
/// the property each relation is responsible for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Expectation {
    /// The signature, digest, and encoding are sound (the crypto checks out).
    pub crypto_consistent: bool,
    /// The age DOB and nationality match the signed credential bytes.
    pub binding_consistent: bool,
    /// The age the age module reasons about is ≥ the policy threshold.
    pub age_ge_threshold: bool,
    /// The nationality the nat module reasons about is in the accepted set.
    pub nationality_accepted: bool,
}

impl Expectation {
    /// Whether the fully bound proof should verify — every property must hold.
    pub fn should_verify(&self) -> bool {
        self.crypto_consistent
            && self.binding_consistent
            && self.age_ge_threshold
            && self.nationality_accepted
    }
}

/// A named fixture: a signed credential, the policy it is judged against, the
/// predicate attributes the modules use, and the declared [`Expectation`].
pub struct Fixture {
    pub name: &'static str,
    pub description: &'static str,
    pub signed: SignedCredential,
    pub policy: Policy,
    /// Date of birth fed to the age module (differs from the credential only in
    /// `tampered_dob_bytes`).
    pub age_dob: DateOfBirth,
    /// Nationality code fed to the nat module.
    pub nat_code: u32,
    pub expectation: Expectation,
}

impl Fixture {
    /// Compose the full pipeline witness (includes the P256 draft when the
    /// signature verifies).
    pub fn pipeline_witness(&self) -> PipelineWitness {
        PipelineWitness::build_with_attributes(
            self.signed.clone(),
            self.policy.clone(),
            self.age_dob,
            self.nat_code,
        )
    }

    /// Compose the pipeline witness without the (heavier) P256 draft — for fast
    /// crypto / binding checks.
    pub fn pipeline_witness_lite(&self) -> PipelineWitness {
        PipelineWitness::build_with_attributes_lite(
            self.signed.clone(),
            self.policy.clone(),
            self.age_dob,
            self.nat_code,
        )
    }

    /// Recompute the expectation from the witness and the reference oracles. The
    /// tests assert this equals the declared [`Expectation`].
    pub fn actual_expectation(&self) -> Expectation {
        let report = self.pipeline_witness_lite().check_consistency();
        Expectation {
            crypto_consistent: report.crypto_ok(),
            binding_consistent: report.bindings_ok(),
            age_ge_threshold: self.age_dob.0.key() <= self.policy.age_cutoff().key(),
            nationality_accepted: self.policy.accepted_nationalities.contains(&self.nat_code),
        }
    }
}

/// The reference verifier policy the fixtures are built against: reference date
/// 2026-06-17, threshold 18, accepted set {DE, FR, IT, ES}.
pub fn demo_policy() -> Policy {
    Policy {
        current_date: Date {
            year: 2026,
            month: 6,
            day: 17,
        },
        min_age_years: 18,
        accepted_nationalities: vec![276, 250, 380, 724],
    }
}

/// Build an honest fixture: the age DOB and nationality are taken from the
/// credential, and the signature is over the credential's real bytes.
fn honest(
    name: &'static str,
    description: &'static str,
    credential: Credential,
    expectation: Expectation,
) -> Fixture {
    let signed = sign_credential(&credential, &IssuerKey::demo());
    Fixture {
        name,
        description,
        age_dob: DateOfBirth(credential_dob(&credential)),
        nat_code: u32::from(credential.nationality),
        signed,
        policy: demo_policy(),
        expectation,
    }
}

/// Valid, comfortably over 18 (born 2000-01-01, Germany).
pub fn valid_over_18() -> Fixture {
    honest(
        "valid_over_18",
        "Born 2000-01-01 (age 26), DE — every property holds; should verify.",
        Credential::new(2000, 1, 1, 276),
        Expectation {
            crypto_consistent: true,
            binding_consistent: true,
            age_ge_threshold: true,
            nationality_accepted: true,
        },
    )
}

/// Valid, exactly 18 on the reference date (the age boundary; born 2008-06-17,
/// France — cutoff is 2008-06-17, so DOB == cutoff is accepted).
pub fn valid_exactly_18() -> Fixture {
    honest(
        "valid_exactly_18",
        "Born 2008-06-17, FR — turns 18 exactly on the reference date; should verify.",
        Credential::new(2008, 6, 17, 250),
        Expectation {
            crypto_consistent: true,
            binding_consistent: true,
            age_ge_threshold: true,
            nationality_accepted: true,
        },
    )
}

/// Under 18 by one day (born 2008-06-18, Germany) — crypto and binding sound,
/// but the age sub-statement is false.
pub fn under_18() -> Fixture {
    honest(
        "under_18",
        "Born 2008-06-18, DE — one day too young on the reference date; age fails.",
        Credential::new(2008, 6, 18, 276),
        Expectation {
            crypto_consistent: true,
            binding_consistent: true,
            age_ge_threshold: false,
            nationality_accepted: true,
        },
    )
}

/// Nationality outside the accepted set (born 2000-01-01, USA = 840) — crypto,
/// binding, and age sound, but the nationality membership fails.
pub fn wrong_nationality() -> Fixture {
    honest(
        "wrong_nationality",
        "Born 2000-01-01, US (840) — not in the accepted set; nationality fails.",
        Credential::new(2000, 1, 1, 840),
        Expectation {
            crypto_consistent: true,
            binding_consistent: true,
            age_ge_threshold: true,
            nationality_accepted: false,
        },
    )
}

/// Credential↔predicate mismatch: a real under-18 credential (born 2010-01-01)
/// is signed, but the age module is fed an over-18 date of birth (2000-01-01).
/// The signature is valid and the age sub-statement passes against the injected
/// date — only the binding is broken.
pub fn tampered_dob_bytes() -> Fixture {
    let credential = Credential::new(2010, 1, 1, 276);
    let signed = sign_credential(&credential, &IssuerKey::demo());
    let injected_over_18 = DateOfBirth(Date {
        year: 2000,
        month: 1,
        day: 1,
    });
    Fixture {
        name: "tampered_dob_bytes",
        description:
            "Real DOB 2010-01-01 signed, but the age module is fed 2000-01-01; binding fails.",
        signed,
        policy: demo_policy(),
        age_dob: injected_over_18,
        nat_code: 276,
        expectation: Expectation {
            crypto_consistent: true,
            binding_consistent: false,
            age_ge_threshold: true, // true w.r.t. the injected DOB
            nationality_accepted: true,
        },
    }
}

/// Credential↔predicate mismatch on nationality: a credential for Germany
/// (276) is signed, but the nat module is fed France (250) — a *different* code
/// that is also in the accepted set, so the membership sub-statement still
/// passes. Crypto, age, and membership hold; only the nationality binding is
/// broken (the code the nat module proves ≠ the credential's signed nationality
/// bytes). This is the nationality twin of `tampered_dob_bytes`.
pub fn tampered_nationality_bytes() -> Fixture {
    let credential = Credential::new(2000, 1, 1, 276); // real nationality DE
    let signed = sign_credential(&credential, &IssuerKey::demo());
    let injected_other_accepted = 250; // FR — in the accepted set, but not the credential's code
    Fixture {
        name: "tampered_nationality_bytes",
        description:
            "Real nationality DE(276) signed, but the nat module is fed FR(250); binding fails.",
        signed,
        policy: demo_policy(),
        age_dob: DateOfBirth(credential_dob(&credential)),
        nat_code: injected_other_accepted,
        expectation: Expectation {
            crypto_consistent: true,
            binding_consistent: false,
            age_ge_threshold: true,
            nationality_accepted: true, // 250 ∈ accepted set
        },
    }
}

/// Tampered signature (born 2000-01-01, Germany; the low bit of `s` flipped) —
/// binding and statements sound, but the signature no longer verifies.
pub fn bad_signature() -> Fixture {
    let credential = Credential::new(2000, 1, 1, 276);
    let mut signed = sign_credential(&credential, &IssuerKey::demo());
    signed.corrupt_signature();
    Fixture {
        name: "bad_signature",
        description: "Valid statement but the signature's s bit is flipped; ECDSA fails.",
        age_dob: DateOfBirth(credential_dob(&credential)),
        nat_code: u32::from(credential.nationality),
        signed,
        policy: demo_policy(),
        expectation: Expectation {
            crypto_consistent: false,
            binding_consistent: true,
            age_ge_threshold: true,
            nationality_accepted: true,
        },
    }
}

/// All seven fixtures, in catalogue order.
pub fn all() -> Vec<Fixture> {
    vec![
        valid_over_18(),
        valid_exactly_18(),
        under_18(),
        wrong_nationality(),
        tampered_dob_bytes(),
        tampered_nationality_bytes(),
        bad_signature(),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn declared_expectations_match_reality() {
        for f in all() {
            assert_eq!(
                f.expectation,
                f.actual_expectation(),
                "fixture `{}` declares an expectation the oracle disagrees with",
                f.name
            );
        }
    }

    #[test]
    fn only_valid_fixtures_should_verify() {
        let verifying: Vec<&str> = all()
            .iter()
            .filter(|f| f.expectation.should_verify())
            .map(|f| f.name)
            .collect();
        assert_eq!(verifying, vec!["valid_over_18", "valid_exactly_18"]);
    }

    #[test]
    fn each_negative_isolates_one_property() {
        // Exactly one of the four properties is false in each negative fixture.
        for f in all() {
            let e = f.expectation;
            let falses = [
                e.crypto_consistent,
                e.binding_consistent,
                e.age_ge_threshold,
                e.nationality_accepted,
            ]
            .iter()
            .filter(|b| !**b)
            .count();
            let expected_falses = usize::from(!e.should_verify());
            assert_eq!(
                falses, expected_falses,
                "fixture `{}` should break exactly one property",
                f.name
            );
        }
    }
}
