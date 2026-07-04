//! The pure, proving-free translation layer between the SDK's mdoc-shaped
//! UniFFI contract types ([`ZkPublicStatement`], [`ZkWitness`]) and the
//! prover's relying-party types (`PublicStatement`, `Credential`, `Policy`).
//!
//! Everything here is deterministic and side-effect-free: it *constructs* the
//! prover's types but never proves or verifies — swapping the stub prove/verify
//! bodies for real STWO calls is §9.2. This layer is what the soundness of the
//! whole consumer path rests on, because it must produce **byte-identical**
//! policy inputs on the prove (wallet) and verify (verifier) sides:
//! `verify_identity`'s caller-argument binding rejects any `Policy` drift. Both
//! sides call the *same* [`to_policy`] / [`to_public_statement`] over the same
//! request parameters, so that symmetry holds by construction — neither depends
//! on the private held values.
//!
//! ## Intermediate-iteration decisions (ROADMAP_E2E §9 "two contracts")
//! 1. **Issuer key.** The statement's `issuer_key_x/y` are **ignored**; the
//!    proof binds the deterministic [`IssuerKey::demo`] (the POC re-signs the
//!    11-byte credential). Binding the real EU issuer key is mdoc-in-circuit
//!    (§8.1).
//! 2. **Attribute source.** The cleartext `birth_date` / `nationalities` the app
//!    extracted are trusted as-is; the signature / MSO / item bytes in the
//!    witness are unused this iteration.
//! 3. **Predicate-mode neutralization.** `And` proves both predicates for real;
//!    `Age` neutralizes nationality with the **universal accepted set** (every
//!    assigned ISO code — trivially satisfiable *and* reconstructible by a
//!    verifier that never learns the held code); `Nat` neutralizes age with
//!    `min_age = 0` (cutoff = today, so any real DOB clears it); `Or` is
//!    rejected.

use std::collections::HashSet;

use eu_id_prover::{
    all_nationality_codes, AffinePoint, Credential, Date, IssuerKey, Policy, PublicStatement,
};

use crate::{PredicateMode, ZkError, ZkPublicStatement, ZkWitness};

/// Build a [`ZkError::InvalidInput`] with an actionable message.
fn invalid(msg: impl Into<String>) -> ZkError {
    ZkError::InvalidInput(msg.into())
}

/// The fixed POC issuer key the proof binds (decision 1). Deterministic, so the
/// prove and verify sides recover the identical `Q`.
pub(crate) fn issuer_key() -> AffinePoint {
    IssuerKey::demo().public_key()
}

/// Map a [`ZkPublicStatement`] to the prover's [`PublicStatement`]: the demo
/// issuer key, the policy derived from the request parameters, and the fixed demo
/// holder nonce signature. Symmetric — the verifier rebuilds the identical
/// statement from its own request.
///
/// The holder-presence nonce signature the STARK now folds in is a fixed demo
/// device-key signature (decision 4); the mdoc `SessionTranscript` nonce carried
/// in [`ZkPublicStatement`] stays envelope-bound (not STARK-bound). Binding a
/// real device key is the mdoc device-key milestone.
pub(crate) fn to_public_statement(
    statement: &ZkPublicStatement,
) -> Result<PublicStatement, ZkError> {
    Ok(PublicStatement::new(
        issuer_key(),
        to_policy(statement)?,
        eu_id_prover::fixtures::demo_nonce_statement(),
    ))
}

/// Map a [`ZkPublicStatement`] to the prover's [`Policy`] — reference date,
/// minimum age, and accepted-nationality set — applying the predicate-mode
/// neutralization (decision 3).
///
/// This consumes **only** the public request parameters (never the private held
/// values), so the prove and verify sides produce the same `Policy`. That is
/// exactly what lets `verify_identity`'s `AgePolicyMismatch` / `NatPolicyMismatch`
/// gates pass for an honest proof.
pub(crate) fn to_policy(statement: &ZkPublicStatement) -> Result<Policy, ZkError> {
    let mode = statement.predicate_mode;
    if matches!(mode, PredicateMode::Or) {
        return Err(invalid(
            "predicate mode `or` is not supported (only `age`, `nat`, `and`)",
        ));
    }

    let current = epoch_day_to_date(statement.today_epoch_day)?;

    // Age leg: real threshold when active, else neutralized to 0 (cutoff =
    // today ⇒ every real DOB clears it).
    let min_age_years = if mode.uses_age() {
        let threshold = statement
            .age_threshold_years
            .ok_or_else(|| invalid("age predicate active but `age_threshold_years` is absent"))?;
        validate_min_age(current, threshold)?;
        threshold
    } else {
        0
    };

    // Nat leg: real accepted set when active, else neutralized with the
    // universal set (every assigned code is a member — identical on both sides
    // because it does not depend on the private held nationality).
    let accepted_nationalities = if mode.uses_nat() {
        let accepted = statement
            .accepted_numeric_countries
            .clone()
            .ok_or_else(|| {
                invalid("nationality predicate active but `accepted_numeric_countries` is absent")
            })?;
        validate_accepted_set(&accepted)?;
        accepted
    } else {
        all_nationality_codes()
    };

    Ok(Policy {
        current_date: current,
        min_age_years,
        accepted_nationalities,
    })
}

/// Map a [`ZkWitness`] to the prover's private [`Credential`] (prove side only).
/// The `policy` (built from the statement) supplies the accepted set the held
/// code is selected against; `mode` says which predicates are actually active.
///
/// **Selective disclosure.** A neutralized predicate (decision 3) must not force
/// the holder to disclose the irrelevant attribute. So when the *age* predicate
/// is neutralized the holder may leave `birth_date` empty, and when the *nat*
/// predicate is neutralized the holder may leave `nationalities` empty — in each
/// case a value that trivially clears the neutralized leg is substituted. This
/// only touches the private witness (verify rebuilds the statement, never the
/// credential), so the prove/verify symmetry is unaffected. The substituted
/// values satisfy the neutralized predicate by construction: `min_age = 0` makes
/// the age cutoff today (and the bound is inclusive, so a DOB of today passes),
/// and the universal accepted set contains every assigned code.
pub(crate) fn to_credential(
    witness: &ZkWitness,
    policy: &Policy,
    mode: PredicateMode,
) -> Result<Credential, ZkError> {
    // Age neutralized + no date supplied ⇒ default to today's date, which clears
    // the `min_age = 0` cutoff (inclusive). A supplied date is still validated.
    let (year, month, day) = if !mode.uses_age() && witness.birth_date.is_empty() {
        let d = policy.current_date;
        (d.year as u16, d.month as u8, d.day as u8)
    } else {
        parse_birth_date(&witness.birth_date)?
    };

    // Nat neutralized + no nationality supplied ⇒ default to any assigned code
    // (the accepted set is universal, so it is a trivial member). A supplied set
    // is still selected against the accepted set.
    let nationality = if !mode.uses_nat() && witness.nationalities.is_empty() {
        default_assigned_code()
    } else {
        select_nationality(&witness.nationalities, &policy.accepted_nationalities)?
    };

    Ok(Credential::new(year, month, day, nationality))
}

/// A deterministic assigned ISO-3166-1 numeric code, used to fill the credential
/// when the nat predicate is neutralized and the holder discloses no
/// nationality. Any assigned code is a member of the universal accepted set.
fn default_assigned_code() -> u16 {
    all_nationality_codes()
        .first()
        .copied()
        .and_then(|c| u16::try_from(c).ok())
        .unwrap_or(276) // Germany — always assigned
}

/// Reject an age threshold beyond the age predicate's supported span. Reuses the
/// prover's own bound (currently 120 years) rather than hardcoding it.
fn validate_min_age(current: Date, min_age: u32) -> Result<(), ZkError> {
    let max_supported = Policy {
        current_date: current,
        min_age_years: 0,
        accepted_nationalities: Vec::new(),
    }
    .age_public_input()
    .bounds
    .max_supported_age_years;
    if min_age > max_supported {
        return Err(invalid(format!(
            "age threshold {min_age} exceeds the maximum supported age {max_supported}"
        )));
    }
    Ok(())
}

/// Mirror `NationalityPredicate::validate`: at least 2 distinct codes, all
/// assigned ISO-3166-1 numeric. (`Policy::nat_public_input` sorts + dedups, so
/// "distinct" matches the count the predicate ultimately checks.)
fn validate_accepted_set(accepted: &[u32]) -> Result<(), ZkError> {
    let distinct: HashSet<u32> = accepted.iter().copied().collect();
    if distinct.len() < 2 {
        return Err(invalid(
            "accepted nationality set must contain at least 2 distinct ISO-3166-1 numeric codes",
        ));
    }
    let assigned: HashSet<u32> = all_nationality_codes().into_iter().collect();
    for &code in accepted {
        if !assigned.contains(&code) {
            return Err(invalid(format!(
                "{code} is not an assigned ISO-3166-1 numeric country code"
            )));
        }
    }
    Ok(())
}

/// Parse a strict `"YYYY-MM-DD"` (mdoc `full-date`) into `(year, month, day)`.
///
/// Only the structural shape and coarse field ranges are checked here; full
/// calendar validity (real day-of-month, age within bounds) is enforced by the
/// age predicate at prove time, so a structurally-valid but impossible date
/// surfaces there as a failed prove rather than here.
fn parse_birth_date(s: &str) -> Result<(u16, u8, u8), ZkError> {
    let parts: Vec<&str> = s.split('-').collect();
    if parts.len() != 3 || parts[0].len() != 4 || parts[1].len() != 2 || parts[2].len() != 2 {
        return Err(invalid(format!(
            "birth_date must be `YYYY-MM-DD`, got `{s}`"
        )));
    }
    let year: u16 = parts[0]
        .parse()
        .map_err(|_| invalid(format!("invalid year in birth_date `{s}`")))?;
    let month: u8 = parts[1]
        .parse()
        .map_err(|_| invalid(format!("invalid month in birth_date `{s}`")))?;
    let day: u8 = parts[2]
        .parse()
        .map_err(|_| invalid(format!("invalid day in birth_date `{s}`")))?;
    if !(1..=12).contains(&month) {
        return Err(invalid(format!(
            "birth_date month must be 1..=12, got {month}"
        )));
    }
    if !(1..=31).contains(&day) {
        return Err(invalid(format!("birth_date day must be 1..=31, got {day}")));
    }
    Ok((year, month, day))
}

/// Select the single nationality code embedded in the credential from the held
/// set.
///
/// **Selection rule:** prefer a held code that is in the accepted set, so the
/// credential-bound nat predicate finds a match and an honest proof succeeds;
/// otherwise fall back to the first held code — a holder genuinely not in the
/// accepted set then cannot prove membership (the proof fails at witness time,
/// like an under-age request), which is the correct outcome, not an input
/// error. For age-only mode the accepted set is universal, so the first held
/// (assigned) code is chosen. The chosen code must be an assigned ISO numeric
/// (else it is not in any membership table — surfaced as invalid input).
fn select_nationality(held: &[u32], accepted: &[u32]) -> Result<u16, ZkError> {
    if held.is_empty() {
        return Err(invalid("witness carries no nationalities"));
    }
    let accepted_set: HashSet<u32> = accepted.iter().copied().collect();
    let chosen = held
        .iter()
        .copied()
        .find(|c| accepted_set.contains(c))
        .unwrap_or(held[0]);

    let assigned: HashSet<u32> = all_nationality_codes().into_iter().collect();
    if !assigned.contains(&chosen) {
        return Err(invalid(format!(
            "{chosen} is not an assigned ISO-3166-1 numeric country code"
        )));
    }
    u16::try_from(chosen).map_err(|_| {
        invalid(format!(
            "nationality code {chosen} exceeds the 16-bit credential field"
        ))
    })
}

/// Convert an epoch-day integer (days since 1970-01-01) to a [`Date`].
///
/// Howard Hinnant's `civil_from_days` (the inverse of `days_from_civil`), exact
/// over the whole proleptic Gregorian range. In practice `today_epoch_day` is
/// always post-1970, but negatives are handled correctly regardless.
fn epoch_day_to_date(epoch_day: i32) -> Result<Date, ZkError> {
    let z = i64::from(epoch_day) + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = z - era * 146_097; // [0, 146096]
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365; // [0, 399]
    let year = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100); // [0, 365]
    let mp = (5 * doy + 2) / 153; // [0, 11]
    let day = doy - (153 * mp + 2) / 5 + 1; // [1, 31]
    let month = if mp < 10 { mp + 3 } else { mp - 9 }; // [1, 12]
    let year = year + i64::from(month <= 2);

    let year = u32::try_from(year).map_err(|_| {
        invalid(format!(
            "today_epoch_day {epoch_day} maps to a year outside the supported range"
        ))
    })?;
    Ok(Date {
        year,
        month: month as u32,
        day: day as u32,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::NatMode;

    /// Forward Gregorian-to-epoch-day (Hinnant) — the inverse of the function
    /// under test, used to cross-check it over a sweep of dates.
    fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
        let y = if m <= 2 { y - 1 } else { y };
        let era = if y >= 0 { y } else { y - 399 } / 400;
        let yoe = y - era * 400; // [0, 399]
        let mp = if m > 2 { m - 3 } else { m + 9 };
        let doy = (153 * mp + 2) / 5 + d - 1; // [0, 365]
        let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy; // [0, 146096]
        era * 146_097 + doe - 719_468
    }

    fn date(year: u32, month: u32, day: u32) -> Date {
        Date { year, month, day }
    }

    fn statement_with(mode: PredicateMode) -> ZkPublicStatement {
        ZkPublicStatement {
            spec_id: "stwo-euid-pid-v1".to_string(),
            version: 1,
            doctype: "eu.europa.ec.eudi.pid.1".to_string(),
            namespace: "eu.europa.ec.eudi.pid.1".to_string(),
            issuer_key_x: vec![0x11; 32],
            issuer_key_y: vec![0x22; 32],
            // 2020-01-01.
            today_epoch_day: days_from_civil(2020, 1, 1) as i32,
            nonce: vec![0xab, 0xcd],
            predicate_mode: mode,
            age_threshold_years: Some(18),
            // Germany, France (both assigned, distinct).
            accepted_numeric_countries: Some(vec![276, 250]),
            nat_mode: NatMode::Any,
        }
    }

    fn witness() -> ZkWitness {
        ZkWitness {
            issuer_sig_r: vec![1; 32],
            issuer_sig_s: vec![2; 32],
            sig_structure: vec![3; 16],
            mso: vec![4; 16],
            birth_date_item: vec![5; 8],
            nationality_item: vec![6; 8],
            birth_date: "1990-07-15".to_string(),
            nationalities: vec![276], // Germany
            digest_ids: std::collections::HashMap::new(),
        }
    }

    // ---- epoch-day conversion ---------------------------------------------

    #[test]
    fn epoch_day_known_vectors() {
        assert_eq!(epoch_day_to_date(0).unwrap(), date(1970, 1, 1));
        assert_eq!(epoch_day_to_date(10_957).unwrap(), date(2000, 1, 1));
        assert_eq!(epoch_day_to_date(-1).unwrap(), date(1969, 12, 31));
    }

    #[test]
    fn epoch_day_round_trips_against_forward_algorithm() {
        // A sweep across leap years, month/day boundaries, and both eras.
        for &(y, m, d) in &[
            (1970, 1, 1),
            (1999, 12, 31),
            (2000, 2, 29), // leap
            (2020, 2, 29), // leap
            (2021, 3, 1),
            (2024, 6, 23),
            (2100, 2, 28), // non-leap century
        ] {
            let ed = days_from_civil(y, m, d) as i32;
            assert_eq!(
                epoch_day_to_date(ed).unwrap(),
                date(y as u32, m as u32, d as u32),
                "epoch day {ed}"
            );
        }
    }

    // ---- predicate-mode neutralization ------------------------------------

    #[test]
    fn and_mode_keeps_both_predicates_real() {
        let policy = to_policy(&statement_with(PredicateMode::And)).unwrap();
        assert_eq!(policy.current_date, date(2020, 1, 1));
        assert_eq!(policy.min_age_years, 18);
        assert_eq!(policy.accepted_nationalities, vec![276, 250]);
    }

    #[test]
    fn age_mode_neutralizes_nat_with_universal_set() {
        let policy = to_policy(&statement_with(PredicateMode::Age)).unwrap();
        assert_eq!(policy.min_age_years, 18);
        // The accepted set is the universal one, regardless of what the
        // statement carried — every assigned code is a trivial member.
        assert_eq!(policy.accepted_nationalities, all_nationality_codes());
        assert!(policy.accepted_nationalities.contains(&276));
        assert!(policy.accepted_nationalities.len() > 200);
    }

    #[test]
    fn nat_mode_neutralizes_age_with_zero_threshold() {
        let policy = to_policy(&statement_with(PredicateMode::Nat)).unwrap();
        // min_age 0 ⇒ cutoff is today ⇒ any real DOB clears the age check.
        assert_eq!(policy.min_age_years, 0);
        assert_eq!(policy.age_cutoff(), policy.current_date);
        assert_eq!(policy.accepted_nationalities, vec![276, 250]);
    }

    #[test]
    fn or_mode_is_rejected() {
        let err = to_policy(&statement_with(PredicateMode::Or)).unwrap_err();
        assert!(matches!(err, ZkError::InvalidInput(_)));
    }

    // ---- symmetry: prove side == verify side ------------------------------

    #[test]
    fn policy_is_symmetric_across_modes() {
        // The "prove side" and "verify side" both call `to_policy` on the same
        // request parameters; the result must be byte-identical (the prover's
        // caller-argument binding rejects any drift). It uses no private values,
        // so a different witness cannot change it.
        for mode in [PredicateMode::Age, PredicateMode::Nat, PredicateMode::And] {
            let stmt = statement_with(mode);
            let prove_side = to_policy(&stmt).unwrap();
            let verify_side = to_policy(&stmt).unwrap();
            assert_eq!(prove_side, verify_side, "mode {mode:?}");

            // And the derived predicate public inputs — exactly what the prover
            // binds and the verifier checks — match the prover's normalization.
            let api = prove_side.age_public_input();
            assert_eq!(api.current, prove_side.current_date);
            assert_eq!(api.min_age_years, prove_side.min_age_years);
            let mut expected_nat = prove_side.accepted_nationalities.clone();
            expected_nat.sort_unstable();
            expected_nat.dedup();
            assert_eq!(prove_side.nat_public_input().acceptable, expected_nat);
        }
    }

    #[test]
    fn universal_set_does_not_depend_on_the_held_value() {
        // Age-only neutralization is reconstructible because it is the same set
        // no matter what nationality the (private) holder carries.
        let stmt = statement_with(PredicateMode::Age);
        let a = to_policy(&stmt).unwrap();
        // The verifier never sees the witness; building twice from the request
        // alone yields the identical accepted set.
        let b = to_policy(&stmt).unwrap();
        assert_eq!(a.accepted_nationalities, b.accepted_nationalities);
        assert_eq!(a.accepted_nationalities, all_nationality_codes());
    }

    // ---- public statement -------------------------------------------------

    #[test]
    fn public_statement_uses_the_demo_issuer_key() {
        let stmt = statement_with(PredicateMode::And);
        let ps = to_public_statement(&stmt).unwrap();
        // The statement's issuer_key_x/y (0x11.. / 0x22..) are ignored.
        assert_eq!(ps.issuer_key.x, IssuerKey::demo().public_key().x);
        assert_eq!(ps.issuer_key.y, IssuerKey::demo().public_key().y);
        assert_ne!(ps.issuer_key.x.0.to_vec(), vec![0x11; 32]);
    }

    // ---- witness -> credential --------------------------------------------

    #[test]
    fn credential_parses_date_and_selects_accepted_code() {
        let policy = to_policy(&statement_with(PredicateMode::And)).unwrap();
        let cred = to_credential(&witness(), &policy, PredicateMode::And).unwrap();
        assert_eq!(cred.birth_year, 1990);
        assert_eq!(cred.birth_month, 7);
        assert_eq!(cred.birth_day, 15);
        assert_eq!(cred.nationality, 276);
    }

    #[test]
    fn credential_prefers_a_held_code_in_the_accepted_set() {
        // Holds France(250) and Germany(276); accepted set is {Germany, Italy}.
        let mut stmt = statement_with(PredicateMode::Nat);
        stmt.accepted_numeric_countries = Some(vec![276, 380]); // DE, IT
        let policy = to_policy(&stmt).unwrap();

        let mut w = witness();
        w.nationalities = vec![250, 276]; // FR (not accepted), DE (accepted)
        let cred = to_credential(&w, &policy, PredicateMode::Nat).unwrap();
        assert_eq!(cred.nationality, 276, "must pick the accepted held code");
    }

    #[test]
    fn credential_falls_back_to_first_held_when_none_accepted() {
        // Held FR(250) only; accepted {DE, IT}. FR is a valid assigned code, so
        // the credential carries it — the nat predicate will then (correctly)
        // fail to prove membership at prove time.
        let mut stmt = statement_with(PredicateMode::Nat);
        stmt.accepted_numeric_countries = Some(vec![276, 380]);
        let policy = to_policy(&stmt).unwrap();

        let mut w = witness();
        w.nationalities = vec![250];
        let cred = to_credential(&w, &policy, PredicateMode::Nat).unwrap();
        assert_eq!(cred.nationality, 250);
    }

    // ---- input validation -------------------------------------------------

    #[test]
    fn rejects_a_bad_date_string() {
        let policy = to_policy(&statement_with(PredicateMode::And)).unwrap();
        for bad in [
            "1990/07/15",
            "90-07-15",
            "1990-13-01",
            "1990-07-32",
            "garbage",
        ] {
            let mut w = witness();
            w.birth_date = bad.to_string();
            assert!(
                matches!(
                    to_credential(&w, &policy, PredicateMode::And),
                    Err(ZkError::InvalidInput(_))
                ),
                "expected rejection for `{bad}`"
            );
        }
    }

    #[test]
    fn rejects_an_unassigned_held_code() {
        let policy = to_policy(&statement_with(PredicateMode::And)).unwrap();
        let mut w = witness();
        w.nationalities = vec![1]; // not an assigned ISO numeric
        assert!(matches!(
            to_credential(&w, &policy, PredicateMode::And),
            Err(ZkError::InvalidInput(_))
        ));
    }

    #[test]
    fn rejects_an_empty_held_set() {
        let policy = to_policy(&statement_with(PredicateMode::And)).unwrap();
        let mut w = witness();
        w.nationalities = vec![];
        assert!(matches!(
            to_credential(&w, &policy, PredicateMode::And),
            Err(ZkError::InvalidInput(_))
        ));
    }

    // ---- selective disclosure: a neutralized predicate needs no witness -----

    #[test]
    fn age_only_allows_an_empty_nationality_set() {
        // Verifier asks only for age ⇒ the holder discloses no nationality.
        // The credential is filled with a default assigned code (trivially a
        // member of the universal accepted set), so prove can proceed.
        let policy = to_policy(&statement_with(PredicateMode::Age)).unwrap();
        let mut w = witness();
        w.nationalities = vec![];
        let cred = to_credential(&w, &policy, PredicateMode::Age).unwrap();
        let assigned: HashSet<u32> = all_nationality_codes().into_iter().collect();
        assert!(assigned.contains(&u32::from(cred.nationality)));
    }

    #[test]
    fn nat_only_allows_an_empty_birth_date() {
        // Verifier asks only for nationality ⇒ the holder discloses no DOB.
        // The credential is filled with today's date, which clears the
        // neutralized `min_age = 0` cutoff (inclusive).
        let stmt = statement_with(PredicateMode::Nat);
        let policy = to_policy(&stmt).unwrap();
        let mut w = witness();
        w.birth_date = String::new();
        let cred = to_credential(&w, &policy, PredicateMode::Nat).unwrap();
        assert_eq!(
            date(
                u32::from(cred.birth_year),
                u32::from(cred.birth_month),
                u32::from(cred.birth_day)
            ),
            policy.current_date,
            "default DOB must equal the policy reference date"
        );
    }

    #[test]
    fn and_mode_still_requires_both_witness_fields() {
        // Neutralization is per-predicate: with both active, an absent field is
        // still a hard error (no silent default).
        let policy = to_policy(&statement_with(PredicateMode::And)).unwrap();

        let mut w = witness();
        w.nationalities = vec![];
        assert!(matches!(
            to_credential(&w, &policy, PredicateMode::And),
            Err(ZkError::InvalidInput(_))
        ));

        let mut w = witness();
        w.birth_date = String::new();
        assert!(matches!(
            to_credential(&w, &policy, PredicateMode::And),
            Err(ZkError::InvalidInput(_))
        ));
    }

    #[test]
    fn rejects_a_too_small_accepted_set() {
        let mut stmt = statement_with(PredicateMode::Nat);
        stmt.accepted_numeric_countries = Some(vec![276, 276]); // dedups to one
        assert!(matches!(to_policy(&stmt), Err(ZkError::InvalidInput(_))));

        stmt.accepted_numeric_countries = Some(vec![276]);
        assert!(matches!(to_policy(&stmt), Err(ZkError::InvalidInput(_))));
    }

    #[test]
    fn rejects_an_unassigned_code_in_accepted_set() {
        let mut stmt = statement_with(PredicateMode::And);
        stmt.accepted_numeric_countries = Some(vec![276, 1]); // 1 is unassigned
        assert!(matches!(to_policy(&stmt), Err(ZkError::InvalidInput(_))));
    }

    #[test]
    fn rejects_an_over_large_age_threshold() {
        let mut stmt = statement_with(PredicateMode::Age);
        stmt.age_threshold_years = Some(200); // beyond the 120y supported span
        assert!(matches!(to_policy(&stmt), Err(ZkError::InvalidInput(_))));
    }

    #[test]
    fn rejects_a_missing_required_field() {
        // Age active but no threshold.
        let mut stmt = statement_with(PredicateMode::And);
        stmt.age_threshold_years = None;
        assert!(matches!(to_policy(&stmt), Err(ZkError::InvalidInput(_))));

        // Nat active but no accepted set.
        let mut stmt = statement_with(PredicateMode::And);
        stmt.accepted_numeric_countries = None;
        assert!(matches!(to_policy(&stmt), Err(ZkError::InvalidInput(_))));
    }
}
