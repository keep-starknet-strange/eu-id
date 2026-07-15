//! Translation from the SDK's [`ZkPublicStatement`] to the production mdoc
//! prover's public [`Policy`].
//!
//! The mapping is deterministic and side-effect-free. Both proving and
//! verification derive the same policy from the same public request, so neither
//! depends on private mdoc values.
//!
//! `And` proves both predicates; `Age` neutralizes nationality with the
//! universal assigned-country set; `Nat` neutralizes age with `min_age = 0`;
//! `Or` is rejected.

use std::collections::HashSet;

use eu_id_prover::{all_nationality_codes, Date, Policy};

use crate::{PredicateMode, ZkError, ZkPublicStatement};

/// Build a [`ZkError::InvalidInput`] with an actionable message.
fn invalid(msg: impl Into<String>) -> ZkError {
    ZkError::InvalidInput(msg.into())
}

/// Map a [`ZkPublicStatement`] to the prover's [`Policy`] — reference date,
/// minimum age, and accepted-nationality set.
///
/// This consumes **only** the public request parameters (never the private held
/// values), so the prove and verify sides produce the same `Policy`. That is
/// exactly what lets the production mdoc prover and verifier agree.
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

    let accepted_nationalities_alpha2 = accepted_alpha2_set(&accepted_nationalities)?;

    Ok(Policy {
        current_date: current,
        min_age_years,
        accepted_nationalities,
        accepted_nationalities_alpha2,
    })
}

fn accepted_alpha2_set(accepted_numeric: &[u32]) -> Result<Vec<[u8; 2]>, ZkError> {
    accepted_numeric
        .iter()
        .map(|code| {
            let country = celes::Country::from_value(
                usize::try_from(*code).map_err(|_| invalid("country code out of range"))?,
            )
            .map_err(|_| invalid(format!("unknown ISO-3166 numeric code {code}")))?;
            country
                .alpha2
                .as_bytes()
                .try_into()
                .map_err(|_| invalid(format!("country {code} has malformed alpha-2 code")))
        })
        .collect()
}

/// Reject an age threshold beyond the age predicate's supported span. Reuses the
/// prover's own bound (currently 120 years) rather than hardcoding it.
fn validate_min_age(current: Date, min_age: u32) -> Result<(), ZkError> {
    let max_supported = Policy {
        current_date: current,
        min_age_years: 0,
        accepted_nationalities: Vec::new(),
        accepted_nationalities_alpha2: Vec::new(),
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

    // ---- input validation -------------------------------------------------

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
