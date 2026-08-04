//! Translation from the SDK's [`ZkPublicStatement`] to the production mdoc
//! prover's public [`Policy`].
//!
//! The mapping is deterministic and side-effect-free. Both proving and
//! verification derive the same policy from the same public request, so neither
//! depends on private mdoc values.
//!
//! `And` proves both predicates. `Age` neutralizes nationality with the
//! universal assigned-country set. `Nat` neutralizes age with `min_age = 0`.

use eu_id_prover::{Date, Policy};

use crate::{ZkError, ZkPublicStatement};

/// Build a [`ZkError::InvalidInput`] with an actionable message.
fn invalid(msg: impl Into<String>) -> ZkError {
    ZkError::InvalidInput(msg.into())
}

/// Map a [`ZkPublicStatement`] to the prover's [`Policy`].
///
/// It uses only public request values. Proving and verification therefore build
/// the same policy without reading credential attributes.
pub(crate) fn to_policy(statement: &ZkPublicStatement) -> Result<Policy, ZkError> {
    let mode = statement.predicate_mode;

    let epoch_day = i32::try_from(statement.now_epoch_seconds / 86_400)
        .map_err(|_| invalid("now_epoch_seconds is outside the supported date range"))?;
    let current = epoch_day_to_date(epoch_day)?;

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

    let accepted_nationalities = if mode.uses_nat() {
        let accepted = statement
            .accepted_alpha2_countries
            .as_deref()
            .ok_or_else(|| {
                invalid("nationality predicate active but `accepted_alpha2_countries` is absent")
            })?;
        accepted_country_codes(accepted)?
    } else {
        all_country_codes()
    };

    Ok(Policy {
        current_date: current,
        min_age_years,
        accepted_nationalities,
    })
}

fn all_country_codes() -> Vec<[u8; 2]> {
    (b'A'..=b'Z')
        .flat_map(|first| (b'A'..=b'Z').map(move |second| [first, second]))
        .filter(|code| eu_id_prover::is_assigned_iso_alpha2(*code))
        .collect()
}

/// Validate the sole public nationality representation.
fn accepted_country_codes(accepted: &[String]) -> Result<Vec<[u8; 2]>, ZkError> {
    if accepted.is_empty() {
        return Err(invalid("accepted nationality set must not be empty"));
    }
    if accepted.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(invalid(
            "accepted nationality set must be sorted and unique",
        ));
    }

    accepted
        .iter()
        .map(|code| {
            let bytes: [u8; 2] = code.as_bytes().try_into().map_err(|_| {
                invalid(format!(
                    "`{code}` is not an uppercase ISO 3166-1 alpha-2 country code"
                ))
            })?;
            if !eu_id_prover::is_assigned_iso_alpha2(bytes) {
                return Err(invalid(format!(
                    "`{code}` is not an assigned ISO 3166-1 alpha-2 country code"
                )));
            }
            Ok(bytes)
        })
        .collect()
}

/// Reject an age threshold beyond the age predicate's supported span. Reuses the
/// prover's 120-year bound instead of a duplicate constant.
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

/// Convert an epoch-day integer (days since 1970-01-01) to a [`Date`].
///
/// Convert with the inverse of Howard Hinnant's `days_from_civil` algorithm.
/// The conversion is exact over the proleptic Gregorian range.
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
    use crate::PredicateMode;

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
            version: 2,
            profile_id: "eudi-pid-p256-identity".to_string(),
            circuit_hash: "00".repeat(32),
            root_policy_hash: vec![0; 32],
            doctype: "eu.europa.ec.eudi.pid.1".to_string(),
            namespace: "eu.europa.ec.eudi.pid.1".to_string(),
            issuer_public_key_x: vec![0x11; 32],
            issuer_public_key_y: vec![0x22; 32],
            // 2020-01-01T00:00:00Z.
            now_epoch_seconds: u64::try_from(days_from_civil(2020, 1, 1)).unwrap() * 86_400,
            session_transcript: vec![0xab, 0xcd],
            predicate_mode: mode,
            age_threshold_years: Some(18),
            // Germany, France (both assigned, distinct, and sorted by alpha-2).
            accepted_alpha2_countries: Some(vec!["DE".to_string(), "FR".to_string()]),
            revocation_public_key_x: vec![0x33; 32],
            revocation_public_key_y: vec![0x44; 32],
            revocation_epoch: 1,
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
        assert_eq!(policy.accepted_nationalities, vec![*b"DE", *b"FR"]);
    }

    #[test]
    fn age_mode_uses_the_universal_nationality_set() {
        let policy = to_policy(&statement_with(PredicateMode::Age)).unwrap();
        assert_eq!(policy.min_age_years, 18);
        // The accepted set is the universal one, regardless of what the
        // statement carried — every assigned code is a trivial member.
        assert_eq!(policy.accepted_nationalities, all_country_codes());
        assert!(policy.accepted_nationalities.contains(b"DE"));
        assert!(policy.accepted_nationalities.len() > 200);
    }

    #[test]
    fn nationality_mode_uses_a_zero_age_threshold() {
        let policy = to_policy(&statement_with(PredicateMode::Nat)).unwrap();
        // min_age 0 ⇒ cutoff is today ⇒ any real DOB clears the age check.
        assert_eq!(policy.min_age_years, 0);
        assert_eq!(policy.age_cutoff(), policy.current_date);
        assert_eq!(policy.accepted_nationalities, vec![*b"DE", *b"FR"]);
    }

    // ---- symmetry: prove side == verify side ------------------------------

    #[test]
    fn policy_is_symmetric_across_modes() {
        // The "prove side" and "verify side" both call `to_policy` on the same
        // request parameters. The result must be byte-identical (the prover's
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
            let mut expected_nat = prove_side
                .accepted_nationalities
                .iter()
                .map(|code| u32::from(u16::from_be_bytes(*code)))
                .collect::<Vec<_>>();
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
        // The verifier never sees the witness. Building twice from the request
        // alone yields the identical accepted set.
        let b = to_policy(&stmt).unwrap();
        assert_eq!(a.accepted_nationalities, b.accepted_nationalities);
        assert_eq!(a.accepted_nationalities, all_country_codes());
    }

    // ---- input validation -------------------------------------------------

    #[test]
    fn accepts_a_singleton_accepted_set() {
        let mut stmt = statement_with(PredicateMode::Nat);
        stmt.accepted_alpha2_countries = Some(vec!["DE".to_string()]);
        let policy = to_policy(&stmt).unwrap();
        assert_eq!(policy.accepted_nationalities, vec![*b"DE"]);
    }

    #[test]
    fn rejects_a_noncanonical_accepted_set() {
        let mut stmt = statement_with(PredicateMode::Nat);
        stmt.accepted_alpha2_countries = Some(Vec::new());
        assert!(matches!(to_policy(&stmt), Err(ZkError::InvalidInput(_))));

        stmt.accepted_alpha2_countries = Some(vec!["DE".to_string(), "DE".to_string()]);
        assert!(matches!(to_policy(&stmt), Err(ZkError::InvalidInput(_))));

        stmt.accepted_alpha2_countries = Some(vec!["FR".to_string(), "DE".to_string()]);
        assert!(matches!(to_policy(&stmt), Err(ZkError::InvalidInput(_))));
    }

    #[test]
    fn rejects_non_iso_alpha2_codes() {
        for code in ["de", "D", "DEU", "D1", "QU", "QS", "XK", "ZZ"] {
            let mut stmt = statement_with(PredicateMode::And);
            stmt.accepted_alpha2_countries = Some(vec![code.to_string()]);
            assert!(
                matches!(to_policy(&stmt), Err(ZkError::InvalidInput(_))),
                "{code} must be rejected"
            );
        }
    }

    #[test]
    fn rejects_an_age_threshold_above_the_supported_bound() {
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
        stmt.accepted_alpha2_countries = None;
        assert!(matches!(to_policy(&stmt), Err(ZkError::InvalidInput(_))));
    }
}
