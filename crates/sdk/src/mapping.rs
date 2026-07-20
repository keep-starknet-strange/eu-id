//! Deterministic translation from the SDK's public request to the mdoc policy.

use std::collections::HashSet;

use eu_id_prover::{all_nationality_codes, Date, Policy};

use crate::{PredicateMode, ZkError, ZkPublicStatement};

fn invalid(msg: impl Into<String>) -> ZkError {
    ZkError::InvalidInput(msg.into())
}

/// Map the verifier's public request to the policy bound by the mdoc proof.
pub(crate) fn to_policy(statement: &ZkPublicStatement) -> Result<Policy, ZkError> {
    let mode = statement.predicate_mode;
    if matches!(mode, PredicateMode::Or) {
        return Err(invalid(
            "predicate mode `or` is not supported (only `age`, `nat`, `and`)",
        ));
    }

    let current = epoch_day_to_date(statement.today_epoch_day)?;
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
        accepted_nationalities_alpha2: accepted_alpha2_set(&accepted_nationalities)?,
        accepted_nationalities,
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

/// Convert days since 1970-01-01 to a proleptic-Gregorian date.
fn epoch_day_to_date(epoch_day: i32) -> Result<Date, ZkError> {
    let z = i64::from(epoch_day) + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let year = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
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
    use crate::{IssuerKey, NatMode};

    fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
        let y = if m <= 2 { y - 1 } else { y };
        let era = if y >= 0 { y } else { y - 399 } / 400;
        let yoe = y - era * 400;
        let mp = if m > 2 { m - 3 } else { m + 9 };
        let doy = (153 * mp + 2) / 5 + d - 1;
        let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
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
            issuer_key: IssuerKey::MlDsa { pk_hash: vec![0x11; 32] },
            today_epoch_day: days_from_civil(2020, 1, 1) as i32,
            nonce: vec![0xab, 0xcd],
            predicate_mode: mode,
            age_threshold_years: Some(18),
            accepted_numeric_countries: Some(vec![276, 250]),
            nat_mode: NatMode::Any,
        }
    }

    #[test]
    fn epoch_day_known_vectors() {
        assert_eq!(epoch_day_to_date(0).unwrap(), date(1970, 1, 1));
        assert_eq!(epoch_day_to_date(10_957).unwrap(), date(2000, 1, 1));
        assert_eq!(epoch_day_to_date(-1).unwrap(), date(1969, 12, 31));
    }

    #[test]
    fn epoch_day_round_trips_against_forward_algorithm() {
        for &(y, m, d) in &[
            (1970, 1, 1),
            (1999, 12, 31),
            (2000, 2, 29),
            (2020, 2, 29),
            (2021, 3, 1),
            (2024, 6, 23),
            (2100, 2, 28),
        ] {
            let epoch_day = days_from_civil(y, m, d) as i32;
            assert_eq!(
                epoch_day_to_date(epoch_day).unwrap(),
                date(y as u32, m as u32, d as u32)
            );
        }
    }

    #[test]
    fn predicate_modes_map_to_the_expected_policy() {
        let both = to_policy(&statement_with(PredicateMode::And)).unwrap();
        assert_eq!(both.current_date, date(2020, 1, 1));
        assert_eq!(both.min_age_years, 18);
        assert_eq!(both.accepted_nationalities, vec![276, 250]);

        let age = to_policy(&statement_with(PredicateMode::Age)).unwrap();
        assert_eq!(age.min_age_years, 18);
        assert_eq!(age.accepted_nationalities, all_nationality_codes());

        let nat = to_policy(&statement_with(PredicateMode::Nat)).unwrap();
        assert_eq!(nat.min_age_years, 0);
        assert_eq!(nat.age_cutoff(), nat.current_date);

        assert!(matches!(
            to_policy(&statement_with(PredicateMode::Or)),
            Err(ZkError::InvalidInput(_))
        ));
    }

    #[test]
    fn policy_mapping_rejects_invalid_bounds() {
        let mut statement = statement_with(PredicateMode::And);
        statement.accepted_numeric_countries = Some(vec![276]);
        assert!(matches!(
            to_policy(&statement),
            Err(ZkError::InvalidInput(_))
        ));

        statement.accepted_numeric_countries = Some(vec![276, 1]);
        assert!(matches!(
            to_policy(&statement),
            Err(ZkError::InvalidInput(_))
        ));

        statement.accepted_numeric_countries = Some(vec![276, 250]);
        statement.age_threshold_years = Some(200);
        assert!(matches!(
            to_policy(&statement),
            Err(ZkError::InvalidInput(_))
        ));
    }

    #[test]
    fn policy_mapping_requires_active_predicate_fields() {
        let mut statement = statement_with(PredicateMode::And);
        statement.age_threshold_years = None;
        assert!(matches!(
            to_policy(&statement),
            Err(ZkError::InvalidInput(_))
        ));

        let mut statement = statement_with(PredicateMode::And);
        statement.accepted_numeric_countries = None;
        assert!(matches!(
            to_policy(&statement),
            Err(ZkError::InvalidInput(_))
        ));
    }
}
