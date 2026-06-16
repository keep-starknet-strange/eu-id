pub mod bit_decomposition;
pub mod range_check;

/// Helper enum for selecting an age-check strategy. Used inside the crate (e.g.
/// by the demo CLI and benches) to represent a choice; external callers pick a
/// strategy by calling [`range_check::AgeRangeCheck`] or
/// [`bit_decomposition::AgeBitDecomposition`] directly.
#[derive(Clone, Copy)]
pub enum AgeCheckStrategy {
    BitDecomposition,
    RangeCheck,
}

#[cfg(test)]
mod tests {
    use super::bit_decomposition::AgeBitDecomposition;
    use super::range_check::AgeRangeCheck;
    use crate::age::types::{AgeBounds, Date, DateOfBirth, Error, PublicInput};
    use crate::AgeInputError;
    use stwo::core::pcs::PcsConfig;

    macro_rules! age_predicate_tests {
        ($module:ident, $Predicate:ty, $new:expr, $new_non_validating:expr) => {
            mod $module {
                use super::*;

                fn setup_today(min_age_years: u32) -> PublicInput {
                    PublicInput::new(Date { year: 2026, month: 5, day: 19 }, min_age_years)
                }

                fn dob(year: u32, month: u32, day: u32) -> DateOfBirth {
                    DateOfBirth(Date { year, month, day })
                }

                fn validating_predicate() -> $Predicate {
                    $new
                }

                fn non_validating_predicate() -> $Predicate {
                    $new_non_validating
                }

                #[test]
                fn proves_and_verifies_exactly_minimum_age() {
                    let predicate = validating_predicate();
                    let proof = predicate.prove(&setup_today(18), &dob(2008, 5, 19)).unwrap();
                    predicate.verify(&proof).unwrap();
                }

                #[test]
                fn proves_and_verifies_older_than_minimum_age() {
                    let predicate = validating_predicate();
                    let proof = predicate.prove(&setup_today(18), &dob(2008, 5, 18)).unwrap();
                    predicate.verify(&proof).unwrap();
                }

                #[test]
                fn proves_and_verifies_with_custom_bounds() {
                    let predicate = validating_predicate();
                    let bounds = AgeBounds {
                        min_supported_year: 1990,
                        max_supported_year: 2030,
                        max_supported_age_years: 40,
                    };
                    let proof = predicate
                        .prove(&PublicInput::new_with_bounds(Date { year: 2026, month: 5, day: 19 }, 18, bounds), &dob(2008, 5, 19))
                        .unwrap();
                    predicate.verify(&proof).unwrap();
                }

                #[test]
                fn validate_rejects_underage() {
                    let predicate = validating_predicate();
                    let error = predicate.prove(&setup_today(18), &dob(2008, 5, 20)).unwrap_err();
                    assert!(matches!(error, Error::Input(AgeInputError::UnderAge)));
                }

                #[test]
                fn validate_rejects_invalid_month() {
                    let predicate = validating_predicate();
                    let error = predicate
                        .prove(&PublicInput::new(Date { year: 2026, month: 13, day: 19 }, 18), &dob(2000, 1, 1))
                        .unwrap_err();
                    assert!(matches!(error, Error::Input(AgeInputError::InvalidMonth(13))));
                }

                #[test]
                fn validate_rejects_invalid_day() {
                    let predicate = validating_predicate();
                    let error = predicate.prove(&setup_today(18), &dob(2000, 1, 32)).unwrap_err();
                    assert!(matches!(error, Error::Input(AgeInputError::InvalidDay(32))));
                }

                #[test]
                fn validate_rejects_invalid_supported_bounds() {
                    let predicate = validating_predicate();
                    let bounds = AgeBounds {
                        min_supported_year: 2030,
                        max_supported_year: 2020,
                        max_supported_age_years: 18,
                    };
                    let error = predicate
                        .prove(&PublicInput::new_with_bounds(Date { year: 2026, month: 5, day: 19 }, 18, bounds), &dob(2000, 1, 1))
                        .unwrap_err();
                    assert!(matches!(error, Error::Input(AgeInputError::Invalid(ref m)) if m.contains("exceeds max")));
                }

                #[test]
                fn validate_rejects_min_age_above_supported_bound() {
                    let predicate = validating_predicate();
                    let bounds = AgeBounds::new(Date { year: 2026, month: 12, day: 19 }, 18);
                    let public = PublicInput::new_with_bounds(
                        Date { year: 2026, month: 5, day: 19 },
                        bounds.max_supported_age_years + 1,
                        bounds,
                    );
                    let error = predicate.prove(&public, &dob(2000, 1, 1)).unwrap_err();
                    assert!(matches!(error, Error::Input(AgeInputError::Invalid(ref m)) if m.contains("over 18")));
                }

                #[test]
                fn no_validation_underage_fails_capacity_check() {
                    let predicate = non_validating_predicate();
                    let error = predicate.prove(&setup_today(18), &dob(2008, 5, 20)).unwrap_err();
                    assert!(matches!(error, Error::Input(AgeInputError::Invalid(_))));
                }

                #[test]
                fn verification_fails_on_mutated_proof() {
                    let predicate = validating_predicate();
                    let mut proof = predicate.prove(&setup_today(18), &dob(2000, 1, 1)).unwrap();
                    proof.public.min_age_years = 21;
                    assert!(matches!(predicate.verify(&proof), Err(Error::Verification(_))));
                }

                // --- Calendar validity ---

                #[test]
                fn proves_and_verifies_feb29_in_leap_year() {
                    // Feb 29 is valid in a leap year; this also exercises the leap-year branch
                    // of the calendar lookup
                    let predicate = validating_predicate();
                    let proof = predicate.prove(&setup_today(18), &dob(2000, 2, 29)).unwrap();
                    predicate.verify(&proof).unwrap();
                }

                #[test]
                fn circuit_rejects_day_exceeding_month_maximum() {
                    // April has 30 days. Day 31 passes Date::validate (accepts 1..=31 blindly)
                    // but the valid-day lookup in the circuit must reject it. The mismatched
                    // logup sums only manifest at verify time, not during proving.
                    let predicate = non_validating_predicate();
                    let proof = predicate.prove(&setup_today(18), &dob(1990, 4, 31)).unwrap();
                    assert!(predicate.verify(&proof).is_err());
                }

                #[test]
                fn circuit_rejects_feb29_in_non_leap_year() {
                    // 2005 is not a leap year so Feb 29 does not exist. Day 29 passes
                    // Date::validate but the calendar lookup maps Feb 2005 to max_days=28,
                    // so (28, 29) is not in the valid-day table. Logup sums detected at verify.
                    let predicate = non_validating_predicate();
                    let proof = predicate.prove(&setup_today(18), &dob(2005, 2, 29)).unwrap();
                    assert!(predicate.verify(&proof).is_err());
                }

                // --- Boundary cases ---

                #[test]
                fn proves_and_verifies_dob_at_min_supported_year() {
                    // year_offset = 0, year_bound_slack = year_span: lower bound of the year range
                    let predicate = validating_predicate();
                    let proof = predicate.prove(&setup_today(18), &dob(1906, 1, 1)).unwrap();
                    predicate.verify(&proof).unwrap();
                }

                #[test]
                fn proves_and_verifies_with_zero_min_age() {
                    // min_age = 0 and DOB = current_date: age_slack = 0, year_offset = year_span
                    let predicate = validating_predicate();
                    let public = PublicInput::new(Date { year: 2026, month: 5, day: 19 }, 0);
                    let proof = predicate.prove(&public, &dob(2026, 5, 19)).unwrap();
                    predicate.verify(&proof).unwrap();
                }

                // --- Proof mutation ---

                #[test]
                fn verification_fails_on_mutated_current_date() {
                    // Shifting the current date forward changes the cutoff constraint
                    let predicate = validating_predicate();
                    let mut proof = predicate.prove(&setup_today(18), &dob(2000, 1, 1)).unwrap();
                    proof.public.current.year += 1;
                    assert!(predicate.verify(&proof).is_err());
                }

                #[test]
                fn verification_fails_on_mutated_bounds() {
                    // Changing min_supported_year changes the table_index computation in the
                    // circuit constraint, so the committed witness no longer satisfies the AIR
                    let predicate = validating_predicate();
                    let mut proof = predicate.prove(&setup_today(18), &dob(2000, 1, 1)).unwrap();
                    proof.public.bounds.min_supported_year -= 1;
                    assert!(predicate.verify(&proof).is_err());
                }

                #[test]
                fn verification_fails_on_mutated_claimed_sum() {
                    // Negating age_claimed_sum breaks the global logup balance check
                    let predicate = validating_predicate();
                    let mut proof = predicate.prove(&setup_today(18), &dob(2000, 1, 1)).unwrap();
                    proof.age_claimed_sum = -proof.age_claimed_sum;
                    assert!(predicate.verify(&proof).is_err());
                }
            }
        };
    }

    age_predicate_tests!(
        range_check,
        AgeRangeCheck,
        AgeRangeCheck::new(PcsConfig::default()),
        AgeRangeCheck::new_with_input_validation(PcsConfig::default(), false)
    );

    age_predicate_tests!(
        bit_decomposition,
        AgeBitDecomposition,
        AgeBitDecomposition::new(PcsConfig::default()),
        AgeBitDecomposition::new_with_input_validation(PcsConfig::default(), false)
    );
}
