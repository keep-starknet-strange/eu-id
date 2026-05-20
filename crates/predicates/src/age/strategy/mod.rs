pub(crate) mod bit_decomposition;
pub(crate) mod range_check;

#[cfg(test)]
mod tests {
    use super::bit_decomposition::AgeBitDecomposition;
    use super::range_check::AgeRangeCheck;
    use crate::age::types::{AgeBounds, Date, DateOfBirth, Error, PublicInput};
    use crate::predicate::StarkPredicate;
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
