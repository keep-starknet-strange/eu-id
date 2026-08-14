//! Translation from the SDK's [`ProductPublicStatementV2`] to the production mdoc
//! prover's public [`Policy`].
//!
//! The mapping is deterministic and side-effect-free. Both proving and
//! verification derive the same policy from the same public request, so neither
//! depends on private mdoc values.
//!
//! `And` proves both predicates. `Age` neutralizes nationality with the
//! universal assigned-country set. `Nat` neutralizes age with `min_age = 0`.

use eu_id_prover::{Date, Policy};

use crate::{ProductPublicStatementV2, ZkError};

/// Build a [`ZkError::InvalidInput`] with an actionable message.
fn invalid(msg: impl Into<String>) -> ZkError {
    ZkError::InvalidInput(msg.into())
}

/// Map a [`ProductPublicStatementV2`] to the prover's [`Policy`].
///
/// It uses only public request values. Proving and verification therefore build
/// the same policy without reading credential attributes.
pub(crate) fn to_policy(statement: &ProductPublicStatementV2) -> Result<Policy, ZkError> {
    let mode = statement.predicate_mode;

    let timestamp =
        eu_id_prover::mdoc::utc_timestamp_from_epoch_seconds(statement.now_epoch_seconds)
            .map_err(|_| invalid("now_epoch_seconds is outside the supported date range"))?;
    let current = Date {
        year: u32::from(timestamp.year),
        month: u32::from(timestamp.month),
        day: u32::from(timestamp.day),
    };

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        PredicateMode, PRODUCT_DOCTYPE, PRODUCT_NAMESPACE, PRODUCT_SPEC_ID,
        PRODUCT_STATEMENT_VERSION,
    };
    use eu_id_prover::product_profile::PRODUCT_PROFILE_ID;

    const TEST_NOW_EPOCH_SECONDS: u64 = 1_577_836_800;

    fn date(year: u32, month: u32, day: u32) -> Date {
        Date { year, month, day }
    }

    fn statement_with(mode: PredicateMode) -> ProductPublicStatementV2 {
        ProductPublicStatementV2 {
            spec_id: PRODUCT_SPEC_ID.to_string(),
            version: PRODUCT_STATEMENT_VERSION,
            profile_id: PRODUCT_PROFILE_ID.to_string(),
            circuit_hash: "00".repeat(32),
            root_policy_hash: vec![0; 32],
            doctype: PRODUCT_DOCTYPE.to_string(),
            namespace: PRODUCT_NAMESPACE.to_string(),
            issuer_public_key_x: vec![0x11; 32],
            issuer_public_key_y: vec![0x22; 32],
            // 2020-01-01T00:00:00Z.
            now_epoch_seconds: TEST_NOW_EPOCH_SECONDS,
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
