use crate::age::calendar::max_days_at;
use crate::utils;
use serde::{Deserialize, Serialize};
use stwo::core::channel::Channel;
use stwo::core::fields::m31::P as M31_MODULUS;
use stwo::core::fields::qm31::QM31;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;
use stwo::core::verifier::VerificationError;
use stwo::prover::ProvingError;

pub(crate) const DATE_MONTH_BASE: u32 = 32;
pub(crate) const DATE_YEAR_BASE: u32 = 512;
pub(crate) const MAX_FIELD_DATE_KEY: u32 = M31_MODULUS - 1;

pub(crate) const MAX_SUPPORTED_YEARS: u32 = 120;


/// Bounds that define the age predicate's accepted input domain.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AgeBounds {
    pub min_supported_year: u32,
    pub max_supported_year: u32,
    pub max_supported_age_years: u32,
}

impl AgeBounds {

    pub(crate) fn new(from_current: Date, max_supported_years_diff: u32) -> Self {
        Self {
            min_supported_year: from_current.year - max_supported_years_diff,
            max_supported_year: from_current.year,
            max_supported_age_years: max_supported_years_diff,
        }
    }

    pub(crate) fn validate(&self) -> Result<(), AgeInputError> {
        if self.min_supported_year > self.max_supported_year {
            return Err(AgeInputError::Invalid(format!(
                "min supported year {} exceeds max supported year {}",
                self.min_supported_year, self.max_supported_year
            )));
        }
        if self.max_supported_age_years > self.year_span() {
            return Err(AgeInputError::Invalid(format!(
                "max supported age {} exceeds supported year span {}",
                self.max_supported_age_years,
                self.year_span()
            )));
        }
        if self.max_date_key_checked().is_none() {
            return Err(AgeInputError::Invalid(format!(
                "max supported year {} cannot be represented as a date key",
                self.max_supported_year
            )));
        }
        if self.max_date_key() > MAX_FIELD_DATE_KEY {
            return Err(AgeInputError::Invalid(format!(
                "max supported year {} exceeds the M31 date-key range",
                self.max_supported_year
            )));
        }
        Ok(())
    }

    pub(crate) const fn year_span(&self) -> u32 {
        self.max_supported_year - self.min_supported_year
    }

    pub(crate) fn year_offset_bits(&self) -> usize {
        utils::bits_needed(self.year_span())
    }

    pub(crate) fn age_slack_bits(&self) -> usize {
        utils::bits_needed(self.max_date_key() - self.min_date_key())
    }

    fn min_date_key(&self) -> u32 {
        utils::date_key(self.min_supported_year, 1, 1)
    }

    fn max_date_key(&self) -> u32 {
        self.max_date_key_checked()
            .expect("AgeBounds::validate ensures date-key arithmetic fits in u32")
    }

    fn max_date_key_checked(&self) -> Option<u32> {
        utils::date_key_checked(self.max_supported_year, 12, 31)
    }
}

/// Public statement for an age proof.
///
/// The prover proves knowledge of a private date of birth whose age is at least
/// `min_age_years` on `current_date`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PublicInput {
    pub current: Date,
    pub min_age_years: u32,
    pub bounds: AgeBounds,
}

impl PublicInput {
    pub fn new(current: Date, min_age_years: u32) -> Self {
        Self {
            current,
            min_age_years,
            bounds: AgeBounds::new(current, MAX_SUPPORTED_YEARS),
        }
    }

    pub fn new_with_bounds(current: Date, min_age_years: u32, bounds: AgeBounds) -> Self {
        Self {
            current,
            min_age_years,
            bounds,
        }
    }

    pub fn cutoff_date(&self) -> Date {
        Date {
            year: self.current.year - self.min_age_years,
            month: self.current.month,
            day: self.current.day,
        }
    }

    pub(crate) fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.current.year as u64);
        channel.mix_u64(self.current.month as u64);
        channel.mix_u64(self.current.day as u64);
        channel.mix_u64(self.min_age_years as u64);
        channel.mix_u64(self.bounds.min_supported_year as u64);
        channel.mix_u64(self.bounds.max_supported_year as u64);
        channel.mix_u64(self.bounds.max_supported_age_years as u64);
    }
}

/// Private date of birth witness supplied only to the prover.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DateOfBirth(pub Date);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Date {
    pub year: u32,
    pub month: u32,
    pub day: u32,
}

impl Date {
    pub fn validate(&self, bounds: &AgeBounds) -> Result<(), AgeInputError> {
        if !(bounds.min_supported_year..=bounds.max_supported_year).contains(&self.year) {
            return Err(AgeInputError::InvalidYear {
                year: self.year,
                min: bounds.min_supported_year,
                max: bounds.max_supported_year,
            });
        }
        if !(1..=12).contains(&self.month) {
            return Err(AgeInputError::InvalidMonth(self.month));
        }
        let max_days = max_days_at(self.month, self.year);
        if !(1..=max_days).contains(&self.day) {
            return Err(AgeInputError::InvalidDay(self.day));
        }
        Ok(())
    }

    pub fn key(&self) -> u32 {
        utils::date_key(self.year, self.month, self.day)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Witness {
    pub public: PublicInput,
    pub dob: Date,
    pub cutoff: Date,
    pub age_slack: u32,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AgeBitDecompositionProof {
    pub public: PublicInput,
    pub age_claimed_sum: QM31,
    pub calendar_table_claimed_sum: QM31,
    pub valid_day_table_claimed_sum: QM31,
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AgeRangeCheckProof {
    pub public: PublicInput,
    pub age_claimed_sum: QM31,
    pub calendar_table_claimed_sum: QM31,
    pub valid_day_table_claimed_sum: QM31,
    pub day_delta_claimed_sum: QM31,
    pub month_delta_claimed_sum: QM31,
    pub year_delta_claimed_sum: QM31,
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
}

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    Input(#[from] AgeInputError),
    #[error(transparent)]
    Proving(#[from] ProvingError),
    #[error(transparent)]
    Verification(#[from] VerificationError),
}

#[derive(Debug, thiserror::Error)]
pub enum AgeInputError {
    #[error("Invalid year: expected {min}..={max}, got {year}")]
    InvalidYear { year: u32, min: u32, max: u32 },
    #[error("Invalid month: expected 1..=12, got {0}")]
    InvalidMonth(u32),
    #[error("Invalid day: expected 1..=31, got {0}")]
    InvalidDay(u32),
    #[error("Invalid input: {0}")]
    Invalid(String),
    #[error("User is underage")]
    UnderAge,
}