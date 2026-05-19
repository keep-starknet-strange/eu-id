use crate::utils::{bit_sum, constrain_bits, field_const, read_bits};
use num_traits::Zero;
use serde::{Deserialize, Serialize};
use stwo::core::channel::Channel;
use stwo::core::fields::m31::{BaseField, P as M31_MODULUS};
use stwo::core::fields::qm31::QM31;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;
use stwo::core::verifier::VerificationError;
use stwo::prover::ProvingError;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, TraceLocationAllocator,
};
use utils::read_bits_dynamic;
use crate::utils;

pub(crate) const MONTH_OFFSET_BITS: usize = 4;
pub(crate) const DAY_OFFSET_BITS: usize = 5;

pub(crate) const DATE_VALUE_COLUMNS: usize = 4;

pub(crate) const DATE_MONTH_BASE: u32 = 32;
pub(crate) const DATE_YEAR_BASE: u32 = 512;
pub(crate) const MAX_FIELD_DATE_KEY: u32 = M31_MODULUS - 1;

pub(crate) const DEFAULT_MIN_SUPPORTED_YEAR: u32 = 1900;
pub(crate) const DEFAULT_MAX_SUPPORTED_YEAR: u32 = 2100;
pub(crate) const DEFAULT_MAX_SUPPORTED_AGE_YEARS: u32 = 150;

pub(crate) const AGE_CONSTRAINT_LOG_DEGREE: u32 = 1;
pub(crate) const MIN_AGE_TRACE_LOG_SIZE: u32 = 5;

/// Bounds that define the age predicate's accepted input domain.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AgeBounds {
    pub min_supported_year: u32,
    pub max_supported_year: u32,
    pub max_supported_age_years: u32,
}

impl Default for AgeBounds {
    fn default() -> Self {
        Self {
            min_supported_year: DEFAULT_MIN_SUPPORTED_YEAR,
            max_supported_year: DEFAULT_MAX_SUPPORTED_YEAR,
            max_supported_age_years: DEFAULT_MAX_SUPPORTED_AGE_YEARS,
        }
    }
}

impl AgeBounds {
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

    pub(crate) fn trace_columns(&self) -> usize {
        DATE_VALUE_COLUMNS
            + self.year_offset_bits()
            + self.year_offset_bits()
            + MONTH_OFFSET_BITS
            + MONTH_OFFSET_BITS
            + DAY_OFFSET_BITS
            + DAY_OFFSET_BITS
            + self.age_slack_bits()
    }

    pub(crate) fn trace_log_size(&self) -> u32 {
        MIN_AGE_TRACE_LOG_SIZE
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
pub struct Setup {
    pub current: Date,
    pub min_age_years: u32,
    pub bounds: AgeBounds,
}

impl Setup {
    pub fn new(current: Date, min_age_years: u32) -> Self {
        Self {
            current,
            min_age_years,
            bounds: AgeBounds::default(),
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
        if !(1..=31).contains(&self.day) {
            return Err(AgeInputError::InvalidDay(self.day));
        }
        Ok(())
    }

    pub fn key(&self) -> u32 {
        utils::date_key(self.year, self.month, self.day)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgeWitness {
    pub setup: Setup,
    pub dob: Date,
    pub cutoff: Date,
    pub age_slack: u32,
}

#[derive(Clone)]
pub(crate) struct AgeClaim {
    pub(crate) setup: Setup,
    pub(crate) log_size: u32,
}

impl AgeClaim {
    pub(crate) fn new(setup: Setup) -> Self {
        Self {
            log_size: setup.bounds.trace_log_size(),
            setup,
        }
    }

    pub(crate) fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.setup.current.year as u64);
        channel.mix_u64(self.setup.current.month as u64);
        channel.mix_u64(self.setup.current.day as u64);
        channel.mix_u64(self.setup.min_age_years as u64);
        channel.mix_u64(self.setup.bounds.min_supported_year as u64);
        channel.mix_u64(self.setup.bounds.max_supported_year as u64);
        channel.mix_u64(self.setup.bounds.max_supported_age_years as u64);
        channel.mix_u64(self.log_size as u64);
    }

    pub(crate) fn into_component(self) -> AgeComponent {
        AgeComponent::new(
            &mut TraceLocationAllocator::default(),
            self.clone(),
            QM31::zero(),
        )
    }
}

impl FrameworkEval for AgeClaim {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + AGE_CONSTRAINT_LOG_DEGREE
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let dob_year = eval.next_trace_mask();
        let dob_month = eval.next_trace_mask();
        let dob_day = eval.next_trace_mask();
        let age_slack = eval.next_trace_mask();

        let bounds = self.setup.bounds;
        let year_offset_bits = read_bits_dynamic::<E>(&mut eval, bounds.year_offset_bits());
        let year_bound_slack_bits = read_bits_dynamic::<E>(&mut eval, bounds.year_offset_bits());
        let month_offset_bits = read_bits::<E, MONTH_OFFSET_BITS>(&mut eval);
        let month_bound_slack_bits = read_bits::<E, MONTH_OFFSET_BITS>(&mut eval);
        let day_offset_bits = read_bits::<E, DAY_OFFSET_BITS>(&mut eval);
        let day_bound_slack_bits = read_bits::<E, DAY_OFFSET_BITS>(&mut eval);
        let age_slack_bits = read_bits_dynamic::<E>(&mut eval, bounds.age_slack_bits());

        constrain_bits(&mut eval, &year_offset_bits);
        constrain_bits(&mut eval, &year_bound_slack_bits);
        constrain_bits(&mut eval, &month_offset_bits);
        constrain_bits(&mut eval, &month_bound_slack_bits);
        constrain_bits(&mut eval, &day_offset_bits);
        constrain_bits(&mut eval, &day_bound_slack_bits);
        constrain_bits(&mut eval, &age_slack_bits);

        let year_offset = bit_sum::<E>(&year_offset_bits);
        let year_bound_slack = bit_sum::<E>(&year_bound_slack_bits);
        let month_offset = bit_sum::<E>(&month_offset_bits);
        let month_bound_slack = bit_sum::<E>(&month_bound_slack_bits);
        let day_offset = bit_sum::<E>(&day_offset_bits);
        let day_bound_slack = bit_sum::<E>(&day_bound_slack_bits);
        let age_slack_from_bits = bit_sum::<E>(&age_slack_bits);

        eval.add_constraint(
            dob_year.clone() - field_const::<E>(bounds.min_supported_year) - year_offset.clone(),
        );
        eval.add_constraint(field_const::<E>(bounds.year_span()) - year_offset - year_bound_slack);
        eval.add_constraint(dob_month.clone() - field_const::<E>(1) - month_offset.clone());
        eval.add_constraint(field_const::<E>(11) - month_offset - month_bound_slack);
        eval.add_constraint(dob_day.clone() - field_const::<E>(1) - day_offset.clone());
        eval.add_constraint(field_const::<E>(30) - day_offset - day_bound_slack);
        eval.add_constraint(age_slack.clone() - age_slack_from_bits);

        let cutoff_key = self.setup.cutoff_date().key();
        let dob_key = dob_year * BaseField::from_u32_unchecked(DATE_YEAR_BASE)
            + dob_month * BaseField::from_u32_unchecked(DATE_MONTH_BASE)
            + dob_day;

        eval.add_constraint(field_const::<E>(cutoff_key) - dob_key - age_slack);

        eval
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AgeProof {
    pub setup: Setup,
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
}

type AgeComponent = FrameworkComponent<AgeClaim>;

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
