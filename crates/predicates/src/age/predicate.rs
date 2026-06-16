use crate::age::types::{AgeInputError, DateOfBirth, Error, PublicInput, Witness};
use stwo::core::pcs::PcsConfig;

pub struct AgePredicate {
    pub pcs_config: PcsConfig,
    pub validate_input: bool,
}

impl AgePredicate {
    pub fn new(pcs_config: PcsConfig) -> Self {
        Self {
            pcs_config,
            validate_input: true,
        }
    }

    #[cfg(test)]
    pub(crate) fn new_with_input_validation(pcs_config: PcsConfig, validate_input: bool) -> Self {
        Self {
            pcs_config,
            validate_input,
        }
    }

    pub(crate) fn validate(&self, public: &PublicInput) -> Result<(), Error> {
        public.bounds.validate()?;

        if !self.validate_input {
            return Ok(());
        }

        public.current.validate(&public.bounds)?;

        if public.min_age_years > public.bounds.max_supported_age_years {
            return Err(AgeInputError::Invalid(format!(
                "age check cannot be for people over {} years old",
                public.bounds.max_supported_age_years
            ))
            .into());
        }

        let cutoff_year = public
            .current
            .year
            .checked_sub(public.min_age_years)
            .ok_or(AgeInputError::Invalid(String::from(
                "current year is smaller than minimum age",
            )))?;

        if cutoff_year < public.bounds.min_supported_year {
            return Err(AgeInputError::Invalid(format!(
                "age check cannot apply to people born before {}",
                public.bounds.min_supported_year
            ))
            .into());
        }

        Ok(())
    }

    pub(crate) fn witness(
        &self,
        public: &PublicInput,
        private: &DateOfBirth,
    ) -> Result<Witness, Error> {
        let dob = private.0;

        if self.validate_input {
            dob.validate(&public.bounds)?;
        }

        let cutoff = public.cutoff_date();
        let cutoff_num = cutoff.key();
        let dob_num = dob.key();

        if self.validate_input && dob_num > cutoff_num {
            return Err(AgeInputError::UnderAge.into());
        }

        let slack = cutoff_num.wrapping_sub(dob_num);
        // Needs to always be validated
        let slack_capacity = 1u64
            .checked_shl(public.bounds.age_slack_bits() as u32)
            .ok_or(AgeInputError::Invalid(String::from(
                "date difference bit-width exceeds supported range",
            )))?;
        if u64::from(slack) >= slack_capacity {
            return Err(AgeInputError::Invalid(String::from(
                "date difference exceeds supported range",
            ))
            .into());
        }

        Ok(Witness {
            public: *public,
            dob,
            cutoff,
            age_slack: slack,
        })
    }
}
