use crate::nat::nationalities::Nationality;
use crate::nat::types::{Error, InputError, PrivateInput, PublicInput, Witness};
use strum::IntoEnumIterator;
use stwo::core::pcs::PcsConfig;

pub struct NationalityPredicate {
    pub pcs_config: PcsConfig,
}

impl NationalityPredicate {
    pub fn new(pcs_config: PcsConfig) -> Self {
        Self { pcs_config }
    }

    pub(crate) fn validate(&self, public: &PublicInput) -> Result<(), Error> {
        if public.acceptable.len() < 2 {
            return Err(InputError::AcceptableSetTooSmall.into());
        }
        // Nationality enum variants are ordered by numeric code (iso-preset sorts by code).
        let valid_codes: Vec<u32> = Nationality::iter().map(|n| n as u32).collect();
        for &code in &public.acceptable {
            if valid_codes.binary_search(&code).is_err() {
                return Err(InputError::InvalidNationalityCode(code).into());
            }
        }
        Ok(())
    }

    pub(crate) fn witness(
        &self,
        public: &PublicInput,
        private: &PrivateInput,
    ) -> Result<Witness, Error> {
        for &nat in &private.nationalities {
            if let Ok(row_index) = public.acceptable.binary_search(&nat) {
                return Ok(Witness {
                    public: public.clone(),
                    nationality: nat,
                    nat_index: row_index,
                });
            }
        }
        Err(InputError::NoMatch.into())
    }
}
