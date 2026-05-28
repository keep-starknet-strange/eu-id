use std::fmt;

use stwo::core::channel::Channel;
use stwo::core::fields::m31::M31;

use crate::constants::{P256_GX, P256_GY};
use crate::limbs::P256M31BigInt;
use crate::types::U256;

use super::setup_air::{ScalarSetupClaim, ScalarSetupOutput};

pub const CERT_ID_U1_GENERATOR: u32 = 0;
pub const CERT_ID_U2_PUBLIC_KEY: u32 = 1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertScalarInputClaim {
    pub rows: Vec<CertScalarInputRow>,
}

impl CertScalarInputClaim {
    pub fn from_scalar_setup(
        scalar_setup: &ScalarSetupClaim,
    ) -> Result<Self, CertScalarInputError> {
        let mut rows = Vec::with_capacity(2 * scalar_setup.rows.len());
        for row in &scalar_setup.rows {
            rows.push(CertScalarInputRow::from_scalar_setup_output(
                &row.output,
                CertificateScalarSource::U1Generator,
            ));
            rows.push(CertScalarInputRow::from_scalar_setup_output(
                &row.output,
                CertificateScalarSource::U2PublicKey,
            ));
        }
        let claim = Self { rows };
        claim.verify()?;
        Ok(claim)
    }

    pub fn verify(&self) -> Result<(), CertScalarInputError> {
        for row in &self.rows {
            row.verify()?;
        }
        Ok(())
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.rows.len() as u64);
        for row in &self.rows {
            channel.mix_u64(row.sig_id.0 as u64);
            channel.mix_u64(row.cert_id.0 as u64);
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertScalarInputRow {
    pub sig_id: M31,
    pub cert_id: M31,
    pub scalar: P256M31BigInt,
    pub base_x: P256M31BigInt,
    pub base_y: P256M31BigInt,
    pub base_inf: M31,
    pub scalar_is_zero: M31,
    pub scalar_is_nonzero: M31,
    pub cert_active: M31,
    pub cert_zero_active: M31,
}

impl CertScalarInputRow {
    pub fn from_scalar_setup_output(
        output: &ScalarSetupOutput<M31>,
        source: CertificateScalarSource,
    ) -> Self {
        let scalar = match source {
            CertificateScalarSource::U1Generator => output.u1.clone(),
            CertificateScalarSource::U2PublicKey => output.u2.clone(),
        };
        let scalar_is_zero = m31_bool(is_zero_bigint(&scalar));
        let scalar_is_nonzero = m31_bool(!is_zero_bigint(&scalar));
        Self {
            sig_id: output.sig_id,
            cert_id: M31::from_u32_unchecked(source.cert_id()),
            base_x: source.base_x(output),
            base_y: source.base_y(output),
            base_inf: M31::from_u32_unchecked(0),
            scalar,
            scalar_is_zero,
            scalar_is_nonzero,
            cert_active: scalar_is_nonzero,
            cert_zero_active: scalar_is_zero,
        }
    }

    pub fn verify(&self) -> Result<(), CertScalarInputError> {
        require_bool("scalar_is_zero", self.scalar_is_zero)?;
        require_bool("scalar_is_nonzero", self.scalar_is_nonzero)?;
        require_bool("cert_active", self.cert_active)?;
        require_bool("cert_zero_active", self.cert_zero_active)?;
        require_eq(
            "scalar_is_zero + scalar_is_nonzero",
            self.scalar_is_zero.0 + self.scalar_is_nonzero.0,
            1,
        )?;
        let scalar_zero = is_zero_bigint(&self.scalar);
        require_eq(
            "scalar_is_zero",
            self.scalar_is_zero.0,
            u32::from(scalar_zero),
        )?;
        require_eq(
            "scalar_is_nonzero",
            self.scalar_is_nonzero.0,
            u32::from(!scalar_zero),
        )?;
        require_eq("cert_active", self.cert_active.0, self.scalar_is_nonzero.0)?;
        require_eq(
            "cert_zero_active",
            self.cert_zero_active.0,
            self.scalar_is_zero.0,
        )?;
        require_eq("base_inf", self.base_inf.0, 0)?;
        if self.cert_id.0 == CERT_ID_U2_PUBLIC_KEY && scalar_zero {
            return Err(CertScalarInputError::UnexpectedZeroU2 {
                sig_id: self.sig_id.0,
            });
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CertificateScalarSource {
    U1Generator,
    U2PublicKey,
}

impl CertificateScalarSource {
    pub const fn cert_id(self) -> u32 {
        match self {
            Self::U1Generator => CERT_ID_U1_GENERATOR,
            Self::U2PublicKey => CERT_ID_U2_PUBLIC_KEY,
        }
    }

    fn base_x(self, output: &ScalarSetupOutput<M31>) -> P256M31BigInt {
        match self {
            Self::U1Generator => P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_GX)),
            Self::U2PublicKey => output.pub_x.clone(),
        }
    }

    fn base_y(self, output: &ScalarSetupOutput<M31>) -> P256M31BigInt {
        match self {
            Self::U1Generator => P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_GY)),
            Self::U2PublicKey => output.pub_y.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CertScalarInputError {
    FlagMismatch {
        field: &'static str,
        expected: u32,
        actual: u32,
    },
    NonBooleanFlag {
        field: &'static str,
        actual: u32,
    },
    UnexpectedZeroU2 {
        sig_id: u32,
    },
}

impl fmt::Display for CertScalarInputError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FlagMismatch {
                field,
                expected,
                actual,
            } => write!(
                f,
                "certificate scalar input mismatch for {field}: expected {expected}, got {actual}"
            ),
            Self::NonBooleanFlag { field, actual } => {
                write!(
                    f,
                    "certificate scalar input flag {field} must be boolean, got {actual}"
                )
            }
            Self::UnexpectedZeroU2 { sig_id } => {
                write!(f, "signature {sig_id} has an unexpected zero u2 scalar")
            }
        }
    }
}

impl std::error::Error for CertScalarInputError {}

fn is_zero_bigint(value: &P256M31BigInt) -> bool {
    value.limbs().iter().all(|limb| limb.0 == 0)
}

fn m31_bool(value: bool) -> M31 {
    M31::from_u32_unchecked(u32::from(value))
}

fn require_bool(field: &'static str, value: M31) -> Result<(), CertScalarInputError> {
    if value.0 <= 1 {
        return Ok(());
    }
    Err(CertScalarInputError::NonBooleanFlag {
        field,
        actual: value.0,
    })
}

fn require_eq(field: &'static str, actual: u32, expected: u32) -> Result<(), CertScalarInputError> {
    if actual == expected {
        return Ok(());
    }
    Err(CertScalarInputError::FlagMismatch {
        field,
        expected,
        actual,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY};
    use crate::public_inputs::{
        public_ecdsa_consumer_claimed_sum, PublicEcdsaInputClaim, PublicEcdsaInstanceRelation,
    };
    use crate::scalar::setup_air::ScalarSetupClaim;
    use crate::types::{AffinePoint, EcdsaVerifyInput, Signature};
    use stwo::core::fields::qm31::SecureField;

    fn test_input(message_hash: U256, r: u64) -> EcdsaVerifyInput {
        EcdsaVerifyInput {
            message_hash,
            signature: Signature {
                r: scalar(r),
                s: scalar(11),
            },
            public_key: AffinePoint {
                x: U256::from_le_u64s(&P256_GX),
                y: U256::from_le_u64s(&P256_GY),
            },
        }
    }

    fn scalar(value: u64) -> U256 {
        U256::from_le_u64s(&[value, 0, 0, 0])
    }

    #[test]
    fn cert_scalar_claim_binds_two_certificates_per_signature() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(scalar(42), 77)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");

        assert_eq!(certs.rows.len(), 2);
        assert_eq!(certs.rows[0].cert_id.0, CERT_ID_U1_GENERATOR);
        assert_eq!(certs.rows[0].scalar, scalar_setup.rows[0].output.u1);
        assert_eq!(
            certs.rows[0].base_x,
            P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_GX))
        );
        assert_eq!(certs.rows[1].cert_id.0, CERT_ID_U2_PUBLIC_KEY);
        assert_eq!(certs.rows[1].scalar, scalar_setup.rows[0].output.u2);
        assert_eq!(certs.rows[1].base_x, scalar_setup.rows[0].output.pub_x);
    }

    #[test]
    fn cert_scalar_claim_allows_u1_zero_branch() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(U256::ZERO, 77)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");

        assert_eq!(certs.rows[0].cert_id.0, CERT_ID_U1_GENERATOR);
        assert_eq!(certs.rows[0].scalar_is_zero.0, 1);
        assert_eq!(certs.rows[0].cert_zero_active.0, 1);
        assert_eq!(certs.rows[0].cert_active.0, 0);
        assert_eq!(certs.rows[1].cert_id.0, CERT_ID_U2_PUBLIC_KEY);
        assert_eq!(certs.rows[1].scalar_is_nonzero.0, 1);
    }

    #[test]
    fn cert_scalar_e2e_keeps_public_logup_balanced() {
        let relation = PublicEcdsaInstanceRelation::dummy();
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(scalar(42), 77)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let public_interaction = public_claim.initial_logup_claim(&relation);
        let vm_consumers =
            public_ecdsa_consumer_claimed_sum(&scalar_setup.public_consumers(), &relation);

        scalar_setup.verify().expect("scalar setup verifies");
        certs.verify().expect("cert inputs verify");
        assert_eq!(
            public_interaction.claimed_sum + vm_consumers,
            SecureField::from(M31::from_u32_unchecked(0))
        );
    }

    #[test]
    fn cert_scalar_claim_rejects_mutated_zero_flag() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(scalar(42), 77)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let mut certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        certs.rows[0].scalar_is_zero = M31::from_u32_unchecked(1);

        let err = certs.verify().expect_err("mutated zero flag must fail");

        assert!(matches!(err, CertScalarInputError::FlagMismatch { .. }));
    }

    #[test]
    fn cert_scalar_claim_rejects_zero_u2() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(U256::ZERO, 77)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let mut certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        certs.rows[1].scalar = P256M31BigInt::zero();
        certs.rows[1].scalar_is_zero = M31::from_u32_unchecked(1);
        certs.rows[1].scalar_is_nonzero = M31::from_u32_unchecked(0);
        certs.rows[1].cert_active = M31::from_u32_unchecked(0);
        certs.rows[1].cert_zero_active = M31::from_u32_unchecked(1);

        let err = certs.verify().expect_err("zero u2 must fail");

        assert!(matches!(err, CertScalarInputError::UnexpectedZeroU2 { .. }));
    }

    #[test]
    fn cert_scalar_claim_mixes_into_transcript() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(scalar(42), 77)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let mut channel = stwo::core::channel::Blake2sM31Channel::default();

        certs.mix_into(&mut channel);
    }
}
