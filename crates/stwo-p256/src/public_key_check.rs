use stwo::core::fields::m31::M31;

use crate::constants::{P256_B, P256_MODULUS};
use crate::field_ops::{add_mod_witness, sub_mod_witness};
use crate::fp_solinas::{FpSolinasError, FpSolinasMulTrace};
use crate::limbs::P256M31BigInt;
use crate::public_inputs::{PublicEcdsaInputClaim, PublicEcdsaInstance};
use crate::types::U256;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicKeyOnCurveClaim {
    pub rows: Vec<PublicKeyOnCurveRow>,
}

impl PublicKeyOnCurveClaim {
    pub fn from_public_inputs(
        public_inputs: &PublicEcdsaInputClaim,
    ) -> Result<Self, PublicKeyOnCurveError> {
        let rows = public_inputs
            .instances
            .iter()
            .map(PublicKeyOnCurveRow::from_public_input)
            .collect::<Result<Vec<_>, _>>()?;
        let claim = Self { rows };
        claim.verify()?;
        Ok(claim)
    }

    pub fn verify(&self) -> Result<(), PublicKeyOnCurveError> {
        for row in &self.rows {
            row.verify()?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicKeyOnCurveRow {
    pub sig_id: M31,
    pub x: P256M31BigInt,
    pub y: P256M31BigInt,
    pub y_squared: FpSolinasMulTrace,
    pub x_squared: FpSolinasMulTrace,
    pub x_cubed: FpSolinasMulTrace,
    pub three_x: FpSolinasMulTrace,
    pub rhs: P256M31BigInt,
}

impl PublicKeyOnCurveRow {
    fn from_public_input(public: &PublicEcdsaInstance<M31>) -> Result<Self, PublicKeyOnCurveError> {
        require_field_element("pub_x", &public.pub_x)?;
        require_field_element("pub_y", &public.pub_y)?;
        let x = public.pub_x.to_u256();
        let y = public.pub_y.to_u256();
        let y_squared = FpSolinasMulTrace::new(&y, &y)?;
        let x_squared = FpSolinasMulTrace::new(&x, &x)?;
        let x_cubed = FpSolinasMulTrace::new(&x_squared.result.to_u256(), &x)?;
        let three_x = FpSolinasMulTrace::new(&U256::from_le_u64s(&[3, 0, 0, 0]), &x)?;
        let modulus = U256::from_le_u64s(&P256_MODULUS);
        let x3_minus_3x = sub_mod_witness(
            &x_cubed.result.to_u256(),
            &three_x.result.to_u256(),
            &modulus,
        )
        .result
        .to_u256();
        let rhs = add_mod_witness(&x3_minus_3x, &U256::from_le_u64s(&P256_B), &modulus)
            .result
            .to_u256();
        if y_squared.result.to_u256() != rhs {
            return Err(PublicKeyOnCurveError::PointOffCurve {
                sig_id: public.sig_id.0,
            });
        }

        Ok(Self {
            sig_id: public.sig_id,
            x: public.pub_x.clone(),
            y: public.pub_y.clone(),
            y_squared,
            x_squared,
            x_cubed,
            three_x,
            rhs: P256M31BigInt::from_u256(&rhs),
        })
    }

    pub fn verify(&self) -> Result<(), PublicKeyOnCurveError> {
        require_field_element("pub_x", &self.x)?;
        require_field_element("pub_y", &self.y)?;
        self.y_squared.verify()?;
        self.x_squared.verify()?;
        self.x_cubed.verify()?;
        self.three_x.verify()?;

        if self.y_squared.lhs != self.y || self.y_squared.rhs != self.y {
            return Err(PublicKeyOnCurveError::TraceInputMismatch {
                sig_id: self.sig_id.0,
                trace: "y_squared",
            });
        }
        if self.x_squared.lhs != self.x || self.x_squared.rhs != self.x {
            return Err(PublicKeyOnCurveError::TraceInputMismatch {
                sig_id: self.sig_id.0,
                trace: "x_squared",
            });
        }
        if self.x_cubed.lhs != self.x_squared.result || self.x_cubed.rhs != self.x {
            return Err(PublicKeyOnCurveError::TraceInputMismatch {
                sig_id: self.sig_id.0,
                trace: "x_cubed",
            });
        }
        if self.three_x.lhs != P256M31BigInt::from_u256(&U256::from_le_u64s(&[3, 0, 0, 0]))
            || self.three_x.rhs != self.x
        {
            return Err(PublicKeyOnCurveError::TraceInputMismatch {
                sig_id: self.sig_id.0,
                trace: "three_x",
            });
        }

        let modulus = U256::from_le_u64s(&P256_MODULUS);
        let x3_minus_3x = sub_mod_witness(
            &self.x_cubed.result.to_u256(),
            &self.three_x.result.to_u256(),
            &modulus,
        )
        .result
        .to_u256();
        let rhs = add_mod_witness(&x3_minus_3x, &U256::from_le_u64s(&P256_B), &modulus)
            .result
            .to_u256();
        if self.rhs.to_u256() != rhs {
            return Err(PublicKeyOnCurveError::RhsMismatch {
                sig_id: self.sig_id.0,
            });
        }
        if self.y_squared.result.to_u256() != rhs {
            return Err(PublicKeyOnCurveError::PointOffCurve {
                sig_id: self.sig_id.0,
            });
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PublicKeyOnCurveError {
    FieldElementOutOfRange { field: &'static str },
    FpSolinas(FpSolinasError),
    TraceInputMismatch { sig_id: u32, trace: &'static str },
    RhsMismatch { sig_id: u32 },
    PointOffCurve { sig_id: u32 },
}

impl From<FpSolinasError> for PublicKeyOnCurveError {
    fn from(value: FpSolinasError) -> Self {
        Self::FpSolinas(value)
    }
}

fn require_field_element(
    field: &'static str,
    value: &P256M31BigInt,
) -> Result<(), PublicKeyOnCurveError> {
    if is_less_than_modulus(value) {
        Ok(())
    } else {
        Err(PublicKeyOnCurveError::FieldElementOutOfRange { field })
    }
}

fn is_less_than_modulus(value: &P256M31BigInt) -> bool {
    let modulus = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS));
    for (lhs, rhs) in value.limbs().iter().zip(modulus.limbs()).rev() {
        match lhs.0.cmp(&rhs.0) {
            core::cmp::Ordering::Less => return true,
            core::cmp::Ordering::Greater => return false,
            core::cmp::Ordering::Equal => {}
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY};
    use crate::types::{AffinePoint, EcdsaVerifyInput, Signature};

    fn public_claim() -> PublicEcdsaInputClaim {
        PublicEcdsaInputClaim::from_inputs(&[EcdsaVerifyInput {
            message_hash: scalar(42),
            signature: Signature {
                r: scalar(77),
                s: scalar(1),
            },
            public_key: AffinePoint {
                x: U256::from_le_u64s(&P256_GX),
                y: U256::from_le_u64s(&P256_GY),
            },
        }])
    }

    fn scalar(value: u64) -> U256 {
        U256::from_le_u64s(&[value, 0, 0, 0])
    }

    #[test]
    fn public_key_on_curve_claim_accepts_generator() {
        let claim =
            PublicKeyOnCurveClaim::from_public_inputs(&public_claim()).expect("valid public key");

        claim.verify().expect("claim verifies");
        assert_eq!(claim.rows.len(), 1);
    }

    #[test]
    fn public_key_on_curve_claim_rejects_mutated_y() {
        let mut public = public_claim();
        public.instances[0].pub_y = P256M31BigInt::from_u256(&scalar(1));

        let err = PublicKeyOnCurveClaim::from_public_inputs(&public)
            .expect_err("off-curve public key must fail");

        assert!(matches!(err, PublicKeyOnCurveError::PointOffCurve { .. }));
    }

    #[test]
    fn public_key_on_curve_claim_detects_mutated_trace_input() {
        let mut claim =
            PublicKeyOnCurveClaim::from_public_inputs(&public_claim()).expect("valid public key");
        claim.rows[0].x_squared.rhs = P256M31BigInt::from_u256(&scalar(2));

        let err = claim.verify().expect_err("mutated trace input must fail");

        assert!(matches!(
            err,
            PublicKeyOnCurveError::FpSolinas(FpSolinasError::RawProductMismatch)
                | PublicKeyOnCurveError::TraceInputMismatch { .. }
        ));
    }

    #[test]
    fn public_key_on_curve_claim_detects_mutated_rhs() {
        let mut claim =
            PublicKeyOnCurveClaim::from_public_inputs(&public_claim()).expect("valid public key");
        claim.rows[0].rhs = P256M31BigInt::zero();

        let err = claim.verify().expect_err("mutated rhs must fail");

        assert!(matches!(err, PublicKeyOnCurveError::RhsMismatch { .. }));
    }
}
