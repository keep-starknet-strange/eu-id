use stwo::core::fields::m31::M31;

use crate::constants::{P256_MODULUS, P256_ORDER};
use crate::curve::{point_add, point_double, scalar_mul};
use crate::fake_glv_chain::{FakeGlvChainCert, FakeGlvChainClaim};
use crate::field_ops::{add_mod_witness, sub_mod_witness};
use crate::prepared_table::PreparedAffinePoint;
use crate::public_inputs::{PublicEcdsaInputClaim, PublicEcdsaInstance};
use crate::scalar::cert_bind::{
    CertScalarInputClaim, CertScalarInputRow, CERT_ID_U1_GENERATOR, CERT_ID_U2_PUBLIC_KEY,
};
use crate::scalar::fake_glv_scalar::{FakeGlvScalarHintClaim, FakeGlvScalarHintRow};
use crate::types::{AffinePoint, U256};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalEcdsaCheckClaim {
    pub rows: Vec<FinalEcdsaCheckRow>,
}

impl FinalEcdsaCheckClaim {
    pub fn from_claims(
        public_inputs: &PublicEcdsaInputClaim,
        cert_inputs: &CertScalarInputClaim,
        fake_glv_scalars: &FakeGlvScalarHintClaim,
        fake_glv_chain: &FakeGlvChainClaim,
    ) -> Result<Self, FinalEcdsaCheckError> {
        let expected_cert_rows = public_inputs.instances.len() * 2;
        if cert_inputs.rows.len() != expected_cert_rows
            || fake_glv_scalars.rows.len() != expected_cert_rows
            || fake_glv_chain.certs.len() != expected_cert_rows
        {
            return Err(FinalEcdsaCheckError::RowCountMismatch {
                public_inputs: public_inputs.instances.len(),
                certs: cert_inputs.rows.len(),
                fake_glv: fake_glv_scalars.rows.len(),
                chain: fake_glv_chain.certs.len(),
            });
        }

        let rows = public_inputs
            .instances
            .iter()
            .enumerate()
            .map(|(sig_index, public)| {
                let cert_index = sig_index * 2;
                FinalEcdsaCheckRow::from_claims(
                    public,
                    &cert_inputs.rows[cert_index],
                    &cert_inputs.rows[cert_index + 1],
                    &fake_glv_scalars.rows[cert_index],
                    &fake_glv_scalars.rows[cert_index + 1],
                    &fake_glv_chain.certs[cert_index],
                    &fake_glv_chain.certs[cert_index + 1],
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let claim = Self { rows };
        claim.verify()?;
        Ok(claim)
    }

    pub fn verify(&self) -> Result<(), FinalEcdsaCheckError> {
        for row in &self.rows {
            row.verify()?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalEcdsaCheckRow {
    pub sig_id: M31,
    pub h1: PreparedAffinePoint,
    pub h2: PreparedAffinePoint,
    pub r_point: PreparedAffinePoint,
    pub r_x_ge_n: M31,
    pub expected_r: crate::limbs::P256M31BigInt,
}

impl FinalEcdsaCheckRow {
    fn from_claims(
        public: &PublicEcdsaInstance<M31>,
        cert_u1: &CertScalarInputRow,
        cert_u2: &CertScalarInputRow,
        fake_glv_u1: &FakeGlvScalarHintRow,
        fake_glv_u2: &FakeGlvScalarHintRow,
        chain_u1: &FakeGlvChainCert,
        chain_u2: &FakeGlvChainCert,
    ) -> Result<Self, FinalEcdsaCheckError> {
        require_cert(public.sig_id, CERT_ID_U1_GENERATOR, cert_u1)?;
        require_cert(public.sig_id, CERT_ID_U2_PUBLIC_KEY, cert_u2)?;
        require_fake_glv(cert_u1, fake_glv_u1)?;
        require_fake_glv(cert_u2, fake_glv_u2)?;
        require_chain(cert_u1, chain_u1)?;
        require_chain(cert_u2, chain_u2)?;

        let h1 = scalar_mul_point(cert_u1)?;
        let h2 = scalar_mul_point(cert_u2)?;
        require_chain_r3_matches_h("u1", &h1, fake_glv_u1, chain_u1)?;
        require_chain_r3_matches_h("u2", &h2, fake_glv_u2, chain_u2)?;

        let r_point = add_optional_points(h1.to_option(), h2.to_option()).ok_or(
            FinalEcdsaCheckError::InfinityFinalR {
                sig_id: public.sig_id.0,
            },
        )?;
        let r_point = PreparedAffinePoint::from_affine(r_point);
        let (r_x_mod_n, r_x_ge_n) = x_mod_order(&r_point.x.to_u256())?;
        if r_x_mod_n != public.r.to_u256() {
            return Err(FinalEcdsaCheckError::SignatureRMismatch {
                sig_id: public.sig_id.0,
            });
        }

        Ok(Self {
            sig_id: public.sig_id,
            h1,
            h2,
            r_point,
            r_x_ge_n: M31::from_u32_unchecked(r_x_ge_n),
            expected_r: public.r.clone(),
        })
    }

    pub fn verify(&self) -> Result<(), FinalEcdsaCheckError> {
        require_bool("r_x_ge_n", self.r_x_ge_n)?;
        self.h1
            .verify()
            .map_err(FinalEcdsaCheckError::PreparedPoint)?;
        self.h2
            .verify()
            .map_err(FinalEcdsaCheckError::PreparedPoint)?;
        self.r_point
            .verify()
            .map_err(FinalEcdsaCheckError::PreparedPoint)?;
        if self.r_point.inf.0 == 1 {
            return Err(FinalEcdsaCheckError::InfinityFinalR {
                sig_id: self.sig_id.0,
            });
        }

        let expected_r_point = add_optional_points(self.h1.to_option(), self.h2.to_option())
            .ok_or(FinalEcdsaCheckError::InfinityFinalR {
                sig_id: self.sig_id.0,
            })?;
        if self.r_point != PreparedAffinePoint::from_affine(expected_r_point) {
            return Err(FinalEcdsaCheckError::FinalRPointMismatch {
                sig_id: self.sig_id.0,
            });
        }

        let (r_x_mod_n, r_x_ge_n) = x_mod_order(&self.r_point.x.to_u256())?;
        if r_x_ge_n != self.r_x_ge_n.0 {
            return Err(FinalEcdsaCheckError::ReductionFlagMismatch {
                sig_id: self.sig_id.0,
                expected: r_x_ge_n,
                actual: self.r_x_ge_n.0,
            });
        }
        if r_x_mod_n != self.expected_r.to_u256() {
            return Err(FinalEcdsaCheckError::SignatureRMismatch {
                sig_id: self.sig_id.0,
            });
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FinalEcdsaCheckError {
    RowCountMismatch {
        public_inputs: usize,
        certs: usize,
        fake_glv: usize,
        chain: usize,
    },
    IdMismatch {
        source: &'static str,
        sig_id: u32,
        cert_id: u32,
        expected_sig_id: u32,
        expected_cert_id: u32,
    },
    NonBooleanFlag {
        field: &'static str,
        actual: u32,
    },
    PreparedPoint(crate::prepared_table::PreparedTableError),
    ChainR3Mismatch {
        source: &'static str,
        sig_id: u32,
    },
    InfinityFinalR {
        sig_id: u32,
    },
    FinalRPointMismatch {
        sig_id: u32,
    },
    SignatureRMismatch {
        sig_id: u32,
    },
    XCoordinateOutOfRange,
    ReductionFlagMismatch {
        sig_id: u32,
        expected: u32,
        actual: u32,
    },
}

fn require_cert(
    expected_sig_id: M31,
    expected_cert_id: u32,
    cert: &CertScalarInputRow,
) -> Result<(), FinalEcdsaCheckError> {
    if cert.sig_id == expected_sig_id && cert.cert_id.0 == expected_cert_id {
        Ok(())
    } else {
        Err(FinalEcdsaCheckError::IdMismatch {
            source: "cert",
            sig_id: cert.sig_id.0,
            cert_id: cert.cert_id.0,
            expected_sig_id: expected_sig_id.0,
            expected_cert_id,
        })
    }
}

fn require_fake_glv(
    cert: &CertScalarInputRow,
    fake_glv: &FakeGlvScalarHintRow,
) -> Result<(), FinalEcdsaCheckError> {
    if fake_glv.sig_id == cert.sig_id && fake_glv.cert_id == cert.cert_id {
        Ok(())
    } else {
        Err(FinalEcdsaCheckError::IdMismatch {
            source: "fake_glv",
            sig_id: fake_glv.sig_id.0,
            cert_id: fake_glv.cert_id.0,
            expected_sig_id: cert.sig_id.0,
            expected_cert_id: cert.cert_id.0,
        })
    }
}

fn require_chain(
    cert: &CertScalarInputRow,
    chain: &FakeGlvChainCert,
) -> Result<(), FinalEcdsaCheckError> {
    if chain.sig_id == cert.sig_id && chain.cert_id == cert.cert_id {
        Ok(())
    } else {
        Err(FinalEcdsaCheckError::IdMismatch {
            source: "fake_glv_chain",
            sig_id: chain.sig_id.0,
            cert_id: chain.cert_id.0,
            expected_sig_id: cert.sig_id.0,
            expected_cert_id: cert.cert_id.0,
        })
    }
}

fn scalar_mul_point(
    cert: &CertScalarInputRow,
) -> Result<PreparedAffinePoint, FinalEcdsaCheckError> {
    if cert.cert_active.0 == 0 {
        return Ok(PreparedAffinePoint::infinity());
    }
    let base = AffinePoint {
        x: cert.base_x.to_u256(),
        y: cert.base_y.to_u256(),
    };
    Ok(scalar_mul(&cert.scalar.to_u256(), &base).map_or_else(
        PreparedAffinePoint::infinity,
        PreparedAffinePoint::from_affine,
    ))
}

fn require_chain_r3_matches_h(
    source: &'static str,
    h: &PreparedAffinePoint,
    fake_glv: &FakeGlvScalarHintRow,
    chain: &FakeGlvChainCert,
) -> Result<(), FinalEcdsaCheckError> {
    if fake_glv.cert_active.0 == 0 {
        if chain.r3 == PreparedAffinePoint::infinity() {
            return Ok(());
        }
        return Err(FinalEcdsaCheckError::ChainR3Mismatch {
            source,
            sig_id: chain.sig_id.0,
        });
    }

    let signed_h = match fake_glv.hint.s2_sign_bit.0 {
        0 => h.clone(),
        1 => prepared(negate_optional(h.to_option())),
        actual => {
            return Err(FinalEcdsaCheckError::NonBooleanFlag {
                field: "s2_sign_bit",
                actual,
            });
        }
    };
    let expected_r3 = triple(&signed_h);
    if chain.r3 == expected_r3 {
        Ok(())
    } else {
        Err(FinalEcdsaCheckError::ChainR3Mismatch {
            source,
            sig_id: chain.sig_id.0,
        })
    }
}

fn triple(point: &PreparedAffinePoint) -> PreparedAffinePoint {
    let doubled = prepared(double_optional(point.to_option()));
    prepared(add_optional_points(doubled.to_option(), point.to_option()))
}

fn x_mod_order(x: &U256) -> Result<(U256, u32), FinalEcdsaCheckError> {
    let n = U256::from_le_u64s(&P256_ORDER);
    match cmp_u256(x, &n) {
        core::cmp::Ordering::Less => Ok((x.clone(), 0)),
        core::cmp::Ordering::Equal => Ok((U256::ZERO, 1)),
        core::cmp::Ordering::Greater => {
            let reduced = sub_words(x, &n);
            if cmp_u256(&reduced, &n).is_lt() {
                Ok((reduced, 1))
            } else {
                Err(FinalEcdsaCheckError::XCoordinateOutOfRange)
            }
        }
    }
}

fn add_optional_points(lhs: Option<AffinePoint>, rhs: Option<AffinePoint>) -> Option<AffinePoint> {
    match (lhs, rhs) {
        (None, None) => None,
        (Some(point), None) | (None, Some(point)) => Some(point),
        (Some(lhs), Some(rhs)) if lhs == rhs => Some(point_double(&lhs).output),
        (Some(lhs), Some(rhs)) if is_additive_inverse(&lhs, &rhs) => None,
        (Some(lhs), Some(rhs)) => Some(point_add(&lhs, &rhs).output),
    }
}

fn double_optional(point: Option<AffinePoint>) -> Option<AffinePoint> {
    point.map(|point| point_double(&point).output)
}

fn negate_optional(point: Option<AffinePoint>) -> Option<AffinePoint> {
    point.map(|point| AffinePoint {
        x: point.x,
        y: sub_mod_witness(
            &U256::from_le_u64s(&P256_MODULUS),
            &point.y,
            &U256::from_le_u64s(&P256_MODULUS),
        )
        .result
        .to_u256(),
    })
}

fn prepared(point: Option<AffinePoint>) -> PreparedAffinePoint {
    point.map_or_else(
        PreparedAffinePoint::infinity,
        PreparedAffinePoint::from_affine,
    )
}

fn is_additive_inverse(lhs: &AffinePoint, rhs: &AffinePoint) -> bool {
    lhs.x == rhs.x
        && add_mod_witness(&lhs.y, &rhs.y, &U256::from_le_u64s(&P256_MODULUS))
            .result
            .to_u256()
            == U256::ZERO
}

fn sub_words(lhs: &U256, rhs: &U256) -> U256 {
    let lhs = lhs.to_le_u64s();
    let rhs = rhs.to_le_u64s();
    let mut diff = [0u64; 4];
    let mut borrow = 0u64;
    for i in 0..4 {
        let (s1, c1) = lhs[i].overflowing_sub(rhs[i]);
        let (s2, c2) = s1.overflowing_sub(borrow);
        diff[i] = s2;
        borrow = (c1 as u64) + (c2 as u64);
    }
    U256::from_le_u64s(&diff)
}

fn cmp_u256(lhs: &U256, rhs: &U256) -> core::cmp::Ordering {
    let lhs = lhs.to_le_u64s();
    let rhs = rhs.to_le_u64s();
    for i in (0..4).rev() {
        match lhs[i].cmp(&rhs[i]) {
            core::cmp::Ordering::Equal => {}
            ordering => return ordering,
        }
    }
    core::cmp::Ordering::Equal
}

fn require_bool(field: &'static str, value: M31) -> Result<(), FinalEcdsaCheckError> {
    if value.0 <= 1 {
        return Ok(());
    }
    Err(FinalEcdsaCheckError::NonBooleanFlag {
        field,
        actual: value.0,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY};
    use crate::curve::mod_inverse;
    use crate::field_ops::mul_mod_witness;
    use crate::proof::P256ProofClaim;
    use crate::types::{EcdsaVerifyInput, Signature};

    fn valid_real_input_with_small_u_scalars(u1: u64, u2: u64) -> EcdsaVerifyInput {
        assert_ne!(u2, 0, "u2 must use the active fake-GLV branch");
        let n = U256::from_le_u64s(&P256_ORDER);
        let public_key = generator_point();
        let r_point = scalar_mul(&scalar(u1 + u2), &public_key).expect("nonzero R");
        let r = x_mod_order(&r_point.x).unwrap().0;
        let u2_inv = mod_inverse(&scalar(u2), &n);
        let s = mul_mod_witness(&r, &u2_inv, &n).result.to_u256();
        let message_hash = mul_mod_witness(&scalar(u1), &s, &n).result.to_u256();

        EcdsaVerifyInput {
            message_hash,
            signature: Signature { r, s },
            public_key,
        }
    }

    fn scalar(value: u64) -> U256 {
        U256::from_le_u64s(&[value, 0, 0, 0])
    }

    fn generator_point() -> AffinePoint {
        AffinePoint {
            x: U256::from_le_u64s(&P256_GX),
            y: U256::from_le_u64s(&P256_GY),
        }
    }

    #[test]
    fn final_check_accepts_real_signature_claim() {
        let proof_claim = P256ProofClaim::from_inputs_with_trivial_fake_glv_hints(&[
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("valid current proof claim");

        proof_claim
            .final_check
            .verify()
            .expect("final check verifies");
        assert_eq!(proof_claim.final_check.rows.len(), 1);
        assert_eq!(proof_claim.final_check.rows[0].r_point.inf.0, 0);
    }

    #[test]
    fn final_check_accepts_zero_u1_real_signature_claim() {
        let proof_claim = P256ProofClaim::from_inputs_with_trivial_fake_glv_hints(&[
            valid_real_input_with_small_u_scalars(0, 11),
        ])
        .expect("valid zero-u1 current proof claim");

        assert_eq!(
            proof_claim.final_check.rows[0].h1,
            PreparedAffinePoint::infinity()
        );
        proof_claim
            .final_check
            .verify()
            .expect("final check verifies");
    }

    #[test]
    fn final_check_detects_mutated_final_r() {
        let mut proof_claim = P256ProofClaim::from_inputs_with_trivial_fake_glv_hints(&[
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("valid current proof claim");
        proof_claim.final_check.rows[0].r_point = PreparedAffinePoint::infinity();

        let err = proof_claim
            .final_check
            .verify()
            .expect_err("mutated final R must fail");

        assert!(matches!(err, FinalEcdsaCheckError::InfinityFinalR { .. }));
    }

    #[test]
    fn final_check_detects_mutated_signature_r() {
        let mut proof_claim = P256ProofClaim::from_inputs_with_trivial_fake_glv_hints(&[
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("valid current proof claim");
        proof_claim.final_check.rows[0].expected_r = crate::limbs::P256M31BigInt::zero();

        let err = proof_claim
            .final_check
            .verify()
            .expect_err("mutated r must fail");

        assert!(matches!(
            err,
            FinalEcdsaCheckError::SignatureRMismatch { .. }
        ));
    }
}
