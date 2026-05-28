use std::fmt;

use stwo::core::channel::Channel;
use stwo::core::fields::m31::M31;
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};
use stwo_p256_utils::scalar_arithmetic::{words_to_limbs, P256_ORDER};

use crate::limbs::P256M31BigInt;

use super::cert_bind::{CertScalarInputClaim, CertScalarInputRow};

pub const FAKE_GLV_SMALL_LIMBS: usize = 10;
pub const FAKE_GLV_TOP_LIMB_BITS: u32 = 11;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FakeGlvScalarHintClaim {
    pub rows: Vec<FakeGlvScalarHintRow>,
}

impl FakeGlvScalarHintClaim {
    pub fn from_cert_inputs(
        certs: &CertScalarInputClaim,
        hints: Vec<FakeGlvScalarHint>,
    ) -> Result<Self, FakeGlvScalarHintError> {
        if certs.rows.len() != hints.len() {
            return Err(FakeGlvScalarHintError::HintCountMismatch {
                cert_rows: certs.rows.len(),
                hints: hints.len(),
            });
        }
        let rows = certs
            .rows
            .iter()
            .zip(hints)
            .map(|(cert, hint)| FakeGlvScalarHintRow::new(cert, hint))
            .collect::<Vec<_>>();
        let claim = Self { rows };
        claim.verify()?;
        Ok(claim)
    }

    pub fn verify(&self) -> Result<(), FakeGlvScalarHintError> {
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
pub struct FakeGlvScalarHintRow {
    pub sig_id: M31,
    pub cert_id: M31,
    pub cert_active: M31,
    pub cert_zero_active: M31,
    pub scalar: P256M31BigInt,
    pub hint: FakeGlvScalarHint,
}

impl FakeGlvScalarHintRow {
    pub fn new(cert: &CertScalarInputRow, hint: FakeGlvScalarHint) -> Self {
        Self {
            sig_id: cert.sig_id,
            cert_id: cert.cert_id,
            cert_active: cert.cert_active,
            cert_zero_active: cert.cert_zero_active,
            scalar: cert.scalar.clone(),
            hint,
        }
    }

    pub fn verify(&self) -> Result<(), FakeGlvScalarHintError> {
        require_bool("cert_active", self.cert_active)?;
        require_bool("cert_zero_active", self.cert_zero_active)?;
        require_bool("s2_sign_bit", self.hint.s2_sign_bit)?;
        self.hint.s1.require_128_bit_bound("s1")?;
        self.hint.s2_abs.require_128_bit_bound("s2_abs")?;
        self.hint.q.require_128_bit_bound("q")?;

        if self.cert_active.0 == 0 {
            if self.hint.is_zero() {
                return Ok(());
            }
            return Err(FakeGlvScalarHintError::InactiveHintNonZero {
                sig_id: self.sig_id.0,
                cert_id: self.cert_id.0,
            });
        }

        if self.hint.s1.is_zero() {
            return Err(FakeGlvScalarHintError::ZeroSmallScalar { field: "s1" });
        }
        if self.hint.s2_abs.is_zero() {
            return Err(FakeGlvScalarHintError::ZeroSmallScalar { field: "s2_abs" });
        }
        verify_scalar_equation(&self.scalar, &self.hint)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FakeGlvScalarHint {
    pub s1: FakeGlvSmallScalar,
    pub s2_abs: FakeGlvSmallScalar,
    pub s2_sign_bit: M31,
    pub q: FakeGlvSmallScalar,
}

impl FakeGlvScalarHint {
    pub const fn zero() -> Self {
        Self {
            s1: FakeGlvSmallScalar::zero(),
            s2_abs: FakeGlvSmallScalar::zero(),
            s2_sign_bit: M31::from_u32_unchecked(0),
            q: FakeGlvSmallScalar::zero(),
        }
    }

    pub fn trivial_for_small_scalar(
        scalar: &P256M31BigInt,
    ) -> Result<Self, FakeGlvScalarHintError> {
        let s = FakeGlvSmallScalar::from_p256_if_128_bit(scalar)
            .ok_or(FakeGlvScalarHintError::ScalarDoesNotFitTrivialHint)?;
        if s.is_zero() {
            return Ok(Self::zero());
        }
        Ok(Self {
            s1: s,
            s2_abs: FakeGlvSmallScalar::one(),
            s2_sign_bit: M31::from_u32_unchecked(1),
            q: FakeGlvSmallScalar::zero(),
        })
    }

    fn is_zero(&self) -> bool {
        self.s1.is_zero() && self.s2_abs.is_zero() && self.s2_sign_bit.0 == 0 && self.q.is_zero()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FakeGlvSmallScalar {
    pub limbs: [M31; FAKE_GLV_SMALL_LIMBS],
}

impl FakeGlvSmallScalar {
    pub const fn zero() -> Self {
        Self {
            limbs: [M31::from_u32_unchecked(0); FAKE_GLV_SMALL_LIMBS],
        }
    }

    pub fn one() -> Self {
        let mut scalar = Self::zero();
        scalar.limbs[0] = M31::from_u32_unchecked(1);
        scalar
    }

    pub fn from_u64(value: u64) -> Self {
        let p256 = P256M31BigInt::from_u256(&crate::types::U256::from_le_u64s(&[value, 0, 0, 0]));
        Self::from_p256_if_128_bit(&p256).expect("u64 fits in fake-GLV small scalar")
    }

    pub fn from_p256_if_128_bit(value: &P256M31BigInt) -> Option<Self> {
        let limbs = value.limbs();
        let upper_zero = limbs[FAKE_GLV_SMALL_LIMBS..].iter().all(|limb| limb.0 == 0);
        let top_fits = limbs[FAKE_GLV_SMALL_LIMBS - 1].0 < (1 << FAKE_GLV_TOP_LIMB_BITS);
        (upper_zero && top_fits).then(|| Self {
            limbs: limbs[..FAKE_GLV_SMALL_LIMBS]
                .try_into()
                .expect("fixed slice length"),
        })
    }

    pub fn is_zero(&self) -> bool {
        self.limbs.iter().all(|limb| limb.0 == 0)
    }

    fn require_128_bit_bound(self, field: &'static str) -> Result<(), FakeGlvScalarHintError> {
        for (index, limb) in self.limbs.iter().enumerate() {
            let bound = if index == FAKE_GLV_SMALL_LIMBS - 1 {
                1 << FAKE_GLV_TOP_LIMB_BITS
            } else {
                1 << LIMB_BITS
            };
            if limb.0 >= bound {
                return Err(FakeGlvScalarHintError::SmallScalarOutOfRange {
                    field,
                    limb: index,
                    value: limb.0,
                    bound,
                });
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FakeGlvScalarHintError {
    HintCountMismatch {
        cert_rows: usize,
        hints: usize,
    },
    NonBooleanFlag {
        field: &'static str,
        actual: u32,
    },
    SmallScalarOutOfRange {
        field: &'static str,
        limb: usize,
        value: u32,
        bound: u32,
    },
    ZeroSmallScalar {
        field: &'static str,
    },
    InactiveHintNonZero {
        sig_id: u32,
        cert_id: u32,
    },
    ScalarDoesNotFitTrivialHint,
    ScalarEquationMismatch {
        digit: usize,
        residue: i128,
    },
    ScalarEquationCarryMismatch {
        carry: i128,
    },
}

impl fmt::Display for FakeGlvScalarHintError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::HintCountMismatch { cert_rows, hints } => write!(
                f,
                "fake-GLV hint count mismatch: {cert_rows} cert rows, {hints} hints"
            ),
            Self::NonBooleanFlag { field, actual } => {
                write!(f, "fake-GLV flag {field} must be boolean, got {actual}")
            }
            Self::SmallScalarOutOfRange {
                field,
                limb,
                value,
                bound,
            } => write!(
                f,
                "fake-GLV scalar {field}[{limb}] out of range: value {value}, bound {bound}"
            ),
            Self::ZeroSmallScalar { field } => {
                write!(f, "fake-GLV nonzero branch requires {field} > 0")
            }
            Self::InactiveHintNonZero { sig_id, cert_id } => write!(
                f,
                "inactive fake-GLV hint for signature {sig_id}, certificate {cert_id} must be zero"
            ),
            Self::ScalarDoesNotFitTrivialHint => write!(
                f,
                "scalar does not fit the trivial fake-GLV small-scalar hint"
            ),
            Self::ScalarEquationMismatch { digit, residue } => write!(
                f,
                "fake-GLV scalar equation has nonzero residue {residue} at digit {digit}"
            ),
            Self::ScalarEquationCarryMismatch { carry } => write!(
                f,
                "fake-GLV scalar equation ended with nonzero carry {carry}"
            ),
        }
    }
}

impl std::error::Error for FakeGlvScalarHintError {}

fn verify_scalar_equation(
    scalar: &P256M31BigInt,
    hint: &FakeGlvScalarHint,
) -> Result<(), FakeGlvScalarHintError> {
    const EQUATION_LIMBS: usize = N_LIMBS + FAKE_GLV_SMALL_LIMBS;
    let mut coeffs = [0i128; EQUATION_LIMBS];
    let n = words_to_limbs(&P256_ORDER);

    for (i, (scalar_limb, n_limb)) in scalar.limbs().iter().zip(n).enumerate() {
        for j in 0..FAKE_GLV_SMALL_LIMBS {
            coeffs[i + j] += scalar_limb.0 as i128 * hint.s2_abs.limbs[j].0 as i128;
            coeffs[i + j] -= n_limb as i128 * hint.q.limbs[j].0 as i128;
        }
    }

    let s1_sign = if hint.s2_sign_bit.0 == 0 { 1 } else { -1 };
    for (coeff, s1_limb) in coeffs
        .iter_mut()
        .zip(hint.s1.limbs)
        .take(FAKE_GLV_SMALL_LIMBS)
    {
        *coeff += s1_sign * s1_limb.0 as i128;
    }

    let base = 1i128 << LIMB_BITS;
    let mut carry = 0i128;
    for (digit, coeff) in coeffs.into_iter().enumerate() {
        let total = coeff + carry;
        let residue = total.rem_euclid(base);
        if residue != 0 {
            return Err(FakeGlvScalarHintError::ScalarEquationMismatch { digit, residue });
        }
        carry = total.div_euclid(base);
    }
    if carry != 0 {
        return Err(FakeGlvScalarHintError::ScalarEquationCarryMismatch { carry });
    }
    Ok(())
}

fn require_bool(field: &'static str, value: M31) -> Result<(), FakeGlvScalarHintError> {
    if value.0 <= 1 {
        return Ok(());
    }
    Err(FakeGlvScalarHintError::NonBooleanFlag {
        field,
        actual: value.0,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY};
    use crate::public_inputs::{
        public_ecdsa_consumer_claimed_sum, PublicEcdsaInputClaim, PublicEcdsaInstanceRelation,
    };
    use crate::scalar::cert_bind::CertScalarInputClaim;
    use crate::scalar::setup_air::ScalarSetupClaim;
    use crate::types::{AffinePoint, EcdsaVerifyInput, Signature, U256};
    use stwo::core::fields::qm31::SecureField;

    fn test_input(message_hash: u64, r: u64, s: u64) -> EcdsaVerifyInput {
        EcdsaVerifyInput {
            message_hash: scalar(message_hash),
            signature: Signature {
                r: scalar(r),
                s: scalar(s),
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

    fn trivial_hints(certs: &CertScalarInputClaim) -> Vec<FakeGlvScalarHint> {
        certs
            .rows
            .iter()
            .map(|row| FakeGlvScalarHint::trivial_for_small_scalar(&row.scalar).unwrap())
            .collect()
    }

    #[test]
    fn fake_glv_scalar_hints_verify_trivial_small_scalars() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(42, 77, 1)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let hints = trivial_hints(&certs);

        let fake_glv = FakeGlvScalarHintClaim::from_cert_inputs(&certs, hints)
            .expect("valid fake-GLV scalar hints");

        fake_glv.verify().expect("fake-GLV scalar hints verify");
        assert_eq!(fake_glv.rows.len(), 2);
    }

    #[test]
    fn fake_glv_scalar_e2e_keeps_public_logup_balanced() {
        let relation = PublicEcdsaInstanceRelation::dummy();
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(42, 77, 1)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let fake_glv = FakeGlvScalarHintClaim::from_cert_inputs(&certs, trivial_hints(&certs))
            .expect("valid fake-GLV scalar hints");
        let public_interaction = public_claim.initial_logup_claim(&relation);
        let vm_consumers =
            public_ecdsa_consumer_claimed_sum(&scalar_setup.public_consumers(), &relation);

        scalar_setup.verify().expect("scalar setup verifies");
        certs.verify().expect("cert inputs verify");
        fake_glv.verify().expect("fake-GLV scalar hints verify");
        assert_eq!(
            public_interaction.claimed_sum + vm_consumers,
            SecureField::from(M31::from_u32_unchecked(0))
        );
    }

    #[test]
    fn fake_glv_scalar_hints_allow_zero_branch_with_zero_hint() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(0, 77, 1)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let fake_glv = FakeGlvScalarHintClaim::from_cert_inputs(&certs, trivial_hints(&certs))
            .expect("valid fake-GLV scalar hints");

        assert_eq!(fake_glv.rows[0].cert_active.0, 0);
        assert!(fake_glv.rows[0].hint.is_zero());
        assert_eq!(fake_glv.rows[1].cert_active.0, 1);
        fake_glv.verify().expect("zero branch verifies");
    }

    #[test]
    fn fake_glv_scalar_hints_reject_mutated_s1() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(42, 77, 1)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let mut fake_glv = FakeGlvScalarHintClaim::from_cert_inputs(&certs, trivial_hints(&certs))
            .expect("valid fake-GLV scalar hints");
        fake_glv.rows[0].hint.s1.limbs[0] = M31::from_u32_unchecked(43);

        let err = fake_glv.verify().expect_err("mutated s1 must fail");

        assert!(matches!(
            err,
            FakeGlvScalarHintError::ScalarEquationMismatch { .. }
        ));
    }

    #[test]
    fn fake_glv_scalar_hints_reject_flipped_sign() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(42, 77, 1)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let mut fake_glv = FakeGlvScalarHintClaim::from_cert_inputs(&certs, trivial_hints(&certs))
            .expect("valid fake-GLV scalar hints");
        fake_glv.rows[0].hint.s2_sign_bit = M31::from_u32_unchecked(0);

        let err = fake_glv.verify().expect_err("flipped sign must fail");

        assert!(matches!(
            err,
            FakeGlvScalarHintError::ScalarEquationMismatch { .. }
        ));
    }

    #[test]
    fn fake_glv_scalar_hints_reject_zero_s2_abs_on_nonzero_branch() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(42, 77, 1)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let mut fake_glv = FakeGlvScalarHintClaim::from_cert_inputs(&certs, trivial_hints(&certs))
            .expect("valid fake-GLV scalar hints");
        fake_glv.rows[0].hint.s2_abs = FakeGlvSmallScalar::zero();

        let err = fake_glv
            .verify()
            .expect_err("zero s2_abs must fail on nonzero branch");

        assert!(matches!(
            err,
            FakeGlvScalarHintError::ZeroSmallScalar { field: "s2_abs" }
        ));
    }

    #[test]
    fn fake_glv_scalar_hints_mix_into_transcript() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(42, 77, 1)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let fake_glv = FakeGlvScalarHintClaim::from_cert_inputs(&certs, trivial_hints(&certs))
            .expect("valid fake-GLV scalar hints");
        let mut channel = stwo::core::channel::Blake2sM31Channel::default();

        fake_glv.mix_into(&mut channel);
    }
}
