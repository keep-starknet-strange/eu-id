use std::fmt;

use stwo::core::channel::Channel;
use stwo::core::fields::m31::M31;

use super::fake_glv_scalar::{FakeGlvScalarHintClaim, FakeGlvScalarHintRow, FakeGlvSmallScalar};

pub const FAKE_GLV_SELECTOR_CHUNKS: usize = 63;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FakeGlvSelectorClaim {
    pub rows: Vec<FakeGlvSelectorRow>,
}

impl FakeGlvSelectorClaim {
    pub fn from_scalar_hints(
        scalar_hints: &FakeGlvScalarHintClaim,
    ) -> Result<Self, FakeGlvSelectorError> {
        let rows = scalar_hints
            .rows
            .iter()
            .map(FakeGlvSelectorRow::from_scalar_hint)
            .collect::<Vec<_>>();
        let claim = Self { rows };
        claim.verify(scalar_hints)?;
        Ok(claim)
    }

    pub fn verify(
        &self,
        scalar_hints: &FakeGlvScalarHintClaim,
    ) -> Result<(), FakeGlvSelectorError> {
        if self.rows.len() != scalar_hints.rows.len() {
            return Err(FakeGlvSelectorError::RowCountMismatch {
                selectors: self.rows.len(),
                scalar_hints: scalar_hints.rows.len(),
            });
        }
        for (row, scalar_hint) in self.rows.iter().zip(&scalar_hints.rows) {
            row.verify(scalar_hint)?;
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
pub struct FakeGlvSelectorRow {
    pub sig_id: M31,
    pub cert_id: M31,
    pub cert_active: M31,
    pub s1_lsb: M31,
    pub s2_lsb: M31,
    pub s1_msb: M31,
    pub s2_msb: M31,
    pub selectors: [M31; FAKE_GLV_SELECTOR_CHUNKS],
    pub selector_final: M31,
    pub init_base_index: M31,
}

impl FakeGlvSelectorRow {
    pub fn from_scalar_hint(scalar_hint: &FakeGlvScalarHintRow) -> Self {
        if scalar_hint.cert_active.0 == 0 {
            return Self::zero(scalar_hint.sig_id, scalar_hint.cert_id);
        }

        let s1 = decompose_small_scalar(&scalar_hint.hint.s1);
        let s2 = decompose_small_scalar(&scalar_hint.hint.s2_abs);
        let selectors =
            core::array::from_fn(|i| M31::from_u32_unchecked(s1.chunks[i] + 4 * s2.chunks[i]));
        Self {
            sig_id: scalar_hint.sig_id,
            cert_id: scalar_hint.cert_id,
            cert_active: scalar_hint.cert_active,
            s1_lsb: M31::from_u32_unchecked(s1.lsb),
            s2_lsb: M31::from_u32_unchecked(s2.lsb),
            s1_msb: M31::from_u32_unchecked(s1.msb),
            s2_msb: M31::from_u32_unchecked(s2.msb),
            selectors,
            selector_final: M31::from_u32_unchecked(5 + s1.msb + 4 * s2.msb),
            init_base_index: M31::from_u32_unchecked(2 + s1.msb + 4 * s2.msb),
        }
    }

    pub fn zero(sig_id: M31, cert_id: M31) -> Self {
        Self {
            sig_id,
            cert_id,
            cert_active: M31::from_u32_unchecked(0),
            s1_lsb: M31::from_u32_unchecked(0),
            s2_lsb: M31::from_u32_unchecked(0),
            s1_msb: M31::from_u32_unchecked(0),
            s2_msb: M31::from_u32_unchecked(0),
            selectors: [M31::from_u32_unchecked(0); FAKE_GLV_SELECTOR_CHUNKS],
            selector_final: M31::from_u32_unchecked(0),
            init_base_index: M31::from_u32_unchecked(0),
        }
    }

    pub fn verify(&self, scalar_hint: &FakeGlvScalarHintRow) -> Result<(), FakeGlvSelectorError> {
        require_matching_id("sig_id", self.sig_id, scalar_hint.sig_id)?;
        require_matching_id("cert_id", self.cert_id, scalar_hint.cert_id)?;
        require_matching_id("cert_active", self.cert_active, scalar_hint.cert_active)?;
        require_bool("s1_lsb", self.s1_lsb)?;
        require_bool("s2_lsb", self.s2_lsb)?;
        require_bool("s1_msb", self.s1_msb)?;
        require_bool("s2_msb", self.s2_msb)?;

        if self.cert_active.0 == 0 {
            return self.verify_inactive_zeroed();
        }

        let s1 = reconstruct_small_scalar(
            self.s1_lsb,
            self.s1_msb,
            self.selectors
                .map(|selector| M31::from_u32_unchecked(selector.0 % 4)),
        );
        let s2 = reconstruct_small_scalar(
            self.s2_lsb,
            self.s2_msb,
            self.selectors
                .map(|selector| M31::from_u32_unchecked(selector.0 / 4)),
        );
        if s1 != small_scalar_to_u128(&scalar_hint.hint.s1) {
            return Err(FakeGlvSelectorError::ReconstructionMismatch { field: "s1" });
        }
        if s2 != small_scalar_to_u128(&scalar_hint.hint.s2_abs) {
            return Err(FakeGlvSelectorError::ReconstructionMismatch { field: "s2_abs" });
        }

        for (index, selector) in self.selectors.iter().enumerate() {
            if selector.0 >= 16 {
                return Err(FakeGlvSelectorError::SelectorOutOfRange {
                    index,
                    value: selector.0,
                });
            }
        }
        require_eq(
            "selector_final",
            self.selector_final.0,
            5 + self.s1_msb.0 + 4 * self.s2_msb.0,
        )?;
        require_eq(
            "init_base_index",
            self.init_base_index.0,
            2 + self.s1_msb.0 + 4 * self.s2_msb.0,
        )?;
        Ok(())
    }

    fn verify_inactive_zeroed(&self) -> Result<(), FakeGlvSelectorError> {
        require_eq("inactive s1_lsb", self.s1_lsb.0, 0)?;
        require_eq("inactive s2_lsb", self.s2_lsb.0, 0)?;
        require_eq("inactive s1_msb", self.s1_msb.0, 0)?;
        require_eq("inactive s2_msb", self.s2_msb.0, 0)?;
        require_eq("inactive selector_final", self.selector_final.0, 0)?;
        require_eq("inactive init_base_index", self.init_base_index.0, 0)?;
        for (index, selector) in self.selectors.iter().enumerate() {
            if selector.0 != 0 {
                return Err(FakeGlvSelectorError::InactiveSelectorNonZero {
                    index,
                    value: selector.0,
                });
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ScalarDecomposition {
    lsb: u32,
    chunks: [u32; FAKE_GLV_SELECTOR_CHUNKS],
    msb: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FakeGlvSelectorError {
    RowCountMismatch {
        selectors: usize,
        scalar_hints: usize,
    },
    IdMismatch {
        field: &'static str,
        selector: u32,
        scalar_hint: u32,
    },
    NonBooleanFlag {
        field: &'static str,
        actual: u32,
    },
    SelectorOutOfRange {
        index: usize,
        value: u32,
    },
    FieldMismatch {
        field: &'static str,
        expected: u32,
        actual: u32,
    },
    InactiveSelectorNonZero {
        index: usize,
        value: u32,
    },
    ReconstructionMismatch {
        field: &'static str,
    },
}

impl fmt::Display for FakeGlvSelectorError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RowCountMismatch {
                selectors,
                scalar_hints,
            } => write!(
                f,
                "fake-GLV selector row count mismatch: {selectors} selectors, {scalar_hints} scalar hints"
            ),
            Self::IdMismatch {
                field,
                selector,
                scalar_hint,
            } => write!(
                f,
                "fake-GLV selector {field} mismatch: selector={selector}, scalar_hint={scalar_hint}"
            ),
            Self::NonBooleanFlag { field, actual } => {
                write!(f, "fake-GLV selector flag {field} must be boolean, got {actual}")
            }
            Self::SelectorOutOfRange { index, value } => {
                write!(f, "fake-GLV selector[{index}] out of range: {value}")
            }
            Self::FieldMismatch {
                field,
                expected,
                actual,
            } => write!(
                f,
                "fake-GLV selector {field} mismatch: expected {expected}, got {actual}"
            ),
            Self::InactiveSelectorNonZero { index, value } => write!(
                f,
                "inactive fake-GLV selector[{index}] must be zero, got {value}"
            ),
            Self::ReconstructionMismatch { field } => {
                write!(f, "fake-GLV selector reconstruction mismatch for {field}")
            }
        }
    }
}

impl std::error::Error for FakeGlvSelectorError {}

fn decompose_small_scalar(value: &FakeGlvSmallScalar) -> ScalarDecomposition {
    ScalarDecomposition {
        lsb: bit_at(value, 0),
        chunks: core::array::from_fn(|i| bit_at(value, 1 + 2 * i) + 2 * bit_at(value, 2 + 2 * i)),
        msb: bit_at(value, 127),
    }
}

fn reconstruct_small_scalar(lsb: M31, msb: M31, chunks: [M31; FAKE_GLV_SELECTOR_CHUNKS]) -> u128 {
    let mut value = lsb.0 as u128;
    for (i, chunk) in chunks.into_iter().enumerate() {
        value += (chunk.0 as u128) << (1 + 2 * i);
    }
    value + ((msb.0 as u128) << 127)
}

fn small_scalar_to_u128(value: &FakeGlvSmallScalar) -> u128 {
    let mut result = 0u128;
    for (i, limb) in value.limbs.iter().enumerate() {
        result += (limb.0 as u128) << (13 * i);
    }
    result
}

fn bit_at(value: &FakeGlvSmallScalar, bit: usize) -> u32 {
    let limb = bit / 13;
    let offset = bit % 13;
    (value.limbs[limb].0 >> offset) & 1
}

fn require_bool(field: &'static str, value: M31) -> Result<(), FakeGlvSelectorError> {
    if value.0 <= 1 {
        return Ok(());
    }
    Err(FakeGlvSelectorError::NonBooleanFlag {
        field,
        actual: value.0,
    })
}

fn require_matching_id(
    field: &'static str,
    selector: M31,
    scalar_hint: M31,
) -> Result<(), FakeGlvSelectorError> {
    if selector == scalar_hint {
        return Ok(());
    }
    Err(FakeGlvSelectorError::IdMismatch {
        field,
        selector: selector.0,
        scalar_hint: scalar_hint.0,
    })
}

fn require_eq(field: &'static str, actual: u32, expected: u32) -> Result<(), FakeGlvSelectorError> {
    if actual == expected {
        return Ok(());
    }
    Err(FakeGlvSelectorError::FieldMismatch {
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
    use crate::scalar::cert_bind::CertScalarInputClaim;
    use crate::scalar::fake_glv_scalar::{FakeGlvScalarHint, FakeGlvScalarHintClaim};
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

    fn build_fake_glv() -> (
        PublicEcdsaInputClaim,
        ScalarSetupClaim,
        CertScalarInputClaim,
        FakeGlvScalarHintClaim,
    ) {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(42, 77, 1)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let hints = certs
            .rows
            .iter()
            .map(|row| FakeGlvScalarHint::trivial_for_small_scalar(&row.scalar).unwrap())
            .collect();
        let fake_glv =
            FakeGlvScalarHintClaim::from_cert_inputs(&certs, hints).expect("valid hints");
        (public_claim, scalar_setup, certs, fake_glv)
    }

    #[test]
    fn fake_glv_selectors_reconstruct_small_scalars() {
        let (_, _, _, fake_glv) = build_fake_glv();
        let selectors =
            FakeGlvSelectorClaim::from_scalar_hints(&fake_glv).expect("valid selectors");

        selectors.verify(&fake_glv).expect("selectors verify");
        assert_eq!(selectors.rows.len(), 2);
        assert_eq!(selectors.rows[0].s1_lsb.0, 0);
        assert_eq!(selectors.rows[0].selectors[0].0, 1);
        assert_eq!(selectors.rows[0].selector_final.0, 5);
        assert_eq!(selectors.rows[0].init_base_index.0, 2);
    }

    #[test]
    fn fake_glv_selectors_e2e_keeps_public_logup_balanced() {
        let relation = PublicEcdsaInstanceRelation::dummy();
        let (public_claim, scalar_setup, certs, fake_glv) = build_fake_glv();
        let selectors =
            FakeGlvSelectorClaim::from_scalar_hints(&fake_glv).expect("valid selectors");
        let public_interaction = public_claim.initial_logup_claim(&relation);
        let vm_consumers =
            public_ecdsa_consumer_claimed_sum(&scalar_setup.public_consumers(), &relation);

        scalar_setup.verify().expect("scalar setup verifies");
        certs.verify().expect("cert inputs verify");
        fake_glv.verify().expect("fake-GLV hints verify");
        selectors.verify(&fake_glv).expect("selectors verify");
        assert_eq!(
            public_interaction.claimed_sum + vm_consumers,
            SecureField::from(M31::from_u32_unchecked(0))
        );
    }

    #[test]
    fn fake_glv_selectors_zero_inactive_branch() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(0, 77, 1)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let hints = certs
            .rows
            .iter()
            .map(|row| FakeGlvScalarHint::trivial_for_small_scalar(&row.scalar).unwrap())
            .collect();
        let fake_glv =
            FakeGlvScalarHintClaim::from_cert_inputs(&certs, hints).expect("valid hints");
        let selectors =
            FakeGlvSelectorClaim::from_scalar_hints(&fake_glv).expect("valid selectors");

        assert_eq!(selectors.rows[0].cert_active.0, 0);
        assert_eq!(
            selectors.rows[0].selectors,
            [M31::from_u32_unchecked(0); 63]
        );
        selectors.verify(&fake_glv).expect("selectors verify");
    }

    #[test]
    fn fake_glv_selectors_reject_mutated_selector() {
        let (_, _, _, fake_glv) = build_fake_glv();
        let mut selectors =
            FakeGlvSelectorClaim::from_scalar_hints(&fake_glv).expect("valid selectors");
        selectors.rows[0].selectors[0] = M31::from_u32_unchecked(11);

        let err = selectors
            .verify(&fake_glv)
            .expect_err("mutated selector must fail");

        assert!(matches!(
            err,
            FakeGlvSelectorError::ReconstructionMismatch { field: "s1" }
        ));
    }

    #[test]
    fn fake_glv_selectors_reject_mutated_final_selector() {
        let (_, _, _, fake_glv) = build_fake_glv();
        let mut selectors =
            FakeGlvSelectorClaim::from_scalar_hints(&fake_glv).expect("valid selectors");
        selectors.rows[0].selector_final = M31::from_u32_unchecked(6);

        let err = selectors
            .verify(&fake_glv)
            .expect_err("mutated final selector must fail");

        assert!(matches!(
            err,
            FakeGlvSelectorError::FieldMismatch {
                field: "selector_final",
                ..
            }
        ));
    }

    #[test]
    fn fake_glv_selectors_mix_into_transcript() {
        let (_, _, _, fake_glv) = build_fake_glv();
        let selectors =
            FakeGlvSelectorClaim::from_scalar_hints(&fake_glv).expect("valid selectors");
        let mut channel = stwo::core::channel::Blake2sM31Channel::default();

        selectors.mix_into(&mut channel);
    }
}
