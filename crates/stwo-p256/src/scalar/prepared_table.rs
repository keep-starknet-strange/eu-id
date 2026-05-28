use stwo::core::fields::m31::M31;

use crate::constants::P256_MODULUS;
use crate::curve::{point_add, point_double, scalar_mul};
use crate::field_ops::{add_mod_witness, sub_mod_witness};
use crate::limbs::P256M31BigInt;
use crate::prepared_point::{
    PreparedPointInstance, PreparedPointTraceClaim, PreparedPointUseCountClaim,
    PREPARED_BASE_COUNT, TABLE16_INDEX,
};
use crate::types::{AffinePoint, U256};

use super::cert_bind::{CertScalarInputClaim, CertScalarInputRow};
use super::fake_glv_scalar::{FakeGlvScalarHintClaim, FakeGlvScalarHintRow};
use super::fake_glv_selector::{FakeGlvSelectorClaim, FakeGlvSelectorRow};
use super::fake_glv_selector_lookup::Selector16DecodeEntry;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedTableClaim {
    pub certs: Vec<PreparedTableCert>,
}

impl PreparedTableClaim {
    pub fn from_claims(
        cert_inputs: &CertScalarInputClaim,
        fake_glv_scalars: &FakeGlvScalarHintClaim,
        selectors: &FakeGlvSelectorClaim,
    ) -> Result<Self, PreparedTableError> {
        if cert_inputs.rows.len() != fake_glv_scalars.rows.len()
            || cert_inputs.rows.len() != selectors.rows.len()
        {
            return Err(PreparedTableError::RowCountMismatch {
                certs: cert_inputs.rows.len(),
                fake_glv: fake_glv_scalars.rows.len(),
                selectors: selectors.rows.len(),
            });
        }

        let certs = cert_inputs
            .rows
            .iter()
            .zip(&fake_glv_scalars.rows)
            .zip(&selectors.rows)
            .map(|((cert, fake_glv), selector)| PreparedTableCert::new(cert, fake_glv, selector))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self { certs })
    }

    pub fn verify(&self) -> Result<(), PreparedTableError> {
        for cert in &self.certs {
            cert.verify()?;
        }
        Ok(())
    }

    pub fn prepared_point_trace(
        &self,
        use_counts: &PreparedPointUseCountClaim,
    ) -> Result<PreparedPointTraceClaim, PreparedTableError> {
        if self.certs.len() != use_counts.certs.len() {
            return Err(PreparedTableError::UseCountCountMismatch {
                tables: self.certs.len(),
                use_counts: use_counts.certs.len(),
            });
        }

        Ok(PreparedPointTraceClaim::from_use_counts(
            use_counts,
            |sig_id, cert_id, table_index| {
                self.instance(sig_id, cert_id, table_index)
                    .unwrap_or_else(|| PreparedPointInstance::dummy(sig_id, cert_id, table_index))
            },
        ))
    }

    pub fn instance(
        &self,
        sig_id: M31,
        cert_id: M31,
        table_index: u32,
    ) -> Option<PreparedPointInstance<M31>> {
        self.certs
            .iter()
            .find(|cert| cert.sig_id == sig_id && cert.cert_id == cert_id)
            .and_then(|cert| cert.instance(table_index))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedTableCert {
    pub sig_id: M31,
    pub cert_id: M31,
    pub cert_active: M31,
    pub base: [PreparedAffinePoint; PREPARED_BASE_COUNT],
    pub r3: PreparedAffinePoint,
    pub table16: PreparedAffinePoint,
}

impl PreparedTableCert {
    fn new(
        cert: &CertScalarInputRow,
        fake_glv: &FakeGlvScalarHintRow,
        selector: &FakeGlvSelectorRow,
    ) -> Result<Self, PreparedTableError> {
        require_same_id("fake_glv", cert, fake_glv.sig_id, fake_glv.cert_id)?;
        require_same_id("selector", cert, selector.sig_id, selector.cert_id)?;

        if cert.cert_active.0 == 0 {
            return Ok(Self {
                sig_id: cert.sig_id,
                cert_id: cert.cert_id,
                cert_active: cert.cert_active,
                base: core::array::from_fn(|_| PreparedAffinePoint::infinity()),
                r3: PreparedAffinePoint::infinity(),
                table16: PreparedAffinePoint::infinity(),
            });
        }

        let p = AffinePoint {
            x: cert.base_x.to_u256(),
            y: cert.base_y.to_u256(),
        };
        let h =
            scalar_mul(&cert.scalar.to_u256(), &p).ok_or(PreparedTableError::MissingHintPoint {
                sig_id: cert.sig_id.0,
                cert_id: cert.cert_id.0,
            })?;
        let r = signed_hint_point(&h, fake_glv.hint.s2_sign_bit)?;
        let p3 = scalar_mul(&U256::from_le_u64s(&[3, 0, 0, 0]), &p).ok_or(
            PreparedTableError::MissingTriplePoint {
                point: "P",
                sig_id: cert.sig_id.0,
                cert_id: cert.cert_id.0,
            },
        )?;
        let r3 = scalar_mul(&U256::from_le_u64s(&[3, 0, 0, 0]), &r).ok_or(
            PreparedTableError::MissingTriplePoint {
                point: "R",
                sig_id: cert.sig_id.0,
                cert_id: cert.cert_id.0,
            },
        )?;

        let base = [
            prepared(add_optional_points(
                Some(p3.clone()),
                negate_optional(Some(r.clone())),
            )),
            prepared(add_optional_points(
                Some(p.clone()),
                negate_optional(Some(r.clone())),
            )),
            prepared(add_optional_points(Some(p.clone()), Some(r.clone()))),
            prepared(add_optional_points(Some(p3.clone()), Some(r.clone()))),
            prepared(add_optional_points(
                Some(p3.clone()),
                negate_optional(Some(r3.clone())),
            )),
            prepared(add_optional_points(
                Some(p.clone()),
                negate_optional(Some(r3.clone())),
            )),
            prepared(add_optional_points(Some(p.clone()), Some(r3.clone()))),
            prepared(add_optional_points(Some(p3.clone()), Some(r3.clone()))),
        ];

        let selector0 =
            Selector16DecodeEntry::from_selector(selector.selectors[0]).map_err(|_| {
                PreparedTableError::InvalidSelector {
                    selector: selector.selectors[0].0,
                }
            })?;
        let selected = apply_selector(&base, selector0)?;
        let table16 = prepared(add_optional_points(selected.to_option(), Some(r3.clone())));

        Ok(Self {
            sig_id: cert.sig_id,
            cert_id: cert.cert_id,
            cert_active: cert.cert_active,
            base,
            r3: prepared(Some(r3)),
            table16,
        })
    }

    pub fn verify(&self) -> Result<(), PreparedTableError> {
        if self.cert_active.0 > 1 {
            return Err(PreparedTableError::NonBooleanFlag {
                field: "cert_active",
                actual: self.cert_active.0,
            });
        }
        for point in &self.base {
            point.verify()?;
        }
        self.r3.verify()?;
        self.table16.verify()?;
        Ok(())
    }

    pub fn instance(&self, table_index: u32) -> Option<PreparedPointInstance<M31>> {
        let point = match table_index {
            0..=7 => self.base[table_index as usize].clone(),
            TABLE16_INDEX => self.table16.clone(),
            _ => return None,
        };
        Some(point.instance(self.sig_id, self.cert_id, table_index))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedAffinePoint {
    pub x: P256M31BigInt,
    pub y: P256M31BigInt,
    pub inf: M31,
}

impl PreparedAffinePoint {
    pub const fn infinity() -> Self {
        Self {
            x: P256M31BigInt::zero(),
            y: P256M31BigInt::zero(),
            inf: M31::from_u32_unchecked(1),
        }
    }

    pub fn from_affine(point: AffinePoint) -> Self {
        Self {
            x: P256M31BigInt::from_u256(&point.x),
            y: P256M31BigInt::from_u256(&point.y),
            inf: M31::from_u32_unchecked(0),
        }
    }

    pub fn verify(&self) -> Result<(), PreparedTableError> {
        if self.inf.0 > 1 {
            return Err(PreparedTableError::NonBooleanFlag {
                field: "inf",
                actual: self.inf.0,
            });
        }
        if self.inf.0 == 1 && (self.x != P256M31BigInt::zero() || self.y != P256M31BigInt::zero()) {
            return Err(PreparedTableError::NonCanonicalInfinity);
        }
        Ok(())
    }

    pub fn to_option(&self) -> Option<AffinePoint> {
        (self.inf.0 == 0).then(|| AffinePoint {
            x: self.x.to_u256(),
            y: self.y.to_u256(),
        })
    }

    pub fn instance(
        &self,
        sig_id: M31,
        cert_id: M31,
        table_index: u32,
    ) -> PreparedPointInstance<M31> {
        PreparedPointInstance {
            sig_id,
            cert_id,
            table_index: M31::from_u32_unchecked(table_index),
            x: self.x.clone(),
            y: self.y.clone(),
            inf: self.inf,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreparedTableError {
    RowCountMismatch {
        certs: usize,
        fake_glv: usize,
        selectors: usize,
    },
    UseCountCountMismatch {
        tables: usize,
        use_counts: usize,
    },
    IdMismatch {
        source: &'static str,
        cert_sig_id: u32,
        cert_cert_id: u32,
        other_sig_id: u32,
        other_cert_id: u32,
    },
    InvalidSelector {
        selector: u32,
    },
    NonBooleanFlag {
        field: &'static str,
        actual: u32,
    },
    MissingHintPoint {
        sig_id: u32,
        cert_id: u32,
    },
    MissingTriplePoint {
        point: &'static str,
        sig_id: u32,
        cert_id: u32,
    },
    NonCanonicalInfinity,
}

fn require_same_id(
    source: &'static str,
    cert: &CertScalarInputRow,
    other_sig_id: M31,
    other_cert_id: M31,
) -> Result<(), PreparedTableError> {
    if cert.sig_id == other_sig_id && cert.cert_id == other_cert_id {
        Ok(())
    } else {
        Err(PreparedTableError::IdMismatch {
            source,
            cert_sig_id: cert.sig_id.0,
            cert_cert_id: cert.cert_id.0,
            other_sig_id: other_sig_id.0,
            other_cert_id: other_cert_id.0,
        })
    }
}

fn signed_hint_point(h: &AffinePoint, s2_sign_bit: M31) -> Result<AffinePoint, PreparedTableError> {
    match s2_sign_bit.0 {
        0 => Ok(h.clone()),
        1 => Ok(negate_point(h)),
        actual => Err(PreparedTableError::NonBooleanFlag {
            field: "s2_sign_bit",
            actual,
        }),
    }
}

fn apply_selector(
    base: &[PreparedAffinePoint; PREPARED_BASE_COUNT],
    selector: Selector16DecodeEntry,
) -> Result<PreparedAffinePoint, PreparedTableError> {
    let base_index = selector.base_index.0 as usize;
    let point = base
        .get(base_index)
        .cloned()
        .ok_or(PreparedTableError::InvalidSelector {
            selector: selector.selector.0,
        })?;
    if selector.neg_bit.0 == 0 {
        Ok(point)
    } else if selector.neg_bit.0 == 1 {
        Ok(prepared(negate_optional(point.to_option())))
    } else {
        Err(PreparedTableError::NonBooleanFlag {
            field: "selector.neg_bit",
            actual: selector.neg_bit.0,
        })
    }
}

fn prepared(point: Option<AffinePoint>) -> PreparedAffinePoint {
    point.map_or_else(
        PreparedAffinePoint::infinity,
        PreparedAffinePoint::from_affine,
    )
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

fn negate_optional(point: Option<AffinePoint>) -> Option<AffinePoint> {
    point.map(|point| negate_point(&point))
}

fn negate_point(point: &AffinePoint) -> AffinePoint {
    AffinePoint {
        x: point.x.clone(),
        y: sub_mod_witness(
            &U256::from_le_u64s(&P256_MODULUS),
            &point.y,
            &U256::from_le_u64s(&P256_MODULUS),
        )
        .result
        .to_u256(),
    }
}

fn is_additive_inverse(lhs: &AffinePoint, rhs: &AffinePoint) -> bool {
    lhs.x == rhs.x
        && add_mod_witness(&lhs.y, &rhs.y, &U256::from_le_u64s(&P256_MODULUS))
            .result
            .to_u256()
            == U256::ZERO
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY};
    use crate::public_inputs::PublicEcdsaInputClaim;
    use crate::scalar::cert_bind::CertScalarInputClaim;
    use crate::scalar::fake_glv_scalar::{FakeGlvScalarHint, FakeGlvScalarHintClaim};
    use crate::scalar::fake_glv_selector::FakeGlvSelectorClaim;
    use crate::scalar::setup_air::ScalarSetupClaim;
    use crate::types::{Signature, U256};

    fn test_input(message_hash: u64, r: u64, s: u64) -> crate::types::EcdsaVerifyInput {
        crate::types::EcdsaVerifyInput {
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

    fn build_table(
        message_hash: u64,
    ) -> (
        CertScalarInputClaim,
        FakeGlvScalarHintClaim,
        FakeGlvSelectorClaim,
        PreparedTableClaim,
    ) {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(message_hash, 77, 1)]);
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
        let table =
            PreparedTableClaim::from_claims(&certs, &fake_glv, &selectors).expect("valid table");
        (certs, fake_glv, selectors, table)
    }

    #[test]
    fn prepared_table_generates_active_base_and_table16_points() {
        let (_, _, _, table) = build_table(42);

        assert_eq!(table.certs.len(), 2);
        for cert in &table.certs {
            assert_eq!(cert.cert_active.0, 1);
            for point in &cert.base {
                point.verify().expect("base point is canonical");
            }
            assert_eq!(cert.r3.inf.0, 0);
            assert_eq!(cert.table16.inf.0, 0);
        }
    }

    #[test]
    fn prepared_table_table16_matches_selector0_plus_r3() {
        let (_, _, selectors, table) = build_table(42);

        for (selector, cert) in selectors.rows.iter().zip(&table.certs) {
            let decoded = Selector16DecodeEntry::from_selector(selector.selectors[0]).unwrap();
            let selected = apply_selector(&cert.base, decoded).unwrap();
            let expected = prepared(add_optional_points(
                selected.to_option(),
                cert.r3.to_option(),
            ));

            assert_eq!(cert.table16, expected);
        }
    }

    #[test]
    fn prepared_table_inactive_cert_is_canonical_infinity() {
        let (_, _, _, table) = build_table(0);

        assert_eq!(table.certs[0].cert_active.0, 0);
        assert_eq!(
            table.certs[0].base,
            core::array::from_fn(|_| PreparedAffinePoint::infinity())
        );
        assert_eq!(table.certs[0].r3, PreparedAffinePoint::infinity());
        assert_eq!(table.certs[0].table16, PreparedAffinePoint::infinity());
        assert_eq!(table.certs[1].cert_active.0, 1);
    }
}
