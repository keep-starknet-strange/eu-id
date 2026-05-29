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

use super::cert_bind::{CertScalarInputClaim, CertScalarInputRow, CERT_ID_U1_GENERATOR};
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

    pub fn verify_prepared_point_trace(
        &self,
        use_counts: &PreparedPointUseCountClaim,
        trace: &PreparedPointTraceClaim,
    ) -> Result<(), PreparedTableError> {
        let expected = self.prepared_point_trace(use_counts)?;
        if &expected == trace {
            Ok(())
        } else {
            Err(PreparedTableError::PreparedPointTraceMismatch)
        }
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
pub struct PreparedTableEcTraceClaim {
    pub rows: Vec<PreparedTableEcRow>,
}

impl PreparedTableEcTraceClaim {
    pub fn from_claims(
        cert_inputs: &CertScalarInputClaim,
        fake_glv_scalars: &FakeGlvScalarHintClaim,
        selectors: &FakeGlvSelectorClaim,
        table: &PreparedTableClaim,
    ) -> Result<Self, PreparedTableError> {
        if cert_inputs.rows.len() != fake_glv_scalars.rows.len()
            || cert_inputs.rows.len() != selectors.rows.len()
            || cert_inputs.rows.len() != table.certs.len()
        {
            return Err(PreparedTableError::EcTraceCountMismatch {
                certs: cert_inputs.rows.len(),
                fake_glv: fake_glv_scalars.rows.len(),
                selectors: selectors.rows.len(),
                tables: table.certs.len(),
            });
        }

        let mut rows = Vec::new();
        for (((cert, fake_glv), selector), table_cert) in cert_inputs
            .rows
            .iter()
            .zip(&fake_glv_scalars.rows)
            .zip(&selectors.rows)
            .zip(&table.certs)
        {
            rows.extend(prepared_table_ec_rows_for_cert(
                cert, fake_glv, selector, table_cert,
            )?);
        }
        let claim = Self { rows };
        claim.verify()?;
        Ok(claim)
    }

    pub fn verify(&self) -> Result<(), PreparedTableError> {
        for row in &self.rows {
            row.verify()?;
        }
        Ok(())
    }

    pub fn active_row_count(&self) -> usize {
        self.rows.len()
    }

    pub fn verify_against_table(
        &self,
        table: &PreparedTableClaim,
    ) -> Result<(), PreparedTableError> {
        for cert in &table.certs {
            let cert_rows = self
                .rows
                .iter()
                .filter(|row| row.sig_id == cert.sig_id && row.cert_id == cert.cert_id)
                .collect::<Vec<_>>();
            if cert.cert_active.0 == 0 {
                if cert_rows.is_empty() {
                    continue;
                }
                return Err(PreparedTableError::InactiveEcTraceRows {
                    sig_id: cert.sig_id.0,
                    cert_id: cert.cert_id.0,
                });
            }

            let expected_rows = if cert.cert_id.0 == CERT_ID_U1_GENERATOR {
                PREPARED_BASE_COUNT + 3
            } else {
                PREPARED_BASE_COUNT + 5
            };
            if cert_rows.len() != expected_rows {
                return Err(PreparedTableError::EcTraceCertRowCountMismatch {
                    sig_id: cert.sig_id.0,
                    cert_id: cert.cert_id.0,
                    expected: expected_rows,
                    actual: cert_rows.len(),
                });
            }

            require_unique_output(
                &cert_rows,
                cert.sig_id,
                cert.cert_id,
                PreparedTableEcRowKind::AddR2R,
                "R3",
                &cert.r3,
            )?;
            for (index, point) in cert.base.iter().enumerate() {
                require_unique_output(
                    &cert_rows,
                    cert.sig_id,
                    cert.cert_id,
                    PreparedTableEcRowKind::Base(index as u32),
                    "Base",
                    point,
                )?;
            }
            require_unique_output(
                &cert_rows,
                cert.sig_id,
                cert.cert_id,
                PreparedTableEcRowKind::Table16,
                "Table16",
                &cert.table16,
            )?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedTableEcRow {
    pub sig_id: M31,
    pub cert_id: M31,
    pub kind: PreparedTableEcRowKind,
    pub lhs: PreparedAffinePoint,
    pub rhs: PreparedAffinePoint,
    pub output: PreparedAffinePoint,
}

impl PreparedTableEcRow {
    fn double(
        sig_id: M31,
        cert_id: M31,
        kind: PreparedTableEcRowKind,
        input: PreparedAffinePoint,
        output: PreparedAffinePoint,
    ) -> Self {
        Self {
            sig_id,
            cert_id,
            kind,
            lhs: input,
            rhs: PreparedAffinePoint::infinity(),
            output,
        }
    }

    fn add(
        sig_id: M31,
        cert_id: M31,
        kind: PreparedTableEcRowKind,
        lhs: PreparedAffinePoint,
        rhs: PreparedAffinePoint,
        output: PreparedAffinePoint,
    ) -> Self {
        Self {
            sig_id,
            cert_id,
            kind,
            lhs,
            rhs,
            output,
        }
    }

    pub fn verify(&self) -> Result<(), PreparedTableError> {
        self.lhs.verify()?;
        self.rhs.verify()?;
        self.output.verify()?;
        let expected = match self.kind {
            PreparedTableEcRowKind::DoubleP | PreparedTableEcRowKind::DoubleR => {
                double_optional(self.lhs.to_option())
            }
            PreparedTableEcRowKind::AddP2P
            | PreparedTableEcRowKind::AddR2R
            | PreparedTableEcRowKind::Base(_)
            | PreparedTableEcRowKind::Table16 => {
                add_optional_points(self.lhs.to_option(), self.rhs.to_option())
            }
        };
        let expected = prepared(expected);
        if self.output == expected {
            Ok(())
        } else {
            Err(PreparedTableError::EcTraceOutputMismatch {
                sig_id: self.sig_id.0,
                cert_id: self.cert_id.0,
                kind: self.kind,
            })
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreparedTableEcRowKind {
    DoubleP,
    AddP2P,
    DoubleR,
    AddR2R,
    Base(u32),
    Table16,
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
    EcTraceCountMismatch {
        certs: usize,
        fake_glv: usize,
        selectors: usize,
        tables: usize,
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
    EcTraceOutputMismatch {
        sig_id: u32,
        cert_id: u32,
        kind: PreparedTableEcRowKind,
    },
    PreparedTableOutputMismatch {
        sig_id: u32,
        cert_id: u32,
        table_index: u32,
    },
    PreparedPointTraceMismatch,
    InactiveEcTraceRows {
        sig_id: u32,
        cert_id: u32,
    },
    EcTraceCertRowCountMismatch {
        sig_id: u32,
        cert_id: u32,
        expected: usize,
        actual: usize,
    },
    EcTraceExpectedOutputMissing {
        sig_id: u32,
        cert_id: u32,
        label: &'static str,
    },
    EcTraceExpectedOutputDuplicate {
        sig_id: u32,
        cert_id: u32,
        label: &'static str,
    },
    EcTraceExpectedOutputMismatch {
        sig_id: u32,
        cert_id: u32,
        label: &'static str,
    },
    NonCanonicalInfinity,
}

fn require_unique_output(
    rows: &[&PreparedTableEcRow],
    sig_id: M31,
    cert_id: M31,
    kind: PreparedTableEcRowKind,
    label: &'static str,
    expected: &PreparedAffinePoint,
) -> Result<(), PreparedTableError> {
    let matches = rows
        .iter()
        .copied()
        .filter(|row| row.kind == kind)
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [] => Err(PreparedTableError::EcTraceExpectedOutputMissing {
            sig_id: sig_id.0,
            cert_id: cert_id.0,
            label,
        }),
        [row] if &row.output == expected => Ok(()),
        [_row] => Err(PreparedTableError::EcTraceExpectedOutputMismatch {
            sig_id: sig_id.0,
            cert_id: cert_id.0,
            label,
        }),
        _ => Err(PreparedTableError::EcTraceExpectedOutputDuplicate {
            sig_id: sig_id.0,
            cert_id: cert_id.0,
            label,
        }),
    }
}

fn prepared_table_ec_rows_for_cert(
    cert: &CertScalarInputRow,
    fake_glv: &FakeGlvScalarHintRow,
    selector: &FakeGlvSelectorRow,
    table: &PreparedTableCert,
) -> Result<Vec<PreparedTableEcRow>, PreparedTableError> {
    require_same_id("fake_glv", cert, fake_glv.sig_id, fake_glv.cert_id)?;
    require_same_id("selector", cert, selector.sig_id, selector.cert_id)?;
    if cert.sig_id != table.sig_id || cert.cert_id != table.cert_id {
        return Err(PreparedTableError::IdMismatch {
            source: "prepared_table",
            cert_sig_id: cert.sig_id.0,
            cert_cert_id: cert.cert_id.0,
            other_sig_id: table.sig_id.0,
            other_cert_id: table.cert_id.0,
        });
    }
    if cert.cert_active.0 == 0 {
        return Ok(Vec::new());
    }

    let sig_id = cert.sig_id;
    let cert_id = cert.cert_id;
    let p = PreparedAffinePoint::from_affine(AffinePoint {
        x: cert.base_x.to_u256(),
        y: cert.base_y.to_u256(),
    });
    let h = scalar_mul(
        &cert.scalar.to_u256(),
        &p.to_option().expect("base point finite"),
    )
    .ok_or(PreparedTableError::MissingHintPoint {
        sig_id: cert.sig_id.0,
        cert_id: cert.cert_id.0,
    })?;
    let r = PreparedAffinePoint::from_affine(signed_hint_point(&h, fake_glv.hint.s2_sign_bit)?);

    let mut rows = Vec::new();
    let p3 = if cert.cert_id.0 == CERT_ID_U1_GENERATOR {
        PreparedAffinePoint::from_affine(
            scalar_mul(&U256::from_le_u64s(&[3, 0, 0, 0]), &p.to_option().unwrap()).ok_or(
                PreparedTableError::MissingTriplePoint {
                    point: "P",
                    sig_id: cert.sig_id.0,
                    cert_id: cert.cert_id.0,
                },
            )?,
        )
    } else {
        let p2 = prepared(double_optional(p.to_option()));
        rows.push(PreparedTableEcRow::double(
            sig_id,
            cert_id,
            PreparedTableEcRowKind::DoubleP,
            p.clone(),
            p2.clone(),
        ));
        let p3 = prepared(add_optional_points(p2.to_option(), p.to_option()));
        rows.push(PreparedTableEcRow::add(
            sig_id,
            cert_id,
            PreparedTableEcRowKind::AddP2P,
            p2,
            p.clone(),
            p3.clone(),
        ));
        p3
    };

    let r2 = prepared(double_optional(r.to_option()));
    rows.push(PreparedTableEcRow::double(
        sig_id,
        cert_id,
        PreparedTableEcRowKind::DoubleR,
        r.clone(),
        r2.clone(),
    ));
    rows.push(PreparedTableEcRow::add(
        sig_id,
        cert_id,
        PreparedTableEcRowKind::AddR2R,
        r2.clone(),
        r.clone(),
        table.r3.clone(),
    ));

    let base_operands = [
        (p3.clone(), prepared(negate_optional(r.to_option()))),
        (p.clone(), prepared(negate_optional(r.to_option()))),
        (p.clone(), r.clone()),
        (p3.clone(), r.clone()),
        (p3.clone(), prepared(negate_optional(table.r3.to_option()))),
        (p.clone(), prepared(negate_optional(table.r3.to_option()))),
        (p.clone(), table.r3.clone()),
        (p3.clone(), table.r3.clone()),
    ];

    for (index, (lhs, rhs)) in base_operands.into_iter().enumerate() {
        let output = table.base[index].clone();
        rows.push(PreparedTableEcRow::add(
            sig_id,
            cert_id,
            PreparedTableEcRowKind::Base(index as u32),
            lhs.clone(),
            rhs.clone(),
            output.clone(),
        ));
        let expected = prepared(add_optional_points(lhs.to_option(), rhs.to_option()));
        if output != expected {
            return Err(PreparedTableError::PreparedTableOutputMismatch {
                sig_id: sig_id.0,
                cert_id: cert_id.0,
                table_index: index as u32,
            });
        }
    }

    let selector0 = Selector16DecodeEntry::from_selector(selector.selectors[0]).map_err(|_| {
        PreparedTableError::InvalidSelector {
            selector: selector.selectors[0].0,
        }
    })?;
    let selected = apply_selector(&table.base, selector0)?;
    rows.push(PreparedTableEcRow::add(
        sig_id,
        cert_id,
        PreparedTableEcRowKind::Table16,
        selected.clone(),
        table.r3.clone(),
        table.table16.clone(),
    ));
    let expected_table16 = prepared(add_optional_points(
        selected.to_option(),
        table.r3.to_option(),
    ));
    if table.table16 != expected_table16 {
        return Err(PreparedTableError::PreparedTableOutputMismatch {
            sig_id: sig_id.0,
            cert_id: cert_id.0,
            table_index: TABLE16_INDEX,
        });
    }

    Ok(rows)
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

fn double_optional(point: Option<AffinePoint>) -> Option<AffinePoint> {
    point.map(|point| point_double(&point).output)
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

    #[test]
    fn prepared_table_ec_trace_records_expected_active_rows() {
        let (certs, fake_glv, selectors, table) = build_table(42);
        let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
            .expect("valid ec trace");

        trace.verify().expect("ec trace verifies");
        assert_eq!(trace.active_row_count(), 24);
        assert!(trace
            .rows
            .iter()
            .any(|row| row.kind == PreparedTableEcRowKind::Base(0)));
        assert!(trace
            .rows
            .iter()
            .any(|row| row.kind == PreparedTableEcRowKind::Table16));
    }

    #[test]
    fn prepared_table_ec_trace_skips_inactive_zero_branch() {
        let (certs, fake_glv, selectors, table) = build_table(0);
        let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
            .expect("valid ec trace");

        assert_eq!(table.certs[0].cert_active.0, 0);
        assert_eq!(trace.active_row_count(), 13);
        assert!(trace
            .rows
            .iter()
            .all(|row| row.cert_id == table.certs[1].cert_id));
    }

    #[test]
    fn prepared_table_ec_trace_detects_mutated_output() {
        let (certs, fake_glv, selectors, table) = build_table(42);
        let mut trace =
            PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
                .expect("valid ec trace");
        trace.rows[0].output = PreparedAffinePoint::infinity();

        let err = trace.verify().expect_err("mutated output must fail");

        assert!(matches!(
            err,
            PreparedTableError::EcTraceOutputMismatch { .. }
        ));
    }

    #[test]
    fn prepared_table_ec_trace_links_outputs_to_table_points() {
        let (certs, fake_glv, selectors, table) = build_table(42);
        let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
            .expect("valid ec trace");

        trace
            .verify_against_table(&table)
            .expect("ec trace outputs match table points");
    }

    #[test]
    fn prepared_table_ec_trace_detects_mutated_table_output_link() {
        let (certs, fake_glv, selectors, mut table) = build_table(42);
        let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
            .expect("valid ec trace");
        table.certs[0].base[0] = PreparedAffinePoint::infinity();

        let err = trace
            .verify_against_table(&table)
            .expect_err("mutated table output link must fail");

        assert!(matches!(
            err,
            PreparedTableError::EcTraceExpectedOutputMismatch { label: "Base", .. }
        ));
    }

    #[test]
    fn prepared_table_prepared_point_trace_matches_table_and_use_counts() {
        let (_, _, selectors, table) = build_table(42);
        let use_counts =
            PreparedPointUseCountClaim::from_selector_claim(&selectors).expect("valid counts");
        let prepared_trace = table
            .prepared_point_trace(&use_counts)
            .expect("prepared trace generates");

        table
            .verify_prepared_point_trace(&use_counts, &prepared_trace)
            .expect("prepared providers match table");
    }

    #[test]
    fn prepared_table_prepared_point_trace_detects_mutated_provider() {
        let (_, _, selectors, table) = build_table(42);
        let use_counts =
            PreparedPointUseCountClaim::from_selector_claim(&selectors).expect("valid counts");
        let mut prepared_trace = table
            .prepared_point_trace(&use_counts)
            .expect("prepared trace generates");
        prepared_trace.providers[0].instance.x = P256M31BigInt::zero();

        let err = table
            .verify_prepared_point_trace(&use_counts, &prepared_trace)
            .expect_err("mutated provider must fail");

        assert_eq!(err, PreparedTableError::PreparedPointTraceMismatch);
    }
}
