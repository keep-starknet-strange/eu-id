use stwo::core::fields::m31::M31;

use crate::constants::P256_MODULUS;
use crate::curve::{point_add, point_double, scalar_mul};
use crate::field_ops::{add_mod_witness, sub_mod_witness};
use crate::prepared_point::{PreparedPointInstance, TABLE16_INDEX};
use crate::prepared_table::{PreparedAffinePoint, PreparedTableClaim};
use crate::types::{AffinePoint, U256};

use super::cert_bind::{CertScalarInputClaim, CertScalarInputRow};
use super::fake_glv_scalar::{FakeGlvScalarHintClaim, FakeGlvScalarHintRow};
use super::fake_glv_selector::{FakeGlvSelectorClaim, FakeGlvSelectorRow};
use super::fake_glv_selector_lookup::Selector16DecodeEntry;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FakeGlvChainClaim {
    pub certs: Vec<FakeGlvChainCert>,
}

impl FakeGlvChainClaim {
    pub fn from_claims(
        cert_inputs: &CertScalarInputClaim,
        fake_glv_scalars: &FakeGlvScalarHintClaim,
        selectors: &FakeGlvSelectorClaim,
        prepared_table: &PreparedTableClaim,
    ) -> Result<Self, FakeGlvChainError> {
        if cert_inputs.rows.len() != fake_glv_scalars.rows.len()
            || cert_inputs.rows.len() != selectors.rows.len()
            || cert_inputs.rows.len() != prepared_table.certs.len()
        {
            return Err(FakeGlvChainError::RowCountMismatch {
                certs: cert_inputs.rows.len(),
                fake_glv: fake_glv_scalars.rows.len(),
                selectors: selectors.rows.len(),
                tables: prepared_table.certs.len(),
            });
        }

        let certs = cert_inputs
            .rows
            .iter()
            .zip(&fake_glv_scalars.rows)
            .zip(&selectors.rows)
            .zip(&prepared_table.certs)
            .map(|(((cert, fake_glv), selector), table)| {
                FakeGlvChainCert::from_claims(cert, fake_glv, selector, table)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let claim = Self { certs };
        claim.verify()?;
        Ok(claim)
    }

    /// Test-only: build a [`FakeGlvChainClaim`] where the cert at
    /// `override_cert_index` uses the injected `R'` (paired with a prepared
    /// table built from the same `R'`); other certs use the production path.
    /// Does NOT call [`Self::verify`], so the `final_acc == r3` gate is not
    /// asserted here — callers observe it (or the downstream AIR) instead.
    #[cfg(test)]
    pub(crate) fn from_claims_with_r_override(
        cert_inputs: &CertScalarInputClaim,
        fake_glv_scalars: &FakeGlvScalarHintClaim,
        selectors: &FakeGlvSelectorClaim,
        prepared_table: &PreparedTableClaim,
        override_cert_index: usize,
        r_override: AffinePoint,
    ) -> Result<Self, FakeGlvChainError> {
        let certs = cert_inputs
            .rows
            .iter()
            .zip(&fake_glv_scalars.rows)
            .zip(&selectors.rows)
            .zip(&prepared_table.certs)
            .enumerate()
            .map(|(index, (((cert, fake_glv), selector), table))| {
                if index == override_cert_index {
                    FakeGlvChainCert::from_claims_with_r_override(
                        cert,
                        selector,
                        table,
                        r_override.clone(),
                    )
                } else {
                    FakeGlvChainCert::from_claims(cert, fake_glv, selector, table)
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self { certs })
    }

    pub fn verify(&self) -> Result<(), FakeGlvChainError> {
        for cert in &self.certs {
            cert.verify()?;
        }
        Ok(())
    }

    pub fn verify_against_claims(
        &self,
        cert_inputs: &CertScalarInputClaim,
        fake_glv_scalars: &FakeGlvScalarHintClaim,
        selectors: &FakeGlvSelectorClaim,
        prepared_table: &PreparedTableClaim,
    ) -> Result<(), FakeGlvChainError> {
        let expected = Self::from_claims(cert_inputs, fake_glv_scalars, selectors, prepared_table)?;
        if self == &expected {
            Ok(())
        } else {
            Err(FakeGlvChainError::ChainTraceMismatch {
                expected: expected.active_row_count(),
                actual: self.active_row_count(),
            })
        }
    }

    pub fn prepared_point_consumers(&self) -> Vec<PreparedPointInstance<M31>> {
        self.certs
            .iter()
            .flat_map(FakeGlvChainCert::prepared_point_consumers)
            .collect()
    }

    pub fn active_row_count(&self) -> usize {
        self.certs.iter().map(|cert| cert.rows.len()).sum()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FakeGlvPrimitiveEcTraceClaim {
    pub rows: Vec<FakeGlvPrimitiveEcRow>,
}

impl FakeGlvPrimitiveEcTraceClaim {
    pub fn from_chain(chain: &FakeGlvChainClaim) -> Result<Self, FakeGlvChainError> {
        let rows = primitive_ec_rows_for_chain(chain)?;
        let claim = Self { rows };
        claim.verify_against_chain(chain)?;
        Ok(claim)
    }

    pub fn verify(&self) -> Result<(), FakeGlvChainError> {
        for row in &self.rows {
            row.verify()?;
        }
        Ok(())
    }

    pub fn verify_against_chain(&self, chain: &FakeGlvChainClaim) -> Result<(), FakeGlvChainError> {
        self.verify()?;
        let expected = primitive_ec_rows_for_chain(chain)?;
        if self.rows == expected {
            Ok(())
        } else {
            Err(FakeGlvChainError::PrimitiveTraceMismatch {
                expected: expected.len(),
                actual: self.rows.len(),
            })
        }
    }

    pub fn active_row_count(&self) -> usize {
        self.rows.len()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FakeGlvPrimitiveEcRow {
    pub sig_id: M31,
    pub cert_id: M31,
    pub chain_kind: FakeGlvChainRowKind,
    pub op: FakeGlvPrimitiveEcOp,
    pub lhs: PreparedAffinePoint,
    pub rhs: PreparedAffinePoint,
    pub output: PreparedAffinePoint,
}

impl FakeGlvPrimitiveEcRow {
    fn double(
        source: &FakeGlvChainRow,
        lhs: PreparedAffinePoint,
        output: PreparedAffinePoint,
    ) -> Self {
        Self {
            sig_id: source.sig_id,
            cert_id: source.cert_id,
            chain_kind: source.kind,
            op: FakeGlvPrimitiveEcOp::Double,
            lhs,
            rhs: PreparedAffinePoint::infinity(),
            output,
        }
    }

    fn add(
        source: &FakeGlvChainRow,
        lhs: PreparedAffinePoint,
        rhs: PreparedAffinePoint,
        output: PreparedAffinePoint,
    ) -> Self {
        Self {
            sig_id: source.sig_id,
            cert_id: source.cert_id,
            chain_kind: source.kind,
            op: FakeGlvPrimitiveEcOp::Add,
            lhs,
            rhs,
            output,
        }
    }

    pub fn verify(&self) -> Result<(), FakeGlvChainError> {
        self.lhs
            .verify()
            .map_err(FakeGlvChainError::PreparedPoint)?;
        self.rhs
            .verify()
            .map_err(FakeGlvChainError::PreparedPoint)?;
        self.output
            .verify()
            .map_err(FakeGlvChainError::PreparedPoint)?;
        let expected = match self.op {
            FakeGlvPrimitiveEcOp::Double => prepared(double_optional(self.lhs.to_option())),
            FakeGlvPrimitiveEcOp::Add => prepared(add_optional_points(
                self.lhs.to_option(),
                self.rhs.to_option(),
            )),
        };
        if self.output == expected {
            Ok(())
        } else {
            Err(FakeGlvChainError::PrimitiveRowOutputMismatch {
                sig_id: self.sig_id.0,
                cert_id: self.cert_id.0,
                chain_kind: self.chain_kind,
                op: self.op,
            })
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FakeGlvPrimitiveEcOp {
    Double,
    Add,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FakeGlvChainCert {
    pub sig_id: M31,
    pub cert_id: M31,
    pub cert_active: M31,
    pub rows: Vec<FakeGlvChainRow>,
    pub final_acc: PreparedAffinePoint,
    pub r3: PreparedAffinePoint,
    consumers: Vec<PreparedPointInstance<M31>>,
}

impl FakeGlvChainCert {
    fn from_claims(
        cert: &CertScalarInputRow,
        fake_glv: &FakeGlvScalarHintRow,
        selector: &FakeGlvSelectorRow,
        table: &crate::prepared_table::PreparedTableCert,
    ) -> Result<Self, FakeGlvChainError> {
        require_same_id("fake_glv", cert, fake_glv.sig_id, fake_glv.cert_id)?;
        require_same_id("selector", cert, selector.sig_id, selector.cert_id)?;
        if cert.sig_id != table.sig_id || cert.cert_id != table.cert_id {
            return Err(FakeGlvChainError::IdMismatch {
                source: "prepared_table",
                cert_sig_id: cert.sig_id.0,
                cert_cert_id: cert.cert_id.0,
                other_sig_id: table.sig_id.0,
                other_cert_id: table.cert_id.0,
            });
        }

        if cert.cert_active.0 == 0 {
            return Ok(Self {
                sig_id: cert.sig_id,
                cert_id: cert.cert_id,
                cert_active: cert.cert_active,
                rows: Vec::new(),
                final_acc: PreparedAffinePoint::infinity(),
                r3: PreparedAffinePoint::infinity(),
                consumers: Vec::new(),
            });
        }

        let p = PreparedAffinePoint::from_affine(AffinePoint {
            x: cert.base_x.to_u256(),
            y: cert.base_y.to_u256(),
        });
        let h = scalar_mul(
            &cert.scalar.to_u256(),
            &p.to_option().expect("base point finite"),
        )
        .ok_or(FakeGlvChainError::MissingHintPoint {
            sig_id: cert.sig_id.0,
            cert_id: cert.cert_id.0,
        })?;
        let r = PreparedAffinePoint::from_affine(signed_hint_point(&h, fake_glv.hint.s2_sign_bit)?);

        let mut rows = Vec::new();
        let mut consumers = Vec::new();

        let mut acc = table_point(table, selector.init_base_index.0)?;
        consumers.push(acc.instance(cert.sig_id, cert.cert_id, selector.init_base_index.0));
        rows.push(FakeGlvChainRow {
            sig_id: cert.sig_id,
            cert_id: cert.cert_id,
            kind: FakeGlvChainRowKind::MsbInit,
            acc_before: PreparedAffinePoint::infinity(),
            operand: acc.clone(),
            acc_after: acc.clone(),
        });

        let selector0 =
            Selector16DecodeEntry::from_selector(selector.selectors[0]).map_err(|_| {
                FakeGlvChainError::InvalidSelector {
                    selector: selector.selectors[0].0,
                }
            })?;
        consumers.push(table_point(table, selector0.base_index.0)?.instance(
            cert.sig_id,
            cert.cert_id,
            selector0.base_index.0,
        ));

        for (step, selector_value) in selector.selectors.iter().enumerate().skip(1).rev() {
            let decoded = Selector16DecodeEntry::from_selector(*selector_value).map_err(|_| {
                FakeGlvChainError::InvalidSelector {
                    selector: selector_value.0,
                }
            })?;
            let operand = selected_base_point(table, decoded)?;
            consumers.push(table_point(table, decoded.base_index.0)?.instance(
                cert.sig_id,
                cert.cert_id,
                decoded.base_index.0,
            ));
            let next = chain_step(&acc, &operand);
            rows.push(FakeGlvChainRow {
                sig_id: cert.sig_id,
                cert_id: cert.cert_id,
                kind: FakeGlvChainRowKind::ChainStep(step as u32),
                acc_before: acc,
                operand,
                acc_after: next.clone(),
            });
            acc = next;
        }

        let table16 = table.table16.clone();
        consumers.push(table16.instance(cert.sig_id, cert.cert_id, TABLE16_INDEX));
        let next = chain_step(&acc, &table16);
        rows.push(FakeGlvChainRow {
            sig_id: cert.sig_id,
            cert_id: cert.cert_id,
            kind: FakeGlvChainRowKind::Table16Step,
            acc_before: acc,
            operand: table16,
            acc_after: next.clone(),
        });
        acc = next;

        let correction = lsb_correction(selector, &p, &r, table)?;
        if selector.s1_lsb.0 == 0 && selector.s2_lsb.0 == 0 {
            consumers.push(table.base[2].instance(cert.sig_id, cert.cert_id, 2));
        }
        let final_acc = prepared(add_optional_points(acc.to_option(), correction.to_option()));
        rows.push(FakeGlvChainRow {
            sig_id: cert.sig_id,
            cert_id: cert.cert_id,
            kind: FakeGlvChainRowKind::LsbCorrection,
            acc_before: acc,
            operand: correction,
            acc_after: final_acc.clone(),
        });

        let cert = Self {
            sig_id: cert.sig_id,
            cert_id: cert.cert_id,
            cert_active: cert.cert_active,
            rows,
            final_acc,
            r3: table.r3.clone(),
            consumers,
        };
        cert.verify()?;
        Ok(cert)
    }

    /// Test-only variant of [`Self::from_claims`] that uses an injected hint
    /// point `R'` for the `lsb_correction` operand instead of the production
    /// `R = signed_hint(scalar_mul(u, base))`. Pair it with a prepared table
    /// built from the same `R'` (see
    /// [`crate::prepared_table::PreparedTableCert::new_with_r_override`]) to
    /// produce an internally consistent wrong-`R` chain. Returns the
    /// constructed cert *without* running [`Self::verify`], so callers can
    /// observe whether the `final_acc == r3` gate holds for the wrong `R'`.
    #[cfg(test)]
    pub(crate) fn from_claims_with_r_override(
        cert: &CertScalarInputRow,
        selector: &FakeGlvSelectorRow,
        table: &crate::prepared_table::PreparedTableCert,
        r_override: AffinePoint,
    ) -> Result<Self, FakeGlvChainError> {
        assert_eq!(cert.cert_active.0, 1, "override path requires active cert");
        let p = PreparedAffinePoint::from_affine(AffinePoint {
            x: cert.base_x.to_u256(),
            y: cert.base_y.to_u256(),
        });
        let r = PreparedAffinePoint::from_affine(r_override);

        let mut rows = Vec::new();
        let mut consumers = Vec::new();

        let mut acc = table_point(table, selector.init_base_index.0)?;
        consumers.push(acc.instance(cert.sig_id, cert.cert_id, selector.init_base_index.0));
        rows.push(FakeGlvChainRow {
            sig_id: cert.sig_id,
            cert_id: cert.cert_id,
            kind: FakeGlvChainRowKind::MsbInit,
            acc_before: PreparedAffinePoint::infinity(),
            operand: acc.clone(),
            acc_after: acc.clone(),
        });

        let selector0 =
            Selector16DecodeEntry::from_selector(selector.selectors[0]).map_err(|_| {
                FakeGlvChainError::InvalidSelector {
                    selector: selector.selectors[0].0,
                }
            })?;
        consumers.push(table_point(table, selector0.base_index.0)?.instance(
            cert.sig_id,
            cert.cert_id,
            selector0.base_index.0,
        ));

        for (step, selector_value) in selector.selectors.iter().enumerate().skip(1).rev() {
            let decoded = Selector16DecodeEntry::from_selector(*selector_value).map_err(|_| {
                FakeGlvChainError::InvalidSelector {
                    selector: selector_value.0,
                }
            })?;
            let operand = selected_base_point(table, decoded)?;
            consumers.push(table_point(table, decoded.base_index.0)?.instance(
                cert.sig_id,
                cert.cert_id,
                decoded.base_index.0,
            ));
            let next = chain_step(&acc, &operand);
            rows.push(FakeGlvChainRow {
                sig_id: cert.sig_id,
                cert_id: cert.cert_id,
                kind: FakeGlvChainRowKind::ChainStep(step as u32),
                acc_before: acc,
                operand,
                acc_after: next.clone(),
            });
            acc = next;
        }

        let table16 = table.table16.clone();
        consumers.push(table16.instance(cert.sig_id, cert.cert_id, TABLE16_INDEX));
        let next = chain_step(&acc, &table16);
        rows.push(FakeGlvChainRow {
            sig_id: cert.sig_id,
            cert_id: cert.cert_id,
            kind: FakeGlvChainRowKind::Table16Step,
            acc_before: acc,
            operand: table16,
            acc_after: next.clone(),
        });
        acc = next;

        let correction = lsb_correction(selector, &p, &r, table)?;
        if selector.s1_lsb.0 == 0 && selector.s2_lsb.0 == 0 {
            consumers.push(table.base[2].instance(cert.sig_id, cert.cert_id, 2));
        }
        let final_acc = prepared(add_optional_points(acc.to_option(), correction.to_option()));
        rows.push(FakeGlvChainRow {
            sig_id: cert.sig_id,
            cert_id: cert.cert_id,
            kind: FakeGlvChainRowKind::LsbCorrection,
            acc_before: acc,
            operand: correction,
            acc_after: final_acc.clone(),
        });

        Ok(Self {
            sig_id: cert.sig_id,
            cert_id: cert.cert_id,
            cert_active: cert.cert_active,
            rows,
            final_acc,
            r3: table.r3.clone(),
            consumers,
        })
    }

    pub fn verify(&self) -> Result<(), FakeGlvChainError> {
        if self.cert_active.0 > 1 {
            return Err(FakeGlvChainError::NonBooleanFlag {
                field: "cert_active",
                actual: self.cert_active.0,
            });
        }
        for row in &self.rows {
            row.verify()?;
        }
        if self.cert_active.0 == 1 && self.final_acc != self.r3 {
            return Err(FakeGlvChainError::FinalAccumulatorMismatch {
                sig_id: self.sig_id.0,
                cert_id: self.cert_id.0,
            });
        }
        Ok(())
    }

    pub fn prepared_point_consumers(&self) -> Vec<PreparedPointInstance<M31>> {
        self.consumers.clone()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FakeGlvChainRow {
    pub sig_id: M31,
    pub cert_id: M31,
    pub kind: FakeGlvChainRowKind,
    pub acc_before: PreparedAffinePoint,
    pub operand: PreparedAffinePoint,
    pub acc_after: PreparedAffinePoint,
}

impl FakeGlvChainRow {
    pub fn verify(&self) -> Result<(), FakeGlvChainError> {
        self.acc_before
            .verify()
            .map_err(FakeGlvChainError::PreparedPoint)?;
        self.operand
            .verify()
            .map_err(FakeGlvChainError::PreparedPoint)?;
        self.acc_after
            .verify()
            .map_err(FakeGlvChainError::PreparedPoint)?;
        let expected = match self.kind {
            FakeGlvChainRowKind::MsbInit => self.operand.clone(),
            FakeGlvChainRowKind::ChainStep(_) | FakeGlvChainRowKind::Table16Step => {
                chain_step(&self.acc_before, &self.operand)
            }
            FakeGlvChainRowKind::LsbCorrection => prepared(add_optional_points(
                self.acc_before.to_option(),
                self.operand.to_option(),
            )),
        };
        if self.acc_after == expected {
            Ok(())
        } else {
            Err(FakeGlvChainError::RowOutputMismatch {
                sig_id: self.sig_id.0,
                cert_id: self.cert_id.0,
                kind: self.kind,
            })
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FakeGlvChainRowKind {
    MsbInit,
    ChainStep(u32),
    Table16Step,
    LsbCorrection,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FakeGlvChainError {
    RowCountMismatch {
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
    RowOutputMismatch {
        sig_id: u32,
        cert_id: u32,
        kind: FakeGlvChainRowKind,
    },
    PrimitiveRowOutputMismatch {
        sig_id: u32,
        cert_id: u32,
        chain_kind: FakeGlvChainRowKind,
        op: FakeGlvPrimitiveEcOp,
    },
    PrimitiveTraceMismatch {
        expected: usize,
        actual: usize,
    },
    EcTraceRowsExceedDomain {
        rows: usize,
        domain: usize,
    },
    ProjectiveSourceInvalid,
    ProjectiveSourceTooShort {
        source_offset: usize,
        fake_glv: usize,
        projective: usize,
    },
    RelationImbalance {
        relation: &'static str,
    },
    PreprocessedColumnMissing,
    ProofLayer,
    ChainTraceMismatch {
        expected: usize,
        actual: usize,
    },
    FinalAccumulatorMismatch {
        sig_id: u32,
        cert_id: u32,
    },
    MissingTablePoint {
        table_index: u32,
    },
    PreparedPoint(crate::prepared_table::PreparedTableError),
}

fn primitive_ec_rows_for_chain(
    chain: &FakeGlvChainClaim,
) -> Result<Vec<FakeGlvPrimitiveEcRow>, FakeGlvChainError> {
    let mut rows = Vec::new();
    for cert in &chain.certs {
        for row in &cert.rows {
            match row.kind {
                FakeGlvChainRowKind::MsbInit => {}
                FakeGlvChainRowKind::ChainStep(_) | FakeGlvChainRowKind::Table16Step => {
                    let doubled = prepared(double_optional(row.acc_before.to_option()));
                    rows.push(FakeGlvPrimitiveEcRow::double(
                        row,
                        row.acc_before.clone(),
                        doubled.clone(),
                    ));
                    let quadrupled = prepared(double_optional(doubled.to_option()));
                    rows.push(FakeGlvPrimitiveEcRow::double(
                        row,
                        doubled,
                        quadrupled.clone(),
                    ));
                    rows.push(FakeGlvPrimitiveEcRow::add(
                        row,
                        quadrupled,
                        row.operand.clone(),
                        row.acc_after.clone(),
                    ));
                }
                FakeGlvChainRowKind::LsbCorrection => {
                    rows.push(FakeGlvPrimitiveEcRow::add(
                        row,
                        row.acc_before.clone(),
                        row.operand.clone(),
                        row.acc_after.clone(),
                    ));
                }
            }
        }
    }
    for row in &rows {
        row.verify()?;
    }
    Ok(rows)
}

fn table_point(
    table: &crate::prepared_table::PreparedTableCert,
    table_index: u32,
) -> Result<PreparedAffinePoint, FakeGlvChainError> {
    match table_index {
        0..=7 => Ok(table.base[table_index as usize].clone()),
        TABLE16_INDEX => Ok(table.table16.clone()),
        _ => Err(FakeGlvChainError::MissingTablePoint { table_index }),
    }
}

fn selected_base_point(
    table: &crate::prepared_table::PreparedTableCert,
    selector: Selector16DecodeEntry,
) -> Result<PreparedAffinePoint, FakeGlvChainError> {
    let base = table_point(table, selector.base_index.0)?;
    if selector.neg_bit.0 == 0 {
        Ok(base)
    } else if selector.neg_bit.0 == 1 {
        Ok(prepared(negate_optional(base.to_option())))
    } else {
        Err(FakeGlvChainError::NonBooleanFlag {
            field: "selector.neg_bit",
            actual: selector.neg_bit.0,
        })
    }
}

fn chain_step(acc: &PreparedAffinePoint, operand: &PreparedAffinePoint) -> PreparedAffinePoint {
    let doubled = prepared(double_optional(acc.to_option()));
    let quadrupled = prepared(double_optional(doubled.to_option()));
    prepared(add_optional_points(
        quadrupled.to_option(),
        operand.to_option(),
    ))
}

fn lsb_correction(
    selector: &FakeGlvSelectorRow,
    p: &PreparedAffinePoint,
    r: &PreparedAffinePoint,
    table: &crate::prepared_table::PreparedTableCert,
) -> Result<PreparedAffinePoint, FakeGlvChainError> {
    if selector.s1_lsb.0 > 1 {
        return Err(FakeGlvChainError::NonBooleanFlag {
            field: "s1_lsb",
            actual: selector.s1_lsb.0,
        });
    }
    if selector.s2_lsb.0 > 1 {
        return Err(FakeGlvChainError::NonBooleanFlag {
            field: "s2_lsb",
            actual: selector.s2_lsb.0,
        });
    }
    match (selector.s1_lsb.0, selector.s2_lsb.0) {
        (1, 1) => Ok(PreparedAffinePoint::infinity()),
        (0, 1) => Ok(prepared(negate_optional(p.to_option()))),
        (1, 0) => Ok(prepared(negate_optional(r.to_option()))),
        (0, 0) => Ok(prepared(negate_optional(table.base[2].to_option()))),
        _ => unreachable!("lsb values are checked above"),
    }
}

fn require_same_id(
    source: &'static str,
    cert: &CertScalarInputRow,
    other_sig_id: M31,
    other_cert_id: M31,
) -> Result<(), FakeGlvChainError> {
    if cert.sig_id == other_sig_id && cert.cert_id == other_cert_id {
        Ok(())
    } else {
        Err(FakeGlvChainError::IdMismatch {
            source,
            cert_sig_id: cert.sig_id.0,
            cert_cert_id: cert.cert_id.0,
            other_sig_id: other_sig_id.0,
            other_cert_id: other_cert_id.0,
        })
    }
}

fn signed_hint_point(h: &AffinePoint, s2_sign_bit: M31) -> Result<AffinePoint, FakeGlvChainError> {
    match s2_sign_bit.0 {
        0 => Ok(h.clone()),
        1 => Ok(negate_point(h)),
        actual => Err(FakeGlvChainError::NonBooleanFlag {
            field: "s2_sign_bit",
            actual,
        }),
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
    use crate::scalar::prepared_table::PreparedTableClaim;
    use crate::scalar::setup_air::ScalarSetupClaim;
    use crate::types::{EcdsaVerifyInput, Signature};

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

    fn build_chain(
        message_hash: u64,
    ) -> (
        CertScalarInputClaim,
        FakeGlvScalarHintClaim,
        FakeGlvSelectorClaim,
        PreparedTableClaim,
        FakeGlvChainClaim,
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
        let table = PreparedTableClaim::from_claims(&certs, &fake_glv, &selectors).unwrap();
        let chain = FakeGlvChainClaim::from_claims(&certs, &fake_glv, &selectors, &table).unwrap();
        (certs, fake_glv, selectors, table, chain)
    }

    #[test]
    fn fake_glv_chain_trace_reaches_r3_for_active_certs() {
        let (_, _, _, _, chain) = build_chain(42);

        assert_eq!(chain.certs.len(), 2);
        assert_eq!(chain.active_row_count(), 130);
        for cert in &chain.certs {
            assert_eq!(cert.final_acc, cert.r3);
            cert.verify().expect("cert chain verifies");
        }
    }

    #[test]
    fn fake_glv_chain_trace_skips_inactive_zero_branch() {
        let (_, _, _, _, chain) = build_chain(0);

        assert_eq!(chain.certs[0].cert_active.0, 0);
        assert!(chain.certs[0].rows.is_empty());
        assert!(chain.certs[0].prepared_point_consumers().is_empty());
        assert_eq!(chain.certs[1].cert_active.0, 1);
        assert_eq!(chain.active_row_count(), 65);
    }

    #[test]
    fn fake_glv_chain_trace_produces_expected_prepared_point_consumers() {
        let (_, _, selectors, _, chain) = build_chain(42);
        let consumers = chain.prepared_point_consumers();

        assert_eq!(consumers.len(), 130);
        assert_eq!(consumers[0].table_index, selectors.rows[0].init_base_index);
        assert!(consumers
            .iter()
            .any(|consumer| consumer.table_index.0 == TABLE16_INDEX));
    }

    #[test]
    fn fake_glv_chain_trace_detects_mutated_row_output() {
        let (_, _, _, _, mut chain) = build_chain(42);
        chain.certs[0].rows[1].acc_after = PreparedAffinePoint::infinity();

        let err = chain.verify().expect_err("mutated row must fail");

        assert!(matches!(err, FakeGlvChainError::RowOutputMismatch { .. }));
    }

    #[test]
    fn fake_glv_chain_trace_links_back_to_source_claims() {
        let (certs, fake_glv, selectors, table, chain) = build_chain(42);

        chain
            .verify_against_claims(&certs, &fake_glv, &selectors, &table)
            .expect("chain links to source claims");
    }

    #[test]
    fn fake_glv_chain_trace_detects_mutated_source_link() {
        let (certs, fake_glv, selectors, table, mut chain) = build_chain(42);
        chain.certs[0].rows[0].kind = FakeGlvChainRowKind::Table16Step;

        let err = chain
            .verify_against_claims(&certs, &fake_glv, &selectors, &table)
            .expect_err("mutated chain/source link must fail");

        assert!(matches!(err, FakeGlvChainError::ChainTraceMismatch { .. }));
    }

    #[test]
    fn fake_glv_primitive_ec_trace_expands_chain_steps() {
        let (_, _, _, _, chain) = build_chain(42);
        let trace =
            FakeGlvPrimitiveEcTraceClaim::from_chain(&chain).expect("primitive ec trace builds");

        trace
            .verify_against_chain(&chain)
            .expect("primitive ec trace links to chain");
        assert_eq!(trace.active_row_count(), 380);
        assert!(matches!(trace.rows[0].op, FakeGlvPrimitiveEcOp::Double));
        assert!(trace
            .rows
            .iter()
            .any(|row| row.chain_kind == FakeGlvChainRowKind::LsbCorrection));
    }

    #[test]
    fn fake_glv_primitive_ec_trace_skips_inactive_zero_branch() {
        let (_, _, _, _, chain) = build_chain(0);
        let trace =
            FakeGlvPrimitiveEcTraceClaim::from_chain(&chain).expect("primitive ec trace builds");

        assert_eq!(trace.active_row_count(), 190);
        assert!(trace
            .rows
            .iter()
            .all(|row| row.cert_id == chain.certs[1].cert_id));
    }

    #[test]
    fn fake_glv_primitive_ec_trace_detects_mutated_output() {
        let (_, _, _, _, chain) = build_chain(42);
        let mut trace =
            FakeGlvPrimitiveEcTraceClaim::from_chain(&chain).expect("primitive ec trace builds");
        trace.rows[0].output = PreparedAffinePoint::infinity();

        let err = trace
            .verify_against_chain(&chain)
            .expect_err("mutated primitive row must fail");

        assert!(matches!(
            err,
            FakeGlvChainError::PrimitiveRowOutputMismatch { .. }
        ));
    }

    #[test]
    fn fake_glv_primitive_ec_trace_detects_missing_row() {
        let (_, _, _, _, chain) = build_chain(42);
        let mut trace =
            FakeGlvPrimitiveEcTraceClaim::from_chain(&chain).expect("primitive ec trace builds");
        trace.rows.pop();

        let err = trace
            .verify_against_chain(&chain)
            .expect_err("missing primitive row must fail");

        assert!(matches!(
            err,
            FakeGlvChainError::PrimitiveTraceMismatch { .. }
        ));
    }
}
