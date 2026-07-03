use stwo::core::fields::m31::M31;

use crate::constants::{P256_B, P256_MODULUS};
use crate::curve::mod_inverse;
use crate::fake_glv_chain::{FakeGlvPrimitiveEcOp, FakeGlvPrimitiveEcTraceClaim};
use crate::field_ops::{add_mod_witness, mul_mod_witness, sub_mod_witness};
use crate::limbs::P256M31BigInt;
use crate::prepared_table::{
    PreparedAffinePoint, PreparedTableEcRowKind, PreparedTableEcTraceClaim,
};
use crate::types::{AffinePoint, U256};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveEcTraceClaim {
    pub rows: Vec<ProjectiveEcRow>,
}

impl ProjectiveEcTraceClaim {
    pub fn from_native_traces(
        prepared: &PreparedTableEcTraceClaim,
        fake_glv: &FakeGlvPrimitiveEcTraceClaim,
    ) -> Result<Self, ProjectiveEcError> {
        Self::from_native_traces_inner(prepared, fake_glv, true)
    }

    pub(crate) fn from_native_traces_trusted(
        prepared: &PreparedTableEcTraceClaim,
        fake_glv: &FakeGlvPrimitiveEcTraceClaim,
    ) -> Result<Self, ProjectiveEcError> {
        Self::from_native_traces_inner(prepared, fake_glv, false)
    }

    fn from_native_traces_inner(
        prepared: &PreparedTableEcTraceClaim,
        fake_glv: &FakeGlvPrimitiveEcTraceClaim,
        verify: bool,
    ) -> Result<Self, ProjectiveEcError> {
        use rayon::prelude::*;
        let mut rows = prepared
            .rows
            .par_iter()
            .map(|row| {
                let op = match row.kind {
                    PreparedTableEcRowKind::DoubleP | PreparedTableEcRowKind::DoubleR => {
                        ProjectiveEcOp::Double
                    }
                    PreparedTableEcRowKind::AddP2P
                    | PreparedTableEcRowKind::AddR2R
                    | PreparedTableEcRowKind::Base(_)
                    | PreparedTableEcRowKind::Table16 => ProjectiveEcOp::MixedAdd,
                };
                ProjectiveEcRow::new(row.sig_id, row.cert_id, op, &row.lhs, &row.rhs, &row.output)
            })
            .collect::<Vec<_>>();
        rows.extend(
            fake_glv
                .rows
                .par_iter()
                .map(|row| {
                    let op = match row.op {
                        FakeGlvPrimitiveEcOp::Double => ProjectiveEcOp::Double,
                        FakeGlvPrimitiveEcOp::Add => ProjectiveEcOp::MixedAdd,
                    };
                    ProjectiveEcRow::new(
                        row.sig_id,
                        row.cert_id,
                        op,
                        &row.lhs,
                        &row.rhs,
                        &row.output,
                    )
                })
                .collect::<Vec<_>>(),
        );

        let claim = Self { rows };
        if verify {
            claim.verify()?;
        }
        Ok(claim)
    }

    pub fn verify(&self) -> Result<(), ProjectiveEcError> {
        for row in &self.rows {
            row.verify()?;
        }
        Ok(())
    }

    pub fn verify_against_native_traces(
        &self,
        prepared: &PreparedTableEcTraceClaim,
        fake_glv: &FakeGlvPrimitiveEcTraceClaim,
    ) -> Result<(), ProjectiveEcError> {
        let expected = Self::from_native_traces(prepared, fake_glv)?;
        if self == &expected {
            Ok(())
        } else {
            Err(ProjectiveEcError::NativeTraceMismatch {
                expected: expected.rows.len(),
                actual: self.rows.len(),
            })
        }
    }

    pub fn active_row_count(&self) -> usize {
        self.rows.len()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveEcRow {
    pub sig_id: M31,
    pub cert_id: M31,
    pub op: ProjectiveEcOp,
    pub lhs_affine: PreparedAffinePoint,
    pub rhs_affine: PreparedAffinePoint,
    pub output_affine: PreparedAffinePoint,
    pub output_projective: ProjectivePoint,
}

impl ProjectiveEcRow {
    pub(crate) fn new(
        sig_id: M31,
        cert_id: M31,
        op: ProjectiveEcOp,
        lhs_affine: &PreparedAffinePoint,
        rhs_affine: &PreparedAffinePoint,
        output_affine: &PreparedAffinePoint,
    ) -> Self {
        let lhs = ProjectivePoint::from_prepared(lhs_affine);
        let output_projective = match op {
            ProjectiveEcOp::Double => rcb_double(&lhs),
            ProjectiveEcOp::MixedAdd => rcb_mixed_add(&lhs, rhs_affine),
        };
        Self {
            sig_id,
            cert_id,
            op,
            lhs_affine: lhs_affine.clone(),
            rhs_affine: rhs_affine.clone(),
            output_affine: output_affine.clone(),
            output_projective,
        }
    }

    pub fn verify(&self) -> Result<(), ProjectiveEcError> {
        self.lhs_affine
            .verify()
            .map_err(ProjectiveEcError::PreparedPoint)?;
        self.rhs_affine
            .verify()
            .map_err(ProjectiveEcError::PreparedPoint)?;
        self.output_affine
            .verify()
            .map_err(ProjectiveEcError::PreparedPoint)?;
        self.output_projective.verify()?;

        let lhs = ProjectivePoint::from_prepared(&self.lhs_affine);
        let expected_projective = match self.op {
            ProjectiveEcOp::Double => rcb_double(&lhs),
            ProjectiveEcOp::MixedAdd => rcb_mixed_add(&lhs, &self.rhs_affine),
        };
        if self.output_projective != expected_projective {
            return Err(ProjectiveEcError::ProjectiveOutputMismatch {
                sig_id: self.sig_id.0,
                cert_id: self.cert_id.0,
                op: self.op,
            });
        }

        let exported = self.output_projective.to_prepared()?;
        if exported == self.output_affine {
            Ok(())
        } else {
            Err(ProjectiveEcError::AffineOutputMismatch {
                sig_id: self.sig_id.0,
                cert_id: self.cert_id.0,
                op: self.op,
            })
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProjectiveEcOp {
    Double,
    MixedAdd,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectivePoint {
    pub x: P256M31BigInt,
    pub y: P256M31BigInt,
    pub z: P256M31BigInt,
}

impl ProjectivePoint {
    pub fn infinity() -> Self {
        Self {
            x: P256M31BigInt::zero(),
            y: P256M31BigInt::from_u256(&U256::from_le_u64s(&[1, 0, 0, 0])),
            z: P256M31BigInt::zero(),
        }
    }

    pub fn from_prepared(point: &PreparedAffinePoint) -> Self {
        match point.to_option() {
            Some(point) => Self {
                x: P256M31BigInt::from_u256(&point.x),
                y: P256M31BigInt::from_u256(&point.y),
                z: P256M31BigInt::from_u256(&U256::from_le_u64s(&[1, 0, 0, 0])),
            },
            None => Self::infinity(),
        }
    }

    pub fn to_prepared(&self) -> Result<PreparedAffinePoint, ProjectiveEcError> {
        self.verify()?;
        if self.z == P256M31BigInt::zero() {
            if self.x != P256M31BigInt::zero() || self.y == P256M31BigInt::zero() {
                return Err(ProjectiveEcError::InvalidProjectiveInfinity);
            }
            return Ok(PreparedAffinePoint::infinity());
        }

        let modulus = modulus();
        let z_inv = mod_inverse(&self.z.to_u256(), &modulus);
        let x = mul_mod_witness(&self.x.to_u256(), &z_inv, &modulus)
            .result
            .to_u256();
        let y = mul_mod_witness(&self.y.to_u256(), &z_inv, &modulus)
            .result
            .to_u256();
        Ok(PreparedAffinePoint::from_affine(AffinePoint { x, y }))
    }

    pub fn verify(&self) -> Result<(), ProjectiveEcError> {
        require_field_element("x", &self.x)?;
        require_field_element("y", &self.y)?;
        require_field_element("z", &self.z)?;
        if self.x == P256M31BigInt::zero()
            && self.y == P256M31BigInt::zero()
            && self.z == P256M31BigInt::zero()
        {
            return Err(ProjectiveEcError::ForbiddenZeroProjective);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProjectiveEcError {
    FieldElementOutOfRange {
        field: &'static str,
    },
    ForbiddenZeroProjective,
    InvalidProjectiveInfinity,
    PreparedPoint(crate::prepared_table::PreparedTableError),
    ProjectiveOutputMismatch {
        sig_id: u32,
        cert_id: u32,
        op: ProjectiveEcOp,
    },
    AffineOutputMismatch {
        sig_id: u32,
        cert_id: u32,
        op: ProjectiveEcOp,
    },
    NativeTraceMismatch {
        expected: usize,
        actual: usize,
    },
}

pub fn rcb_double(input: &ProjectivePoint) -> ProjectivePoint {
    let x1 = input.x.to_u256();
    let y1 = input.y.to_u256();
    let z1 = input.z.to_u256();

    let t0 = fp_mul(&x1, &x1);
    let t1 = fp_mul(&y1, &y1);
    let mut t2 = fp_mul(&z1, &z1);
    let mut t3 = fp_mul(&x1, &y1);
    t3 = fp_add(&t3, &t3);
    let mut z3 = fp_mul(&x1, &z1);
    z3 = fp_add(&z3, &z3);
    let mut y3 = fp_mul(&curve_b(), &t2);
    y3 = fp_sub(&y3, &z3);
    let mut x3 = fp_add(&y3, &y3);
    y3 = fp_add(&x3, &y3);
    x3 = fp_sub(&t1, &y3);
    y3 = fp_add(&t1, &y3);
    y3 = fp_mul(&x3, &y3);
    x3 = fp_mul(&x3, &t3);
    t3 = fp_add(&t2, &t2);
    t2 = fp_add(&t2, &t3);
    z3 = fp_mul(&curve_b(), &z3);
    z3 = fp_sub(&z3, &t2);
    z3 = fp_sub(&z3, &t0);
    t3 = fp_add(&z3, &z3);
    z3 = fp_add(&z3, &t3);
    t3 = fp_add(&t0, &t0);
    let mut t0 = fp_add(&t3, &t0);
    t0 = fp_sub(&t0, &t2);
    t0 = fp_mul(&t0, &z3);
    y3 = fp_add(&y3, &t0);
    t0 = fp_mul(&y1, &z1);
    t0 = fp_add(&t0, &t0);
    z3 = fp_mul(&t0, &z3);
    x3 = fp_sub(&x3, &z3);
    z3 = fp_mul(&t0, &t1);
    z3 = fp_add(&z3, &z3);
    z3 = fp_add(&z3, &z3);

    projective_from_u256(x3, y3, z3)
}

pub fn rcb_mixed_add(state: &ProjectivePoint, operand: &PreparedAffinePoint) -> ProjectivePoint {
    let Some(operand) = operand.to_option() else {
        return state.clone();
    };

    let x1 = state.x.to_u256();
    let y1 = state.y.to_u256();
    let z1 = state.z.to_u256();
    let x2 = operand.x;
    let y2 = operand.y;

    let mut t0 = fp_mul(&x1, &x2);
    let mut t1 = fp_mul(&y1, &y2);
    let mut t3 = fp_add(&x2, &y2);
    let mut t4 = fp_add(&x1, &y1);
    t3 = fp_mul(&t3, &t4);
    t4 = fp_add(&t0, &t1);
    t3 = fp_sub(&t3, &t4);
    t4 = fp_mul(&y2, &z1);
    t4 = fp_add(&t4, &y1);
    let mut y3 = fp_mul(&x2, &z1);
    y3 = fp_add(&y3, &x1);
    let mut z3 = fp_mul(&curve_b(), &z1);
    let mut x3 = fp_sub(&y3, &z3);
    z3 = fp_add(&x3, &x3);
    x3 = fp_add(&x3, &z3);
    z3 = fp_sub(&t1, &x3);
    x3 = fp_add(&t1, &x3);
    y3 = fp_mul(&curve_b(), &y3);
    t1 = fp_add(&z1, &z1);
    let t2 = fp_add(&t1, &z1);
    y3 = fp_sub(&y3, &t2);
    y3 = fp_sub(&y3, &t0);
    t1 = fp_add(&y3, &y3);
    y3 = fp_add(&t1, &y3);
    t1 = fp_add(&t0, &t0);
    t0 = fp_add(&t1, &t0);
    t0 = fp_sub(&t0, &t2);
    t1 = fp_mul(&t4, &y3);
    let t2 = fp_mul(&t0, &y3);
    y3 = fp_mul(&x3, &z3);
    y3 = fp_add(&y3, &t2);
    x3 = fp_mul(&t3, &x3);
    x3 = fp_sub(&x3, &t1);
    z3 = fp_mul(&t4, &z3);
    t1 = fp_mul(&t3, &t0);
    z3 = fp_add(&z3, &t1);

    projective_from_u256(x3, y3, z3)
}

fn projective_from_u256(x: U256, y: U256, z: U256) -> ProjectivePoint {
    ProjectivePoint {
        x: P256M31BigInt::from_u256(&x),
        y: P256M31BigInt::from_u256(&y),
        z: P256M31BigInt::from_u256(&z),
    }
}

fn fp_add(lhs: &U256, rhs: &U256) -> U256 {
    add_mod_witness(lhs, rhs, &modulus()).result.to_u256()
}

fn fp_sub(lhs: &U256, rhs: &U256) -> U256 {
    sub_mod_witness(lhs, rhs, &modulus()).result.to_u256()
}

fn fp_mul(lhs: &U256, rhs: &U256) -> U256 {
    mul_mod_witness(lhs, rhs, &modulus()).result.to_u256()
}

fn modulus() -> U256 {
    U256::from_le_u64s(&P256_MODULUS)
}

fn curve_b() -> U256 {
    U256::from_le_u64s(&P256_B)
}

fn require_field_element(
    field: &'static str,
    value: &P256M31BigInt,
) -> Result<(), ProjectiveEcError> {
    if is_less_than_modulus(value) {
        Ok(())
    } else {
        Err(ProjectiveEcError::FieldElementOutOfRange { field })
    }
}

fn is_less_than_modulus(value: &P256M31BigInt) -> bool {
    let modulus = P256M31BigInt::from_u256(&modulus());
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
    use crate::curve::{point_add, point_double};
    use crate::field_ops::sub_mod_witness;
    use crate::prepared_table::{PreparedTableEcRow, PreparedTableEcRowKind};

    fn generator() -> PreparedAffinePoint {
        PreparedAffinePoint::from_affine(AffinePoint {
            x: U256::from_le_u64s(&P256_GX),
            y: U256::from_le_u64s(&P256_GY),
        })
    }

    fn negate(point: &PreparedAffinePoint) -> PreparedAffinePoint {
        let point = point.to_option().unwrap();
        PreparedAffinePoint::from_affine(AffinePoint {
            x: point.x,
            y: sub_mod_witness(&modulus(), &point.y, &modulus())
                .result
                .to_u256(),
        })
    }

    #[test]
    fn rcb_double_matches_affine_double() {
        let g = generator();
        let projective = rcb_double(&ProjectivePoint::from_prepared(&g));
        let expected =
            PreparedAffinePoint::from_affine(point_double(&g.to_option().unwrap()).output);

        assert_eq!(projective.to_prepared().unwrap(), expected);
    }

    #[test]
    fn rcb_double_keeps_infinity_canonical() {
        let projective = rcb_double(&ProjectivePoint::infinity());

        assert_eq!(projective, ProjectivePoint::infinity());
        assert_eq!(
            projective.to_prepared().unwrap(),
            PreparedAffinePoint::infinity()
        );
    }

    #[test]
    fn rcb_mixed_add_matches_affine_add() {
        let g = generator();
        let g2 = PreparedAffinePoint::from_affine(point_double(&g.to_option().unwrap()).output);
        let projective = rcb_mixed_add(&ProjectivePoint::from_prepared(&g), &g2);
        let expected = PreparedAffinePoint::from_affine(
            point_add(&g.to_option().unwrap(), &g2.to_option().unwrap()).output,
        );

        assert_eq!(projective.to_prepared().unwrap(), expected);
    }

    #[test]
    fn rcb_mixed_add_handles_operand_infinity() {
        let g = generator();
        let projective = rcb_mixed_add(
            &ProjectivePoint::from_prepared(&g),
            &PreparedAffinePoint::infinity(),
        );

        assert_eq!(projective.to_prepared().unwrap(), g);
    }

    #[test]
    fn rcb_mixed_add_handles_state_infinity() {
        let g = generator();
        let projective = rcb_mixed_add(&ProjectivePoint::infinity(), &g);

        assert_eq!(projective.to_prepared().unwrap(), g);
    }

    #[test]
    fn rcb_mixed_add_handles_additive_inverse() {
        let g = generator();
        let neg_g = negate(&g);
        let projective = rcb_mixed_add(&ProjectivePoint::from_prepared(&g), &neg_g);

        assert_eq!(
            projective.to_prepared().unwrap(),
            PreparedAffinePoint::infinity()
        );
    }

    #[test]
    fn projective_ec_trace_links_back_to_native_ec_rows() {
        let g = generator();
        let g2 = PreparedAffinePoint::from_affine(point_double(&g.to_option().unwrap()).output);
        let prepared = PreparedTableEcTraceClaim {
            rows: vec![PreparedTableEcRow {
                sig_id: M31::from_u32_unchecked(0),
                cert_id: M31::from_u32_unchecked(0),
                kind: PreparedTableEcRowKind::DoubleR,
                lhs: g.clone(),
                rhs: PreparedAffinePoint::infinity(),
                output: g2,
            }],
        };
        let fake_glv = FakeGlvPrimitiveEcTraceClaim { rows: Vec::new() };
        let trace = ProjectiveEcTraceClaim::from_native_traces(&prepared, &fake_glv)
            .expect("projective trace generates");

        trace
            .verify_against_native_traces(&prepared, &fake_glv)
            .expect("native source linkage verifies");
    }

    #[test]
    fn projective_ec_trace_detects_mutated_native_source_link() {
        let g = generator();
        let g2 = PreparedAffinePoint::from_affine(point_double(&g.to_option().unwrap()).output);
        let prepared = PreparedTableEcTraceClaim {
            rows: vec![PreparedTableEcRow {
                sig_id: M31::from_u32_unchecked(0),
                cert_id: M31::from_u32_unchecked(0),
                kind: PreparedTableEcRowKind::DoubleR,
                lhs: g.clone(),
                rhs: PreparedAffinePoint::infinity(),
                output: g2.clone(),
            }],
        };
        let fake_glv = FakeGlvPrimitiveEcTraceClaim { rows: Vec::new() };
        let mut trace = ProjectiveEcTraceClaim::from_native_traces(&prepared, &fake_glv)
            .expect("projective trace generates");
        trace.rows[0].output_affine = g;

        let err = trace
            .verify_against_native_traces(&prepared, &fake_glv)
            .expect_err("mutated projective source link must fail");

        assert!(matches!(err, ProjectiveEcError::NativeTraceMismatch { .. }));
    }
}
