use std::fmt;

use stwo::core::{
    air::Component,
    channel::Channel,
    fields::{m31::M31, qm31::SecureField},
    pcs::TreeVec,
    ColumnVec,
};
use stwo::prover::{
    backend::simd::{
        m31::{PackedM31, LOG_N_LANES},
        qm31::PackedQM31,
        SimdBackend,
    },
    ComponentProver,
};
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator,
};
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};
use stwo_p256_utils::scalar_arithmetic::{words_to_limbs, P256_ORDER};

use crate::limbs::{P256BigInt, P256M31BigInt};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};

use super::cert_bind::{
    CertScalarInputClaim, CertScalarInputRelation, CertScalarInputRow,
    CERT_SCALAR_INPUT_RELATION_ARITY,
};

pub const FAKE_GLV_SMALL_LIMBS: usize = 10;
pub const FAKE_GLV_TOP_LIMB_BITS: u32 = 11;
pub const FAKE_GLV_SCALAR_RELATION_ARITY: usize = 2 + 2 * FAKE_GLV_SMALL_LIMBS + 2;

relation!(FakeGlvScalarRelation, FAKE_GLV_SCALAR_RELATION_ARITY);

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

pub type FakeGlvScalarAirComponent = FrameworkComponent<FakeGlvScalarAirEval>;

pub const FAKE_GLV_SCALAR_TRACE_COLUMNS: usize =
    1 + CERT_SCALAR_INPUT_RELATION_ARITY + FAKE_GLV_SCALAR_ROW_COLUMNS;
const FAKE_GLV_SCALAR_ROW_COLUMNS: usize = 4 + N_LIMBS + 2 * FAKE_GLV_SMALL_LIMBS + 1
    + FAKE_GLV_SMALL_LIMBS;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FakeGlvScalarAirProofClaim {
    pub log_size: u32,
}

impl FakeGlvScalarAirProofClaim {
    pub fn from_claim(claim: &FakeGlvScalarHintClaim) -> Self {
        Self {
            log_size: padded_log_size(claim.rows.len()),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FakeGlvScalarAirInteractionClaim {
    pub claimed_sum: SecureField,
    pub cert_consumer_claimed_sum: SecureField,
}

impl FakeGlvScalarAirInteractionClaim {
    pub fn zero() -> Self {
        Self {
            claimed_sum: secure_zero(),
            cert_consumer_claimed_sum: secure_zero(),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}

pub struct FakeGlvScalarAirComponents {
    pub scalar: FakeGlvScalarAirComponent,
}

impl FakeGlvScalarAirComponents {
    pub(crate) fn new(
        allocator: &mut TraceLocationAllocator,
        claim: FakeGlvScalarAirProofClaim,
        interaction_claim: &FakeGlvScalarAirInteractionClaim,
        cert_relation: &CertScalarInputRelation,
    ) -> Self {
        Self {
            scalar: FakeGlvScalarAirComponent::new(
                allocator,
                FakeGlvScalarAirEval {
                    log_size: claim.log_size,
                    cert_relation: cert_relation.clone(),
                },
                interaction_claim.claimed_sum,
            ),
        }
    }

    pub fn components(&self) -> Vec<&dyn Component> {
        vec![&self.scalar as &dyn Component]
    }

    pub fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![&self.scalar as &dyn ComponentProver<SimdBackend>]
    }

    pub fn trace_log_degree_bounds(&self) -> TreeVec<ColumnVec<u32>> {
        self.scalar.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self) -> u32 {
        self.scalar.max_constraint_log_degree_bound()
    }
}

#[derive(Clone)]
pub struct FakeGlvScalarAirEval {
    pub log_size: u32,
    pub cert_relation: CertScalarInputRelation,
}

impl FrameworkEval for FakeGlvScalarAirEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.next_trace_mask();
        let cert = read_cert_relation_values(&mut eval);
        let row = FakeGlvScalarAirRow::read(&mut eval);
        let one = E::F::from(M31::from_u32_unchecked(1));

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        for value in cert.iter().cloned().chain(row.values()) {
            eval.add_constraint((one.clone() - active.clone()) * value);
        }
        eval.add_to_relation(RelationEntry::new(
            &self.cert_relation,
            E::EF::from(active.clone()),
            &cert,
        ));
        constrain_fake_glv_scalar_trivial(&mut eval, active, &cert, &row);
        eval.finalize_logup();
        eval
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

#[derive(Clone)]
struct FakeGlvScalarAirRow<F> {
    sig_id: F,
    cert_id: F,
    cert_active: F,
    cert_zero_active: F,
    scalar: P256BigInt<F>,
    s1: [F; FAKE_GLV_SMALL_LIMBS],
    s2_abs: [F; FAKE_GLV_SMALL_LIMBS],
    s2_sign_bit: F,
    q: [F; FAKE_GLV_SMALL_LIMBS],
}

impl<F: Clone> FakeGlvScalarAirRow<F> {
    fn values(&self) -> Vec<F> {
        let mut values = Vec::with_capacity(FAKE_GLV_SCALAR_ROW_COLUMNS);
        values.push(self.sig_id.clone());
        values.push(self.cert_id.clone());
        values.push(self.cert_active.clone());
        values.push(self.cert_zero_active.clone());
        values.extend(self.scalar.limbs().iter().cloned());
        values.extend(self.s1.iter().cloned());
        values.extend(self.s2_abs.iter().cloned());
        values.push(self.s2_sign_bit.clone());
        values.extend(self.q.iter().cloned());
        values
    }

}

impl<F> FakeGlvScalarAirRow<F> {
    fn read<E: EvalAtRow<F = F>>(eval: &mut E) -> Self {
        Self {
            sig_id: eval.next_trace_mask(),
            cert_id: eval.next_trace_mask(),
            cert_active: eval.next_trace_mask(),
            cert_zero_active: eval.next_trace_mask(),
            scalar: P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask())),
            s1: core::array::from_fn(|_| eval.next_trace_mask()),
            s2_abs: core::array::from_fn(|_| eval.next_trace_mask()),
            s2_sign_bit: eval.next_trace_mask(),
            q: core::array::from_fn(|_| eval.next_trace_mask()),
        }
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

pub fn gen_fake_glv_scalar_air_base_trace(
    certs: &CertScalarInputClaim,
    scalars: &FakeGlvScalarHintClaim,
    proof_claim: FakeGlvScalarAirProofClaim,
) -> ColumnVec<M31ColumnEval> {
    let row_count = 1usize << proof_claim.log_size;
    assert!(scalars.rows.len() <= row_count);
    assert_eq!(certs.rows.len(), scalars.rows.len());
    let mut columns =
        vec![vec![M31::from_u32_unchecked(0); row_count]; FAKE_GLV_SCALAR_TRACE_COLUMNS];
    for (row_index, (cert, scalar)) in certs.rows.iter().zip(&scalars.rows).enumerate() {
        let mut offset = 0usize;
        columns[offset][row_index] = M31::from_u32_unchecked(1);
        offset += 1;
        write_cert_relation_values(&mut columns, &mut offset, cert, row_index);
        write_fake_glv_scalar_row(&mut columns, &mut offset, scalar, row_index);
        debug_assert_eq!(offset, FAKE_GLV_SCALAR_TRACE_COLUMNS);
    }
    columns
        .into_iter()
        .map(|values| m31_column_eval(proof_claim.log_size, values))
        .collect()
}

pub(crate) fn gen_fake_glv_scalar_air_interaction_trace(
    base: &[M31ColumnEval],
    cert_relation: &CertScalarInputRelation,
) -> (ColumnVec<M31ColumnEval>, FakeGlvScalarAirInteractionClaim) {
    assert_eq!(base.len(), FAKE_GLV_SCALAR_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        col.write_frac(
            vec_row,
            PackedQM31::from(base[0].data[vec_row]),
            cert_relation.combine(&cert_packed_values_from_base(base, vec_row)),
        );
    }
    col.finalize_col();
    let (trace, claimed_sum) = logup.finalize_last();
    let cert_consumer_claimed_sum: SecureField = storage_rows(base)
        .filter(|row| row[0] != M31::from_u32_unchecked(0))
        .map(|row| -> SecureField {
            let denominator: SecureField = cert_relation.combine(&cert_values_from_base(&row));
            SecureField::from(row[0]) / denominator
        })
        .sum();
    (
        trace,
        FakeGlvScalarAirInteractionClaim {
            claimed_sum,
            cert_consumer_claimed_sum,
        },
    )
}

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

fn read_cert_relation_values<E: EvalAtRow>(
    eval: &mut E,
) -> [E::F; CERT_SCALAR_INPUT_RELATION_ARITY] {
    core::array::from_fn(|_| eval.next_trace_mask())
}

fn constrain_fake_glv_scalar_trivial<E: EvalAtRow>(
    eval: &mut E,
    active: E::F,
    cert: &[E::F; CERT_SCALAR_INPUT_RELATION_ARITY],
    row: &FakeGlvScalarAirRow<E::F>,
) {
    let zero = E::F::from(M31::from_u32_unchecked(0));
    let one = E::F::from(M31::from_u32_unchecked(1));
    let cert_scalar_start = 2;
    let cert_active = cert[2 + 3 * N_LIMBS + 3].clone();
    let cert_zero_active = cert[2 + 3 * N_LIMBS + 4].clone();

    eval.add_constraint(active.clone() * (row.sig_id.clone() - cert[0].clone()));
    eval.add_constraint(active.clone() * (row.cert_id.clone() - cert[1].clone()));
    eval.add_constraint(active.clone() * (row.cert_active.clone() - cert_active));
    eval.add_constraint(active.clone() * (row.cert_zero_active.clone() - cert_zero_active));
    for flag in [
        row.cert_active.clone(),
        row.cert_zero_active.clone(),
        row.s2_sign_bit.clone(),
    ] {
        eval.add_constraint(flag.clone() * (flag - one.clone()));
    }
    for limb in 0..N_LIMBS {
        eval.add_constraint(
            active.clone()
                * (row.scalar.limbs()[limb].clone() - cert[cert_scalar_start + limb].clone()),
        );
        if limb < FAKE_GLV_SMALL_LIMBS {
            eval.add_constraint(
                active.clone()
                    * (row.s1[limb].clone() - row.scalar.limbs()[limb].clone()),
            );
        } else {
            eval.add_constraint(active.clone() * row.scalar.limbs()[limb].clone());
        }
    }
    for limb in 0..FAKE_GLV_SMALL_LIMBS {
        let expected_s2 = if limb == 0 { one.clone() } else { zero.clone() };
        eval.add_constraint(row.cert_active.clone() * (row.s2_abs[limb].clone() - expected_s2));
        eval.add_constraint(row.cert_zero_active.clone() * row.s2_abs[limb].clone());
        eval.add_constraint(active.clone() * row.q[limb].clone());
    }
    eval.add_constraint(row.cert_active.clone() * (row.s2_sign_bit.clone() - one.clone()));
    eval.add_constraint(row.cert_zero_active.clone() * row.s2_sign_bit.clone());
}

fn write_cert_relation_values(
    columns: &mut [Vec<M31>],
    offset: &mut usize,
    row: &CertScalarInputRow,
    row_index: usize,
) {
    let values = cert_relation_values(row);
    for value in values {
        columns[*offset][row_index] = value;
        *offset += 1;
    }
}

fn cert_relation_values(row: &CertScalarInputRow) -> [M31; CERT_SCALAR_INPUT_RELATION_ARITY] {
    core::array::from_fn(|index| {
        if index == 0 {
            return row.sig_id;
        }
        if index == 1 {
            return row.cert_id;
        }
        let offset = index - 2;
        if offset < N_LIMBS {
            return row.scalar.limbs()[offset];
        }
        if offset < 2 * N_LIMBS {
            return row.base_x.limbs()[offset - N_LIMBS];
        }
        if offset < 3 * N_LIMBS {
            return row.base_y.limbs()[offset - 2 * N_LIMBS];
        }
        match offset - 3 * N_LIMBS {
            0 => row.base_inf,
            1 => row.scalar_is_zero,
            2 => row.scalar_is_nonzero,
            3 => row.cert_active,
            4 => row.cert_zero_active,
            _ => panic!("cert relation index {index} out of range"),
        }
    })
}

fn write_fake_glv_scalar_row(
    columns: &mut [Vec<M31>],
    offset: &mut usize,
    row: &FakeGlvScalarHintRow,
    row_index: usize,
) {
    columns[*offset][row_index] = row.sig_id;
    *offset += 1;
    columns[*offset][row_index] = row.cert_id;
    *offset += 1;
    columns[*offset][row_index] = row.cert_active;
    *offset += 1;
    columns[*offset][row_index] = row.cert_zero_active;
    *offset += 1;
    for value in row.scalar.limbs() {
        columns[*offset][row_index] = *value;
        *offset += 1;
    }
    for value in row.hint.s1.limbs {
        columns[*offset][row_index] = value;
        *offset += 1;
    }
    for value in row.hint.s2_abs.limbs {
        columns[*offset][row_index] = value;
        *offset += 1;
    }
    columns[*offset][row_index] = row.hint.s2_sign_bit;
    *offset += 1;
    for value in row.hint.q.limbs {
        columns[*offset][row_index] = value;
        *offset += 1;
    }
}

fn cert_packed_values_from_base(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; CERT_SCALAR_INPUT_RELATION_ARITY] {
    core::array::from_fn(|index| base[1 + index].data[vec_row])
}

fn cert_values_from_base(row: &[M31]) -> [M31; CERT_SCALAR_INPUT_RELATION_ARITY] {
    core::array::from_fn(|index| row[1 + index])
}

fn storage_rows(base: &[M31ColumnEval]) -> impl Iterator<Item = Vec<M31>> + '_ {
    let row_count = base[0].domain.size();
    (0..row_count).map(|row| {
        let vec_row = row / (1 << LOG_N_LANES);
        let lane = row % (1 << LOG_N_LANES);
        base.iter()
            .map(|column| column.data[vec_row].to_array()[lane])
            .collect::<Vec<_>>()
    })
}

fn secure_zero() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(0))
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
