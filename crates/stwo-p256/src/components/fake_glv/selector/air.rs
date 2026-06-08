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
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    TraceLocationAllocator,
};

use crate::scalar::fake_glv_scalar::{
    FakeGlvScalarHintClaim, FakeGlvScalarHintRow, FakeGlvScalarRelation, FakeGlvSmallScalar,
    FAKE_GLV_SCALAR_RELATION_ARITY, FAKE_GLV_SMALL_LIMBS,
};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};

pub const FAKE_GLV_SELECTOR_CHUNKS: usize = 63;
const FAKE_GLV_SELECTOR_LIMB_CARRIES: usize = FAKE_GLV_SMALL_LIMBS;
pub const FAKE_GLV_SELECTOR_TRACE_COLUMNS: usize =
    1 + FAKE_GLV_SCALAR_RELATION_ARITY + FAKE_GLV_SELECTOR_ROW_COLUMNS;
const FAKE_GLV_SELECTOR_ROW_COLUMNS: usize =
    7 + 3 * FAKE_GLV_SELECTOR_CHUNKS + 2 + FAKE_GLV_SELECTOR_LIMB_CARRIES;
const SCALAR_RELATION_S1_START: usize = 2;
const SCALAR_RELATION_S2_START: usize = SCALAR_RELATION_S1_START + FAKE_GLV_SMALL_LIMBS;
const SCALAR_RELATION_SIGN: usize = SCALAR_RELATION_S2_START + FAKE_GLV_SMALL_LIMBS;
const SCALAR_RELATION_ACTIVE: usize = SCALAR_RELATION_SIGN + 1;

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

pub type FakeGlvSelectorAirComponent = FrameworkComponent<FakeGlvSelectorAirEval>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FakeGlvSelectorAirProofClaim {
    pub log_size: u32,
}

impl FakeGlvSelectorAirProofClaim {
    pub fn from_claim(claim: &FakeGlvSelectorClaim) -> Self {
        Self {
            log_size: padded_log_size(claim.rows.len()),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FakeGlvSelectorAirInteractionClaim {
    pub claimed_sum: SecureField,
    pub scalar_consumer_claimed_sum: SecureField,
}

impl FakeGlvSelectorAirInteractionClaim {
    pub fn zero() -> Self {
        Self {
            claimed_sum: secure_zero(),
            scalar_consumer_claimed_sum: secure_zero(),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}

pub struct FakeGlvSelectorAirComponents {
    pub selector: FakeGlvSelectorAirComponent,
}

impl FakeGlvSelectorAirComponents {
    pub(crate) fn new(
        allocator: &mut TraceLocationAllocator,
        claim: FakeGlvSelectorAirProofClaim,
        interaction_claim: &FakeGlvSelectorAirInteractionClaim,
        relation: &FakeGlvScalarRelation,
    ) -> Self {
        Self {
            selector: FakeGlvSelectorAirComponent::new(
                allocator,
                FakeGlvSelectorAirEval {
                    log_size: claim.log_size,
                    scalar_relation: relation.clone(),
                },
                interaction_claim.claimed_sum,
            ),
        }
    }

    pub fn components(&self) -> Vec<&dyn Component> {
        vec![&self.selector as &dyn Component]
    }

    pub fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![&self.selector as &dyn ComponentProver<SimdBackend>]
    }

    pub fn trace_log_degree_bounds(&self) -> TreeVec<ColumnVec<u32>> {
        self.selector.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self) -> u32 {
        self.selector.max_constraint_log_degree_bound()
    }
}

#[derive(Clone)]
pub struct FakeGlvSelectorAirEval {
    pub log_size: u32,
    pub scalar_relation: FakeGlvScalarRelation,
}

impl FrameworkEval for FakeGlvSelectorAirEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.next_trace_mask();
        let scalar: [E::F; FAKE_GLV_SCALAR_RELATION_ARITY] =
            core::array::from_fn(|_| eval.next_trace_mask());
        let row = FakeGlvSelectorAirRow::read(&mut eval);
        let one = E::F::from(M31::from_u32_unchecked(1));
        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        for value in scalar.iter().cloned().chain(row.values()) {
            eval.add_constraint((one.clone() - active.clone()) * value);
        }
        eval.add_to_relation(RelationEntry::new(
            &self.scalar_relation,
            E::EF::from(active.clone()),
            &scalar,
        ));
        constrain_selector_from_trivial_scalar(&mut eval, active, &scalar, &row);
        eval.finalize_logup();
        eval
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

#[derive(Clone)]
struct FakeGlvSelectorAirRow<F> {
    sig_id: F,
    cert_id: F,
    cert_active: F,
    s1_lsb: F,
    s2_lsb: F,
    s1_msb: F,
    s2_msb: F,
    selectors: [F; FAKE_GLV_SELECTOR_CHUNKS],
    selector_low_bits: [F; FAKE_GLV_SELECTOR_CHUNKS],
    selector_high_bits: [F; FAKE_GLV_SELECTOR_CHUNKS],
    selector_final: F,
    init_base_index: F,
    carries: [F; FAKE_GLV_SELECTOR_LIMB_CARRIES],
}

impl<F: Clone> FakeGlvSelectorAirRow<F> {
    fn values(&self) -> Vec<F> {
        let mut values = Vec::with_capacity(FAKE_GLV_SELECTOR_ROW_COLUMNS);
        values.push(self.sig_id.clone());
        values.push(self.cert_id.clone());
        values.push(self.cert_active.clone());
        values.push(self.s1_lsb.clone());
        values.push(self.s2_lsb.clone());
        values.push(self.s1_msb.clone());
        values.push(self.s2_msb.clone());
        values.extend(self.selectors.iter().cloned());
        values.extend(self.selector_low_bits.iter().cloned());
        values.extend(self.selector_high_bits.iter().cloned());
        values.push(self.selector_final.clone());
        values.push(self.init_base_index.clone());
        values.extend(self.carries.iter().cloned());
        values
    }
}

impl<F> FakeGlvSelectorAirRow<F> {
    fn read<E: EvalAtRow<F = F>>(eval: &mut E) -> Self {
        Self {
            sig_id: eval.next_trace_mask(),
            cert_id: eval.next_trace_mask(),
            cert_active: eval.next_trace_mask(),
            s1_lsb: eval.next_trace_mask(),
            s2_lsb: eval.next_trace_mask(),
            s1_msb: eval.next_trace_mask(),
            s2_msb: eval.next_trace_mask(),
            selectors: core::array::from_fn(|_| eval.next_trace_mask()),
            selector_low_bits: core::array::from_fn(|_| eval.next_trace_mask()),
            selector_high_bits: core::array::from_fn(|_| eval.next_trace_mask()),
            selector_final: eval.next_trace_mask(),
            init_base_index: eval.next_trace_mask(),
            carries: core::array::from_fn(|_| eval.next_trace_mask()),
        }
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

pub fn gen_fake_glv_selector_air_base_trace(
    scalars: &FakeGlvScalarHintClaim,
    selectors: &FakeGlvSelectorClaim,
    proof_claim: FakeGlvSelectorAirProofClaim,
) -> ColumnVec<M31ColumnEval> {
    let row_count = 1usize << proof_claim.log_size;
    assert!(selectors.rows.len() <= row_count);
    assert_eq!(scalars.rows.len(), selectors.rows.len());
    let mut columns =
        vec![vec![M31::from_u32_unchecked(0); row_count]; FAKE_GLV_SELECTOR_TRACE_COLUMNS];
    for (row_index, (scalar, selector)) in scalars.rows.iter().zip(&selectors.rows).enumerate() {
        let mut offset = 0usize;
        columns[offset][row_index] = M31::from_u32_unchecked(1);
        offset += 1;
        write_scalar_relation_values(&mut columns, &mut offset, scalar, row_index);
        write_selector_row(&mut columns, &mut offset, scalar, selector, row_index);
        debug_assert_eq!(offset, FAKE_GLV_SELECTOR_TRACE_COLUMNS);
    }
    columns
        .into_iter()
        .map(|values| m31_column_eval(proof_claim.log_size, values))
        .collect()
}

pub(crate) fn gen_fake_glv_selector_air_interaction_trace(
    base: &[M31ColumnEval],
    relation: &FakeGlvScalarRelation,
) -> (ColumnVec<M31ColumnEval>, FakeGlvSelectorAirInteractionClaim) {
    assert_eq!(base.len(), FAKE_GLV_SELECTOR_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        col.write_frac(
            vec_row,
            PackedQM31::from(base[0].data[vec_row]),
            relation.combine(&scalar_packed_values_from_selector_base(base, vec_row)),
        );
    }
    col.finalize_col();
    let (trace, claimed_sum) = logup.finalize_last();
    let scalar_consumer_claimed_sum: SecureField = storage_rows(base)
        .filter(|row| row[0] != M31::from_u32_unchecked(0))
        .map(|row| -> SecureField {
            let denominator: SecureField =
                relation.combine(&scalar_values_from_selector_base(&row));
            SecureField::from(row[0]) / denominator
        })
        .sum();
    (
        trace,
        FakeGlvSelectorAirInteractionClaim {
            claimed_sum,
            scalar_consumer_claimed_sum,
        },
    )
}

fn constrain_selector_from_trivial_scalar<E: EvalAtRow>(
    eval: &mut E,
    active: E::F,
    scalar: &[E::F; FAKE_GLV_SCALAR_RELATION_ARITY],
    row: &FakeGlvSelectorAirRow<E::F>,
) {
    let zero = E::F::from(M31::from_u32_unchecked(0));
    let one = E::F::from(M31::from_u32_unchecked(1));
    let two = E::F::from(M31::from_u32_unchecked(2));
    let four = E::F::from(M31::from_u32_unchecked(4));
    let five = E::F::from(M31::from_u32_unchecked(5));
    let base = E::F::from(M31::from_u32_unchecked(1 << 13));
    let cert_active = scalar[SCALAR_RELATION_ACTIVE].clone();
    let inactive = active.clone() - cert_active.clone();

    eval.add_constraint(active.clone() * (row.sig_id.clone() - scalar[0].clone()));
    eval.add_constraint(active.clone() * (row.cert_id.clone() - scalar[1].clone()));
    eval.add_constraint(active.clone() * (row.cert_active.clone() - cert_active.clone()));

    for flag in [
        row.cert_active.clone(),
        row.s1_lsb.clone(),
        row.s2_lsb.clone(),
        row.s1_msb.clone(),
        row.s2_msb.clone(),
    ] {
        eval.add_constraint(flag.clone() * (flag - one.clone()));
    }
    for ((selector, low_bit), high_bit) in row
        .selectors
        .iter()
        .zip(&row.selector_low_bits)
        .zip(&row.selector_high_bits)
    {
        eval.add_constraint(low_bit.clone() * (low_bit.clone() - one.clone()));
        eval.add_constraint(high_bit.clone() * (high_bit.clone() - one.clone()));
        eval.add_constraint(
            active.clone()
                * (selector.clone() - low_bit.clone() - two.clone() * high_bit.clone()),
        );
    }
    for carry in &row.carries {
        eval.add_constraint(carry.clone() * (carry.clone() - one.clone()));
    }

    eval.add_constraint(row.cert_active.clone() * (row.s2_lsb.clone() - one.clone()));
    eval.add_constraint(inactive.clone() * row.s2_lsb.clone());
    eval.add_constraint(active.clone() * row.s2_msb.clone());
    eval.add_constraint(active.clone() * (scalar[SCALAR_RELATION_S2_START].clone() - cert_active.clone()));
    for limb in 1..FAKE_GLV_SMALL_LIMBS {
        eval.add_constraint(active.clone() * scalar[SCALAR_RELATION_S2_START + limb].clone());
    }
    eval.add_constraint(active.clone() * (scalar[SCALAR_RELATION_SIGN].clone() - cert_active.clone()));

    let mut previous_carry = zero.clone();
    for limb in 0..FAKE_GLV_SMALL_LIMBS {
        let contribution = selector_limb_contribution(row, limb);
        let carry_out = row.carries[limb].clone();
        eval.add_constraint(
            active.clone()
                * (previous_carry + contribution
                    - scalar[SCALAR_RELATION_S1_START + limb].clone()
                    - base.clone() * carry_out.clone()),
        );
        previous_carry = carry_out;
    }
    eval.add_constraint(active.clone() * previous_carry);

    eval.add_constraint(inactive.clone() * row.s1_lsb.clone());
    eval.add_constraint(inactive.clone() * row.s1_msb.clone());
    for selector in &row.selectors {
        eval.add_constraint(inactive.clone() * selector.clone());
    }
    for bit in row.selector_low_bits.iter().chain(&row.selector_high_bits) {
        eval.add_constraint(inactive.clone() * bit.clone());
    }
    for carry in &row.carries {
        eval.add_constraint(inactive.clone() * carry.clone());
    }

    eval.add_constraint(
        row.cert_active.clone()
            * (row.selector_final.clone() - five.clone() - row.s1_msb.clone()
                - four.clone() * row.s2_msb.clone()),
    );
    eval.add_constraint(inactive.clone() * row.selector_final.clone());
    eval.add_constraint(
        row.cert_active.clone()
            * (row.init_base_index.clone() - two.clone() - row.s1_msb.clone()
                - four * row.s2_msb.clone()),
    );
    eval.add_constraint(inactive * row.init_base_index.clone());
}

fn selector_limb_contribution<F>(row: &FakeGlvSelectorAirRow<F>, limb: usize) -> F
where
    F: Clone
        + std::ops::Add<Output = F>
        + std::ops::Mul<Output = F>
        + From<M31>,
{
    let mut contribution = F::from(M31::from_u32_unchecked(0));
    if limb == 0 {
        contribution = contribution + row.s1_lsb.clone();
    }
    for (index, selector) in row.selectors.iter().enumerate() {
        let start_bit = 1 + 2 * index;
        if start_bit / 13 == limb {
            contribution = contribution
                + selector.clone() * F::from(M31::from_u32_unchecked(1 << (start_bit % 13)));
        }
    }
    if 127 / 13 == limb {
        contribution =
            contribution + row.s1_msb.clone() * F::from(M31::from_u32_unchecked(1 << (127 % 13)));
    }
    contribution
}

fn write_scalar_relation_values(
    columns: &mut [Vec<M31>],
    offset: &mut usize,
    row: &FakeGlvScalarHintRow,
    row_index: usize,
) {
    let values = fake_glv_scalar_relation_values(row);
    for value in values {
        columns[*offset][row_index] = value;
        *offset += 1;
    }
}

fn fake_glv_scalar_relation_values(
    row: &FakeGlvScalarHintRow,
) -> [M31; FAKE_GLV_SCALAR_RELATION_ARITY] {
    core::array::from_fn(|index| {
        if index == 0 {
            return row.sig_id;
        }
        if index == 1 {
            return row.cert_id;
        }
        let offset = index - 2;
        if offset < FAKE_GLV_SMALL_LIMBS {
            return row.hint.s1.limbs[offset];
        }
        if offset < 2 * FAKE_GLV_SMALL_LIMBS {
            return row.hint.s2_abs.limbs[offset - FAKE_GLV_SMALL_LIMBS];
        }
        match offset - 2 * FAKE_GLV_SMALL_LIMBS {
            0 => row.hint.s2_sign_bit,
            1 => row.cert_active,
            _ => panic!("fake GLV scalar relation index {index} out of range"),
        }
    })
}

fn write_selector_row(
    columns: &mut [Vec<M31>],
    offset: &mut usize,
    scalar: &FakeGlvScalarHintRow,
    row: &FakeGlvSelectorRow,
    row_index: usize,
) {
    columns[*offset][row_index] = row.sig_id;
    *offset += 1;
    columns[*offset][row_index] = row.cert_id;
    *offset += 1;
    columns[*offset][row_index] = row.cert_active;
    *offset += 1;
    columns[*offset][row_index] = row.s1_lsb;
    *offset += 1;
    columns[*offset][row_index] = row.s2_lsb;
    *offset += 1;
    columns[*offset][row_index] = row.s1_msb;
    *offset += 1;
    columns[*offset][row_index] = row.s2_msb;
    *offset += 1;
    for selector in row.selectors {
        columns[*offset][row_index] = selector;
        *offset += 1;
    }
    for selector in row.selectors {
        columns[*offset][row_index] = M31::from_u32_unchecked(selector.0 & 1);
        *offset += 1;
    }
    for selector in row.selectors {
        columns[*offset][row_index] = M31::from_u32_unchecked((selector.0 >> 1) & 1);
        *offset += 1;
    }
    columns[*offset][row_index] = row.selector_final;
    *offset += 1;
    columns[*offset][row_index] = row.init_base_index;
    *offset += 1;
    for carry in selector_reconstruction_carries(scalar, row) {
        columns[*offset][row_index] = carry;
        *offset += 1;
    }
}

fn selector_reconstruction_carries(
    scalar: &FakeGlvScalarHintRow,
    selector: &FakeGlvSelectorRow,
) -> [M31; FAKE_GLV_SELECTOR_LIMB_CARRIES] {
    let mut carries = [M31::from_u32_unchecked(0); FAKE_GLV_SELECTOR_LIMB_CARRIES];
    let mut carry = 0i64;
    for (limb, carry_out_slot) in carries.iter_mut().enumerate() {
        let total = carry + selector_limb_contribution_u32(selector, limb) as i64;
        let target = scalar.hint.s1.limbs[limb].0 as i64;
        let diff = total - target;
        debug_assert_eq!(diff % (1 << 13), 0);
        carry = diff / (1 << 13);
        debug_assert!(carry == 0 || carry == 1);
        *carry_out_slot = M31::from_u32_unchecked(carry as u32);
    }
    debug_assert_eq!(carry, 0);
    carries
}

fn selector_limb_contribution_u32(row: &FakeGlvSelectorRow, limb: usize) -> u32 {
    let mut contribution = 0u32;
    if limb == 0 {
        contribution += row.s1_lsb.0;
    }
    for (index, selector) in row.selectors.iter().enumerate() {
        let start_bit = 1 + 2 * index;
        if start_bit / 13 == limb {
            contribution += selector.0 * (1 << (start_bit % 13));
        }
    }
    if 127 / 13 == limb {
        contribution += row.s1_msb.0 * (1 << (127 % 13));
    }
    contribution
}

fn scalar_packed_values_from_selector_base(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; FAKE_GLV_SCALAR_RELATION_ARITY] {
    core::array::from_fn(|index| base[1 + index].data[vec_row])
}

fn scalar_values_from_selector_base(row: &[M31]) -> [M31; FAKE_GLV_SCALAR_RELATION_ARITY] {
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
