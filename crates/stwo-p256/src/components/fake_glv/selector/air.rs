use serde::{Deserialize, Serialize};
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
    // sig_id, cert_id, cert_active, s1_lsb, s2_lsb, s1_msb, s2_msb            (7)
    // selectors, s1 low/high bits, s2 low/high bits                          (5·CHUNKS)
    // selector_final, init_base_index                                        (2)
    // s1 reconstruction carries, s2 reconstruction carries                   (2·CARRIES)
    7 + 5 * FAKE_GLV_SELECTOR_CHUNKS + 2 + 2 * FAKE_GLV_SELECTOR_LIMB_CARRIES;
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FakeGlvSelectorAirInteractionClaim {
    pub claimed_sum: SecureField,
}

impl FakeGlvSelectorAirInteractionClaim {
    pub fn zero() -> Self {
        Self {
            claimed_sum: secure_zero(),
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
        constrain_selector_from_scalar(&mut eval, active, &scalar, &row);
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
    /// Bit 0 / bit 1 of the 2-bit `s1` chunk (= low two bits of `selector`).
    selector_low_bits: [F; FAKE_GLV_SELECTOR_CHUNKS],
    selector_high_bits: [F; FAKE_GLV_SELECTOR_CHUNKS],
    /// Bit 0 / bit 1 of the 2-bit `s2` chunk (= high two bits of `selector`).
    selector_s2_low_bits: [F; FAKE_GLV_SELECTOR_CHUNKS],
    selector_s2_high_bits: [F; FAKE_GLV_SELECTOR_CHUNKS],
    selector_final: F,
    init_base_index: F,
    /// `s1` reconstruction limb carries.
    carries: [F; FAKE_GLV_SELECTOR_LIMB_CARRIES],
    /// `s2_abs` reconstruction limb carries.
    s2_carries: [F; FAKE_GLV_SELECTOR_LIMB_CARRIES],
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
        values.extend(self.selector_s2_low_bits.iter().cloned());
        values.extend(self.selector_s2_high_bits.iter().cloned());
        values.push(self.selector_final.clone());
        values.push(self.init_base_index.clone());
        values.extend(self.carries.iter().cloned());
        values.extend(self.s2_carries.iter().cloned());
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
            selector_s2_low_bits: core::array::from_fn(|_| eval.next_trace_mask()),
            selector_s2_high_bits: core::array::from_fn(|_| eval.next_trace_mask()),
            selector_final: eval.next_trace_mask(),
            init_base_index: eval.next_trace_mask(),
            carries: core::array::from_fn(|_| eval.next_trace_mask()),
            s2_carries: core::array::from_fn(|_| eval.next_trace_mask()),
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
    (trace, FakeGlvSelectorAirInteractionClaim { claimed_sum })
}

/// Constrain the selector reconstruction for an ARBITRARY fake-GLV
/// decomposition (`s1`, `s2_abs` each a 128-bit half-scalar, `s2_sign_bit` free).
///
/// Each `selector[i] ∈ {0..15}` packs two 2-bit chunks:
/// `selector[i] = s1_chunk[i] + 4·s2_chunk[i]`, where `s1_chunk[i]` is bits
/// `(1+2i, 2+2i)` of `s1` and `s2_chunk[i]` the same bits of `s2_abs`. The four
/// chunk bits are witnessed (`selector_{low,high}_bits`,
/// `selector_s2_{low,high}_bits`), boolean-constrained, and tied to `selector`.
/// Two independent borrow-free 13-bit carry chains then reconstruct `s1` and
/// `s2_abs` from their chunk bits + `{s1,s2}_{lsb,msb}` and bind them to the
/// `FakeGlvScalarRelation` tuple (so the selector cannot reconstruct a different
/// `(s1, s2_abs)` than the one the scalar AIR proved satisfies
/// `scalar · s2_abs ≡ selected_s1 (mod n)`). `s2_sign_bit` flows through the
/// relation tuple untouched (consumed by the signed-operand component).
fn constrain_selector_from_scalar<E: EvalAtRow>(
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
    // Each selector decomposes into a 2-bit `s1` chunk (low two bits) and a
    // 2-bit `s2` chunk (high two bits): `selector = (b0 + 2·b1) + 4·(c0 + 2·c1)`.
    for ((((selector, low_bit), high_bit), s2_low), s2_high) in row
        .selectors
        .iter()
        .zip(&row.selector_low_bits)
        .zip(&row.selector_high_bits)
        .zip(&row.selector_s2_low_bits)
        .zip(&row.selector_s2_high_bits)
    {
        for bit in [low_bit, high_bit, s2_low, s2_high] {
            eval.add_constraint(bit.clone() * (bit.clone() - one.clone()));
        }
        let s1_chunk = low_bit.clone() + two.clone() * high_bit.clone();
        let s2_chunk = s2_low.clone() + two.clone() * s2_high.clone();
        eval.add_constraint(
            active.clone() * (selector.clone() - s1_chunk - four.clone() * s2_chunk),
        );
    }
    for carry in row.carries.iter().chain(&row.s2_carries) {
        eval.add_constraint(carry.clone() * (carry.clone() - one.clone()));
    }

    // `s1` reconstruction: limb-by-limb 13-bit carry chain over the s1 chunk
    // bits + `s1_lsb`/`s1_msb`, bound to the relation's `s1` limbs.
    let mut previous_carry = zero.clone();
    for limb in 0..FAKE_GLV_SMALL_LIMBS {
        let contribution = s1_limb_contribution(row, limb);
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

    // `s2_abs` reconstruction: the symmetric chain over the s2 chunk bits +
    // `s2_lsb`/`s2_msb`, bound to the relation's `s2_abs` limbs.
    let mut previous_carry = zero.clone();
    for limb in 0..FAKE_GLV_SMALL_LIMBS {
        let contribution = s2_limb_contribution(row, limb);
        let carry_out = row.s2_carries[limb].clone();
        eval.add_constraint(
            active.clone()
                * (previous_carry + contribution
                    - scalar[SCALAR_RELATION_S2_START + limb].clone()
                    - base.clone() * carry_out.clone()),
        );
        previous_carry = carry_out;
    }
    eval.add_constraint(active.clone() * previous_carry);

    eval.add_constraint(inactive.clone() * row.s1_lsb.clone());
    eval.add_constraint(inactive.clone() * row.s1_msb.clone());
    eval.add_constraint(inactive.clone() * row.s2_lsb.clone());
    eval.add_constraint(inactive.clone() * row.s2_msb.clone());
    for selector in &row.selectors {
        eval.add_constraint(inactive.clone() * selector.clone());
    }
    for bit in row
        .selector_low_bits
        .iter()
        .chain(&row.selector_high_bits)
        .chain(&row.selector_s2_low_bits)
        .chain(&row.selector_s2_high_bits)
    {
        eval.add_constraint(inactive.clone() * bit.clone());
    }
    for carry in row.carries.iter().chain(&row.s2_carries) {
        eval.add_constraint(inactive.clone() * carry.clone());
    }

    eval.add_constraint(
        row.cert_active.clone()
            * (row.selector_final.clone()
                - five.clone()
                - row.s1_msb.clone()
                - four.clone() * row.s2_msb.clone()),
    );
    eval.add_constraint(inactive.clone() * row.selector_final.clone());
    eval.add_constraint(
        row.cert_active.clone()
            * (row.init_base_index.clone()
                - two.clone()
                - row.s1_msb.clone()
                - four * row.s2_msb.clone()),
    );
    eval.add_constraint(inactive * row.init_base_index.clone());
}

/// `s1` limb `limb` contribution from the 2-bit s1 chunks (`b0 + 2·b1`) plus the
/// `s1_lsb` (bit 0) and `s1_msb` (bit 127) boundary bits.
fn s1_limb_contribution<F>(row: &FakeGlvSelectorAirRow<F>, limb: usize) -> F
where
    F: Clone + std::ops::Add<Output = F> + std::ops::Mul<Output = F> + From<M31>,
{
    chunk_limb_contribution(
        limb,
        &row.selector_low_bits,
        &row.selector_high_bits,
        row.s1_lsb.clone(),
        row.s1_msb.clone(),
    )
}

/// `s2_abs` limb `limb` contribution — the symmetric helper over the s2 chunk
/// bits and `s2_lsb`/`s2_msb`.
fn s2_limb_contribution<F>(row: &FakeGlvSelectorAirRow<F>, limb: usize) -> F
where
    F: Clone + std::ops::Add<Output = F> + std::ops::Mul<Output = F> + From<M31>,
{
    chunk_limb_contribution(
        limb,
        &row.selector_s2_low_bits,
        &row.selector_s2_high_bits,
        row.s2_lsb.clone(),
        row.s2_msb.clone(),
    )
}

/// Shared 13-bit limb contribution for a 128-bit half-scalar reconstructed from
/// `lsb` (bit 0), 63 two-bit chunks (`low + 2·high` at bits `1+2i`), and `msb`
/// (bit 127). Identical layout for `s1` and `s2_abs`.
fn chunk_limb_contribution<F>(
    limb: usize,
    low_bits: &[F; FAKE_GLV_SELECTOR_CHUNKS],
    high_bits: &[F; FAKE_GLV_SELECTOR_CHUNKS],
    lsb: F,
    msb: F,
) -> F
where
    F: Clone + std::ops::Add<Output = F> + std::ops::Mul<Output = F> + From<M31>,
{
    let two = F::from(M31::from_u32_unchecked(2));
    let mut contribution = F::from(M31::from_u32_unchecked(0));
    if limb == 0 {
        contribution = contribution + lsb;
    }
    for (index, (low_bit, high_bit)) in low_bits.iter().zip(high_bits).enumerate() {
        let start_bit = 1 + 2 * index;
        if start_bit / 13 == limb {
            let chunk = low_bit.clone() + two.clone() * high_bit.clone();
            contribution =
                contribution + chunk * F::from(M31::from_u32_unchecked(1 << (start_bit % 13)));
        }
    }
    if 127 / 13 == limb {
        contribution = contribution + msb * F::from(M31::from_u32_unchecked(1 << (127 % 13)));
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
    // s1 chunk bits (low two bits of `selector`).
    for selector in row.selectors {
        columns[*offset][row_index] = M31::from_u32_unchecked(selector.0 & 1);
        *offset += 1;
    }
    for selector in row.selectors {
        columns[*offset][row_index] = M31::from_u32_unchecked((selector.0 >> 1) & 1);
        *offset += 1;
    }
    // s2 chunk bits (high two bits of `selector`).
    for selector in row.selectors {
        columns[*offset][row_index] = M31::from_u32_unchecked((selector.0 >> 2) & 1);
        *offset += 1;
    }
    for selector in row.selectors {
        columns[*offset][row_index] = M31::from_u32_unchecked((selector.0 >> 3) & 1);
        *offset += 1;
    }
    columns[*offset][row_index] = row.selector_final;
    *offset += 1;
    columns[*offset][row_index] = row.init_base_index;
    *offset += 1;
    for carry in selector_reconstruction_carries(scalar, row, ChunkSource::S1) {
        columns[*offset][row_index] = carry;
        *offset += 1;
    }
    for carry in selector_reconstruction_carries(scalar, row, ChunkSource::S2) {
        columns[*offset][row_index] = carry;
        *offset += 1;
    }
}

/// Which half-scalar a reconstruction chain targets.
#[derive(Clone, Copy)]
enum ChunkSource {
    S1,
    S2,
}

fn selector_reconstruction_carries(
    scalar: &FakeGlvScalarHintRow,
    selector: &FakeGlvSelectorRow,
    source: ChunkSource,
) -> [M31; FAKE_GLV_SELECTOR_LIMB_CARRIES] {
    let target_limbs = match source {
        ChunkSource::S1 => &scalar.hint.s1.limbs,
        ChunkSource::S2 => &scalar.hint.s2_abs.limbs,
    };
    let mut carries = [M31::from_u32_unchecked(0); FAKE_GLV_SELECTOR_LIMB_CARRIES];
    let mut carry = 0i64;
    for (limb, carry_out_slot) in carries.iter_mut().enumerate() {
        let total = carry + selector_limb_contribution_u32(selector, limb, source) as i64;
        let target = target_limbs[limb].0 as i64;
        let diff = total - target;
        debug_assert_eq!(diff % (1 << 13), 0);
        carry = diff / (1 << 13);
        debug_assert!(carry == 0 || carry == 1);
        *carry_out_slot = M31::from_u32_unchecked(carry as u32);
    }
    debug_assert_eq!(carry, 0);
    carries
}

fn selector_limb_contribution_u32(
    row: &FakeGlvSelectorRow,
    limb: usize,
    source: ChunkSource,
) -> u32 {
    // s1 chunk = `selector % 4` (low two bits); s2 chunk = `selector / 4` (high
    // two bits). lsb/msb are this half-scalar's boundary bits.
    let (lsb, msb, chunk_of): (u32, u32, fn(u32) -> u32) = match source {
        ChunkSource::S1 => (row.s1_lsb.0, row.s1_msb.0, |selector| selector % 4),
        ChunkSource::S2 => (row.s2_lsb.0, row.s2_msb.0, |selector| selector / 4),
    };
    let mut contribution = 0u32;
    if limb == 0 {
        contribution += lsb;
    }
    for (index, selector) in row.selectors.iter().enumerate() {
        let start_bit = 1 + 2 * index;
        if start_bit / 13 == limb {
            contribution += chunk_of(selector.0) * (1 << (start_bit % 13));
        }
    }
    if 127 / 13 == limb {
        contribution += msb * (1 << (127 % 13));
    }
    contribution
}

fn scalar_packed_values_from_selector_base(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; FAKE_GLV_SCALAR_RELATION_ARITY] {
    core::array::from_fn(|index| base[1 + index].data[vec_row])
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

    /// Recording `EvalAtRow` for the selector AIR: serves base-trace masks in
    /// read order, records each polynomial constraint, skips the one LogUp
    /// relation (the reconstruction pins are pure polynomial constraints).
    struct RecordingSelectorEvaluator<'a> {
        base: &'a [Vec<M31>],
        col_index: usize,
        row: usize,
        constraints: Vec<SecureField>,
    }

    impl stwo_constraint_framework::EvalAtRow for RecordingSelectorEvaluator<'_> {
        type F = M31;
        type EF = SecureField;

        fn next_interaction_mask<const N: usize>(
            &mut self,
            interaction: usize,
            offsets: [isize; N],
        ) -> [M31; N] {
            assert_eq!(interaction, 1, "selector AIR reads only the base trace");
            let col = self.col_index;
            self.col_index += 1;
            offsets.map(|offset| {
                assert_eq!(offset, 0, "selector AIR reads only offset-0 masks");
                self.base[col][self.row]
            })
        }

        fn add_constraint<G>(&mut self, constraint: G)
        where
            Self::EF: std::ops::Mul<G, Output = Self::EF> + From<G>,
        {
            self.constraints.push(Self::EF::from(constraint));
        }

        fn combine_ef(values: [M31; 4]) -> SecureField {
            SecureField::from_m31_array(values)
        }

        fn add_to_relation<R: stwo_constraint_framework::Relation<M31, SecureField>>(
            &mut self,
            _entry: stwo_constraint_framework::RelationEntry<'_, M31, SecureField, R>,
        ) {
        }

        fn finalize_logup(&mut self) {}
        fn finalize_logup_in_pairs(&mut self) {}
    }

    fn selector_air_constraints_hold(base: &[Vec<M31>], log_size: u32) -> bool {
        use num_traits::Zero;
        for row in 0..(1usize << log_size) {
            let recorder = RecordingSelectorEvaluator {
                base,
                col_index: 0,
                row,
                constraints: Vec::new(),
            };
            let recorder = FakeGlvSelectorAirEval {
                log_size,
                scalar_relation: FakeGlvScalarRelation::dummy(),
            }
            .evaluate(recorder);
            if recorder.constraints.iter().any(|value| !value.is_zero()) {
                return false;
            }
        }
        true
    }

    /// Gap A: the selector AIR's polynomial constraints must hold for an
    /// ARBITRARY fake-GLV decomposition (`s2_abs != 1`, real 128-bit halves) —
    /// the case the previous trivial-only constraint (`s2_lsb = 1`,
    /// `s2_msb = 0`, `s2[0] = cert_active`) rejected. Builds the
    /// `FakeGlvScalarHint::decompose` hint for a near-order scalar, generates the
    /// selector trace, and asserts the AIR accepts it; then asserts a tampered
    /// `s2_abs` reconstruction limb is rejected (the s2 carry chain fires).
    #[test]
    fn fake_glv_selector_air_accepts_arbitrary_s2() {
        use crate::limbs::P256M31BigInt;
        use crate::scalar::scalar_mod_mul::columns::padded_log_size;

        // A mid-range scalar (all four 64-bit limbs distinct, top limb well
        // below n's top limb) decomposes into genuinely non-trivial 128-bit
        // halves with `s2_abs != 1` — the case the trivial-only constraint
        // refused.
        let scalar = P256M31BigInt::from_u256(&U256::from_le_u64s(&[
            0x1234_5678_9abc_def0,
            0xfedc_ba98_7654_3210,
            0x0f1e_2d3c_4b5a_6978,
            0x1122_3344_5566_7788,
        ]));
        let hint = FakeGlvScalarHint::decompose(&scalar).expect("arbitrary hint decomposes");
        assert!(
            small_scalar_to_u128(&hint.s2_abs) > 1,
            "fixture must exercise the non-trivial s2 path (got s2_abs = {})",
            small_scalar_to_u128(&hint.s2_abs)
        );

        let scalar_row = FakeGlvScalarHintRow {
            sig_id: M31::from_u32_unchecked(0),
            cert_id: M31::from_u32_unchecked(0),
            cert_active: M31::from_u32_unchecked(1),
            cert_zero_active: M31::from_u32_unchecked(0),
            scalar,
            hint,
        };
        let scalars = FakeGlvScalarHintClaim {
            rows: vec![scalar_row],
        };
        let selectors = FakeGlvSelectorClaim::from_scalar_hints(&scalars).expect("selectors build");
        selectors.verify(&scalars).expect("native verify");

        let proof_claim = FakeGlvSelectorAirProofClaim {
            log_size: padded_log_size(selectors.rows.len()),
        };
        let log_size = proof_claim.log_size;
        let base: Vec<Vec<M31>> =
            gen_fake_glv_selector_air_base_trace(&scalars, &selectors, proof_claim)
                .into_iter()
                .map(|column| column.to_cpu().values)
                .collect();

        assert!(
            selector_air_constraints_hold(&base, log_size),
            "selector AIR must accept the arbitrary-s2 reconstruction"
        );

        // Tamper one committed `s2_abs` relation limb: the s2 reconstruction
        // carry chain (which binds reconstructed s2 to the relation tuple) must
        // now be unsatisfiable. `s2_abs` limbs sit at relation offset
        // `SCALAR_RELATION_S2_START`, i.e. base column `1 + SCALAR_RELATION_S2_START`.
        let s2_limb_col = 1 + SCALAR_RELATION_S2_START;
        let mut forged = base.clone();
        forged[s2_limb_col][0] += M31::from_u32_unchecked(1);
        assert!(
            !selector_air_constraints_hold(&forged, log_size),
            "forged s2_abs limb must be rejected by the s2 reconstruction chain"
        );
    }
}
