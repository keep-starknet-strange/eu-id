//! Private device-public-key evaluation for hosted ML-DSA verification.
//!
//! U5 supplies canonical stage-zero NTT cells, U9 supplies the packed `t1`
//! cells, and this module proves the inverse NTT, evaluates `A` and
//! `2^13 * t1`, and closes the complete 66-term integer-lift identity.

mod fold;
mod ntt;
mod t1;

use stwo::core::air::Component;
use stwo::core::fields::qm31::SecureField;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::ComponentProver;
use stwo_constraint_framework::{FrameworkComponent, TraceLocationAllocator};

use crate::binding::{SharedNttCellRelation, SharedT1CellRelation};
use crate::coeffs::relations::{EvalAtRsRelation, RangeRelation};
use crate::coeffs::RcUses;
use crate::constants::{K, L};
use crate::reference::ntt::NttPoly;
use crate::types::{MlDsaVerifyInput, T1Poly};

pub use fold::{
    fold_interaction_layout, fold_preprocessed_ids, fold_preprocessed_log_sizes,
    gen_fold_interaction, gen_fold_preprocessed, PrivateFoldEval,
};
pub use ntt::{
    gen_ntt_base, gen_ntt_interaction, gen_ntt_preprocessed, ntt_interaction_layout,
    ntt_preprocessed_ids, ntt_preprocessed_log_sizes, ntt_trace_layout, NttBase, NttButterflyEval,
    NttClaims, NttScalingEval, NTT_BUTTERFLY_LOG_SIZE, NTT_SCALING_LOG_SIZE,
};
pub use t1::{
    gen_t1_base, gen_t1_interaction, gen_t1_preprocessed, t1_interaction_layout,
    t1_preprocessed_ids, t1_preprocessed_log_sizes, t1_trace_layout, T1Base, T1Eval, T1Interaction,
    T1_LOG_SIZE,
};

pub const COEFF_EVAL_BASE: usize = 0;
pub const COEFF_EVAL_COUNT: usize = 30;
pub const A_EVAL_BASE: usize = COEFF_EVAL_BASE + COEFF_EVAL_COUNT;
pub const A_EVAL_COUNT: usize = K * L;
pub const T1_EVAL_BASE: usize = A_EVAL_BASE + A_EVAL_COUNT;
pub const T1_EVAL_COUNT: usize = K;
pub const PRIVATE_EVAL_COUNT: usize = T1_EVAL_BASE + T1_EVAL_COUNT;

const _: () = assert!(COEFF_EVAL_COUNT == crate::coeffs::layout::N_GROUPS);
const _: () = assert!(A_EVAL_BASE == 30);
const _: () = assert!(T1_EVAL_BASE == 60);
const _: () = assert!(PRIVATE_EVAL_COUNT == 66);

/// Shared relation handles whose challenges are owned by U5 and U9.
#[derive(Clone)]
pub struct PrivateKeyEvalBindings {
    pub ntt: SharedNttCellRelation,
    pub t1: SharedT1CellRelation,
}

impl PrivateKeyEvalBindings {
    pub fn new(ntt: SharedNttCellRelation, t1: SharedT1CellRelation) -> Self {
        Self { ntt, t1 }
    }
}

/// Relation instances reused by every private-key evaluation component.
#[derive(Clone)]
pub struct PrivateKeyEvalRelations {
    pub ntt: crate::binding::NttCellRelation,
    pub t1: crate::binding::T1CellRelation,
    pub eval: EvalAtRsRelation,
    pub range: RangeRelation,
}

impl PrivateKeyEvalRelations {
    pub fn from_bindings(
        bindings: &PrivateKeyEvalBindings,
        eval: EvalAtRsRelation,
        range: RangeRelation,
    ) -> Self {
        Self {
            ntt: bindings.ntt.get(),
            t1: bindings.t1.get(),
            eval,
            range,
        }
    }

    #[cfg(test)]
    pub(crate) fn dummy() -> Self {
        Self {
            ntt: crate::binding::NttCellRelation::dummy(),
            t1: crate::binding::T1CellRelation::dummy(),
            eval: EvalAtRsRelation::dummy(),
            range: RangeRelation::dummy(),
        }
    }
}

/// Prover-only decoded public-key material used to construct U6 traces.
#[derive(Clone)]
pub struct PrivateKeyEvalWitness {
    pub a_hat: Vec<NttPoly>,
    pub t1: [T1Poly; K],
}

impl PrivateKeyEvalWitness {
    pub fn from_input(input: &MlDsaVerifyInput) -> Result<Self, PrivateKeyEvalError> {
        input
            .validate_public_key()
            .map_err(PrivateKeyEvalError::InvalidPublicKey)?;
        let expanded = crate::reference::expand_a::expand_a(&input.rho);
        let mut a_hat = Vec::with_capacity(A_EVAL_COUNT);
        for i in 0..K {
            for j in 0..L {
                a_hat.push(expanded.matrix[i][j]);
            }
        }
        Ok(Self {
            a_hat,
            t1: input.t1,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivateKeyEvalError {
    InvalidPublicKey(&'static str),
    WrongEvalCount { expected: usize, actual: usize },
}

impl core::fmt::Display for PrivateKeyEvalError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidPublicKey(message) => f.write_str(message),
            Self::WrongEvalCount { expected, actual } => {
                write!(
                    f,
                    "expected {expected} private-key evaluations, got {actual}"
                )
            }
        }
    }
}

impl std::error::Error for PrivateKeyEvalError {}

/// The exact proof order: coeffs 0..29, A 30..59, scaled-t1 60..65.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateDeviceEvals([SecureField; PRIVATE_EVAL_COUNT]);

impl PrivateDeviceEvals {
    pub fn from_parts(
        coeffs: &[SecureField],
        a: &[SecureField],
        t1: &[SecureField],
    ) -> Result<Self, PrivateKeyEvalError> {
        if coeffs.len() != COEFF_EVAL_COUNT || a.len() != A_EVAL_COUNT || t1.len() != T1_EVAL_COUNT
        {
            return Err(PrivateKeyEvalError::WrongEvalCount {
                expected: PRIVATE_EVAL_COUNT,
                actual: coeffs.len() + a.len() + t1.len(),
            });
        }
        let mut values = [SecureField::default(); PRIVATE_EVAL_COUNT];
        values[COEFF_EVAL_BASE..A_EVAL_BASE].copy_from_slice(coeffs);
        values[A_EVAL_BASE..T1_EVAL_BASE].copy_from_slice(a);
        values[T1_EVAL_BASE..PRIVATE_EVAL_COUNT].copy_from_slice(t1);
        Ok(Self(values))
    }

    pub fn try_from_slice(values: &[SecureField]) -> Result<Self, PrivateKeyEvalError> {
        let values: [SecureField; PRIVATE_EVAL_COUNT] =
            values
                .try_into()
                .map_err(|_| PrivateKeyEvalError::WrongEvalCount {
                    expected: PRIVATE_EVAL_COUNT,
                    actual: values.len(),
                })?;
        Ok(Self(values))
    }

    pub fn as_slice(&self) -> &[SecureField] {
        &self.0
    }

    pub fn into_vec(self) -> Vec<SecureField> {
        self.0.into()
    }

    pub(crate) fn coeff(&self, id: usize) -> SecureField {
        self.0[id]
    }

    pub(crate) fn a(&self, i: usize, j: usize) -> SecureField {
        self.0[A_EVAL_BASE + i * L + j]
    }

    pub(crate) fn t1(&self, i: usize) -> SecureField {
        self.0[T1_EVAL_BASE + i]
    }
}

#[derive(Clone, Debug, Default)]
pub struct PrivateKeyEvalClaims {
    pub ntt: NttClaims,
    pub t1: SecureField,
    pub fold: SecureField,
}

pub struct PrivateKeyBase {
    pub trace: Vec<crate::air_util::ColEval>,
    pub range_uses: RcUses,
}

pub fn gen_private_key_base(witness: &PrivateKeyEvalWitness) -> PrivateKeyBase {
    let NttBase {
        mut trace,
        mut range_uses,
    } = gen_ntt_base(&witness.a_hat);
    let T1Base {
        trace: t1_trace,
        range_uses: t1_uses,
    } = gen_t1_base(&witness.t1);
    range_uses.add_assign(&t1_uses);
    trace.extend(t1_trace);
    PrivateKeyBase { trace, range_uses }
}

pub struct PrivateKeyInteraction {
    pub trace: Vec<crate::air_util::ColEval>,
    pub a_evals: Vec<SecureField>,
    pub t1_evals: Vec<SecureField>,
    pub ntt_claims: NttClaims,
    pub t1_claim: SecureField,
}

pub fn gen_private_key_interaction(
    witness: &PrivateKeyEvalWitness,
    r: SecureField,
    s: SecureField,
    relations: &PrivateKeyEvalRelations,
) -> PrivateKeyInteraction {
    let ntt = gen_ntt_interaction(&witness.a_hat, r, s, relations);
    let t1 = gen_t1_interaction(&witness.t1, r, s, relations);
    let mut trace = ntt.trace;
    trace.extend(t1.trace);
    PrivateKeyInteraction {
        trace,
        a_evals: ntt.a_evals,
        t1_evals: t1.evals,
        ntt_claims: ntt.claims,
        t1_claim: t1.claimed_sum,
    }
}

pub fn preprocessed_ids(
) -> Vec<stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId> {
    let mut ids = ntt_preprocessed_ids();
    ids.extend(t1_preprocessed_ids());
    ids.extend(fold_preprocessed_ids());
    ids
}

pub fn preprocessed_log_sizes() -> Vec<u32> {
    let mut sizes = ntt_preprocessed_log_sizes();
    sizes.extend(t1_preprocessed_log_sizes());
    sizes.extend(fold_preprocessed_log_sizes());
    sizes
}

pub fn gen_preprocessed() -> Vec<crate::air_util::ColEval> {
    let mut columns = gen_ntt_preprocessed();
    columns.extend(gen_t1_preprocessed());
    columns.extend(gen_fold_preprocessed());
    columns
}

pub fn trace_layout() -> Vec<u32> {
    let mut layout = ntt_trace_layout();
    layout.extend(t1_trace_layout());
    layout
}

pub fn interaction_layout() -> Vec<u32> {
    let mut layout = ntt_interaction_layout();
    layout.extend(t1_interaction_layout());
    layout
}

pub struct PrivateKeyTraceComponents {
    ntt_butterfly: FrameworkComponent<NttButterflyEval>,
    ntt_scaling: FrameworkComponent<NttScalingEval>,
    t1: FrameworkComponent<T1Eval>,
}

impl PrivateKeyTraceComponents {
    pub fn new(
        allocator: &mut TraceLocationAllocator,
        r: SecureField,
        s: SecureField,
        relations: PrivateKeyEvalRelations,
        claims: &PrivateKeyEvalClaims,
    ) -> Self {
        let ntt_butterfly = FrameworkComponent::new(
            allocator,
            NttButterflyEval {
                relations: relations.clone(),
            },
            claims.ntt.butterfly,
        );
        let ntt_scaling = FrameworkComponent::new(
            allocator,
            NttScalingEval {
                r,
                s,
                relations: relations.clone(),
            },
            claims.ntt.scaling,
        );
        let t1 = FrameworkComponent::new(
            allocator,
            T1Eval {
                r,
                s,
                relations: relations.clone(),
            },
            claims.t1,
        );
        Self {
            ntt_butterfly,
            ntt_scaling,
            t1,
        }
    }

    pub fn trace_components(&self) -> Vec<&dyn Component> {
        vec![&self.ntt_butterfly, &self.ntt_scaling, &self.t1]
    }

    pub fn trace_prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![&self.ntt_butterfly, &self.ntt_scaling, &self.t1]
    }
}

pub fn build_fold_component(
    allocator: &mut TraceLocationAllocator,
    rho_rlc: SecureField,
    r: SecureField,
    s: SecureField,
    relations: PrivateKeyEvalRelations,
    evals: PrivateDeviceEvals,
    claim: SecureField,
) -> FrameworkComponent<PrivateFoldEval> {
    FrameworkComponent::new(
        allocator,
        PrivateFoldEval {
            rho_rlc,
            r,
            s,
            relations,
            evals,
        },
        claim,
    )
}

pub(crate) fn range_tuple<E: stwo_constraint_framework::EvalAtRow>(
    value: E::F,
    kind: crate::coeffs::tables::RcKind,
) -> [E::F; 2] {
    [value, E::F::from(crate::air_util::m31(kind.bound_id()))]
}

pub(crate) fn range_denominator(
    relation: &RangeRelation,
    value: u32,
    kind: crate::coeffs::tables::RcKind,
) -> SecureField {
    use stwo_constraint_framework::Relation;
    relation.combine(&[
        crate::air_util::m31(value),
        crate::air_util::m31(kind.bound_id()),
    ])
}

pub(crate) fn combine_batch(entries: &[(SecureField, SecureField)]) -> (SecureField, SecureField) {
    use num_traits::{One, Zero};
    let denominator = entries
        .iter()
        .fold(SecureField::one(), |acc, (_, den)| acc * *den);
    let numerator =
        entries
            .iter()
            .enumerate()
            .fold(SecureField::zero(), |acc, (index, (num, _))| {
                let other = entries
                    .iter()
                    .enumerate()
                    .filter(|(other, _)| *other != index)
                    .fold(SecureField::one(), |product, (_, (_, den))| product * *den);
                acc + *num * other
            });
    (numerator, denominator)
}

pub(crate) fn gen_batched_logup(
    log_size: u32,
    rows: &[Vec<(SecureField, SecureField)>],
    entries_per_row: usize,
) -> (Vec<crate::air_util::ColEval>, SecureField) {
    use stwo::prover::backend::simd::m31::N_LANES;
    use stwo::prover::backend::simd::qm31::PackedQM31;
    use stwo_constraint_framework::LogupTraceGenerator;

    const BATCH: usize = 4;
    let circle_to_coset = crate::air_util::circle_row_to_coset(log_size);
    let mut logup = LogupTraceGenerator::new(log_size);
    for start in (0..entries_per_row).step_by(BATCH) {
        let end = (start + BATCH).min(entries_per_row);
        logup.col_from_fn(|vec_row| {
            let mut numerators = [SecureField::default(); N_LANES];
            let mut denominators = [SecureField::default(); N_LANES];
            for lane in 0..N_LANES {
                let circle_row = vec_row * N_LANES + lane;
                let coset = circle_to_coset[circle_row];
                let (num, den) = combine_batch(&rows[coset][start..end]);
                numerators[lane] = num;
                denominators[lane] = den;
            }
            (
                PackedQM31::from_array(numerators),
                PackedQM31::from_array(denominators),
            )
        });
    }
    logup.finalize_last()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn private_eval_order_is_exact_and_length_checked() {
        let values: Vec<_> = (0..PRIVATE_EVAL_COUNT)
            .map(|value| SecureField::from(crate::air_util::m31(value as u32)))
            .collect();
        let evals = PrivateDeviceEvals::try_from_slice(&values).unwrap();
        assert_eq!(evals.as_slice(), values);
        assert!(PrivateDeviceEvals::try_from_slice(&values[..65]).is_err());
        assert_eq!(evals.a(5, 4), values[59]);
        assert_eq!(evals.t1(5), values[65]);
    }
}
