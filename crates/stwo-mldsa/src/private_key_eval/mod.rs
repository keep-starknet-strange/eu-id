//! Private device-public-key evaluation for hosted ML-DSA verification.
//!
//! Private `ExpandA` supplies canonical stage-zero NTT cells. The private
//! device-key binder supplies packed `t1` cells. This module proves the inverse
//! NTT, evaluates `A` and `2^13 * t1`, and closes the selected integer identity.
//! The relation vector keeps the maximum 66-slot shape. AIR constraints bind
//! every inactive ML-DSA-44 slot to zero.

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
use crate::profile::MlDsaProfile;
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

/// Maximum-shape relation layout. Active counts come from `MlDsaProfile`.
pub const COEFF_EVAL_BASE: usize = 0;
/// Number of coefficient-polynomial evaluation slots (one per Horner group).
pub const COEFF_EVAL_COUNT: usize = 30;
/// First slot of the matrix-`A` evaluations.
pub const A_EVAL_BASE: usize = COEFF_EVAL_BASE + COEFF_EVAL_COUNT;
/// Number of matrix-`A` evaluation slots (`k · l`, maximum shape).
pub const A_EVAL_COUNT: usize = K * L;
/// First slot of the scaled-`t1` evaluations.
pub const T1_EVAL_BASE: usize = A_EVAL_BASE + A_EVAL_COUNT;
/// Number of scaled-`t1` evaluation slots (`k`, maximum shape).
pub const T1_EVAL_COUNT: usize = K;
/// Total evaluation slots: 30 + 30 + 6 = 66.
pub const PRIVATE_EVAL_COUNT: usize = T1_EVAL_BASE + T1_EVAL_COUNT;

const _: () = assert!(COEFF_EVAL_COUNT == crate::coeffs::layout::N_GROUPS);
const _: () = assert!(A_EVAL_BASE == 30);
const _: () = assert!(T1_EVAL_BASE == 60);
const _: () = assert!(PRIVATE_EVAL_COUNT == 66);

/// Shared relation handles from `ExpandA` and the private device-key binder.
#[derive(Clone)]
pub struct PrivateKeyEvalBindings {
    /// Shared NTT-cell handle from `ExpandA`.
    pub ntt: SharedNttCellRelation,
    /// Shared packed-`t1` cell handle from the private device-key binder.
    pub t1: SharedT1CellRelation,
}

impl PrivateKeyEvalBindings {
    /// Bundle the two shared handles.
    pub fn new(ntt: SharedNttCellRelation, t1: SharedT1CellRelation) -> Self {
        Self { ntt, t1 }
    }
}

/// Relation instances reused by every private-key evaluation component.
#[derive(Clone)]
pub struct PrivateKeyEvalRelations {
    /// NTT-cell relation (inverse-NTT stage chain).
    pub ntt: crate::binding::NttCellRelation,
    /// Packed-`t1` cell relation.
    pub t1: crate::binding::T1CellRelation,
    /// Claimed-evaluation relation shared with the coeffs component.
    pub eval: EvalAtRsRelation,
    /// Proof-wide range relation.
    pub range: RangeRelation,
}

impl PrivateKeyEvalRelations {
    /// Resolve the shared handles into relation instances.
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

/// Prover-only decoded public-key material for private-key evaluation traces.
#[derive(Clone)]
pub struct PrivateKeyEvalWitness {
    /// The verifier-selected parameter set.
    pub profile: MlDsaProfile,
    /// The expanded matrix `Â`, row-major `k × l` NTT-domain polynomials.
    pub a_hat: Vec<NttPoly>,
    /// The decoded public-key vector `t1`.
    pub t1: [T1Poly; K],
}

impl PrivateKeyEvalWitness {
    /// Build the witness from the decoded verification input.
    pub fn from_input(
        profile: MlDsaProfile,
        input: &MlDsaVerifyInput,
    ) -> Result<Self, PrivateKeyEvalError> {
        input
            .validate_public_key(profile)
            .map_err(PrivateKeyEvalError::InvalidPublicKey)?;
        let expanded = crate::reference::expand_a::expand_a(profile, &input.rho);
        let mut a_hat = vec![[0; crate::constants::N]; A_EVAL_COUNT];
        let mut poly = 0;
        for i in 0..profile.k() {
            for j in 0..profile.l() {
                a_hat[poly] = expanded.matrix[i][j];
                poly += 1;
            }
        }
        Ok(Self {
            profile,
            a_hat,
            t1: input.t1,
        })
    }
}

/// Errors from private-key evaluation witness construction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivateKeyEvalError {
    /// The decoded public key contains a non-canonical or non-zero-inactive
    /// `t1` coefficient.
    InvalidPublicKey(&'static str),
    /// The device message does not fit the fixed message capacity.
    MessageExceedsCapacity {
        /// Actual message length in bytes.
        message_len: usize,
        /// Fixed message capacity in bytes.
        message_capacity: usize,
    },
    /// A `PrivateDeviceEvals` constructor received the wrong number of
    /// evaluations.
    WrongEvalCount {
        /// Expected evaluation count (`PRIVATE_EVAL_COUNT`).
        expected: usize,
        /// Actual evaluation count received.
        actual: usize,
    },
}

impl core::fmt::Display for PrivateKeyEvalError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidPublicKey(message) => f.write_str(message),
            Self::MessageExceedsCapacity {
                message_len,
                message_capacity,
            } => write!(
                f,
                "device message length {message_len} exceeds fixed capacity {message_capacity}"
            ),
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

/// Fixed proof order: coeffs 0..29, A 30..59, and scaled t1 60..65.
/// ML-DSA-44 uses the first 16 A slots and first 4 t1 slots. Its other slots
/// are relation-bound to zero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateDeviceEvals([SecureField; PRIVATE_EVAL_COUNT]);

impl PrivateDeviceEvals {
    /// Assemble from the three fixed segments (coeffs, `A`, scaled `t1`).
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

    /// Build from exactly `PRIVATE_EVAL_COUNT` evaluations in proof order.
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

    /// The evaluations in proof order.
    pub fn as_slice(&self) -> &[SecureField] {
        &self.0
    }

    /// Consume into a `Vec` in proof order.
    pub fn into_vec(self) -> Vec<SecureField> {
        self.0.into()
    }

    pub(crate) fn coeff(&self, id: usize) -> SecureField {
        self.0[id]
    }

    pub(crate) fn a_for(&self, profile: MlDsaProfile, i: usize, j: usize) -> SecureField {
        self.0[A_EVAL_BASE + i * profile.l() + j]
    }

    pub(crate) fn t1(&self, i: usize) -> SecureField {
        self.0[T1_EVAL_BASE + i]
    }
}

/// LogUp claimed sums of the private-key evaluation components.
#[derive(Clone, Debug, Default)]
pub struct PrivateKeyEvalClaims {
    /// Inverse-NTT claimed sums (butterfly chain and scaling/eval).
    pub ntt: NttClaims,
    /// Packed-`t1` component claimed sum.
    pub t1: SecureField,
    /// Fold component claimed sum.
    pub fold: SecureField,
}

/// Base-trace output of the private-key evaluation components.
pub struct PrivateKeyBase {
    /// The concatenated NTT and `t1` base columns.
    pub trace: Vec<crate::air_util::ColEval>,
    /// The merged range-table uses.
    pub range_uses: RcUses,
}

/// Generate the concatenated NTT + `t1` base trace and the merged rc census.
pub fn gen_private_key_base(witness: &PrivateKeyEvalWitness) -> PrivateKeyBase {
    let NttBase {
        mut trace,
        mut range_uses,
    } = gen_ntt_base(witness.profile, &witness.a_hat);
    let T1Base {
        trace: t1_trace,
        range_uses: t1_uses,
    } = gen_t1_base(witness.profile, &witness.t1);
    range_uses.add_assign(&t1_uses);
    trace.extend(t1_trace);
    PrivateKeyBase { trace, range_uses }
}

/// Interaction-trace output of the private-key evaluation components.
pub struct PrivateKeyInteraction {
    /// The concatenated NTT and `t1` interaction columns.
    pub trace: Vec<crate::air_util::ColEval>,
    /// The `k·l` claimed `A` evaluations (row-major).
    pub a_evals: Vec<SecureField>,
    /// The `k` claimed scaled-`t1` evaluations.
    pub t1_evals: Vec<SecureField>,
    /// Inverse-NTT claimed sums.
    pub ntt_claims: NttClaims,
    /// Packed-`t1` claimed sum.
    pub t1_claim: SecureField,
}

/// Generate the NTT + `t1` interaction trace at the drawn `(r, s)`.
pub fn gen_private_key_interaction(
    witness: &PrivateKeyEvalWitness,
    r: SecureField,
    s: SecureField,
    relations: &PrivateKeyEvalRelations,
) -> PrivateKeyInteraction {
    let ntt = gen_ntt_interaction(witness.profile, &witness.a_hat, r, s, relations);
    let t1 = gen_t1_interaction(witness.profile, &witness.t1, r, s, relations);
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

/// Preprocessed ids of all three components (NTT, `t1`, fold), in commit order.
pub fn preprocessed_ids(
    profile: MlDsaProfile,
) -> Vec<stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId> {
    let mut ids = ntt_preprocessed_ids(profile);
    ids.extend(t1_preprocessed_ids(profile));
    ids.extend(fold_preprocessed_ids());
    ids
}

/// Preprocessed log sizes, matching [`preprocessed_ids`] order.
pub fn preprocessed_log_sizes() -> Vec<u32> {
    let mut sizes = ntt_preprocessed_log_sizes();
    sizes.extend(t1_preprocessed_log_sizes());
    sizes.extend(fold_preprocessed_log_sizes());
    sizes
}

/// Generate the preprocessed columns for the selected profile.
pub fn gen_preprocessed(profile: MlDsaProfile) -> Vec<crate::air_util::ColEval> {
    let mut columns = gen_ntt_preprocessed(profile);
    columns.extend(gen_t1_preprocessed(profile));
    columns.extend(gen_fold_preprocessed());
    columns
}

/// Base-trace column log sizes (NTT then `t1`).
pub fn trace_layout() -> Vec<u32> {
    let mut layout = ntt_trace_layout();
    layout.extend(t1_trace_layout());
    layout
}

/// Interaction column log sizes (NTT then `t1`).
pub fn interaction_layout() -> Vec<u32> {
    let mut layout = ntt_interaction_layout();
    layout.extend(t1_interaction_layout());
    layout
}

/// The three framework components of the private-key evaluation trace.
pub struct PrivateKeyTraceComponents {
    ntt_butterfly: FrameworkComponent<NttButterflyEval>,
    ntt_scaling: FrameworkComponent<NttScalingEval>,
    t1: FrameworkComponent<T1Eval>,
}

impl PrivateKeyTraceComponents {
    /// Build the butterfly, scaling, and `t1` components at `(r, s)`.
    pub fn new(
        allocator: &mut TraceLocationAllocator,
        profile: MlDsaProfile,
        r: SecureField,
        s: SecureField,
        relations: PrivateKeyEvalRelations,
        claims: &PrivateKeyEvalClaims,
    ) -> Self {
        let ntt_butterfly = FrameworkComponent::new(
            allocator,
            NttButterflyEval {
                profile,
                relations: relations.clone(),
            },
            claims.ntt.butterfly,
        );
        let ntt_scaling = FrameworkComponent::new(
            allocator,
            NttScalingEval {
                profile,
                r,
                s,
                relations: relations.clone(),
            },
            claims.ntt.scaling,
        );
        let t1 = FrameworkComponent::new(
            allocator,
            T1Eval {
                profile,
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

    /// Verifier-side component references.
    pub fn trace_components(&self) -> Vec<&dyn Component> {
        vec![&self.ntt_butterfly, &self.ntt_scaling, &self.t1]
    }

    /// Prover-side component references.
    pub fn trace_prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![&self.ntt_butterfly, &self.ntt_scaling, &self.t1]
    }
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
pub(crate) mod proof_test {
    use stwo::core::air::Component;
    use stwo::core::channel::Blake2sChannel;
    use stwo::core::fields::m31::M31;
    use stwo::core::fields::qm31::SecureField;
    use stwo::prover::backend::simd::SimdBackend;
    use stwo::prover::{ComponentProver, TreeBuilder};
    use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
    use stwo_constraint_framework::{FrameworkComponent, FrameworkEval, TraceLocationAllocator};

    use air_core::{Air, AirProver, TreeLayout};

    use crate::air_util::{col_eval, m31, ColEval};

    pub(crate) fn active_id() -> PreProcessedColumnId {
        PreProcessedColumnId {
            id: "test_private_key_formula_active".to_string(),
        }
    }

    pub(crate) struct OneRowAir<E: FrameworkEval + Clone + Sync> {
        eval: E,
        log_size: u32,
        trace: Vec<ColEval>,
        component: Option<FrameworkComponent<E>>,
    }

    impl<E: FrameworkEval + Clone + Sync> OneRowAir<E> {
        pub(crate) fn new(eval: E, values: &[M31]) -> Self {
            let log_size = eval.log_size();
            let trace = values
                .iter()
                .map(|&value| {
                    let mut column = vec![m31(0); 1usize << log_size];
                    column[0] = value;
                    col_eval(log_size, column)
                })
                .collect();
            Self {
                eval,
                log_size,
                trace,
                component: None,
            }
        }
    }

    impl<E: FrameworkEval + Clone + Sync> Air for OneRowAir<E> {
        fn mix_public(&self, _channel: &mut Blake2sChannel) {}

        fn draw_relations(&mut self, _channel: &mut Blake2sChannel) {}

        fn layout(&self) -> TreeLayout {
            TreeLayout {
                preprocessed: vec![self.log_size],
                trace: vec![self.log_size; self.trace.len()],
                interaction: vec![self.log_size],
            }
        }

        fn claimed_sums(&self) -> Vec<SecureField> {
            Vec::new()
        }

        fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
            vec![active_id()]
        }

        fn canonical_preprocessed_columns(
            &mut self,
        ) -> Result<Vec<ColEval>, stwo::core::verifier::VerificationError> {
            let mut active = vec![m31(0); 1usize << self.log_size];
            active[0] = m31(1);
            Ok(vec![col_eval(self.log_size, active)])
        }

        fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
            self.component = Some(FrameworkComponent::new(
                allocator,
                self.eval.clone(),
                SecureField::default(),
            ));
        }

        fn components(&self) -> Vec<&dyn Component> {
            vec![self.component.as_ref().expect("test component")]
        }
    }

    impl<E: FrameworkEval + Clone + Sync> AirProver for OneRowAir<E> {
        fn max_log_size(&self) -> u32 {
            self.log_size
        }

        fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
            tb.extend_evals(
                self.canonical_preprocessed_columns()
                    .expect("test preprocessed column"),
            );
        }

        fn preprocessed_column_fingerprints(
            &mut self,
        ) -> Vec<air_core::PreprocessedColumnFingerprint> {
            let ids = self.preprocessed_column_ids();
            let columns = self
                .canonical_preprocessed_columns()
                .expect("test preprocessed column");
            air_core::fingerprint_preprocessed_columns("private_key_formula_test", &ids, &columns)
        }

        fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
            tb.extend_evals(self.trace.clone());
        }

        fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
            tb.extend_evals(vec![col_eval(
                self.log_size,
                vec![m31(0); 1usize << self.log_size],
            )]);
        }

        fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
            vec![self.component.as_ref().expect("test component")]
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::profile::ML_DSA_65;

    #[test]
    fn private_eval_order_is_exact_and_length_checked() {
        let values: Vec<_> = (0..PRIVATE_EVAL_COUNT)
            .map(|value| SecureField::from(crate::air_util::m31(value as u32)))
            .collect();
        let evals = PrivateDeviceEvals::try_from_slice(&values).unwrap();
        assert_eq!(evals.as_slice(), values);
        assert!(PrivateDeviceEvals::try_from_slice(&values[..65]).is_err());
        assert_eq!(evals.a_for(ML_DSA_65, 5, 4), values[59]);
        assert_eq!(evals.t1(5), values[65]);
    }
}
