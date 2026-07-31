//! Randomizes individual private-data LogUp claimed-sum slots.
//!
//! The prover samples `v` and `m` for each module.
//! It adds two opposite fractions to two claim slots.
//! Their global sum is zero, and each slot is uniform.
//! The proof carries `v` and `m`.
//! The verifier rebuilds both fractions at OODS.
//! A change breaks the LogUp boundary.
//! The published pair still reveals the module sum.
//! This method does not make STWO zero knowledge.

use rand::RngCore;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{QM31, SECURE_EXTENSION_DEGREE};
use stwo::prover::backend::simd::m31::PackedM31;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
};

// Draw one relation instance for each randomized module.
relation!(ClaimedSumBlinderRelation, SECURE_EXTENSION_DEGREE);

/// Sample one uniform M31 cell from the host CSPRNG.
fn random_m31() -> M31 {
    let mut rng = rand::thread_rng();
    loop {
        let candidate = rng.next_u32() & 0x7fff_ffff;
        if candidate != 0x7fff_ffff {
            return M31::from_u32_unchecked(candidate);
        }
    }
}

/// Fresh uniform QM31 from the host CSPRNG.
pub(crate) fn random_qm31() -> QM31 {
    QM31::from_m31_array(std::array::from_fn(|_| random_m31()))
}

/// `combine(v)` as a packed constant for prover-side interaction columns.
pub(crate) fn blinder_denominator(relation: &ClaimedSumBlinderRelation, v: QM31) -> PackedQM31 {
    let limbs = v.to_m31_array().map(PackedM31::broadcast);
    relation.combine(&limbs)
}

/// AIR-side constant emit shared by every pair member: `numerator = sign · m`
/// over the tuple `v`, ungated (every row of the component).
pub(crate) fn add_blinder_relation_entry<E: EvalAtRow>(
    eval: &mut E,
    relation: &ClaimedSumBlinderRelation,
    v: QM31,
    m: QM31,
    negate: bool,
) {
    let v_limbs = v.to_m31_array().map(E::F::from);
    let m_const = E::combine_ef(m.to_m31_array().map(E::F::from));
    let numerator = if negate { -m_const } else { m_const };
    eval.add_to_relation(RelationEntry::new(relation, numerator, &v_limbs));
}

/// The counterpart component of a single-claim module's pair: no preprocessed
/// or base-trace columns, one constant LogUp fraction `−m/(z − combine(v))` on
/// every row. Its published claimed sum is `−2^log_size · m/(z − combine(v))`,
/// a function of per-proof randomness only.
#[derive(Clone)]
pub(crate) struct ClaimedSumBlinderEval {
    pub(crate) log_size: u32,
    pub(crate) relation: ClaimedSumBlinderRelation,
    pub(crate) v: QM31,
    pub(crate) m: QM31,
}

impl FrameworkEval for ClaimedSumBlinderEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        add_blinder_relation_entry(&mut eval, &self.relation, self.v, self.m, true);
        eval.finalize_logup();
        eval
    }
}

/// Prover-side interaction trace for [`ClaimedSumBlinderEval`]: one QM31
/// column (`SECURE_EXTENSION_DEGREE` base columns) carrying the constant
/// counterpart fraction. Returns the trace and its claimed sum.
pub(crate) fn blinder_counter_interaction(
    log_size: u32,
    relation: &ClaimedSumBlinderRelation,
    v: QM31,
    m: QM31,
) -> (
    Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    QM31,
) {
    let numerator = -PackedQM31::broadcast(m);
    let denominator = blinder_denominator(relation, v);
    let mut logup = LogupTraceGenerator::new(log_size);
    logup.col_from_fn(|_| (numerator, denominator));
    logup.finalize_last()
}
