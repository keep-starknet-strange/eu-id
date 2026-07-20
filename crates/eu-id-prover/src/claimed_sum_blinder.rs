//! Q-015 §4b Class-E claimed-sum blinder pairs.
//!
//! Every per-component LogUp claimed sum carried in [`crate::mdoc::MdocCircuitProof`]
//! that is a function of private witness data leaks under the public `(z, α)`
//! challenges. The masking rule (tasks/mdoc-mailbox/answers/Q-015.md §4b,
//! tasks/p4c-masking-note.md Case 4) is: mask the SPLIT, not the balance. Per
//! masked module the prover samples a fresh `v ∈ QM31` and a free multiplicity
//! `m ∈ QM31` and emits `+m/(z − combine(v))` into one published claimed-sum
//! slot and `−m/(z − combine(v))` into a second slot of the same module. The
//! global fold (`air_core` sums every module's claimed sums to zero) is
//! untouched because the two members cancel exactly; each individual published
//! number is shifted by a per-proof uniform QM31 value, so the published sum is
//! uniform (exact ZK argument, no numeric bound needed).
//!
//! Mechanics: `v` and `m` ride inside the module's serialized interaction
//! claim, so the verifier's `evaluate` reproduces the same constant fraction at
//! the OODS point (the same pattern as `MacBindingEval` reading `self.av`).
//! The fraction is constant across all rows of its component; both members are
//! emitted ungated over the full domain, so a pair cancels exactly when
//! `rows(+side) · m == rows(−side) · m_counter`. Tampering `v`, `m`, or a
//! blinded claimed sum in a serialized proof breaks the component's LogUp
//! boundary constraint at OODS, so the pair is bound — there is no free
//! claimed-sum term (the P4b blind_claim-hole lesson).

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

// One relation type, one instance drawn per masked module (distinct z/α per
// module), used by both members of that module's pair and by nothing else.
relation!(ClaimedSumBlinderRelation, SECURE_EXTENSION_DEGREE);

/// Fresh uniform M31 cell from the host CSPRNG (never channel-derived: the
/// blinder must stay secret from the verifier). Rejection-sampled like the
/// per-module `random_m31_cell` helpers.
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
