//! `keccak_round` LogUp → GKR offload (W3b).
//!
//! The round component's ~900 log-11 interaction columns are replaced by ONE
//! LogUp-GKR proof over the flattened fraction multiset plus a single
//! `MleEval` tie-back component (8 committed tree-3 columns) that binds the
//! GKR input-layer claims back to the committed base trace.
//!
//! ## Layout (proven by the W3a spike, see `tasks/quantum-safe-branch-plan.md` §Q5)
//!
//! The whole per-row fraction multiset — all four relation families in the
//! exact [`keccak_round::collect_round_lookups`] emission order — is ONE
//! flattened `Layer::LogUpGeneric` instance with the **lookup slot in the HIGH
//! index bits and the trace row in the LOW bits**. The GKR OOD point splits as
//! `r = (r_slot ‖ r_row)` and, because every `Relation::combine` is an affine
//! form with row-independent coefficients, the input-layer MLEs decompose as
//!
//! ```text
//! den_mle(r) = Σ_slot eq(slot, r_slot) · combine_slot([tupleⱼ_mle(r_row)]ⱼ)
//! num_mle(r) = Σ_slot eq(slot, r_slot) · num_slot_mle(r_row)
//! ```
//!
//! so the tie-back lives entirely on the **row domain**: one δ-folded coeff
//! column `c(row) = Σ_slot eq(slot,r_slot)·(δ·num_slot(row) + den_slot(row))`
//! whose MLE at `r_row` must equal `δ·num_claim + den_claim − pad(r_slot)`
//! (padding slots contribute the constant fraction `0/1`). The
//! [`RoundCoeffOracle`] reconstructs `c` at the STARK OODS point purely from
//! the round component's committed base-column mask values, closing the chain:
//! GKR sum == claimed sum, GKR input claims == coeff-column MLE, coeff column
//! == affine image of the committed base columns.
//!
//! ## Fiat-Shamir order (both sides identical)
//!
//! tree-2 commit → `prove_batch`/`partially_verify_batch` on the shared
//! channel → draw δ → commit the tree-3 tie-back trace. The GKR proof is thus
//! bound to trees 0-2, the drawn relations and the mixed claimed sums; the
//! tie-back columns commit after the GKR transcript.

use num_traits::{One, Zero};
use stwo::core::air::accumulation::PointEvaluationAccumulator;
use stwo::core::channel::Channel;
use stwo::core::circle::CirclePoint;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::core::fields::FieldExpOps;
use stwo::core::pcs::{TreeSubspan, TreeVec};
use stwo::core::verifier::VerificationError;
use stwo::core::ColumnVec;
use stwo::prover::backend::simd::m31::{LOG_N_LANES, N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::lookups::gkr_prover::{prove_batch, Layer};
use stwo::prover::lookups::gkr_verifier::{partially_verify_batch, Gate, GkrArtifact};
use stwo::prover::lookups::mle::Mle;
use stwo_constraint_framework::mle_eval::MleCoeffColumnOracle;
use stwo_constraint_framework::{PointEvaluator, Relation};

use air_core::gkr::{decode_gkr_batch_proof, encode_gkr_batch_proof};

use crate::keccak_round::{
    build_fracs, collect_round_lookups, data_log_size, InteractionClaimData, RoundLookupKind,
    N_TOTAL_LOOKUPS,
};
use crate::relations::KeccakRelations;

/// Slot-index bits of the flattened GKR instance (898 real slots → 1024).
pub const LOG_SLOTS: u32 = 10;
const _: () = assert!(
    N_TOTAL_LOOKUPS <= 1 << LOG_SLOTS && N_TOTAL_LOOKUPS > 1 << (LOG_SLOTS - 1),
    "LOG_SLOTS must be ilog2(next_power_of_two(N_TOTAL_LOOKUPS))"
);

/// Committed tree-3 columns of the tie-back trace (eq evals + shifted prefix
/// sums, each one QM31 column = 4 M31 columns).
pub const N_TIEBACK_COLUMNS: usize = 2 * SECURE_EXTENSION_DEGREE;

/// Everything both sides derive from the GKR transcript for the tie-back.
pub struct RoundTieBack {
    /// The row half of the GKR OOD point — the MleEval evaluation point.
    pub r_row: Vec<SecureField>,
    /// Post-GKR channel-drawn folding challenge for num+den.
    pub delta: SecureField,
    /// `eq(slot, r_slot)` for every slot index `0..2^LOG_SLOTS` (MSB-first).
    pub eq_ws: Vec<SecureField>,
    /// `δ·num_claim + den_claim − Σ_{padding slots} eq(slot, r_slot)`.
    pub mle_claim: SecureField,
}

/// `eq(bits(index) MSB-first over LOG_SLOTS, r_slot)` for every slot: the slot
/// index's MOST significant bit pairs with `r_slot[0]` (stwo's `Mle` /
/// GKR OOD convention — the first point coordinate splits the top half).
fn eq_weights(r_slot: &[SecureField]) -> Vec<SecureField> {
    let mut ws = vec![SecureField::one()];
    for &p in r_slot {
        // The freshly-processed coordinate becomes the LSB; earlier
        // coordinates shift toward the MSB, so r_slot[0] ends at the top bit.
        let mut next = Vec::with_capacity(ws.len() * 2);
        for w in &ws {
            next.push(*w * (SecureField::one() - p));
            next.push(*w * p);
        }
        ws = next;
    }
    ws
}

fn tieback_from_artifact(
    artifact: &GkrArtifact,
    delta: SecureField,
    log_size: u32,
) -> Result<RoundTieBack, VerificationError> {
    let bad = |msg: &str| VerificationError::InvalidStructure(format!("round GKR: {msg}"));
    if artifact.n_variables_by_instance.as_slice() != [(LOG_SLOTS + log_size) as usize] {
        return Err(bad("wrong instance count or variable count"));
    }
    let claims = artifact
        .claims_to_verify_by_instance
        .first()
        .ok_or_else(|| bad("missing input-layer claims"))?;
    let [num_claim, den_claim] = claims.as_slice() else {
        return Err(bad("input-layer claims must be [num, den]"));
    };
    if artifact.ood_point.len() != (LOG_SLOTS + log_size) as usize {
        return Err(bad("OOD point length mismatch"));
    }
    let (r_slot, r_row) = artifact.ood_point.split_at(LOG_SLOTS as usize);
    let eq_ws = eq_weights(r_slot);
    let pad: SecureField = eq_ws[N_TOTAL_LOOKUPS..].iter().copied().sum();
    Ok(RoundTieBack {
        r_row: r_row.to_vec(),
        delta,
        eq_ws,
        mle_claim: delta * *num_claim + *den_claim - pad,
    })
}

// =============================================================================
// Prover side.
// =============================================================================

/// Prover state: the per-slot fraction columns (the single witness source for
/// the claimed sum, the GKR leaves and the tie-back coeff column).
pub struct RoundGkrProver {
    fracs: Vec<(Vec<PackedQM31>, Vec<PackedQM31>)>,
    log_size: u32,
    claimed_sum: SecureField,
}

impl RoundGkrProver {
    /// Build the fraction multiset and its exact sum (== the columnar
    /// `claimed_sum` the offloaded interaction trace would have produced).
    pub fn new(rel: &KeccakRelations, data: &InteractionClaimData) -> Self {
        let fracs = build_fracs(rel, data);
        let mut total = PackedQM31::zero();
        for (num, den) in &fracs {
            let inv = PackedQM31::batch_inverse(den);
            for (n, d_inv) in num.iter().zip(&inv) {
                total += *n * *d_inv;
            }
        }
        let claimed_sum = total.to_array().iter().copied().sum();
        Self {
            fracs,
            log_size: data_log_size(data),
            claimed_sum,
        }
    }

    pub fn claimed_sum(&self) -> SecureField {
        self.claimed_sum
    }

    /// Flatten to the slot-high/row-low `LogUpGeneric` instance, prove it on
    /// the shared channel, draw δ, and build the δ-folded coeff column.
    /// Returns `(gkr_blob, tie_back, coeff_mle)`.
    pub fn prove(
        self,
        channel: &mut impl Channel,
    ) -> (Vec<u8>, RoundTieBack, Mle<SimdBackend, SecureField>) {
        let n_rows = 1usize << self.log_size;
        let n_vec_rows = 1usize << (self.log_size - LOG_N_LANES);
        let size = (1usize << LOG_SLOTS) * n_rows;

        // Padding slots hold the neutral fraction 0/1.
        let mut num_flat = vec![SecureField::zero(); size];
        let mut den_flat = vec![SecureField::one(); size];
        for (s, (num, den)) in self.fracs.iter().enumerate() {
            for vr in 0..n_vec_rows {
                let na = num[vr].to_array();
                let da = den[vr].to_array();
                let base = s * n_rows + vr * N_LANES;
                for l in 0..N_LANES {
                    num_flat[base + l] = na[l];
                    den_flat[base + l] = da[l];
                }
            }
        }
        let layer = Layer::LogUpGeneric {
            numerators: Mle::<SimdBackend, SecureField>::new(num_flat.into_iter().collect()),
            denominators: Mle::<SimdBackend, SecureField>::new(den_flat.into_iter().collect()),
        };
        let (proof, artifact) = prove_batch(channel, vec![layer]);
        debug_assert_eq!(
            proof.output_claims_by_instance[0][0],
            self.claimed_sum * proof.output_claims_by_instance[0][1],
            "GKR output claim != round claimed sum"
        );
        let delta = channel.draw_secure_felt();
        let tie_back = tieback_from_artifact(&artifact, delta, self.log_size)
            .expect("prover-built GKR artifact has the canonical shape");

        // c(row) = Σ_slot eq(slot, r_slot) · (δ·num_slot(row) + den_slot(row)).
        let packed_delta = PackedQM31::broadcast(delta);
        let mut coeff = vec![PackedQM31::zero(); n_vec_rows];
        for (s, (num, den)) in self.fracs.iter().enumerate() {
            let w = PackedQM31::broadcast(tie_back.eq_ws[s]);
            for (vr, acc) in coeff.iter_mut().enumerate() {
                *acc += w * (packed_delta * num[vr] + den[vr]);
            }
        }
        let coeff_mle = Mle::<SimdBackend, SecureField>::new(
            coeff
                .iter()
                .flat_map(|p| p.to_array())
                .collect::<Vec<_>>()
                .into_iter()
                .collect(),
        );
        (encode_gkr_batch_proof(&proof), tie_back, coeff_mle)
    }
}

// =============================================================================
// Verifier side.
// =============================================================================

/// Replay the GKR proof against the shared channel, bind its output claim to
/// the round's claimed sum (fail-closed), draw δ, and derive the tie-back.
pub fn verify_round_gkr(
    blob: &[u8],
    claimed_sum: SecureField,
    log_size: u32,
    channel: &mut impl Channel,
) -> Result<RoundTieBack, VerificationError> {
    let bad = |msg: String| VerificationError::InvalidStructure(format!("round GKR: {msg}"));
    let proof =
        decode_gkr_batch_proof(blob).map_err(|e| bad(format!("blob decode failed: {e}")))?;
    let [output] = proof.output_claims_by_instance.as_slice() else {
        return Err(bad("expected exactly one GKR instance".into()));
    };
    let [num_out, den_out] = output.as_slice() else {
        return Err(bad("output claims must be [num, den]".into()));
    };
    if *den_out == SecureField::zero() {
        return Err(bad("zero output denominator".into()));
    }
    // The GKR-proven multiset sum must sit exactly where the columnar claimed
    // sum sat in the global LogUp balance.
    if *num_out != claimed_sum * *den_out {
        return Err(bad("output claim does not match the round claimed sum".into()));
    }
    let artifact = partially_verify_batch(vec![Gate::LogUp], &proof, channel)
        .map_err(|e| bad(format!("replay failed: {e}")))?;
    let delta = channel.draw_secure_felt();
    tieback_from_artifact(&artifact, delta, log_size)
}

// =============================================================================
// The MLE coeff-column oracle over the round's committed base columns.
// =============================================================================

/// Reconstructs the δ-folded coeff column at the STARK OODS point from the
/// round component's base-column mask values: replays
/// [`collect_round_lookups`] through a [`PointEvaluator`] over the component's
/// trace sub-tree, combines each tuple through its relation, and folds with
/// the verifier-computed `eq(slot, r_slot)` weights.
pub struct RoundCoeffOracle {
    /// The round `FrameworkComponent`'s trace locations in the shared trees.
    pub locations: Vec<TreeSubspan>,
    pub relations: KeccakRelations,
    pub log_size: u32,
    pub delta: SecureField,
    pub eq_ws: Vec<SecureField>,
}

impl MleCoeffColumnOracle for RoundCoeffOracle {
    fn evaluate_at_point(
        &self,
        _point: CirclePoint<SecureField>,
        mask: &TreeVec<ColumnVec<Vec<SecureField>>>,
    ) -> SecureField {
        // Dummy accumulator: we only extract mask values through the walk.
        let mut acc = PointEvaluationAccumulator::new(SecureField::one());
        let mut eval = PointEvaluator::new(
            mask.sub_tree(&self.locations),
            &mut acc,
            SecureField::one(),
            self.log_size,
            SecureField::zero(),
        );
        let lookups = collect_round_lookups(&mut eval);
        let mut out = SecureField::zero();
        for (s, lk) in lookups.iter().enumerate() {
            let den: SecureField = match lk.kind {
                RoundLookupKind::Kr => self.relations.keccak_round.combine(&lk.tuple),
                RoundLookupKind::Xor3 => self.relations.xor3.combine(&lk.tuple),
                RoundLookupKind::Andnot => self.relations.andnot.combine(&lk.tuple),
                RoundLookupKind::Split(r) => self.relations.split[r - 1].combine(&lk.tuple),
            };
            out += self.eq_ws[s] * (self.delta * lk.num + den);
        }
        out
    }
}
