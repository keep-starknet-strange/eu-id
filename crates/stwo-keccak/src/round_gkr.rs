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
use stwo::prover::backend::simd::column::SecureColumn;
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
    build_fracs, collect_round_lookups, data_log_size, InteractionClaimData, RoundFractions,
    RoundLookupKind, N_TOTAL_LOOKUPS,
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
    fracs: RoundFractions,
    log_size: u32,
    claimed_sum: SecureField,
}

/// Sum every packed fraction in canonical slot/row order. One global batch
/// lets Stwo split the inversion work across its fixed-size Rayon chunks.
fn global_claimed_sum(fracs: &RoundFractions) -> SecureField {
    let inverses = PackedQM31::batch_inverse(fracs.denominators());
    let mut total = PackedQM31::zero();
    for (numerator, denominator_inverse) in fracs.numerators().iter().zip(&inverses) {
        total += *numerator * *denominator_inverse;
    }
    // Preserve the legacy lane-reduction order exactly.
    total.to_array().iter().copied().sum()
}

/// Materialize the canonical slot-high/row-low GKR leaves without unpacking
/// QM31 SIMD lanes. The trailing slots are the neutral fraction 0/1.
fn gkr_input_layer(fracs: &RoundFractions, log_size: u32) -> Layer<SimdBackend> {
    let n_rows = 1usize << log_size;
    let n_vec_rows = 1usize << (log_size - LOG_N_LANES);
    assert_eq!(
        fracs.n_vec_rows(),
        n_vec_rows,
        "round fraction stride must match its trace log size"
    );
    assert_eq!(
        fracs.n_slots(),
        N_TOTAL_LOOKUPS,
        "round GKR must contain every canonical lookup slot"
    );

    let packed_size = (1usize << LOG_SLOTS) * n_vec_rows;
    let scalar_size = (1usize << LOG_SLOTS) * n_rows;
    let mut numerators = Vec::with_capacity(packed_size);
    numerators.extend_from_slice(fracs.numerators());
    numerators.resize(packed_size, PackedQM31::zero());
    let mut denominators = Vec::with_capacity(packed_size);
    denominators.extend_from_slice(fracs.denominators());
    denominators.resize(packed_size, PackedQM31::one());
    debug_assert_eq!(packed_size * N_LANES, scalar_size);

    Layer::LogUpGeneric {
        numerators: Mle::<SimdBackend, SecureField>::new(SecureColumn {
            data: numerators,
            length: scalar_size,
        }),
        denominators: Mle::<SimdBackend, SecureField>::new(SecureColumn {
            data: denominators,
            length: scalar_size,
        }),
    }
}

impl RoundGkrProver {
    /// Build the fraction multiset and its exact sum (== the columnar
    /// `claimed_sum` the offloaded interaction trace would have produced).
    pub fn new(rel: &KeccakRelations, data: &InteractionClaimData) -> Self {
        let fracs = build_fracs(rel, data);
        let claimed_sum = global_claimed_sum(&fracs);
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
        let layer = gkr_input_layer(&self.fracs, self.log_size);
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
        for s in 0..self.fracs.n_slots() {
            let (num, den) = self.fracs.slot(s);
            let w = PackedQM31::broadcast(tie_back.eq_ws[s]);
            for (vr, acc) in coeff.iter_mut().enumerate() {
                *acc += w * (packed_delta * num[vr] + den[vr]);
            }
        }
        let coeff_mle = Mle::<SimdBackend, SecureField>::new(SecureColumn {
            data: coeff,
            length: n_rows,
        });
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
        return Err(bad(
            "output claim does not match the round claimed sum".into()
        ));
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

#[cfg(test)]
mod tests {
    use stwo::core::channel::Blake2sChannel;
    use stwo::prover::backend::simd::m31::PackedM31;
    use stwo::prover::backend::Column;

    use super::*;
    use crate::constants::N_BYTES_IN_STATE;
    use crate::keccak_round::{generate_interaction_trace, Claim};

    fn round_data(invocations: usize) -> InteractionClaimData {
        let input = vec![[PackedM31::zero(); N_BYTES_IN_STATE + 2]];
        let (_, _, data) = Claim::generate_trace(input, invocations);
        data
    }

    /// The claimed-sum implementation before the packed/global-inversion
    /// optimization: invert every slot separately, then accumulate slot/row.
    fn legacy_claimed_sum(fracs: &RoundFractions) -> SecureField {
        let mut total = PackedQM31::zero();
        for slot in 0..fracs.n_slots() {
            let (numerators, denominators) = fracs.slot(slot);
            let inverses = PackedQM31::batch_inverse(denominators);
            for (numerator, denominator_inverse) in numerators.iter().zip(&inverses) {
                total += *numerator * *denominator_inverse;
            }
        }
        total.to_array().iter().copied().sum()
    }

    /// The scalar unpack/repack path before the packed-leaf optimization.
    fn legacy_gkr_input_layer(fracs: &RoundFractions, log_size: u32) -> Layer<SimdBackend> {
        let n_rows = 1usize << log_size;
        let n_vec_rows = 1usize << (log_size - LOG_N_LANES);
        let scalar_size = (1usize << LOG_SLOTS) * n_rows;
        let mut numerators = vec![SecureField::zero(); scalar_size];
        let mut denominators = vec![SecureField::one(); scalar_size];

        for slot in 0..fracs.n_slots() {
            let (slot_numerators, slot_denominators) = fracs.slot(slot);
            for vr in 0..n_vec_rows {
                let packed_numerators = slot_numerators[vr].to_array();
                let packed_denominators = slot_denominators[vr].to_array();
                let base = slot * n_rows + vr * N_LANES;
                for lane in 0..N_LANES {
                    numerators[base + lane] = packed_numerators[lane];
                    denominators[base + lane] = packed_denominators[lane];
                }
            }
        }

        Layer::LogUpGeneric {
            numerators: Mle::<SimdBackend, SecureField>::new(numerators.into_iter().collect()),
            denominators: Mle::<SimdBackend, SecureField>::new(denominators.into_iter().collect()),
        }
    }

    fn layer_values(layer: Layer<SimdBackend>) -> (Vec<SecureField>, Vec<SecureField>) {
        let Layer::LogUpGeneric {
            numerators,
            denominators,
        } = layer
        else {
            panic!("round GKR input must be a generic LogUp layer");
        };
        (numerators.to_cpu(), denominators.to_cpu())
    }

    #[test]
    fn packed_leaves_and_global_claimed_sum_match_legacy_exactly() {
        let data = round_data(33);
        let log_size = data_log_size(&data);
        let mut relation_channel = Blake2sChannel::default();
        let relations = KeccakRelations::draw(&mut relation_channel);
        let fracs = build_fracs(&relations, &data);

        let packed_values = layer_values(gkr_input_layer(&fracs, log_size));
        let legacy_values = layer_values(legacy_gkr_input_layer(&fracs, log_size));
        assert_eq!(
            packed_values, legacy_values,
            "packed leaves must preserve slot/row/lane order and 0/1 padding"
        );

        let packed_sum = global_claimed_sum(&fracs);
        assert_eq!(
            packed_sum,
            legacy_claimed_sum(&fracs),
            "one global inversion must preserve the legacy claimed sum"
        );
        let (columnar_claim, _) = generate_interaction_trace(&relations, &data);
        assert_eq!(
            packed_sum, columnar_claim.claimed_sum,
            "GKR claimed sum must remain identical to the columnar LogUp"
        );
    }

    #[test]
    fn packed_and_legacy_layers_produce_identical_seeded_gkr_transcript() {
        let data = round_data(33);
        let log_size = data_log_size(&data);

        // Drawing relations and mixing the claimed sum mirrors the production
        // channel position immediately before the round GKR block.
        let mut packed_channel = Blake2sChannel::default();
        let relations = KeccakRelations::draw(&mut packed_channel);
        let mut legacy_channel = Blake2sChannel::default();
        let _ = KeccakRelations::draw(&mut legacy_channel);
        let fracs = build_fracs(&relations, &data);
        let sum = global_claimed_sum(&fracs);
        packed_channel.mix_felts(&[sum]);
        legacy_channel.mix_felts(&[sum]);

        let (packed_proof, packed_artifact) =
            prove_batch(&mut packed_channel, vec![gkr_input_layer(&fracs, log_size)]);
        let (legacy_proof, legacy_artifact) = prove_batch(
            &mut legacy_channel,
            vec![legacy_gkr_input_layer(&fracs, log_size)],
        );

        assert_eq!(
            encode_gkr_batch_proof(&packed_proof),
            encode_gkr_batch_proof(&legacy_proof),
            "packed leaves must produce a byte-identical GKR proof"
        );
        assert_eq!(packed_artifact.ood_point, legacy_artifact.ood_point);
        assert_eq!(
            packed_artifact.claims_to_verify_by_instance,
            legacy_artifact.claims_to_verify_by_instance
        );
        assert_eq!(
            packed_artifact.n_variables_by_instance,
            legacy_artifact.n_variables_by_instance
        );

        let packed_delta = packed_channel.draw_secure_felt();
        let legacy_delta = legacy_channel.draw_secure_felt();
        assert_eq!(
            packed_delta, legacy_delta,
            "the post-GKR transcript challenge must remain identical"
        );
        let packed_tieback =
            tieback_from_artifact(&packed_artifact, packed_delta, log_size).unwrap();
        let legacy_tieback =
            tieback_from_artifact(&legacy_artifact, legacy_delta, log_size).unwrap();
        assert_eq!(packed_tieback.r_row, legacy_tieback.r_row);
        assert_eq!(packed_tieback.delta, legacy_tieback.delta);
        assert_eq!(packed_tieback.eq_ws, legacy_tieback.eq_ws);
        assert_eq!(packed_tieback.mle_claim, legacy_tieback.mle_claim);
    }

    #[test]
    fn production_log12_lengths_keep_slot_high_and_row_low() {
        const PRODUCTION_LOG_SIZE: u32 = 12;
        let n_rows = 1usize << PRODUCTION_LOG_SIZE;
        let n_vec_rows = 1usize << (PRODUCTION_LOG_SIZE - LOG_N_LANES);
        let active_packed_len = N_TOTAL_LOOKUPS * n_vec_rows;
        let padded_packed_len = (1usize << LOG_SLOTS) * n_vec_rows;

        assert_eq!(n_vec_rows, 256);
        assert_eq!(active_packed_len, 229_888);
        assert_eq!(padded_packed_len, 262_144);
        assert_eq!(
            (N_TOTAL_LOOKUPS - 1) * n_vec_rows + (n_vec_rows - 1),
            active_packed_len - 1,
            "slot 897 row 255 must be the final active packed leaf"
        );
        assert_eq!(
            ((N_TOTAL_LOOKUPS - 1) * n_vec_rows + (n_vec_rows - 1)) * N_LANES + (N_LANES - 1),
            N_TOTAL_LOOKUPS * n_rows - 1,
            "the final SIMD lane must remain the final row of slot 897"
        );
        assert_eq!(
            padded_packed_len * N_LANES,
            1usize << (LOG_SLOTS + PRODUCTION_LOG_SIZE),
            "SecureColumn length is scalar, not packed"
        );
        assert_eq!(n_vec_rows * N_LANES, n_rows);
    }
}
