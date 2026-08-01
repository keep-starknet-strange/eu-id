//! GKR offload for carrier LogUp interactions.
//!
//! A LogUp GKR proof replaces the carrier component's interaction columns. One
//! `MleEval` tie-back component binds the GKR input claims to the committed
//! base trace. The component uses eight committed tree-3 columns.
//!
//! ## Layout
//!
//! The proof puts all five relation families in one `Layer::LogUpMultiplicities`
//! instance. It uses the order from
//! [`crate::carrier::collect_lookups`]. The lookup slot uses the high index
//! bits. The trace row uses the low index bits. The GKR OOD point splits as
//! `r = (r_slot ‖ r_row)`. Each `Relation::combine` is an affine form with
//! row-independent coefficients. Thus, the input MLEs decompose as follows:
//!
//! ```text
//! den_mle(r) = Σ_slot eq(slot, r_slot) · combine_slot([tupleⱼ_mle(r_row)]ⱼ)
//! num_mle(r) = Σ_slot eq(slot, r_slot) · num_slot_mle(r_row)
//! ```
//!
//! The tie-back uses only the row domain. It has one δ-folded coefficient
//! column: `c(row) = Σ_slot eq(slot,r_slot)·(δ·num_slot(row) +
//! den_slot(row))`. Its MLE at `r_row` must equal `δ·num_claim + den_claim −
//! pad(r_slot)`. Padding slots contribute the constant fraction `0/1`.
//! [`RoundCoeffOracle`] reconstructs `c` at the STARK OODS point from the
//! committed base-column mask values.
//!
//! ## Fiat-Shamir order
//!
//! Commit tree 2. Then, run `prove_batch` or `partially_verify_batch` on the
//! shared channel. Draw δ and commit the tree-3 tie-back trace. This sequence
//! binds the GKR proof to trees 0-2, the relations, and the claimed sums.
//!
//! ## TS13 demo soundness contribution
//!
//! The n=261 profile has 10 slot variables and 13 row variables. Its 23 GKR
//! layers contain 253 sumcheck rounds. Each round has degree at most three.
//! Let `q = (2^31 - 1)^4`, the size of QM31. A conservative union bound is
//! `759/q` for sumcheck, `23/q` for the layer column folds, `1/q` for δ, and
//! `8191/q` for the outer log13 MLE identity. The total is `8974/q`, which is
//! about `2^-110.9`. The demo's existing 108-bit algebraic OODS bound remains
//! the limiting algebraic bound. Its 128-bit PCS query and proof-of-work bound
//! also remains stronger than the 108-bit bound.

use num_traits::{One, Zero};
use stwo::core::air::accumulation::PointEvaluationAccumulator;
use stwo::core::channel::Channel;
use stwo::core::circle::CirclePoint;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::core::fields::FieldExpOps;
use stwo::core::pcs::{TreeSubspan, TreeVec};
use stwo::core::verifier::VerificationError;
use stwo::core::ColumnVec;
use stwo::prover::backend::simd::column::{BaseColumn, SecureColumn};
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES, N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::lookups::gkr_prover::{prove_batch, Layer};
use stwo::prover::lookups::gkr_verifier::{partially_verify_batch, Gate, GkrArtifact};
use stwo::prover::lookups::mle::Mle;
use stwo_constraint_framework::mle_eval::MleCoeffColumnOracle;
use stwo_constraint_framework::{PointEvaluator, Relation};

use air_core::gkr::{decode_gkr_batch_proof, encode_gkr_batch_proof};

use crate::carrier::{
    build_fractions, collect_lookups, Fractions, InteractionData, LookupKind, N_TOTAL_LOOKUPS,
};
use crate::relations::KeccakRelations;

/// Slot-index bits of the flattened GKR instance (899 real slots to 1024).
pub const LOG_SLOTS: u32 = 10;
const _: () = assert!(
    N_TOTAL_LOOKUPS <= 1 << LOG_SLOTS && N_TOTAL_LOOKUPS > 1 << (LOG_SLOTS - 1),
    "LOG_SLOTS must be ilog2(next_power_of_two(N_TOTAL_LOOKUPS))"
);

/// Committed tree-3 columns of the tie-back trace (eq evals + shifted prefix
/// sums, each one QM31 column = 4 M31 columns).
pub const N_TIEBACK_COLUMNS: usize = 2 * SECURE_EXTENSION_DEGREE;
const _: () = assert!(N_TIEBACK_COLUMNS == 8);

/// Everything both sides derive from the GKR transcript for the tie-back.
pub struct RoundTieBack {
    /// The row half of the GKR OOD point. This is the MleEval evaluation point.
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
/// GKR OOD convention. The first point coordinate splits the top half).
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
    let bad = |msg: &str| VerificationError::InvalidStructure(format!("carrier GKR: {msg}"));
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

// Prover side.

/// Prover state for the fraction columns, GKR leaves, and tie-back column.
pub struct RoundGkrProver {
    fracs: Fractions,
    log_size: u32,
    claimed_sum: SecureField,
}

/// Sum every packed fraction in canonical slot/row order. One global batch
/// lets Stwo split the inversion work across its fixed-size Rayon chunks.
fn global_claimed_sum(fracs: &Fractions) -> SecureField {
    let inverses = PackedQM31::batch_inverse(fracs.denominators());
    let mut total = PackedQM31::zero();
    for (numerator, denominator_inverse) in fracs.numerators().iter().zip(&inverses) {
        total += *denominator_inverse * *numerator;
    }
    // Reduce the lanes in the fixed order that defines the claimed sum.
    total.to_array().iter().copied().sum()
}

/// Materialize the canonical slot-high/row-low GKR leaves without unpacking
/// SIMD lanes. The trailing slots are the neutral fraction 0/1.
fn gkr_input_layer(fracs: &Fractions, log_size: u32) -> Layer<SimdBackend> {
    let n_rows = 1usize << log_size;
    let n_vec_rows = 1usize << (log_size - LOG_N_LANES);
    assert_eq!(
        fracs.n_vector_rows(),
        n_vec_rows,
        "carrier fraction stride must match its trace log size"
    );
    assert_eq!(
        fracs.n_slots(),
        N_TOTAL_LOOKUPS,
        "carrier GKR must contain every canonical lookup slot"
    );

    let packed_size = (1usize << LOG_SLOTS) * n_vec_rows;
    let scalar_size = (1usize << LOG_SLOTS) * n_rows;
    let mut numerators = Vec::with_capacity(packed_size);
    numerators.extend_from_slice(fracs.numerators());
    numerators.resize(packed_size, PackedM31::zero());
    let mut denominators = Vec::with_capacity(packed_size);
    denominators.extend_from_slice(fracs.denominators());
    denominators.resize(packed_size, PackedQM31::one());
    debug_assert_eq!(packed_size * N_LANES, scalar_size);

    Layer::LogUpMultiplicities {
        numerators: Mle::<SimdBackend, BaseField>::new(BaseColumn {
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
    pub fn new(rel: &KeccakRelations, data: &InteractionData) -> Self {
        let fracs = build_fractions(rel, data);
        let claimed_sum = global_claimed_sum(&fracs);
        Self {
            fracs,
            log_size: data.log_size,
            claimed_sum,
        }
    }

    pub fn claimed_sum(&self) -> SecureField {
        self.claimed_sum
    }

    /// Flatten to the slot-high/row-low multiplicities instance, prove it on
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
            "GKR output claim != carrier claimed sum"
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

// Verifier side.

/// Replay the GKR proof, bind its output to the carrier sum, and derive the
/// tie-back.
pub fn verify_round_gkr(
    blob: &[u8],
    claimed_sum: SecureField,
    log_size: u32,
    channel: &mut impl Channel,
) -> Result<RoundTieBack, VerificationError> {
    let bad = |msg: String| VerificationError::InvalidStructure(format!("carrier GKR: {msg}"));
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

// The MLE coefficient-column oracle over the committed carrier columns.

/// Reconstruct the folded coefficient at the STARK OODS point from committed
/// carrier masks. The oracle replays [`collect_lookups`] and folds each lookup
/// with the verifier-computed slot weight.
pub struct RoundCoeffOracle {
    /// The carrier component's trace locations in the shared trees.
    pub locations: Vec<TreeSubspan>,
    pub relations: KeccakRelations,
    pub log_size: u32,
    pub delta: SecureField,
    pub eq_ws: Vec<SecureField>,
    pub n_perms: usize,
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
        let lookups = collect_lookups(&mut eval, self.n_perms);
        assert_eq!(lookups.len(), N_TOTAL_LOOKUPS);
        let mut out = SecureField::zero();
        for (s, lk) in lookups.iter().enumerate() {
            let den: SecureField = match lk.kind {
                LookupKind::Schedule => self.relations.round_schedule.combine(&lk.tuple),
                LookupKind::State => self.relations.keccak_state.combine(&lk.tuple),
                LookupKind::Xor3 => self.relations.xor3.combine(&lk.tuple),
                LookupKind::Andnot => self.relations.andnot.combine(&lk.tuple),
                LookupKind::Split(r) => self.relations.split[r - 1].combine(&lk.tuple),
            };
            out += self.eq_ws[s] * (self.delta * lk.num + den);
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use stwo::core::channel::Blake2sChannel;
    use stwo::core::fields::m31::M31;
    use stwo::prover::backend::simd::m31::PackedM31;
    use stwo::prover::backend::Column;
    use stwo_constraint_framework::{EvalAtRow, ORIGINAL_TRACE_IDX};

    use super::*;
    use crate::constants::N_BYTES_IN_STATE;
    use crate::utils::{circle_row_to_coset, ColEval};
    use crate::{carrier, keccak};

    fn carrier_witness(n_perms: usize) -> carrier::Witness {
        let mut inputs = vec![[PackedM31::zero(); N_BYTES_IN_STATE + 1]; n_perms];
        for (permutation, input) in inputs.iter_mut().enumerate() {
            input[N_BYTES_IN_STATE] = PackedM31::from(M31::from(permutation as u32));
        }
        let boundaries = keccak::generate_boundary_witness(&inputs);
        carrier::generate(&boundaries)
    }

    fn carrier_data(n_perms: usize) -> InteractionData {
        carrier_witness(n_perms).interaction
    }

    fn multilinear_eval(values: &[SecureField], point: &[SecureField]) -> SecureField {
        match point {
            [] => values[0],
            [coordinate, rest @ ..] => {
                let (left, right) = values.split_at(values.len() / 2);
                let left = multilinear_eval(left, rest);
                let right = multilinear_eval(right, rest);
                left + *coordinate * (right - left)
            }
        }
    }

    struct MleMaskEvaluator {
        masks: Vec<[SecureField; 2]>,
        column: usize,
    }

    impl MleMaskEvaluator {
        fn new(trace: &[ColEval], point: &[SecureField], log_size: u32) -> Self {
            let row_to_coset = circle_row_to_coset(log_size);
            let mut coset_to_row = vec![0; row_to_coset.len()];
            for (row, coset) in row_to_coset.iter().copied().enumerate() {
                coset_to_row[coset] = row;
            }

            let masks = trace
                .iter()
                .map(|column| {
                    let current: Vec<SecureField> = column
                        .values
                        .to_cpu()
                        .into_iter()
                        .map(SecureField::from)
                        .collect();
                    let previous: Vec<SecureField> = row_to_coset
                        .iter()
                        .map(|coset| {
                            let previous_coset =
                                (coset + row_to_coset.len() - 1) % row_to_coset.len();
                            current[coset_to_row[previous_coset]]
                        })
                        .collect();
                    [
                        multilinear_eval(&previous, point),
                        multilinear_eval(&current, point),
                    ]
                })
                .collect();
            Self { masks, column: 0 }
        }
    }

    impl EvalAtRow for MleMaskEvaluator {
        type F = SecureField;
        type EF = SecureField;

        fn next_interaction_mask<const N: usize>(
            &mut self,
            interaction: usize,
            offsets: [isize; N],
        ) -> [Self::F; N] {
            assert_eq!(interaction, ORIGINAL_TRACE_IDX);
            let mask = self.masks[self.column];
            self.column += 1;
            offsets.map(|offset| match offset {
                -1 => mask[0],
                0 => mask[1],
                _ => panic!("unsupported carrier mask offset {offset}"),
            })
        }

        fn add_constraint<G>(&mut self, _constraint: G)
        where
            Self::EF: std::ops::Mul<G, Output = Self::EF> + From<G>,
        {
        }

        fn combine_ef(_values: [Self::F; SECURE_EXTENSION_DEGREE]) -> Self::EF {
            unreachable!("the carrier lookup walk reads base-trace masks only")
        }
    }

    /// Scalar reference: invert each slot, then add the fractions.
    fn slotwise_claimed_sum_reference(fracs: &Fractions) -> SecureField {
        let mut total = PackedQM31::zero();
        for slot in 0..fracs.n_slots() {
            let (numerators, denominators) = fracs.slot(slot);
            let inverses = PackedQM31::batch_inverse(denominators);
            for (numerator, denominator_inverse) in numerators.iter().zip(&inverses) {
                total += *denominator_inverse * *numerator;
            }
        }
        total.to_array().iter().copied().sum()
    }

    /// Secure-field reference for the multiplicities GKR input layer.
    fn generic_gkr_input_layer_reference(fracs: &Fractions, log_size: u32) -> Layer<SimdBackend> {
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
                    numerators[base + lane] = SecureField::from(packed_numerators[lane]);
                    denominators[base + lane] = packed_denominators[lane];
                }
            }
        }

        Layer::LogUpGeneric {
            numerators: Mle::<SimdBackend, SecureField>::new(numerators.into_iter().collect()),
            denominators: Mle::<SimdBackend, SecureField>::new(denominators.into_iter().collect()),
        }
    }

    fn generic_layer_values(layer: Layer<SimdBackend>) -> (Vec<SecureField>, Vec<SecureField>) {
        let Layer::LogUpGeneric {
            numerators,
            denominators,
        } = layer
        else {
            panic!("carrier GKR input must be a generic LogUp layer");
        };
        (numerators.to_cpu(), denominators.to_cpu())
    }

    fn multiplicities_layer_values(
        layer: Layer<SimdBackend>,
    ) -> (Vec<SecureField>, Vec<SecureField>) {
        let Layer::LogUpMultiplicities {
            numerators,
            denominators,
        } = layer
        else {
            panic!("carrier GKR input must be a multiplicities LogUp layer");
        };
        (
            numerators
                .to_cpu()
                .into_iter()
                .map(SecureField::from)
                .collect(),
            denominators.to_cpu(),
        )
    }

    fn generic_tieback_coefficients(
        layer: Layer<SimdBackend>,
        tie_back: &RoundTieBack,
        log_size: u32,
    ) -> Vec<SecureField> {
        let (numerators, denominators) = generic_layer_values(layer);
        let n_rows = 1usize << log_size;
        (0..n_rows)
            .map(|row| {
                (0..N_TOTAL_LOOKUPS)
                    .map(|slot| {
                        let index = slot * n_rows + row;
                        tie_back.eq_ws[slot]
                            * (tie_back.delta * numerators[index] + denominators[index])
                    })
                    .sum()
            })
            .collect()
    }

    #[test]
    fn multiplicities_leaves_and_claimed_sum_match_generic_reference() {
        let data = carrier_data(2);
        let log_size = data.log_size;
        let mut relation_channel = Blake2sChannel::default();
        let relations = KeccakRelations::draw(&mut relation_channel);
        let fracs = build_fractions(&relations, &data);

        let multiplicities_values = multiplicities_layer_values(gkr_input_layer(&fracs, log_size));
        let generic_values =
            generic_layer_values(generic_gkr_input_layer_reference(&fracs, log_size));
        assert_eq!(
            multiplicities_values, generic_values,
            "base leaves must preserve the secure embedding and slot, row, lane, and padding order"
        );

        let multiplicities_sum = global_claimed_sum(&fracs);
        assert_eq!(
            multiplicities_sum,
            slotwise_claimed_sum_reference(&fracs),
            "global inversion must match the slotwise reference sum"
        );
        let (columnar_claim, _) = carrier::generate_interaction_trace(&relations, &data);
        assert_eq!(
            multiplicities_sum, columnar_claim.claimed_sum,
            "GKR claimed sum must remain identical to the columnar LogUp"
        );
    }

    #[test]
    fn carrier_denominator_oracle_reconstructs_and_detects_tampering() {
        const N_PERMUTATIONS: usize = 2;

        let witness = carrier_witness(N_PERMUTATIONS);
        let log_size = witness.interaction.log_size;
        let mut relation_channel = Blake2sChannel::default();
        let relations = KeccakRelations::draw(&mut relation_channel);
        let fractions = build_fractions(&relations, &witness.interaction);

        let mut gkr_channel = Blake2sChannel::default();
        let (_, artifact) = prove_batch(
            &mut gkr_channel,
            vec![gkr_input_layer(&fractions, log_size)],
        );
        let [numerator_claim, denominator_claim] =
            artifact.claims_to_verify_by_instance[0].as_slice()
        else {
            panic!("carrier GKR input claims must contain a numerator and denominator");
        };
        let (slot_point, row_point) = artifact.ood_point.split_at(LOG_SLOTS as usize);
        let weights = eq_weights(slot_point);

        let mut evaluator = MleMaskEvaluator::new(&witness.trace, row_point, log_size);
        let lookups = carrier::collect_lookups(&mut evaluator, N_PERMUTATIONS);
        assert_eq!(evaluator.column, witness.trace.len());
        assert_eq!(lookups.len(), N_TOTAL_LOOKUPS);

        let mut reconstructed_numerator = SecureField::zero();
        let mut reconstructed_denominator = SecureField::zero();
        for (slot, lookup) in lookups.iter().enumerate() {
            let denominator: SecureField = match lookup.kind {
                LookupKind::Schedule => relations.round_schedule.combine(&lookup.tuple),
                LookupKind::State => relations.keccak_state.combine(&lookup.tuple),
                LookupKind::Xor3 => relations.xor3.combine(&lookup.tuple),
                LookupKind::Andnot => relations.andnot.combine(&lookup.tuple),
                LookupKind::Split(shift) => relations.split[shift - 1].combine(&lookup.tuple),
            };
            reconstructed_numerator += weights[slot] * lookup.num;
            reconstructed_denominator += weights[slot] * denominator;
        }
        reconstructed_denominator += weights[N_TOTAL_LOOKUPS..]
            .iter()
            .copied()
            .sum::<SecureField>();

        assert_eq!(reconstructed_numerator, *numerator_claim);
        assert_eq!(reconstructed_denominator, *denominator_claim);

        let honest_schedule_denominator: SecureField =
            relations.round_schedule.combine(&lookups[0].tuple);
        let mut tampered_schedule_tuple = lookups[0].tuple.clone();
        tampered_schedule_tuple[0] += SecureField::one();
        let tampered_schedule_denominator: SecureField =
            relations.round_schedule.combine(&tampered_schedule_tuple);
        let tampered_reconstruction = reconstructed_denominator
            + weights[0] * (tampered_schedule_denominator - honest_schedule_denominator);
        assert_ne!(tampered_reconstruction, *denominator_claim);
    }

    #[test]
    fn multiplicities_layer_preserves_seeded_gkr_and_tieback() {
        let data = carrier_data(2);
        let log_size = data.log_size;

        // Draw the relations and mix the claimed sum at the protocol channel
        // position before the carrier GKR block.
        let mut multiplicities_channel = Blake2sChannel::default();
        let relations = KeccakRelations::draw(&mut multiplicities_channel);
        let mut generic_channel = Blake2sChannel::default();
        let _ = KeccakRelations::draw(&mut generic_channel);
        let mut prover_channel = Blake2sChannel::default();
        let _ = KeccakRelations::draw(&mut prover_channel);
        let fracs = build_fractions(&relations, &data);
        let sum = global_claimed_sum(&fracs);
        multiplicities_channel.mix_felts(&[sum]);
        generic_channel.mix_felts(&[sum]);
        prover_channel.mix_felts(&[sum]);

        let (multiplicities_proof, multiplicities_artifact) = prove_batch(
            &mut multiplicities_channel,
            vec![gkr_input_layer(&fracs, log_size)],
        );
        let (generic_proof, generic_artifact) = prove_batch(
            &mut generic_channel,
            vec![generic_gkr_input_layer_reference(&fracs, log_size)],
        );

        let multiplicities_blob = encode_gkr_batch_proof(&multiplicities_proof);
        assert_eq!(
            multiplicities_blob,
            encode_gkr_batch_proof(&generic_proof),
            "base leaves must produce a byte-identical GKR proof"
        );
        assert_eq!(
            multiplicities_artifact.ood_point,
            generic_artifact.ood_point
        );
        assert_eq!(
            multiplicities_artifact.claims_to_verify_by_instance,
            generic_artifact.claims_to_verify_by_instance
        );
        assert_eq!(
            multiplicities_artifact.n_variables_by_instance,
            generic_artifact.n_variables_by_instance
        );

        let multiplicities_delta = multiplicities_channel.draw_secure_felt();
        let generic_delta = generic_channel.draw_secure_felt();
        assert_eq!(
            multiplicities_delta, generic_delta,
            "the post-GKR transcript challenge must remain identical"
        );
        let multiplicities_tieback =
            tieback_from_artifact(&multiplicities_artifact, multiplicities_delta, log_size)
                .unwrap();
        let generic_tieback =
            tieback_from_artifact(&generic_artifact, generic_delta, log_size).unwrap();
        assert_eq!(multiplicities_tieback.r_row, generic_tieback.r_row);
        assert_eq!(multiplicities_tieback.delta, generic_tieback.delta);
        assert_eq!(multiplicities_tieback.eq_ws, generic_tieback.eq_ws);
        assert_eq!(multiplicities_tieback.mle_claim, generic_tieback.mle_claim);

        let (prover_blob, prover_tieback, coeff_mle) =
            RoundGkrProver::new(&relations, &data).prove(&mut prover_channel);
        assert_eq!(prover_blob, multiplicities_blob);
        assert_eq!(prover_tieback.r_row, multiplicities_tieback.r_row);
        assert_eq!(prover_tieback.delta, multiplicities_tieback.delta);
        assert_eq!(prover_tieback.eq_ws, multiplicities_tieback.eq_ws);
        assert_eq!(prover_tieback.mle_claim, multiplicities_tieback.mle_claim);

        let generic_coefficients = generic_tieback_coefficients(
            generic_gkr_input_layer_reference(&fracs, log_size),
            &generic_tieback,
            log_size,
        );
        assert_eq!(coeff_mle.to_cpu(), generic_coefficients);
        assert_eq!(
            multilinear_eval(&generic_coefficients, &generic_tieback.r_row),
            generic_tieback.mle_claim,
            "the folded coefficient MLE must keep the exact tie-back claim"
        );

        let multiplicities_next = multiplicities_channel.draw_secure_felt();
        let generic_next = generic_channel.draw_secure_felt();
        let prover_next = prover_channel.draw_secure_felt();
        assert_eq!(
            multiplicities_next, generic_next,
            "the channel must remain identical after the folding challenge"
        );
        assert_eq!(
            generic_next, prover_next,
            "RoundGkrProver must leave the channel at the same position"
        );
    }

    #[test]
    fn log12_lengths_keep_slot_high_and_row_low() {
        const LOG_SIZE: u32 = 12;
        let n_rows = 1usize << LOG_SIZE;
        let n_vec_rows = 1usize << (LOG_SIZE - LOG_N_LANES);
        let active_packed_len = N_TOTAL_LOOKUPS * n_vec_rows;
        let padded_packed_len = (1usize << LOG_SLOTS) * n_vec_rows;

        assert_eq!(n_vec_rows, 256);
        assert_eq!(active_packed_len, 230_144);
        assert_eq!(padded_packed_len, 262_144);
        assert_eq!(
            (N_TOTAL_LOOKUPS - 1) * n_vec_rows + (n_vec_rows - 1),
            active_packed_len - 1,
            "slot 898 row 255 must be the final active packed leaf"
        );
        assert_eq!(
            ((N_TOTAL_LOOKUPS - 1) * n_vec_rows + (n_vec_rows - 1)) * N_LANES + (N_LANES - 1),
            N_TOTAL_LOOKUPS * n_rows - 1,
            "the final SIMD lane must remain the final row of slot 898"
        );
        assert_eq!(
            padded_packed_len * N_LANES,
            1usize << (LOG_SLOTS + LOG_SIZE),
            "SecureColumn length is scalar, not packed"
        );
        assert_eq!(n_vec_rows * N_LANES, n_rows);
    }
}
