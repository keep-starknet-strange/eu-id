//! γ-digest reshape gadget: one LogUp provide per wide row instead of one
//! fraction per range-checked value.
//!
//! Design + soundness worksheet: `docs/gamma-digest-design.md`. In short: a
//! wide consumer row's fixed list of range-checked values `v_0..v_{L-1}` is
//! bound into a single QM31 digest `D = Σ v_i · γ^{P−1−i}` (`P` = the
//! lane-padded length, γ channel-drawn AFTER the base commit), yielded as one
//! `GammaDigest` tuple `(tag, row_index, d0..d3)`. A tall expander component
//! re-commits the same values K per row, recomputes the digest with a running
//! accumulator `acc = acc_prev·γ^K + Σ_j v_j·γ^{K−1−j}` (group resets via
//! preprocessed start flags), consumes the digest tuple at each preprocessed
//! group end, and emits the K range-check uses per row that the wide row no
//! longer pays for.
//!
//! The digest coordinates on the wide side are degree-1 M31-linear
//! combinations of base columns (the coordinates of `γ^i·v` are `coord_j(γ^i)
//! · v`), so adoption adds NO wide columns and NO wide constraints — only the
//! single relation entry.

use core::array;

use stwo::core::channel::Channel;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::core::utils::{bit_reverse_index, coset_index_to_circle_domain_index};
use stwo::prover::backend::simd::m31::{LOG_N_LANES, N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, INTERACTION_TRACE_IDX,
};

use crate::range_checks::{consecutive_batching, write_batched_logup_columns, RangeCheckRelation};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};

/// Values per tall-expander row (`K` in the design doc). 8 keeps the tall
/// instances small (group of L values → ceil(L/8) rows) while the batched
/// logup stays at 5 QM31 columns (K range uses + 1 digest use, batch 2).
pub const GAMMA_DIGEST_LANES: usize = 8;

/// `(tag, row_index, d0, d1, d2, d3)`.
pub const GAMMA_DIGEST_RELATION_ARITY: usize = 2 + SECURE_EXTENSION_DEGREE;

relation!(GammaDigestRelation, GAMMA_DIGEST_RELATION_ARITY);

// Tags are globally unique per (adopted component, table kind); they keep
// digest tuples from ever colliding across instances.
pub const GAMMA_TAG_FAKE_GLV_RANGE13: u32 = 1;
pub const GAMMA_TAG_FAKE_GLV_SIGNED: u32 = 2;
pub const GAMMA_TAG_PREPARED_RANGE13: u32 = 3;
pub const GAMMA_TAG_PREPARED_SIGNED: u32 = 4;

/// The post-base-commit digest challenge: γ and its powers up to the largest
/// lane-padded value-list length any adopted component uses. Drawn at the
/// same transcript position as the LogUp relations (mirrors
/// [`crate::components::hinted_mul::HintedMulChallenge`]).
#[derive(Clone, Debug)]
pub struct GammaChallenge {
    pub gamma: SecureField,
    powers: Vec<SecureField>,
}

impl GammaChallenge {
    pub fn draw(channel: &mut impl Channel, max_padded_values: usize) -> Self {
        Self::from_gamma(channel.draw_secure_felt(), max_padded_values)
    }

    pub fn from_gamma(gamma: SecureField, max_padded_values: usize) -> Self {
        let one = SecureField::from(M31::from_u32_unchecked(1));
        let mut powers = Vec::with_capacity(max_padded_values.max(GAMMA_DIGEST_LANES) + 1);
        powers.push(one);
        for _ in 0..max_padded_values.max(GAMMA_DIGEST_LANES) {
            powers.push(*powers.last().unwrap() * gamma);
        }
        Self { gamma, powers }
    }

    pub fn power(&self, exponent: usize) -> SecureField {
        self.powers[exponent]
    }
}

// ---------------------------------------------------------------------------
// Wide side (the adopting component)
// ---------------------------------------------------------------------------

/// Round a value-list length up to a whole number of tall rows.
pub const fn gamma_padded_values(values_len: usize) -> usize {
    values_len.div_ceil(GAMMA_DIGEST_LANES) * GAMMA_DIGEST_LANES
}

/// Eval-side: yield (−presence) the digest tuple for one wide row. `values`
/// is the row's fixed use-column list in digest order; missing tail lanes are
/// implicit zeros. The digest coordinates are built as degree-1 expressions of
/// the value columns, so this adds one relation entry and nothing else.
pub fn yield_gamma_digest<E: EvalAtRow>(
    eval: &mut E,
    relation: &GammaDigestRelation,
    challenge: &GammaChallenge,
    tag: u32,
    row_index: E::F,
    presence: E::F,
    pad_value: M31,
    values: &[E::F],
) {
    let padded = gamma_padded_values(values.len());
    // The lane-padding tail holds `pad_value` on the tall side; its digest
    // contribution `pad·(γ^0 + … + γ^(P−L−1))` is a constant.
    let pad_sum = pad_tail_sum(challenge, values.len()) * SecureField::from(pad_value);
    let pad_coords = pad_sum.to_m31_array();
    let mut coords: [E::F; SECURE_EXTENSION_DEGREE] =
        array::from_fn(|coord| E::F::from(pad_coords[coord]));
    for (i, value) in values.iter().enumerate() {
        let power = challenge.power(padded - 1 - i).to_m31_array();
        for (coord, power_coord) in coords.iter_mut().zip(power) {
            *coord = coord.clone() + E::F::from(power_coord) * value.clone();
        }
    }
    let mut tuple = Vec::with_capacity(GAMMA_DIGEST_RELATION_ARITY);
    tuple.push(E::F::from(M31::from_u32_unchecked(tag)));
    tuple.push(row_index);
    tuple.extend(coords);
    eval.add_to_relation(RelationEntry::new(
        relation,
        -E::EF::from(presence),
        &tuple,
    ));
}

/// Sum of the γ powers covering the lane-padding tail: `γ^0 + … + γ^(P−L−1)`.
fn pad_tail_sum(challenge: &GammaChallenge, values_len: usize) -> SecureField {
    let padded = gamma_padded_values(values_len);
    let mut sum = SecureField::from(M31::from_u32_unchecked(0));
    for power in 0..(padded - values_len) {
        sum += challenge.power(power);
    }
    sum
}

/// Gen-side digest of one wide row's concrete values (lane-padded with
/// `pad_value`).
pub fn gamma_digest_of_values(
    challenge: &GammaChallenge,
    pad_value: M31,
    values: &[M31],
) -> SecureField {
    let padded = gamma_padded_values(values.len());
    let mut digest = pad_tail_sum(challenge, values.len()) * SecureField::from(pad_value);
    for (i, value) in values.iter().enumerate() {
        digest += challenge.power(padded - 1 - i) * SecureField::from(*value);
    }
    digest
}

/// Gen-side `(tag, row_index, d0..d3)` tuple matching [`yield_gamma_digest`].
pub fn gamma_digest_tuple(tag: u32, row_index: M31, digest: SecureField) -> [M31; GAMMA_DIGEST_RELATION_ARITY] {
    let coords = digest.to_m31_array();
    [
        M31::from_u32_unchecked(tag),
        row_index,
        coords[0],
        coords[1],
        coords[2],
        coords[3],
    ]
}

// ---------------------------------------------------------------------------
// Tall expander component (one instance per (component, kind))
// ---------------------------------------------------------------------------

/// Static geometry of one tall instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GammaTallLayout {
    pub tag: u32,
    /// Number of wide rows yielding a digest (= digest groups).
    pub group_count: usize,
    /// The wide row's use-list length L (pre-padding).
    pub values_per_group: usize,
}

impl GammaTallLayout {
    pub const fn rows_per_group(&self) -> usize {
        self.values_per_group.div_ceil(GAMMA_DIGEST_LANES)
    }

    pub const fn padded_values(&self) -> usize {
        gamma_padded_values(self.values_per_group)
    }

    pub fn active_rows(&self) -> usize {
        self.group_count * self.rows_per_group()
    }

    pub fn log_size(&self) -> u32 {
        padded_log_size(self.active_rows()).max(LOG_N_LANES)
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.tag as u64);
        channel.mix_u64(self.group_count as u64);
        channel.mix_u64(self.values_per_group as u64);
    }
}

/// Witness of one tall instance: per group (wide row), the L values in digest
/// order. The wide row's `row_index` is its position in this vector.
#[derive(Clone, Debug)]
pub struct GammaTallInstance {
    pub layout: GammaTallLayout,
    /// Value of the lane-padding tail (and a member of the kind's range
    /// table — e.g. `encode_signed_carry(0)` for the signed kind).
    pub pad_value: M31,
    pub group_values: Vec<Vec<M31>>,
}

impl GammaTallInstance {
    pub fn new(
        tag: u32,
        values_per_group: usize,
        pad_value: M31,
        group_values: Vec<Vec<M31>>,
    ) -> Self {
        assert!(values_per_group > 0, "empty digest group");
        for values in &group_values {
            assert_eq!(values.len(), values_per_group, "ragged digest group");
        }
        Self {
            layout: GammaTallLayout {
                tag,
                group_count: group_values.len(),
                values_per_group,
            },
            pad_value,
            group_values,
        }
    }

    /// Lane value at (coset row, lane): group `r / G`, in-group row `r % G`.
    /// Scheduled groups pad their tail lanes with `pad_value`; rows past the
    /// schedule are all-zero.
    fn lane_value(&self, coset_row: usize, lane: usize) -> M31 {
        let g = self.layout.rows_per_group();
        let group = coset_row / g;
        let index = (coset_row % g) * GAMMA_DIGEST_LANES + lane;
        if group >= self.layout.group_count {
            M31::from_u32_unchecked(0)
        } else if index < self.layout.values_per_group {
            self.group_values[group][index]
        } else {
            self.pad_value
        }
    }

    /// All lane-padded values of one group (digest order).
    pub fn padded_group_values(&self, group: usize) -> Vec<M31> {
        let mut values = self.group_values[group].clone();
        values.resize(self.layout.padded_values(), self.pad_value);
        values
    }

    /// Every value the tall instance range-checks, flattened (the kind's
    /// provider multiplicity seed — the single source of truth).
    pub fn all_scheduled_values(&self) -> Vec<M31> {
        (0..self.layout.group_count)
            .flat_map(|group| self.padded_group_values(group))
            .collect()
    }
}

fn gamma_tall_column_id(tag: u32, name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("p256_gamma_tall_{tag}_{name}"),
    }
}

pub fn gamma_tall_preprocessed_ids(tag: u32) -> Vec<PreProcessedColumnId> {
    ["row_id", "start", "end", "in_group"]
        .into_iter()
        .map(|name| gamma_tall_column_id(tag, name))
        .collect()
}

/// Preprocessed schedule columns: `row_id` (which wide row this tall row
/// expands), `start`/`end` (group boundaries), `in_group` (1 on scheduled
/// rows). Coset row 0 is always a group start, so the cyclic wrap of the
/// `[-1]` accumulator mask is multiplied by `(1 − start) = 0`.
pub fn gen_gamma_tall_preprocessed_trace(layout: &GammaTallLayout) -> Vec<M31ColumnEval> {
    let log_size = layout.log_size();
    let rows = 1usize << log_size;
    let g = layout.rows_per_group();
    let mut row_id = vec![M31::from_u32_unchecked(0); rows];
    let mut start = vec![M31::from_u32_unchecked(0); rows];
    let mut end = vec![M31::from_u32_unchecked(0); rows];
    let mut in_group = vec![M31::from_u32_unchecked(0); rows];
    for row in 0..layout.active_rows() {
        row_id[row] = M31::from_u32_unchecked((row / g) as u32);
        start[row] = M31::from_u32_unchecked(u32::from(row % g == 0));
        end[row] = M31::from_u32_unchecked(u32::from(row % g == g - 1));
        in_group[row] = M31::from_u32_unchecked(1);
    }
    [row_id, start, end, in_group]
        .into_iter()
        .map(|values| m31_column_eval(log_size, values))
        .collect()
}

/// Base trace: the K lane columns (coset order; padding rows are zero).
pub fn gen_gamma_tall_base_trace(instance: &GammaTallInstance) -> Vec<M31ColumnEval> {
    let log_size = instance.layout.log_size();
    let rows = 1usize << log_size;
    (0..GAMMA_DIGEST_LANES)
        .map(|lane| {
            let values = (0..rows)
                .map(|row| instance.lane_value(row, lane))
                .collect();
            m31_column_eval(log_size, values)
        })
        .collect()
}

/// Resolve one of a tall instance's preprocessed columns by id (for id-keyed
/// global preprocessed-trace generators).
pub fn gamma_tall_preprocessed_column(
    layout: &GammaTallLayout,
    id: &PreProcessedColumnId,
) -> Option<M31ColumnEval> {
    let ids = gamma_tall_preprocessed_ids(layout.tag);
    let index = ids.iter().position(|candidate| candidate == id)?;
    Some(gen_gamma_tall_preprocessed_trace(layout).swap_remove(index))
}

pub type GammaTallComponent = FrameworkComponent<GammaTallEval>;

/// The tall expander AIR. Interaction layout: 4 accumulator coordinate
/// columns FIRST (read with `[-1, 0]` masks), then the batched logup columns.
#[derive(Clone)]
pub struct GammaTallEval {
    pub layout: GammaTallLayout,
    pub challenge: GammaChallenge,
    pub digest: GammaDigestRelation,
    pub range: RangeCheckRelation,
}

impl FrameworkEval for GammaTallEval {
    fn log_size(&self) -> u32 {
        self.layout.log_size()
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.layout.log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let tag = self.layout.tag;
        let row_id = eval.get_preprocessed_column(gamma_tall_column_id(tag, "row_id"));
        let start = eval.get_preprocessed_column(gamma_tall_column_id(tag, "start"));
        let end = eval.get_preprocessed_column(gamma_tall_column_id(tag, "end"));
        let in_group = eval.get_preprocessed_column(gamma_tall_column_id(tag, "in_group"));
        let values: [E::F; GAMMA_DIGEST_LANES] = array::from_fn(|_| eval.next_trace_mask());

        // Accumulator coordinates, previous and current row.
        let coords: [[E::F; 2]; SECURE_EXTENSION_DEGREE] =
            array::from_fn(|_| eval.next_interaction_mask(INTERACTION_TRACE_IDX, [-1, 0]));
        let acc_prev = E::combine_ef(coords.each_ref().map(|pair| pair[0].clone()));
        let acc = E::combine_ef(coords.each_ref().map(|pair| pair[1].clone()));

        // C1: acc = (1 − start)·acc_prev·γ^K + Σ_j v_j·γ^(K−1−j). Ungated:
        // padding rows keep multiplying the chain by γ^K (the gen does the
        // same), and the coset-row-0 wrap is killed by start = 1. Degree 2.
        let one = E::F::from(M31::from_u32_unchecked(1));
        let gamma_k = E::EF::from(self.challenge.power(GAMMA_DIGEST_LANES));
        let mut expected = E::EF::from(one - start) * acc_prev * gamma_k;
        for (j, value) in values.iter().enumerate() {
            expected = expected
                + E::EF::from(self.challenge.power(GAMMA_DIGEST_LANES - 1 - j)) * value.clone();
        }
        eval.add_constraint(acc - expected);

        // K range uses: every scheduled lane value is consumed exactly once
        // (the numerator is preprocessed — no witness gate can skip a check).
        for value in &values {
            eval.add_to_relation(RelationEntry::new(
                &self.range,
                E::EF::from(in_group.clone()),
                &[value.clone()],
            ));
        }
        // Digest use at the group end: acc must equal the wide row's digest.
        let mut tuple = Vec::with_capacity(GAMMA_DIGEST_RELATION_ARITY);
        tuple.push(E::F::from(M31::from_u32_unchecked(tag)));
        tuple.push(row_id);
        tuple.extend(coords.iter().map(|pair| pair[1].clone()));
        eval.add_to_relation(RelationEntry::new(&self.digest, E::EF::from(end), &tuple));

        eval.finalize_logup_batched(&consecutive_batching(GAMMA_DIGEST_LANES + 1, 2));
        eval
    }
}

/// Interaction claim of one tall instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GammaTallInteractionClaim {
    /// The component's logup claimed sum (range uses + digest uses).
    pub claimed_sum: SecureField,
    /// The digest-use part (balances against the wide rows' yields).
    pub digest_use_sum: SecureField,
    /// The range-use part (balances against the kind's range provider).
    pub range_use_sum: SecureField,
}

impl GammaTallInteractionClaim {
    pub fn zero() -> Self {
        let zero = SecureField::from(M31::from_u32_unchecked(0));
        Self {
            claimed_sum: zero,
            digest_use_sum: zero,
            range_use_sum: zero,
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum, self.digest_use_sum, self.range_use_sum]);
    }
}

/// Interaction trace: 4 accumulator coordinate columns, then the batched
/// logup columns, in the exact order [`GammaTallEval::evaluate`] reads them.
pub fn gen_gamma_tall_interaction_trace(
    instance: &GammaTallInstance,
    challenge: &GammaChallenge,
    digest_relation: &GammaDigestRelation,
    range_relation: &RangeCheckRelation,
) -> (Vec<M31ColumnEval>, GammaTallInteractionClaim) {
    let layout = &instance.layout;
    let log_size = layout.log_size();
    let rows = 1usize << log_size;
    let g = layout.rows_per_group();
    let zero = SecureField::from(M31::from_u32_unchecked(0));
    let one = SecureField::from(M31::from_u32_unchecked(1));

    // Accumulator chain in coset order (padding rows keep multiplying by γ^K,
    // matching the ungated C1).
    let gamma_k = challenge.power(GAMMA_DIGEST_LANES);
    let mut acc = vec![zero; rows];
    for row in 0..rows {
        let prev = if row % g == 0 && row < layout.active_rows() {
            zero // group start: (1 − start) kills the chain term
        } else if row == 0 {
            zero
        } else {
            acc[row - 1]
        };
        let mut value = prev * gamma_k;
        for lane in 0..GAMMA_DIGEST_LANES {
            value += challenge.power(GAMMA_DIGEST_LANES - 1 - lane)
                * SecureField::from(instance.lane_value(row, lane));
        }
        acc[row] = value;
    }
    let mut trace: Vec<M31ColumnEval> = (0..SECURE_EXTENSION_DEGREE)
        .map(|coord| {
            m31_column_eval(
                log_size,
                acc.iter().map(|value| value.to_m31_array()[coord]).collect(),
            )
        })
        .collect();

    // Logup entries (eval order: K range uses, then the digest use), packed
    // over the circle-domain row layout.
    let vec_rows = 1usize << (log_size - LOG_N_LANES);
    let mut entries: Vec<(Vec<PackedQM31>, Vec<PackedQM31>)> = Vec::new();
    let mut digest_use_sum = zero;
    let mut range_use_sum = zero;
    // Map circle-domain (bit-reversed) rows back to coset indices.
    let mut row_lookup = vec![0usize; rows];
    for coset in 0..rows {
        let domain_row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset, log_size),
            log_size,
        );
        row_lookup[domain_row] = coset;
    }
    for lane in 0..GAMMA_DIGEST_LANES {
        let mut numerators = Vec::with_capacity(vec_rows);
        let mut denominators = Vec::with_capacity(vec_rows);
        for vec_row in 0..vec_rows {
            let mut numerator = [zero; N_LANES];
            let mut denominator = [one; N_LANES];
            for simd_lane in 0..N_LANES {
                let coset = row_lookup[vec_row * N_LANES + simd_lane];
                let value = instance.lane_value(coset, lane);
                let in_group = coset < layout.active_rows();
                let denom: SecureField = range_relation.combine(&[value]);
                numerator[simd_lane] = if in_group { one } else { zero };
                denominator[simd_lane] = denom;
                if in_group {
                    range_use_sum += one / denom;
                }
            }
            numerators.push(PackedQM31::from_array(numerator));
            denominators.push(PackedQM31::from_array(denominator));
        }
        entries.push((numerators, denominators));
    }
    {
        let mut numerators = Vec::with_capacity(vec_rows);
        let mut denominators = Vec::with_capacity(vec_rows);
        for vec_row in 0..vec_rows {
            let mut numerator = [zero; N_LANES];
            let mut denominator = [one; N_LANES];
            for simd_lane in 0..N_LANES {
                let coset = row_lookup[vec_row * N_LANES + simd_lane];
                let is_end = coset < layout.active_rows() && coset % g == g - 1;
                let row_id = M31::from_u32_unchecked((coset / g) as u32);
                let digest_coords = acc[coset].to_m31_array();
                let tuple = [
                    M31::from_u32_unchecked(layout.tag),
                    row_id,
                    digest_coords[0],
                    digest_coords[1],
                    digest_coords[2],
                    digest_coords[3],
                ];
                let denom: SecureField = digest_relation.combine(&tuple);
                numerator[simd_lane] = if is_end { one } else { zero };
                denominator[simd_lane] = denom;
                if is_end {
                    digest_use_sum += one / denom;
                }
            }
            numerators.push(PackedQM31::from_array(numerator));
            denominators.push(PackedQM31::from_array(denominator));
        }
        entries.push((numerators, denominators));
    }

    let mut logup = LogupTraceGenerator::new(log_size);
    write_batched_logup_columns(&mut logup, &entries, 2);
    let (logup_trace, claimed_sum) = logup.finalize_last();
    trace.extend(logup_trace);

    (
        trace,
        GammaTallInteractionClaim {
            claimed_sum,
            digest_use_sum,
            range_use_sum,
        },
    )
}

/// Gen-side yield sum of the wide rows feeding one tall instance: the exact
/// counterpart of [`GammaTallInteractionClaim::digest_use_sum`]. Adopting
/// components fold these fractions into their own logup; this helper computes
/// the analytic sum for balance accounting and tests.
pub fn gamma_digest_yield_sum(
    instance: &GammaTallInstance,
    challenge: &GammaChallenge,
    digest_relation: &GammaDigestRelation,
) -> SecureField {
    let mut sum = SecureField::from(M31::from_u32_unchecked(0));
    for group in 0..instance.layout.group_count {
        // `padded_group_values` is already lane-padded, so no further padding
        // happens inside the digest (`P − L = 0` ⇒ pad term vanishes).
        let digest = gamma_digest_of_values(
            challenge,
            instance.pad_value,
            &instance.padded_group_values(group),
        );
        let tuple = gamma_digest_tuple(
            instance.layout.tag,
            M31::from_u32_unchecked(group as u32),
            digest,
        );
        let denom: SecureField = digest_relation.combine(&tuple);
        sum -= SecureField::from(M31::from_u32_unchecked(1)) / denom;
    }
    sum
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use std::ops::Deref;
    use stwo::core::channel::Blake2sChannel;
    use stwo_constraint_framework::{
        assert_constraints_on_trace, TraceLocationAllocator, PREPROCESSED_TRACE_IDX,
    };

    use super::*;
    use crate::debug::MockCommitmentScheme;

    fn m31(value: u32) -> M31 {
        M31::from_u32_unchecked(value)
    }

    fn test_instance(tag: u32) -> GammaTallInstance {
        // 3 groups of 11 values (K=8 -> 2 rows/group, 5 padding lanes), with a
        // nonzero pad value to exercise the constant tail term.
        let group_values = (0..3u32)
            .map(|g| (0..11u32).map(|i| m31((g * 977 + 13 * i + 7) % 8192)).collect())
            .collect();
        GammaTallInstance::new(tag, 11, m31(3), group_values)
    }

    fn test_challenge() -> GammaChallenge {
        GammaChallenge::from_gamma(
            SecureField::from_m31_array(core::array::from_fn(|i| m31(23 + 31 * i as u32))),
            gamma_padded_values(11),
        )
    }

    fn draw_relations() -> (GammaDigestRelation, RangeCheckRelation) {
        let mut channel = Blake2sChannel::default();
        (
            GammaDigestRelation::draw(&mut channel),
            RangeCheckRelation::draw(&mut channel),
        )
    }

    /// The wide-side coordinate trick: each digest coordinate is an M31-linear
    /// combination of the values (QM31 · M31 is coordinate-wise), so the
    /// eval-side degree-1 expressions reproduce the gen-side digest exactly.
    #[test]
    fn gamma_digest_coordinates_are_m31_linear() {
        let challenge = test_challenge();
        let values: Vec<M31> = (0..11u32).map(|i| m31(1 + 591 * i)).collect();
        let pad = m31(3);
        let digest = gamma_digest_of_values(&challenge, pad, &values);
        let padded = gamma_padded_values(values.len());
        let pad_coords =
            (pad_tail_sum(&challenge, values.len()) * SecureField::from(pad)).to_m31_array();
        let mut coords = pad_coords;
        for (i, value) in values.iter().enumerate() {
            let power = challenge.power(padded - 1 - i).to_m31_array();
            for (coord, power_coord) in coords.iter_mut().zip(power) {
                *coord += power_coord * *value;
            }
        }
        assert_eq!(digest.to_m31_array(), coords);
    }

    /// Honest tall trace satisfies all constraints (pins the `[-1]` mask
    /// direction and the coset-order accumulator layout) and its digest uses
    /// balance the wide-side yields exactly.
    #[test]
    fn gamma_tall_honest_constraints_and_balance() {
        let tag = 42;
        let instance = test_instance(tag);
        let challenge = test_challenge();
        let (digest_relation, range_relation) = draw_relations();

        let preprocessed = gen_gamma_tall_preprocessed_trace(&instance.layout);
        let base = gen_gamma_tall_base_trace(&instance);
        let (interaction, interaction_claim) = gen_gamma_tall_interaction_trace(
            &instance,
            &challenge,
            &digest_relation,
            &range_relation,
        );

        // Wide-side yields cancel the tall digest uses.
        let yields = gamma_digest_yield_sum(&instance, &challenge, &digest_relation);
        assert_eq!(interaction_claim.digest_use_sum + yields, SecureField::from(m31(0)));
        // The component total splits exactly into its two parts.
        assert_eq!(
            interaction_claim.claimed_sum,
            interaction_claim.digest_use_sum + interaction_claim.range_use_sum
        );

        let mut commitment_scheme = MockCommitmentScheme::default();
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(preprocessed);
        tree_builder.finalize_interaction();
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(base);
        tree_builder.finalize_interaction();
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(interaction);
        tree_builder.finalize_interaction();

        let mut allocator =
            TraceLocationAllocator::new_with_preprocessed_columns(&gamma_tall_preprocessed_ids(tag));
        let component = GammaTallComponent::new(
            &mut allocator,
            GammaTallEval {
                layout: instance.layout,
                challenge,
                digest: digest_relation,
                range: range_relation,
            },
            interaction_claim.claimed_sum,
        );

        let trace = commitment_scheme.trace_domain_evaluations();
        let mut component_trace = trace
            .sub_tree(component.trace_locations())
            .map(|tree| tree.into_iter().cloned().collect_vec());
        component_trace[PREPROCESSED_TRACE_IDX] = component
            .preprocessed_column_indices()
            .iter()
            .map(|index| trace[PREPROCESSED_TRACE_IDX][*index])
            .collect();
        let component_eval = component.deref();
        assert_constraints_on_trace(
            &component_trace,
            instance.layout.log_size(),
            |eval| {
                let _ = component_eval.evaluate(eval);
            },
            component.claimed_sum(),
        );
    }

    /// Flipping one digested value (tall side regenerated, wide yields kept
    /// honest) breaks the GammaDigest balance: the binding the gadget exists
    /// for.
    #[test]
    fn gamma_tall_value_flip_breaks_digest_balance() {
        let tag = 42;
        let honest = test_instance(tag);
        let challenge = test_challenge();
        let (digest_relation, range_relation) = draw_relations();
        let honest_yields = gamma_digest_yield_sum(&honest, &challenge, &digest_relation);

        let mut forged = honest.clone();
        forged.group_values[1][4] = m31(forged.group_values[1][4].0 ^ 1);
        let (_, forged_claim) = gen_gamma_tall_interaction_trace(
            &forged,
            &challenge,
            &digest_relation,
            &range_relation,
        );
        assert_ne!(
            forged_claim.digest_use_sum + honest_yields,
            SecureField::from(m31(0)),
            "a flipped tall value must unbalance the digest relation"
        );
    }

    /// Swapping two groups' digests on the yield side (replay across rows of
    /// the same tag) is caught by the `row_index` tuple field.
    #[test]
    fn gamma_tall_row_swap_breaks_digest_balance() {
        let tag = 42;
        let instance = test_instance(tag);
        let challenge = test_challenge();
        let (digest_relation, range_relation) = draw_relations();
        let (_, claim) = gen_gamma_tall_interaction_trace(
            &instance,
            &challenge,
            &digest_relation,
            &range_relation,
        );

        // Forge yields with row indices 0 and 1 swapped.
        let mut swapped = SecureField::from(m31(0));
        for group in 0..instance.layout.group_count {
            let digest = gamma_digest_of_values(
                &challenge,
                instance.pad_value,
                &instance.padded_group_values(group),
            );
            let row_index = match group {
                0 => 1u32,
                1 => 0u32,
                other => other as u32,
            };
            let tuple = gamma_digest_tuple(tag, m31(row_index), digest);
            let denom: SecureField = digest_relation.combine(&tuple);
            swapped -= SecureField::from(m31(1)) / denom;
        }
        assert_ne!(
            claim.digest_use_sum + swapped,
            SecureField::from(m31(0)),
            "digest replay across row indices must unbalance the relation"
        );
    }

    /// A different tag with identical values must not cancel (no cross-
    /// component replay).
    #[test]
    fn gamma_tall_tag_mismatch_breaks_digest_balance() {
        let instance_a = test_instance(7);
        let instance_b = test_instance(8);
        let challenge = test_challenge();
        let (digest_relation, range_relation) = draw_relations();
        let (_, claim_a) = gen_gamma_tall_interaction_trace(
            &instance_a,
            &challenge,
            &digest_relation,
            &range_relation,
        );
        let yields_b = gamma_digest_yield_sum(&instance_b, &challenge, &digest_relation);
        assert_ne!(claim_a.digest_use_sum + yields_b, SecureField::from(m31(0)));
    }
}
