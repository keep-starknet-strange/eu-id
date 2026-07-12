//! In-circuit binding of MSO / item preimage byte windows (Phase D).
//!
//! A single multi-window LogUp component that consumes byte windows exposed by
//! the SHA modules (via [`air_core::relations::SharedFieldRelation`]) and binds
//! each to a constant or an attribute digest target:
//!
//! - **Constant** — the window bytes must equal a public constant (D1 element
//!   identifier pins, D3 device-key coordinates equal to the coprocessor's
//!   proven device public key bytes).
//! - **Digest(i)** — a 32-byte `valueDigests` window in the issuer MSO preimage
//!   must byte-equal the selected item SHA module's digest, via a
//!   shared [`air_core::relations::SharedDigestRelation`] (D2 digest membership).
//!
//! Implementing all five bind surfaces as one sized-once component (rather than
//! five log-4 dust components) follows the Phase D perf rule.

use air_core::relations::{FieldBytesRelation, SharedFieldRelation};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use rand_core::{OsRng, RngCore};
use serde::{Deserialize, Serialize};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{QM31, SECURE_EXTENSION_DEGREE};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::utils::{bit_reverse_index, coset_index_to_circle_domain_index};
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    TraceLocationAllocator,
};

use crate::claimed_sum_blinder::{
    add_blinder_relation_entry, blinder_counter_interaction, blinder_denominator, random_qm31,
    ClaimedSumBlinderEval, ClaimedSumBlinderRelation,
};

pub(crate) const MDOC_MAX_DISCLOSED_ATTRIBUTES: usize = 4;

/// One bind surface; each window is one row. The next SIMD-sized domain fits
/// four attributes plus the MSO anchor rows.
const MDOC_WINDOW_BIND_LOG_SIZE: u32 = 9;
/// Byte-value witness columns (max window length is a 32-byte digest / coord).
const MDOC_WINDOW_BIND_TRACE_COLS: usize = 32;
/// `active`, `field_id`, four attribute source selectors, 32 `byte_active`,
/// and 32 `expected` byte columns.
const MDOC_WINDOW_BIND_PREPROCESSED_COLS: usize = 70;
const ATTR_FIELD_ACTIVE_START: usize = 2;
const BYTE_ACTIVE_START: usize = ATTR_FIELD_ACTIVE_START + MDOC_MAX_DISCLOSED_ATTRIBUTES;
const EXPECTED_START: usize = BYTE_ACTIVE_START + 32;

type MdocWindowColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type MdocWindowBindComponent = FrameworkComponent<MdocWindowBindEval>;

/// A public constant bound to a byte window in one private attribute item.
#[derive(Clone, Debug)]
pub(crate) struct MdocWindowBindRow {
    field_id: u32,
    attribute_index: usize,
    len: usize,
    expected: [u8; 32],
    witness: [u8; 32],
}

impl MdocWindowBindRow {
    pub(crate) fn constant(field_id: u32, attribute_index: usize, bytes: &[u8]) -> Self {
        assert!(attribute_index < MDOC_MAX_DISCLOSED_ATTRIBUTES);
        let mut expected = [0u8; 32];
        expected[..bytes.len()].copy_from_slice(bytes);
        Self {
            field_id,
            attribute_index,
            len: bytes.len(),
            expected,
            witness: expected,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct MdocWindowBindInteractionClaim {
    pub(crate) claimed_sum: QM31,
    /// Q-015 §4b blinder pair (see `claimed_sum_blinder`).
    pub(crate) blinder_v: QM31,
    pub(crate) blinder_m: QM31,
    pub(crate) blinder_claimed_sum: QM31,
}

pub(crate) struct MdocWindowBind {
    rows: Vec<MdocWindowBindRow>,
    attribute_field_handles: Vec<SharedFieldRelation>,
    blinder_relation: Option<ClaimedSumBlinderRelation>,
    interaction_claim: Option<MdocWindowBindInteractionClaim>,
    component: Option<MdocWindowBindComponent>,
    blinder_component: Option<FrameworkComponent<ClaimedSumBlinderEval>>,
}

impl MdocWindowBind {
    pub(crate) fn new_for_attributes(
        rows: Vec<MdocWindowBindRow>,
        attribute_field_handles: Vec<SharedFieldRelation>,
    ) -> Self {
        assert!(attribute_field_handles.len() <= MDOC_MAX_DISCLOSED_ATTRIBUTES);
        assert_rows_match_handles(&rows, attribute_field_handles.len());
        Self {
            rows,
            attribute_field_handles,
            blinder_relation: None,
            interaction_claim: None,
            component: None,
            blinder_component: None,
        }
    }

    pub(crate) fn verifier_for_attributes(
        rows: Vec<MdocWindowBindRow>,
        attribute_field_handles: Vec<SharedFieldRelation>,
        interaction_claim: MdocWindowBindInteractionClaim,
    ) -> Self {
        assert!(attribute_field_handles.len() <= MDOC_MAX_DISCLOSED_ATTRIBUTES);
        assert_rows_match_handles(&rows, attribute_field_handles.len());
        Self {
            rows,
            attribute_field_handles,
            blinder_relation: None,
            interaction_claim: Some(interaction_claim),
            component: None,
            blinder_component: None,
        }
    }

    pub(crate) fn interaction_claim(&self) -> &MdocWindowBindInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("mdoc window bind interaction claim is set")
    }

    fn attribute_field_relations(&self) -> Vec<FieldBytesRelation> {
        self.attribute_field_handles
            .iter()
            .map(SharedFieldRelation::get)
            .collect()
    }

    fn n_lookups(&self) -> usize {
        32 * self.attribute_field_handles.len() + 1
    }
}

/// Fail-closed shape check: a row may only reference a source/target whose
/// relation handle exists in this composition (otherwise its LogUp site would
/// silently not be emitted and the balance argument would be vacuous).
fn assert_rows_match_handles(rows: &[MdocWindowBindRow], n_attributes: usize) {
    for row in rows {
        assert!(row.attribute_index < n_attributes);
    }
}

#[derive(Clone)]
struct MdocWindowBindEval {
    attribute_field_relations: Vec<FieldBytesRelation>,
    blinder_relation: ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
}

fn m31_const<E: EvalAtRow>(value: u32) -> E::F {
    E::F::from(M31::from_u32_unchecked(value))
}

fn coset_order_to_circle_domain_order(log_size: u32, values: Vec<M31>) -> Vec<M31> {
    let mut ordered = vec![M31::from_u32_unchecked(0); 1usize << log_size];
    for (coset_index, value) in values.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        );
        ordered[row] = value;
    }
    ordered
}

fn mdoc_window_column_eval(log_size: u32, coset_values: Vec<M31>) -> MdocWindowColumnEval {
    CircleEvaluation::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(coset_order_to_circle_domain_order(log_size, coset_values)),
    )
}

fn mdoc_window_bind_col_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mdoc/window_bind/{name}"),
    }
}

fn mdoc_window_bind_preprocessed_column_ids() -> Vec<PreProcessedColumnId> {
    let mut ids = vec![
        mdoc_window_bind_col_id("active"),
        mdoc_window_bind_col_id("field_id"),
    ];
    ids.extend(
        (0..MDOC_MAX_DISCLOSED_ATTRIBUTES)
            .map(|i| mdoc_window_bind_col_id(&format!("attr_field_active_{i}"))),
    );
    ids.extend((0..32).map(|i| mdoc_window_bind_col_id(&format!("byte_active_{i}"))));
    ids.extend((0..32).map(|i| mdoc_window_bind_col_id(&format!("expected_{i}"))));
    ids
}

fn mdoc_window_bind_preprocessed_columns(rows: &[MdocWindowBindRow]) -> Vec<MdocWindowColumnEval> {
    let mut columns = vec![
        vec![M31::from_u32_unchecked(0); 1 << MDOC_WINDOW_BIND_LOG_SIZE];
        MDOC_WINDOW_BIND_PREPROCESSED_COLS
    ];
    for (row_idx, row) in rows.iter().enumerate() {
        columns[0][row_idx] = M31::from_u32_unchecked(1);
        columns[1][row_idx] = M31::from_u32_unchecked(row.field_id);
        for i in 0..32 {
            if i < row.len {
                columns[BYTE_ACTIVE_START + i][row_idx] = M31::from_u32_unchecked(1);
            }
            columns[EXPECTED_START + i][row_idx] =
                M31::from_u32_unchecked(u32::from(row.expected[i]));
        }
        let source_col = ATTR_FIELD_ACTIVE_START + row.attribute_index;
        columns[source_col][row_idx] = M31::from_u32_unchecked(1);
    }
    columns
        .into_iter()
        .map(|values| mdoc_window_column_eval(MDOC_WINDOW_BIND_LOG_SIZE, values))
        .collect()
}

fn mdoc_window_bind_base_trace(rows: &[MdocWindowBindRow]) -> Vec<MdocWindowColumnEval> {
    (0..32)
        .map(|byte_idx| {
            let mut values = vec![M31::from_u32_unchecked(0); 1 << MDOC_WINDOW_BIND_LOG_SIZE];
            for value in &mut values {
                *value = random_m31_cell();
            }
            for (row_idx, row) in rows.iter().enumerate() {
                if byte_idx < row.len {
                    values[row_idx] = M31::from_u32_unchecked(u32::from(row.witness[byte_idx]));
                }
            }
            mdoc_window_column_eval(MDOC_WINDOW_BIND_LOG_SIZE, values)
        })
        .collect()
}

fn mdoc_window_bind_interaction_trace(
    rows: &[MdocWindowBindRow],
    attribute_field_relations: &[FieldBytesRelation],
    blinder_relation: &ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
) -> (Vec<MdocWindowColumnEval>, QM31) {
    let preprocessed = mdoc_window_bind_preprocessed_columns(rows);
    let trace = mdoc_window_bind_base_trace(rows);
    let n_vec_rows = 1usize << (MDOC_WINDOW_BIND_LOG_SIZE - LOG_N_LANES);
    let mut sites: Vec<Vec<(PackedQM31, PackedQM31)>> =
        Vec::with_capacity(32 * attribute_field_relations.len());
    for byte_idx in 0..32 {
        let source_relations = attribute_field_relations
            .iter()
            .enumerate()
            .map(|(i, relation)| (ATTR_FIELD_ACTIVE_START + i, relation));
        for (source_col, relation) in source_relations {
            sites.push(
                (0..n_vec_rows)
                    .map(|vec_row| {
                        let numerator = PackedQM31::from(
                            preprocessed[BYTE_ACTIVE_START + byte_idx].data[vec_row]
                                * preprocessed[source_col].data[vec_row],
                        );
                        let denominator = relation.combine(&[
                            preprocessed[1].data[vec_row],
                            PackedM31::broadcast(M31::from_u32_unchecked(byte_idx as u32)),
                            trace[byte_idx].data[vec_row],
                        ]);
                        (numerator, denominator)
                    })
                    .collect(),
            );
        }
    }
    // Q-015 blinder `+m/(z−combine(v))` on every row, emitted LAST to match
    // `MdocWindowBindEval::evaluate`.
    let blinder_num = PackedQM31::broadcast(blinder_m);
    let blinder_den = blinder_denominator(blinder_relation, blinder_v);
    sites.push(vec![(blinder_num, blinder_den); n_vec_rows]);
    let mut logup = LogupTraceGenerator::new(MDOC_WINDOW_BIND_LOG_SIZE);
    let mut site_idx = 0usize;
    while site_idx + 1 < sites.len() {
        let left = &sites[site_idx];
        let right = &sites[site_idx + 1];
        logup.col_from_iter((0..n_vec_rows).map(|vec_row| {
            let (n0, d0) = left[vec_row];
            let (n1, d1) = right[vec_row];
            (n0 * d1 + n1 * d0, d0 * d1)
        }));
        site_idx += 2;
    }
    if site_idx < sites.len() {
        let last = &sites[site_idx];
        logup.col_from_iter((0..n_vec_rows).map(|vec_row| last[vec_row]));
    }
    logup.finalize_last()
}

impl FrameworkEval for MdocWindowBindEval {
    fn log_size(&self) -> u32 {
        MDOC_WINDOW_BIND_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        MDOC_WINDOW_BIND_LOG_SIZE + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(mdoc_window_bind_col_id("active"));
        let field_id = eval.get_preprocessed_column(mdoc_window_bind_col_id("field_id"));
        let attr_field_active: Vec<E::F> = (0..MDOC_MAX_DISCLOSED_ATTRIBUTES)
            .map(|i| {
                eval.get_preprocessed_column(mdoc_window_bind_col_id(&format!(
                    "attr_field_active_{i}"
                )))
            })
            .collect();
        let one = m31_const::<E>(1);
        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        for attr_field_active in &attr_field_active {
            eval.add_constraint(
                attr_field_active.clone() * (attr_field_active.clone() - one.clone()),
            );
        }
        let attr_field_active_sum = attr_field_active
            .iter()
            .cloned()
            .fold(m31_const::<E>(0), |acc, value| acc + value);
        eval.add_constraint(active.clone() * (attr_field_active_sum - one.clone()));

        for byte_idx in 0..32 {
            let byte_active = eval.get_preprocessed_column(mdoc_window_bind_col_id(&format!(
                "byte_active_{byte_idx}"
            )));
            let expected = eval
                .get_preprocessed_column(mdoc_window_bind_col_id(&format!("expected_{byte_idx}")));
            let value = eval.next_trace_mask();
            eval.add_constraint(byte_active.clone() * (byte_active.clone() - one.clone()));
            eval.add_constraint(active.clone() * byte_active.clone() * (value.clone() - expected));
            for (source_active, relation) in attr_field_active
                .iter()
                .cloned()
                .zip(self.attribute_field_relations.iter())
            {
                eval.add_to_relation(RelationEntry::new(
                    relation,
                    E::EF::from(byte_active.clone() * source_active),
                    &[
                        field_id.clone(),
                        m31_const::<E>(byte_idx as u32),
                        value.clone(),
                    ],
                ));
            }
        }
        // Q-015 blinder `+m/(z−combine(v))`, ungated, emitted LAST to match
        // the generator's site order.
        add_blinder_relation_entry(
            &mut eval,
            &self.blinder_relation,
            self.blinder_v,
            self.blinder_m,
            false,
        );
        eval.finalize_logup_in_pairs();
        eval
    }
}

impl Air for MdocWindowBind {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        for row in &self.rows {
            channel.mix_u64(u64::from(row.field_id));
            channel.mix_u64(row.attribute_index as u64);
            channel.mix_u64(row.len as u64);
            for &byte in &row.expected[..row.len] {
                channel.mix_u64(u64::from(byte));
            }
        }
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.blinder_relation = Some(ClaimedSumBlinderRelation::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![MDOC_WINDOW_BIND_LOG_SIZE; MDOC_WINDOW_BIND_PREPROCESSED_COLS],
            trace: vec![MDOC_WINDOW_BIND_LOG_SIZE; MDOC_WINDOW_BIND_TRACE_COLS],
            // Main component columns plus one column for the Q-015 blinder
            // counterpart component.
            interaction: vec![
                MDOC_WINDOW_BIND_LOG_SIZE;
                (self.n_lookups().div_ceil(2) + 1) * SECURE_EXTENSION_DEGREE
            ],
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        let claim = self.interaction_claim();
        vec![claim.claimed_sum, claim.blinder_claimed_sum]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        mdoc_window_bind_preprocessed_column_ids()
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let claim = self.interaction_claim().clone();
        let blinder_relation = self
            .blinder_relation
            .clone()
            .expect("mdoc window bind blinder relation drawn before components");
        self.component = Some(MdocWindowBindComponent::new(
            allocator,
            MdocWindowBindEval {
                attribute_field_relations: self.attribute_field_relations(),
                blinder_relation: blinder_relation.clone(),
                blinder_v: claim.blinder_v,
                blinder_m: claim.blinder_m,
            },
            claim.claimed_sum,
        ));
        self.blinder_component = Some(FrameworkComponent::new(
            allocator,
            ClaimedSumBlinderEval {
                log_size: MDOC_WINDOW_BIND_LOG_SIZE,
                relation: blinder_relation,
                v: claim.blinder_v,
                m: claim.blinder_m,
            },
            claim.blinder_claimed_sum,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![
            self.component
                .as_ref()
                .expect("mdoc window bind component is built"),
            self.blinder_component
                .as_ref()
                .expect("mdoc window bind blinder component is built"),
        ]
    }
}

impl AirProver for MdocWindowBind {
    fn max_log_size(&self) -> u32 {
        MDOC_WINDOW_BIND_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        MDOC_WINDOW_BIND_LOG_SIZE + 1
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        self.write_selected_preprocessed(tb, &mdoc_window_bind_preprocessed_column_ids());
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc_window_bind::MdocWindowBind",
            &mdoc_window_bind_preprocessed_column_ids(),
            &mdoc_window_bind_preprocessed_columns(&self.rows),
        )
    }

    fn write_selected_preprocessed(
        &mut self,
        tb: &mut TreeBuilder<SimdBackend, air_core::Mc>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        let all_ids = mdoc_window_bind_preprocessed_column_ids();
        let all_columns = mdoc_window_bind_preprocessed_columns(&self.rows);
        let selected = selected_ids
            .iter()
            .map(|id| {
                all_ids
                    .iter()
                    .position(|candidate| candidate == id)
                    .map(|index| all_columns[index].clone())
                    .expect("unexpected mdoc window bind preprocessed selection")
            })
            .collect();
        tb.extend_evals(selected);
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(mdoc_window_bind_base_trace(&self.rows));
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let blinder_v = random_qm31();
        let blinder_m = random_qm31();
        let blinder_relation = self
            .blinder_relation
            .clone()
            .expect("mdoc window bind blinder relation drawn before interaction");
        let (trace, claimed_sum) = mdoc_window_bind_interaction_trace(
            &self.rows,
            &self.attribute_field_relations(),
            &blinder_relation,
            blinder_v,
            blinder_m,
        );
        tb.extend_evals(trace);
        let (blinder_trace, blinder_claimed_sum) = blinder_counter_interaction(
            MDOC_WINDOW_BIND_LOG_SIZE,
            &blinder_relation,
            blinder_v,
            blinder_m,
        );
        tb.extend_evals(blinder_trace);
        self.interaction_claim = Some(MdocWindowBindInteractionClaim {
            claimed_sum,
            blinder_v,
            blinder_m,
            blinder_claimed_sum,
        });
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            self.component
                .as_ref()
                .expect("mdoc window bind component is built"),
            self.blinder_component
                .as_ref()
                .expect("mdoc window bind blinder component is built"),
        ]
    }
}

fn random_m31_cell() -> M31 {
    loop {
        let value = OsRng.next_u32() & 0x7fff_ffff;
        if value < 2_147_483_647 {
            return M31::from_u32_unchecked(value);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::VecDeque;

    use stwo::prover::backend::simd::m31::N_LANES;
    use stwo_constraint_framework::{Multiplicity, PREPROCESSED_TRACE_IDX};

    #[derive(Default)]
    struct RowEval {
        preprocessed: VecDeque<Vec<M31>>,
        original: VecDeque<Vec<M31>>,
        constraints: Vec<QM31>,
    }

    impl RowEval {
        fn inactive_window_row() -> Self {
            let blind = M31::from_u32_unchecked(2);
            let zero = M31::from_u32_unchecked(0);
            let mut row = Self::default();

            for _ in 0..MDOC_WINDOW_BIND_PREPROCESSED_COLS {
                row.preprocessed.push_back(vec![zero]);
            }
            for _ in 0..MDOC_WINDOW_BIND_TRACE_COLS {
                row.original.push_back(vec![blind]);
            }

            row
        }

        fn nonzero_constraints(&self) -> Vec<(usize, QM31)> {
            self.constraints
                .iter()
                .copied()
                .enumerate()
                .filter(|(_, value)| *value != QM31::from_u32_unchecked(0, 0, 0, 0))
                .collect()
        }
    }

    impl EvalAtRow for RowEval {
        type F = M31;
        type EF = QM31;

        fn next_interaction_mask<const N: usize>(
            &mut self,
            interaction: usize,
            _offsets: [isize; N],
        ) -> [Self::F; N] {
            let queue = match interaction {
                PREPROCESSED_TRACE_IDX => &mut self.preprocessed,
                stwo_constraint_framework::ORIGINAL_TRACE_IDX => &mut self.original,
                _ => panic!("unexpected interaction index {interaction}"),
            };
            let values = queue
                .pop_front()
                .unwrap_or_else(|| panic!("missing mask for interaction {interaction}"));
            assert_eq!(values.len(), N, "mask arity mismatch");
            std::array::from_fn(|index| values[index])
        }

        fn add_constraint<G>(&mut self, constraint: G)
        where
            Self::EF: std::ops::Mul<G, Output = Self::EF> + From<G>,
        {
            self.constraints.push(QM31::from(constraint));
        }

        fn combine_ef(values: [Self::F; SECURE_EXTENSION_DEGREE]) -> Self::EF {
            QM31::from_m31_array(values)
        }

        fn add_to_relation<R: Relation<Self::F, Self::EF>>(
            &mut self,
            _entry: RelationEntry<'_, Self::F, Self::EF, R>,
        ) {
        }

        fn write_logup_frac_typed(
            &mut self,
            _numerator: Multiplicity<Self::F, Self::EF>,
            _denominator: Self::EF,
        ) {
        }

        fn finalize_logup_in_pairs(&mut self) {}
    }

    fn trace_fingerprint(trace: &[MdocWindowColumnEval]) -> Vec<[M31; N_LANES]> {
        trace
            .iter()
            .flat_map(|column| column.data.iter().map(|packed| packed.to_array()))
            .collect()
    }

    fn test_rows() -> Vec<MdocWindowBindRow> {
        vec![
            MdocWindowBindRow::constant(7, 0, b"abc"),
            MdocWindowBindRow::constant(8, 0, b"def"),
        ]
    }

    #[test]
    fn mdoc_window_bind_inactive_rows_are_not_zero_pinned() {
        let eval = MdocWindowBindEval {
            attribute_field_relations: Vec::new(),
            blinder_relation: ClaimedSumBlinderRelation::dummy(),
            blinder_v: QM31::from_u32_unchecked(1, 2, 3, 4),
            blinder_m: QM31::from_u32_unchecked(5, 6, 7, 8),
        };
        let row = eval.evaluate(RowEval::inactive_window_row());

        let nonzero = row.nonzero_constraints();
        assert!(
            nonzero.is_empty(),
            "inactive mdoc window row still hits constraints: {nonzero:?}"
        );
    }

    #[test]
    fn mdoc_window_bind_class_a_has_256_blind_rows_and_fresh_inactive_cells() {
        assert!(
            (1usize << MDOC_WINDOW_BIND_LOG_SIZE) - test_rows().len() >= 256,
            "mdoc window bind Class A needs at least 256 blind rows"
        );

        let rows = test_rows();
        let first = trace_fingerprint(&mdoc_window_bind_base_trace(&rows));
        let second = trace_fingerprint(&mdoc_window_bind_base_trace(&rows));
        let zero = [M31::from_u32_unchecked(0); N_LANES];

        assert!(
            first.iter().any(|value| *value != zero),
            "mdoc window inactive rows are still all zero"
        );
        assert_ne!(
            first, second,
            "mdoc window inactive cells must be fresh per trace"
        );
    }
}
