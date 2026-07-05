//! In-circuit binding and policy comparison for mdoc validity dates.
//!
//! The issuer SHA module exposes the `validFrom` and `validUntil` full-date
//! windows from the signed MSO preimage. This component consumes those bytes,
//! parses the `YYYY-MM-DD` text in-circuit, and proves:
//!
//! - `validFrom <= policy.current_date`
//! - `policy.current_date <= validUntil`

use air_core::relations::{field_id, FieldBytesRelation, SharedFieldRelation};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use predicates::Date;
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

const MDOC_VALIDITY_LOG_SIZE: u32 = LOG_N_LANES;
const DATE_TEXT_LEN: usize = 10;
const DATE_DIGITS: usize = 8;
const DIGIT_BITS: usize = 4;
const DATE_SLACK_BITS: usize = 23;
const MONTH_RANGE_BITS: usize = 4;
const DAY_RANGE_BITS: usize = 5;
const MDOC_VALIDITY_PREPROCESSED_COLS: usize = 4;
const MDOC_VALIDITY_TRACE_COLS: usize = DATE_TEXT_LEN
    + DATE_DIGITS * DIGIT_BITS
    + DATE_SLACK_BITS
    + 2 * MONTH_RANGE_BITS
    + 2 * DAY_RANGE_BITS;
const MDOC_VALIDITY_LOOKUPS: usize = DATE_TEXT_LEN;
const MDOC_VALIDITY_INTERACTION_COLS: usize =
    MDOC_VALIDITY_LOOKUPS.div_ceil(2) * SECURE_EXTENSION_DEGREE;

type MdocValidityColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type MdocValidityComponent = FrameworkComponent<MdocValidityEval>;

#[derive(Clone, Copy, Debug)]
pub(crate) struct MdocValidityRow {
    field_id: u32,
    valid_from: bool,
    bytes: [u8; DATE_TEXT_LEN],
}

impl MdocValidityRow {
    fn new(field_id: u32, valid_from: bool, bytes: [u8; DATE_TEXT_LEN]) -> Self {
        Self {
            field_id,
            valid_from,
            bytes,
        }
    }
}

pub(crate) fn mdoc_validity_rows(
    valid_from: [u8; DATE_TEXT_LEN],
    valid_until: [u8; DATE_TEXT_LEN],
) -> Vec<MdocValidityRow> {
    vec![
        MdocValidityRow::new(field_id::MDOC_VALID_FROM, true, valid_from),
        MdocValidityRow::new(field_id::MDOC_VALID_UNTIL, false, valid_until),
    ]
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct MdocValidityInteractionClaim {
    pub(crate) claimed_sum: QM31,
}

pub(crate) struct MdocValidityBind {
    policy_date: Date,
    rows: Vec<MdocValidityRow>,
    issuer_field_handle: SharedFieldRelation,
    interaction_claim: Option<MdocValidityInteractionClaim>,
    component: Option<MdocValidityComponent>,
}

impl MdocValidityBind {
    pub(crate) fn new(
        policy_date: Date,
        rows: Vec<MdocValidityRow>,
        issuer_field_handle: SharedFieldRelation,
    ) -> Self {
        Self {
            policy_date,
            rows,
            issuer_field_handle,
            interaction_claim: None,
            component: None,
        }
    }

    pub(crate) fn verifier(
        policy_date: Date,
        rows: Vec<MdocValidityRow>,
        issuer_field_handle: SharedFieldRelation,
        interaction_claim: MdocValidityInteractionClaim,
    ) -> Self {
        Self {
            policy_date,
            rows,
            issuer_field_handle,
            interaction_claim: Some(interaction_claim),
            component: None,
        }
    }

    pub(crate) fn interaction_claim(&self) -> &MdocValidityInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("mdoc validity interaction claim is set")
    }

    fn issuer_field_relation(&self) -> FieldBytesRelation {
        self.issuer_field_handle.get()
    }
}

#[derive(Clone)]
struct MdocValidityEval {
    policy_date: Date,
    issuer_field_relation: FieldBytesRelation,
}

fn m31_const<E: EvalAtRow>(value: u32) -> E::F {
    E::F::from(M31::from_u32_unchecked(value))
}

fn bit_sum<E: EvalAtRow>(bits: &[E::F]) -> E::F {
    bits.iter()
        .enumerate()
        .fold(m31_const::<E>(0), |acc, (bit_idx, bit)| {
            acc + m31_const::<E>(1u32 << bit_idx) * bit.clone()
        })
}

fn date_key(year: u32, month: u32, day: u32) -> u32 {
    year * 512 + month * 32 + day
}

fn policy_date_key(policy_date: Date) -> u32 {
    date_key(policy_date.year, policy_date.month, policy_date.day)
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

fn mdoc_validity_column_eval(log_size: u32, coset_values: Vec<M31>) -> MdocValidityColumnEval {
    CircleEvaluation::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(coset_order_to_circle_domain_order(log_size, coset_values)),
    )
}

fn mdoc_validity_col_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mdoc/validity/{name}"),
    }
}

fn mdoc_validity_preprocessed_column_ids() -> Vec<PreProcessedColumnId> {
    vec![
        mdoc_validity_col_id("active"),
        mdoc_validity_col_id("field_id"),
        mdoc_validity_col_id("valid_from_active"),
        mdoc_validity_col_id("valid_until_active"),
    ]
}

fn mdoc_validity_preprocessed_columns(rows: &[MdocValidityRow]) -> Vec<MdocValidityColumnEval> {
    let mut columns = vec![
        vec![M31::from_u32_unchecked(0); 1 << MDOC_VALIDITY_LOG_SIZE];
        MDOC_VALIDITY_PREPROCESSED_COLS
    ];
    for (row_idx, row) in rows.iter().enumerate() {
        columns[0][row_idx] = M31::from_u32_unchecked(1);
        columns[1][row_idx] = M31::from_u32_unchecked(row.field_id);
        if row.valid_from {
            columns[2][row_idx] = M31::from_u32_unchecked(1);
        } else {
            columns[3][row_idx] = M31::from_u32_unchecked(1);
        }
    }
    columns
        .into_iter()
        .map(|values| mdoc_validity_column_eval(MDOC_VALIDITY_LOG_SIZE, values))
        .collect()
}

fn bits_for(value: u32, bits: usize) -> Vec<u32> {
    (0..bits).map(|bit| (value >> bit) & 1).collect()
}

fn parse_date_text(bytes: &[u8; DATE_TEXT_LEN]) -> Option<(u32, u32, u32)> {
    if bytes[4] != b'-' || bytes[7] != b'-' {
        return None;
    }
    for &idx in &[0usize, 1, 2, 3, 5, 6, 8, 9] {
        if !bytes[idx].is_ascii_digit() {
            return None;
        }
    }
    let year = u32::from(bytes[0] - b'0') * 1000
        + u32::from(bytes[1] - b'0') * 100
        + u32::from(bytes[2] - b'0') * 10
        + u32::from(bytes[3] - b'0');
    let month = u32::from(bytes[5] - b'0') * 10 + u32::from(bytes[6] - b'0');
    let day = u32::from(bytes[8] - b'0') * 10 + u32::from(bytes[9] - b'0');
    Some((year, month, day))
}

fn row_slack(policy_key: u32, row: &MdocValidityRow) -> u32 {
    let Some((year, month, day)) = parse_date_text(&row.bytes) else {
        return 0;
    };
    let signed_key = date_key(year, month, day);
    if row.valid_from {
        policy_key.saturating_sub(signed_key)
    } else {
        signed_key.saturating_sub(policy_key)
    }
}

fn lower_range_slack(value: u32) -> u32 {
    value.saturating_sub(1)
}

fn upper_range_slack(max: u32, value: u32) -> u32 {
    max.saturating_sub(value)
}

fn mdoc_validity_base_trace(
    policy_date: Date,
    rows: &[MdocValidityRow],
) -> Vec<MdocValidityColumnEval> {
    let policy_key = policy_date_key(policy_date);
    let mut columns = vec![
        vec![M31::from_u32_unchecked(0); 1 << MDOC_VALIDITY_LOG_SIZE];
        MDOC_VALIDITY_TRACE_COLS
    ];
    for (row_idx, row) in rows.iter().enumerate() {
        let mut col_idx = 0usize;
        for byte in row.bytes {
            columns[col_idx][row_idx] = M31::from_u32_unchecked(u32::from(byte));
            col_idx += 1;
        }
        let digits = [
            row.bytes[0],
            row.bytes[1],
            row.bytes[2],
            row.bytes[3],
            row.bytes[5],
            row.bytes[6],
            row.bytes[8],
            row.bytes[9],
        ];
        for byte in digits {
            let digit = byte
                .checked_sub(b'0')
                .filter(|digit| *digit <= 9)
                .unwrap_or(0);
            for bit in bits_for(u32::from(digit), DIGIT_BITS) {
                columns[col_idx][row_idx] = M31::from_u32_unchecked(bit);
                col_idx += 1;
            }
        }
        for bit in bits_for(row_slack(policy_key, row), DATE_SLACK_BITS) {
            columns[col_idx][row_idx] = M31::from_u32_unchecked(bit);
            col_idx += 1;
        }
        let (_, month, day) = parse_date_text(&row.bytes).unwrap_or((0, 0, 0));
        for bit in bits_for(lower_range_slack(month), MONTH_RANGE_BITS) {
            columns[col_idx][row_idx] = M31::from_u32_unchecked(bit);
            col_idx += 1;
        }
        for bit in bits_for(upper_range_slack(12, month), MONTH_RANGE_BITS) {
            columns[col_idx][row_idx] = M31::from_u32_unchecked(bit);
            col_idx += 1;
        }
        for bit in bits_for(lower_range_slack(day), DAY_RANGE_BITS) {
            columns[col_idx][row_idx] = M31::from_u32_unchecked(bit);
            col_idx += 1;
        }
        for bit in bits_for(upper_range_slack(31, day), DAY_RANGE_BITS) {
            columns[col_idx][row_idx] = M31::from_u32_unchecked(bit);
            col_idx += 1;
        }
        debug_assert_eq!(col_idx, MDOC_VALIDITY_TRACE_COLS);
    }
    columns
        .into_iter()
        .map(|values| mdoc_validity_column_eval(MDOC_VALIDITY_LOG_SIZE, values))
        .collect()
}

fn mdoc_validity_interaction_trace(
    policy_date: Date,
    rows: &[MdocValidityRow],
    issuer_field_relation: &FieldBytesRelation,
) -> (Vec<MdocValidityColumnEval>, MdocValidityInteractionClaim) {
    let preprocessed = mdoc_validity_preprocessed_columns(rows);
    let trace = mdoc_validity_base_trace(policy_date, rows);
    let n_vec_rows = 1usize << (MDOC_VALIDITY_LOG_SIZE - LOG_N_LANES);
    let mut sites: Vec<Vec<(PackedQM31, PackedQM31)>> = Vec::with_capacity(MDOC_VALIDITY_LOOKUPS);
    for (byte_idx, trace_col) in trace.iter().enumerate().take(DATE_TEXT_LEN) {
        sites.push(
            (0..n_vec_rows)
                .map(|vec_row| {
                    let numerator = PackedQM31::from(preprocessed[0].data[vec_row]);
                    let denominator = issuer_field_relation.combine(&[
                        preprocessed[1].data[vec_row],
                        PackedM31::broadcast(M31::from_u32_unchecked(byte_idx as u32)),
                        trace_col.data[vec_row],
                    ]);
                    (numerator, denominator)
                })
                .collect(),
        );
    }
    let mut logup = LogupTraceGenerator::new(MDOC_VALIDITY_LOG_SIZE);
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
    let (trace, claimed_sum) = logup.finalize_last();
    (trace, MdocValidityInteractionClaim { claimed_sum })
}

impl FrameworkEval for MdocValidityEval {
    fn log_size(&self) -> u32 {
        MDOC_VALIDITY_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        MDOC_VALIDITY_LOG_SIZE + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(mdoc_validity_col_id("active"));
        let field_id = eval.get_preprocessed_column(mdoc_validity_col_id("field_id"));
        let valid_from_active =
            eval.get_preprocessed_column(mdoc_validity_col_id("valid_from_active"));
        let valid_until_active =
            eval.get_preprocessed_column(mdoc_validity_col_id("valid_until_active"));
        let one = m31_const::<E>(1);
        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint(valid_from_active.clone() * (valid_from_active.clone() - one.clone()));
        eval.add_constraint(
            valid_until_active.clone() * (valid_until_active.clone() - one.clone()),
        );
        eval.add_constraint(
            active.clone() * (valid_from_active.clone() + valid_until_active.clone() - one.clone()),
        );

        let bytes: [E::F; DATE_TEXT_LEN] = std::array::from_fn(|_| eval.next_trace_mask());
        let digit_bits: [[E::F; DIGIT_BITS]; DATE_DIGITS] =
            std::array::from_fn(|_| std::array::from_fn(|_| eval.next_trace_mask()));
        let slack_bits: [E::F; DATE_SLACK_BITS] = std::array::from_fn(|_| eval.next_trace_mask());
        let month_lower_bits: [E::F; MONTH_RANGE_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let month_upper_bits: [E::F; MONTH_RANGE_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let day_lower_bits: [E::F; DAY_RANGE_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let day_upper_bits: [E::F; DAY_RANGE_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());

        for value in bytes
            .iter()
            .chain(digit_bits.iter().flatten())
            .chain(slack_bits.iter())
            .chain(month_lower_bits.iter())
            .chain(month_upper_bits.iter())
            .chain(day_lower_bits.iter())
            .chain(day_upper_bits.iter())
        {
            eval.add_constraint((one.clone() - active.clone()) * value.clone());
        }

        eval.add_constraint(active.clone() * (bytes[4].clone() - m31_const::<E>(b'-' as u32)));
        eval.add_constraint(active.clone() * (bytes[7].clone() - m31_const::<E>(b'-' as u32)));

        let digit_positions = [0usize, 1, 2, 3, 5, 6, 8, 9];
        let mut digits = Vec::with_capacity(DATE_DIGITS);
        for (digit_idx, &byte_pos) in digit_positions.iter().enumerate() {
            let bits = &digit_bits[digit_idx];
            for bit in bits {
                eval.add_constraint(bit.clone() * (bit.clone() - one.clone()));
            }
            let digit = bytes[byte_pos].clone() - m31_const::<E>(b'0' as u32);
            let recomposed = bits[0].clone()
                + m31_const::<E>(2) * bits[1].clone()
                + m31_const::<E>(4) * bits[2].clone()
                + m31_const::<E>(8) * bits[3].clone();
            eval.add_constraint(active.clone() * (digit.clone() - recomposed));
            eval.add_constraint(bits[3].clone() * bits[2].clone());
            eval.add_constraint(bits[3].clone() * bits[1].clone());
            digits.push(digit);
        }

        for bit in slack_bits
            .iter()
            .chain(month_lower_bits.iter())
            .chain(month_upper_bits.iter())
            .chain(day_lower_bits.iter())
            .chain(day_upper_bits.iter())
        {
            eval.add_constraint(bit.clone() * (bit.clone() - one.clone()));
        }

        let year = m31_const::<E>(1000) * digits[0].clone()
            + m31_const::<E>(100) * digits[1].clone()
            + m31_const::<E>(10) * digits[2].clone()
            + digits[3].clone();
        let month = m31_const::<E>(10) * digits[4].clone() + digits[5].clone();
        let day = m31_const::<E>(10) * digits[6].clone() + digits[7].clone();
        let date_key =
            m31_const::<E>(512) * year + m31_const::<E>(32) * month.clone() + day.clone();
        let policy_key = m31_const::<E>(policy_date_key(self.policy_date));
        let compare_slack = bit_sum::<E>(&slack_bits);
        let month_lower = bit_sum::<E>(&month_lower_bits);
        let month_upper = bit_sum::<E>(&month_upper_bits);
        let day_lower = bit_sum::<E>(&day_lower_bits);
        let day_upper = bit_sum::<E>(&day_upper_bits);

        eval.add_constraint(active.clone() * (month.clone() - one.clone() - month_lower));
        eval.add_constraint(active.clone() * (m31_const::<E>(12) - month - month_upper));
        eval.add_constraint(active.clone() * (day.clone() - one.clone() - day_lower));
        eval.add_constraint(active.clone() * (m31_const::<E>(31) - day - day_upper));
        eval.add_constraint(
            valid_from_active * (policy_key.clone() - date_key.clone() - compare_slack.clone()),
        );
        eval.add_constraint(valid_until_active * (date_key - policy_key - compare_slack));

        for (byte_idx, value) in bytes.into_iter().enumerate() {
            eval.add_to_relation(RelationEntry::new(
                &self.issuer_field_relation,
                E::EF::from(active.clone()),
                &[field_id.clone(), m31_const::<E>(byte_idx as u32), value],
            ));
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

impl Air for MdocValidityBind {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(self.policy_date.year as u64);
        channel.mix_u64(self.policy_date.month as u64);
        channel.mix_u64(self.policy_date.day as u64);
        for row in &self.rows {
            channel.mix_u64(u64::from(row.field_id));
            channel.mix_u64(u64::from(!row.valid_from));
        }
    }

    fn draw_relations(&mut self, _channel: &mut Blake2sChannel) {}

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![MDOC_VALIDITY_LOG_SIZE; MDOC_VALIDITY_PREPROCESSED_COLS],
            trace: vec![MDOC_VALIDITY_LOG_SIZE; MDOC_VALIDITY_TRACE_COLS],
            interaction: vec![MDOC_VALIDITY_LOG_SIZE; MDOC_VALIDITY_INTERACTION_COLS],
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        vec![self.interaction_claim().claimed_sum]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        mdoc_validity_preprocessed_column_ids()
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.component = Some(MdocValidityComponent::new(
            allocator,
            MdocValidityEval {
                policy_date: self.policy_date,
                issuer_field_relation: self.issuer_field_relation(),
            },
            self.interaction_claim().claimed_sum,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![self
            .component
            .as_ref()
            .expect("mdoc validity component is built")]
    }
}

impl AirProver for MdocValidityBind {
    fn max_log_size(&self) -> u32 {
        MDOC_VALIDITY_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        MDOC_VALIDITY_LOG_SIZE + 1
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        self.write_selected_preprocessed(tb, &mdoc_validity_preprocessed_column_ids());
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc_validity::MdocValidityBind",
            &mdoc_validity_preprocessed_column_ids(),
            &mdoc_validity_preprocessed_columns(&self.rows),
        )
    }

    fn write_selected_preprocessed(
        &mut self,
        tb: &mut TreeBuilder<SimdBackend, air_core::Mc>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        let all_ids = mdoc_validity_preprocessed_column_ids();
        let all_columns = mdoc_validity_preprocessed_columns(&self.rows);
        let selected = selected_ids
            .iter()
            .map(|id| {
                all_ids
                    .iter()
                    .position(|candidate| candidate == id)
                    .map(|index| all_columns[index].clone())
                    .expect("unexpected mdoc validity preprocessed selection")
            })
            .collect();
        tb.extend_evals(selected);
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(mdoc_validity_base_trace(self.policy_date, &self.rows));
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let (trace, claim) = mdoc_validity_interaction_trace(
            self.policy_date,
            &self.rows,
            &self.issuer_field_relation(),
        );
        tb.extend_evals(trace);
        self.interaction_claim = Some(claim);
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![self
            .component
            .as_ref()
            .expect("mdoc validity component is built")]
    }
}
