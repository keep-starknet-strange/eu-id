//! Fixed country-code normalization table for private mdoc predicates.
//!
//! The single shared relation is
//! `(tag, num_hi, num_lo, upper0, upper1)`. Row 0 is the numeric branch's
//! dummy lookup; rows 1..=250 are the exact `celes` 2.8.2 country order,
//! including XK/383. The remaining rows are fixed inactive masks. Only the
//! inactive multiplicity cells are freshly randomized per proof.

use std::fmt;

use air_core::relations::SharedRelation;
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use rand::RngCore;
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{QM31, SECURE_EXTENSION_DEGREE};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::utils::{bit_reverse_index, coset_index_to_circle_domain_index};
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::PackedM31;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator,
};

pub(crate) const MDOC_COUNTRY_CODE_TABLE_LOG_SIZE: u32 = 9;
pub(crate) const MDOC_COUNTRY_CODE_TABLE_ROWS: usize = 1usize << MDOC_COUNTRY_CODE_TABLE_LOG_SIZE;
pub(crate) const MDOC_COUNTRY_CODE_COUNT: usize = 250;
pub(crate) const MDOC_COUNTRY_CODE_ACTIVE_ROWS: usize = MDOC_COUNTRY_CODE_COUNT + 1;
pub(crate) const MDOC_COUNTRY_CODE_TAG_NUMERIC: u32 = 0;
pub(crate) const MDOC_COUNTRY_CODE_TAG_ALPHA2: u32 = 1;
pub(crate) const MDOC_COUNTRY_CODE_TAG_INACTIVE: u32 = 2;
pub(crate) const MDOC_COUNTRY_CODE_RELATION_ARITY: usize = 5;
pub(crate) const MDOC_COUNTRY_CODE_PREPROCESSED_COLS: usize = 6;
pub(crate) const MDOC_COUNTRY_CODE_TRACE_COLS: usize = 1;
pub(crate) const MDOC_COUNTRY_CODE_INTERACTION_COLS: usize = SECURE_EXTENSION_DEGREE;

const MDOC_COUNTRY_CODE_TABLE_VERSION: u64 = 1;
const MDOC_COUNTRY_CODE_TABLE_DOMAIN: u64 = 0x4d44_4f43_434f_554e;
const MDOC_COUNTRY_CODE_MAX_MULTIPLICITY: u32 = 0x7fff_fffe;
const MDOC_COUNTRY_CODE_INACTIVE_SEED: u32 = 0x735c_e1e5;

relation!(MdocCountryCodeRelation, MDOC_COUNTRY_CODE_RELATION_ARITY);

pub(crate) type SharedMdocCountryCodeRelation = SharedRelation<MdocCountryCodeRelation>;
type MdocCountryCodeColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type MdocCountryCodeComponent = FrameworkComponent<MdocCountryCodeTableEval>;

/// Stable table digest used by the circuit-version resource tuple.
///
/// The value is over the semantic row-major six-column table, with each M31
/// cell encoded as a little-endian `u32`. The test below independently
/// recomputes it from `celes` 2.8.2.
pub(crate) const MDOC_COUNTRY_CODE_TABLE_SHA256: [u8; 32] = [
    107, 226, 233, 168, 42, 227, 63, 38, 252, 117, 225, 241, 167, 240, 215, 205, 8, 10, 92, 52, 30,
    123, 164, 206, 166, 65, 18, 57, 105, 138, 128, 7,
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct MdocCountryCodeTuple {
    pub(crate) tag: u32,
    pub(crate) num_hi: u32,
    pub(crate) num_lo: u32,
    pub(crate) upper0: u32,
    pub(crate) upper1: u32,
}

impl MdocCountryCodeTuple {
    pub(crate) const fn numeric_dummy() -> Self {
        Self {
            tag: MDOC_COUNTRY_CODE_TAG_NUMERIC,
            num_hi: 0,
            num_lo: 0,
            upper0: 0,
            upper1: 0,
        }
    }

    pub(crate) const fn values(self) -> [u32; MDOC_COUNTRY_CODE_RELATION_ARITY] {
        [self.tag, self.num_hi, self.num_lo, self.upper0, self.upper1]
    }

    fn m31_values(self) -> [M31; MDOC_COUNTRY_CODE_RELATION_ARITY] {
        self.values().map(M31::from_u32_unchecked)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct MdocCountryCodeRow {
    active: u32,
    tuple: MdocCountryCodeTuple,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum MdocCountryCodeError {
    NoConsumers,
    UnknownAlpha2([u8; 2]),
    UnknownTuple(MdocCountryCodeTuple),
    MultiplicityOverflow {
        row: usize,
        current: u32,
        additional: u32,
    },
}

impl fmt::Display for MdocCountryCodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoConsumers => write!(f, "country-code table requires at least one consumer"),
            Self::UnknownAlpha2(alpha2) => write!(
                f,
                "unknown uppercase alpha-2 country code {:02x}{:02x}",
                alpha2[0], alpha2[1]
            ),
            Self::UnknownTuple(tuple) => {
                write!(f, "country-code tuple {tuple:?} is not an active table row")
            }
            Self::MultiplicityOverflow {
                row,
                current,
                additional,
            } => write!(
                f,
                "country-code row {row} multiplicity {current} + {additional} exceeds the M31-safe cap"
            ),
        }
    }
}

impl std::error::Error for MdocCountryCodeError {}

/// Exact provider census contributed by one private-item consumer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MdocCountryCodeUses {
    counts: [u32; MDOC_COUNTRY_CODE_ACTIVE_ROWS],
}

impl Default for MdocCountryCodeUses {
    fn default() -> Self {
        Self {
            counts: [0; MDOC_COUNTRY_CODE_ACTIVE_ROWS],
        }
    }
}

impl MdocCountryCodeUses {
    pub(crate) fn record_numeric_dummy(&mut self) -> Result<(), MdocCountryCodeError> {
        self.add_row(0, 1)
    }

    /// Record one alpha-2 lookup and return its normalized big-endian numeric
    /// country code.
    #[cfg(test)]
    pub(crate) fn record_alpha2(
        &mut self,
        upper: [u8; 2],
    ) -> Result<[u8; 2], MdocCountryCodeError> {
        let row =
            country_row_for_alpha2(upper).ok_or(MdocCountryCodeError::UnknownAlpha2(upper))?;
        self.add_row(row, 1)?;
        let tuple = country_code_rows()[row].tuple;
        Ok([tuple.num_hi as u8, tuple.num_lo as u8])
    }

    pub(crate) fn record_tuple(
        &mut self,
        tuple: MdocCountryCodeTuple,
    ) -> Result<(), MdocCountryCodeError> {
        let row = country_row_for_tuple(tuple).ok_or(MdocCountryCodeError::UnknownTuple(tuple))?;
        self.add_row(row, 1)
    }

    pub(crate) fn total_uses(&self) -> u64 {
        self.counts.iter().map(|&count| u64::from(count)).sum()
    }

    fn add_row(&mut self, row: usize, additional: u32) -> Result<(), MdocCountryCodeError> {
        let current = self.counts[row];
        let total =
            current
                .checked_add(additional)
                .ok_or(MdocCountryCodeError::MultiplicityOverflow {
                    row,
                    current,
                    additional,
                })?;
        if total > MDOC_COUNTRY_CODE_MAX_MULTIPLICITY {
            return Err(MdocCountryCodeError::MultiplicityOverflow {
                row,
                current,
                additional,
            });
        }
        self.counts[row] = total;
        Ok(())
    }
}

pub(crate) fn mdoc_country_code_numeric_dummy_tuple() -> MdocCountryCodeTuple {
    MdocCountryCodeTuple::numeric_dummy()
}

pub(crate) fn mdoc_country_code_alpha2_tuple(
    upper: [u8; 2],
) -> Result<MdocCountryCodeTuple, MdocCountryCodeError> {
    country_row_for_alpha2(upper)
        .map(|row| country_code_rows()[row].tuple)
        .ok_or(MdocCountryCodeError::UnknownAlpha2(upper))
}

fn country_row_for_alpha2(upper: [u8; 2]) -> Option<usize> {
    country_code_rows()
        .iter()
        .take(MDOC_COUNTRY_CODE_ACTIVE_ROWS)
        .position(|row| {
            row.tuple.upper0 == u32::from(upper[0])
                && row.tuple.upper1 == u32::from(upper[1])
                && row.tuple.tag == MDOC_COUNTRY_CODE_TAG_ALPHA2
        })
}

fn country_row_for_tuple(tuple: MdocCountryCodeTuple) -> Option<usize> {
    country_code_rows()
        .iter()
        .take(MDOC_COUNTRY_CODE_ACTIVE_ROWS)
        .position(|row| row.tuple == tuple)
}

fn deterministic_inactive_cell(row: usize, slot: usize) -> u32 {
    let mut value = MDOC_COUNTRY_CODE_INACTIVE_SEED
        ^ (row as u32).wrapping_mul(0x9e37_79b9)
        ^ (slot as u32).wrapping_mul(0x85eb_ca6b);
    value ^= value >> 16;
    value = value.wrapping_mul(0x7feb_352d);
    value ^= value >> 15;
    value = value.wrapping_mul(0x846c_a68b);
    value ^= value >> 16;
    value % 0x7fff_fffe
}

fn country_code_rows() -> [MdocCountryCodeRow; MDOC_COUNTRY_CODE_TABLE_ROWS] {
    let mut rows = [MdocCountryCodeRow {
        active: 0,
        tuple: MdocCountryCodeTuple::numeric_dummy(),
    }; MDOC_COUNTRY_CODE_TABLE_ROWS];
    rows[0].active = 1;

    for (index, country) in celes::Country::get_countries().into_iter().enumerate() {
        let alpha2: [u8; 2] = country
            .alpha2
            .as_bytes()
            .try_into()
            .expect("celes 2.8.2 alpha-2 codes are exactly two bytes");
        let numeric =
            u16::try_from(country.value).expect("celes 2.8.2 numeric country codes fit u16");
        rows[index + 1] = MdocCountryCodeRow {
            active: 1,
            tuple: MdocCountryCodeTuple {
                tag: MDOC_COUNTRY_CODE_TAG_ALPHA2,
                num_hi: u32::from((numeric >> 8) as u8),
                num_lo: u32::from(numeric as u8),
                upper0: u32::from(alpha2[0]),
                upper1: u32::from(alpha2[1]),
            },
        };
    }

    for (row, entry) in rows
        .iter_mut()
        .enumerate()
        .skip(MDOC_COUNTRY_CODE_ACTIVE_ROWS)
    {
        entry.tuple = MdocCountryCodeTuple {
            tag: MDOC_COUNTRY_CODE_TAG_INACTIVE,
            num_hi: deterministic_inactive_cell(row, 0),
            num_lo: deterministic_inactive_cell(row, 1),
            upper0: deterministic_inactive_cell(row, 2),
            upper1: deterministic_inactive_cell(row, 3),
        };
    }
    rows
}

fn random_m31_cell() -> M31 {
    let mut rng = rand::thread_rng();
    loop {
        let value = rng.next_u32() & 0x7fff_ffff;
        if value < 0x7fff_ffff {
            return M31::from_u32_unchecked(value);
        }
    }
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

fn column(coset_values: Vec<M31>) -> MdocCountryCodeColumnEval {
    CircleEvaluation::new(
        CanonicCoset::new(MDOC_COUNTRY_CODE_TABLE_LOG_SIZE).circle_domain(),
        BaseColumn::from_iter(coset_order_to_circle_domain_order(
            MDOC_COUNTRY_CODE_TABLE_LOG_SIZE,
            coset_values,
        )),
    )
}

fn preprocessed_column_ids() -> Vec<PreProcessedColumnId> {
    ["active", "tag", "num_hi", "num_lo", "upper0", "upper1"]
        .into_iter()
        .map(|name| PreProcessedColumnId {
            id: format!("mdoc/country_code/v{MDOC_COUNTRY_CODE_TABLE_VERSION}/celes_2_8_2/{name}"),
        })
        .collect()
}

fn preprocessed_columns() -> Vec<MdocCountryCodeColumnEval> {
    let rows = country_code_rows();
    let mut values = (0..MDOC_COUNTRY_CODE_PREPROCESSED_COLS)
        .map(|_| Vec::with_capacity(MDOC_COUNTRY_CODE_TABLE_ROWS))
        .collect::<Vec<_>>();
    for row in rows {
        values[0].push(M31::from_u32_unchecked(row.active));
        for (column, value) in row.tuple.m31_values().into_iter().enumerate() {
            values[column + 1].push(value);
        }
    }
    values.into_iter().map(column).collect()
}

fn aggregate_uses(
    uses: &[MdocCountryCodeUses],
) -> Result<[u32; MDOC_COUNTRY_CODE_ACTIVE_ROWS], MdocCountryCodeError> {
    if uses.is_empty() {
        return Err(MdocCountryCodeError::NoConsumers);
    }
    let mut totals = [0u32; MDOC_COUNTRY_CODE_ACTIVE_ROWS];
    for consumer in uses {
        for (row, (&additional, total)) in consumer.counts.iter().zip(totals.iter_mut()).enumerate()
        {
            let current = *total;
            let next = current.checked_add(additional).ok_or(
                MdocCountryCodeError::MultiplicityOverflow {
                    row,
                    current,
                    additional,
                },
            )?;
            if next > MDOC_COUNTRY_CODE_MAX_MULTIPLICITY {
                return Err(MdocCountryCodeError::MultiplicityOverflow {
                    row,
                    current,
                    additional,
                });
            }
            *total = next;
        }
    }
    Ok(totals)
}

fn multiplicity_values(totals: &[u32; MDOC_COUNTRY_CODE_ACTIVE_ROWS]) -> Vec<M31> {
    let mut values: Vec<M31> = totals
        .iter()
        .copied()
        .map(M31::from_u32_unchecked)
        .collect();
    values.resize_with(MDOC_COUNTRY_CODE_TABLE_ROWS, random_m31_cell);
    values
}

fn interaction_trace(
    multiplicity: &MdocCountryCodeColumnEval,
    relation: &MdocCountryCodeRelation,
) -> (Vec<MdocCountryCodeColumnEval>, QM31) {
    let preprocessed = preprocessed_columns();
    let mut logup = LogupTraceGenerator::new(MDOC_COUNTRY_CODE_TABLE_LOG_SIZE);
    logup.col_from_fn(|row| {
        let tuple: [PackedM31; MDOC_COUNTRY_CODE_RELATION_ARITY] =
            std::array::from_fn(|index| preprocessed[index + 1].data[row]);
        let denominator: PackedQM31 = relation.combine(&tuple);
        let numerator = -PackedQM31::from(preprocessed[0].data[row] * multiplicity.data[row]);
        (numerator, denominator)
    });
    logup.finalize_last()
}

#[derive(Clone)]
pub(crate) struct MdocCountryCodeTableEval {
    relation: MdocCountryCodeRelation,
}

impl FrameworkEval for MdocCountryCodeTableEval {
    fn log_size(&self) -> u32 {
        MDOC_COUNTRY_CODE_TABLE_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        MDOC_COUNTRY_CODE_TABLE_LOG_SIZE + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let ids = preprocessed_column_ids();
        let active = eval.get_preprocessed_column(ids[0].clone());
        let tuple = [
            eval.get_preprocessed_column(ids[1].clone()),
            eval.get_preprocessed_column(ids[2].clone()),
            eval.get_preprocessed_column(ids[3].clone()),
            eval.get_preprocessed_column(ids[4].clone()),
            eval.get_preprocessed_column(ids[5].clone()),
        ];
        let multiplicity = eval.next_trace_mask();
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(active * multiplicity),
            &tuple,
        ));
        eval.finalize_logup();
        eval
    }
}

/// One proof-wide country-code provider shared by all private item consumers.
pub(crate) struct MdocCountryCodeTable {
    handle: SharedMdocCountryCodeRelation,
    multiplicity: Option<MdocCountryCodeColumnEval>,
    relation: Option<MdocCountryCodeRelation>,
    claimed_sum: QM31,
    component: Option<MdocCountryCodeComponent>,
}

impl MdocCountryCodeTable {
    pub(crate) fn prover(
        uses: &[MdocCountryCodeUses],
        handle: SharedMdocCountryCodeRelation,
    ) -> Result<Self, MdocCountryCodeError> {
        let totals = aggregate_uses(uses)?;
        Ok(Self {
            handle,
            multiplicity: Some(column(multiplicity_values(&totals))),
            relation: None,
            claimed_sum: QM31::from_u32_unchecked(0, 0, 0, 0),
            component: None,
        })
    }

    pub(crate) fn verifier(claimed_sum: QM31, handle: SharedMdocCountryCodeRelation) -> Self {
        Self {
            handle,
            multiplicity: None,
            relation: None,
            claimed_sum,
            component: None,
        }
    }

    pub(crate) fn claimed_sum(&self) -> QM31 {
        self.claimed_sum
    }

    fn relation(&self) -> MdocCountryCodeRelation {
        self.relation
            .clone()
            .expect("country-code relation is drawn")
    }
}

impl Air for MdocCountryCodeTable {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(MDOC_COUNTRY_CODE_TABLE_DOMAIN);
        channel.mix_u64(MDOC_COUNTRY_CODE_TABLE_VERSION);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let relation = MdocCountryCodeRelation::draw(channel);
        self.handle.set(relation.clone());
        self.relation = Some(relation);
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![
                MDOC_COUNTRY_CODE_TABLE_LOG_SIZE;
                MDOC_COUNTRY_CODE_PREPROCESSED_COLS
            ],
            trace: vec![MDOC_COUNTRY_CODE_TABLE_LOG_SIZE; MDOC_COUNTRY_CODE_TRACE_COLS],
            interaction: vec![MDOC_COUNTRY_CODE_TABLE_LOG_SIZE; MDOC_COUNTRY_CODE_INTERACTION_COLS],
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        vec![self.claimed_sum]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_column_ids()
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(preprocessed_columns())
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.component = Some(MdocCountryCodeComponent::new(
            allocator,
            MdocCountryCodeTableEval {
                relation: self.relation(),
            },
            self.claimed_sum,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![self
            .component
            .as_ref()
            .expect("country-code table component is built")]
    }
}

impl AirProver for MdocCountryCodeTable {
    fn max_log_size(&self) -> u32 {
        MDOC_COUNTRY_CODE_TABLE_LOG_SIZE
    }

    fn write_preprocessed(&mut self, tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tree.extend_evals(preprocessed_columns());
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc_country_code_table",
            &preprocessed_column_ids(),
            &preprocessed_columns(),
        )
    }

    fn write_trace(&mut self, tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tree.extend_evals(vec![self
            .multiplicity
            .clone()
            .expect("country-code prover multiplicity")]);
    }

    fn write_interaction(&mut self, tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let (trace, claimed_sum) = interaction_trace(
            self.multiplicity
                .as_ref()
                .expect("country-code prover multiplicity"),
            &self.relation(),
        );
        self.claimed_sum = claimed_sum;
        tree.extend_evals(trace);
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![self
            .component
            .as_ref()
            .expect("country-code table component is built")]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use sha2::{Digest, Sha256};
    use stwo::core::fields::qm31::SecureField;
    use stwo::core::pcs::PcsConfig;
    use stwo::core::proof::StarkProof;

    const TEST_CONSUMER_DOMAIN: u64 = 0x4d44_4f43_434f_4e53;
    const TEST_CONSUMER_TRACE_COLS: usize = 1 + MDOC_COUNTRY_CODE_RELATION_ARITY;

    fn table_digest(rows: &[MdocCountryCodeRow]) -> [u8; 32] {
        let mut digest = Sha256::new();
        for row in rows {
            for value in std::iter::once(row.active).chain(row.tuple.values()) {
                digest.update(value.to_le_bytes());
            }
        }
        digest.finalize().into()
    }

    fn consumer_trace(tuples: &[MdocCountryCodeTuple]) -> Vec<MdocCountryCodeColumnEval> {
        assert!(tuples.len() <= MDOC_COUNTRY_CODE_TABLE_ROWS);
        let mut columns = vec![
            vec![M31::from_u32_unchecked(0); MDOC_COUNTRY_CODE_TABLE_ROWS];
            TEST_CONSUMER_TRACE_COLS
        ];
        for (row, tuple) in tuples.iter().copied().enumerate() {
            columns[0][row] = M31::from_u32_unchecked(1);
            for (index, value) in tuple.m31_values().into_iter().enumerate() {
                columns[index + 1][row] = value;
            }
        }
        columns.into_iter().map(column).collect()
    }

    fn consumer_interaction(
        tuples: &[MdocCountryCodeTuple],
        relation: &MdocCountryCodeRelation,
    ) -> (Vec<MdocCountryCodeColumnEval>, QM31) {
        let trace = consumer_trace(tuples);
        let mut logup = LogupTraceGenerator::new(MDOC_COUNTRY_CODE_TABLE_LOG_SIZE);
        logup.col_from_fn(|row| {
            let tuple: [PackedM31; MDOC_COUNTRY_CODE_RELATION_ARITY] =
                std::array::from_fn(|index| trace[index + 1].data[row]);
            (
                PackedQM31::from(trace[0].data[row]),
                relation.combine(&tuple),
            )
        });
        logup.finalize_last()
    }

    #[derive(Clone)]
    struct TestConsumerEval {
        relation: MdocCountryCodeRelation,
    }

    impl FrameworkEval for TestConsumerEval {
        fn log_size(&self) -> u32 {
            MDOC_COUNTRY_CODE_TABLE_LOG_SIZE
        }

        fn max_constraint_log_degree_bound(&self) -> u32 {
            MDOC_COUNTRY_CODE_TABLE_LOG_SIZE + 1
        }

        fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
            let active = eval.next_trace_mask();
            let tuple: [E::F; MDOC_COUNTRY_CODE_RELATION_ARITY] =
                std::array::from_fn(|_| eval.next_trace_mask());
            let one = E::F::from(M31::from_u32_unchecked(1));
            eval.add_constraint(active.clone() * (one - active.clone()));
            eval.add_to_relation(RelationEntry::new(
                &self.relation,
                E::EF::from(active),
                &tuple,
            ));
            eval.finalize_logup();
            eval
        }
    }

    struct TestConsumer {
        tuples: Option<Vec<MdocCountryCodeTuple>>,
        handle: SharedMdocCountryCodeRelation,
        relation: Option<MdocCountryCodeRelation>,
        claimed_sum: QM31,
        component: Option<FrameworkComponent<TestConsumerEval>>,
    }

    impl TestConsumer {
        fn prover(
            tuples: Vec<MdocCountryCodeTuple>,
            handle: SharedMdocCountryCodeRelation,
        ) -> Self {
            Self {
                tuples: Some(tuples),
                handle,
                relation: None,
                claimed_sum: QM31::from_u32_unchecked(0, 0, 0, 0),
                component: None,
            }
        }

        fn verifier(claimed_sum: QM31, handle: SharedMdocCountryCodeRelation) -> Self {
            Self {
                tuples: None,
                handle,
                relation: None,
                claimed_sum,
                component: None,
            }
        }

        fn relation(&self) -> MdocCountryCodeRelation {
            self.relation.clone().expect("test relation is drawn")
        }
    }

    impl Air for TestConsumer {
        fn mix_public(&self, channel: &mut Blake2sChannel) {
            channel.mix_u64(TEST_CONSUMER_DOMAIN);
            channel.mix_u64(MDOC_COUNTRY_CODE_TABLE_VERSION);
        }

        fn draw_relations(&mut self, _channel: &mut Blake2sChannel) {
            self.relation = Some(self.handle.get());
        }

        fn layout(&self) -> TreeLayout {
            TreeLayout {
                preprocessed: Vec::new(),
                trace: vec![MDOC_COUNTRY_CODE_TABLE_LOG_SIZE; TEST_CONSUMER_TRACE_COLS],
                interaction: vec![MDOC_COUNTRY_CODE_TABLE_LOG_SIZE; SECURE_EXTENSION_DEGREE],
            }
        }

        fn claimed_sums(&self) -> Vec<QM31> {
            vec![self.claimed_sum]
        }

        fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
            Vec::new()
        }

        fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
            self.component = Some(FrameworkComponent::new(
                allocator,
                TestConsumerEval {
                    relation: self.relation(),
                },
                self.claimed_sum,
            ));
        }

        fn components(&self) -> Vec<&dyn Component> {
            vec![self
                .component
                .as_ref()
                .expect("test consumer component is built")]
        }
    }

    impl AirProver for TestConsumer {
        fn max_log_size(&self) -> u32 {
            MDOC_COUNTRY_CODE_TABLE_LOG_SIZE
        }

        fn write_preprocessed(&mut self, _tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

        fn write_trace(&mut self, tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
            tree.extend_evals(consumer_trace(
                self.tuples.as_deref().expect("test consumer witness"),
            ));
        }

        fn write_interaction(&mut self, tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
            let (trace, claimed_sum) = consumer_interaction(
                self.tuples.as_deref().expect("test consumer witness"),
                &self.relation(),
            );
            self.claimed_sum = claimed_sum;
            tree.extend_evals(trace);
        }

        fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
            vec![self
                .component
                .as_ref()
                .expect("test consumer component is built")]
        }
    }

    struct LookupProof {
        proof: StarkProof<air_core::Hasher>,
        table_claim: QM31,
        consumer_claim: QM31,
    }

    fn prove_lookup(
        uses: MdocCountryCodeUses,
        tuples: Vec<MdocCountryCodeTuple>,
        config: PcsConfig,
    ) -> LookupProof {
        let handle = SharedMdocCountryCodeRelation::new();
        let mut table =
            MdocCountryCodeTable::prover(&[uses], handle.clone()).expect("valid table census");
        let mut consumer = TestConsumer::prover(tuples, handle);
        let proof = air_core::prove(&mut [&mut table, &mut consumer], config)
            .expect("locally valid lookup proof");
        LookupProof {
            proof,
            table_claim: table.claimed_sum(),
            consumer_claim: consumer.claimed_sum,
        }
    }

    fn verify_lookup(fixture: &LookupProof) -> Result<(), air_core::VerifyError> {
        let handle = SharedMdocCountryCodeRelation::new();
        let mut table = MdocCountryCodeTable::verifier(fixture.table_claim, handle.clone());
        let mut consumer = TestConsumer::verifier(fixture.consumer_claim, handle);
        let expected_root = air_core::compute_canonical_preprocessed_root(
            &mut [&mut table, &mut consumer],
            fixture.proof.config,
        )
        .expect("canonical country table root");
        air_core::verify_with_expected_preprocessed_root(
            &mut [&mut table, &mut consumer],
            &fixture.proof,
            Some(expected_root),
        )
    }

    #[test]
    fn table_is_exact_celes_2_8_2_order_and_has_golden_digest() {
        assert!(
            include_str!("../Cargo.toml").contains("celes = \"=2.8.2\""),
            "the circuit's source dependency must remain exactly pinned"
        );
        let rows = country_code_rows();
        assert_eq!(rows[0].active, 1);
        assert_eq!(rows[0].tuple, MdocCountryCodeTuple::numeric_dummy());

        let countries = celes::Country::get_countries();
        assert_eq!(countries.len(), MDOC_COUNTRY_CODE_COUNT);
        for (index, country) in countries.into_iter().enumerate() {
            let row = rows[index + 1];
            let alpha2: [u8; 2] = country.alpha2.as_bytes().try_into().unwrap();
            let numeric = country.value as u16;
            assert_eq!(row.active, 1, "celes row {index} must be active");
            assert_eq!(
                row.tuple,
                MdocCountryCodeTuple {
                    tag: MDOC_COUNTRY_CODE_TAG_ALPHA2,
                    num_hi: u32::from((numeric >> 8) as u8),
                    num_lo: u32::from(numeric as u8),
                    upper0: u32::from(alpha2[0]),
                    upper1: u32::from(alpha2[1]),
                },
                "table row {} differs from celes country {country:?}",
                index + 1
            );
        }

        let xk = rows
            .iter()
            .filter(|row| {
                row.active == 1
                    && row.tuple.upper0 == u32::from(b'X')
                    && row.tuple.upper1 == u32::from(b'K')
            })
            .collect::<Vec<_>>();
        assert_eq!(xk.len(), 1, "XK must occur exactly once");
        assert_eq!([xk[0].tuple.num_hi, xk[0].tuple.num_lo], [1, 127]);
        assert_eq!(
            table_digest(&rows),
            MDOC_COUNTRY_CODE_TABLE_SHA256,
            "country table changed; update only with a circuit-version review"
        );
    }

    #[test]
    fn inactive_rows_are_fixed_masks_and_multiplicities_are_fresh() {
        let first_rows = country_code_rows();
        let second_rows = country_code_rows();
        assert_eq!(first_rows, second_rows);
        assert!(first_rows[..MDOC_COUNTRY_CODE_ACTIVE_ROWS]
            .iter()
            .all(|row| row.active == 1));
        assert!(first_rows[MDOC_COUNTRY_CODE_ACTIVE_ROWS..]
            .iter()
            .enumerate()
            .all(|(offset, row)| {
                let table_row = MDOC_COUNTRY_CODE_ACTIVE_ROWS + offset;
                row.active == 0
                    && row.tuple.tag == MDOC_COUNTRY_CODE_TAG_INACTIVE
                    && row.tuple.num_hi == deterministic_inactive_cell(table_row, 0)
                    && row.tuple.num_lo == deterministic_inactive_cell(table_row, 1)
                    && row.tuple.upper0 == deterministic_inactive_cell(table_row, 2)
                    && row.tuple.upper1 == deterministic_inactive_cell(table_row, 3)
            }));

        let mut uses = MdocCountryCodeUses::default();
        uses.record_numeric_dummy().unwrap();
        uses.record_alpha2(*b"DE").unwrap();
        let totals = aggregate_uses(&[uses]).unwrap();
        let first = multiplicity_values(&totals);
        let second = multiplicity_values(&totals);
        for row in 0..MDOC_COUNTRY_CODE_ACTIVE_ROWS {
            assert_eq!(first[row], M31::from_u32_unchecked(totals[row]));
            assert_eq!(second[row], first[row]);
        }
        assert_ne!(
            &first[MDOC_COUNTRY_CODE_ACTIVE_ROWS..],
            &second[MDOC_COUNTRY_CODE_ACTIVE_ROWS..],
            "inactive committed multiplicities must be freshly randomized"
        );
    }

    #[test]
    fn uses_are_typed_exact_and_checked() {
        let mut uses = MdocCountryCodeUses::default();
        assert_eq!(uses.total_uses(), 0);
        uses.record_numeric_dummy().unwrap();
        assert_eq!(uses.record_alpha2(*b"DE").unwrap(), [1, 20]);
        assert_eq!(uses.total_uses(), 2);
        uses.record_tuple(mdoc_country_code_alpha2_tuple(*b"FR").unwrap())
            .unwrap();
        assert_eq!(uses.total_uses(), 3);
        assert_eq!(
            uses.record_alpha2(*b"ZZ"),
            Err(MdocCountryCodeError::UnknownAlpha2(*b"ZZ"))
        );
        assert!(matches!(
            uses.record_tuple(MdocCountryCodeTuple {
                tag: MDOC_COUNTRY_CODE_TAG_ALPHA2,
                num_hi: 1,
                num_lo: 20,
                upper0: u32::from(b'F'),
                upper1: u32::from(b'R'),
            }),
            Err(MdocCountryCodeError::UnknownTuple(_))
        ));

        uses.counts[0] = MDOC_COUNTRY_CODE_MAX_MULTIPLICITY;
        assert!(matches!(
            uses.record_numeric_dummy(),
            Err(MdocCountryCodeError::MultiplicityOverflow { row: 0, .. })
        ));
        assert_eq!(
            MdocCountryCodeTable::prover(&[], SharedMdocCountryCodeRelation::new()).err(),
            Some(MdocCountryCodeError::NoConsumers)
        );
    }

    #[test]
    fn layout_degree_coefficients_relation_and_fingerprints_are_frozen() {
        let mut uses = MdocCountryCodeUses::default();
        uses.record_numeric_dummy().unwrap();
        let mut first = MdocCountryCodeTable::prover(
            std::slice::from_ref(&uses),
            SharedMdocCountryCodeRelation::new(),
        )
        .unwrap();
        let mut second =
            MdocCountryCodeTable::prover(&[uses], SharedMdocCountryCodeRelation::new()).unwrap();

        assert_eq!(
            first.layout().preprocessed,
            vec![MDOC_COUNTRY_CODE_TABLE_LOG_SIZE; MDOC_COUNTRY_CODE_PREPROCESSED_COLS]
        );
        assert_eq!(first.layout().trace, vec![MDOC_COUNTRY_CODE_TABLE_LOG_SIZE]);
        assert_eq!(
            first.layout().interaction,
            vec![MDOC_COUNTRY_CODE_TABLE_LOG_SIZE; SECURE_EXTENSION_DEGREE]
        );
        assert_eq!(
            AirProver::max_constraint_log_degree_bound(&first),
            MDOC_COUNTRY_CODE_TABLE_LOG_SIZE + 1
        );
        assert!(!AirProver::store_polynomial_coefficients(&first));
        let relation = MdocCountryCodeRelation::dummy();
        assert_eq!(
            <MdocCountryCodeRelation as Relation<M31, SecureField>>::get_size(&relation),
            MDOC_COUNTRY_CODE_RELATION_ARITY
        );

        let first_fingerprints = first.preprocessed_column_fingerprints();
        let second_fingerprints = second.preprocessed_column_fingerprints();
        assert_eq!(first_fingerprints, second_fingerprints);
        assert_eq!(
            first_fingerprints.len(),
            MDOC_COUNTRY_CODE_PREPROCESSED_COLS
        );
        assert!(first_fingerprints
            .iter()
            .all(|fingerprint| fingerprint.log_size == MDOC_COUNTRY_CODE_TABLE_LOG_SIZE));
        assert_eq!(
            first_fingerprints
                .iter()
                .map(|fingerprint| fingerprint.id.id.as_str())
                .collect::<Vec<_>>(),
            [
                "mdoc/country_code/v1/celes_2_8_2/active",
                "mdoc/country_code/v1/celes_2_8_2/tag",
                "mdoc/country_code/v1/celes_2_8_2/num_hi",
                "mdoc/country_code/v1/celes_2_8_2/num_lo",
                "mdoc/country_code/v1/celes_2_8_2/upper0",
                "mdoc/country_code/v1/celes_2_8_2/upper1",
            ]
        );
        let canonical = first.canonical_preprocessed_columns().unwrap();
        assert_eq!(canonical.len(), MDOC_COUNTRY_CODE_PREPROCESSED_COLS);
        assert!(canonical
            .iter()
            .all(|column| column.domain.log_size() == MDOC_COUNTRY_CODE_TABLE_LOG_SIZE));
    }

    #[test]
    fn production_pcs_proof_balances_numeric_and_alpha_lookups() {
        let mut uses = MdocCountryCodeUses::default();
        uses.record_numeric_dummy().unwrap();
        let normalized = uses.record_alpha2(*b"DE").unwrap();
        assert_eq!(normalized, [1, 20]);
        let fixture = prove_lookup(
            uses,
            vec![
                mdoc_country_code_numeric_dummy_tuple(),
                mdoc_country_code_alpha2_tuple(*b"DE").unwrap(),
            ],
            crate::mdoc::mdoc_production_pcs_config(),
        );
        verify_lookup(&fixture).expect("numeric dummy and DE mapping must balance");
    }

    #[test]
    fn proof_rejects_wrong_pair_unknown_tuple_and_multiplicity() {
        let germany = mdoc_country_code_alpha2_tuple(*b"DE").unwrap();

        let mut germany_uses = MdocCountryCodeUses::default();
        germany_uses.record_alpha2(*b"DE").unwrap();
        let wrong_pair = prove_lookup(
            germany_uses.clone(),
            vec![MdocCountryCodeTuple {
                upper0: u32::from(b'F'),
                upper1: u32::from(b'R'),
                ..germany
            }],
            PcsConfig::default(),
        );
        assert!(
            verify_lookup(&wrong_pair).is_err(),
            "a numeric/alpha mismatch must not balance"
        );

        let unknown = prove_lookup(
            MdocCountryCodeUses::default(),
            vec![MdocCountryCodeTuple {
                tag: MDOC_COUNTRY_CODE_TAG_ALPHA2,
                num_hi: 0,
                num_lo: 0,
                upper0: u32::from(b'Z'),
                upper1: u32::from(b'Z'),
            }],
            PcsConfig::default(),
        );
        assert!(
            verify_lookup(&unknown).is_err(),
            "an unknown tuple must not balance"
        );

        let multiplicity = prove_lookup(germany_uses, vec![germany, germany], PcsConfig::default());
        assert!(
            verify_lookup(&multiplicity).is_err(),
            "consumer/provider multiplicity mismatch must not balance"
        );
    }
}
