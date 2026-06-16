//! Wraps the range-check age strategy as [`air_core`] proving modules.
//!
//! [`RangeCheckProver`] holds the witness and contributes all columns (prover
//! side). [`RangeCheckVerifier`] holds only the public input and the claimed
//! sums from the proof (verifier side).

use crate::age::calendar::{calendar_log_size, valid_date_ranges};
use crate::age::strategy::range_check::components::{components, preprocessed_column_ids};
use crate::age::strategy::range_check::interaction::InteractionTraces;
use crate::age::strategy::range_check::lookup_elements::LookupElements;
use crate::age::strategy::range_check::preprocessed::Preprocessed;
use crate::age::strategy::range_check::witness::WitnessData;
use crate::age::types::{PublicInput, Witness};
use air_core::{Air, AirProver, TreeLayout};
use stwo::core::air::Component;
use stwo::core::channel::Blake2sChannel;
use stwo::core::fields::qm31::QM31;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::TraceLocationAllocator;

/// Column layout shared by both prover and verifier: it depends only on the
/// public input (its bounds), never on the witness.
fn layout(public: &PublicInput) -> TreeLayout {
    let bounds = &public.bounds;
    let cal = calendar_log_size(bounds);
    let valid_day = valid_date_ranges()[0].domain.log_size();
    let day = Preprocessed::day_range().log_size();
    let month = Preprocessed::month_range().log_size();
    let year = Preprocessed::year_range(bounds).log_size();
    let witness = WitnessData::log_size();
    TreeLayout {
        // Tree 0: calendar (2), valid-day (2), day/month/year delta tables (1 each).
        preprocessed: vec![cal, cal, valid_day, valid_day, day, month, year],
        // Tree 1: 9 witness columns + 5 multiplicity columns.
        trace: std::iter::repeat_n(witness, 9)
            .chain([cal, valid_day, day, month, year])
            .collect(),
        // Tree 2: age (5 LogUp fractions = 20 M31) + cal (4) + valid_day (4) +
        // each delta table (4).
        interaction: std::iter::repeat_n(witness, 20)
            .chain(std::iter::repeat_n(cal, 4))
            .chain(std::iter::repeat_n(valid_day, 4))
            .chain(std::iter::repeat_n(day, 4))
            .chain(std::iter::repeat_n(month, 4))
            .chain(std::iter::repeat_n(year, 4))
            .collect(),
    }
}

/// Bind the public statement and the three range-check table claims to the
/// transcript. This is what makes age's range-check strategy differ from a
/// plain predicate: it mixes the delta-table claims right after tree 0.
fn mix_public(public: &PublicInput, channel: &mut Blake2sChannel) {
    public.mix_into(channel);
    Preprocessed::day_range().claim().mix_into(channel);
    Preprocessed::month_range().claim().mix_into(channel);
    Preprocessed::year_range(&public.bounds)
        .claim()
        .mix_into(channel);
}

/// Prover-side module: built from the public input and the witness.
pub struct RangeCheckProver {
    public: PublicInput,
    preprocessed: Preprocessed,
    witness_data: WitnessData,
    lookup_elements: Option<LookupElements>,
    claimed_sums: Vec<QM31>,
    components: Option<RangeCheckComponents>,
}

impl RangeCheckProver {
    pub fn new(public: &PublicInput, witness: &Witness) -> Self {
        let preprocessed = Preprocessed::new(&public.bounds);
        let witness_data = WitnessData::new(witness, &preprocessed);
        Self {
            public: *public,
            preprocessed,
            witness_data,
            lookup_elements: None,
            claimed_sums: Vec::new(),
            components: None,
        }
    }

    fn relations(&self) -> &LookupElements {
        self.lookup_elements
            .as_ref()
            .expect("relations are drawn before they are used")
    }

    fn built_components(&self) -> &RangeCheckComponents {
        self.components
            .as_ref()
            .expect("components are built before they are borrowed")
    }
}

impl Air for RangeCheckProver {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        mix_public(&self.public, channel);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.lookup_elements = Some(LookupElements::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        layout(&self.public)
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        self.claimed_sums.clone()
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_column_ids(&self.public.bounds)
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(build_components(
            allocator,
            &self.public,
            self.relations().clone(),
            &self.claimed_sums,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        component_refs(self.built_components())
    }
}

impl AirProver for RangeCheckProver {
    fn max_log_size(&self) -> u32 {
        self.preprocessed.cal_trace[0].domain.log_size()
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        self.preprocessed.extend_evals(tb);
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        self.witness_data.extend_evals(tb);
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let interaction =
            InteractionTraces::new(&self.witness_data, &self.preprocessed, self.relations());
        interaction.extend_evals(tb);
        self.claimed_sums = vec![
            interaction.age_claimed_sum,
            interaction.cal_claimed_sum,
            interaction.valid_day_claimed_sum,
            interaction.day_delta_claimed_sum,
            interaction.month_delta_claimed_sum,
            interaction.year_delta_claimed_sum,
        ];
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        prover_component_refs(self.built_components())
    }
}

/// Verifier-side module: built from the public input and the proof's claimed
/// sums. It has no witness and only implements [`Air`].
pub struct RangeCheckVerifier {
    public: PublicInput,
    lookup_elements: Option<LookupElements>,
    claimed_sums: Vec<QM31>,
    components: Option<RangeCheckComponents>,
}

impl RangeCheckVerifier {
    pub fn new(public: &PublicInput, claimed_sums: Vec<QM31>) -> Self {
        Self {
            public: *public,
            lookup_elements: None,
            claimed_sums,
            components: None,
        }
    }

    fn relations(&self) -> &LookupElements {
        self.lookup_elements
            .as_ref()
            .expect("relations are drawn before they are used")
    }

    fn built_components(&self) -> &RangeCheckComponents {
        self.components
            .as_ref()
            .expect("components are built before they are borrowed")
    }
}

impl Air for RangeCheckVerifier {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        mix_public(&self.public, channel);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.lookup_elements = Some(LookupElements::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        layout(&self.public)
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        self.claimed_sums.clone()
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_column_ids(&self.public.bounds)
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(build_components(
            allocator,
            &self.public,
            self.relations().clone(),
            &self.claimed_sums,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        component_refs(self.built_components())
    }
}

type RangeCheckComponents = (
    crate::age::strategy::range_check::eval::AgeRangeCheckComponent,
    crate::age::calendar::CalendarTableComponent,
    crate::age::calendar::ValidDayTableComponent,
    crate::age::strategy::range_check::preprocessed::DayDeltaTableComponent,
    crate::age::strategy::range_check::preprocessed::MonthDeltaTableComponent,
    crate::age::strategy::range_check::preprocessed::YearDeltaTableComponent,
);

/// Assemble the six components for the range-check strategy from the shared
/// allocator, the drawn relations, and the claimed sums (in
/// `[age, cal, valid_day, day, month, year]` order).
fn build_components(
    allocator: &mut TraceLocationAllocator,
    public: &PublicInput,
    lookup_elements: LookupElements,
    claimed_sums: &[QM31],
) -> RangeCheckComponents {
    components(
        allocator,
        public,
        lookup_elements,
        claimed_sums[0],
        claimed_sums[1],
        claimed_sums[2],
        claimed_sums[3],
        claimed_sums[4],
        claimed_sums[5],
    )
}

/// Borrow the six built components as `dyn Component`, in commit order.
fn component_refs(c: &RangeCheckComponents) -> Vec<&dyn Component> {
    vec![&c.0, &c.1, &c.2, &c.3, &c.4, &c.5]
}

/// Borrow the six built components as `dyn ComponentProver`, in commit order.
fn prover_component_refs(c: &RangeCheckComponents) -> Vec<&dyn ComponentProver<SimdBackend>> {
    vec![&c.0, &c.1, &c.2, &c.3, &c.4, &c.5]
}
