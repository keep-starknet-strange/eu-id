//! Wraps the bit-decomposition age strategy as [`air_core`] proving modules.
//!
//! [`BitDecompositionProver`] holds the witness and contributes all columns
//! (prover side). [`BitDecompositionVerifier`] holds only the public input and
//! the claimed sums from the proof (verifier side).

use crate::age::calendar::{calendar_log_size, valid_date_ranges};
use crate::age::strategy::bit_decomposition::components::{components, preprocessed_column_ids};
use crate::age::strategy::bit_decomposition::interaction::InteractionTraces;
use crate::age::strategy::bit_decomposition::lookup_elements::LookupElements;
use crate::age::strategy::bit_decomposition::preprocessed::Preprocessed;
use crate::age::strategy::bit_decomposition::witness::WitnessData;
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
    let witness = WitnessData::log_size();
    TreeLayout {
        // Tree 0: calendar (2) + valid-day (2).
        preprocessed: vec![cal, cal, valid_day, valid_day],
        // Tree 1: bit-decomposed witness columns + calendar/valid-day multiplicities.
        trace: std::iter::repeat_n(witness, WitnessData::trace_columns(bounds))
            .chain([cal, valid_day])
            .collect(),
        // Tree 2: age (2 LogUp fractions = 8 M31) + cal (4) + valid_day (4).
        interaction: std::iter::repeat_n(witness, 8)
            .chain(std::iter::repeat_n(cal, 4))
            .chain(std::iter::repeat_n(valid_day, 4))
            .collect(),
    }
}

/// Prover-side module: built from the public input and the witness.
pub struct BitDecompositionProver {
    public: PublicInput,
    preprocessed: Preprocessed,
    witness_data: WitnessData,
    lookup_elements: Option<LookupElements>,
    claimed_sums: Vec<QM31>,
    components: Option<BitDecompositionComponents>,
}

impl BitDecompositionProver {
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

    fn built_components(&self) -> &BitDecompositionComponents {
        self.components
            .as_ref()
            .expect("components are built before they are borrowed")
    }
}

impl Air for BitDecompositionProver {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        self.public.mix_into(channel);
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

impl AirProver for BitDecompositionProver {
    fn max_log_size(&self) -> u32 {
        WitnessData::log_size().max(self.preprocessed.cal_trace[0].domain.log_size())
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
        ];
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        prover_component_refs(self.built_components())
    }
}

/// Verifier-side module: built from the public input and the proof's claimed
/// sums. It has no witness and only implements [`Air`].
pub struct BitDecompositionVerifier {
    public: PublicInput,
    lookup_elements: Option<LookupElements>,
    claimed_sums: Vec<QM31>,
    components: Option<BitDecompositionComponents>,
}

impl BitDecompositionVerifier {
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

    fn built_components(&self) -> &BitDecompositionComponents {
        self.components
            .as_ref()
            .expect("components are built before they are borrowed")
    }
}

impl Air for BitDecompositionVerifier {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        self.public.mix_into(channel);
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

type BitDecompositionComponents = (
    crate::age::strategy::bit_decomposition::eval::AgeBitDecompositionComponent,
    crate::age::calendar::CalendarTableComponent,
    crate::age::calendar::ValidDayTableComponent,
);

/// Assemble the three components for the bit-decomposition strategy from the
/// shared allocator, the drawn relations, and the claimed sums (in
/// `[age, cal, valid_day]` order).
fn build_components(
    allocator: &mut TraceLocationAllocator,
    public: &PublicInput,
    lookup_elements: LookupElements,
    claimed_sums: &[QM31],
) -> BitDecompositionComponents {
    components(
        allocator,
        public,
        lookup_elements,
        claimed_sums[0],
        claimed_sums[1],
        claimed_sums[2],
    )
}

/// Borrow the three built components as `dyn Component`, in commit order.
fn component_refs(c: &BitDecompositionComponents) -> Vec<&dyn Component> {
    vec![&c.0, &c.1, &c.2]
}

/// Borrow the three built components as `dyn ComponentProver`, in commit order.
fn prover_component_refs(c: &BitDecompositionComponents) -> Vec<&dyn ComponentProver<SimdBackend>> {
    vec![&c.0, &c.1, &c.2]
}
