//! Wraps the nationality predicate as a [`combiner`] proving module.
//!
//! [`NatProver`] holds the witness and contributes all columns (prover side).
//! [`NatVerifier`] holds only the public input and claimed sums from the proof
//! (verifier side). Both share the same transcript binding, layout, and
//! component assembly via the [`Air`] trait.

use crate::nat::components::{components, preprocessed_column_ids};
use crate::nat::eval::NationalityComponent;
use crate::nat::interaction::InteractionTraces;
use crate::nat::lookup_elements::LookupElements;
use crate::nat::preprocessed::Preprocessed;
use crate::nat::table::NatTableComponent;
use crate::nat::types::{PublicInput, Witness};
use crate::nat::witness::WitnessData;
use air_core::{Air, AirProver, TreeLayout};
use stwo::core::air::Component;
use stwo::core::channel::Blake2sChannel;
use stwo::core::fields::qm31::QM31;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::TraceLocationAllocator;

/// The nationality predicate's two components, in commit order.
type NatComponents = (NationalityComponent, NatTableComponent);

/// Borrow the built components as `dyn Component`, in commit order.
fn component_refs(c: &NatComponents) -> Vec<&dyn Component> {
    vec![&c.0, &c.1]
}

/// Borrow the built components as `dyn ComponentProver`, in commit order.
fn prover_component_refs(c: &NatComponents) -> Vec<&dyn ComponentProver<SimdBackend>> {
    vec![&c.0, &c.1]
}

/// Column layout shared by both prover and verifier: it depends only on the
/// public input, never on the witness.
fn layout(public: &PublicInput) -> TreeLayout {
    let table_log_size = public.log_size();
    let nat_log_size = WitnessData::log_size();
    TreeLayout {
        // Tree 0: the acceptable-nationality table (1 column).
        preprocessed: vec![table_log_size],
        // Tree 1: nationality witness column + table multiplicity column.
        trace: vec![nat_log_size, table_log_size],
        // Tree 2: one LogUp fraction each (4 M31 columns) for nat and table.
        interaction: std::iter::repeat_n(nat_log_size, 4)
            .chain(std::iter::repeat_n(table_log_size, 4))
            .collect(),
    }
}

/// Prover-side module: built from the public input and the witness.
pub struct NatProver {
    public: PublicInput,
    preprocessed: Preprocessed,
    witness_data: WitnessData,
    lookup_elements: Option<LookupElements>,
    claimed_sums: Vec<QM31>,
    components: Option<NatComponents>,
}

impl NatProver {
    pub fn new(public: &PublicInput, witness: &Witness) -> Self {
        Self {
            public: public.clone(),
            preprocessed: Preprocessed::new(public),
            witness_data: WitnessData::new(witness, public),
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

    fn built_components(&self) -> &NatComponents {
        self.components
            .as_ref()
            .expect("components are built before they are borrowed")
    }
}

impl Air for NatProver {
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
        preprocessed_column_ids(&self.public)
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(components(
            allocator,
            &self.public,
            self.relations().clone(),
            self.claimed_sums[0],
            self.claimed_sums[1],
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        component_refs(self.built_components())
    }
}

impl AirProver for NatProver {
    fn max_log_size(&self) -> u32 {
        WitnessData::log_size().max(self.public.log_size())
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
        self.claimed_sums = vec![interaction.nat_claimed_sum, interaction.table_claimed_sum];
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        prover_component_refs(self.built_components())
    }
}

/// Verifier-side module: built from the public input and the proof's claimed
/// sums. It has no witness and only implements [`Air`].
pub struct NatVerifier {
    public: PublicInput,
    lookup_elements: Option<LookupElements>,
    claimed_sums: Vec<QM31>,
    components: Option<NatComponents>,
}

impl NatVerifier {
    pub fn new(public: &PublicInput, nat_claimed_sum: QM31, table_claimed_sum: QM31) -> Self {
        Self {
            public: public.clone(),
            lookup_elements: None,
            claimed_sums: vec![nat_claimed_sum, table_claimed_sum],
            components: None,
        }
    }

    fn relations(&self) -> &LookupElements {
        self.lookup_elements
            .as_ref()
            .expect("relations are drawn before they are used")
    }

    fn built_components(&self) -> &NatComponents {
        self.components
            .as_ref()
            .expect("components are built before they are borrowed")
    }
}

impl Air for NatVerifier {
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
        preprocessed_column_ids(&self.public)
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(components(
            allocator,
            &self.public,
            self.relations().clone(),
            self.claimed_sums[0],
            self.claimed_sums[1],
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        component_refs(self.built_components())
    }
}
