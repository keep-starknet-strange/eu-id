//! Wraps the nationality predicate as a [`combiner`] proving module.
//!
//! [`NatProver`] holds the witness and contributes all columns (prover side).
//! [`NatVerifier`] holds only the public input and claimed sums from the proof
//! (verifier side). Both share the same transcript binding, layout, and
//! component assembly via the [`Air`] trait.

use air_core::{Air, AirProver, TreeLayout};
use crate::nat::components::components;
use crate::nat::interaction::InteractionTraces;
use crate::nat::lookup_elements::LookupElements;
use crate::nat::preprocessed::Preprocessed;
use crate::nat::types::{PublicInput, Witness};
use crate::nat::witness::WitnessData;
use stwo::core::air::Component;
use stwo::core::channel::Blake2sChannel;
use stwo::core::fields::qm31::QM31;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::{ComponentProver, TreeBuilder};

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
}

impl NatProver {
    pub fn new(public: &PublicInput, witness: &Witness) -> Self {
        Self {
            public: public.clone(),
            preprocessed: Preprocessed::new(public),
            witness_data: WitnessData::new(witness, public),
            lookup_elements: None,
            claimed_sums: Vec::new(),
        }
    }

    fn relations(&self) -> &LookupElements {
        self.lookup_elements
            .as_ref()
            .expect("relations are drawn before they are used")
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

    fn components(&self) -> Vec<Box<dyn Component>> {
        let (nat, table) = components(
            &self.public,
            self.relations().clone(),
            self.claimed_sums[0],
            self.claimed_sums[1],
        );
        vec![Box::new(nat), Box::new(table)]
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

    fn prover_components(&self) -> Vec<Box<dyn ComponentProver<SimdBackend>>> {
        let (nat, table) = components(
            &self.public,
            self.relations().clone(),
            self.claimed_sums[0],
            self.claimed_sums[1],
        );
        vec![Box::new(nat), Box::new(table)]
    }
}

/// Verifier-side module: built from the public input and the proof's claimed
/// sums. It has no witness and only implements [`Air`].
pub struct NatVerifier {
    public: PublicInput,
    lookup_elements: Option<LookupElements>,
    claimed_sums: Vec<QM31>,
}

impl NatVerifier {
    pub fn new(public: &PublicInput, nat_claimed_sum: QM31, table_claimed_sum: QM31) -> Self {
        Self {
            public: public.clone(),
            lookup_elements: None,
            claimed_sums: vec![nat_claimed_sum, table_claimed_sum],
        }
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

    fn components(&self) -> Vec<Box<dyn Component>> {
        let lookup_elements = self
            .lookup_elements
            .clone()
            .expect("relations are drawn before they are used");
        let (nat, table) = components(
            &self.public,
            lookup_elements,
            self.claimed_sums[0],
            self.claimed_sums[1],
        );
        vec![Box::new(nat), Box::new(table)]
    }
}
