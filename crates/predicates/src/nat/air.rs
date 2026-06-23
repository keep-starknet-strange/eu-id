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
use air_core::relations::{FieldBytesRelation, SharedFieldRelation};
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

/// Column layout shared by both prover and verifier: it depends on the public
/// input and whether the nationality binding is wired (`bind_nat`), never
/// on the witness values. Binding adds three trace columns (the `bind_active`
/// selector + the two nationality bytes) and two LogUp fractions (the
/// nationality-byte requires) to the nationality component. The nationality
/// component pairs consecutive LogUp fractions.
fn layout(public: &PublicInput, bind_nat: bool) -> TreeLayout {
    let table_log_size = public.log_size();
    let nat_log_size = WitnessData::log_size();
    // The nationality component: 1 (+3 binding) trace columns and 1 (+2 binding)
    // logical LogUp fractions, paired into secure columns, each four M31
    // (`SECURE_EXTENSION_DEGREE`).
    let nat_trace_cols = if bind_nat { 4 } else { 1 };
    let logical_nat_lookups = if bind_nat { 3usize } else { 1 };
    let nat_interaction_cols = logical_nat_lookups.div_ceil(2) * 4;
    TreeLayout {
        // Tree 0: the acceptable-nationality table (1 column).
        preprocessed: vec![table_log_size],
        // Tree 1: nationality witness column(s) + table multiplicity column.
        trace: std::iter::repeat_n(nat_log_size, nat_trace_cols)
            .chain([table_log_size])
            .collect(),
        // Tree 2: nationality LogUp fractions + the table's one fraction.
        interaction: std::iter::repeat_n(nat_log_size, nat_interaction_cols)
            .chain(std::iter::repeat_n(table_log_size, 4))
            .collect(),
    }
}

/// Prover-side module: built from the public input and the witness.
pub struct NatProver {
    public: PublicInput,
    witness: Witness,
    preprocessed: Preprocessed,
    witness_data: WitnessData,
    /// Shared `Sha256Field` channel when the nationality binding is wired.
    /// `None` for a standalone nat proof (the module stays internally balanced).
    nat_binding: Option<SharedFieldRelation>,
    lookup_elements: Option<LookupElements>,
    claimed_sums: Vec<QM31>,
    components: Option<NatComponents>,
}

impl NatProver {
    pub fn new(public: &PublicInput, witness: &Witness) -> Self {
        Self {
            public: public.clone(),
            witness: witness.clone(),
            preprocessed: Preprocessed::new(public),
            witness_data: WitnessData::new(witness, public, false),
            nat_binding: None,
            lookup_elements: None,
            claimed_sums: Vec::new(),
            components: None,
        }
    }

    /// Bind the nationality this module proves set-membership for to the
    /// credential's signed nationality bytes: require the two nationality bytes
    /// on the shared `Sha256Field` channel `handle`, which the SHA module yields.
    /// Off by default; regenerates the witness with the binding columns. The
    /// matching [`NatVerifier`] must set the same handle.
    pub fn with_nat_binding(mut self, handle: SharedFieldRelation) -> Self {
        self.witness_data = WitnessData::new(&self.witness, &self.public, true);
        self.nat_binding = Some(handle);
        self
    }

    /// The drawn field relation, read from the shared handle once it is
    /// populated (after every module's `draw_relations`).
    fn nat_relation(&self) -> Option<FieldBytesRelation> {
        self.nat_binding.as_ref().map(|handle| handle.get())
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
        layout(&self.public, self.nat_binding.is_some())
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
            self.nat_relation(),
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
        let nat_field = self.nat_relation();
        let interaction = InteractionTraces::new(
            &self.witness_data,
            &self.preprocessed,
            self.relations(),
            nat_field.as_ref(),
        );
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
    nat_binding: Option<SharedFieldRelation>,
    lookup_elements: Option<LookupElements>,
    claimed_sums: Vec<QM31>,
    components: Option<NatComponents>,
}

impl NatVerifier {
    pub fn new(public: &PublicInput, nat_claimed_sum: QM31, table_claimed_sum: QM31) -> Self {
        Self {
            public: public.clone(),
            nat_binding: None,
            lookup_elements: None,
            claimed_sums: vec![nat_claimed_sum, table_claimed_sum],
            components: None,
        }
    }

    /// Match a [`NatProver::with_nat_binding`] proof: read the two nationality
    /// bytes from the same shared `Sha256Field` channel so the verifier rebuilds
    /// the bound component (the extra columns + the require terms).
    pub fn with_nat_binding(mut self, handle: SharedFieldRelation) -> Self {
        self.nat_binding = Some(handle);
        self
    }

    fn nat_relation(&self) -> Option<FieldBytesRelation> {
        self.nat_binding.as_ref().map(|handle| handle.get())
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
        layout(&self.public, self.nat_binding.is_some())
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
            self.nat_relation(),
            self.claimed_sums[0],
            self.claimed_sums[1],
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        component_refs(self.built_components())
    }
}

#[cfg(test)]
mod binding_tests {
    //! Isolated nationality↔credential binding tests: drive the bound nat
    //! module against a *synthetic* field producer that plays SHA's role (yields
    //! the two nationality bytes on the shared `Sha256Field` channel). This
    //! exercises the whole bound path — the binding layout, the
    //! boolean/reconciliation constraints, and the cross-module balance — through
    //! a real `air_core::prove`/`verify`, without the (slow) P256 + SHA proof.

    use super::*;
    use crate::nat::types::PrivateInput;
    use crate::nat::NationalityPredicate;
    use crate::predicate::{PredicateProver, PredicateVerifier};
    use air_core::relations::field_id;
    use num_traits::One;
    use stwo::core::air::Component;
    use stwo::core::channel::Blake2sChannel;
    use stwo::core::fields::m31::M31;
    use stwo::core::fields::qm31::SecureField;
    use stwo::core::pcs::PcsConfig;
    use stwo::prover::backend::simd::SimdBackend;
    use stwo::prover::{ComponentProver, TreeBuilder};
    use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
    use stwo_constraint_framework::Relation;

    /// The two nationality byte values for a `code` — the big-endian recomposition
    /// `Credential::encode` / the SHA field provider produce.
    fn nat_bytes(code: u32) -> [u32; 2] {
        [code >> 8, code & 0xFF]
    }

    /// A trace-less module that plays the SHA field provider: it draws the shared
    /// `Sha256Field` relation, shares it, and yields `−1/combine(NATIONALITY, i,
    /// byte)` for the two nationality bytes — exactly the term SHA contributes for
    /// the nationality window (`−is_first_block`, one yield per byte).
    struct NatProvider {
        bytes: [u32; 2],
        handle: SharedFieldRelation,
        relation: Option<FieldBytesRelation>,
    }

    impl NatProvider {
        fn new(bytes: [u32; 2], handle: SharedFieldRelation) -> Self {
            Self {
                bytes,
                handle,
                relation: None,
            }
        }
    }

    impl Air for NatProvider {
        fn mix_public(&self, _channel: &mut Blake2sChannel) {}

        fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
            let relation = FieldBytesRelation::draw(channel);
            self.handle.set(relation.clone());
            self.relation = Some(relation);
        }

        fn layout(&self) -> TreeLayout {
            TreeLayout {
                preprocessed: vec![],
                trace: vec![],
                interaction: vec![],
            }
        }

        fn claimed_sums(&self) -> Vec<QM31> {
            let relation = self.relation.as_ref().expect("relation drawn");
            let sum: SecureField = self
                .bytes
                .iter()
                .enumerate()
                .map(|(i, &b)| {
                    let values = [
                        M31::from_u32_unchecked(field_id::NATIONALITY),
                        M31::from_u32_unchecked(i as u32),
                        M31::from_u32_unchecked(b),
                    ];
                    let denom: SecureField =
                        <FieldBytesRelation as Relation<M31, SecureField>>::combine(
                            relation, &values,
                        );
                    -SecureField::from(M31::one()) / denom
                })
                .sum();
            vec![sum]
        }

        fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
            vec![]
        }

        fn build_components(&mut self, _allocator: &mut TraceLocationAllocator) {}

        fn components(&self) -> Vec<&dyn Component> {
            vec![]
        }
    }

    impl AirProver for NatProvider {
        fn max_log_size(&self) -> u32 {
            1
        }
        fn max_constraint_log_degree_bound(&self) -> u32 {
            2
        }
        fn write_preprocessed(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}
        fn write_trace(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}
        fn write_interaction(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}
        fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
            vec![]
        }
    }

    // DE=276, FR=250 — a two-entry accepted set (the validate minimum).
    fn eu_set() -> PublicInput {
        PublicInput::new(vec![276, 250])
    }

    fn private(code: u32) -> PrivateInput {
        PrivateInput {
            nationalities: vec![code],
        }
    }

    /// The bound nat module's nationality-byte requires cancel the producer's
    /// yields when the code the module proves membership for matches the bytes the
    /// producer yields — the proof verifies.
    #[test]
    fn bound_nat_balances_against_matching_nat_yields() {
        let public = eu_set();

        let handle = SharedFieldRelation::new();
        let mut provider = NatProvider::new(nat_bytes(276), handle.clone());
        let mut nat = NationalityPredicate::new(PcsConfig::default())
            .prover(&public, &private(276))
            .unwrap()
            .with_nat_binding(handle);

        let proof = {
            let mut modules: [&mut dyn AirProver; 2] = [&mut provider, &mut nat];
            air_core::prove(&mut modules, PcsConfig::default()).expect("bound nat proves")
        };
        let sums = nat.claimed_sums();

        let handle_v = SharedFieldRelation::new();
        let mut provider_v = NatProvider::new(nat_bytes(276), handle_v.clone());
        let mut nat_v = NationalityPredicate::new(PcsConfig::default())
            .verifier(&public, &sums)
            .unwrap()
            .with_nat_binding(handle_v);
        let mut modules: [&mut dyn Air; 2] = [&mut provider_v, &mut nat_v];
        air_core::verify(&mut modules, &proof).expect("bound nat verifies against matching yields");
    }

    /// When the producer yields a *different* nationality than the nat module
    /// proves membership for (the credential↔predicate attack), the requires no
    /// longer cancel the yields — the global balance breaks and the verifier
    /// rejects. The prover still succeeds (each module is internally consistent;
    /// the imbalance is a verify-time check). Both codes are in the accepted set,
    /// so membership alone cannot catch the swap — only the binding does.
    #[test]
    fn bound_nat_rejects_mismatched_nat_yields() {
        let public = eu_set();
        // The nat module proves membership for DE (276)...
        // ...but the producer yields the bytes of FR (250) — as if the signed
        // credential held a different (also accepted) nationality.
        let credential_bytes = nat_bytes(250);
        assert_ne!(credential_bytes, nat_bytes(276));

        let handle = SharedFieldRelation::new();
        let mut provider = NatProvider::new(credential_bytes, handle.clone());
        let mut nat = NationalityPredicate::new(PcsConfig::default())
            .prover(&public, &private(276))
            .unwrap()
            .with_nat_binding(handle);

        let proof = {
            let mut modules: [&mut dyn AirProver; 2] = [&mut provider, &mut nat];
            air_core::prove(&mut modules, PcsConfig::default())
                .expect("prover accepts the mismatch")
        };
        let sums = nat.claimed_sums();

        let handle_v = SharedFieldRelation::new();
        let mut provider_v = NatProvider::new(credential_bytes, handle_v.clone());
        let mut nat_v = NationalityPredicate::new(PcsConfig::default())
            .verifier(&public, &sums)
            .unwrap()
            .with_nat_binding(handle_v);
        let mut modules: [&mut dyn Air; 2] = [&mut provider_v, &mut nat_v];
        assert!(
            air_core::verify(&mut modules, &proof).is_err(),
            "a nationality that differs from the yielded credential bytes must be rejected",
        );
    }
}
