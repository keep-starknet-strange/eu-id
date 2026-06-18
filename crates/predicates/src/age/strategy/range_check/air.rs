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

/// Column layout shared by both prover and verifier: it depends on the public
/// input (its bounds) and whether the §6.6 DOB binding is wired (`bind_dob`),
/// never on the witness values. Binding adds three trace columns (the
/// `bind_active` selector + the two birth-year bytes) and four LogUp fractions
/// (the DOB-byte requires) to the age component.
fn layout(public: &PublicInput, bind_dob: bool) -> TreeLayout {
    let bounds = &public.bounds;
    let cal = calendar_log_size(bounds);
    let valid_day = valid_date_ranges()[0].domain.log_size();
    let day = Preprocessed::day_range().log_size();
    let month = Preprocessed::month_range().log_size();
    let year = Preprocessed::year_range(bounds).log_size();
    let witness = WitnessData::log_size();
    // The age component: 9 (+3 binding) trace columns and 5 (+4 binding) solo
    // LogUp fractions, each fraction four M31 (`SECURE_EXTENSION_DEGREE`).
    let age_trace_cols = if bind_dob { 12 } else { 9 };
    let age_interaction_cols = if bind_dob { 36 } else { 20 };
    TreeLayout {
        // Tree 0: calendar (2), valid-day (2), day/month/year delta tables (1 each).
        preprocessed: vec![cal, cal, valid_day, valid_day, day, month, year],
        // Tree 1: age witness columns + 5 multiplicity columns.
        trace: std::iter::repeat_n(witness, age_trace_cols)
            .chain([cal, valid_day, day, month, year])
            .collect(),
        // Tree 2: age LogUp fractions + cal (4) + valid_day (4) + each delta
        // table (4).
        interaction: std::iter::repeat_n(witness, age_interaction_cols)
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
    witness: Witness,
    preprocessed: Preprocessed,
    witness_data: WitnessData,
    /// Shared `Sha256Field` channel when the §6.6 DOB binding is wired. `None`
    /// for a standalone age proof (the module stays internally balanced).
    dob_binding: Option<SharedFieldRelation>,
    lookup_elements: Option<LookupElements>,
    claimed_sums: Vec<QM31>,
    components: Option<RangeCheckComponents>,
}

impl RangeCheckProver {
    pub fn new(public: &PublicInput, witness: &Witness) -> Self {
        let preprocessed = Preprocessed::new(&public.bounds);
        let witness_data = WitnessData::new(witness, &preprocessed, false);
        Self {
            public: *public,
            witness: witness.clone(),
            preprocessed,
            witness_data,
            dob_binding: None,
            lookup_elements: None,
            claimed_sums: Vec::new(),
            components: None,
        }
    }

    /// Bind the date of birth this module reasons about to the credential's
    /// signed DOB bytes (`docs/ROADMAP_E2E` §6.6): require the four DOB bytes on
    /// the shared `Sha256Field` channel `handle`, which the SHA module yields.
    /// Off by default; regenerates the witness with the binding columns. The
    /// matching [`RangeCheckVerifier`] must set the same handle.
    pub fn with_dob_binding(mut self, handle: SharedFieldRelation) -> Self {
        self.witness_data = WitnessData::new(&self.witness, &self.preprocessed, true);
        self.dob_binding = Some(handle);
        self
    }

    /// The drawn field relation, read from the shared handle once it is
    /// populated (after every module's `draw_relations`).
    fn dob_relation(&self) -> Option<FieldBytesRelation> {
        self.dob_binding.as_ref().map(|handle| handle.get())
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
        layout(&self.public, self.dob_binding.is_some())
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
            self.dob_relation(),
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
        let dob = self.dob_relation();
        let interaction = InteractionTraces::new(
            &self.witness_data,
            &self.preprocessed,
            self.relations(),
            dob.as_ref(),
        );
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
    dob_binding: Option<SharedFieldRelation>,
    lookup_elements: Option<LookupElements>,
    claimed_sums: Vec<QM31>,
    components: Option<RangeCheckComponents>,
}

impl RangeCheckVerifier {
    pub fn new(public: &PublicInput, claimed_sums: Vec<QM31>) -> Self {
        Self {
            public: *public,
            dob_binding: None,
            lookup_elements: None,
            claimed_sums,
            components: None,
        }
    }

    /// Match a [`RangeCheckProver::with_dob_binding`] proof: read the four DOB
    /// bytes from the same shared `Sha256Field` channel so the verifier rebuilds
    /// the bound component (the extra columns + the require terms).
    pub fn with_dob_binding(mut self, handle: SharedFieldRelation) -> Self {
        self.dob_binding = Some(handle);
        self
    }

    fn dob_relation(&self) -> Option<FieldBytesRelation> {
        self.dob_binding.as_ref().map(|handle| handle.get())
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
        layout(&self.public, self.dob_binding.is_some())
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
            self.dob_relation(),
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
    dob_binding: Option<FieldBytesRelation>,
) -> RangeCheckComponents {
    components(
        allocator,
        public,
        lookup_elements,
        dob_binding,
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

#[cfg(test)]
mod binding_tests {
    //! Isolated DOB↔credential binding (§6.6) tests: drive the bound age module
    //! against a *synthetic* field producer that plays SHA's role (yields the
    //! four DOB bytes on the shared `Sha256Field` channel). This exercises the
    //! whole bound path — the binding layout, the boolean/reconciliation
    //! constraints, and the cross-module balance — through a real
    //! `air_core::prove`/`verify`, without the (slow) P256 + SHA proof.

    use super::*;
    use crate::predicate::{PredicateProver, PredicateVerifier};
    use crate::{AgeRangeCheck, Date, DateOfBirth, PublicInput};
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

    /// The four DOB byte values for a `(year, month, day)` — the big-endian
    /// recomposition `Credential::encode` / the SHA field provider produce.
    fn dob_bytes(year: u32, month: u32, day: u32) -> [u32; 4] {
        [year >> 8, year & 0xFF, month, day]
    }

    /// A trace-less module that plays the SHA field provider: it draws the shared
    /// `Sha256Field` relation, shares it, and yields `−1/combine(DOB, i, byte)`
    /// for the four DOB bytes — exactly the term SHA contributes for the DOB
    /// window (`−is_first_block`, one yield per byte).
    struct DobProvider {
        bytes: [u32; 4],
        handle: SharedFieldRelation,
        relation: Option<FieldBytesRelation>,
    }

    impl DobProvider {
        fn new(bytes: [u32; 4], handle: SharedFieldRelation) -> Self {
            Self {
                bytes,
                handle,
                relation: None,
            }
        }
    }

    impl Air for DobProvider {
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
                        M31::from_u32_unchecked(field_id::DOB),
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

    impl AirProver for DobProvider {
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

    fn over_18_public() -> PublicInput {
        PublicInput::new(
            Date {
                year: 2026,
                month: 6,
                day: 17,
            },
            18,
        )
    }

    /// The bound age module's DOB requires cancel the producer's yields when the
    /// date of birth the module proves matches the bytes the producer yields —
    /// the proof verifies.
    #[test]
    fn bound_age_balances_against_matching_dob_yields() {
        let public = over_18_public();
        let dob = DateOfBirth(Date {
            year: 2000,
            month: 1,
            day: 1,
        });

        let handle = SharedFieldRelation::new();
        let mut provider = DobProvider::new(dob_bytes(2000, 1, 1), handle.clone());
        let mut age = AgeRangeCheck::new(PcsConfig::default())
            .prover(&public, &dob)
            .unwrap()
            .with_dob_binding(handle);

        let proof = {
            let mut modules: [&mut dyn AirProver; 2] = [&mut provider, &mut age];
            air_core::prove(&mut modules, PcsConfig::default()).expect("bound age proves")
        };
        let sums = age.claimed_sums();

        let handle_v = SharedFieldRelation::new();
        let mut provider_v = DobProvider::new(dob_bytes(2000, 1, 1), handle_v.clone());
        let mut age_v = AgeRangeCheck::new(PcsConfig::default())
            .verifier(&public, &sums)
            .unwrap()
            .with_dob_binding(handle_v);
        let mut modules: [&mut dyn Air; 2] = [&mut provider_v, &mut age_v];
        air_core::verify(&mut modules, &proof).expect("bound age verifies against matching yields");
    }

    /// When the producer yields a *different* date of birth than the age module
    /// proves (the credential↔predicate attack), the requires no longer cancel
    /// the yields — the global balance breaks and the verifier rejects. The
    /// prover still succeeds (each module is internally consistent; the imbalance
    /// is a verify-time check).
    #[test]
    fn bound_age_rejects_mismatched_dob_yields() {
        let public = over_18_public();
        // The age module proves an over-18 date of birth (2000-01-01)...
        let dob = DateOfBirth(Date {
            year: 2000,
            month: 1,
            day: 1,
        });
        // ...but the producer yields the bytes of a *different* (also over-18)
        // date — as if the signed credential held 1999-01-01.
        let credential_bytes = dob_bytes(1999, 1, 1);
        assert_ne!(credential_bytes, dob_bytes(2000, 1, 1));

        let handle = SharedFieldRelation::new();
        let mut provider = DobProvider::new(credential_bytes, handle.clone());
        let mut age = AgeRangeCheck::new(PcsConfig::default())
            .prover(&public, &dob)
            .unwrap()
            .with_dob_binding(handle);

        let proof = {
            let mut modules: [&mut dyn AirProver; 2] = [&mut provider, &mut age];
            air_core::prove(&mut modules, PcsConfig::default())
                .expect("prover accepts the mismatch")
        };
        let sums = age.claimed_sums();

        let handle_v = SharedFieldRelation::new();
        let mut provider_v = DobProvider::new(credential_bytes, handle_v.clone());
        let mut age_v = AgeRangeCheck::new(PcsConfig::default())
            .verifier(&public, &sums)
            .unwrap()
            .with_dob_binding(handle_v);
        let mut modules: [&mut dyn Air; 2] = [&mut provider_v, &mut age_v];
        assert!(
            air_core::verify(&mut modules, &proof).is_err(),
            "a DOB that differs from the yielded credential bytes must be rejected",
        );
    }
}
