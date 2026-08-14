//! Wraps the nationality predicate as a `combiner` proving module.
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
use crate::utils::validate_claim_masks;
use air_core::claim_mask::{ClaimMaskError, ClaimMaskTrace, SharedClaimMaskChallenge};
use air_core::relations::{FieldBytesRelation, SharedFieldRelation};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
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

/// Returns the column layout for the prover and verifier.
///
/// The layout depends on public input and whether nationality binding is active.
/// Six base columns hold private prefix selectors, value, membership, and state.
/// Nationality binding adds two byte columns.
fn ordered_claim_mask_log_sizes(public: &PublicInput) -> Vec<u32> {
    vec![
        WitnessData::log_size(),
        crate::nat::table::blind_log_size(public),
    ]
}

fn layout(public: &PublicInput, bind_nat: bool, claim_masks_enabled: bool) -> TreeLayout {
    // Class-D: the accepted-set table commits over the blinded (`log+1`) domain.
    let table_log_size = crate::nat::table::blind_log_size(public);
    let nat_log_size = WitnessData::log_size();
    // Policy membership, signed-code validity, and two prefix-transition sites
    // give four logical LogUp fractions. Semantic byte binding adds two more.
    let nat_trace_cols = if bind_nat { 8 } else { 6 };
    let logical_nat_lookups =
        (if bind_nat { 6usize } else { 4 }) + usize::from(claim_masks_enabled);
    let nat_interaction_cols = logical_nat_lookups.div_ceil(2) * 4;
    let mut trace = Vec::new();
    trace.extend(std::iter::repeat_n(nat_log_size, nat_trace_cols));
    if claim_masks_enabled {
        trace.extend([nat_log_size; 4]);
    }
    trace.extend([table_log_size; 2]);
    if claim_masks_enabled {
        trace.extend([table_log_size; 4]);
    }
    TreeLayout {
        // Tree 0: fixed prefix metadata [allowed, row, first], the public
        // accepted-set table, and the fixed signed-code table.
        preprocessed: std::iter::repeat_n(nat_log_size, 3)
            .chain([table_log_size; 4])
            .collect(),
        // Tree 1: nationality/prefix witness columns plus table multiplicity.
        trace,
        // Tree 2: nationality LogUp fractions plus the table's gated fraction.
        // Masking adds one unbatched secure column to the table.
        interaction: std::iter::repeat_n(nat_log_size, nat_interaction_cols)
            .chain(std::iter::repeat_n(
                table_log_size,
                4 + usize::from(claim_masks_enabled) * 4,
            ))
            .collect(),
    }
}

fn canonical_preprocessed(preprocessed: &Preprocessed) -> Vec<air_core::PreprocessedColumnEval> {
    let mut columns = preprocessed.prefix.clone();
    columns.extend(preprocessed.acceptable.clone());
    columns.extend(preprocessed.signed_valid.clone());
    columns
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
    claim_masks: Option<Vec<ClaimMaskTrace>>,
    claim_mask_challenge: Option<SharedClaimMaskChallenge>,
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
            claim_masks: None,
            claim_mask_challenge: None,
            claimed_sums: Vec::new(),
            components: None,
        }
    }

    /// Binds the proved nationality to two signed credential bytes.
    ///
    /// The SHA module yields these bytes on the shared `Sha256Field` channel.
    /// This method rebuilds the witness with binding columns.
    /// The matching [`NatVerifier`] must use the same handle.
    pub fn with_nat_binding(mut self, handle: SharedFieldRelation) -> Self {
        self.witness_data = WitnessData::new(&self.witness, &self.public, true);
        self.nat_binding = Some(handle);
        self
    }

    /// Component log sizes in exact `[nationality, accepted-table]` order.
    pub fn ordered_claim_mask_log_sizes(&self) -> Vec<u32> {
        ordered_claim_mask_log_sizes(&self.public)
    }

    /// Attach the two ordered private traces allocated by the global mask ring.
    pub fn with_claim_masks(
        mut self,
        masks: Vec<ClaimMaskTrace>,
        challenge: SharedClaimMaskChallenge,
    ) -> Result<Self, ClaimMaskError> {
        validate_claim_masks(&masks, &self.ordered_claim_mask_log_sizes())?;
        self.claim_masks = Some(masks);
        self.claim_mask_challenge = Some(challenge);
        Ok(self)
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

    fn claim_mask_beta(&self) -> Option<QM31> {
        self.claim_mask_challenge.as_ref().map(|shared| {
            shared
                .require()
                .expect("claim-mask challenge anchor must follow all masked modules")
        })
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
        layout(
            &self.public,
            self.nat_binding.is_some(),
            self.claim_masks.is_some(),
        )
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        self.claimed_sums.clone()
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_column_ids(&self.public)
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(canonical_preprocessed(&self.preprocessed))
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(components(
            allocator,
            &self.public,
            self.relations().clone(),
            self.nat_relation(),
            self.claimed_sums[0],
            self.claimed_sums[1],
            self.claim_mask_beta(),
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        component_refs(self.built_components())
    }
}

impl AirProver for NatProver {
    fn max_log_size(&self) -> u32 {
        WitnessData::log_size().max(crate::nat::table::blind_log_size(&self.public))
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        self.preprocessed.extend_evals(tb);
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        let mut columns = Vec::new();
        columns.extend(self.preprocessed.prefix.clone());
        columns.extend(self.preprocessed.acceptable.clone());
        columns.extend(self.preprocessed.signed_valid.clone());
        fingerprint_preprocessed_columns(
            "predicates::NatProver",
            &preprocessed_column_ids(&self.public),
            &columns,
        )
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let Some(masks) = self.claim_masks.as_ref() else {
            self.witness_data.extend_evals(tb);
            return;
        };
        tb.extend_evals(self.witness_data.witness_trace.clone());
        tb.extend_evals(masks[0].columns().to_vec());
        tb.extend_evals(self.witness_data.table_mult_trace.clone());
        tb.extend_evals(masks[1].columns().to_vec());
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let nat_field = self.nat_relation();
        let interaction = InteractionTraces::new(
            &self.witness_data,
            &self.preprocessed,
            self.relations(),
            nat_field.as_ref(),
            self.claim_masks.as_deref(),
            self.claim_mask_beta(),
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
    claim_mask_challenge: Option<SharedClaimMaskChallenge>,
    claimed_sums: Vec<QM31>,
    components: Option<NatComponents>,
}

impl NatVerifier {
    pub fn new(public: &PublicInput, nat_claimed_sum: QM31, table_claimed_sum: QM31) -> Self {
        Self {
            public: public.clone(),
            nat_binding: None,
            lookup_elements: None,
            claim_mask_challenge: None,
            claimed_sums: vec![nat_claimed_sum, table_claimed_sum],
            components: None,
        }
    }

    /// Matches a [`NatProver::with_nat_binding`] proof.
    ///
    /// Reads two nationality bytes from the shared `Sha256Field` channel.
    /// The verifier then rebuilds the bound component.
    pub fn with_nat_binding(mut self, handle: SharedFieldRelation) -> Self {
        self.nat_binding = Some(handle);
        self
    }

    /// Component log sizes in exact `[nationality, accepted-table]` order.
    pub fn ordered_claim_mask_log_sizes(&self) -> Vec<u32> {
        ordered_claim_mask_log_sizes(&self.public)
    }

    /// Enable the fixed two-component masked layout for verification.
    pub fn with_claim_masks(mut self, challenge: SharedClaimMaskChallenge) -> Self {
        self.claim_mask_challenge = Some(challenge);
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

    fn claim_mask_beta(&self) -> Option<QM31> {
        self.claim_mask_challenge.as_ref().map(|shared| {
            shared
                .require()
                .expect("claim-mask challenge anchor must follow all masked modules")
        })
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
        layout(
            &self.public,
            self.nat_binding.is_some(),
            self.claim_mask_challenge.is_some(),
        )
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        self.claimed_sums.clone()
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_column_ids(&self.public)
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(canonical_preprocessed(&Preprocessed::new(&self.public)))
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(components(
            allocator,
            &self.public,
            self.relations().clone(),
            self.nat_relation(),
            self.claimed_sums[0],
            self.claimed_sums[1],
            self.claim_mask_beta(),
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        component_refs(self.built_components())
    }
}

#[cfg(test)]
mod claim_mask_tests {
    use super::*;
    use crate::nat::types::PrivateInput;
    use crate::nat::NationalityPredicate;
    use crate::predicate::PredicateProver;
    use air_core::claim_mask::{
        ClaimMaskChallengeModule, ClaimMaskError, ClaimMaskRing, CLAIM_MASK_MIN_LOG_SIZE,
    };
    use air_core::{prove, verify};
    use num_traits::One;
    use stwo::core::pcs::PcsConfig;

    fn inputs() -> (NationalityPredicate, PublicInput, PrivateInput) {
        let code = crate::nat::nationalities::pack_alpha2;
        (
            NationalityPredicate::new(PcsConfig::default()),
            PublicInput::new(vec![code(*b"FR"), code(*b"DE"), code(*b"GR")]),
            PrivateInput {
                nationalities: vec![code(*b"US"), code(*b"DE")],
            },
        )
    }

    fn take_masks(log_sizes: &[u32]) -> Vec<ClaimMaskTrace> {
        let mut ring = ClaimMaskRing::new(log_sizes).unwrap();
        let masks = log_sizes
            .iter()
            .map(|&log_size| ring.take(log_size).unwrap())
            .collect();
        ring.finish().unwrap();
        masks
    }

    #[test]
    fn masked_nationality_round_trip_rejects_claim_and_layout_tampering() {
        let (predicate, public, private) = inputs();
        let base_prover = predicate.prover(&public, &private).unwrap();
        let log_sizes = base_prover.ordered_claim_mask_log_sizes();
        assert_eq!(log_sizes.len(), 2);
        assert!(log_sizes
            .iter()
            .all(|&log_size| log_size >= CLAIM_MASK_MIN_LOG_SIZE));

        let prover_shared = SharedClaimMaskChallenge::new();
        let mut prover = base_prover
            .with_claim_masks(take_masks(&log_sizes), prover_shared.clone())
            .unwrap();
        let mut prover_anchor =
            ClaimMaskChallengeModule::new(prover_shared, log_sizes.clone()).unwrap();
        let proof = prove(&mut [&mut prover, &mut prover_anchor], PcsConfig::default()).unwrap();
        let claimed_sums = prover.claimed_sums();

        let verifier_shared = SharedClaimMaskChallenge::new();
        let mut verifier = predicate
            .verifier_for_private_prefix(&public, &claimed_sums)
            .unwrap()
            .with_claim_masks(verifier_shared.clone());
        let mut verifier_anchor =
            ClaimMaskChallengeModule::new(verifier_shared, log_sizes.clone()).unwrap();
        verify(&mut [&mut verifier, &mut verifier_anchor], &proof).unwrap();

        let mut tampered_sums = claimed_sums.clone();
        tampered_sums[0] += QM31::one();
        let tampered_shared = SharedClaimMaskChallenge::new();
        let mut tampered = predicate
            .verifier_for_private_prefix(&public, &tampered_sums)
            .unwrap()
            .with_claim_masks(tampered_shared.clone());
        let mut tampered_anchor =
            ClaimMaskChallengeModule::new(tampered_shared, log_sizes.clone()).unwrap();
        assert!(verify(&mut [&mut tampered, &mut tampered_anchor], &proof,).is_err());

        let unmasked = predicate
            .verifier_for_private_prefix(&public, &claimed_sums)
            .unwrap()
            .layout();
        let masked = verifier.layout();
        assert_eq!(masked.trace.len(), unmasked.trace.len() + 2 * 4);
        assert!(masked.interaction.len() > unmasked.interaction.len());
    }

    #[test]
    fn masked_nationality_rejects_missing_and_wrong_log_traces() {
        let (predicate, public, private) = inputs();
        let log_sizes = predicate
            .prover(&public, &private)
            .unwrap()
            .ordered_claim_mask_log_sizes();

        let mut missing = take_masks(&log_sizes);
        missing.pop();
        let error = predicate
            .prover(&public, &private)
            .unwrap()
            .with_claim_masks(missing, SharedClaimMaskChallenge::new())
            .err()
            .unwrap();
        assert!(matches!(error, ClaimMaskError::Exhausted { .. }));

        let wrong_log_sizes = [log_sizes[0] + 1, log_sizes[1]];
        let error = predicate
            .prover(&public, &private)
            .unwrap()
            .with_claim_masks(
                take_masks(&wrong_log_sizes),
                SharedClaimMaskChallenge::new(),
            )
            .err()
            .unwrap();
        assert!(matches!(
            error,
            ClaimMaskError::LogSizeOutOfOrder { index: 0, .. }
        ));
    }
}

#[cfg(test)]
mod signed_validity_tests {
    use super::*;
    use crate::nat::nationalities::pack_alpha2;
    use crate::nat::table::gen_signed_valid_multiplicity_column;
    use crate::nat::types::Witness;
    use crate::nat::NationalityPredicate;
    use air_core::{prove, verify};
    use stwo::core::pcs::PcsConfig;

    #[test]
    fn omitted_or_wrong_signed_validity_multiplicity_is_rejected() {
        let de = pack_alpha2(*b"DE");
        let public = PublicInput::new(vec![de]);
        let witness = Witness {
            public: public.clone(),
            nationalities: vec![de],
            accepted: vec![true],
            accepted_rows: vec![Some(0)],
        };

        for supplied_codes in [Vec::new(), vec![de, de]] {
            let mut prover = NatProver::new(&public, &witness);
            prover.witness_data.table_mult_trace[1] =
                gen_signed_valid_multiplicity_column(&public, &supplied_codes);
            let proof = prove(&mut [&mut prover], PcsConfig::default()).unwrap();
            let mut verifier = NationalityPredicate::new(PcsConfig::default())
                .verifier_for_private_prefix(&public, &prover.claimed_sums())
                .unwrap();
            assert!(verify(&mut [&mut verifier], &proof).is_err());
        }
    }
}

#[cfg(test)]
mod binding_tests {
    //! Tests nationality binding with a synthetic SHA field provider.
    //! The provider yields two nationality bytes on `Sha256Field`.
    //! Real `air_core` proof operations check the layout, constraints, and balance.

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

    fn alpha2(code: &[u8; 2]) -> u32 {
        crate::nat::nationalities::pack_alpha2(*code)
    }

    /// Synthetic SHA field provider without a trace.
    ///
    /// It draws and shares the `Sha256Field` relation.
    /// It yields `−1/combine(NATIONALITY, i, byte)` for each nationality byte.
    struct NatProvider {
        bytes: Vec<[u32; 2]>,
        handle: SharedFieldRelation,
        relation: Option<FieldBytesRelation>,
    }

    impl NatProvider {
        fn new(bytes: Vec<[u32; 2]>, handle: SharedFieldRelation) -> Self {
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
                .flat_map(|(row, bytes)| {
                    bytes.iter().enumerate().map(move |(offset, &byte)| {
                        let values = [
                            M31::from_u32_unchecked(field_id::NATIONALITY),
                            M31::from_u32_unchecked((2 * row + offset) as u32),
                            M31::from_u32_unchecked(byte),
                        ];
                        let denom: SecureField =
                            <FieldBytesRelation as Relation<M31, SecureField>>::combine(
                                relation, &values,
                            );
                        -SecureField::from(M31::one()) / denom
                    })
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

    fn eu_set() -> PublicInput {
        PublicInput::new(vec![alpha2(b"DE"), alpha2(b"FR")])
    }

    fn private(code: u32) -> PrivateInput {
        PrivateInput {
            nationalities: vec![code],
        }
    }

    /// Confirms that matching nationality requires and yields balance.
    #[test]
    fn bound_nat_balances_against_matching_nat_yields() {
        let public = eu_set();

        let handle = SharedFieldRelation::new();
        let mut provider = NatProvider::new(vec![nat_bytes(alpha2(b"DE"))], handle.clone());
        let mut nat = NationalityPredicate::new(PcsConfig::default())
            .prover(&public, &private(alpha2(b"DE")))
            .unwrap()
            .with_nat_binding(handle);

        let proof = {
            let mut modules: [&mut dyn AirProver; 2] = [&mut provider, &mut nat];
            air_core::prove(&mut modules, PcsConfig::default()).expect("bound nat proves")
        };
        let sums = nat.claimed_sums();

        let handle_v = SharedFieldRelation::new();
        let mut provider_v = NatProvider::new(vec![nat_bytes(alpha2(b"DE"))], handle_v.clone());
        let mut nat_v = NationalityPredicate::new(PcsConfig::default())
            .verifier(&public, &sums)
            .unwrap()
            .with_nat_binding(handle_v);
        let mut modules: [&mut dyn Air; 2] = [&mut provider_v, &mut nat_v];
        air_core::verify(&mut modules, &proof).expect("bound nat verifies against matching yields");
    }

    /// Confirms that a different producer nationality breaks the global balance.
    ///
    /// Each module remains internally consistent.
    /// Both codes remain in the accepted set.
    /// Thus, only the binding detects the swap.
    #[test]
    fn bound_nat_rejects_mismatched_nat_yields() {
        let public = eu_set();
        // The nat module proves membership for DE.
        // The producer instead yields FR.
        // This simulates another accepted nationality in the signed credential.
        let credential_bytes = nat_bytes(alpha2(b"FR"));
        assert_ne!(credential_bytes, nat_bytes(alpha2(b"DE")));

        let handle = SharedFieldRelation::new();
        let mut provider = NatProvider::new(vec![credential_bytes], handle.clone());
        let mut nat = NationalityPredicate::new(PcsConfig::default())
            .prover(&public, &private(alpha2(b"DE")))
            .unwrap()
            .with_nat_binding(handle);

        let proof = {
            let mut modules: [&mut dyn AirProver; 2] = [&mut provider, &mut nat];
            air_core::prove(&mut modules, PcsConfig::default())
                .expect("prover accepts the mismatch")
        };
        let sums = nat.claimed_sums();

        let handle_v = SharedFieldRelation::new();
        let mut provider_v = NatProvider::new(vec![credential_bytes], handle_v.clone());
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

    #[test]
    fn bound_nat_consumes_every_signed_array_entry() {
        let public = eu_set();
        let private = PrivateInput {
            nationalities: vec![alpha2(b"US"), alpha2(b"DE")],
        };
        let signed_bytes = vec![nat_bytes(alpha2(b"US")), nat_bytes(alpha2(b"DE"))];

        let handle = SharedFieldRelation::new();
        let mut provider = NatProvider::new(signed_bytes.clone(), handle.clone());
        let mut nat = NationalityPredicate::new(PcsConfig::default())
            .prover(&public, &private)
            .unwrap()
            .with_nat_binding(handle);
        let proof = {
            let mut modules: [&mut dyn AirProver; 2] = [&mut provider, &mut nat];
            air_core::prove(&mut modules, PcsConfig::default()).expect("array proof")
        };
        let sums = nat.claimed_sums();

        let handle_v = SharedFieldRelation::new();
        let mut provider_v = NatProvider::new(signed_bytes, handle_v.clone());
        let mut nat_v = NationalityPredicate::new(PcsConfig::default())
            .verifier_for_private_prefix(&public, &sums)
            .unwrap()
            .with_nat_binding(handle_v);
        let mut modules: [&mut dyn Air; 2] = [&mut provider_v, &mut nat_v];
        air_core::verify(&mut modules, &proof).expect("complete signed array verifies");

        let bad_handle = SharedFieldRelation::new();
        let mut bad_provider = NatProvider::new(
            vec![nat_bytes(alpha2(b"DE")), nat_bytes(alpha2(b"DE"))],
            bad_handle.clone(),
        );
        let mut bad_nat = NationalityPredicate::new(PcsConfig::default())
            .verifier_for_private_prefix(&public, &sums)
            .unwrap()
            .with_nat_binding(bad_handle);
        let mut bad_modules: [&mut dyn Air; 2] = [&mut bad_provider, &mut bad_nat];
        assert!(
            air_core::verify(&mut bad_modules, &proof).is_err(),
            "changing a non-matching signed entry must break the indexed binding"
        );

        for (produced, label) in [
            (vec![nat_bytes(alpha2(b"US"))], "shorter producer"),
            (
                vec![
                    nat_bytes(alpha2(b"US")),
                    nat_bytes(alpha2(b"DE")),
                    nat_bytes(alpha2(b"FR")),
                ],
                "longer producer",
            ),
        ] {
            let length_handle = SharedFieldRelation::new();
            let mut length_provider = NatProvider::new(produced, length_handle.clone());
            let mut length_nat = NationalityPredicate::new(PcsConfig::default())
                .verifier_for_private_prefix(&public, &sums)
                .unwrap()
                .with_nat_binding(length_handle);
            let mut length_modules: [&mut dyn Air; 2] = [&mut length_provider, &mut length_nat];
            assert!(
                air_core::verify(&mut length_modules, &proof).is_err(),
                "{label} must break the private-prefix relation balance"
            );
        }
    }
}
