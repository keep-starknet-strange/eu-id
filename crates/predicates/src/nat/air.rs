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
use crate::utils::validate_claim_masks;
use air_core::claim_mask::{ClaimMaskError, ClaimMaskTrace, SharedClaimMaskChallenge};
use air_core::relations::{FieldBytesRelation, SharedFieldRelation};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
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
/// input, the transcript-bound signed-array length, and whether the semantic
/// nationality binding is wired. The four base columns hold the value,
/// membership bit, and existential prefix state; binding adds two byte columns.
fn ordered_claim_mask_log_sizes(public: &PublicInput) -> Vec<u32> {
    vec![
        WitnessData::log_size(),
        crate::nat::table::blind_log_size(public),
    ]
}

fn layout(
    public: &PublicInput,
    nationality_count: usize,
    bind_nat: bool,
    claim_masks_enabled: bool,
) -> TreeLayout {
    debug_assert!((1..=256).contains(&nationality_count));
    // Class-D: the accepted-set table commits over the blinded (`log+1`) domain.
    let table_log_size = crate::nat::table::blind_log_size(public);
    let nat_log_size = WitnessData::log_size();
    // Membership plus the two prefix-transition sites give three logical
    // LogUp fractions; semantic byte binding adds two more.
    let nat_trace_cols = if bind_nat { 6 } else { 4 };
    let logical_nat_lookups =
        (if bind_nat { 5usize } else { 3 }) + usize::from(claim_masks_enabled);
    let nat_interaction_cols = logical_nat_lookups.div_ceil(2) * 4;
    let mut trace = Vec::new();
    trace.extend(std::iter::repeat_n(nat_log_size, nat_trace_cols));
    if claim_masks_enabled {
        trace.extend([nat_log_size; 4]);
    }
    trace.push(table_log_size);
    if claim_masks_enabled {
        trace.extend([table_log_size; 4]);
    }
    TreeLayout {
        // Tree 0: active-prefix metadata [active, row, first, last] plus the
        // Class-D blinded accepted-set table's [value, is_dummy] pair.
        preprocessed: std::iter::repeat_n(nat_log_size, 4)
            .chain([table_log_size, table_log_size])
            .collect(),
        // Tree 1: nationality/prefix witness columns plus table multiplicity.
        trace,
        // Tree 2: nationality LogUp fractions plus the table's gated fraction;
        // masking adds one unbatched secure column to the table.
        interaction: std::iter::repeat_n(nat_log_size, nat_interaction_cols)
            .chain(std::iter::repeat_n(
                table_log_size,
                4 + usize::from(claim_masks_enabled) * 4,
            ))
            .collect(),
    }
}

fn canonical_preprocessed(preprocessed: &Preprocessed) -> Vec<air_core::PreprocessedColumnEval> {
    let mut columns = preprocessed.active.clone();
    columns.extend(preprocessed.acceptable.clone());
    columns
}

/// Prover-side module: built from the public input and the witness.
pub struct NatProver {
    public: PublicInput,
    witness: Witness,
    nationality_count: usize,
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
        let nationality_count = witness.nationalities.len();
        Self {
            public: public.clone(),
            witness: witness.clone(),
            nationality_count,
            preprocessed: Preprocessed::new(public, nationality_count),
            witness_data: WitnessData::new(witness, public, false),
            nat_binding: None,
            lookup_elements: None,
            claim_masks: None,
            claim_mask_challenge: None,
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
        channel.mix_u64(self.nationality_count as u64);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.lookup_elements = Some(LookupElements::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        layout(
            &self.public,
            self.nationality_count,
            self.nat_binding.is_some(),
            self.claim_masks.is_some(),
        )
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        self.claimed_sums.clone()
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_column_ids(&self.public, self.nationality_count)
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
            self.nationality_count,
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
        columns.extend(self.preprocessed.active.clone());
        columns.extend(self.preprocessed.acceptable.clone());
        fingerprint_preprocessed_columns(
            "predicates::NatProver",
            &preprocessed_column_ids(&self.public, self.nationality_count),
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
    nationality_count: usize,
    nat_binding: Option<SharedFieldRelation>,
    lookup_elements: Option<LookupElements>,
    claim_mask_challenge: Option<SharedClaimMaskChallenge>,
    claimed_sums: Vec<QM31>,
    components: Option<NatComponents>,
}

impl NatVerifier {
    pub fn new(
        public: &PublicInput,
        nationality_count: usize,
        nat_claimed_sum: QM31,
        table_claimed_sum: QM31,
    ) -> Self {
        Self {
            public: public.clone(),
            nationality_count,
            nat_binding: None,
            lookup_elements: None,
            claim_mask_challenge: None,
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
        channel.mix_u64(self.nationality_count as u64);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.lookup_elements = Some(LookupElements::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        layout(
            &self.public,
            self.nationality_count,
            self.nat_binding.is_some(),
            self.claim_mask_challenge.is_some(),
        )
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        self.claimed_sums.clone()
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_column_ids(&self.public, self.nationality_count)
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(canonical_preprocessed(&Preprocessed::new(
            &self.public,
            self.nationality_count,
        )))
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(components(
            allocator,
            &self.public,
            self.nationality_count,
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
        (
            NationalityPredicate::new(PcsConfig::default()),
            PublicInput::new(vec![250, 276, 300]),
            PrivateInput {
                nationalities: vec![840, 276],
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
            .verifier_with_count(&public, private.nationalities.len(), &claimed_sums)
            .unwrap()
            .with_claim_masks(verifier_shared.clone());
        let mut verifier_anchor =
            ClaimMaskChallengeModule::new(verifier_shared, log_sizes.clone()).unwrap();
        verify(&mut [&mut verifier, &mut verifier_anchor], &proof).unwrap();

        let mut tampered_sums = claimed_sums.clone();
        tampered_sums[0] += QM31::one();
        let tampered_shared = SharedClaimMaskChallenge::new();
        let mut tampered = predicate
            .verifier_with_count(&public, private.nationalities.len(), &tampered_sums)
            .unwrap()
            .with_claim_masks(tampered_shared.clone());
        let mut tampered_anchor =
            ClaimMaskChallengeModule::new(tampered_shared, log_sizes.clone()).unwrap();
        assert!(verify(&mut [&mut tampered, &mut tampered_anchor], &proof,).is_err());

        let unmasked = predicate
            .verifier_with_count(&public, private.nationalities.len(), &claimed_sums)
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
        let mut provider = NatProvider::new(vec![nat_bytes(276)], handle.clone());
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
        let mut provider_v = NatProvider::new(vec![nat_bytes(276)], handle_v.clone());
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
        let mut provider = NatProvider::new(vec![credential_bytes], handle.clone());
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
            nationalities: vec![840, 276],
        };
        let signed_bytes = vec![nat_bytes(840), nat_bytes(276)];

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
            .verifier_with_count(&public, 2, &sums)
            .unwrap()
            .with_nat_binding(handle_v);
        let mut modules: [&mut dyn Air; 2] = [&mut provider_v, &mut nat_v];
        air_core::verify(&mut modules, &proof).expect("complete signed array verifies");

        let bad_handle = SharedFieldRelation::new();
        let mut bad_provider =
            NatProvider::new(vec![nat_bytes(276), nat_bytes(276)], bad_handle.clone());
        let mut bad_nat = NationalityPredicate::new(PcsConfig::default())
            .verifier_with_count(&public, 2, &sums)
            .unwrap()
            .with_nat_binding(bad_handle);
        let mut bad_modules: [&mut dyn Air; 2] = [&mut bad_provider, &mut bad_nat];
        assert!(
            air_core::verify(&mut bad_modules, &proof).is_err(),
            "changing a non-matching signed entry must break the indexed binding"
        );
    }
}
