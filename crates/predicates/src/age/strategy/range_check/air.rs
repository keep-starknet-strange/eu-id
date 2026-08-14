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
use crate::age::strategy::range_check::witness::{DobBindingMode, WitnessData};
use crate::age::types::{PublicInput, Witness};
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
use stwo::core::verifier::VerificationError;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::TraceLocationAllocator;

pub const RANGE_CHECK_CLAIM_COUNT: usize = 6;

/// Returns the column layout for the prover and verifier.
///
/// The layout depends on public bounds and `dob_binding_mode`.
/// It does not depend on witness values.
/// DOB binding adds mode-specific trace columns.
/// It also adds one LogUp fraction for each exposed DOB byte.
/// The age component pairs consecutive fractions.
fn ordered_claim_mask_log_sizes(public: &PublicInput) -> Vec<u32> {
    let bounds = &public.bounds;
    let cal = calendar_log_size(bounds);
    let valid_day = valid_date_ranges()[0].domain.log_size();
    let day = Preprocessed::day_range().blind_log_size();
    let month = Preprocessed::month_range().blind_log_size();
    let year = Preprocessed::year_range(bounds).blind_log_size();
    let witness = WitnessData::log_size();
    vec![witness, cal, valid_day, day, month, year]
}

fn layout(
    public: &PublicInput,
    dob_binding_mode: Option<DobBindingMode>,
    claim_masks_enabled: bool,
) -> TreeLayout {
    let [witness, cal, valid_day, day, month, year]: [u32; 6] =
        ordered_claim_mask_log_sizes(public)
            .try_into()
            .expect("age has exactly six claim-bearing components");
    // The age component has nine base trace columns.
    // DOB binding adds mode-specific columns.
    // Five base LogUp fractions precede one require for each exposed DOB byte.
    // Each secure column pairs two fractions and contains four M31 values.
    let age_trace_cols = 9 + dob_binding_mode
        .map(DobBindingMode::trace_columns)
        .unwrap_or(0);
    let logical_age_lookups = 5
        + dob_binding_mode
            .map(DobBindingMode::field_bytes)
            .unwrap_or(0)
        + usize::from(claim_masks_enabled);
    let age_interaction_cols = logical_age_lookups.div_ceil(2) * 4;
    let mut trace = Vec::new();
    trace.extend(std::iter::repeat_n(witness, age_trace_cols));
    if claim_masks_enabled {
        trace.extend([witness; 4]);
    }
    for log_size in [cal, valid_day, day, month, year] {
        trace.push(log_size);
        if claim_masks_enabled {
            trace.extend([log_size; 4]);
        }
    }
    let table_interaction_cols = 4 + usize::from(claim_masks_enabled) * 4;
    TreeLayout {
        // Tree 0: age `active` selector (over `witness` log), calendar (2),
        // valid-day value pair + dummy selector (3), and each Class-D delta
        // table's [value, is_dummy] pair.
        preprocessed: vec![
            witness, cal, cal, valid_day, valid_day, valid_day, day, day, month, month, year, year,
        ],
        // Tree 1: each component's ordinary columns followed immediately by
        // its four claim-mask coordinate columns when masking is enabled.
        trace,
        // Tree 2: the age LogUp fractions plus each table's ordinary secure
        // column. Masking adds one unbatched secure column to each table.
        interaction: std::iter::repeat_n(witness, age_interaction_cols)
            .chain(std::iter::repeat_n(cal, table_interaction_cols))
            .chain(std::iter::repeat_n(valid_day, table_interaction_cols))
            .chain(std::iter::repeat_n(day, table_interaction_cols))
            .chain(std::iter::repeat_n(month, table_interaction_cols))
            .chain(std::iter::repeat_n(year, table_interaction_cols))
            .collect(),
    }
}

fn canonical_preprocessed(preprocessed: &Preprocessed) -> Vec<air_core::PreprocessedColumnEval> {
    let mut columns = Vec::new();
    columns.extend(preprocessed.active_trace.clone());
    columns.extend(preprocessed.cal_trace.clone());
    columns.extend(preprocessed.valid_day_trace.clone());
    columns.extend(preprocessed.day_delta_table.clone());
    columns.extend(preprocessed.month_delta_table.clone());
    columns.extend(preprocessed.year_delta_table.clone());
    columns
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
    /// Shared `Sha256Field` channel when the DOB binding is wired. `None`
    /// for a standalone age proof (the module stays internally balanced).
    dob_binding: Option<SharedFieldRelation>,
    dob_binding_mode: Option<DobBindingMode>,
    lookup_elements: Option<LookupElements>,
    claim_masks: Option<Vec<ClaimMaskTrace>>,
    claim_mask_challenge: Option<SharedClaimMaskChallenge>,
    claimed_sums: Vec<QM31>,
    components: Option<RangeCheckComponents>,
}

impl RangeCheckProver {
    pub fn new(public: &PublicInput, witness: &Witness) -> Self {
        let preprocessed = Preprocessed::new(&public.bounds);
        let witness_data = WitnessData::new(witness, &preprocessed, None);
        Self {
            public: *public,
            witness: witness.clone(),
            preprocessed,
            witness_data,
            dob_binding: None,
            dob_binding_mode: None,
            lookup_elements: None,
            claim_masks: None,
            claim_mask_challenge: None,
            claimed_sums: Vec::new(),
            components: None,
        }
    }

    /// Binds a `YYYY-MM-DD` DOB window to the credential.
    ///
    /// The channel exposes ten ASCII bytes.
    /// Circuit constraints recompose them into the packed birth date.
    /// [`RangeCheckVerifier::with_text_dob_binding`] matches this layout.
    pub fn with_text_dob_binding(mut self, handle: SharedFieldRelation) -> Self {
        self.witness_data = WitnessData::new(
            &self.witness,
            &self.preprocessed,
            Some(DobBindingMode::Text),
        );
        self.dob_binding = Some(handle);
        self.dob_binding_mode = Some(DobBindingMode::Text);
        self
    }

    /// Component log sizes in the exact `[age, calendar, valid-day, day,
    /// month, year]` order used by the global claim-mask ring.
    pub fn ordered_claim_mask_log_sizes(&self) -> Vec<u32> {
        ordered_claim_mask_log_sizes(&self.public)
    }

    /// Attach the six ordered private mask traces allocated by the global ring.
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

    fn claim_mask_beta(&self) -> Option<QM31> {
        self.claim_mask_challenge.as_ref().map(|shared| {
            shared
                .require()
                .expect("claim-mask challenge anchor must follow all masked modules")
        })
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
        layout(
            &self.public,
            self.dob_binding_mode,
            self.claim_masks.is_some(),
        )
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        self.claimed_sums.clone()
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_column_ids(&self.public.bounds)
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(canonical_preprocessed(&self.preprocessed))
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(build_components(
            allocator,
            &self.public,
            self.relations().clone(),
            &self.claimed_sums,
            self.dob_relation(),
            self.dob_binding_mode,
            self.claim_mask_beta(),
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        component_refs(self.built_components())
    }
}

impl AirProver for RangeCheckProver {
    fn max_log_size(&self) -> u32 {
        self.preprocessed.cal_trace[0]
            .domain
            .log_size()
            .max(WitnessData::log_size())
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        self.preprocessed.extend_evals(tb);
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        let mut columns = Vec::new();
        columns.extend(self.preprocessed.active_trace.clone());
        columns.extend(self.preprocessed.cal_trace.clone());
        columns.extend(self.preprocessed.valid_day_trace.clone());
        columns.extend(self.preprocessed.day_delta_table.clone());
        columns.extend(self.preprocessed.month_delta_table.clone());
        columns.extend(self.preprocessed.year_delta_table.clone());
        fingerprint_preprocessed_columns(
            "predicates::RangeCheckProver",
            &preprocessed_column_ids(&self.public.bounds),
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
        for (ordinary, mask) in [
            (&self.witness_data.cal_mult_trace, &masks[1]),
            (&self.witness_data.valid_day_mult_trace, &masks[2]),
            (&self.witness_data.day_delta_mult_trace, &masks[3]),
            (&self.witness_data.month_delta_mult_trace, &masks[4]),
            (&self.witness_data.year_delta_mult_trace, &masks[5]),
        ] {
            tb.extend_evals(ordinary.clone());
            tb.extend_evals(mask.columns().to_vec());
        }
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let dob = self.dob_relation();
        let interaction = InteractionTraces::new(
            &self.witness_data,
            &self.preprocessed,
            self.relations(),
            dob.as_ref(),
            self.claim_masks.as_deref(),
            self.claim_mask_beta(),
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
    dob_binding_mode: Option<DobBindingMode>,
    lookup_elements: Option<LookupElements>,
    claim_mask_challenge: Option<SharedClaimMaskChallenge>,
    claimed_sums: Vec<QM31>,
    components: Option<RangeCheckComponents>,
}

impl RangeCheckVerifier {
    pub fn new(public: &PublicInput, claimed_sums: Vec<QM31>) -> Self {
        Self {
            public: *public,
            dob_binding: None,
            dob_binding_mode: None,
            lookup_elements: None,
            claim_mask_challenge: None,
            claimed_sums,
            components: None,
        }
    }

    /// Match a [`RangeCheckProver::with_text_dob_binding`] proof.
    pub fn with_text_dob_binding(mut self, handle: SharedFieldRelation) -> Self {
        self.dob_binding = Some(handle);
        self.dob_binding_mode = Some(DobBindingMode::Text);
        self
    }

    /// Component log sizes in the exact `[age, calendar, valid-day, day,
    /// month, year]` order expected by masked proofs.
    pub fn ordered_claim_mask_log_sizes(&self) -> Vec<u32> {
        ordered_claim_mask_log_sizes(&self.public)
    }

    /// Enable the fixed six-component masked layout for verification.
    pub fn with_claim_masks(mut self, challenge: SharedClaimMaskChallenge) -> Self {
        self.claim_mask_challenge = Some(challenge);
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

    fn claim_mask_beta(&self) -> Option<QM31> {
        self.claim_mask_challenge.as_ref().map(|shared| {
            shared
                .require()
                .expect("claim-mask challenge anchor must follow all masked modules")
        })
    }
}

impl Air for RangeCheckVerifier {
    fn validate_structure(&self) -> Result<(), VerificationError> {
        if self.claimed_sums.len() != RANGE_CHECK_CLAIM_COUNT {
            return Err(VerificationError::InvalidStructure(format!(
                "age range-check claim count is {}, expected {}",
                self.claimed_sums.len(),
                RANGE_CHECK_CLAIM_COUNT,
            )));
        }
        Ok(())
    }

    fn mix_public(&self, channel: &mut Blake2sChannel) {
        mix_public(&self.public, channel);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.lookup_elements = Some(LookupElements::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        layout(
            &self.public,
            self.dob_binding_mode,
            self.claim_mask_challenge.is_some(),
        )
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        self.claimed_sums.clone()
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_column_ids(&self.public.bounds)
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(canonical_preprocessed(&Preprocessed::new(
            &self.public.bounds,
        )))
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(build_components(
            allocator,
            &self.public,
            self.relations().clone(),
            &self.claimed_sums,
            self.dob_relation(),
            self.dob_binding_mode,
            self.claim_mask_beta(),
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
    dob_binding_mode: Option<DobBindingMode>,
    claim_mask_beta: Option<QM31>,
) -> RangeCheckComponents {
    components(
        allocator,
        public,
        lookup_elements,
        dob_binding,
        dob_binding_mode,
        claimed_sums[0],
        claimed_sums[1],
        claimed_sums[2],
        claimed_sums[3],
        claimed_sums[4],
        claimed_sums[5],
        claim_mask_beta,
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
mod claim_mask_tests {
    use super::*;
    use crate::age::types::{Date, DateOfBirth};
    use crate::predicate::{PredicateProver, PredicateVerifier};
    use crate::AgeRangeCheck;
    use air_core::claim_mask::{
        ClaimMaskChallengeModule, ClaimMaskError, ClaimMaskRing, CLAIM_MASK_MIN_LOG_SIZE,
    };
    use air_core::{prove, verify};
    use num_traits::One;
    use stwo::core::pcs::PcsConfig;

    fn inputs() -> (AgeRangeCheck, PublicInput, DateOfBirth) {
        (
            AgeRangeCheck::new(PcsConfig::default()),
            PublicInput::new(
                Date {
                    year: 2025,
                    month: 7,
                    day: 1,
                },
                18,
            ),
            DateOfBirth(Date {
                year: 2000,
                month: 2,
                day: 29,
            }),
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
    fn verifier_rejects_a_seventh_claimed_sum() {
        let (predicate, public, _) = inputs();
        let extra_claims = vec![QM31::from_u32_unchecked(0, 0, 0, 0); 7];
        assert!(predicate.verifier(&public, &extra_claims).is_err());

        let verifier = RangeCheckVerifier::new(&public, extra_claims);
        assert!(verifier.validate_structure().is_err());
    }

    #[test]
    fn masked_age_round_trip_rejects_claim_and_layout_tampering() {
        let (predicate, public, private) = inputs();
        let base_prover = predicate.prover(&public, &private).unwrap();
        let log_sizes = base_prover.ordered_claim_mask_log_sizes();
        assert_eq!(log_sizes.len(), 6);
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
            .verifier(&public, &claimed_sums)
            .unwrap()
            .with_claim_masks(verifier_shared.clone());
        let mut verifier_anchor =
            ClaimMaskChallengeModule::new(verifier_shared, log_sizes.clone()).unwrap();
        verify(&mut [&mut verifier, &mut verifier_anchor], &proof).unwrap();

        let mut tampered_sums = claimed_sums.clone();
        tampered_sums[0] += QM31::one();
        let tampered_shared = SharedClaimMaskChallenge::new();
        let mut tampered = predicate
            .verifier(&public, &tampered_sums)
            .unwrap()
            .with_claim_masks(tampered_shared.clone());
        let mut tampered_anchor =
            ClaimMaskChallengeModule::new(tampered_shared, log_sizes.clone()).unwrap();
        assert!(verify(&mut [&mut tampered, &mut tampered_anchor], &proof,).is_err());

        let unmasked = predicate.verifier(&public, &claimed_sums).unwrap().layout();
        let masked = verifier.layout();
        assert_eq!(masked.trace.len(), unmasked.trace.len() + 6 * 4);
        assert!(masked.interaction.len() > unmasked.interaction.len());
    }

    #[test]
    fn masked_age_rejects_missing_and_out_of_order_traces() {
        let (predicate, public, private) = inputs();
        let prover = predicate.prover(&public, &private).unwrap();
        let log_sizes = prover.ordered_claim_mask_log_sizes();

        let mut missing = take_masks(&log_sizes);
        missing.pop();
        let error = predicate
            .prover(&public, &private)
            .unwrap()
            .with_claim_masks(missing, SharedClaimMaskChallenge::new())
            .err()
            .unwrap();
        assert!(matches!(error, ClaimMaskError::Exhausted { .. }));

        let mut out_of_order = take_masks(&log_sizes);
        out_of_order.swap(0, 1);
        let error = predicate
            .prover(&public, &private)
            .unwrap()
            .with_claim_masks(out_of_order, SharedClaimMaskChallenge::new())
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
    //! Tests the DOB-to-credential binding with a synthetic SHA field provider.
    //! The provider yields four DOB bytes on `Sha256Field`.
    //! Real `air_core` proof operations check the layout, constraints, and balance.

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

    fn dob_text_bytes(year: u32, month: u32, day: u32) -> Vec<u32> {
        format!("{year:04}-{month:02}-{day:02}")
            .bytes()
            .map(u32::from)
            .collect()
    }

    /// Synthetic SHA field provider without a trace.
    ///
    /// It draws and shares the `Sha256Field` relation.
    /// It yields `−1/combine(DOB, i, byte)` once for each DOB byte.
    struct DobProvider {
        bytes: Vec<u32>,
        handle: SharedFieldRelation,
        relation: Option<FieldBytesRelation>,
    }

    impl DobProvider {
        fn new(bytes: impl Into<Vec<u32>>, handle: SharedFieldRelation) -> Self {
            Self {
                bytes: bytes.into(),
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

    /// Confirms that a different producer DOB breaks the global balance.
    ///
    /// Each module remains internally consistent.
    /// Thus, the verifier detects the mismatch after proof generation.
    #[test]
    fn bound_age_rejects_mismatched_text_dob_yields() {
        let public = over_18_public();
        // The age module proves an over-18 date of birth (2000-01-01)...
        let dob = DateOfBirth(Date {
            year: 2000,
            month: 1,
            day: 1,
        });
        // ...but the producer yields the bytes of a *different* (also over-18)
        // date — as if the signed credential held 1999-01-01.
        let credential_bytes = dob_text_bytes(1999, 1, 1);
        assert_ne!(credential_bytes, dob_text_bytes(2000, 1, 1));

        let handle = SharedFieldRelation::new();
        let mut provider = DobProvider::new(credential_bytes.clone(), handle.clone());
        let mut age = AgeRangeCheck::new(PcsConfig::default())
            .prover(&public, &dob)
            .unwrap()
            .with_text_dob_binding(handle);

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
            .with_text_dob_binding(handle_v);
        let mut modules: [&mut dyn Air; 2] = [&mut provider_v, &mut age_v];
        assert!(
            air_core::verify(&mut modules, &proof).is_err(),
            "a DOB that differs from the yielded credential bytes must be rejected",
        );
    }

    /// The text-form DOB binding balances when the ten `YYYY-MM-DD` bytes the
    /// producer yields recompose to the date the age module proves.
    #[test]
    fn bound_age_balances_against_matching_text_dob_yields() {
        let public = PublicInput::new(
            Date {
                year: 2026,
                month: 7,
                day: 3,
            },
            18,
        );
        let dob = DateOfBirth(Date {
            year: 1990,
            month: 7,
            day: 15,
        });

        let handle = SharedFieldRelation::new();
        let mut provider = DobProvider::new(dob_text_bytes(1990, 7, 15), handle.clone());
        let mut age = AgeRangeCheck::new(PcsConfig::default())
            .prover(&public, &dob)
            .unwrap()
            .with_text_dob_binding(handle);

        let proof = {
            let mut modules: [&mut dyn AirProver; 2] = [&mut provider, &mut age];
            air_core::prove(&mut modules, PcsConfig::default()).expect("text-bound age proves")
        };
        let sums = age.claimed_sums();

        let handle_v = SharedFieldRelation::new();
        let mut provider_v = DobProvider::new(dob_text_bytes(1990, 7, 15), handle_v.clone());
        let mut age_v = AgeRangeCheck::new(PcsConfig::default())
            .verifier(&public, &sums)
            .unwrap()
            .with_text_dob_binding(handle_v);
        let mut modules: [&mut dyn Air; 2] = [&mut provider_v, &mut age_v];
        air_core::verify(&mut modules, &proof).expect("text DOB verifies against matching yields");
    }

    /// A corrupted digit byte (a non-`0..9` ASCII character) breaks the require
    /// balance — the verifier rejects.
    #[test]
    fn bound_age_rejects_text_dob_digit_corruption() {
        let public = over_18_public();
        let dob = DateOfBirth(Date {
            year: 2000,
            month: 1,
            day: 1,
        });
        let mut credential_bytes = dob_text_bytes(2000, 1, 1);
        credential_bytes[2] = b'A' as u32;

        let handle = SharedFieldRelation::new();
        let mut provider = DobProvider::new(credential_bytes.clone(), handle.clone());
        let mut age = AgeRangeCheck::new(PcsConfig::default())
            .prover(&public, &dob)
            .unwrap()
            .with_text_dob_binding(handle);
        let proof = {
            let mut modules: [&mut dyn AirProver; 2] = [&mut provider, &mut age];
            air_core::prove(&mut modules, PcsConfig::default()).expect("prover accepts imbalance")
        };
        let sums = age.claimed_sums();

        let handle_v = SharedFieldRelation::new();
        let mut provider_v = DobProvider::new(credential_bytes, handle_v.clone());
        let mut age_v = AgeRangeCheck::new(PcsConfig::default())
            .verifier(&public, &sums)
            .unwrap()
            .with_text_dob_binding(handle_v);
        let mut modules: [&mut dyn Air; 2] = [&mut provider_v, &mut age_v];
        assert!(air_core::verify(&mut modules, &proof).is_err());
    }

    /// A wrong separator byte (not `-` at position 4) breaks the require balance
    /// — the verifier rejects.
    #[test]
    fn bound_age_rejects_text_dob_separator_corruption() {
        let public = over_18_public();
        let dob = DateOfBirth(Date {
            year: 2000,
            month: 1,
            day: 1,
        });
        let mut credential_bytes = dob_text_bytes(2000, 1, 1);
        credential_bytes[4] = b'/' as u32;

        let handle = SharedFieldRelation::new();
        let mut provider = DobProvider::new(credential_bytes.clone(), handle.clone());
        let mut age = AgeRangeCheck::new(PcsConfig::default())
            .prover(&public, &dob)
            .unwrap()
            .with_text_dob_binding(handle);
        let proof = {
            let mut modules: [&mut dyn AirProver; 2] = [&mut provider, &mut age];
            air_core::prove(&mut modules, PcsConfig::default()).expect("prover accepts imbalance")
        };
        let sums = age.claimed_sums();

        let handle_v = SharedFieldRelation::new();
        let mut provider_v = DobProvider::new(credential_bytes, handle_v.clone());
        let mut age_v = AgeRangeCheck::new(PcsConfig::default())
            .verifier(&public, &sums)
            .unwrap()
            .with_text_dob_binding(handle_v);
        let mut modules: [&mut dyn Air; 2] = [&mut provider_v, &mut age_v];
        assert!(air_core::verify(&mut modules, &proof).is_err());
    }
}
