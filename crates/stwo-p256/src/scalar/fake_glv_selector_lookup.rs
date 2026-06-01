use std::collections::BTreeMap;

use num_traits::{One, Zero};
use stwo::{
    core::{
        air::Component,
        channel::Channel,
        fields::{m31::M31, qm31::SecureField},
        pcs::{CommitmentSchemeVerifier, PcsConfig, TreeVec},
        poly::circle::CanonicCoset,
        proof::StarkProof,
        utils::{bit_reverse_index, coset_index_to_circle_domain_index},
        verifier::verify,
        ColumnVec,
    },
    prover::{
        backend::simd::{
            column::BaseColumn,
            m31::{PackedM31, LOG_N_LANES},
            qm31::{PackedQM31, PackedSecureField},
            SimdBackend,
        },
        backend::BackendForChannel,
        poly::{circle::CircleEvaluation, circle::PolyOps, BitReversedOrder},
        prove, CommitmentSchemeProver, ComponentProver,
    },
};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator,
};

use super::fake_glv_selector::{FakeGlvSelectorClaim, FAKE_GLV_SELECTOR_CHUNKS};

relation!(Selector4x4Relation, 3);
relation!(Selector16DecodeRelation, 3);
relation!(FinalSelectorRelation, 4);

pub type SelectorColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;

pub const SELECTOR4X4_LOG_SIZE: u32 = 4;
pub const SELECTOR16_DECODE_LOG_SIZE: u32 = 4;
/// Four real final-selector rows, padded to one SIMD vector for LogUp trace generation.
pub const FINAL_SELECTOR_LOG_SIZE: u32 = LOG_N_LANES;

const SELECTOR4X4_A_COLUMN: &str = "p256_selector4x4_a";
const SELECTOR4X4_B_COLUMN: &str = "p256_selector4x4_b";
const SELECTOR4X4_SELECTOR_COLUMN: &str = "p256_selector4x4_selector";
const SELECTOR16_SELECTOR_COLUMN: &str = "p256_selector16_selector";
const SELECTOR16_BASE_INDEX_COLUMN: &str = "p256_selector16_base_index";
const SELECTOR16_NEG_BIT_COLUMN: &str = "p256_selector16_neg_bit";
const FINAL_SELECTOR_S1_MSB_COLUMN: &str = "p256_final_selector_s1_msb";
const FINAL_SELECTOR_S2_MSB_COLUMN: &str = "p256_final_selector_s2_msb";
const FINAL_SELECTOR_VALUE_COLUMN: &str = "p256_final_selector_value";
const FINAL_SELECTOR_INIT_BASE_COLUMN: &str = "p256_final_selector_init_base";

#[derive(Clone, Debug)]
pub struct FakeGlvSelectorLookupRelations {
    pub selector4x4: Selector4x4Relation,
    pub selector16_decode: Selector16DecodeRelation,
    pub final_selector: FinalSelectorRelation,
}

#[derive(Clone, Debug)]
pub struct Selector4x4ProviderClaim;

impl Selector4x4ProviderClaim {
    pub fn log_size(&self) -> u32 {
        SELECTOR4X4_LOG_SIZE
    }

    pub fn preprocessed_column_ids(&self) -> [PreProcessedColumnId; 3] {
        selector4x4_column_ids()
    }

    pub fn gen_preprocessed_columns(&self) -> [SelectorColumnEval; 3] {
        let table = selector4x4_table();
        [
            selector_column(SELECTOR4X4_LOG_SIZE, table.map(|entry| entry.a)),
            selector_column(SELECTOR4X4_LOG_SIZE, table.map(|entry| entry.b)),
            selector_column(SELECTOR4X4_LOG_SIZE, table.map(|entry| entry.selector)),
        ]
    }

    pub fn gen_multiplicity_trace(&self, requests: &SelectorLookupRequests) -> SelectorColumnEval {
        let mut multiplicity = [M31::zero(); 16];
        for entry in &requests.selector4x4 {
            entry.verify().expect("selector4x4 request must be valid");
            multiplicity[entry.selector.0 as usize] += M31::one();
        }
        selector_column(SELECTOR4X4_LOG_SIZE, multiplicity)
    }
}

#[derive(Clone, Debug)]
pub struct Selector16DecodeProviderClaim;

impl Selector16DecodeProviderClaim {
    pub fn log_size(&self) -> u32 {
        SELECTOR16_DECODE_LOG_SIZE
    }

    pub fn preprocessed_column_ids(&self) -> [PreProcessedColumnId; 3] {
        selector16_decode_column_ids()
    }

    pub fn gen_preprocessed_columns(&self) -> [SelectorColumnEval; 3] {
        let table = selector16_decode_table();
        [
            selector_column(
                SELECTOR16_DECODE_LOG_SIZE,
                table.map(|entry| entry.selector),
            ),
            selector_column(
                SELECTOR16_DECODE_LOG_SIZE,
                table.map(|entry| entry.base_index),
            ),
            selector_column(SELECTOR16_DECODE_LOG_SIZE, table.map(|entry| entry.neg_bit)),
        ]
    }

    pub fn gen_multiplicity_trace(&self, requests: &SelectorLookupRequests) -> SelectorColumnEval {
        let mut multiplicity = [M31::zero(); 16];
        for entry in &requests.selector16_decode {
            entry
                .verify()
                .expect("selector16 decode request must be valid");
            multiplicity[entry.selector.0 as usize] += M31::one();
        }
        selector_column(SELECTOR16_DECODE_LOG_SIZE, multiplicity)
    }
}

#[derive(Clone, Debug)]
pub struct FinalSelectorProviderClaim;

impl FinalSelectorProviderClaim {
    pub fn log_size(&self) -> u32 {
        FINAL_SELECTOR_LOG_SIZE
    }

    pub fn preprocessed_column_ids(&self) -> [PreProcessedColumnId; 4] {
        final_selector_column_ids()
    }

    pub fn gen_preprocessed_columns(&self) -> [SelectorColumnEval; 4] {
        let table = padded_final_selector_table();
        [
            selector_column(FINAL_SELECTOR_LOG_SIZE, table.map(|entry| entry.s1_msb)),
            selector_column(FINAL_SELECTOR_LOG_SIZE, table.map(|entry| entry.s2_msb)),
            selector_column(
                FINAL_SELECTOR_LOG_SIZE,
                table.map(|entry| entry.selector_final),
            ),
            selector_column(
                FINAL_SELECTOR_LOG_SIZE,
                table.map(|entry| entry.init_base_index),
            ),
        ]
    }

    pub fn gen_multiplicity_trace(&self, requests: &SelectorLookupRequests) -> SelectorColumnEval {
        let mut multiplicity = [M31::zero(); 1usize << FINAL_SELECTOR_LOG_SIZE];
        for entry in &requests.final_selector {
            entry
                .verify()
                .expect("final selector request must be valid");
            multiplicity[final_selector_row_index(*entry)] += M31::one();
        }
        selector_column(FINAL_SELECTOR_LOG_SIZE, multiplicity)
    }
}

#[derive(Clone, Debug)]
pub struct Selector4x4Eval {
    pub relation: Selector4x4Relation,
}

impl FrameworkEval for Selector4x4Eval {
    fn log_size(&self) -> u32 {
        SELECTOR4X4_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        SELECTOR4X4_LOG_SIZE + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let [a_id, b_id, selector_id] = selector4x4_column_ids();
        let a = eval.get_preprocessed_column(a_id);
        let b = eval.get_preprocessed_column(b_id);
        let selector = eval.get_preprocessed_column(selector_id);
        let multiplicity = eval.next_trace_mask();
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(multiplicity),
            &[a, b, selector],
        ));
        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type Selector4x4Component = FrameworkComponent<Selector4x4Eval>;

#[derive(Clone, Debug)]
pub struct Selector16DecodeEval {
    pub relation: Selector16DecodeRelation,
}

impl FrameworkEval for Selector16DecodeEval {
    fn log_size(&self) -> u32 {
        SELECTOR16_DECODE_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        SELECTOR16_DECODE_LOG_SIZE + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let [selector_id, base_index_id, neg_bit_id] = selector16_decode_column_ids();
        let selector = eval.get_preprocessed_column(selector_id);
        let base_index = eval.get_preprocessed_column(base_index_id);
        let neg_bit = eval.get_preprocessed_column(neg_bit_id);
        let multiplicity = eval.next_trace_mask();
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(multiplicity),
            &[selector, base_index, neg_bit],
        ));
        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type Selector16DecodeComponent = FrameworkComponent<Selector16DecodeEval>;

#[derive(Clone, Debug)]
pub struct FinalSelectorEval {
    pub relation: FinalSelectorRelation,
}

impl FrameworkEval for FinalSelectorEval {
    fn log_size(&self) -> u32 {
        FINAL_SELECTOR_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        FINAL_SELECTOR_LOG_SIZE + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let [s1_msb_id, s2_msb_id, selector_id, init_base_id] = final_selector_column_ids();
        let s1_msb = eval.get_preprocessed_column(s1_msb_id);
        let s2_msb = eval.get_preprocessed_column(s2_msb_id);
        let selector_final = eval.get_preprocessed_column(selector_id);
        let init_base_index = eval.get_preprocessed_column(init_base_id);
        let multiplicity = eval.next_trace_mask();
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(multiplicity),
            &[s1_msb, s2_msb, selector_final, init_base_index],
        ));
        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type FinalSelectorComponent = FrameworkComponent<FinalSelectorEval>;

#[derive(Clone, Debug, Default)]
pub struct SelectorProviderInteractionClaim {
    pub selector4x4: SelectorLookupInteractionClaim,
    pub selector16_decode: SelectorLookupInteractionClaim,
    pub final_selector: SelectorLookupInteractionClaim,
}

impl SelectorProviderInteractionClaim {
    pub fn zero() -> Self {
        Self::default()
    }

    pub fn claimed_sum(&self) -> SecureField {
        self.selector4x4.claimed_sum
            + self.selector16_decode.claimed_sum
            + self.final_selector.claimed_sum
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[
            self.selector4x4.claimed_sum,
            self.selector16_decode.claimed_sum,
            self.final_selector.claimed_sum,
        ]);
    }

    pub fn gen_interaction_traces(
        requests: &SelectorLookupRequests,
        relations: &FakeGlvSelectorLookupRelations,
    ) -> (ColumnVec<SelectorColumnEval>, Self) {
        let selector4x4_claim = Selector4x4ProviderClaim;
        let selector16_claim = Selector16DecodeProviderClaim;
        let final_selector_claim = FinalSelectorProviderClaim;

        let selector4x4_preprocessed = selector4x4_claim.gen_preprocessed_columns();
        let selector16_preprocessed = selector16_claim.gen_preprocessed_columns();
        let final_selector_preprocessed = final_selector_claim.gen_preprocessed_columns();

        let (selector4x4_trace, selector4x4_interaction) = gen_provider_interaction_trace_3(
            &selector4x4_claim.gen_multiplicity_trace(requests),
            &selector4x4_preprocessed,
            &relations.selector4x4,
        );
        let (selector16_trace, selector16_interaction) = gen_provider_interaction_trace_3(
            &selector16_claim.gen_multiplicity_trace(requests),
            &selector16_preprocessed,
            &relations.selector16_decode,
        );
        let (final_selector_trace, final_selector_interaction) = gen_provider_interaction_trace_4(
            &final_selector_claim.gen_multiplicity_trace(requests),
            &final_selector_preprocessed,
            &relations.final_selector,
        );

        let mut trace = Vec::new();
        trace.extend(selector4x4_trace);
        trace.extend(selector16_trace);
        trace.extend(final_selector_trace);

        (
            trace,
            Self {
                selector4x4: selector4x4_interaction,
                selector16_decode: selector16_interaction,
                final_selector: final_selector_interaction,
            },
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SelectorLookupProviderProofClaim;

impl SelectorLookupProviderProofClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(SELECTOR4X4_LOG_SIZE as u64);
        channel.mix_u64(SELECTOR16_DECODE_LOG_SIZE as u64);
        channel.mix_u64(FINAL_SELECTOR_LOG_SIZE as u64);
    }

    pub fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut allocator = TraceLocationAllocator::default();
        let _ = SelectorLookupProviderComponents::new(
            &mut allocator,
            &SelectorProviderInteractionClaim::zero(),
            &FakeGlvSelectorLookupRelations::dummy(),
        );
        allocator.preprocessed_columns().clone()
    }

    pub fn trace_log_degree_bounds(&self, ids: &[PreProcessedColumnId]) -> TreeVec<ColumnVec<u32>> {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = SelectorLookupProviderComponents::new(
            &mut allocator,
            &SelectorProviderInteractionClaim::zero(),
            &FakeGlvSelectorLookupRelations::dummy(),
        );
        components.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self, ids: &[PreProcessedColumnId]) -> u32 {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = SelectorLookupProviderComponents::new(
            &mut allocator,
            &SelectorProviderInteractionClaim::zero(),
            &FakeGlvSelectorLookupRelations::dummy(),
        );
        components.max_constraint_log_degree_bound()
    }
}

#[derive(Clone, Debug)]
pub struct SelectorLookupProviderProof<H: stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted>
{
    pub claim: SelectorLookupProviderProofClaim,
    pub interaction_claim: SelectorProviderInteractionClaim,
    pub stark_proof: StarkProof<H>,
}

pub struct SelectorLookupProviderComponents {
    pub selector4x4: Selector4x4Component,
    pub selector16_decode: Selector16DecodeComponent,
    pub final_selector: FinalSelectorComponent,
}

impl SelectorLookupProviderComponents {
    pub fn new(
        allocator: &mut TraceLocationAllocator,
        interaction_claim: &SelectorProviderInteractionClaim,
        relations: &FakeGlvSelectorLookupRelations,
    ) -> Self {
        Self {
            selector4x4: Selector4x4Component::new(
                allocator,
                Selector4x4Eval {
                    relation: relations.selector4x4.clone(),
                },
                interaction_claim.selector4x4.claimed_sum,
            ),
            selector16_decode: Selector16DecodeComponent::new(
                allocator,
                Selector16DecodeEval {
                    relation: relations.selector16_decode.clone(),
                },
                interaction_claim.selector16_decode.claimed_sum,
            ),
            final_selector: FinalSelectorComponent::new(
                allocator,
                FinalSelectorEval {
                    relation: relations.final_selector.clone(),
                },
                interaction_claim.final_selector.claimed_sum,
            ),
        }
    }

    pub fn components(&self) -> Vec<&dyn Component> {
        vec![
            &self.selector4x4 as &dyn Component,
            &self.selector16_decode as &dyn Component,
            &self.final_selector as &dyn Component,
        ]
    }

    pub fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            &self.selector4x4 as &dyn ComponentProver<SimdBackend>,
            &self.selector16_decode as &dyn ComponentProver<SimdBackend>,
            &self.final_selector as &dyn ComponentProver<SimdBackend>,
        ]
    }

    pub fn trace_log_degree_bounds(&self) -> TreeVec<ColumnVec<u32>> {
        TreeVec::concat_cols(
            self.components()
                .into_iter()
                .map(|component| component.trace_log_degree_bounds()),
        )
    }

    pub fn max_constraint_log_degree_bound(&self) -> u32 {
        self.components()
            .into_iter()
            .map(|component| component.max_constraint_log_degree_bound())
            .max()
            .unwrap_or(0)
    }
}

pub fn gen_selector_lookup_provider_preprocessed_trace() -> ColumnVec<SelectorColumnEval> {
    let selector4x4 = Selector4x4ProviderClaim;
    let selector16 = Selector16DecodeProviderClaim;
    let final_selector = FinalSelectorProviderClaim;
    let mut trace = Vec::new();
    trace.extend(selector4x4.gen_preprocessed_columns());
    trace.extend(selector16.gen_preprocessed_columns());
    trace.extend(final_selector.gen_preprocessed_columns());
    trace
}

pub fn gen_selector_lookup_provider_base_trace(
    requests: &SelectorLookupRequests,
) -> ColumnVec<SelectorColumnEval> {
    let selector4x4 = Selector4x4ProviderClaim;
    let selector16 = Selector16DecodeProviderClaim;
    let final_selector = FinalSelectorProviderClaim;
    vec![
        selector4x4.gen_multiplicity_trace(requests),
        selector16.gen_multiplicity_trace(requests),
        final_selector.gen_multiplicity_trace(requests),
    ]
}

pub fn prove_selector_lookup_provider_proof_slice<MC: stwo::core::channel::MerkleChannel>(
    requests: &SelectorLookupRequests,
    config: PcsConfig,
) -> Result<SelectorLookupProviderProof<MC::H>, SelectorLookupError>
where
    SimdBackend: BackendForChannel<MC>,
{
    requests.verify()?;
    let claim = SelectorLookupProviderProofClaim;
    let ids = claim.preprocessed_column_ids();
    let max_constraint_log_degree_bound = claim.max_constraint_log_degree_bound(&ids);
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(
            config
                .lifting_log_size
                .unwrap_or(max_constraint_log_degree_bound + config.fri_config.log_blowup_factor),
        )
        .circle_domain()
        .half_coset,
    );

    let mut channel = MC::C::default();
    let mut commitment_scheme = CommitmentSchemeProver::<SimdBackend, MC>::new(config, &twiddles);
    commitment_scheme.set_store_polynomials_coefficients();

    let preprocessed = gen_selector_lookup_provider_preprocessed_trace();
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(preprocessed);
    tree_builder.commit(&mut channel);

    claim.mix_into(&mut channel);
    let base = gen_selector_lookup_provider_base_trace(requests);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(base);
    tree_builder.commit(&mut channel);

    let relations = FakeGlvSelectorLookupRelations::draw(&mut channel);
    let (interaction, interaction_claim) =
        SelectorProviderInteractionClaim::gen_interaction_traces(requests, &relations);
    if interaction_claim.claimed_sum() + selector_lookup_consumer_claimed_sum(requests, &relations)
        != secure_zero()
    {
        return Err(SelectorLookupError::RelationImbalance {
            relation: "SelectorLookups",
        });
    }
    interaction_claim.mix_into(&mut channel);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction);
    tree_builder.commit(&mut channel);

    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let components =
        SelectorLookupProviderComponents::new(&mut allocator, &interaction_claim, &relations);
    assert_eq!(
        commitment_scheme
            .polynomials()
            .as_cols_ref()
            .map_cols(|column| column.evals.domain.log_size() - config.fri_config.log_blowup_factor)
            .0,
        components.trace_log_degree_bounds().0
    );
    let stark_proof = prove(
        &components.component_provers(),
        &mut channel,
        commitment_scheme,
    )
    .map_err(|_| SelectorLookupError::ProofLayer)?;

    Ok(SelectorLookupProviderProof {
        claim,
        interaction_claim,
        stark_proof,
    })
}

pub fn verify_selector_lookup_provider_proof_slice<MC: stwo::core::channel::MerkleChannel>(
    proof: SelectorLookupProviderProof<MC::H>,
) -> Result<(), SelectorLookupError> {
    let SelectorLookupProviderProof {
        claim,
        interaction_claim,
        stark_proof,
    } = proof;

    let ids = claim.preprocessed_column_ids();
    let log_degree_bounds = claim.trace_log_degree_bounds(&ids);
    let mut channel = MC::C::default();
    let commitment_scheme = &mut CommitmentSchemeVerifier::<MC>::new(stark_proof.config);

    commitment_scheme.commit(
        stark_proof.commitments[0],
        &log_degree_bounds[0],
        &mut channel,
    );

    claim.mix_into(&mut channel);
    commitment_scheme.commit(
        stark_proof.commitments[1],
        &log_degree_bounds[1],
        &mut channel,
    );

    let relations = FakeGlvSelectorLookupRelations::draw(&mut channel);

    interaction_claim.mix_into(&mut channel);
    commitment_scheme.commit(
        stark_proof.commitments[2],
        &log_degree_bounds[2],
        &mut channel,
    );

    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let components =
        SelectorLookupProviderComponents::new(&mut allocator, &interaction_claim, &relations);
    verify(
        &components.components(),
        &mut channel,
        commitment_scheme,
        stark_proof,
    )
    .map_err(|_| SelectorLookupError::ProofLayer)
}

impl FakeGlvSelectorLookupRelations {
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            selector4x4: Selector4x4Relation::draw(channel),
            selector16_decode: Selector16DecodeRelation::draw(channel),
            final_selector: FinalSelectorRelation::draw(channel),
        }
    }

    pub fn dummy() -> Self {
        Self {
            selector4x4: Selector4x4Relation::dummy(),
            selector16_decode: Selector16DecodeRelation::dummy(),
            final_selector: FinalSelectorRelation::dummy(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Selector4x4Entry {
    pub a: M31,
    pub b: M31,
    pub selector: M31,
}

impl Selector4x4Entry {
    pub fn new(a: u32, b: u32) -> Self {
        Self {
            a: M31::from_u32_unchecked(a),
            b: M31::from_u32_unchecked(b),
            selector: M31::from_u32_unchecked(a + 4 * b),
        }
    }

    pub fn values(self) -> [M31; 3] {
        [self.a, self.b, self.selector]
    }

    pub fn verify(self) -> Result<(), SelectorLookupError> {
        if self.a.0 >= 4 || self.b.0 >= 4 || self.selector.0 != self.a.0 + 4 * self.b.0 {
            return Err(SelectorLookupError::InvalidSelector4x4(self));
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Selector16DecodeEntry {
    pub selector: M31,
    pub base_index: M31,
    pub neg_bit: M31,
}

impl Selector16DecodeEntry {
    pub fn from_selector(selector: M31) -> Result<Self, SelectorLookupError> {
        let (base_index, neg_bit) = decode_selector16(selector.0)
            .ok_or(SelectorLookupError::Selector16OutOfRange { selector })?;
        Ok(Self {
            selector,
            base_index: M31::from_u32_unchecked(base_index),
            neg_bit: M31::from_u32_unchecked(neg_bit),
        })
    }

    pub fn values(self) -> [M31; 3] {
        [self.selector, self.base_index, self.neg_bit]
    }

    pub fn verify(self) -> Result<(), SelectorLookupError> {
        let expected = Self::from_selector(self.selector)?;
        if self != expected {
            return Err(SelectorLookupError::InvalidSelector16Decode {
                actual: self,
                expected,
            });
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FinalSelectorEntry {
    pub s1_msb: M31,
    pub s2_msb: M31,
    pub selector_final: M31,
    pub init_base_index: M31,
}

impl FinalSelectorEntry {
    pub fn new(s1_msb: M31, s2_msb: M31) -> Self {
        Self {
            s1_msb,
            s2_msb,
            selector_final: M31::from_u32_unchecked(5 + s1_msb.0 + 4 * s2_msb.0),
            init_base_index: M31::from_u32_unchecked(2 + s1_msb.0 + 4 * s2_msb.0),
        }
    }

    pub fn values(self) -> [M31; 4] {
        [
            self.s1_msb,
            self.s2_msb,
            self.selector_final,
            self.init_base_index,
        ]
    }

    pub fn verify(self) -> Result<(), SelectorLookupError> {
        if self.s1_msb.0 > 1 || self.s2_msb.0 > 1 {
            return Err(SelectorLookupError::InvalidFinalSelector(self));
        }
        let expected = Self::new(self.s1_msb, self.s2_msb);
        if self != expected {
            return Err(SelectorLookupError::InvalidFinalSelector(self));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SelectorLookupRequests {
    pub selector4x4: Vec<Selector4x4Entry>,
    pub selector16_decode: Vec<Selector16DecodeEntry>,
    pub final_selector: Vec<FinalSelectorEntry>,
}

impl SelectorLookupRequests {
    pub fn from_selector_claim(claim: &FakeGlvSelectorClaim) -> Result<Self, SelectorLookupError> {
        let mut requests = Self::default();
        for row in &claim.rows {
            if row.cert_active.0 == 0 {
                continue;
            }

            for selector in row.selectors {
                let a = selector.0 % 4;
                let b = selector.0 / 4;
                let selector4x4 = Selector4x4Entry {
                    a: M31::from_u32_unchecked(a),
                    b: M31::from_u32_unchecked(b),
                    selector,
                };
                selector4x4.verify()?;
                requests.selector4x4.push(selector4x4);
                requests
                    .selector16_decode
                    .push(Selector16DecodeEntry::from_selector(selector)?);
            }

            let final_selector = FinalSelectorEntry {
                s1_msb: row.s1_msb,
                s2_msb: row.s2_msb,
                selector_final: row.selector_final,
                init_base_index: row.init_base_index,
            };
            final_selector.verify()?;
            requests.final_selector.push(final_selector);
        }
        Ok(requests)
    }

    pub fn verify(&self) -> Result<(), SelectorLookupError> {
        for entry in &self.selector4x4 {
            entry.verify()?;
        }
        for entry in &self.selector16_decode {
            entry.verify()?;
        }
        for entry in &self.final_selector {
            entry.verify()?;
        }
        Ok(())
    }

    pub fn expected_selector4x4_uses(&self) -> usize {
        self.final_selector.len() * FAKE_GLV_SELECTOR_CHUNKS
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SelectorLookupAudit {
    selector4x4: BTreeMap<[u32; 3], i64>,
    selector16_decode: BTreeMap<[u32; 3], i64>,
    final_selector: BTreeMap<[u32; 4], i64>,
}

impl SelectorLookupAudit {
    pub fn balanced_for_requests(
        requests: &SelectorLookupRequests,
    ) -> Result<Self, SelectorLookupError> {
        requests.verify()?;
        let mut audit = Self::default();
        audit.add_consumers(requests);
        audit.add_multiplicity_providers(requests);
        Ok(audit)
    }

    pub fn add_consumers(&mut self, requests: &SelectorLookupRequests) {
        for entry in &requests.selector4x4 {
            *self
                .selector4x4
                .entry(entry.values().map(|value| value.0))
                .or_default() += 1;
        }
        for entry in &requests.selector16_decode {
            *self
                .selector16_decode
                .entry(entry.values().map(|value| value.0))
                .or_default() += 1;
        }
        for entry in &requests.final_selector {
            *self
                .final_selector
                .entry(entry.values().map(|value| value.0))
                .or_default() += 1;
        }
    }

    pub fn add_multiplicity_providers(&mut self, requests: &SelectorLookupRequests) {
        for entry in &requests.selector4x4 {
            *self
                .selector4x4
                .entry(entry.values().map(|value| value.0))
                .or_default() -= 1;
        }
        for entry in &requests.selector16_decode {
            *self
                .selector16_decode
                .entry(entry.values().map(|value| value.0))
                .or_default() -= 1;
        }
        for entry in &requests.final_selector {
            *self
                .final_selector
                .entry(entry.values().map(|value| value.0))
                .or_default() -= 1;
        }
    }

    pub fn is_balanced(&self) -> bool {
        self.selector4x4.values().all(|count| *count == 0)
            && self.selector16_decode.values().all(|count| *count == 0)
            && self.final_selector.values().all(|count| *count == 0)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SelectorLookupInteractionClaim {
    pub claimed_sum: SecureField,
}

impl Default for SelectorLookupInteractionClaim {
    fn default() -> Self {
        Self {
            claimed_sum: SecureField::from(M31::from_u32_unchecked(0)),
        }
    }
}

pub fn selector_lookup_consumer_claimed_sum(
    requests: &SelectorLookupRequests,
    relations: &FakeGlvSelectorLookupRelations,
) -> SecureField {
    selector_lookup_claimed_sum(requests, relations, 1)
}

pub fn selector_lookup_provider_claimed_sum(
    requests: &SelectorLookupRequests,
    relations: &FakeGlvSelectorLookupRelations,
) -> SecureField {
    selector_lookup_claimed_sum(requests, relations, -1)
}

fn selector_lookup_claimed_sum(
    requests: &SelectorLookupRequests,
    relations: &FakeGlvSelectorLookupRelations,
    numerator: i64,
) -> SecureField {
    requests
        .selector4x4
        .iter()
        .map(|entry| selector_fraction(&relations.selector4x4, &entry.values(), numerator))
        .sum::<SecureField>()
        + requests
            .selector16_decode
            .iter()
            .map(|entry| {
                selector_fraction(&relations.selector16_decode, &entry.values(), numerator)
            })
            .sum::<SecureField>()
        + requests
            .final_selector
            .iter()
            .map(|entry| selector_fraction(&relations.final_selector, &entry.values(), numerator))
            .sum::<SecureField>()
}

fn selector_fraction<R, const N: usize>(
    relation: &R,
    values: &[M31; N],
    numerator: i64,
) -> SecureField
where
    R: Relation<M31, SecureField>,
{
    let denominator: SecureField = relation.combine(values);
    secure_from_i64(numerator) / denominator
}

fn gen_provider_interaction_trace_3<R: Relation<PackedM31, PackedSecureField>>(
    multiplicity: &SelectorColumnEval,
    values: &[SelectorColumnEval; 3],
    relation: &R,
) -> (
    ColumnVec<SelectorColumnEval>,
    SelectorLookupInteractionClaim,
) {
    assert_provider_domains(multiplicity, values);
    let log_size = multiplicity.domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let denominator: PackedQM31 = relation.combine(&[
            values[0].data[vec_row],
            values[1].data[vec_row],
            values[2].data[vec_row],
        ]);
        let numerator = -PackedQM31::from(multiplicity.data[vec_row]);
        col.write_frac(vec_row, numerator, denominator);
    }
    col.finalize_col();
    let (trace, claimed_sum) = logup.finalize_last();
    (trace, SelectorLookupInteractionClaim { claimed_sum })
}

fn gen_provider_interaction_trace_4<R: Relation<PackedM31, PackedSecureField>>(
    multiplicity: &SelectorColumnEval,
    values: &[SelectorColumnEval; 4],
    relation: &R,
) -> (
    ColumnVec<SelectorColumnEval>,
    SelectorLookupInteractionClaim,
) {
    assert_provider_domains(multiplicity, values);
    let log_size = multiplicity.domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let denominator: PackedQM31 = relation.combine(&[
            values[0].data[vec_row],
            values[1].data[vec_row],
            values[2].data[vec_row],
            values[3].data[vec_row],
        ]);
        let numerator = -PackedQM31::from(multiplicity.data[vec_row]);
        col.write_frac(vec_row, numerator, denominator);
    }
    col.finalize_col();
    let (trace, claimed_sum) = logup.finalize_last();
    (trace, SelectorLookupInteractionClaim { claimed_sum })
}

fn assert_provider_domains<const N: usize>(
    multiplicity: &SelectorColumnEval,
    values: &[SelectorColumnEval; N],
) {
    for value in values {
        assert_eq!(
            multiplicity.domain.log_size(),
            value.domain.log_size(),
            "selector provider columns must share log_size",
        );
    }
}

pub fn add_selector4x4_consumer<E: EvalAtRow>(
    eval: &mut E,
    relation: &Selector4x4Relation,
    gate: E::F,
    entry: &[E::F; 3],
) {
    eval.add_to_relation(RelationEntry::new(relation, E::EF::from(gate), entry));
}

pub fn add_selector16_decode_consumer<E: EvalAtRow>(
    eval: &mut E,
    relation: &Selector16DecodeRelation,
    gate: E::F,
    entry: &[E::F; 3],
) {
    eval.add_to_relation(RelationEntry::new(relation, E::EF::from(gate), entry));
}

pub fn add_final_selector_consumer<E: EvalAtRow>(
    eval: &mut E,
    relation: &FinalSelectorRelation,
    gate: E::F,
    entry: &[E::F; 4],
) {
    eval.add_to_relation(RelationEntry::new(relation, E::EF::from(gate), entry));
}

pub fn selector4x4_table() -> [Selector4x4Entry; 16] {
    core::array::from_fn(|selector| {
        let selector = selector as u32;
        Selector4x4Entry {
            a: M31::from_u32_unchecked(selector % 4),
            b: M31::from_u32_unchecked(selector / 4),
            selector: M31::from_u32_unchecked(selector),
        }
    })
}

pub fn selector4x4_column_ids() -> [PreProcessedColumnId; 3] {
    [
        column_id(SELECTOR4X4_A_COLUMN),
        column_id(SELECTOR4X4_B_COLUMN),
        column_id(SELECTOR4X4_SELECTOR_COLUMN),
    ]
}

pub fn selector16_decode_table() -> [Selector16DecodeEntry; 16] {
    core::array::from_fn(|selector| {
        Selector16DecodeEntry::from_selector(M31::from_u32_unchecked(selector as u32))
            .expect("selector table entry is valid")
    })
}

pub fn selector16_decode_column_ids() -> [PreProcessedColumnId; 3] {
    [
        column_id(SELECTOR16_SELECTOR_COLUMN),
        column_id(SELECTOR16_BASE_INDEX_COLUMN),
        column_id(SELECTOR16_NEG_BIT_COLUMN),
    ]
}

pub fn final_selector_table() -> [FinalSelectorEntry; 4] {
    [
        FinalSelectorEntry::new(M31::from_u32_unchecked(0), M31::from_u32_unchecked(0)),
        FinalSelectorEntry::new(M31::from_u32_unchecked(1), M31::from_u32_unchecked(0)),
        FinalSelectorEntry::new(M31::from_u32_unchecked(0), M31::from_u32_unchecked(1)),
        FinalSelectorEntry::new(M31::from_u32_unchecked(1), M31::from_u32_unchecked(1)),
    ]
}

fn padded_final_selector_table() -> [FinalSelectorEntry; 1usize << FINAL_SELECTOR_LOG_SIZE] {
    let real = final_selector_table();
    core::array::from_fn(|index| {
        if index < real.len() {
            real[index]
        } else {
            FinalSelectorEntry {
                s1_msb: M31::zero(),
                s2_msb: M31::zero(),
                selector_final: M31::zero(),
                init_base_index: M31::zero(),
            }
        }
    })
}

pub fn final_selector_column_ids() -> [PreProcessedColumnId; 4] {
    [
        column_id(FINAL_SELECTOR_S1_MSB_COLUMN),
        column_id(FINAL_SELECTOR_S2_MSB_COLUMN),
        column_id(FINAL_SELECTOR_VALUE_COLUMN),
        column_id(FINAL_SELECTOR_INIT_BASE_COLUMN),
    ]
}

fn column_id(id: &str) -> PreProcessedColumnId {
    PreProcessedColumnId { id: id.into() }
}

fn selector_column<const N: usize>(log_size: u32, values: [M31; N]) -> SelectorColumnEval {
    assert_eq!(N, 1usize << log_size, "selector table size mismatch");
    let mut ordered = vec![M31::zero(); N];
    for (coset_index, value) in values.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        );
        ordered[row] = value;
    }
    CircleEvaluation::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(ordered),
    )
}

fn final_selector_row_index(entry: FinalSelectorEntry) -> usize {
    (entry.s1_msb.0 + 2 * entry.s2_msb.0) as usize
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SelectorLookupError {
    InvalidSelector4x4(Selector4x4Entry),
    Selector16OutOfRange {
        selector: M31,
    },
    InvalidSelector16Decode {
        actual: Selector16DecodeEntry,
        expected: Selector16DecodeEntry,
    },
    InvalidFinalSelector(FinalSelectorEntry),
    RelationImbalance {
        relation: &'static str,
    },
    ProofLayer,
}

fn decode_selector16(selector: u32) -> Option<(u32, u32)> {
    Some(match selector {
        0 => (7, 1),
        1 => (6, 1),
        2 => (5, 0),
        3 => (4, 0),
        4 => (3, 1),
        5 => (2, 1),
        6 => (1, 0),
        7 => (0, 0),
        8 => (0, 1),
        9 => (1, 1),
        10 => (2, 0),
        11 => (3, 0),
        12 => (4, 1),
        13 => (5, 1),
        14 => (6, 0),
        15 => (7, 0),
        _ => return None,
    })
}

fn secure_from_i64(value: i64) -> SecureField {
    const MODULUS: i64 = (1i64 << 31) - 1;
    SecureField::from(M31::from_u32_unchecked(value.rem_euclid(MODULUS) as u32))
}

fn secure_zero() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(0))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY};
    use crate::public_inputs::{
        public_ecdsa_consumer_claimed_sum, PublicEcdsaInputClaim, PublicEcdsaInstanceRelation,
    };
    use crate::scalar::cert_bind::CertScalarInputClaim;
    use crate::scalar::fake_glv_scalar::{FakeGlvScalarHint, FakeGlvScalarHintClaim};
    use crate::scalar::fake_glv_selector::FakeGlvSelectorClaim;
    use crate::scalar::setup_air::ScalarSetupClaim;
    use crate::types::{AffinePoint, EcdsaVerifyInput, Signature, U256};
    use stwo::core::fri::FriConfig;
    use stwo::core::pcs::PcsConfig;
    use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
    use stwo_constraint_framework::TraceLocationAllocator;

    fn test_input(message_hash: u64, r: u64, s: u64) -> EcdsaVerifyInput {
        EcdsaVerifyInput {
            message_hash: scalar(message_hash),
            signature: Signature {
                r: scalar(r),
                s: scalar(s),
            },
            public_key: AffinePoint {
                x: U256::from_le_u64s(&P256_GX),
                y: U256::from_le_u64s(&P256_GY),
            },
        }
    }

    fn scalar(value: u64) -> U256 {
        U256::from_le_u64s(&[value, 0, 0, 0])
    }

    fn build_selectors() -> (
        PublicEcdsaInputClaim,
        ScalarSetupClaim,
        FakeGlvSelectorClaim,
    ) {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(42, 77, 1)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let hints = certs
            .rows
            .iter()
            .map(|row| FakeGlvScalarHint::trivial_for_small_scalar(&row.scalar).unwrap())
            .collect();
        let fake_glv =
            FakeGlvScalarHintClaim::from_cert_inputs(&certs, hints).expect("valid hints");
        let selectors =
            FakeGlvSelectorClaim::from_scalar_hints(&fake_glv).expect("valid selectors");
        (public_claim, scalar_setup, selectors)
    }

    fn column_sum(column: &SelectorColumnEval) -> u32 {
        column
            .data
            .iter()
            .flat_map(|packed| packed.to_array())
            .map(|value| value.0)
            .sum()
    }

    fn selector_lookup_provider_low_ram_config() -> PcsConfig {
        let claim = SelectorLookupProviderProofClaim;
        let ids = claim.preprocessed_column_ids();
        let max_constraint_log_degree_bound = claim.max_constraint_log_degree_bound(&ids);
        let fri_config = FriConfig::new(5, 4, 64, 1);
        PcsConfig {
            pow_bits: 0,
            fri_config,
            lifting_log_size: Some(
                (max_constraint_log_degree_bound + fri_config.log_blowup_factor).max(10),
            ),
        }
    }

    #[test]
    fn selector_tables_have_expected_shapes() {
        assert_eq!(selector4x4_table().len(), 16);
        assert_eq!(selector16_decode_table().len(), 16);
        assert_eq!(final_selector_table().len(), 4);
        assert_eq!(selector16_decode_table()[0].base_index.0, 7);
        assert_eq!(selector16_decode_table()[0].neg_bit.0, 1);
        assert_eq!(selector16_decode_table()[15].base_index.0, 7);
        assert_eq!(selector16_decode_table()[15].neg_bit.0, 0);
        assert_eq!(final_selector_table()[3].selector_final.0, 10);
        assert_eq!(final_selector_table()[3].init_base_index.0, 7);
    }

    #[test]
    fn selector_requests_from_reconstruction_balance_provider_multiplicities() {
        let (_, _, selectors) = build_selectors();
        let requests =
            SelectorLookupRequests::from_selector_claim(&selectors).expect("valid requests");
        let audit = SelectorLookupAudit::balanced_for_requests(&requests).expect("valid audit");

        assert_eq!(requests.final_selector.len(), 2);
        assert_eq!(
            requests.expected_selector4x4_uses(),
            2 * FAKE_GLV_SELECTOR_CHUNKS
        );
        assert_eq!(requests.selector4x4.len(), 2 * FAKE_GLV_SELECTOR_CHUNKS);
        assert_eq!(
            requests.selector16_decode.len(),
            2 * FAKE_GLV_SELECTOR_CHUNKS
        );
        assert!(audit.is_balanced());
    }

    #[test]
    fn selector_provider_claims_generate_preprocessed_and_multiplicity_columns() {
        let (_, _, selectors) = build_selectors();
        let requests =
            SelectorLookupRequests::from_selector_claim(&selectors).expect("valid requests");
        let selector4x4 = Selector4x4ProviderClaim;
        let selector16 = Selector16DecodeProviderClaim;
        let final_selector = FinalSelectorProviderClaim;

        assert_eq!(selector4x4.gen_preprocessed_columns()[0].domain.size(), 16);
        assert_eq!(selector16.gen_preprocessed_columns()[0].domain.size(), 16);
        assert_eq!(
            final_selector.gen_preprocessed_columns()[0].domain.size(),
            16
        );
        assert_eq!(
            column_sum(&selector4x4.gen_multiplicity_trace(&requests)),
            requests.selector4x4.len() as u32
        );
        assert_eq!(
            column_sum(&selector16.gen_multiplicity_trace(&requests)),
            requests.selector16_decode.len() as u32
        );
        assert_eq!(
            column_sum(&final_selector.gen_multiplicity_trace(&requests)),
            requests.final_selector.len() as u32
        );
    }

    #[test]
    fn selector_provider_components_allocate_expected_columns() {
        let relations = FakeGlvSelectorLookupRelations::dummy();
        let mut ids = Vec::new();
        ids.extend(selector4x4_column_ids());
        ids.extend(selector16_decode_column_ids());
        ids.extend(final_selector_column_ids());
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);

        let selector4x4 = Selector4x4Component::new(
            &mut allocator,
            Selector4x4Eval {
                relation: relations.selector4x4,
            },
            SecureField::from(M31::from_u32_unchecked(0)),
        );
        let selector16 = Selector16DecodeComponent::new(
            &mut allocator,
            Selector16DecodeEval {
                relation: relations.selector16_decode,
            },
            SecureField::from(M31::from_u32_unchecked(0)),
        );
        let final_selector = FinalSelectorComponent::new(
            &mut allocator,
            FinalSelectorEval {
                relation: relations.final_selector,
            },
            SecureField::from(M31::from_u32_unchecked(0)),
        );

        assert_eq!(selector4x4.preprocessed_column_indices().len(), 3);
        assert_eq!(selector16.preprocessed_column_indices().len(), 3);
        assert_eq!(final_selector.preprocessed_column_indices().len(), 4);
        assert_eq!(selector4x4.trace_locations().len(), 3);
        assert_eq!(selector16.trace_locations().len(), 3);
        assert_eq!(final_selector.trace_locations().len(), 3);
    }

    #[test]
    fn selector_lookup_logup_sums_balance() {
        let (_, _, selectors) = build_selectors();
        let requests =
            SelectorLookupRequests::from_selector_claim(&selectors).expect("valid requests");
        let relations = FakeGlvSelectorLookupRelations::dummy();
        let providers = selector_lookup_provider_claimed_sum(&requests, &relations);
        let consumers = selector_lookup_consumer_claimed_sum(&requests, &relations);

        assert_eq!(
            providers + consumers,
            SecureField::from(M31::from_u32_unchecked(0))
        );
    }

    #[test]
    fn selector_provider_interaction_claim_matches_direct_provider_sum() {
        let (_, _, selectors) = build_selectors();
        let requests =
            SelectorLookupRequests::from_selector_claim(&selectors).expect("valid requests");
        let relations = FakeGlvSelectorLookupRelations::dummy();
        let (trace, claim) =
            SelectorProviderInteractionClaim::gen_interaction_traces(&requests, &relations);

        assert!(!trace.is_empty());
        assert_eq!(
            claim.claimed_sum(),
            selector_lookup_provider_claimed_sum(&requests, &relations)
        );
    }

    #[test]
    fn selector_lookup_provider_proof_slice_proves_and_verifies() {
        let (_, _, selectors) = build_selectors();
        let requests =
            SelectorLookupRequests::from_selector_claim(&selectors).expect("valid requests");
        let proof = prove_selector_lookup_provider_proof_slice::<Blake2sMerkleChannel>(
            &requests,
            selector_lookup_provider_low_ram_config(),
        )
        .expect("selector lookup provider slice proves");

        verify_selector_lookup_provider_proof_slice::<Blake2sMerkleChannel>(proof)
            .expect("selector lookup provider slice verifies");
    }

    #[test]
    fn selector_lookup_e2e_preserves_public_balance() {
        let relation = PublicEcdsaInstanceRelation::dummy();
        let (public_claim, scalar_setup, selectors) = build_selectors();
        let requests =
            SelectorLookupRequests::from_selector_claim(&selectors).expect("valid requests");
        let audit = SelectorLookupAudit::balanced_for_requests(&requests).expect("valid audit");
        let public_interaction = public_claim.initial_logup_claim(&relation);
        let vm_consumers =
            public_ecdsa_consumer_claimed_sum(&scalar_setup.public_consumers(), &relation);

        scalar_setup.verify().expect("scalar setup verifies");
        assert!(audit.is_balanced());
        assert_eq!(
            public_interaction.claimed_sum + vm_consumers,
            SecureField::from(M31::from_u32_unchecked(0))
        );
    }

    #[test]
    fn selector_lookup_rejects_invalid_decode_entry() {
        let actual = Selector16DecodeEntry {
            selector: M31::from_u32_unchecked(10),
            base_index: M31::from_u32_unchecked(7),
            neg_bit: M31::from_u32_unchecked(0),
        };

        let err = actual.verify().expect_err("wrong decode must fail");

        assert!(matches!(
            err,
            SelectorLookupError::InvalidSelector16Decode { .. }
        ));
    }

    #[test]
    fn selector_lookup_rejects_invalid_final_selector_entry() {
        let entry = FinalSelectorEntry {
            s1_msb: M31::from_u32_unchecked(1),
            s2_msb: M31::from_u32_unchecked(1),
            selector_final: M31::from_u32_unchecked(9),
            init_base_index: M31::from_u32_unchecked(7),
        };

        let err = entry.verify().expect_err("wrong final selector must fail");

        assert!(matches!(err, SelectorLookupError::InvalidFinalSelector(_)));
    }
}
