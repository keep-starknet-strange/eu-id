//! Shared SHA table-provider module.
//!
//! This module moves the message-agnostic split-pack/range table providers out
//! of repeated SHA instances. Each SHA consumer still owns its main trace,
//! digest relation, field exposure, and consumer-side lookups; this module owns
//! only the fixed table preprocessed columns plus the union multiplicities that
//! satisfy those lookups.

use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use serde::{Deserialize, Serialize};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::{SecureField, QM31, SECURE_EXTENSION_DEGREE};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::TraceLocationAllocator;

use crate::components::{
    range_log_size, shared_table_preprocessed_column_ids, RangeKEval, RoundSplitPackEval,
    SigmaSplitPackEval, RANGE_TABLES, ROUND_SPLIT_TABLES, SIGMA_SPLIT_TABLES,
};
use crate::field_exposure::FieldExposure;
use crate::interaction::{build_interaction_columns, producer_frac_column, ComponentClaim};
use crate::multiplicities::{
    range_k_multiplicities, round_split_pack_multiplicities, sigma_split_pack_multiplicities,
    sum_multiplicity_vectors,
};
use crate::preprocessed::{
    generate_shared_table_preprocessed_trace, shared_table_preprocessed_log_sizes, LOG_SIZE_16,
};
use crate::relations::{Sha256Relations, SharedShaTableRelations};
use crate::tables::{
    build_round_split_pack_table, build_sigma_split_pack_table, Half16, LowerSigmaPartition,
    RoundPartition,
};
use crate::types::Sha256Witness;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ShaTablesInteractionClaim {
    pub round_split_pack: Vec<ComponentClaim>,
    pub sigma_split_pack: Vec<ComponentClaim>,
    pub range: Vec<ComponentClaim>,
}

impl ShaTablesInteractionClaim {
    pub fn claimed_sums(&self) -> Vec<QM31> {
        let mut out = Vec::new();
        out.extend(self.round_split_pack.iter().map(|c| c.claimed_sum));
        out.extend(self.sigma_split_pack.iter().map(|c| c.claimed_sum));
        out.extend(self.range.iter().map(|c| c.claimed_sum));
        out
    }
}

#[derive(Clone, Debug)]
pub struct ShaTableMultiplicities {
    pub round_split_pack: Vec<Vec<u32>>,
    pub sigma_split_pack: Vec<Vec<u32>>,
    pub range: Vec<Vec<u32>>,
}

impl ShaTableMultiplicities {
    pub fn from_consumers(consumers: &[(&Sha256Witness, FieldExposure)]) -> Self {
        assert!(
            !consumers.is_empty(),
            "shared SHA table provider needs at least one consumer",
        );

        let mut round_split_pack = Vec::with_capacity(ROUND_SPLIT_TABLES.len());
        for &(p, h) in ROUND_SPLIT_TABLES {
            round_split_pack.push(sum_multiplicity_vectors(
                consumers
                    .iter()
                    .map(|(witness, _)| round_split_pack_multiplicities(witness, p, h)),
            ));
        }

        let mut sigma_split_pack = Vec::with_capacity(SIGMA_SPLIT_TABLES.len());
        for &(p, h) in SIGMA_SPLIT_TABLES {
            sigma_split_pack.push(sum_multiplicity_vectors(
                consumers
                    .iter()
                    .map(|(witness, _)| sigma_split_pack_multiplicities(witness, p, h)),
            ));
        }

        let mut range = Vec::with_capacity(RANGE_TABLES.len());
        for &kind in RANGE_TABLES {
            range.push(sum_multiplicity_vectors(consumers.iter().map(
                |(witness, exposure)| range_k_multiplicities(witness, kind, exposure),
            )));
        }

        Self {
            round_split_pack,
            sigma_split_pack,
            range,
        }
    }
}

pub struct ShaTablesProver {
    multiplicities: ShaTableMultiplicities,
    shared: SharedShaTableRelations,
    relations: Option<Sha256Relations>,
    interaction_claim: Option<ShaTablesInteractionClaim>,
    components: Option<ShaTablesComponents>,
}

impl ShaTablesProver {
    pub fn new(multiplicities: ShaTableMultiplicities, shared: SharedShaTableRelations) -> Self {
        Self {
            multiplicities,
            shared,
            relations: None,
            interaction_claim: None,
            components: None,
        }
    }

    pub fn interaction_claim(&self) -> &ShaTablesInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("shared SHA table interaction claim is set during proving")
    }

    fn relations(&self) -> &Sha256Relations {
        self.relations
            .as_ref()
            .expect("shared SHA table relations are drawn before use")
    }

    fn built_components(&self) -> &ShaTablesComponents {
        self.components
            .as_ref()
            .expect("shared SHA table components are built before use")
    }
}

pub struct ShaTablesVerifier {
    interaction_claim: ShaTablesInteractionClaim,
    shared: SharedShaTableRelations,
    relations: Option<Sha256Relations>,
    components: Option<ShaTablesComponents>,
}

impl ShaTablesVerifier {
    pub fn new(
        interaction_claim: ShaTablesInteractionClaim,
        shared: SharedShaTableRelations,
    ) -> Self {
        Self {
            interaction_claim,
            shared,
            relations: None,
            components: None,
        }
    }

    fn relations(&self) -> &Sha256Relations {
        self.relations
            .as_ref()
            .expect("shared SHA table relations are drawn before use")
    }

    fn built_components(&self) -> &ShaTablesComponents {
        self.components
            .as_ref()
            .expect("shared SHA table components are built before use")
    }
}

impl Air for ShaTablesProver {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(0x5348_4154_4142_4c45);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let relations = Sha256Relations::draw_sha_tables_provider(channel);
        self.shared.set(&relations.split_pack, &relations.range);
        self.relations = Some(relations);
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: shared_table_preprocessed_log_sizes(),
            trace: shared_table_trace_log_sizes(),
            interaction: shared_table_interaction_log_sizes(),
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        self.interaction_claim().claimed_sums()
    }

    fn preprocessed_column_ids(
        &self,
    ) -> Vec<stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId> {
        shared_table_preprocessed_column_ids()
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(ShaTablesComponents::new(
            allocator,
            self.interaction_claim(),
            self.relations(),
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built_components().components()
    }
}

impl AirProver for ShaTablesProver {
    fn max_log_size(&self) -> u32 {
        LOG_SIZE_16
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let (evals, _ids, _log_sizes) = generate_shared_table_preprocessed_trace();
        tb.extend_evals(evals);
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        let (evals, ids, _log_sizes) = generate_shared_table_preprocessed_trace();
        fingerprint_preprocessed_columns("stwo_sha256::ShaTablesProver", &ids, &evals)
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        tb.extend_evals(shared_table_trace(&self.multiplicities));
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let (evals, claim) = shared_table_interaction_trace(self.relations(), &self.multiplicities);
        tb.extend_evals(evals);
        self.interaction_claim = Some(claim);
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        self.built_components().component_provers()
    }
}

impl Air for ShaTablesVerifier {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(0x5348_4154_4142_4c45);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let relations = Sha256Relations::draw_sha_tables_provider(channel);
        self.shared.set(&relations.split_pack, &relations.range);
        self.relations = Some(relations);
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: shared_table_preprocessed_log_sizes(),
            trace: shared_table_trace_log_sizes(),
            interaction: shared_table_interaction_log_sizes(),
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        self.interaction_claim.claimed_sums()
    }

    fn preprocessed_column_ids(
        &self,
    ) -> Vec<stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId> {
        shared_table_preprocessed_column_ids()
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(ShaTablesComponents::new(
            allocator,
            &self.interaction_claim,
            self.relations(),
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built_components().components()
    }
}

fn shared_table_trace_log_sizes() -> Vec<u32> {
    let mut out = Vec::new();
    out.extend(std::iter::repeat_n(LOG_SIZE_16, ROUND_SPLIT_TABLES.len()));
    out.extend(std::iter::repeat_n(LOG_SIZE_16, SIGMA_SPLIT_TABLES.len()));
    for &kind in RANGE_TABLES {
        out.push(range_log_size(kind));
    }
    out
}

fn shared_table_interaction_log_sizes() -> Vec<u32> {
    let mut out = Vec::new();
    for _ in ROUND_SPLIT_TABLES {
        out.extend(std::iter::repeat_n(LOG_SIZE_16, SECURE_EXTENSION_DEGREE));
    }
    for _ in SIGMA_SPLIT_TABLES {
        out.extend(std::iter::repeat_n(LOG_SIZE_16, SECURE_EXTENSION_DEGREE));
    }
    for &kind in RANGE_TABLES {
        out.extend(std::iter::repeat_n(
            range_log_size(kind),
            SECURE_EXTENSION_DEGREE,
        ));
    }
    out
}

fn mult_col_to_eval(
    mults: &[u32],
    log_size: u32,
) -> CircleEvaluation<SimdBackend, BaseField, BitReversedOrder> {
    debug_assert_eq!(mults.len(), 1usize << log_size);
    let domain = CanonicCoset::new(log_size).circle_domain();
    let col: BaseColumn = mults.iter().map(|&m| BaseField::from(m)).collect();
    CircleEvaluation::new(domain, col)
}

fn shared_table_trace(
    multiplicities: &ShaTableMultiplicities,
) -> Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let mut out = Vec::new();
    for mults in &multiplicities.round_split_pack {
        out.push(mult_col_to_eval(mults, LOG_SIZE_16));
    }
    for mults in &multiplicities.sigma_split_pack {
        out.push(mult_col_to_eval(mults, LOG_SIZE_16));
    }
    for (&kind, mults) in RANGE_TABLES.iter().zip(&multiplicities.range) {
        out.push(mult_col_to_eval(mults, range_log_size(kind)));
    }
    out
}

fn shared_table_interaction_trace(
    relations: &Sha256Relations,
    multiplicities: &ShaTableMultiplicities,
) -> (
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    ShaTablesInteractionClaim,
) {
    let mut combined = Vec::new();

    let mut round_split_pack = Vec::with_capacity(ROUND_SPLIT_TABLES.len());
    for (i, &(p, h)) in ROUND_SPLIT_TABLES.iter().enumerate() {
        let (trace, sum) = round_split_pack_interaction_from_multiplicities(
            relations,
            &multiplicities.round_split_pack[i],
            p,
            h,
        );
        combined.extend(trace);
        round_split_pack.push(ComponentClaim { claimed_sum: sum });
    }

    let mut sigma_split_pack = Vec::with_capacity(SIGMA_SPLIT_TABLES.len());
    for (i, &(p, h)) in SIGMA_SPLIT_TABLES.iter().enumerate() {
        let (trace, sum) = sigma_split_pack_interaction_from_multiplicities(
            relations,
            &multiplicities.sigma_split_pack[i],
            p,
            h,
        );
        combined.extend(trace);
        sigma_split_pack.push(ComponentClaim { claimed_sum: sum });
    }

    let mut range = Vec::with_capacity(RANGE_TABLES.len());
    for (i, &kind) in RANGE_TABLES.iter().enumerate() {
        let (trace, sum) =
            range_interaction_from_multiplicities(relations, &multiplicities.range[i], kind);
        combined.extend(trace);
        range.push(ComponentClaim { claimed_sum: sum });
    }

    (
        combined,
        ShaTablesInteractionClaim {
            round_split_pack,
            sigma_split_pack,
            range,
        },
    )
}

fn round_split_pack_interaction_from_multiplicities(
    relations: &Sha256Relations,
    mults: &[u32],
    p: RoundPartition,
    h: Half16,
) -> (
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let groups = match p {
        RoundPartition::Sigma0AndMaj => crate::partitions::SIGMA0_GROUPS,
        RoundPartition::Sigma1AndCh => crate::partitions::SIGMA1_GROUPS,
    };
    let rows = build_round_split_pack_table(&groups, p.s_mask(), h);
    let row_iter = rows.iter().map(|r| {
        [
            BaseField::from(r.key),
            BaseField::from(r.groups[0]),
            BaseField::from(r.groups[1]),
            BaseField::from(r.groups[2]),
            BaseField::from(r.groups[3]),
        ]
    });
    let frac = match (p, h) {
        (RoundPartition::Sigma0AndMaj, Half16::Lo) => {
            producer_frac_column(&relations.split_pack.sigma0_lo, mults, row_iter)
        }
        (RoundPartition::Sigma0AndMaj, Half16::Hi) => {
            producer_frac_column(&relations.split_pack.sigma0_hi, mults, row_iter)
        }
        (RoundPartition::Sigma1AndCh, Half16::Lo) => {
            producer_frac_column(&relations.split_pack.sigma1_lo, mults, row_iter)
        }
        (RoundPartition::Sigma1AndCh, Half16::Hi) => {
            producer_frac_column(&relations.split_pack.sigma1_hi, mults, row_iter)
        }
    };
    build_interaction_columns(LOG_SIZE_16, vec![frac])
}

fn sigma_split_pack_interaction_from_multiplicities(
    relations: &Sha256Relations,
    mults: &[u32],
    p: LowerSigmaPartition,
    h: Half16,
) -> (
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let rows = build_sigma_split_pack_table(p.parts(), h);
    let row_iter = rows.iter().map(|r| {
        [
            BaseField::from(r.key),
            BaseField::from(r.groups[0]),
            BaseField::from(r.groups[1]),
        ]
    });
    let frac = match (p, h) {
        (LowerSigmaPartition::LowerSigma0, Half16::Lo) => {
            producer_frac_column(&relations.split_pack.lower_sigma0_lo, mults, row_iter)
        }
        (LowerSigmaPartition::LowerSigma0, Half16::Hi) => {
            producer_frac_column(&relations.split_pack.lower_sigma0_hi, mults, row_iter)
        }
        (LowerSigmaPartition::LowerSigma1, Half16::Lo) => {
            producer_frac_column(&relations.split_pack.lower_sigma1_lo, mults, row_iter)
        }
        (LowerSigmaPartition::LowerSigma1, Half16::Hi) => {
            producer_frac_column(&relations.split_pack.lower_sigma1_hi, mults, row_iter)
        }
    };
    build_interaction_columns(LOG_SIZE_16, vec![frac])
}

fn range_interaction_from_multiplicities(
    relations: &Sha256Relations,
    mults: &[u32],
    kind: crate::components::RangeKind,
) -> (
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let log_size = range_log_size(kind);
    let n_rows = 1usize << log_size;
    let k = kind.bound() as usize;
    let row_iter = (0..n_rows).map(|i| {
        let value = if i < k { i as u32 } else { 0u32 };
        [BaseField::from(value)]
    });
    let frac = match kind {
        crate::components::RangeKind::Range2 => {
            producer_frac_column(&relations.range.range_2, mults, row_iter)
        }
        crate::components::RangeKind::Range4 => {
            producer_frac_column(&relations.range.range_4, mults, row_iter)
        }
        crate::components::RangeKind::Range5 => {
            producer_frac_column(&relations.range.range_5, mults, row_iter)
        }
        crate::components::RangeKind::Range16 => {
            producer_frac_column(&relations.range.range_16, mults, row_iter)
        }
    };
    build_interaction_columns(log_size, vec![frac])
}

struct ShaTablesComponents {
    round_split_pack: Vec<stwo_constraint_framework::FrameworkComponent<RoundSplitPackEval>>,
    sigma_split_pack: Vec<stwo_constraint_framework::FrameworkComponent<SigmaSplitPackEval>>,
    range: Vec<stwo_constraint_framework::FrameworkComponent<RangeKEval>>,
}

impl ShaTablesComponents {
    fn new(
        allocator: &mut TraceLocationAllocator,
        claim: &ShaTablesInteractionClaim,
        relations: &Sha256Relations,
    ) -> Self {
        let mut round_split_pack = Vec::with_capacity(ROUND_SPLIT_TABLES.len());
        for (i, &(p, h)) in ROUND_SPLIT_TABLES.iter().enumerate() {
            round_split_pack.push(stwo_constraint_framework::FrameworkComponent::new(
                allocator,
                RoundSplitPackEval {
                    log_size: LOG_SIZE_16,
                    partition: p,
                    half: h,
                    relations: relations.clone(),
                    shared_tables: true,
                },
                claim.round_split_pack[i].claimed_sum,
            ));
        }

        let mut sigma_split_pack = Vec::with_capacity(SIGMA_SPLIT_TABLES.len());
        for (i, &(p, h)) in SIGMA_SPLIT_TABLES.iter().enumerate() {
            sigma_split_pack.push(stwo_constraint_framework::FrameworkComponent::new(
                allocator,
                SigmaSplitPackEval {
                    log_size: LOG_SIZE_16,
                    partition: p,
                    half: h,
                    relations: relations.clone(),
                    shared_tables: true,
                },
                claim.sigma_split_pack[i].claimed_sum,
            ));
        }

        let mut range = Vec::with_capacity(RANGE_TABLES.len());
        for (i, &kind) in RANGE_TABLES.iter().enumerate() {
            range.push(stwo_constraint_framework::FrameworkComponent::new(
                allocator,
                RangeKEval {
                    log_size: range_log_size(kind),
                    kind,
                    relations: relations.clone(),
                    shared_tables: true,
                },
                claim.range[i].claimed_sum,
            ));
        }

        Self {
            round_split_pack,
            sigma_split_pack,
            range,
        }
    }

    fn components(&self) -> Vec<&dyn Component> {
        let mut out: Vec<&dyn Component> = Vec::new();
        out.extend(self.round_split_pack.iter().map(|c| c as &dyn Component));
        out.extend(self.sigma_split_pack.iter().map(|c| c as &dyn Component));
        out.extend(self.range.iter().map(|c| c as &dyn Component));
        out
    }

    fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        let mut out: Vec<&dyn ComponentProver<SimdBackend>> = Vec::new();
        out.extend(
            self.round_split_pack
                .iter()
                .map(|c| c as &dyn ComponentProver<SimdBackend>),
        );
        out.extend(
            self.sigma_split_pack
                .iter()
                .map(|c| c as &dyn ComponentProver<SimdBackend>),
        );
        out.extend(
            self.range
                .iter()
                .map(|c| c as &dyn ComponentProver<SimdBackend>),
        );
        out
    }
}
