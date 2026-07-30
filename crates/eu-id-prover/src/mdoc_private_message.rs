//! Private issuer `Sig_structure` byte provider.
//!
//! Each active row provides one `(HOSTED_MSG_FIELD_ID, index, byte)` tuple for
//! the issuer ML-DSA absorb plus `extra_uses` additional consumers. The public
//! preprocessing fixes only `(active, index)` from `message_len`; bytes and
//! multiplicities remain in the committed trace.

use std::fmt;

use air_core::relations::{FieldBytesRelation, SharedFieldRelation};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use rand::RngCore;
use serde::{Deserialize, Serialize};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{QM31, SECURE_EXTENSION_DEGREE};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::utils::{bit_reverse_index, coset_index_to_circle_domain_index};
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::PackedM31;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    TraceLocationAllocator,
};
use stwo_mldsa::statement::HOSTED_MSG_FIELD_ID;

use crate::claimed_sum_blinder::{
    add_blinder_relation_entry, blinder_counter_interaction, blinder_denominator, random_qm31,
    ClaimedSumBlinderEval, ClaimedSumBlinderRelation,
};

pub(crate) const MDOC_PRIVATE_MESSAGE_MAX_BYTES: usize =
    crate::ts13::TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES;
const MDOC_PRIVATE_MESSAGE_BLIND_ROWS: usize = 256;
const MDOC_PRIVATE_MESSAGE_VERSION: u64 = 1;
const MDOC_PRIVATE_MESSAGE_DOMAIN: u64 = 0x4d44_4f43_5052_4956;
const MDOC_PRIVATE_MESSAGE_PREPROCESSED_COLS: usize = 2;
const MDOC_PRIVATE_MESSAGE_TRACE_COLS: usize = 2;
const MDOC_PRIVATE_MESSAGE_MAIN_INTERACTION_COLS: usize = SECURE_EXTENSION_DEGREE;
const MDOC_PRIVATE_MESSAGE_BLINDER_INTERACTION_COLS: usize = SECURE_EXTENSION_DEGREE;
const MAX_EXTRA_USES: u32 = 0x7fff_fffd;

type MdocPrivateMessageColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type MdocPrivateMessageComponent = FrameworkComponent<MdocPrivateMessageEval>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum MdocPrivateMessageError {
    EmptyMessage,
    MessageTooLong {
        length: usize,
        max: usize,
    },
    TraceSizeOverflow {
        message_len: usize,
    },
    ExtraUsesLengthMismatch {
        message_len: usize,
        extra_uses_len: usize,
    },
    ExtraUsesOverflow {
        index: usize,
        extra_uses: u32,
    },
}

impl fmt::Display for MdocPrivateMessageError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyMessage => write!(f, "private issuer message is empty"),
            Self::MessageTooLong { length, max } => write!(
                f,
                "private issuer message length {length} exceeds the {max}-byte cap"
            ),
            Self::TraceSizeOverflow { message_len } => write!(
                f,
                "private issuer message length {message_len} overflows the provider trace shape"
            ),
            Self::ExtraUsesLengthMismatch {
                message_len,
                extra_uses_len,
            } => write!(
                f,
                "private issuer message has {message_len} bytes but {extra_uses_len} multiplicities"
            ),
            Self::ExtraUsesOverflow { index, extra_uses } => write!(
                f,
                "private issuer message multiplicity {extra_uses} at byte {index} cannot be incremented in M31"
            ),
        }
    }
}

impl std::error::Error for MdocPrivateMessageError {}

fn checked_log_size(message_len: usize) -> Result<u32, MdocPrivateMessageError> {
    if message_len == 0 {
        return Err(MdocPrivateMessageError::EmptyMessage);
    }
    let needed = message_len
        .checked_add(MDOC_PRIVATE_MESSAGE_BLIND_ROWS)
        .ok_or(MdocPrivateMessageError::TraceSizeOverflow { message_len })?;
    let domain_rows = needed
        .checked_next_power_of_two()
        .ok_or(MdocPrivateMessageError::TraceSizeOverflow { message_len })?;
    if message_len > MDOC_PRIVATE_MESSAGE_MAX_BYTES {
        return Err(MdocPrivateMessageError::MessageTooLong {
            length: message_len,
            max: MDOC_PRIVATE_MESSAGE_MAX_BYTES,
        });
    }
    Ok(domain_rows.ilog2())
}

fn random_m31_cell() -> M31 {
    let mut rng = rand::thread_rng();
    loop {
        let candidate = rng.next_u32() & 0x7fff_ffff;
        if candidate != 0x7fff_ffff {
            return M31::from_u32_unchecked(candidate);
        }
    }
}

fn coset_order_to_circle_domain_order(log_size: u32, values: Vec<M31>) -> Vec<M31> {
    let mut ordered = vec![M31::from_u32_unchecked(0); 1usize << log_size];
    for (coset_index, value) in values.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        );
        ordered[row] = value;
    }
    ordered
}

fn private_message_column_eval(
    log_size: u32,
    coset_values: Vec<M31>,
) -> MdocPrivateMessageColumnEval {
    CircleEvaluation::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(coset_order_to_circle_domain_order(log_size, coset_values)),
    )
}

fn private_message_col_id(message_len: usize, log_size: u32, name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!(
            "mdoc/private_message/v{MDOC_PRIVATE_MESSAGE_VERSION}/len_{message_len}/log_{log_size}/{name}"
        ),
    }
}

fn private_message_preprocessed_column_ids(
    message_len: usize,
    log_size: u32,
) -> Vec<PreProcessedColumnId> {
    vec![
        private_message_col_id(message_len, log_size, "active"),
        private_message_col_id(message_len, log_size, "index"),
    ]
}

fn private_message_preprocessed_columns(
    message_len: usize,
    log_size: u32,
) -> Vec<MdocPrivateMessageColumnEval> {
    let domain_rows = 1usize << log_size;
    let active = (0..domain_rows)
        .map(|index| M31::from_u32_unchecked(u32::from(index < message_len)))
        .collect();
    let index = (0..domain_rows)
        .map(|index| M31::from_u32_unchecked(index as u32))
        .collect();
    vec![
        private_message_column_eval(log_size, active),
        private_message_column_eval(log_size, index),
    ]
}

#[derive(Clone)]
struct MdocPrivateMessageWitness {
    bytes: Vec<M31>,
    extra_uses: Vec<M31>,
}

impl MdocPrivateMessageWitness {
    fn new(
        message: Vec<u8>,
        extra_uses: Vec<u32>,
        log_size: u32,
    ) -> Result<Self, MdocPrivateMessageError> {
        if message.len() != extra_uses.len() {
            return Err(MdocPrivateMessageError::ExtraUsesLengthMismatch {
                message_len: message.len(),
                extra_uses_len: extra_uses.len(),
            });
        }
        if let Some((index, &extra_uses)) = extra_uses
            .iter()
            .enumerate()
            .find(|(_, extra_uses)| **extra_uses > MAX_EXTRA_USES)
        {
            return Err(MdocPrivateMessageError::ExtraUsesOverflow { index, extra_uses });
        }

        let domain_rows = 1usize << log_size;
        let mut byte_cells = Vec::with_capacity(domain_rows);
        byte_cells.extend(
            message
                .into_iter()
                .map(|byte| M31::from_u32_unchecked(u32::from(byte))),
        );
        byte_cells.resize_with(domain_rows, random_m31_cell);

        let mut extra_use_cells = Vec::with_capacity(domain_rows);
        extra_use_cells.extend(extra_uses.into_iter().map(M31::from_u32_unchecked));
        extra_use_cells.resize_with(domain_rows, random_m31_cell);

        Ok(Self {
            bytes: byte_cells,
            extra_uses: extra_use_cells,
        })
    }

    fn trace(&self, log_size: u32) -> Vec<MdocPrivateMessageColumnEval> {
        vec![
            private_message_column_eval(log_size, self.bytes.clone()),
            private_message_column_eval(log_size, self.extra_uses.clone()),
        ]
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct MdocPrivateMessageInteractionClaim {
    pub(crate) claimed_sum: QM31,
    pub(crate) blinder_v: QM31,
    pub(crate) blinder_m: QM31,
    pub(crate) blinder_claimed_sum: QM31,
}

#[derive(Clone)]
struct MdocPrivateMessageEval {
    message_len: usize,
    log_size: u32,
    message_relation: FieldBytesRelation,
    blinder_relation: ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
}

impl FrameworkEval for MdocPrivateMessageEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(private_message_col_id(
            self.message_len,
            self.log_size,
            "active",
        ));
        let index = eval.get_preprocessed_column(private_message_col_id(
            self.message_len,
            self.log_size,
            "index",
        ));
        let byte = eval.next_trace_mask();
        let extra_uses = eval.next_trace_mask();
        let one = E::F::from(M31::from_u32_unchecked(1));
        eval.add_to_relation(RelationEntry::new(
            &self.message_relation,
            -E::EF::from(active * (one + extra_uses)),
            &[
                E::F::from(M31::from_u32_unchecked(HOSTED_MSG_FIELD_ID)),
                index,
                byte,
            ],
        ));
        // Claimed-sum blinder is deliberately the final main-component site.
        add_blinder_relation_entry(
            &mut eval,
            &self.blinder_relation,
            self.blinder_v,
            self.blinder_m,
            false,
        );
        eval.finalize_logup_in_pairs();
        eval
    }
}

fn private_message_interaction_trace(
    message_len: usize,
    log_size: u32,
    witness: &MdocPrivateMessageWitness,
    message_relation: &FieldBytesRelation,
    blinder_relation: &ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
) -> (Vec<MdocPrivateMessageColumnEval>, QM31) {
    let preprocessed = private_message_preprocessed_columns(message_len, log_size);
    let trace = witness.trace(log_size);
    let blinder_numerator = PackedQM31::broadcast(blinder_m);
    let blinder_denominator = blinder_denominator(blinder_relation, blinder_v);
    let mut logup = LogupTraceGenerator::new(log_size);
    logup.col_from_fn(|vec_row| {
        let one = PackedM31::broadcast(M31::from_u32_unchecked(1));
        let provider_numerator =
            -PackedQM31::from(preprocessed[0].data[vec_row] * (one + trace[1].data[vec_row]));
        let provider_denominator: PackedQM31 = message_relation.combine(&[
            PackedM31::broadcast(M31::from_u32_unchecked(HOSTED_MSG_FIELD_ID)),
            preprocessed[1].data[vec_row],
            trace[0].data[vec_row],
        ]);
        (
            provider_numerator * blinder_denominator + blinder_numerator * provider_denominator,
            provider_denominator * blinder_denominator,
        )
    });
    logup.finalize_last()
}

pub(crate) struct MdocPrivateMessageProvider {
    message_len: usize,
    log_size: u32,
    witness: Option<MdocPrivateMessageWitness>,
    message_handle: SharedFieldRelation,
    message_relation: Option<FieldBytesRelation>,
    blinder_relation: Option<ClaimedSumBlinderRelation>,
    interaction_claim: Option<MdocPrivateMessageInteractionClaim>,
    component: Option<MdocPrivateMessageComponent>,
    blinder_component: Option<FrameworkComponent<ClaimedSumBlinderEval>>,
}

impl MdocPrivateMessageProvider {
    pub(crate) fn new(
        message: Vec<u8>,
        extra_uses: Vec<u32>,
        message_handle: SharedFieldRelation,
    ) -> Result<Self, MdocPrivateMessageError> {
        let message_len = message.len();
        let log_size = checked_log_size(message_len)?;
        let witness = MdocPrivateMessageWitness::new(message, extra_uses, log_size)?;
        Ok(Self {
            message_len,
            log_size,
            witness: Some(witness),
            message_handle,
            message_relation: None,
            blinder_relation: None,
            interaction_claim: None,
            component: None,
            blinder_component: None,
        })
    }

    pub(crate) fn verifier(
        message_len: usize,
        message_handle: SharedFieldRelation,
        interaction_claim: MdocPrivateMessageInteractionClaim,
    ) -> Result<Self, MdocPrivateMessageError> {
        let log_size = checked_log_size(message_len)?;
        Ok(Self {
            message_len,
            log_size,
            witness: None,
            message_handle,
            message_relation: None,
            blinder_relation: None,
            interaction_claim: Some(interaction_claim),
            component: None,
            blinder_component: None,
        })
    }

    #[cfg(test)]
    pub(crate) fn message_len(&self) -> usize {
        self.message_len
    }

    #[cfg(test)]
    pub(crate) fn log_size(&self) -> u32 {
        self.log_size
    }

    pub(crate) fn claim(&self) -> &MdocPrivateMessageInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("private issuer message interaction claim is set")
    }

    fn message_relation(&self) -> FieldBytesRelation {
        self.message_relation
            .clone()
            .expect("private issuer message relation is drawn")
    }
}

impl Air for MdocPrivateMessageProvider {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(MDOC_PRIVATE_MESSAGE_DOMAIN);
        channel.mix_u64(MDOC_PRIVATE_MESSAGE_VERSION);
        channel.mix_u64(self.message_len as u64);
        channel.mix_u64(u64::from(self.log_size));
        channel.mix_u64(MDOC_PRIVATE_MESSAGE_PREPROCESSED_COLS as u64);
        channel.mix_u64(MDOC_PRIVATE_MESSAGE_TRACE_COLS as u64);
        channel.mix_u64(
            (MDOC_PRIVATE_MESSAGE_MAIN_INTERACTION_COLS
                + MDOC_PRIVATE_MESSAGE_BLINDER_INTERACTION_COLS) as u64,
        );
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        assert!(
            !self.message_handle.is_set(),
            "private issuer message provider needs a fresh relation handle"
        );
        let message_relation = FieldBytesRelation::draw(channel);
        self.message_handle.set(message_relation.clone());
        self.message_relation = Some(message_relation);
        self.blinder_relation = Some(ClaimedSumBlinderRelation::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![self.log_size; MDOC_PRIVATE_MESSAGE_PREPROCESSED_COLS],
            trace: vec![self.log_size; MDOC_PRIVATE_MESSAGE_TRACE_COLS],
            interaction: vec![
                self.log_size;
                MDOC_PRIVATE_MESSAGE_MAIN_INTERACTION_COLS
                    + MDOC_PRIVATE_MESSAGE_BLINDER_INTERACTION_COLS
            ],
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        let claim = self.claim();
        vec![claim.claimed_sum, claim.blinder_claimed_sum]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        private_message_preprocessed_column_ids(self.message_len, self.log_size)
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(private_message_preprocessed_columns(
            self.message_len,
            self.log_size,
        ))
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let claim = self.claim().clone();
        let blinder_relation = self
            .blinder_relation
            .clone()
            .expect("private issuer message blinder relation is drawn");
        self.component = Some(MdocPrivateMessageComponent::new(
            allocator,
            MdocPrivateMessageEval {
                message_len: self.message_len,
                log_size: self.log_size,
                message_relation: self.message_relation(),
                blinder_relation: blinder_relation.clone(),
                blinder_v: claim.blinder_v,
                blinder_m: claim.blinder_m,
            },
            claim.claimed_sum,
        ));
        self.blinder_component = Some(FrameworkComponent::new(
            allocator,
            ClaimedSumBlinderEval {
                log_size: self.log_size,
                relation: blinder_relation,
                v: claim.blinder_v,
                m: claim.blinder_m,
            },
            claim.blinder_claimed_sum,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![
            self.component
                .as_ref()
                .expect("private issuer message component is built"),
            self.blinder_component
                .as_ref()
                .expect("private issuer message blinder component is built"),
        ]
    }
}

impl AirProver for MdocPrivateMessageProvider {
    fn max_log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        self.write_selected_preprocessed(tb, &self.preprocessed_column_ids());
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc_private_message::MdocPrivateMessageProvider",
            &self.preprocessed_column_ids(),
            &private_message_preprocessed_columns(self.message_len, self.log_size),
        )
    }

    fn write_selected_preprocessed(
        &mut self,
        tb: &mut TreeBuilder<SimdBackend, air_core::Mc>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        let all_ids = self.preprocessed_column_ids();
        let all_columns = private_message_preprocessed_columns(self.message_len, self.log_size);
        let selected = selected_ids
            .iter()
            .map(|id| {
                all_ids
                    .iter()
                    .position(|candidate| candidate == id)
                    .map(|index| all_columns[index].clone())
                    .expect("unexpected private issuer message preprocessed selection")
            })
            .collect();
        tb.extend_evals(selected);
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let witness = self
            .witness
            .as_ref()
            .expect("private issuer message prover has a witness");
        tb.extend_evals(witness.trace(self.log_size));
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let witness = self
            .witness
            .as_ref()
            .expect("private issuer message prover has a witness");
        let blinder_v = random_qm31();
        let blinder_m = random_qm31();
        let blinder_relation = self
            .blinder_relation
            .clone()
            .expect("private issuer message blinder relation is drawn");
        let (trace, claimed_sum) = private_message_interaction_trace(
            self.message_len,
            self.log_size,
            witness,
            &self.message_relation(),
            &blinder_relation,
            blinder_v,
            blinder_m,
        );
        tb.extend_evals(trace);
        let (blinder_trace, blinder_claimed_sum) =
            blinder_counter_interaction(self.log_size, &blinder_relation, blinder_v, blinder_m);
        tb.extend_evals(blinder_trace);
        self.interaction_claim = Some(MdocPrivateMessageInteractionClaim {
            claimed_sum,
            blinder_v,
            blinder_m,
            blinder_claimed_sum,
        });
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            self.component
                .as_ref()
                .expect("private issuer message component is built"),
            self.blinder_component
                .as_ref()
                .expect("private issuer message blinder component is built"),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use stwo::core::verifier::VerificationError;
    use stwo::prover::backend::simd::m31::LOG_N_LANES;
    use stwo::prover::backend::Column as _;

    const TEST_CONSUMER_DOMAIN: u64 = 0x4d44_4f43_4d55_5445;

    fn qm31(value: u32) -> QM31 {
        QM31::from(M31::from_u32_unchecked(value))
    }

    fn claim() -> MdocPrivateMessageInteractionClaim {
        MdocPrivateMessageInteractionClaim {
            claimed_sum: qm31(1),
            blinder_v: qm31(2),
            blinder_m: qm31(3),
            blinder_claimed_sum: qm31(4),
        }
    }

    fn logical_value(column: &MdocPrivateMessageColumnEval, log_size: u32, index: usize) -> u32 {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(index, log_size),
            log_size,
        );
        column.values.at(row).0
    }

    #[derive(Clone)]
    struct TestMessageUseEval {
        message: Vec<u8>,
        uses: Vec<u32>,
        relation: FieldBytesRelation,
    }

    impl FrameworkEval for TestMessageUseEval {
        fn log_size(&self) -> u32 {
            LOG_N_LANES
        }

        fn max_constraint_log_degree_bound(&self) -> u32 {
            LOG_N_LANES + 1
        }

        fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
            let active = eval.next_trace_mask();
            let one = E::F::from(M31::from_u32_unchecked(1));
            eval.add_constraint(active.clone() * (one - active.clone()));
            for (index, (&byte, &uses)) in self.message.iter().zip(&self.uses).enumerate() {
                eval.add_to_relation(RelationEntry::new(
                    &self.relation,
                    E::EF::from(active.clone() * E::F::from(M31::from_u32_unchecked(uses))),
                    &[
                        E::F::from(M31::from_u32_unchecked(HOSTED_MSG_FIELD_ID)),
                        E::F::from(M31::from_u32_unchecked(index as u32)),
                        E::F::from(M31::from_u32_unchecked(u32::from(byte))),
                    ],
                ));
            }
            eval.finalize_logup_in_pairs();
            eval
        }
    }

    fn test_consumer_trace() -> Vec<MdocPrivateMessageColumnEval> {
        let mut active = vec![M31::from_u32_unchecked(0); 1usize << LOG_N_LANES];
        active[0] = M31::from_u32_unchecked(1);
        vec![private_message_column_eval(LOG_N_LANES, active)]
    }

    fn test_consumer_interaction(
        message: &[u8],
        uses: &[u32],
        relation: &FieldBytesRelation,
    ) -> (Vec<MdocPrivateMessageColumnEval>, QM31) {
        assert_eq!(message.len(), uses.len());
        let trace = test_consumer_trace();
        let mut logup = LogupTraceGenerator::new(LOG_N_LANES);
        for first_index in (0..message.len()).step_by(2) {
            logup.col_from_fn(|vec_row| {
                let entry = |index: usize| {
                    (
                        PackedQM31::from(
                            trace[0].data[vec_row]
                                * PackedM31::broadcast(M31::from_u32_unchecked(uses[index])),
                        ),
                        relation.combine(&[
                            PackedM31::broadcast(M31::from_u32_unchecked(HOSTED_MSG_FIELD_ID)),
                            PackedM31::broadcast(M31::from_u32_unchecked(index as u32)),
                            PackedM31::broadcast(M31::from_u32_unchecked(u32::from(
                                message[index],
                            ))),
                        ]),
                    )
                };
                let (left_numerator, left_denominator) = entry(first_index);
                if first_index + 1 == message.len() {
                    return (left_numerator, left_denominator);
                }
                let (right_numerator, right_denominator) = entry(first_index + 1);
                (
                    left_numerator * right_denominator + right_numerator * left_denominator,
                    left_denominator * right_denominator,
                )
            });
        }
        logup.finalize_last()
    }

    struct TestMessageUseConsumer {
        message: Vec<u8>,
        uses: Vec<u32>,
        handle: SharedFieldRelation,
        relation: Option<FieldBytesRelation>,
        claimed_sum: Option<QM31>,
        component: Option<FrameworkComponent<TestMessageUseEval>>,
    }

    impl TestMessageUseConsumer {
        fn new(message: Vec<u8>, uses: Vec<u32>, handle: SharedFieldRelation) -> Self {
            assert_eq!(message.len(), uses.len());
            assert!(!message.is_empty());
            Self {
                message,
                uses,
                handle,
                relation: None,
                claimed_sum: None,
                component: None,
            }
        }

        fn relation(&self) -> FieldBytesRelation {
            self.relation
                .clone()
                .expect("test message-use relation is drawn")
        }

        fn claimed_sum(&self) -> QM31 {
            self.claimed_sum
                .expect("test message-use claimed sum is set")
        }
    }

    impl Air for TestMessageUseConsumer {
        fn mix_public(&self, channel: &mut Blake2sChannel) {
            channel.mix_u64(TEST_CONSUMER_DOMAIN);
            channel.mix_u64(self.message.len() as u64);
            for (&byte, &uses) in self.message.iter().zip(&self.uses) {
                channel.mix_u64(u64::from(byte));
                channel.mix_u64(u64::from(uses));
            }
        }

        fn draw_relations(&mut self, _channel: &mut Blake2sChannel) {
            let relation = self.handle.get();
            self.claimed_sum =
                Some(test_consumer_interaction(&self.message, &self.uses, &relation).1);
            self.relation = Some(relation);
        }

        fn layout(&self) -> TreeLayout {
            TreeLayout {
                preprocessed: Vec::new(),
                trace: vec![LOG_N_LANES],
                interaction: vec![
                    LOG_N_LANES;
                    self.message.len().div_ceil(2) * SECURE_EXTENSION_DEGREE
                ],
            }
        }

        fn claimed_sums(&self) -> Vec<QM31> {
            vec![self.claimed_sum()]
        }

        fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
            Vec::new()
        }

        fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
            self.component = Some(FrameworkComponent::new(
                allocator,
                TestMessageUseEval {
                    message: self.message.clone(),
                    uses: self.uses.clone(),
                    relation: self.relation(),
                },
                self.claimed_sum(),
            ));
        }

        fn components(&self) -> Vec<&dyn Component> {
            vec![self
                .component
                .as_ref()
                .expect("test message-use component is built")]
        }
    }

    impl AirProver for TestMessageUseConsumer {
        fn max_log_size(&self) -> u32 {
            LOG_N_LANES
        }

        fn max_constraint_log_degree_bound(&self) -> u32 {
            LOG_N_LANES + 1
        }

        fn write_preprocessed(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

        fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
            Vec::new()
        }

        fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
            tb.extend_evals(test_consumer_trace());
        }

        fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
            let (trace, claimed_sum) =
                test_consumer_interaction(&self.message, &self.uses, &self.relation());
            debug_assert_eq!(claimed_sum, self.claimed_sum());
            tb.extend_evals(trace);
        }

        fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
            vec![self
                .component
                .as_ref()
                .expect("test message-use component is built")]
        }
    }

    struct TestMessageUseProof {
        stark: stwo::core::proof::StarkProof<air_core::Hasher>,
        provider_claim: MdocPrivateMessageInteractionClaim,
    }

    fn prove_message_uses(
        message: &[u8],
        provider_extra_uses: &[u32],
        consumer_uses: &[u32],
    ) -> TestMessageUseProof {
        let handle = SharedFieldRelation::new();
        let mut provider = MdocPrivateMessageProvider::new(
            message.to_vec(),
            provider_extra_uses.to_vec(),
            handle.clone(),
        )
        .unwrap();
        let mut consumer =
            TestMessageUseConsumer::new(message.to_vec(), consumer_uses.to_vec(), handle);
        let stark = air_core::prove(
            &mut [&mut provider, &mut consumer],
            stwo::core::pcs::PcsConfig::default(),
        )
        .expect("private message use fixture proves");
        TestMessageUseProof {
            stark,
            provider_claim: provider.claim().clone(),
        }
    }

    fn verify_message_uses(
        message: &[u8],
        consumer_uses: &[u32],
        proof: &TestMessageUseProof,
    ) -> Result<(), air_core::VerifyError> {
        let handle = SharedFieldRelation::new();
        let mut provider = MdocPrivateMessageProvider::verifier(
            message.len(),
            handle.clone(),
            proof.provider_claim.clone(),
        )
        .unwrap();
        let mut consumer =
            TestMessageUseConsumer::new(message.to_vec(), consumer_uses.to_vec(), handle);
        air_core::verify_with_expected_preprocessed_root(
            &mut [&mut provider, &mut consumer],
            &proof.stark,
            None,
        )
    }

    fn assert_logup_unbalanced(error: air_core::VerifyError) {
        match error {
            air_core::VerifyError::Stark(VerificationError::InvalidStructure(reason)) => {
                assert_eq!(reason, "LogUp claimed sums do not cancel")
            }
            other => panic!("expected global LogUp imbalance, got {other:?}"),
        }
    }

    fn provider_net_claim(
        provider: &MdocPrivateMessageProvider,
        message_relation: &FieldBytesRelation,
        blinder_relation: &ClaimedSumBlinderRelation,
        blinder_v: QM31,
        blinder_m: QM31,
    ) -> QM31 {
        let provider_claim = private_message_interaction_trace(
            provider.message_len,
            provider.log_size,
            provider.witness.as_ref().unwrap(),
            message_relation,
            blinder_relation,
            blinder_v,
            blinder_m,
        )
        .1;
        let blinder_claim =
            blinder_counter_interaction(provider.log_size, blinder_relation, blinder_v, blinder_m)
                .1;
        provider_claim + blinder_claim
    }

    #[test]
    fn rejects_zero_over_cap_shape_overflow_and_bad_multiplicity_shape() {
        assert_eq!(
            MdocPrivateMessageProvider::new(Vec::new(), Vec::new(), SharedFieldRelation::new())
                .err(),
            Some(MdocPrivateMessageError::EmptyMessage)
        );
        assert_eq!(
            MdocPrivateMessageProvider::verifier(
                MDOC_PRIVATE_MESSAGE_MAX_BYTES + 1,
                SharedFieldRelation::new(),
                claim(),
            )
            .err(),
            Some(MdocPrivateMessageError::MessageTooLong {
                length: MDOC_PRIVATE_MESSAGE_MAX_BYTES + 1,
                max: MDOC_PRIVATE_MESSAGE_MAX_BYTES,
            })
        );
        assert_eq!(
            checked_log_size(usize::MAX),
            Err(MdocPrivateMessageError::TraceSizeOverflow {
                message_len: usize::MAX,
            })
        );
        assert!(MdocPrivateMessageProvider::new(
            vec![0; MDOC_PRIVATE_MESSAGE_MAX_BYTES],
            vec![0; MDOC_PRIVATE_MESSAGE_MAX_BYTES],
            SharedFieldRelation::new(),
        )
        .is_ok());
        assert_eq!(
            MdocPrivateMessageProvider::new(vec![1, 2], vec![0], SharedFieldRelation::new(),).err(),
            Some(MdocPrivateMessageError::ExtraUsesLengthMismatch {
                message_len: 2,
                extra_uses_len: 1,
            })
        );
        assert_eq!(
            MdocPrivateMessageProvider::new(
                vec![1],
                vec![MAX_EXTRA_USES + 1],
                SharedFieldRelation::new(),
            )
            .err(),
            Some(MdocPrivateMessageError::ExtraUsesOverflow {
                index: 0,
                extra_uses: MAX_EXTRA_USES + 1,
            })
        );
    }

    #[test]
    fn equal_length_private_messages_have_identical_public_shape() {
        let mut first = MdocPrivateMessageProvider::new(
            vec![1, 2, 3],
            vec![0, 0, 0],
            SharedFieldRelation::new(),
        )
        .unwrap();
        let mut second = MdocPrivateMessageProvider::new(
            vec![9, 8, 7],
            vec![3, 2, 1],
            SharedFieldRelation::new(),
        )
        .unwrap();

        assert_eq!(
            first.preprocessed_column_ids(),
            second.preprocessed_column_ids()
        );
        assert_eq!(
            first.preprocessed_column_fingerprints(),
            second.preprocessed_column_fingerprints()
        );
        let mut first_channel = Blake2sChannel::default();
        let mut second_channel = Blake2sChannel::default();
        first.mix_public(&mut first_channel);
        second.mix_public(&mut second_channel);
        assert_eq!(
            FieldBytesRelation::draw(&mut first_channel),
            FieldBytesRelation::draw(&mut second_channel)
        );
    }

    #[test]
    fn active_trace_commits_exact_bytes_and_extra_uses() {
        let provider = MdocPrivateMessageProvider::new(
            vec![0, 255, 42],
            vec![0, 2, 7],
            SharedFieldRelation::new(),
        )
        .unwrap();
        let public = private_message_preprocessed_columns(provider.message_len, provider.log_size);
        for index in 0..provider.message_len {
            assert_eq!(logical_value(&public[0], provider.log_size, index), 1);
            assert_eq!(
                logical_value(&public[1], provider.log_size, index),
                index as u32
            );
        }
        assert_eq!(
            logical_value(&public[0], provider.log_size, provider.message_len),
            0
        );
        assert_eq!(
            logical_value(&public[1], provider.log_size, provider.message_len),
            provider.message_len as u32
        );

        let trace = provider.witness.as_ref().unwrap().trace(provider.log_size);
        for (index, expected) in [0, 255, 42].into_iter().enumerate() {
            assert_eq!(logical_value(&trace[0], provider.log_size, index), expected);
        }
        for (index, expected) in [0, 2, 7].into_iter().enumerate() {
            assert_eq!(logical_value(&trace[1], provider.log_size, index), expected);
        }
    }

    #[test]
    fn inactive_trace_cells_are_fresh_for_both_private_columns() {
        let first =
            MdocPrivateMessageProvider::new(vec![7, 8], vec![1, 0], SharedFieldRelation::new())
                .unwrap();
        let second =
            MdocPrivateMessageProvider::new(vec![7, 8], vec![1, 0], SharedFieldRelation::new())
                .unwrap();
        let first = first.witness.as_ref().unwrap();
        let second = second.witness.as_ref().unwrap();
        assert_ne!(&first.bytes[2..], &second.bytes[2..]);
        assert_ne!(&first.extra_uses[2..], &second.extra_uses[2..]);
    }

    #[test]
    fn per_position_multiplicity_changes_break_claim_balance_and_cap_is_exact() {
        let mut channel = Blake2sChannel::default();
        let message_relation = FieldBytesRelation::draw(&mut channel);
        let blinder_relation = ClaimedSumBlinderRelation::draw(&mut channel);
        let blinder_v = qm31(17);
        let blinder_m = qm31(19);
        let message = [2, 3, 5, 7, 11, 13, 17];
        let expected_extra_uses = vec![1; message.len()];
        let expected_consumer_uses = vec![2; message.len()];
        let consumer_claim =
            test_consumer_interaction(&message, &expected_consumer_uses, &message_relation).1;
        let balance = |extra_uses: Vec<u32>| {
            let provider = MdocPrivateMessageProvider::new(
                message.to_vec(),
                extra_uses,
                SharedFieldRelation::new(),
            )
            .unwrap();
            provider_net_claim(
                &provider,
                &message_relation,
                &blinder_relation,
                blinder_v,
                blinder_m,
            ) + consumer_claim
        };

        assert_eq!(balance(expected_extra_uses.clone()), qm31(0));
        for index in 0..message.len() {
            let mut missing_provider_use = expected_extra_uses.clone();
            missing_provider_use[index] -= 1;
            assert_ne!(
                balance(missing_provider_use),
                qm31(0),
                "one missing provider use at byte {index} must not balance"
            );

            let mut extra_provider_use = expected_extra_uses.clone();
            extra_provider_use[index] += 1;
            assert_ne!(
                balance(extra_provider_use),
                qm31(0),
                "one extra provider use at byte {index} must not balance"
            );
        }

        let max_provider = MdocPrivateMessageProvider::new(
            vec![23],
            vec![MAX_EXTRA_USES],
            SharedFieldRelation::new(),
        )
        .unwrap();
        let max_consumer_claim =
            test_consumer_interaction(&[23], &[MAX_EXTRA_USES + 1], &message_relation).1;
        assert_eq!(
            provider_net_claim(
                &max_provider,
                &message_relation,
                &blinder_relation,
                blinder_v,
                blinder_m,
            ) + max_consumer_claim,
            qm31(0),
            "the largest non-wrapping M31 multiplicity must remain usable"
        );
        assert_eq!(
            MdocPrivateMessageProvider::new(
                vec![23, 29],
                vec![0, MAX_EXTRA_USES + 1],
                SharedFieldRelation::new(),
            )
            .err(),
            Some(MdocPrivateMessageError::ExtraUsesOverflow {
                index: 1,
                extra_uses: MAX_EXTRA_USES + 1,
            })
        );
    }

    #[test]
    fn composed_mu_consumer_is_total_and_rejects_missing_or_extra_use_claims() {
        let message: Vec<u8> = (0..37)
            .map(|index| (index as u8).wrapping_mul(29).wrapping_add(7))
            .collect();
        let provider_extra_uses = vec![0; message.len()];
        let complete_uses = vec![1; message.len()];

        let honest = prove_message_uses(&message, &provider_extra_uses, &complete_uses);
        verify_message_uses(&message, &complete_uses, &honest)
            .expect("one mu use for every private-message index must verify");

        for (index, altered_uses) in [
            (0, 0),
            (message.len() / 2, 0),
            (message.len() - 1, 0),
            (message.len() / 2, 2),
        ] {
            let mut uses = complete_uses.clone();
            uses[index] = altered_uses;
            let malformed = prove_message_uses(&message, &provider_extra_uses, &uses);
            let error = verify_message_uses(&message, &uses, &malformed)
                .expect_err("unbalanced private-message use proof must be rejected");
            assert_logup_unbalanced(error);
        }
    }

    #[test]
    fn layout_claim_serialization_and_component_order_are_fixed() {
        let expected_claim = claim();
        let encoded = bincode::serialize(&expected_claim).unwrap();
        let decoded: MdocPrivateMessageInteractionClaim = bincode::deserialize(&encoded).unwrap();
        assert_eq!(decoded, expected_claim);

        let handle = SharedFieldRelation::new();
        let mut provider =
            MdocPrivateMessageProvider::verifier(17, handle.clone(), decoded).unwrap();
        assert_eq!(provider.message_len(), 17);
        assert_eq!(provider.log_size(), 9);
        let layout = provider.layout();
        assert_eq!(layout.preprocessed, vec![9; 2]);
        assert_eq!(layout.trace, vec![9; 2]);
        assert_eq!(layout.interaction, vec![9; 2 * SECURE_EXTENSION_DEGREE]);
        assert_eq!(provider.claimed_sums(), vec![qm31(1), qm31(4)]);

        let mut channel = Blake2sChannel::default();
        provider.draw_relations(&mut channel);
        assert!(handle.is_set());
        let ids = provider.preprocessed_column_ids();
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids.as_slice());
        provider.build_components(&mut allocator);
        assert_eq!(
            provider.components().len(),
            2,
            "main provider must be followed immediately by its blinder counterpart"
        );
    }

    #[test]
    fn provider_air_stays_within_the_degree_two_budget() {
        let provider =
            MdocPrivateMessageProvider::new(vec![1], vec![0], SharedFieldRelation::new()).unwrap();
        let eval = MdocPrivateMessageEval {
            message_len: provider.message_len,
            log_size: provider.log_size,
            message_relation: FieldBytesRelation::dummy(),
            blinder_relation: ClaimedSumBlinderRelation::dummy(),
            blinder_v: qm31(1),
            blinder_m: qm31(2),
        };
        assert_eq!(
            FrameworkEval::max_constraint_log_degree_bound(&eval),
            provider.log_size + 1
        );
        assert_eq!(
            AirProver::max_constraint_log_degree_bound(&provider),
            provider.log_size + 1
        );
    }
}
