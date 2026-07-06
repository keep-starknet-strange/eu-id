//! M31-side mdoc P4b Longfellow GF(2^128) MAC binding.
//!
//! The committed trace only carries one bit-serial row per MAC bit. The
//! `a_v`-dependent terms live in the post-interaction tree after the shared
//! MAC challenge is published.

use std::{cell::RefCell, rc::Rc};

use air_core::relations::{
    field_id, DigestBytesRelation, FieldBytesRelation, SharedDigestRelation, SharedFieldRelation,
};
use air_core::{fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint};
use eu_id_ec_coprocessor::mac::Gf128;
use serde::{Deserialize, Serialize};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
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
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator,
};

const MACS_PER_PROOF: usize = 6;
const HALF_BYTES: usize = 16;
const GF_BITS: usize = 128;
const ACTIVE_ROWS: usize = MACS_PER_PROOF * GF_BITS;
const CONSUMER_LOG_SIZE: u32 = 10;
const BINDING_LOG_SIZE: u32 = 4;
const CONSUMER_PREPROCESSED_COLS: usize = 3 + MACS_PER_PROOF + GF_BITS;
const BINDING_PREPROCESSED_COLS: usize = 5;
const CONSUMER_TRACE_COLS: usize = 1 + GF_BITS;
const POST_TRACE_COLS: usize = 2 * GF_BITS;
const BINDING_TRACE_COLS: usize = 32;
const INTERACTION_COLS_PER_FRACTION: usize = 4;
const CONSUMER_INTERACTION_COLS: usize = INTERACTION_COLS_PER_FRACTION;
const BINDING_INTERACTION_COLS: usize = 18 * INTERACTION_COLS_PER_FRACTION;
const CHECK_NEW_SELECTOR_BOOLS: bool = false;
const CHECK_S_CONSTRAINTS: bool = true;
const CHECK_POST_COLUMN_CONSTRAINTS: bool = true;
const CHECK_POST_CONSTRAINTS: bool = true;
const CHECK_POST_FINAL_TAG: bool = true;

type MacColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type ConsumerComponent = FrameworkComponent<MacConsumerEval>;
type BindingComponent = FrameworkComponent<MacBindingEval>;

relation!(MacHalfRelation, 17);

#[derive(Clone)]
struct MacHalfWitness {
    ap: [u8; HALF_BYTES],
    x: [u8; HALF_BYTES],
}

#[derive(Clone, Debug, Default)]
pub(crate) struct MdocP4bMacSharedState(Rc<RefCell<Option<MdocP4bMacPublic>>>);

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct MdocP4bMacPublic {
    pub(crate) av: Gf128,
    pub(crate) tags: Vec<Gf128>,
}

impl MdocP4bMacSharedState {
    pub(crate) fn publish(&self, public: MdocP4bMacPublic) {
        *self.0.borrow_mut() = Some(public);
    }

    fn get(&self) -> Option<MdocP4bMacPublic> {
        self.0.borrow().clone()
    }
}

pub(crate) struct MdocMacBind {
    rows: [MacHalfWitness; MACS_PER_PROOF],
    mac_state: Option<MdocP4bMacSharedState>,
    issuer_digest_handle: Option<SharedDigestRelation>,
    issuer_field_handle: Option<SharedFieldRelation>,
    av: Option<[u8; HALF_BYTES]>,
    tags: Option<[[u8; HALF_BYTES]; MACS_PER_PROOF]>,
    mac_half_relation: Option<MacHalfRelation>,
    interaction_claim: Option<MdocMacInteractionClaim>,
    consumer_component: Option<ConsumerComponent>,
    binding_component: Option<BindingComponent>,
}

impl Clone for MdocMacBind {
    fn clone(&self) -> Self {
        Self {
            rows: self.rows.clone(),
            mac_state: self.mac_state.clone(),
            issuer_digest_handle: self.issuer_digest_handle.clone(),
            issuer_field_handle: self.issuer_field_handle.clone(),
            tags: self.tags,
            av: self.av,
            mac_half_relation: None,
            interaction_claim: self.interaction_claim.clone(),
            consumer_component: None,
            binding_component: None,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct MdocMacInteractionClaim {
    pub(crate) consumer: QM31,
    pub(crate) binding: QM31,
}

#[derive(Clone)]
struct MacConsumerEval {
    mac_half_relation: MacHalfRelation,
    av: [u8; HALF_BYTES],
    tags: [[u8; HALF_BYTES]; MACS_PER_PROOF],
}

#[derive(Clone)]
struct MacBindingEval {
    mac_half_relation: MacHalfRelation,
    issuer_digest_relation: DigestBytesRelation,
    issuer_field_relation: FieldBytesRelation,
}

impl MdocMacBind {
    pub(crate) fn prover(
        mac_key_shares: &eu_id_ec_coprocessor::ecdsa::MdocP4bMacKeyShares,
        mac_values: [Gf128; MACS_PER_PROOF],
        mac_state: MdocP4bMacSharedState,
        issuer_digest_handle: SharedDigestRelation,
        issuer_field_handle: SharedFieldRelation,
    ) -> Self {
        Self {
            rows: std::array::from_fn(|index| MacHalfWitness {
                ap: mac_key_shares.0[index],
                x: mac_values[index],
            }),
            mac_state: Some(mac_state),
            issuer_digest_handle: Some(issuer_digest_handle),
            issuer_field_handle: Some(issuer_field_handle),
            av: None,
            tags: None,
            mac_half_relation: None,
            interaction_claim: None,
            consumer_component: None,
            binding_component: None,
        }
    }

    pub(crate) fn verifier(
        mac_state: MdocP4bMacSharedState,
        issuer_digest_handle: SharedDigestRelation,
        issuer_field_handle: SharedFieldRelation,
        interaction_claim: MdocMacInteractionClaim,
    ) -> Self {
        Self {
            rows: std::array::from_fn(|_| MacHalfWitness {
                ap: [0; HALF_BYTES],
                x: [0; HALF_BYTES],
            }),
            mac_state: Some(mac_state),
            issuer_digest_handle: Some(issuer_digest_handle),
            issuer_field_handle: Some(issuer_field_handle),
            av: None,
            tags: None,
            mac_half_relation: None,
            interaction_claim: Some(interaction_claim),
            consumer_component: None,
            binding_component: None,
        }
    }

    fn mac_half_relation(&self) -> &MacHalfRelation {
        self.mac_half_relation
            .as_ref()
            .expect("MAC half relation drawn before use")
    }

    fn issuer_digest_relation(&self) -> DigestBytesRelation {
        self.issuer_digest_handle
            .as_ref()
            .expect("issuer digest handle is set")
            .get()
    }

    fn issuer_field_relation(&self) -> FieldBytesRelation {
        self.issuer_field_handle
            .as_ref()
            .expect("issuer field handle is set")
            .get()
    }

    pub(crate) fn interaction_claim(&self) -> &MdocMacInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("mdoc MAC interaction claim is set")
    }

    fn public_from_state(
        &self,
    ) -> Result<([u8; HALF_BYTES], [[u8; HALF_BYTES]; MACS_PER_PROOF]), String> {
        let public = self
            .mac_state
            .as_ref()
            .and_then(MdocP4bMacSharedState::get)
            .ok_or_else(|| "mdoc MAC public state missing".to_string())?;
        let tags: [[u8; HALF_BYTES]; MACS_PER_PROOF] =
            public.tags.try_into().map_err(|tags: Vec<Gf128>| {
                format!("expected {MACS_PER_PROOF} MAC tags, got {}", tags.len())
            })?;
        Ok((public.av, tags))
    }
}

impl Air for MdocMacBind {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(0x4d44_4f43_4d41_4303);
        channel.mix_u64(MACS_PER_PROOF as u64);
        channel.mix_u64(GF_BITS as u64);
        channel.mix_u64(ACTIVE_ROWS as u64);
        channel.mix_u64(POST_TRACE_COLS as u64);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.mac_half_relation = Some(MacHalfRelation::draw(channel));
    }

    fn layout(&self) -> air_core::TreeLayout {
        air_core::TreeLayout {
            preprocessed: std::iter::repeat_n(CONSUMER_LOG_SIZE, CONSUMER_PREPROCESSED_COLS)
                .chain(std::iter::repeat_n(
                    BINDING_LOG_SIZE,
                    BINDING_PREPROCESSED_COLS,
                ))
                .collect(),
            trace: std::iter::repeat_n(CONSUMER_LOG_SIZE, CONSUMER_TRACE_COLS)
                .chain(std::iter::repeat_n(BINDING_LOG_SIZE, BINDING_TRACE_COLS))
                .collect(),
            interaction: std::iter::repeat_n(CONSUMER_LOG_SIZE, CONSUMER_INTERACTION_COLS)
                .chain(std::iter::repeat_n(
                    BINDING_LOG_SIZE,
                    BINDING_INTERACTION_COLS,
                ))
                .collect(),
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        let claim = self.interaction_claim();
        vec![claim.consumer, claim.binding]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut ids = Vec::with_capacity(CONSUMER_PREPROCESSED_COLS + BINDING_PREPROCESSED_COLS);
        ids.push(mac_col_id("consumer/active"));
        ids.push(mac_col_id("consumer/first"));
        ids.push(mac_col_id("consumer/last"));
        ids.extend((0..MACS_PER_PROOF).map(|i| mac_col_id(&format!("consumer/mac_{i}"))));
        ids.extend((0..GF_BITS).map(|i| mac_col_id(&format!("consumer/step_{i}"))));
        ids.push(mac_col_id("binding/active"));
        ids.push(mac_col_id("binding/digest_active"));
        ids.push(mac_col_id("binding/field_active"));
        ids.push(mac_col_id("binding/field_id"));
        ids.push(mac_col_id("binding/slot"));
        ids
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let av = self.av.unwrap_or([0; HALF_BYTES]);
        let tags = self.tags.unwrap_or([[0; HALF_BYTES]; MACS_PER_PROOF]);
        self.consumer_component = Some(ConsumerComponent::new(
            allocator,
            MacConsumerEval {
                mac_half_relation: self.mac_half_relation().clone(),
                av,
                tags,
            },
            self.interaction_claim().consumer,
        ));
        self.binding_component = Some(BindingComponent::new(
            allocator,
            MacBindingEval {
                mac_half_relation: self.mac_half_relation().clone(),
                issuer_digest_relation: self.issuer_digest_relation(),
                issuer_field_relation: self.issuer_field_relation(),
            },
            self.interaction_claim().binding,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![
            self.consumer_component
                .as_ref()
                .expect("consumer component built"),
            self.binding_component
                .as_ref()
                .expect("binding component built"),
        ]
    }

    fn post_interaction_log_sizes(&self) -> Vec<u32> {
        if CHECK_POST_COLUMN_CONSTRAINTS || CHECK_POST_CONSTRAINTS {
            std::iter::repeat_n(CONSUMER_LOG_SIZE, POST_TRACE_COLS).collect()
        } else {
            Vec::new()
        }
    }

    fn verify_post_interaction(
        &mut self,
        channel: &mut Blake2sChannel,
    ) -> Result<(), stwo::core::verifier::VerificationError> {
        let (av, tags) = self
            .public_from_state()
            .map_err(stwo::core::verifier::VerificationError::InvalidStructure)?;
        mix_av_and_tags(channel, &av, &tags);
        self.av = Some(av);
        self.tags = Some(tags);
        Ok(())
    }
}

impl AirProver for MdocMacBind {
    fn max_log_size(&self) -> u32 {
        CONSUMER_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        CONSUMER_LOG_SIZE + 1
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(preprocessed_trace());
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc_mac",
            &self.preprocessed_column_ids(),
            &preprocessed_trace(),
        )
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(consumer_trace(&self.rows));
        tb.extend_evals(binding_trace(&self.rows));
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let (consumer_trace, consumer_claim) =
            consumer_interaction_trace(&self.rows, self.mac_half_relation());
        let (binding_trace, binding_claim) = binding_interaction_trace(
            &self.rows,
            self.mac_half_relation(),
            &self.issuer_digest_relation(),
            &self.issuer_field_relation(),
        );
        tb.extend_evals(consumer_trace);
        tb.extend_evals(binding_trace);
        self.interaction_claim = Some(MdocMacInteractionClaim {
            consumer: consumer_claim,
            binding: binding_claim,
        });
    }

    fn prove_post_interaction(&mut self, channel: &mut Blake2sChannel) {
        let (av, tags) = self
            .public_from_state()
            .expect("mdoc MAC public values are published before MAC post-interaction");
        mix_av_and_tags(channel, &av, &tags);
        self.av = Some(av);
        self.tags = Some(tags);
    }

    fn write_post_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let av = self.av.expect("a_v set before post-interaction trace");
        tb.extend_evals(post_interaction_trace(&self.rows, &av));
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            self.consumer_component
                .as_ref()
                .expect("consumer component built"),
            self.binding_component
                .as_ref()
                .expect("binding component built"),
        ]
    }
}

impl FrameworkEval for MacConsumerEval {
    fn log_size(&self) -> u32 {
        CONSUMER_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        CONSUMER_LOG_SIZE + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(mac_col_id("consumer/active"));
        let first = eval.get_preprocessed_column(mac_col_id("consumer/first"));
        let last = eval.get_preprocessed_column(mac_col_id("consumer/last"));
        let mac_selectors = (0..MACS_PER_PROOF)
            .map(|i| eval.get_preprocessed_column(mac_col_id(&format!("consumer/mac_{i}"))))
            .collect::<Vec<_>>();
        let step_selectors = (0..GF_BITS)
            .map(|i| eval.get_preprocessed_column(mac_col_id(&format!("consumer/step_{i}"))))
            .collect::<Vec<_>>();
        let one = m31_const::<E>(1);

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint(first.clone() * (first.clone() - one.clone()));
        eval.add_constraint(last.clone() * (last.clone() - one.clone()));
        eval.add_constraint(first.clone() * (one.clone() - active.clone()));
        eval.add_constraint(last.clone() * (one.clone() - active.clone()));
        for selector in &mac_selectors {
            if CHECK_NEW_SELECTOR_BOOLS {
                eval.add_constraint(selector.clone() * (selector.clone() - one.clone()));
            }
        }
        for selector in &step_selectors {
            if CHECK_NEW_SELECTOR_BOOLS {
                eval.add_constraint(selector.clone() * (selector.clone() - one.clone()));
            }
        }

        let ap_bit = eval.next_trace_mask();
        let s_pairs = (0..GF_BITS)
            .map(|_| {
                eval.next_interaction_mask(stwo_constraint_framework::ORIGINAL_TRACE_IDX, [0, -1])
            })
            .collect::<Vec<_>>();
        let term_bits = if CHECK_POST_COLUMN_CONSTRAINTS || CHECK_POST_CONSTRAINTS {
            (0..GF_BITS)
                .map(|_| eval.next_interaction_mask::<1>(3, [0])[0].clone())
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        };
        let post_acc_pairs = if CHECK_POST_COLUMN_CONSTRAINTS || CHECK_POST_CONSTRAINTS {
            (0..GF_BITS)
                .map(|_| eval.next_interaction_mask(3, [0, -1]))
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        };
        let s_bits = s_pairs
            .iter()
            .map(|pair| pair[0].clone())
            .collect::<Vec<_>>();
        let s_prev_bits = s_pairs
            .iter()
            .map(|pair| pair[1].clone())
            .collect::<Vec<_>>();
        let post_acc_bits = post_acc_pairs
            .iter()
            .map(|pair| pair[0].clone())
            .collect::<Vec<_>>();
        let post_acc_prev_bits = post_acc_pairs
            .iter()
            .map(|pair| pair[1].clone())
            .collect::<Vec<_>>();

        eval.add_constraint(ap_bit.clone() * (ap_bit.clone() - one.clone()));
        eval.add_constraint((one.clone() - active.clone()) * ap_bit.clone());
        for bit in &s_bits {
            eval.add_constraint(bit.clone() * (bit.clone() - one.clone()));
            eval.add_constraint((one.clone() - active.clone()) * bit.clone());
        }
        for bit in &post_acc_bits {
            if CHECK_POST_COLUMN_CONSTRAINTS {
                eval.add_constraint(bit.clone() * (bit.clone() - one.clone()));
                eval.add_constraint((one.clone() - active.clone()) * bit.clone());
            }
        }
        for bit in &term_bits {
            if CHECK_POST_COLUMN_CONSTRAINTS {
                eval.add_constraint(bit.clone() * (bit.clone() - one.clone()));
                eval.add_constraint((one.clone() - active.clone()) * bit.clone());
            }
        }

        let mut mac_index = m31_const::<E>(0);
        for (index, selector) in mac_selectors.iter().enumerate() {
            mac_index += selector.clone() * m31_const::<E>(index as u32);
        }
        let mut half_values = Vec::with_capacity(1 + HALF_BYTES);
        half_values.push(mac_index);
        for byte_index in 0..HALF_BYTES {
            let bit = byte_index * 8;
            half_values.push(byte_expr::<E>(&s_bits[bit..bit + 8]));
        }
        eval.add_to_relation(RelationEntry::new(
            &self.mac_half_relation,
            -E::EF::from(first.clone()),
            &half_values,
        ));

        if CHECK_S_CONSTRAINTS {
            for bit_index in 0..GF_BITS {
                let expected = mul_x_bit_expr::<E>(bit_index, &s_prev_bits);
                eval.add_constraint(
                    (active.clone() - first.clone()) * (s_bits[bit_index].clone() - expected),
                );
            }
        }

        let av_bits = bytes_to_bits(&self.av);
        let mut av_row_bit = m31_const::<E>(0);
        for (selector, bit) in step_selectors.iter().zip(av_bits) {
            if bit {
                av_row_bit += selector.clone();
            }
        }
        let tag_bits = self
            .tags
            .iter()
            .map(bytes_to_bits)
            .collect::<Vec<[bool; GF_BITS]>>();
        if CHECK_POST_CONSTRAINTS {
            for bit_index in 0..GF_BITS {
                let term = term_bits[bit_index].clone();
                let key_bit = xor_expr::<E>(ap_bit.clone(), av_row_bit.clone());
                eval.add_constraint(term.clone() - key_bit * s_bits[bit_index].clone());
                let expected = first.clone() * term.clone()
                    + (active.clone() - first.clone())
                        * xor_expr::<E>(post_acc_prev_bits[bit_index].clone(), term);
                eval.add_constraint(post_acc_bits[bit_index].clone() - expected);
                let mut tag_bit = m31_const::<E>(0);
                for (mac_index, selector) in mac_selectors.iter().enumerate() {
                    if tag_bits[mac_index][bit_index] {
                        tag_bit += selector.clone();
                    }
                }
                if CHECK_POST_FINAL_TAG {
                    eval.add_constraint(
                        last.clone() * (post_acc_bits[bit_index].clone() - tag_bit),
                    );
                }
            }
        }

        eval.finalize_logup();
        eval
    }
}

impl FrameworkEval for MacBindingEval {
    fn log_size(&self) -> u32 {
        BINDING_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        BINDING_LOG_SIZE + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(mac_col_id("binding/active"));
        let digest_active = eval.get_preprocessed_column(mac_col_id("binding/digest_active"));
        let field_active = eval.get_preprocessed_column(mac_col_id("binding/field_active"));
        let field_id_col = eval.get_preprocessed_column(mac_col_id("binding/field_id"));
        let slot = eval.get_preprocessed_column(mac_col_id("binding/slot"));
        let one = m31_const::<E>(1);

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint(digest_active.clone() * (digest_active.clone() - one.clone()));
        eval.add_constraint(field_active.clone() * (field_active.clone() - one.clone()));
        eval.add_constraint(digest_active.clone() * (one.clone() - active.clone()));
        eval.add_constraint(field_active.clone() * (one.clone() - active.clone()));

        let bytes = (0..32).map(|_| eval.next_trace_mask()).collect::<Vec<_>>();
        for byte in &bytes {
            eval.add_constraint((one.clone() - active.clone()) * byte.clone());
        }

        eval.add_to_relation(RelationEntry::new(
            &self.issuer_digest_relation,
            E::EF::from(digest_active.clone()),
            &bytes,
        ));

        for (byte_idx, byte) in bytes.iter().enumerate() {
            eval.add_to_relation(RelationEntry::new(
                &self.issuer_field_relation,
                E::EF::from(field_active.clone()),
                &[
                    field_id_col.clone(),
                    m31_const::<E>(byte_idx as u32),
                    byte.clone(),
                ],
            ));
        }

        let lo_index = slot.clone() + slot.clone();
        let hi_index = lo_index.clone() + one.clone();
        let mut lo_values = Vec::with_capacity(1 + HALF_BYTES);
        lo_values.push(lo_index);
        lo_values.extend((0..HALF_BYTES).map(|i| bytes[31 - i].clone()));
        eval.add_to_relation(RelationEntry::new(
            &self.mac_half_relation,
            E::EF::from(active.clone()),
            &lo_values,
        ));
        let mut hi_values = Vec::with_capacity(1 + HALF_BYTES);
        hi_values.push(hi_index);
        hi_values.extend((0..HALF_BYTES).map(|i| bytes[15 - i].clone()));
        eval.add_to_relation(RelationEntry::new(
            &self.mac_half_relation,
            E::EF::from(active),
            &hi_values,
        ));

        eval.finalize_logup_in_pairs();
        eval
    }
}

fn preprocessed_trace() -> Vec<MacColumnEval> {
    let mut columns =
        vec![vec![M31::from_u32_unchecked(0); 1 << CONSUMER_LOG_SIZE]; CONSUMER_PREPROCESSED_COLS];
    for mac_index in 0..MACS_PER_PROOF {
        for step in 0..GF_BITS {
            let row = mac_index * GF_BITS + step;
            columns[0][row] = M31::from_u32_unchecked(1);
            columns[1][row] = M31::from_u32_unchecked(u32::from(step == 0));
            columns[2][row] = M31::from_u32_unchecked(u32::from(step == GF_BITS - 1));
            columns[3 + mac_index][row] = M31::from_u32_unchecked(1);
            columns[3 + MACS_PER_PROOF + step][row] = M31::from_u32_unchecked(1);
        }
    }
    let mut out = columns
        .into_iter()
        .map(|values| column_eval(CONSUMER_LOG_SIZE, values))
        .collect::<Vec<_>>();
    out.extend(binding_preprocessed_trace());
    out
}

fn binding_preprocessed_trace() -> Vec<MacColumnEval> {
    let mut columns =
        vec![vec![M31::from_u32_unchecked(0); 1 << BINDING_LOG_SIZE]; BINDING_PREPROCESSED_COLS];
    for slot in 0..3 {
        columns[0][slot] = M31::from_u32_unchecked(1);
        columns[1][slot] = M31::from_u32_unchecked(u32::from(slot == 0));
        columns[2][slot] = M31::from_u32_unchecked(u32::from(slot != 0));
        columns[3][slot] = M31::from_u32_unchecked(match slot {
            1 => field_id::MDOC_DEVICE_KEY_X,
            2 => field_id::MDOC_DEVICE_KEY_Y,
            _ => 0,
        });
        columns[4][slot] = M31::from_u32_unchecked(slot as u32);
    }
    columns
        .into_iter()
        .map(|values| column_eval(BINDING_LOG_SIZE, values))
        .collect()
}

fn binding_value_rows(rows: &[MacHalfWitness; MACS_PER_PROOF]) -> [[u8; 32]; 3] {
    std::array::from_fn(|slot| {
        let lo = rows[slot * 2].x;
        let hi = rows[slot * 2 + 1].x;
        let mut bytes = [0u8; 32];
        for i in 0..HALF_BYTES {
            bytes[i] = hi[HALF_BYTES - 1 - i];
            bytes[HALF_BYTES + i] = lo[HALF_BYTES - 1 - i];
        }
        bytes
    })
}

fn binding_trace(rows: &[MacHalfWitness; MACS_PER_PROOF]) -> Vec<MacColumnEval> {
    let value_rows = binding_value_rows(rows);
    let mut columns =
        vec![vec![M31::from_u32_unchecked(0); 1 << BINDING_LOG_SIZE]; BINDING_TRACE_COLS];
    for (slot, bytes) in value_rows.iter().enumerate() {
        for (byte_idx, &byte) in bytes.iter().enumerate() {
            columns[byte_idx][slot] = M31::from_u32_unchecked(u32::from(byte));
        }
    }
    columns
        .into_iter()
        .map(|values| column_eval(BINDING_LOG_SIZE, values))
        .collect()
}

fn binding_interaction_trace(
    rows: &[MacHalfWitness; MACS_PER_PROOF],
    mac_half_relation: &MacHalfRelation,
    issuer_digest_relation: &DigestBytesRelation,
    issuer_field_relation: &FieldBytesRelation,
) -> (Vec<MacColumnEval>, QM31) {
    let preprocessed = binding_preprocessed_trace();
    let active = &preprocessed[0];
    let digest_active = &preprocessed[1];
    let field_active = &preprocessed[2];
    let field_ids = &preprocessed[3];
    let slots = &preprocessed[4];
    let bytes = binding_trace(rows);
    let n_vec_rows = bytes[0].data.len();
    let mut sites: Vec<Vec<(PackedQM31, PackedQM31)>> = Vec::with_capacity(35);
    sites.push(
        (0..n_vec_rows)
            .map(|vec_row| {
                let values = (0..32)
                    .map(|byte_idx| bytes[byte_idx].data[vec_row])
                    .collect::<Vec<_>>();
                (
                    PackedQM31::from(digest_active.data[vec_row]),
                    issuer_digest_relation.combine(&values),
                )
            })
            .collect(),
    );
    for byte_idx in 0..32 {
        sites.push(
            (0..n_vec_rows)
                .map(|vec_row| {
                    let values = [
                        field_ids.data[vec_row],
                        PackedM31::broadcast(M31::from_u32_unchecked(byte_idx as u32)),
                        bytes[byte_idx].data[vec_row],
                    ];
                    (
                        PackedQM31::from(field_active.data[vec_row]),
                        issuer_field_relation.combine(&values),
                    )
                })
                .collect(),
        );
    }
    for half in 0..2 {
        sites.push(
            (0..n_vec_rows)
                .map(|vec_row| {
                    let mut values = Vec::with_capacity(1 + HALF_BYTES);
                    let slot = slots.data[vec_row];
                    let mac_index =
                        slot + slot + PackedM31::broadcast(M31::from_u32_unchecked(half));
                    values.push(mac_index);
                    if half == 0 {
                        values.extend((0..HALF_BYTES).map(|i| bytes[31 - i].data[vec_row]));
                    } else {
                        values.extend((0..HALF_BYTES).map(|i| bytes[15 - i].data[vec_row]));
                    }
                    (
                        PackedQM31::from(active.data[vec_row]),
                        mac_half_relation.combine(&values),
                    )
                })
                .collect(),
        );
    }

    let mut logup = LogupTraceGenerator::new(BINDING_LOG_SIZE);
    let mut site_idx = 0usize;
    while site_idx + 1 < sites.len() {
        let left = &sites[site_idx];
        let right = &sites[site_idx + 1];
        logup.col_from_iter((0..n_vec_rows).map(|vec_row| {
            let (n0, d0) = left[vec_row];
            let (n1, d1) = right[vec_row];
            (n0 * d1 + n1 * d0, d0 * d1)
        }));
        site_idx += 2;
    }
    if site_idx < sites.len() {
        let last = &sites[site_idx];
        logup.col_from_iter((0..n_vec_rows).map(|vec_row| last[vec_row]));
    }
    logup.finalize_last()
}

fn consumer_trace(rows: &[MacHalfWitness; MACS_PER_PROOF]) -> Vec<MacColumnEval> {
    let mut columns =
        vec![vec![M31::from_u32_unchecked(0); 1 << CONSUMER_LOG_SIZE]; CONSUMER_TRACE_COLS];
    for (mac_index, row) in rows.iter().enumerate() {
        let ap_bits = bytes_to_bits(&row.ap);
        let ladder = s_ladder(&row.x);
        for step in 0..GF_BITS {
            let out_row = mac_index * GF_BITS + step;
            columns[0][out_row] = M31::from_u32_unchecked(u32::from(ap_bits[step]));
            for bit_index in 0..GF_BITS {
                columns[1 + bit_index][out_row] =
                    M31::from_u32_unchecked(u32::from(ladder[step][bit_index]));
            }
        }
    }
    columns
        .into_iter()
        .map(|values| column_eval(CONSUMER_LOG_SIZE, values))
        .collect()
}

fn consumer_interaction_trace(
    rows: &[MacHalfWitness; MACS_PER_PROOF],
    mac_half_relation: &MacHalfRelation,
) -> (Vec<MacColumnEval>, QM31) {
    let mut first_values = vec![M31::from_u32_unchecked(0); 1 << CONSUMER_LOG_SIZE];
    let mut mac_values = vec![M31::from_u32_unchecked(0); 1 << CONSUMER_LOG_SIZE];
    let mut byte_values =
        vec![vec![M31::from_u32_unchecked(0); 1 << CONSUMER_LOG_SIZE]; HALF_BYTES];
    for row in 0..ACTIVE_ROWS {
        let mac = row / GF_BITS;
        let step = row % GF_BITS;
        first_values[row] = M31::from_u32_unchecked(u32::from(step == 0));
        mac_values[row] = M31::from_u32_unchecked(mac as u32);
        for (byte_idx, column) in byte_values.iter_mut().enumerate() {
            column[row] = M31::from_u32_unchecked(u32::from(rows[mac].x[byte_idx]));
        }
    }
    let first_eval = column_eval(CONSUMER_LOG_SIZE, first_values);
    let mac_eval = column_eval(CONSUMER_LOG_SIZE, mac_values);
    let byte_evals = byte_values
        .into_iter()
        .map(|values| column_eval(CONSUMER_LOG_SIZE, values))
        .collect::<Vec<_>>();
    let mut logup = LogupTraceGenerator::new(CONSUMER_LOG_SIZE);
    logup.col_from_fn(|vec_row| {
        let mut values = Vec::with_capacity(1 + HALF_BYTES);
        values.push(mac_eval.data[vec_row]);
        for byte_idx in 0..HALF_BYTES {
            values.push(byte_evals[byte_idx].data[vec_row]);
        }
        let numerator = -PackedQM31::from(first_eval.data[vec_row]);
        (numerator, mac_half_relation.combine(&values))
    });
    logup.finalize_last()
}

fn post_interaction_trace(
    rows: &[MacHalfWitness; MACS_PER_PROOF],
    av: &[u8; HALF_BYTES],
) -> Vec<MacColumnEval> {
    let mut columns =
        vec![vec![M31::from_u32_unchecked(0); 1 << CONSUMER_LOG_SIZE]; POST_TRACE_COLS];
    let av_bits = bytes_to_bits(av);
    for (mac_index, row) in rows.iter().enumerate() {
        let ap_bits = bytes_to_bits(&row.ap);
        let ladder = s_ladder(&row.x);
        let mut acc = [false; GF_BITS];
        for step in 0..GF_BITS {
            let out_row = mac_index * GF_BITS + step;
            let key_bit = ap_bits[step] ^ av_bits[step];
            for bit in 0..GF_BITS {
                let term = key_bit && ladder[step][bit];
                if term {
                    acc[bit] ^= true;
                }
                columns[bit][out_row] = M31::from_u32_unchecked(u32::from(term));
                columns[GF_BITS + bit][out_row] = M31::from_u32_unchecked(u32::from(acc[bit]));
            }
        }
        debug_assert_eq!(
            bits_to_bytes(&acc),
            gf128_mul(&xor_128(&row.ap, av), &row.x)
        );
    }
    for row in ACTIVE_ROWS..(1 << CONSUMER_LOG_SIZE) {
        for bit in 0..GF_BITS {
            columns[bit][row] = M31::from_u32_unchecked(0);
            columns[GF_BITS + bit][row] = M31::from_u32_unchecked(0);
        }
    }
    columns
        .into_iter()
        .map(|values| column_eval(CONSUMER_LOG_SIZE, values))
        .collect()
}

fn mix_av_and_tags(
    channel: &mut Blake2sChannel,
    av: &[u8; HALF_BYTES],
    tags: &[[u8; HALF_BYTES]; MACS_PER_PROOF],
) {
    channel.mix_u64(0x5034_424d_4143_5447);
    for byte in av {
        channel.mix_u64(u64::from(*byte));
    }
    for tag in tags {
        for byte in tag {
            channel.mix_u64(u64::from(*byte));
        }
    }
}

fn column_eval(log_size: u32, values: Vec<M31>) -> MacColumnEval {
    let mut ordered = vec![M31::from_u32_unchecked(0); 1usize << log_size];
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

fn xor_expr<E: EvalAtRow>(a: E::F, b: E::F) -> E::F {
    a.clone() + b.clone() - m31_const::<E>(2) * a * b
}

fn byte_expr<E: EvalAtRow>(bits: &[E::F]) -> E::F {
    debug_assert_eq!(bits.len(), 8);
    bits.iter()
        .enumerate()
        .fold(m31_const::<E>(0), |acc, (index, bit)| {
            acc + m31_const::<E>(1u32 << index) * bit.clone()
        })
}

fn mul_x_bit_expr<E: EvalAtRow>(bit_index: usize, prev: &[E::F]) -> E::F {
    let high = prev[GF_BITS - 1].clone();
    match bit_index {
        0 => high,
        1 | 2 | 7 => xor_expr::<E>(prev[bit_index - 1].clone(), high),
        _ => prev[bit_index - 1].clone(),
    }
}

fn mac_col_id(id: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mdoc/mac/{id}"),
    }
}

fn m31_const<E: EvalAtRow>(value: u32) -> E::F {
    E::F::from(M31::from_u32_unchecked(value))
}

fn bytes_to_bits(bytes: &[u8; HALF_BYTES]) -> [bool; GF_BITS] {
    let mut bits = [false; GF_BITS];
    for (byte_index, byte) in bytes.iter().enumerate() {
        for bit_index in 0..8 {
            bits[byte_index * 8 + bit_index] = ((byte >> bit_index) & 1) == 1;
        }
    }
    bits
}

fn bits_to_bytes(bits: &[bool; GF_BITS]) -> [u8; HALF_BYTES] {
    let mut bytes = [0u8; HALF_BYTES];
    for (bit_index, bit) in bits.iter().enumerate() {
        if *bit {
            bytes[bit_index / 8] |= 1 << (bit_index % 8);
        }
    }
    bytes
}

fn xor_128(left: &[u8; HALF_BYTES], right: &[u8; HALF_BYTES]) -> [u8; HALF_BYTES] {
    std::array::from_fn(|i| left[i] ^ right[i])
}

fn gf128_mul(left: &[u8; HALF_BYTES], right: &[u8; HALF_BYTES]) -> [u8; HALF_BYTES] {
    let left = bytes_to_bits(left);
    let right = bytes_to_bits(right);
    let mut coeffs = [false; 255];
    for i in 0..GF_BITS {
        for j in 0..GF_BITS {
            coeffs[i + j] ^= left[i] & right[j];
        }
    }
    for high in (GF_BITS..255).rev() {
        if coeffs[high] {
            for offset in [0usize, 1, 2, 7] {
                coeffs[high - GF_BITS + offset] ^= true;
            }
        }
    }
    let mut out = [false; GF_BITS];
    out.copy_from_slice(&coeffs[..GF_BITS]);
    bits_to_bytes(&out)
}

fn s_ladder(x: &[u8; HALF_BYTES]) -> [[bool; GF_BITS]; GF_BITS] {
    let mut out = [[false; GF_BITS]; GF_BITS];
    out[0] = bytes_to_bits(x);
    for step in 1..GF_BITS {
        let prev = out[step - 1];
        let high = prev[GF_BITS - 1];
        out[step][0] = high;
        for bit in 1..GF_BITS {
            out[step][bit] = prev[bit - 1];
        }
        out[step][1] ^= high;
        out[step][2] ^= high;
        out[step][7] ^= high;
    }
    out
}
