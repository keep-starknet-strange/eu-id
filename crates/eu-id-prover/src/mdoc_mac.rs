//! M31-side mdoc P4b Longfellow GF(2^128) MAC binding.
//!
//! The committed trace only carries one bit-serial row per MAC bit. The
//! `a_v`-dependent terms live in the post-interaction tree after the shared
//! MAC challenge is published.

use std::{cell::RefCell, rc::Rc};

use air_core::claim_mask::{
    add_claim_mask_fraction, ClaimMaskTrace, SharedClaimMaskChallenge, CLAIM_MASK_TRACE_COLUMNS,
};
use air_core::relations::{
    field_id, DigestBytesRelation, FieldBytesRelation, SharedDigestRelation, SharedFieldRelation,
};
use air_core::{fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint};
use eu_id_ec_coprocessor::mac::Gf128;
use rand::RngCore;
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

const MACS_PER_PROOF: usize = eu_id_ec_coprocessor::ecdsa::MDOC_P4B_MAC_HALF_COUNT;
const HALF_BYTES: usize = 16;
const GF_BITS: usize = 128;
const ACTIVE_ROWS: usize = MACS_PER_PROOF * GF_BITS;
// Eight bound halves occupy 1,024 active rows. Keep another 1,024 rows for
// Class-C polynomial masking of every witness column.
const CONSUMER_LOG_SIZE: u32 = 11;
const CONSUMER_ROWS: usize = 1 << CONSUMER_LOG_SIZE;
const INACTIVE_ROWS: usize = CONSUMER_ROWS - ACTIVE_ROWS;
const BINDING_LOG_SIZE: u32 = 9;
const CONSUMER_PREPROCESSED_COLS: usize = 3 + MACS_PER_PROOF + GF_BITS;
const BINDING_PREPROCESSED_COLS: usize = 6;
const CONSUMER_TRACE_COLS: usize = 1 + GF_BITS;
const POST_TRACE_COLS: usize = 2 * GF_BITS;
const BINDING_TRACE_COLS: usize = 32;
const INTERACTION_COLS_PER_FRACTION: usize = 4;
// Consumer: mac_half yield + optional committed claim-mask fraction.
const CONSUMER_INTERACTION_COLS: usize = 2 * INTERACTION_COLS_PER_FRACTION;
// Binding: issuer digest + revocation digest + 32 device-key bytes + two
// half-value sites + optional committed claim mask = 37 fractions.
const BINDING_INTERACTION_COLS: usize = 19 * INTERACTION_COLS_PER_FRACTION;
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

#[derive(Clone)]
struct MacConsumerDecoyRows {
    ap: [bool; INACTIVE_ROWS],
    s: [[bool; GF_BITS]; INACTIVE_ROWS],
    post_acc: [[bool; GF_BITS]; INACTIVE_ROWS],
}

impl MacConsumerDecoyRows {
    fn random() -> Self {
        Self {
            ap: std::array::from_fn(|_| random_bit()),
            s: std::array::from_fn(|_| random_gf_bits()),
            post_acc: std::array::from_fn(|_| random_gf_bits()),
        }
    }
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
    revocation_digest_handle: Option<SharedDigestRelation>,
    revocation_digest_relation: Option<DigestBytesRelation>,
    has_revocation: bool,
    issuer_field_handle: Option<SharedFieldRelation>,
    av: Option<[u8; HALF_BYTES]>,
    tags: Option<[[u8; HALF_BYTES]; MACS_PER_PROOF]>,
    mac_half_relation: Option<MacHalfRelation>,
    claim_mask_traces: Option<[ClaimMaskTrace; 2]>,
    claim_mask_challenge: Option<SharedClaimMaskChallenge>,
    interaction_claim: Option<MdocMacInteractionClaim>,
    consumer_decoys: Option<MacConsumerDecoyRows>,
    consumer_component: Option<ConsumerComponent>,
    binding_component: Option<BindingComponent>,
}

impl Clone for MdocMacBind {
    fn clone(&self) -> Self {
        Self {
            rows: self.rows.clone(),
            mac_state: self.mac_state.clone(),
            issuer_digest_handle: self.issuer_digest_handle.clone(),
            revocation_digest_handle: self.revocation_digest_handle.clone(),
            revocation_digest_relation: None,
            has_revocation: self.has_revocation,
            issuer_field_handle: self.issuer_field_handle.clone(),
            tags: self.tags,
            av: self.av,
            mac_half_relation: None,
            claim_mask_traces: self.claim_mask_traces.clone(),
            claim_mask_challenge: self.claim_mask_challenge.clone(),
            interaction_claim: self.interaction_claim.clone(),
            consumer_decoys: self.consumer_decoys.clone(),
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
    claim_mask_beta: Option<QM31>,
    av: [u8; HALF_BYTES],
    tags: [[u8; HALF_BYTES]; MACS_PER_PROOF],
}

#[derive(Clone)]
struct MacBindingEval {
    mac_half_relation: MacHalfRelation,
    claim_mask_beta: Option<QM31>,
    issuer_digest_relation: DigestBytesRelation,
    revocation_digest_relation: DigestBytesRelation,
    issuer_field_relation: FieldBytesRelation,
}

impl MdocMacBind {
    pub(crate) fn prover(
        mac_key_shares: &eu_id_ec_coprocessor::ecdsa::MdocP4bMacKeyShares,
        mac_values: [Gf128; MACS_PER_PROOF],
        mac_state: MdocP4bMacSharedState,
        issuer_digest_handle: SharedDigestRelation,
        revocation_digest_handle: Option<SharedDigestRelation>,
        issuer_field_handle: SharedFieldRelation,
    ) -> Self {
        let has_revocation = revocation_digest_handle.is_some();
        Self {
            rows: std::array::from_fn(|index| MacHalfWitness {
                ap: mac_key_shares.0[index],
                x: mac_values[index],
            }),
            mac_state: Some(mac_state),
            issuer_digest_handle: Some(issuer_digest_handle),
            revocation_digest_handle,
            revocation_digest_relation: None,
            has_revocation,
            issuer_field_handle: Some(issuer_field_handle),
            av: None,
            tags: None,
            mac_half_relation: None,
            claim_mask_traces: None,
            claim_mask_challenge: None,
            interaction_claim: None,
            consumer_decoys: None,
            consumer_component: None,
            binding_component: None,
        }
    }

    pub(crate) fn verifier(
        mac_state: MdocP4bMacSharedState,
        issuer_digest_handle: SharedDigestRelation,
        revocation_digest_handle: Option<SharedDigestRelation>,
        issuer_field_handle: SharedFieldRelation,
        interaction_claim: MdocMacInteractionClaim,
    ) -> Self {
        let has_revocation = revocation_digest_handle.is_some();
        Self {
            rows: std::array::from_fn(|_| MacHalfWitness {
                ap: [0; HALF_BYTES],
                x: [0; HALF_BYTES],
            }),
            mac_state: Some(mac_state),
            issuer_digest_handle: Some(issuer_digest_handle),
            revocation_digest_handle,
            revocation_digest_relation: None,
            has_revocation,
            issuer_field_handle: Some(issuer_field_handle),
            av: None,
            tags: None,
            mac_half_relation: None,
            claim_mask_traces: None,
            claim_mask_challenge: None,
            interaction_claim: Some(interaction_claim),
            consumer_decoys: None,
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

    fn revocation_digest_relation(&self) -> DigestBytesRelation {
        self.revocation_digest_relation
            .as_ref()
            .expect("revocation digest relation drawn before use")
            .clone()
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

    pub(crate) fn ordered_claim_mask_log_sizes(&self) -> Vec<u32> {
        vec![CONSUMER_LOG_SIZE, BINDING_LOG_SIZE]
    }

    pub(crate) fn with_claim_masks(
        mut self,
        traces: Vec<ClaimMaskTrace>,
        challenge: SharedClaimMaskChallenge,
    ) -> Result<Self, String> {
        let traces: [ClaimMaskTrace; 2] = traces.try_into().map_err(|traces: Vec<_>| {
            format!("mdoc MAC needs 2 claim masks, got {}", traces.len())
        })?;
        for (index, (trace, expected)) in traces
            .iter()
            .zip([CONSUMER_LOG_SIZE, BINDING_LOG_SIZE])
            .enumerate()
        {
            if trace.log_size() != expected {
                return Err(format!(
                    "mdoc MAC claim mask {index} has log size {}, expected {expected}",
                    trace.log_size()
                ));
            }
        }
        self.claim_mask_traces = Some(traces);
        self.claim_mask_challenge = Some(challenge);
        Ok(self)
    }

    pub(crate) fn with_claim_masks_verifier(mut self, challenge: SharedClaimMaskChallenge) -> Self {
        self.claim_mask_challenge = Some(challenge);
        self
    }

    fn claim_mask_beta(&self) -> Option<QM31> {
        self.claim_mask_challenge
            .as_ref()
            .map(|shared| shared.require().expect("claim-mask anchor drawn first"))
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
        channel.mix_u64(0x4d44_4f43_4d41_4304);
        channel.mix_u64(MACS_PER_PROOF as u64);
        channel.mix_u64(GF_BITS as u64);
        channel.mix_u64(ACTIVE_ROWS as u64);
        channel.mix_u64(POST_TRACE_COLS as u64);
        channel.mix_u64(u64::from(self.has_revocation));
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.mac_half_relation = Some(MacHalfRelation::draw(channel));
        self.revocation_digest_relation = Some(
            self.revocation_digest_handle
                .as_ref()
                .map(SharedDigestRelation::get)
                .unwrap_or_else(|| DigestBytesRelation::draw(channel)),
        );
    }

    fn layout(&self) -> air_core::TreeLayout {
        let mask_enabled = self.claim_mask_challenge.is_some();
        let mut trace =
            std::iter::repeat_n(CONSUMER_LOG_SIZE, CONSUMER_TRACE_COLS).collect::<Vec<_>>();
        if mask_enabled {
            trace.extend(std::iter::repeat_n(
                CONSUMER_LOG_SIZE,
                CLAIM_MASK_TRACE_COLUMNS,
            ));
        }
        trace.extend(std::iter::repeat_n(BINDING_LOG_SIZE, BINDING_TRACE_COLS));
        if mask_enabled {
            trace.extend(std::iter::repeat_n(
                BINDING_LOG_SIZE,
                CLAIM_MASK_TRACE_COLUMNS,
            ));
        }
        air_core::TreeLayout {
            preprocessed: std::iter::repeat_n(CONSUMER_LOG_SIZE, CONSUMER_PREPROCESSED_COLS)
                .chain(std::iter::repeat_n(
                    BINDING_LOG_SIZE,
                    BINDING_PREPROCESSED_COLS,
                ))
                .collect(),
            trace,
            interaction: std::iter::repeat_n(
                CONSUMER_LOG_SIZE,
                if mask_enabled {
                    CONSUMER_INTERACTION_COLS
                } else {
                    INTERACTION_COLS_PER_FRACTION
                },
            )
            .chain(std::iter::repeat_n(
                BINDING_LOG_SIZE,
                if mask_enabled {
                    BINDING_INTERACTION_COLS
                } else {
                    18 * INTERACTION_COLS_PER_FRACTION
                },
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
        ids.push(mac_col_id("binding/issuer_digest_active"));
        ids.push(mac_col_id("binding/revocation_digest_active"));
        ids.push(mac_col_id("binding/field_active"));
        ids.push(mac_col_id("binding/field_id"));
        ids.push(mac_col_id("binding/slot"));
        ids
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<MacColumnEval>, stwo::core::verifier::VerificationError> {
        Ok(preprocessed_trace(self.has_revocation))
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let av = self.av.unwrap_or([0; HALF_BYTES]);
        let tags = self.tags.unwrap_or([[0; HALF_BYTES]; MACS_PER_PROOF]);
        self.consumer_component = Some(ConsumerComponent::new(
            allocator,
            MacConsumerEval {
                mac_half_relation: self.mac_half_relation().clone(),
                claim_mask_beta: self.claim_mask_beta(),
                av,
                tags,
            },
            self.interaction_claim().consumer,
        ));
        self.binding_component = Some(BindingComponent::new(
            allocator,
            MacBindingEval {
                mac_half_relation: self.mac_half_relation().clone(),
                claim_mask_beta: self.claim_mask_beta(),
                issuer_digest_relation: self.issuer_digest_relation(),
                revocation_digest_relation: self.revocation_digest_relation(),
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
        tb.extend_evals(preprocessed_trace(self.has_revocation));
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc_mac",
            &self.preprocessed_column_ids(),
            &preprocessed_trace(self.has_revocation),
        )
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let decoys = MacConsumerDecoyRows::random();
        tb.extend_evals(consumer_trace(&self.rows, &decoys));
        if let Some(masks) = &self.claim_mask_traces {
            tb.extend_evals(masks[0].columns().to_vec());
        }
        self.consumer_decoys = Some(decoys);
        tb.extend_evals(binding_trace(&self.rows));
        if let Some(masks) = &self.claim_mask_traces {
            tb.extend_evals(masks[1].columns().to_vec());
        }
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let claim_mask_beta = self.claim_mask_beta();
        let consumer_mask = self.claim_mask_traces.as_ref().map(|masks| &masks[0]);
        let binding_mask = self.claim_mask_traces.as_ref().map(|masks| &masks[1]);
        let (consumer_trace, consumer_claim) = consumer_interaction_trace(
            &self.rows,
            self.mac_half_relation(),
            consumer_mask,
            claim_mask_beta,
        );
        let (binding_trace, binding_claim) = binding_interaction_trace(
            &self.rows,
            self.mac_half_relation(),
            &self.issuer_digest_relation(),
            &self.revocation_digest_relation(),
            &self.issuer_field_relation(),
            self.has_revocation,
            binding_mask,
            claim_mask_beta,
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
        let decoys = self
            .consumer_decoys
            .as_ref()
            .expect("MAC consumer decoys generated before post-interaction trace");
        tb.extend_evals(post_interaction_trace(&self.rows, &av, decoys));
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
        for bit in &s_bits {
            eval.add_constraint(bit.clone() * (bit.clone() - one.clone()));
        }
        for bit in &post_acc_bits {
            if CHECK_POST_COLUMN_CONSTRAINTS {
                eval.add_constraint(bit.clone() * (bit.clone() - one.clone()));
            }
        }
        for bit in &term_bits {
            if CHECK_POST_COLUMN_CONSTRAINTS {
                eval.add_constraint(bit.clone() * (bit.clone() - one.clone()));
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
                eval.add_constraint(
                    first.clone() * (post_acc_bits[bit_index].clone() - term.clone())
                        + (active.clone() - first.clone())
                            * (post_acc_bits[bit_index].clone()
                                - xor_expr::<E>(post_acc_prev_bits[bit_index].clone(), term)),
                );
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

        if let Some(beta) = self.claim_mask_beta {
            add_claim_mask_fraction(&mut eval, beta);
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
        let issuer_digest_active =
            eval.get_preprocessed_column(mac_col_id("binding/issuer_digest_active"));
        let revocation_digest_active =
            eval.get_preprocessed_column(mac_col_id("binding/revocation_digest_active"));
        let field_active = eval.get_preprocessed_column(mac_col_id("binding/field_active"));
        let field_id_col = eval.get_preprocessed_column(mac_col_id("binding/field_id"));
        let slot = eval.get_preprocessed_column(mac_col_id("binding/slot"));
        let one = m31_const::<E>(1);

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint(
            issuer_digest_active.clone() * (issuer_digest_active.clone() - one.clone()),
        );
        eval.add_constraint(
            revocation_digest_active.clone() * (revocation_digest_active.clone() - one.clone()),
        );
        eval.add_constraint(field_active.clone() * (field_active.clone() - one.clone()));
        eval.add_constraint(issuer_digest_active.clone() * (one.clone() - active.clone()));
        eval.add_constraint(revocation_digest_active.clone() * (one.clone() - active.clone()));
        eval.add_constraint(field_active.clone() * (one.clone() - active.clone()));

        let bytes = (0..32).map(|_| eval.next_trace_mask()).collect::<Vec<_>>();

        eval.add_to_relation(RelationEntry::new(
            &self.issuer_digest_relation,
            E::EF::from(issuer_digest_active.clone()),
            &bytes,
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.revocation_digest_relation,
            E::EF::from(revocation_digest_active.clone()),
            &bytes,
        ));

        // A slot with no live binding (the revocation slot when the statement
        // carries no revocation leg) is pinned to the public nonzero
        // placeholder; pinning it to zero would zero its MAC tags and publish
        // a constant revocation-off marker in every proof.
        let placeholder_bytes = absent_revocation_slot_bytes();
        let zero_active =
            active.clone() - issuer_digest_active - revocation_digest_active - field_active.clone();
        for (byte_idx, byte) in bytes.iter().enumerate() {
            eval.add_constraint(
                zero_active.clone()
                    * (byte.clone() - m31_const::<E>(u32::from(placeholder_bytes[byte_idx]))),
            );
        }

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

        if let Some(beta) = self.claim_mask_beta {
            add_claim_mask_fraction(&mut eval, beta);
        }

        eval.finalize_logup_in_pairs();
        eval
    }
}

fn preprocessed_trace(has_revocation: bool) -> Vec<MacColumnEval> {
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
    out.extend(binding_preprocessed_trace(has_revocation));
    out
}

fn binding_preprocessed_trace(has_revocation: bool) -> Vec<MacColumnEval> {
    let mut columns =
        vec![vec![M31::from_u32_unchecked(0); 1 << BINDING_LOG_SIZE]; BINDING_PREPROCESSED_COLS];
    for slot in 0..(MACS_PER_PROOF / 2) {
        columns[0][slot] = M31::from_u32_unchecked(1);
        columns[1][slot] = M31::from_u32_unchecked(u32::from(slot == 0));
        columns[2][slot] = M31::from_u32_unchecked(u32::from(has_revocation && slot == 3));
        columns[3][slot] = M31::from_u32_unchecked(u32::from(matches!(slot, 1 | 2)));
        columns[4][slot] = M31::from_u32_unchecked(match slot {
            1 => field_id::MDOC_DEVICE_KEY_X,
            2 => field_id::MDOC_DEVICE_KEY_Y,
            _ => 0,
        });
        columns[5][slot] = M31::from_u32_unchecked(slot as u32);
    }
    columns
        .into_iter()
        .map(|values| column_eval(BINDING_LOG_SIZE, values))
        .collect()
}

/// The 32 binding-slot bytes an absent revocation slot must carry: the
/// `MDOC_P4B_ABSENT_REVOCATION_MAC_VALUE` placeholder in both halves, laid out
/// exactly as `binding_value_rows` lays out live values.
fn absent_revocation_slot_bytes() -> [u8; 32] {
    let placeholder = eu_id_ec_coprocessor::ecdsa::MDOC_P4B_ABSENT_REVOCATION_MAC_VALUE;
    let mut bytes = [0u8; 32];
    for i in 0..HALF_BYTES {
        bytes[i] = placeholder[HALF_BYTES - 1 - i];
        bytes[HALF_BYTES + i] = placeholder[HALF_BYTES - 1 - i];
    }
    bytes
}

fn binding_value_rows(rows: &[MacHalfWitness; MACS_PER_PROOF]) -> [[u8; 32]; MACS_PER_PROOF / 2] {
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
    for column in &mut columns {
        for value in column.iter_mut().skip(3) {
            *value = random_m31_cell();
        }
    }
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
    revocation_digest_relation: &DigestBytesRelation,
    issuer_field_relation: &FieldBytesRelation,
    has_revocation: bool,
    claim_mask_trace: Option<&ClaimMaskTrace>,
    claim_mask_beta: Option<QM31>,
) -> (Vec<MacColumnEval>, QM31) {
    let preprocessed = binding_preprocessed_trace(has_revocation);
    let active = &preprocessed[0];
    let issuer_digest_active = &preprocessed[1];
    let revocation_digest_active = &preprocessed[2];
    let field_active = &preprocessed[3];
    let field_ids = &preprocessed[4];
    let slots = &preprocessed[5];
    let bytes = binding_trace(rows);
    let n_vec_rows = bytes[0].data.len();
    let mut sites: Vec<Vec<(PackedQM31, PackedQM31)>> =
        Vec::with_capacity(36 + usize::from(claim_mask_trace.is_some()));
    sites.push(
        (0..n_vec_rows)
            .map(|vec_row| {
                let values = (0..32)
                    .map(|byte_idx| bytes[byte_idx].data[vec_row])
                    .collect::<Vec<_>>();
                (
                    PackedQM31::from(issuer_digest_active.data[vec_row]),
                    issuer_digest_relation.combine(&values),
                )
            })
            .collect(),
    );
    sites.push(
        (0..n_vec_rows)
            .map(|vec_row| {
                let values = (0..32)
                    .map(|byte_idx| bytes[byte_idx].data[vec_row])
                    .collect::<Vec<_>>();
                (
                    PackedQM31::from(revocation_digest_active.data[vec_row]),
                    revocation_digest_relation.combine(&values),
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
    match (claim_mask_trace, claim_mask_beta) {
        (Some(mask), Some(beta)) => {
            assert_eq!(mask.log_size(), BINDING_LOG_SIZE);
            sites.push(
                (0..n_vec_rows)
                    .map(|vec_row| mask.packed_fraction_at(vec_row, beta))
                    .collect(),
            );
        }
        (None, None) => {}
        _ => panic!("mdoc MAC binding mask and challenge must be configured together"),
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

fn consumer_trace(
    rows: &[MacHalfWitness; MACS_PER_PROOF],
    decoys: &MacConsumerDecoyRows,
) -> Vec<MacColumnEval> {
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
    for row in ACTIVE_ROWS..CONSUMER_ROWS {
        let decoy = row - ACTIVE_ROWS;
        columns[0][row] = M31::from_u32_unchecked(u32::from(decoys.ap[decoy]));
        for bit_index in 0..GF_BITS {
            columns[1 + bit_index][row] =
                M31::from_u32_unchecked(u32::from(decoys.s[decoy][bit_index]));
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
    claim_mask_trace: Option<&ClaimMaskTrace>,
    claim_mask_beta: Option<QM31>,
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
    match (claim_mask_trace, claim_mask_beta) {
        (Some(mask), Some(beta)) => {
            assert_eq!(mask.log_size(), CONSUMER_LOG_SIZE);
            logup.col_from_iter(
                (0..mask.packed_rows()).map(|vec_row| mask.packed_fraction_at(vec_row, beta)),
            );
        }
        (None, None) => {}
        _ => panic!("mdoc MAC consumer mask and challenge must be configured together"),
    }
    logup.finalize_last()
}

fn post_interaction_trace(
    rows: &[MacHalfWitness; MACS_PER_PROOF],
    av: &[u8; HALF_BYTES],
    decoys: &MacConsumerDecoyRows,
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
    for row in ACTIVE_ROWS..CONSUMER_ROWS {
        let decoy = row - ACTIVE_ROWS;
        for bit in 0..GF_BITS {
            let term = decoys.ap[decoy] && decoys.s[decoy][bit];
            columns[bit][row] = M31::from_u32_unchecked(u32::from(term));
            columns[GF_BITS + bit][row] =
                M31::from_u32_unchecked(u32::from(decoys.post_acc[decoy][bit]));
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

fn random_bit() -> bool {
    let mut byte = [0u8; 1];
    rand::thread_rng().fill_bytes(&mut byte);
    byte[0] & 1 == 1
}

fn random_m31_cell() -> M31 {
    let mut rng = rand::thread_rng();
    loop {
        let value = rng.next_u32() & 0x7fff_ffff;
        if value < 2_147_483_647 {
            return M31::from_u32_unchecked(value);
        }
    }
}

fn random_gf_bits() -> [bool; GF_BITS] {
    let mut bytes = [0u8; HALF_BYTES];
    rand::thread_rng().fill_bytes(&mut bytes);
    bytes_to_bits(&bytes)
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::VecDeque;

    use air_core::claim_mask::{ClaimMaskChallengeModule, ClaimMaskRing};
    use stwo::core::fields::qm31::SECURE_EXTENSION_DEGREE;
    use stwo::prover::backend::simd::m31::N_LANES;
    use stwo_constraint_framework::{Multiplicity, PREPROCESSED_TRACE_IDX};

    #[derive(Default)]
    struct RowEval {
        preprocessed: VecDeque<Vec<M31>>,
        original: VecDeque<Vec<M31>>,
        post: VecDeque<Vec<M31>>,
        constraints: Vec<QM31>,
    }

    impl RowEval {
        fn inactive_decoy_slack_row() -> Self {
            let bit = M31::from_u32_unchecked(1);
            let zero = M31::from_u32_unchecked(0);
            let mut row = Self::default();

            row.preprocessed.push_back(vec![zero]); // active
            row.preprocessed.push_back(vec![zero]); // first
            row.preprocessed.push_back(vec![zero]); // last
            for _ in 0..MACS_PER_PROOF {
                row.preprocessed.push_back(vec![zero]);
            }
            for _ in 0..GF_BITS {
                row.preprocessed.push_back(vec![zero]);
            }

            row.original.push_back(vec![bit]); // ap
            for _ in 0..GF_BITS {
                row.original.push_back(vec![bit, zero]); // s, previous s
            }
            for _ in 0..GF_BITS {
                row.post.push_back(vec![bit]); // term
            }
            for _ in 0..GF_BITS {
                row.post.push_back(vec![bit, zero]); // post accumulator, previous accumulator
            }

            row
        }

        fn inactive_binding_row() -> Self {
            let bit = M31::from_u32_unchecked(1);
            let zero = M31::from_u32_unchecked(0);
            let mut row = Self::default();

            row.preprocessed.push_back(vec![zero]); // active
            row.preprocessed.push_back(vec![zero]); // issuer digest active
            row.preprocessed.push_back(vec![zero]); // revocation digest active
            row.preprocessed.push_back(vec![zero]); // field active
            row.preprocessed.push_back(vec![zero]); // field id
            row.preprocessed.push_back(vec![zero]); // slot
            for _ in 0..32 {
                row.original.push_back(vec![bit]); // inactive byte cell
            }

            row
        }

        fn nonzero_constraints(&self) -> Vec<(usize, QM31)> {
            self.constraints
                .iter()
                .copied()
                .enumerate()
                .filter(|(_, value)| *value != QM31::from_u32_unchecked(0, 0, 0, 0))
                .collect()
        }
    }

    impl EvalAtRow for RowEval {
        type F = M31;
        type EF = QM31;

        fn next_interaction_mask<const N: usize>(
            &mut self,
            interaction: usize,
            _offsets: [isize; N],
        ) -> [Self::F; N] {
            let queue = match interaction {
                PREPROCESSED_TRACE_IDX => &mut self.preprocessed,
                stwo_constraint_framework::ORIGINAL_TRACE_IDX => &mut self.original,
                3 => &mut self.post,
                _ => panic!("unexpected interaction index {interaction}"),
            };
            let values = queue
                .pop_front()
                .unwrap_or_else(|| panic!("missing mask for interaction {interaction}"));
            assert_eq!(values.len(), N, "mask arity mismatch");
            std::array::from_fn(|index| values[index])
        }

        fn add_constraint<G>(&mut self, constraint: G)
        where
            Self::EF: std::ops::Mul<G, Output = Self::EF> + From<G>,
        {
            self.constraints.push(QM31::from(constraint));
        }

        fn combine_ef(values: [Self::F; SECURE_EXTENSION_DEGREE]) -> Self::EF {
            QM31::from_m31_array(values)
        }

        fn add_to_relation<R: Relation<Self::F, Self::EF>>(
            &mut self,
            _entry: RelationEntry<'_, Self::F, Self::EF, R>,
        ) {
        }

        fn write_logup_frac_typed(
            &mut self,
            _numerator: Multiplicity<Self::F, Self::EF>,
            _denominator: Self::EF,
        ) {
        }

        fn finalize_logup(&mut self) {}

        fn finalize_logup_in_pairs(&mut self) {}
    }

    #[test]
    fn mdoc_mac_consumer_decoy_slack_rows_are_not_zero_pinned() {
        let eval = MacConsumerEval {
            mac_half_relation: MacHalfRelation::dummy(),
            claim_mask_beta: None,
            av: [0; HALF_BYTES],
            tags: [[0; HALF_BYTES]; MACS_PER_PROOF],
        };
        let row = eval.evaluate(RowEval::inactive_decoy_slack_row());

        let nonzero = row.nonzero_constraints();
        assert!(
            nonzero.is_empty(),
            "inactive MAC consumer decoy row still hits constraints: {nonzero:?}"
        );
    }

    fn test_rows() -> [MacHalfWitness; MACS_PER_PROOF] {
        std::array::from_fn(|_| MacHalfWitness {
            ap: [0; HALF_BYTES],
            x: [0; HALF_BYTES],
        })
    }

    fn test_claim_masks() -> (ClaimMaskTrace, ClaimMaskTrace, QM31) {
        let log_sizes = [CONSUMER_LOG_SIZE, BINDING_LOG_SIZE];
        let mut ring = ClaimMaskRing::new(&log_sizes).unwrap();
        let consumer = ring.take(CONSUMER_LOG_SIZE).unwrap();
        let binding = ring.take(BINDING_LOG_SIZE).unwrap();
        ring.finish().unwrap();

        let shared = SharedClaimMaskChallenge::new();
        let mut anchor = ClaimMaskChallengeModule::new(shared.clone(), log_sizes).unwrap();
        anchor.draw_relations(&mut Blake2sChannel::default());
        let beta = shared.require().unwrap();
        (consumer, binding, beta)
    }

    #[test]
    fn mdoc_mac_consumer_mask_delta_matches_private_target() {
        let rows = test_rows();
        let mut channel = Blake2sChannel::default();
        let relation = MacHalfRelation::draw(&mut channel);
        let (mask, _, beta) = test_claim_masks();

        let (_, unmasked) = consumer_interaction_trace(&rows, &relation, None, None);
        let (_, masked) = consumer_interaction_trace(&rows, &relation, Some(&mask), Some(beta));

        assert_eq!(masked - unmasked, beta * mask.target_sum());
    }

    #[test]
    fn mdoc_mac_binding_mask_delta_matches_private_target() {
        let rows = test_rows();
        let mut channel = Blake2sChannel::default();
        let mac_half_relation = MacHalfRelation::draw(&mut channel);
        let issuer_digest_relation = DigestBytesRelation::draw(&mut channel);
        let revocation_digest_relation = DigestBytesRelation::draw(&mut channel);
        let issuer_field_relation = FieldBytesRelation::draw(&mut channel);
        let (_, mask, beta) = test_claim_masks();

        let (_, unmasked) = binding_interaction_trace(
            &rows,
            &mac_half_relation,
            &issuer_digest_relation,
            &revocation_digest_relation,
            &issuer_field_relation,
            true,
            None,
            None,
        );
        let (_, masked) = binding_interaction_trace(
            &rows,
            &mac_half_relation,
            &issuer_digest_relation,
            &revocation_digest_relation,
            &issuer_field_relation,
            true,
            Some(&mask),
            Some(beta),
        );

        assert_eq!(masked - unmasked, beta * mask.target_sum());
    }

    fn trace_fingerprint(trace: &[MacColumnEval]) -> Vec<[M31; N_LANES]> {
        trace
            .iter()
            .flat_map(|column| column.data.iter().map(|packed| packed.to_array()))
            .collect()
    }

    #[test]
    fn mdoc_mac_consumer_trace_fills_inactive_rows_with_fresh_decoys() {
        let rows = test_rows();
        let first_decoys = MacConsumerDecoyRows::random();
        let second_decoys = MacConsumerDecoyRows::random();
        let first_consumer = consumer_trace(&rows, &first_decoys);
        let second_consumer = consumer_trace(&rows, &second_decoys);
        let first_post = post_interaction_trace(&rows, &[0x5a; HALF_BYTES], &first_decoys);
        let second_post = post_interaction_trace(&rows, &[0x5a; HALF_BYTES], &second_decoys);

        let first_consumer_inactive = trace_fingerprint(&first_consumer);
        let second_consumer_inactive = trace_fingerprint(&second_consumer);
        let first_post_inactive = trace_fingerprint(&first_post);
        let second_post_inactive = trace_fingerprint(&second_post);

        let zero = [M31::from_u32_unchecked(0); N_LANES];
        assert!(
            first_consumer_inactive.iter().any(|value| *value != zero),
            "consumer inactive rows are still all zero"
        );
        assert!(
            first_post_inactive.iter().any(|value| *value != zero),
            "post-interaction inactive rows are still all zero"
        );
        assert_ne!(
            first_consumer_inactive, second_consumer_inactive,
            "consumer inactive decoys must be fresh per trace"
        );
        assert_ne!(
            first_post_inactive, second_post_inactive,
            "post-interaction inactive decoys must be fresh per trace"
        );
    }

    #[test]
    fn mdoc_mac_binding_inactive_rows_are_not_zero_pinned() {
        let eval = MacBindingEval {
            mac_half_relation: MacHalfRelation::dummy(),
            claim_mask_beta: None,
            issuer_digest_relation: DigestBytesRelation::dummy(),
            revocation_digest_relation: DigestBytesRelation::dummy(),
            issuer_field_relation: FieldBytesRelation::dummy(),
        };
        let row = eval.evaluate(RowEval::inactive_binding_row());

        let nonzero = row.nonzero_constraints();
        assert!(
            nonzero.is_empty(),
            "inactive MAC binding row still hits constraints: {nonzero:?}"
        );
    }

    #[test]
    #[allow(clippy::assertions_on_constants)]
    fn mdoc_mac_binding_class_a_has_256_blind_rows_and_fresh_inactive_cells() {
        assert!(
            (1usize << BINDING_LOG_SIZE) - (MACS_PER_PROOF / 2) >= 256,
            "MAC binding Class A needs at least 256 blind rows"
        );

        let rows = test_rows();
        let first = trace_fingerprint(&binding_trace(&rows));
        let second = trace_fingerprint(&binding_trace(&rows));
        let zero = [M31::from_u32_unchecked(0); N_LANES];

        assert!(
            first.iter().any(|value| *value != zero),
            "MAC binding inactive rows are still all zero"
        );
        assert_ne!(
            first, second,
            "MAC binding inactive cells must be fresh per trace"
        );
    }
}
