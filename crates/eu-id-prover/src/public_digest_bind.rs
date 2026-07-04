use air_core::relations::{DigestBytesRelation, SharedDigestRelation};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use serde::{Deserialize, Serialize};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::utils::{bit_reverse_index, coset_index_to_circle_domain_index};
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES};
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

pub(crate) struct PublicDigestBind {
    digest: [u8; 32],
    digest_handle: SharedDigestRelation,
    interaction_claim: Option<PublicDigestBindInteractionClaim>,
    component: Option<PublicDigestBindComponent>,
}

impl PublicDigestBind {
    pub(crate) fn new(digest: [u8; 32], digest_handle: SharedDigestRelation) -> Self {
        Self {
            digest,
            digest_handle,
            interaction_claim: None,
            component: None,
        }
    }

    pub(crate) fn verifier(
        digest: [u8; 32],
        digest_handle: SharedDigestRelation,
        interaction_claim: PublicDigestBindInteractionClaim,
    ) -> Self {
        Self {
            digest,
            digest_handle,
            interaction_claim: Some(interaction_claim),
            component: None,
        }
    }

    fn relation(&self) -> DigestBytesRelation {
        self.digest_handle.get()
    }

    pub(crate) fn interaction_claim(&self) -> &PublicDigestBindInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("public digest bind interaction claim is set")
    }
}

const PUBLIC_DIGEST_LOG_SIZE: u32 = LOG_N_LANES;
const PUBLIC_DIGEST_TRACE_COLS: usize = 32;
const PUBLIC_DIGEST_INTERACTION_COLS: usize = 4;

type PublicDigestColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type PublicDigestBindComponent = FrameworkComponent<PublicDigestBindEval>;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct PublicDigestBindInteractionClaim {
    pub(crate) claimed_sum: QM31,
}

#[derive(Clone)]
struct PublicDigestBindEval {
    digest: [u8; 32],
    relation: DigestBytesRelation,
}

fn public_digest_active_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: "mdoc/public_digest_bind_active".to_string(),
    }
}

fn m31_const<E: EvalAtRow>(value: u32) -> E::F {
    E::F::from(M31::from_u32_unchecked(value))
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

fn public_digest_column_eval(log_size: u32, coset_values: Vec<M31>) -> PublicDigestColumnEval {
    CircleEvaluation::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(coset_order_to_circle_domain_order(log_size, coset_values)),
    )
}

fn public_digest_active_column() -> PublicDigestColumnEval {
    let mut values = vec![M31::from_u32_unchecked(0); 1usize << PUBLIC_DIGEST_LOG_SIZE];
    values[0] = M31::from_u32_unchecked(1);
    public_digest_column_eval(PUBLIC_DIGEST_LOG_SIZE, values)
}

fn public_digest_base_trace(digest: &[u8; 32]) -> Vec<PublicDigestColumnEval> {
    (0..PUBLIC_DIGEST_TRACE_COLS)
        .map(|index| {
            let mut values = vec![M31::from_u32_unchecked(0); 1usize << PUBLIC_DIGEST_LOG_SIZE];
            values[0] = M31::from_u32_unchecked(u32::from(digest[index]));
            public_digest_column_eval(PUBLIC_DIGEST_LOG_SIZE, values)
        })
        .collect()
}

fn public_digest_interaction_trace(
    digest: &[u8; 32],
    relation: &DigestBytesRelation,
) -> (
    Vec<PublicDigestColumnEval>,
    PublicDigestBindInteractionClaim,
) {
    let base = public_digest_base_trace(digest);
    let active = public_digest_active_column();
    let n_vec_rows = 1usize << (PUBLIC_DIGEST_LOG_SIZE - LOG_N_LANES);
    let mut logup = LogupTraceGenerator::new(PUBLIC_DIGEST_LOG_SIZE);
    logup.col_from_fn(|vec_row| {
        let numerator = PackedQM31::from(active.data[vec_row]);
        let mut values = [PackedM31::broadcast(M31::from_u32_unchecked(0)); 32];
        for index in 0..32 {
            values[index] = base[index].data[vec_row];
        }
        let denominator = relation.combine(&values);
        (numerator, denominator)
    });
    debug_assert_eq!(n_vec_rows, 1);
    let (trace, claimed_sum) = logup.finalize_last();
    (trace, PublicDigestBindInteractionClaim { claimed_sum })
}

impl FrameworkEval for PublicDigestBindEval {
    fn log_size(&self) -> u32 {
        PUBLIC_DIGEST_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        PUBLIC_DIGEST_LOG_SIZE + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(public_digest_active_id());
        let one = m31_const::<E>(1);
        eval.add_constraint(active.clone() * (active.clone() - one.clone()));

        let mut values = Vec::with_capacity(32);
        for &byte in &self.digest {
            let value = eval.next_trace_mask();
            let expected = m31_const::<E>(u32::from(byte));
            eval.add_constraint(
                active.clone() * (value.clone() - expected)
                    + (one.clone() - active.clone()) * value.clone(),
            );
            values.push(value);
        }
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            E::EF::from(active),
            &values,
        ));
        eval.finalize_logup();
        eval
    }
}

impl Air for PublicDigestBind {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        for &byte in &self.digest {
            channel.mix_u64(u64::from(byte));
        }
    }

    fn draw_relations(&mut self, _channel: &mut Blake2sChannel) {}

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![PUBLIC_DIGEST_LOG_SIZE],
            trace: vec![PUBLIC_DIGEST_LOG_SIZE; PUBLIC_DIGEST_TRACE_COLS],
            interaction: vec![PUBLIC_DIGEST_LOG_SIZE; PUBLIC_DIGEST_INTERACTION_COLS],
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        vec![self.interaction_claim().claimed_sum]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        vec![public_digest_active_id()]
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.component = Some(PublicDigestBindComponent::new(
            allocator,
            PublicDigestBindEval {
                digest: self.digest,
                relation: self.relation(),
            },
            self.interaction_claim().claimed_sum,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![self
            .component
            .as_ref()
            .expect("public digest bind component is built")]
    }
}

impl AirProver for PublicDigestBind {
    fn max_log_size(&self) -> u32 {
        PUBLIC_DIGEST_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        PUBLIC_DIGEST_LOG_SIZE + 1
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        self.write_selected_preprocessed(tb, &[public_digest_active_id()]);
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc::PublicDigestBind",
            &[public_digest_active_id()],
            &[public_digest_active_column()],
        )
    }

    fn write_selected_preprocessed(
        &mut self,
        tb: &mut TreeBuilder<SimdBackend, air_core::Mc>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        if selected_ids == [public_digest_active_id()] {
            tb.extend_evals(vec![public_digest_active_column()]);
        } else {
            assert!(
                selected_ids.is_empty(),
                "unexpected public digest bind preprocessed selection"
            );
        }
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(public_digest_base_trace(&self.digest));
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let (trace, claim) = public_digest_interaction_trace(&self.digest, &self.relation());
        tb.extend_evals(trace);
        self.interaction_claim = Some(claim);
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![self
            .component
            .as_ref()
            .expect("public digest bind component is built")]
    }
}
