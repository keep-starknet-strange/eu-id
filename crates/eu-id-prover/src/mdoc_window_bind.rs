//! In-circuit binding of MSO / item preimage byte windows (Phase D).
//!
//! A single multi-window LogUp component that consumes byte windows exposed by
//! the SHA modules (via [`air_core::relations::SharedFieldRelation`]) and binds
//! each to one of three targets:
//!
//! - **Constant** — the window bytes must equal a public constant (D1 element
//!   identifier pins, D3 device-key coordinates equal to the coprocessor's
//!   proven device public key bytes).
//! - **BirthDigest / NationalityDigest** — the 32-byte `valueDigests` window in
//!   the issuer MSO preimage must byte-equal the item SHA module's digest, via a
//!   shared [`air_core::relations::SharedDigestRelation`] (D2 digest membership).
//!
//! Implementing all five bind surfaces as one sized-once component (rather than
//! five log-4 dust components) follows the Phase D perf rule.

use air_core::relations::{
    field_id, DigestBytesRelation, FieldBytesRelation, SharedDigestRelation, SharedFieldRelation,
};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use serde::{Deserialize, Serialize};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{QM31, SECURE_EXTENSION_DEGREE};
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

/// One log-lanes-tall bind surface; each window is one row.
const MDOC_WINDOW_BIND_LOG_SIZE: u32 = LOG_N_LANES;
/// Byte-value witness columns (max window length is a 32-byte digest / coord).
const MDOC_WINDOW_BIND_TRACE_COLS: usize = 32;
/// `active`, `field_id`, `constant_active`, `birth_digest_active`,
/// `nat_digest_active`, three source selectors, 32 `byte_active`, 32 `expected`.
const MDOC_WINDOW_BIND_PREPROCESSED_COLS: usize = 72;
/// 32 bytes × 3 field sources + 2 digest yields.
const MDOC_WINDOW_BIND_LOOKUPS: usize = 32 * 3 + 2;
const MDOC_WINDOW_BIND_INTERACTION_COLS: usize =
    MDOC_WINDOW_BIND_LOOKUPS.div_ceil(2) * SECURE_EXTENSION_DEGREE;

type MdocWindowColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type MdocWindowBindComponent = FrameworkComponent<MdocWindowBindEval>;

/// Which SHA field provider a window's bytes are drawn from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MdocFieldSource {
    IssuerMso,
    BirthItem,
    NationalityItem,
}

/// The binding target for a row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MdocWindowTarget {
    Constant,
    BirthDigest,
    NationalityDigest,
}

/// A single window-bind row: `len` window bytes read from `source` (indexed by
/// `field_id`), bound to `target`. For `Constant` targets the bytes must equal
/// `expected`; for digest targets the 32-byte `witness` must equal the item SHA
/// digest carried by the shared digest relation.
#[derive(Clone, Debug)]
pub(crate) struct MdocWindowBindRow {
    field_id: u32,
    source: MdocFieldSource,
    len: usize,
    target: MdocWindowTarget,
    expected: [u8; 32],
    witness: [u8; 32],
}

impl MdocWindowBindRow {
    pub(crate) fn constant(field_id: u32, source: MdocFieldSource, bytes: &[u8]) -> Self {
        let mut expected = [0u8; 32];
        expected[..bytes.len()].copy_from_slice(bytes);
        Self {
            field_id,
            source,
            len: bytes.len(),
            target: MdocWindowTarget::Constant,
            expected,
            witness: expected,
        }
    }

    fn birth_digest(bytes: [u8; 32]) -> Self {
        Self {
            field_id: field_id::MDOC_BIRTH_DATE_DIGEST,
            source: MdocFieldSource::IssuerMso,
            len: 32,
            target: MdocWindowTarget::BirthDigest,
            expected: [0u8; 32],
            witness: bytes,
        }
    }

    fn nat_digest(bytes: [u8; 32]) -> Self {
        Self {
            field_id: field_id::MDOC_NATIONALITY_DIGEST,
            source: MdocFieldSource::IssuerMso,
            len: 32,
            target: MdocWindowTarget::NationalityDigest,
            expected: [0u8; 32],
            witness: bytes,
        }
    }
}

/// Build the six bind rows for the prover: the `digest` argument supplies the
/// witness digest bytes read from the issuer preimage windows; the verifier
/// passes `None` (zeros — the digest bytes are reconstructed by the LogUp
/// relation, not asserted host-side).
pub(crate) fn mdoc_window_bind_rows(
    birth_date_element: &[u8],
    nationality_element: &[u8],
    device_key_x: &[u8; 32],
    device_key_y: &[u8; 32],
    digest_witnesses: Option<([u8; 32], [u8; 32])>,
) -> Vec<MdocWindowBindRow> {
    let (birth_digest, nat_digest) = digest_witnesses.unwrap_or(([0u8; 32], [0u8; 32]));
    vec![
        MdocWindowBindRow::constant(
            field_id::MDOC_BIRTH_DATE_ELEMENT_ID,
            MdocFieldSource::BirthItem,
            birth_date_element,
        ),
        MdocWindowBindRow::constant(
            field_id::MDOC_NATIONALITY_ELEMENT_ID,
            MdocFieldSource::NationalityItem,
            nationality_element,
        ),
        MdocWindowBindRow::birth_digest(birth_digest),
        MdocWindowBindRow::nat_digest(nat_digest),
        MdocWindowBindRow::constant(
            field_id::MDOC_DEVICE_KEY_X,
            MdocFieldSource::IssuerMso,
            device_key_x,
        ),
        MdocWindowBindRow::constant(
            field_id::MDOC_DEVICE_KEY_Y,
            MdocFieldSource::IssuerMso,
            device_key_y,
        ),
    ]
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct MdocWindowBindInteractionClaim {
    pub(crate) claimed_sum: QM31,
}

pub(crate) struct MdocWindowBind {
    rows: Vec<MdocWindowBindRow>,
    issuer_field_handle: SharedFieldRelation,
    birth_field_handle: SharedFieldRelation,
    nat_field_handle: SharedFieldRelation,
    birth_digest_handle: SharedDigestRelation,
    nat_digest_handle: SharedDigestRelation,
    interaction_claim: Option<MdocWindowBindInteractionClaim>,
    component: Option<MdocWindowBindComponent>,
}

impl MdocWindowBind {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        rows: Vec<MdocWindowBindRow>,
        issuer_field_handle: SharedFieldRelation,
        birth_field_handle: SharedFieldRelation,
        nat_field_handle: SharedFieldRelation,
        birth_digest_handle: SharedDigestRelation,
        nat_digest_handle: SharedDigestRelation,
    ) -> Self {
        Self {
            rows,
            issuer_field_handle,
            birth_field_handle,
            nat_field_handle,
            birth_digest_handle,
            nat_digest_handle,
            interaction_claim: None,
            component: None,
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn verifier(
        rows: Vec<MdocWindowBindRow>,
        issuer_field_handle: SharedFieldRelation,
        birth_field_handle: SharedFieldRelation,
        nat_field_handle: SharedFieldRelation,
        birth_digest_handle: SharedDigestRelation,
        nat_digest_handle: SharedDigestRelation,
        interaction_claim: MdocWindowBindInteractionClaim,
    ) -> Self {
        Self {
            rows,
            issuer_field_handle,
            birth_field_handle,
            nat_field_handle,
            birth_digest_handle,
            nat_digest_handle,
            interaction_claim: Some(interaction_claim),
            component: None,
        }
    }

    pub(crate) fn interaction_claim(&self) -> &MdocWindowBindInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("mdoc window bind interaction claim is set")
    }

    fn issuer_field_relation(&self) -> FieldBytesRelation {
        self.issuer_field_handle.get()
    }

    fn birth_field_relation(&self) -> FieldBytesRelation {
        self.birth_field_handle.get()
    }

    fn nat_field_relation(&self) -> FieldBytesRelation {
        self.nat_field_handle.get()
    }

    fn birth_digest_relation(&self) -> DigestBytesRelation {
        self.birth_digest_handle.get()
    }

    fn nat_digest_relation(&self) -> DigestBytesRelation {
        self.nat_digest_handle.get()
    }
}

#[derive(Clone)]
struct MdocWindowBindEval {
    issuer_field_relation: FieldBytesRelation,
    birth_field_relation: FieldBytesRelation,
    nat_field_relation: FieldBytesRelation,
    birth_digest_relation: DigestBytesRelation,
    nat_digest_relation: DigestBytesRelation,
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

fn mdoc_window_column_eval(log_size: u32, coset_values: Vec<M31>) -> MdocWindowColumnEval {
    CircleEvaluation::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(coset_order_to_circle_domain_order(log_size, coset_values)),
    )
}

fn mdoc_window_bind_col_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mdoc/window_bind/{name}"),
    }
}

fn mdoc_window_bind_preprocessed_column_ids() -> Vec<PreProcessedColumnId> {
    let mut ids = vec![
        mdoc_window_bind_col_id("active"),
        mdoc_window_bind_col_id("field_id"),
        mdoc_window_bind_col_id("constant_active"),
        mdoc_window_bind_col_id("birth_digest_active"),
        mdoc_window_bind_col_id("nat_digest_active"),
        mdoc_window_bind_col_id("issuer_field_active"),
        mdoc_window_bind_col_id("birth_field_active"),
        mdoc_window_bind_col_id("nat_field_active"),
    ];
    ids.extend((0..32).map(|i| mdoc_window_bind_col_id(&format!("byte_active_{i}"))));
    ids.extend((0..32).map(|i| mdoc_window_bind_col_id(&format!("expected_{i}"))));
    ids
}

fn mdoc_window_bind_preprocessed_columns(rows: &[MdocWindowBindRow]) -> Vec<MdocWindowColumnEval> {
    let mut columns = vec![
        vec![M31::from_u32_unchecked(0); 1 << MDOC_WINDOW_BIND_LOG_SIZE];
        MDOC_WINDOW_BIND_PREPROCESSED_COLS
    ];
    for (row_idx, row) in rows.iter().enumerate() {
        columns[0][row_idx] = M31::from_u32_unchecked(1);
        columns[1][row_idx] = M31::from_u32_unchecked(row.field_id);
        columns[2][row_idx] =
            M31::from_u32_unchecked(u32::from(row.target == MdocWindowTarget::Constant));
        columns[3][row_idx] =
            M31::from_u32_unchecked(u32::from(row.target == MdocWindowTarget::BirthDigest));
        columns[4][row_idx] =
            M31::from_u32_unchecked(u32::from(row.target == MdocWindowTarget::NationalityDigest));
        for i in 0..32 {
            if i < row.len {
                columns[8 + i][row_idx] = M31::from_u32_unchecked(1);
            }
            columns[40 + i][row_idx] = M31::from_u32_unchecked(u32::from(row.expected[i]));
        }
        let source_col = match row.source {
            MdocFieldSource::IssuerMso => 5,
            MdocFieldSource::BirthItem => 6,
            MdocFieldSource::NationalityItem => 7,
        };
        columns[source_col][row_idx] = M31::from_u32_unchecked(1);
    }
    columns
        .into_iter()
        .map(|values| mdoc_window_column_eval(MDOC_WINDOW_BIND_LOG_SIZE, values))
        .collect()
}

fn mdoc_window_bind_base_trace(rows: &[MdocWindowBindRow]) -> Vec<MdocWindowColumnEval> {
    (0..32)
        .map(|byte_idx| {
            let mut values = vec![M31::from_u32_unchecked(0); 1 << MDOC_WINDOW_BIND_LOG_SIZE];
            for (row_idx, row) in rows.iter().enumerate() {
                if byte_idx < row.len {
                    values[row_idx] = M31::from_u32_unchecked(u32::from(row.witness[byte_idx]));
                }
            }
            mdoc_window_column_eval(MDOC_WINDOW_BIND_LOG_SIZE, values)
        })
        .collect()
}

fn mdoc_window_bind_interaction_trace(
    rows: &[MdocWindowBindRow],
    issuer_field_relation: &FieldBytesRelation,
    birth_field_relation: &FieldBytesRelation,
    nat_field_relation: &FieldBytesRelation,
    birth_digest_relation: &DigestBytesRelation,
    nat_digest_relation: &DigestBytesRelation,
) -> (Vec<MdocWindowColumnEval>, MdocWindowBindInteractionClaim) {
    let preprocessed = mdoc_window_bind_preprocessed_columns(rows);
    let trace = mdoc_window_bind_base_trace(rows);
    let n_vec_rows = 1usize << (MDOC_WINDOW_BIND_LOG_SIZE - LOG_N_LANES);
    let mut sites: Vec<Vec<(PackedQM31, PackedQM31)>> =
        Vec::with_capacity(MDOC_WINDOW_BIND_LOOKUPS);
    for byte_idx in 0..32 {
        for (source_col, relation) in [
            (5usize, issuer_field_relation),
            (6usize, birth_field_relation),
            (7usize, nat_field_relation),
        ] {
            sites.push(
                (0..n_vec_rows)
                    .map(|vec_row| {
                        let numerator = PackedQM31::from(
                            preprocessed[8 + byte_idx].data[vec_row]
                                * preprocessed[source_col].data[vec_row],
                        );
                        let denominator = relation.combine(&[
                            preprocessed[1].data[vec_row],
                            PackedM31::broadcast(M31::from_u32_unchecked(byte_idx as u32)),
                            trace[byte_idx].data[vec_row],
                        ]);
                        (numerator, denominator)
                    })
                    .collect(),
            );
        }
    }
    for (active_col, relation) in [
        (3usize, birth_digest_relation),
        (4usize, nat_digest_relation),
    ] {
        sites.push(
            (0..n_vec_rows)
                .map(|vec_row| {
                    let numerator = PackedQM31::from(preprocessed[active_col].data[vec_row]);
                    let mut values = [PackedM31::broadcast(M31::from_u32_unchecked(0)); 32];
                    for (byte_idx, value) in values.iter_mut().enumerate() {
                        *value = trace[byte_idx].data[vec_row];
                    }
                    let denominator = relation.combine(&values);
                    (numerator, denominator)
                })
                .collect(),
        );
    }
    debug_assert_eq!(sites.len(), MDOC_WINDOW_BIND_LOOKUPS);
    let mut logup = LogupTraceGenerator::new(MDOC_WINDOW_BIND_LOG_SIZE);
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
    let (trace, claimed_sum) = logup.finalize_last();
    (trace, MdocWindowBindInteractionClaim { claimed_sum })
}

impl FrameworkEval for MdocWindowBindEval {
    fn log_size(&self) -> u32 {
        MDOC_WINDOW_BIND_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        MDOC_WINDOW_BIND_LOG_SIZE + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(mdoc_window_bind_col_id("active"));
        let field_id = eval.get_preprocessed_column(mdoc_window_bind_col_id("field_id"));
        let constant_active =
            eval.get_preprocessed_column(mdoc_window_bind_col_id("constant_active"));
        let birth_digest_active =
            eval.get_preprocessed_column(mdoc_window_bind_col_id("birth_digest_active"));
        let nat_digest_active =
            eval.get_preprocessed_column(mdoc_window_bind_col_id("nat_digest_active"));
        let issuer_field_active =
            eval.get_preprocessed_column(mdoc_window_bind_col_id("issuer_field_active"));
        let birth_field_active =
            eval.get_preprocessed_column(mdoc_window_bind_col_id("birth_field_active"));
        let nat_field_active =
            eval.get_preprocessed_column(mdoc_window_bind_col_id("nat_field_active"));
        let one = m31_const::<E>(1);
        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint(constant_active.clone() * (constant_active.clone() - one.clone()));
        eval.add_constraint(
            birth_digest_active.clone() * (birth_digest_active.clone() - one.clone()),
        );
        eval.add_constraint(nat_digest_active.clone() * (nat_digest_active.clone() - one.clone()));
        eval.add_constraint(
            issuer_field_active.clone() * (issuer_field_active.clone() - one.clone()),
        );
        eval.add_constraint(
            birth_field_active.clone() * (birth_field_active.clone() - one.clone()),
        );
        eval.add_constraint(nat_field_active.clone() * (nat_field_active.clone() - one.clone()));
        eval.add_constraint(
            active.clone()
                * (constant_active.clone()
                    + birth_digest_active.clone()
                    + nat_digest_active.clone()
                    - one.clone()),
        );
        eval.add_constraint(
            active.clone()
                * (issuer_field_active.clone()
                    + birth_field_active.clone()
                    + nat_field_active.clone()
                    - one.clone()),
        );

        let mut values = Vec::with_capacity(32);
        for byte_idx in 0..32 {
            let byte_active = eval.get_preprocessed_column(mdoc_window_bind_col_id(&format!(
                "byte_active_{byte_idx}"
            )));
            let expected = eval
                .get_preprocessed_column(mdoc_window_bind_col_id(&format!("expected_{byte_idx}")));
            let value = eval.next_trace_mask();
            eval.add_constraint(byte_active.clone() * (byte_active.clone() - one.clone()));
            eval.add_constraint((one.clone() - byte_active.clone()) * value.clone());
            eval.add_constraint(
                constant_active.clone() * byte_active.clone() * (value.clone() - expected),
            );
            for (source_active, relation) in [
                (issuer_field_active.clone(), &self.issuer_field_relation),
                (birth_field_active.clone(), &self.birth_field_relation),
                (nat_field_active.clone(), &self.nat_field_relation),
            ] {
                eval.add_to_relation(RelationEntry::new(
                    relation,
                    E::EF::from(byte_active.clone() * source_active),
                    &[
                        field_id.clone(),
                        m31_const::<E>(byte_idx as u32),
                        value.clone(),
                    ],
                ));
            }
            values.push(value);
        }
        eval.add_to_relation(RelationEntry::new(
            &self.birth_digest_relation,
            E::EF::from(birth_digest_active),
            &values,
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.nat_digest_relation,
            E::EF::from(nat_digest_active),
            &values,
        ));
        eval.finalize_logup_in_pairs();
        eval
    }
}

impl Air for MdocWindowBind {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        for row in &self.rows {
            channel.mix_u64(u64::from(row.field_id));
            channel.mix_u64(row.len as u64);
            channel.mix_u64(match row.target {
                MdocWindowTarget::Constant => 0,
                MdocWindowTarget::BirthDigest => 1,
                MdocWindowTarget::NationalityDigest => 2,
            });
            if row.target == MdocWindowTarget::Constant {
                for &byte in &row.expected[..row.len] {
                    channel.mix_u64(u64::from(byte));
                }
            }
        }
    }

    fn draw_relations(&mut self, _channel: &mut Blake2sChannel) {}

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![MDOC_WINDOW_BIND_LOG_SIZE; MDOC_WINDOW_BIND_PREPROCESSED_COLS],
            trace: vec![MDOC_WINDOW_BIND_LOG_SIZE; MDOC_WINDOW_BIND_TRACE_COLS],
            interaction: vec![MDOC_WINDOW_BIND_LOG_SIZE; MDOC_WINDOW_BIND_INTERACTION_COLS],
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        vec![self.interaction_claim().claimed_sum]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        mdoc_window_bind_preprocessed_column_ids()
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.component = Some(MdocWindowBindComponent::new(
            allocator,
            MdocWindowBindEval {
                issuer_field_relation: self.issuer_field_relation(),
                birth_field_relation: self.birth_field_relation(),
                nat_field_relation: self.nat_field_relation(),
                birth_digest_relation: self.birth_digest_relation(),
                nat_digest_relation: self.nat_digest_relation(),
            },
            self.interaction_claim().claimed_sum,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![self
            .component
            .as_ref()
            .expect("mdoc window bind component is built")]
    }
}

impl AirProver for MdocWindowBind {
    fn max_log_size(&self) -> u32 {
        MDOC_WINDOW_BIND_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        MDOC_WINDOW_BIND_LOG_SIZE + 1
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        self.write_selected_preprocessed(tb, &mdoc_window_bind_preprocessed_column_ids());
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc_window_bind::MdocWindowBind",
            &mdoc_window_bind_preprocessed_column_ids(),
            &mdoc_window_bind_preprocessed_columns(&self.rows),
        )
    }

    fn write_selected_preprocessed(
        &mut self,
        tb: &mut TreeBuilder<SimdBackend, air_core::Mc>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        let all_ids = mdoc_window_bind_preprocessed_column_ids();
        let all_columns = mdoc_window_bind_preprocessed_columns(&self.rows);
        let selected = selected_ids
            .iter()
            .map(|id| {
                all_ids
                    .iter()
                    .position(|candidate| candidate == id)
                    .map(|index| all_columns[index].clone())
                    .expect("unexpected mdoc window bind preprocessed selection")
            })
            .collect();
        tb.extend_evals(selected);
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(mdoc_window_bind_base_trace(&self.rows));
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let (trace, claim) = mdoc_window_bind_interaction_trace(
            &self.rows,
            &self.issuer_field_relation(),
            &self.birth_field_relation(),
            &self.nat_field_relation(),
            &self.birth_digest_relation(),
            &self.nat_digest_relation(),
        );
        tb.extend_evals(trace);
        self.interaction_claim = Some(claim);
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![self
            .component
            .as_ref()
            .expect("mdoc window bind component is built")]
    }
}
