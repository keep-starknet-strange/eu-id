//! Test harness for `sampleinball_fsm` via `air-core`. Contributes, in commit order:
//!   1. `sib`             — the [CHAL] FSM + ternary/τ + c-binding component.
//!   2. `range_table`      — the shared `(value, bound_id)` range table (C5),
//!      self-drawn here (standalone mode) rather than shared through a hosted
//!      handle.
//!   3. `ccell_provider`   — TEST-SIDE balancer yielding the coeffs C-cell
//!      `(c_bind_id, c)` tuples that the FSM consumes.
//!   4. `hashio_producer`  — TEST-SIDE balancer yielding the squeeze bytes the FSM
//!      consumes. The composed statement uses the proven sponge squeeze.

use num_traits::Zero;
use stwo::core::air::Component;
use stwo::core::channel::Blake2sChannel;
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::PcsConfig;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;
use stwo::core::verifier::VerificationError;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::{ComponentProver, ProvingError, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{FrameworkComponent, TraceLocationAllocator};

use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};

use crate::air_util::{enc_signed, padded_log_size, ColEval};
use crate::balancer::{
    gen_balancer_interaction, gen_balancer_trace, BalancerEval, BalancerRelation,
    BALANCER_INTERACTION_COLS,
};
use crate::binding::{CCELL_ARITY, HASH_IO_ARITY, STREAM_ID_SIB_SQUEEZE};
use crate::coeffs::tables::{
    gen_range_table_interaction, gen_range_table_multiplicities, gen_range_table_preprocessed,
    range_table_log_size, range_table_preprocessed_ids, RangeTableEval, RANGE_TABLE_INTERACTION_COLS,
};
use crate::coeffs::tables::RcKind;
use crate::constants::N;
use crate::profile::ML_DSA_65;
use crate::witness::MlDsaWitness;

use super::relations::SibRelations;
use super::{
    gen_sib_base_trace, gen_sib_interaction, gen_sib_metadata, gen_sib_preprocessed,
    sib_preprocessed_ids, SibEval, MAX_SIB_SQUEEZE_BYTES, N_ACCESSES, N_BASE_COLS,
    N_INTERACTION_COLS,
};

pub struct SibProof {
    pub sib_claimed_sum: SecureField,
    pub range_claimed_sum: SecureField,
    pub ccell_claimed_sum: SecureField,
    pub hashio_claimed_sum: SecureField,
    pub log_size: u32,
    pub ccell_log_size: u32,
    pub hashio_log_size: u32,
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
}

fn sib_log_size() -> u32 {
    // Cover the stream+c stages AND the offline-memory sorted view (N_ACCESSES).
    padded_log_size((MAX_SIB_SQUEEZE_BYTES + N).max(N_ACCESSES))
}
fn ccell_log_size() -> u32 {
    padded_log_size(N)
}
fn hashio_log_size() -> u32 {
    padded_log_size(MAX_SIB_SQUEEZE_BYTES)
}

fn all_preprocessed_ids() -> Vec<PreProcessedColumnId> {
    let mut ids = sib_preprocessed_ids();
    ids.extend(range_table_preprocessed_ids());
    ids
}

fn all_preprocessed_log_sizes(log_size: u32) -> Vec<u32> {
    let mut sizes = vec![log_size; sib_preprocessed_ids().len()];
    sizes.extend(vec![range_table_log_size(); range_table_preprocessed_ids().len()]);
    sizes
}

fn gen_all_preprocessed(log_size: u32) -> Vec<ColEval> {
    let mut cols = gen_sib_preprocessed(ML_DSA_65, log_size);
    cols.extend(gen_range_table_preprocessed());
    cols
}

/// This standalone harness's own range-use census, converted to the 7-slot
/// shape [`gen_range_table_multiplicities`] expects. Only Rc8/Rc11 are ever
/// nonzero for SIB; the rest stay at the `RcUses::new()` zero default.
fn range_uses_arrays(rc_uses: &crate::coeffs::RcUses) -> [&[u32]; 7] {
    core::array::from_fn(|index| rc_uses.for_kind(RcKind::ALL[index]))
}

fn ccell_tuples(witness: &MlDsaWitness) -> Vec<Vec<u32>> {
    (0..N)
        .map(|m| vec![m as u32, enc_signed(witness.digits.c[m]).0])
        .collect()
}

fn hashio_tuples(bytes: &[u8]) -> Vec<Vec<u32>> {
    bytes
        .iter()
        .enumerate()
        .map(|(pos, &b)| vec![STREAM_ID_SIB_SQUEEZE, pos as u32, b as u32])
        .collect()
}

struct Built {
    sib: FrameworkComponent<SibEval>,
    range: FrameworkComponent<RangeTableEval>,
    ccell: FrameworkComponent<BalancerEval>,
    hashio: FrameworkComponent<BalancerEval>,
}

impl Built {
    fn as_components(&self) -> Vec<&dyn Component> {
        vec![
            &self.sib as &dyn Component,
            &self.range as &dyn Component,
            &self.ccell as &dyn Component,
            &self.hashio as &dyn Component,
        ]
    }
    fn as_prover(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            &self.sib as &dyn ComponentProver<SimdBackend>,
            &self.range as &dyn ComponentProver<SimdBackend>,
            &self.ccell as &dyn ComponentProver<SimdBackend>,
            &self.hashio as &dyn ComponentProver<SimdBackend>,
        ]
    }
}

pub struct SibProver {
    witness: MlDsaWitness,
    relations: Option<SibRelations>,
    sib_claimed_sum: SecureField,
    range_claimed_sum: SecureField,
    ccell_claimed_sum: SecureField,
    hashio_claimed_sum: SecureField,
    range_mult: Option<ColEval>,
    stream_bytes: Vec<u8>,
    built: Option<Built>,
}

struct SibVerifier {
    witness_log_size: u32,
    hashio_log_size: u32,
    sib_claimed_sum: SecureField,
    range_claimed_sum: SecureField,
    ccell_claimed_sum: SecureField,
    hashio_claimed_sum: SecureField,
    relations: Option<SibRelations>,
    built: Option<Built>,
}

#[allow(clippy::too_many_arguments)]
fn build_components(
    allocator: &mut TraceLocationAllocator,
    log_size: u32,
    ccell_ls: u32,
    hashio_ls: u32,
    relations: &SibRelations,
    sib_claimed_sum: SecureField,
    range_claimed_sum: SecureField,
    ccell_claimed_sum: SecureField,
    hashio_claimed_sum: SecureField,
) -> Built {
    let sib = FrameworkComponent::new(
        allocator,
        SibEval {
            profile: crate::profile::ML_DSA_65,
            log_size,
            ns: String::new(),
            sib_stream: STREAM_ID_SIB_SQUEEZE,
            relations: relations.clone(),
        },
        sib_claimed_sum,
    );
    // Standalone-only shared range table (C5): SIB draws its OWN `range`
    // relation independently (`SibRelations::draw`), so it needs its own
    // matching provider here, not the hosted `SharedRangeTable` handle.
    let range = FrameworkComponent::new(
        allocator,
        RangeTableEval {
            relation: relations.range.clone(),
        },
        range_claimed_sum,
    );
    // ccell provider: FSM consumes (+); provider yields (−).
    let ccell = FrameworkComponent::new(
        allocator,
        BalancerEval {
            log_size: ccell_ls,
            arity: CCELL_ARITY,
            relation: BalancerRelation::CCell(relations.ccell.clone()),
            sign_positive: false,
        },
        ccell_claimed_sum,
    );
    // hashio producer: FSM consumes (−); producer yields (+).
    let hashio = FrameworkComponent::new(
        allocator,
        BalancerEval {
            log_size: hashio_ls,
            arity: HASH_IO_ARITY,
            relation: BalancerRelation::HashIo(relations.hash_io.clone()),
            sign_positive: true,
        },
        hashio_claimed_sum,
    );
    Built {
        sib,
        range,
        ccell,
        hashio,
    }
}

fn module_trace_layout(log_size: u32, ccell_ls: u32, hashio_ls: u32) -> Vec<u32> {
    let mut trace = vec![log_size; N_BASE_COLS];
    trace.push(range_table_log_size());
    for _ in 0..crate::balancer::balancer_base_cols(CCELL_ARITY) {
        trace.push(ccell_ls);
    }
    for _ in 0..crate::balancer::balancer_base_cols(HASH_IO_ARITY) {
        trace.push(hashio_ls);
    }
    trace
}

fn module_interaction_layout(log_size: u32, ccell_ls: u32, hashio_ls: u32) -> Vec<u32> {
    let mut inter = vec![log_size; N_INTERACTION_COLS];
    for _ in 0..RANGE_TABLE_INTERACTION_COLS {
        inter.push(range_table_log_size());
    }
    for _ in 0..BALANCER_INTERACTION_COLS {
        inter.push(ccell_ls);
    }
    for _ in 0..BALANCER_INTERACTION_COLS {
        inter.push(hashio_ls);
    }
    inter
}

impl Air for SibProver {
    fn mix_public(&self, _channel: &mut Blake2sChannel) {}
    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.relations = Some(SibRelations::draw(channel));
    }
    fn layout(&self) -> TreeLayout {
        let ls = sib_log_size();
        TreeLayout {
            preprocessed: all_preprocessed_log_sizes(ls),
            trace: module_trace_layout(ls, ccell_log_size(), hashio_log_size()),
            interaction: module_interaction_layout(ls, ccell_log_size(), hashio_log_size()),
        }
    }
    fn claimed_sums(&self) -> Vec<SecureField> {
        vec![
            self.sib_claimed_sum,
            self.range_claimed_sum,
            self.ccell_claimed_sum,
            self.hashio_claimed_sum,
        ]
    }
    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        all_preprocessed_ids()
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.built = Some(build_components(
            allocator,
            sib_log_size(),
            ccell_log_size(),
            hashio_log_size(),
            self.relations.as_ref().expect("relations"),
            self.sib_claimed_sum,
            self.range_claimed_sum,
            self.ccell_claimed_sum,
            self.hashio_claimed_sum,
        ));
    }
    fn components(&self) -> Vec<&dyn Component> {
        self.built.as_ref().expect("built").as_components()
    }
}

impl AirProver for SibProver {
    fn max_log_size(&self) -> u32 {
        sib_log_size()
            .max(range_table_log_size())
            .max(ccell_log_size())
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.max_log_size() + 1
    }
    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(gen_all_preprocessed(sib_log_size()));
    }
    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        let ls = sib_log_size();
        fingerprint_preprocessed_columns(
            "mldsa_sib",
            &all_preprocessed_ids(),
            &gen_all_preprocessed(ls),
        )
    }
    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let ls = sib_log_size();
        let mut evals = gen_sib_base_trace(&self.witness, ls);
        let metadata = gen_sib_metadata(&self.witness);
        self.stream_bytes = metadata.stream_bytes;
        let range_mult = gen_range_table_multiplicities(range_uses_arrays(&metadata.rc_uses));
        self.range_mult = Some(range_mult.clone());
        evals.push(range_mult);
        evals.extend(gen_balancer_trace(
            ccell_log_size(),
            &ccell_tuples(&self.witness),
        ));
        evals.extend(gen_balancer_trace(
            hashio_log_size(),
            &hashio_tuples(&self.stream_bytes),
        ));
        tb.extend_evals(evals);
    }
    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let ls = sib_log_size();
        let relations = self.relations.clone().expect("relations");
        let interaction = gen_sib_interaction(&self.witness, ls, STREAM_ID_SIB_SQUEEZE, &relations);
        let mut evals = interaction.trace;
        self.sib_claimed_sum = interaction.claimed_sum;

        let (range_tr, range_sum) = gen_range_table_interaction(
            self.range_mult.as_ref().expect("range mult written"),
            &relations.range,
        );
        evals.extend(range_tr);
        self.range_claimed_sum = range_sum;
        let (ctr, csum) = gen_balancer_interaction(
            ccell_log_size(),
            &ccell_tuples(&self.witness),
            &BalancerRelation::CCell(relations.ccell.clone()),
            false,
        );
        self.ccell_claimed_sum = csum;
        evals.extend(ctr);
        let (htr, hsum) = gen_balancer_interaction(
            hashio_log_size(),
            &hashio_tuples(&self.stream_bytes),
            &BalancerRelation::HashIo(relations.hash_io.clone()),
            true,
        );
        self.hashio_claimed_sum = hsum;
        evals.extend(htr);
        tb.extend_evals(evals);
    }
    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        self.built.as_ref().expect("built").as_prover()
    }
}

impl Air for SibVerifier {
    fn mix_public(&self, _channel: &mut Blake2sChannel) {}
    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.relations = Some(SibRelations::draw(channel));
    }
    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: all_preprocessed_log_sizes(self.witness_log_size),
            trace: module_trace_layout(
                self.witness_log_size,
                ccell_log_size(),
                self.hashio_log_size,
            ),
            interaction: module_interaction_layout(
                self.witness_log_size,
                ccell_log_size(),
                self.hashio_log_size,
            ),
        }
    }
    fn claimed_sums(&self) -> Vec<SecureField> {
        vec![
            self.sib_claimed_sum,
            self.range_claimed_sum,
            self.ccell_claimed_sum,
            self.hashio_claimed_sum,
        ]
    }
    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        all_preprocessed_ids()
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.built = Some(build_components(
            allocator,
            self.witness_log_size,
            ccell_log_size(),
            self.hashio_log_size,
            self.relations.as_ref().expect("relations"),
            self.sib_claimed_sum,
            self.range_claimed_sum,
            self.ccell_claimed_sum,
            self.hashio_claimed_sum,
        ));
    }
    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, VerificationError> {
        // Reconstruct tree-0 verifier-side for the pinned-root check in
        // `verify_sib`. `witness_log_size` equals `sib_log_size()` on the honest
        // path (rejected otherwise before we get here), so this matches the
        // columns the prover committed, in `all_preprocessed_ids` order.
        Ok(gen_all_preprocessed(self.witness_log_size))
    }
    fn components(&self) -> Vec<&dyn Component> {
        self.built.as_ref().expect("built").as_components()
    }
}

pub fn prove_sib(witness: MlDsaWitness, config: PcsConfig) -> Result<SibProof, ProvingError> {
    super::validate_stream(&witness).map_err(|_| ProvingError::ConstraintsNotSatisfied)?;
    let log_size = sib_log_size();
    let hio_ls = hashio_log_size();
    let mut prover = SibProver {
        witness,
        relations: None,
        sib_claimed_sum: SecureField::zero(),
        range_claimed_sum: SecureField::zero(),
        ccell_claimed_sum: SecureField::zero(),
        hashio_claimed_sum: SecureField::zero(),
        range_mult: None,
        stream_bytes: Vec::new(),
        built: None,
    };
    let stark_proof = air_core::prove(&mut [&mut prover], config)?;
    Ok(SibProof {
        sib_claimed_sum: prover.sib_claimed_sum,
        range_claimed_sum: prover.range_claimed_sum,
        ccell_claimed_sum: prover.ccell_claimed_sum,
        hashio_claimed_sum: prover.hashio_claimed_sum,
        log_size,
        ccell_log_size: ccell_log_size(),
        hashio_log_size: hio_ls,
        stark_proof,
    })
}

/// Verify a standalone SampleInBall proof under the caller's exact PCS policy.
pub fn verify_sib(
    proof: &SibProof,
    _witness: &MlDsaWitness,
    expected_config: PcsConfig,
) -> Result<(), VerificationError> {
    if proof.stark_proof.config != expected_config {
        return Err(VerificationError::InvalidStructure(
            "mldsa_sib: unexpected PCS configuration".into(),
        ));
    }
    if proof.log_size != sib_log_size()
        || proof.ccell_log_size != ccell_log_size()
        || proof.hashio_log_size != hashio_log_size()
    {
        return Err(VerificationError::InvalidStructure(
            "mldsa_sib: unexpected standalone layout".into(),
        ));
    }
    let mut verifier = SibVerifier {
        witness_log_size: proof.log_size,
        hashio_log_size: proof.hashio_log_size,
        sib_claimed_sum: proof.sib_claimed_sum,
        range_claimed_sum: proof.range_claimed_sum,
        ccell_claimed_sum: proof.ccell_claimed_sum,
        hashio_claimed_sum: proof.hashio_claimed_sum,
        relations: None,
        built: None,
    };
    let expected_root =
        air_core::compute_canonical_preprocessed_root(&mut [&mut verifier], expected_config)?;
    air_core::verify_with_expected_preprocessed_root(
        &mut [&mut verifier],
        &proof.stark_proof,
        Some(expected_root),
    )
    .map_err(|error| match error {
        air_core::VerifyError::Stark(error) => error,
        air_core::VerifyError::PreprocessedRootMismatch { .. } => {
            VerificationError::InvalidStructure(
                "mldsa_sib: preprocessed root mismatch (forged tree-0)".into(),
            )
        }
    })
}
