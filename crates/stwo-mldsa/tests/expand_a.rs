mod common;

use std::sync::{Mutex, OnceLock};

use air_core::{
    compute_preprocessed_root_uncached, Air, AirProver, CommitmentRoot,
    PreprocessedColumnFingerprint, TreeLayout, VerifyError,
};
use num_traits::{One, Zero};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::P as M31_MODULUS;
use stwo::core::fields::qm31::SecureField;
use stwo::core::proof::StarkProof;
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::{ComponentProver, ProvingError, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{FrameworkComponent, TraceLocationAllocator};

use stwo_keccak::relations::{KeccakRelations, SharedKeccakRelations};
use stwo_keccak::service::{KeccakServiceProver, KeccakServiceVerifier};
use stwo_keccak::sponge::Shape;
use stwo_mldsa::air_util::padded_log_size;
use stwo_mldsa::balancer::{
    balancer_base_cols, gen_balancer_interaction, gen_balancer_trace, BalancerEval,
    BalancerRelation, BALANCER_INTERACTION_COLS,
};
use stwo_mldsa::binding::{HASH_IO_ARITY, NTT_CELL_ARITY, RHO_CELL_ARITY};
use stwo_mldsa::coeffs::relations::SharedRangeRelation;
use stwo_mldsa::coeffs::tables::SharedRangeTable;
use stwo_mldsa::constants::{L, N, Q};
use stwo_mldsa::expand_a::{
    absorb_stream_id, derive_expand_a_witness, shake128_absorb_streams, shake128_job_shapes,
    squeeze_stream_id, ExpandABindings, ExpandAClaim, ExpandAPreprocessedComponent, ExpandAProver,
    ExpandATraceAttack, ExpandAVerifier, ABSORB_ACTIVE_ROWS, MATRIX_POLYS, MAX_CANDIDATES,
    MAX_EXPAND_A_SQUEEZE_BYTES, REJECTION_BASE_COLS, TRACE_COL_ACCEPT, TRACE_COL_ACCEPT_SLACK0,
    TRACE_COL_ACCEPT_SLACK1, TRACE_COL_ACCEPT_SLACK2, TRACE_COL_B0, TRACE_COL_B1, TRACE_COL_B2,
    TRACE_COL_INDEX, TRACE_COL_LOW7, TRACE_COL_REJECT_DELTA, TRACE_COL_SAMPLE,
};
use stwo_mldsa::profile::ML_DSA_65;
use stwo_mldsa::reference::sponge::shake128;

const NAMESPACE: &str = "expand-a-test";
const STREAM_BASE: u32 = 256;
const OWNER_TAG: u64 = 0x4558_5041_4f57_4e52;
const BALANCER_TAG: u64 = 0x4558_5041_4241_4c41;
const ABSORB_PRE_BYTE_POS: usize = 0;
const ABSORB_PRE_STREAM: usize = 1;
const REJECTION_PRE_BYTE_POS: usize = 3;
const REJECTION_PRE_STREAM: usize = 4;
static PROOF_LOCK: Mutex<()> = Mutex::new(());
static CORE_PREPROCESSED_ROOT: OnceLock<CommitmentRoot> = OnceLock::new();
static SERVICE_PREPROCESSED_ROOT: OnceLock<CommitmentRoot> = OnceLock::new();

/// Draws the exact Keccak relation family without providing a sponge. Core AIR
/// tests balance HashIo with explicit tuples; the ignored integration test uses
/// the real Keccak service instead.
struct TestKeccakOwner {
    handle: SharedKeccakRelations,
}

impl Air for TestKeccakOwner {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(OWNER_TAG);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.handle.set(KeccakRelations::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![],
            trace: vec![],
            interaction: vec![],
        }
    }

    fn claimed_sums(&self) -> Vec<SecureField> {
        vec![]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        vec![]
    }

    fn build_components(&mut self, _allocator: &mut TraceLocationAllocator) {}

    fn components(&self) -> Vec<&dyn Component> {
        vec![]
    }
}

impl AirProver for TestKeccakOwner {
    fn max_log_size(&self) -> u32 {
        LOG_N_LANES
    }

    fn write_preprocessed(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        vec![]
    }

    fn write_trace(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

    fn write_interaction(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![]
    }
}

#[derive(Clone, Copy)]
enum BindingKind {
    Absorb,
    Squeeze,
    Rho,
    Ntt,
}

struct BindingSpec {
    kind: BindingKind,
    tuples: Vec<Vec<u32>>,
    sign_positive: bool,
}

impl BindingSpec {
    fn arity(&self) -> usize {
        match self.kind {
            BindingKind::Absorb | BindingKind::Squeeze => HASH_IO_ARITY,
            BindingKind::Rho => RHO_CELL_ARITY,
            BindingKind::Ntt => NTT_CELL_ARITY,
        }
    }

    fn log_size(&self) -> u32 {
        padded_log_size(self.tuples.len())
    }
}

struct TestBalancers {
    specs: Vec<BindingSpec>,
    claims: Vec<SecureField>,
    keccak_handle: SharedKeccakRelations,
    bindings: ExpandABindings,
    relations: Vec<BalancerRelation>,
    built: Vec<FrameworkComponent<BalancerEval>>,
}

impl TestBalancers {
    fn new(
        rho: &[u8; 32],
        hash_rho: &[u8; 32],
        include_hash: bool,
        keccak_handle: SharedKeccakRelations,
        bindings: ExpandABindings,
    ) -> Self {
        let mut specs = Vec::new();
        if include_hash {
            let (absorb, squeeze) = hash_tuples(hash_rho);
            specs.push(BindingSpec {
                kind: BindingKind::Absorb,
                tuples: absorb,
                sign_positive: false,
            });
            specs.push(BindingSpec {
                kind: BindingKind::Squeeze,
                tuples: squeeze,
                sign_positive: true,
            });
        }
        specs.push(BindingSpec {
            kind: BindingKind::Rho,
            tuples: rho_tuples(rho),
            sign_positive: false,
        });
        specs.push(BindingSpec {
            kind: BindingKind::Ntt,
            tuples: ntt_tuples(rho),
            sign_positive: false,
        });
        let claims = vec![SecureField::zero(); specs.len()];
        Self {
            specs,
            claims,
            keccak_handle,
            bindings,
            relations: Vec::new(),
            built: Vec::new(),
        }
    }

    fn with_claims(mut self, claims: Vec<SecureField>) -> Self {
        assert_eq!(claims.len(), self.specs.len());
        self.claims = claims;
        self
    }

    fn relation(&self, kind: BindingKind) -> BalancerRelation {
        match kind {
            BindingKind::Absorb | BindingKind::Squeeze => {
                BalancerRelation::HashIo(self.keccak_handle.get().hash_io)
            }
            BindingKind::Rho => BalancerRelation::RhoCell(self.bindings.rho.get()),
            BindingKind::Ntt => BalancerRelation::NttCell(self.bindings.ntt.get()),
        }
    }
}

impl Air for TestBalancers {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(BALANCER_TAG);
        channel.mix_u64(self.specs.len() as u64);
    }

    fn draw_relations(&mut self, _channel: &mut Blake2sChannel) {
        self.relations = self
            .specs
            .iter()
            .map(|spec| self.relation(spec.kind))
            .collect();
    }

    fn layout(&self) -> TreeLayout {
        let mut trace = Vec::new();
        let mut interaction = Vec::new();
        for spec in &self.specs {
            trace.extend(vec![spec.log_size(); balancer_base_cols(spec.arity())]);
            interaction.extend(vec![spec.log_size(); BALANCER_INTERACTION_COLS]);
        }
        TreeLayout {
            preprocessed: vec![],
            trace,
            interaction,
        }
    }

    fn claimed_sums(&self) -> Vec<SecureField> {
        self.claims.clone()
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        vec![]
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.built = self
            .specs
            .iter()
            .zip(&self.relations)
            .zip(&self.claims)
            .map(|((spec, relation), &claim)| {
                FrameworkComponent::new(
                    allocator,
                    BalancerEval {
                        log_size: spec.log_size(),
                        arity: spec.arity(),
                        relation: relation.clone(),
                        sign_positive: spec.sign_positive,
                    },
                    claim,
                )
            })
            .collect();
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built
            .iter()
            .map(|component| component as &dyn Component)
            .collect()
    }
}

impl AirProver for TestBalancers {
    fn max_log_size(&self) -> u32 {
        self.specs
            .iter()
            .map(BindingSpec::log_size)
            .max()
            .unwrap_or(LOG_N_LANES)
    }

    fn write_preprocessed(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        vec![]
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let mut trace = Vec::new();
        for spec in &self.specs {
            trace.extend(gen_balancer_trace(spec.log_size(), &spec.tuples));
        }
        tb.extend_evals(trace);
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let mut trace = Vec::new();
        for (index, (spec, relation)) in self.specs.iter().zip(&self.relations).enumerate() {
            let (component_trace, claim) = gen_balancer_interaction(
                spec.log_size(),
                &spec.tuples,
                relation,
                spec.sign_positive,
            );
            self.claims[index] = claim;
            trace.extend(component_trace);
        }
        tb.extend_evals(trace);
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        self.built
            .iter()
            .map(|component| component as &dyn ComponentProver<SimdBackend>)
            .collect()
    }
}

fn rho_tuples(rho: &[u8; 32]) -> Vec<Vec<u32>> {
    rho.iter()
        .enumerate()
        .map(|(index, &byte)| vec![index as u32, byte as u32])
        .collect()
}

fn ntt_tuples(rho: &[u8; 32]) -> Vec<Vec<u32>> {
    let expanded = stwo_mldsa::reference::expand_a::expand_a(ML_DSA_65, rho);
    let mut tuples = Vec::with_capacity(MATRIX_POLYS * N);
    for poly in 0..MATRIX_POLYS {
        for (index, &value) in expanded.matrix[poly / L][poly % L].iter().enumerate() {
            // C7b: the NTT cell's value is a 12/11-bit split (base 4096),
            // not the earlier 8/8/7-bit byte split.
            tuples.push(vec![
                poly as u32,
                0,
                index as u32,
                value & 0xfff,
                value >> 12,
            ]);
        }
    }
    tuples
}

fn hash_tuples(rho: &[u8; 32]) -> (Vec<Vec<u32>>, Vec<Vec<u32>>) {
    let messages = shake128_absorb_streams(ML_DSA_65, rho);
    let mut absorb = Vec::with_capacity(MATRIX_POLYS * 34);
    let mut squeeze = Vec::with_capacity(MATRIX_POLYS * MAX_EXPAND_A_SQUEEZE_BYTES);
    for (poly, message) in messages.iter().enumerate() {
        for (position, &byte) in message.iter().enumerate() {
            absorb.push(vec![
                absorb_stream_id(ML_DSA_65, STREAM_BASE, poly).expect("valid absorb stream id"),
                position as u32,
                byte as u32,
            ]);
        }
        let output = shake128(&[message], MAX_EXPAND_A_SQUEEZE_BYTES).0;
        for (position, &byte) in output.iter().enumerate() {
            squeeze.push(vec![
                squeeze_stream_id(ML_DSA_65, STREAM_BASE, poly).expect("valid squeeze stream id"),
                position as u32,
                byte as u32,
            ]);
        }
    }
    (absorb, squeeze)
}

#[derive(Clone)]
struct CoreProof {
    rho: [u8; 32],
    expand_claim: ExpandAClaim,
    range_claim: SecureField,
    balancer_claims: Vec<SecureField>,
    stark: StarkProof<air_core::Hasher>,
}

fn prove_core(
    rho: [u8; 32],
    hash_rho: [u8; 32],
    attack: Option<ExpandATraceAttack>,
) -> Result<CoreProof, ProvingError> {
    let range_handle = SharedRangeRelation::new();
    let keccak_handle = SharedKeccakRelations::new();
    let bindings = ExpandABindings::new();
    let witness = derive_expand_a_witness(ML_DSA_65, rho).expect("canonical witness");
    let mut expand = ExpandAProver::new(
        ML_DSA_65,
        witness,
        NAMESPACE,
        STREAM_BASE,
        range_handle.clone(),
        keccak_handle.clone(),
        bindings.clone(),
    )
    .expect("validated ExpandA");
    if let Some(attack) = attack {
        expand = expand.with_trace_attack(attack);
    }
    let mut range = SharedRangeTable::prover(&[expand.range_uses().clone()], range_handle);
    let mut owner = TestKeccakOwner {
        handle: keccak_handle.clone(),
    };
    let mut balancers = TestBalancers::new(&rho, &hash_rho, true, keccak_handle, bindings);
    let stark = air_core::prove(
        &mut [&mut range, &mut owner, &mut expand, &mut balancers],
        common::standalone_pcs_config(),
    )?;
    Ok(CoreProof {
        rho,
        expand_claim: expand.claim(),
        range_claim: range.claimed_sum(),
        balancer_claims: balancers.claimed_sums(),
        stark,
    })
}

fn expected_core_preprocessed_root() -> CommitmentRoot {
    *CORE_PREPROCESSED_ROOT.get_or_init(|| {
        let range_handle = SharedRangeRelation::new();
        let keccak_handle = SharedKeccakRelations::new();
        let bindings = ExpandABindings::new();
        let witness =
            derive_expand_a_witness(ML_DSA_65, [0u8; 32]).expect("canonical root witness");
        let mut expand = ExpandAProver::new(
            ML_DSA_65,
            witness,
            NAMESPACE,
            STREAM_BASE,
            range_handle.clone(),
            keccak_handle,
            bindings,
        )
        .expect("canonical root ExpandA");
        let mut range = SharedRangeTable::prover(&[expand.range_uses().clone()], range_handle);
        compute_preprocessed_root_uncached(
            &mut [&mut range, &mut expand],
            common::standalone_pcs_config(),
        )
    })
}

fn verify_core_with_config(
    proof: &CoreProof,
    namespace: &str,
    stream_base: u32,
) -> Result<(), VerifyError> {
    let range_handle = SharedRangeRelation::new();
    let keccak_handle = SharedKeccakRelations::new();
    let bindings = ExpandABindings::new();
    let mut range = SharedRangeTable::verifier(proof.range_claim, range_handle.clone());
    let mut owner = TestKeccakOwner {
        handle: keccak_handle.clone(),
    };
    let mut expand = ExpandAVerifier::new(
        ML_DSA_65,
        proof.expand_claim.clone(),
        namespace,
        stream_base,
        range_handle,
        keccak_handle.clone(),
        bindings.clone(),
    )
    .expect("valid ExpandA verifier configuration");
    let mut balancers = TestBalancers::new(&proof.rho, &proof.rho, true, keccak_handle, bindings)
        .with_claims(proof.balancer_claims.clone());
    air_core::verify_with_expected_preprocessed_root(
        &mut [&mut range, &mut owner, &mut expand, &mut balancers],
        &proof.stark,
        Some(expected_core_preprocessed_root()),
    )
}

fn verify_core(proof: &CoreProof) -> Result<(), VerifyError> {
    verify_core_with_config(proof, NAMESPACE, STREAM_BASE)
}

fn candidate_rows(rho: &[u8; 32]) -> (usize, usize, usize) {
    let messages = shake128_absorb_streams(ML_DSA_65, rho);
    let mut first_accept = None;
    let mut first_reject = None;
    let mut done = None;
    for (poly, message) in messages.iter().enumerate() {
        let output = shake128(&[message], MAX_EXPAND_A_SQUEEZE_BYTES).0;
        let mut accepted = 0usize;
        for candidate in 0..MAX_CANDIDATES {
            let row = poly * MAX_CANDIDATES + candidate;
            let offset = 3 * candidate;
            let value = output[offset] as u32
                | (output[offset + 1] as u32) << 8
                | ((output[offset + 2] as u32 & 0x7f) << 16);
            if accepted < N {
                if value < Q {
                    first_accept.get_or_insert(row);
                    accepted += 1;
                    if accepted == N && candidate + 1 < MAX_CANDIDATES {
                        done.get_or_insert(row + 1);
                    }
                } else {
                    first_reject.get_or_insert(row);
                }
            }
        }
    }
    (
        first_accept.expect("at least one accepted candidate"),
        first_reject.expect("fixture has a rejected candidate"),
        done.expect("fixture finishes before cap"),
    )
}

/// The raw `(b0, b1, b2)` squeeze bytes backing rejection row `row`.
fn candidate_bytes(rho: &[u8; 32], row: usize) -> [u8; 3] {
    let messages = shake128_absorb_streams(ML_DSA_65, rho);
    let poly = row / MAX_CANDIDATES;
    let candidate = row % MAX_CANDIDATES;
    let output = shake128(&[&messages[poly]], MAX_EXPAND_A_SQUEEZE_BYTES).0;
    let offset = 3 * candidate;
    [output[offset], output[offset + 1], output[offset + 2]]
}

#[test]
fn fixed_expand_a_proves_and_verifies() {
    let _guard = PROOF_LOCK.lock().unwrap();
    let rho = [42u8; 32];
    let proof = prove_core(rho, rho, None).expect("honest proof");
    verify_core(&proof).expect("honest verify");

    let mut tampered = proof.clone();
    tampered.expand_claim.absorb_claimed_sum += SecureField::one();
    assert!(
        verify_core(&tampered).is_err(),
        "forged absorb claim accepted"
    );

    let mut tampered = proof.clone();
    tampered.expand_claim.rejection_claimed_sum += SecureField::one();
    assert!(
        verify_core(&tampered).is_err(),
        "forged ExpandA claim accepted"
    );

    let mut tampered = proof.clone();
    tampered.range_claim += SecureField::one();
    assert!(
        verify_core(&tampered).is_err(),
        "forged range claim accepted"
    );

    for claim_index in 0..proof.balancer_claims.len() {
        let mut tampered = proof.clone();
        tampered.balancer_claims[claim_index] += SecureField::one();
        assert!(
            verify_core(&tampered).is_err(),
            "forged counterpart claim {claim_index} accepted"
        );
    }
    assert!(
        verify_core_with_config(&proof, "wrong-expand-a-namespace", STREAM_BASE).is_err(),
        "wrong namespace transcript accepted"
    );
    assert!(
        verify_core_with_config(&proof, NAMESPACE, STREAM_BASE + 128).is_err(),
        "wrong stream-base transcript accepted"
    );

    let preprocessing_attack = ExpandATraceAttack::Preprocessed {
        component: ExpandAPreprocessedComponent::Absorb,
        row: ABSORB_ACTIVE_ROWS,
        column: ABSORB_PRE_STREAM,
        value: 1,
    };
    let forged_preprocessing = prove_core(rho, rho, Some(preprocessing_attack))
        .expect("padding metadata is unconstrained");
    assert!(matches!(
        verify_core(&forged_preprocessing),
        Err(VerifyError::PreprocessedRootMismatch { .. })
    ));
}

/// Slow manual release test:
/// `rtk cargo test --release -p stwo-mldsa --test expand_a adversarial_traces_and_disconnected_matrix_fail -- --ignored --exact`
#[test]
#[ignore = "serial proof-level adversarial matrix"]
fn adversarial_traces_and_disconnected_matrix_fail() {
    let _guard = PROOF_LOCK.lock().unwrap();
    let rho = [42u8; 32];

    // This test makes ExpandA and its rho and NttCell consumers agree on a
    // forged matrix. The canonical SHAKE provider still uses the correct rho.
    let forged = prove_core([99u8; 32], rho, None).expect("local constraints stay self-consistent");
    assert!(
        verify_core(&forged).is_err(),
        "disconnected forged A_hat must not satisfy the global HashIo balance"
    );

    let (accept_row, reject_row, done_row) = candidate_rows(&rho);
    let attacks = [
        ExpandATraceAttack::Absorb { row: 0, value: 43 },
        ExpandATraceAttack::Absorb { row: 1, value: 43 },
        ExpandATraceAttack::Absorb {
            row: 32 * MATRIX_POLYS,
            value: 1,
        },
        ExpandATraceAttack::Absorb {
            row: 33 * MATRIX_POLYS,
            value: 1,
        },
        ExpandATraceAttack::Absorb {
            row: ABSORB_ACTIVE_ROWS,
            value: 1,
        },
        ExpandATraceAttack::Preprocessed {
            component: ExpandAPreprocessedComponent::Absorb,
            row: 0,
            column: ABSORB_PRE_BYTE_POS,
            value: 1,
        },
        ExpandATraceAttack::Preprocessed {
            component: ExpandAPreprocessedComponent::Absorb,
            row: 0,
            column: ABSORB_PRE_STREAM,
            value: 17,
        },
        ExpandATraceAttack::Rejection {
            row: 0,
            column: TRACE_COL_LOW7,
            value: 128,
        },
        ExpandATraceAttack::Rejection {
            row: accept_row,
            column: TRACE_COL_LOW7,
            value: 128,
        },
        ExpandATraceAttack::Rejection {
            row: 0,
            column: TRACE_COL_SAMPLE,
            value: 2,
        },
        ExpandATraceAttack::Rejection {
            row: reject_row,
            column: TRACE_COL_SAMPLE,
            value: 0,
        },
        ExpandATraceAttack::Rejection {
            row: reject_row,
            column: TRACE_COL_ACCEPT,
            value: 1,
        },
        ExpandATraceAttack::Rejection {
            row: accept_row,
            column: TRACE_COL_ACCEPT,
            value: 0,
        },
        ExpandATraceAttack::Rejection {
            row: accept_row,
            column: TRACE_COL_ACCEPT,
            value: 2,
        },
        ExpandATraceAttack::Rejection {
            row: 0,
            column: TRACE_COL_INDEX,
            value: 1,
        },
        ExpandATraceAttack::Rejection {
            row: 1,
            column: TRACE_COL_INDEX,
            value: 7,
        },
        ExpandATraceAttack::Rejection {
            row: 1,
            column: TRACE_COL_INDEX,
            value: M31_MODULUS - 1,
        },
        ExpandATraceAttack::Rejection {
            row: MAX_CANDIDATES,
            column: TRACE_COL_INDEX,
            value: 1,
        },
        ExpandATraceAttack::Rejection {
            row: accept_row,
            column: TRACE_COL_INDEX,
            value: 7,
        },
        ExpandATraceAttack::Rejection {
            row: MAX_CANDIDATES - 1,
            column: TRACE_COL_INDEX,
            value: 255,
        },
        ExpandATraceAttack::Rejection {
            row: done_row,
            column: TRACE_COL_SAMPLE,
            value: 1,
        },
        ExpandATraceAttack::Rejection {
            row: done_row,
            column: TRACE_COL_ACCEPT,
            value: 1,
        },
        ExpandATraceAttack::Rejection {
            row: done_row,
            column: TRACE_COL_INDEX,
            value: 255,
        },
        ExpandATraceAttack::Rejection {
            row: accept_row,
            column: TRACE_COL_ACCEPT_SLACK0,
            value: 256,
        },
        ExpandATraceAttack::Rejection {
            row: accept_row,
            column: TRACE_COL_ACCEPT_SLACK1,
            value: 256,
        },
        ExpandATraceAttack::Rejection {
            row: accept_row,
            column: TRACE_COL_ACCEPT_SLACK2,
            value: 128,
        },
        ExpandATraceAttack::Rejection {
            row: reject_row,
            column: TRACE_COL_REJECT_DELTA,
            value: 1 << 13,
        },
        ExpandATraceAttack::Rejection {
            row: accept_row,
            column: TRACE_COL_B0,
            value: 256,
        },
        ExpandATraceAttack::Rejection {
            row: accept_row,
            column: TRACE_COL_B1,
            value: 256,
        },
        ExpandATraceAttack::Rejection {
            row: accept_row,
            column: TRACE_COL_B2,
            value: 256,
        },
        ExpandATraceAttack::Preprocessed {
            component: ExpandAPreprocessedComponent::Rejection,
            row: accept_row,
            column: REJECTION_PRE_BYTE_POS,
            value: 1,
        },
        ExpandATraceAttack::Preprocessed {
            component: ExpandAPreprocessedComponent::Rejection,
            row: accept_row,
            column: REJECTION_PRE_STREAM,
            value: 16,
        },
    ];
    for attack in attacks {
        assert!(
            matches!(
                prove_core(rho, rho, Some(attack)),
                Err(ProvingError::ConstraintsNotSatisfied)
            ),
            "attack unexpectedly proved: {attack:?}"
        );
    }
}

/// Wave A deleted the witnessed `top` column and replaced it with the
/// `(b2-low7) ∈ {0,128}` gate (`top_gap * (top_gap - 128) == 0`, see
/// `expand_a::mod::RejectionEval::evaluate`). Bumping `b2` by one on an
/// active row (leaving `low7` untouched) keeps every other constraint
/// satisfied but moves `top_gap` off both {0,128}, so this must be caught
/// by that gate specifically -- not by an out-of-range byte value.
#[test]
fn rejection_air_rejects_stray_top_bit_gap() {
    let _guard = PROOF_LOCK.lock().unwrap();
    let rho = [42u8; 32];
    let (accept_row, _, _) = candidate_rows(&rho);
    let bytes = candidate_bytes(&rho, accept_row);
    let attack = ExpandATraceAttack::Rejection {
        row: accept_row,
        column: TRACE_COL_B2,
        value: u32::from(bytes[2]) + 1,
    };
    assert!(
        matches!(
            prove_core(rho, rho, Some(attack)),
            Err(ProvingError::ConstraintsNotSatisfied)
        ),
        "b2 off by one from low7 by neither 0 nor 128 must not prove"
    );
}

#[derive(Clone)]
struct ServiceProof {
    rho: [u8; 32],
    expand_claim: ExpandAClaim,
    range_claim: SecureField,
    service_claims: Vec<SecureField>,
    balancer_claims: Vec<SecureField>,
    payloads: Vec<Vec<u8>>,
    stark: StarkProof<air_core::Hasher>,
}

fn prove_with_service(rho: [u8; 32], service_rho: [u8; 32]) -> Result<ServiceProof, ProvingError> {
    let range_handle = SharedRangeRelation::new();
    let keccak_handle = SharedKeccakRelations::new();
    let bindings = ExpandABindings::new();
    let witness = derive_expand_a_witness(ML_DSA_65, rho).expect("canonical witness");
    let mut expand = ExpandAProver::new(
        ML_DSA_65,
        witness,
        NAMESPACE,
        STREAM_BASE,
        range_handle.clone(),
        keccak_handle.clone(),
        bindings.clone(),
    )
    .expect("validated ExpandA");
    let mut range = SharedRangeTable::prover(&[expand.range_uses().clone()], range_handle);
    let shapes = shake128_job_shapes(ML_DSA_65, STREAM_BASE).expect("valid ExpandA service shapes");
    let messages = shake128_absorb_streams(ML_DSA_65, &service_rho);
    let mut service = KeccakServiceProver::new(shapes, messages, keccak_handle.clone());
    let mut balancers = TestBalancers::new(&rho, &rho, false, keccak_handle, bindings);
    let (stark, payloads) = air_core::prove_with_post_interaction(
        &mut [&mut range, &mut service, &mut expand, &mut balancers],
        common::standalone_pcs_config(),
    )?;
    Ok(ServiceProof {
        rho,
        expand_claim: expand.claim(),
        range_claim: range.claimed_sum(),
        service_claims: service.claimed_sums(),
        balancer_claims: balancers.claimed_sums(),
        payloads,
        stark,
    })
}

fn expected_service_preprocessed_root() -> CommitmentRoot {
    *SERVICE_PREPROCESSED_ROOT.get_or_init(|| {
        let range_handle = SharedRangeRelation::new();
        let keccak_handle = SharedKeccakRelations::new();
        let bindings = ExpandABindings::new();
        let rho = [0u8; 32];
        let witness = derive_expand_a_witness(ML_DSA_65, rho).expect("canonical root witness");
        let mut expand = ExpandAProver::new(
            ML_DSA_65,
            witness,
            NAMESPACE,
            STREAM_BASE,
            range_handle.clone(),
            keccak_handle.clone(),
            bindings,
        )
        .expect("canonical root ExpandA");
        let mut range = SharedRangeTable::prover(&[expand.range_uses().clone()], range_handle);
        let shapes =
            shake128_job_shapes(ML_DSA_65, STREAM_BASE).expect("canonical root service shapes");
        let messages = shake128_absorb_streams(ML_DSA_65, &rho);
        let mut service = KeccakServiceProver::new(shapes, messages, keccak_handle);
        compute_preprocessed_root_uncached(
            &mut [&mut range, &mut service, &mut expand],
            common::standalone_pcs_config(),
        )
    })
}

fn verify_with_service(proof: &ServiceProof) -> Result<(), VerifyError> {
    verify_with_service_shapes(
        proof,
        shake128_job_shapes(ML_DSA_65, STREAM_BASE).expect("valid ExpandA service shapes"),
    )
}

fn verify_with_service_shapes(proof: &ServiceProof, shapes: Vec<Shape>) -> Result<(), VerifyError> {
    let range_handle = SharedRangeRelation::new();
    let keccak_handle = SharedKeccakRelations::new();
    let bindings = ExpandABindings::new();
    let mut range = SharedRangeTable::verifier(proof.range_claim, range_handle.clone());
    let mut service =
        KeccakServiceVerifier::new(shapes, proof.service_claims.clone(), keccak_handle.clone());
    let mut expand = ExpandAVerifier::new(
        ML_DSA_65,
        proof.expand_claim.clone(),
        NAMESPACE,
        STREAM_BASE,
        range_handle,
        keccak_handle.clone(),
        bindings.clone(),
    )
    .expect("valid ExpandA verifier configuration");
    let mut balancers = TestBalancers::new(&proof.rho, &proof.rho, false, keccak_handle, bindings)
        .with_claims(proof.balancer_claims.clone());
    air_core::verify_with_expected_preprocessed_root_and_payloads(
        &mut [&mut range, &mut service, &mut expand, &mut balancers],
        &proof.stark,
        Some(expected_service_preprocessed_root()),
        &proof.payloads,
    )
}

/// Slow manual release test:
/// `rtk cargo test --release -p stwo-mldsa --test expand_a six_block_expand_a_composes_with_real_keccak_service -- --ignored --exact`
#[test]
#[ignore = "real 180-permutation SHAKE-128 service integration"]
fn six_block_expand_a_composes_with_real_keccak_service() {
    let _guard = PROOF_LOCK.lock().unwrap();
    let rho = [77u8; 32];
    let proof = prove_with_service(rho, rho).expect("real service proof");
    verify_with_service(&proof).expect("real service verify");
    assert_eq!(proof.service_claims.len(), 12);
    let canonical =
        shake128_job_shapes(ML_DSA_65, STREAM_BASE).expect("valid canonical service shapes");
    let mut shape_attacks = Vec::new();
    for n_squeeze in [3, 5, 7] {
        let mut shapes = canonical.clone();
        shapes[0] = Shape::shake128(
            34,
            n_squeeze,
            shapes[0].absorb_stream_id,
            shapes[0].squeeze_stream_id,
        );
        shape_attacks.push((format!("{n_squeeze} squeeze blocks"), shapes));
    }
    let mut shapes = canonical.clone();
    shapes.pop();
    shape_attacks.push(("29 jobs".to_owned(), shapes));
    let mut shapes = canonical.clone();
    shapes.push(Shape::shake128(
        34,
        6,
        STREAM_BASE + 1_000,
        STREAM_BASE + 1_001,
    ));
    shape_attacks.push(("31 jobs".to_owned(), shapes));
    let mut shapes = canonical.clone();
    shapes.swap(0, 1);
    shape_attacks.push(("wrong job order".to_owned(), shapes));
    let mut shapes = canonical.clone();
    shapes[0] = Shape::new(
        34,
        6,
        shapes[0].absorb_stream_id,
        shapes[0].squeeze_stream_id,
    );
    shape_attacks.push(("wrong XOF mode".to_owned(), shapes));
    let mut shapes = canonical.clone();
    shapes[0] = Shape::shake128(
        33,
        6,
        shapes[0].absorb_stream_id,
        shapes[0].squeeze_stream_id,
    );
    shape_attacks.push(("wrong message length".to_owned(), shapes));
    let mut shapes = canonical;
    shapes[0] = Shape::shake128(
        34,
        6,
        shapes[0].absorb_stream_id + 128,
        shapes[0].squeeze_stream_id + 128,
    );
    shape_attacks.push(("wrong stream ids".to_owned(), shapes));
    let mut shapes =
        shake128_job_shapes(ML_DSA_65, STREAM_BASE).expect("valid canonical service shapes");
    shapes[0] = Shape::shake128(
        34,
        6,
        shapes[0].absorb_stream_id + 128,
        shapes[0].squeeze_stream_id,
    );
    shape_attacks.push(("wrong absorb stream id".to_owned(), shapes));
    let mut shapes =
        shake128_job_shapes(ML_DSA_65, STREAM_BASE).expect("valid canonical service shapes");
    shapes[0] = Shape::shake128(
        34,
        6,
        shapes[0].absorb_stream_id,
        shapes[0].squeeze_stream_id + 128,
    );
    shape_attacks.push(("wrong squeeze stream id".to_owned(), shapes));
    for (name, shapes) in shape_attacks {
        assert!(
            verify_with_service_shapes(&proof, shapes).is_err(),
            "{name} accepted a canonical six-block proof"
        );
    }

    for claim_index in [0, 2, 11] {
        let mut tampered = proof.clone();
        tampered.service_claims[claim_index] += SecureField::one();
        assert!(
            verify_with_service(&tampered).is_err(),
            "forged service claim {claim_index} accepted"
        );
    }
    for claim_index in 0..proof.balancer_claims.len() {
        let mut tampered = proof.clone();
        tampered.balancer_claims[claim_index] += SecureField::one();
        assert!(
            verify_with_service(&tampered).is_err(),
            "forged real-service counterpart claim {claim_index} accepted"
        );
    }
    drop(proof);

    let forged = prove_with_service([99u8; 32], rho).expect("locally self-consistent forged proof");
    assert!(
        verify_with_service(&forged).is_err(),
        "the Keccak HashIo relation must reject a disconnected forged A_hat"
    );
}

#[test]
fn proof_shape_constants_are_fixed() {
    assert_eq!(REJECTION_BASE_COLS, 13);
    let shapes = shake128_job_shapes(ML_DSA_65, STREAM_BASE).expect("valid ExpandA service shapes");
    assert_eq!(shapes.len(), 30);
    assert!(shapes
        .iter()
        .all(|shape| shape.n_squeeze == 6 && shape.n_perms() == 6));
}
