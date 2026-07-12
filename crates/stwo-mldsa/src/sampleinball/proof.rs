//! Standalone prove/verify for `sampleinball_fsm` via `air-core` (mirrors
//! `crate::decomp::proof`). Contributes, in commit order:
//!   1. `sib`             — the [CHAL] FSM + ternary/τ + c-binding component.
//!   2. rc providers       — rc8, rc9 (one each).
//!   3. `ccell_provider`   — TEST-SIDE balancer yielding the coeffs C-cell
//!      `(c_bind_id, c)` tuples the FSM consumes (M6 uses the real coeffs C group).
//!   4. `hashio_producer`  — TEST-SIDE balancer yielding the squeeze bytes the FSM
//!      consumes (M6 uses the proven sponge squeeze).

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

use crate::air_util::{padded_log_size, ColEval};
use crate::balancer::{
    gen_balancer_interaction, gen_balancer_trace, BalancerEval, BalancerRelation,
    BALANCER_INTERACTION_COLS,
};
use crate::binding::{CCELL_ARITY, HASH_IO_ARITY, STREAM_ID_SIB_SQUEEZE};
use crate::constants::N;
use crate::witness::MlDsaWitness;

use super::relations::{RcRelation, SibRelations};
use super::tables::{
    gen_table_interaction, gen_table_multiplicities, gen_table_preprocessed, RcKind, RcTableEval,
    RC_TABLE_INTERACTION_COLS,
};
use super::{
    gen_sib_base_trace, gen_sib_interaction, gen_sib_preprocessed, sib_preprocessed_ids, SibEval,
    N_ACCESSES, N_BASE_COLS, N_INTERACTION_COLS,
};

const N_RC: usize = 3;

pub struct SibProof {
    pub sib_claimed_sum: SecureField,
    pub rc_claimed_sums: [SecureField; N_RC],
    pub ccell_claimed_sum: SecureField,
    pub hashio_claimed_sum: SecureField,
    pub log_size: u32,
    pub ccell_log_size: u32,
    pub hashio_log_size: u32,
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
}

fn sib_log_size(witness: &MlDsaWitness) -> u32 {
    // Cover the stream+c stages AND the offline-memory sorted view (N_ACCESSES).
    padded_log_size((witness.sponge.sample_in_ball_squeezed.len() + N).max(N_ACCESSES))
}
fn ccell_log_size() -> u32 {
    padded_log_size(N)
}
fn hashio_log_size(witness: &MlDsaWitness) -> u32 {
    padded_log_size(witness.sponge.sample_in_ball_squeezed.len())
}

fn all_preprocessed_ids() -> Vec<PreProcessedColumnId> {
    let mut ids = sib_preprocessed_ids();
    for kind in RcKind::ALL {
        ids.push(kind.value_column_id());
    }
    ids
}

fn all_preprocessed_log_sizes(log_size: u32) -> Vec<u32> {
    let mut sizes = vec![log_size; sib_preprocessed_ids().len()];
    for kind in RcKind::ALL {
        sizes.push(kind.log_size());
    }
    sizes
}

fn gen_all_preprocessed(witness: &MlDsaWitness, log_size: u32) -> Vec<ColEval> {
    let mut cols = gen_sib_preprocessed(witness, log_size);
    for kind in RcKind::ALL {
        cols.push(gen_table_preprocessed(kind));
    }
    cols
}

fn ccell_tuples(witness: &MlDsaWitness) -> Vec<Vec<u32>> {
    (0..N)
        .map(|m| vec![m as u32, enc(witness.digits.c[m])])
        .collect()
}

fn hashio_tuples(bytes: &[u8]) -> Vec<Vec<u32>> {
    bytes
        .iter()
        .enumerate()
        .map(|(pos, &b)| vec![STREAM_ID_SIB_SQUEEZE, pos as u32, b as u32])
        .collect()
}

fn enc(v: i128) -> u32 {
    const P: i128 = (1 << 31) - 1;
    (((v % P) + P) % P) as u32
}

struct Built {
    sib: FrameworkComponent<SibEval>,
    rc: Vec<FrameworkComponent<RcTableEval>>,
    ccell: FrameworkComponent<BalancerEval>,
    hashio: FrameworkComponent<BalancerEval>,
}

impl Built {
    fn as_components(&self) -> Vec<&dyn Component> {
        let mut out: Vec<&dyn Component> = vec![&self.sib];
        out.extend(self.rc.iter().map(|c| c as &dyn Component));
        out.push(&self.ccell);
        out.push(&self.hashio);
        out
    }
    fn as_prover(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        let mut out: Vec<&dyn ComponentProver<SimdBackend>> = vec![&self.sib];
        out.extend(
            self.rc
                .iter()
                .map(|c| c as &dyn ComponentProver<SimdBackend>),
        );
        out.push(&self.ccell);
        out.push(&self.hashio);
        out
    }
}

fn rc_relation(r: &SibRelations, kind: RcKind) -> &RcRelation {
    match kind {
        RcKind::Rc8 => &r.rc8,
        RcKind::Rc9 => &r.rc9,
        RcKind::Rc11 => &r.rc11,
    }
}

pub struct SibProver {
    witness: MlDsaWitness,
    relations: Option<SibRelations>,
    sib_claimed_sum: SecureField,
    rc_claimed_sums: [SecureField; N_RC],
    ccell_claimed_sum: SecureField,
    hashio_claimed_sum: SecureField,
    rc_mult: Vec<ColEval>,
    stream_bytes: Vec<u8>,
    built: Option<Built>,
}

struct SibVerifier {
    witness_log_size: u32,
    hashio_log_size: u32,
    sib_claimed_sum: SecureField,
    rc_claimed_sums: [SecureField; N_RC],
    ccell_claimed_sum: SecureField,
    hashio_claimed_sum: SecureField,
    relations: Option<SibRelations>,
    // The verifier reproduces preprocessed shapes from the same public stream
    // length; here we store the witness-derived c/stream tuples via the proof.
    ccell_tuples: Vec<Vec<u32>>,
    hashio_tuples: Vec<Vec<u32>>,
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
    rc_claimed_sums: &[SecureField; N_RC],
    ccell_claimed_sum: SecureField,
    hashio_claimed_sum: SecureField,
) -> Built {
    let sib = FrameworkComponent::new(
        allocator,
        SibEval {
            log_size,
            ns: String::new(),
            sib_stream: STREAM_ID_SIB_SQUEEZE,
            relations: relations.clone(),
        },
        sib_claimed_sum,
    );
    let mut rc = Vec::with_capacity(N_RC);
    for (idx, kind) in RcKind::ALL.iter().enumerate() {
        rc.push(FrameworkComponent::new(
            allocator,
            RcTableEval {
                kind: *kind,
                relation: rc_relation(relations, *kind).clone(),
            },
            rc_claimed_sums[idx],
        ));
    }
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
        rc,
        ccell,
        hashio,
    }
}

fn module_trace_layout(log_size: u32, ccell_ls: u32, hashio_ls: u32) -> Vec<u32> {
    let mut trace = vec![log_size; N_BASE_COLS];
    for kind in RcKind::ALL {
        trace.push(kind.log_size());
    }
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
    for kind in RcKind::ALL {
        for _ in 0..RC_TABLE_INTERACTION_COLS {
            inter.push(kind.log_size());
        }
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
        let ls = sib_log_size(&self.witness);
        TreeLayout {
            preprocessed: all_preprocessed_log_sizes(ls),
            trace: module_trace_layout(ls, ccell_log_size(), hashio_log_size(&self.witness)),
            interaction: module_interaction_layout(
                ls,
                ccell_log_size(),
                hashio_log_size(&self.witness),
            ),
        }
    }
    fn claimed_sums(&self) -> Vec<SecureField> {
        let mut s = vec![self.sib_claimed_sum];
        s.extend(self.rc_claimed_sums);
        s.push(self.ccell_claimed_sum);
        s.push(self.hashio_claimed_sum);
        s
    }
    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        all_preprocessed_ids()
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.built = Some(build_components(
            allocator,
            sib_log_size(&self.witness),
            ccell_log_size(),
            hashio_log_size(&self.witness),
            self.relations.as_ref().expect("relations"),
            self.sib_claimed_sum,
            &self.rc_claimed_sums,
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
        sib_log_size(&self.witness)
            .max(RcKind::Rc9.log_size())
            .max(ccell_log_size())
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.max_log_size() + 1
    }
    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(gen_all_preprocessed(
            &self.witness,
            sib_log_size(&self.witness),
        ));
    }
    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        let ls = sib_log_size(&self.witness);
        fingerprint_preprocessed_columns(
            "mldsa_sib",
            &all_preprocessed_ids(),
            &gen_all_preprocessed(&self.witness, ls),
        )
    }
    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let ls = sib_log_size(&self.witness);
        let mut evals = gen_sib_base_trace(&self.witness, ls);
        let dry = gen_sib_interaction(
            &self.witness,
            ls,
            STREAM_ID_SIB_SQUEEZE,
            &SibRelations::dummy(),
        );
        self.stream_bytes = dry.stream_bytes.clone();
        self.rc_mult = RcKind::ALL
            .iter()
            .map(|kind| gen_table_multiplicities(*kind, dry.rc_uses.for_kind(*kind)))
            .collect();
        evals.extend(self.rc_mult.clone());
        evals.extend(gen_balancer_trace(
            ccell_log_size(),
            &ccell_tuples(&self.witness),
        ));
        evals.extend(gen_balancer_trace(
            hashio_log_size(&self.witness),
            &hashio_tuples(&self.stream_bytes),
        ));
        tb.extend_evals(evals);
    }
    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let ls = sib_log_size(&self.witness);
        let relations = self.relations.clone().expect("relations");
        let interaction = gen_sib_interaction(&self.witness, ls, STREAM_ID_SIB_SQUEEZE, &relations);
        let mut evals = interaction.trace;
        self.sib_claimed_sum = interaction.claimed_sum;

        for (idx, kind) in RcKind::ALL.iter().enumerate() {
            let (tr, sum) =
                gen_table_interaction(*kind, &self.rc_mult[idx], rc_relation(&relations, *kind));
            evals.extend(tr);
            self.rc_claimed_sums[idx] = sum;
        }
        let (ctr, csum) = gen_balancer_interaction(
            ccell_log_size(),
            &ccell_tuples(&self.witness),
            &BalancerRelation::CCell(relations.ccell.clone()),
            false,
        );
        self.ccell_claimed_sum = csum;
        evals.extend(ctr);
        let (htr, hsum) = gen_balancer_interaction(
            hashio_log_size(&self.witness),
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
        let mut s = vec![self.sib_claimed_sum];
        s.extend(self.rc_claimed_sums);
        s.push(self.ccell_claimed_sum);
        s.push(self.hashio_claimed_sum);
        s
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
            &self.rc_claimed_sums,
            self.ccell_claimed_sum,
            self.hashio_claimed_sum,
        ));
    }
    fn components(&self) -> Vec<&dyn Component> {
        self.built.as_ref().expect("built").as_components()
    }
}

pub fn prove_sib(witness: MlDsaWitness, config: PcsConfig) -> Result<SibProof, ProvingError> {
    let log_size = sib_log_size(&witness);
    let hio_ls = hashio_log_size(&witness);
    let mut prover = SibProver {
        witness,
        relations: None,
        sib_claimed_sum: SecureField::zero(),
        rc_claimed_sums: [SecureField::zero(); N_RC],
        ccell_claimed_sum: SecureField::zero(),
        hashio_claimed_sum: SecureField::zero(),
        rc_mult: Vec::new(),
        stream_bytes: Vec::new(),
        built: None,
    };
    let stark_proof = air_core::prove(&mut [&mut prover], config)?;
    Ok(SibProof {
        sib_claimed_sum: prover.sib_claimed_sum,
        rc_claimed_sums: prover.rc_claimed_sums,
        ccell_claimed_sum: prover.ccell_claimed_sum,
        hashio_claimed_sum: prover.hashio_claimed_sum,
        log_size,
        ccell_log_size: ccell_log_size(),
        hashio_log_size: hio_ls,
        stark_proof,
    })
}

pub fn verify_sib(proof: &SibProof, witness: &MlDsaWitness) -> Result<(), VerificationError> {
    let mut verifier = SibVerifier {
        witness_log_size: proof.log_size,
        hashio_log_size: proof.hashio_log_size,
        sib_claimed_sum: proof.sib_claimed_sum,
        rc_claimed_sums: proof.rc_claimed_sums,
        ccell_claimed_sum: proof.ccell_claimed_sum,
        hashio_claimed_sum: proof.hashio_claimed_sum,
        relations: None,
        ccell_tuples: ccell_tuples(witness),
        hashio_tuples: hashio_tuples(&witness.sponge.sample_in_ball_squeezed),
        built: None,
    };
    let _ = (&verifier.ccell_tuples, &verifier.hashio_tuples);
    air_core::verify(&mut [&mut verifier], &proof.stark_proof)
}
