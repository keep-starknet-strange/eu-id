//! Standalone prove/verify for a single SHAKE-256 hash, wiring every component
//! through the `air-core` orchestrator.
//!
//! Component order (identical in every `Air`/`AirProver` method — the
//! orchestrator concatenates layouts, claimed sums, and components positionally,
//! so any drift breaks verification):
//!
//! 1. `sponge`            — absorb/pad/squeeze; requests permutations, HashIo.
//! 2. `io_provider`       — closes HashIo against the public message/output.
//! 3. `keccak`            — one permutation per row; KeccakState + KeccakRound.
//! 4. `keccak_round`      — one round per row; spread xor3/andnot/split lookups.
//! 5. nine table providers — dense (xor3+andnot), conv, split_1..split_7.

use num_traits::Zero;
use serde::{Deserialize, Serialize};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo::core::verifier::VerificationError;
use stwo::prover::backend::simd::m31::PackedM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::{ComponentProver, ProvingError, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{FrameworkComponent, TraceLocationAllocator};

use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, CommitmentRoot, PreprocessedColumnFingerprint,
    TreeLayout,
};

use crate::constants::N_BYTES_IN_STATE;
use crate::keccak;
use crate::keccak_round;
use crate::relations::KeccakRelations;
use crate::sponge::{self, io_provider, Shape};
use crate::tables_air::{self, TableKind, TableMultiplicities};

/// A self-contained SHAKE-256 proof.
#[derive(Serialize, Deserialize)]
pub struct KeccakProof {
    pub shape: Shape,
    pub message: Vec<u8>,
    pub output: Vec<u8>,
    pub sponge_claim: sponge::Claim,
    pub keccak_claim: keccak::Claim,
    pub round_claim: keccak_round::Claim,
    pub sponge_ic: sponge::InteractionClaim,
    pub io_ic: io_provider::InteractionClaim,
    pub keccak_ic: keccak::InteractionClaim,
    pub round_ic: keccak_round::InteractionClaim,
    pub tables_ic: tables_air::InteractionClaim,
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
}

/// The witness the prover carries between air-core phases.
struct KeccakWitness {
    message: Vec<u8>,
    output: Vec<u8>,
    shape: Shape,
    // Traces built up front (phase 1).
    sponge_run: sponge::SpongeRun,
    keccak_data: keccak::InteractionClaimData,
    keccak_claim: keccak::Claim,
    keccak_trace: Vec<TraceCol>,
    round_data: keccak_round::InteractionClaimData,
    round_claim: keccak_round::Claim,
    round_trace: Vec<TraceCol>,
    table_mult: TableMultiplicities,
    io_data: io_provider::Data,
}

pub type TraceCol = stwo::prover::poly::circle::CircleEvaluation<
    SimdBackend,
    stwo::core::fields::m31::BaseField,
    stwo::prover::poly::BitReversedOrder,
>;

/// The keccak + keccak_round witness for a set of permutation requests, plus
/// the round-derived table multiplicities. Shared by the standalone SHAKE proof
/// and downstream compositions (stwo-mldsa's three-chain statement) so the
/// perm-packing / round-expansion logic has one source of truth.
pub struct PermWitness {
    pub keccak_claim: keccak::Claim,
    pub keccak_trace: Vec<TraceCol>,
    pub keccak_data: keccak::InteractionClaimData,
    pub round_claim: keccak_round::Claim,
    pub round_trace: Vec<TraceCol>,
    pub round_data: keccak_round::InteractionClaimData,
    pub table_mult: TableMultiplicities,
}

/// Build the keccak permutation prover + round prover traces for `perm_inputs`
/// (concatenated across any number of sponge instances; each row is a splatted
/// `[state|perm_id]` with lane 0 real). Table multiplicities cover the round
/// lookups; callers add each sponge's xor/conv uses via
/// [`TableMultiplicities::add_sponge`].
pub fn build_perm_witness(perm_inputs: &[[PackedM31; N_BYTES_IN_STATE + 1]]) -> PermWitness {
    // keccak boundary rows from the sponge's requests (25 rows per perm; the
    // rotated wrapper consumes the splatted per-perm rows directly).
    let (keccak_claim, keccak_trace, keccak_data) = keccak::Claim::generate_trace(perm_inputs);

    // keccak_round rows: expand each permutation into 24 round rows
    // `[state(200) | round_index]`.
    // Each keccak permutation is committed on lane 0 only (the sponge splats a
    // single logical instance; keccak's enabler is active on lane 0). So the
    // round component must supply exactly `n_perms * 24` round instances, one
    // per (perm, round). We collect them as per-lane `(state, round_idx)` pairs
    // and pack `N_LANES` distinct instances into each vec-row — the round
    // trace's `fill_row` reads the round index per lane, so lanes may hold
    // different rounds.
    let mut round_instances: Vec<([u8; N_BYTES_IN_STATE], u32)> = Vec::new();
    for prow in perm_inputs {
        // lane 0 holds the real perm input state, in spread form; unspread it to
        // bytes for the native per-round advance.
        let mut state = [0u8; N_BYTES_IN_STATE];
        for i in 0..N_BYTES_IN_STATE {
            state[i] = crate::utils::unspread_u32(prow[i].to_array()[0].0) as u8;
        }
        for round in 0..crate::constants::N_ROUNDS {
            round_instances.push((state, round as u32));
            let mut sp: [PackedM31; N_BYTES_IN_STATE] =
                std::array::from_fn(|i| PackedM31::from(stwo::core::fields::m31::M31::from(state[i] as u32)));
            crate::utils::keccak_f1600_round(&mut sp, round);
            for i in 0..N_BYTES_IN_STATE {
                state[i] = sp[i].to_array()[0].0 as u8;
            }
        }
    }
    let n_rounds = round_instances.len();
    let round_inputs = pack_round_instances(&round_instances);
    let (round_claim, round_ct, round_data) =
        keccak_round::Claim::generate_trace(round_inputs, n_rounds);

    let table_mult = TableMultiplicities::from_round(&round_data);

    PermWitness {
        keccak_claim,
        keccak_trace,
        keccak_data,
        round_claim,
        round_trace: round_ct.to_evals().into_iter().collect(),
        round_data,
        table_mult,
    }
}

/// Build every trace once, before the air-core phases run.
fn build_witness(message: &[u8], n_squeeze: usize) -> KeccakWitness {
    const ABSORB_STREAM: u32 = 0;
    const SQUEEZE_STREAM: u32 = 1;

    let sponge_run = sponge::generate_trace(message, n_squeeze, ABSORB_STREAM, SQUEEZE_STREAM, 0);
    let shape = sponge_run.claim.shape;
    let output = sponge_run.output.clone();

    let perm = build_perm_witness(&sponge_run.perm_inputs);
    let mut table_mult = perm.table_mult;
    table_mult.add_sponge(&sponge_run.data.xor, &sponge_run.data.conv);
    let io_data = io_provider::build_data(message, &output, shape);

    KeccakWitness {
        message: message.to_vec(),
        output,
        shape,
        sponge_run,
        keccak_data: perm.keccak_data,
        keccak_claim: perm.keccak_claim,
        keccak_trace: perm.keccak_trace,
        round_data: perm.round_data,
        round_claim: perm.round_claim,
        round_trace: perm.round_trace,
        table_mult,
        io_data,
    }
}

/// Pack per-lane `(state, round_idx)` instances into `[state|round]` vec-rows,
/// `N_LANES` distinct instances per row (padding the last row with zeros).
fn pack_round_instances(
    instances: &[([u8; N_BYTES_IN_STATE], u32)],
) -> Vec<[PackedM31; N_BYTES_IN_STATE + 1]> {
    use stwo::core::fields::m31::M31;
    use stwo::prover::backend::simd::m31::N_LANES;
    let n_vec_rows = instances.len().div_ceil(N_LANES);
    let mut rows = Vec::with_capacity(n_vec_rows);
    for vr in 0..n_vec_rows {
        let mut row = [PackedM31::zero(); N_BYTES_IN_STATE + 1];
        let mut state_lanes = [[M31::from(0u32); N_LANES]; N_BYTES_IN_STATE];
        let mut round_lanes = [M31::from(0u32); N_LANES];
        for lane in 0..N_LANES {
            let idx = vr * N_LANES + lane;
            if idx >= instances.len() {
                break;
            }
            let (state, round) = &instances[idx];
            for i in 0..N_BYTES_IN_STATE {
                // The round component consumes state limbs in *spread* form.
                state_lanes[i][lane] = M31::from(crate::utils::spread_u32(state[i] as u32));
            }
            round_lanes[lane] = M31::from(*round);
        }
        for i in 0..N_BYTES_IN_STATE {
            row[i] = PackedM31::from_array(state_lanes[i]);
        }
        row[N_BYTES_IN_STATE] = PackedM31::from_array(round_lanes);
        rows.push(row);
    }
    rows
}

pub struct KeccakProver {
    witness: KeccakWitness,
    relations: Option<KeccakRelations>,
    ic: Option<InteractionClaims>,
    components: Option<Components>,
}

pub struct KeccakVerifier {
    shape: Shape,
    message: Vec<u8>,
    output: Vec<u8>,
    ic: InteractionClaims,
    relations: Option<KeccakRelations>,
    components: Option<Components>,
}

#[derive(Clone)]
struct InteractionClaims {
    sponge: sponge::InteractionClaim,
    io: io_provider::InteractionClaim,
    keccak: keccak::InteractionClaim,
    round: keccak_round::InteractionClaim,
    tables: tables_air::InteractionClaim,
}

impl InteractionClaims {
    fn claimed_sums(&self) -> Vec<QM31> {
        let mut out = vec![
            self.sponge.claimed_sum,
            self.io.claimed_sum,
            self.keccak.claimed_sum,
            self.round.claimed_sum,
        ];
        out.extend(self.tables.claimed_sums.iter().copied());
        out
    }
}

impl KeccakProver {
    fn ic(&self) -> &InteractionClaims {
        self.ic.as_ref().expect("interaction claims set during proving")
    }
    fn relations(&self) -> &KeccakRelations {
        self.relations.as_ref().expect("relations drawn before use")
    }
    fn built(&self) -> &Components {
        self.components.as_ref().expect("components built before use")
    }
}

impl KeccakVerifier {
    fn relations(&self) -> &KeccakRelations {
        self.relations.as_ref().expect("relations drawn before use")
    }
    fn built(&self) -> &Components {
        self.components.as_ref().expect("components built before use")
    }
}

fn mix_public_common(
    channel: &mut Blake2sChannel,
    shape: &Shape,
    message: &[u8],
    output: &[u8],
) {
    channel.mix_u64(shape.message_len as u64);
    channel.mix_u64(shape.n_squeeze as u64);
    channel.mix_u64(shape.absorb_stream_id as u64);
    channel.mix_u64(shape.squeeze_stream_id as u64);
    for &b in message {
        channel.mix_u64(b as u64);
    }
    for &b in output {
        channel.mix_u64(b as u64);
    }
}

fn preprocessed_ids(n_perms: usize) -> Vec<PreProcessedColumnId> {
    let mut ids = keccak::schedule_ids(n_perms);
    ids.extend(tables_air::all_preprocessed_column_ids());
    ids
}

fn preprocessed_layout(keccak_claim: &keccak::Claim) -> Vec<u32> {
    let mut sizes = vec![keccak_claim.log_size(); keccak::N_SCHEDULE_COLS];
    sizes.extend(tables_air::all_preprocessed_log_sizes());
    sizes
}

fn gen_preprocessed(n_perms: usize) -> Vec<TraceCol> {
    let mut cols = keccak::gen_schedule_preprocessed(n_perms);
    cols.extend(tables_air::generate_preprocessed_trace());
    cols
}

impl Air for KeccakProver {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        mix_public_common(channel, &self.witness.shape, &self.witness.message, &self.witness.output);
    }
    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.relations = Some(KeccakRelations::draw(channel));
    }
    fn layout(&self) -> TreeLayout {
        layout_for(&self.witness.shape, &self.witness.keccak_claim, &self.witness.round_claim, &self.witness.message, &self.witness.output)
    }
    fn claimed_sums(&self) -> Vec<QM31> {
        self.ic().claimed_sums()
    }
    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_ids(self.witness.shape.n_perms())
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(Components::new(
            allocator,
            self.relations().clone(),
            &self.witness.sponge_run.claim,
            &self.witness.keccak_claim,
            &self.witness.round_claim,
            &self.witness.message,
            &self.witness.output,
            self.ic(),
        ));
    }
    fn components(&self) -> Vec<&dyn Component> {
        self.built().as_components()
    }
}

impl AirProver for KeccakProver {
    fn max_log_size(&self) -> u32 {
        // The largest committed domain across all components — the 2^16 byte-pair
        // tables dominate for small messages, but the round/keccak components can
        // exceed them for long inputs. Twiddles must cover the max.
        self.witness
            .round_claim
            .log_size
            .max(self.witness.keccak_claim.log_size())
            .max(tables_air::TableKind::Dense.log_size())
    }
    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        tb.extend_evals(gen_preprocessed(self.witness.shape.n_perms()));
    }
    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        let n_perms = self.witness.shape.n_perms();
        fingerprint_preprocessed_columns(
            "stwo_keccak::KeccakProver",
            &preprocessed_ids(n_perms),
            &gen_preprocessed(n_perms),
        )
    }
    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let mut evals = Vec::new();
        evals.extend(std::mem::take(&mut self.witness.sponge_run.trace));
        evals.extend(io_provider::trace());
        evals.extend(std::mem::take(&mut self.witness.keccak_trace));
        evals.extend(std::mem::take(&mut self.witness.round_trace));
        evals.extend(tables_air::generate_trace(&self.witness.table_mult));
        tb.extend_evals(evals);
    }
    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let rel = self.relations().clone();
        let mut evals = Vec::new();

        let (sponge_ic, sponge_tr) = sponge::generate_interaction_trace(&rel, &self.witness.sponge_run.data);
        evals.extend(sponge_tr);
        let (io_ic, io_tr) = io_provider::generate_interaction_trace(&rel, &self.witness.io_data);
        evals.extend(io_tr);
        let (keccak_ic, keccak_tr) = keccak::generate_interaction_trace(&rel, &self.witness.keccak_data);
        evals.extend(keccak_tr);
        let (round_ic, round_tr) = keccak_round::generate_interaction_trace(&rel, &self.witness.round_data);
        evals.extend(round_tr);
        let (tables_ic, tables_tr) = tables_air::generate_interaction_trace(&rel, &self.witness.table_mult);
        evals.extend(tables_tr);

        tb.extend_evals(evals);
        self.ic = Some(InteractionClaims {
            sponge: sponge_ic,
            io: io_ic,
            keccak: keccak_ic,
            round: round_ic,
            tables: tables_ic,
        });
    }
    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        self.built().as_prover_components()
    }
}

impl Air for KeccakVerifier {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        mix_public_common(channel, &self.shape, &self.message, &self.output);
    }
    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.relations = Some(KeccakRelations::draw(channel));
    }
    fn layout(&self) -> TreeLayout {
        let keccak_claim = keccak::Claim { n_perms: self.shape.n_perms() };
        let round_claim = keccak_round::Claim { log_size: round_log_size(&self.shape) };
        layout_for(&self.shape, &keccak_claim, &round_claim, &self.message, &self.output)
    }
    fn claimed_sums(&self) -> Vec<QM31> {
        self.ic.claimed_sums()
    }
    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_ids(self.shape.n_perms())
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let sponge_claim = sponge::Claim {
            log_size: stwo::prover::backend::simd::m31::LOG_N_LANES,
            shape: self.shape,
        };
        let keccak_claim = keccak::Claim { n_perms: self.shape.n_perms() };
        let round_claim = keccak_round::Claim { log_size: round_log_size(&self.shape) };
        self.components = Some(Components::new(
            allocator,
            self.relations().clone(),
            &sponge_claim,
            &keccak_claim,
            &round_claim,
            &self.message,
            &self.output,
            &self.ic,
        ));
    }
    fn components(&self) -> Vec<&dyn Component> {
        self.built().as_components()
    }
}

fn round_log_size(shape: &Shape) -> u32 {
    let n = shape.n_perms() * crate::constants::N_ROUNDS;
    std::cmp::max((n as u32).next_power_of_two().ilog2(), stwo::prover::backend::simd::m31::LOG_N_LANES)
}

fn layout_for(
    shape: &Shape,
    keccak_claim: &keccak::Claim,
    round_claim: &keccak_round::Claim,
    message: &[u8],
    output: &[u8],
) -> TreeLayout {
    let sponge_claim = sponge::Claim {
        log_size: stwo::prover::backend::simd::m31::LOG_N_LANES,
        shape: *shape,
    };
    let io_claim = io_provider::Claim {
        log_size: stwo::prover::backend::simd::m31::LOG_N_LANES,
        shape: *shape,
    };
    let _ = (message, output);

    let mut trace = Vec::new();
    trace.extend(sponge_claim.log_sizes()[1].clone());
    trace.extend(io_claim.log_sizes()[1].clone());
    trace.extend(keccak_claim.log_sizes()[1].clone());
    trace.extend(round_claim.log_sizes()[1].clone());
    // One multiplicity column per relation (Dense has two: xor3 + andnot).
    for kind in TableKind::ALL {
        for _ in 0..kind.n_relations() {
            trace.push(kind.log_size());
        }
    }

    let mut interaction = Vec::new();
    interaction.extend(sponge_claim.log_sizes()[2].clone());
    interaction.extend(io_claim.log_sizes()[2].clone());
    interaction.extend(keccak_claim.log_sizes()[2].clone());
    interaction.extend(round_claim.log_sizes()[2].clone());
    // tables: one paired column per table => SECURE_EXTENSION_DEGREE cols each.
    for kind in TableKind::ALL {
        for _ in 0..stwo::core::fields::qm31::SECURE_EXTENSION_DEGREE {
            interaction.push(kind.log_size());
        }
    }

    TreeLayout {
        preprocessed: preprocessed_layout(keccak_claim),
        trace,
        interaction,
    }
}

// ── Component holder ──

struct Components {
    sponge: sponge::Component,
    io: io_provider::Component,
    keccak: keccak::Component,
    round: keccak_round::Component,
    tables: Vec<tables_air::Component>,
}

impl Components {
    #[allow(clippy::too_many_arguments)]
    fn new(
        allocator: &mut TraceLocationAllocator,
        relations: KeccakRelations,
        sponge_claim: &sponge::Claim,
        keccak_claim: &keccak::Claim,
        round_claim: &keccak_round::Claim,
        message: &[u8],
        output: &[u8],
        ic: &InteractionClaims,
    ) -> Self {
        let sponge = FrameworkComponent::new(
            allocator,
            sponge::Eval { claim: sponge_claim.clone(), relations: relations.clone() },
            ic.sponge.claimed_sum,
        );
        let io = FrameworkComponent::new(
            allocator,
            io_provider::Eval {
                log_size: stwo::prover::backend::simd::m31::LOG_N_LANES,
                shape: sponge_claim.shape,
                message: message.to_vec(),
                output: output.to_vec(),
                relations: relations.clone(),
            },
            ic.io.claimed_sum,
        );
        let keccak = FrameworkComponent::new(
            allocator,
            keccak::Eval { claim: *keccak_claim, relations: relations.clone() },
            ic.keccak.claimed_sum,
        );
        let round = FrameworkComponent::new(
            allocator,
            keccak_round::Eval { claim: *round_claim, relations: relations.clone() },
            ic.round.claimed_sum,
        );
        let mut tables = Vec::with_capacity(TableKind::ALL.len());
        for (i, kind) in TableKind::ALL.iter().enumerate() {
            tables.push(FrameworkComponent::new(
                allocator,
                tables_air::Eval {
                    log_size: kind.log_size(),
                    kind: *kind,
                    relations: relations.clone(),
                },
                ic.tables.claimed_sums[i],
            ));
        }
        Self { sponge, io, keccak, round, tables }
    }

    fn as_components(&self) -> Vec<&dyn Component> {
        let mut out: Vec<&dyn Component> = vec![&self.sponge, &self.io, &self.keccak, &self.round];
        out.extend(self.tables.iter().map(|c| c as &dyn Component));
        out
    }
    fn as_prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        let mut out: Vec<&dyn ComponentProver<SimdBackend>> =
            vec![&self.sponge, &self.io, &self.keccak, &self.round];
        out.extend(self.tables.iter().map(|c| c as &dyn ComponentProver<SimdBackend>));
        out
    }
}

// ── Top-level entry points ──

pub fn prove_shake256(
    message: &[u8],
    n_squeeze: usize,
    config: PcsConfig,
) -> Result<KeccakProof, ProvingError> {
    let witness = build_witness(message, n_squeeze);
    let shape = witness.shape;
    let sponge_claim = witness.sponge_run.claim.clone();
    let keccak_claim = witness.keccak_claim;
    let round_claim = witness.round_claim;
    let msg = witness.message.clone();
    let output = witness.output.clone();

    let mut prover = KeccakProver {
        witness,
        relations: None,
        ic: None,
        components: None,
    };
    let stark_proof = air_core::prove(&mut [&mut prover], config)?;
    let ic = prover.ic().clone();

    Ok(KeccakProof {
        shape,
        message: msg,
        output,
        sponge_claim,
        keccak_claim,
        round_claim,
        sponge_ic: ic.sponge,
        io_ic: ic.io,
        keccak_ic: ic.keccak,
        round_ic: ic.round,
        tables_ic: ic.tables,
        stark_proof,
    })
}

/// Compute the expected tree-0 (preprocessed) commitment root for a standalone
/// SHAKE-256 proof, by rebuilding the prover-side [`KeccakProver`] from the
/// public message + shape and running the prover's tree-0 commit path
/// ([`air_core::compute_preprocessed_root_uncached`]). The keccak round-cyclic
/// tables + range tables are shape-determined, but the padded per-instance
/// preprocessed layout is sized to the proof's `shape` (a public field), so the
/// uncached variant is used to pin this specific shape's tree exactly (mirroring
/// the `stwo-mldsa` standalone pin and the P-256 hinted-mul schedule case). The
/// witness rebuilt here materializes only shape-derived preprocessed content.
///
/// # Soundness
///
/// This root is the tree-0 soundness anchor (F-ROOT class): the Blake2s Merkle
/// root binds the contents, order, and sizes of every preprocessed table.
/// [`verify_shake256`] recomputes it from the public message/shape and rejects
/// fail-closed on mismatch, so a forged preprocessed tree never reaches the
/// STARK verifier.
pub fn shake256_expected_preprocessed_root(proof: &KeccakProof, config: PcsConfig) -> CommitmentRoot {
    let witness = build_witness(&proof.message, proof.shape.n_squeeze);
    let mut prover = KeccakProver {
        witness,
        relations: None,
        ic: None,
        components: None,
    };
    air_core::compute_preprocessed_root_uncached(&mut [&mut prover], config)
}

pub fn verify_shake256(proof: &KeccakProof) -> Result<(), VerificationError> {
    // Global logup sum is checked by air_core::verify; add an early structural
    // check for a friendlier error.
    let ic = InteractionClaims {
        sponge: proof.sponge_ic.clone(),
        io: proof.io_ic.clone(),
        keccak: proof.keccak_ic.clone(),
        round: proof.round_ic.clone(),
        tables: proof.tables_ic.clone(),
    };
    if ic.claimed_sums().iter().fold(QM31::zero(), |a, &s| a + s) != QM31::zero() {
        return Err(VerificationError::InvalidStructure("keccak logup sum nonzero".into()));
    }

    let mut verifier = KeccakVerifier {
        shape: proof.shape,
        message: proof.message.clone(),
        output: proof.output.clone(),
        ic,
        relations: None,
        components: None,
    };
    // Pin the preprocessed (tree-0) root before any transcript work: recompute
    // it from the public message/shape and reject a forged preprocessed tree
    // fail-closed (F-ROOT hardening).
    let expected_root = shake256_expected_preprocessed_root(proof, proof.stark_proof.config);
    air_core::verify_with_expected_preprocessed_root(
        &mut [&mut verifier],
        &proof.stark_proof,
        Some(expected_root),
    )
    .map_err(|error| match error {
        air_core::VerifyError::Stark(error) => error,
        air_core::VerifyError::PreprocessedRootMismatch { .. } => {
            VerificationError::InvalidStructure("keccak preprocessed root mismatch (forged tree-0)".into())
        }
    })
}
