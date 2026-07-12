//! The rotated (vertical) sponge component: one trace row per Keccak-f[1600]
//! PERMUTATION, constant width, for a whole JOB LIST of SHAKE-256 sponges
//! (S1 of the PQ perf campaign — see `tasks/keccak-service-design.md`).
//!
//! The horizontal [`crate::sponge`] commits one column per absorb/state/squeeze
//! byte, so its column count grows with the message length (the measured
//! column whale). This component rotates that layout: the rows are the
//! concatenation of every job's permutations (absorb perms then extra squeeze
//! perms), and the width is fixed at [`N_BASE_COLS`] base columns.
//!
//! ## Row semantics (job-local permutation index `r`, `0 ≤ r < n_perms`)
//!
//! * `r < n_absorb` — an ABSORB row: consumes padded block `r`.
//! * `r ≥ n_absorb − 1` — a SQUEEZE-OUT row: this row's post-state rate is
//!   squeeze block `s = r − (n_absorb − 1)` (post-state framing — the last
//!   absorb row doubles as squeeze block 0, exactly FIPS 202).
//!
//! ## Chaining (Pattern B, `[-1, 0]` masks on `post`)
//!
//! The 200 `post` columns are read with a `[-1, 0]` mask: `post_prev` is the
//! previous row's post-permutation state. The pre-state of row `r` is built by
//! MULTIPLICITY-GATED KeccakState IN tuples (three variants, so every tuple
//! cell stays degree ≤ 1 — the design doc's "folded into the IN tuple
//! construction"):
//!
//! * `is_first`             → `[perm_id, IN, block0_spread | 0…0]` (capacity 0:
//!   a job's chain NEVER leaks in from the previous job or the wraparound row).
//! * `is_absorb − is_first` → `[perm_id, IN, new_rate | post_prev.capacity]`,
//!   with `new_rate = prev_rate ⊕ block` witnessed and xor3-table-checked.
//! * `is_active − is_absorb`→ `[perm_id, IN, post_prev]` (extra squeeze perm).
//!
//! Every schedule flag/constant is PREPROCESSED (trusted — pinned by the
//! tree-0 root), so all plain constraints are degree ≤ 2 and every logup
//! tuple cell is degree ≤ 1; batch-4 logup constraints are degree 5 at
//! `max_constraint_log_degree_bound = log + 2`.
//!
//! ## Relation signs (I-2: EXACTLY the horizontal sponge's)
//!
//! conv use (+), xor3 use (+), HashIo absorb consume (−) / squeeze yield (+),
//! KeccakState IN yield (+) / OUT require (−).

#![allow(clippy::needless_range_loop)]

use num_traits::{One, Zero};
use serde::{Deserialize, Serialize};
use stwo::core::channel::Channel;
use stwo::core::fields::m31::{BaseField, M31};
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::core::pcs::TreeVec;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES, N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    ORIGINAL_TRACE_IDX,
};

use crate::constants::{DELIMITED_SUFFIX, FINAL_BIT, N_BYTES_IN_RATE, N_BYTES_IN_STATE};
use crate::relations::{KeccakRelations, KECCAK_STATE_ARITY};
use crate::sponge::Shape;
use crate::utils::{circle_row_to_coset, col_eval, spread_u32, ColEval};

const RATE: usize = N_BYTES_IN_RATE;

/// Base (witness) columns: `block_byte[136] | block_spread[136] | new_rate[136]
/// | post[200] | squeeze_byte[136]`.
pub const N_BASE_COLS: usize = 3 * RATE + N_BYTES_IN_STATE + RATE;

/// Schedule (preprocessed) columns: 9 scalars + `pad_gate[136]` + `pad_val[136]`.
pub const N_SCHEDULE_COLS: usize = 9 + 2 * RATE;

/// Logup entries per row: conv-block(136) + io-absorb(136) + xor3(136) +
/// state(4: IN×3 gated variants + OUT) + conv-squeeze(136) + io-squeeze(136).
pub const N_LOGUP_ENTRIES: usize = 5 * RATE + 4;

/// Logup fractions batched per interaction column (`finalize_logup_batched`).
/// Batch 4 needs constraint degree `1 + 4·1 = 5 ≤ D5`, available at
/// `max_constraint_log_degree_bound = log + 2`.
pub const LOGUP_BATCH: usize = 4;

/// Interaction columns (batch-4 QM31 fractions, pre-expanded to M31).
pub const N_INTERACTION_COLS: usize =
    SECURE_EXTENSION_DEGREE * N_LOGUP_ENTRIES.div_ceil(LOGUP_BATCH);

// =============================================================================
// Job list.
// =============================================================================

/// The ordered sponge jobs of one component instance. Perm-id bases are
/// stamped cumulatively over the list ([`JobList::new`]), so the shared
/// [`crate::relations::KeccakStateRelation`] never crosses jobs.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct JobList {
    pub jobs: Vec<Shape>,
}

impl JobList {
    /// Build the list from job shapes, re-stamping `perm_id_base` cumulatively
    /// (any incoming base is ignored — the list owns the global perm-id plan).
    pub fn new(shapes: impl IntoIterator<Item = Shape>) -> Self {
        let mut jobs = Vec::new();
        let mut base = 0usize;
        for shape in shapes {
            let stamped = Shape::with_perm_id_base(
                shape.message_len,
                shape.n_squeeze,
                shape.absorb_stream_id,
                shape.squeeze_stream_id,
                base,
            );
            base += stamped.n_perms();
            jobs.push(stamped);
        }
        assert!(!jobs.is_empty(), "job list must have at least one job");
        Self { jobs }
    }

    pub fn n_perms_total(&self) -> usize {
        self.jobs.iter().map(Shape::n_perms).sum()
    }

    pub fn log_size(&self) -> u32 {
        (self.n_perms_total() as u32)
            .next_power_of_two()
            .ilog2()
            .max(LOG_N_LANES)
    }

    /// Stable FNV-1a digest of the full job-list shape, embedded in every
    /// schedule preprocessed id (I-5: the id encodes the job list, so two
    /// different job lists can never alias through tree-0 first-writer dedup).
    pub fn shape_digest(&self) -> String {
        let mut h: u64 = 0xcbf2_9ce4_8422_2325;
        let mut mix = |v: u64| {
            for b in v.to_le_bytes() {
                h ^= b as u64;
                h = h.wrapping_mul(0x0000_0100_0000_01b3);
            }
        };
        mix(self.jobs.len() as u64);
        for s in &self.jobs {
            mix(s.message_len as u64);
            mix(s.n_squeeze as u64);
            mix(s.absorb_stream_id as u64);
            mix(s.squeeze_stream_id as u64);
            mix(s.perm_id_base as u64);
        }
        format!("{h:016x}")
    }

    /// Bind every job's public shape (and the derived layout) to the transcript.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.jobs.len() as u64);
        channel.mix_u64(self.log_size() as u64);
        for s in &self.jobs {
            channel.mix_u64(s.message_len as u64);
            channel.mix_u64(s.n_squeeze as u64);
            channel.mix_u64(s.absorb_stream_id as u64);
            channel.mix_u64(s.squeeze_stream_id as u64);
            channel.mix_u64(s.perm_id_base as u64);
        }
    }
}

// =============================================================================
// Schedule (preprocessed, shape-derived — witness-independent).
// =============================================================================

/// One row's schedule entry (all preprocessed).
#[derive(Clone)]
struct RowSched {
    first: bool,
    absorb: bool,
    squeeze_out: bool,
    perm_id: u32,
    absorb_stream: u32,
    squeeze_stream: u32,
    absorb_pos_base: u32,
    squeeze_pos_base: u32,
    /// `pad_gate[j] = 1` iff byte `j` of this row's block is a pad10*1 constant.
    pad_gate: [u8; RATE],
    /// The pad constant at gated positions (0 elsewhere).
    pad_val: [u8; RATE],
}

/// Build the per-row schedule for the whole job list (active rows only).
fn build_schedule(jobs: &JobList) -> Vec<RowSched> {
    let mut rows = Vec::with_capacity(jobs.n_perms_total());
    for shape in &jobs.jobs {
        let f = shape.message_len % RATE;
        for r in 0..shape.n_perms() {
            let absorb = r < shape.n_absorb;
            let last_absorb = r + 1 == shape.n_absorb;
            let squeeze_out = r + 1 >= shape.n_absorb;
            let mut pad_gate = [0u8; RATE];
            let mut pad_val = [0u8; RATE];
            if absorb && last_absorb {
                for j in f..RATE {
                    pad_gate[j] = 1;
                    let mut v = 0u8;
                    if j == f {
                        v ^= DELIMITED_SUFFIX;
                    }
                    if j == RATE - 1 {
                        v ^= FINAL_BIT;
                    }
                    pad_val[j] = v;
                }
            }
            rows.push(RowSched {
                first: r == 0,
                absorb,
                squeeze_out,
                perm_id: (shape.perm_id_base + r) as u32,
                absorb_stream: shape.absorb_stream_id,
                squeeze_stream: shape.squeeze_stream_id,
                absorb_pos_base: (r * RATE) as u32,
                squeeze_pos_base: if squeeze_out {
                    ((r + 1 - shape.n_absorb) * RATE) as u32
                } else {
                    0
                },
                pad_gate,
                pad_val,
            });
        }
    }
    rows
}

fn schedule_id(digest: &str, name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("keccak_svc/{digest}/{name}"),
    }
}

const SCALAR_SCHED_NAMES: [&str; 9] = [
    "is_active",
    "is_first",
    "is_absorb",
    "is_squeeze_out",
    "perm_id",
    "absorb_stream",
    "squeeze_stream",
    "absorb_pos_base",
    "squeeze_pos_base",
];

/// The schedule preprocessed column ids, in commit order.
pub fn schedule_ids(jobs: &JobList) -> Vec<PreProcessedColumnId> {
    let d = jobs.shape_digest();
    let mut ids: Vec<PreProcessedColumnId> = SCALAR_SCHED_NAMES
        .iter()
        .map(|n| schedule_id(&d, n))
        .collect();
    for j in 0..RATE {
        ids.push(schedule_id(&d, &format!("pad_gate_{j}")));
    }
    for j in 0..RATE {
        ids.push(schedule_id(&d, &format!("pad_val_{j}")));
    }
    ids
}

/// Generate the schedule preprocessed columns (commit order = [`schedule_ids`]).
pub fn gen_schedule_preprocessed(jobs: &JobList) -> Vec<ColEval> {
    let log_size = jobs.log_size();
    let rows = 1usize << log_size;
    let sched = build_schedule(jobs);
    let m = M31::from_u32_unchecked;

    let scalar = |f: &dyn Fn(&RowSched) -> u32| -> Vec<M31> {
        let mut col = vec![M31::zero(); rows];
        for (r, s) in sched.iter().enumerate() {
            col[r] = m(f(s));
        }
        col
    };

    let mut cols: Vec<Vec<M31>> = vec![
        scalar(&|_| 1),
        scalar(&|s| s.first as u32),
        scalar(&|s| s.absorb as u32),
        scalar(&|s| s.squeeze_out as u32),
        scalar(&|s| s.perm_id),
        scalar(&|s| s.absorb_stream),
        scalar(&|s| s.squeeze_stream),
        scalar(&|s| s.absorb_pos_base),
        scalar(&|s| s.squeeze_pos_base),
    ];
    for j in 0..RATE {
        cols.push(scalar(&move |s| s.pad_gate[j] as u32));
    }
    for j in 0..RATE {
        cols.push(scalar(&move |s| s.pad_val[j] as u32));
    }
    debug_assert_eq!(cols.len(), N_SCHEDULE_COLS);
    cols.into_iter().map(|c| col_eval(log_size, c)).collect()
}

// =============================================================================
// Witness (trace) generation.
// =============================================================================

/// One active row's committed values (bytes; spreads derived). Cells a row does
/// not use stay 0 — the constraint side gates them out with zero multiplicity.
#[derive(Clone)]
pub struct RowData {
    pub block_byte: [u8; RATE],
    pub new_rate: [u8; RATE],
    pub prev_post: [u8; N_BYTES_IN_STATE],
    pub post: [u8; N_BYTES_IN_STATE],
    pub squeeze_byte: [u8; RATE],
}

impl Default for RowData {
    fn default() -> Self {
        Self {
            block_byte: [0; RATE],
            new_rate: [0; RATE],
            prev_post: [0; N_BYTES_IN_STATE],
            post: [0; N_BYTES_IN_STATE],
            squeeze_byte: [0; RATE],
        }
    }
}

/// The prover-side sponge run over the whole job list.
pub struct SpongeVRun {
    pub jobs: JobList,
    /// Active rows in coset order (`len == jobs.n_perms_total()`).
    pub rows: Vec<RowData>,
    /// Permutation input rows `[spread_state(200) | perm_id]` for
    /// [`crate::stark::build_perm_witness`] (lane 0 real, splatted).
    pub perm_inputs: Vec<[PackedM31; N_BYTES_IN_STATE + 1]>,
    /// xor3 uses per non-first absorb row, for [`crate::tables_air::TableMultiplicities::add_sponge`].
    pub xor: Vec<Vec<[PackedM31; 2]>>,
    /// conv uses (block bytes + squeeze bytes), same destination.
    pub conv: Vec<[PackedM31; 2]>,
    /// Per-job full squeeze outputs (`136 · n_squeeze` bytes each).
    pub outputs: Vec<Vec<u8>>,
}

fn splat(v: u32) -> PackedM31 {
    PackedM31::from(M31::from(v))
}
fn spread_splat(b: u8) -> PackedM31 {
    splat(spread_u32(b as u32))
}

/// Run every job's sponge natively and record the per-permutation rows.
pub fn generate_jobs(jobs: &JobList, messages: &[Vec<u8>]) -> SpongeVRun {
    assert_eq!(messages.len(), jobs.jobs.len(), "one message per job");
    let mut rows: Vec<RowData> = Vec::with_capacity(jobs.n_perms_total());
    let mut perm_inputs = Vec::with_capacity(jobs.n_perms_total());
    let mut xor = Vec::new();
    let mut conv = Vec::new();
    let mut outputs = Vec::new();

    for (shape, message) in jobs.jobs.iter().zip(messages) {
        assert_eq!(message.len(), shape.message_len, "message length mismatch");
        let f = shape.message_len % RATE;

        // Padded absorb blocks.
        let mut blocks = vec![[0u8; RATE]; shape.n_absorb];
        for (i, &b) in message.iter().enumerate() {
            blocks[i / RATE][i % RATE] = b;
        }
        blocks[shape.n_absorb - 1][f] ^= DELIMITED_SUFFIX;
        blocks[shape.n_absorb - 1][RATE - 1] ^= FINAL_BIT;

        let mut state = [0u8; N_BYTES_IN_STATE];
        let mut output = Vec::with_capacity(shape.output_len());

        for r in 0..shape.n_perms() {
            let mut row = RowData {
                prev_post: state,
                ..RowData::default()
            };
            if r < shape.n_absorb {
                row.block_byte = blocks[r];
                for j in 0..RATE {
                    conv.push([splat(blocks[r][j] as u32), spread_splat(blocks[r][j])]);
                }
                if r == 0 {
                    state[..RATE].copy_from_slice(&blocks[0]);
                    // capacity stays 0.
                } else {
                    let mut uses = Vec::with_capacity(RATE);
                    for j in 0..RATE {
                        let old = state[j];
                        let m = blocks[r][j];
                        let newv = old ^ m;
                        uses.push([spread_splat(old) + spread_splat(m), spread_splat(newv)]);
                        row.new_rate[j] = newv;
                        state[j] = newv;
                    }
                    xor.push(uses);
                }
            }
            // Pre-permutation state → perm input (spread, lane-0 splat).
            let mut prow = [PackedM31::zero(); N_BYTES_IN_STATE + 1];
            for i in 0..N_BYTES_IN_STATE {
                prow[i] = spread_splat(state[i]);
            }
            prow[N_BYTES_IN_STATE] = splat((shape.perm_id_base + r) as u32);
            perm_inputs.push(prow);

            crate::sponge::native_keccak_f_bytes(&mut state);
            row.post = state;

            if r + 1 >= shape.n_absorb {
                row.squeeze_byte.copy_from_slice(&state[..RATE]);
                output.extend_from_slice(&state[..RATE]);
                for j in 0..RATE {
                    conv.push([splat(state[j] as u32), spread_splat(state[j])]);
                }
            }
            rows.push(row);
        }
        debug_assert_eq!(output.len(), shape.output_len());
        outputs.push(output);
    }

    SpongeVRun {
        jobs: jobs.clone(),
        rows,
        perm_inputs,
        xor,
        conv,
        outputs,
    }
}

/// Assemble the 744 base trace columns (commit order = the AIR's read order).
pub fn generate_base_trace(run: &SpongeVRun) -> Vec<ColEval> {
    let log_size = run.jobs.log_size();
    let rows = 1usize << log_size;
    let m = M31::from_u32_unchecked;
    let mut cols: Vec<Vec<M31>> = vec![vec![M31::zero(); rows]; N_BASE_COLS];
    for (r, row) in run.rows.iter().enumerate() {
        let mut c = 0usize;
        for j in 0..RATE {
            cols[c + j][r] = m(row.block_byte[j] as u32);
        }
        c += RATE;
        for j in 0..RATE {
            cols[c + j][r] = m(spread_u32(row.block_byte[j] as u32));
        }
        c += RATE;
        for j in 0..RATE {
            cols[c + j][r] = m(spread_u32(row.new_rate[j] as u32));
        }
        c += RATE;
        for i in 0..N_BYTES_IN_STATE {
            cols[c + i][r] = m(spread_u32(row.post[i] as u32));
        }
        c += N_BYTES_IN_STATE;
        for j in 0..RATE {
            cols[c + j][r] = m(row.squeeze_byte[j] as u32);
        }
        debug_assert_eq!(c + RATE, N_BASE_COLS);
    }
    cols.into_iter().map(|c| col_eval(log_size, c)).collect()
}

// =============================================================================
// Claim.
// =============================================================================

#[derive(Clone, Serialize, Deserialize, Debug)]
pub struct Claim {
    pub jobs: JobList,
}

impl Claim {
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let ls = self.jobs.log_size();
        TreeVec::new(vec![
            vec![ls; N_SCHEDULE_COLS],
            vec![ls; N_BASE_COLS],
            vec![ls; N_INTERACTION_COLS],
        ])
    }
}

// =============================================================================
// Constraints.
// =============================================================================

#[derive(Clone)]
pub struct Eval {
    pub jobs: JobList,
    pub relations: KeccakRelations,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.jobs.log_size()
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Every plain constraint is degree ≤ 2, every logup numerator is a
        // degree ≤ 1 preprocessed gate, and every tuple cell — hence every
        // denominator — is degree ≤ 1, so batch-4 logup constraints are
        // degree 1 + 4·1 = 5 ≤ D5, which log + 2 affords (the M4 trap around
        // the Pattern-B `[-1, 0]` masks is fixed in the pinned engine).
        self.log_size() + 2
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let rel = &self.relations;
        let d = self.jobs.shape_digest();

        // Schedule (preprocessed, trusted — no boolean constraints needed).
        let is_active = eval.get_preprocessed_column(schedule_id(&d, "is_active"));
        let is_first = eval.get_preprocessed_column(schedule_id(&d, "is_first"));
        let is_absorb = eval.get_preprocessed_column(schedule_id(&d, "is_absorb"));
        let is_squeeze_out = eval.get_preprocessed_column(schedule_id(&d, "is_squeeze_out"));
        let perm_id = eval.get_preprocessed_column(schedule_id(&d, "perm_id"));
        let absorb_stream = eval.get_preprocessed_column(schedule_id(&d, "absorb_stream"));
        let squeeze_stream = eval.get_preprocessed_column(schedule_id(&d, "squeeze_stream"));
        let absorb_pos_base = eval.get_preprocessed_column(schedule_id(&d, "absorb_pos_base"));
        let squeeze_pos_base = eval.get_preprocessed_column(schedule_id(&d, "squeeze_pos_base"));
        let pad_gate: Vec<E::F> = (0..RATE)
            .map(|j| eval.get_preprocessed_column(schedule_id(&d, &format!("pad_gate_{j}"))))
            .collect();
        let pad_val: Vec<E::F> = (0..RATE)
            .map(|j| eval.get_preprocessed_column(schedule_id(&d, &format!("pad_val_{j}"))))
            .collect();

        // Base columns (commit order).
        let block_byte: Vec<E::F> = (0..RATE).map(|_| eval.next_trace_mask()).collect();
        let block_spread: Vec<E::F> = (0..RATE).map(|_| eval.next_trace_mask()).collect();
        let new_rate: Vec<E::F> = (0..RATE).map(|_| eval.next_trace_mask()).collect();
        // post with the [-1, 0] chaining mask: [prev row's post, this row's post].
        let post_masks: Vec<[E::F; 2]> = (0..N_BYTES_IN_STATE)
            .map(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [-1, 0]))
            .collect();
        let post_prev = |i: usize| post_masks[i][0].clone();
        let post = |i: usize| post_masks[i][1].clone();
        let squeeze_byte: Vec<E::F> = (0..RATE).map(|_| eval.next_trace_mask()).collect();

        // pad10*1: gated positions of an absorb row's block are pinned to the
        // preprocessed pad constant (degree 2; gate + value both preprocessed).
        for j in 0..RATE {
            eval.add_constraint(pad_gate[j].clone() * (block_byte[j].clone() - pad_val[j].clone()));
        }

        // 1. conv: bind every absorb-row block byte to its spread limb (+).
        for j in 0..RATE {
            eval.add_to_relation(RelationEntry::base(
                &rel.conv,
                is_absorb.clone(),
                &[block_byte[j].clone(), block_spread[j].clone()],
            ));
        }
        // 2. HashIo: consume the real message bytes (−). The message gate is
        // `is_absorb − pad_gate[j]` (1 on message positions of absorb rows).
        for j in 0..RATE {
            let jf = E::F::from(BaseField::from(j as u32));
            eval.add_to_relation(RelationEntry::base(
                &rel.hash_io,
                -(is_absorb.clone() - pad_gate[j].clone()),
                &[
                    absorb_stream.clone(),
                    absorb_pos_base.clone() + jf,
                    block_byte[j].clone(),
                ],
            ));
        }
        // 3. xor3: rate ^= block on non-first absorb rows (+). Key is the
        // degree-1 sum of the two committed spreads; output is the witnessed
        // new_rate spread (range- and correctness-bound by dense-table rows).
        for j in 0..RATE {
            eval.add_to_relation(RelationEntry::base(
                &rel.xor3,
                is_absorb.clone() - is_first.clone(),
                &[post_prev(j) + block_spread[j].clone(), new_rate[j].clone()],
            ));
        }
        // 4. KeccakState: three gated IN variants (+) and the OUT require (−).
        let mk_state = |rate: &dyn Fn(usize) -> E::F, cap: &dyn Fn(usize) -> E::F| {
            let mut t: Vec<E::F> = Vec::with_capacity(KECCAK_STATE_ARITY);
            t.push(perm_id.clone());
            t.push(E::F::zero()); // direction::IN
            for j in 0..RATE {
                t.push(rate(j));
            }
            for i in RATE..N_BYTES_IN_STATE {
                t.push(cap(i));
            }
            t
        };
        // first perm of a job: rate = block0 spread, capacity = 0.
        let in_first = mk_state(&|j| block_spread[j].clone(), &|_| E::F::zero());
        eval.add_to_relation(RelationEntry::base(
            &rel.keccak_state,
            is_first.clone(),
            &in_first,
        ));
        // later absorb perms: rate = new_rate, capacity chains from prev post.
        let in_absorb = mk_state(&|j| new_rate[j].clone(), &post_prev);
        eval.add_to_relation(RelationEntry::base(
            &rel.keccak_state,
            is_absorb.clone() - is_first.clone(),
            &in_absorb,
        ));
        // extra squeeze perms: the whole pre-state chains from prev post.
        let in_squeeze = mk_state(&post_prev, &post_prev);
        eval.add_to_relation(RelationEntry::base(
            &rel.keccak_state,
            is_active.clone() - is_absorb.clone(),
            &in_squeeze,
        ));
        // OUT: require the witnessed post state from the keccak component (−).
        let mut out_tuple: Vec<E::F> = Vec::with_capacity(KECCAK_STATE_ARITY);
        out_tuple.push(perm_id.clone());
        out_tuple.push(E::F::one()); // direction::OUT
        for i in 0..N_BYTES_IN_STATE {
            out_tuple.push(post(i));
        }
        eval.add_to_relation(RelationEntry::base(
            &rel.keccak_state,
            -is_active.clone(),
            &out_tuple,
        ));
        // 5. conv: bind squeeze bytes to this row's post rate spreads (+).
        for j in 0..RATE {
            eval.add_to_relation(RelationEntry::base(
                &rel.conv,
                is_squeeze_out.clone(),
                &[squeeze_byte[j].clone(), post(j)],
            ));
        }
        // 6. HashIo: yield the squeeze bytes (+).
        for j in 0..RATE {
            let jf = E::F::from(BaseField::from(j as u32));
            eval.add_to_relation(RelationEntry::base(
                &rel.hash_io,
                is_squeeze_out.clone(),
                &[
                    squeeze_stream.clone(),
                    squeeze_pos_base.clone() + jf,
                    squeeze_byte[j].clone(),
                ],
            ));
        }

        eval.finalize_logup_batched(LOGUP_BATCH);
        eval
    }
}

pub type Component = FrameworkComponent<Eval>;

// =============================================================================
// Interaction trace.
// =============================================================================

#[derive(Clone, Serialize, Deserialize, Debug)]
pub struct InteractionClaim {
    pub claimed_sum: SecureField,
}

impl InteractionClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}

/// The 684 per-row logup fractions in EXACTLY the AIR's emission order.
/// Zero-multiplicity entries are `(0, 1)` — sound because the batch constraint
/// evaluates the symbolic multiplicity (a preprocessed gate that IS zero
/// there), so the committed accumulator step is 0 either way.
fn row_fracs(
    rel: &KeccakRelations,
    sched: &RowSched,
    row: &RowData,
) -> Vec<(SecureField, SecureField)> {
    let zero = SecureField::zero();
    let one = SecureField::one();
    let m = M31::from_u32_unchecked;
    let sp = |b: u8| m(spread_u32(b as u32));
    let mut out: Vec<(SecureField, SecureField)> = Vec::with_capacity(N_LOGUP_ENTRIES);

    // 1. conv block (+is_absorb).
    for j in 0..RATE {
        if sched.absorb {
            let den: SecureField = rel
                .conv
                .combine(&[m(row.block_byte[j] as u32), sp(row.block_byte[j])]);
            out.push((one, den));
        } else {
            out.push((zero, one));
        }
    }
    // 2. io absorb consume (−(is_absorb − pad_gate)).
    for j in 0..RATE {
        if sched.absorb && sched.pad_gate[j] == 0 {
            let den: SecureField = rel.hash_io.combine(&[
                m(sched.absorb_stream),
                m(sched.absorb_pos_base + j as u32),
                m(row.block_byte[j] as u32),
            ]);
            out.push((-one, den));
        } else {
            out.push((zero, one));
        }
    }
    // 3. xor3 (+(is_absorb − is_first)).
    for j in 0..RATE {
        if sched.absorb && !sched.first {
            let key = sp(row.prev_post[j]) + sp(row.block_byte[j]);
            let den: SecureField = rel.xor3.combine(&[key, sp(row.new_rate[j])]);
            out.push((one, den));
        } else {
            out.push((zero, one));
        }
    }
    // 4. state: IN_first, IN_absorb, IN_squeeze (+ gates), OUT (−1).
    let state_tuple = |dir: u32, rate: &dyn Fn(usize) -> M31, cap: &dyn Fn(usize) -> M31| {
        let mut t = Vec::with_capacity(KECCAK_STATE_ARITY);
        t.push(m(sched.perm_id));
        t.push(m(dir));
        for j in 0..RATE {
            t.push(rate(j));
        }
        for i in RATE..N_BYTES_IN_STATE {
            t.push(cap(i));
        }
        t
    };
    if sched.first {
        let t = state_tuple(0, &|j| sp(row.block_byte[j]), &|_| M31::zero());
        out.push((one, rel.keccak_state.combine(&t)));
    } else {
        out.push((zero, one));
    }
    if sched.absorb && !sched.first {
        let t = state_tuple(0, &|j| sp(row.new_rate[j]), &|i| sp(row.prev_post[i]));
        out.push((one, rel.keccak_state.combine(&t)));
    } else {
        out.push((zero, one));
    }
    if !sched.absorb {
        let t = state_tuple(0, &|j| sp(row.prev_post[j]), &|i| sp(row.prev_post[i]));
        out.push((one, rel.keccak_state.combine(&t)));
    } else {
        out.push((zero, one));
    }
    {
        let t = state_tuple(1, &|j| sp(row.post[j]), &|i| sp(row.post[i]));
        out.push((-one, rel.keccak_state.combine(&t)));
    }
    // 5. conv squeeze (+is_squeeze_out).
    for j in 0..RATE {
        if sched.squeeze_out {
            let den: SecureField = rel
                .conv
                .combine(&[m(row.squeeze_byte[j] as u32), sp(row.squeeze_byte[j])]);
            out.push((one, den));
        } else {
            out.push((zero, one));
        }
    }
    // 6. io squeeze yield (+is_squeeze_out).
    for j in 0..RATE {
        if sched.squeeze_out {
            let den: SecureField = rel.hash_io.combine(&[
                m(sched.squeeze_stream),
                m(sched.squeeze_pos_base + j as u32),
                m(row.squeeze_byte[j] as u32),
            ]);
            out.push((one, den));
        } else {
            out.push((zero, one));
        }
    }
    debug_assert_eq!(out.len(), N_LOGUP_ENTRIES);
    out
}

/// Build the interaction trace: batch-4 columns matching
/// `finalize_logup_batched(LOGUP_BATCH)` over the AIR's emission order
/// (consecutive chunks; the last chunk may be smaller).
pub fn generate_interaction_trace(
    rel: &KeccakRelations,
    run: &SpongeVRun,
) -> (InteractionClaim, Vec<ColEval>) {
    let log_size = run.jobs.log_size();
    let sched = build_schedule(&run.jobs);
    assert_eq!(sched.len(), run.rows.len(), "schedule/rows length mismatch");

    // Per active coset row: the 684 (num, den) fractions.
    let fracs: Vec<Vec<(SecureField, SecureField)>> = sched
        .iter()
        .zip(&run.rows)
        .map(|(s, r)| row_fracs(rel, s, r))
        .collect();
    let zero = SecureField::zero();
    let one = SecureField::one();
    let entry = |coset: usize, e: usize| -> (SecureField, SecureField) {
        if coset < fracs.len() {
            fracs[coset][e]
        } else {
            (zero, one)
        }
    };

    let row_lookup = circle_row_to_coset(log_size);
    let n_vec_rows = 1usize << (log_size - LOG_N_LANES);
    let mut gen = LogupTraceGenerator::new(log_size);
    // Fold each chunk exactly like `finalize_logup_batched`: start from the
    // first fraction, then num = d·num + n·den, den = den·d.
    for k in 0..N_LOGUP_ENTRIES.div_ceil(LOGUP_BATCH) {
        let lo = k * LOGUP_BATCH;
        let hi = (lo + LOGUP_BATCH).min(N_LOGUP_ENTRIES);
        let mut col = gen.new_col();
        for vr in 0..n_vec_rows {
            let mut num = [zero; N_LANES];
            let mut den = [one; N_LANES];
            for lane in 0..N_LANES {
                let coset = row_lookup[vr * N_LANES + lane];
                let (mut n_acc, mut d_acc) = entry(coset, lo);
                for e in lo + 1..hi {
                    let (n, d) = entry(coset, e);
                    n_acc = d * n_acc + n * d_acc;
                    d_acc = d_acc * d;
                }
                num[lane] = n_acc;
                den[lane] = d_acc;
            }
            col.write_frac(vr, PackedQM31::from_array(num), PackedQM31::from_array(den));
        }
        col.finalize_col();
    }
    let (trace, claimed_sum) = gen.finalize_last();
    (InteractionClaim { claimed_sum }, trace)
}
