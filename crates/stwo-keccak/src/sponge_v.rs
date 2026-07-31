//! The vertical sponge component uses one constant-width trace row for each
//! Keccak-f[1600] permutation in an ordered list of SHAKE-128 and SHAKE-256
//! jobs.
//!
//! The rows contain every job's absorb and extra squeeze permutations. The
//! width is fixed at [`N_BASE_COLS`] base columns.
//!
//! ## Row semantics (job-local permutation index `r`, `0 ≤ r < n_perms`)
//!
//! * `r < n_absorb`: an ABSORB row that consumes padded block `r`.
//! * `r ≥ n_absorb − 1`: a SQUEEZE-OUT row. Its post-state rate is squeeze
//!   block `s = r − (n_absorb − 1)`. The last absorb row is also squeeze block
//!   0, as specified by FIPS 202.
//!
//! ## Chaining (Pattern B, `[-1, 0]` masks on `post`)
//!
//! The 200 `post` columns use a `[-1, 0]` mask. `post_prev` is the
//! previous row's post-permutation state. The pre-state of row `r` is built by
//! multiplicity-gated KeccakState input tuples. The three variants keep each
//! tuple cell at degree 1 or less:
//!
//! * `is_first`             → `[perm_id, IN, block0_spread | 0…0]` (capacity 0:
//!   this prevents input from a previous job or the wraparound row).
//! * `is_absorb − is_first` → `[perm_id, IN, new_rate | post_prev.capacity]`,
//!   with `new_rate = prev_rate ⊕ block` witnessed and xor3-table-checked.
//! * `is_active − is_absorb`→ `[perm_id, IN, post_prev]` (extra squeeze perm).
//!
//! The tree-0 root pins the committed schedule columns. The AIR derives rate,
//! capacity-mode, and padding values from those columns. Plain constraints
//! have degree at most 4. Batch-four LogUp constraints have degree 5.
//!
//! ## Relation signs
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

use crate::constants::{
    DELIMITED_SUFFIX, FINAL_BIT, N_BYTES_IN_RATE, N_BYTES_IN_SHAKE128_RATE, N_BYTES_IN_STATE,
};
use crate::relations::{KeccakRelations, KECCAK_STATE_ARITY};
use crate::sponge::{Shape, XofMode};
use crate::utils::{circle_row_to_coset, col_eval, spread_u32, ColEval};

/// Maximum supported rate: SHAKE-128's 168 bytes. SHAKE-256 rows gate off
/// columns 136..168 through the preprocessed schedule.
pub const MAX_RATE: usize = N_BYTES_IN_SHAKE128_RATE;

/// Base (witness) columns: `block_byte[MAX_RATE] | block_spread[MAX_RATE] |
/// new_rate[MAX_RATE] | post[200] | squeeze_byte[MAX_RATE]`.
pub const N_BASE_COLS: usize = 3 * MAX_RATE + N_BYTES_IN_STATE + MAX_RATE;

/// Capacity-mode-only base columns: the actual absorb selector, the actual
/// squeeze selector, and the verifier-length-derived pad suffix mask.
pub const N_CAPACITY_BASE_COLS: usize = 2 + MAX_RATE;

/// Scalar schedule columns. Padding masks add one column per distinct,
/// nonzero fixed-job mask.
pub const N_SCHEDULE_COLS: usize = 10;

/// Logup entries per row: five MAX_RATE byte families plus six state entries
/// (mode-gated first/absorb inputs, squeeze input, and output).
pub const N_LOGUP_ENTRIES: usize = 5 * MAX_RATE + 6;

/// Logup fractions batched per interaction column (`finalize_logup_batched`).
/// Batch 4 needs constraint degree `1 + 4·1 = 5 ≤ D5`, available at
/// `max_constraint_log_degree_bound = log + 2`.
pub const LOGUP_BATCH: usize = 4;

/// Interaction columns (batch-4 QM31 fractions, pre-expanded to M31).
pub const N_INTERACTION_COLS: usize =
    SECURE_EXTENSION_DEGREE * N_LOGUP_ENTRIES.div_ceil(LOGUP_BATCH);

fn n_logup_entries(jobs: &JobList) -> usize {
    N_LOGUP_ENTRIES + usize::from(jobs.has_message_capacity())
}

pub fn n_interaction_cols(jobs: &JobList) -> usize {
    SECURE_EXTENSION_DEGREE * n_logup_entries(jobs).div_ceil(LOGUP_BATCH)
}

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
    /// The list owns the global permutation-id plan and ignores an input base.
    pub fn new(shapes: impl IntoIterator<Item = Shape>) -> Self {
        let mut jobs = Vec::new();
        let mut base = 0usize;
        for shape in shapes {
            assert_eq!(
                shape.n_absorb,
                (shape.geometry_message_len() + 1).div_ceil(shape.rate()),
                "shape n_absorb must match its fixed geometry"
            );
            if let Some(capacity) = shape.message_capacity {
                assert!(
                    shape.message_len <= capacity,
                    "capacity-shaped message exceeds its fixed capacity"
                );
                assert_eq!(
                    shape.n_squeeze, 1,
                    "capacity-shaped jobs require one squeeze block"
                );
                assert_eq!(
                    shape.xof_mode,
                    XofMode::Shake256,
                    "capacity-shaped jobs currently support SHAKE-256 only"
                );
            }
            let stamped = shape.with_rebased_perm_ids(base);
            base += stamped.n_perms();
            jobs.push(stamped);
        }
        assert!(!jobs.is_empty(), "job list must have at least one job");
        Self { jobs }
    }

    pub fn n_perms_total(&self) -> usize {
        self.jobs.iter().map(Shape::n_perms).sum()
    }

    pub fn has_message_capacity(&self) -> bool {
        self.jobs.iter().any(Shape::has_message_capacity)
    }

    pub fn capacity_job_count(&self) -> usize {
        self.jobs
            .iter()
            .filter(|shape| shape.has_message_capacity())
            .count()
    }

    pub fn n_schedule_cols(&self) -> usize {
        N_SCHEDULE_COLS
            + pad_gate_aliases(self)
                .iter()
                .enumerate()
                .filter(|(column, alias)| **alias == Some(*column))
                .count()
            + self.capacity_job_count()
    }

    pub fn n_base_cols(&self) -> usize {
        N_BASE_COLS + usize::from(self.has_message_capacity()) * N_CAPACITY_BASE_COLS
    }

    pub fn log_size(&self) -> u32 {
        (self.n_perms_total() as u32)
            .next_power_of_two()
            .ilog2()
            .max(LOG_N_LANES)
    }

    /// Stable FNV-1a digest of the full job-list shape, embedded in every
    /// schedule preprocessed identifier. It encodes the job list, so two
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
            mix(s.xof_mode.transcript_tag());
            mix(s.rate() as u64);
            if let Some(capacity) = s.message_capacity {
                // Capacity schedules must match across actual request lengths
                // but must not match a fixed-length shape.
                mix(0x4341_5041_4349_5459);
                mix(capacity as u64);
            } else {
                mix(s.message_len as u64);
            }
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
            channel.mix_u64(s.xof_mode.transcript_tag());
            channel.mix_u64(s.rate() as u64);
            channel.mix_u64(s.message_len as u64);
            channel.mix_u64(s.n_squeeze as u64);
            channel.mix_u64(s.absorb_stream_id as u64);
            channel.mix_u64(s.squeeze_stream_id as u64);
            channel.mix_u64(s.perm_id_base as u64);
            if let Some(capacity) = s.message_capacity {
                channel.mix_u64(0x4341_5041_4349_5459);
                channel.mix_u64(capacity as u64);
            }
        }
    }
}

// =============================================================================
// The preprocessed schedule depends only on the shape.
// =============================================================================

/// One canonical row used to generate the committed schedule columns.
#[derive(Clone)]
struct RowSched {
    first: bool,
    absorb: bool,
    squeeze_out: bool,
    shake128: bool,
    perm_id: u32,
    absorb_stream: u32,
    squeeze_stream: u32,
    absorb_pos_base: u32,
    squeeze_pos_base: u32,
    capacity_mode: bool,
    capacity_job: Option<usize>,
    /// `pad_gate[j] = 1` iff byte `j` of this row's block is a pad10*1 constant.
    pad_gate: [u8; MAX_RATE],
}

/// Build the per-row schedule for the whole job list (active rows only).
fn build_schedule(jobs: &JobList) -> Vec<RowSched> {
    let mut rows = Vec::with_capacity(jobs.n_perms_total());
    let mut next_capacity_job = 0usize;
    for shape in &jobs.jobs {
        let capacity_job = shape.has_message_capacity().then(|| {
            let job = next_capacity_job;
            next_capacity_job += 1;
            job
        });
        let rate = shape.rate();
        let f = shape.geometry_message_len() % rate;
        for r in 0..shape.n_perms() {
            let absorb = r < shape.n_absorb;
            let last_absorb = r + 1 == shape.n_absorb;
            let squeeze_out = r + 1 >= shape.n_absorb;
            let mut pad_gate = [0u8; MAX_RATE];
            if absorb && last_absorb {
                pad_gate[f..rate].fill(1);
            }
            rows.push(RowSched {
                first: r == 0,
                absorb,
                squeeze_out,
                shake128: shape.xof_mode == XofMode::Shake128,
                perm_id: (shape.perm_id_base + r) as u32,
                absorb_stream: shape.absorb_stream_id,
                squeeze_stream: shape.squeeze_stream_id,
                absorb_pos_base: (r * rate) as u32,
                squeeze_pos_base: if squeeze_out {
                    ((r + 1 - shape.n_absorb) * rate) as u32
                } else {
                    0
                },
                capacity_mode: shape.has_message_capacity(),
                capacity_job,
                pad_gate,
            });
        }
    }
    rows
}

fn fixed_job_uses_pad_at(shape: &Shape, byte: usize) -> bool {
    if shape.has_message_capacity() {
        return false;
    }
    let rate = shape.rate();
    byte >= shape.message_len % rate && byte < rate
}

/// Map each logical fixed-padding mask to its first equal nonzero mask.
/// Capacity-job rows are zero because their padding mask is committed.
fn pad_gate_aliases(jobs: &JobList) -> [Option<usize>; MAX_RATE] {
    let mut aliases = [None; MAX_RATE];
    for byte in 0..MAX_RATE {
        if !jobs
            .jobs
            .iter()
            .any(|shape| fixed_job_uses_pad_at(shape, byte))
        {
            continue;
        }
        let representative = (0..byte).find(|&candidate| {
            aliases[candidate] == Some(candidate)
                && jobs.jobs.iter().all(|shape| {
                    fixed_job_uses_pad_at(shape, candidate) == fixed_job_uses_pad_at(shape, byte)
                })
        });
        aliases[byte] = Some(representative.unwrap_or(byte));
    }
    aliases
}

fn schedule_id(digest: &str, name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("keccak_svc/{digest}/{name}"),
    }
}

const SCALAR_SCHED_NAMES: [&str; 10] = [
    "is_active",
    "is_first",
    "is_absorb",
    "is_squeeze_out",
    "is_shake128",
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
    for (byte, alias) in pad_gate_aliases(jobs).into_iter().enumerate() {
        if alias == Some(byte) {
            ids.push(schedule_id(&d, &format!("pad_gate_{byte}")));
        }
    }
    if jobs.has_message_capacity() {
        for job in 0..jobs.capacity_job_count() {
            ids.push(schedule_id(&d, &format!("capacity_job_{job}")));
        }
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
        scalar(&|s| s.shake128 as u32),
        scalar(&|s| s.perm_id),
        scalar(&|s| s.absorb_stream),
        scalar(&|s| s.squeeze_stream),
        scalar(&|s| s.absorb_pos_base),
        scalar(&|s| s.squeeze_pos_base),
    ];
    for (byte, alias) in pad_gate_aliases(jobs).into_iter().enumerate() {
        if alias == Some(byte) {
            cols.push(scalar(&move |s| {
                (!s.capacity_mode && s.pad_gate[byte] != 0) as u32
            }));
        }
    }
    if jobs.has_message_capacity() {
        for job in 0..jobs.capacity_job_count() {
            cols.push(scalar(&move |s| (s.capacity_job == Some(job)) as u32));
        }
    }
    debug_assert_eq!(cols.len(), jobs.n_schedule_cols());
    cols.into_iter().map(|c| col_eval(log_size, c)).collect()
}

// =============================================================================
// Witness (trace) generation.
// =============================================================================

/// One active row's committed values (bytes; spreads derived). Cells a row does
/// not use stay 0. The constraints gate them out with zero multiplicity.
#[derive(Clone)]
pub struct RowData {
    /// Actual absorb activity. For fixed shapes this mirrors the preprocessed
    /// schedule; for capacity shapes it is a committed monotone prefix.
    pub absorb_active: bool,
    /// Actual squeeze-output row. In capacity mode this selects the last
    /// actual absorb row, not the last allocated row.
    pub squeeze_active: bool,
    /// Dynamic pad suffix for capacity mode (and the mirrored static pad mask
    /// for fixed mode when a mixed job list carries these columns).
    pub pad_gate: [u8; MAX_RATE],
    pub block_byte: [u8; MAX_RATE],
    pub new_rate: [u8; MAX_RATE],
    pub prev_post: [u8; N_BYTES_IN_STATE],
    pub post: [u8; N_BYTES_IN_STATE],
    pub squeeze_byte: [u8; MAX_RATE],
}

impl Default for RowData {
    fn default() -> Self {
        Self {
            absorb_active: false,
            squeeze_active: false,
            pad_gate: [0; MAX_RATE],
            block_byte: [0; MAX_RATE],
            new_rate: [0; MAX_RATE],
            prev_post: [0; N_BYTES_IN_STATE],
            post: [0; N_BYTES_IN_STATE],
            squeeze_byte: [0; MAX_RATE],
        }
    }
}

/// The prover-side sponge run over the whole job list.
pub struct SpongeVRun {
    pub jobs: JobList,
    /// Active rows in coset order (`len == jobs.n_perms_total()`).
    pub rows: Vec<RowData>,
    /// Permutation input rows `[spread_state(200) | perm_id]` for
    /// [`crate::service::build_perm_witness`] (lane 0 real, splatted).
    pub perm_inputs: Vec<[PackedM31; N_BYTES_IN_STATE + 1]>,
    /// xor3 uses per non-first absorb row, for [`crate::tables_air::TableMultiplicities::add_sponge`].
    pub xor: Vec<Vec<[PackedM31; 2]>>,
    /// conv uses (block bytes + squeeze bytes), same destination.
    pub conv: Vec<[PackedM31; 2]>,
    /// Per-job full squeeze outputs (`shape.rate() · n_squeeze` bytes each).
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
        let rate = shape.rate();
        let f = shape.message_len % rate;
        let actual_n_absorb = shape.actual_n_absorb();

        // Padded absorb blocks.
        let mut blocks = vec![[0u8; MAX_RATE]; actual_n_absorb];
        for (i, &b) in message.iter().enumerate() {
            blocks[i / rate][i % rate] = b;
        }
        blocks[actual_n_absorb - 1][f] ^= DELIMITED_SUFFIX;
        blocks[actual_n_absorb - 1][rate - 1] ^= FINAL_BIT;

        let mut state = [0u8; N_BYTES_IN_STATE];
        let mut output = Vec::with_capacity(shape.output_len());

        for r in 0..shape.n_perms() {
            let absorb_active = if shape.has_message_capacity() {
                r < actual_n_absorb
            } else {
                r < shape.n_absorb
            };
            let squeeze_active = if shape.has_message_capacity() {
                r + 1 == actual_n_absorb
            } else {
                r + 1 >= shape.n_absorb
            };
            let unused_capacity_row = shape.has_message_capacity() && !absorb_active;
            let mut row = RowData {
                absorb_active,
                squeeze_active,
                prev_post: state,
                ..RowData::default()
            };
            if absorb_active {
                row.block_byte = blocks[r];
                if r + 1 == actual_n_absorb {
                    row.pad_gate[f..rate].fill(1);
                }
                for j in 0..rate {
                    conv.push([splat(blocks[r][j] as u32), spread_splat(blocks[r][j])]);
                }
                if r == 0 {
                    state[..rate].copy_from_slice(&blocks[0][..rate]);
                    // capacity stays 0.
                } else {
                    let mut uses = Vec::with_capacity(rate);
                    for j in 0..rate {
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
            let mut permutation_state = if unused_capacity_row {
                [0u8; N_BYTES_IN_STATE]
            } else {
                state
            };
            // Pre-permutation state → perm input (spread, lane-0 splat).
            let mut prow = [PackedM31::zero(); N_BYTES_IN_STATE + 1];
            for i in 0..N_BYTES_IN_STATE {
                prow[i] = spread_splat(permutation_state[i]);
            }
            prow[N_BYTES_IN_STATE] = splat((shape.perm_id_base + r) as u32);
            perm_inputs.push(prow);

            crate::sponge::native_keccak_f_bytes(&mut permutation_state);
            row.post = permutation_state;
            if !unused_capacity_row {
                state = permutation_state;
            }

            if squeeze_active {
                row.squeeze_byte[..rate].copy_from_slice(&row.post[..rate]);
                output.extend_from_slice(&row.post[..rate]);
                for j in 0..rate {
                    conv.push([splat(row.post[j] as u32), spread_splat(row.post[j])]);
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

/// Assemble the fixed-width base trace columns (commit order = AIR read order).
pub fn generate_base_trace(run: &SpongeVRun) -> Vec<ColEval> {
    let log_size = run.jobs.log_size();
    let rows = 1usize << log_size;
    let m = M31::from_u32_unchecked;
    let mut cols: Vec<Vec<M31>> = vec![vec![M31::zero(); rows]; run.jobs.n_base_cols()];
    for (r, row) in run.rows.iter().enumerate() {
        let mut c = 0usize;
        for j in 0..MAX_RATE {
            cols[c + j][r] = m(row.block_byte[j] as u32);
        }
        c += MAX_RATE;
        for j in 0..MAX_RATE {
            cols[c + j][r] = m(spread_u32(row.block_byte[j] as u32));
        }
        c += MAX_RATE;
        for j in 0..MAX_RATE {
            cols[c + j][r] = m(spread_u32(row.new_rate[j] as u32));
        }
        c += MAX_RATE;
        for i in 0..N_BYTES_IN_STATE {
            cols[c + i][r] = m(spread_u32(row.post[i] as u32));
        }
        c += N_BYTES_IN_STATE;
        for j in 0..MAX_RATE {
            cols[c + j][r] = m(row.squeeze_byte[j] as u32);
        }
        c += MAX_RATE;
        if run.jobs.has_message_capacity() {
            cols[c][r] = m(row.absorb_active as u32);
            c += 1;
            cols[c][r] = m(row.squeeze_active as u32);
            c += 1;
            for j in 0..MAX_RATE {
                cols[c + j][r] = m(row.pad_gate[j] as u32);
            }
            c += MAX_RATE;
        }
        debug_assert_eq!(c, run.jobs.n_base_cols());
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
            vec![ls; self.jobs.n_schedule_cols()],
            vec![ls; self.jobs.n_base_cols()],
            vec![ls; n_interaction_cols(&self.jobs)],
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
        // The capacity-prefix constraint has degree 4. Every other plain
        // constraint has degree 2 or less. Every tuple cell and denominator
        // has degree 1 or less, so batch-four LogUp constraints reach degree 5.
        // The log + 2 bound supports both cases.
        self.log_size() + 2
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let rel = &self.relations;
        let d = self.jobs.shape_digest();

        // The preprocessed schedule does not need boolean constraints.
        let is_active = eval.get_preprocessed_column(schedule_id(&d, "is_active"));
        let is_first = eval.get_preprocessed_column(schedule_id(&d, "is_first"));
        let is_absorb = eval.get_preprocessed_column(schedule_id(&d, "is_absorb"));
        let is_squeeze_out = eval.get_preprocessed_column(schedule_id(&d, "is_squeeze_out"));
        let is_shake128 = eval.get_preprocessed_column(schedule_id(&d, "is_shake128"));
        let perm_id = eval.get_preprocessed_column(schedule_id(&d, "perm_id"));
        let absorb_stream = eval.get_preprocessed_column(schedule_id(&d, "absorb_stream"));
        let squeeze_stream = eval.get_preprocessed_column(schedule_id(&d, "squeeze_stream"));
        let absorb_pos_base = eval.get_preprocessed_column(schedule_id(&d, "absorb_pos_base"));
        let squeeze_pos_base = eval.get_preprocessed_column(schedule_id(&d, "squeeze_pos_base"));
        let rate_gate: Vec<E::F> = (0..MAX_RATE)
            .map(|j| {
                if j < N_BYTES_IN_RATE {
                    is_active.clone()
                } else {
                    is_shake128.clone()
                }
            })
            .collect();
        let mut scheduled_pad_gate: Vec<E::F> = Vec::with_capacity(MAX_RATE);
        for (byte, alias) in pad_gate_aliases(&self.jobs).into_iter().enumerate() {
            let gate = match alias {
                None => E::F::zero(),
                Some(representative) if representative == byte => {
                    eval.get_preprocessed_column(schedule_id(&d, &format!("pad_gate_{byte}")))
                }
                Some(representative) => scheduled_pad_gate[representative].clone(),
            };
            scheduled_pad_gate.push(gate);
        }
        // Select the public actual length with capacity-only one-hot schedule
        // columns. Their sum is the capacity-mode gate. The selected constants
        // affect constraints and transcript, never the column bytes or ids.
        let mut capacity_mode = E::F::zero();
        let mut actual_message_len = E::F::zero();
        if self.jobs.has_message_capacity() {
            for (capacity_job, shape) in self
                .jobs
                .jobs
                .iter()
                .filter(|shape| shape.has_message_capacity())
                .enumerate()
            {
                let selector = eval.get_preprocessed_column(schedule_id(
                    &d,
                    &format!("capacity_job_{capacity_job}"),
                ));
                capacity_mode += selector.clone();
                actual_message_len +=
                    selector * E::F::from(BaseField::from(shape.message_len as u32));
            }
        }

        // Base columns (commit order).
        let block_byte: Vec<E::F> = (0..MAX_RATE).map(|_| eval.next_trace_mask()).collect();
        let block_spread: Vec<E::F> = (0..MAX_RATE).map(|_| eval.next_trace_mask()).collect();
        let new_rate: Vec<E::F> = (0..MAX_RATE).map(|_| eval.next_trace_mask()).collect();
        // post with the [-1, 0] chaining mask: [prev row's post, this row's post].
        let post_masks: Vec<[E::F; 2]> = (0..N_BYTES_IN_STATE)
            .map(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [-1, 0]))
            .collect();
        let post_prev = |i: usize| post_masks[i][0].clone();
        let post = |i: usize| post_masks[i][1].clone();
        let squeeze_byte: Vec<E::F> = (0..MAX_RATE).map(|_| eval.next_trace_mask()).collect();
        let (absorb_active, absorb_next, squeeze_active, pad_gate) =
            if self.jobs.has_message_capacity() {
                let absorb_masks = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
                let squeeze_active = eval.next_trace_mask();
                let pad_gate = (0..MAX_RATE).map(|_| eval.next_trace_mask()).collect();
                (
                    absorb_masks[0].clone(),
                    absorb_masks[1].clone(),
                    squeeze_active,
                    pad_gate,
                )
            } else {
                (
                    is_absorb.clone(),
                    E::F::zero(),
                    is_squeeze_out.clone(),
                    scheduled_pad_gate.clone(),
                )
            };
        let one = E::F::one();
        let fixed_mode = one.clone() - capacity_mode.clone();

        if self.jobs.has_message_capacity() {
            // The actual absorb rows are a non-empty monotone prefix of the
            // fixed capacity rows. `squeeze_active` is exactly its final row.
            eval.add_constraint(absorb_active.clone() * (one.clone() - absorb_active.clone()));
            eval.add_constraint(squeeze_active.clone() * (one.clone() - squeeze_active.clone()));
            eval.add_constraint(fixed_mode.clone() * (absorb_active.clone() - is_absorb.clone()));
            eval.add_constraint(
                fixed_mode.clone() * (squeeze_active.clone() - is_squeeze_out.clone()),
            );
            eval.add_constraint(
                capacity_mode.clone() * is_first.clone() * (absorb_active.clone() - one.clone()),
            );
            eval.add_constraint(
                capacity_mode.clone()
                    * (one.clone() - is_squeeze_out.clone())
                    * absorb_next.clone()
                    * (one.clone() - absorb_active.clone()),
            );
            eval.add_constraint(
                capacity_mode.clone()
                    * (squeeze_active.clone() - absorb_active.clone()
                        + (one.clone() - is_squeeze_out.clone()) * absorb_next.clone()),
            );
        }

        // Fixed jobs use the preprocessed padding schedule. Capacity jobs
        // commit the padding suffix and bind its rising edge to the public
        // length. The last rate byte is always in the suffix.
        for j in 0..MAX_RATE {
            if self.jobs.has_message_capacity() {
                eval.add_constraint(
                    fixed_mode.clone() * (pad_gate[j].clone() - scheduled_pad_gate[j].clone()),
                );
                eval.add_constraint(pad_gate[j].clone() * (one.clone() - pad_gate[j].clone()));
                eval.add_constraint(
                    capacity_mode.clone()
                        * pad_gate[j].clone()
                        * (one.clone() - squeeze_active.clone()),
                );
                eval.add_constraint(
                    capacity_mode.clone()
                        * (one.clone() - rate_gate[j].clone())
                        * pad_gate[j].clone(),
                );
                let previous_pad = if j == 0 {
                    E::F::zero()
                } else {
                    pad_gate[j - 1].clone()
                };
                let pad_start = pad_gate[j].clone() - previous_pad.clone();
                if j < N_BYTES_IN_RATE {
                    eval.add_constraint(
                        capacity_mode.clone() * previous_pad * (one.clone() - pad_gate[j].clone()),
                    );
                    let position = absorb_pos_base.clone() + E::F::from(BaseField::from(j as u32));
                    eval.add_constraint(
                        capacity_mode.clone()
                            * pad_start.clone()
                            * (position - actual_message_len.clone()),
                    );
                }
                let expected_pad = pad_start * E::F::from(BaseField::from(DELIMITED_SUFFIX as u32))
                    + if j == N_BYTES_IN_RATE - 1 {
                        squeeze_active.clone() * E::F::from(BaseField::from(FINAL_BIT as u32))
                    } else {
                        E::F::zero()
                    };
                eval.add_constraint(
                    capacity_mode.clone()
                        * pad_gate[j].clone()
                        * (block_byte[j].clone() - expected_pad),
                );
            }
            let previous_pad = if j == 0 {
                E::F::zero()
            } else {
                scheduled_pad_gate[j - 1].clone()
            };
            let pad_start = scheduled_pad_gate[j].clone() - previous_pad;
            let final_gate = if j == N_BYTES_IN_RATE - 1 {
                is_active.clone() - is_shake128.clone()
            } else if j == N_BYTES_IN_SHAKE128_RATE - 1 {
                is_shake128.clone()
            } else {
                E::F::zero()
            };
            let expected_pad = pad_start * E::F::from(BaseField::from(DELIMITED_SUFFIX as u32))
                + final_gate * E::F::from(BaseField::from(FINAL_BIT as u32));
            eval.add_constraint(
                fixed_mode.clone()
                    * scheduled_pad_gate[j].clone()
                    * (block_byte[j].clone() - expected_pad),
            );
        }
        if self.jobs.has_message_capacity() {
            eval.add_constraint(
                capacity_mode.clone()
                    * (pad_gate[N_BYTES_IN_RATE - 1].clone() - squeeze_active.clone()),
            );
            let inactive_capacity = capacity_mode.clone() * (one.clone() - absorb_active.clone());
            for j in 0..MAX_RATE {
                // Every cell unused by the fixed-capacity message is
                // canonical. The unused permutation itself is tied to the
                // zero Keccak input below, which uniquely fixes `post`.
                eval.add_constraint(inactive_capacity.clone() * block_byte[j].clone());
                eval.add_constraint(inactive_capacity.clone() * block_spread[j].clone());
                eval.add_constraint(inactive_capacity.clone() * new_rate[j].clone());
                let outside_rate = capacity_mode.clone() * (one.clone() - rate_gate[j].clone());
                eval.add_constraint(outside_rate.clone() * block_byte[j].clone());
                eval.add_constraint(outside_rate.clone() * block_spread[j].clone());
                eval.add_constraint(outside_rate.clone() * new_rate[j].clone());
                eval.add_constraint(outside_rate * squeeze_byte[j].clone());
                eval.add_constraint(
                    capacity_mode.clone()
                        * (one.clone() - squeeze_active.clone())
                        * squeeze_byte[j].clone(),
                );
                eval.add_constraint(capacity_mode.clone() * is_first.clone() * new_rate[j].clone());
            }
        }

        // 1. conv: bind every absorb-row block byte to its spread limb (+).
        for j in 0..MAX_RATE {
            eval.add_to_relation(RelationEntry::base(
                &rel.conv,
                absorb_active.clone() * rate_gate[j].clone(),
                &[block_byte[j].clone(), block_spread[j].clone()],
            ));
        }
        // 2. HashIo: consume the real message bytes (−). The message gate is
        // `absorb_active·rate_gate[j] − pad_gate[j]` (1 on message positions).
        for j in 0..MAX_RATE {
            let jf = E::F::from(BaseField::from(j as u32));
            eval.add_to_relation(RelationEntry::base(
                &rel.hash_io,
                -(absorb_active.clone() * rate_gate[j].clone() - pad_gate[j].clone()),
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
        for j in 0..MAX_RATE {
            eval.add_to_relation(RelationEntry::base(
                &rel.xor3,
                (absorb_active.clone() - is_first.clone()) * rate_gate[j].clone(),
                &[post_prev(j) + block_spread[j].clone(), new_rate[j].clone()],
            ));
        }
        // 4. KeccakState: mode-gated 136/168-byte IN variants (+) and OUT (−).
        // Keeping each variant's tuple linear avoids a conditional product in
        // the relation denominator.
        let mk_state =
            |rate_len: usize, rate: &dyn Fn(usize) -> E::F, cap: &dyn Fn(usize) -> E::F| {
                let mut t: Vec<E::F> = Vec::with_capacity(KECCAK_STATE_ARITY);
                t.push(perm_id.clone());
                t.push(E::F::zero()); // direction::IN
                for j in 0..rate_len {
                    t.push(rate(j));
                }
                for i in rate_len..N_BYTES_IN_STATE {
                    t.push(cap(i));
                }
                t
            };
        let shake256 = is_active.clone() - is_shake128.clone();
        // First perm of a job: rate = block0 spread, capacity = 0.
        let in_first_256 = mk_state(N_BYTES_IN_RATE, &|j| block_spread[j].clone(), &|_| {
            E::F::zero()
        });
        eval.add_to_relation(RelationEntry::base(
            &rel.keccak_state,
            is_first.clone() * shake256.clone(),
            &in_first_256,
        ));
        let in_first_128 = mk_state(
            N_BYTES_IN_SHAKE128_RATE,
            &|j| block_spread[j].clone(),
            &|_| E::F::zero(),
        );
        eval.add_to_relation(RelationEntry::base(
            &rel.keccak_state,
            is_first.clone() * is_shake128.clone(),
            &in_first_128,
        ));
        // Later absorb perms: rate = new_rate, capacity chains from prev post.
        let in_absorb_256 = mk_state(N_BYTES_IN_RATE, &|j| new_rate[j].clone(), &post_prev);
        eval.add_to_relation(RelationEntry::base(
            &rel.keccak_state,
            (absorb_active.clone() - is_first.clone()) * shake256,
            &in_absorb_256,
        ));
        let in_absorb_128 = mk_state(
            N_BYTES_IN_SHAKE128_RATE,
            &|j| new_rate[j].clone(),
            &post_prev,
        );
        eval.add_to_relation(RelationEntry::base(
            &rel.keccak_state,
            (absorb_active.clone() - is_first.clone()) * is_shake128,
            &in_absorb_128,
        ));
        // extra squeeze perms: the whole pre-state chains from prev post.
        let in_squeeze = mk_state(MAX_RATE, &post_prev, &post_prev);
        eval.add_to_relation(RelationEntry::base(
            &rel.keccak_state,
            is_active.clone() - is_absorb.clone(),
            &in_squeeze,
        ));
        if self.jobs.has_message_capacity() {
            // Allocated-but-unused rows prove one canonical independent
            // Keccak-f(0) invocation. They cannot carry a hidden chain or
            // unconstrained state even though they do not absorb/squeeze.
            let in_unused = mk_state(MAX_RATE, &|_| E::F::zero(), &|_| E::F::zero());
            eval.add_to_relation(RelationEntry::base(
                &rel.keccak_state,
                capacity_mode.clone() * (one.clone() - absorb_active.clone()),
                &in_unused,
            ));
        }
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
        for j in 0..MAX_RATE {
            eval.add_to_relation(RelationEntry::base(
                &rel.conv,
                squeeze_active.clone() * rate_gate[j].clone(),
                &[squeeze_byte[j].clone(), post(j)],
            ));
        }
        // 6. HashIo: yield the squeeze bytes (+).
        for j in 0..MAX_RATE {
            let jf = E::F::from(BaseField::from(j as u32));
            eval.add_to_relation(RelationEntry::base(
                &rel.hash_io,
                squeeze_active.clone() * rate_gate[j].clone(),
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

/// The per-row logup fractions in EXACTLY the AIR's emission order.
/// Zero-multiplicity entries are `(0, 1)`. This is sound because the batch constraint
/// evaluates the symbolic multiplicity (a preprocessed gate that IS zero
/// there), so the committed accumulator step is 0 either way.
fn row_fracs(
    rel: &KeccakRelations,
    sched: &RowSched,
    row: &RowData,
    has_message_capacity: bool,
) -> Vec<(SecureField, SecureField)> {
    let zero = SecureField::zero();
    let one = SecureField::one();
    let m = M31::from_u32_unchecked;
    let sp = |b: u8| m(spread_u32(b as u32));
    let mut out: Vec<(SecureField, SecureField)> =
        Vec::with_capacity(N_LOGUP_ENTRIES + usize::from(has_message_capacity));

    let rate = if sched.shake128 {
        N_BYTES_IN_SHAKE128_RATE
    } else {
        N_BYTES_IN_RATE
    };

    // 1. conv block (+is_absorb·rate_gate).
    for j in 0..MAX_RATE {
        if row.absorb_active && j < rate {
            let den: SecureField = rel
                .conv
                .combine(&[m(row.block_byte[j] as u32), sp(row.block_byte[j])]);
            out.push((one, den));
        } else {
            out.push((zero, one));
        }
    }
    // 2. io absorb consume (−(is_absorb·rate_gate − pad_gate)).
    for j in 0..MAX_RATE {
        if row.absorb_active && j < rate && row.pad_gate[j] == 0 {
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
    // 3. xor3 (+(is_absorb − is_first)·rate_gate).
    for j in 0..MAX_RATE {
        if row.absorb_active && !sched.first && j < rate {
            let key = sp(row.prev_post[j]) + sp(row.block_byte[j]);
            let den: SecureField = rel.xor3.combine(&[key, sp(row.new_rate[j])]);
            out.push((one, den));
        } else {
            out.push((zero, one));
        }
    }
    // 4. state: mode-gated IN_first/IN_absorb, IN_squeeze, OUT.
    let state_tuple = |dir: u32,
                       rate_len: usize,
                       rate_values: &dyn Fn(usize) -> M31,
                       cap: &dyn Fn(usize) -> M31| {
        let mut t = Vec::with_capacity(KECCAK_STATE_ARITY);
        t.push(m(sched.perm_id));
        t.push(m(dir));
        for j in 0..rate_len {
            t.push(rate_values(j));
        }
        for i in rate_len..N_BYTES_IN_STATE {
            t.push(cap(i));
        }
        t
    };
    if sched.first && !sched.shake128 {
        let t = state_tuple(0, N_BYTES_IN_RATE, &|j| sp(row.block_byte[j]), &|_| {
            M31::zero()
        });
        out.push((one, rel.keccak_state.combine(&t)));
    } else {
        out.push((zero, one));
    }
    if sched.first && sched.shake128 {
        let t = state_tuple(
            0,
            N_BYTES_IN_SHAKE128_RATE,
            &|j| sp(row.block_byte[j]),
            &|_| M31::zero(),
        );
        out.push((one, rel.keccak_state.combine(&t)));
    } else {
        out.push((zero, one));
    }
    if row.absorb_active && !sched.first && !sched.shake128 {
        let t = state_tuple(0, N_BYTES_IN_RATE, &|j| sp(row.new_rate[j]), &|i| {
            sp(row.prev_post[i])
        });
        out.push((one, rel.keccak_state.combine(&t)));
    } else {
        out.push((zero, one));
    }
    if row.absorb_active && !sched.first && sched.shake128 {
        let t = state_tuple(
            0,
            N_BYTES_IN_SHAKE128_RATE,
            &|j| sp(row.new_rate[j]),
            &|i| sp(row.prev_post[i]),
        );
        out.push((one, rel.keccak_state.combine(&t)));
    } else {
        out.push((zero, one));
    }
    if !sched.absorb {
        let t = state_tuple(0, MAX_RATE, &|j| sp(row.prev_post[j]), &|i| {
            sp(row.prev_post[i])
        });
        out.push((one, rel.keccak_state.combine(&t)));
    } else {
        out.push((zero, one));
    }
    if has_message_capacity {
        if sched.capacity_mode && !row.absorb_active {
            let t = state_tuple(0, MAX_RATE, &|_| M31::zero(), &|_| M31::zero());
            out.push((one, rel.keccak_state.combine(&t)));
        } else {
            out.push((zero, one));
        }
    }
    {
        let t = state_tuple(1, MAX_RATE, &|j| sp(row.post[j]), &|i| sp(row.post[i]));
        out.push((-one, rel.keccak_state.combine(&t)));
    }
    // 5. conv squeeze (+is_squeeze_out).
    for j in 0..MAX_RATE {
        if row.squeeze_active && j < rate {
            let den: SecureField = rel
                .conv
                .combine(&[m(row.squeeze_byte[j] as u32), sp(row.squeeze_byte[j])]);
            out.push((one, den));
        } else {
            out.push((zero, one));
        }
    }
    // 6. io squeeze yield (+is_squeeze_out).
    for j in 0..MAX_RATE {
        if row.squeeze_active && j < rate {
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
    debug_assert_eq!(
        out.len(),
        N_LOGUP_ENTRIES + usize::from(has_message_capacity)
    );
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

    // Per active coset row: all `(num, den)` fractions.
    let fracs: Vec<Vec<(SecureField, SecureField)>> = sched
        .iter()
        .zip(&run.rows)
        .map(|(s, r)| row_fracs(rel, s, r, run.jobs.has_message_capacity()))
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
    let n_entries = n_logup_entries(&run.jobs);
    for k in 0..n_entries.div_ceil(LOGUP_BATCH) {
        let lo = k * LOGUP_BATCH;
        let hi = (lo + LOGUP_BATCH).min(n_entries);
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
                    d_acc *= d;
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn schedule_reuses_equal_padding_masks_and_omits_derived_columns() {
        let jobs = JobList::new([
            Shape::new(16, 1, 0, 1),
            Shape::new(34, 1, 2, 3),
            Shape::new(48, 1, 4, 5),
            Shape::new(86, 1, 6, 7),
            Shape::shake128(16, 1, 8, 9),
        ]);
        let aliases = pad_gate_aliases(&jobs);
        assert!(aliases[..16].iter().all(Option::is_none));
        for (range, representative) in [
            (16..34, 16),
            (34..48, 34),
            (48..86, 48),
            (86..136, 86),
            (136..168, 136),
        ] {
            assert!(aliases[range]
                .iter()
                .all(|alias| *alias == Some(representative)));
        }

        let ids = schedule_ids(&jobs);
        assert_eq!(jobs.n_schedule_cols(), N_SCHEDULE_COLS + 5);
        assert_eq!(ids.len(), jobs.n_schedule_cols());
        assert_eq!(gen_schedule_preprocessed(&jobs).len(), ids.len());
        assert!(ids.iter().all(|id| !id.id.contains("rate_gate_")));
        assert!(ids.iter().all(|id| !id.id.contains("pad_val_")));
        for representative in [16, 34, 48, 86, 136] {
            assert!(ids
                .iter()
                .any(|id| id.id.ends_with(&format!("/pad_gate_{representative}"))));
        }
    }

    #[test]
    fn capacity_jobs_do_not_commit_unused_fixed_padding_masks() {
        let jobs = JobList::new([Shape::with_message_capacity(303, 1_024, 1, 0, 1).unwrap()]);
        assert!(pad_gate_aliases(&jobs).iter().all(Option::is_none));
        assert_eq!(jobs.n_schedule_cols(), N_SCHEDULE_COLS + 1);
        let ids = schedule_ids(&jobs);
        assert!(ids.iter().all(|id| !id.id.contains("pad_gate_")));
        assert!(ids.iter().all(|id| !id.id.ends_with("/capacity_mode")));
        assert!(ids.iter().all(|id| !id.id.ends_with("/capacity_last")));
        assert!(ids.iter().any(|id| id.id.ends_with("/capacity_job_0")));
    }

    #[test]
    fn derived_fixed_padding_values_match_fips_padding() {
        let shapes = vec![
            Shape::new(0, 1, 0, 1),
            Shape::new(N_BYTES_IN_RATE - 1, 1, 2, 3),
            Shape::shake128(0, 1, 4, 5),
            Shape::shake128(N_BYTES_IN_SHAKE128_RATE - 1, 1, 6, 7),
        ];
        let messages = shapes
            .iter()
            .map(|shape| vec![0; shape.message_len])
            .collect::<Vec<_>>();
        let jobs = JobList::new(shapes);
        let run = generate_jobs(&jobs, &messages);
        let schedule = build_schedule(&jobs);

        for (scheduled, row) in schedule.iter().zip(&run.rows) {
            for byte in 0..MAX_RATE {
                let previous = byte
                    .checked_sub(1)
                    .map_or(0, |previous| scheduled.pad_gate[previous]);
                let pad_start = i16::from(scheduled.pad_gate[byte]) - i16::from(previous);
                let final_gate = usize::from(
                    (byte == N_BYTES_IN_RATE - 1 && !scheduled.shake128)
                        || (byte == N_BYTES_IN_SHAKE128_RATE - 1 && scheduled.shake128),
                ) as i16;
                let expected = if scheduled.pad_gate[byte] == 0 {
                    0
                } else {
                    (pad_start * i16::from(DELIMITED_SUFFIX) + final_gate * i16::from(FINAL_BIT))
                        as u8
                };
                assert_eq!(row.block_byte[byte], expected);
            }
        }
    }
}
