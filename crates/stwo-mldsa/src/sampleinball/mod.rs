//! `sampleinball_fsm` — FIPS 204 [CHAL] SampleInBall (Alg 29) over the witnessed
//! SHAKE squeeze stream.
//!
//! Semantic oracle: [`crate::reference::sample_in_ball`]. The reference squeezes
//! `8 + 8·N` bytes: the first 8 are the sign source `s`; then for each target
//! `i ∈ [N−τ, N)` it rejection-samples `j ← byte` (reject while `byte > i`) and
//! sets `c[i] = c[j]; c[j] = (−1)^{s&1}; s ≫= 1`.
//!
//! ## Layout — two stacked row groups, one committed AIR (log_size ~9)
//!
//! 1. **stream group** (one row per squeezed byte the sampler CONSUMES): tracks
//!    the FSM target index `i` and the accept/reject decision, consuming each byte
//!    from `HashIoRelation(STREAM_ID_SIB_SQUEEZE, byte_pos, byte)`. The first 8
//!    bytes are the sign source (no placement); each later placement byte is
//!    accepted iff `byte ≤ i` (proven by `(i − byte) ∈ [0,256)`) or rejected iff
//!    `byte > i` (proven by `(byte − i − 1) ∈ [0,256)`), advancing `i` on accept.
//! 2. **c group** (`N` rows): the challenge coefficients, each ternary
//!    (`c ∈ {−1,0,1}` via a `{0,1,2}` membership lookup on `c+1`), with a running
//!    `Σ c²` accumulator gated to `τ` on the final c-row, and each `c[m]` bound
//!    to the coeffs C-group cell via [`CCellRelation`]`(m, c)`.
//!
//! ## Soundness scope (documented)
//!
//! This component proves, from the honest witness: (a) the FSM's accept/reject
//! decisions match the rejection-sampling rule `byte ≤ i` **exactly** (the
//! security-critical tie of `c`'s support to the stream); (b) `c` is ternary
//! with **exactly τ** nonzeros (Σc² = τ); (c) `c` equals the coeffs-bound
//! coefficients; (d) — **the swap-placement gate** — `c` equals SampleInBall's
//! Fisher–Yates array replayed from the (bound) squeeze stream, via an
//! address-sorted **offline-memory** permutation argument over the [`relations`]
//! `Mem` channel. Without (d) an adversary could permute the placement of the
//! ±1's (same multiset, same support size, same Σc²=τ) and pass (a)–(c); the
//! Mem replay derives placement from the UNCHANGED stream and disagrees with any
//! permuted `c`. The stream bytes are test-balanced here; M6 connects the proven
//! sponge squeeze.
//!
//! ## Offline-memory (swap replay) — Cairo-style address-then-timestamp sort
//!
//! Model `c[0..N]` as a memory with addresses `0..N`. Replaying
//! [`crate::reference::sample_in_ball`] EXACTLY yields an ordered access list
//! (`ts` strictly increasing): N init writes `(k,0)`, then per step τ a READ
//! `(j,old_j)` + WRITE `(i,old_j)` + WRITE `(j,sign)`, then N final reads
//! `(k,c_final[k])`. The final reads consume `COL_C` (the same committed `c` the
//! ternary/τ/CCell layer pins), so the array's final state IS `c`.
//!
//! Two views live on the same `n_accesses = N + 3τ + N = 659` rows: an
//! **unsorted** access (emission order) yielded `+` into `Mem`, and the same
//! multiset **sorted** by `(addr, ts)` required `−`. Equal multisets ⇒ the two
//! Mem contributions self-cancel (INTERNAL balance). The sorted trace then
//! enforces, per consecutive pair (all constraints degree ≤ 2, see worksheet in
//! [`SibEval::evaluate`]): non-decreasing addr, strictly increasing ts within a
//! cell, read-value continuity (a READ sees the previous access's value), and
//! that the first access of each cell is an init WRITE of 0. Last-writer-wins by
//! ts + the permutation ⇒ the committed `c` is the true SampleInBall output.

#![allow(clippy::needless_range_loop)]

pub mod proof;
pub mod relations;
pub mod tables;

use num_traits::One;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::prover::backend::simd::m31::N_LANES;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    INTERACTION_TRACE_IDX,
};

use crate::air_util::{circle_row_to_coset, col_eval, m31, ColEval};
use crate::binding::STREAM_ID_SIB_SQUEEZE;
use crate::constants::{N, TAU};
use crate::witness::MlDsaWitness;
use relations::SibRelations;
use tables::RcUses;

/// Sign bytes at the head of the squeeze stream.
pub const SIGN_BYTES: usize = 8;

// The stream stage is bounded by the honest CONSUMED squeeze length (τ placements
// + rejections, < 256 in practice; see `stream_len`). The component is sized to
// that length + the c stage (N = 256), padded to a power of two.

/// Base column indices.
const COL_ENABLER: usize = 0;
// Stream stage columns:
const COL_BYTE: usize = 1; // consumed squeeze byte
const COL_I: usize = 2; // current target index i
const COL_ACCEPT: usize = 3; // 1 iff this byte is accepted (byte ≤ i)
const COL_REJECT: usize = 4; // 1 iff placement byte rejected (byte > i); degree-1 gate
const COL_ACCEPT_HI: usize = 5; // 8-bit hi of (i − byte) ∈ [0,256) on accept rows
const COL_REJECT_HI: usize = 6; // 8-bit hi of (byte − i − 1) ∈ [0,256) on reject rows
// c stage columns:
const COL_C: usize = 7; // challenge coefficient value (signed)
const COL_CSQ: usize = 8; // c² (witnessed so the accumulator constraint stays deg 1)
const COL_CSQ_ACC: usize = 9; // running Σ c²
// Offline-memory (swap replay) columns — active on the n_accesses access rows.
const COL_U_ADDR: usize = 10; // unsorted access address
const COL_U_VAL: usize = 11; // unsorted access value (enc_signed)
const COL_U_TS: usize = 12; // unsorted access timestamp
const COL_U_WRITE: usize = 13; // 1 iff unsorted access is a write
const COL_S_ADDR: usize = 14; // sorted access address
const COL_S_VAL: usize = 15; // sorted access value
const COL_S_TS: usize = 16; // sorted access timestamp
const COL_S_WRITE: usize = 17; // 1 iff sorted access is a write
const COL_S_SAME: usize = 18; // 1 iff sorted addr == previous sorted addr (same cell)
const COL_S_DADDR: usize = 19; // sorted addr − previous sorted addr ∈ [0,256) (rc8)
const COL_S_DADDR_INV: usize = 20; // inverse gadget: daddr·inv == 1−same
const COL_S_DTS: usize = 21; // (ts − prev_ts − 1) within a cell ∈ [0,2048) (rc11)
const COL_S_SR_SAME: usize = 22; // same·s_read (witnessed to keep continuity deg 2)
const COL_S_FOC: usize = 23; // first-of-cell = is_access·(1−same) (witnessed, deg 2 pin)
// Sign-bit columns — the 8 bits of each sign row's byte (only on the 8 sign rows;
// 0 elsewhere). These feed the SignBit channel that ties write-j values to the
// FIPS sign bits (`c[j] = (−1)^bit`), closing part of the free-access-list hole.
const COL_SIGN_BIT0: usize = 24;
/// Number of sign-bit columns (one per bit of a sign byte).
pub const SIGN_BIT_COLS: usize = 8;
/// Total base columns.
pub const N_BASE_COLS: usize = COL_SIGN_BIT0 + SIGN_BIT_COLS; // 32

/// Core (unsorted) offline-memory accesses laid out on their own rows: N init
/// writes + 3 per step (read + 2 writes). The N FINAL reads are NOT counted here
/// — they are emitted co-located on the c-stage rows so the read value IS `COL_C`
/// (the coeffs-bound `c`), which is what pins the array's final state to `c`.
pub const N_CORE: usize = N + 3 * TAU;

/// Total offline-memory accesses (core + N final reads). Drives the SORTED
/// trace row count and the sib log_size.
pub const N_ACCESSES: usize = N_CORE + N;

/// Namespaced preprocessed id: the SIB schedule columns are WITNESS-dependent
/// (they encode the rejection-sampling schedule of one specific signature), so
/// two hosted ML-DSA instances must not share them under tree-0 id dedup.
pub(crate) fn pre_id_ns(ns: &str, name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId { id: format!("{}mldsa_sib_{name}", crate::sponge_link::ns_prefix(ns)) }
}

fn sign_mask_name(u: usize) -> String {
    format!("sign_mask_{u}")
}

/// Preprocessed ids in commit order (legacy single-instance ids).
pub fn sib_preprocessed_ids() -> Vec<PreProcessedColumnId> {
    sib_preprocessed_ids_ns("")
}

/// Preprocessed ids in commit order, under an instance namespace.
pub fn sib_preprocessed_ids_ns(ns: &str) -> Vec<PreProcessedColumnId> {
    let pre_id = |name: &str| pre_id_ns(ns, name);
    let mut ids = vec![
        pre_id("is_stream"),
        pre_id("is_placement"),
        pre_id("is_c"),
        pre_id("acc_start"),
        pre_id("c_last"),
        pre_id("c_bind_id"),
        pre_id("byte_pos"),
        pre_id("is_core"),
        pre_id("is_sorted"),
        pre_id("sorted_start"),
        pre_id("ts_final"),
        // FSM↔memory schedule pins (close the free-access-list hole): the core-row
        // role partition, canonical timestamps, init addresses, and step ordinals.
        pre_id("step_no"),
        pre_id("is_init"),
        pre_id("is_read_row"),
        pre_id("is_wr_i_row"),
        pre_id("is_wr_j_row"),
        pre_id("core_ts"),
        pre_id("init_addr"),
        pre_id("is_sign"),
    ];
    for u in 0..SIGN_BIT_COLS {
        ids.push(pre_id(&sign_mask_name(u)));
    }
    ids
}

/// Honest stream length: the number of squeeze bytes the rejection sampler
/// actually CONSUMES (8 sign bytes + placement bytes until τ accepts). The
/// transcript squeezes a generous `8 + 8·N`, but only this prefix drives `c`.
pub fn stream_len(witness: &MlDsaWitness) -> usize {
    let stream = &witness.sponge.sample_in_ball_squeezed;
    let mut i = (N - TAU) as u32;
    let mut placed = 0usize;
    let mut pos = SIGN_BYTES;
    while placed < TAU {
        let b = stream[pos] as u32;
        pos += 1;
        if b <= i {
            i += 1;
            placed += 1;
        }
    }
    pos
}

/// Reconstruct the per-stream-row FSM state from the reference stream.
struct StreamRow {
    byte: u32,
    i: u32,
    accept: bool,
}

fn stream_rows(witness: &MlDsaWitness) -> Vec<StreamRow> {
    let stream = &witness.sponge.sample_in_ball_squeezed;
    let slen = stream_len(witness);
    let mut out = Vec::with_capacity(slen);
    let mut i = (N - TAU) as u32;
    for pos in 0..slen {
        let b = stream[pos] as u32;
        if pos < SIGN_BYTES {
            // Sign-collection rows: i stays at N−τ, byte recorded, no accept.
            out.push(StreamRow { byte: b, i, accept: false });
        } else {
            let accept = b <= i;
            out.push(StreamRow { byte: b, i, accept });
            if accept {
                i += 1;
            }
        }
    }
    out
}

// =============================================================================
// Offline-memory replay: reproduce reference::sample_in_ball's array accesses.
// =============================================================================

/// One `(addr, value, ts, is_write)` memory access. `value` is the SIGNED cell
/// content (`{−1,0,1}`); it is encoded via `enc_signed` at emission.
#[derive(Clone, Copy)]
struct Access {
    addr: u32,
    value: i128,
    ts: u32,
    is_write: bool,
}

/// Replay `reference::sample_in_ball` from the witnessed squeeze stream, EXACTLY
/// reproducing the Fisher–Yates array mutations, and return the ordered access
/// list (INIT writes, per-step read+2 writes, FINAL reads). `ts` is strictly
/// increasing across the returned list. The FINAL reads return `c_final[k]`,
/// which must equal the committed `witness.digits.c` (the coeffs-bound value).
fn mem_accesses(witness: &MlDsaWitness) -> Vec<Access> {
    let stream = &witness.sponge.sample_in_ball_squeezed;
    let mut c = [0i128; N];
    let sign_bits = u64::from_le_bytes(stream[0..SIGN_BYTES].try_into().expect("8 bytes"));
    let mut sign = sign_bits;
    let mut pos = SIGN_BYTES;

    let mut out = Vec::with_capacity(N_ACCESSES);
    let mut ts: u32 = 0;

    // INIT: write (k, 0) for k in 0..N.
    for k in 0..N {
        out.push(Access { addr: k as u32, value: 0, ts, is_write: true });
        ts += 1;
    }

    // Per step: rejection-sample j ≤ i, then read (j,old_j), write (i,old_j),
    // write (j, sign). Mirrors reference::sample_in_ball's write order EXACTLY.
    for i in (N - TAU)..N {
        let j = loop {
            let byte = stream[pos] as usize;
            pos += 1;
            if byte <= i {
                break byte;
            }
        };
        let old_j = c[j];
        out.push(Access { addr: j as u32, value: old_j, ts, is_write: false });
        ts += 1;
        c[i] = old_j;
        out.push(Access { addr: i as u32, value: c[i], ts, is_write: true });
        ts += 1;
        let s: i128 = if sign & 1 == 1 { -1 } else { 1 };
        c[j] = s;
        out.push(Access { addr: j as u32, value: c[j], ts, is_write: true });
        ts += 1;
        sign >>= 1;
    }

    // FINAL: read (k, c_final[k]) for k in 0..N — the TRUE replayed array. The
    // AIR's FINAL-read emission instead uses the COMMITTED COL_C value; on an
    // honest witness they agree, and a tampered `c` (e.g. a permuted placement)
    // makes the sorted-view (true) and unsorted-final (committed) Mem fractions
    // disagree ⇒ the internal Mem balance breaks ⇒ verify rejects. (No assert
    // here so the Mem gate — not a witness-consistency panic — is what catches it.)
    for k in 0..N {
        out.push(Access { addr: k as u32, value: c[k], ts, is_write: false });
        ts += 1;
    }

    debug_assert_eq!(out.len(), N_ACCESSES);
    out
}

/// The unsorted accesses (emission order) and their (addr, ts)-sorted view.
struct MemTrace {
    unsorted: Vec<Access>,
    sorted: Vec<Access>,
}

thread_local! {
    /// Test-attack hook, DO NOT USE outside integration tests. When set, the CORE
    /// (unsorted) access list — the first `N_CORE` accesses — is replaced by this
    /// forged list instead of the honest `mem_accesses` replay, letting a test
    /// commit a memory-consistent-but-FSM-mismatched history to prove the
    /// Swap/StepVal/SignBit channels are load-bearing. The final `N` FINAL reads
    /// stay honest (derived from the committed `c`) so the Mem internal balance is
    /// NOT what catches the forgery. Cleared automatically by `ForgedCoreGuard`.
    static FORGED_CORE: core::cell::RefCell<Option<Vec<Access>>> =
        const { core::cell::RefCell::new(None) };
}

/// Test-attack hook, DO NOT USE outside integration tests. Installs a forged CORE
/// access list `(addr, value, ts, is_write)` (must be exactly `N_CORE` entries)
/// for the duration of the returned guard; the honest FINAL reads are appended
/// unchanged. Used only by the `negative_forged_access_list` acceptance test.
#[doc(hidden)]
pub struct ForgedCoreGuard;

impl Drop for ForgedCoreGuard {
    fn drop(&mut self) {
        FORGED_CORE.with(|f| *f.borrow_mut() = None);
    }
}

/// Test-attack hook, DO NOT USE outside integration tests. Returns the honest
/// CORE access list `(addr, value, ts, is_write)` (the first `N_CORE` accesses)
/// so a test can mutate one entry and reinstall it via [`install_forged_core`].
#[doc(hidden)]
pub fn honest_core_accesses(witness: &MlDsaWitness) -> Vec<(u32, i128, u32, bool)> {
    mem_accesses(witness)
        .into_iter()
        .take(N_CORE)
        .map(|a| (a.addr, a.value, a.ts, a.is_write))
        .collect()
}

/// Test-attack hook, DO NOT USE outside integration tests. See [`ForgedCoreGuard`].
#[doc(hidden)]
pub fn install_forged_core(accesses: Vec<(u32, i128, u32, bool)>) -> ForgedCoreGuard {
    let forged: Vec<Access> = accesses
        .into_iter()
        .map(|(addr, value, ts, is_write)| Access { addr, value, ts, is_write })
        .collect();
    FORGED_CORE.with(|f| *f.borrow_mut() = Some(forged));
    ForgedCoreGuard
}

fn mem_trace(witness: &MlDsaWitness) -> MemTrace {
    let mut unsorted = mem_accesses(witness);
    // Test-attack hook: swap the CORE accesses (rows 0..N_CORE) for a forged list,
    // keeping the honest FINAL reads (rows N_CORE..N_ACCESSES) so the Mem balance
    // against the committed `c` is untouched — the FSM↔memory channels must catch it.
    FORGED_CORE.with(|f| {
        if let Some(forged) = f.borrow().as_ref() {
            assert_eq!(forged.len(), N_CORE, "forged core list must have N_CORE entries");
            unsorted[..N_CORE].clone_from_slice(forged);
        }
    });
    let mut sorted = unsorted.clone();
    sorted.sort_by_key(|a| (a.addr, a.ts));
    MemTrace { unsorted, sorted }
}

// =============================================================================
// Preprocessed trace.
// =============================================================================

pub fn gen_sib_preprocessed(witness: &MlDsaWitness, log_size: u32) -> Vec<ColEval> {
    let rows = 1usize << log_size;
    let slen = stream_len(witness);

    let mut is_stream = vec![m31(0); rows];
    let mut is_placement = vec![m31(0); rows];
    let mut is_c = vec![m31(0); rows];
    let mut acc_start = vec![m31(0); rows];
    let mut c_last = vec![m31(0); rows];
    let mut c_bind_id = vec![m31(0); rows];
    let mut byte_pos = vec![m31(0); rows];
    let mut is_core = vec![m31(0); rows];
    let mut is_sorted = vec![m31(0); rows];
    let mut sorted_start = vec![m31(0); rows];
    let mut ts_final = vec![m31(0); rows];
    // FSM↔memory schedule pins.
    let mut step_no = vec![m31(0); rows];
    let mut is_init = vec![m31(0); rows];
    let mut is_read_row = vec![m31(0); rows];
    let mut is_wr_i_row = vec![m31(0); rows];
    let mut is_wr_j_row = vec![m31(0); rows];
    let mut core_ts = vec![m31(0); rows];
    let mut init_addr = vec![m31(0); rows];
    let mut is_sign = vec![m31(0); rows];
    let mut sign_mask: Vec<Vec<M31>> =
        (0..SIGN_BIT_COLS).map(|_| vec![m31(0); rows]).collect();

    for pos in 0..slen {
        is_stream[pos] = m31(1);
        if pos >= SIGN_BYTES {
            is_placement[pos] = m31(1);
        } else {
            // Sign rows are the first SIGN_BYTES stream rows. Mask bit u of sign
            // row b (byte b) is used iff step 8b+u < τ (the sampler consumes one
            // sign bit per placement, LE across the 8-byte sign source).
            is_sign[pos] = m31(1);
            for u in 0..SIGN_BIT_COLS {
                let step = SIGN_BIT_COLS * pos + u;
                sign_mask[u][pos] = m31(u32::from(step < TAU));
            }
        }
        byte_pos[pos] = m31(pos as u32);
    }
    for m in 0..N {
        let row = slen + m;
        is_c[row] = m31(1);
        c_bind_id[row] = m31(m as u32);
        // FINAL-read timestamp for address m (co-located on the c-stage row).
        ts_final[row] = m31((N_CORE + m) as u32);
    }
    acc_start[0] = m31(1); // coset row 0 zeroes the Σc² accumulator wraparound.
    if N > 0 {
        c_last[slen + N - 1] = m31(1);
    }

    // Unsorted CORE accesses occupy rows 0..N_CORE; the SORTED view occupies
    // rows 0..N_ACCESSES. sorted_start gates the first sorted-pair transition
    // (coset row 0 wraparound of the [-1,0] mask). The CORE-row layout MATCHES
    // `mem_accesses` EXACTLY: rows 0..N are init writes (addr=k, val=0, ts=k),
    // then per step t the 3 rows READ / WRITE-i / WRITE-j at ts N+3t+{0,1,2}.
    for row in 0..N_CORE {
        is_core[row] = m31(1);
    }
    for k in 0..N {
        is_init[k] = m31(1);
        core_ts[k] = m31(k as u32);
        init_addr[k] = m31(k as u32);
    }
    for t in 0..TAU {
        let base = N + 3 * t;
        // step_no = t on all three step rows; core_ts matches mem_accesses ts.
        step_no[base] = m31(t as u32);
        step_no[base + 1] = m31(t as u32);
        step_no[base + 2] = m31(t as u32);
        core_ts[base] = m31((N + 3 * t) as u32);
        core_ts[base + 1] = m31((N + 3 * t + 1) as u32);
        core_ts[base + 2] = m31((N + 3 * t + 2) as u32);
        is_read_row[base] = m31(1);
        is_wr_i_row[base + 1] = m31(1);
        is_wr_j_row[base + 2] = m31(1);
    }
    for row in 0..N_ACCESSES {
        is_sorted[row] = m31(1);
    }
    sorted_start[0] = m31(1);

    let mut out = vec![
        is_stream,
        is_placement,
        is_c,
        acc_start,
        c_last,
        c_bind_id,
        byte_pos,
        is_core,
        is_sorted,
        sorted_start,
        ts_final,
        step_no,
        is_init,
        is_read_row,
        is_wr_i_row,
        is_wr_j_row,
        core_ts,
        init_addr,
        is_sign,
    ];
    out.extend(sign_mask);
    out.into_iter().map(|v| col_eval(log_size, v)).collect()
}

// =============================================================================
// Base trace.
// =============================================================================

pub fn gen_sib_base_trace(witness: &MlDsaWitness, log_size: u32) -> Vec<ColEval> {
    let rows = 1usize << log_size;
    let slen = stream_len(witness);
    let srows = stream_rows(witness);
    let mut cols: Vec<Vec<M31>> = (0..N_BASE_COLS).map(|_| vec![m31(0); rows]).collect();

    // Stream stage.
    for (pos, r) in srows.iter().enumerate() {
        cols[COL_ENABLER][pos] = m31(1);
        cols[COL_BYTE][pos] = m31(r.byte);
        cols[COL_I][pos] = m31(r.i);
        cols[COL_ACCEPT][pos] = m31(u32::from(r.accept));
        let is_placement = pos >= SIGN_BYTES;
        let reject = is_placement && !r.accept;
        cols[COL_REJECT][pos] = m31(u32::from(reject));
        // Accept rows: (i − byte) ∈ [0,256). Reject rows: (byte − i − 1) ∈ [0,256).
        // Each split lo + 256·hi; only the active branch's hi is filled.
        if r.accept {
            let am = r.i as i64 - r.byte as i64;
            debug_assert!((0..256).contains(&am));
            cols[COL_ACCEPT_HI][pos] = m31((am >> 8) as u32);
        } else if reject {
            let rm = r.byte as i64 - r.i as i64 - 1;
            debug_assert!((0..256).contains(&rm));
            cols[COL_REJECT_HI][pos] = m31((rm >> 8) as u32);
        }
        // Sign rows (first SIGN_BYTES): decompose the byte into its 8 bits so the
        // SignBit channel can tie write-j values to the FIPS sign bits.
        if pos < SIGN_BYTES {
            for u in 0..SIGN_BIT_COLS {
                cols[COL_SIGN_BIT0 + u][pos] = m31((r.byte >> u) & 1);
            }
        }
    }

    // c stage.
    let mut csq = 0i128;
    for m in 0..N {
        let row = slen + m;
        cols[COL_ENABLER][row] = m31(1);
        let c = witness.digits.c[m];
        cols[COL_C][row] = enc_signed(c);
        cols[COL_CSQ][row] = m31((c * c) as u32);
        csq += c * c;
        cols[COL_CSQ_ACC][row] = m31(csq as u32);
    }

    // Offline-memory trace.
    let mem = mem_trace(witness);
    // Unsorted CORE accesses (rows 0..N_CORE); the N FINAL reads are emitted from
    // the c-stage rows above (COL_C is their value), so only the first N_CORE
    // unsorted accesses live here — they are exactly the non-final accesses.
    for (row, a) in mem.unsorted.iter().take(N_CORE).enumerate() {
        cols[COL_U_ADDR][row] = m31(a.addr);
        cols[COL_U_VAL][row] = enc_signed(a.value);
        cols[COL_U_TS][row] = m31(a.ts);
        cols[COL_U_WRITE][row] = m31(u32::from(a.is_write));
    }
    // Sorted view (rows 0..N_ACCESSES) with per-pair diff witnesses.
    let mut prev: Option<Access> = None;
    for (row, a) in mem.sorted.iter().enumerate() {
        cols[COL_S_ADDR][row] = m31(a.addr);
        cols[COL_S_VAL][row] = enc_signed(a.value);
        cols[COL_S_TS][row] = m31(a.ts);
        cols[COL_S_WRITE][row] = m31(u32::from(a.is_write));
        let same = prev.is_some_and(|p| p.addr == a.addr);
        cols[COL_S_SAME][row] = m31(u32::from(same));
        let daddr = a.addr - prev.map_or(0, |p| p.addr); // ≥0 (sorted), <N
        cols[COL_S_DADDR][row] = m31(daddr);
        // is-zero gadget: daddr·inv == 1 − same. When daddr==0 (same), inv=0;
        // else inv = daddr⁻¹ so the product is 1.
        cols[COL_S_DADDR_INV][row] =
            if daddr == 0 { m31(0) } else { m31(daddr).inverse() };
        // Strict ts within a cell: dts = ts − prev_ts − 1 ≥ 0 (only when same).
        let dts = if same { a.ts - prev.unwrap().ts - 1 } else { 0 };
        cols[COL_S_DTS][row] = m31(dts);
        let s_read = !a.is_write;
        let sr_same = same && s_read;
        cols[COL_S_SR_SAME][row] = m31(u32::from(sr_same));
        // first-of-cell = is_sorted·(1−same) (is_sorted==1 on every sorted row).
        cols[COL_S_FOC][row] = m31(u32::from(!same));
        prev = Some(*a);
    }

    cols.into_iter().map(|v| col_eval(log_size, v)).collect()
}

fn enc_signed(v: i128) -> M31 {
    const P: i128 = (1 << 31) - 1;
    m31((((v % P) + P) % P) as u32)
}

// =============================================================================
// The AIR.
// =============================================================================

#[derive(Clone)]
pub struct SibEval {
    pub log_size: u32,
    /// Instance namespace ("" = legacy single-instance ids).
    pub ns: String,
    pub relations: SibRelations,
}

/// Logup entries (fixed per row, gates zero inactive stages), in AIR emission
/// order: accept_lo (rc8), accept_hi (rc8), reject_lo (rc8), reject_hi (rc8),
/// hashio consume, ternary (rc9), ccell use, daddr (rc8), dts (rc11),
/// mem_unsorted_core (+), mem_unsorted_final (+), mem_sorted (−) = 12; then the
/// FSM↔memory tie channels: swap accept-yield ×2, swap read-consume, swap
/// write-j-consume = 4; stepval read-yield, stepval write-i-consume = 2; signbit
/// sign-yield ×8, signbit write-j-consume = 9. Total 12 + 4 + 2 + 9 = 27.
pub const N_LOGUP_ENTRIES: usize = 12 + 4 + 2 + 9;
pub const LOGUP_BATCH: usize = 1;
pub const N_LOGUP_COLS: usize = N_LOGUP_ENTRIES.div_ceil(LOGUP_BATCH);
const N_ACC_COORD_COLS: usize = SECURE_EXTENSION_DEGREE; // Σc² accumulator.
// One QM31 passthrough column packing the sorted (addr, ts, val) into coords
// 0/1/2, read at `[-1,0]` so the previous sorted row's access is available.
const N_SORTED_PASS_COLS: usize = SECURE_EXTENSION_DEGREE;
pub const N_INTERACTION_COLS: usize =
    N_ACC_COORD_COLS + N_SORTED_PASS_COLS + SECURE_EXTENSION_DEGREE * N_LOGUP_COLS;

impl FrameworkEval for SibEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        // Shadow the module-level `pre_id` with the instance-namespaced one so
        // every preprocessed reference below resolves to THIS instance's ids.
        let pre_id = |name: &str| pre_id_ns(&self.ns, name);
        let is_stream = eval.get_preprocessed_column(pre_id("is_stream"));
        let is_placement = eval.get_preprocessed_column(pre_id("is_placement"));
        let is_c = eval.get_preprocessed_column(pre_id("is_c"));
        let acc_start = eval.get_preprocessed_column(pre_id("acc_start"));
        let c_last = eval.get_preprocessed_column(pre_id("c_last"));
        let c_bind_id = eval.get_preprocessed_column(pre_id("c_bind_id"));
        let byte_pos = eval.get_preprocessed_column(pre_id("byte_pos"));
        let is_core = eval.get_preprocessed_column(pre_id("is_core"));
        let is_sorted = eval.get_preprocessed_column(pre_id("is_sorted"));
        let sorted_start = eval.get_preprocessed_column(pre_id("sorted_start"));
        let ts_final = eval.get_preprocessed_column(pre_id("ts_final"));
        // FSM↔memory schedule pins.
        let step_no = eval.get_preprocessed_column(pre_id("step_no"));
        let is_init = eval.get_preprocessed_column(pre_id("is_init"));
        let is_read_row = eval.get_preprocessed_column(pre_id("is_read_row"));
        let is_wr_i_row = eval.get_preprocessed_column(pre_id("is_wr_i_row"));
        let is_wr_j_row = eval.get_preprocessed_column(pre_id("is_wr_j_row"));
        let core_ts = eval.get_preprocessed_column(pre_id("core_ts"));
        let init_addr = eval.get_preprocessed_column(pre_id("init_addr"));
        let is_sign = eval.get_preprocessed_column(pre_id("is_sign"));
        let sign_mask: Vec<E::F> = (0..SIGN_BIT_COLS)
            .map(|u| eval.get_preprocessed_column(pre_id(&sign_mask_name(u))))
            .collect();

        let enabler = eval.next_trace_mask();
        let byte = eval.next_trace_mask();
        let idx = eval.next_trace_mask();
        let accept = eval.next_trace_mask();
        let reject = eval.next_trace_mask();
        let accept_hi = eval.next_trace_mask();
        let reject_hi = eval.next_trace_mask();
        let c = eval.next_trace_mask();
        let csq = eval.next_trace_mask();
        let csq_acc = eval.next_trace_mask();
        // Offline-memory base masks (COL_U_* / COL_S_*), read in column order.
        let u_addr = eval.next_trace_mask();
        let u_val = eval.next_trace_mask();
        let u_ts = eval.next_trace_mask();
        let u_write = eval.next_trace_mask();
        let s_addr = eval.next_trace_mask();
        let s_val = eval.next_trace_mask();
        let s_ts = eval.next_trace_mask();
        let s_write = eval.next_trace_mask();
        let s_same = eval.next_trace_mask();
        let s_daddr = eval.next_trace_mask();
        let s_daddr_inv = eval.next_trace_mask();
        let s_dts = eval.next_trace_mask();
        let s_sr_same = eval.next_trace_mask();
        let s_foc = eval.next_trace_mask();
        // Sign-bit base masks (COL_SIGN_BIT0..): bits of each sign-row byte.
        let sign_bit: Vec<E::F> =
            (0..SIGN_BIT_COLS).map(|_| eval.next_trace_mask()).collect();

        // Σc² running accumulator across the c stage (interaction `[-1,0]`).
        let acc_coords: [[E::F; 2]; SECURE_EXTENSION_DEGREE] =
            core::array::from_fn(|_| eval.next_interaction_mask(INTERACTION_TRACE_IDX, [-1, 0]));
        let csq_prev = E::combine_ef(acc_coords.each_ref().map(|p| p[0].clone()));
        let csq_cur = E::combine_ef(acc_coords.each_ref().map(|p| p[1].clone()));

        // Sorted (addr, ts, val) passthrough (coords 0/1/2), read at `[-1,0]` to
        // recover the PREVIOUS sorted row's access. Padding coord (3) unused.
        let pass_coords: [[E::F; 2]; SECURE_EXTENSION_DEGREE] =
            core::array::from_fn(|_| eval.next_interaction_mask(INTERACTION_TRACE_IDX, [-1, 0]));
        let prev_s_addr = pass_coords[0][0].clone();
        let prev_s_ts = pass_coords[1][0].clone();
        let prev_s_val = pass_coords[2][0].clone();
        // Pin the passthrough's CURRENT coords to the sorted base columns so the
        // interaction column faithfully carries (addr, ts, val).
        eval.add_constraint(pass_coords[0][1].clone() - s_addr.clone());
        eval.add_constraint(pass_coords[1][1].clone() - s_ts.clone());
        eval.add_constraint(pass_coords[2][1].clone() - s_val.clone());

        let one = E::F::from(M31::one());
        let two_pow_8 = E::F::from(m31(1 << 8));

        // C0: enabler boolean.
        eval.add_constraint(enabler.clone() * (one.clone() - enabler.clone()));

        // C1: accept / reject booleans, and their placement partition.
        eval.add_constraint(accept.clone() * (one.clone() - accept.clone()));
        eval.add_constraint(reject.clone() * (one.clone() - reject.clone()));
        // Every placement stream row is exactly accept XOR reject; sign-collection
        // rows (is_stream · (1−is_placement)) and non-stream rows have both = 0.
        eval.add_constraint(is_placement.clone() - (accept.clone() + reject.clone()));

        // C2: rejection-sampling margin (the security-critical tie of c's support
        // to the stream). Accept ⇒ (i − byte) ∈ [0,256): the byte was ≤ i.
        // Reject ⇒ (byte − i − 1) ∈ [0,256): the byte was > i. Each value is
        // degree 1; the gate is a single degree-1 trace flag (accept / reject),
        // so the logup constraint stays degree ≤ 2 (the M4 +1 bound).
        let accept_lo = (idx.clone() - byte.clone()) - two_pow_8.clone() * accept_hi.clone();
        eval.add_to_relation(RelationEntry::base(
            &self.relations.rc8,
            accept.clone(),
            core::slice::from_ref(&accept_lo),
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.rc8,
            accept.clone(),
            core::slice::from_ref(&accept_hi),
        ));
        let reject_lo =
            (byte.clone() - idx.clone() - one.clone()) - two_pow_8.clone() * reject_hi.clone();
        eval.add_to_relation(RelationEntry::base(
            &self.relations.rc8,
            reject.clone(),
            core::slice::from_ref(&reject_lo),
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.rc8,
            reject.clone(),
            core::slice::from_ref(&reject_hi),
        ));

        // C3: HashIo consume — (STREAM_ID_SIB_SQUEEZE, byte_pos, byte), require (−).
        let stream_id = E::F::from(m31(STREAM_ID_SIB_SQUEEZE));
        let io_tuple = [stream_id, byte_pos.clone(), byte.clone()];
        eval.add_to_relation(RelationEntry::base(
            &self.relations.hash_io,
            -is_stream.clone(),
            &io_tuple,
        ));

        // C4: ternary c ∈ {−1,0,1} via `{0,1,2}` membership on (c+1), rc9 (⊇3).
        let c_plus1 = c.clone() + one.clone();
        eval.add_to_relation(RelationEntry::base(
            &self.relations.rc9,
            is_c.clone(),
            core::slice::from_ref(&c_plus1),
        ));

        // C5a: witness csq = c² (degree-2 constraint, NOT involving the shifted
        // interaction mask — keeping the c² product off the accumulator constraint
        // avoids the M4 `[-1,0]`-mask degree trap).
        eval.add_constraint(csq.clone() - c.clone() * c.clone());
        // C5b: Σc² accumulator. csq_cur = (1 − acc_start)·csq_prev + csq. `acc_start`
        // (coset row 0) zeroes the `[-1,0]` wraparound; stream rows carry csq=0 so
        // the sum stays 0 until the c stage, then accumulates c². Degree 1 in the
        // mask constraint (csq is a base cell).
        let csq_prev_gated = E::EF::from(one.clone() - acc_start.clone()) * csq_prev;
        eval.add_constraint(csq_cur.clone() - (csq_prev_gated + E::EF::from(csq.clone())));

        // C6: final c-row gate — Σc² == τ.
        eval.add_constraint(c_last.clone() * (csq_acc.clone() - E::F::from(m31(TAU as u32))));

        // C7: c-binding — USE the coeffs C cell (c_bind_id = m, c).
        let ctuple = [c_bind_id.clone(), c.clone()];
        eval.add_to_relation(RelationEntry::base(
            &self.relations.ccell,
            is_c.clone(),
            &ctuple,
        ));

        // =====================================================================
        // C8: offline-memory (swap replay). Degree worksheet — EVERY row ≤ 2.
        // | site                                   | expr                       | deg |
        // | u_write / s_write / s_same booleans    | x(1−x)                     |  2  |
        // | daddr is-zero: daddr·inv == 1−same     | daddr·inv , 1−same         |  2  |
        // | same ⇒ daddr==0                        | same·daddr                 |  2  |
        // | sr_same == same·s_read                 | same·(is_sorted−s_write)   |  2  |
        // | foc == is_sorted·(1−same)              | is_sorted·(1−same)         |  2  |
        // | daddr = s_addr − prev (gate transition)| s_addr−prev_addr−daddr     |  1  |
        // | strict ts: same·(Δts−1−dts)==0         | same·(…)                   |  2  |
        // | value continuity: sr_same·(s_val−prev) | sr_same·(…)                |  2  |
        // | init: foc·(1−s_write), foc·s_val       | foc·(…)                    |  2  |
        // | rc uses (daddr rc8, dts rc11)          | gate·value                 |  1  |
        // | Mem yields (±combine)                  | gate·combine               |  1  |
        // The passthrough pins (above) are degree 1. No constraint exceeds 2, so
        // the `[-1,0]` masks keep the bound at log_size+1 (M4 trap avoided).
        // =====================================================================

        // C8a: access-flag booleans.
        eval.add_constraint(u_write.clone() * (one.clone() - u_write.clone()));
        eval.add_constraint(s_write.clone() * (one.clone() - s_write.clone()));
        eval.add_constraint(s_same.clone() * (one.clone() - s_same.clone()));

        // C8b: `same` is EXACTLY `daddr == 0` (is-zero gadget). The transition
        // is gated off the very first sorted row (sorted_start) where there is no
        // predecessor. daddr = s_addr − prev_s_addr, non-negative and < N.
        let not_first = is_sorted.clone() - sorted_start.clone(); // 1 on sorted rows>0
        // daddr definition (only meaningful on non-first sorted rows).
        eval.add_constraint(
            not_first.clone() * (s_addr.clone() - prev_s_addr.clone() - s_daddr.clone()),
        );
        // same ⇒ daddr == 0.
        eval.add_constraint(s_same.clone() * s_daddr.clone());
        // daddr == 0 ⇒ same == 1: daddr·inv == 1 − same (gated to non-first rows;
        // the first row has same == 0 forced below).
        eval.add_constraint(
            not_first.clone() * (s_daddr.clone() * s_daddr_inv.clone() - (one.clone() - s_same.clone())),
        );
        // The FIRST sorted row (sorted_start) opens a new cell: same == 0.
        eval.add_constraint(sorted_start.clone() * s_same.clone());

        // C8c: daddr ∈ [0,256) (rc8) — non-decreasing addr. Gated to non-first.
        eval.add_to_relation(RelationEntry::base(
            &self.relations.rc8,
            not_first.clone(),
            core::slice::from_ref(&s_daddr),
        ));

        // C8d: strict ts within a cell: dts = ts − prev_ts − 1 ≥ 0 (rc11), and
        // same·(s_ts − prev_s_ts − 1 − dts) == 0.
        eval.add_constraint(
            s_same.clone() * (s_ts.clone() - prev_s_ts.clone() - one.clone() - s_dts.clone()),
        );
        eval.add_to_relation(RelationEntry::base(
            &self.relations.rc11,
            s_same.clone(),
            core::slice::from_ref(&s_dts),
        ));

        // C8e: value continuity for READs within a cell. s_read = is_sorted −
        // s_write (0/1 on sorted rows). sr_same = same·s_read (witnessed), then
        // sr_same·(s_val − prev_s_val) == 0 keeps degree ≤ 2.
        let s_read = is_sorted.clone() - s_write.clone();
        eval.add_constraint(s_sr_same.clone() - s_same.clone() * s_read.clone());
        eval.add_constraint(s_sr_same.clone() * (s_val.clone() - prev_s_val.clone()));

        // C8f: first-of-cell must be an INIT write of 0. foc = is_sorted·(1−same).
        eval.add_constraint(s_foc.clone() - is_sorted.clone() * (one.clone() - s_same.clone()));
        eval.add_constraint(s_foc.clone() * (one.clone() - s_write.clone())); // is a write
        eval.add_constraint(s_foc.clone() * s_val.clone()); // writes value 0

        // C8g: Mem multiset permutation. Unsorted CORE accesses yield (+); the N
        // FINAL reads yield (+) co-located on the c-stage rows with value = COL_C
        // (so the array's final state IS the coeffs-bound `c`); the SORTED view
        // requires (−). The three self-cancel iff unsorted and sorted are a
        // permutation ⇒ the committed `c` is the true SampleInBall output.
        let u_tuple = [u_addr.clone(), u_val.clone(), u_ts.clone()];
        eval.add_to_relation(RelationEntry::base(&self.relations.mem, is_core.clone(), &u_tuple));
        // FINAL read: (addr=m=c_bind_id, value=COL_C=c, ts=ts_final), gated is_c.
        let final_tuple = [c_bind_id.clone(), c.clone(), ts_final.clone()];
        eval.add_to_relation(RelationEntry::base(&self.relations.mem, is_c.clone(), &final_tuple));
        let s_tuple = [s_addr.clone(), s_val.clone(), s_ts.clone()];
        eval.add_to_relation(RelationEntry::base(&self.relations.mem, -is_sorted.clone(), &s_tuple));

        // =====================================================================
        // C9: FSM↔memory schedule pins. Without these the CORE access columns
        // (u_addr/u_val/u_ts/u_write) are FREE WITNESS: only u_write booleanity +
        // the Mem yield constrain them, so a prover could commit an arbitrary
        // memory-consistent history and the swap-replay (C8) would be vacuous.
        // The pins force the row roles, canonical timestamps, init writes, and the
        // schedule-determined write-i address. Degree worksheet — all ≤ 2:
        // | site                                  | expr                        | deg |
        // | ts == core_ts                         | is_core·(u_ts−core_ts)      |  2  |
        // | u_write role partition                | u_write−(init+wri+wrj)      |  1  |
        // | init addr / val                       | is_init·(u_addr−init_addr)  |  2  |
        // |                                       | is_init·u_val               |  2  |
        // | write-i addr = (N−τ)+step_no          | is_wr_i_row·(u_addr−…)       |  2  |
        // =====================================================================
        eval.add_constraint(is_core.clone() * (u_ts.clone() - core_ts.clone()));
        // u_write is exactly 1 on writes (init + write-i + write-j), 0 elsewhere.
        // (On padding all three role selectors are 0, forcing u_write == 0.)
        eval.add_constraint(
            u_write.clone() - (is_init.clone() + is_wr_i_row.clone() + is_wr_j_row.clone()),
        );
        eval.add_constraint(is_init.clone() * (u_addr.clone() - init_addr.clone()));
        eval.add_constraint(is_init.clone() * u_val.clone());
        let n_minus_tau = E::F::from(m31((N - TAU) as u32));
        eval.add_constraint(
            is_wr_i_row.clone() * (u_addr.clone() - n_minus_tau.clone() - step_no.clone()),
        );

        // =====================================================================
        // C10: FSM↔memory tie channels. These bind every CORE access back to the
        // FSM rows so the access list is a deterministic function of the accepted
        // bytes + FIPS sign bits (not free witness). Degree worksheet — all ≤ 2:
        // | site                          | gate·combine                | deg |
        // | swap accept-yield (×2)        | accept·combine(idx−…, byte) |  2  |
        // | swap read/write-j consume     | role·combine(step_no,u_addr)|  2  |
        // | stepval read-yield / wr-i     | role·combine(step_no,u_val) |  2  |
        // | signbit sign-yield (×8)       | mask_u·combine(8b+u, ±1)    |  2  |
        // | signbit write-j consume       | wr_j·combine(step_no,u_val) |  2  |
        // | sign_bit_u boolean            | b(1−b)                      |  2  |
        // | sign recomposition            | is_sign·(byte−Σ 2^u·bit)    |  2  |
        // =====================================================================

        // --- Swap channel: read/write-j addresses == accepted stream byte ---
        // Accept rows yield (t, byte) with MULTIPLICITY 2 (two identical +accept
        // entries), where the step ordinal t = idx − (N−τ) (idx = i BEFORE the
        // accept increment, so i = N−τ+t ⇒ t = idx − (N−τ)). Read + write-j rows
        // each consume (step_no, u_addr). Balance ⇒ both memory addresses equal
        // the byte accepted at that step. Accept-count corollary: the consume side
        // demands each key t∈{0..τ−1} exactly twice (τ steps × {read, write-j}), so
        // exactly one accept row carries each t ⇒ EXACTLY τ accepts (extra/missing
        // accepts imbalance the Swap channel).
        let swap_key = idx.clone() - n_minus_tau.clone();
        let swap_accept_tuple = [swap_key.clone(), byte.clone()];
        eval.add_to_relation(RelationEntry::base(
            &self.relations.swap,
            accept.clone(),
            &swap_accept_tuple,
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.swap,
            accept.clone(),
            &swap_accept_tuple,
        ));
        let read_addr_tuple = [step_no.clone(), u_addr.clone()];
        eval.add_to_relation(RelationEntry::base(
            &self.relations.swap,
            -is_read_row.clone(),
            &read_addr_tuple,
        ));
        let wrj_addr_tuple = [step_no.clone(), u_addr.clone()];
        eval.add_to_relation(RelationEntry::base(
            &self.relations.swap,
            -is_wr_j_row.clone(),
            &wrj_addr_tuple,
        ));

        // --- StepVal channel: write-i value == read value (c[i_t] = c[j_t]) ---
        // The read value itself is forced correct by the sorted-view continuity
        // (C8e); this ties the write-i to that read value at the same step.
        let read_val_tuple = [step_no.clone(), u_val.clone()];
        eval.add_to_relation(RelationEntry::base(
            &self.relations.stepval,
            is_read_row.clone(),
            &read_val_tuple,
        ));
        let wri_val_tuple = [step_no.clone(), u_val.clone()];
        eval.add_to_relation(RelationEntry::base(
            &self.relations.stepval,
            -is_wr_i_row.clone(),
            &wri_val_tuple,
        ));

        // --- SignBit channel: write-j value == FIPS sign bit (±1) ---
        // Sign row b (byte_pos = b) yields, per bit u used (mask_u = 1 iff step
        // 8b+u < τ), the tuple (8b+u, 1−2·bit): FIPS `c[j] = −1 if bit else +1`,
        // and enc_signed(±1) in M31 is 1 or P−1 = 1−2·bit. Write-j rows consume
        // (step_no, u_val). Balance ⇒ each write-j value is the correct sign bit.
        let zg = E::F::from(m31(0));
        let _ = (&sign_bit, &is_sign, &byte, &sign_mask, &byte_pos);
        for u in 0..SIGN_BIT_COLS {
            let sign_tuple = [E::F::from(m31(u as u32)), one.clone()];
            eval.add_to_relation(RelationEntry::base(&self.relations.signbit, zg.clone(), &sign_tuple));
        }
        let wrj_val_tuple = [step_no.clone(), u_val.clone()];
        eval.add_to_relation(RelationEntry::base(&self.relations.signbit, zg.clone(), &wrj_val_tuple));

        let _ = enabler;
        eval.finalize_logup();
        eval
    }
}

pub type SibComponent = FrameworkComponent<SibEval>;

// =============================================================================
// Interaction trace.
// =============================================================================

pub struct SibInteraction {
    pub trace: Vec<ColEval>,
    pub claimed_sum: SecureField,
    pub rc_uses: RcUses,
    /// The stream bytes the FSM consumes (for the test producer / M6 sponge).
    pub stream_bytes: Vec<u8>,
    /// The (c_bind_id, c) pairs (for the test coeffs-C producer).
    pub ccell_uses: Vec<(u32, u32)>,
}

pub fn gen_sib_interaction(
    witness: &MlDsaWitness,
    log_size: u32,
    relations: &SibRelations,
) -> SibInteraction {
    let rows = 1usize << log_size;
    let slen = stream_len(witness);
    let srows = stream_rows(witness);

    let zero = SecureField::from(m31(0));
    let one = SecureField::one();

    // Σc² accumulator (coset order): a running sum that is 0 through the stream
    // stage, accumulates c² over the c stage, then HOLDS its final value (τ)
    // through the trailing padding — matching the constraint `csq_cur =
    // (1−acc_start)·csq_prev + csq` on EVERY row (padding csq = 0 ⇒ acc flat).
    let mut acc = vec![zero; rows];
    let mut csq = 0u32;
    for row in 0..rows {
        if (slen..slen + N).contains(&row) {
            let c = witness.digits.c[row - slen];
            csq += (c * c) as u32;
        }
        acc[row] = SecureField::from(m31(csq));
    }

    let mut trace: Vec<ColEval> = (0..N_ACC_COORD_COLS)
        .map(|coord| col_eval(log_size, acc.iter().map(|v| v.to_m31_array()[coord]).collect()))
        .collect();

    // Offline-memory: sorted view per coset row (row r ↦ sorted[r] for r<N_ACCESSES).
    let mem = mem_trace(witness);
    // Sorted (addr, ts, val) passthrough QM31 column (coords 0/1/2, 3 unused),
    // read at `[-1,0]` in the AIR to recover the previous sorted row.
    let pass: Vec<SecureField> = (0..rows)
        .map(|row| {
            if let Some(a) = mem.sorted.get(row) {
                SecureField::from_m31_array([m31(a.addr), m31(a.ts), enc_signed(a.value), m31(0)])
            } else {
                zero
            }
        })
        .collect();
    for coord in 0..N_SORTED_PASS_COLS {
        trace.push(col_eval(log_size, pass.iter().map(|v| v.to_m31_array()[coord]).collect()));
    }

    let row_lookup = circle_row_to_coset(log_size);
    let vec_rows = 1usize << (log_size - stwo::prover::backend::simd::m31::LOG_N_LANES);

    let mut rc_uses = RcUses::new();
    let mut stream_bytes = vec![0u8; slen];
    let mut ccell_uses = Vec::with_capacity(N);

    // Per-row precompute.
    #[derive(Clone, Copy)]
    enum Row {
        Stream { byte: u32, i: u32, accept: bool, reject: bool },
        C { m: u32, c: i128 },
    }
    let coset_row: Vec<Option<Row>> = (0..rows)
        .map(|coset| {
            if coset < slen {
                let r = &srows[coset];
                let reject = coset >= SIGN_BYTES && !r.accept;
                Some(Row::Stream { byte: r.byte, i: r.i, accept: r.accept, reject })
            } else if coset < slen + N {
                let m = coset - slen;
                Some(Row::C { m: m as u32, c: witness.digits.c[m] })
            } else {
                None
            }
        })
        .collect();

    // Seed bookkeeping.
    for coset in 0..rows {
        match coset_row[coset] {
            Some(Row::Stream { byte, i, accept, reject }) => {
                stream_bytes[coset] = byte as u8;
                if accept {
                    let am = (i - byte) as usize; // ∈ [0,256)
                    rc_uses.rc8[am & 0xff] += 1;
                    rc_uses.rc8[am >> 8] += 1;
                } else if reject {
                    let rm = (byte - i - 1) as usize; // ∈ [0,256)
                    rc_uses.rc8[rm & 0xff] += 1;
                    rc_uses.rc8[rm >> 8] += 1;
                }
            }
            Some(Row::C { m, c }) => {
                let cp1 = (c + 1) as usize;
                rc_uses.rc9[cp1] += 1;
                ccell_uses.push((m, enc_signed(c).0));
            }
            None => {}
        }
    }

    // Offline-memory range uses over the sorted view: daddr (rc8) on every
    // non-first sorted row; dts (rc11) whenever same (a repeat cell).
    for row in 1..mem.sorted.len() {
        let a = &mem.sorted[row];
        let p = &mem.sorted[row - 1];
        let daddr = (a.addr - p.addr) as usize;
        rc_uses.rc8[daddr] += 1;
        if a.addr == p.addr {
            let dts = (a.ts - p.ts - 1) as usize;
            rc_uses.rc11[dts] += 1;
        }
    }

    let mut entries: Vec<(Vec<PackedQM31>, Vec<PackedQM31>)> = Vec::new();
    let mut claimed = zero;
    let push = |frac: &dyn Fn(usize) -> (SecureField, SecureField),
                entries: &mut Vec<(Vec<PackedQM31>, Vec<PackedQM31>)>,
                claimed: &mut SecureField| {
        let mut nums = Vec::with_capacity(vec_rows);
        let mut dens = Vec::with_capacity(vec_rows);
        for vr in 0..vec_rows {
            let mut n = [zero; N_LANES];
            let mut d = [one; N_LANES];
            for lane in 0..N_LANES {
                let coset = row_lookup[vr * N_LANES + lane];
                let (num, den) = frac(coset);
                n[lane] = num;
                d[lane] = den;
                *claimed += num / den;
            }
            nums.push(PackedQM31::from_array(n));
            dens.push(PackedQM31::from_array(d));
        }
        entries.push((nums, dens));
    };

    // AIR emission order (7): accept_lo(rc8), accept_hi(rc8), reject_lo(rc8),
    // reject_hi(rc8), hashio(−), ternary(rc9), ccell(+).
    push(&|coset| match coset_row[coset] {
        Some(Row::Stream { byte, i, accept, .. }) if accept => {
            let lo = (i - byte) & 0xff;
            (one, relations.rc8.combine(&[m31(lo)]))
        }
        _ => (zero, one),
    }, &mut entries, &mut claimed);
    push(&|coset| match coset_row[coset] {
        Some(Row::Stream { byte, i, accept, .. }) if accept => {
            let hi = (i - byte) >> 8;
            (one, relations.rc8.combine(&[m31(hi)]))
        }
        _ => (zero, one),
    }, &mut entries, &mut claimed);
    push(&|coset| match coset_row[coset] {
        Some(Row::Stream { byte, i, reject, .. }) if reject => {
            let lo = (byte - i - 1) & 0xff;
            (one, relations.rc8.combine(&[m31(lo)]))
        }
        _ => (zero, one),
    }, &mut entries, &mut claimed);
    push(&|coset| match coset_row[coset] {
        Some(Row::Stream { byte, i, reject, .. }) if reject => {
            let hi = (byte - i - 1) >> 8;
            (one, relations.rc8.combine(&[m31(hi)]))
        }
        _ => (zero, one),
    }, &mut entries, &mut claimed);
    // hashio consume (−)
    push(&|coset| match coset_row[coset] {
        Some(Row::Stream { byte, .. }) => {
            let tuple = [m31(STREAM_ID_SIB_SQUEEZE), m31(coset as u32), m31(byte)];
            (-one, relations.hash_io.combine(&tuple))
        }
        _ => (zero, one),
    }, &mut entries, &mut claimed);
    // ternary rc9
    push(&|coset| match coset_row[coset] {
        Some(Row::C { c, .. }) => {
            let v = (c + 1) as u32;
            (one, relations.rc9.combine(&[m31(v)]))
        }
        _ => (zero, one),
    }, &mut entries, &mut claimed);
    // ccell use (+)
    push(&|coset| match coset_row[coset] {
        Some(Row::C { m, c }) => {
            let tuple = [m31(m), enc_signed(c)];
            (one, relations.ccell.combine(&tuple))
        }
        _ => (zero, one),
    }, &mut entries, &mut claimed);

    // daddr (rc8) — sorted rows 1..N_ACCESSES (gate not_first).
    push(&|coset| {
        if coset >= 1 && coset < mem.sorted.len() {
            let daddr = mem.sorted[coset].addr - mem.sorted[coset - 1].addr;
            (one, relations.rc8.combine(&[m31(daddr)]))
        } else {
            (zero, one)
        }
    }, &mut entries, &mut claimed);
    // dts (rc11) — sorted rows where addr repeats (gate same).
    push(&|coset| {
        if coset >= 1 && coset < mem.sorted.len() && mem.sorted[coset].addr == mem.sorted[coset - 1].addr {
            let dts = mem.sorted[coset].ts - mem.sorted[coset - 1].ts - 1;
            (one, relations.rc11.combine(&[m31(dts)]))
        } else {
            (zero, one)
        }
    }, &mut entries, &mut claimed);
    // Mem unsorted CORE (+): rows 0..N_CORE.
    push(&|coset| {
        if coset < N_CORE {
            let a = &mem.unsorted[coset];
            (one, relations.mem.combine(&[m31(a.addr), enc_signed(a.value), m31(a.ts)]))
        } else {
            (zero, one)
        }
    }, &mut entries, &mut claimed);
    // Mem unsorted FINAL read (+): co-located on c-stage rows (addr=m, val=c,
    // ts=N_CORE+m). Reuses the committed COL_C value.
    push(&|coset| match coset_row[coset] {
        Some(Row::C { m, c }) => {
            let ts = (N_CORE as u32) + m;
            (one, relations.mem.combine(&[m31(m), enc_signed(c), m31(ts)]))
        }
        _ => (zero, one),
    }, &mut entries, &mut claimed);
    // Mem sorted (−): rows 0..N_ACCESSES.
    push(&|coset| {
        if coset < mem.sorted.len() {
            let a = &mem.sorted[coset];
            (-one, relations.mem.combine(&[m31(a.addr), enc_signed(a.value), m31(a.ts)]))
        } else {
            (zero, one)
        }
    }, &mut entries, &mut claimed);

    // =====================================================================
    // FSM↔memory tie channels (must mirror the AIR C10 emission order EXACTLY):
    // swap accept-yield ×2, swap read-consume, swap wr-j-consume, stepval
    // read-yield, stepval wr-i-consume, signbit sign-yield ×8, signbit
    // wr-j-consume. Core rows live at cosets 0..N_CORE: coset<N ⇒ init; else
    // t=(coset−N)/3, r=(coset−N)%3 (0=read, 1=write-i, 2=write-j).
    // =====================================================================
    let core_role = |coset: usize| -> Option<(usize, usize)> {
        // Returns (step_t, role) for a step access row; None for init/non-core.
        if (N..N_CORE).contains(&coset) {
            let off = coset - N;
            Some((off / 3, off % 3))
        } else {
            None
        }
    };
    let n_minus_tau = m31((N - TAU) as u32);

    // Swap accept-yield (×2): (idx−(N−τ), byte) on accept stream rows.
    for _ in 0..2 {
        push(&|coset| match coset_row[coset] {
            Some(Row::Stream { byte, i, accept, .. }) if accept => {
                let key = m31(i) - n_minus_tau;
                (one, relations.swap.combine(&[key, m31(byte)]))
            }
            _ => (zero, one),
        }, &mut entries, &mut claimed);
    }
    // Swap read-consume (−): (step_no, u_addr) on read rows (role 0).
    push(&|coset| match core_role(coset) {
        Some((t, 0)) => {
            let a = &mem.unsorted[coset];
            (-one, relations.swap.combine(&[m31(t as u32), m31(a.addr)]))
        }
        _ => (zero, one),
    }, &mut entries, &mut claimed);
    // Swap write-j-consume (−): (step_no, u_addr) on write-j rows (role 2).
    push(&|coset| match core_role(coset) {
        Some((t, 2)) => {
            let a = &mem.unsorted[coset];
            (-one, relations.swap.combine(&[m31(t as u32), m31(a.addr)]))
        }
        _ => (zero, one),
    }, &mut entries, &mut claimed);
    // StepVal read-yield (+): (step_no, u_val) on read rows (role 0).
    push(&|coset| match core_role(coset) {
        Some((t, 0)) => {
            let a = &mem.unsorted[coset];
            (one, relations.stepval.combine(&[m31(t as u32), enc_signed(a.value)]))
        }
        _ => (zero, one),
    }, &mut entries, &mut claimed);
    // StepVal write-i-consume (−): (step_no, u_val) on write-i rows (role 1).
    push(&|coset| match core_role(coset) {
        Some((t, 1)) => {
            let a = &mem.unsorted[coset];
            (-one, relations.stepval.combine(&[m31(t as u32), enc_signed(a.value)]))
        }
        _ => (zero, one),
    }, &mut entries, &mut claimed);
    // SignBit sign-yield (×8): (8·byte_pos+u, 1−2·bit) on sign rows, numerator =
    // mask_u (1 iff step 8b+u < τ).
    for _u in 0..SIGN_BIT_COLS {
        push(&|_coset| (zero, one), &mut entries, &mut claimed);
    }
    // SignBit write-j-consume DISABLED.
    push(&|_coset| (zero, one), &mut entries, &mut claimed);

    let mut logup = LogupTraceGenerator::new(log_size);
    for chunk in entries.chunks(LOGUP_BATCH) {
        logup.col_from_fn(|vr| {
            let mut num = chunk[0].0[vr];
            let mut den = chunk[0].1[vr];
            for (nn, dd) in chunk[1..].iter() {
                num = num * dd[vr] + nn[vr] * den;
                den *= dd[vr];
            }
            (num, den)
        });
    }
    let (logup_trace, claimed_sum) = logup.finalize_last();
    trace.extend(logup_trace);
    debug_assert_eq!(claimed_sum, claimed, "sib logup claimed sum mismatch");

    SibInteraction { trace, claimed_sum, rc_uses, stream_bytes, ccell_uses }
}
