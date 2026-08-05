//! `sampleinball_fsm` implements FIPS 204 [CHAL] SampleInBall (Algorithm 29)
//! over the witnessed
//! SHAKE squeeze stream.
//!
//! [`crate::reference::sample_in_ball`] defines the reference behavior. It
//! squeezes rate blocks on demand. The first 8 bytes are the sign source `s`.
//! For each target
//! `i ∈ [N−τ, N)` it rejection-samples `j ← byte` (reject while `byte > i`) and
//! sets `c[i] = c[j]; c[j] = (−1)^{s&1}; s ≫= 1`.
//!
//! ## Layout
//!
//! One committed AIR contains two stacked row groups at log size 10.
//!
//! 1. **stream group** (one row per byte in the profile resource cap): binds
//!    136 bytes for ML-DSA-44 or 680 bytes for ML-DSA-65 from
//!    `HashIoRelation(STREAM_ID_SIB_SQUEEZE, byte_pos, byte)`. An `active` base
//!    bit selects the unique prefix through the final accepted placement. The
//!    first 8 active bytes are the sign source; each later active byte is
//!    accepted iff `byte ≤ i` (proven by `(i − byte) ∈ [0,256)`) or rejected
//!    iff `byte > i` (proven by `(byte − i − 1) ∈ [0,256)`). Every inactive
//!    padding row is constrained to `i = 256`, so consumption cannot stop early.
//! 2. **c group** (`N` rows): the challenge coefficients, each ternary
//!    (`c² = csq` and `c·csq = c`, hence `c ∈ {−1,0,1}`), with a running `Σ c²`
//!    accumulator gated to `τ` on the final c-row, and each `c[m]` bound to the
//!    coeffs C-group cell via [`CCellRelation`]`(m, c)`.
//!
//! ## Soundness
//!
//! This component constrains four properties. (a) The FSM decisions match the
//! rejection-sampling rule `byte ≤ i`. (b) `c` is ternary and has exactly τ
//! nonzero coefficients (`Σc² = τ`). (c) `c` equals the coeffs-bound
//! coefficients. (d) The swap-placement gate constrains `c` to SampleInBall's
//! Fisher–Yates array replayed from the bound squeeze stream, via an
//! address-sorted **offline-memory** permutation argument over the [`relations`]
//! `Mem` channel. Without (d), a prover can permute the placement of the
//! ±1 values while preserving their multiset and pass (a) through (c). The
//! Mem replay derives placement from the same stream and rejects a
//! permuted `c`. Standalone tests balance the stream bytes. The composed
//! statement connects the proven sponge output.
//!
//! ## Offline-memory swap replay
//!
//! Model `c[0..N]` as a memory with addresses `0..N`. Replaying
//! [`crate::reference::sample_in_ball`] yields an ordered access list with
//! strictly increasing `ts`: N initial writes `(k,0)`, then one read
//! `(j,old_j)` and two writes `(i,old_j)` and `(j,sign)` for each of τ steps,
//! then N final reads `(k,c_final[k])`. The final reads consume `COL_C`, which
//! the ternary, τ, and CCell constraints bind. Thus, the final array state is
//! `c`.
//!
//! Two views live on the same `n_accesses = N + 3τ + N = 659` rows: an
//! **unsorted** access (emission order) yielded `+` into `Mem`, and the same
//! multiset **sorted** by `(addr, ts)` required `−`. Equal multisets ⇒ the two
//! Mem contributions cancel internally. For each consecutive pair, the sorted
//! trace then enforces constraints of degree 2 or less in
//! [`SibEval::evaluate`]: non-decreasing addr, strictly increasing ts within a
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
    EvalAtRow, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry, INTERACTION_TRACE_IDX,
};

use crate::air_util::{circle_row_to_coset, col_eval, enc_signed, m31, ColEval};
use crate::constants::{N, TAU};
use crate::profile::MlDsaProfile;
use crate::witness::MlDsaWitness;
use relations::SibRelations;
use tables::RcUses;

/// Sign bytes at the head of the squeeze stream.
pub const SIGN_BYTES: usize = 8;

/// SHAKE-256 rate in bytes.
pub const SHAKE256_RATE: usize = 136;

/// Resource cap for the SampleInBall rejection stream.
///
/// This is the maximum cap for the fixed internal storage. ML-DSA-44 uses one
/// block and has exhaustion probability about 2^-202.929. ML-DSA-65 uses five
/// blocks. This is a resource cap, not a semantic worst-case bound. FIPS 204
/// sampling is unbounded.
pub const MAX_SIB_SQUEEZE_BLOCKS: usize = 5;

/// Byte length of the maximum SampleInBall squeeze stream.
pub const MAX_SIB_SQUEEZE_BYTES: usize = SHAKE256_RATE * MAX_SIB_SQUEEZE_BLOCKS;

// The stream stage binds the verifier-selected resource cap. `active` selects
// only the FIPS-consumed prefix. The c stage follows the selected stream rows.

/// Base column indices.
const COL_ACTIVE: usize = 0;
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
                          // Offline-memory (swap replay) columns — active on the n_accesses access rows.
const COL_U_ADDR: usize = 9; // unsorted access address
const COL_U_VAL: usize = 10; // unsorted access value (enc_signed)
const COL_U_TS: usize = 11; // unsorted access timestamp
const COL_U_WRITE: usize = 12; // 1 iff unsorted access is a write
const COL_S_ADDR: usize = 13; // sorted access address
const COL_S_VAL: usize = 14; // sorted access value
const COL_S_TS: usize = 15; // sorted access timestamp
const COL_S_WRITE: usize = 16; // 1 iff sorted access is a write
const COL_S_SAME: usize = 17; // 1 iff sorted addr == previous sorted addr (same cell)
const COL_S_DADDR: usize = 18; // sorted addr − previous sorted addr ∈ [0,256) (rc8)
const COL_S_DADDR_INV: usize = 19; // inverse gadget: daddr·inv == 1−same
const COL_S_DTS: usize = 20; // (ts − prev_ts − 1) within a cell ∈ [0,2048) (rc11)
const COL_S_SR_SAME: usize = 21; // same·s_read (witnessed to keep continuity deg 2)
const COL_S_FOC: usize = 22; // first-of-cell = is_access·(1−same) (witnessed, deg 2 pin)
                             // Sign-bit columns — the 8 bits of each sign row's byte (only on the 8 sign rows;
                             // 0 elsewhere). These feed the SignBit channel that ties write-j values to the
                             // FIPS sign bits (`c[j] = (−1)^bit`).
const COL_SIGN_BIT0: usize = 23;
/// Number of sign-bit columns (one per bit of a sign byte).
pub const SIGN_BIT_COLS: usize = 8;
/// Total base columns.
pub const N_BASE_COLS: usize = COL_SIGN_BIT0 + SIGN_BIT_COLS; // 31

/// Core (unsorted) offline-memory accesses laid out on their own rows: N init
/// writes + 3 per step (read + 2 writes). The N FINAL reads are NOT counted here
/// — they are emitted co-located on the c-stage rows so the read value IS `COL_C`
/// (the coeffs-bound `c`), which is what pins the array's final state to `c`.
pub const N_CORE: usize = N + 3 * TAU;

/// Total offline-memory accesses (core + N final reads). Drives the SORTED
/// trace row count and the sib log_size.
pub const N_ACCESSES: usize = N_CORE + N;

fn squeeze_bytes(profile: MlDsaProfile) -> usize {
    SHAKE256_RATE * profile.sample_in_ball_squeeze_blocks()
}

fn n_core(profile: MlDsaProfile) -> usize {
    N + 3 * profile.tau()
}

fn n_accesses(profile: MlDsaProfile) -> usize {
    n_core(profile) + N
}

/// Preprocessed id for one hosted ML-DSA instance. The schedule content is
/// static across instances (function of `(profile, log_size)` only), and
/// cross-instance separation lives in each instance's own relation draws
/// (distinct `SibRelations` per namespace, from a channel already mixed with
/// the instance namespace — see `statement::mix_public`/`draw_relations`), not
/// in the preprocessed id. Deliberately UNNAMESPACED so air-core's
/// content-fingerprint dedup collapses the 28 identical columns committed
/// once instead of once per hosted instance. `ns` is accepted for call-site
/// symmetry with other components' `pre_id_ns` helpers; air-core's id-content
/// fingerprint guard fails loudly if this ever stops being content-only.
pub(crate) fn pre_id_ns(_ns: &str, name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mldsa_sib_{name}"),
    }
}

fn sign_mask_name(u: usize) -> String {
    format!("sign_mask_{u}")
}

/// Preprocessed identifiers in commit order for a single instance.
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
        // Bind the core-row roles, timestamps, initial addresses, and step
        // numbers to the FSM schedule.
        pre_id("step_no"),
        pre_id("is_init"),
        pre_id("is_read_row"),
        pre_id("is_wr_i_row"),
        pre_id("is_wr_j_row"),
        pre_id("core_ts"),
        pre_id("init_addr"),
        pre_id("is_sign"),
        pre_id("stream_last"),
    ];
    for u in 0..SIGN_BIT_COLS {
        ids.push(pre_id(&sign_mask_name(u)));
    }
    ids
}

fn accepted_prefix_len(profile: MlDsaProfile, stream: &[u8]) -> Result<usize, &'static str> {
    if stream.len() > squeeze_bytes(profile) {
        return Err("SampleInBall stream exceeds the selected resource cap");
    }
    if stream.len() < SIGN_BYTES {
        return Err("SampleInBall stream is missing sign bytes");
    }
    let tau = profile.tau();
    let mut i = (N - tau) as u32;
    let mut placed = 0usize;
    let mut pos = SIGN_BYTES;
    while placed < tau {
        let b = *stream
            .get(pos)
            .ok_or("SampleInBall stream ends before the final accepted placement")?
            as u32;
        pos += 1;
        if b <= i {
            i += 1;
            placed += 1;
        }
    }
    Ok(pos)
}

/// Validate the witness stream without panicking.
///
/// The stream must end on the canonical SHAKE block containing the final
/// accepted placement and must stay within the selected cap.
pub fn validate_stream(witness: &MlDsaWitness) -> Result<usize, &'static str> {
    let stream = &witness.sponge.sample_in_ball_squeezed;
    let consumed = accepted_prefix_len(witness.profile, stream)?;
    let expected = SHAKE256_RATE * consumed.div_ceil(SHAKE256_RATE);
    if stream.len() != expected {
        return Err("SampleInBall squeeze length is not canonically derived");
    }
    Ok(consumed)
}

/// Return the consumed-prefix length after validation.
pub fn stream_len(witness: &MlDsaWitness) -> usize {
    validate_stream(witness).expect("validated SampleInBall witness stream")
}

/// Deterministic profile-sized squeeze stream committed by the Keccak service
/// and consumed in full by this component.
pub(crate) fn fixed_squeeze_stream(witness: &MlDsaWitness) -> Vec<u8> {
    crate::reference::sponge::shake256(
        &[&witness.sponge.sample_in_ball_absorbed],
        squeeze_bytes(witness.profile),
    )
    .0
}

/// Reconstruct the per-stream-row FSM state from the reference stream.
struct StreamRow {
    byte: u32,
    i: u32,
    active: bool,
    accept: bool,
}

fn stream_rows(witness: &MlDsaWitness) -> Vec<StreamRow> {
    let stream = fixed_squeeze_stream(witness);
    let tau = witness.profile.tau();
    let stream_bytes = squeeze_bytes(witness.profile);
    let mut out = Vec::with_capacity(stream_bytes);
    let mut i = (N - tau) as u32;
    let mut placed = 0usize;
    for pos in 0..stream_bytes {
        let b = stream[pos] as u32;
        if pos < SIGN_BYTES {
            // Sign-collection rows: i stays at N−τ, byte recorded, no accept.
            out.push(StreamRow {
                byte: b,
                i,
                active: true,
                accept: false,
            });
        } else {
            let active = placed < tau;
            let accept = active && b <= i;
            out.push(StreamRow {
                byte: b,
                i,
                active,
                accept,
            });
            if accept {
                i += 1;
                placed += 1;
            }
        }
    }
    FORGED_STREAM_I.with(|forged| {
        if let Some(indices) = forged.borrow().as_ref() {
            assert_eq!(
                indices.len(),
                out.len(),
                "forged stream-index list must match the fixed stream length"
            );
            for (row, &idx) in out.iter_mut().zip(indices) {
                row.i = idx;
            }
        }
    });
    FORGED_ACTIVE.with(|forged| {
        if let Some(active) = forged.borrow().as_ref() {
            assert_eq!(
                active.len(),
                out.len(),
                "forged active list must match the fixed stream length"
            );
            for (row, &value) in out.iter_mut().zip(active) {
                row.active = value;
            }
        }
    });
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
    let stream = fixed_squeeze_stream(witness);
    let mut c = [0i128; N];
    let sign_bits = u64::from_le_bytes(stream[0..SIGN_BYTES].try_into().expect("8 bytes"));
    let mut sign = sign_bits;
    let mut pos = SIGN_BYTES;

    let tau = witness.profile.tau();
    let accesses = n_accesses(witness.profile);
    let mut out = Vec::with_capacity(accesses);
    let mut ts: u32 = 0;

    // INIT: write (k, 0) for k in 0..N.
    for k in 0..N {
        out.push(Access {
            addr: k as u32,
            value: 0,
            ts,
            is_write: true,
        });
        ts += 1;
    }

    // Per step: rejection-sample j ≤ i, then read (j,old_j), write (i,old_j),
    // write (j, sign). Mirrors reference::sample_in_ball's write order EXACTLY.
    for i in (N - tau)..N {
        let j = loop {
            let byte = stream[pos] as usize;
            pos += 1;
            if byte <= i {
                break byte;
            }
        };
        let old_j = c[j];
        out.push(Access {
            addr: j as u32,
            value: old_j,
            ts,
            is_write: false,
        });
        ts += 1;
        c[i] = old_j;
        out.push(Access {
            addr: i as u32,
            value: c[i],
            ts,
            is_write: true,
        });
        ts += 1;
        let s: i128 = if sign & 1 == 1 { -1 } else { 1 };
        c[j] = s;
        out.push(Access {
            addr: j as u32,
            value: c[j],
            ts,
            is_write: true,
        });
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
        out.push(Access {
            addr: k as u32,
            value: c[k],
            ts,
            is_write: false,
        });
        ts += 1;
    }

    debug_assert_eq!(out.len(), accesses);
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

    /// Test-only attack hooks for exercising individual AIR constraints with a
    /// fully self-consistent malicious trace generator.
    static FORGED_STREAM_I: core::cell::RefCell<Option<Vec<u32>>> =
        const { core::cell::RefCell::new(None) };
    static FORGED_ACTIVE: core::cell::RefCell<Option<Vec<bool>>> =
        const { core::cell::RefCell::new(None) };
    static FORGED_SIGN_BYTES: core::cell::RefCell<Option<[u8; SIGN_BYTES]>> =
        const { core::cell::RefCell::new(None) };
    static FORGED_SORTED_WRITES: core::cell::RefCell<Option<Vec<bool>>> =
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
        .take(n_core(witness.profile))
        .map(|a| (a.addr, a.value, a.ts, a.is_write))
        .collect()
}

/// Test-attack hook, DO NOT USE outside integration tests. See [`ForgedCoreGuard`].
#[doc(hidden)]
pub fn install_forged_core(accesses: Vec<(u32, i128, u32, bool)>) -> ForgedCoreGuard {
    let forged: Vec<Access> = accesses
        .into_iter()
        .map(|(addr, value, ts, is_write)| Access {
            addr,
            value,
            ts,
            is_write,
        })
        .collect();
    FORGED_CORE.with(|f| *f.borrow_mut() = Some(forged));
    ForgedCoreGuard
}

/// Test-attack hook: returns the honest consumed stream rows as
/// `(byte, i_before, accept)` tuples.
#[doc(hidden)]
pub fn honest_stream_rows(witness: &MlDsaWitness) -> Vec<(u32, u32, bool)> {
    let guard = FORGED_STREAM_I.with(|f| f.borrow_mut().take());
    let rows = stream_rows(witness)
        .into_iter()
        .map(|row| (row.byte, row.i, row.accept))
        .collect();
    FORGED_STREAM_I.with(|f| *f.borrow_mut() = guard);
    rows
}

/// Test hook that overrides only `COL_I` on consumed stream rows. It can make a
/// balanced history that violates the ordered FIPS sampling transition.
#[doc(hidden)]
pub struct ForgedStreamIndicesGuard;

impl Drop for ForgedStreamIndicesGuard {
    fn drop(&mut self) {
        FORGED_STREAM_I.with(|f| *f.borrow_mut() = None);
    }
}

#[doc(hidden)]
pub fn install_forged_stream_indices(indices: Vec<u32>) -> ForgedStreamIndicesGuard {
    FORGED_STREAM_I.with(|f| *f.borrow_mut() = Some(indices));
    ForgedStreamIndicesGuard
}

/// Test-attack hook: returns the honest fixed-stream active-prefix bits.
#[doc(hidden)]
pub fn honest_active_rows(witness: &MlDsaWitness) -> Vec<bool> {
    let guard = FORGED_ACTIVE.with(|f| f.borrow_mut().take());
    let active = stream_rows(witness)
        .into_iter()
        .map(|row| row.active)
        .collect();
    FORGED_ACTIVE.with(|f| *f.borrow_mut() = guard);
    active
}

/// Test-attack hook: overrides the fixed-stream active-prefix bits while
/// leaving bytes, accept decisions, and index history unchanged.
#[doc(hidden)]
pub struct ForgedActiveGuard;

impl Drop for ForgedActiveGuard {
    fn drop(&mut self) {
        FORGED_ACTIVE.with(|f| *f.borrow_mut() = None);
    }
}

#[doc(hidden)]
pub fn install_forged_active(active: Vec<bool>) -> ForgedActiveGuard {
    FORGED_ACTIVE.with(|f| *f.borrow_mut() = Some(active));
    ForgedActiveGuard
}

/// Test-attack hook: overrides the sign-bit witness columns while leaving the
/// HashIo-bound stream bytes unchanged. Both byte recomposition and the SignBit
/// balance independently bind these columns to the honest execution.
#[doc(hidden)]
pub struct ForgedSignBytesGuard;

impl Drop for ForgedSignBytesGuard {
    fn drop(&mut self) {
        FORGED_SIGN_BYTES.with(|f| *f.borrow_mut() = None);
    }
}

#[doc(hidden)]
pub fn install_forged_sign_bytes(bytes: [u8; SIGN_BYTES]) -> ForgedSignBytesGuard {
    FORGED_SIGN_BYTES.with(|f| *f.borrow_mut() = Some(bytes));
    ForgedSignBytesGuard
}

fn trace_sign_byte(stream: &[u8], pos: usize) -> u8 {
    FORGED_SIGN_BYTES.with(|f| f.borrow().as_ref().map_or(stream[pos], |bytes| bytes[pos]))
}

/// Test-attack hook: returns the honest `(addr, value, ts, is_write)` sorted
/// memory view before any forged sorted-classification override is installed.
#[doc(hidden)]
pub fn honest_sorted_accesses(witness: &MlDsaWitness) -> Vec<(u32, i128, u32, bool)> {
    let mut sorted = mem_accesses(witness);
    sorted.sort_by_key(|a| (a.addr, a.ts));
    sorted
        .into_iter()
        .map(|a| (a.addr, a.value, a.ts, a.is_write))
        .collect()
}

/// Test-attack hook: replaces the sorted view's read/write flags without
/// changing `(addr, value, ts)`. This is exactly the forgery that passed when
/// `MemRelation` omitted access classification.
#[doc(hidden)]
pub struct ForgedSortedWritesGuard;

impl Drop for ForgedSortedWritesGuard {
    fn drop(&mut self) {
        FORGED_SORTED_WRITES.with(|f| *f.borrow_mut() = None);
    }
}

#[doc(hidden)]
pub fn install_forged_sorted_writes(writes: Vec<bool>) -> ForgedSortedWritesGuard {
    FORGED_SORTED_WRITES.with(|f| *f.borrow_mut() = Some(writes));
    ForgedSortedWritesGuard
}

fn mem_trace(witness: &MlDsaWitness) -> MemTrace {
    let mut unsorted = mem_accesses(witness);
    let core = n_core(witness.profile);
    // Test-attack hook: swap the CORE accesses (rows 0..N_CORE) for a forged list,
    // keeping the honest FINAL reads (rows N_CORE..N_ACCESSES) so the Mem balance
    // against the committed `c` is untouched — the FSM↔memory channels must catch it.
    FORGED_CORE.with(|f| {
        if let Some(forged) = f.borrow().as_ref() {
            assert_eq!(
                forged.len(),
                core,
                "forged core list must have N_CORE entries"
            );
            unsorted[..core].clone_from_slice(forged);
            // A malicious CORE is paired with the attacker's committed final
            // `c`, not the honest replay's final values. This keeps the Mem
            // permutation internally balanced so the dedicated FSM/sign
            // constraints, rather than an unrelated generator inconsistency,
            // reject the forged history.
            for k in 0..N {
                unsorted[core + k].value = witness.digits.c[k];
            }
        }
    });
    let mut sorted = unsorted.clone();
    sorted.sort_by_key(|a| (a.addr, a.ts));
    FORGED_SORTED_WRITES.with(|f| {
        if let Some(writes) = f.borrow().as_ref() {
            assert_eq!(
                writes.len(),
                sorted.len(),
                "forged sorted-write list must match N_ACCESSES"
            );
            for (access, &is_write) in sorted.iter_mut().zip(writes) {
                access.is_write = is_write;
            }
        }
    });
    MemTrace { unsorted, sorted }
}

// =============================================================================
// Preprocessed trace.
// =============================================================================

/// Reconstruct the canonical, signature-independent SampleInBall schedule.
pub fn gen_sib_preprocessed(profile: MlDsaProfile, log_size: u32) -> Vec<ColEval> {
    let rows = 1usize << log_size;
    let stream_bytes = squeeze_bytes(profile);
    let core = n_core(profile);
    let accesses = n_accesses(profile);
    let tau = profile.tau();
    assert!(
        stream_bytes + N <= rows,
        "SampleInBall schedule does not fit its trace domain"
    );

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
    let mut stream_last = vec![m31(0); rows];
    let mut sign_mask: Vec<Vec<M31>> = (0..SIGN_BIT_COLS).map(|_| vec![m31(0); rows]).collect();

    for pos in 0..stream_bytes {
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
                sign_mask[u][pos] = m31(u32::from(step < tau));
            }
        }
        byte_pos[pos] = m31(pos as u32);
    }
    stream_last[stream_bytes - 1] = m31(1);
    for m in 0..N {
        let row = stream_bytes + m;
        is_c[row] = m31(1);
        c_bind_id[row] = m31(m as u32);
        // FINAL-read timestamp for address m (co-located on the c-stage row).
        ts_final[row] = m31((core + m) as u32);
    }
    acc_start[0] = m31(1); // coset row 0 zeroes the Σc² accumulator wraparound.
    if N > 0 {
        c_last[stream_bytes + N - 1] = m31(1);
    }

    // Unsorted CORE accesses occupy rows 0..N_CORE; the SORTED view occupies
    // rows 0..N_ACCESSES. sorted_start gates the first sorted-pair transition
    // (coset row 0 wraparound of the [-1,0] mask). The CORE-row layout MATCHES
    // `mem_accesses` EXACTLY: rows 0..N are init writes (addr=k, val=0, ts=k),
    // then per step t the 3 rows READ / WRITE-i / WRITE-j at ts N+3t+{0,1,2}.
    for row in 0..core {
        is_core[row] = m31(1);
    }
    for k in 0..N {
        is_init[k] = m31(1);
        core_ts[k] = m31(k as u32);
        init_addr[k] = m31(k as u32);
    }
    for t in 0..tau {
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
    for row in 0..accesses {
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
        stream_last,
    ];
    out.extend(sign_mask);
    out.into_iter().map(|v| col_eval(log_size, v)).collect()
}

// =============================================================================
// Base trace.
// =============================================================================

pub fn gen_sib_base_trace(witness: &MlDsaWitness, log_size: u32) -> Vec<ColEval> {
    let rows = 1usize << log_size;
    let srows = stream_rows(witness);
    let stream = fixed_squeeze_stream(witness);
    let stream_bytes = squeeze_bytes(witness.profile);
    let core = n_core(witness.profile);
    let mut cols: Vec<Vec<M31>> = (0..N_BASE_COLS).map(|_| vec![m31(0); rows]).collect();

    // Stream stage.
    for (pos, r) in srows.iter().enumerate() {
        cols[COL_ACTIVE][pos] = m31(u32::from(r.active));
        cols[COL_BYTE][pos] = m31(r.byte);
        cols[COL_I][pos] = m31(r.i);
        cols[COL_ACCEPT][pos] = m31(u32::from(r.accept));
        let is_placement = pos >= SIGN_BYTES;
        let reject = is_placement && r.active && !r.accept;
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
            let sign_byte = trace_sign_byte(&stream, pos);
            for u in 0..SIGN_BIT_COLS {
                cols[COL_SIGN_BIT0 + u][pos] = m31(u32::from((sign_byte >> u) & 1));
            }
        }
    }

    // c stage.
    for m in 0..N {
        let row = stream_bytes + m;
        let c = witness.digits.c[m];
        cols[COL_C][row] = enc_signed(c);
        cols[COL_CSQ][row] = m31((c * c) as u32);
    }

    // Offline-memory trace.
    let mem = mem_trace(witness);
    // Unsorted CORE accesses (rows 0..N_CORE); the N FINAL reads are emitted from
    // the c-stage rows above (COL_C is their value), so only the first N_CORE
    // unsorted accesses live here — they are exactly the non-final accesses.
    for (row, a) in mem.unsorted.iter().take(core).enumerate() {
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
        cols[COL_S_DADDR_INV][row] = if daddr == 0 {
            m31(0)
        } else {
            m31(daddr).inverse()
        };
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

// =============================================================================
// The AIR.
// =============================================================================

#[derive(Clone)]
pub struct SibEval {
    pub log_size: u32,
    pub profile: MlDsaProfile,
    /// Instance namespace. An empty value preserves single-instance identifiers.
    pub ns: String,
    /// The HashIo stream id the SIB squeeze bytes are consumed from. Per
    /// instance under a SHARED keccak relation set: `stream_base +`
    /// [`STREAM_ID_SIB_SQUEEZE`] (the standalone default is the constant).
    pub sib_stream: u32,
    pub relations: SibRelations,
}

/// Logup entries (fixed per row, gates zero inactive stages), in AIR emission
/// order: accept_lo (rc8), accept_hi (rc8), reject_lo (rc8), reject_hi (rc8),
/// hashio consume, c+1 bound (rc9), ccell use, daddr (rc8), dts (rc11),
/// mem_unsorted_core (+), mem_unsorted_final (+), mem_sorted (−) = 12; then the
/// FSM↔memory tie channels: swap accept-yield ×2, swap read-consume, swap
/// write-j-consume = 4; stepval read-yield, stepval write-i-consume = 2; signbit
/// sign-yield ×8, signbit write-j-consume = 9. Total 12 + 4 + 2 + 9 = 27.
pub const N_LOGUP_ENTRIES: usize = 12 + 4 + 2 + 9;
pub const LOGUP_BATCH: usize = 4;
pub const N_LOGUP_COLS: usize = N_LOGUP_ENTRIES.div_ceil(LOGUP_BATCH);
const N_ACC_COORD_COLS: usize = SECURE_EXTENSION_DEGREE; // Σc² accumulator.
                                                         // One QM31 passthrough column packing sorted (addr, ts, val) into coords
                                                         // 0/1/2 and the SampleInBall state-after value into coord 3.
const N_SORTED_PASS_COLS: usize = SECURE_EXTENSION_DEGREE;
pub const N_INTERACTION_COLS: usize =
    N_ACC_COORD_COLS + N_SORTED_PASS_COLS + SECURE_EXTENSION_DEGREE * N_LOGUP_COLS;

impl FrameworkEval for SibEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Every base constraint ≤ 2; LogUp batch [`LOGUP_BATCH`] = 4 over
        // degree-1 denominators gives constraint degree 5 (D ≤ 5 ⇒ +2).
        self.log_size + 2
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
        let stream_last = eval.get_preprocessed_column(pre_id("stream_last"));
        let sign_mask: Vec<E::F> = (0..SIGN_BIT_COLS)
            .map(|u| eval.get_preprocessed_column(pre_id(&sign_mask_name(u))))
            .collect();

        let active = eval.next_trace_mask();
        let byte = eval.next_trace_mask();
        let idx = eval.next_trace_mask();
        let accept = eval.next_trace_mask();
        let reject = eval.next_trace_mask();
        let accept_hi = eval.next_trace_mask();
        let reject_hi = eval.next_trace_mask();
        let c = eval.next_trace_mask();
        let csq = eval.next_trace_mask();
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
        let sign_bit: Vec<E::F> = (0..SIGN_BIT_COLS).map(|_| eval.next_trace_mask()).collect();

        // Σc² running accumulator across the c stage (interaction `[-1,0]`).
        let acc_coords: [[E::F; 2]; SECURE_EXTENSION_DEGREE] =
            core::array::from_fn(|_| eval.next_interaction_mask(INTERACTION_TRACE_IDX, [-1, 0]));
        let csq_prev = E::combine_ef(acc_coords.each_ref().map(|p| p[0].clone()));
        let csq_cur = E::combine_ef(acc_coords.each_ref().map(|p| p[1].clone()));

        // Packed passthrough, read at `[-1,0]`: coords 0/1/2 carry sorted
        // `(addr, ts, val)` and coord 3 carries the FSM state after this byte.
        let pass_coords: [[E::F; 2]; SECURE_EXTENSION_DEGREE] =
            core::array::from_fn(|_| eval.next_interaction_mask(INTERACTION_TRACE_IDX, [-1, 0]));
        let prev_s_addr = pass_coords[0][0].clone();
        let prev_s_ts = pass_coords[1][0].clone();
        let prev_s_val = pass_coords[2][0].clone();
        let prev_fsm_after = pass_coords[3][0].clone();
        // Pin the passthrough's CURRENT coords to the sorted base columns so the
        // interaction column faithfully carries (addr, ts, val).
        eval.add_constraint(pass_coords[0][1].clone() - s_addr.clone());
        eval.add_constraint(pass_coords[1][1].clone() - s_ts.clone());
        eval.add_constraint(pass_coords[2][1].clone() - s_val.clone());
        eval.add_constraint(pass_coords[3][1].clone() - idx.clone() - accept.clone());

        let one = E::F::from(M31::one());
        let two_pow_8 = E::F::from(m31(1 << 8));
        let n_minus_tau = E::F::from(m31((N - self.profile.tau()) as u32));
        let n = E::F::from(m31(N as u32));

        // C0: `active` is a boolean confined to the fixed squeeze rows. All
        // sign-source rows are active. Once inactive, a placement row is pinned
        // to state N; the ordered transition plus the fixed 49-step Swap
        // consumers prevents an early stop or a later reactivation.
        eval.add_constraint(active.clone() * (one.clone() - active.clone()));
        eval.add_constraint(active.clone() * (one.clone() - is_stream.clone()));
        eval.add_constraint(is_sign.clone() * (one.clone() - active.clone()));
        eval.add_constraint(
            is_placement.clone() * (one.clone() - active.clone()) * (idx.clone() - n.clone()),
        );

        // C1: accept / reject booleans, and their placement partition.
        eval.add_constraint(accept.clone() * (one.clone() - accept.clone()));
        eval.add_constraint(reject.clone() * (one.clone() - reject.clone()));
        // Every active placement row is exactly accept XOR reject. Inactive
        // padding and sign-source rows have both flags zero.
        eval.add_constraint(
            is_placement.clone() * active.clone() - (accept.clone() + reject.clone()),
        );

        // C1b: exact ordered FIPS 204 Alg 29 rejection FSM. Sign rows hold the
        // initial state N−τ. Every placement row, including fixed padding,
        // begins at the previous row's state-after value. Inactive rows are
        // pinned to N above and therefore hold N forever.
        eval.add_constraint(is_sign.clone() * (idx.clone() - n_minus_tau.clone()));
        eval.add_constraint(is_placement.clone() * (idx.clone() - prev_fsm_after));
        eval.add_constraint(stream_last * (idx.clone() + accept.clone() - n));

        // C2: rejection-sampling margin (the security-critical tie of c's support
        // to the stream). Accept ⇒ (i − byte) ∈ [0,256): the byte was ≤ i.
        // Reject ⇒ (byte − i − 1) ∈ [0,256): the byte was > i. Each value is
        // degree 1; the gate is a single degree-1 trace flag (accept / reject),
        // so the LogUp constraint stays at degree 2 or less.
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
        let stream_id = E::F::from(m31(self.sib_stream));
        let io_tuple = [stream_id, byte_pos.clone(), byte.clone()];
        eval.add_to_relation(RelationEntry::base(
            &self.relations.hash_io,
            -is_stream.clone(),
            &io_tuple,
        ));

        // C4: bound c+1 to [0,512), then enforce ternary directly. The rc9
        // lookup alone is only a range check; together with csq=c² below,
        // c·csq=c is the degree-2 polynomial identity c³=c.
        let c_plus1 = c.clone() + one.clone();
        eval.add_to_relation(RelationEntry::base(
            &self.relations.rc9,
            is_c.clone(),
            core::slice::from_ref(&c_plus1),
        ));
        eval.add_constraint(c.clone() * csq.clone() - c.clone());

        // C5a: witness csq = c² (degree-2 constraint, NOT involving the shifted
        // interaction mask. Keeping c² out of the accumulator constraint keeps
        // the shifted-mask degree in range. c is zero outside the c stage, so
        // the running sum below cannot be padded with unconstrained row values.
        eval.add_constraint(csq.clone() - c.clone() * c.clone());
        eval.add_constraint((one.clone() - is_c.clone()) * c.clone());
        // C5b: Σc² accumulator. csq_cur = (1 − acc_start)·csq_prev + csq. `acc_start`
        // (coset row 0) zeroes the `[-1,0]` wraparound; stream rows carry csq=0 so
        // the sum stays 0 until the c stage, then accumulates c². Degree 1 in the
        // mask constraint (csq is a base cell).
        let csq_prev_gated = E::EF::from(one.clone() - acc_start.clone()) * csq_prev;
        eval.add_constraint(csq_cur.clone() - (csq_prev_gated + E::EF::from(csq.clone())));

        // C6: final c-row gate — the constrained running accumulator is Σc²=τ.
        // This must use `csq_cur` directly; a separate base accumulator would be
        // free witness unless explicitly tied to the interaction column.
        let tau = E::EF::from(E::F::from(m31(self.profile.tau() as u32)));
        eval.add_constraint(E::EF::from(c_last.clone()) * (csq_cur.clone() - tau));

        // C7: c-binding — USE the coeffs C cell (c_bind_id = m, c).
        let ctuple = [c_bind_id.clone(), c.clone()];
        eval.add_to_relation(RelationEntry::base(
            &self.relations.ccell,
            is_c.clone(),
            &ctuple,
        ));

        // =====================================================================
        // C8: offline-memory swap replay. Each row has degree 2 or less.
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
        // The passthrough pins above have degree 1. No constraint exceeds degree
        // 2, so the `[-1,0]` masks keep the bound at log_size+1.
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
            not_first.clone()
                * (s_daddr.clone() * s_daddr_inv.clone() - (one.clone() - s_same.clone())),
        );
        // The first sorted row opens a new cell, so same == 0.
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
        let u_tuple = [u_addr.clone(), u_val.clone(), u_ts.clone(), u_write.clone()];
        eval.add_to_relation(RelationEntry::base(
            &self.relations.mem,
            is_core.clone(),
            &u_tuple,
        ));
        // FINAL read: (addr=m=c_bind_id, value=COL_C=c, ts=ts_final), gated is_c.
        let final_tuple = [
            c_bind_id.clone(),
            c.clone(),
            ts_final.clone(),
            E::F::from(m31(0)),
        ];
        eval.add_to_relation(RelationEntry::base(
            &self.relations.mem,
            is_c.clone(),
            &final_tuple,
        ));
        let s_tuple = [s_addr.clone(), s_val.clone(), s_ts.clone(), s_write.clone()];
        eval.add_to_relation(RelationEntry::base(
            &self.relations.mem,
            -is_sorted.clone(),
            &s_tuple,
        ));

        // =====================================================================
        // C9: FSM↔memory schedule pins. Without these, the core access columns
        // (u_addr/u_val/u_ts/u_write) are free witness values. Only u_write
        // booleanity and the Mem yield constrain them, so a prover could commit an arbitrary
        // memory-consistent history and the swap-replay (C8) would be vacuous.
        // The pins force the row roles, canonical timestamps, init writes, and the
        // schedule-determined write-i address. All constraints have degree 2
        // or less:
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
        eval.add_constraint(
            is_wr_i_row.clone() * (u_addr.clone() - n_minus_tau.clone() - step_no.clone()),
        );

        // =====================================================================
        // C10: FSM↔memory tie channels. These bind every CORE access back to the
        // FSM rows so the access list is a deterministic function of the accepted
        // bytes and FIPS sign bits. All constraints have degree 2 or less:
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
        // exactly one accept row carries each t. Thus, there are exactly τ
        // accepts. Extra or missing accepts unbalance the Swap channel.
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
        let two = E::F::from(m31(2));
        let eight = E::F::from(m31(SIGN_BIT_COLS as u32));
        let mut sign_recomposition = E::F::from(m31(0));
        let mut bit_weight = E::F::from(m31(1));
        for u in 0..SIGN_BIT_COLS {
            let bit = sign_bit[u].clone();
            eval.add_constraint(bit.clone() * (one.clone() - bit.clone()));
            sign_recomposition += bit_weight.clone() * bit.clone();
            bit_weight += bit_weight.clone();

            let sign_tuple = [
                byte_pos.clone() * eight.clone() + E::F::from(m31(u as u32)),
                one.clone() - two.clone() * bit,
            ];
            eval.add_to_relation(RelationEntry::base(
                &self.relations.signbit,
                sign_mask[u].clone(),
                &sign_tuple,
            ));
        }
        eval.add_constraint(is_sign * (byte - sign_recomposition));
        let wrj_val_tuple = [step_no.clone(), u_val.clone()];
        eval.add_to_relation(RelationEntry::base(
            &self.relations.signbit,
            -is_wr_j_row,
            &wrj_val_tuple,
        ));

        eval.finalize_logup_batched(LOGUP_BATCH);
        eval
    }
}

// =============================================================================
// Interaction trace.
// =============================================================================

pub struct SibInteraction {
    pub trace: Vec<ColEval>,
    pub claimed_sum: SecureField,
    pub rc_uses: RcUses,
    /// The stream bytes that the FSM consumes.
    pub stream_bytes: Vec<u8>,
    /// The (c_bind_id, c) pairs (for the test coeffs-C producer).
    pub ccell_uses: Vec<(u32, u32)>,
}

/// Witness-only outputs needed for base multiplicity columns and standalone
/// balancers. No Fiat–Shamir relation values are required.
pub struct SibMetadata {
    pub rc_uses: RcUses,
    pub stream_bytes: Vec<u8>,
}

pub fn gen_sib_metadata(witness: &MlDsaWitness) -> SibMetadata {
    let srows = stream_rows(witness);
    let mem = mem_trace(witness);
    gen_sib_metadata_from_parts(witness, &srows, &mem)
}

fn gen_sib_metadata_from_parts(
    witness: &MlDsaWitness,
    srows: &[StreamRow],
    mem: &MemTrace,
) -> SibMetadata {
    let mut rc_uses = RcUses::new();
    let mut stream_bytes = Vec::with_capacity(srows.len());
    for (row, stream_row) in srows.iter().enumerate() {
        let byte = stream_row.byte;
        stream_bytes.push(byte as u8);
        if stream_row.accept {
            let margin = (stream_row.i - byte) as usize;
            rc_uses.rc8[margin & 0xff] += 1;
            rc_uses.rc8[margin >> 8] += 1;
        } else if row >= SIGN_BYTES && stream_row.active {
            let margin = (byte - stream_row.i - 1) as usize;
            rc_uses.rc8[margin & 0xff] += 1;
            rc_uses.rc8[margin >> 8] += 1;
        }
    }

    for &c in &witness.digits.c {
        rc_uses.rc9[(c + 1) as usize] += 1;
    }

    // Offline-memory range uses over the sorted view: daddr (rc8) on every
    // non-first sorted row; dts (rc11) whenever the address repeats.
    for pair in mem.sorted.windows(2) {
        let previous = &pair[0];
        let current = &pair[1];
        rc_uses.rc8[(current.addr - previous.addr) as usize] += 1;
        if current.addr == previous.addr {
            rc_uses.rc11[(current.ts - previous.ts - 1) as usize] += 1;
        }
    }

    SibMetadata {
        rc_uses,
        stream_bytes,
    }
}

pub fn gen_sib_interaction(
    witness: &MlDsaWitness,
    log_size: u32,
    sib_stream: u32,
    relations: &SibRelations,
) -> SibInteraction {
    let rows = 1usize << log_size;
    let slen = squeeze_bytes(witness.profile);
    let core = n_core(witness.profile);
    let tau = witness.profile.tau();
    let srows = stream_rows(witness);
    let stream = fixed_squeeze_stream(witness);

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
        .map(|coord| {
            col_eval(
                log_size,
                acc.iter().map(|v| v.to_m31_array()[coord]).collect(),
            )
        })
        .collect();

    // Offline-memory: sorted view per coset row (row r ↦ sorted[r] for r<N_ACCESSES).
    let mem = mem_trace(witness);
    let metadata = gen_sib_metadata_from_parts(witness, &srows, &mem);
    // Packed passthrough QM31 column: sorted (addr, ts, val) in coords 0/1/2,
    // and the ordered SampleInBall state-after value in coord 3.
    let pass: Vec<SecureField> = (0..rows)
        .map(|row| {
            let (addr, ts, value) = mem.sorted.get(row).map_or((m31(0), m31(0), m31(0)), |a| {
                (m31(a.addr), m31(a.ts), enc_signed(a.value))
            });
            let fsm_after = srows
                .get(row)
                .map_or(m31(0), |r| m31(r.i + u32::from(r.accept)));
            SecureField::from_m31_array([addr, ts, value, fsm_after])
        })
        .collect();
    for coord in 0..N_SORTED_PASS_COLS {
        trace.push(col_eval(
            log_size,
            pass.iter().map(|v| v.to_m31_array()[coord]).collect(),
        ));
    }

    let row_lookup = circle_row_to_coset(log_size);
    let vec_rows = 1usize << (log_size - stwo::prover::backend::simd::m31::LOG_N_LANES);

    // Per-row precompute.
    #[derive(Clone, Copy)]
    enum Row {
        Stream {
            byte: u32,
            i: u32,
            accept: bool,
            reject: bool,
        },
        C {
            m: u32,
            c: i128,
        },
    }
    let coset_row: Vec<Option<Row>> = (0..rows)
        .map(|coset| {
            if coset < slen {
                let r = &srows[coset];
                let reject = coset >= SIGN_BYTES && r.active && !r.accept;
                Some(Row::Stream {
                    byte: r.byte,
                    i: r.i,
                    accept: r.accept,
                    reject,
                })
            } else if coset < slen + N {
                let m = coset - slen;
                Some(Row::C {
                    m: m as u32,
                    c: witness.digits.c[m],
                })
            } else {
                None
            }
        })
        .collect();

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
    // reject_hi(rc8), hashio(−), c+1 bound(rc9), ccell(+).
    push(
        &|coset| match coset_row[coset] {
            Some(Row::Stream {
                byte, i, accept, ..
            }) if accept => {
                let lo = (i - byte) & 0xff;
                (one, relations.rc8.combine(&[m31(lo)]))
            }
            _ => (zero, one),
        },
        &mut entries,
        &mut claimed,
    );
    push(
        &|coset| match coset_row[coset] {
            Some(Row::Stream {
                byte, i, accept, ..
            }) if accept => {
                let hi = (i - byte) >> 8;
                (one, relations.rc8.combine(&[m31(hi)]))
            }
            _ => (zero, one),
        },
        &mut entries,
        &mut claimed,
    );
    push(
        &|coset| match coset_row[coset] {
            Some(Row::Stream {
                byte, i, reject, ..
            }) if reject => {
                let lo = (byte - i - 1) & 0xff;
                (one, relations.rc8.combine(&[m31(lo)]))
            }
            _ => (zero, one),
        },
        &mut entries,
        &mut claimed,
    );
    push(
        &|coset| match coset_row[coset] {
            Some(Row::Stream {
                byte, i, reject, ..
            }) if reject => {
                let hi = (byte - i - 1) >> 8;
                (one, relations.rc8.combine(&[m31(hi)]))
            }
            _ => (zero, one),
        },
        &mut entries,
        &mut claimed,
    );
    // hashio consume (−)
    push(
        &|coset| match coset_row[coset] {
            Some(Row::Stream { byte, .. }) => {
                let tuple = [m31(sib_stream), m31(coset as u32), m31(byte)];
                (-one, relations.hash_io.combine(&tuple))
            }
            _ => (zero, one),
        },
        &mut entries,
        &mut claimed,
    );
    // c+1 range bound (ternary itself is enforced by c³=c in the AIR).
    push(
        &|coset| match coset_row[coset] {
            Some(Row::C { c, .. }) => {
                let v = (c + 1) as u32;
                (one, relations.rc9.combine(&[m31(v)]))
            }
            _ => (zero, one),
        },
        &mut entries,
        &mut claimed,
    );
    // ccell use (+)
    push(
        &|coset| match coset_row[coset] {
            Some(Row::C { m, c }) => {
                let tuple = [m31(m), enc_signed(c)];
                (one, relations.ccell.combine(&tuple))
            }
            _ => (zero, one),
        },
        &mut entries,
        &mut claimed,
    );

    // daddr (rc8) — sorted rows 1..N_ACCESSES (gate not_first).
    push(
        &|coset| {
            if coset >= 1 && coset < mem.sorted.len() {
                let daddr = mem.sorted[coset].addr - mem.sorted[coset - 1].addr;
                (one, relations.rc8.combine(&[m31(daddr)]))
            } else {
                (zero, one)
            }
        },
        &mut entries,
        &mut claimed,
    );
    // dts (rc11) — sorted rows where addr repeats (gate same).
    push(
        &|coset| {
            if coset >= 1
                && coset < mem.sorted.len()
                && mem.sorted[coset].addr == mem.sorted[coset - 1].addr
            {
                let dts = mem.sorted[coset].ts - mem.sorted[coset - 1].ts - 1;
                (one, relations.rc11.combine(&[m31(dts)]))
            } else {
                (zero, one)
            }
        },
        &mut entries,
        &mut claimed,
    );
    // Mem unsorted CORE (+): rows 0..N_CORE.
    push(
        &|coset| {
            if coset < core {
                let a = &mem.unsorted[coset];
                (
                    one,
                    relations.mem.combine(&[
                        m31(a.addr),
                        enc_signed(a.value),
                        m31(a.ts),
                        m31(u32::from(a.is_write)),
                    ]),
                )
            } else {
                (zero, one)
            }
        },
        &mut entries,
        &mut claimed,
    );
    // Mem unsorted FINAL read (+): co-located on c-stage rows (addr=m, val=c,
    // ts=N_CORE+m). Reuses the committed COL_C value.
    push(
        &|coset| match coset_row[coset] {
            Some(Row::C { m, c }) => {
                let ts = (core as u32) + m;
                (
                    one,
                    relations
                        .mem
                        .combine(&[m31(m), enc_signed(c), m31(ts), m31(0)]),
                )
            }
            _ => (zero, one),
        },
        &mut entries,
        &mut claimed,
    );
    // Mem sorted (−): rows 0..N_ACCESSES.
    push(
        &|coset| {
            if coset < mem.sorted.len() {
                let a = &mem.sorted[coset];
                (
                    -one,
                    relations.mem.combine(&[
                        m31(a.addr),
                        enc_signed(a.value),
                        m31(a.ts),
                        m31(u32::from(a.is_write)),
                    ]),
                )
            } else {
                (zero, one)
            }
        },
        &mut entries,
        &mut claimed,
    );

    // =====================================================================
    // FSM↔memory tie channels (must mirror the AIR C10 emission order EXACTLY):
    // swap accept-yield ×2, swap read-consume, swap wr-j-consume, stepval
    // read-yield, stepval wr-i-consume, signbit sign-yield ×8, signbit
    // wr-j-consume. Core rows live at cosets 0..N_CORE: coset<N ⇒ init; else
    // t=(coset−N)/3, r=(coset−N)%3 (0=read, 1=write-i, 2=write-j).
    // =====================================================================
    let core_role = |coset: usize| -> Option<(usize, usize)> {
        // Returns (step_t, role) for a step access row; None for init/non-core.
        if (N..core).contains(&coset) {
            let off = coset - N;
            Some((off / 3, off % 3))
        } else {
            None
        }
    };
    let n_minus_tau = m31((N - tau) as u32);

    // Swap accept-yield (×2): (idx−(N−τ), byte) on accept stream rows.
    for _ in 0..2 {
        push(
            &|coset| match coset_row[coset] {
                Some(Row::Stream {
                    byte, i, accept, ..
                }) if accept => {
                    let key = m31(i) - n_minus_tau;
                    (one, relations.swap.combine(&[key, m31(byte)]))
                }
                _ => (zero, one),
            },
            &mut entries,
            &mut claimed,
        );
    }
    // Swap read-consume (−): (step_no, u_addr) on read rows (role 0).
    push(
        &|coset| match core_role(coset) {
            Some((t, 0)) => {
                let a = &mem.unsorted[coset];
                (-one, relations.swap.combine(&[m31(t as u32), m31(a.addr)]))
            }
            _ => (zero, one),
        },
        &mut entries,
        &mut claimed,
    );
    // Swap write-j-consume (−): (step_no, u_addr) on write-j rows (role 2).
    push(
        &|coset| match core_role(coset) {
            Some((t, 2)) => {
                let a = &mem.unsorted[coset];
                (-one, relations.swap.combine(&[m31(t as u32), m31(a.addr)]))
            }
            _ => (zero, one),
        },
        &mut entries,
        &mut claimed,
    );
    // StepVal read-yield (+): (step_no, u_val) on read rows (role 0).
    push(
        &|coset| match core_role(coset) {
            Some((t, 0)) => {
                let a = &mem.unsorted[coset];
                (
                    one,
                    relations
                        .stepval
                        .combine(&[m31(t as u32), enc_signed(a.value)]),
                )
            }
            _ => (zero, one),
        },
        &mut entries,
        &mut claimed,
    );
    // StepVal write-i-consume (−): (step_no, u_val) on write-i rows (role 1).
    push(
        &|coset| match core_role(coset) {
            Some((t, 1)) => {
                let a = &mem.unsorted[coset];
                (
                    -one,
                    relations
                        .stepval
                        .combine(&[m31(t as u32), enc_signed(a.value)]),
                )
            }
            _ => (zero, one),
        },
        &mut entries,
        &mut claimed,
    );
    // SignBit sign-yield (×8): (8·byte_pos+u, 1−2·bit) on sign rows, numerator =
    // mask_u (1 iff step 8b+u < τ).
    for u in 0..SIGN_BIT_COLS {
        push(
            &|coset| {
                if coset < SIGN_BYTES {
                    let step = SIGN_BIT_COLS * coset + u;
                    if step < tau {
                        let bit = (trace_sign_byte(&stream, coset) >> u) & 1;
                        let value = if bit == 1 { -1 } else { 1 };
                        return (
                            one,
                            relations
                                .signbit
                                .combine(&[m31(step as u32), enc_signed(value)]),
                        );
                    }
                }
                (zero, one)
            },
            &mut entries,
            &mut claimed,
        );
    }
    // SignBit write-j-consume (−): (step_no, u_val) on write-j rows (role 2).
    push(
        &|coset| match core_role(coset) {
            Some((t, 2)) => {
                let a = &mem.unsorted[coset];
                (
                    -one,
                    relations
                        .signbit
                        .combine(&[m31(t as u32), enc_signed(a.value)]),
                )
            }
            _ => (zero, one),
        },
        &mut entries,
        &mut claimed,
    );

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

    let ccell_uses = witness
        .digits
        .c
        .iter()
        .enumerate()
        .map(|(m, &c)| (m as u32, enc_signed(c).0))
        .collect();
    let SibMetadata {
        rc_uses,
        stream_bytes,
    } = metadata;
    SibInteraction {
        trace,
        claimed_sum,
        rc_uses,
        stream_bytes,
        ccell_uses,
    }
}
