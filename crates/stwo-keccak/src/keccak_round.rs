//! The `keccak_round` component: one trace row proves one Keccak-f[1600]
//! round (theta, rho, pi, chi, iota) over **spread** 8-bit limbs.
//!
//! ## Spread-form fusion (M3b)
//!
//! The Keccak state is carried in spread form (`spread(b) = Σ bᵢ·4ⁱ`, see
//! [`crate::utils`]) across every round and across the `KeccakRound` /
//! `KeccakStateRelation` links. Working in spread form collapses the round's
//! lookups:
//!
//! - **xor3** — XOR of up to three spread bytes is ONE lookup with a degree-1
//!   sum key `s1+s2+s3` into a dense `2^16` table. Theta's 5-way column parity
//!   `C[x]` is two chained xor3 (vs four `xor_8_8`); the theta-apply
//!   `res = S ⊕ C[x−1] ⊕ rotl(C[x+1],1)` is one *fused* xor3 (vs a separate `D`
//!   then a second xor); chi's closing `a ⊕ (¬b'∧b'')` is one xor3 whose third
//!   input is 0 — or, on lane 0, `spread(rc)` so **iota is folded in for free**.
//! - **andnot** — `(¬b'∧b'')` is ONE lookup with key `spread(b')+2·spread(b'')`
//!   into a dense `2^16` table (vs the byte-pair `chi_8_8`).
//! - **split_r** — the rho/theta sub-byte rotation splits a spread byte at bit
//!   boundary `2r` via the spread split tables; `spread` is additive across the
//!   disjoint hi/lo ranges, so `spread_lo = spread_byte − spread_hi·4^r` is a
//!   linear expression and the recombination is
//!   `res = spread_hi[i] + spread_lo[(i+1)%8]·4^{8-r}`.
//!
//! Every committed limb is either a lookup *output* (xor3/andnot result, split
//! hi) — certified as a valid spread value by its dense/self-certifying table —
//! or a lookup *key* built as a degree-1 combo of such certified limbs (so the
//! lookup that consumes it certifies it in turn). The incoming state limbs are
//! certified by the sponge's `conv` boundary and carried unchanged.

#![allow(non_snake_case)]

use num_traits::{One, Zero};
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, ParallelIterator};
use serde::{Deserialize, Serialize};
use stwo::core::channel::Channel;
use stwo::core::fields::m31::{BaseField, M31};
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::core::pcs::TreeVec;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES, N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::BackendForChannel;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo_air_utils::trace::component_trace::ComponentTrace;
use stwo_air_utils_derive::{IterMut, ParIterMut, Uninitialized};
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
};

use crate::constants::{
    N_BYTES_IN_STATE, N_BYTES_IN_U64, N_LANES_KECCAK, RHO_OFFSETS, SQRT_N_LANES,
};
use crate::relations::KeccakRelations;
use crate::utils::{spread_u32, unspread_u32, Enabler};

/// Round constants including the trailing dummy "next" value (index 24).
const IOTA_RC_PLUS: [u64; 25] = crate::constants::IOTA_RC;

// ── Lookup budgets per row (must match the AIR's `add_to_relation` order) ──

const N_KECCAK_ROUND_LOOKUPS: usize = 2;

/// xor3 uses: theta C-parity (2 per byte · 5 · 8), theta-apply (25 · 8), chi
/// closing (25 · 8, folding iota on lane 0).
pub const N_XOR3_C: usize = 2 * SQRT_N_LANES * N_BYTES_IN_U64; // 80
pub const N_XOR3_THETA_APPLY: usize = N_LANES_KECCAK * N_BYTES_IN_U64; // 200
pub const N_XOR3_CHI_CLOSE: usize = N_LANES_KECCAK * N_BYTES_IN_U64; // 200
pub const N_XOR3_LOOKUPS: usize = N_XOR3_C + N_XOR3_THETA_APPLY + N_XOR3_CHI_CLOSE; // 480

/// andnot uses: one per chi byte.
pub const N_ANDNOT_LOOKUPS: usize = N_LANES_KECCAK * N_BYTES_IN_U64; // 200

/// split uses: the theta C-rotation (rotr 63, r=7) is 5 lanes · 8 bytes, and
/// rho does the 22 lanes with r≠0 · 8 bytes. Byte-only lanes emit none.
pub const N_SPLIT_C_ROT: usize = SQRT_N_LANES * N_BYTES_IN_U64; // 40
pub const N_SPLIT_RHO: usize = (N_LANES_KECCAK - 3) * N_BYTES_IN_U64; // 176
pub const N_SPLIT_LOOKUPS: usize = N_SPLIT_C_ROT + N_SPLIT_RHO; // 216

/// hi-limb witness columns: one per split lookup.
const N_HI_WITNESS: usize = N_SPLIT_LOOKUPS;

const N_COLUMNS: usize = 1
    + 2 * N_BYTES_IN_U64            // current_rc + next_rc (byte constants)
    + N_BYTES_IN_STATE             // initial spread state
    + N_XOR3_C                     // theta C-parity intermediates (t + C)
    + N_HI_WITNESS                 // spread-hi witnesses for all rotations
    + N_XOR3_THETA_APPLY           // theta-apply outputs (res_S)
    + N_ANDNOT_LOOKUPS             // chi andnot outputs
    + N_XOR3_CHI_CLOSE; // chi closing outputs (new state, incl. iota)

const N_TOTAL_LOOKUPS: usize =
    N_KECCAK_ROUND_LOOKUPS + N_XOR3_LOOKUPS + N_ANDNOT_LOOKUPS + N_SPLIT_LOOKUPS;

/// Logup fractions batched per interaction column (`finalize_logup_batched`).
/// Batch 4 needs constraint degree `1 + 4·1 = 5 ≤ D5`, available at
/// `max_constraint_log_degree_bound = log + 2`.
pub const LOGUP_BATCH: usize = 4;

const N_INTERACTION_COLUMNS: usize =
    SECURE_EXTENSION_DEGREE * N_TOTAL_LOOKUPS.div_ceil(LOGUP_BATCH);

/// Number of base + interaction committed cells for one row (one packed
/// permutation-round across `N_LANES` SIMD lanes).
pub const N_COMMITTED_COLUMNS: usize = N_COLUMNS + N_INTERACTION_COLUMNS;

#[derive(Default)]
struct Idx {
    col: usize,
    xor3: usize,
    andnot: usize,
    split: usize,
}

pub struct InteractionClaimData {
    pub lookup_data: LookupData,
    pub non_padded_length: usize,
}

#[derive(Uninitialized, IterMut, ParIterMut)]
pub struct LookupData {
    pub keccak_round: [Vec<[PackedM31; N_BYTES_IN_STATE + N_BYTES_IN_U64]>; N_KECCAK_ROUND_LOOKUPS],
    /// `[key, out]` — key is the degree-1 sum, out the spread(xor) result.
    pub xor3: [Vec<[PackedM31; 2]>; N_XOR3_LOOKUPS],
    /// `[u, out]` — `u = spread(b')+2·spread(b'')`, out = spread(¬b'∧b'').
    pub andnot: [Vec<[PackedM31; 2]>; N_ANDNOT_LOOKUPS],
    /// `[shift_r, spread_byte, spread_hi, spread_lo]`; `shift_r` selects the
    /// `Split*` relation and is constant across SIMD lanes.
    pub split: [Vec<[PackedM31; 4]>; N_SPLIT_LOOKUPS],
}

#[derive(Copy, Clone, Default, Serialize, Deserialize, Debug)]
pub struct Claim {
    pub log_size: u32,
}

impl Claim {
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        TreeVec::new(vec![
            vec![],
            vec![self.log_size; N_COLUMNS],
            vec![self.log_size; N_INTERACTION_COLUMNS],
        ])
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    /// Build the round trace. Input rows are `[spread_state(200) | round_index]`.
    pub fn generate_trace(
        mut input: Vec<[PackedM31; N_BYTES_IN_STATE + 1]>,
        invocations: usize,
    ) -> (Self, ComponentTrace<N_COLUMNS>, InteractionClaimData)
    where
        SimdBackend: BackendForChannel<Blake2sMerkleChannel>,
    {
        let log_size = std::cmp::max(invocations.next_power_of_two().ilog2(), LOG_N_LANES);
        input.resize(
            1 << (log_size - LOG_N_LANES),
            [PackedM31::zero(); N_BYTES_IN_STATE + 1],
        );
        let enabler_col = Enabler::new(invocations);

        let (mut trace, mut lookup_data) = unsafe {
            (
                ComponentTrace::<N_COLUMNS>::uninitialized(log_size),
                LookupData::uninitialized(log_size - LOG_N_LANES),
            )
        };

        (
            trace.par_iter_mut(),
            input.into_par_iter(),
            lookup_data.par_iter_mut(),
        )
            .into_par_iter()
            .enumerate()
            .for_each(|(row_index, (mut row, input, mut lookup_data))| {
                fill_row(
                    row_index,
                    &enabler_col,
                    &input,
                    &mut row[..],
                    &mut lookup_data,
                );
            });

        let claim = Self { log_size };
        (
            claim,
            trace,
            InteractionClaimData {
                lookup_data,
                non_padded_length: invocations,
            },
        )
    }
}

// ── Byte-lane views (trace-gen works on bytes, commits spread) ──

/// A 64-bit lane as 8 per-SIMD-lane byte arrays.
type ByteLane = [[u32; N_LANES]; N_BYTES_IN_U64];

/// Extract the byte value of a spread limb per SIMD lane.
fn unspread_lane(limb: PackedM31) -> [u32; N_LANES] {
    let a = limb.to_array();
    std::array::from_fn(|l| unspread_u32(a[l].0))
}

/// Spread a per-lane byte array into a packed limb.
fn spread_lane(bytes: &[u32; N_LANES]) -> PackedM31 {
    PackedM31::from_array(std::array::from_fn(|l| M31::from(spread_u32(bytes[l]))))
}

fn xor_bytes(a: &[u32; N_LANES], b: &[u32; N_LANES]) -> [u32; N_LANES] {
    std::array::from_fn(|l| a[l] ^ b[l])
}

fn andnot_bytes(b1: &[u32; N_LANES], b2: &[u32; N_LANES]) -> [u32; N_LANES] {
    std::array::from_fn(|l| ((!b1[l]) & b2[l]) & 0xFF)
}

#[allow(clippy::type_complexity)]
fn fill_row(
    row_index: usize,
    enabler_col: &Enabler,
    input: &[PackedM31; N_BYTES_IN_STATE + 1],
    row: &mut [&mut PackedM31],
    lookup_data: &mut LookupDataMutChunk<'_>,
) {
    let mut idx = Idx::default();
    *row[idx.col] = enabler_col.packed_at(row_index);
    idx.col += 1;

    // Round constants for this round and the next, in SPREAD form (the link
    // markers). Carrying them spread lets iota fold directly into lane 0's
    // closing xor3 with no extra column.
    let round_of = |lane_val: u32| lane_val as usize;
    let current_rc: [PackedM31; N_BYTES_IN_U64] = std::array::from_fn(|i| {
        PackedM31::from_array(std::array::from_fn(|lane| {
            let r = round_of(input[N_BYTES_IN_STATE].to_array()[lane].0);
            M31::from(spread_u32(IOTA_RC_PLUS[r].to_le_bytes()[i] as u32))
        }))
    });
    for b in current_rc {
        *row[idx.col] = b;
        idx.col += 1;
    }
    let next_rc: [PackedM31; N_BYTES_IN_U64] = std::array::from_fn(|i| {
        PackedM31::from_array(std::array::from_fn(|lane| {
            let r = round_of(input[N_BYTES_IN_STATE].to_array()[lane].0) + 1;
            M31::from(spread_u32(IOTA_RC_PLUS[r].to_le_bytes()[i] as u32))
        }))
    });
    for b in next_rc {
        *row[idx.col] = b;
        idx.col += 1;
    }

    // Initial spread state columns + the incoming chain link.
    for x in &input[..N_BYTES_IN_STATE] {
        *row[idx.col] = *x;
        idx.col += 1;
    }
    let round_data: Vec<PackedM31> = current_rc
        .iter()
        .chain(input[..N_BYTES_IN_STATE].iter())
        .cloned()
        .collect();
    *lookup_data.keccak_round[0] = round_data.try_into().unwrap();

    // Per-lane byte view of the incoming state.
    let mut S: [ByteLane; N_LANES_KECCAK] = std::array::from_fn(|lane| {
        std::array::from_fn(|i| unspread_lane(input[lane * N_BYTES_IN_U64 + i]))
    });
    // Spread limb of the incoming state, for building xor3 keys as sums.
    let S0_spread: [[PackedM31; N_BYTES_IN_U64]; N_LANES_KECCAK] =
        std::array::from_fn(|lane| std::array::from_fn(|i| input[lane * N_BYTES_IN_U64 + i]));

    // ── Theta: C[x] = xor of 5 column lanes via 2 chained xor3 ──
    let mut C_bytes: [ByteLane; SQRT_N_LANES] = std::array::from_fn(|_| Default::default());
    let mut C_spread: [[PackedM31; N_BYTES_IN_U64]; SQRT_N_LANES] =
        std::array::from_fn(|_| [PackedM31::zero(); N_BYTES_IN_U64]);
    for x in 0..SQRT_N_LANES {
        for i in 0..N_BYTES_IN_U64 {
            // t = s0 ^ s1 ^ s2
            let t = xor_bytes(&xor_bytes(&S[x][i], &S[x + 5][i]), &S[x + 10][i]);
            let t_spread = write_xor3(
                &mut idx,
                row,
                lookup_data,
                &S0_spread[x][i],
                &S0_spread[x + 5][i],
                &S0_spread[x + 10][i],
                &t,
            );
            // C = t ^ s3 ^ s4
            let c = xor_bytes(&xor_bytes(&t, &S[x + 15][i]), &S[x + 20][i]);
            let c_spread = write_xor3(
                &mut idx,
                row,
                lookup_data,
                &t_spread,
                &S0_spread[x + 15][i],
                &S0_spread[x + 20][i],
                &c,
            );
            C_bytes[x][i] = c;
            C_spread[x][i] = c_spread;
        }
    }

    // rotl(C[x+1], 1) == rotr(C[x+1], 63): r=7 split lookups on spread bytes.
    let mut Crot_bytes: [ByteLane; SQRT_N_LANES] = std::array::from_fn(|_| Default::default());
    let mut Crot_spread: [[PackedM31; N_BYTES_IN_U64]; SQRT_N_LANES] =
        std::array::from_fn(|_| [PackedM31::zero(); N_BYTES_IN_U64]);
    for x in 0..SQRT_N_LANES {
        let xp1 = (x + 1) % SQRT_N_LANES;
        let (rb, rs) = rotr_split(
            &C_bytes[xp1],
            &C_spread[xp1],
            63,
            &mut idx,
            row,
            lookup_data,
        );
        Crot_bytes[x] = rb;
        Crot_spread[x] = rs;
    }

    // ── Theta-apply (fused): res_S[x+5y] = S ^ C[x-1] ^ rotl(C[x+1],1) ──
    // Keys use the *incoming* spread state (S0_spread), C, and Crot — all
    // pre-theta values. Outputs become the post-theta spread state.
    let mut S_spread: [[PackedM31; N_BYTES_IN_U64]; N_LANES_KECCAK] =
        std::array::from_fn(|_| [PackedM31::zero(); N_BYTES_IN_U64]);
    for y in 0..SQRT_N_LANES {
        for x in 0..SQRT_N_LANES {
            let id = x + 5 * y;
            let xm1 = (x + 4) % SQRT_N_LANES;
            for i in 0..N_BYTES_IN_U64 {
                let v = xor_bytes(&xor_bytes(&S[id][i], &C_bytes[xm1][i]), &Crot_bytes[x][i]);
                let vs = write_xor3(
                    &mut idx,
                    row,
                    lookup_data,
                    &S0_spread[id][i],
                    &C_spread[xm1][i],
                    &Crot_spread[x][i],
                    &v,
                );
                S[id][i] = v;
                S_spread[id][i] = vs;
            }
        }
    }

    // ── Rho + Pi ── (spread split rotations)
    let mut B_bytes: [ByteLane; N_LANES_KECCAK] = std::array::from_fn(|_| Default::default());
    let mut B_spread: [[PackedM31; N_BYTES_IN_U64]; N_LANES_KECCAK] =
        std::array::from_fn(|_| [PackedM31::zero(); N_BYTES_IN_U64]);
    for x in 0..SQRT_N_LANES {
        for y in 0..SQRT_N_LANES {
            let off = RHO_OFFSETS[x][y];
            let rotr = if off == 0 { 0 } else { 64 - off };
            let dst = 5 * y + ((2 * x + 3 * y) % SQRT_N_LANES);
            let (rb, rs) = rotr_split(
                &S[x + 5 * y],
                &S_spread[x + 5 * y],
                rotr,
                &mut idx,
                row,
                lookup_data,
            );
            B_bytes[dst] = rb;
            B_spread[dst] = rs;
        }
    }

    // ── Chi + Iota (fused closing xor3) ──
    // Chi reads B in M3's `5x+y` convention and writes the output state at
    // `x+5y` (the two together are the KAT-validated rho/pi/chi layout). Iota
    // folds into the output-lane-0 closing xor3 (out_idx == 0).
    for y in 0..SQRT_N_LANES {
        for x in 0..SQRT_N_LANES {
            let a_idx = 5 * x + y;
            let b1_idx = 5 * ((x + 1) % SQRT_N_LANES) + y;
            let b2_idx = 5 * ((x + 2) % SQRT_N_LANES) + y;
            let out_idx = x + 5 * y;
            for i in 0..N_BYTES_IN_U64 {
                // andnot = (!b1) & b2
                let an = andnot_bytes(&B_bytes[b1_idx][i], &B_bytes[b2_idx][i]);
                let an_spread = write_andnot(
                    &mut idx,
                    row,
                    lookup_data,
                    &B_spread[b1_idx][i],
                    &B_spread[b2_idx][i],
                    &an,
                );
                // closing: out = a ^ andnot [ ^ rc on output lane 0 byte i ]
                let mut out = xor_bytes(&B_bytes[a_idx][i], &an);
                let rc_spread = if out_idx == 0 {
                    let rc_byte = unspread_lane(current_rc[i]);
                    out = xor_bytes(&out, &rc_byte);
                    current_rc[i]
                } else {
                    PackedM31::zero()
                };
                let out_spread = write_xor3(
                    &mut idx,
                    row,
                    lookup_data,
                    &B_spread[a_idx][i],
                    &an_spread,
                    &rc_spread,
                    &out,
                );
                S[out_idx][i] = out;
                S_spread[out_idx][i] = out_spread;
            }
        }
    }

    // Outgoing chain link (spread state).
    let mut out = [PackedM31::zero(); N_BYTES_IN_STATE];
    for lane in 0..N_LANES_KECCAK {
        let base = lane * N_BYTES_IN_U64;
        for i in 0..N_BYTES_IN_U64 {
            out[base + i] = S_spread[lane][i];
        }
    }
    let next_data: Vec<PackedM31> = next_rc.iter().chain(out.iter()).cloned().collect();
    *lookup_data.keccak_round[1] = next_data.try_into().unwrap();
}

/// Write one xor3: commit the spread output limb, record `[key, out]`.
#[allow(clippy::too_many_arguments)]
fn write_xor3(
    idx: &mut Idx,
    row: &mut [&mut PackedM31],
    lookup_data: &mut LookupDataMutChunk<'_>,
    s1: &PackedM31,
    s2: &PackedM31,
    s3: &PackedM31,
    out_bytes: &[u32; N_LANES],
) -> PackedM31 {
    let out = spread_lane(out_bytes);
    *row[idx.col] = out;
    idx.col += 1;
    let key = *s1 + *s2 + *s3;
    *lookup_data.xor3[idx.xor3] = [key, out];
    idx.xor3 += 1;
    out
}

/// Write one andnot: commit the spread output limb, record `[u, out]`.
fn write_andnot(
    idx: &mut Idx,
    row: &mut [&mut PackedM31],
    lookup_data: &mut LookupDataMutChunk<'_>,
    b1_spread: &PackedM31,
    b2_spread: &PackedM31,
    out_bytes: &[u32; N_LANES],
) -> PackedM31 {
    let out = spread_lane(out_bytes);
    *row[idx.col] = out;
    idx.col += 1;
    let u = *b1_spread + *b2_spread + *b2_spread; // spread(b1) + 2·spread(b2)
    *lookup_data.andnot[idx.andnot] = [u, out];
    idx.andnot += 1;
    out
}

/// Right-rotation of a 64-bit lane by `n` bits on spread limbs. Writes the
/// `spread_hi` witnesses and one spread split tuple per byte; returns the
/// rotated byte view and spread limbs.
#[allow(clippy::type_complexity)]
fn rotr_split(
    a_bytes: &ByteLane,
    a_spread: &[PackedM31; N_BYTES_IN_U64],
    n: usize,
    idx: &mut Idx,
    row: &mut [&mut PackedM31],
    lookup_data: &mut LookupDataMutChunk<'_>,
) -> (ByteLane, [PackedM31; N_BYTES_IN_U64]) {
    let q = n / 8;
    let r = n % 8;
    // Byte relabel (free): new[i] = old[(i+q) mod 8].
    let rot_bytes: ByteLane = std::array::from_fn(|i| a_bytes[(i + q) % N_BYTES_IN_U64]);
    let rot_spread: [PackedM31; N_BYTES_IN_U64] =
        std::array::from_fn(|i| a_spread[(i + q) % N_BYTES_IN_U64]);
    if r == 0 {
        return (rot_bytes, rot_spread);
    }

    let four_pow_r = M31::from(1u32 << (2 * r));
    let four_pow_8mr = M31::from(1u32 << (2 * (8 - r)));
    let lo_mask = (1u32 << r) - 1;
    let shift_tag = PackedM31::from(M31::from(r as u32));

    // Per-byte split into (hi, lo).
    let mut hi_bytes: ByteLane = Default::default();
    let mut lo_bytes: ByteLane = Default::default();
    for i in 0..N_BYTES_IN_U64 {
        for l in 0..N_LANES {
            hi_bytes[i][l] = rot_bytes[i][l] >> r;
            lo_bytes[i][l] = rot_bytes[i][l] & lo_mask;
        }
    }

    // Witness spread_hi; derive spread_lo = spread_byte - spread_hi·4^r; emit
    // the split lookup; recombine res = spread_hi[i] + spread_lo[(i+1)]·4^{8-r}.
    let mut hi_spread = [PackedM31::zero(); N_BYTES_IN_U64];
    let mut lo_spread = [PackedM31::zero(); N_BYTES_IN_U64];
    for i in 0..N_BYTES_IN_U64 {
        hi_spread[i] = spread_lane(&hi_bytes[i]);
        lo_spread[i] = rot_spread[i] - hi_spread[i] * four_pow_r;
        *row[idx.col] = hi_spread[i];
        idx.col += 1;
        *lookup_data.split[idx.split] = [shift_tag, rot_spread[i], hi_spread[i], lo_spread[i]];
        idx.split += 1;
    }

    let mut res_bytes: ByteLane = Default::default();
    let mut res_spread = [PackedM31::zero(); N_BYTES_IN_U64];
    for i in 0..N_BYTES_IN_U64 {
        for l in 0..N_LANES {
            res_bytes[i][l] = (hi_bytes[i][l] | (lo_bytes[(i + 1) % 8][l] << (8 - r))) & 0xFF;
        }
        res_spread[i] = hi_spread[i] + lo_spread[(i + 1) % N_BYTES_IN_U64] * four_pow_8mr;
    }
    (res_bytes, res_spread)
}

// ─────────────────────────────── Constraints ───────────────────────────────

#[derive(Clone)]
pub struct Eval {
    pub claim: Claim,
    pub relations: KeccakRelations,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Every logup numerator is degree ≤ 1 (±enabler or 1) and every tuple
        // cell — hence every denominator — is degree ≤ 1, so batch-4 logup
        // constraints are degree 1 + 4·1 = 5 ≤ D5, which log + 2 affords.
        self.log_size() + 2
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        evaluate_round(&mut eval, &self.relations);
        eval
    }
}

/// The round constraint body, extracted so the negative-test collector can
/// reuse it against a hand-built `EvalAtRow`.
pub fn evaluate_round<E: EvalAtRow>(eval: &mut E, rel: &KeccakRelations) {
    let enabler = eval.next_trace_mask();
    eval.add_constraint(enabler.clone() * (E::F::one() - enabler.clone()));
    let enabler_ef = E::EF::from(enabler);

    let current_rc: [E::F; N_BYTES_IN_U64] = std::array::from_fn(|_| eval.next_trace_mask());
    let next_rc: [E::F; N_BYTES_IN_U64] = std::array::from_fn(|_| eval.next_trace_mask());
    let state: [E::F; N_BYTES_IN_STATE] = std::array::from_fn(|_| eval.next_trace_mask());

    // Incoming chain link (require).
    let round_data: Vec<E::F> = current_rc.iter().chain(state.iter()).cloned().collect();
    eval.add_to_relation(RelationEntry::new(
        &rel.keccak_round,
        -enabler_ef.clone(),
        &round_data,
    ));

    // Spread state limbs, lane-grouped.
    let S0: [[E::F; N_BYTES_IN_U64]; N_LANES_KECCAK] = std::array::from_fn(|lane| {
        std::array::from_fn(|i| state[lane * N_BYTES_IN_U64 + i].clone())
    });

    // Theta C-parity: C[x] via 2 chained xor3.
    let mut C: [[E::F; N_BYTES_IN_U64]; SQRT_N_LANES] =
        std::array::from_fn(|_| std::array::from_fn(|_| E::F::zero()));
    for x in 0..SQRT_N_LANES {
        for i in 0..N_BYTES_IN_U64 {
            let t = eval.next_trace_mask();
            xor3_lookup(
                eval,
                rel,
                &[
                    S0[x][i].clone(),
                    S0[x + 5][i].clone(),
                    S0[x + 10][i].clone(),
                ],
                &t,
            );
            let c = eval.next_trace_mask();
            xor3_lookup(
                eval,
                rel,
                &[t.clone(), S0[x + 15][i].clone(), S0[x + 20][i].clone()],
                &c,
            );
            C[x][i] = c;
        }
    }

    // rotl(C[x+1],1) = rotr(C[x+1],63): r=7 splits.
    let Crot: [[E::F; N_BYTES_IN_U64]; SQRT_N_LANES] =
        std::array::from_fn(|x| rotr_constraint(eval, rel, &C[(x + 1) % SQRT_N_LANES], 63));

    // Theta-apply (fused): res_S = S ^ C[x-1] ^ Crot[x].
    let mut S: [[E::F; N_BYTES_IN_U64]; N_LANES_KECCAK] =
        std::array::from_fn(|_| std::array::from_fn(|_| E::F::zero()));
    for y in 0..SQRT_N_LANES {
        for x in 0..SQRT_N_LANES {
            let id = x + 5 * y;
            let xm1 = (x + 4) % SQRT_N_LANES;
            for i in 0..N_BYTES_IN_U64 {
                let res = eval.next_trace_mask();
                xor3_lookup(
                    eval,
                    rel,
                    &[S0[id][i].clone(), C[xm1][i].clone(), Crot[x][i].clone()],
                    &res,
                );
                S[id][i] = res;
            }
        }
    }

    // Rho + Pi.
    let mut B: [[E::F; N_BYTES_IN_U64]; N_LANES_KECCAK] =
        std::array::from_fn(|_| std::array::from_fn(|_| E::F::zero()));
    for x in 0..SQRT_N_LANES {
        for y in 0..SQRT_N_LANES {
            let off = RHO_OFFSETS[x][y];
            let rotr = if off == 0 { 0 } else { 64 - off };
            let dst = 5 * y + ((2 * x + 3 * y) % SQRT_N_LANES);
            B[dst] = rotr_constraint(eval, rel, &S[x + 5 * y], rotr);
        }
    }

    // Chi + Iota (fused closing xor3).
    let mut out_state: [[E::F; N_BYTES_IN_U64]; N_LANES_KECCAK] =
        std::array::from_fn(|_| std::array::from_fn(|_| E::F::zero()));
    for y in 0..SQRT_N_LANES {
        for x in 0..SQRT_N_LANES {
            let a_idx = 5 * x + y;
            let b1_idx = 5 * ((x + 1) % SQRT_N_LANES) + y;
            let b2_idx = 5 * ((x + 2) % SQRT_N_LANES) + y;
            let out_idx = x + 5 * y;
            for i in 0..N_BYTES_IN_U64 {
                let an = eval.next_trace_mask();
                andnot_lookup(eval, rel, &B[b1_idx][i], &B[b2_idx][i], &an);
                let out = eval.next_trace_mask();
                // iota folds into output-lane-0's closing xor3: the rc columns
                // carry spread(rc), so the third input is `current_rc[i]`.
                let third = if out_idx == 0 {
                    current_rc[i].clone()
                } else {
                    E::F::zero()
                };
                xor3_lookup(eval, rel, &[B[a_idx][i].clone(), an.clone(), third], &out);
                out_state[out_idx][i] = out;
            }
        }
    }

    // Outgoing chain link (yield): spread state.
    let mut out: Vec<E::F> = next_rc.to_vec();
    for lane in &out_state {
        out.extend(lane.iter().cloned());
    }
    eval.add_to_relation(RelationEntry::new(&rel.keccak_round, enabler_ef, &out));

    eval.finalize_logup_batched(LOGUP_BATCH);
}

fn xor3_lookup<E: EvalAtRow>(eval: &mut E, rel: &KeccakRelations, ins: &[E::F; 3], out: &E::F) {
    let key = ins[0].clone() + ins[1].clone() + ins[2].clone();
    eval.add_to_relation(RelationEntry::new(
        &rel.xor3,
        E::EF::one(),
        &[key, out.clone()],
    ));
}

fn andnot_lookup<E: EvalAtRow>(
    eval: &mut E,
    rel: &KeccakRelations,
    b1: &E::F,
    b2: &E::F,
    out: &E::F,
) {
    let u = b1.clone() + b2.clone() + b2.clone();
    eval.add_to_relation(RelationEntry::new(
        &rel.andnot,
        E::EF::one(),
        &[u, out.clone()],
    ));
}

/// Rho rotation in the constraint domain on spread limbs; mirrors `rotr_split`.
fn rotr_constraint<E: EvalAtRow>(
    eval: &mut E,
    rel: &KeccakRelations,
    a: &[E::F; N_BYTES_IN_U64],
    n: usize,
) -> [E::F; N_BYTES_IN_U64] {
    let q = n / 8;
    let r = n % 8;
    let rot: [E::F; N_BYTES_IN_U64] = std::array::from_fn(|i| a[(i + q) % N_BYTES_IN_U64].clone());
    if r == 0 {
        return rot;
    }
    let four_pow_r = M31::from(1u32 << (2 * r));
    let four_pow_8mr = M31::from(1u32 << (2 * (8 - r)));

    let hi: [E::F; N_BYTES_IN_U64] = std::array::from_fn(|_| eval.next_trace_mask());
    let lo: [E::F; N_BYTES_IN_U64] =
        std::array::from_fn(|i| rot[i].clone() - hi[i].clone() * four_pow_r);
    for i in 0..N_BYTES_IN_U64 {
        eval.add_to_relation(RelationEntry::new(
            &rel.split[r - 1],
            E::EF::one(),
            &[rot[i].clone(), hi[i].clone(), lo[i].clone()],
        ));
    }
    std::array::from_fn(|i| hi[i].clone() + lo[(i + 1) % N_BYTES_IN_U64].clone() * four_pow_8mr)
}

pub type Component = FrameworkComponent<Eval>;

// ─────────────────────────────── Interaction ───────────────────────────────

#[derive(Clone, Serialize, Deserialize, Debug)]
pub struct InteractionClaim {
    pub claimed_sum: SecureField,
}

impl InteractionClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}

/// Build the interaction trace, batching lookups in `add_to_relation` order
/// in consecutive chunks of [`LOGUP_BATCH`] (matching `finalize_logup_batched`;
/// the last chunk may be smaller).
///
/// Emission order (must equal `evaluate_round`):
///   kr[0], [theta C: 2 xor3 per byte, 5·8], [C_rot split 0..40],
///   [theta-apply 200 xor3], [rho split 40..216],
///   [chi: andnot then closing-xor3, interleaved per byte, 25·8],
///   kr[1].
pub fn generate_interaction_trace(
    rel: &KeccakRelations,
    data: &InteractionClaimData,
) -> (
    InteractionClaim,
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
) {
    let log_size = std::cmp::max(
        data.non_padded_length.next_power_of_two().ilog2(),
        LOG_N_LANES,
    );
    let enabler = Enabler::new(data.non_padded_length);
    let mut gen = LogupTraceGenerator::new(log_size);
    let n_vec_rows = 1usize << (log_size - LOG_N_LANES);

    let mut fracs: Vec<(Vec<PackedQM31>, Vec<PackedQM31>)> = Vec::with_capacity(N_TOTAL_LOOKUPS);
    let ld = &data.lookup_data;

    let push_xor3 = |fracs: &mut Vec<_>, lo: usize, hi: usize| {
        for lk in &ld.xor3[lo..hi] {
            fracs.push(dense_fraction(&rel.xor3, lk, n_vec_rows));
        }
    };
    let push_split = |fracs: &mut Vec<_>, lo: usize, hi: usize| {
        for lk in &ld.split[lo..hi] {
            fracs.push(split_fraction(rel, lk, n_vec_rows));
        }
    };

    fracs.push(link_fraction(
        &rel.keccak_round,
        &ld.keccak_round[0],
        &enabler,
        n_vec_rows,
        true,
    ));
    push_xor3(&mut fracs, 0, N_XOR3_C); // theta C-parity 0..80
    push_split(&mut fracs, 0, N_SPLIT_C_ROT); // C_rot 0..40
    push_xor3(&mut fracs, N_XOR3_C, N_XOR3_C + N_XOR3_THETA_APPLY); // theta-apply 80..280
    push_split(&mut fracs, N_SPLIT_C_ROT, N_SPLIT_LOOKUPS); // rho 40..216
                                                            // Chi: per byte, andnot then closing xor3, interleaved (matching evaluate).
    let chi_close_lo = N_XOR3_C + N_XOR3_THETA_APPLY;
    for j in 0..N_ANDNOT_LOOKUPS {
        fracs.push(dense_fraction(&rel.andnot, &ld.andnot[j], n_vec_rows));
        fracs.push(dense_fraction(
            &rel.xor3,
            &ld.xor3[chi_close_lo + j],
            n_vec_rows,
        ));
    }
    fracs.push(link_fraction(
        &rel.keccak_round,
        &ld.keccak_round[1],
        &enabler,
        n_vec_rows,
        false,
    ));

    debug_assert_eq!(fracs.len(), N_TOTAL_LOOKUPS);

    // Fold each chunk exactly like `finalize_logup_batched`: start from the
    // first fraction, then num = d·num + n·den, den = den·d.
    for chunk in fracs.chunks(LOGUP_BATCH) {
        let mut col = gen.new_col();
        for vr in 0..n_vec_rows {
            let (mut num, mut den) = (chunk[0].0[vr], chunk[0].1[vr]);
            for (n, d) in &chunk[1..] {
                num = d[vr] * num + n[vr] * den;
                den *= d[vr];
            }
            col.write_frac(vr, num, den);
        }
        col.finalize_col();
    }

    let (trace, claimed_sum) = gen.finalize_last();
    (InteractionClaim { claimed_sum }, trace)
}

fn dense_fraction<R: Relation<PackedM31, PackedQM31>>(
    rel: &R,
    lookup: &[[PackedM31; 2]],
    n_vec_rows: usize,
) -> (Vec<PackedQM31>, Vec<PackedQM31>) {
    let num = vec![PackedQM31::one(); n_vec_rows];
    let mut den = vec![PackedQM31::one(); n_vec_rows];
    for (vr, d) in den.iter_mut().enumerate() {
        *d = rel.combine(&lookup[vr]);
    }
    (num, den)
}

fn split_fraction(
    rel: &KeccakRelations,
    lookup: &[[PackedM31; 4]],
    n_vec_rows: usize,
) -> (Vec<PackedQM31>, Vec<PackedQM31>) {
    let shift = lookup[0][0].to_array()[0].0 as usize;
    let split_rel = &rel.split[shift - 1];
    let num = vec![PackedQM31::one(); n_vec_rows];
    let mut den = vec![PackedQM31::one(); n_vec_rows];
    for (vr, d) in den.iter_mut().enumerate() {
        let tuple = [lookup[vr][1], lookup[vr][2], lookup[vr][3]];
        *d = split_rel.combine(&tuple);
    }
    (num, den)
}

fn link_fraction<R: Relation<PackedM31, PackedQM31>>(
    rel: &R,
    lookup: &[[PackedM31; N_BYTES_IN_STATE + N_BYTES_IN_U64]],
    enabler: &Enabler,
    n_vec_rows: usize,
    negate: bool,
) -> (Vec<PackedQM31>, Vec<PackedQM31>) {
    let mut num = vec![PackedQM31::one(); n_vec_rows];
    let mut den = vec![PackedQM31::one(); n_vec_rows];
    for vr in 0..n_vec_rows {
        let e = PackedQM31::from(enabler.packed_at(vr));
        num[vr] = if negate { -e } else { e };
        den[vr] = rel.combine(&lookup[vr]);
    }
    (num, den)
}

pub const N_COLUMNS_PUB: usize = N_COLUMNS;
pub const N_INTERACTION_COLUMNS_PUB: usize = N_INTERACTION_COLUMNS;

// ─────────────────────── W3a: GKR-offload oracle de-risk ────────────────────
//
// De-risk spike (the toy_horner pattern for keccak_round): does the batched
// LogUp denominator/numerator multiset that `keccak_round` emits today
// reconstruct, at the GKR OOD point, as a selector-weighted `Relation::combine`
// of the *base-trace* column values? If yes, the `MleCoeffColumnOracle` for the
// GKR tie-back is a low-degree combination of committed columns and the offload
// is arithmetically sound. See `tasks/quantum-safe-branch-plan.md` §Q5.
//
// Layout: the whole per-row fraction multiset (all four families, in the exact
// `generate_interaction_trace` emission order) is ONE flattened `LogUpGeneric`
// GKR instance with the lookup-slot in the HIGH index bits and the trace row in
// the LOW bits. The OOD point splits as `r = (r_slot ‖ r_row)`; the denominator
// MLE decomposes as `Σ_slot eq(slot, r_slot) · den_slot_mle(r_row)`, and because
// every `Relation::combine` is an AFFINE form `z − Σ αⱼ·tupleⱼ` (row-independent
// coeffs), multilinear eval commutes with it:
//   `den_slot_mle(r_row) == combine([tupleⱼ_mle(r_row)])`.
// So the oracle only needs each base column's MLE at `r_row` — exactly what a
// single W2 `MleEval` tie-back over the row-domain proves. No slot×row domain
// blow-up, dissolving the obstruction §Q5 feared.
#[cfg(test)]
mod gkr_offload_spike {
    use super::*;
    use stwo::core::channel::Blake2sChannel;
    use stwo::prover::lookups::gkr_prover::{prove_batch, Layer};
    use stwo::prover::lookups::mle::Mle;
    use stwo_constraint_framework::Relation;

    use crate::relations::KECCAK_ROUND_ARITY;

    type SF = SecureField;

    /// Multilinear eval with `point[0]` the most-significant index bit — matches
    /// stwo's `Mle::eval_at_point` / GKR OOD convention.
    fn ml_eval(evals: &[SF], point: &[SF]) -> SF {
        match point {
            [] => evals[0],
            [p0, rest @ ..] => {
                let (lhs, rhs) = evals.split_at(evals.len() / 2);
                let le = ml_eval(lhs, rest);
                let re = ml_eval(rhs, rest);
                *p0 * (re - le) + le
            }
        }
    }

    /// `eq(bits(index) MSB-first over `nbits`, point)`.
    fn eq_index(index: usize, nbits: usize, point: &[SF]) -> SF {
        let mut acc = SF::one();
        for (i, pt) in point.iter().enumerate().take(nbits) {
            let bit = (index >> (nbits - 1 - i)) & 1;
            acc *= if bit == 1 { *pt } else { SF::one() - *pt };
        }
        acc
    }

    /// Which relation a slot's denominator combines through.
    #[derive(Clone)]
    enum Kind {
        Kr,
        Xor3,
        Andnot,
        Split(usize), // shift-1 index into rel.split
    }

    fn combine_slot(rel: &KeccakRelations, kind: &Kind, vals: &[SF]) -> SF {
        match kind {
            Kind::Kr => rel.keccak_round.combine(vals),
            Kind::Xor3 => rel.xor3.combine(vals),
            Kind::Andnot => rel.andnot.combine(vals),
            Kind::Split(r) => rel.split[*r].combine(vals),
        }
    }

    /// One lookup slot: per-row tuple-entry vectors + per-row numerator vector.
    struct Slot {
        kind: Kind,
        tuples: Vec<Vec<SF>>,
        num: Vec<SF>,
    }

    /// Extract tuple-entry `e` of a `[PackedM31; K]` lookup array as a per-row
    /// `SecureField` vector (row = vec_row * N_LANES + lane).
    fn entry_rows<const K: usize>(data: &[[PackedM31; K]], e: usize) -> Vec<SF> {
        let mut out = Vec::with_capacity(data.len() * N_LANES);
        for chunk in data {
            for m in chunk[e].to_array() {
                out.push(SF::from(m));
            }
        }
        out
    }

    fn packed_rows(data: &[PackedM31]) -> Vec<SF> {
        let mut out = Vec::with_capacity(data.len() * N_LANES);
        for p in data {
            for m in p.to_array() {
                out.push(SF::from(m));
            }
        }
        out
    }

    /// Build every slot in the exact `generate_interaction_trace` emission order.
    fn build_slots(ld: &LookupData, enabler: &Enabler, n_vec_rows: usize) -> Vec<Slot> {
        let enab: Vec<SF> = {
            let packed: Vec<PackedM31> = (0..n_vec_rows).map(|vr| enabler.packed_at(vr)).collect();
            packed_rows(&packed)
        };
        let neg_enab: Vec<SF> = enab.iter().map(|e| -*e).collect();
        let pos_enab = enab.clone();
        let ones = vec![SF::one(); enab.len()];

        let mut slots: Vec<Slot> = Vec::with_capacity(N_TOTAL_LOOKUPS);

        let xor3_slot = |j: usize| Slot {
            kind: Kind::Xor3,
            tuples: vec![entry_rows(&ld.xor3[j], 0), entry_rows(&ld.xor3[j], 1)],
            num: ones.clone(),
        };
        let split_slot = |j: usize| {
            let shift = ld.split[j][0][0].to_array()[0].0 as usize;
            Slot {
                kind: Kind::Split(shift - 1),
                tuples: vec![
                    entry_rows(&ld.split[j], 1),
                    entry_rows(&ld.split[j], 2),
                    entry_rows(&ld.split[j], 3),
                ],
                num: ones.clone(),
            }
        };

        // kr[0] (negate=true → -enabler, matching generate_interaction_trace)
        slots.push(Slot {
            kind: Kind::Kr,
            tuples: (0..KECCAK_ROUND_ARITY)
                .map(|e| entry_rows(&ld.keccak_round[0], e))
                .collect(),
            num: neg_enab.clone(),
        });
        // theta C-parity xor3 0..80
        for j in 0..N_XOR3_C {
            slots.push(xor3_slot(j));
        }
        // C_rot split 0..40
        for j in 0..N_SPLIT_C_ROT {
            slots.push(split_slot(j));
        }
        // theta-apply xor3 80..280
        for j in N_XOR3_C..N_XOR3_C + N_XOR3_THETA_APPLY {
            slots.push(xor3_slot(j));
        }
        // rho split 40..216
        for j in N_SPLIT_C_ROT..N_SPLIT_LOOKUPS {
            slots.push(split_slot(j));
        }
        // chi: andnot then closing xor3, interleaved per byte
        let chi_close_lo = N_XOR3_C + N_XOR3_THETA_APPLY;
        for j in 0..N_ANDNOT_LOOKUPS {
            slots.push(Slot {
                kind: Kind::Andnot,
                tuples: vec![entry_rows(&ld.andnot[j], 0), entry_rows(&ld.andnot[j], 1)],
                num: ones.clone(),
            });
            slots.push(xor3_slot(chi_close_lo + j));
        }
        // kr[1] (negate=false → +enabler)
        slots.push(Slot {
            kind: Kind::Kr,
            tuples: (0..KECCAK_ROUND_ARITY)
                .map(|e| entry_rows(&ld.keccak_round[1], e))
                .collect(),
            num: pos_enab,
        });

        assert_eq!(slots.len(), N_TOTAL_LOOKUPS);
        slots
    }

    #[test]
    fn denominator_oracle_reconstructs_at_gkr_ood_point() {
        // 1. Real keccak_round witness (all-zero spread state, round 0 — a valid
        //    input; the multiset sum is well-defined for any input and GKR proves
        //    that same sum, which is all the tie-back must preserve).
        let invocations = 3usize;
        let log_size = std::cmp::max(invocations.next_power_of_two().ilog2(), LOG_N_LANES);
        let n_vec_rows = 1usize << (log_size - LOG_N_LANES);
        let n_rows = 1usize << log_size;
        let input = vec![[PackedM31::zero(); N_BYTES_IN_STATE + 1]; n_vec_rows];
        let (claim, _trace, icd) = Claim::generate_trace(input, invocations);
        assert_eq!(claim.log_size, log_size);

        let mut ch = Blake2sChannel::default();
        let rel = KeccakRelations::draw(&mut ch);

        // Ground-truth columnar claimed sum (the value the offload must preserve).
        let (columnar, _itr) = generate_interaction_trace(&rel, &icd);
        let columnar_sum = columnar.claimed_sum;

        // 2. Flatten the multiset into one LogUpGeneric instance (slot high bits).
        let enabler = Enabler::new(icd.non_padded_length);
        let slots = build_slots(&icd.lookup_data, &enabler, n_vec_rows);

        let n_slots_pad = N_TOTAL_LOOKUPS.next_power_of_two();
        let log_slots = n_slots_pad.ilog2() as usize;
        let v = log_slots + log_size as usize;
        let size = 1usize << v;

        let mut den_flat = vec![SF::one(); size]; // padding fractions: 0 / 1
        let mut num_flat = vec![SF::zero(); size];
        for (s, slot) in slots.iter().enumerate() {
            for row in 0..n_rows {
                let tvals: Vec<SF> = slot.tuples.iter().map(|t| t[row]).collect();
                let idx = s * n_rows + row;
                den_flat[idx] = combine_slot(&rel, &slot.kind, &tvals);
                num_flat[idx] = slot.num[row];
            }
        }

        let num_mle = Mle::<SimdBackend, SF>::new(num_flat.iter().copied().collect());
        let den_mle = Mle::<SimdBackend, SF>::new(den_flat.iter().copied().collect());
        let layer = Layer::LogUpGeneric {
            numerators: num_mle,
            denominators: den_mle,
        };

        let mut gkr_ch = Blake2sChannel::default();
        let (proof, artifact) = prove_batch(&mut gkr_ch, vec![layer]);

        // 3. GKR-proven sum == columnar claimed sum (step 5).
        let out = &proof.output_claims_by_instance[0];
        let gkr_sum = out[0] / out[1];
        assert_eq!(gkr_sum, columnar_sum, "GKR sum != columnar claimed sum");

        // 4. Oracle reconstruction at the GKR OOD point (step 3).
        let ood = &artifact.ood_point;
        assert_eq!(ood.len(), v);
        let r_slot = &ood[..log_slots];
        let r_row = &ood[log_slots..];
        let claims = &artifact.claims_to_verify_by_instance[0]; // [num, den]
        let (num_claim, den_claim) = (claims[0], claims[1]);

        let reconstruct = |slots: &[Slot]| -> (SF, SF) {
            let mut num_recon = SF::zero();
            let mut den_recon = SF::zero();
            for s in 0..n_slots_pad {
                let w = eq_index(s, log_slots, r_slot);
                if s < slots.len() {
                    let slot = &slots[s];
                    let tuple_evals: Vec<SF> =
                        slot.tuples.iter().map(|t| ml_eval(t, r_row)).collect();
                    den_recon += w * combine_slot(&rel, &slot.kind, &tuple_evals);
                    num_recon += w * ml_eval(&slot.num, r_row);
                } else {
                    den_recon += w * SF::one(); // padding den = 1, num = 0
                }
            }
            (num_recon, den_recon)
        };

        let (num_recon, den_recon) = reconstruct(&slots);
        assert_eq!(
            den_recon, den_claim,
            "denominator oracle reconstruction != GKR claim"
        );
        assert_eq!(
            num_recon, num_claim,
            "numerator oracle reconstruction != GKR claim"
        );

        // 5. Tamper negative (step 6): flip one base cell → reconstruction rejects.
        let mut tampered = build_slots(&icd.lookup_data, &enabler, n_vec_rows);
        tampered[1].tuples[1][0] += SF::one();
        let (_, den_tampered) = reconstruct(&tampered);
        assert_ne!(
            den_tampered, den_claim,
            "tampered base cell must break the reconstruction"
        );
    }
}
