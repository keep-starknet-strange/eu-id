//! Build the arithmetic witness for one Keccak-f[1600] round per row.
//!
//! ## Spread-form fusion
//!
//! The Keccak state uses spread form (`spread(b) = Σ bᵢ·4ⁱ`; see
//! [`crate::utils`]). This form reduces the number of round lookups:
//!
//! - **xor3:** XOR of up to three spread bytes uses one lookup with a degree-1
//!   sum key `s1+s2+s3` into a dense `2^16` table. Theta's 5-way column parity
//!   `C[x]` uses two chained xor3 lookups. The theta step
//!   `res = S ⊕ C[x−1] ⊕ rotl(C[x+1],1)` uses one xor3 lookup. The chi step
//!   `a ⊕ (¬b'∧b'')` uses one xor3 lookup whose third input is 0. On lane 0,
//!   the third input is `spread(rc)`, which also applies iota.
//! - **andnot:** `(¬b'∧b'')` retargets onto the xor3 table via the identity
//!   `spread(b'⊕b'') = 2·spread(¬b'∧b'') + spread(b') − spread(b'')`: the
//!   committed andnot output is checked by an xor3 lookup keyed
//!   `spread(b')+spread(b'')` whose expected xor output is that expression.
//! - **split_r:** the rho/theta sub-byte rotation splits a spread byte at bit
//!   boundary `2r` via the spread split tables; `spread` is additive across the
//!   disjoint hi/lo ranges, so `spread_lo = spread_byte − spread_hi·4^r` is a
//!   linear expression and the recombination is
//!   `res = spread_hi[i] + spread_lo[(i+1)%8]·4^{8-r}`.
//!
//! The carrier AIR consumes the trace columns and lookup payloads from this
//! module. This module does not define a separate proof component.

#![allow(non_snake_case)]

use num_traits::Zero;
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, ParallelIterator};
use stwo::core::fields::m31::M31;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES, N_LANES};
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::BackendForChannel;
use stwo_air_utils::trace::component_trace::ComponentTrace;
use stwo_air_utils_derive::{IterMut, ParIterMut, Uninitialized};
use stwo_constraint_framework::EvalAtRow;

use crate::constants::{
    IOTA_RC, N_BYTES_IN_STATE, N_BYTES_IN_U64, N_LANES_KECCAK, RHO_OFFSETS, SQRT_N_LANES,
};
use crate::utils::{spread_u32, unspread_u32};

// Lookup budgets for one arithmetic row.

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

/// Number of committed helper-trace columns before the interleaved chi/andnot
/// cells: theta C-parity intermediates (t + C), all rotation spread-hi
/// witnesses, and theta-apply outputs (res_S). This is also the first
/// committed column (column 0) of the helper trace: the enabler, current_rc,
/// perm_id, round_idx, and initial spread-state groups are computed in
/// `fill_row` for the round arithmetic but are never committed as helper
/// columns — the carrier commits its own schedule/state columns for those
/// directly from the boundary witness (see `carrier::generate`), so
/// materializing them here would only be discarded at the copy site.
pub const ROUND_PRE_CHI_COLUMNS: usize = N_XOR3_C + N_HI_WITNESS + N_XOR3_THETA_APPLY;

/// Only the andnot output is committed for each Chi cell (contiguous right
/// after the pre-chi block); the closing xor3 (Chi's `a ^ andnot [^ rc]`
/// round-output cell) is a lookup payload only, written by
/// `write_xor3_payload_only`. The carrier reads the round output back from
/// its own next-row carrier-state mask (`collect_arithmetic_lookups`'s
/// `output_state` argument), never from this helper trace, so committing it
/// here would be a discarded column.
pub const N_ARITHMETIC_COLUMNS: usize = ROUND_PRE_CHI_COLUMNS + N_ANDNOT_LOOKUPS;

/// Number of arithmetic lookups that the carrier uses for one round row.
pub const N_ARITHMETIC_LOOKUPS: usize = N_XOR3_LOOKUPS + N_ANDNOT_LOOKUPS + N_SPLIT_LOOKUPS;

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
    /// `[key, out]`: key is the degree-1 sum and out is the spread(xor) result.
    pub xor3: [Vec<[PackedM31; 2]>; N_XOR3_LOOKUPS],
    /// `[key, xor_out]` retargeted onto the xor3 table: `key =
    /// spread(b')+spread(b'')`, `xor_out = 2·andnot + spread(b') −
    /// spread(b'')` derived from the committed andnot output.
    pub andnot: [Vec<[PackedM31; 2]>; N_ANDNOT_LOOKUPS],
    /// `[shift_r, spread_byte, spread_hi, spread_lo]`; `shift_r` selects the
    /// `Split*` relation and is constant across SIMD lanes.
    pub split: [Vec<[PackedM31; 4]>; N_SPLIT_LOOKUPS],
}

/// Build the round arithmetic trace and its lookup payloads.
///
/// Each input row is `[spread_state(200) | round_index | permutation_id]`.
pub fn generate_arithmetic_trace(
    mut input: Vec<[PackedM31; N_BYTES_IN_STATE + 2]>,
    invocations: usize,
) -> (ComponentTrace<N_ARITHMETIC_COLUMNS>, InteractionClaimData)
where
    SimdBackend: BackendForChannel<Blake2sMerkleChannel>,
{
    let log_size = std::cmp::max(invocations.next_power_of_two().ilog2(), LOG_N_LANES);
    input.resize(
        1 << (log_size - LOG_N_LANES),
        [PackedM31::zero(); N_BYTES_IN_STATE + 2],
    );

    // SAFETY: both allocations have exactly one entry per SIMD row. The
    // parallel zip below visits every row once, and `fill_row` initializes
    // every trace cell and lookup tuple before either allocation is returned.
    let (mut trace, mut lookup_data) = unsafe {
        (
            ComponentTrace::<N_ARITHMETIC_COLUMNS>::uninitialized(log_size),
            LookupData::uninitialized(log_size - LOG_N_LANES),
        )
    };

    (
        trace.par_iter_mut(),
        input.into_par_iter(),
        lookup_data.par_iter_mut(),
    )
        .into_par_iter()
        .for_each(|(mut row, input, mut lookup_data)| {
            fill_row(&input, &mut row[..], &mut lookup_data);
        });

    (
        trace,
        InteractionClaimData {
            lookup_data,
            non_padded_length: invocations,
        },
    )
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
    input: &[PackedM31; N_BYTES_IN_STATE + 2],
    row: &mut [&mut PackedM31],
    lookup_data: &mut LookupDataMutChunk<'_>,
) {
    let mut idx = Idx::default();

    // Carry the current constant in spread form. This lets Iota use the
    // closing lane-zero xor3 without an extra conversion column. Used only
    // by the Chi/Iota fold below: the carrier commits its own round-constant
    // schedule columns directly (see `carrier::generate`), so this value is
    // never a helper-trace column (see `N_ARITHMETIC_COLUMNS`'s doc).
    let round_of = |lane_val: u32| lane_val as usize;
    let current_rc: [PackedM31; N_BYTES_IN_U64] = std::array::from_fn(|i| {
        PackedM31::from_array(std::array::from_fn(|lane| {
            let r = round_of(input[N_BYTES_IN_STATE].to_array()[lane].0);
            M31::from(spread_u32(IOTA_RC[r].to_le_bytes()[i] as u32))
        }))
    });

    // Per-lane byte view of the incoming state. Neither the initial spread
    // state (`input[..N_BYTES_IN_STATE]`) nor `perm_id`/`round_idx`
    // (`input[N_BYTES_IN_STATE..]`) are committed as helper columns: the
    // carrier commits its own carrier-state and schedule columns directly
    // from the boundary witness.
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
    // Keys use the incoming spread state (S0_spread), C, and Crot. All
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
    // Chi reads B in the `5x+y` convention and writes the output state at
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
                // Payload only: the carrier reads this round-output cell
                // back from its own next-row carrier-state mask, never from
                // this helper trace (see `N_ARITHMETIC_COLUMNS`'s doc), so it
                // is never committed as a helper column.
                write_xor3_payload_only(
                    &mut idx,
                    lookup_data,
                    &B_spread[a_idx][i],
                    &an_spread,
                    &rc_spread,
                    &out,
                );
            }
        }
    }
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

/// Record one xor3 lookup payload without committing a helper-trace column
/// (used for the Chi-close round-output cell only; see
/// `N_ARITHMETIC_COLUMNS`'s doc).
fn write_xor3_payload_only(
    idx: &mut Idx,
    lookup_data: &mut LookupDataMutChunk<'_>,
    s1: &PackedM31,
    s2: &PackedM31,
    s3: &PackedM31,
    out_bytes: &[u32; N_LANES],
) {
    let out = spread_lane(out_bytes);
    let key = *s1 + *s2 + *s3;
    *lookup_data.xor3[idx.xor3] = [key, out];
    idx.xor3 += 1;
}

/// Write one andnot: commit the spread output limb, record the xor3-retarget
/// tuple `[key, xor_out]` (see the module doc's andnot identity).
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
    let key = *b1_spread + *b2_spread;
    let xor_out = out + out + *b1_spread - *b2_spread;
    *lookup_data.andnot[idx.andnot] = [key, xor_out];
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

/// Select the table relation for one arithmetic lookup.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArithmeticLookupKind {
    Xor3,
    Andnot,
    /// Sub-byte shift. The value is in the range 1 through 7.
    Split(usize),
}

/// One carrier arithmetic lookup in canonical order.
pub struct ArithmeticLookup<E: EvalAtRow> {
    pub kind: ArithmeticLookupKind,
    pub numerator: E::EF,
    pub tuple: Vec<E::F>,
}

/// Read the committed arithmetic columns and build the carrier lookups.
pub fn collect_arithmetic_lookups<E: EvalAtRow>(
    eval: &mut E,
    state: &[E::F; N_BYTES_IN_STATE],
    output_state: &[E::F; N_BYTES_IN_STATE],
    round_constant: &[E::F; N_BYTES_IN_U64],
    numerator: E::EF,
) -> Vec<ArithmeticLookup<E>> {
    let mut lookups = Vec::with_capacity(N_ARITHMETIC_LOOKUPS);
    let initial: [[E::F; N_BYTES_IN_U64]; N_LANES_KECCAK] = std::array::from_fn(|lane| {
        std::array::from_fn(|byte| state[lane * N_BYTES_IN_U64 + byte].clone())
    });

    let mut parity: [[E::F; N_BYTES_IN_U64]; SQRT_N_LANES] =
        std::array::from_fn(|_| std::array::from_fn(|_| E::F::zero()));
    for x in 0..SQRT_N_LANES {
        for byte in 0..N_BYTES_IN_U64 {
            let partial = eval.next_trace_mask();
            push_arithmetic_xor3(
                &mut lookups,
                &[
                    initial[x][byte].clone(),
                    initial[x + 5][byte].clone(),
                    initial[x + 10][byte].clone(),
                ],
                &partial,
                numerator.clone(),
            );
            let value = eval.next_trace_mask();
            push_arithmetic_xor3(
                &mut lookups,
                &[
                    partial,
                    initial[x + 15][byte].clone(),
                    initial[x + 20][byte].clone(),
                ],
                &value,
                numerator.clone(),
            );
            parity[x][byte] = value;
        }
    }

    let rotated_parity: [[E::F; N_BYTES_IN_U64]; SQRT_N_LANES] = std::array::from_fn(|x| {
        collect_arithmetic_rotation(
            eval,
            &mut lookups,
            &parity[(x + 1) % SQRT_N_LANES],
            63,
            numerator.clone(),
        )
    });

    let mut theta: [[E::F; N_BYTES_IN_U64]; N_LANES_KECCAK] =
        std::array::from_fn(|_| std::array::from_fn(|_| E::F::zero()));
    for y in 0..SQRT_N_LANES {
        for x in 0..SQRT_N_LANES {
            let lane = x + 5 * y;
            let previous_x = (x + 4) % SQRT_N_LANES;
            for byte in 0..N_BYTES_IN_U64 {
                let result = eval.next_trace_mask();
                push_arithmetic_xor3(
                    &mut lookups,
                    &[
                        initial[lane][byte].clone(),
                        parity[previous_x][byte].clone(),
                        rotated_parity[x][byte].clone(),
                    ],
                    &result,
                    numerator.clone(),
                );
                theta[lane][byte] = result;
            }
        }
    }

    let mut rho_pi: [[E::F; N_BYTES_IN_U64]; N_LANES_KECCAK] =
        std::array::from_fn(|_| std::array::from_fn(|_| E::F::zero()));
    for x in 0..SQRT_N_LANES {
        for y in 0..SQRT_N_LANES {
            let offset = RHO_OFFSETS[x][y];
            let rotation = if offset == 0 { 0 } else { 64 - offset };
            let destination = 5 * y + ((2 * x + 3 * y) % SQRT_N_LANES);
            rho_pi[destination] = collect_arithmetic_rotation(
                eval,
                &mut lookups,
                &theta[x + 5 * y],
                rotation,
                numerator.clone(),
            );
        }
    }

    for y in 0..SQRT_N_LANES {
        for x in 0..SQRT_N_LANES {
            let a = 5 * x + y;
            let b1 = 5 * ((x + 1) % SQRT_N_LANES) + y;
            let b2 = 5 * ((x + 2) % SQRT_N_LANES) + y;
            let output_lane = x + 5 * y;
            for byte in 0..N_BYTES_IN_U64 {
                let andnot = eval.next_trace_mask();
                push_arithmetic_andnot(
                    &mut lookups,
                    &rho_pi[b1][byte],
                    &rho_pi[b2][byte],
                    &andnot,
                    numerator.clone(),
                );
                let output = output_state[output_lane * N_BYTES_IN_U64 + byte].clone();
                let iota = if output_lane == 0 {
                    round_constant[byte].clone()
                } else {
                    E::F::zero()
                };
                push_arithmetic_xor3(
                    &mut lookups,
                    &[rho_pi[a][byte].clone(), andnot, iota],
                    &output,
                    numerator.clone(),
                );
            }
        }
    }

    debug_assert_eq!(lookups.len(), N_ARITHMETIC_LOOKUPS);
    lookups
}

fn push_arithmetic_xor3<E: EvalAtRow>(
    lookups: &mut Vec<ArithmeticLookup<E>>,
    values: &[E::F; 3],
    output: &E::F,
    numerator: E::EF,
) {
    lookups.push(ArithmeticLookup {
        kind: ArithmeticLookupKind::Xor3,
        numerator,
        tuple: vec![
            values[0].clone() + values[1].clone() + values[2].clone(),
            output.clone(),
        ],
    });
}

fn push_arithmetic_andnot<E: EvalAtRow>(
    lookups: &mut Vec<ArithmeticLookup<E>>,
    b1: &E::F,
    b2: &E::F,
    output: &E::F,
    numerator: E::EF,
) {
    // Retarget onto the xor3 table: spread(b1^b2) = 2*output + b1 - b2 (see
    // module doc). `output` is still the committed andnot spread limb.
    lookups.push(ArithmeticLookup {
        kind: ArithmeticLookupKind::Andnot,
        numerator,
        tuple: vec![
            b1.clone() + b2.clone(),
            output.clone() + output.clone() + b1.clone() - b2.clone(),
        ],
    });
}

fn collect_arithmetic_rotation<E: EvalAtRow>(
    eval: &mut E,
    lookups: &mut Vec<ArithmeticLookup<E>>,
    input: &[E::F; N_BYTES_IN_U64],
    rotation: usize,
    numerator: E::EF,
) -> [E::F; N_BYTES_IN_U64] {
    let whole_bytes = rotation / 8;
    let bits = rotation % 8;
    let rotated: [E::F; N_BYTES_IN_U64] =
        std::array::from_fn(|index| input[(index + whole_bytes) % N_BYTES_IN_U64].clone());
    if bits == 0 {
        return rotated;
    }
    let four_pow_bits = M31::from(1u32 << (2 * bits));
    let four_pow_remaining = M31::from(1u32 << (2 * (8 - bits)));
    let high: [E::F; N_BYTES_IN_U64] = std::array::from_fn(|_| eval.next_trace_mask());
    let low: [E::F; N_BYTES_IN_U64] =
        std::array::from_fn(|index| rotated[index].clone() - high[index].clone() * four_pow_bits);
    for index in 0..N_BYTES_IN_U64 {
        lookups.push(ArithmeticLookup {
            kind: ArithmeticLookupKind::Split(bits),
            numerator: numerator.clone(),
            tuple: vec![
                rotated[index].clone(),
                high[index].clone(),
                low[index].clone(),
            ],
        });
    }
    std::array::from_fn(|index| {
        high[index].clone() + low[(index + 1) % N_BYTES_IN_U64].clone() * four_pow_remaining
    })
}
