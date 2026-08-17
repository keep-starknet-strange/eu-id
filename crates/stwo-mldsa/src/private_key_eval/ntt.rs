//! Proven inverse NTT over the expanded matrix `Â` for private-key ML-DSA
//! verification.
//!
//! Private `ExpandA` yields each accepted coefficient as a stage-zero
//! [`crate::binding::NttCellRelation`] cell `(poly, stage, index, limb0,
//! limb1)` with a 12/11-bit limb split (base 4096). The butterfly component
//! replays the 8-stage Gentleman–Sande inverse NTT: each row consumes two
//! stage-`s` cells and yields two stage-`s+1` cells. The scaling component
//! consumes the final stage-8 cells, multiplies by `256^-1 mod q`, splits the
//! canonical output into balanced base-`B` digits, and Horner-accumulates
//! each polynomial at the drawn `(r, s)`. It yields `Â_ij(r, s)` into
//! `EvalAtRsRelation` at slots `A_EVAL_BASE + i·l + j`.
//!
//! ## Limb and canonicity policy
//!
//! Values are 12/11-bit limb pairs (C7b). Outputs consumed non-modularly
//! downstream (`output0`, `output1`, scaling `output`) carry a slack
//! complement that pins the exact representative in `[0, Q)`. Purely modular
//! intermediates (`diff`, `quotient`) carry value-limb range checks only
//! (C7a): their consumers need only the residue mod `Q`.

use num_traits::{One, Zero};
use stwo::core::fields::m31::{M31, P as M31_MODULUS};
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkEval, Relation, RelationEntry, INTERACTION_TRACE_IDX,
};

use crate::air_util::{col_eval, enc_signed, m31, ColEval};
use crate::coeffs::tables::RcKind;
use crate::coeffs::RcUses;
use crate::constants::{K, L, N, Q, ZETA};
use crate::profile::MlDsaProfile;
#[cfg(test)]
use crate::profile::ML_DSA_65;
use crate::reference::ntt::NttPoly;
use crate::witness::B;

use super::{
    gen_batched_logup, range_denominator, range_tuple, PrivateKeyEvalRelations, A_EVAL_BASE,
};

/// Number of matrix polynomials (`k · l`, maximum shape).
pub const MATRIX_POLYS: usize = K * L;
/// Inverse-NTT stage count: `log2(N) = 8`.
pub const NTT_STAGES: usize = 8;
/// Butterfly trace log size (covers `MATRIX_POLYS·NTT_STAGES·N/2` rows).
pub const NTT_BUTTERFLY_LOG_SIZE: u32 = 15;
/// Scaling trace log size (covers `MATRIX_POLYS·N` rows).
pub const NTT_SCALING_LOG_SIZE: u32 = 13;

const CARRY_OFFSET: i64 = 1 << 12;
const N_INV: u32 = 8_347_681;
const LOGUP_BATCH: usize = 4;

#[derive(Clone, Copy)]
struct ButterflyRow {
    poly: usize,
    stage: usize,
    index0: usize,
    index1: usize,
    twiddle: u32,
}

#[derive(Clone, Copy)]
struct ScalingRow {
    poly: usize,
    index: usize,
    eval_start: bool,
    eval_end: bool,
}

fn zeta_table() -> [u32; N] {
    let mut powers = [0u64; N];
    let mut current = 1u64;
    for value in &mut powers {
        *value = current;
        current = current * ZETA as u64 % Q as u64;
    }
    let mut zetas = [0u32; N];
    for (index, value) in zetas.iter_mut().enumerate() {
        *value = powers[(index as u8).reverse_bits() as usize] as u32;
    }
    zetas
}

fn butterfly_schedule() -> Vec<ButterflyRow> {
    let zetas = zeta_table();
    let mut rows = Vec::with_capacity(MATRIX_POLYS * NTT_STAGES * N / 2);
    for poly in 0..MATRIX_POLYS {
        let mut m = N;
        let mut len = 1usize;
        for stage in 0..NTT_STAGES {
            let mut start = 0usize;
            while start < N {
                m -= 1;
                let twiddle = Q - zetas[m];
                for index0 in start..start + len {
                    rows.push(ButterflyRow {
                        poly,
                        stage,
                        index0,
                        index1: index0 + len,
                        twiddle,
                    });
                }
                start += 2 * len;
            }
            len <<= 1;
        }
    }
    rows
}

fn scaling_schedule() -> Vec<ScalingRow> {
    let mut rows = Vec::with_capacity(MATRIX_POLYS * N);
    for poly in 0..MATRIX_POLYS {
        for position in 0..N {
            rows.push(ScalingRow {
                poly,
                index: N - 1 - position,
                eval_start: position == 0,
                eval_end: position + 1 == N,
            });
        }
    }
    rows
}

// C7b: the twiddle constant is a 12/11-bit split (base 4096), not the
// earlier 8/8/7-bit byte split -- one fewer preprocessed limb column.
const BUTTERFLY_PRE_NAMES: [&str; 7] = [
    "active", "poly", "stage", "index0", "index1", "twiddle0", "twiddle1",
];
const SCALING_PRE_NAMES: [&str; 5] = ["active", "eval_start", "eval_end", "poly", "index"];

fn butterfly_pre_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mldsa_private_key_ntt_butterfly_{name}"),
    }
}

fn butterfly_active_id(profile: MlDsaProfile) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mldsa_private_key_ntt_butterfly_{profile:?}_active"),
    }
}

fn scaling_pre_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mldsa_private_key_ntt_scaling_{name}"),
    }
}

fn scaling_active_id(profile: MlDsaProfile) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mldsa_private_key_ntt_scaling_{profile:?}_active"),
    }
}

/// Preprocessed ids for both components (butterfly then scaling), in commit
/// order.
pub fn ntt_preprocessed_ids(profile: MlDsaProfile) -> Vec<PreProcessedColumnId> {
    core::iter::once(butterfly_active_id(profile))
        .chain(
            BUTTERFLY_PRE_NAMES[1..]
                .iter()
                .map(|name| butterfly_pre_id(name)),
        )
        .chain(core::iter::once(scaling_active_id(profile)))
        .chain(
            SCALING_PRE_NAMES[1..]
                .iter()
                .map(|name| scaling_pre_id(name)),
        )
        .collect()
}

/// Preprocessed log sizes, matching [`ntt_preprocessed_ids`] order.
pub fn ntt_preprocessed_log_sizes() -> Vec<u32> {
    let mut sizes = vec![NTT_BUTTERFLY_LOG_SIZE; BUTTERFLY_PRE_NAMES.len()];
    sizes.extend(vec![NTT_SCALING_LOG_SIZE; SCALING_PRE_NAMES.len()]);
    sizes
}

/// Generate the butterfly and scaling preprocessed columns for the selected
/// profile (schedule, active flags, and the split twiddle limbs).
pub fn gen_ntt_preprocessed(profile: MlDsaProfile) -> Vec<ColEval> {
    let mut result = Vec::with_capacity(BUTTERFLY_PRE_NAMES.len() + SCALING_PRE_NAMES.len());
    let mut columns =
        vec![vec![m31(0); 1usize << NTT_BUTTERFLY_LOG_SIZE]; BUTTERFLY_PRE_NAMES.len()];
    for (row, item) in butterfly_schedule().iter().enumerate() {
        columns[0][row] = m31(u32::from(item.poly < profile.matrix_polys()));
        columns[1][row] = m31(item.poly as u32);
        columns[2][row] = m31(item.stage as u32);
        columns[3][row] = m31(item.index0 as u32);
        columns[4][row] = m31(item.index1 as u32);
        let twiddle = split12_11(item.twiddle);
        for limb in 0..2 {
            columns[5 + limb][row] = m31(twiddle[limb]);
        }
    }
    result.extend(
        columns
            .into_iter()
            .map(|column| col_eval(NTT_BUTTERFLY_LOG_SIZE, column)),
    );

    let mut columns = vec![vec![m31(0); 1usize << NTT_SCALING_LOG_SIZE]; SCALING_PRE_NAMES.len()];
    for (row, item) in scaling_schedule().iter().enumerate() {
        columns[0][row] = m31(u32::from(item.poly < profile.matrix_polys()));
        columns[1][row] = m31(item.eval_start as u32);
        columns[2][row] = m31(item.eval_end as u32);
        columns[3][row] = m31(item.poly as u32);
        columns[4][row] = m31(item.index as u32);
    }
    result.extend(
        columns
            .into_iter()
            .map(|column| col_eval(NTT_SCALING_LOG_SIZE, column)),
    );
    result
}

// C7a: B_DIFF_SLACK, B_QUOTIENT_SLACK, and S_QUOTIENT_SLACK were deleted.
// `diff` and `quotient` are purely-modular intermediates: their downstream
// consumer (the twiddle multiplication, `add_mul_constraints`) only needs the
// z*x ≡ out (mod Q) identity, which holds for ANY alias `diff+k*Q` as long as
// `quotient` absorbs the difference -- so their own canonicity is never
// load-bearing (see `add_canonical_range_lookups` below and the module-level
// C7a negative tests). B_OUT0_SLACK, B_OUT1_SLACK, and S_OUTPUT_SLACK are
// NEVER deleted: canonicity slack is load-bearing exactly where a value is
// consumed non-modularly. OUT0/OUT1 feed the *next* stage's `borrow = input0
// < input1` integer comparison, and S_OUTPUT feeds the balanced-digit
// decomposition that produces `a_eval` -- both require the value's exact
// integer representative in [0, Q), not just its residue mod Q.
//
// C7b: every value/slack group re-limbs from 3 columns (8/8/7-bit, base 256)
// to 2 (12/11-bit, base 4096); each multiplication's carry count drops from
// 4 to 2 (`mul_carries`/`add_mul_constraints`).
const B_IN0: usize = 0;
const B_IN1: usize = 2;
const B_OUT0: usize = 4;
const B_OUT0_SLACK: usize = 6;
const B_DIFF: usize = 8;
const B_OUT1: usize = 10;
const B_OUT1_SLACK: usize = 12;
const B_QUOTIENT: usize = 14;
const B_REDUCE: usize = 16;
const B_BORROW: usize = 17;
const B_CARRY: usize = 18;
/// Butterfly base-column count: eight limb pairs + reduce/borrow + 2 carries.
pub const NTT_BUTTERFLY_BASE_COLS: usize = 20;

const S_INPUT: usize = 0;
const S_OUTPUT: usize = 2;
const S_OUTPUT_SLACK: usize = 4;
const S_QUOTIENT: usize = 6;
const S_CARRY: usize = 8;
const S_DIGIT: usize = 10;
/// Scaling base-column count: five limb pairs + 2 carries + 3 digits.
pub const NTT_SCALING_BASE_COLS: usize = 13;

/// Butterfly LogUp entries per row: 4 NTT-cell ties + 12 range uses +
/// 2 carries.
pub const NTT_BUTTERFLY_LOGUP_ENTRIES: usize = 18;
/// Scaling LogUp entries per row: 1 NTT-cell consume + 6 output/quotient
/// range uses + 2 carries + 3 digit uses + 1 eval yield.
pub const NTT_SCALING_LOGUP_ENTRIES: usize = 13;
/// Butterfly interaction columns: batched LogUp (batch 4).
pub const NTT_BUTTERFLY_INTERACTION_COLS: usize =
    SECURE_EXTENSION_DEGREE * NTT_BUTTERFLY_LOGUP_ENTRIES.div_ceil(LOGUP_BATCH);
/// Scaling interaction columns: 4 accumulator coords + batched LogUp.
pub const NTT_SCALING_INTERACTION_COLS: usize = SECURE_EXTENSION_DEGREE
    + SECURE_EXTENSION_DEGREE * NTT_SCALING_LOGUP_ENTRIES.div_ceil(LOGUP_BATCH);

/// Base-trace column log sizes (butterfly then scaling).
pub fn ntt_trace_layout() -> Vec<u32> {
    let mut layout = vec![NTT_BUTTERFLY_LOG_SIZE; NTT_BUTTERFLY_BASE_COLS];
    layout.extend(vec![NTT_SCALING_LOG_SIZE; NTT_SCALING_BASE_COLS]);
    layout
}

/// Interaction column log sizes (butterfly then scaling).
pub fn ntt_interaction_layout() -> Vec<u32> {
    let mut layout = vec![NTT_BUTTERFLY_LOG_SIZE; NTT_BUTTERFLY_INTERACTION_COLS];
    layout.extend(vec![NTT_SCALING_LOG_SIZE; NTT_SCALING_INTERACTION_COLS]);
    layout
}

/// C7b: 12/11-bit limb split (base 4096), replacing the earlier 8/8/7-bit
/// byte split. `Q = 1 + 4096·2046` -- Q's OWN 12/11 split is exactly
/// `(q0, q1) = (1, 2046)`, which is why the schoolbook equations below use
/// the literal constant `2046` rather than a separately-split `q`.
const _: () = assert!(Q == 1 + 4096 * 2046);
/// C7b(N9): every intermediate cross-term product in `mul_carries`
/// (`z0·x1+z1·x0` and `z1·x1`, with each factor < 4096 or < 2048) stays
/// comfortably inside the M31 field's representable range as a plain i64
/// computation -- no field wraparound sneaks into an "exact but wrong"
/// equation.
const _: () = assert!(4095u32 * 4095 + 4096 * 4096 < M31_MODULUS);
fn split12_11(value: u32) -> [u32; 2] {
    [value & 0xfff, value >> 12]
}

fn write_value_limbs(columns: &mut [Vec<M31>], value_base: usize, row: usize, value: u32) {
    let value_limbs = split12_11(value);
    for limb in 0..2 {
        columns[value_base + limb][row] = m31(value_limbs[limb]);
    }
}

fn write_canonical(
    columns: &mut [Vec<M31>],
    value_base: usize,
    slack_base: usize,
    row: usize,
    value: u32,
) {
    write_value_limbs(columns, value_base, row, value);
    let slack_limbs = split12_11(Q - 1 - value);
    for limb in 0..2 {
        columns[slack_base + limb][row] = m31(slack_limbs[limb]);
    }
}

/// Three-level schoolbook multiplication `z*x = out + Q*k`, Q-factored as
/// `1 + 4096·2046`:
///   e0 = z0·x0 − k0 − out0        = 4096·c1
///   e1 = z0·x1+z1·x0 − k1 − 2046·k0 − out1 + c1 = 4096·c2
///   e2 = z1·x1 − 2046·k1 + c2      = 0
/// Carries: c1 ∈ [−1,4094], c2 ∈ [−2047,4093] (only 9 units of honest
/// headroom on c1 -- see the boundary sweep in the tests below).
fn mul_carries(constant: u32, value: u32, output: u32, quotient: u32) -> [i64; 2] {
    let z = split12_11(constant);
    let x = split12_11(value);
    let k = split12_11(quotient);
    let out = split12_11(output);
    let e0 = z[0] as i64 * x[0] as i64 - k[0] as i64 - out[0] as i64;
    let c1 = e0 / 4096;
    let e1 = z[0] as i64 * x[1] as i64 + z[1] as i64 * x[0] as i64
        - k[1] as i64
        - 2046 * k[0] as i64
        - out[1] as i64
        + c1;
    let c2 = e1 / 4096;
    debug_assert_eq!(e0, 4096 * c1);
    debug_assert_eq!(e1, 4096 * c2);
    debug_assert_eq!(z[1] as i64 * x[1] as i64 - 2046 * k[1] as i64 + c2, 0);
    [c1, c2]
}

fn mul_witness(constant: u32, value: u32) -> (u32, u32, [i64; 2]) {
    let product = constant as u64 * value as u64;
    let output = (product % Q as u64) as u32;
    let quotient = (product / Q as u64) as u32;
    (
        output,
        quotient,
        mul_carries(constant, value, output, quotient),
    )
}

fn balanced3(value: u32) -> [i64; 3] {
    crate::witness::balanced_digits::<3>(value as i128).map(|digit| digit as i64)
}

/// Records the 2 value-limb range uses only (Rc12, Rc11). Used for
/// purely-modular intermediates (`diff`, `quotient`) that never need the
/// slack complement -- see the C7a module comment above `B_IN0`.
fn record_value_range_uses(uses: &mut RcUses, value: u32) {
    let limbs = split12_11(value);
    uses.record(RcKind::Rc12, limbs[0]);
    uses.record(RcKind::Rc11, limbs[1]);
}

/// Records both the value-limb and slack-complement range uses (4 total).
/// Used for values that are consumed non-modularly downstream (`output0`,
/// `output1`, `output`), where exact canonicity in `[0, Q)` is load-bearing.
fn record_canonical_uses(uses: &mut RcUses, value: u32) {
    record_value_range_uses(uses, value);
    record_value_range_uses(uses, Q - 1 - value);
}

/// Base-trace output of the inverse-NTT components.
pub struct NttBase {
    /// The concatenated butterfly and scaling base columns.
    pub trace: Vec<ColEval>,
    /// The merged range-table uses.
    pub range_uses: RcUses,
}

/// Generate the butterfly and scaling base traces and their rc census.
pub fn gen_ntt_base(profile: MlDsaProfile, a_hat: &[NttPoly]) -> NttBase {
    assert_eq!(a_hat.len(), MATRIX_POLYS);
    let mut states = a_hat.to_vec();
    let mut range_uses = RcUses::new();
    let mut columns = vec![vec![m31(0); 1usize << NTT_BUTTERFLY_LOG_SIZE]; NTT_BUTTERFLY_BASE_COLS];
    for (row, item) in butterfly_schedule().iter().enumerate() {
        if item.poly >= profile.matrix_polys() {
            continue;
        }
        let input0 = states[item.poly][item.index0];
        let input1 = states[item.poly][item.index1];
        for (limb, value) in split12_11(input0).into_iter().enumerate() {
            columns[B_IN0 + limb][row] = m31(value);
        }
        for (limb, value) in split12_11(input1).into_iter().enumerate() {
            columns[B_IN1 + limb][row] = m31(value);
        }
        let sum = input0 + input1;
        let reduce = sum >= Q;
        let output0 = if reduce { sum - Q } else { sum };
        let borrow = input0 < input1;
        let diff = if borrow {
            input0 + Q - input1
        } else {
            input0 - input1
        };
        write_canonical(&mut columns, B_OUT0, B_OUT0_SLACK, row, output0);
        write_value_limbs(&mut columns, B_DIFF, row, diff);
        record_canonical_uses(&mut range_uses, output0);
        record_value_range_uses(&mut range_uses, diff);
        columns[B_REDUCE][row] = m31(reduce as u32);
        columns[B_BORROW][row] = m31(borrow as u32);
        states[item.poly][item.index0] = output0;

        let (output1, quotient, carries) = mul_witness(item.twiddle, diff);
        write_canonical(&mut columns, B_OUT1, B_OUT1_SLACK, row, output1);
        write_value_limbs(&mut columns, B_QUOTIENT, row, quotient);
        record_canonical_uses(&mut range_uses, output1);
        record_value_range_uses(&mut range_uses, quotient);
        for (limb, carry) in carries.into_iter().enumerate() {
            columns[B_CARRY + limb][row] = enc_signed(carry);
            range_uses.record(RcKind::Rc13, (carry + CARRY_OFFSET) as u32);
        }
        states[item.poly][item.index1] = output1;
    }
    let mut trace: Vec<_> = columns
        .into_iter()
        .map(|column| col_eval(NTT_BUTTERFLY_LOG_SIZE, column))
        .collect();

    let mut columns = vec![vec![m31(0); 1usize << NTT_SCALING_LOG_SIZE]; NTT_SCALING_BASE_COLS];
    for (row, item) in scaling_schedule().iter().enumerate() {
        if item.poly >= profile.matrix_polys() {
            continue;
        }
        let input = states[item.poly][item.index];
        for (limb, value) in split12_11(input).into_iter().enumerate() {
            columns[S_INPUT + limb][row] = m31(value);
        }
        let (output, quotient, carries) = mul_witness(N_INV, input);
        write_canonical(&mut columns, S_OUTPUT, S_OUTPUT_SLACK, row, output);
        write_value_limbs(&mut columns, S_QUOTIENT, row, quotient);
        record_canonical_uses(&mut range_uses, output);
        record_value_range_uses(&mut range_uses, quotient);
        for (limb, carry) in carries.into_iter().enumerate() {
            columns[S_CARRY + limb][row] = enc_signed(carry);
            range_uses.record(RcKind::Rc13, (carry + CARRY_OFFSET) as u32);
        }
        for (limb, digit) in balanced3(output).into_iter().enumerate() {
            columns[S_DIGIT + limb][row] = enc_signed(digit);
            range_uses.record(RcKind::Rc9, (digit + 256) as u32);
        }
    }
    trace.extend(
        columns
            .into_iter()
            .map(|column| col_eval(NTT_SCALING_LOG_SIZE, column)),
    );
    NttBase { trace, range_uses }
}

fn recompose2<F>(limbs: &[F; 2], c4096: F) -> F
where
    F: Clone + core::ops::Add<Output = F> + core::ops::Mul<Output = F>,
{
    limbs[0].clone() + c4096 * limbs[1].clone()
}

/// C7b: the three-level schoolbook multiplication (see the module comment
/// above `B_IN0`), Q-factored as `1 + 4096·2046` (so `q0=1` drops out,
/// `q1=2046` is used directly rather than via a separately-split `q`).
fn add_mul_constraints<E: EvalAtRow>(
    eval: &mut E,
    gate: E::F,
    constant: &[E::F; 2],
    input: &[E::F; 2],
    quotient: &[E::F; 2],
    output: &[E::F; 2],
    carries: &[E::F; 2],
) {
    let c2046 = E::F::from(m31(2046));
    let c4096 = E::F::from(m31(4096));
    let e0 = constant[0].clone() * input[0].clone() - quotient[0].clone() - output[0].clone();
    eval.add_constraint(gate.clone() * (e0 - c4096.clone() * carries[0].clone()));
    let e1 = constant[0].clone() * input[1].clone() + constant[1].clone() * input[0].clone()
        - quotient[1].clone()
        - c2046.clone() * quotient[0].clone()
        - output[1].clone()
        + carries[0].clone();
    eval.add_constraint(gate.clone() * (e1 - c4096 * carries[1].clone()));
    let e2 =
        constant[1].clone() * input[1].clone() - c2046 * quotient[1].clone() + carries[1].clone();
    eval.add_constraint(gate * e2);
}

fn add_canonical_constraint<E: EvalAtRow>(
    eval: &mut E,
    gate: E::F,
    value: &[E::F; 2],
    slack: &[E::F; 2],
) {
    add_canonical_constraint_with_bound(eval, gate, value, slack, Q - 1);
}

fn add_canonical_constraint_with_bound<E: EvalAtRow>(
    eval: &mut E,
    gate: E::F,
    value: &[E::F; 2],
    slack: &[E::F; 2],
    bound: u32,
) {
    let c4096 = E::F::from(m31(4096));
    eval.add_constraint(
        gate * (recompose2(value, c4096.clone()) + recompose2(slack, c4096)
            - E::F::from(m31(bound))),
    );
}

struct ButterflyTransition<F> {
    active: F,
    input0: F,
    input1: F,
    output0: F,
    diff: F,
    reduce: F,
    borrow: F,
    output_adjustment: i64,
}

fn add_butterfly_transition_constraints<E: EvalAtRow>(
    eval: &mut E,
    transition: ButterflyTransition<E::F>,
) {
    let ButterflyTransition {
        active,
        input0,
        input1,
        output0,
        diff,
        reduce,
        borrow,
        output_adjustment,
    } = transition;
    let one = E::F::one();
    let q = E::F::from(m31(Q));
    eval.add_constraint(reduce.clone() * (one.clone() - reduce.clone()));
    eval.add_constraint(borrow.clone() * (one - borrow.clone()));
    eval.add_constraint(
        active.clone()
            * (input0.clone() + input1.clone() - output0 - q.clone() * reduce
                + E::F::from(enc_signed(output_adjustment))),
    );
    eval.add_constraint(active * (input0 + q * borrow - input1 - diff));
}

/// Range-checks a value's 2 limbs only (Rc12, Rc11) -- for purely-modular
/// intermediates (`diff`, `quotient`) that never need the slack complement.
fn add_value_range_lookups<E: EvalAtRow>(
    eval: &mut E,
    relations: &PrivateKeyEvalRelations,
    gate: E::F,
    value: &[E::F; 2],
) {
    eval.add_to_relation(RelationEntry::base(
        &relations.range,
        gate.clone(),
        &range_tuple::<E>(value[0].clone(), RcKind::Rc12),
    ));
    eval.add_to_relation(RelationEntry::base(
        &relations.range,
        gate,
        &range_tuple::<E>(value[1].clone(), RcKind::Rc11),
    ));
}

/// Range-checks both the value and its slack complement (4 lookups total) --
/// for values consumed non-modularly downstream, where exact canonicity in
/// `[0, Q)` is load-bearing (see the C7a module comment above `B_IN0`).
fn add_canonical_range_lookups<E: EvalAtRow>(
    eval: &mut E,
    relations: &PrivateKeyEvalRelations,
    gate: E::F,
    value: &[E::F; 2],
    slack: &[E::F; 2],
) {
    add_value_range_lookups(eval, relations, gate.clone(), value);
    add_value_range_lookups(eval, relations, gate, slack);
}

/// AIR evaluator for one inverse-NTT butterfly row.
#[derive(Clone)]
pub struct NttButterflyEval {
    /// The verifier-selected parameter set.
    pub profile: MlDsaProfile,
    /// The relations this component draws on.
    pub relations: PrivateKeyEvalRelations,
}

impl FrameworkEval for NttButterflyEval {
    fn log_size(&self) -> u32 {
        NTT_BUTTERFLY_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(butterfly_active_id(self.profile));
        let poly = eval.get_preprocessed_column(butterfly_pre_id("poly"));
        let stage = eval.get_preprocessed_column(butterfly_pre_id("stage"));
        let index0 = eval.get_preprocessed_column(butterfly_pre_id("index0"));
        let index1 = eval.get_preprocessed_column(butterfly_pre_id("index1"));
        let twiddle = [
            eval.get_preprocessed_column(butterfly_pre_id("twiddle0")),
            eval.get_preprocessed_column(butterfly_pre_id("twiddle1")),
        ];
        let input0: [E::F; 2] = core::array::from_fn(|_| eval.next_trace_mask());
        let input1: [E::F; 2] = core::array::from_fn(|_| eval.next_trace_mask());
        let output0: [E::F; 2] = core::array::from_fn(|_| eval.next_trace_mask());
        let output0_slack: [E::F; 2] = core::array::from_fn(|_| eval.next_trace_mask());
        let diff: [E::F; 2] = core::array::from_fn(|_| eval.next_trace_mask());
        let output1: [E::F; 2] = core::array::from_fn(|_| eval.next_trace_mask());
        let output1_slack: [E::F; 2] = core::array::from_fn(|_| eval.next_trace_mask());
        let quotient: [E::F; 2] = core::array::from_fn(|_| eval.next_trace_mask());
        let reduce = eval.next_trace_mask();
        let borrow = eval.next_trace_mask();
        let carries: [E::F; 2] = core::array::from_fn(|_| eval.next_trace_mask());

        let one = E::F::one();
        let inactive = one.clone() - active.clone();
        for value in input0
            .iter()
            .chain(input1.iter())
            .chain(output0.iter())
            .chain(output0_slack.iter())
            .chain(diff.iter())
            .chain(output1.iter())
            .chain(output1_slack.iter())
            .chain(quotient.iter())
            .chain(core::iter::once(&reduce))
            .chain(core::iter::once(&borrow))
            .chain(carries.iter())
        {
            eval.add_constraint(inactive.clone() * value.clone());
        }
        let c4096 = E::F::from(m31(4096));
        let input0_value = recompose2(&input0, c4096.clone());
        let input1_value = recompose2(&input1, c4096.clone());
        let output0_value = recompose2(&output0, c4096.clone());
        let diff_value = recompose2(&diff, c4096);

        add_butterfly_transition_constraints(
            &mut eval,
            ButterflyTransition {
                active: active.clone(),
                input0: input0_value,
                input1: input1_value,
                output0: output0_value,
                diff: diff_value,
                reduce,
                borrow,
                output_adjustment: 0,
            },
        );
        for (value, slack) in [(&output0, &output0_slack), (&output1, &output1_slack)] {
            add_canonical_constraint(&mut eval, active.clone(), value, slack);
        }
        add_mul_constraints(
            &mut eval,
            active.clone(),
            &twiddle,
            &diff,
            &quotient,
            &output1,
            &carries,
        );

        let next_stage = stage.clone() + one;
        for (numerator, row_stage, index, value) in [
            (-active.clone(), stage.clone(), index0.clone(), &input0),
            (-active.clone(), stage.clone(), index1.clone(), &input1),
            (active.clone(), next_stage.clone(), index0, &output0),
            (active.clone(), next_stage, index1, &output1),
        ] {
            eval.add_to_relation(RelationEntry::base(
                &self.relations.ntt,
                numerator,
                &[
                    poly.clone(),
                    row_stage,
                    index,
                    value[0].clone(),
                    value[1].clone(),
                ],
            ));
        }
        // Emission order must match `gen_ntt_interaction`'s `push_range_entries`
        // calls exactly: output0 (canonical), diff (value-only), output1
        // (canonical), quotient (value-only).
        add_canonical_range_lookups(
            &mut eval,
            &self.relations,
            active.clone(),
            &output0,
            &output0_slack,
        );
        add_value_range_lookups(&mut eval, &self.relations, active.clone(), &diff);
        add_canonical_range_lookups(
            &mut eval,
            &self.relations,
            active.clone(),
            &output1,
            &output1_slack,
        );
        add_value_range_lookups(&mut eval, &self.relations, active.clone(), &quotient);
        for carry in carries {
            eval.add_to_relation(RelationEntry::base(
                &self.relations.range,
                active.clone(),
                &range_tuple::<E>(carry + E::F::from(m31(CARRY_OFFSET as u32)), RcKind::Rc13),
            ));
        }
        eval.finalize_logup_batched(LOGUP_BATCH);
        eval
    }
}

/// AIR evaluator for the inverse-NTT scaling and Horner evaluation rows.
#[derive(Clone)]
pub struct NttScalingEval {
    /// The verifier-selected parameter set.
    pub profile: MlDsaProfile,
    /// Drawn Horner evaluation point `r`.
    pub r: SecureField,
    /// Drawn digit-combination point `s`.
    pub s: SecureField,
    /// The relations this component draws on.
    pub relations: PrivateKeyEvalRelations,
}

impl FrameworkEval for NttScalingEval {
    fn log_size(&self) -> u32 {
        NTT_SCALING_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(scaling_active_id(self.profile));
        let eval_start = eval.get_preprocessed_column(scaling_pre_id("eval_start"));
        let eval_end = eval.get_preprocessed_column(scaling_pre_id("eval_end"));
        let poly = eval.get_preprocessed_column(scaling_pre_id("poly"));
        let index = eval.get_preprocessed_column(scaling_pre_id("index"));
        let input: [E::F; 2] = core::array::from_fn(|_| eval.next_trace_mask());
        let output: [E::F; 2] = core::array::from_fn(|_| eval.next_trace_mask());
        let output_slack: [E::F; 2] = core::array::from_fn(|_| eval.next_trace_mask());
        let quotient: [E::F; 2] = core::array::from_fn(|_| eval.next_trace_mask());
        let carries: [E::F; 2] = core::array::from_fn(|_| eval.next_trace_mask());
        let digits: [E::F; 3] = core::array::from_fn(|_| eval.next_trace_mask());
        let acc_masks: [[E::F; 2]; SECURE_EXTENSION_DEGREE] =
            core::array::from_fn(|_| eval.next_interaction_mask(INTERACTION_TRACE_IDX, [-1, 0]));
        let acc_prev = E::combine_ef(acc_masks.each_ref().map(|mask| mask[0].clone()));
        let acc_cur = E::combine_ef(acc_masks.each_ref().map(|mask| mask[1].clone()));

        let inactive = E::F::one() - active.clone();
        for value in input
            .iter()
            .chain(output.iter())
            .chain(output_slack.iter())
            .chain(quotient.iter())
            .chain(carries.iter())
            .chain(digits.iter())
        {
            eval.add_constraint(inactive.clone() * value.clone());
        }

        add_canonical_constraint(&mut eval, active.clone(), &output, &output_slack);
        let constant = split12_11(N_INV).map(|value| E::F::from(m31(value)));
        add_mul_constraints(
            &mut eval,
            active.clone(),
            &constant,
            &input,
            &quotient,
            &output,
            &carries,
        );
        let output_value = recompose2(&output, E::F::from(m31(4096)));
        let digit_value = digits[0].clone()
            + E::F::from(m31(B as u32)) * digits[1].clone()
            + E::F::from(m31((B * B) as u32)) * digits[2].clone();
        eval.add_constraint(active.clone() * (output_value - digit_value));

        let mut s_power = SecureField::one();
        let mut digit_row = E::EF::zero();
        for digit in &digits {
            digit_row += E::EF::from(digit.clone()) * E::EF::from(s_power);
            s_power *= self.s;
        }
        let expected_acc = E::EF::from(active.clone())
            * (E::EF::from(E::F::one() - eval_start) * acc_prev * E::EF::from(self.r) + digit_row);
        eval.add_constraint(acc_cur - expected_acc);

        eval.add_to_relation(RelationEntry::base(
            &self.relations.ntt,
            -active.clone(),
            &[
                poly.clone(),
                E::F::from(m31(NTT_STAGES as u32)),
                index,
                input[0].clone(),
                input[1].clone(),
            ],
        ));
        add_canonical_range_lookups(
            &mut eval,
            &self.relations,
            active.clone(),
            &output,
            &output_slack,
        );
        add_value_range_lookups(&mut eval, &self.relations, active.clone(), &quotient);
        for carry in carries {
            eval.add_to_relation(RelationEntry::base(
                &self.relations.range,
                active.clone(),
                &range_tuple::<E>(carry + E::F::from(m31(CARRY_OFFSET as u32)), RcKind::Rc13),
            ));
        }
        for digit in digits {
            eval.add_to_relation(RelationEntry::base(
                &self.relations.range,
                active.clone(),
                &range_tuple::<E>(digit + E::F::from(m31(256)), RcKind::Rc9),
            ));
        }
        let mut tuple = vec![poly + E::F::from(m31(A_EVAL_BASE as u32))];
        tuple.extend(acc_masks.iter().map(|mask| mask[1].clone()));
        eval.add_to_relation(RelationEntry::base(&self.relations.eval, -eval_end, &tuple));
        eval.finalize_logup_batched(LOGUP_BATCH);
        eval
    }
}

/// LogUp claimed sums of the two inverse-NTT components.
#[derive(Clone, Copy, Debug, Default)]
pub struct NttClaims {
    /// Butterfly-chain claimed sum.
    pub butterfly: SecureField,
    /// Scaling/eval claimed sum.
    pub scaling: SecureField,
}

/// Interaction-trace output of the inverse-NTT components.
pub struct NttInteraction {
    /// The concatenated butterfly and scaling interaction columns.
    pub trace: Vec<ColEval>,
    /// `a_evals[poly]` = claimed `Â_ij(r, s)`, row-major.
    pub a_evals: Vec<SecureField>,
    /// The two components' claimed sums.
    pub claims: NttClaims,
}

/// Mirrors `add_value_range_lookups`: 2 value-limb entries only (Rc12, Rc11).
fn push_value_range_entries(
    entries: &mut Vec<(SecureField, SecureField)>,
    relations: &PrivateKeyEvalRelations,
    value: u32,
) {
    let limbs = split12_11(value);
    entries.push((
        SecureField::one(),
        range_denominator(&relations.range, limbs[0], RcKind::Rc12),
    ));
    entries.push((
        SecureField::one(),
        range_denominator(&relations.range, limbs[1], RcKind::Rc11),
    ));
}

/// Mirrors `add_canonical_range_lookups`: value-limb entries plus their slack
/// complement (4 total).
fn push_range_entries(
    entries: &mut Vec<(SecureField, SecureField)>,
    relations: &PrivateKeyEvalRelations,
    value: u32,
) {
    push_value_range_entries(entries, relations, value);
    push_value_range_entries(entries, relations, Q - 1 - value);
}

/// Generate the butterfly and scaling interaction traces at the drawn
/// `(r, s)`.
pub fn gen_ntt_interaction(
    profile: MlDsaProfile,
    a_hat: &[NttPoly],
    r: SecureField,
    s: SecureField,
    relations: &PrivateKeyEvalRelations,
) -> NttInteraction {
    assert_eq!(a_hat.len(), MATRIX_POLYS);
    let zero = SecureField::zero();
    let one = SecureField::one();
    let mut states = a_hat.to_vec();
    let mut rows =
        vec![vec![(zero, one); NTT_BUTTERFLY_LOGUP_ENTRIES]; 1usize << NTT_BUTTERFLY_LOG_SIZE];
    for (row, item) in butterfly_schedule().iter().enumerate() {
        if item.poly >= profile.matrix_polys() {
            continue;
        }
        let input0 = states[item.poly][item.index0];
        let input1 = states[item.poly][item.index1];
        let input0_limbs = split12_11(input0);
        let input1_limbs = split12_11(input1);
        let mut entries = Vec::with_capacity(NTT_BUTTERFLY_LOGUP_ENTRIES);
        entries.push((
            -one,
            relations.ntt.combine(&[
                m31(item.poly as u32),
                m31(item.stage as u32),
                m31(item.index0 as u32),
                m31(input0_limbs[0]),
                m31(input0_limbs[1]),
            ]),
        ));
        entries.push((
            -one,
            relations.ntt.combine(&[
                m31(item.poly as u32),
                m31(item.stage as u32),
                m31(item.index1 as u32),
                m31(input1_limbs[0]),
                m31(input1_limbs[1]),
            ]),
        ));
        let sum = input0 + input1;
        let output0 = if sum >= Q { sum - Q } else { sum };
        let diff = if input0 < input1 {
            input0 + Q - input1
        } else {
            input0 - input1
        };
        let (output1, quotient, carries) = mul_witness(item.twiddle, diff);
        let output0_limbs = split12_11(output0);
        let output1_limbs = split12_11(output1);
        entries.push((
            one,
            relations.ntt.combine(&[
                m31(item.poly as u32),
                m31((item.stage + 1) as u32),
                m31(item.index0 as u32),
                m31(output0_limbs[0]),
                m31(output0_limbs[1]),
            ]),
        ));
        entries.push((
            one,
            relations.ntt.combine(&[
                m31(item.poly as u32),
                m31((item.stage + 1) as u32),
                m31(item.index1 as u32),
                m31(output1_limbs[0]),
                m31(output1_limbs[1]),
            ]),
        ));
        states[item.poly][item.index0] = output0;
        states[item.poly][item.index1] = output1;
        // Order must match the AIR: output0 (canonical), diff (value-only),
        // output1 (canonical), quotient (value-only).
        push_range_entries(&mut entries, relations, output0);
        push_value_range_entries(&mut entries, relations, diff);
        push_range_entries(&mut entries, relations, output1);
        push_value_range_entries(&mut entries, relations, quotient);
        for carry in carries {
            entries.push((
                one,
                range_denominator(
                    &relations.range,
                    (carry + CARRY_OFFSET) as u32,
                    RcKind::Rc13,
                ),
            ));
        }
        assert_eq!(entries.len(), NTT_BUTTERFLY_LOGUP_ENTRIES);
        rows[row] = entries;
    }
    let (butterfly_trace, butterfly_claim) =
        gen_batched_logup(NTT_BUTTERFLY_LOG_SIZE, &rows, NTT_BUTTERFLY_LOGUP_ENTRIES);

    let mut rows =
        vec![vec![(zero, one); NTT_SCALING_LOGUP_ENTRIES]; 1usize << NTT_SCALING_LOG_SIZE];
    let mut acc = vec![zero; 1usize << NTT_SCALING_LOG_SIZE];
    let mut a_evals = vec![zero; MATRIX_POLYS];
    let mut running = zero;
    for (row, item) in scaling_schedule().iter().enumerate() {
        if item.poly >= profile.matrix_polys() {
            acc[row] = zero;
            if item.eval_end {
                rows[row][NTT_SCALING_LOGUP_ENTRIES - 1] = (
                    -one,
                    relations.eval.combine(&[
                        m31((A_EVAL_BASE + item.poly) as u32),
                        m31(0),
                        m31(0),
                        m31(0),
                        m31(0),
                    ]),
                );
            }
            continue;
        }
        let input = states[item.poly][item.index];
        let input_limbs = split12_11(input);
        let mut entries = Vec::with_capacity(NTT_SCALING_LOGUP_ENTRIES);
        entries.push((
            -one,
            relations.ntt.combine(&[
                m31(item.poly as u32),
                m31(NTT_STAGES as u32),
                m31(item.index as u32),
                m31(input_limbs[0]),
                m31(input_limbs[1]),
            ]),
        ));
        let (output, quotient, carries) = mul_witness(N_INV, input);
        push_range_entries(&mut entries, relations, output);
        push_value_range_entries(&mut entries, relations, quotient);
        for carry in carries {
            entries.push((
                one,
                range_denominator(
                    &relations.range,
                    (carry + CARRY_OFFSET) as u32,
                    RcKind::Rc13,
                ),
            ));
        }
        let digits = balanced3(output);
        let digit_row = SecureField::from(enc_signed(digits[0]))
            + s * SecureField::from(enc_signed(digits[1]))
            + s * s * SecureField::from(enc_signed(digits[2]));
        running = if item.eval_start {
            digit_row
        } else {
            running * r + digit_row
        };
        acc[row] = running;
        for digit in digits {
            entries.push((
                one,
                range_denominator(&relations.range, (digit + 256) as u32, RcKind::Rc9),
            ));
        }
        if item.eval_end {
            a_evals[item.poly] = running;
            let coords = running.to_m31_array();
            entries.push((
                -one,
                relations.eval.combine(&[
                    m31((A_EVAL_BASE + item.poly) as u32),
                    coords[0],
                    coords[1],
                    coords[2],
                    coords[3],
                ]),
            ));
        } else {
            entries.push((zero, one));
        }
        assert_eq!(entries.len(), NTT_SCALING_LOGUP_ENTRIES);
        rows[row] = entries;
    }
    let mut scaling_trace: Vec<_> = (0..SECURE_EXTENSION_DEGREE)
        .map(|coordinate| {
            col_eval(
                NTT_SCALING_LOG_SIZE,
                acc.iter()
                    .map(|value| value.to_m31_array()[coordinate])
                    .collect(),
            )
        })
        .collect();
    let (scaling_logup, scaling_claim) =
        gen_batched_logup(NTT_SCALING_LOG_SIZE, &rows, NTT_SCALING_LOGUP_ENTRIES);
    scaling_trace.extend(scaling_logup);
    let mut trace = butterfly_trace;
    trace.extend(scaling_trace);
    NttInteraction {
        trace,
        a_evals,
        claims: NttClaims {
            butterfly: butterfly_claim,
            scaling: scaling_claim,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::private_key_eval::proof_test::{active_id as test_active_id, OneRowAir};
    use stwo::core::pcs::PcsConfig;
    use stwo::prover::backend::simd::m31::LOG_N_LANES;

    #[derive(Clone, Copy)]
    enum Formula {
        Butterfly { output_adjustment: i64 },
        Normalizer { constant: u32 },
        Canonical { bound: u32 },
    }

    #[derive(Clone)]
    struct FormulaEval {
        formula: Formula,
    }

    impl FrameworkEval for FormulaEval {
        fn log_size(&self) -> u32 {
            LOG_N_LANES
        }

        fn max_constraint_log_degree_bound(&self) -> u32 {
            LOG_N_LANES + 1
        }

        fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
            let fixed_active = eval.get_preprocessed_column(test_active_id());
            let active = eval.next_trace_mask();
            eval.add_constraint(active.clone() - fixed_active);
            match self.formula {
                Formula::Butterfly { output_adjustment } => {
                    let input0 = eval.next_trace_mask();
                    let input1 = eval.next_trace_mask();
                    let output0 = eval.next_trace_mask();
                    let diff = eval.next_trace_mask();
                    let reduce = eval.next_trace_mask();
                    let borrow = eval.next_trace_mask();
                    add_butterfly_transition_constraints(
                        &mut eval,
                        ButterflyTransition {
                            active,
                            input0,
                            input1,
                            output0,
                            diff,
                            reduce,
                            borrow,
                            output_adjustment,
                        },
                    );
                }
                Formula::Normalizer { constant } => {
                    let input = core::array::from_fn(|_| eval.next_trace_mask());
                    let quotient = core::array::from_fn(|_| eval.next_trace_mask());
                    let output = core::array::from_fn(|_| eval.next_trace_mask());
                    let carries = core::array::from_fn(|_| eval.next_trace_mask());
                    add_mul_constraints(
                        &mut eval,
                        active,
                        &split12_11(constant).map(|value| E::F::from(m31(value))),
                        &input,
                        &quotient,
                        &output,
                        &carries,
                    );
                }
                Formula::Canonical { bound } => {
                    let value = core::array::from_fn(|_| eval.next_trace_mask());
                    let slack = core::array::from_fn(|_| eval.next_trace_mask());
                    add_canonical_constraint_with_bound(&mut eval, active, &value, &slack, bound);
                }
            }
            let dummy = eval.next_interaction_mask(INTERACTION_TRACE_IDX, [0]);
            eval.add_constraint(dummy[0].clone());
            eval
        }
    }

    fn assert_forged_formula_rejected(label: &str, trace: &[M31], forged: Formula, exact: Formula) {
        let mut prover = OneRowAir::new(FormulaEval { formula: forged }, trace);
        let proof = air_core::prove(&mut [&mut prover], PcsConfig::default())
            .unwrap_or_else(|error| panic!("{label}: forged proving failed: {error:?}"));
        let mut forged_verifier = OneRowAir::new(FormulaEval { formula: forged }, trace);
        air_core::verify(&mut [&mut forged_verifier], &proof)
            .unwrap_or_else(|error| panic!("{label}: forged control failed: {error:?}"));
        let mut exact_verifier = OneRowAir::new(FormulaEval { formula: exact }, trace);
        assert!(
            air_core::verify(&mut [&mut exact_verifier], &proof).is_err(),
            "{label}: the exact formula must reject the input"
        );
    }

    #[test]
    fn malformed_inverse_ntt_rows_prove_only_under_forged_formulas() {
        assert_forged_formula_rejected(
            "inverse-butterfly transition",
            &[m31(1), m31(10), m31(3), m31(14), m31(7), m31(0), m31(0)],
            Formula::Butterfly {
                output_adjustment: 1,
            },
            Formula::Butterfly {
                output_adjustment: 0,
            },
        );

        let input = 123_456;
        let (output, quotient, carries) = mul_witness(N_INV - 1, input);
        let mut normalization_trace = vec![m31(1)];
        normalization_trace.extend(split12_11(input).map(m31));
        normalization_trace.extend(split12_11(quotient).map(m31));
        normalization_trace.extend(split12_11(output).map(m31));
        normalization_trace.extend(carries.map(enc_signed));
        assert_forged_formula_rejected(
            "inverse normalization",
            &normalization_trace,
            Formula::Normalizer {
                constant: N_INV - 1,
            },
            Formula::Normalizer { constant: N_INV },
        );

        // C7a(N1): this generic alias check is exactly the mechanism the
        // RETAINED output0/output1/S_OUTPUT canonicity slack relies on (each
        // wraps `add_canonical_constraint`, i.e. this same `bound = Q-1`
        // formula). A forged prover claiming the wider `bound = 2*Q-1` can
        // accept the alias (out+Q, k-1) below; the exact `bound = Q-1`
        // verifier rejects it. `diff`/`quotient` no longer carry this
        // constraint at all post-C7a (see the module comment above `B_IN0`),
        // so this test's coverage is now specifically of the slack that
        // remains load-bearing.
        let alias = Q + 5;
        let slack = Q - 1 - 5;
        let mut alias_trace = vec![m31(1)];
        alias_trace.extend(split12_11(alias).map(m31));
        alias_trace.extend(split12_11(slack).map(m31));
        assert_forged_formula_rejected(
            "inverse-NTT modular alias",
            &alias_trace,
            Formula::Canonical { bound: 2 * Q - 1 },
            Formula::Canonical { bound: Q - 1 },
        );
    }

    /// C7a(N2), re-limbed for C7b: `quotient`'s high limb is still
    /// range-checked via a single value-only Rc11 lookup after deleting its
    /// canonicity slack (only the slack-complement lookup pair was removed;
    /// requirement #1 of the C7a finding keeps the value-limb lookups).
    /// Rc11's domain is exactly `[0, 2048)`; the first excluded value (2048)
    /// cannot even be recorded in the witness-side multiplicity bookkeeping,
    /// since `RcUses::record` indexes its per-value counter vector
    /// directly -- proving no honest witness (and no witness the real AIR's
    /// identical Rc11 lookup could balance) can carry a quotient with a high
    /// limb of 2048 or more.
    #[test]
    #[should_panic]
    fn quotient_high_limb_at_table_boundary_cannot_be_recorded() {
        let value_with_limb1_2048 = 1u32 << 23; // split12_11(2^23) = [0, 2048]
        assert_eq!(split12_11(value_with_limb1_2048)[1], 2048);
        let mut uses = RcUses::new();
        record_value_range_uses(&mut uses, value_with_limb1_2048);
    }

    /// C7a(N3): with `diff`'s canonicity slack deleted, `borrow` is no longer
    /// uniquely pinned by the constraints when `input0 - input1 <= 8190`:
    /// both `(borrow=0, diff=input0-input1)` and
    /// `(borrow=1, diff=input0-input1+Q)` satisfy every remaining constraint
    /// (boolean `borrow`, the linear transition equation, and diff's
    /// value-only range check, since both diffs land inside `[0, 2^23)`).
    /// This is ACCEPTED non-uniqueness, not a soundness gap: `output1` (the
    /// only downstream consumer, itself canonically range-checked) is
    /// identical either way, since `z*diff ≡ z*(diff+Q) (mod Q)` and
    /// `mul_witness` absorbs the difference entirely into `quotient`.
    #[test]
    fn borrow_alias_below_diff_boundary_yields_identical_output1() {
        let twiddle = zeta_table()[1];
        let input0 = 8_190;
        let input1 = 0u32;
        assert!(input0 - input1 <= 8_190);

        let diff_no_borrow = input0 - input1;
        let diff_with_borrow = input0 + Q - input1;
        assert!(diff_no_borrow < (1 << 23));
        assert!(diff_with_borrow < (1 << 23));

        let (output1_no_borrow, _, _) = mul_witness(twiddle, diff_no_borrow);
        let (output1_with_borrow, _, _) = mul_witness(twiddle, diff_with_borrow);
        assert_eq!(
            output1_no_borrow, output1_with_borrow,
            "both accepted (borrow, diff) witnesses must yield the same output1"
        );
    }

    /// C7a(N4), re-limbed for C7b: one step past the N3 alias boundary
    /// (`input0 - input1 = 8191`), the borrowed diff `input0 + Q - input1`
    /// lands exactly at `2^23`, whose high limb is 2048 -- rejected by the
    /// same value-only Rc11 lookup as N2, this time via the concrete
    /// borrow-alias construction that produces it.
    #[test]
    #[should_panic]
    fn diff_at_borrow_alias_boundary_plus_one_rejected() {
        let input0 = 8_191;
        let input1 = 0u32;
        let diff_with_borrow = input0 + Q - input1;
        assert_eq!(diff_with_borrow, 1 << 23);
        let mut uses = RcUses::new();
        record_value_range_uses(&mut uses, diff_with_borrow);
    }

    #[test]
    fn schedules_cover_every_required_cell_once() {
        let schedule = butterfly_schedule();
        assert_eq!(schedule.len(), MATRIX_POLYS * NTT_STAGES * N / 2);
        let mut seen = vec![vec![vec![false; N]; NTT_STAGES]; MATRIX_POLYS];
        for item in schedule {
            assert!(!seen[item.poly][item.stage][item.index0]);
            assert!(!seen[item.poly][item.stage][item.index1]);
            seen[item.poly][item.stage][item.index0] = true;
            seen[item.poly][item.stage][item.index1] = true;
        }
        assert!(seen.into_iter().flatten().flatten().all(|value| value));
        assert_eq!(scaling_schedule().len(), MATRIX_POLYS * N);
    }

    #[test]
    fn inverse_ntt_and_horner_match_independent_reference() {
        let expanded = crate::reference::expand_a::expand_a(ML_DSA_65, &[9; 32]);
        let mut a_hat = Vec::new();
        for i in 0..K {
            for j in 0..L {
                a_hat.push(expanded.matrix[i][j]);
            }
        }
        let r = SecureField::from(m31(13));
        let s = SecureField::from(m31(29));
        let interaction =
            gen_ntt_interaction(ML_DSA_65, &a_hat, r, s, &PrivateKeyEvalRelations::dummy());
        for (poly, source) in a_hat.iter().enumerate() {
            let coefficients = crate::reference::ntt::ntt_inverse(source);
            let mut expected = SecureField::zero();
            for &coefficient in coefficients.iter().rev() {
                let digits = balanced3(coefficient);
                let row = SecureField::from(enc_signed(digits[0]))
                    + s * SecureField::from(enc_signed(digits[1]))
                    + s * s * SecureField::from(enc_signed(digits[2]));
                expected = expected * r + row;
            }
            assert_eq!(interaction.a_evals[poly], expected);
        }
    }

    /// C7b(N6): boundary sweep over all 257 multiplication constants the
    /// real circuit ever uses (256 butterfly twiddles `Q - zeta[m]` + the
    /// scaling constant `N_INV`), crossed with the values named in the C7b
    /// finding plus a handful of pseudo-random samples. `c1` has only 9
    /// units of honest headroom (`c1 ∈ [-1, 4094]` against the `[-4096,4096)`
    /// Rc13 window), so this exhaustive-constants sweep is mandatory, not a
    /// spot check.
    #[test]
    fn multiplication_witness_is_exact_at_boundaries() {
        let zetas = zeta_table();
        let mut constants: Vec<u32> = zetas.iter().map(|&zeta| Q - zeta).collect();
        constants.push(N_INV);
        assert_eq!(constants.len(), 257);

        let mut values = vec![
            0,
            1,
            4095,
            4096,
            8190,
            8191,
            Q / 2,
            Q - 2,
            Q - 1,
            (1 << 23) - 1,
        ];
        let mut rng_state = 0x2026_0805_c7b0_0001u64;
        for _ in 0..8 {
            // A tiny xorshift PRNG: deterministic, dependency-free "random"
            // coverage alongside the named boundary values.
            rng_state ^= rng_state << 13;
            rng_state ^= rng_state >> 7;
            rng_state ^= rng_state << 17;
            values.push((rng_state % Q as u64) as u32);
        }

        for &constant in &constants {
            for &value in &values {
                let (output, quotient, carries) = mul_witness(constant, value);
                assert_eq!(
                    constant as u64 * value as u64,
                    output as u64 + Q as u64 * quotient as u64
                );
                assert!(output < (1 << 23) && quotient < (1 << 23));
                assert!(carries
                    .iter()
                    .all(|carry| (-CARRY_OFFSET..CARRY_OFFSET).contains(carry)));
            }
        }
    }

    /// C7b(N8): a mutant that naively reuses the OLD 8/8/7-bit byte split's
    /// first two limbs (`b0`, `b1`) as if they were the NEW 12/11-bit split's
    /// `(a0, a1)` -- rather than actually re-limbing (`a0 = b0 + 256·lo4`,
    /// `a1 = hi4 + 16·low7`) -- yields a tuple that does not `combine` to the
    /// same value as the real (correctly re-limbed) yield, for any value
    /// that doesn't fit in a single byte. This is exactly the class of bug a
    /// missed re-limb site produces: an "exact but wrong" equation that
    /// still type-checks and still range-checks each limb individually, but
    /// never balances against the real provider/consumer.
    #[test]
    fn mutant_old_three_limb_yield_fails_relation_balance() {
        let relations = PrivateKeyEvalRelations::dummy();
        let value = 123_456u32;
        let correct = split12_11(value);
        let correct_denominator: SecureField =
            relations
                .ntt
                .combine(&[m31(0), m31(0), m31(0), m31(correct[0]), m31(correct[1])]);

        // The old byte split's first two limbs, misused as if they were the
        // new nibble-based limbs.
        let mutant_b0 = value & 0xff;
        let mutant_b1 = (value >> 8) & 0xff;
        let mutant_denominator: SecureField =
            relations
                .ntt
                .combine(&[m31(0), m31(0), m31(0), m31(mutant_b0), m31(mutant_b1)]);
        assert_ne!(
            correct_denominator, mutant_denominator,
            "reusing the old byte-split limbs as the new 12/11-bit limbs must not \
             alias the correctly re-limbed yield"
        );
    }

    #[test]
    fn base_range_census_and_interaction_shape_are_exact() {
        let expanded = crate::reference::expand_a::expand_a(ML_DSA_65, &[42; 32]);
        let a_hat: Vec<_> = expanded.matrix.into_iter().flatten().collect();
        let base = gen_ntt_base(ML_DSA_65, &a_hat);
        let interaction = gen_ntt_interaction(
            ML_DSA_65,
            &a_hat,
            SecureField::from(m31(7)),
            SecureField::from(m31(11)),
            &PrivateKeyEvalRelations::dummy(),
        );
        assert_eq!(interaction.a_evals.len(), MATRIX_POLYS);
        assert_eq!(
            interaction.trace.len(),
            NTT_BUTTERFLY_INTERACTION_COLS + NTT_SCALING_INTERACTION_COLS
        );
        let butterfly_rows = (MATRIX_POLYS * NTT_STAGES * N / 2) as u32;
        let scaling_rows = (MATRIX_POLYS * N) as u32;
        // C7a deleted B_DIFF_SLACK/B_QUOTIENT_SLACK/S_QUOTIENT_SLACK: diff and
        // quotient contribute only 1 (value-only) Rc12/Rc11 instance each
        // instead of 2 (value+slack); output0/output1/output are unaffected.
        // C7b re-limbed every group from 3 columns (Rc8/Rc8/Rc7) to 2
        // (Rc12/Rc11), so each "instance" (value or slack) now contributes
        // exactly one Rc12 use and one Rc11 use -- butterfly has 6 instances
        // per row (output0 value+slack, diff, output1 value+slack, quotient),
        // scaling has 3 (output value+slack, quotient).
        assert_eq!(
            base.range_uses.for_kind(RcKind::Rc12).iter().sum::<u32>(),
            6 * butterfly_rows + 3 * scaling_rows
        );
        assert_eq!(
            base.range_uses.for_kind(RcKind::Rc11).iter().sum::<u32>(),
            6 * butterfly_rows + 3 * scaling_rows
        );
        // Carries: 2 per multiplication (was 4 pre-C7b), one multiplication
        // per row in both butterfly and scaling.
        assert_eq!(
            base.range_uses.for_kind(RcKind::Rc13).iter().sum::<u32>(),
            2 * butterfly_rows + 2 * scaling_rows
        );
        assert_eq!(
            base.range_uses.for_kind(RcKind::Rc9).iter().sum::<u32>(),
            3 * scaling_rows
        );
        assert_eq!(
            base.range_uses
                .for_kind(RcKind::Ternary)
                .iter()
                .sum::<u32>(),
            0
        );
    }
}
