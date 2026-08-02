//! Layered proof for the 24 `Keccak-f[1600]` rounds.
//!
//! The proof binds the committed sponge input nibbles to the committed sponge
//! output. It uses the physical trace row as the permutation coordinate.

use num_traits::{One, Zero};
use rayon::prelude::*;
use stwo::core::air::accumulation::PointEvaluationAccumulator;
use stwo::core::channel::Channel;
use stwo::core::fields::m31::{M31, P as M31_MODULUS};
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::core::pcs::{TreeSubspan, TreeVec};
use stwo::core::verifier::VerificationError;
use stwo::core::ColumnVec;
use stwo::prover::backend::simd::column::SecureColumn;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES, N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::Column;
use stwo::prover::lookups::mle::Mle;
use stwo_constraint_framework::mle_eval::MleCoeffColumnOracle;
use stwo_constraint_framework::{EvalAtRow, PointEvaluator, ORIGINAL_TRACE_IDX};

use crate::constants::{IOTA_RC, N_BYTES_IN_STATE, N_ROUNDS, RHO_OFFSETS};
use crate::sponge_v::{
    JobList, SpongeVRun, MAX_RATE, N_ABSORB_COLS, N_INPUT_NIBBLE_COLS, POST_COL_START,
};
use crate::utils::{circle_row_to_coset, spread_u32};

const PROTOCOL_TAG: u64 = 0x5453_3133_4b47_4b52;
const A_LOCAL_LOG: usize = 11;
const C_LOCAL_LOG: usize = 9;
const N_LOCAL_LOG: usize = 9;
const OUTPUT_SLOT_LOG: usize = 8;
const MAX_SUMCHECK_COEFFICIENTS: usize = EXTRACTION_DEGREE + 1;
const SPREAD_BYTE_SUM: u32 = 21_845;

const CHI_DEGREE: usize = 5;
const THETA_DEGREE: usize = 4;
const PARITY_DEGREE: usize = 6;
const MAX_GATE_SUMCHECK_COEFFICIENTS: usize = PARITY_DEGREE + 1;
const EXTRACTION_DEGREE: usize = 17;

/// Two MLE traces at the public row log size, with four base columns per
/// secure column.
pub const N_TIEBACK_COLUMNS: usize = 2 * 2 * SECURE_EXTENSION_DEGREE;
pub const PRODUCT_P_LOG: u32 = 9;
pub const PRODUCT_PAYLOAD_FIELDS: usize = 8_894;
pub const PRODUCT_PAYLOAD_BYTES: usize = 142_304;

const VALID_NIBBLES: [u32; 16] = [0, 1, 4, 5, 16, 17, 20, 21, 64, 65, 68, 69, 80, 81, 84, 85];

const _: () = assert!(N_INPUT_NIBBLE_COLS == 400);
const _: () = assert!(N_TIEBACK_COLUMNS == 16);
const _: () = assert!(payload_field_count(PRODUCT_P_LOG) == PRODUCT_PAYLOAD_FIELDS);
const _: () = assert!(payload_byte_count(PRODUCT_P_LOG) == PRODUCT_PAYLOAD_BYTES);

/// Return the fixed field count for a public permutation-domain size.
pub const fn payload_field_count(p_log: u32) -> usize {
    450 * p_log as usize + 4_844
}

/// Return the fixed payload size for a public permutation-domain size.
pub const fn payload_byte_count(p_log: u32) -> usize {
    payload_field_count(p_log) * SECURE_EXTENSION_DEGREE * size_of::<u32>()
}

fn invalid(message: impl Into<String>) -> VerificationError {
    VerificationError::InvalidStructure(format!("layered Keccak: {}", message.into()))
}

fn draw_nonbinary(channel: &mut impl Channel) -> SecureField {
    loop {
        let value = channel.draw_secure_felt();
        if value != SecureField::zero() && value != SecureField::one() {
            return value;
        }
    }
}

fn draw_point(channel: &mut impl Channel, n: usize) -> Vec<SecureField> {
    (0..n).map(|_| draw_nonbinary(channel)).collect()
}

fn mix_protocol(jobs: &JobList, channel: &mut impl Channel) {
    channel.mix_u64(PROTOCOL_TAG);
    jobs.mix_into(channel);
}

fn encode_field(value: SecureField, output: &mut Vec<u8>) {
    for limb in value.to_m31_array() {
        output.extend_from_slice(&limb.0.to_le_bytes());
    }
}

struct ProofWriter {
    bytes: Vec<u8>,
    fields: usize,
}

impl ProofWriter {
    fn new(p_log: u32) -> Self {
        Self {
            bytes: Vec::with_capacity(payload_byte_count(p_log)),
            fields: 0,
        }
    }

    fn write(&mut self, value: SecureField) {
        encode_field(value, &mut self.bytes);
        self.fields += 1;
    }

    fn write_many(&mut self, values: &[SecureField]) {
        for &value in values {
            self.write(value);
        }
    }

    fn finish(self, p_log: u32) -> Vec<u8> {
        assert_eq!(self.fields, payload_field_count(p_log));
        assert_eq!(self.bytes.len(), payload_byte_count(p_log));
        self.bytes
    }
}

struct ProofReader<'a> {
    bytes: &'a [u8],
    cursor: usize,
}

impl<'a> ProofReader<'a> {
    fn new(bytes: &'a [u8], p_log: u32) -> Result<Self, VerificationError> {
        let expected = payload_byte_count(p_log);
        if bytes.len() != expected {
            return Err(invalid(format!(
                "payload length is {}, expected {expected}",
                bytes.len()
            )));
        }
        Ok(Self { bytes, cursor: 0 })
    }

    fn read(&mut self) -> Result<SecureField, VerificationError> {
        let mut limbs = [M31::zero(); SECURE_EXTENSION_DEGREE];
        for limb in &mut limbs {
            let end = self
                .cursor
                .checked_add(size_of::<u32>())
                .ok_or_else(|| invalid("payload cursor overflow"))?;
            let bytes: [u8; 4] = self
                .bytes
                .get(self.cursor..end)
                .ok_or_else(|| invalid("short field encoding"))?
                .try_into()
                .expect("four-byte range");
            self.cursor = end;
            let raw = u32::from_le_bytes(bytes);
            if raw >= M31_MODULUS {
                return Err(invalid("noncanonical M31 limb"));
            }
            *limb = M31::from_u32_unchecked(raw);
        }
        Ok(SecureField::from_m31_array(limbs))
    }

    fn read_many(&mut self, n: usize) -> Result<Vec<SecureField>, VerificationError> {
        (0..n).map(|_| self.read()).collect()
    }

    fn finish(self) -> Result<(), VerificationError> {
        if self.cursor != self.bytes.len() {
            return Err(invalid("trailing payload bytes"));
        }
        Ok(())
    }
}

/// Check only the fixed raw codec. This function does not verify the proof.
pub fn is_canonical_payload(bytes: &[u8], p_log: u32) -> bool {
    let Ok(mut reader) = ProofReader::new(bytes, p_log) else {
        return false;
    };
    for _ in 0..payload_field_count(p_log) {
        if reader.read().is_err() {
            return false;
        }
    }
    reader.finish().is_ok()
}

/// Validate the one fixed product wire accepted by the TS13 envelope.
pub fn is_ts13_demo_layered_keccak_wire(bytes: &[u8]) -> bool {
    is_canonical_payload(bytes, PRODUCT_P_LOG)
}

fn eq_weights(point: &[SecureField]) -> Vec<SecureField> {
    let mut weights = vec![SecureField::one()];
    for &coordinate in point {
        let mut next = Vec::with_capacity(weights.len() * 2);
        for &weight in &weights {
            next.push(weight * (SecureField::one() - coordinate));
            next.push(weight * coordinate);
        }
        weights = next;
    }
    weights
}

fn eq_points(left: &[SecureField], right: &[SecureField]) -> SecureField {
    assert_eq!(left.len(), right.len());
    left.iter()
        .zip(right)
        .fold(SecureField::one(), |product, (&a, &b)| {
            product * ((SecureField::one() - a) * (SecureField::one() - b) + a * b)
        })
}

fn mle_eval(values: &[SecureField], point: &[SecureField]) -> SecureField {
    assert_eq!(values.len(), 1usize << point.len());
    let mut folded = values.to_vec();
    for &coordinate in point {
        let half = folded.len() / 2;
        let (left, right) = folded.split_at_mut(half);
        for i in 0..half {
            left[i] += coordinate * (right[i] - left[i]);
        }
        folded.truncate(half);
    }
    folded[0]
}

#[derive(Clone)]
struct BitMatrix {
    log_size: usize,
    words: Vec<u64>,
}

impl BitMatrix {
    fn zero(log_size: usize) -> Self {
        let bits = 1usize << log_size;
        Self {
            log_size,
            words: vec![0; bits.div_ceil(u64::BITS as usize)],
        }
    }

    fn get(&self, index: usize) -> bool {
        debug_assert!(index < 1usize << self.log_size);
        (self.words[index / 64] >> (index % 64)) & 1 != 0
    }

    fn set(&mut self, index: usize, value: bool) {
        if value {
            self.words[index / 64] |= 1 << (index % 64);
        }
    }

    fn swap_prefix_blocks(&mut self, left: usize, right: usize, local_log: usize) {
        assert!(local_log >= 6 && self.log_size >= local_log);
        let words_per_block = 1usize << (local_log - 6);
        for word in 0..words_per_block {
            self.words.swap(
                left * words_per_block + word,
                right * words_per_block + word,
            );
        }
    }
}

struct LayeredWitness {
    p_log: usize,
    active: Vec<bool>,
    inputs: Vec<[u8; N_BYTES_IN_STATE]>,
    outputs: Vec<[u8; N_BYTES_IN_STATE]>,
    a: Vec<BitMatrix>,
    b: Vec<BitMatrix>,
    c: Vec<BitMatrix>,
}

impl LayeredWitness {
    fn new(jobs: &JobList, run: &SpongeVRun) -> Self {
        assert_eq!(&run.jobs, jobs, "layered witness job list mismatch");
        assert_eq!(run.rows.len(), jobs.n_perms_total());

        let p_log = jobs.log_size() as usize;
        let n_p = 1usize << p_log;
        let row_to_coset = circle_row_to_coset(jobs.log_size());
        let schedule = crate::sponge_v::gen_schedule_preprocessed(jobs);
        let active = schedule[0]
            .values
            .to_cpu()
            .into_iter()
            .map(|value| value == M31::one())
            .collect::<Vec<_>>();
        assert_eq!(active.len(), n_p);

        let mut inputs = vec![[0u8; N_BYTES_IN_STATE]; n_p];
        let mut outputs = vec![[0u8; N_BYTES_IN_STATE]; n_p];
        for p in 0..n_p {
            let logical = row_to_coset[p];
            if logical >= run.rows.len() {
                continue;
            }
            inputs[p] = run.rows[logical].input;
            outputs[p] = run.rows[logical].post;
        }

        let mut a = Vec::with_capacity(N_ROUNDS + 1);
        let mut b = Vec::with_capacity(N_ROUNDS);
        let mut c = Vec::with_capacity(N_ROUNDS);
        let mut states = vec![[0u64; 25]; n_p];
        for (p, state) in states.iter_mut().enumerate() {
            for lane in 0..25 {
                state[lane] = u64::from_le_bytes(
                    inputs[p][8 * lane..8 * lane + 8]
                        .try_into()
                        .expect("one Keccak lane"),
                );
            }
        }
        a.push(Self::state_bits(p_log, &states));

        for round in 0..N_ROUNDS {
            let mut parity_words = vec![[0u64; 5]; n_p];
            let mut b_words = vec![[0u64; 25]; n_p];
            let mut next = vec![[0u64; 25]; n_p];
            for p in 0..n_p {
                if !active[p] {
                    continue;
                }
                for x in 0..5 {
                    parity_words[p][x] = (0..5).fold(0, |value, y| value ^ states[p][x + 5 * y]);
                }
                for target_y in 0..5 {
                    for target_x in 0..5 {
                        let source_x = (target_x + 3 * target_y) % 5;
                        let source_y = target_x;
                        let theta = states[p][source_x + 5 * source_y]
                            ^ parity_words[p][(source_x + 4) % 5]
                            ^ parity_words[p][(source_x + 1) % 5].rotate_left(1);
                        b_words[p][target_x + 5 * target_y] =
                            theta.rotate_left(RHO_OFFSETS[source_x][source_y] as u32);
                    }
                }
                for y in 0..5 {
                    for x in 0..5 {
                        let row = 5 * y;
                        next[p][row + x] = b_words[p][row + x]
                            ^ ((!b_words[p][row + (x + 1) % 5]) & b_words[p][row + (x + 2) % 5]);
                    }
                }
                next[p][0] ^= IOTA_RC[round];
            }
            c.push(Self::parity_bits(p_log, &parity_words));
            b.push(Self::state_bits(p_log, &b_words));
            states = next;
            a.push(Self::state_bits(p_log, &states));
        }

        Self {
            p_log,
            active,
            inputs,
            outputs,
            a,
            b,
            c,
        }
    }

    fn swap_permutation_rows(&mut self, left: usize, right: usize) {
        assert!(self.active[left] && self.active[right]);
        self.inputs.swap(left, right);
        self.outputs.swap(left, right);
        for layer in &mut self.a {
            layer.swap_prefix_blocks(left, right, A_LOCAL_LOG);
        }
        for layer in &mut self.b {
            layer.swap_prefix_blocks(left, right, A_LOCAL_LOG);
        }
        for layer in &mut self.c {
            layer.swap_prefix_blocks(left, right, C_LOCAL_LOG);
        }
    }

    fn state_bits(p_log: usize, states: &[[u64; 25]]) -> BitMatrix {
        let mut bits = BitMatrix::zero(p_log + A_LOCAL_LOG);
        for (p, state) in states.iter().enumerate() {
            for lane in 0..25 {
                let word = state[lane];
                for z in 0..64 {
                    bits.set((p << A_LOCAL_LOG) | (lane << 6) | z, (word >> z) & 1 != 0);
                }
            }
        }
        bits
    }

    fn parity_bits(p_log: usize, parity: &[[u64; 5]]) -> BitMatrix {
        let mut bits = BitMatrix::zero(p_log + C_LOCAL_LOG);
        for (p, columns) in parity.iter().enumerate() {
            for x in 0..5 {
                for z in 0..64 {
                    bits.set(
                        (p << C_LOCAL_LOG) | (x << 6) | z,
                        (columns[x] >> z) & 1 != 0,
                    );
                }
            }
        }
        bits
    }

    fn nibble_table(&self) -> Vec<SecureField> {
        let mut values = vec![SecureField::zero(); 1usize << (self.p_log + N_LOCAL_LOG)];
        for p in 0..1usize << self.p_log {
            for byte in 0..N_BYTES_IN_STATE {
                let value = self.inputs[p][byte];
                values[(p << N_LOCAL_LOG) | (2 * byte)] =
                    SecureField::from(M31::from(spread_u32(u32::from(value & 0x0f))));
                values[(p << N_LOCAL_LOG) | (2 * byte + 1)] =
                    SecureField::from(M31::from(spread_u32(u32::from(value >> 4))));
            }
        }
        values
    }

    fn output_fold(&self, slot_point: &[SecureField]) -> Vec<SecureField> {
        assert_eq!(slot_point.len(), OUTPUT_SLOT_LOG);
        let weights = eq_weights(slot_point);
        (0..1usize << self.p_log)
            .into_par_iter()
            .map(|p| {
                (0..N_BYTES_IN_STATE).fold(SecureField::zero(), |sum, byte| {
                    sum + weights[byte]
                        * SecureField::from(M31::from(spread_u32(u32::from(self.outputs[p][byte]))))
                })
            })
            .collect()
    }

    fn input_fold(&self, slot_point: &[SecureField]) -> Vec<SecureField> {
        assert_eq!(slot_point.len(), N_LOCAL_LOG);
        let weights = eq_weights(slot_point);
        (0..1usize << self.p_log)
            .into_par_iter()
            .map(|p| {
                (0..N_BYTES_IN_STATE).fold(SecureField::zero(), |sum, byte| {
                    let value = self.inputs[p][byte];
                    let low = SecureField::from(M31::from(spread_u32(u32::from(value & 0x0f))));
                    let high = SecureField::from(M31::from(spread_u32(u32::from(value >> 4))));
                    sum + weights[2 * byte] * low + weights[2 * byte + 1] * high
                })
            })
            .collect()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LayerDomain {
    A,
    B,
    C,
}

impl LayerDomain {
    const fn local_log(self) -> usize {
        match self {
            Self::A | Self::B => A_LOCAL_LOG,
            Self::C => C_LOCAL_LOG,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WireMap {
    Chi(usize),
    ThetaA,
    ThetaCLeft,
    ThetaCRight,
    Parity(usize),
}

impl WireMap {
    const fn source_domain(self) -> LayerDomain {
        match self {
            Self::Chi(_) => LayerDomain::A,
            Self::ThetaA | Self::ThetaCLeft | Self::ThetaCRight => LayerDomain::B,
            Self::Parity(_) => LayerDomain::C,
        }
    }

    const fn target_domain(self) -> LayerDomain {
        match self {
            Self::Chi(_) => LayerDomain::B,
            Self::ThetaA => LayerDomain::A,
            Self::ThetaCLeft | Self::ThetaCRight => LayerDomain::C,
            Self::Parity(_) => LayerDomain::A,
        }
    }

    fn map_local(self, local: usize) -> Option<usize> {
        match self {
            Self::Chi(read) => {
                let lane = local >> 6;
                let z = local & 63;
                if lane >= 25 || read >= 3 {
                    return None;
                }
                let x = lane % 5;
                let y = lane / 5;
                let source_x = (x + read) % 5;
                Some(((source_x + 5 * y) << 6) | z)
            }
            Self::ThetaA | Self::ThetaCLeft | Self::ThetaCRight => {
                let lane = local >> 6;
                let target_z = local & 63;
                if lane >= 25 {
                    return None;
                }
                let target_x = lane % 5;
                let target_y = lane / 5;
                let source_x = (target_x + 3 * target_y) % 5;
                let source_y = target_x;
                let source_z = (target_z + 64 - RHO_OFFSETS[source_x][source_y] % 64) % 64;
                match self {
                    Self::ThetaA => Some(((source_x + 5 * source_y) << 6) | source_z),
                    Self::ThetaCLeft => Some((((source_x + 4) % 5) << 6) | source_z),
                    Self::ThetaCRight => Some((((source_x + 1) % 5) << 6) | ((source_z + 63) % 64)),
                    _ => unreachable!(),
                }
            }
            Self::Parity(y) => {
                let x = local >> 6;
                let z = local & 63;
                (x < 5 && y < 5).then_some(((x + 5 * y) << 6) | z)
            }
        }
    }
}

#[derive(Clone)]
enum Kernel {
    Eq {
        point: Vec<SecureField>,
    },
    Read {
        point: Vec<SecureField>,
        map: WireMap,
    },
}

impl Kernel {
    fn target_domain(&self) -> LayerDomain {
        match self {
            Self::Eq { .. } => LayerDomain::A,
            Self::Read { map, .. } => map.target_domain(),
        }
    }

    fn factors(&self, p_log: usize, active: &[bool]) -> (Vec<SecureField>, Vec<SecureField>) {
        match self {
            Self::Eq { point } => {
                let local_log = self.target_domain().local_log();
                assert_eq!(point.len(), p_log + local_log);
                (eq_weights(&point[..p_log]), eq_weights(&point[p_log..]))
            }
            Self::Read { point, map } => {
                let from_log = map.source_domain().local_log();
                let to_log = map.target_domain().local_log();
                assert_eq!(point.len(), p_log + from_log);
                assert_eq!(active.len(), 1usize << p_log);
                let mut p_weights = eq_weights(&point[..p_log]);
                for (weight, &is_active) in p_weights.iter_mut().zip(active) {
                    if !is_active {
                        *weight = SecureField::zero();
                    }
                }
                let from_weights = eq_weights(&point[p_log..]);
                let mut local = vec![SecureField::zero(); 1usize << to_log];
                for (source, weight) in from_weights.into_iter().enumerate() {
                    if let Some(target) = map.map_local(source) {
                        local[target] += weight;
                    }
                }
                (p_weights, local)
            }
        }
    }

    #[cfg(test)]
    fn table(&self, p_log: usize, active: &[bool]) -> Vec<SecureField> {
        let (p_weights, local_weights) = self.factors(p_log, active);
        let local_log = self.target_domain().local_log();
        let mut table = vec![SecureField::zero(); 1usize << (p_log + local_log)];
        table
            .par_chunks_mut(1usize << local_log)
            .enumerate()
            .for_each(|(p, row)| {
                for (value, &local) in row.iter_mut().zip(&local_weights) {
                    *value = p_weights[p] * local;
                }
            });
        table
    }

    fn evaluate(&self, target_point: &[SecureField], p_log: usize, active: &[bool]) -> SecureField {
        let local_log = self.target_domain().local_log();
        assert_eq!(target_point.len(), p_log + local_log);
        match self {
            Self::Eq { point } => eq_points(point, target_point),
            Self::Read { .. } => {
                let (p_weights, local_weights) = self.factors(p_log, active);
                let p_eval: SecureField = p_weights
                    .iter()
                    .zip(eq_weights(&target_point[..p_log]))
                    .map(|(&a, b)| a * b)
                    .sum();
                let local_eval: SecureField = local_weights
                    .iter()
                    .zip(eq_weights(&target_point[p_log..]))
                    .map(|(&a, b)| a * b)
                    .sum();
                p_eval * local_eval
            }
        }
    }

    fn evaluate_restricted(
        &self,
        bit: usize,
        nibble_point: &[SecureField],
        p_log: usize,
        active: &[bool],
    ) -> SecureField {
        assert!(bit < 4);
        assert_eq!(self.target_domain(), LayerDomain::A);
        assert_eq!(nibble_point.len(), p_log + N_LOCAL_LOG);
        let (p_weights, a_weights) = self.factors(p_log, active);
        let p_eval: SecureField = p_weights
            .iter()
            .zip(eq_weights(&nibble_point[..p_log]))
            .map(|(&a, b)| a * b)
            .sum();
        let nibble_eq = eq_weights(&nibble_point[p_log..]);
        let mut local_eval = SecureField::zero();
        for (a_local, &weight) in a_weights.iter().enumerate() {
            let (_, nibble, selector) = a_to_nibble(a_local);
            if selector == bit {
                local_eval += weight * nibble_eq[nibble];
            }
        }
        p_eval * local_eval
    }
}

#[derive(Clone)]
struct Claim {
    value: SecureField,
    kernel: Kernel,
}

struct CombinedKernel {
    value: SecureField,
    terms: Vec<(SecureField, Kernel)>,
}

impl CombinedKernel {
    fn grouped_factors(
        &self,
        p_log: usize,
        active: &[bool],
    ) -> Vec<(Vec<SecureField>, Vec<SecureField>)> {
        let target = self.terms[0].1.target_domain();
        let mut factors: Vec<(Vec<SecureField>, Vec<SecureField>)> = Vec::new();
        for (coefficient, kernel) in &self.terms {
            assert_eq!(kernel.target_domain(), target);
            let (p_weights, mut local_weights) = kernel.factors(p_log, active);
            for value in &mut local_weights {
                *value *= *coefficient;
            }
            if let Some((_, sum)) = factors
                .iter_mut()
                .find(|(existing, _)| *existing == p_weights)
            {
                for (sum, value) in sum.iter_mut().zip(local_weights) {
                    *sum += value;
                }
            } else {
                factors.push((p_weights, local_weights));
            }
        }
        factors
    }

    fn table(&self, p_log: usize, active: &[bool]) -> Vec<PackedQM31> {
        let local_size = 1usize << self.terms[0].1.target_domain().local_log();
        let factors = self.grouped_factors(p_log, active);
        let factors = factors
            .into_iter()
            .map(|(p_weights, local_weights)| (p_weights, pack_values(local_weights)))
            .collect::<Vec<_>>();
        let packed_local_size = local_size / N_LANES;
        let mut output = vec![PackedQM31::zero(); (1usize << p_log) * packed_local_size];
        output
            .par_chunks_mut(packed_local_size)
            .enumerate()
            .for_each(|(p, row)| {
                for (p_weights, local_weights) in &factors {
                    let p_weight = PackedQM31::broadcast(p_weights[p]);
                    for (sum, &local_weight) in row.iter_mut().zip(local_weights) {
                        *sum += p_weight * local_weight;
                    }
                }
            });
        output
    }

    fn evaluate(&self, point: &[SecureField], p_log: usize, active: &[bool]) -> SecureField {
        self.terms
            .iter()
            .map(|(coefficient, kernel)| *coefficient * kernel.evaluate(point, p_log, active))
            .sum()
    }

    fn evaluate_restricted(
        &self,
        bit: usize,
        point: &[SecureField],
        p_log: usize,
        active: &[bool],
    ) -> SecureField {
        self.terms
            .iter()
            .map(|(coefficient, kernel)| {
                *coefficient * kernel.evaluate_restricted(bit, point, p_log, active)
            })
            .sum()
    }
}

fn combine_claims(claims: &[Claim], channel: &mut impl Channel) -> CombinedKernel {
    assert!(!claims.is_empty());
    let alpha = if claims.len() == 1 {
        SecureField::one()
    } else {
        channel.mix_felts(&claims.iter().map(|claim| claim.value).collect::<Vec<_>>());
        draw_nonbinary(channel)
    };
    let mut power = SecureField::one();
    let mut value = SecureField::zero();
    let mut terms = Vec::with_capacity(claims.len());
    for claim in claims {
        value += power * claim.value;
        terms.push((power, claim.kernel.clone()));
        power *= alpha;
    }
    CombinedKernel { value, terms }
}

fn a_to_nibble(a_local: usize) -> (usize, usize, usize) {
    let lane = a_local >> 6;
    let z = a_local & 63;
    let byte = 8 * lane + z / 8;
    let half = (z & 7) / 4;
    let bit = z & 3;
    (byte, 2 * byte + half, bit)
}

#[derive(Clone, Copy)]
struct Poly {
    coefficients: [SecureField; MAX_SUMCHECK_COEFFICIENTS],
    degree: usize,
}

impl Poly {
    fn zero() -> Self {
        Self {
            coefficients: [SecureField::zero(); MAX_SUMCHECK_COEFFICIENTS],
            degree: 0,
        }
    }

    fn constant(value: SecureField) -> Self {
        let mut output = Self::zero();
        output.coefficients[0] = value;
        output
    }

    fn linear(left: SecureField, right: SecureField) -> Self {
        let mut output = Self::zero();
        output.coefficients[0] = left;
        output.coefficients[1] = right - left;
        output.degree = usize::from(output.coefficients[1] != SecureField::zero());
        output
    }

    fn add(self, rhs: Self) -> Self {
        let mut output = Self::zero();
        output.degree = self.degree.max(rhs.degree);
        for i in 0..=output.degree {
            output.coefficients[i] = self.coefficients[i] + rhs.coefficients[i];
        }
        output
    }

    fn sub(self, rhs: Self) -> Self {
        self.add(rhs.scale(-SecureField::one()))
    }

    fn scale(mut self, scalar: SecureField) -> Self {
        for coefficient in &mut self.coefficients[..=self.degree] {
            *coefficient *= scalar;
        }
        self
    }

    fn mul(self, rhs: Self) -> Self {
        let degree = self.degree + rhs.degree;
        assert!(degree < MAX_SUMCHECK_COEFFICIENTS);
        let mut output = Self::zero();
        output.degree = degree;
        for i in 0..=self.degree {
            for j in 0..=rhs.degree {
                output.coefficients[i + j] += self.coefficients[i] * rhs.coefficients[j];
            }
        }
        output
    }
}

#[derive(Clone, Copy)]
struct PackedBasePoly {
    coefficients: [PackedM31; PARITY_DEGREE],
    degree: usize,
}

impl PackedBasePoly {
    fn zero() -> Self {
        Self {
            coefficients: [PackedM31::zero(); PARITY_DEGREE],
            degree: 0,
        }
    }

    fn constant(value: M31) -> Self {
        let mut output = Self::zero();
        output.coefficients[0] = PackedM31::broadcast(value);
        output
    }

    fn linear(left: PackedM31, right: PackedM31) -> Self {
        let mut output = Self::zero();
        output.coefficients[0] = left;
        output.coefficients[1] = right - left;
        output.degree = 1;
        output
    }

    fn add(self, rhs: Self) -> Self {
        let mut output = Self::zero();
        output.degree = self.degree.max(rhs.degree);
        for i in 0..=output.degree {
            output.coefficients[i] = self.coefficients[i] + rhs.coefficients[i];
        }
        output
    }

    fn sub(self, rhs: Self) -> Self {
        let mut output = Self::zero();
        output.degree = self.degree.max(rhs.degree);
        for i in 0..=output.degree {
            output.coefficients[i] = self.coefficients[i] - rhs.coefficients[i];
        }
        output
    }

    fn double(self) -> Self {
        self.add(self)
    }

    fn mul(self, rhs: Self) -> Self {
        let degree = self.degree + rhs.degree;
        assert!(degree < PARITY_DEGREE);
        let mut output = Self::zero();
        output.degree = degree;
        for i in 0..=self.degree {
            for j in 0..=rhs.degree {
                output.coefficients[i + j] += self.coefficients[i] * rhs.coefficients[j];
            }
        }
        output
    }
}

#[derive(Clone, Copy)]
struct PackedPolynomial<const N: usize> {
    coefficients: [PackedQM31; N],
    degree: usize,
}

type PackedGatePoly = PackedPolynomial<MAX_GATE_SUMCHECK_COEFFICIENTS>;
type PackedExtractionPoly = PackedPolynomial<MAX_SUMCHECK_COEFFICIENTS>;

impl<const N: usize> PackedPolynomial<N> {
    fn zero() -> Self {
        Self {
            coefficients: [PackedQM31::zero(); N],
            degree: 0,
        }
    }

    fn constant(value: SecureField) -> Self {
        let mut output = Self::zero();
        output.coefficients[0] = PackedQM31::broadcast(value);
        output
    }

    fn linear(left: PackedQM31, right: PackedQM31) -> Self {
        let mut output = Self::zero();
        output.coefficients[0] = left;
        output.coefficients[1] = right - left;
        output.degree = 1;
        output
    }

    fn add(self, rhs: Self) -> Self {
        let mut output = Self::zero();
        output.degree = self.degree.max(rhs.degree);
        for i in 0..=output.degree {
            output.coefficients[i] = self.coefficients[i] + rhs.coefficients[i];
        }
        output
    }

    fn sub(self, rhs: Self) -> Self {
        let mut output = Self::zero();
        output.degree = self.degree.max(rhs.degree);
        for i in 0..=output.degree {
            output.coefficients[i] = self.coefficients[i] - rhs.coefficients[i];
        }
        output
    }

    fn double(self) -> Self {
        self.add(self)
    }

    fn mul(self, rhs: Self) -> Self {
        let degree = self.degree + rhs.degree;
        assert!(degree < N);
        let mut output = Self::zero();
        output.degree = degree;
        for i in 0..=self.degree {
            for j in 0..=rhs.degree {
                output.coefficients[i + j] += self.coefficients[i] * rhs.coefficients[j];
            }
        }
        output
    }

    fn mul_base(self, rhs: PackedBasePoly) -> Self {
        let degree = self.degree + rhs.degree;
        assert!(degree < N);
        let mut output = Self::zero();
        output.degree = degree;
        for i in 0..=self.degree {
            for j in 0..=rhs.degree {
                output.coefficients[i + j] += self.coefficients[i] * rhs.coefficients[j];
            }
        }
        output
    }
}

fn packed_xor_polys(values: &[PackedGatePoly]) -> PackedGatePoly {
    let (first, rest) = values.split_first().expect("nonempty XOR");
    rest.iter().copied().fold(*first, |sum, value| {
        sum.add(value).sub(sum.mul(value).double())
    })
}

fn packed_base_xor_polys(values: &[PackedBasePoly]) -> PackedBasePoly {
    let (first, rest) = values.split_first().expect("nonempty XOR");
    rest.iter().copied().fold(*first, |sum, value| {
        sum.add(value).sub(sum.mul(value).double())
    })
}

fn xor_polys(values: &[Poly]) -> Poly {
    values.iter().copied().fold(Poly::zero(), |sum, value| {
        sum.add(value)
            .sub(sum.mul(value).scale(SecureField::from(2)))
    })
}

fn xor_values(values: &[SecureField]) -> SecureField {
    values
        .iter()
        .copied()
        .fold(SecureField::zero(), |sum, value| {
            sum + value - SecureField::from(2) * sum * value
        })
}

#[derive(Clone, Copy)]
enum GateKind {
    Chi,
    Theta,
    Parity,
}

impl GateKind {
    const fn degree(self) -> usize {
        match self {
            Self::Chi => CHI_DEGREE,
            Self::Theta => THETA_DEGREE,
            Self::Parity => PARITY_DEGREE,
        }
    }

    const fn terminals(self) -> usize {
        match self {
            Self::Chi | Self::Theta => 3,
            Self::Parity => 5,
        }
    }
}

fn gate_pair_polynomial(kind: GateKind, arrays: &[Vec<SecureField>], i: usize) -> Poly {
    let half = arrays[0].len() / 2;
    let linear = |array: usize| Poly::linear(arrays[array][i], arrays[array][i + half]);
    let coefficient = linear(0);
    let gate = match kind {
        GateKind::Chi => {
            let b0 = linear(1);
            let b1 = linear(2);
            let b2 = linear(3);
            let q = linear(4);
            let and_not = Poly::constant(SecureField::one()).sub(b1).mul(b2);
            xor_polys(&[xor_polys(&[b0, and_not]), q])
        }
        GateKind::Theta => xor_polys(&[linear(1), linear(2), linear(3)]),
        GateKind::Parity => xor_polys(&[linear(1), linear(2), linear(3), linear(4), linear(5)]),
    };
    coefficient.mul(gate)
}

fn packed_gate_pair_polynomial(
    kind: GateKind,
    arrays: &[Vec<PackedQM31>],
    i: usize,
) -> PackedGatePoly {
    let half = arrays[0].len() / 2;
    let linear = |array: usize| PackedGatePoly::linear(arrays[array][i], arrays[array][i + half]);
    let coefficient = linear(0);
    let gate = match kind {
        GateKind::Chi => {
            let b0 = linear(1);
            let b1 = linear(2);
            let b2 = linear(3);
            let q = linear(4);
            let and_not = PackedGatePoly::constant(SecureField::one()).sub(b1).mul(b2);
            packed_xor_polys(&[packed_xor_polys(&[b0, and_not]), q])
        }
        GateKind::Theta => packed_xor_polys(&[linear(1), linear(2), linear(3)]),
        GateKind::Parity => {
            packed_xor_polys(&[linear(1), linear(2), linear(3), linear(4), linear(5)])
        }
    };
    coefficient.mul(gate)
}

fn packed_first_gate_pair_polynomial(
    kind: GateKind,
    coefficient: &[PackedQM31],
    terminals: &[Vec<PackedM31>],
    i: usize,
) -> PackedGatePoly {
    let half = coefficient.len() / 2;
    let linear =
        |array: usize| PackedBasePoly::linear(terminals[array][i], terminals[array][i + half]);
    let coefficient = PackedGatePoly::linear(coefficient[i], coefficient[i + half]);
    let gate = match kind {
        GateKind::Chi => {
            let b0 = linear(0);
            let b1 = linear(1);
            let b2 = linear(2);
            let q = linear(3);
            let and_not = PackedBasePoly::constant(M31::one()).sub(b1).mul(b2);
            packed_base_xor_polys(&[packed_base_xor_polys(&[b0, and_not]), q])
        }
        GateKind::Theta => packed_base_xor_polys(&[linear(0), linear(1), linear(2)]),
        GateKind::Parity => {
            packed_base_xor_polys(&[linear(0), linear(1), linear(2), linear(3), linear(4)])
        }
    };
    coefficient.mul_base(gate)
}

fn pack_values(values: Vec<SecureField>) -> Vec<PackedQM31> {
    assert_eq!(values.len() % N_LANES, 0);
    values
        .chunks_exact(N_LANES)
        .map(|chunk| PackedQM31::from_array(chunk.try_into().expect("one SIMD pack")))
        .collect()
}

fn pack_arrays(arrays: Vec<Vec<SecureField>>) -> Vec<Vec<PackedQM31>> {
    arrays.into_iter().map(pack_values).collect()
}

#[cfg(test)]
fn pack_base_values(values: Vec<SecureField>) -> Vec<PackedM31> {
    assert_eq!(values.len() % N_LANES, 0);
    values
        .chunks_exact(N_LANES)
        .map(|chunk| {
            PackedM31::from_array(std::array::from_fn(|lane| {
                let [base, b, c, d] = chunk[lane].to_m31_array();
                assert!(b.is_zero() && c.is_zero() && d.is_zero());
                base
            }))
        })
        .collect()
}

#[cfg(test)]
fn pack_gate_arrays(arrays: Vec<Vec<SecureField>>) -> (Vec<PackedQM31>, Vec<Vec<PackedM31>>) {
    let mut arrays = arrays.into_iter();
    let coefficient = pack_values(arrays.next().expect("gate coefficient"));
    let terminals = arrays.map(pack_base_values).collect();
    (coefficient, terminals)
}

fn unpack_values(values: Vec<PackedQM31>) -> Vec<SecureField> {
    values
        .into_iter()
        .flat_map(|value| value.to_array())
        .collect()
}

#[cfg(test)]
fn unpack_base_values(values: Vec<PackedM31>) -> Vec<SecureField> {
    values
        .into_iter()
        .flat_map(|value| PackedQM31::from(value).to_array())
        .collect()
}

fn unpack_arrays(arrays: Vec<Vec<PackedQM31>>) -> Vec<Vec<SecureField>> {
    arrays.into_iter().map(unpack_values).collect()
}

fn fold_packed_values(values: &mut Vec<PackedQM31>, coordinate: PackedQM31) {
    let half = values.len() / 2;
    {
        let (left, right) = values.split_at_mut(half);
        if half >= 512 {
            left.par_iter_mut()
                .zip(right.par_iter())
                .for_each(|(left, &right)| *left += coordinate * (right - *left));
        } else {
            left.iter_mut()
                .zip(right.iter())
                .for_each(|(left, &right)| *left += coordinate * (right - *left));
        }
    }
    values.truncate(half);
}

fn fold_base_values(values: Vec<PackedM31>, coordinate: PackedQM31) -> Vec<PackedQM31> {
    let half = values.len() / 2;
    let (left, right) = values.split_at(half);
    (0..half)
        .into_par_iter()
        .map(|i| PackedQM31::from(left[i]) + coordinate * (right[i] - left[i]))
        .collect()
}

fn fold_packed_arrays(arrays: &mut [Vec<PackedQM31>], coordinate: SecureField) {
    let coordinate = PackedQM31::broadcast(coordinate);
    let fold = |values: &mut Vec<PackedQM31>| {
        let half = values.len() / 2;
        let (left, right) = values.split_at_mut(half);
        for i in 0..half {
            left[i] += coordinate * (right[i] - left[i]);
        }
        values.truncate(half);
    };
    if arrays[0].len() / 2 >= 512 {
        arrays.par_iter_mut().for_each(fold);
    } else {
        arrays.iter_mut().for_each(fold);
    }
}

fn horizontal_sum(value: PackedQM31) -> SecureField {
    value.to_array().into_iter().sum()
}

fn fold_arrays(arrays: &mut [Vec<SecureField>], coordinate: SecureField) {
    for values in arrays {
        let half = values.len() / 2;
        let (left, right) = values.split_at_mut(half);
        for i in 0..half {
            left[i] += coordinate * (right[i] - left[i]);
        }
        values.truncate(half);
    }
}

fn polynomial_eval(coefficients: &[SecureField], point: SecureField) -> SecureField {
    coefficients
        .iter()
        .rev()
        .fold(SecureField::zero(), |value, &coefficient| {
            value * point + coefficient
        })
}

fn prove_gate_sumcheck(
    kind: GateKind,
    mut claim: SecureField,
    mut coefficient: Vec<PackedQM31>,
    base_terminals: Vec<Vec<PackedM31>>,
    n_variables: usize,
    writer: &mut ProofWriter,
    channel: &mut impl Channel,
) -> (Vec<SecureField>, SecureField, Vec<SecureField>) {
    assert!(n_variables > LOG_N_LANES as usize);
    assert_eq!(
        coefficient.len(),
        1usize << (n_variables - LOG_N_LANES as usize)
    );
    assert_eq!(
        base_terminals.len(),
        kind.terminals() + usize::from(matches!(kind, GateKind::Chi))
    );
    assert!(base_terminals
        .iter()
        .all(|terminal| terminal.len() == coefficient.len()));
    let mut point = Vec::with_capacity(n_variables);
    let packed_rounds = n_variables - LOG_N_LANES as usize;

    let half = coefficient.len() / 2;
    let polynomial = (0..half)
        .into_par_iter()
        .map(|i| {
            packed_first_gate_pair_polynomial(kind, &coefficient, &base_terminals, i).coefficients
        })
        .reduce(
            || [PackedQM31::zero(); MAX_GATE_SUMCHECK_COEFFICIENTS],
            |mut left, right| {
                for i in 0..=kind.degree() {
                    left[i] += right[i];
                }
                left
            },
        );
    let coefficients = polynomial[..=kind.degree()]
        .iter()
        .copied()
        .map(horizontal_sum)
        .collect::<Vec<_>>();
    assert_eq!(
        coefficients[0] + polynomial_eval(&coefficients, SecureField::one()),
        claim,
        "layered gate sumcheck claim mismatch"
    );
    writer.write_many(&coefficients);
    channel.mix_felts(&coefficients);
    let coordinate = draw_nonbinary(channel);
    claim = polynomial_eval(&coefficients, coordinate);
    point.push(coordinate);
    let packed_coordinate = PackedQM31::broadcast(coordinate);
    fold_packed_values(&mut coefficient, packed_coordinate);
    let mut arrays = Vec::with_capacity(1 + base_terminals.len());
    arrays.push(coefficient);
    arrays.extend(
        base_terminals
            .into_iter()
            .map(|terminal| fold_base_values(terminal, packed_coordinate)),
    );

    for _ in 1..packed_rounds {
        let half = arrays[0].len() / 2;
        let polynomial = (0..half)
            .into_par_iter()
            .map(|i| packed_gate_pair_polynomial(kind, &arrays, i).coefficients)
            .reduce(
                || [PackedQM31::zero(); MAX_GATE_SUMCHECK_COEFFICIENTS],
                |mut left, right| {
                    for i in 0..=kind.degree() {
                        left[i] += right[i];
                    }
                    left
                },
            );
        let coefficients = polynomial[..=kind.degree()]
            .iter()
            .copied()
            .map(horizontal_sum)
            .collect::<Vec<_>>();
        assert_eq!(
            coefficients[0] + polynomial_eval(&coefficients, SecureField::one()),
            claim,
            "layered gate sumcheck claim mismatch"
        );
        writer.write_many(&coefficients);
        channel.mix_felts(&coefficients);
        let coordinate = draw_nonbinary(channel);
        claim = polynomial_eval(&coefficients, coordinate);
        point.push(coordinate);
        fold_packed_arrays(&mut arrays, coordinate);
    }

    let mut arrays = unpack_arrays(arrays);
    for _ in packed_rounds..n_variables {
        let half = arrays[0].len() / 2;
        let polynomial = (0..half)
            .into_par_iter()
            .map(|i| gate_pair_polynomial(kind, &arrays, i).coefficients)
            .reduce(
                || [SecureField::zero(); MAX_SUMCHECK_COEFFICIENTS],
                |mut left, right| {
                    for i in 0..=kind.degree() {
                        left[i] += right[i];
                    }
                    left
                },
            );
        let coefficients = &polynomial[..=kind.degree()];
        assert_eq!(
            coefficients[0] + polynomial_eval(coefficients, SecureField::one()),
            claim,
            "layered gate sumcheck claim mismatch"
        );
        writer.write_many(coefficients);
        channel.mix_felts(coefficients);
        let coordinate = draw_nonbinary(channel);
        claim = polynomial_eval(coefficients, coordinate);
        point.push(coordinate);
        fold_arrays(&mut arrays, coordinate);
    }
    let terminals = arrays.into_iter().skip(1).map(|values| values[0]).collect();
    (point, claim, terminals)
}

fn verify_sumcheck(
    mut claim: SecureField,
    n_variables: usize,
    degree: usize,
    reader: &mut ProofReader<'_>,
    channel: &mut impl Channel,
) -> Result<(Vec<SecureField>, SecureField), VerificationError> {
    let mut point = Vec::with_capacity(n_variables);
    for _ in 0..n_variables {
        let coefficients = reader.read_many(degree + 1)?;
        if coefficients[0] + polynomial_eval(&coefficients, SecureField::one()) != claim {
            return Err(invalid("sumcheck round does not match its claim"));
        }
        channel.mix_felts(&coefficients);
        let coordinate = draw_nonbinary(channel);
        claim = polynomial_eval(&coefficients, coordinate);
        point.push(coordinate);
    }
    Ok((point, claim))
}

fn read_table(input: &BitMatrix, map: WireMap, p_log: usize, active: &[bool]) -> Vec<PackedM31> {
    let from_log = map.source_domain().local_log();
    let to_log = map.target_domain().local_log();
    assert_eq!(input.log_size, p_log + to_log);
    (0..1usize << (p_log + from_log - LOG_N_LANES as usize))
        .into_par_iter()
        .map(|pack| {
            let first = pack * N_LANES;
            let values = std::array::from_fn(|lane| {
                let index = first + lane;
                let p = index >> from_log;
                let value = active[p]
                    && map
                        .map_local(index & ((1 << from_log) - 1))
                        .is_some_and(|local| input.get((p << to_log) | local));
                M31::from(u32::from(value))
            });
            PackedM31::from_array(values)
        })
        .collect()
}

fn chi_q_table(p_log: usize, active: &[bool], round: usize) -> Vec<PackedM31> {
    let packed_local_log = A_LOCAL_LOG - LOG_N_LANES as usize;
    (0..1usize << (p_log + packed_local_log))
        .into_par_iter()
        .map(|pack| {
            let p = pack >> packed_local_log;
            let local_pack = pack & ((1 << packed_local_log) - 1);
            if !active[p] || local_pack >= 64 / N_LANES {
                return PackedM31::zero();
            }
            let first_z = local_pack * N_LANES;
            PackedM31::from_array(std::array::from_fn(|lane| {
                M31::from(((IOTA_RC[round] >> (first_z + lane)) & 1) as u32)
            }))
        })
        .collect()
}

fn chi_q_eval(point: &[SecureField], p_log: usize, active: &[bool], round: usize) -> SecureField {
    assert_eq!(point.len(), p_log + A_LOCAL_LOG);
    let p_selector: SecureField = eq_weights(&point[..p_log])
        .into_iter()
        .zip(active)
        .filter_map(|(weight, &is_active)| is_active.then_some(weight))
        .sum();
    let lane_zero = point[p_log..p_log + 5]
        .iter()
        .fold(SecureField::one(), |value, &coordinate| {
            value * (SecureField::one() - coordinate)
        });
    let z_weights = eq_weights(&point[p_log + 5..]);
    let rc: SecureField = z_weights
        .into_iter()
        .enumerate()
        .filter_map(|(z, weight)| ((IOTA_RC[round] >> z) & 1 != 0).then_some(weight))
        .sum();
    p_selector * lane_zero * rc
}

fn gate_maps(kind: GateKind) -> Vec<WireMap> {
    match kind {
        GateKind::Chi => (0..3).map(WireMap::Chi).collect(),
        GateKind::Theta => vec![WireMap::ThetaA, WireMap::ThetaCLeft, WireMap::ThetaCRight],
        GateKind::Parity => (0..5).map(WireMap::Parity).collect(),
    }
}

fn gate_value(kind: GateKind, terminals: &[SecureField], q: SecureField) -> SecureField {
    match kind {
        GateKind::Chi => {
            let and_not = (SecureField::one() - terminals[1]) * terminals[2];
            xor_values(&[xor_values(&[terminals[0], and_not]), q])
        }
        GateKind::Theta | GateKind::Parity => xor_values(terminals),
    }
}

fn prove_gate(
    kind: GateKind,
    round: usize,
    combined: &CombinedKernel,
    witness: &LayeredWitness,
    writer: &mut ProofWriter,
    channel: &mut impl Channel,
) -> Vec<Claim> {
    let maps = gate_maps(kind);
    let coefficient = combined.table(witness.p_log, &witness.active);
    let mut terminals = Vec::with_capacity(maps.len() + usize::from(matches!(kind, GateKind::Chi)));
    for &map in &maps {
        let input = match map.target_domain() {
            LayerDomain::A => &witness.a[round],
            LayerDomain::B => &witness.b[round],
            LayerDomain::C => &witness.c[round],
        };
        terminals.push(read_table(input, map, witness.p_log, &witness.active));
    }
    if matches!(kind, GateKind::Chi) {
        terminals.push(chi_q_table(witness.p_log, &witness.active, round));
    }

    let n_variables = witness.p_log + kind_domain(kind).local_log();
    let (point, terminal_claim, all_terminals) = prove_gate_sumcheck(
        kind,
        combined.value,
        coefficient,
        terminals,
        n_variables,
        writer,
        channel,
    );
    let terminals = &all_terminals[..kind.terminals()];
    let q = if matches!(kind, GateKind::Chi) {
        all_terminals[kind.terminals()]
    } else {
        SecureField::zero()
    };
    let expected =
        combined.evaluate(&point, witness.p_log, &witness.active) * gate_value(kind, terminals, q);
    assert_eq!(terminal_claim, expected, "layered gate terminal mismatch");
    writer.write_many(terminals);
    channel.mix_felts(terminals);
    maps.into_iter()
        .zip(terminals.iter().copied())
        .map(|(map, value)| Claim {
            value,
            kernel: Kernel::Read {
                point: point.clone(),
                map,
            },
        })
        .collect()
}

fn verify_gate(
    kind: GateKind,
    round: usize,
    combined: &CombinedKernel,
    p_log: usize,
    active: &[bool],
    reader: &mut ProofReader<'_>,
    channel: &mut impl Channel,
) -> Result<Vec<Claim>, VerificationError> {
    let maps = gate_maps(kind);
    let n_variables = p_log + kind_domain(kind).local_log();
    let (point, terminal_claim) =
        verify_sumcheck(combined.value, n_variables, kind.degree(), reader, channel)?;
    let terminals = reader.read_many(kind.terminals())?;
    channel.mix_felts(&terminals);
    let q = if matches!(kind, GateKind::Chi) {
        chi_q_eval(&point, p_log, active, round)
    } else {
        SecureField::zero()
    };
    let expected = combined.evaluate(&point, p_log, active) * gate_value(kind, &terminals, q);
    if terminal_claim != expected {
        return Err(invalid("gate terminal equation failed"));
    }
    Ok(maps
        .into_iter()
        .zip(terminals)
        .map(|(map, value)| Claim {
            value,
            kernel: Kernel::Read {
                point: point.clone(),
                map,
            },
        })
        .collect())
}

const fn kind_domain(kind: GateKind) -> LayerDomain {
    match kind {
        GateKind::Chi => LayerDomain::A,
        GateKind::Theta => LayerDomain::B,
        GateKind::Parity => LayerDomain::C,
    }
}

fn polynomial_mul_m31(left: &[M31], right: &[M31]) -> Vec<M31> {
    let mut output = vec![M31::zero(); left.len() + right.len() - 1];
    for (i, &a) in left.iter().enumerate() {
        for (j, &b) in right.iter().enumerate() {
            output[i + j] += a * b;
        }
    }
    output
}

fn nibble_polynomials() -> ([[M31; 16]; 4], [M31; 17]) {
    let mut bit_polynomials = [[M31::zero(); 16]; 4];
    for (index, &value) in VALID_NIBBLES.iter().enumerate() {
        let value = M31::from(value);
        let mut basis = vec![M31::one()];
        let mut denominator = M31::one();
        for (other_index, &other) in VALID_NIBBLES.iter().enumerate() {
            if other_index == index {
                continue;
            }
            let other = M31::from(other);
            basis = polynomial_mul_m31(&basis, &[-other, M31::one()]);
            denominator *= value - other;
        }
        let scale = denominator.inverse();
        for bit in 0..4 {
            if (VALID_NIBBLES[index] >> (2 * bit)) & 1 == 0 {
                continue;
            }
            for (coefficient, &basis_coefficient) in basis.iter().enumerate() {
                bit_polynomials[bit][coefficient] += scale * basis_coefficient;
            }
        }
    }

    let mut validity = vec![M31::one()];
    for value in VALID_NIBBLES {
        validity = polynomial_mul_m31(&validity, &[-M31::from(value), M31::one()]);
    }
    (
        bit_polynomials,
        validity.try_into().expect("degree-16 polynomial"),
    )
}

fn eval_m31_polynomial(coefficients: &[M31], point: SecureField) -> SecureField {
    coefficients
        .iter()
        .rev()
        .fold(SecureField::zero(), |value, &coefficient| {
            value * point + SecureField::from(coefficient)
        })
}

fn polynomial_powers(linear: Poly) -> [Poly; 17] {
    let mut powers = [Poly::zero(); 17];
    powers[0] = Poly::constant(SecureField::one());
    for degree in 1..powers.len() {
        powers[degree] = powers[degree - 1].mul(linear);
    }
    powers
}

fn compose_from_powers(coefficients: &[M31], powers: &[Poly; 17]) -> Poly {
    coefficients
        .iter()
        .enumerate()
        .fold(Poly::zero(), |sum, (degree, &coefficient)| {
            sum.add(powers[degree].scale(SecureField::from(coefficient)))
        })
}

fn extraction_pair_polynomial(
    arrays: &[Vec<SecureField>],
    i: usize,
    bit_polynomials: &[[M31; 16]; 4],
    validity: &[M31; 17],
    lambda: SecureField,
) -> Poly {
    let half = arrays[0].len() / 2;
    let linear = |array: usize| Poly::linear(arrays[array][i], arrays[array][i + half]);
    let n = linear(0);
    let powers = polynomial_powers(n);
    let mut output = Poly::zero();
    for bit in 0..4 {
        output =
            output.add(compose_from_powers(&bit_polynomials[bit], &powers).mul(linear(1 + bit)));
    }
    output.add(
        compose_from_powers(validity, &powers)
            .mul(linear(5))
            .scale(lambda),
    )
}

fn packed_extraction_pair_polynomial(
    arrays: &[Vec<PackedQM31>],
    i: usize,
    bit_polynomials: &[[M31; 16]; 4],
    validity: &[M31; 17],
    lambda: SecureField,
) -> PackedExtractionPoly {
    let half = arrays[0].len() / 2;
    let linear =
        |array: usize| PackedExtractionPoly::linear(arrays[array][i], arrays[array][i + half]);
    let n = linear(0);
    let lambda = PackedQM31::broadcast(lambda);
    let validity_left = arrays[5][i] * lambda;
    let validity_right = arrays[5][i + half] * lambda;
    let mut output =
        PackedExtractionPoly::linear(validity_left * validity[16], validity_right * validity[16]);
    for degree in (0..16).rev() {
        let mut left = validity_left * validity[degree];
        let mut right = validity_right * validity[degree];
        for bit in 0..4 {
            left += arrays[1 + bit][i] * bit_polynomials[bit][degree];
            right += arrays[1 + bit][i + half] * bit_polynomials[bit][degree];
        }
        output = output.mul(n).add(PackedExtractionPoly::linear(left, right));
    }
    output
}

fn prove_extraction_sumcheck(
    mut claim: SecureField,
    arrays: Vec<Vec<SecureField>>,
    n_variables: usize,
    lambda: SecureField,
    writer: &mut ProofWriter,
    channel: &mut impl Channel,
) -> (Vec<SecureField>, SecureField, Vec<SecureField>) {
    let (bit_polynomials, validity) = nibble_polynomials();
    let mut point = Vec::with_capacity(n_variables);
    let packed_rounds = n_variables.saturating_sub(LOG_N_LANES as usize);
    let mut scalar = Some(arrays);
    let mut packed = if packed_rounds == 0 {
        None
    } else {
        Some(pack_arrays(
            scalar.take().expect("scalar extraction arrays"),
        ))
    };
    for _ in 0..packed_rounds {
        let arrays = packed.as_mut().expect("packed extraction arrays");
        let half = arrays[0].len() / 2;
        let polynomial = (0..half)
            .into_par_iter()
            .map(|i| {
                packed_extraction_pair_polynomial(arrays, i, &bit_polynomials, &validity, lambda)
                    .coefficients
            })
            .reduce(
                || [PackedQM31::zero(); MAX_SUMCHECK_COEFFICIENTS],
                |mut left, right| {
                    for i in 0..=EXTRACTION_DEGREE {
                        left[i] += right[i];
                    }
                    left
                },
            );
        let coefficients = polynomial[..=EXTRACTION_DEGREE]
            .iter()
            .copied()
            .map(horizontal_sum)
            .collect::<Vec<_>>();
        assert_eq!(
            coefficients[0] + polynomial_eval(&coefficients, SecureField::one()),
            claim,
            "extraction sumcheck claim mismatch"
        );
        writer.write_many(&coefficients);
        channel.mix_felts(&coefficients);
        let coordinate = draw_nonbinary(channel);
        claim = polynomial_eval(&coefficients, coordinate);
        point.push(coordinate);
        fold_packed_arrays(arrays, coordinate);
    }

    let mut arrays = match packed {
        Some(arrays) => unpack_arrays(arrays),
        None => scalar.expect("scalar extraction arrays"),
    };
    for _ in packed_rounds..n_variables {
        let half = arrays[0].len() / 2;
        let polynomial = (0..half)
            .into_par_iter()
            .map(|i| {
                extraction_pair_polynomial(&arrays, i, &bit_polynomials, &validity, lambda)
                    .coefficients
            })
            .reduce(
                || [SecureField::zero(); MAX_SUMCHECK_COEFFICIENTS],
                |mut left, right| {
                    for i in 0..=EXTRACTION_DEGREE {
                        left[i] += right[i];
                    }
                    left
                },
            );
        let coefficients = &polynomial[..=EXTRACTION_DEGREE];
        assert_eq!(
            coefficients[0] + polynomial_eval(coefficients, SecureField::one()),
            claim,
            "extraction sumcheck claim mismatch"
        );
        writer.write_many(coefficients);
        channel.mix_felts(coefficients);
        let coordinate = draw_nonbinary(channel);
        claim = polynomial_eval(coefficients, coordinate);
        point.push(coordinate);
        fold_arrays(&mut arrays, coordinate);
    }
    let terminals = arrays.into_iter().map(|values| values[0]).collect();
    (point, claim, terminals)
}

fn restricted_tables(
    combined: &CombinedKernel,
    p_log: usize,
    active: &[bool],
) -> [Vec<SecureField>; 4] {
    assert_eq!(
        combined.terms[0].1.target_domain(),
        LayerDomain::A,
        "restricted tables require layer A"
    );
    let size = 1usize << (p_log + N_LOCAL_LOG);
    let local_size = 1usize << N_LOCAL_LOG;
    let factors = combined
        .grouped_factors(p_log, active)
        .into_iter()
        .map(|(p_weights, a_weights)| {
            let mut local: [Vec<SecureField>; 4] =
                std::array::from_fn(|_| vec![SecureField::zero(); local_size]);
            for (a_local, value) in a_weights.into_iter().enumerate() {
                let (_, nibble, bit) = a_to_nibble(a_local);
                local[bit][nibble] += value;
            }
            (p_weights, local)
        })
        .collect::<Vec<_>>();
    let mut output: [Vec<SecureField>; 4] =
        std::array::from_fn(|_| vec![SecureField::zero(); size]);
    output.par_iter_mut().enumerate().for_each(|(bit, table)| {
        table
            .par_chunks_mut(local_size)
            .enumerate()
            .for_each(|(p, row)| {
                for (p_weights, local) in &factors {
                    let p_weight = p_weights[p];
                    for (sum, &value) in row.iter_mut().zip(&local[bit]) {
                        *sum += p_weight * value;
                    }
                }
            });
    });
    output
}

fn prove_extraction(
    claims: &[Claim],
    witness: &LayeredWitness,
    writer: &mut ProofWriter,
    channel: &mut impl Channel,
) -> (Vec<SecureField>, SecureField) {
    assert_eq!(claims.len(), 6);
    let tau = draw_point(channel, witness.p_log + N_LOCAL_LOG);
    let combined = combine_claims(claims, channel);
    let lambda = draw_nonbinary(channel);
    let mut arrays = vec![witness.nibble_table()];
    arrays.extend(restricted_tables(&combined, witness.p_log, &witness.active));
    arrays.push(eq_weights(&tau));
    let (point, terminal_claim, terminals) = prove_extraction_sumcheck(
        combined.value,
        arrays,
        witness.p_log + N_LOCAL_LOG,
        lambda,
        writer,
        channel,
    );
    let n = terminals[0];
    let (bit_polynomials, validity) = nibble_polynomials();
    let functional: SecureField = (0..4)
        .map(|bit| {
            combined.evaluate_restricted(bit, &point, witness.p_log, &witness.active)
                * eval_m31_polynomial(&bit_polynomials[bit], n)
        })
        .sum();
    let expected =
        functional + lambda * eq_points(&tau, &point) * eval_m31_polynomial(&validity, n);
    assert_eq!(terminal_claim, expected, "extraction terminal mismatch");
    writer.write(n);
    channel.mix_felts(&[n]);
    (point, n)
}

fn verify_extraction(
    claims: &[Claim],
    p_log: usize,
    active: &[bool],
    reader: &mut ProofReader<'_>,
    channel: &mut impl Channel,
) -> Result<(Vec<SecureField>, SecureField), VerificationError> {
    if claims.len() != 6 {
        return Err(invalid("input layer must have six claims"));
    }
    let tau = draw_point(channel, p_log + N_LOCAL_LOG);
    let combined = combine_claims(claims, channel);
    let lambda = draw_nonbinary(channel);
    let (point, terminal_claim) = verify_sumcheck(
        combined.value,
        p_log + N_LOCAL_LOG,
        EXTRACTION_DEGREE,
        reader,
        channel,
    )?;
    let n = reader.read()?;
    channel.mix_felts(&[n]);
    let (bit_polynomials, validity) = nibble_polynomials();
    let functional: SecureField = (0..4)
        .map(|bit| {
            combined.evaluate_restricted(bit, &point, p_log, active)
                * eval_m31_polynomial(&bit_polynomials[bit], n)
        })
        .sum();
    let expected =
        functional + lambda * eq_points(&tau, &point) * eval_m31_polynomial(&validity, n);
    if terminal_claim != expected {
        return Err(invalid("extraction terminal equation failed"));
    }
    Ok((point, n))
}

fn output_a_point(output_point: &[SecureField], p_log: usize) -> Vec<SecureField> {
    assert_eq!(output_point.len(), p_log + OUTPUT_SLOT_LOG);
    let mut point = Vec::with_capacity(p_log + A_LOCAL_LOG);
    point.extend_from_slice(&output_point[..p_log]);
    point.extend_from_slice(&output_point[p_log..p_log + 5]);
    point.extend_from_slice(&output_point[p_log + 5..]);
    point.push(SecureField::from(256) / SecureField::from(257));
    point.push(SecureField::from(16) / SecureField::from(17));
    point.push(SecureField::from(4) / SecureField::from(5));
    point
}

fn active_schedule(jobs: &JobList) -> Vec<bool> {
    crate::sponge_v::gen_schedule_preprocessed(jobs)[0]
        .values
        .to_cpu()
        .into_iter()
        .map(|value| value == M31::one())
        .collect()
}

/// One committed-source opening and its prover-side MLE values.
pub struct SourceTieBack {
    pub row_point: Vec<SecureField>,
    pub slot_point: Vec<SecureField>,
    pub claim: SecureField,
    pub mle: Mle<SimdBackend, SecureField>,
}

/// One committed-source opening reconstructed by the verifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceOpening {
    pub row_point: Vec<SecureField>,
    pub slot_point: Vec<SecureField>,
    pub claim: SecureField,
}

/// The raw layered proof and its two source MLEs.
pub struct LayeredProof {
    pub payload: Vec<u8>,
    pub output: SourceTieBack,
    pub input: SourceTieBack,
}

/// The two source openings accepted by the layered verifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LayeredVerification {
    pub output: SourceOpening,
    pub input: SourceOpening,
}

#[derive(Clone, Copy)]
enum SourceMleTamper {
    Perturb {
        output: bool,
        index: usize,
    },
    Swap {
        output: bool,
        left: usize,
        right: usize,
    },
}

impl SourceMleTamper {
    fn apply(self, output: bool, point: &[SecureField], values: &mut [SecureField]) {
        assert!(values.len() >= 3);
        let claim = mle_eval(values, point);
        let weights = eq_weights(point);
        assert_eq!(weights.len(), values.len());
        match self {
            Self::Perturb {
                output: selected,
                index,
            } if selected == output => {
                let correction = (index + 1) % values.len();
                values[index] += SecureField::one();
                values[correction] -= weights[index] / weights[correction];
            }
            Self::Swap {
                output: selected,
                left,
                right,
            } if selected == output => {
                let correction = (0..values.len())
                    .find(|&index| index != left && index != right)
                    .expect("one source-MLE correction row");
                let before = weights[left] * values[left] + weights[right] * values[right];
                values.swap(left, right);
                let after = weights[left] * values[left] + weights[right] * values[right];
                assert_ne!(before, after, "source-MLE row swap must change the oracle");
                values[correction] += (before - after) / weights[correction];
            }
            _ => {}
        }
        assert_eq!(mle_eval(values, point), claim);
    }
}

/// Prover state for one canonical layered Keccak proof.
pub struct LayeredKeccakProver {
    jobs: JobList,
    witness: LayeredWitness,
    source_mle_tamper: Option<SourceMleTamper>,
}

impl LayeredKeccakProver {
    pub fn new(jobs: &JobList, run: &SpongeVRun) -> Self {
        Self {
            jobs: jobs.clone(),
            witness: LayeredWitness::new(jobs, run),
            source_mle_tamper: None,
        }
    }

    /// Change one independent witness bit in adversarial tests.
    #[doc(hidden)]
    pub fn flip_state_bit(&mut self, round: usize, p: usize, lane: usize, z: usize) {
        assert!(round <= N_ROUNDS && p < 1usize << self.witness.p_log && lane < 32 && z < 64);
        let index = (p << A_LOCAL_LOG) | (lane << 6) | z;
        let value = !self.witness.a[round].get(index);
        if value {
            self.witness.a[round].words[index / 64] |= 1 << (index % 64);
        } else {
            self.witness.a[round].words[index / 64] &= !(1 << (index % 64));
        }
    }

    /// Perturb a source MLE in an adversarial test. Preserve its claimed evaluation.
    #[doc(hidden)]
    pub fn perturb_source_mle_value(&mut self, output: bool, index: usize) {
        assert!(index < 1usize << self.witness.p_log);
        self.source_mle_tamper = Some(SourceMleTamper::Perturb { output, index });
    }

    /// Swap two source-MLE rows in an adversarial test. Preserve the claimed evaluation.
    #[doc(hidden)]
    pub fn swap_source_mle_rows(&mut self, output: bool, left: usize, right: usize) {
        let n_rows = 1usize << self.witness.p_log;
        assert!(left < n_rows && right < n_rows && left != right);
        self.source_mle_tamper = Some(SourceMleTamper::Swap {
            output,
            left,
            right,
        });
    }

    /// Swap two active physical permutation rows in an adversarial test.
    #[doc(hidden)]
    pub fn swap_permutation_rows(&mut self, left: usize, right: usize) {
        assert!(left != right);
        self.witness.swap_permutation_rows(left, right);
    }

    pub fn prove(self, channel: &mut impl Channel) -> LayeredProof {
        let Self {
            jobs,
            witness,
            source_mle_tamper,
        } = self;
        let p_log = witness.p_log;
        assert_eq!(p_log, jobs.log_size() as usize);
        mix_protocol(&jobs, channel);

        let output_point = draw_point(channel, p_log + OUTPUT_SLOT_LOG);
        let output_slot_point = output_point[p_log..].to_vec();
        let mut output_values = witness.output_fold(&output_slot_point);
        let output_claim = mle_eval(&output_values, &output_point[..p_log]);
        if let Some(tamper) = source_mle_tamper {
            tamper.apply(true, &output_point[..p_log], &mut output_values);
        }
        let mut writer = ProofWriter::new(p_log as u32);
        writer.write(output_claim);
        channel.mix_felts(&[output_claim]);

        let a24_point = output_a_point(&output_point, p_log);
        let mut a_claims = vec![Claim {
            value: output_claim / SecureField::from(SPREAD_BYTE_SUM),
            kernel: Kernel::Eq { point: a24_point },
        }];

        for round in (0..N_ROUNDS).rev() {
            let chi = combine_claims(&a_claims, channel);
            let b_claims = prove_gate(GateKind::Chi, round, &chi, &witness, &mut writer, channel);
            let theta = combine_claims(&b_claims, channel);
            let mut a_and_c = prove_gate(
                GateKind::Theta,
                round,
                &theta,
                &witness,
                &mut writer,
                channel,
            );
            let c_claims = a_and_c.split_off(1);
            let direct_a = a_and_c.pop().expect("one direct A claim");
            let parity = combine_claims(&c_claims, channel);
            let parity_a = prove_gate(
                GateKind::Parity,
                round,
                &parity,
                &witness,
                &mut writer,
                channel,
            );
            a_claims = Vec::with_capacity(6);
            a_claims.push(direct_a);
            a_claims.extend(parity_a);
        }

        let (input_point, input_claim) =
            prove_extraction(&a_claims, &witness, &mut writer, channel);
        let input_row_point = input_point[..p_log].to_vec();
        let input_slot_point = input_point[p_log..].to_vec();
        let mut input_values = witness.input_fold(&input_slot_point);
        debug_assert_eq!(mle_eval(&input_values, &input_row_point), input_claim);
        if let Some(tamper) = source_mle_tamper {
            tamper.apply(false, &input_row_point, &mut input_values);
        }

        LayeredProof {
            payload: writer.finish(p_log as u32),
            output: SourceTieBack {
                row_point: output_point[..p_log].to_vec(),
                slot_point: output_slot_point,
                claim: output_claim,
                mle: Mle::new(SecureColumn::from_iter(output_values)),
            },
            input: SourceTieBack {
                row_point: input_row_point,
                slot_point: input_slot_point,
                claim: input_claim,
                mle: Mle::new(SecureColumn::from_iter(input_values)),
            },
        }
    }
}

pub fn verify_layered_keccak(
    payload: &[u8],
    jobs: &JobList,
    channel: &mut impl Channel,
) -> Result<LayeredVerification, VerificationError> {
    let p_log = jobs.log_size() as usize;
    let active = active_schedule(jobs);
    let mut reader = ProofReader::new(payload, p_log as u32)?;
    mix_protocol(jobs, channel);

    let output_point = draw_point(channel, p_log + OUTPUT_SLOT_LOG);
    let output_claim = reader.read()?;
    channel.mix_felts(&[output_claim]);
    let mut a_claims = vec![Claim {
        value: output_claim / SecureField::from(SPREAD_BYTE_SUM),
        kernel: Kernel::Eq {
            point: output_a_point(&output_point, p_log),
        },
    }];

    for round in (0..N_ROUNDS).rev() {
        let chi = combine_claims(&a_claims, channel);
        let b_claims = verify_gate(
            GateKind::Chi,
            round,
            &chi,
            p_log,
            &active,
            &mut reader,
            channel,
        )?;
        let theta = combine_claims(&b_claims, channel);
        let mut a_and_c = verify_gate(
            GateKind::Theta,
            round,
            &theta,
            p_log,
            &active,
            &mut reader,
            channel,
        )?;
        let c_claims = a_and_c.split_off(1);
        let direct_a = a_and_c.pop().expect("one direct A claim");
        let parity = combine_claims(&c_claims, channel);
        let parity_a = verify_gate(
            GateKind::Parity,
            round,
            &parity,
            p_log,
            &active,
            &mut reader,
            channel,
        )?;
        a_claims = Vec::with_capacity(6);
        a_claims.push(direct_a);
        a_claims.extend(parity_a);
    }

    let (input_point, input_claim) =
        verify_extraction(&a_claims, p_log, &active, &mut reader, channel)?;
    reader.finish()?;
    Ok(LayeredVerification {
        output: SourceOpening {
            row_point: output_point[..p_log].to_vec(),
            slot_point: output_point[p_log..].to_vec(),
            claim: output_claim,
        },
        input: SourceOpening {
            row_point: input_point[..p_log].to_vec(),
            slot_point: input_point[p_log..].to_vec(),
            claim: input_claim,
        },
    })
}

#[derive(Clone, Copy)]
enum SourceKind {
    Output,
    Input,
}

/// Reconstruct one folded source from allocated sponge trace locations.
#[derive(Clone)]
pub struct SpongeSourceOracle {
    locations: Vec<TreeSubspan>,
    jobs: JobList,
    kind: SourceKind,
    slot_weights: Vec<SecureField>,
}

impl SpongeSourceOracle {
    pub fn output(
        locations: Vec<TreeSubspan>,
        jobs: &JobList,
        slot_point: Vec<SecureField>,
    ) -> Self {
        assert_eq!(slot_point.len(), OUTPUT_SLOT_LOG);
        Self {
            locations,
            jobs: jobs.clone(),
            kind: SourceKind::Output,
            slot_weights: eq_weights(&slot_point),
        }
    }

    pub fn input(
        locations: Vec<TreeSubspan>,
        jobs: &JobList,
        slot_point: Vec<SecureField>,
    ) -> Self {
        assert_eq!(slot_point.len(), N_LOCAL_LOG);
        Self {
            locations,
            jobs: jobs.clone(),
            kind: SourceKind::Input,
            slot_weights: eq_weights(&slot_point),
        }
    }
}

impl MleCoeffColumnOracle for SpongeSourceOracle {
    fn evaluate_at_point(
        &self,
        _point: stwo::core::circle::CirclePoint<SecureField>,
        mask: &TreeVec<ColumnVec<Vec<SecureField>>>,
    ) -> SecureField {
        let mut accumulator = PointEvaluationAccumulator::new(SecureField::one());
        let mut eval = PointEvaluator::new(
            mask.sub_tree(&self.locations),
            &mut accumulator,
            SecureField::one(),
            self.jobs.log_size(),
            SecureField::zero(),
        );

        for _ in 0..POST_COL_START {
            let _ = eval.next_trace_mask();
        }
        let post: Vec<SecureField> = (0..N_BYTES_IN_STATE)
            .map(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [-1, 0])[1])
            .collect();
        if matches!(self.kind, SourceKind::Output) {
            return post
                .into_iter()
                .zip(&self.slot_weights)
                .map(|(value, &weight)| value * weight)
                .sum();
        }

        for _ in 0..MAX_RATE {
            let _ = eval.next_trace_mask();
        }
        if self.jobs.has_message_capacity() {
            let _ = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
            let _ = eval.next_trace_mask();
            for _ in 0..N_ABSORB_COLS {
                let _ = eval.next_trace_mask();
            }
        }
        (0..N_INPUT_NIBBLE_COLS)
            .map(|slot| eval.next_trace_mask() * self.slot_weights[slot])
            .sum()
    }
}

#[cfg(test)]
mod tests {
    use stwo::core::channel::Blake2sChannel;

    use super::*;
    use crate::sponge::Shape;

    fn reference_round(state: &mut [u64; 25], round: usize) {
        const RHO: [u32; 24] = [
            1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20,
            44,
        ];
        const PI: [usize; 24] = [
            10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
        ];
        let mut parity = [0u64; 5];
        for x in 0..5 {
            parity[x] = (0..5).fold(0, |value, y| value ^ state[x + 5 * y]);
        }
        for y in 0..5 {
            for x in 0..5 {
                state[x + 5 * y] ^= parity[(x + 4) % 5] ^ parity[(x + 1) % 5].rotate_left(1);
            }
        }
        let mut current = state[1];
        for i in 0..24 {
            let target = PI[i];
            (state[target], current) = (current.rotate_left(RHO[i]), state[target]);
        }
        for y in 0..5 {
            let row: [u64; 5] = std::array::from_fn(|x| state[x + 5 * y]);
            for x in 0..5 {
                state[x + 5 * y] = row[x] ^ ((!row[(x + 1) % 5]) & row[(x + 2) % 5]);
            }
        }
        state[0] ^= IOTA_RC[round];
    }

    fn fixture() -> (JobList, SpongeVRun) {
        let jobs = JobList::new([Shape::new(7, 1, 10, 11)]);
        let run = crate::sponge_v::generate_jobs(&jobs, &[b"TS13-GKR"[..7].to_vec()]);
        (jobs, run)
    }

    fn deterministic_field(index: usize, salt: u32) -> SecureField {
        let seed = (index as u32).wrapping_mul(0x9e37_79b9).wrapping_add(salt);
        SecureField::from_m31_array(std::array::from_fn(|limb| {
            let limb_salt = (limb as u32 + 1).wrapping_mul(0x045d_9f3b);
            M31::from((seed.rotate_left(7 * limb as u32) ^ limb_salt) & 0x3fff_ffff)
        }))
    }

    fn deterministic_arrays(
        n_arrays: usize,
        n_variables: usize,
        salt: u32,
    ) -> Vec<Vec<SecureField>> {
        let size = 1usize << n_variables;
        (0..n_arrays)
            .map(|array| {
                let array_salt = salt.wrapping_add((array as u32 + 1).wrapping_mul(0x0001_0001));
                (0..size)
                    .map(|index| deterministic_field(index, array_salt))
                    .collect()
            })
            .collect()
    }

    fn deterministic_gate_arrays(
        n_arrays: usize,
        n_variables: usize,
        salt: u32,
    ) -> Vec<Vec<SecureField>> {
        let mut arrays = deterministic_arrays(n_arrays, n_variables, salt);
        for values in &mut arrays[1..] {
            for value in values {
                *value = SecureField::from(value.to_m31_array()[0]);
            }
        }
        arrays
    }

    fn scalar_sumcheck_reference(
        mut claim: SecureField,
        mut arrays: Vec<Vec<SecureField>>,
        n_variables: usize,
        degree: usize,
        pair_polynomial: impl Fn(&[Vec<SecureField>], usize) -> [SecureField; MAX_SUMCHECK_COEFFICIENTS],
        writer: &mut ProofWriter,
        channel: &mut impl Channel,
    ) -> (Vec<SecureField>, SecureField, Vec<SecureField>) {
        let mut point = Vec::with_capacity(n_variables);
        for _ in 0..n_variables {
            let half = arrays[0].len() / 2;
            let mut polynomial = [SecureField::zero(); MAX_SUMCHECK_COEFFICIENTS];
            for i in 0..half {
                let pair = pair_polynomial(&arrays, i);
                for coefficient in 0..=degree {
                    polynomial[coefficient] += pair[coefficient];
                }
            }
            let coefficients = &polynomial[..=degree];
            assert_eq!(
                coefficients[0] + polynomial_eval(coefficients, SecureField::one()),
                claim
            );
            writer.write_many(coefficients);
            channel.mix_felts(coefficients);
            let coordinate = draw_nonbinary(channel);
            claim = polynomial_eval(coefficients, coordinate);
            point.push(coordinate);
            fold_arrays(&mut arrays, coordinate);
        }
        let terminals = arrays.into_iter().map(|values| values[0]).collect();
        (point, claim, terminals)
    }

    fn gate_claim(kind: GateKind, arrays: &[Vec<SecureField>]) -> SecureField {
        (0..arrays[0].len())
            .map(|index| {
                let gate = match kind {
                    GateKind::Chi => gate_value(
                        kind,
                        &[arrays[1][index], arrays[2][index], arrays[3][index]],
                        arrays[4][index],
                    ),
                    GateKind::Theta => gate_value(
                        kind,
                        &[arrays[1][index], arrays[2][index], arrays[3][index]],
                        SecureField::zero(),
                    ),
                    GateKind::Parity => gate_value(
                        kind,
                        &[
                            arrays[1][index],
                            arrays[2][index],
                            arrays[3][index],
                            arrays[4][index],
                            arrays[5][index],
                        ],
                        SecureField::zero(),
                    ),
                };
                arrays[0][index] * gate
            })
            .sum()
    }

    fn assert_gate_sumcheck_matches_scalar(kind: GateKind, n_variables: usize, salt: u32) {
        let n_arrays = 1 + kind.terminals() + usize::from(matches!(kind, GateKind::Chi));
        let arrays = deterministic_gate_arrays(n_arrays, n_variables, salt);
        let claim = gate_claim(kind, &arrays);
        let (coefficient, terminals) = pack_gate_arrays(arrays);
        let mut packed_writer = ProofWriter::new(0);
        let mut packed_channel = Blake2sChannel::default();
        let packed = prove_gate_sumcheck(
            kind,
            claim,
            coefficient,
            terminals,
            n_variables,
            &mut packed_writer,
            &mut packed_channel,
        );
        let packed_next = packed_channel.draw_secure_felt();

        let arrays = deterministic_gate_arrays(n_arrays, n_variables, salt);
        assert_eq!(gate_claim(kind, &arrays), claim);
        let mut scalar_writer = ProofWriter::new(0);
        let mut scalar_channel = Blake2sChannel::default();
        let mut scalar = scalar_sumcheck_reference(
            claim,
            arrays,
            n_variables,
            kind.degree(),
            |arrays, i| gate_pair_polynomial(kind, arrays, i).coefficients,
            &mut scalar_writer,
            &mut scalar_channel,
        );
        scalar.2.remove(0);
        let scalar_next = scalar_channel.draw_secure_felt();

        assert_eq!(packed_writer.bytes, scalar_writer.bytes);
        assert_eq!(packed, scalar);
        assert_eq!(packed_next, scalar_next);
    }

    fn extraction_arrays(n_variables: usize, salt: u32) -> Vec<Vec<SecureField>> {
        let mut arrays = deterministic_arrays(6, n_variables, salt);
        arrays[0] = (0..1usize << n_variables)
            .map(|index| SecureField::from(M31::from(VALID_NIBBLES[(7 * index + 3) % 16])))
            .collect();
        arrays
    }

    fn extraction_claim(arrays: &[Vec<SecureField>], lambda: SecureField) -> SecureField {
        let (bit_polynomials, validity) = nibble_polynomials();
        let half = arrays[0].len() / 2;
        (0..half)
            .map(|i| {
                let polynomial =
                    extraction_pair_polynomial(arrays, i, &bit_polynomials, &validity, lambda);
                polynomial.coefficients[0]
                    + polynomial_eval(
                        &polynomial.coefficients[..=EXTRACTION_DEGREE],
                        SecureField::one(),
                    )
            })
            .sum()
    }

    fn assert_extraction_sumcheck_matches_scalar(n_variables: usize, salt: u32) {
        let lambda = deterministic_field(0, salt ^ 0xa5a5_5a5a);
        let arrays = extraction_arrays(n_variables, salt);
        let claim = extraction_claim(&arrays, lambda);
        let mut packed_writer = ProofWriter::new(0);
        let mut packed_channel = Blake2sChannel::default();
        let packed = prove_extraction_sumcheck(
            claim,
            arrays,
            n_variables,
            lambda,
            &mut packed_writer,
            &mut packed_channel,
        );
        let packed_next = packed_channel.draw_secure_felt();

        let arrays = extraction_arrays(n_variables, salt);
        assert_eq!(extraction_claim(&arrays, lambda), claim);
        let (bit_polynomials, validity) = nibble_polynomials();
        let mut scalar_writer = ProofWriter::new(0);
        let mut scalar_channel = Blake2sChannel::default();
        let scalar = scalar_sumcheck_reference(
            claim,
            arrays,
            n_variables,
            EXTRACTION_DEGREE,
            |arrays, i| {
                extraction_pair_polynomial(arrays, i, &bit_polynomials, &validity, lambda)
                    .coefficients
            },
            &mut scalar_writer,
            &mut scalar_channel,
        );
        let scalar_next = scalar_channel.draw_secure_felt();

        assert_eq!(packed_writer.bytes, scalar_writer.bytes);
        assert_eq!(packed, scalar);
        assert_eq!(packed_next, scalar_next);
    }

    fn naive_kernel_table(kernel: &Kernel, p_log: usize, active: &[bool]) -> Vec<SecureField> {
        match kernel {
            Kernel::Eq { point } => eq_weights(point),
            Kernel::Read { point, map } => {
                let from_log = map.source_domain().local_log();
                let to_log = map.target_domain().local_log();
                let mut table = vec![SecureField::zero(); 1usize << (p_log + to_log)];
                for (source, weight) in eq_weights(point).into_iter().enumerate() {
                    let p = source >> from_log;
                    if active[p] {
                        if let Some(target) = map.map_local(source & ((1 << from_log) - 1)) {
                            table[(p << to_log) | target] += weight;
                        }
                    }
                }
                table
            }
        }
    }

    fn naive_combined_table(
        combined: &CombinedKernel,
        p_log: usize,
        active: &[bool],
    ) -> Vec<SecureField> {
        let target = combined.terms[0].1.target_domain();
        let mut output = vec![SecureField::zero(); 1usize << (p_log + target.local_log())];
        for (coefficient, kernel) in &combined.terms {
            for (sum, value) in output.iter_mut().zip(kernel.table(p_log, active)) {
                *sum += *coefficient * value;
            }
        }
        output
    }

    fn naive_restricted_tables(
        combined: &CombinedKernel,
        p_log: usize,
        active: &[bool],
    ) -> [Vec<SecureField>; 4] {
        let size = 1usize << (p_log + N_LOCAL_LOG);
        let mut output: [Vec<SecureField>; 4] =
            std::array::from_fn(|_| vec![SecureField::zero(); size]);
        for (coefficient, kernel) in &combined.terms {
            for (a_index, value) in kernel.table(p_log, active).into_iter().enumerate() {
                let p = a_index >> A_LOCAL_LOG;
                let (_, nibble, bit) = a_to_nibble(a_index & ((1 << A_LOCAL_LOG) - 1));
                output[bit][(p << N_LOCAL_LOG) | nibble] += *coefficient * value;
            }
        }
        output
    }

    fn is_dead_local(domain: LayerDomain, local: usize) -> bool {
        match domain {
            LayerDomain::A | LayerDomain::B => local >> 6 >= 25,
            LayerDomain::C => local >> 6 >= 5,
        }
    }

    #[test]
    fn raw_codec_is_fixed_and_canonical() {
        let mut writer = ProofWriter::new(PRODUCT_P_LOG);
        for i in 0..PRODUCT_PAYLOAD_FIELDS {
            writer.write(SecureField::from(i as u32));
        }
        let payload = writer.finish(PRODUCT_P_LOG);
        assert_eq!(payload.len(), PRODUCT_PAYLOAD_BYTES);
        assert!(is_canonical_payload(&payload, PRODUCT_P_LOG));

        assert!(!is_canonical_payload(
            &payload[..payload.len() - 1],
            PRODUCT_P_LOG
        ));
        let mut trailing = payload.clone();
        trailing.push(0);
        assert!(!is_canonical_payload(&trailing, PRODUCT_P_LOG));
        let mut noncanonical = payload;
        noncanonical[..4].copy_from_slice(&M31_MODULUS.to_le_bytes());
        assert!(!is_canonical_payload(&noncanonical, PRODUCT_P_LOG));
    }

    #[test]
    fn nibble_polynomials_extract_bits_and_reject_invalid_values() {
        let (bits, validity) = nibble_polynomials();
        for value in VALID_NIBBLES {
            let point = SecureField::from(M31::from(value));
            assert_eq!(eval_m31_polynomial(&validity, point), SecureField::zero());
            let extracted: [SecureField; 4] =
                std::array::from_fn(|bit| eval_m31_polynomial(&bits[bit], point));
            for (bit, result) in extracted.iter().enumerate() {
                assert_eq!(*result, SecureField::from((value >> (2 * bit)) & 1));
            }
            assert_eq!(
                point,
                extracted[0]
                    + SecureField::from(4) * extracted[1]
                    + SecureField::from(16) * extracted[2]
                    + SecureField::from(64) * extracted[3]
            );
        }
        assert_ne!(
            eval_m31_polynomial(&validity, SecureField::from(2)),
            SecureField::zero()
        );
    }

    #[test]
    fn fips_maps_and_all_native_rounds_match() {
        let (jobs, run) = fixture();
        let witness = LayeredWitness::new(&jobs, &run);
        let p = witness
            .active
            .iter()
            .position(|&active| active)
            .expect("one active row");
        let mut state = [0u64; 25];
        for lane in 0..25 {
            state[lane] = u64::from_le_bytes(
                witness.inputs[p][8 * lane..8 * lane + 8]
                    .try_into()
                    .unwrap(),
            );
        }

        for round in 0..N_ROUNDS {
            for x in 0..5 {
                for z in 0..64 {
                    let expected = (0..5).fold(false, |bit, y| {
                        bit ^ witness.a[round].get((p << A_LOCAL_LOG) | ((x + 5 * y) << 6) | z)
                    });
                    assert_eq!(
                        witness.c[round].get((p << C_LOCAL_LOG) | (x << 6) | z),
                        expected,
                        "parity round={round} x={x} z={z}"
                    );
                }
            }
            for local in 0..1usize << A_LOCAL_LOG {
                let b_index = (p << A_LOCAL_LOG) | local;
                if local >> 6 >= 25 {
                    assert!(!witness.b[round].get(b_index));
                    continue;
                }
                let reads =
                    [WireMap::ThetaA, WireMap::ThetaCLeft, WireMap::ThetaCRight].map(|map| {
                        let target = map.map_local(local).expect("live lane map");
                        match map.target_domain() {
                            LayerDomain::A => witness.a[round].get((p << A_LOCAL_LOG) | target),
                            LayerDomain::C => witness.c[round].get((p << C_LOCAL_LOG) | target),
                            LayerDomain::B => unreachable!(),
                        }
                    });
                let expected = reads[0] ^ reads[1] ^ reads[2];
                assert_eq!(witness.b[round].get(b_index), expected);
            }

            reference_round(&mut state, round);
            for byte in 0..N_BYTES_IN_STATE {
                let expected = (state[byte / 8] >> (8 * (byte % 8))) as u8;
                for bit in 0..8 {
                    let lane = byte / 8;
                    let z = 8 * (byte % 8) + bit;
                    assert_eq!(
                        witness.a[round + 1].get((p << A_LOCAL_LOG) | (lane << 6) | z),
                        (expected >> bit) & 1 != 0,
                        "round={round} byte={byte} bit={bit}"
                    );
                }
            }
        }
    }

    #[test]
    fn fixed_kernel_matches_naive_tables_and_restrictions() {
        let p_log = 4;
        let active = (0..1usize << p_log).map(|p| p % 3 != 1).collect::<Vec<_>>();
        let maps = [
            gate_maps(GateKind::Chi),
            gate_maps(GateKind::Theta),
            gate_maps(GateKind::Parity),
        ]
        .concat();

        for (case, map) in maps.into_iter().enumerate() {
            let source_log = map.source_domain().local_log();
            let target_log = map.target_domain().local_log();
            let point = (0..p_log + source_log)
                .map(|i| deterministic_field(i, 0x1000 + case as u32))
                .collect::<Vec<_>>();
            let kernel = Kernel::Read { point, map };
            let table = naive_kernel_table(&kernel, p_log, &active);
            assert_eq!(kernel.table(p_log, &active), table, "wire map {case}");

            let target_point = (0..p_log + target_log)
                .map(|i| deterministic_field(i, 0x2000 + case as u32))
                .collect::<Vec<_>>();
            assert_eq!(
                kernel.evaluate(&target_point, p_log, &active),
                mle_eval(&table, &target_point),
                "wire map {case}"
            );

            for source in 0..1usize << source_log {
                if is_dead_local(map.source_domain(), source) {
                    assert_eq!(
                        map.map_local(source),
                        None,
                        "wire map {case}, source {source}"
                    );
                }
            }
            for p in 0..1usize << p_log {
                for local in 0..1usize << target_log {
                    if !active[p] || is_dead_local(map.target_domain(), local) {
                        assert_eq!(
                            table[(p << target_log) | local],
                            SecureField::zero(),
                            "wire map {case}, row {p}, target {local}"
                        );
                    }
                }
            }

            if map.target_domain() == LayerDomain::A {
                let nibble_point = (0..p_log + N_LOCAL_LOG)
                    .map(|i| deterministic_field(i, 0x3000 + case as u32))
                    .collect::<Vec<_>>();
                for bit in 0..4 {
                    let mut restricted = vec![SecureField::zero(); 1 << (p_log + N_LOCAL_LOG)];
                    for (a_index, &value) in table.iter().enumerate() {
                        let p = a_index >> A_LOCAL_LOG;
                        let (_, nibble, selector) = a_to_nibble(a_index & ((1 << A_LOCAL_LOG) - 1));
                        if selector == bit {
                            restricted[(p << N_LOCAL_LOG) | nibble] += value;
                        }
                    }
                    assert_eq!(
                        kernel.evaluate_restricted(bit, &nibble_point, p_log, &active),
                        mle_eval(&restricted, &nibble_point),
                        "wire map {case}, bit {bit}"
                    );
                }
            }
        }
    }

    #[test]
    fn packed_read_tables_match_scalar_index_order() {
        let p_log = 3;
        let active = (0..1usize << p_log).map(|p| p % 3 != 1).collect::<Vec<_>>();
        let maps = [
            gate_maps(GateKind::Chi),
            gate_maps(GateKind::Theta),
            gate_maps(GateKind::Parity),
        ]
        .concat();

        for (case, map) in maps.into_iter().enumerate() {
            let from_log = map.source_domain().local_log();
            let to_log = map.target_domain().local_log();
            let mut input = BitMatrix::zero(p_log + to_log);
            for index in 0..1usize << (p_log + to_log) {
                input.set(index, (7 * index + case) % 11 < 5);
            }
            let expected = (0..1usize << (p_log + from_log))
                .map(|index| {
                    let p = index >> from_log;
                    SecureField::from(u32::from(
                        active[p]
                            && map
                                .map_local(index & ((1 << from_log) - 1))
                                .is_some_and(|local| input.get((p << to_log) | local)),
                    ))
                })
                .collect::<Vec<_>>();
            assert_eq!(
                unpack_base_values(read_table(&input, map, p_log, &active)),
                expected,
                "wire map {case}"
            );
        }
    }

    #[test]
    fn combined_kernel_groups_equal_row_factors_without_changing_the_table() {
        let p_log = 4;
        let active = (0..1usize << p_log).map(|p| p % 3 != 1).collect::<Vec<_>>();
        let common_row = (0..p_log)
            .map(|i| deterministic_field(i, 0x3900))
            .collect::<Vec<_>>();
        let other_row = (0..p_log)
            .map(|i| deterministic_field(i, 0x3a00))
            .collect::<Vec<_>>();
        let point = |row: &[SecureField], local_log: usize, salt: u32| {
            row.iter()
                .copied()
                .chain((0..local_log).map(|i| deterministic_field(i, salt)))
                .collect::<Vec<_>>()
        };
        let combined = CombinedKernel {
            value: SecureField::zero(),
            terms: vec![
                (
                    deterministic_field(0, 0x3b00),
                    Kernel::Read {
                        point: point(&common_row, C_LOCAL_LOG, 0x3c00),
                        map: WireMap::Parity(0),
                    },
                ),
                (
                    deterministic_field(1, 0x3b00),
                    Kernel::Read {
                        point: point(&common_row, C_LOCAL_LOG, 0x3d00),
                        map: WireMap::Parity(1),
                    },
                ),
                (
                    deterministic_field(2, 0x3b00),
                    Kernel::Read {
                        point: point(&common_row, A_LOCAL_LOG, 0x3e00),
                        map: WireMap::ThetaA,
                    },
                ),
                (
                    deterministic_field(3, 0x3b00),
                    Kernel::Read {
                        point: point(&other_row, C_LOCAL_LOG, 0x3f00),
                        map: WireMap::Parity(2),
                    },
                ),
            ],
        };

        assert_eq!(
            unpack_values(combined.table(p_log, &active)),
            naive_combined_table(&combined, p_log, &active)
        );
        assert_eq!(
            restricted_tables(&combined, p_log, &active),
            naive_restricted_tables(&combined, p_log, &active)
        );

        for (case, maps) in [
            [WireMap::Chi(0), WireMap::Chi(1)],
            [WireMap::ThetaCLeft, WireMap::ThetaCRight],
        ]
        .into_iter()
        .enumerate()
        {
            let source_log = maps[0].source_domain().local_log();
            let combined = CombinedKernel {
                value: SecureField::zero(),
                terms: vec![
                    (
                        deterministic_field(3 * case, 0x4100),
                        Kernel::Read {
                            point: point(&common_row, source_log, 0x4200 + case as u32),
                            map: maps[0],
                        },
                    ),
                    (
                        deterministic_field(3 * case + 1, 0x4100),
                        Kernel::Read {
                            point: point(&common_row, source_log, 0x4300 + case as u32),
                            map: maps[1],
                        },
                    ),
                    (
                        deterministic_field(3 * case + 2, 0x4100),
                        Kernel::Read {
                            point: point(&other_row, source_log, 0x4400 + case as u32),
                            map: maps[0],
                        },
                    ),
                ],
            };
            assert_eq!(
                unpack_values(combined.table(p_log, &active)),
                naive_combined_table(&combined, p_log, &active),
                "target domain {case}"
            );
        }
    }

    #[test]
    fn packed_gate_sumchecks_match_scalar_at_boundary_and_product_size() {
        let one_packed_round = LOG_N_LANES as usize + 1;
        for (case, kind) in [GateKind::Chi, GateKind::Theta, GateKind::Parity]
            .into_iter()
            .enumerate()
        {
            assert_gate_sumcheck_matches_scalar(kind, one_packed_round, 0x4000 + case as u32);
            assert_gate_sumcheck_matches_scalar(
                kind,
                PRODUCT_P_LOG as usize + kind_domain(kind).local_log(),
                0x5000 + case as u32,
            );
        }
    }

    #[test]
    fn packed_extraction_sumcheck_matches_scalar_at_boundary_and_product_size() {
        assert_extraction_sumcheck_matches_scalar(LOG_N_LANES as usize + 1, 0x6000);
        assert_extraction_sumcheck_matches_scalar(PRODUCT_P_LOG as usize + N_LOCAL_LOG, 0x7000);
    }

    #[test]
    fn invalid_nibble_proof_rejects_zero_validity_claim() {
        let n_variables = LOG_N_LANES as usize + 1;
        let size = 1usize << n_variables;
        let mut arrays = vec![vec![SecureField::zero(); size]; 6];
        arrays[0][0] = SecureField::from(2);
        arrays[5] = eq_weights(&vec![SecureField::from(2); n_variables]);
        let lambda = SecureField::from(7);
        let actual_claim = extraction_claim(&arrays, lambda);
        assert_ne!(actual_claim, SecureField::zero());

        let mut prover_channel = Blake2sChannel::default();
        let mut writer = ProofWriter::new(0);
        prove_extraction_sumcheck(
            actual_claim,
            arrays,
            n_variables,
            lambda,
            &mut writer,
            &mut prover_channel,
        );

        let mut control_channel = Blake2sChannel::default();
        let mut control_reader = ProofReader {
            bytes: &writer.bytes,
            cursor: 0,
        };
        verify_sumcheck(
            actual_claim,
            n_variables,
            EXTRACTION_DEGREE,
            &mut control_reader,
            &mut control_channel,
        )
        .expect("the nonzero validity claim is the control proof");

        let mut verifier_channel = Blake2sChannel::default();
        let mut reader = ProofReader {
            bytes: &writer.bytes,
            cursor: 0,
        };
        assert!(verify_sumcheck(
            SecureField::zero(),
            n_variables,
            EXTRACTION_DEGREE,
            &mut reader,
            &mut verifier_channel,
        )
        .is_err());
    }

    #[test]
    fn source_folds_match_direct_multilinear_evaluation() {
        let (jobs, run) = fixture();
        let witness = LayeredWitness::new(&jobs, &run);
        let p_log = jobs.log_size() as usize;
        let row_point = (0..p_log)
            .map(|i| SecureField::from((i + 3) as u32))
            .collect::<Vec<_>>();

        let output_slot_point = (0..OUTPUT_SLOT_LOG)
            .map(|i| SecureField::from((i + 17) as u32))
            .collect::<Vec<_>>();
        let output_fold = witness.output_fold(&output_slot_point);
        let mut output_table = vec![SecureField::zero(); 1 << (p_log + OUTPUT_SLOT_LOG)];
        for p in 0..1usize << p_log {
            for byte in 0..N_BYTES_IN_STATE {
                output_table[(p << OUTPUT_SLOT_LOG) | byte] =
                    SecureField::from(M31::from(spread_u32(u32::from(witness.outputs[p][byte]))));
            }
        }
        let mut output_point = row_point.clone();
        output_point.extend_from_slice(&output_slot_point);
        assert_eq!(
            mle_eval(&output_fold, &row_point),
            mle_eval(&output_table, &output_point)
        );

        let input_slot_point = (0..N_LOCAL_LOG)
            .map(|i| SecureField::from((i + 41) as u32))
            .collect::<Vec<_>>();
        let input_fold = witness.input_fold(&input_slot_point);
        let input_table = witness.nibble_table();
        let mut input_point = row_point.clone();
        input_point.extend_from_slice(&input_slot_point);
        assert_eq!(
            mle_eval(&input_fold, &row_point),
            mle_eval(&input_table, &input_point)
        );
    }

    #[test]
    fn source_oracle_offsets_match_the_sponge_layout() {
        let fixed = JobList::new([Shape::new(1, 1, 0, 1)]);
        let capacity = JobList::new([Shape::with_message_capacity(1, 272, 1, 0, 1).unwrap()]);
        let fixed_input_start = POST_COL_START + N_BYTES_IN_STATE + MAX_RATE;

        assert_eq!(POST_COL_START, 3 * N_ABSORB_COLS);
        assert_eq!(POST_COL_START, 408);
        assert_eq!(fixed.input_nibble_col_start(), fixed_input_start);
        assert_eq!(fixed_input_start, 776);
        assert_eq!(
            capacity.input_nibble_col_start(),
            fixed_input_start + 2 + N_ABSORB_COLS
        );
        assert_eq!(capacity.input_nibble_col_start(), 914);
    }

    #[test]
    fn capacity_zero_rows_are_active_and_padding_rows_stay_zero() {
        let shape = Shape::with_message_capacity(0, 300, 1, 12, 13).unwrap();
        let jobs = JobList::new([shape]);
        let run = crate::sponge_v::generate_jobs(&jobs, &[Vec::new()]);
        let witness = LayeredWitness::new(&jobs, &run);
        let row_to_coset = circle_row_to_coset(jobs.log_size());

        for p in 0..1usize << witness.p_log {
            let logical = row_to_coset[p];
            if witness.active[p] {
                assert!(logical < run.rows.len());
                if logical > 0 {
                    assert!(witness.inputs[p].iter().all(|&byte| byte == 0));
                    assert!((0..1usize << A_LOCAL_LOG)
                        .all(|local| !witness.a[0].get((p << A_LOCAL_LOG) | local)));
                    assert!((0..25 * 64)
                        .any(|local| witness.a[N_ROUNDS].get((p << A_LOCAL_LOG) | local)));
                }
            } else {
                for round in 0..=N_ROUNDS {
                    assert!((0..1usize << A_LOCAL_LOG)
                        .all(|local| !witness.a[round].get((p << A_LOCAL_LOG) | local)));
                }
                for round in 0..N_ROUNDS {
                    assert!((0..1usize << A_LOCAL_LOG)
                        .all(|local| !witness.b[round].get((p << A_LOCAL_LOG) | local)));
                    assert!((0..1usize << C_LOCAL_LOG)
                        .all(|local| !witness.c[round].get((p << C_LOCAL_LOG) | local)));
                }
            }
        }
    }

    #[test]
    fn fixed_iota_evaluation_matches_its_boolean_table() {
        let (jobs, run) = fixture();
        let witness = LayeredWitness::new(&jobs, &run);
        let point = (0..witness.p_log + A_LOCAL_LOG)
            .map(|i| SecureField::from((i + 7) as u32))
            .collect::<Vec<_>>();
        for round in 0..N_ROUNDS {
            assert_eq!(
                chi_q_eval(&point, witness.p_log, &witness.active, round),
                mle_eval(
                    &unpack_base_values(chi_q_table(witness.p_log, &witness.active, round)),
                    &point,
                ),
                "Iota round {round}"
            );
        }

        let p_selector: SecureField = eq_weights(&point[..witness.p_log])
            .into_iter()
            .zip(&witness.active)
            .filter_map(|(weight, &active)| active.then_some(weight))
            .sum();
        let lane_zero = point[witness.p_log..witness.p_log + 5]
            .iter()
            .fold(SecureField::one(), |value, &coordinate| {
                value * (SecureField::one() - coordinate)
            });
        let bit_zero_weight = eq_weights(&point[witness.p_log + 5..])[0];
        let alternate_round_zero = chi_q_eval(&point, witness.p_log, &witness.active, 0)
            - p_selector * lane_zero * bit_zero_weight;
        assert_ne!(
            alternate_round_zero,
            chi_q_eval(&point, witness.p_log, &witness.active, 0),
            "removing the fixed round-zero Iota bit must change the verifier equation"
        );
    }

    #[test]
    fn coherent_alternate_iota_chi_proof_fails_fixed_verifier() {
        let p_log = 0;
        let active = vec![true];
        let round = 0;
        let n_variables = p_log + A_LOCAL_LOG;
        let mut combined = CombinedKernel {
            value: SecureField::zero(),
            terms: vec![(
                SecureField::one(),
                Kernel::Eq {
                    point: vec![SecureField::zero(); n_variables],
                },
            )],
        };
        let coefficient = combined.table(p_log, &active);
        let coefficient_values = unpack_values(coefficient.clone());
        let mut alternate_q_values = unpack_base_values(chi_q_table(p_log, &active, round));
        alternate_q_values[0] = SecureField::zero();
        assert!(alternate_q_values.iter().all(SecureField::is_zero));
        let alternate_q = pack_base_values(alternate_q_values.clone());

        let zero = vec![PackedM31::zero(); 1usize << (n_variables - LOG_N_LANES as usize)];
        let terminals = vec![zero.clone(), zero.clone(), zero, alternate_q.clone()];
        combined.value = coefficient_values
            .iter()
            .zip(&alternate_q_values)
            .map(|(&weight, &q)| weight * q)
            .sum();
        assert_eq!(combined.value, SecureField::zero());

        let mut prover_channel = Blake2sChannel::default();
        let mut writer = ProofWriter::new(0);
        let (point, terminal_claim, all_terminals) = prove_gate_sumcheck(
            GateKind::Chi,
            combined.value,
            coefficient,
            terminals,
            n_variables,
            &mut writer,
            &mut prover_channel,
        );
        let terminals = &all_terminals[..GateKind::Chi.terminals()];
        let alternate_q_terminal = all_terminals[GateKind::Chi.terminals()];
        assert_eq!(alternate_q_terminal, mle_eval(&alternate_q_values, &point));
        assert_eq!(
            terminal_claim,
            combined.evaluate(&point, p_log, &active)
                * gate_value(GateKind::Chi, terminals, alternate_q_terminal)
        );
        assert_ne!(
            alternate_q_terminal,
            chi_q_eval(&point, p_log, &active, round)
        );
        writer.write_many(terminals);
        prover_channel.mix_felts(terminals);

        let mut verifier_channel = Blake2sChannel::default();
        let mut reader = ProofReader {
            bytes: &writer.bytes,
            cursor: 0,
        };
        assert!(verify_gate(
            GateKind::Chi,
            round,
            &combined,
            p_log,
            &active,
            &mut reader,
            &mut verifier_channel,
        )
        .is_err());
    }

    #[test]
    fn bounded_sumcheck_detects_polynomial_corruption() {
        let arrays = vec![
            vec![SecureField::one(); 32],
            (0..32).map(|i| SecureField::from(i & 1)).collect(),
            (0..32).map(|i| SecureField::from((i >> 1) & 1)).collect(),
            (0..32).map(|i| SecureField::from((i >> 2) & 1)).collect(),
        ];
        let claim: SecureField = (0..32)
            .map(|i| arrays[0][i] * xor_values(&[arrays[1][i], arrays[2][i], arrays[3][i]]))
            .sum();
        let mut prover_channel = Blake2sChannel::default();
        let mut writer = ProofWriter::new(0);
        let (coefficient, terminals) = pack_gate_arrays(arrays);
        let (prover_point, prover_terminal, _) = prove_gate_sumcheck(
            GateKind::Theta,
            claim,
            coefficient,
            terminals,
            5,
            &mut writer,
            &mut prover_channel,
        );
        let mut verifier_channel = Blake2sChannel::default();
        let mut reader = ProofReader {
            bytes: &writer.bytes,
            cursor: 0,
        };
        let (verifier_point, verifier_terminal) =
            verify_sumcheck(claim, 5, THETA_DEGREE, &mut reader, &mut verifier_channel).unwrap();
        assert_eq!(prover_point, verifier_point);
        assert_eq!(prover_terminal, verifier_terminal);

        let mut corrupted = writer.bytes;
        let raw = u32::from_le_bytes(corrupted[..4].try_into().unwrap());
        corrupted[..4].copy_from_slice(&((raw + 1) % M31_MODULUS).to_le_bytes());
        let mut corrupt_channel = Blake2sChannel::default();
        let mut corrupt_reader = ProofReader {
            bytes: &corrupted,
            cursor: 0,
        };
        assert!(verify_sumcheck(
            claim,
            5,
            THETA_DEGREE,
            &mut corrupt_reader,
            &mut corrupt_channel,
        )
        .is_err());
    }

    #[test]
    fn layered_proof_round_trips() {
        let (jobs, run) = fixture();
        let mut prover_channel = Blake2sChannel::default();
        let proof = LayeredKeccakProver::new(&jobs, &run).prove(&mut prover_channel);
        assert_eq!(proof.payload.len(), payload_byte_count(jobs.log_size()));
        assert!(is_canonical_payload(&proof.payload, jobs.log_size()));

        let mut verifier_channel = Blake2sChannel::default();
        let verified = verify_layered_keccak(&proof.payload, &jobs, &mut verifier_channel).unwrap();
        assert_eq!(verified.output.row_point, proof.output.row_point);
        assert_eq!(verified.output.slot_point, proof.output.slot_point);
        assert_eq!(verified.output.claim, proof.output.claim);
        assert_eq!(verified.input.row_point, proof.input.row_point);
        assert_eq!(verified.input.slot_point, proof.input.slot_point);
        assert_eq!(verified.input.claim, proof.input.claim);
        assert_eq!(
            prover_channel.draw_secure_felt(),
            verifier_channel.draw_secure_felt()
        );
    }
}
