use core::ops::Range;
use std::time::{Duration, Instant};

use crate::ligero::{
    commit_witness_profiled, v4_circle_params, verify_claim_batch, verify_openings,
    verify_split_claim_batch, verify_split_openings, LigeroClaimBatch, LigeroError,
    LigeroLinearClaim, LigeroParams, LigeroProximityClaim,
};
use crate::mac::{bytes_to_bits, gf128_tag, Gf128, GF128_BITS};
use crate::merkle::ColumnOpening;
use crate::sumcheck::{
    circuit_otp_pad_values, proof_otp_pad_values, prove_circuit, prove_evaluated_circuit,
    prove_evaluated_circuit_sorted_sparse, verify_circuit, verify_circuit_sorted_sparse,
    CircuitSumcheckProof, InputClaims, SumcheckError,
};
use crate::{Circuit, CircuitError, CoprocessorChannel, Fp, Layer, Mle, QuadTerm, TranscriptSeed};
use blake2::{Blake2s256, Digest};
use p256::elliptic_curve::ff::PrimeField;
use p256::elliptic_curve::group::Group;
use p256::elliptic_curve::sec1::{FromEncodedPoint, ToEncodedPoint};
use p256::{AffinePoint as P256AffinePoint, EncodedPoint, FieldBytes, ProjectivePoint, Scalar};
use serde::{Deserialize, Serialize};
use stwo_p256_utils::scalar_arithmetic::{
    ScalarArithmeticError, ScalarFieldMulTrace, U256Words, P256_ORDER,
};

pub const LAYOUT_LEN: usize = 2680;
pub const LIMB_BITS: usize = 13;
pub const N_LIMBS: usize = 20;
pub const C1_INPUT_LIMBS_INPUT_LOG_SIZE: usize = 7;
pub const C1_INPUT_LIMBS_OUTPUT_LOG_SIZE: usize = 3;
pub const C2_CANONICALITY_INPUT_LOG_SIZE: usize = 3;
pub const C2_CANONICALITY_OUTPUT_LOG_SIZE: usize = 2;
pub const C3_C5_SCALAR_SETUP_INPUT_LOG_SIZE: usize = 4;
pub const C3_C5_SCALAR_SETUP_OUTPUT_LOG_SIZE: usize = 2;
pub const C6_SCALAR_BITS_INPUT_LOG_SIZE: usize = 10;
pub const C6_SCALAR_BITS_OUTPUT_LOG_SIZE: usize = 10;
pub const C11_FINAL_ADD_INPUT_LOG_SIZE: usize = 4;
pub const C11_FINAL_ADD_OUTPUT_LOG_SIZE: usize = 2;
pub const C12_ON_CURVE_INPUT_LOG_SIZE: usize = 11;
pub const C12_ON_CURVE_OUTPUT_LOG_SIZE: usize = 11;
pub const C13_SLOPE_INVERSES_INPUT_LOG_SIZE: usize = 12;
pub const C13_SLOPE_INVERSES_OUTPUT_LOG_SIZE: usize = 11;
pub const C14_C15_INPUT_LOG_SIZE: usize = 3;
pub const C14_C15_OUTPUT_LOG_SIZE: usize = 3;
pub const MAC_HALF_GROUP_A_INPUT_LOG_SIZE: usize = 9;
pub const MAC_HALF_GROUP_B_INPUT_LOG_SIZE: usize = 11;
pub const MAC_HALF_INPUT_LOG_SIZE: usize = 11;
pub const MAC_HALF_TREE_LOG_SIZE: usize = 11;
pub const MAC_HALF_TREE_BLOCK_SIZE: usize = 1;
const MAC_HALF_PRODUCT_COEFFS: usize = 2 * GF128_BITS - 1;
pub const MAC_HALF_PARITY_Q_BITS: usize = 9;
pub const MAC_HALF_PARITY_MAX_S: usize = 632;
const MAC_HALF_BOOL_CONSTRAINTS: usize = 2 * GF128_BITS + GF128_BITS * MAC_HALF_PARITY_Q_BITS;
const MAC_HALF_TAG_CONSTRAINTS: usize = GF128_BITS;
const MAC_HALF_LOCAL_CONSTRAINTS: usize = MAC_HALF_BOOL_CONSTRAINTS + MAC_HALF_TAG_CONSTRAINTS;
const MAC_BATCH_GROUP_A_INPUT_LOG_SIZE: usize = 13;
const MAC_BATCH_GROUP_B_INPUT_LOG_SIZE: usize = 13;
const MAC_BATCH_INPUT_LOG_SIZE: usize = 14;
const MAC_BATCH_TREE_LOG_SIZE: usize = 14;
const MAC_BATCH_HALF_GROUP_A_INPUT_STRIDE: usize = 1usize << MAC_HALF_GROUP_A_INPUT_LOG_SIZE;
const MAC_BATCH_HALF_GROUP_B_INPUT_STRIDE: usize = GF128_BITS * MAC_HALF_PARITY_Q_BITS;
const MAC_HALF_GROUP_B_INPUT_START: usize = 1usize << MAC_HALF_GROUP_A_INPUT_LOG_SIZE;
const MAC_BATCH_GROUP_B_INPUT_START: usize = 1usize << MAC_BATCH_GROUP_A_INPUT_LOG_SIZE;
const MAC_BATCH_OUTPUT_STRIDE: usize = GF128_BITS + MAC_HALF_LOCAL_CONSTRAINTS;
const MAC_BATCH_TREE_HALF_WIDTH: usize = mac_half_tree_width();
pub const MAC_HALF_CONST_ONE_INDEX: usize = 0;
pub const MAC_HALF_X_BITS_START: usize = 1;
pub const MAC_HALF_AP_BITS_START: usize = MAC_HALF_X_BITS_START + GF128_BITS;
pub const MAC_HALF_Q_BITS_START: usize = MAC_HALF_GROUP_B_INPUT_START;
pub const MAC_HALF_USED_INPUTS: usize = MAC_HALF_Q_BITS_START + GF128_BITS * MAC_HALF_PARITY_Q_BITS;
pub const MAC_HALF_GROUP_A_USED_INPUTS: usize = MAC_HALF_AP_BITS_START + GF128_BITS;
pub const MAC_HALF_GROUP_B_USED_INPUTS: usize = GF128_BITS * MAC_HALF_PARITY_Q_BITS;
pub const MAC_HALF_COMMITTED_PRIVATE_INPUTS: usize =
    (MAC_HALF_GROUP_A_USED_INPUTS - 1) + MAC_HALF_GROUP_B_USED_INPUTS;
pub const MDOC_P4B_MAC_HALF_COUNT: usize = 6;
pub const MDOC_P4B_MAC_COMMITTED_PRIVATE_INPUTS: usize =
    MDOC_P4B_MAC_HALF_COUNT * MAC_HALF_COMMITTED_PRIVATE_INPUTS;
pub const IMPLEMENTED_CIRCUIT_FAMILY_COUNT: usize = 9;

const C6_CONST_ONE_INDEX: u32 = 0;
const C1_CONST_ONE_INDEX: u32 = 0;
const C1_VALUES_START_INDEX: u32 = 1;
const C1_LIMBS_START_INDEX: u32 = 6;
const C2_CONST_ONE_INDEX: u32 = 0;
const C2_R_INDEX: u32 = 1;
const C2_S_INDEX: u32 = 2;
const C2_R_INV_INDEX: u32 = 3;
const C2_S_INV_INDEX: u32 = 4;
const C2_QX_INDEX: u32 = 5;
const C2_QY_INDEX: u32 = 6;
const C2_QX2_INDEX: u32 = 7;
const C3_CONST_ONE_INDEX: u32 = 0;
const C3_Z_INDEX: u32 = 1;
const C3_R_INDEX: u32 = 2;
const C3_S_INDEX: u32 = 3;
const C3_SINV_INDEX: u32 = 4;
const C3_U1_INDEX: u32 = 5;
const C3_U2_INDEX: u32 = 6;
const C3_QINV_INDEX: u32 = 7;
const C3_Q1_INDEX: u32 = 8;
const C3_Q2_INDEX: u32 = 9;
const C6_U1_INDEX: u32 = 1;
const C6_U2_INDEX: u32 = 2;
const C6_BITS_START_INDEX: u32 = 3;
const C6_U1_RECOMPOSE_OUTPUT: u32 = 512;
const C6_U2_RECOMPOSE_OUTPUT: u32 = 513;
const C9_C10_ACCUMULATOR_POINTS_PER_SCALAR: usize = 256;
const C11_CONST_ONE_INDEX: u32 = 0;
const C11_AX_INDEX: u32 = 1;
const C11_AY_INDEX: u32 = 2;
const C11_BX_INDEX: u32 = 3;
const C11_BY_INDEX: u32 = 4;
const C11_RX_INDEX: u32 = 5;
const C11_RY_INDEX: u32 = 6;
const C11_LAMBDA_INDEX: u32 = 7;
const C11_DENOM_INV_INDEX: u32 = 8;
const C12_POINT_COUNT: usize = 515;
const C12_ACCUMULATOR_POINT_COUNT: usize = 512;
const C12_CONST_ONE_INDEX: u32 = 0;
const C12_POINTS_START_INDEX: u32 = 1;
const C12_FINAL_POINT_INDEX: usize = C12_POINT_COUNT - 1;
const C13_SLOPE_INVERSE_COUNT: usize = 1027;
const C13_LADDER_DENOMINATOR_COUNT: usize = 513;
const C13_FINAL_ADD_DENOM_INDEX: usize = 2 * C13_LADDER_DENOMINATOR_COUNT;
const C13_CONST_ONE_INDEX: u32 = 0;
const C13_DENOMS_START_INDEX: u32 = 1;
const C13_INVS_START_INDEX: u32 = C13_DENOMS_START_INDEX + C13_SLOPE_INVERSE_COUNT as u32;
const C14_CONST_ONE_INDEX: u32 = 0;
const C14_RX_INDEX: u32 = 1;
const C14_K_INDEX: u32 = 2;
const C14_R_PRIME_INDEX: u32 = 3;
const C14_SIGNATURE_R_INDEX: u32 = 4;
const C15_FLAGS_START_INDEX: u32 = 5;
const IMPLEMENTED_BUNDLE_LIGERO_LABEL: &[u8] = b"s4-ecdsa-implemented-bundle";
const COPROCESSOR_TRANSCRIPT_DOMAIN: &[u8] = b"eu-id-ec-coproc-v1";

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CircuitTranscriptShape {
    pub label: &'static [u8],
    pub layers: Vec<(usize, usize)>,
}

const P256_B_BE: [u8; 32] = [
    0x5a, 0xc6, 0x35, 0xd8, 0xaa, 0x3a, 0x93, 0xe7, 0xb3, 0xeb, 0xbd, 0x55, 0x76, 0x98, 0x86, 0xbc,
    0x65, 0x1d, 0x06, 0xb0, 0xcc, 0x53, 0xb0, 0xf6, 0x3b, 0xce, 0x3c, 0x3e, 0x27, 0xd2, 0x60, 0x4b,
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LayoutSlot {
    InputLimbs,
    ScalarInverses,
    UScalars,
    ModNQuotients,
    ScalarBits,
    U1GAccumulators,
    U2QAccumulators,
    CorrectedEndpoints,
    U1GDenominatorInverses,
    U2QDenominatorInverses,
    FinalAddDenominatorInverse,
    SlopeInverses,
    FinalPoint,
    FinalReduction,
    InfinityFlags,
    MacHalf,
}

pub fn layout_range(slot: LayoutSlot) -> Range<usize> {
    match slot {
        LayoutSlot::InputLimbs => 0..100,
        LayoutSlot::ScalarInverses => 100..101,
        LayoutSlot::UScalars => 101..103,
        LayoutSlot::ModNQuotients => 103..106,
        LayoutSlot::ScalarBits => 106..618,
        LayoutSlot::U1GAccumulators => 618..1130,
        LayoutSlot::U2QAccumulators => 1130..1642,
        LayoutSlot::CorrectedEndpoints => 1642..1646,
        LayoutSlot::U1GDenominatorInverses => 1646..2159,
        LayoutSlot::U2QDenominatorInverses => 2159..2672,
        LayoutSlot::FinalAddDenominatorInverse => 2672..2673,
        LayoutSlot::SlopeInverses => 1646..2673,
        LayoutSlot::FinalPoint => 2673..2675,
        LayoutSlot::FinalReduction => 2675..2677,
        LayoutSlot::InfinityFlags => 2677..2680,
        LayoutSlot::MacHalf => 0..0,
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct EcdsaInput {
    pub z: [u8; 32],
    pub r: [u8; 32],
    pub s: [u8; 32],
    pub qx: [u8; 32],
    pub qy: [u8; 32],
}

#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
pub struct EcdsaPublicProjection {
    pub z: Option<[u8; 32]>,
    pub r: Option<[u8; 32]>,
    pub s: Option<[u8; 32]>,
    pub qx: Option<[u8; 32]>,
    pub qy: Option<[u8; 32]>,
}

impl EcdsaPublicProjection {
    pub fn full(input: &EcdsaInput) -> Self {
        Self {
            z: Some(input.z),
            r: Some(input.r),
            s: Some(input.s),
            qx: Some(input.qx),
            qy: Some(input.qy),
        }
    }

    pub fn issuer_key_only(qx: [u8; 32], qy: [u8; 32]) -> Self {
        Self {
            qx: Some(qx),
            qy: Some(qy),
            ..Self::default()
        }
    }

    pub fn message_hash_only(z: [u8; 32]) -> Self {
        Self {
            z: Some(z),
            ..Self::default()
        }
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Witness {
    pub values: Vec<Fp>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct ImplementedCircuitProofs {
    pub proofs: Vec<CircuitSumcheckProof>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct ImplementedCircuitBundle {
    pub params: LigeroParams,
    pub root: [u8; 32],
    #[serde(default)]
    pub root_b: Option<[u8; 32]>,
    pub proximity_openings: Vec<ColumnOpening>,
    #[serde(default)]
    pub proximity_openings_b: Vec<ColumnOpening>,
    pub proximity_claim: LigeroProximityClaim,
    #[serde(default)]
    pub proximity_claim_b: Option<LigeroProximityClaim>,
    pub claim_batch: LigeroClaimBatch,
    #[serde(default)]
    pub claim_batch_b: Option<LigeroClaimBatch>,
    pub consistency_claim_values: Vec<Fp>,
    pub mac_tags: Vec<Gf128>,
    pub entries: Vec<ImplementedCircuitBundleEntry>,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct MdocP4bMacKeyShares(pub [Gf128; MDOC_P4B_MAC_HALF_COUNT]);

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct ImplementedCircuitBundleEntry {
    pub proof: CircuitSumcheckProof,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ImplementedCircuitProveProfile {
    pub witness_check: Duration,
    pub circuit_build: Duration,
    pub ligero_row_encode: Duration,
    pub ligero_merkle_build: Duration,
    pub ligero_proximity_claim: Duration,
    pub ligero_openings: Duration,
    pub sumcheck: Duration,
    pub committed_values: usize,
    pub committed_nonzero_values: usize,
    pub max_row_nonzero_values: usize,
    pub ligero_rows: usize,
    pub sumcheck_by_family: [Duration; IMPLEMENTED_CIRCUIT_FAMILY_COUNT],
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ImplementedCircuitVerifyProfile {
    pub setup: Duration,
    pub ligero_proximity: Duration,
    pub systematic_reconstruct: Duration,
    pub sumcheck: Duration,
    pub input_claims: Duration,
    pub consistency: Duration,
    pub sumcheck_by_family: [Duration; IMPLEMENTED_CIRCUIT_FAMILY_COUNT],
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MdocP4bProveProfile {
    pub witness_check: Duration,
    pub circuit_build: Duration,
    pub ligero_row_encode: Duration,
    pub ligero_merkle_build: Duration,
    pub ligero_proximity_claim: Duration,
    pub ligero_openings: Duration,
    pub sumcheck: Duration,
    pub claim_batch: Duration,
    pub row_inventory: MdocP4bRowInventory,
    pub sumcheck_by_instance: Vec<MdocP4bInstanceTiming>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MdocP4bVerifyProfile {
    pub setup: Duration,
    pub ligero_proximity: Duration,
    pub sumcheck: Duration,
    pub input_claims: Duration,
    pub consistency: Duration,
    pub claim_batch: Duration,
    pub sumcheck_by_instance: Vec<MdocP4bInstanceTiming>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MdocP4bInstanceTiming {
    pub role: &'static str,
    pub label: String,
    pub elapsed: Duration,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MdocP4bRowInventory {
    pub row_len: usize,
    pub committed_values: usize,
    pub committed_rows: usize,
    pub encoded_rows_total: usize,
    pub ecdsa_input_values: usize,
    pub ecdsa_input_rows: usize,
    pub mac_input_values: usize,
    pub mac_input_rows: usize,
    pub otp_pad_values: usize,
    pub otp_pad_rows: usize,
    pub blind_rows: usize,
    pub linear_claims: usize,
    pub linear_claim_touched_rows: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WitnessError {
    LayoutMismatch,
    NonCanonicalScalar,
    ZeroScalar,
    NonCanonicalCoordinate,
    InvalidPublicKey,
    ExceptionalTrace,
    ScalarArithmetic,
    ConstraintViolation { slot: LayoutSlot },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ImplementedCircuitProofError {
    Witness(WitnessError),
    Circuit(CircuitError),
    Sumcheck(SumcheckError),
    Ligero(LigeroError),
    SignatureCountMismatch { inputs: usize, witnesses: usize },
    WrongProofCount { expected: usize, actual: usize },
    InputClaimOpeningRejected,
    ProximityOpeningRejected,
    InputBindingRejected,
    CrossFamilyBindingRejected,
}

pub fn generate_witness(input: &EcdsaInput) -> Result<Witness, WitnessError> {
    let _z = parse_scalar(input.z)?;
    let _r = parse_nonzero_scalar(input.r)?;
    let s = parse_nonzero_scalar(input.s)?;
    let public_key = parse_public_key(input.qx, input.qy)?;

    let sinv_scalar = scalar_inverse(s)?;
    let z_words = words_from_be(input.z);
    let r_words = words_from_be(input.r);
    let s_words = words_from_be(input.s);
    let sinv_words = words_from_be(sinv_scalar.to_repr().into());
    let one_words = [1, 0, 0, 0];
    let q_inv = ScalarFieldMulTrace::new_with_expected_result(
        "s4_sinv",
        &s_words,
        &sinv_words,
        &one_words,
        &P256_ORDER,
    )
    .map_err(map_scalar_error)?
    .mul
    .quotient_words();

    let u1_trace = ScalarFieldMulTrace::new("s4_u1", &z_words, &sinv_words, &P256_ORDER)
        .map_err(map_scalar_error)?;
    let u2_trace = ScalarFieldMulTrace::new("s4_u2", &r_words, &sinv_words, &P256_ORDER)
        .map_err(map_scalar_error)?;
    let u1_words = u1_trace.mul.result_words();
    let u2_words = u2_trace.mul.result_words();
    let q1 = u1_trace.mul.quotient_words();
    let q2 = u2_trace.mul.quotient_words();
    let r_point = final_point(&public_key, &u1_words, &u2_words)?;
    let (rx_words, reduction_flag) = reduce_field_x_to_scalar(words_from_be(r_point.0));

    let mut values = vec![Fp::ZERO; LAYOUT_LEN];
    let input_range = layout_range(LayoutSlot::InputLimbs);
    let input_limbs = &mut values[input_range];
    for (input_index, bytes) in [input.z, input.r, input.s, input.qx, input.qy]
        .into_iter()
        .enumerate()
    {
        let limbs = limbs_13(bytes);
        let start = input_index * N_LIMBS;
        for (offset, limb) in limbs.into_iter().enumerate() {
            input_limbs[start + offset] = Fp::from_u64(limb as u64);
        }
    }

    values[layout_range(LayoutSlot::ScalarInverses).start] = fp_from_words(&sinv_words);

    let us_range = layout_range(LayoutSlot::UScalars);
    values[us_range.start] = fp_from_words(&u1_words);
    values[us_range.start + 1] = fp_from_words(&u2_words);

    let q_range = layout_range(LayoutSlot::ModNQuotients);
    values[q_range.start] = fp_from_words(&q_inv);
    values[q_range.start + 1] = fp_from_words(&q1);
    values[q_range.start + 2] = fp_from_words(&q2);

    let bits_range = layout_range(LayoutSlot::ScalarBits);
    write_scalar_bits(
        &mut values[bits_range.start..bits_range.start + 256],
        &u1_words,
    );
    write_scalar_bits(
        &mut values[bits_range.start + 256..bits_range.end],
        &u2_words,
    );

    let u1_raw = write_ladder_accumulators(
        &mut values,
        LayoutSlot::U1GAccumulators,
        ProjectivePoint::GENERATOR,
        &u1_words,
    )?;
    let u2_base = ProjectivePoint::from(public_key);
    let u2_raw =
        write_ladder_accumulators(&mut values, LayoutSlot::U2QAccumulators, u2_base, &u2_words)?;

    let u1_point = u1_raw - double_256(ProjectivePoint::GENERATOR);
    let u2_point = u2_raw - double_256(u2_base);
    let corrected = layout_range(LayoutSlot::CorrectedEndpoints);
    write_projective_point(&mut values[corrected.clone()], 0, u1_point)?;
    write_projective_point(&mut values[corrected], 2, u2_point)?;

    let u1_accumulators = values[layout_range(LayoutSlot::U1GAccumulators)].to_vec();
    let u1_denoms = layout_range(LayoutSlot::U1GDenominatorInverses);
    write_ladder_slope_inverses_from_accumulators(
        &mut values[u1_denoms],
        ProjectivePoint::GENERATOR,
        &u1_accumulators,
    )?;
    let u2_accumulators = values[layout_range(LayoutSlot::U2QAccumulators)].to_vec();
    let u2_denoms = layout_range(LayoutSlot::U2QDenominatorInverses);
    write_ladder_slope_inverses_from_accumulators(
        &mut values[u2_denoms],
        ProjectivePoint::from(public_key),
        &u2_accumulators,
    )?;
    let final_add_inverse = layout_range(LayoutSlot::FinalAddDenominatorInverse);
    write_inverse(
        &mut values[final_add_inverse],
        0,
        final_add_denominator(u1_point, u2_point)?,
    )?;

    let final_point_range = layout_range(LayoutSlot::FinalPoint);
    values[final_point_range.start] = Fp::from_bytes_be(r_point.0).expect("R.x is a field element");
    values[final_point_range.start + 1] =
        Fp::from_bytes_be(r_point.1).expect("R.y is a field element");

    let final_reduction_range = layout_range(LayoutSlot::FinalReduction);
    values[final_reduction_range.start] = Fp::from_u64(reduction_flag as u64);
    values[final_reduction_range.start + 1] = fp_from_words(&rx_words);

    Ok(Witness { values })
}

pub fn verify_witness(input: &EcdsaInput, witness: &Witness) -> Result<(), WitnessError> {
    if witness.values.len() != LAYOUT_LEN {
        return Err(WitnessError::LayoutMismatch);
    }

    let expected = generate_witness(input)?;
    for slot in [
        LayoutSlot::InputLimbs,
        LayoutSlot::ScalarInverses,
        LayoutSlot::UScalars,
        LayoutSlot::ModNQuotients,
        LayoutSlot::ScalarBits,
        LayoutSlot::U1GAccumulators,
        LayoutSlot::U2QAccumulators,
        LayoutSlot::CorrectedEndpoints,
        LayoutSlot::SlopeInverses,
        LayoutSlot::FinalPoint,
        LayoutSlot::FinalReduction,
        LayoutSlot::InfinityFlags,
    ] {
        require_equal_slot(slot, &expected, witness)?;
    }
    let final_reduction = layout_range(LayoutSlot::FinalReduction);
    let signature_r = Fp::from_bytes_be(input.r).ok_or(WitnessError::NonCanonicalScalar)?;
    if witness.values[final_reduction.start + 1] != signature_r {
        return Err(WitnessError::ConstraintViolation {
            slot: LayoutSlot::FinalReduction,
        });
    }
    Ok(())
}

pub fn verify_implemented_circuits(
    input: &EcdsaInput,
    witness: &Witness,
) -> Result<(), WitnessError> {
    for instance in implemented_circuit_instances(input, witness)? {
        require_circuit_satisfied(Ok(instance.circuit), Ok(instance.input), instance.slot)?;
    }
    Ok(())
}

pub fn prove_implemented_circuit_proofs(
    input: &EcdsaInput,
    witness: &Witness,
    commitment_root: [u8; 32],
    transcript_seed: TranscriptSeed,
) -> Result<ImplementedCircuitProofs, ImplementedCircuitProofError> {
    verify_witness(input, witness).map_err(ImplementedCircuitProofError::Witness)?;
    let mut proofs = Vec::new();
    for instance in implemented_circuit_instances(input, witness)
        .map_err(ImplementedCircuitProofError::Witness)?
    {
        let layers = instance
            .circuit
            .evaluate_input(instance.input)
            .map_err(ImplementedCircuitProofError::Circuit)?;
        let mut channel =
            CoprocessorChannel::from_seed(transcript_seed, COPROCESSOR_TRANSCRIPT_DOMAIN);
        channel.mix_bytes(instance.label);
        proofs.push(
            prove_circuit(&instance.circuit, &layers, commitment_root, &mut channel)
                .map_err(ImplementedCircuitProofError::Sumcheck)?,
        );
    }
    Ok(ImplementedCircuitProofs { proofs })
}

pub fn verify_implemented_circuit_proofs(
    proofs: &ImplementedCircuitProofs,
    commitment_root: [u8; 32],
    transcript_seed: TranscriptSeed,
) -> Result<Vec<InputClaims>, ImplementedCircuitProofError> {
    let circuits =
        implemented_circuit_verifier_instances().map_err(ImplementedCircuitProofError::Circuit)?;
    if proofs.proofs.len() != circuits.len() {
        return Err(ImplementedCircuitProofError::WrongProofCount {
            expected: circuits.len(),
            actual: proofs.proofs.len(),
        });
    }

    circuits
        .into_iter()
        .zip(&proofs.proofs)
        .map(|(instance, proof)| {
            let mut channel =
                CoprocessorChannel::from_seed(transcript_seed, COPROCESSOR_TRANSCRIPT_DOMAIN);
            channel.mix_bytes(instance.label);
            verify_circuit(&instance.circuit, proof, commitment_root, &mut channel)
                .map_err(ImplementedCircuitProofError::Sumcheck)
        })
        .collect()
}

pub fn prove_implemented_circuit_bundle(
    input: &EcdsaInput,
    witness: &Witness,
    transcript_seed: TranscriptSeed,
) -> Result<ImplementedCircuitBundle, ImplementedCircuitProofError> {
    prove_implemented_circuit_bundle_profiled(input, witness, transcript_seed)
        .map(|(bundle, _)| bundle)
}

pub fn prove_implemented_circuit_bundle_batch(
    inputs: &[EcdsaInput],
    witnesses: &[Witness],
    transcript_seed: TranscriptSeed,
) -> Result<ImplementedCircuitBundle, ImplementedCircuitProofError> {
    prove_implemented_circuit_bundle_batch_profiled(inputs, witnesses, transcript_seed)
        .map(|(bundle, _)| bundle)
}

pub fn prove_implemented_circuit_bundle_batch_with_projection(
    inputs: &[EcdsaInput],
    projections: &[EcdsaPublicProjection],
    witnesses: &[Witness],
    transcript_seed: TranscriptSeed,
) -> Result<ImplementedCircuitBundle, ImplementedCircuitProofError> {
    prove_implemented_circuit_bundle_batch_with_projection_profiled(
        inputs,
        projections,
        witnesses,
        transcript_seed,
    )
    .map(|(bundle, _)| bundle)
}

pub fn prove_implemented_circuit_bundle_batch_profiled(
    inputs: &[EcdsaInput],
    witnesses: &[Witness],
    transcript_seed: TranscriptSeed,
) -> Result<(ImplementedCircuitBundle, ImplementedCircuitProveProfile), ImplementedCircuitProofError>
{
    let projections: Vec<_> = inputs.iter().map(EcdsaPublicProjection::full).collect();
    prove_implemented_circuit_bundle_batch_with_projection_profiled(
        inputs,
        &projections,
        witnesses,
        transcript_seed,
    )
}

pub fn prove_implemented_circuit_bundle_batch_with_projection_profiled(
    inputs: &[EcdsaInput],
    projections: &[EcdsaPublicProjection],
    witnesses: &[Witness],
    transcript_seed: TranscriptSeed,
) -> Result<(ImplementedCircuitBundle, ImplementedCircuitProveProfile), ImplementedCircuitProofError>
{
    if inputs.len() != witnesses.len() {
        return Err(ImplementedCircuitProofError::SignatureCountMismatch {
            inputs: inputs.len(),
            witnesses: witnesses.len(),
        });
    }
    if inputs.len() != projections.len() {
        return Err(ImplementedCircuitProofError::SignatureCountMismatch {
            inputs: inputs.len(),
            witnesses: projections.len(),
        });
    }

    let mut profile = ImplementedCircuitProveProfile::default();
    let start = Instant::now();
    for (input, witness) in inputs.iter().zip(witnesses) {
        verify_witness(input, witness).map_err(ImplementedCircuitProofError::Witness)?;
    }
    profile.witness_check = start.elapsed();
    let (bundle, inner_profile) =
        prove_implemented_circuit_bundle_batch_unchecked_with_projection_profiled(
            inputs,
            projections,
            witnesses,
            transcript_seed,
        )?;
    profile.circuit_build = inner_profile.circuit_build;
    profile.ligero_row_encode = inner_profile.ligero_row_encode;
    profile.ligero_merkle_build = inner_profile.ligero_merkle_build;
    profile.ligero_proximity_claim = inner_profile.ligero_proximity_claim;
    profile.ligero_openings = inner_profile.ligero_openings;
    profile.sumcheck = inner_profile.sumcheck;
    profile.committed_values = inner_profile.committed_values;
    profile.committed_nonzero_values = inner_profile.committed_nonzero_values;
    profile.max_row_nonzero_values = inner_profile.max_row_nonzero_values;
    profile.ligero_rows = inner_profile.ligero_rows;
    profile.sumcheck_by_family = inner_profile.sumcheck_by_family;
    Ok((bundle, profile))
}

pub fn prove_implemented_circuit_bundle_batch_unchecked_profiled(
    inputs: &[EcdsaInput],
    witnesses: &[Witness],
    transcript_seed: TranscriptSeed,
) -> Result<(ImplementedCircuitBundle, ImplementedCircuitProveProfile), ImplementedCircuitProofError>
{
    let projections: Vec<_> = inputs.iter().map(EcdsaPublicProjection::full).collect();
    prove_implemented_circuit_bundle_batch_unchecked_with_projection_profiled(
        inputs,
        &projections,
        witnesses,
        transcript_seed,
    )
}

pub fn prove_implemented_circuit_bundle_batch_unchecked_with_projection_profiled(
    inputs: &[EcdsaInput],
    projections: &[EcdsaPublicProjection],
    witnesses: &[Witness],
    transcript_seed: TranscriptSeed,
) -> Result<(ImplementedCircuitBundle, ImplementedCircuitProveProfile), ImplementedCircuitProofError>
{
    if inputs.len() != witnesses.len() {
        return Err(ImplementedCircuitProofError::SignatureCountMismatch {
            inputs: inputs.len(),
            witnesses: witnesses.len(),
        });
    }
    if inputs.len() != projections.len() {
        return Err(ImplementedCircuitProofError::SignatureCountMismatch {
            inputs: inputs.len(),
            witnesses: projections.len(),
        });
    }

    let mut profile = ImplementedCircuitProveProfile::default();
    let start = Instant::now();
    let mut all_instances = Vec::with_capacity(inputs.len());
    for (input, witness) in inputs.iter().zip(witnesses) {
        all_instances.push(
            implemented_circuit_instances(input, witness)
                .map_err(ImplementedCircuitProofError::Witness)?,
        );
    }

    let (committed_values, all_layouts) = prover_committed_values(&all_instances);
    profile.circuit_build = start.elapsed();
    profile.committed_values = committed_values.len();
    profile.committed_nonzero_values = committed_values
        .iter()
        .filter(|&&value| value != Fp::ZERO)
        .count();

    let params = implemented_circuit_ligero_params(committed_values.len());
    profile.max_row_nonzero_values = committed_values
        .chunks(params.row_len)
        .map(|chunk| chunk.iter().filter(|&&value| value != Fp::ZERO).count())
        .max()
        .unwrap_or(0);
    let (commitment, commit_profile) = commit_witness_profiled(&committed_values, params)
        .map_err(ImplementedCircuitProofError::Ligero)?;
    profile.ligero_row_encode = commit_profile.row_encode;
    profile.ligero_merkle_build = commit_profile.merkle_build;
    profile.ligero_rows = commit_profile.rows;

    let root = commitment.root();
    let gamma = ligero_proximity_gamma(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        root,
        ligero_row_count(committed_values.len(), params.row_len),
        transcript_seed,
    );
    let start = Instant::now();
    let proximity_claim = commitment
        .proximity_claim(&gamma)
        .map_err(ImplementedCircuitProofError::Ligero)?;
    profile.ligero_proximity_claim = start.elapsed();

    let start = Instant::now();
    let proximity_indices = ligero_proximity_indices(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        root,
        params,
        transcript_seed,
    );
    let proximity_openings = commitment
        .open_columns(&proximity_indices)
        .map_err(ImplementedCircuitProofError::Ligero)?;
    profile.ligero_openings = start.elapsed();

    let mut entries = Vec::new();
    let start = Instant::now();
    for (signature_index, (projection, instances)) in
        projections.iter().zip(&all_instances).enumerate()
    {
        for (family_index, instance) in instances.iter().enumerate() {
            let layers = instance
                .circuit
                .evaluate_input(instance.input.clone())
                .map_err(ImplementedCircuitProofError::Circuit)?;
            let mut channel =
                CoprocessorChannel::from_seed(transcript_seed, COPROCESSOR_TRANSCRIPT_DOMAIN);
            mix_bundle_signature_index(signature_index, &mut channel);
            channel.mix_bytes(instance.label);
            mix_ecdsa_public_projection(projection, &mut channel);
            let family_start = Instant::now();
            let proof = prove_evaluated_circuit(&instance.circuit, &layers, root, &mut channel)
                .map_err(ImplementedCircuitProofError::Sumcheck)?;
            profile.sumcheck_by_family[family_index] += family_start.elapsed();
            entries.push(ImplementedCircuitBundleEntry { proof });
        }
    }
    profile.sumcheck = start.elapsed();
    let (claim_batch, consistency_claim_values) = prover_claim_batch(
        &commitment,
        projections,
        &all_instances,
        &all_layouts,
        &entries,
        transcript_seed,
    )?;

    Ok((
        ImplementedCircuitBundle {
            params,
            root,
            root_b: None,
            proximity_openings,
            proximity_openings_b: Vec::new(),
            proximity_claim,
            proximity_claim_b: None,
            claim_batch,
            claim_batch_b: None,
            consistency_claim_values,
            mac_tags: Vec::new(),
            entries,
        },
        profile,
    ))
}

pub fn prove_implemented_circuit_bundle_profiled(
    input: &EcdsaInput,
    witness: &Witness,
    transcript_seed: TranscriptSeed,
) -> Result<(ImplementedCircuitBundle, ImplementedCircuitProveProfile), ImplementedCircuitProofError>
{
    let mut profile = ImplementedCircuitProveProfile::default();

    let start = Instant::now();
    verify_witness(input, witness).map_err(ImplementedCircuitProofError::Witness)?;
    profile.witness_check = start.elapsed();
    let (bundle, inner_profile) =
        prove_implemented_circuit_bundle_unchecked_profiled(input, witness, transcript_seed)?;
    profile.circuit_build = inner_profile.circuit_build;
    profile.ligero_row_encode = inner_profile.ligero_row_encode;
    profile.ligero_merkle_build = inner_profile.ligero_merkle_build;
    profile.ligero_proximity_claim = inner_profile.ligero_proximity_claim;
    profile.ligero_openings = inner_profile.ligero_openings;
    profile.sumcheck = inner_profile.sumcheck;
    profile.committed_values = inner_profile.committed_values;
    profile.committed_nonzero_values = inner_profile.committed_nonzero_values;
    profile.max_row_nonzero_values = inner_profile.max_row_nonzero_values;
    profile.ligero_rows = inner_profile.ligero_rows;
    profile.sumcheck_by_family = inner_profile.sumcheck_by_family;
    Ok((bundle, profile))
}

/// Proves using a witness that the caller has already checked.
///
/// The normal `prove_implemented_circuit_bundle` path remains checked; this is
/// used by the benchmark after `generate_witness` so witness generation and
/// proof generation are measured as separate BL7 buckets.
pub fn prove_implemented_circuit_bundle_unchecked_profiled(
    input: &EcdsaInput,
    witness: &Witness,
    transcript_seed: TranscriptSeed,
) -> Result<(ImplementedCircuitBundle, ImplementedCircuitProveProfile), ImplementedCircuitProofError>
{
    let mut profile = ImplementedCircuitProveProfile::default();
    let start = Instant::now();
    let instances = implemented_circuit_instances(input, witness)
        .map_err(ImplementedCircuitProofError::Witness)?;
    let all_instances = vec![instances];

    let (committed_values, all_layouts) = prover_committed_values(&all_instances);
    profile.circuit_build = start.elapsed();
    profile.committed_values = committed_values.len();
    profile.committed_nonzero_values = committed_values
        .iter()
        .filter(|&&value| value != Fp::ZERO)
        .count();

    let params = implemented_circuit_ligero_params(committed_values.len());
    profile.max_row_nonzero_values = committed_values
        .chunks(params.row_len)
        .map(|chunk| chunk.iter().filter(|&&value| value != Fp::ZERO).count())
        .max()
        .unwrap_or(0);
    let (commitment, commit_profile) = commit_witness_profiled(&committed_values, params)
        .map_err(ImplementedCircuitProofError::Ligero)?;
    profile.ligero_row_encode = commit_profile.row_encode;
    profile.ligero_merkle_build = commit_profile.merkle_build;
    profile.ligero_rows = commit_profile.rows;

    let root = commitment.root();
    let gamma = ligero_proximity_gamma(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        root,
        ligero_row_count(committed_values.len(), params.row_len),
        transcript_seed,
    );
    let start = Instant::now();
    let proximity_claim = commitment
        .proximity_claim(&gamma)
        .map_err(ImplementedCircuitProofError::Ligero)?;
    profile.ligero_proximity_claim = start.elapsed();

    let start = Instant::now();
    let proximity_indices = ligero_proximity_indices(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        root,
        params,
        transcript_seed,
    );
    let proximity_openings = commitment
        .open_columns(&proximity_indices)
        .map_err(ImplementedCircuitProofError::Ligero)?;
    profile.ligero_openings = start.elapsed();

    let mut entries = Vec::new();
    let start = Instant::now();
    for (index, instance) in all_instances[0].iter().enumerate() {
        let layers = instance
            .circuit
            .evaluate_input(instance.input.clone())
            .map_err(ImplementedCircuitProofError::Circuit)?;
        let mut channel =
            CoprocessorChannel::from_seed(transcript_seed, COPROCESSOR_TRANSCRIPT_DOMAIN);
        mix_bundle_signature_index(0, &mut channel);
        channel.mix_bytes(instance.label);
        let projection = EcdsaPublicProjection::full(input);
        mix_ecdsa_public_projection(&projection, &mut channel);
        let family_start = Instant::now();
        let proof = prove_evaluated_circuit(&instance.circuit, &layers, root, &mut channel)
            .map_err(ImplementedCircuitProofError::Sumcheck)?;
        profile.sumcheck_by_family[index] = family_start.elapsed();
        entries.push(ImplementedCircuitBundleEntry { proof });
    }
    profile.sumcheck = start.elapsed();
    let single_projection = [EcdsaPublicProjection::full(input)];
    let (claim_batch, consistency_claim_values) = prover_claim_batch(
        &commitment,
        &single_projection,
        &all_instances,
        &all_layouts,
        &entries,
        transcript_seed,
    )?;

    Ok((
        ImplementedCircuitBundle {
            params,
            root,
            root_b: None,
            proximity_openings,
            proximity_openings_b: Vec::new(),
            proximity_claim,
            proximity_claim_b: None,
            claim_batch,
            claim_batch_b: None,
            consistency_claim_values,
            mac_tags: Vec::new(),
            entries,
        },
        profile,
    ))
}

pub fn prove_mdoc_p4b_circuit_bundle(
    issuer_input: &EcdsaInput,
    issuer_projection: &EcdsaPublicProjection,
    issuer_witness: &Witness,
    device_input: &EcdsaInput,
    device_projection: &EcdsaPublicProjection,
    device_witness: &Witness,
    revocation: Option<(&EcdsaInput, &EcdsaPublicProjection, &Witness)>,
    mac_key_shares: &MdocP4bMacKeyShares,
    transcript_seed: TranscriptSeed,
) -> Result<ImplementedCircuitBundle, ImplementedCircuitProofError> {
    prove_mdoc_p4b_circuit_bundle_profiled(
        issuer_input,
        issuer_projection,
        issuer_witness,
        device_input,
        device_projection,
        device_witness,
        revocation,
        mac_key_shares,
        transcript_seed,
    )
    .map(|(bundle, _)| bundle)
}

pub fn prove_mdoc_p4b_circuit_bundle_profiled(
    issuer_input: &EcdsaInput,
    issuer_projection: &EcdsaPublicProjection,
    issuer_witness: &Witness,
    device_input: &EcdsaInput,
    device_projection: &EcdsaPublicProjection,
    device_witness: &Witness,
    revocation: Option<(&EcdsaInput, &EcdsaPublicProjection, &Witness)>,
    mac_key_shares: &MdocP4bMacKeyShares,
    transcript_seed: TranscriptSeed,
) -> Result<(ImplementedCircuitBundle, MdocP4bProveProfile), ImplementedCircuitProofError> {
    let mut profile = MdocP4bProveProfile::default();
    let start = Instant::now();
    verify_witness(issuer_input, issuer_witness).map_err(ImplementedCircuitProofError::Witness)?;
    verify_witness(device_input, device_witness).map_err(ImplementedCircuitProofError::Witness)?;
    if let Some((revocation_input, _, revocation_witness)) = revocation {
        verify_witness(revocation_input, revocation_witness)
            .map_err(ImplementedCircuitProofError::Witness)?;
    }
    profile.witness_check = start.elapsed();

    let start = Instant::now();
    let mut instances = Vec::new();
    for instance in implemented_circuit_instances(issuer_input, issuer_witness)
        .map_err(ImplementedCircuitProofError::Witness)?
    {
        instances.push(MdocP4bProverInstance::ecdsa(0, instance));
    }
    for instance in implemented_circuit_instances(device_input, device_witness)
        .map_err(ImplementedCircuitProofError::Witness)?
    {
        instances.push(MdocP4bProverInstance::ecdsa(1, instance));
    }
    if let Some((revocation_input, _, revocation_witness)) = revocation {
        for instance in implemented_circuit_instances(revocation_input, revocation_witness)
            .map_err(ImplementedCircuitProofError::Witness)?
        {
            instances.push(MdocP4bProverInstance::ecdsa(2, instance));
        }
    }
    let mac_values = mdoc_p4b_mac_values(issuer_input, device_input);
    let mac_tags_placeholder = vec![[0u8; 16]; MDOC_P4B_MAC_HALF_COUNT];
    let circuit = build_mac_batch_circuit(&[0u8; 16], &mac_tags_placeholder)
        .map_err(ImplementedCircuitProofError::Circuit)?;
    let input = mac_batch_group_a_input(mac_key_shares, &mac_values)
        .map_err(ImplementedCircuitProofError::Witness)?;
    instances.push(MdocP4bProverInstance {
        label: MDOC_P4B_MAC_BATCH_LABEL,
        role: MdocP4bCircuitRole::MacBatch,
        circuit,
        input,
    });

    let (committed_values, layouts) = mdoc_p4b_committed_values(&instances);
    let params = implemented_circuit_ligero_params(committed_values.len());
    profile.circuit_build = start.elapsed();
    let (commitment, commit_profile) = commit_witness_profiled(&committed_values, params)
        .map_err(ImplementedCircuitProofError::Ligero)?;
    profile.ligero_row_encode = commit_profile.row_encode;
    profile.ligero_merkle_build = commit_profile.merkle_build;
    profile.row_inventory = mdoc_p4b_row_inventory(
        params,
        committed_values.len(),
        commit_profile.rows,
        &instances,
        &layouts,
        None,
    );
    let root = commitment.root();
    let av = draw_mdoc_p4b_av(transcript_seed, root);
    let mac_tags = mac_key_shares
        .0
        .iter()
        .zip(mac_values.iter())
        .map(|(ap, x)| gf128_tag(ap, &av, x))
        .collect::<Vec<_>>();
    let committed_values_b = mac_batch_group_b_input(mac_key_shares, &av, &mac_values, &mac_tags)
        .map_err(ImplementedCircuitProofError::Witness)?;
    let params_b = implemented_circuit_ligero_params(committed_values_b.len());
    debug_assert_eq!(params, params_b);
    let (commitment_b, commit_profile_b) = commit_witness_profiled(&committed_values_b, params_b)
        .map_err(ImplementedCircuitProofError::Ligero)?;
    profile.ligero_row_encode += commit_profile_b.row_encode;
    profile.ligero_merkle_build += commit_profile_b.merkle_build;
    let root_b = commitment_b.root();
    let full_root = mdoc_p4b_full_root(root, root_b);

    let group_a_rows = ligero_row_count(committed_values.len(), params.row_len);
    let group_b_rows = ligero_row_count(committed_values_b.len(), params.row_len);
    let gamma = ligero_proximity_gamma(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        full_root,
        group_a_rows + group_b_rows,
        transcript_seed,
    );
    let start = Instant::now();
    let proximity_claim = commitment
        .split_proximity_claim(&commitment_b, &gamma)
        .map_err(ImplementedCircuitProofError::Ligero)?;
    profile.ligero_proximity_claim = start.elapsed();
    let start = Instant::now();
    let proximity_indices = ligero_proximity_indices(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        full_root,
        params,
        transcript_seed,
    );
    let proximity_openings = commitment
        .open_columns(&proximity_indices)
        .map_err(ImplementedCircuitProofError::Ligero)?;
    let proximity_openings_b = commitment_b
        .open_columns(&proximity_indices)
        .map_err(ImplementedCircuitProofError::Ligero)?;
    profile.ligero_openings = start.elapsed();

    let mut projections = vec![*issuer_projection, *device_projection];
    if let Some((_, revocation_projection, _)) = revocation {
        projections.push(*revocation_projection);
    }
    let mut entries = Vec::with_capacity(instances.len());
    let sumcheck_start = Instant::now();
    for instance in &instances {
        let circuit = match instance.role {
            MdocP4bCircuitRole::MacBatch => build_mac_batch_circuit(&av, &mac_tags)
                .map_err(ImplementedCircuitProofError::Circuit)?,
            _ => instance.circuit.clone(),
        };
        let input = match instance.role {
            MdocP4bCircuitRole::MacBatch => {
                mac_batch_input_with_av(mac_key_shares, &av, &mac_values, &mac_tags)
                    .map_err(ImplementedCircuitProofError::Witness)?
            }
            _ => instance.input.clone(),
        };
        let layers = circuit
            .evaluate_input(input)
            .map_err(ImplementedCircuitProofError::Circuit)?;
        let mut channel = mdoc_p4b_instance_channel(
            transcript_seed,
            full_root,
            instance.label,
            instance.role,
            &projections,
            &av,
            &mac_tags,
        );
        let instance_start = Instant::now();
        let proof = match instance.role {
            MdocP4bCircuitRole::MacBatch => {
                prove_evaluated_circuit_sorted_sparse(&circuit, &layers, full_root, &mut channel)
            }
            _ => prove_evaluated_circuit(&circuit, &layers, full_root, &mut channel),
        }
        .map_err(ImplementedCircuitProofError::Sumcheck)?;
        profile.sumcheck_by_instance.push(mdoc_p4b_instance_timing(
            instance.role,
            instance.label,
            instance_start.elapsed(),
        ));
        entries.push(ImplementedCircuitBundleEntry { proof });
    }
    profile.sumcheck = sumcheck_start.elapsed();

    let claim_start = Instant::now();
    let (claim_batch, consistency_claim_values, claim_inventory) = mdoc_p4b_prover_claim_batch(
        &commitment,
        &commitment_b,
        params,
        &instances,
        &layouts,
        &entries,
        &projections,
        committed_values.len(),
        &committed_values_b,
        full_root,
        transcript_seed,
    )?;
    profile.claim_batch = claim_start.elapsed();
    profile.row_inventory = mdoc_p4b_row_inventory(
        params,
        committed_values.len(),
        commit_profile.rows,
        &instances,
        &layouts,
        Some(claim_inventory),
    );

    Ok((
        ImplementedCircuitBundle {
            params,
            root,
            root_b: Some(root_b),
            proximity_openings,
            proximity_openings_b,
            proximity_claim,
            proximity_claim_b: None,
            claim_batch,
            claim_batch_b: None,
            consistency_claim_values,
            mac_tags,
            entries,
        },
        profile,
    ))
}

pub fn verify_implemented_circuit_bundle(
    input: &EcdsaInput,
    bundle: &ImplementedCircuitBundle,
    transcript_seed: TranscriptSeed,
) -> Result<Vec<InputClaims>, ImplementedCircuitProofError> {
    verify_implemented_circuit_bundle_profiled(input, bundle, transcript_seed)
        .map(|(claims, _)| claims)
}

pub fn verify_implemented_circuit_bundle_batch(
    inputs: &[EcdsaInput],
    bundle: &ImplementedCircuitBundle,
    transcript_seed: TranscriptSeed,
) -> Result<Vec<Vec<InputClaims>>, ImplementedCircuitProofError> {
    verify_implemented_circuit_bundle_batch_profiled(inputs, bundle, transcript_seed)
        .map(|(claims, _)| claims)
}

pub fn verify_implemented_circuit_bundle_batch_with_projection(
    projections: &[EcdsaPublicProjection],
    bundle: &ImplementedCircuitBundle,
    transcript_seed: TranscriptSeed,
) -> Result<Vec<Vec<InputClaims>>, ImplementedCircuitProofError> {
    verify_implemented_circuit_bundle_batch_with_projection_profiled(
        projections,
        bundle,
        transcript_seed,
    )
    .map(|(claims, _)| claims)
}

pub fn verify_mdoc_p4b_circuit_bundle(
    issuer_projection: &EcdsaPublicProjection,
    device_projection: &EcdsaPublicProjection,
    revocation_projection: Option<&EcdsaPublicProjection>,
    bundle: &ImplementedCircuitBundle,
    transcript_seed: TranscriptSeed,
) -> Result<(), ImplementedCircuitProofError> {
    verify_mdoc_p4b_circuit_bundle_profiled(
        issuer_projection,
        device_projection,
        revocation_projection,
        bundle,
        transcript_seed,
    )
    .map(|_| ())
}

pub fn verify_mdoc_p4b_circuit_bundle_profiled(
    issuer_projection: &EcdsaPublicProjection,
    device_projection: &EcdsaPublicProjection,
    revocation_projection: Option<&EcdsaPublicProjection>,
    bundle: &ImplementedCircuitBundle,
    transcript_seed: TranscriptSeed,
) -> Result<MdocP4bVerifyProfile, ImplementedCircuitProofError> {
    let mut profile = MdocP4bVerifyProfile::default();
    let setup_start = Instant::now();
    if bundle.mac_tags.len() != MDOC_P4B_MAC_HALF_COUNT {
        return Err(ImplementedCircuitProofError::WrongProofCount {
            expected: MDOC_P4B_MAC_HALF_COUNT,
            actual: bundle.mac_tags.len(),
        });
    }
    let root_b = bundle
        .root_b
        .ok_or(ImplementedCircuitProofError::ProximityOpeningRejected)?;
    let full_root = mdoc_p4b_full_root(bundle.root, root_b);
    let av = draw_mdoc_p4b_av(transcript_seed, bundle.root);
    let mut projections = vec![*issuer_projection, *device_projection];
    if let Some(revocation_projection) = revocation_projection {
        projections.push(*revocation_projection);
    }
    // The instance set is fixed by the verifier's expectation: a bundle whose
    // entry count does not match (revocation present vs absent) is rejected by
    // the proof-count check below.
    let circuits =
        mdoc_p4b_verifier_instances(&av, &bundle.mac_tags, revocation_projection.is_some())?;
    if bundle.entries.len() != circuits.len() {
        return Err(ImplementedCircuitProofError::WrongProofCount {
            expected: circuits.len(),
            actual: bundle.entries.len(),
        });
    }
    let (layouts, committed_len) = mdoc_p4b_verifier_bundle_pad_layouts(&circuits, 0);
    if bundle.params != implemented_circuit_ligero_params(committed_len) {
        return Err(ImplementedCircuitProofError::ProximityOpeningRejected);
    }
    let committed_len_b = 1usize << MAC_BATCH_GROUP_B_INPUT_LOG_SIZE;
    profile.setup = setup_start.elapsed();

    let start = Instant::now();
    let proximity_gamma = ligero_proximity_gamma(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        full_root,
        ligero_row_count(committed_len, bundle.params.row_len)
            + ligero_row_count(committed_len_b, bundle.params.row_len),
        transcript_seed,
    );
    verify_ligero_proximity_indices(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        full_root,
        bundle.params,
        &bundle.proximity_openings,
        transcript_seed,
    )?;
    verify_ligero_proximity_indices(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        full_root,
        bundle.params,
        &bundle.proximity_openings_b,
        transcript_seed,
    )?;
    let proximity_match = verify_split_openings(
        bundle.root,
        root_b,
        bundle.params,
        committed_len,
        committed_len_b,
        &bundle.proximity_openings,
        &bundle.proximity_openings_b,
        &bundle.proximity_claim,
        &proximity_gamma,
    )
    .map_err(ImplementedCircuitProofError::Ligero)?;
    if !proximity_match {
        return Err(ImplementedCircuitProofError::ProximityOpeningRejected);
    }
    profile.ligero_proximity = start.elapsed();

    let mut linear_claims = Vec::new();
    let mut consistency_cursor = 0usize;
    let mut issuer_z = None;
    let mut device_qx = None;
    let mut device_qy = None;
    let mut mac_halves = [None; MDOC_P4B_MAC_HALF_COUNT];
    let mut signer_state = vec![MdocP4bEcdsaConsistency::default(); projections.len()];

    for ((instance, layout), entry) in circuits
        .iter()
        .zip(layouts.iter())
        .zip(bundle.entries.iter())
    {
        let mut channel = mdoc_p4b_instance_channel(
            transcript_seed,
            full_root,
            instance.label,
            instance.role,
            &projections,
            &av,
            &bundle.mac_tags,
        );
        let start = Instant::now();
        let claims = match instance.role {
            MdocP4bCircuitRole::MacBatch => verify_circuit_sorted_sparse(
                &instance.circuit,
                &entry.proof,
                full_root,
                &mut channel,
            ),
            _ => verify_circuit(&instance.circuit, &entry.proof, full_root, &mut channel),
        }
        .map_err(ImplementedCircuitProofError::Sumcheck)?;
        let elapsed = start.elapsed();
        profile.sumcheck += elapsed;
        profile.sumcheck_by_instance.push(mdoc_p4b_instance_timing(
            instance.role,
            instance.label,
            elapsed,
        ));
        let start = Instant::now();
        match instance.role {
            MdocP4bCircuitRole::MacBatch => take_mac_split_input_claims(
                &mut linear_claims,
                bundle,
                &mut consistency_cursor,
                layout,
                ligero_row_count(committed_len, bundle.params.row_len) * bundle.params.row_len,
                &claims,
            )?,
            _ => add_input_claims(&mut linear_claims, layout, &claims),
        }
        add_pad_claims(
            &mut linear_claims,
            layout,
            &proof_otp_pad_values(&entry.proof),
            full_root,
            transcript_seed,
        )?;
        profile.input_claims += start.elapsed();
        let start = Instant::now();
        match instance.role {
            MdocP4bCircuitRole::IssuerEcdsa => {
                mdoc_p4b_take_ecdsa_claims(
                    &mut linear_claims,
                    bundle,
                    &mut consistency_cursor,
                    layout,
                    issuer_projection,
                    &mut signer_state[0],
                    instance.label,
                )?;
                if instance.label == b"s4-ecdsa-c3-c5-scalar-setup" {
                    issuer_z = Some(take_private_value(
                        &mut linear_claims,
                        bundle,
                        &mut consistency_cursor,
                        layout,
                        C3_Z_INDEX as usize,
                    )?);
                }
            }
            MdocP4bCircuitRole::DeviceEcdsa => {
                mdoc_p4b_take_ecdsa_claims(
                    &mut linear_claims,
                    bundle,
                    &mut consistency_cursor,
                    layout,
                    device_projection,
                    &mut signer_state[1],
                    instance.label,
                )?;
                if instance.label == b"s4-ecdsa-c2-canonicality" {
                    device_qx = Some(take_private_value(
                        &mut linear_claims,
                        bundle,
                        &mut consistency_cursor,
                        layout,
                        C2_QX_INDEX as usize,
                    )?);
                    device_qy = Some(take_private_value(
                        &mut linear_claims,
                        bundle,
                        &mut consistency_cursor,
                        layout,
                        C2_QY_INDEX as usize,
                    )?);
                }
            }
            MdocP4bCircuitRole::RevocationEcdsa => {
                // Only reachable when the verifier expects a revocation set:
                // `circuits` contains revocation instances iff
                // `revocation_projection` is `Some`.
                mdoc_p4b_take_ecdsa_claims(
                    &mut linear_claims,
                    bundle,
                    &mut consistency_cursor,
                    layout,
                    revocation_projection.expect("revocation instances imply a projection"),
                    &mut signer_state[2],
                    instance.label,
                )?;
            }
            MdocP4bCircuitRole::MacBatch => {
                for (index, slot) in mac_halves.iter_mut().enumerate() {
                    add_mac_half_public_const_claim(&mut linear_claims, layout, index);
                    *slot = Some(take_mac_half_x_recompose_claim(
                        &mut linear_claims,
                        bundle,
                        &mut consistency_cursor,
                        layout,
                        index,
                    )?);
                }
            }
        }
        profile.consistency += start.elapsed();
    }
    if consistency_cursor != bundle.consistency_claim_values.len() {
        return Err(ImplementedCircuitProofError::InputClaimOpeningRejected);
    }

    let start = Instant::now();
    for state in signer_state {
        state.verify()?;
    }
    verify_mdoc_p4b_native_mac_consistency(issuer_z, device_qx, device_qy, mac_halves)?;
    profile.consistency += start.elapsed();

    let start = Instant::now();
    let claim_gamma = ligero_claim_gamma(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        full_root,
        linear_claims.len(),
        transcript_seed,
    );
    if !verify_split_claim_batch(
        bundle.root,
        root_b,
        bundle.params,
        committed_len,
        committed_len_b,
        &bundle.proximity_openings,
        &bundle.proximity_openings_b,
        &bundle.claim_batch,
        &linear_claims,
        &claim_gamma,
    )
    .map_err(ImplementedCircuitProofError::Ligero)?
    {
        return Err(ImplementedCircuitProofError::InputClaimOpeningRejected);
    }
    profile.claim_batch = start.elapsed();
    Ok(profile)
}

pub fn mdoc_p4b_av_from_root(transcript_seed: TranscriptSeed, root: [u8; 32]) -> Gf128 {
    draw_mdoc_p4b_av(transcript_seed, root)
}

pub fn verify_implemented_circuit_bundle_batch_profiled(
    inputs: &[EcdsaInput],
    bundle: &ImplementedCircuitBundle,
    transcript_seed: TranscriptSeed,
) -> Result<(Vec<Vec<InputClaims>>, ImplementedCircuitVerifyProfile), ImplementedCircuitProofError>
{
    let projections: Vec<_> = inputs.iter().map(EcdsaPublicProjection::full).collect();
    verify_implemented_circuit_bundle_batch_with_projection_profiled(
        &projections,
        bundle,
        transcript_seed,
    )
}

pub fn verify_implemented_circuit_bundle_batch_with_projection_profiled(
    projections: &[EcdsaPublicProjection],
    bundle: &ImplementedCircuitBundle,
    transcript_seed: TranscriptSeed,
) -> Result<(Vec<Vec<InputClaims>>, ImplementedCircuitVerifyProfile), ImplementedCircuitProofError>
{
    let mut profile = ImplementedCircuitVerifyProfile::default();
    let setup_start = Instant::now();
    let circuits =
        implemented_circuit_verifier_instances().map_err(ImplementedCircuitProofError::Circuit)?;
    let expected_entries = projections.len() * circuits.len();
    if bundle.entries.len() != expected_entries {
        return Err(ImplementedCircuitProofError::WrongProofCount {
            expected: expected_entries,
            actual: bundle.entries.len(),
        });
    }

    let mut signature_layouts = Vec::with_capacity(projections.len());
    let mut offset = 0;
    for _ in projections {
        let (layouts, next_offset) = verifier_bundle_pad_layouts(&circuits, offset);
        signature_layouts.push(layouts);
        offset = next_offset;
    }
    let committed_len = offset;
    if bundle.params != implemented_circuit_ligero_params(committed_len) {
        return Err(ImplementedCircuitProofError::ProximityOpeningRejected);
    }
    profile.setup = setup_start.elapsed();

    let start = Instant::now();
    let proximity_gamma = ligero_proximity_gamma(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        bundle.root,
        ligero_row_count(committed_len, bundle.params.row_len),
        transcript_seed,
    );
    verify_ligero_proximity_indices(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        bundle.root,
        bundle.params,
        &bundle.proximity_openings,
        transcript_seed,
    )?;
    let proximity_match = verify_openings(
        bundle.root,
        bundle.params,
        &bundle.proximity_openings,
        &bundle.proximity_claim,
        &proximity_gamma,
    )
    .map_err(ImplementedCircuitProofError::Ligero)?;
    if !proximity_match {
        return Err(ImplementedCircuitProofError::ProximityOpeningRejected);
    }
    profile.ligero_proximity = start.elapsed();

    let mut linear_claims = Vec::new();
    let mut consistency_cursor = 0usize;
    let mut all_claims = Vec::with_capacity(projections.len());
    for (signature_index, (projection, layouts)) in
        projections.iter().zip(&signature_layouts).enumerate()
    {
        let mut verified_claims = Vec::with_capacity(circuits.len());
        let mut u_scalars_from_c3 = None;
        let mut u_scalars_from_c6 = None;
        let mut add_inputs_from_c11 = None;
        let mut denom_inv_from_c11 = None;
        let mut final_from_c11 = None;
        let mut c12_boundaries = None;
        let mut c13_boundary_values = None;
        let mut rx_from_c14 = None;
        for (family_index, ((instance, layout), entry)) in circuits
            .iter()
            .zip(layouts)
            .zip(
                &bundle.entries
                    [signature_index * circuits.len()..(signature_index + 1) * circuits.len()],
            )
            .enumerate()
        {
            let mut channel =
                CoprocessorChannel::from_seed(transcript_seed, COPROCESSOR_TRANSCRIPT_DOMAIN);
            mix_bundle_signature_index(signature_index, &mut channel);
            channel.mix_bytes(instance.label);
            mix_ecdsa_public_projection(projection, &mut channel);
            let start = Instant::now();
            let claims = verify_circuit(&instance.circuit, &entry.proof, bundle.root, &mut channel)
                .map_err(ImplementedCircuitProofError::Sumcheck)?;
            let elapsed = start.elapsed();
            profile.sumcheck += elapsed;
            profile.sumcheck_by_family[family_index] += elapsed;

            let start = Instant::now();
            add_input_claims(&mut linear_claims, layout, &claims);
            add_pad_claims(
                &mut linear_claims,
                layout,
                &proof_otp_pad_values(&entry.proof),
                bundle.root,
                transcript_seed,
            )?;
            profile.input_claims += start.elapsed();

            let start = Instant::now();
            match instance.label {
                b"s4-ecdsa-c1-input-limbs" => {
                    add_c1_public_claims(&mut linear_claims, projection, layout)?
                }
                b"s4-ecdsa-c2-canonicality" => {
                    add_c2_public_claims(&mut linear_claims, projection, layout)?;
                }
                b"s4-ecdsa-c3-c5-scalar-setup" => {
                    add_c3_public_claims(&mut linear_claims, projection, layout)?;
                    u_scalars_from_c3 = Some((
                        take_private_value(
                            &mut linear_claims,
                            bundle,
                            &mut consistency_cursor,
                            layout,
                            C3_U1_INDEX as usize,
                        )?,
                        take_private_value(
                            &mut linear_claims,
                            bundle,
                            &mut consistency_cursor,
                            layout,
                            C3_U2_INDEX as usize,
                        )?,
                    ));
                }
                b"s4-ecdsa-c6-scalar-bits" => {
                    u_scalars_from_c6 = Some((
                        take_private_value(
                            &mut linear_claims,
                            bundle,
                            &mut consistency_cursor,
                            layout,
                            C6_U1_INDEX as usize,
                        )?,
                        take_private_value(
                            &mut linear_claims,
                            bundle,
                            &mut consistency_cursor,
                            layout,
                            C6_U2_INDEX as usize,
                        )?,
                    ));
                }
                b"s4-ecdsa-c11-final-add" => {
                    let ax = take_private_value(
                        &mut linear_claims,
                        bundle,
                        &mut consistency_cursor,
                        layout,
                        C11_AX_INDEX as usize,
                    )?;
                    let ay = take_private_value(
                        &mut linear_claims,
                        bundle,
                        &mut consistency_cursor,
                        layout,
                        C11_AY_INDEX as usize,
                    )?;
                    let bx = take_private_value(
                        &mut linear_claims,
                        bundle,
                        &mut consistency_cursor,
                        layout,
                        C11_BX_INDEX as usize,
                    )?;
                    let by = take_private_value(
                        &mut linear_claims,
                        bundle,
                        &mut consistency_cursor,
                        layout,
                        C11_BY_INDEX as usize,
                    )?;
                    let rx = take_private_value(
                        &mut linear_claims,
                        bundle,
                        &mut consistency_cursor,
                        layout,
                        C11_RX_INDEX as usize,
                    )?;
                    let ry = take_private_value(
                        &mut linear_claims,
                        bundle,
                        &mut consistency_cursor,
                        layout,
                        C11_RY_INDEX as usize,
                    )?;
                    let denom_inv = take_private_value(
                        &mut linear_claims,
                        bundle,
                        &mut consistency_cursor,
                        layout,
                        C11_DENOM_INV_INDEX as usize,
                    )?;
                    add_inputs_from_c11 = Some(((ax, ay), (bx, by)));
                    denom_inv_from_c11 = Some(denom_inv);
                    final_from_c11 = Some((rx, ry));
                }
                b"s4-ecdsa-c12-final-on-curve" => {
                    c12_boundaries = Some(take_c12_boundary_values(
                        &mut linear_claims,
                        bundle,
                        &mut consistency_cursor,
                        layout,
                    )?);
                }
                b"s4-ecdsa-c13-slope-inverses" => {
                    c13_boundary_values = Some(take_c13_boundary_values(
                        &mut linear_claims,
                        bundle,
                        &mut consistency_cursor,
                        layout,
                    )?);
                }
                b"s4-ecdsa-c14-c15-final-check" => {
                    add_c14_public_claims(&mut linear_claims, projection, layout)?;
                    rx_from_c14 = Some(take_private_value(
                        &mut linear_claims,
                        bundle,
                        &mut consistency_cursor,
                        layout,
                        C14_RX_INDEX as usize,
                    )?);
                }
                _ => {}
            }
            profile.consistency += start.elapsed();
            verified_claims.push(claims);
        }
        let start = Instant::now();
        verify_u_scalar_cross_family(u_scalars_from_c3, u_scalars_from_c6)?;
        verify_corrected_endpoint_cross_family(
            c12_boundaries.map(|boundaries| boundaries.corrected_endpoints),
            add_inputs_from_c11,
        )?;
        verify_c13_boundary_cross_family(
            add_inputs_from_c11,
            denom_inv_from_c11,
            final_from_c11,
            c13_boundary_values,
        )?;
        verify_final_point_cross_family(
            final_from_c11,
            c12_boundaries.map(|boundaries| boundaries.final_point),
            rx_from_c14,
        )?;
        profile.consistency += start.elapsed();
        all_claims.push(verified_claims);
    }
    if consistency_cursor != bundle.consistency_claim_values.len() {
        return Err(ImplementedCircuitProofError::InputClaimOpeningRejected);
    }
    let start = Instant::now();
    let claim_gamma = ligero_claim_gamma(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        bundle.root,
        linear_claims.len(),
        transcript_seed,
    );
    if !verify_claim_batch(
        bundle.root,
        bundle.params,
        committed_len,
        &bundle.proximity_openings,
        &bundle.claim_batch,
        &linear_claims,
        &claim_gamma,
    )
    .map_err(ImplementedCircuitProofError::Ligero)?
    {
        return Err(ImplementedCircuitProofError::InputClaimOpeningRejected);
    }
    profile.systematic_reconstruct = start.elapsed();
    Ok((all_claims, profile))
}

pub fn verify_implemented_circuit_bundle_profiled(
    input: &EcdsaInput,
    bundle: &ImplementedCircuitBundle,
    transcript_seed: TranscriptSeed,
) -> Result<(Vec<InputClaims>, ImplementedCircuitVerifyProfile), ImplementedCircuitProofError> {
    let (mut claims, profile) =
        verify_implemented_circuit_bundle_batch_profiled(&[*input], bundle, transcript_seed)?;
    let claims = claims
        .pop()
        .ok_or(ImplementedCircuitProofError::InputClaimOpeningRejected)?;
    Ok((claims, profile))
}

fn verify_u_scalar_cross_family(
    c3: Option<(Fp, Fp)>,
    c6: Option<(Fp, Fp)>,
) -> Result<(), ImplementedCircuitProofError> {
    let (Some(c3), Some(c6)) = (c3, c6) else {
        return Err(ImplementedCircuitProofError::CrossFamilyBindingRejected);
    };
    if c3 != c6 {
        return Err(ImplementedCircuitProofError::CrossFamilyBindingRejected);
    }
    Ok(())
}

fn verify_corrected_endpoint_cross_family(
    c12: Option<((Fp, Fp), (Fp, Fp))>,
    c11: Option<((Fp, Fp), (Fp, Fp))>,
) -> Result<(), ImplementedCircuitProofError> {
    let (Some(c12), Some(c11)) = (c12, c11) else {
        return Err(ImplementedCircuitProofError::CrossFamilyBindingRejected);
    };
    if c12 != c11 {
        return Err(ImplementedCircuitProofError::CrossFamilyBindingRejected);
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct C13BoundaryValues {
    final_add_denominator: Fp,
    final_add_inverse: Fp,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct C12BoundaryValues {
    corrected_endpoints: ((Fp, Fp), (Fp, Fp)),
    final_point: (Fp, Fp),
}

fn verify_c13_boundary_cross_family(
    c11_add: Option<((Fp, Fp), (Fp, Fp))>,
    c11_add_inverse: Option<Fp>,
    c11_final: Option<(Fp, Fp)>,
    c13: Option<C13BoundaryValues>,
) -> Result<(), ImplementedCircuitProofError> {
    let Some(c13) = c13 else {
        return Err(ImplementedCircuitProofError::CrossFamilyBindingRejected);
    };

    let (Some(((ax, _), (bx, _))), Some(c11_add_inverse), Some(_)) =
        (c11_add, c11_add_inverse, c11_final)
    else {
        return Err(ImplementedCircuitProofError::CrossFamilyBindingRejected);
    };
    if c13.final_add_denominator != bx - ax || c13.final_add_inverse != c11_add_inverse {
        return Err(ImplementedCircuitProofError::CrossFamilyBindingRejected);
    }
    Ok(())
}

fn verify_final_point_cross_family(
    c11: Option<(Fp, Fp)>,
    c12: Option<(Fp, Fp)>,
    c14_rx: Option<Fp>,
) -> Result<(), ImplementedCircuitProofError> {
    let (Some(c11), Some(c12), Some(c14_rx)) = (c11, c12, c14_rx) else {
        return Err(ImplementedCircuitProofError::CrossFamilyBindingRejected);
    };
    if c11 != c12 || c11.0 != c14_rx {
        return Err(ImplementedCircuitProofError::CrossFamilyBindingRejected);
    }
    Ok(())
}

fn ligero_row_count(values: usize, row_len: usize) -> usize {
    values.div_ceil(row_len)
}

fn ligero_proximity_gamma(
    label: &[u8],
    root: [u8; 32],
    rows: usize,
    transcript_seed: TranscriptSeed,
) -> Vec<Fp> {
    let mut channel = CoprocessorChannel::from_seed(transcript_seed, COPROCESSOR_TRANSCRIPT_DOMAIN);
    channel.mix_bytes(label);
    channel.mix_bytes(&root);
    channel.mix_bytes(b"s4-ligero-proximity-gamma");
    (0..rows).map(|_| channel.draw_fp()).collect()
}

fn ligero_claim_gamma(
    label: &[u8],
    root: [u8; 32],
    claims: usize,
    transcript_seed: TranscriptSeed,
) -> Vec<Fp> {
    let mut channel = CoprocessorChannel::from_seed(transcript_seed, COPROCESSOR_TRANSCRIPT_DOMAIN);
    channel.mix_bytes(label);
    channel.mix_bytes(&root);
    channel.mix_bytes(b"s4-ligero-claim-gamma");
    (0..claims).map(|_| channel.draw_fp()).collect()
}

fn ligero_proximity_indices(
    label: &[u8],
    root: [u8; 32],
    params: LigeroParams,
    transcript_seed: TranscriptSeed,
) -> Vec<usize> {
    let mut channel = CoprocessorChannel::from_seed(transcript_seed, COPROCESSOR_TRANSCRIPT_DOMAIN);
    channel.mix_bytes(label);
    channel.mix_bytes(&root);
    channel.mix_bytes(b"s4-ligero-proximity-indices");
    let mut indices = Vec::with_capacity(params.openings);
    while indices.len() < params.openings {
        let bytes = channel.draw_fp().to_bytes_be();
        let mut word = [0u8; 8];
        word.copy_from_slice(&bytes[24..]);
        let index = (u64::from_be_bytes(word) as usize) % params.codeword_len;
        if index >= params.row_len && !indices.contains(&index) {
            indices.push(index);
        }
    }
    indices
}

fn verify_ligero_proximity_indices(
    label: &[u8],
    root: [u8; 32],
    params: LigeroParams,
    openings: &[ColumnOpening],
    transcript_seed: TranscriptSeed,
) -> Result<(), ImplementedCircuitProofError> {
    let expected = ligero_proximity_indices(label, root, params, transcript_seed);
    let actual = openings
        .iter()
        .map(|opening| opening.index)
        .collect::<Vec<_>>();
    if actual != expected {
        return Err(ImplementedCircuitProofError::ProximityOpeningRejected);
    }
    Ok(())
}

fn mdoc_p4b_full_root(root_a: [u8; 32], root_b: [u8; 32]) -> [u8; 32] {
    let mut hasher = Blake2s256::new();
    hasher.update(b"eu-id-s4-mdoc-p4b-two-root-v1");
    hasher.update(root_a);
    hasher.update(root_b);
    let digest = hasher.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    out
}

fn mix_bundle_signature_index(signature_index: usize, channel: &mut CoprocessorChannel) {
    channel.mix_bytes(b"s4-ecdsa-bundle-signature-index");
    channel.mix_bytes(&(signature_index as u64).to_be_bytes());
}

fn draw_mdoc_p4b_av(transcript_seed: TranscriptSeed, root: [u8; 32]) -> Gf128 {
    let mut channel = CoprocessorChannel::from_seed(transcript_seed, COPROCESSOR_TRANSCRIPT_DOMAIN);
    channel.mix_bytes(b"s4-mdoc-p4b-mac-public");
    channel.mix_bytes(&root);
    channel.draw_gf128(b"eu-id-p4b-mac-av")
}

fn mdoc_p4b_instance_channel(
    transcript_seed: TranscriptSeed,
    root: [u8; 32],
    label: &[u8],
    role: MdocP4bCircuitRole,
    projections: &[EcdsaPublicProjection],
    av: &Gf128,
    mac_tags: &[Gf128],
) -> CoprocessorChannel {
    let mut channel = CoprocessorChannel::from_seed(transcript_seed, COPROCESSOR_TRANSCRIPT_DOMAIN);
    match role {
        MdocP4bCircuitRole::IssuerEcdsa => {
            mix_bundle_signature_index(0, &mut channel);
            channel.mix_bytes(label);
            mix_ecdsa_public_projection(&projections[0], &mut channel);
        }
        MdocP4bCircuitRole::DeviceEcdsa => {
            mix_bundle_signature_index(1, &mut channel);
            channel.mix_bytes(label);
            mix_ecdsa_public_projection(&projections[1], &mut channel);
        }
        MdocP4bCircuitRole::RevocationEcdsa => {
            mix_bundle_signature_index(2, &mut channel);
            channel.mix_bytes(label);
            mix_ecdsa_public_projection(&projections[2], &mut channel);
        }
        MdocP4bCircuitRole::MacBatch => {
            channel.mix_bytes(b"s4-mdoc-p4b-mac-public");
            channel.mix_bytes(&root);
            channel.mix_bytes(av);
            channel.mix_bytes(&(mac_tags.len() as u64).to_be_bytes());
            for tag in mac_tags {
                channel.mix_bytes(tag);
            }
            channel.mix_bytes(label);
        }
    }
    channel
}

fn mdoc_p4b_mac_values(issuer_input: &EcdsaInput, device_input: &EcdsaInput) -> [Gf128; 6] {
    let [issuer_z_lo, issuer_z_hi] = gf128_halves_from_be32(issuer_input.z);
    let [device_qx_lo, device_qx_hi] = gf128_halves_from_be32(device_input.qx);
    let [device_qy_lo, device_qy_hi] = gf128_halves_from_be32(device_input.qy);
    [
        issuer_z_lo,
        issuer_z_hi,
        device_qx_lo,
        device_qx_hi,
        device_qy_lo,
        device_qy_hi,
    ]
}

pub fn implemented_circuit_gate_count() -> Result<usize, CircuitError> {
    Ok([
        build_c1_input_limbs_circuit()?,
        build_c2_canonicality_circuit()?,
        build_c3_c5_scalar_setup_circuit()?,
        build_c6_scalar_bits_circuit()?,
        build_c11_final_add_circuit()?,
        build_c12_on_curve_circuit()?,
        build_c13_slope_inverses_circuit()?,
        build_c14_c15_final_check_circuit()?,
    ]
    .iter()
    .map(circuit_gate_count)
    .sum())
}

pub fn implemented_circuit_family_labels() -> Result<Vec<&'static [u8]>, CircuitError> {
    Ok(implemented_circuit_verifier_instances()?
        .into_iter()
        .map(|instance| instance.label)
        .collect())
}

pub fn implemented_circuit_transcript_shapes() -> Result<Vec<CircuitTranscriptShape>, CircuitError>
{
    Ok(implemented_circuit_verifier_instances()?
        .into_iter()
        .map(|instance| CircuitTranscriptShape {
            label: instance.label,
            layers: instance
                .circuit
                .layers()
                .iter()
                .map(|layer| (layer.out_log_size(), layer.next_log_size()))
                .collect(),
        })
        .collect())
}

fn circuit_gate_count(circuit: &Circuit) -> usize {
    circuit
        .layers()
        .iter()
        .map(|layer| layer.terms().len())
        .sum()
}

fn implemented_circuit_ligero_params(_input_len: usize) -> LigeroParams {
    // v4: circle-FFT code at ℓ=256 (k = 512, claim bound 770, e = 1662,
    // t = 176, ≈2^-132.2). Same FFT domains as v3 (ℓ=128) with twice the
    // data slots per row: half the rows, so the per-column openings that
    // dominate proof size AND the row-encode work both halve, at unchanged
    // claim-batch cost per row-weight interpolation count (which doubles per
    // row but halves in row count).
    let params = v4_circle_params();
    debug_assert!(params.validate().is_ok());
    debug_assert!(params.soundness_error() <= 2f64.powi(-128));
    params
}

struct ProverCircuitInstance {
    label: &'static [u8],
    slot: LayoutSlot,
    circuit: Circuit,
    input: Vec<Fp>,
}

struct VerifierCircuitInstance {
    label: &'static [u8],
    circuit: Circuit,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MdocP4bCircuitRole {
    IssuerEcdsa,
    DeviceEcdsa,
    RevocationEcdsa,
    MacBatch,
}

struct MdocP4bProverInstance {
    label: &'static [u8],
    role: MdocP4bCircuitRole,
    circuit: Circuit,
    input: Vec<Fp>,
}

impl MdocP4bProverInstance {
    fn ecdsa(signature_index: usize, instance: ProverCircuitInstance) -> Self {
        Self {
            label: instance.label,
            role: match signature_index {
                0 => MdocP4bCircuitRole::IssuerEcdsa,
                1 => MdocP4bCircuitRole::DeviceEcdsa,
                2 => MdocP4bCircuitRole::RevocationEcdsa,
                _ => unreachable!("mdoc P4b bundle has at most three ECDSA instance sets"),
            },
            circuit: instance.circuit,
            input: instance.input,
        }
    }
}

struct MdocP4bVerifierInstance {
    label: &'static [u8],
    role: MdocP4bCircuitRole,
    circuit: Circuit,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct MdocP4bClaimInventory {
    linear_claims: usize,
    linear_claim_touched_rows: usize,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct MdocP4bEcdsaConsistency {
    u_scalars_from_c3: Option<(Fp, Fp)>,
    u_scalars_from_c6: Option<(Fp, Fp)>,
    add_inputs_from_c11: Option<((Fp, Fp), (Fp, Fp))>,
    denom_inv_from_c11: Option<Fp>,
    final_from_c11: Option<(Fp, Fp)>,
    c12_boundaries: Option<C12BoundaryValues>,
    c13_boundary_values: Option<C13BoundaryValues>,
    rx_from_c14: Option<Fp>,
}

impl MdocP4bEcdsaConsistency {
    fn verify(self) -> Result<(), ImplementedCircuitProofError> {
        verify_u_scalar_cross_family(self.u_scalars_from_c3, self.u_scalars_from_c6)?;
        verify_corrected_endpoint_cross_family(
            self.c12_boundaries
                .map(|boundaries| boundaries.corrected_endpoints),
            self.add_inputs_from_c11,
        )?;
        verify_c13_boundary_cross_family(
            self.add_inputs_from_c11,
            self.denom_inv_from_c11,
            self.final_from_c11,
            self.c13_boundary_values,
        )?;
        verify_final_point_cross_family(
            self.final_from_c11,
            self.c12_boundaries.map(|boundaries| boundaries.final_point),
            self.rx_from_c14,
        )?;
        Ok(())
    }
}

const MDOC_P4B_MAC_BATCH_LABEL: &[u8] = b"s4-mdoc-p4b-mac-batch";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct BundleCircuitLayout {
    input_offset: usize,
    input_len: usize,
    pad_offset: usize,
    pad_len: usize,
}

fn verifier_bundle_pad_layouts(
    circuits: &[VerifierCircuitInstance],
    witness_len: usize,
) -> (Vec<BundleCircuitLayout>, usize) {
    let mut offset = witness_len;
    let mut layouts = Vec::with_capacity(circuits.len());
    for instance in circuits {
        let input_len = verifier_circuit_input_len(&instance.circuit);
        let input_offset = offset;
        offset += input_len;
        let pad_len = circuit_otp_pad_values(&instance.circuit).len();
        layouts.push(BundleCircuitLayout {
            input_offset,
            input_len,
            pad_offset: offset,
            pad_len,
        });
        offset += pad_len;
    }
    (layouts, offset)
}

fn mdoc_p4b_verifier_bundle_pad_layouts(
    circuits: &[MdocP4bVerifierInstance],
    witness_len: usize,
) -> (Vec<BundleCircuitLayout>, usize) {
    let mut offset = witness_len;
    let mut layouts = Vec::with_capacity(circuits.len());
    for instance in circuits {
        let input_len = match instance.role {
            MdocP4bCircuitRole::MacBatch => 1usize << MAC_BATCH_GROUP_A_INPUT_LOG_SIZE,
            _ => verifier_circuit_input_len(&instance.circuit),
        };
        let input_offset = offset;
        offset += input_len;
        let pad_len = circuit_otp_pad_values(&instance.circuit).len();
        layouts.push(BundleCircuitLayout {
            input_offset,
            input_len,
            pad_offset: offset,
            pad_len,
        });
        offset += pad_len;
    }
    (layouts, offset)
}

fn prover_committed_values(
    all_instances: &[Vec<ProverCircuitInstance>],
) -> (Vec<Fp>, Vec<Vec<BundleCircuitLayout>>) {
    let mut committed_values = Vec::new();
    let mut all_layouts = Vec::with_capacity(all_instances.len());
    for instances in all_instances {
        let mut layouts = Vec::with_capacity(instances.len());
        for instance in instances {
            let input_offset = committed_values.len();
            committed_values.extend_from_slice(&instance.input);
            let input_len = instance.input.len();
            let pads = circuit_otp_pad_values(&instance.circuit);
            let pad_offset = committed_values.len();
            let pad_len = pads.len();
            committed_values.extend(pads);
            layouts.push(BundleCircuitLayout {
                input_offset,
                input_len,
                pad_offset,
                pad_len,
            });
        }
        all_layouts.push(layouts);
    }
    (committed_values, all_layouts)
}

fn mdoc_p4b_committed_values(
    instances: &[MdocP4bProverInstance],
) -> (Vec<Fp>, Vec<BundleCircuitLayout>) {
    let mut committed_values = Vec::new();
    let mut layouts = Vec::with_capacity(instances.len());
    for instance in instances {
        let input_offset = committed_values.len();
        committed_values.extend_from_slice(&instance.input);
        let input_len = instance.input.len();
        let pads = circuit_otp_pad_values(&instance.circuit);
        let pad_offset = committed_values.len();
        let pad_len = pads.len();
        committed_values.extend(pads);
        layouts.push(BundleCircuitLayout {
            input_offset,
            input_len,
            pad_offset,
            pad_len,
        });
    }
    (committed_values, layouts)
}

fn mdoc_p4b_row_inventory(
    params: LigeroParams,
    committed_values: usize,
    encoded_rows_total: usize,
    instances: &[MdocP4bProverInstance],
    layouts: &[BundleCircuitLayout],
    claim_inventory: Option<MdocP4bClaimInventory>,
) -> MdocP4bRowInventory {
    let mut ecdsa_input_values = 0usize;
    let mut mac_input_values = 0usize;
    let mut otp_pad_values = 0usize;
    let mut ecdsa_input_rows = 0usize;
    let mut mac_input_rows = 0usize;
    let mut otp_pad_rows = 0usize;

    for (instance, layout) in instances.iter().zip(layouts) {
        match instance.role {
            MdocP4bCircuitRole::IssuerEcdsa
            | MdocP4bCircuitRole::DeviceEcdsa
            | MdocP4bCircuitRole::RevocationEcdsa => {
                ecdsa_input_values += layout.input_len;
                ecdsa_input_rows +=
                    row_span_count(layout.input_offset, layout.input_len, params.row_len);
            }
            MdocP4bCircuitRole::MacBatch => {
                mac_input_values += layout.input_len;
                mac_input_rows +=
                    row_span_count(layout.input_offset, layout.input_len, params.row_len);
            }
        }
        otp_pad_values += layout.pad_len;
        otp_pad_rows += row_span_count(layout.pad_offset, layout.pad_len, params.row_len);
    }

    let claim_inventory = claim_inventory.unwrap_or_default();
    MdocP4bRowInventory {
        row_len: params.row_len,
        committed_values,
        committed_rows: committed_values.div_ceil(params.row_len),
        encoded_rows_total,
        ecdsa_input_values,
        ecdsa_input_rows,
        mac_input_values,
        mac_input_rows,
        otp_pad_values,
        otp_pad_rows,
        blind_rows: 2,
        linear_claims: claim_inventory.linear_claims,
        linear_claim_touched_rows: claim_inventory.linear_claim_touched_rows,
    }
}

fn row_span_count(offset: usize, len: usize, row_len: usize) -> usize {
    if len == 0 {
        return 0;
    }
    ((offset % row_len) + len).div_ceil(row_len)
}

fn linear_claim_touched_rows(claims: &[LigeroLinearClaim], row_len: usize) -> usize {
    let mut rows = Vec::new();
    for claim in claims {
        let start = claim.offset / row_len;
        let end = (claim.offset + claim.len).div_ceil(row_len);
        rows.extend(start..end);
    }
    rows.sort_unstable();
    rows.dedup();
    rows.len()
}

fn mdoc_p4b_instance_timing(
    role: MdocP4bCircuitRole,
    label: &'static [u8],
    elapsed: Duration,
) -> MdocP4bInstanceTiming {
    MdocP4bInstanceTiming {
        role: mdoc_p4b_role_name(role),
        label: String::from_utf8_lossy(label).into_owned(),
        elapsed,
    }
}

fn mdoc_p4b_role_name(role: MdocP4bCircuitRole) -> &'static str {
    match role {
        MdocP4bCircuitRole::IssuerEcdsa => "issuer_ecdsa",
        MdocP4bCircuitRole::DeviceEcdsa => "device_ecdsa",
        MdocP4bCircuitRole::RevocationEcdsa => "revocation_ecdsa",
        MdocP4bCircuitRole::MacBatch => "mac_batch",
    }
}

fn verifier_circuit_input_len(circuit: &Circuit) -> usize {
    1usize << circuit.layers().last().expect("non-empty").next_log_size()
}

fn mdoc_p4b_verifier_instances(
    av: &Gf128,
    mac_tags: &[Gf128],
    include_revocation: bool,
) -> Result<Vec<MdocP4bVerifierInstance>, ImplementedCircuitProofError> {
    let mut instances = Vec::new();
    for instance in
        implemented_circuit_verifier_instances().map_err(ImplementedCircuitProofError::Circuit)?
    {
        instances.push(MdocP4bVerifierInstance {
            label: instance.label,
            role: MdocP4bCircuitRole::IssuerEcdsa,
            circuit: instance.circuit,
        });
    }
    for instance in
        implemented_circuit_verifier_instances().map_err(ImplementedCircuitProofError::Circuit)?
    {
        instances.push(MdocP4bVerifierInstance {
            label: instance.label,
            role: MdocP4bCircuitRole::DeviceEcdsa,
            circuit: instance.circuit,
        });
    }
    if include_revocation {
        for instance in implemented_circuit_verifier_instances()
            .map_err(ImplementedCircuitProofError::Circuit)?
        {
            instances.push(MdocP4bVerifierInstance {
                label: instance.label,
                role: MdocP4bCircuitRole::RevocationEcdsa,
                circuit: instance.circuit,
            });
        }
    }
    instances.push(MdocP4bVerifierInstance {
        label: MDOC_P4B_MAC_BATCH_LABEL,
        role: MdocP4bCircuitRole::MacBatch,
        circuit: build_mac_batch_circuit(av, mac_tags)
            .map_err(ImplementedCircuitProofError::Circuit)?,
    });
    Ok(instances)
}

fn prover_claim_batch(
    commitment: &crate::ligero::LigeroCommitment,
    projections: &[EcdsaPublicProjection],
    all_instances: &[Vec<ProverCircuitInstance>],
    all_layouts: &[Vec<BundleCircuitLayout>],
    entries: &[ImplementedCircuitBundleEntry],
    transcript_seed: TranscriptSeed,
) -> Result<(LigeroClaimBatch, Vec<Fp>), ImplementedCircuitProofError> {
    let mut claims = Vec::new();
    let mut consistency_values = Vec::new();
    let circuits_per_signature = all_instances.first().map(|v| v.len()).unwrap_or(0);
    for (signature_index, ((projection, instances), layouts)) in projections
        .iter()
        .zip(all_instances.iter())
        .zip(all_layouts.iter())
        .enumerate()
    {
        for (family_index, (instance, layout)) in instances.iter().zip(layouts).enumerate() {
            let entry = &entries[signature_index * circuits_per_signature + family_index];
            add_input_claims(&mut claims, layout, &entry.proof.input_claims);
            add_pad_claims(
                &mut claims,
                layout,
                &proof_otp_pad_values(&entry.proof),
                commitment.root(),
                transcript_seed,
            )?;
            add_prover_family_fixed_claims(
                &mut claims,
                &mut consistency_values,
                projection,
                instance.label,
                layout,
                &instance.input,
            )?;
        }
    }
    let gamma = ligero_claim_gamma(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        commitment.root(),
        claims.len(),
        transcript_seed,
    );
    let batch = commitment
        .claim_batch(&claims, &gamma)
        .map_err(ImplementedCircuitProofError::Ligero)?;
    Ok((batch, consistency_values))
}

fn mdoc_p4b_prover_claim_batch(
    commitment: &crate::ligero::LigeroCommitment,
    commitment_b: &crate::ligero::LigeroCommitment,
    params: LigeroParams,
    instances: &[MdocP4bProverInstance],
    layouts: &[BundleCircuitLayout],
    entries: &[ImplementedCircuitBundleEntry],
    projections: &[EcdsaPublicProjection],
    committed_len_a: usize,
    group_b_values: &[Fp],
    transcript_root: [u8; 32],
    transcript_seed: TranscriptSeed,
) -> Result<(LigeroClaimBatch, Vec<Fp>, MdocP4bClaimInventory), ImplementedCircuitProofError> {
    let mut claims = Vec::new();
    let mut consistency_values = Vec::new();
    let group_b_offset = ligero_row_count(committed_len_a, params.row_len) * params.row_len;
    for ((instance, layout), entry) in instances.iter().zip(layouts).zip(entries) {
        match instance.role {
            MdocP4bCircuitRole::MacBatch => add_mac_split_input_claims(
                &mut claims,
                &mut consistency_values,
                layout,
                group_b_offset,
                &instance.input,
                group_b_values,
                &entry.proof.input_claims,
            )?,
            _ => add_input_claims(&mut claims, layout, &entry.proof.input_claims),
        }
        add_pad_claims(
            &mut claims,
            layout,
            &proof_otp_pad_values(&entry.proof),
            transcript_root,
            transcript_seed,
        )?;
        match instance.role {
            MdocP4bCircuitRole::IssuerEcdsa => {
                add_prover_family_fixed_claims(
                    &mut claims,
                    &mut consistency_values,
                    &projections[0],
                    instance.label,
                    layout,
                    &instance.input,
                )?;
                if instance.label == b"s4-ecdsa-c3-c5-scalar-setup" {
                    add_private_value(
                        &mut claims,
                        &mut consistency_values,
                        layout,
                        C3_Z_INDEX as usize,
                        &instance.input,
                    )?;
                }
            }
            MdocP4bCircuitRole::DeviceEcdsa => {
                add_prover_family_fixed_claims(
                    &mut claims,
                    &mut consistency_values,
                    &projections[1],
                    instance.label,
                    layout,
                    &instance.input,
                )?;
                if instance.label == b"s4-ecdsa-c2-canonicality" {
                    add_private_value(
                        &mut claims,
                        &mut consistency_values,
                        layout,
                        C2_QX_INDEX as usize,
                        &instance.input,
                    )?;
                    add_private_value(
                        &mut claims,
                        &mut consistency_values,
                        layout,
                        C2_QY_INDEX as usize,
                        &instance.input,
                    )?;
                }
            }
            MdocP4bCircuitRole::RevocationEcdsa => {
                add_prover_family_fixed_claims(
                    &mut claims,
                    &mut consistency_values,
                    &projections[2],
                    instance.label,
                    layout,
                    &instance.input,
                )?;
            }
            MdocP4bCircuitRole::MacBatch => {
                for half in 0..MDOC_P4B_MAC_HALF_COUNT {
                    add_mac_half_public_const_claim(&mut claims, layout, half);
                    add_mac_half_x_recompose_claim(
                        &mut claims,
                        &mut consistency_values,
                        layout,
                        &instance.input,
                        half,
                    )?;
                }
            }
        }
    }
    let gamma = ligero_claim_gamma(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        transcript_root,
        claims.len(),
        transcript_seed,
    );
    let batch = commitment
        .split_claim_batch(commitment_b, &claims, &gamma)
        .map_err(ImplementedCircuitProofError::Ligero)?;
    let inventory = MdocP4bClaimInventory {
        linear_claims: claims.len(),
        linear_claim_touched_rows: linear_claim_touched_rows(&claims, params.row_len),
    };
    Ok((batch, consistency_values, inventory))
}

fn add_input_claims(
    claims: &mut Vec<LigeroLinearClaim>,
    layout: &BundleCircuitLayout,
    input_claims: &InputClaims,
) {
    for (point, value) in input_claims.points.iter().cloned().zip(input_claims.values) {
        claims.push(LigeroLinearClaim {
            offset: layout.input_offset,
            len: layout.input_len,
            point,
            value,
        });
    }
}

fn add_mac_split_input_claims(
    claims: &mut Vec<LigeroLinearClaim>,
    consistency_values: &mut Vec<Fp>,
    layout_a: &BundleCircuitLayout,
    group_b_offset: usize,
    values_a: &[Fp],
    values_b: &[Fp],
    input_claims: &InputClaims,
) -> Result<(), ImplementedCircuitProofError> {
    let mle_a = Mle::new(values_a.to_vec());
    let mle_b = Mle::new(values_b.to_vec());
    for (point, value) in input_claims.points.iter().zip(input_claims.values) {
        if point.len() != MAC_BATCH_INPUT_LOG_SIZE {
            return Err(ImplementedCircuitProofError::InputClaimOpeningRejected);
        }
        let split = point[MAC_BATCH_GROUP_A_INPUT_LOG_SIZE];
        let subpoint = point[..MAC_BATCH_GROUP_A_INPUT_LOG_SIZE].to_vec();
        let value_a = mle_a
            .eval_at(&subpoint)
            .map_err(|_| ImplementedCircuitProofError::InputClaimOpeningRejected)?;
        let value_b = mle_b
            .eval_at(&subpoint)
            .map_err(|_| ImplementedCircuitProofError::InputClaimOpeningRejected)?;
        if (Fp::ONE - split) * value_a + split * value_b != value {
            return Err(ImplementedCircuitProofError::InputClaimOpeningRejected);
        }
        consistency_values.push(value_a);
        consistency_values.push(value_b);
        claims.push(LigeroLinearClaim {
            offset: layout_a.input_offset,
            len: layout_a.input_len,
            point: subpoint.clone(),
            value: value_a,
        });
        claims.push(LigeroLinearClaim {
            offset: group_b_offset,
            len: values_b.len(),
            point: subpoint,
            value: value_b,
        });
    }
    Ok(())
}

fn take_mac_split_input_claims(
    claims: &mut Vec<LigeroLinearClaim>,
    bundle: &ImplementedCircuitBundle,
    cursor: &mut usize,
    layout_a: &BundleCircuitLayout,
    group_b_offset: usize,
    input_claims: &InputClaims,
) -> Result<(), ImplementedCircuitProofError> {
    for (point, value) in input_claims.points.iter().zip(input_claims.values) {
        if point.len() != MAC_BATCH_INPUT_LOG_SIZE {
            return Err(ImplementedCircuitProofError::InputClaimOpeningRejected);
        }
        let value_a = bundle
            .consistency_claim_values
            .get(*cursor)
            .copied()
            .ok_or(ImplementedCircuitProofError::InputClaimOpeningRejected)?;
        *cursor += 1;
        let value_b = bundle
            .consistency_claim_values
            .get(*cursor)
            .copied()
            .ok_or(ImplementedCircuitProofError::InputClaimOpeningRejected)?;
        *cursor += 1;
        let split = point[MAC_BATCH_GROUP_A_INPUT_LOG_SIZE];
        if (Fp::ONE - split) * value_a + split * value_b != value {
            return Err(ImplementedCircuitProofError::InputClaimOpeningRejected);
        }
        let subpoint = point[..MAC_BATCH_GROUP_A_INPUT_LOG_SIZE].to_vec();
        claims.push(LigeroLinearClaim {
            offset: layout_a.input_offset,
            len: layout_a.input_len,
            point: subpoint.clone(),
            value: value_a,
        });
        claims.push(LigeroLinearClaim {
            offset: group_b_offset,
            len: 1usize << MAC_BATCH_GROUP_B_INPUT_LOG_SIZE,
            point: subpoint,
            value: value_b,
        });
    }
    Ok(())
}

fn add_pad_claims(
    claims: &mut Vec<LigeroLinearClaim>,
    layout: &BundleCircuitLayout,
    pads: &[Fp],
    root: [u8; 32],
    transcript_seed: TranscriptSeed,
) -> Result<(), ImplementedCircuitProofError> {
    debug_assert_eq!(layout.pad_len, pads.len());
    if pads.is_empty() {
        return Ok(());
    }
    let point = pad_claim_point(layout.pad_offset, layout.pad_len, root, transcript_seed);
    let value = Mle::new(pads.to_vec())
        .eval_at(&point)
        .map_err(|err| ImplementedCircuitProofError::Ligero(LigeroError::Mle(err)))?;
    claims.push(LigeroLinearClaim {
        offset: layout.pad_offset,
        len: layout.pad_len,
        point,
        value,
    });
    Ok(())
}

fn add_prover_family_fixed_claims(
    claims: &mut Vec<LigeroLinearClaim>,
    consistency_values: &mut Vec<Fp>,
    projection: &EcdsaPublicProjection,
    label: &[u8],
    layout: &BundleCircuitLayout,
    values: &[Fp],
) -> Result<(), ImplementedCircuitProofError> {
    match label {
        b"s4-ecdsa-c1-input-limbs" => add_c1_public_claims(claims, projection, layout)?,
        b"s4-ecdsa-c2-canonicality" => add_c2_public_claims(claims, projection, layout)?,
        b"s4-ecdsa-c3-c5-scalar-setup" => {
            add_c3_public_claims(claims, projection, layout)?;
            add_private_value(
                claims,
                consistency_values,
                layout,
                C3_U1_INDEX as usize,
                values,
            )?;
            add_private_value(
                claims,
                consistency_values,
                layout,
                C3_U2_INDEX as usize,
                values,
            )?;
        }
        b"s4-ecdsa-c6-scalar-bits" => {
            add_private_value(
                claims,
                consistency_values,
                layout,
                C6_U1_INDEX as usize,
                values,
            )?;
            add_private_value(
                claims,
                consistency_values,
                layout,
                C6_U2_INDEX as usize,
                values,
            )?;
        }
        b"s4-ecdsa-c11-final-add" => {
            for index in [
                C11_AX_INDEX,
                C11_AY_INDEX,
                C11_BX_INDEX,
                C11_BY_INDEX,
                C11_RX_INDEX,
                C11_RY_INDEX,
                C11_DENOM_INV_INDEX,
            ] {
                add_private_value(claims, consistency_values, layout, index as usize, values)?;
            }
        }
        b"s4-ecdsa-c12-final-on-curve" => {
            for point in [
                C12_ACCUMULATOR_POINT_COUNT,
                C12_ACCUMULATOR_POINT_COUNT + 1,
                C12_FINAL_POINT_INDEX,
            ] {
                let x = C12_POINTS_START_INDEX as usize + point * 3;
                add_private_value(claims, consistency_values, layout, x, values)?;
                add_private_value(claims, consistency_values, layout, x + 1, values)?;
            }
        }
        b"s4-ecdsa-c13-slope-inverses" => {
            add_private_value(
                claims,
                consistency_values,
                layout,
                C13_DENOMS_START_INDEX as usize + C13_FINAL_ADD_DENOM_INDEX,
                values,
            )?;
            add_private_value(
                claims,
                consistency_values,
                layout,
                C13_INVS_START_INDEX as usize + C13_FINAL_ADD_DENOM_INDEX,
                values,
            )?;
        }
        b"s4-ecdsa-c14-c15-final-check" => {
            add_c14_public_claims(claims, projection, layout)?;
            add_private_value(
                claims,
                consistency_values,
                layout,
                C14_RX_INDEX as usize,
                values,
            )?;
        }
        _ => {}
    }
    Ok(())
}

fn add_c1_public_claims(
    claims: &mut Vec<LigeroLinearClaim>,
    projection: &EcdsaPublicProjection,
    layout: &BundleCircuitLayout,
) -> Result<(), ImplementedCircuitProofError> {
    for (offset, bytes) in [
        projection.z,
        projection.r,
        projection.s,
        projection.qx,
        projection.qy,
    ]
    .into_iter()
    .enumerate()
    .filter_map(|(offset, bytes)| bytes.map(|bytes| (offset, bytes)))
    {
        let value =
            Fp::from_bytes_be(bytes).ok_or(ImplementedCircuitProofError::InputBindingRejected)?;
        add_fixed_claim(
            claims,
            layout.input_offset,
            layout.input_len,
            C1_VALUES_START_INDEX as usize + offset,
            value,
        );
    }
    Ok(())
}

fn add_c2_public_claims(
    claims: &mut Vec<LigeroLinearClaim>,
    projection: &EcdsaPublicProjection,
    layout: &BundleCircuitLayout,
) -> Result<(), ImplementedCircuitProofError> {
    for (index, bytes) in [
        (C2_R_INDEX as usize, projection.r),
        (C2_S_INDEX as usize, projection.s),
        (C2_QX_INDEX as usize, projection.qx),
        (C2_QY_INDEX as usize, projection.qy),
    ]
    .into_iter()
    .filter_map(|(index, bytes)| bytes.map(|bytes| (index, bytes)))
    {
        let value =
            Fp::from_bytes_be(bytes).ok_or(ImplementedCircuitProofError::InputBindingRejected)?;
        add_fixed_claim(claims, layout.input_offset, layout.input_len, index, value);
    }
    Ok(())
}

fn add_c3_public_claims(
    claims: &mut Vec<LigeroLinearClaim>,
    projection: &EcdsaPublicProjection,
    layout: &BundleCircuitLayout,
) -> Result<(), ImplementedCircuitProofError> {
    for (index, bytes) in [
        (C3_Z_INDEX as usize, projection.z),
        (C3_R_INDEX as usize, projection.r),
        (C3_S_INDEX as usize, projection.s),
    ]
    .into_iter()
    .filter_map(|(index, bytes)| bytes.map(|bytes| (index, bytes)))
    {
        let value =
            Fp::from_bytes_be(bytes).ok_or(ImplementedCircuitProofError::InputBindingRejected)?;
        add_fixed_claim(claims, layout.input_offset, layout.input_len, index, value);
    }
    Ok(())
}

fn add_c14_public_claims(
    claims: &mut Vec<LigeroLinearClaim>,
    projection: &EcdsaPublicProjection,
    layout: &BundleCircuitLayout,
) -> Result<(), ImplementedCircuitProofError> {
    if let Some(r) = projection.r {
        let signature_r =
            Fp::from_bytes_be(r).ok_or(ImplementedCircuitProofError::InputBindingRejected)?;
        add_fixed_claim(
            claims,
            layout.input_offset,
            layout.input_len,
            C14_SIGNATURE_R_INDEX as usize,
            signature_r,
        );
    }
    Ok(())
}

fn add_private_value(
    claims: &mut Vec<LigeroLinearClaim>,
    consistency_values: &mut Vec<Fp>,
    layout: &BundleCircuitLayout,
    index: usize,
    values: &[Fp],
) -> Result<Fp, ImplementedCircuitProofError> {
    let value = values
        .get(index)
        .copied()
        .ok_or(ImplementedCircuitProofError::InputClaimOpeningRejected)?;
    consistency_values.push(value);
    add_fixed_claim(claims, layout.input_offset, layout.input_len, index, value);
    Ok(value)
}

fn add_mac_half_public_const_claim(
    claims: &mut Vec<LigeroLinearClaim>,
    layout: &BundleCircuitLayout,
    half: usize,
) {
    let offset = mac_batch_half_group_a_input_offset(half);
    add_fixed_claim(
        claims,
        layout.input_offset,
        layout.input_len,
        offset + MAC_HALF_CONST_ONE_INDEX,
        Fp::ONE,
    );
}

fn add_mac_half_x_recompose_claim(
    claims: &mut Vec<LigeroLinearClaim>,
    consistency_values: &mut Vec<Fp>,
    layout: &BundleCircuitLayout,
    values: &[Fp],
    half: usize,
) -> Result<Fp, ImplementedCircuitProofError> {
    let offset = mac_batch_half_group_a_input_offset(half);
    let value = mac_half_x_recomposed_value(values, offset)?;
    let (point, scale) = mac_half_x_recompose_claim_point();
    consistency_values.push(value);
    claims.push(LigeroLinearClaim {
        offset: layout.input_offset + offset + MAC_HALF_X_BITS_START,
        len: GF128_BITS,
        point,
        value: value * scale,
    });
    Ok(value)
}

fn take_mac_half_x_recompose_claim(
    claims: &mut Vec<LigeroLinearClaim>,
    bundle: &ImplementedCircuitBundle,
    cursor: &mut usize,
    layout: &BundleCircuitLayout,
    half: usize,
) -> Result<Fp, ImplementedCircuitProofError> {
    let value = bundle
        .consistency_claim_values
        .get(*cursor)
        .copied()
        .ok_or(ImplementedCircuitProofError::InputClaimOpeningRejected)?;
    *cursor += 1;
    let (point, scale) = mac_half_x_recompose_claim_point();
    let offset = mac_batch_half_group_a_input_offset(half);
    claims.push(LigeroLinearClaim {
        offset: layout.input_offset + offset + MAC_HALF_X_BITS_START,
        len: GF128_BITS,
        point,
        value: value * scale,
    });
    Ok(value)
}

fn mac_half_x_recomposed_value(
    values: &[Fp],
    offset: usize,
) -> Result<Fp, ImplementedCircuitProofError> {
    let mut out = Fp::ZERO;
    let mut power = Fp::ONE;
    for bit in 0..GF128_BITS {
        let value = values
            .get(offset + MAC_HALF_X_BITS_START + bit)
            .copied()
            .ok_or(ImplementedCircuitProofError::InputClaimOpeningRejected)?;
        out = out + power * value;
        power = power + power;
    }
    Ok(out)
}

fn mac_half_x_recompose_claim_point() -> (Vec<Fp>, Fp) {
    let mut point = Vec::with_capacity(GF128_BITS.ilog2() as usize);
    let mut scale = Fp::ONE;
    for bit in 0..GF128_BITS.ilog2() {
        let mut ratio = Fp::ONE;
        for _ in 0..(1usize << bit) {
            ratio = ratio + ratio;
        }
        let denom_inv = (Fp::ONE + ratio)
            .inverse()
            .expect("1 + 2^j is non-zero in Fp256");
        point.push(ratio * denom_inv);
        scale = scale * denom_inv;
    }
    (point, scale)
}

fn take_private_value(
    claims: &mut Vec<LigeroLinearClaim>,
    bundle: &ImplementedCircuitBundle,
    cursor: &mut usize,
    layout: &BundleCircuitLayout,
    index: usize,
) -> Result<Fp, ImplementedCircuitProofError> {
    let value = bundle
        .consistency_claim_values
        .get(*cursor)
        .copied()
        .ok_or(ImplementedCircuitProofError::InputClaimOpeningRejected)?;
    *cursor += 1;
    add_fixed_claim(claims, layout.input_offset, layout.input_len, index, value);
    Ok(value)
}

fn take_c12_boundary_values(
    claims: &mut Vec<LigeroLinearClaim>,
    bundle: &ImplementedCircuitBundle,
    cursor: &mut usize,
    layout: &BundleCircuitLayout,
) -> Result<C12BoundaryValues, ImplementedCircuitProofError> {
    let mut read_point = |point: usize| {
        let x = C12_POINTS_START_INDEX as usize + point * 3;
        Ok((
            take_private_value(claims, bundle, cursor, layout, x)?,
            take_private_value(claims, bundle, cursor, layout, x + 1)?,
        ))
    };
    Ok(C12BoundaryValues {
        corrected_endpoints: (
            read_point(C12_ACCUMULATOR_POINT_COUNT)?,
            read_point(C12_ACCUMULATOR_POINT_COUNT + 1)?,
        ),
        final_point: read_point(C12_FINAL_POINT_INDEX)?,
    })
}

fn take_c13_boundary_values(
    claims: &mut Vec<LigeroLinearClaim>,
    bundle: &ImplementedCircuitBundle,
    cursor: &mut usize,
    layout: &BundleCircuitLayout,
) -> Result<C13BoundaryValues, ImplementedCircuitProofError> {
    Ok(C13BoundaryValues {
        final_add_denominator: take_private_value(
            claims,
            bundle,
            cursor,
            layout,
            C13_DENOMS_START_INDEX as usize + C13_FINAL_ADD_DENOM_INDEX,
        )?,
        final_add_inverse: take_private_value(
            claims,
            bundle,
            cursor,
            layout,
            C13_INVS_START_INDEX as usize + C13_FINAL_ADD_DENOM_INDEX,
        )?,
    })
}

fn mdoc_p4b_take_ecdsa_claims(
    claims: &mut Vec<LigeroLinearClaim>,
    bundle: &ImplementedCircuitBundle,
    cursor: &mut usize,
    layout: &BundleCircuitLayout,
    projection: &EcdsaPublicProjection,
    state: &mut MdocP4bEcdsaConsistency,
    label: &[u8],
) -> Result<(), ImplementedCircuitProofError> {
    match label {
        b"s4-ecdsa-c1-input-limbs" => add_c1_public_claims(claims, projection, layout)?,
        b"s4-ecdsa-c2-canonicality" => {
            add_c2_public_claims(claims, projection, layout)?;
        }
        b"s4-ecdsa-c3-c5-scalar-setup" => {
            add_c3_public_claims(claims, projection, layout)?;
            state.u_scalars_from_c3 = Some((
                take_private_value(claims, bundle, cursor, layout, C3_U1_INDEX as usize)?,
                take_private_value(claims, bundle, cursor, layout, C3_U2_INDEX as usize)?,
            ));
        }
        b"s4-ecdsa-c6-scalar-bits" => {
            state.u_scalars_from_c6 = Some((
                take_private_value(claims, bundle, cursor, layout, C6_U1_INDEX as usize)?,
                take_private_value(claims, bundle, cursor, layout, C6_U2_INDEX as usize)?,
            ));
        }
        b"s4-ecdsa-c11-final-add" => {
            let ax = take_private_value(claims, bundle, cursor, layout, C11_AX_INDEX as usize)?;
            let ay = take_private_value(claims, bundle, cursor, layout, C11_AY_INDEX as usize)?;
            let bx = take_private_value(claims, bundle, cursor, layout, C11_BX_INDEX as usize)?;
            let by = take_private_value(claims, bundle, cursor, layout, C11_BY_INDEX as usize)?;
            let rx = take_private_value(claims, bundle, cursor, layout, C11_RX_INDEX as usize)?;
            let ry = take_private_value(claims, bundle, cursor, layout, C11_RY_INDEX as usize)?;
            let denom_inv =
                take_private_value(claims, bundle, cursor, layout, C11_DENOM_INV_INDEX as usize)?;
            state.add_inputs_from_c11 = Some(((ax, ay), (bx, by)));
            state.denom_inv_from_c11 = Some(denom_inv);
            state.final_from_c11 = Some((rx, ry));
        }
        b"s4-ecdsa-c12-final-on-curve" => {
            state.c12_boundaries = Some(take_c12_boundary_values(claims, bundle, cursor, layout)?);
        }
        b"s4-ecdsa-c13-slope-inverses" => {
            state.c13_boundary_values =
                Some(take_c13_boundary_values(claims, bundle, cursor, layout)?);
        }
        b"s4-ecdsa-c14-c15-final-check" => {
            add_c14_public_claims(claims, projection, layout)?;
            state.rx_from_c14 = Some(take_private_value(
                claims,
                bundle,
                cursor,
                layout,
                C14_RX_INDEX as usize,
            )?);
        }
        _ => {}
    }
    Ok(())
}

fn verify_mdoc_p4b_native_mac_consistency(
    issuer_z: Option<Fp>,
    device_qx: Option<Fp>,
    device_qy: Option<Fp>,
    mac_halves: [Option<Fp>; MDOC_P4B_MAC_HALF_COUNT],
) -> Result<(), ImplementedCircuitProofError> {
    let read = |index: usize| {
        mac_halves[index].ok_or(ImplementedCircuitProofError::CrossFamilyBindingRejected)
    };
    let issuer_z = issuer_z.ok_or(ImplementedCircuitProofError::CrossFamilyBindingRejected)?;
    let device_qx = device_qx.ok_or(ImplementedCircuitProofError::CrossFamilyBindingRejected)?;
    let device_qy = device_qy.ok_or(ImplementedCircuitProofError::CrossFamilyBindingRejected)?;

    if read(0)? + two_pow_128() * read(1)? != issuer_z {
        return Err(ImplementedCircuitProofError::CrossFamilyBindingRejected);
    }
    if read(2)? + two_pow_128() * read(3)? != device_qx {
        return Err(ImplementedCircuitProofError::CrossFamilyBindingRejected);
    }
    if read(4)? + two_pow_128() * read(5)? != device_qy {
        return Err(ImplementedCircuitProofError::CrossFamilyBindingRejected);
    }
    Ok(())
}

fn add_fixed_claim(
    claims: &mut Vec<LigeroLinearClaim>,
    offset: usize,
    len: usize,
    index: usize,
    value: Fp,
) {
    claims.push(LigeroLinearClaim {
        offset,
        len,
        point: fixed_point(len, index),
        value,
    });
}

fn fixed_point(len: usize, index: usize) -> Vec<Fp> {
    debug_assert!(index < len);
    let vars = len.next_power_of_two().ilog2() as usize;
    (0..vars)
        .map(|bit| {
            if ((index >> bit) & 1) == 1 {
                Fp::ONE
            } else {
                Fp::ZERO
            }
        })
        .collect()
}

fn pad_claim_point(
    pad_offset: usize,
    pad_len: usize,
    root: [u8; 32],
    transcript_seed: TranscriptSeed,
) -> Vec<Fp> {
    let vars = pad_len.next_power_of_two().ilog2() as usize;
    let mut channel = CoprocessorChannel::from_seed(transcript_seed, COPROCESSOR_TRANSCRIPT_DOMAIN);
    channel.mix_bytes(IMPLEMENTED_BUNDLE_LIGERO_LABEL);
    channel.mix_bytes(&root);
    channel.mix_bytes(b"s4-ligero-pad-claim-point");
    channel.mix_bytes(&(pad_offset as u64).to_be_bytes());
    channel.mix_bytes(&(pad_len as u64).to_be_bytes());
    (0..vars).map(|_| channel.draw_fp()).collect()
}

fn implemented_circuit_instances(
    input: &EcdsaInput,
    witness: &Witness,
) -> Result<Vec<ProverCircuitInstance>, WitnessError> {
    if witness.values.len() != LAYOUT_LEN {
        return Err(WitnessError::LayoutMismatch);
    }
    Ok(vec![
        ProverCircuitInstance {
            label: b"s4-ecdsa-c1-input-limbs",
            slot: LayoutSlot::InputLimbs,
            circuit: build_c1_input_limbs_circuit().expect("static C1 circuit is valid"),
            input: c1_input_limbs_input(input, witness)?,
        },
        ProverCircuitInstance {
            label: b"s4-ecdsa-c2-canonicality",
            slot: LayoutSlot::InputLimbs,
            circuit: build_c2_canonicality_circuit().expect("static C2 circuit is valid"),
            input: c2_canonicality_input(input)?,
        },
        ProverCircuitInstance {
            label: b"s4-ecdsa-c3-c5-scalar-setup",
            slot: LayoutSlot::ScalarInverses,
            circuit: build_c3_c5_scalar_setup_circuit().expect("static C3-C5 circuit is valid"),
            input: c3_c5_scalar_setup_input(input, witness)?,
        },
        ProverCircuitInstance {
            label: b"s4-ecdsa-c6-scalar-bits",
            slot: LayoutSlot::ScalarBits,
            circuit: build_c6_scalar_bits_circuit().expect("static C6 circuit is valid"),
            input: c6_scalar_bits_input(witness)?,
        },
        // C9/C10 accumulator on-curve checks ride the C12 family: its input
        // committed the same 512 accumulator points a second time (plus the
        // corrected endpoints and final point) and its circuit runs the same
        // per-point curve equations, so a separate C9/C10 instance re-proved a
        // strict subset over a duplicate committed region (WO-E1b dedup).
        ProverCircuitInstance {
            label: b"s4-ecdsa-c11-final-add",
            slot: LayoutSlot::FinalPoint,
            circuit: build_c11_final_add_circuit().expect("static C11 circuit is valid"),
            input: c11_final_add_input(witness)?,
        },
        ProverCircuitInstance {
            label: b"s4-ecdsa-c12-final-on-curve",
            slot: LayoutSlot::FinalPoint,
            circuit: build_c12_on_curve_circuit().expect("static C12 circuit is valid"),
            input: c12_witness_on_curve_input(witness)?,
        },
        ProverCircuitInstance {
            label: b"s4-ecdsa-c13-slope-inverses",
            slot: LayoutSlot::SlopeInverses,
            circuit: build_c13_slope_inverses_circuit().expect("static C13 circuit is valid"),
            input: c13_slope_inverses_input(input, witness)?,
        },
        ProverCircuitInstance {
            label: b"s4-ecdsa-c14-c15-final-check",
            slot: LayoutSlot::FinalReduction,
            circuit: build_c14_c15_final_check_circuit().expect("static C14/C15 circuit is valid"),
            input: c14_c15_final_check_input(input, witness)?,
        },
    ])
}

fn implemented_circuit_verifier_instances() -> Result<Vec<VerifierCircuitInstance>, CircuitError> {
    Ok(vec![
        VerifierCircuitInstance {
            label: b"s4-ecdsa-c1-input-limbs",
            circuit: build_c1_input_limbs_circuit()?,
        },
        VerifierCircuitInstance {
            label: b"s4-ecdsa-c2-canonicality",
            circuit: build_c2_canonicality_circuit()?,
        },
        VerifierCircuitInstance {
            label: b"s4-ecdsa-c3-c5-scalar-setup",
            circuit: build_c3_c5_scalar_setup_circuit()?,
        },
        VerifierCircuitInstance {
            label: b"s4-ecdsa-c6-scalar-bits",
            circuit: build_c6_scalar_bits_circuit()?,
        },
        VerifierCircuitInstance {
            label: b"s4-ecdsa-c11-final-add",
            circuit: build_c11_final_add_circuit()?,
        },
        VerifierCircuitInstance {
            label: b"s4-ecdsa-c12-final-on-curve",
            circuit: build_c12_on_curve_circuit()?,
        },
        VerifierCircuitInstance {
            label: b"s4-ecdsa-c13-slope-inverses",
            circuit: build_c13_slope_inverses_circuit()?,
        },
        VerifierCircuitInstance {
            label: b"s4-ecdsa-c14-c15-final-check",
            circuit: build_c14_c15_final_check_circuit()?,
        },
    ])
}

pub fn build_mac_half_circuit(av: &Gf128, tag: &Gf128) -> Result<Circuit, CircuitError> {
    let av_bits = bytes_to_bits(av);
    let tag_bits = bytes_to_bits(tag);
    let local_constraints = mac_half_local_constraint_count();
    let mut layers = Vec::new();
    layers.push(mac_half_final_layer(local_constraints)?);
    let mut block_size = 1usize;
    while block_size < MAC_HALF_TREE_BLOCK_SIZE {
        layers.push(mac_half_reduce_tree_layer(
            block_size * 2,
            local_constraints,
        )?);
        block_size *= 2;
    }
    layers.push(mac_half_product_reduce_layer(&tag_bits, local_constraints)?);
    layers.push(mac_half_input_layer(&av_bits)?);
    Circuit::new(layers)
}

fn build_mac_batch_circuit(av: &Gf128, tags: &[Gf128]) -> Result<Circuit, CircuitError> {
    if tags.len() != MDOC_P4B_MAC_HALF_COUNT {
        return Err(CircuitError::InvalidTermIndex);
    }
    let av_bits = bytes_to_bits(av);
    let tag_bits: [[bool; GF128_BITS]; MDOC_P4B_MAC_HALF_COUNT] =
        std::array::from_fn(|index| bytes_to_bits(&tags[index]));
    let local_constraints = mac_half_local_constraint_count();
    let mut layers = Vec::new();
    layers.push(mac_batch_final_layer(local_constraints)?);
    let mut block_size = 1usize;
    while block_size < MAC_HALF_TREE_BLOCK_SIZE {
        layers.push(mac_batch_reduce_tree_layer(
            block_size * 2,
            local_constraints,
        )?);
        block_size *= 2;
    }
    layers.push(mac_batch_product_reduce_layer(
        &tag_bits,
        local_constraints,
    )?);
    layers.push(mac_batch_input_layer(&av_bits)?);
    Circuit::new(layers)
}

pub fn mac_half_input(ap: &Gf128, x: &Gf128) -> Result<Vec<Fp>, WitnessError> {
    mac_half_input_with_av(ap, &[0u8; 16], x)
}

pub fn mac_half_input_with_av(ap: &Gf128, av: &Gf128, x: &Gf128) -> Result<Vec<Fp>, WitnessError> {
    let mut input = vec![Fp::ZERO; 1usize << MAC_HALF_INPUT_LOG_SIZE];
    let group_a = mac_half_group_a_input(ap, x)?;
    input[..group_a.len()].copy_from_slice(&group_a);
    let tag = gf128_tag(ap, av, x);
    let group_b = mac_half_group_b_input(ap, av, x, &tag)?;
    input[MAC_HALF_GROUP_B_INPUT_START..MAC_HALF_GROUP_B_INPUT_START + group_b.len()]
        .copy_from_slice(&group_b);
    Ok(input)
}

fn mac_half_group_a_input(ap: &Gf128, x: &Gf128) -> Result<Vec<Fp>, WitnessError> {
    let ap_bits = bytes_to_bits(ap);
    let x_bits = bytes_to_bits(x);
    let mut input = vec![Fp::ZERO; 1usize << MAC_HALF_GROUP_A_INPUT_LOG_SIZE];

    input[MAC_HALF_CONST_ONE_INDEX] = Fp::ONE;
    for bit in 0..GF128_BITS {
        input[MAC_HALF_X_BITS_START + bit] = fp_bit(x_bits[bit]);
        input[MAC_HALF_AP_BITS_START + bit] = fp_bit(ap_bits[bit]);
    }
    Ok(input)
}

fn mac_half_group_b_input(
    ap: &Gf128,
    av: &Gf128,
    x: &Gf128,
    tag: &Gf128,
) -> Result<Vec<Fp>, WitnessError> {
    let ap_bits = bytes_to_bits(ap);
    let av_bits = bytes_to_bits(av);
    let x_bits = bytes_to_bits(x);
    let tag_bits = bytes_to_bits(tag);
    let q_bits = mac_half_q_witness(&ap_bits, &av_bits, &x_bits, &tag_bits);
    let mut input = vec![Fp::ZERO; MAC_HALF_GROUP_B_USED_INPUTS];
    for bit in 0..GF128_BITS {
        for q_bit in 0..MAC_HALF_PARITY_Q_BITS {
            input[mac_half_group_b_q_bit_index(bit, q_bit)] = fp_bit(q_bits[bit][q_bit]);
        }
    }
    Ok(input)
}

fn mac_batch_group_a_input(
    mac_key_shares: &MdocP4bMacKeyShares,
    mac_values: &[Gf128; MDOC_P4B_MAC_HALF_COUNT],
) -> Result<Vec<Fp>, WitnessError> {
    let mut input = vec![Fp::ZERO; 1usize << MAC_BATCH_GROUP_A_INPUT_LOG_SIZE];
    for half in 0..MDOC_P4B_MAC_HALF_COUNT {
        let offset = mac_batch_half_group_a_input_offset(half);
        let half_input = mac_half_group_a_input(&mac_key_shares.0[half], &mac_values[half])?;
        input[offset..offset + half_input.len()].copy_from_slice(&half_input);
    }
    Ok(input)
}

fn mac_batch_group_b_input(
    mac_key_shares: &MdocP4bMacKeyShares,
    av: &Gf128,
    mac_values: &[Gf128; MDOC_P4B_MAC_HALF_COUNT],
    mac_tags: &[Gf128],
) -> Result<Vec<Fp>, WitnessError> {
    if mac_tags.len() != MDOC_P4B_MAC_HALF_COUNT {
        return Err(WitnessError::LayoutMismatch);
    }
    let mut input = vec![Fp::ZERO; 1usize << MAC_BATCH_GROUP_B_INPUT_LOG_SIZE];
    for half in 0..MDOC_P4B_MAC_HALF_COUNT {
        let offset = mac_batch_half_group_b_input_offset(half);
        let half_input = mac_half_group_b_input(
            &mac_key_shares.0[half],
            av,
            &mac_values[half],
            &mac_tags[half],
        )?;
        input[offset..offset + half_input.len()].copy_from_slice(&half_input);
    }
    Ok(input)
}

fn mac_batch_input_with_av(
    mac_key_shares: &MdocP4bMacKeyShares,
    av: &Gf128,
    mac_values: &[Gf128; MDOC_P4B_MAC_HALF_COUNT],
    mac_tags: &[Gf128],
) -> Result<Vec<Fp>, WitnessError> {
    let mut input = vec![Fp::ZERO; 1usize << MAC_BATCH_INPUT_LOG_SIZE];
    let group_a = mac_batch_group_a_input(mac_key_shares, mac_values)?;
    input[..group_a.len()].copy_from_slice(&group_a);
    let group_b = mac_batch_group_b_input(mac_key_shares, av, mac_values, mac_tags)?;
    input[MAC_BATCH_GROUP_B_INPUT_START..MAC_BATCH_GROUP_B_INPUT_START + group_b.len()]
        .copy_from_slice(&group_b);
    Ok(input)
}

pub fn gf128_halves_from_be32(value: [u8; 32]) -> [Gf128; 2] {
    let mut lo = [0u8; 16];
    let mut hi = [0u8; 16];
    for index in 0..16 {
        lo[index] = value[31 - index];
        hi[index] = value[15 - index];
    }
    [lo, hi]
}

pub fn recompose_gf128_halves(lo: &Gf128, hi: &Gf128) -> Fp {
    let lo_bits = bytes_to_bits(lo);
    let hi_bits = bytes_to_bits(hi);
    fp_from_bits_le(&lo_bits) + two_pow_128() * fp_from_bits_le(&hi_bits)
}

fn mac_half_input_layer(av_bits: &[bool; GF128_BITS]) -> Result<Layer, CircuitError> {
    let av_fold = av_linear_fold_slots(av_bits);
    let mut terms = Vec::with_capacity(28_000);
    add_linear(
        &mut terms,
        mac_half_tree_const_index(),
        MAC_HALF_CONST_ONE_INDEX,
        Fp::ONE,
    );
    for ap_bit in 0..GF128_BITS {
        for x_bit in 0..GF128_BITS {
            add_quadratic(
                &mut terms,
                mac_half_product_coeff_index(ap_bit + x_bit),
                MAC_HALF_AP_BITS_START + ap_bit,
                MAC_HALF_X_BITS_START + x_bit,
                Fp::ONE,
            );
        }
    }
    for (out_bit, leaves) in av_fold.iter().enumerate() {
        for (x_bit, present) in leaves.iter().copied().enumerate() {
            if present {
                add_linear(
                    &mut terms,
                    mac_half_tree_l_index(out_bit),
                    MAC_HALF_X_BITS_START + x_bit,
                    Fp::ONE,
                );
            }
        }
    }
    for bit in 0..GF128_BITS {
        for q_bit in 0..MAC_HALF_PARITY_Q_BITS {
            add_linear(
                &mut terms,
                mac_half_tree_qsum_index(bit),
                mac_half_q_bit_index(bit, q_bit),
                Fp::from_u64(1u64 << q_bit),
            );
        }
    }
    let mut local = mac_half_tree_local_start();
    for bit in 0..GF128_BITS {
        add_bool_constraint(&mut terms, local, MAC_HALF_X_BITS_START + bit);
        local += 1;
        add_bool_constraint(&mut terms, local, MAC_HALF_AP_BITS_START + bit);
        local += 1;
        for q_bit in 0..MAC_HALF_PARITY_Q_BITS {
            add_bool_constraint(&mut terms, local, mac_half_q_bit_index(bit, q_bit));
            local += 1;
        }
    }
    debug_assert_eq!(
        local,
        mac_half_tree_local_start() + MAC_HALF_BOOL_CONSTRAINTS
    );

    Layer::new(MAC_HALF_TREE_LOG_SIZE, MAC_HALF_INPUT_LOG_SIZE, terms)
}

fn mac_batch_input_layer(av_bits: &[bool; GF128_BITS]) -> Result<Layer, CircuitError> {
    let av_fold = av_linear_fold_slots(av_bits);
    let mut terms = Vec::with_capacity(MDOC_P4B_MAC_HALF_COUNT * 28_000);
    for half in 0..MDOC_P4B_MAC_HALF_COUNT {
        let input_offset = mac_batch_half_group_a_input_offset(half);
        let b_input_offset = mac_batch_half_group_b_full_input_offset(half);
        add_linear(
            &mut terms,
            mac_batch_tree_const_index(half),
            input_offset + MAC_HALF_CONST_ONE_INDEX,
            Fp::ONE,
        );
        for ap_bit in 0..GF128_BITS {
            for x_bit in 0..GF128_BITS {
                add_quadratic(
                    &mut terms,
                    mac_batch_product_coeff_index(half, ap_bit + x_bit),
                    input_offset + MAC_HALF_AP_BITS_START + ap_bit,
                    input_offset + MAC_HALF_X_BITS_START + x_bit,
                    Fp::ONE,
                );
            }
        }
        for (out_bit, leaves) in av_fold.iter().enumerate() {
            for (x_bit, present) in leaves.iter().copied().enumerate() {
                if present {
                    add_linear(
                        &mut terms,
                        mac_batch_tree_l_index(half, out_bit),
                        input_offset + MAC_HALF_X_BITS_START + x_bit,
                        Fp::ONE,
                    );
                }
            }
        }
        for bit in 0..GF128_BITS {
            for q_bit in 0..MAC_HALF_PARITY_Q_BITS {
                add_linear(
                    &mut terms,
                    mac_batch_tree_qsum_index(half, bit),
                    b_input_offset + mac_half_group_b_q_bit_index(bit, q_bit),
                    Fp::from_u64(1u64 << q_bit),
                );
            }
        }
        let mut local = mac_batch_tree_local_start(half);
        for bit in 0..GF128_BITS {
            add_bool_constraint(
                &mut terms,
                local,
                input_offset + MAC_HALF_X_BITS_START + bit,
            );
            local += 1;
            add_bool_constraint(
                &mut terms,
                local,
                input_offset + MAC_HALF_AP_BITS_START + bit,
            );
            local += 1;
            for q_bit in 0..MAC_HALF_PARITY_Q_BITS {
                add_bool_constraint(
                    &mut terms,
                    local,
                    b_input_offset + mac_half_group_b_q_bit_index(bit, q_bit),
                );
                local += 1;
            }
        }
        debug_assert_eq!(
            local,
            mac_batch_tree_local_start(half) + MAC_HALF_BOOL_CONSTRAINTS
        );
    }

    Layer::new(MAC_BATCH_TREE_LOG_SIZE, MAC_BATCH_INPUT_LOG_SIZE, terms)
}

fn mac_half_product_reduce_layer(
    tag_bits: &[bool; GF128_BITS],
    local_constraints: usize,
) -> Result<Layer, CircuitError> {
    let mut terms =
        Vec::with_capacity(GF128_BITS * 10 + MAC_HALF_PRODUCT_COEFFS * 3 + local_constraints);
    add_linear(
        &mut terms,
        mac_half_tree_const_index(),
        mac_half_tree_const_index(),
        Fp::ONE,
    );
    for bit in 0..GF128_BITS {
        let tag_pin = mac_half_tree_local_start() + MAC_HALF_BOOL_CONSTRAINTS + bit;
        for power in 0..MAC_HALF_PRODUCT_COEFFS {
            if monomial_reduction_bits(power).contains(&bit) {
                add_linear(
                    &mut terms,
                    tag_pin,
                    mac_half_product_coeff_index(power),
                    Fp::ONE,
                );
            }
        }
        add_linear(&mut terms, tag_pin, mac_half_tree_l_index(bit), Fp::ONE);
        add_linear(
            &mut terms,
            tag_pin,
            mac_half_tree_qsum_index(bit),
            -Fp::from_u64(2),
        );
        if tag_bits[bit] {
            add_constant(&mut terms, tag_pin, -Fp::ONE);
        }
    }
    for index in 0..local_constraints {
        add_linear(
            &mut terms,
            mac_half_tree_local_start() + index,
            mac_half_tree_local_start() + index,
            Fp::ONE,
        );
    }

    Layer::new(MAC_HALF_TREE_LOG_SIZE, MAC_HALF_TREE_LOG_SIZE, terms)
}

fn mac_batch_product_reduce_layer(
    tag_bits: &[[bool; GF128_BITS]; MDOC_P4B_MAC_HALF_COUNT],
    local_constraints: usize,
) -> Result<Layer, CircuitError> {
    let mut terms = Vec::with_capacity(
        MDOC_P4B_MAC_HALF_COUNT
            * (GF128_BITS * 10 + MAC_HALF_PRODUCT_COEFFS * 3 + local_constraints),
    );
    for half in 0..MDOC_P4B_MAC_HALF_COUNT {
        add_linear(
            &mut terms,
            mac_batch_tree_const_index(half),
            mac_batch_tree_const_index(half),
            Fp::ONE,
        );
        for bit in 0..GF128_BITS {
            let tag_pin = mac_batch_tree_local_start(half) + MAC_HALF_BOOL_CONSTRAINTS + bit;
            for power in 0..MAC_HALF_PRODUCT_COEFFS {
                if monomial_reduction_bits(power).contains(&bit) {
                    add_linear(
                        &mut terms,
                        tag_pin,
                        mac_batch_product_coeff_index(half, power),
                        Fp::ONE,
                    );
                }
            }
            add_linear(
                &mut terms,
                tag_pin,
                mac_batch_tree_l_index(half, bit),
                Fp::ONE,
            );
            add_linear(
                &mut terms,
                tag_pin,
                mac_batch_tree_qsum_index(half, bit),
                -Fp::from_u64(2),
            );
            if tag_bits[half][bit] {
                add_constant(&mut terms, tag_pin, -Fp::ONE);
            }
        }
        for index in 0..local_constraints {
            add_linear(
                &mut terms,
                mac_batch_tree_local_start(half) + index,
                mac_batch_tree_local_start(half) + index,
                Fp::ONE,
            );
        }
    }

    Layer::new(MAC_BATCH_TREE_LOG_SIZE, MAC_BATCH_TREE_LOG_SIZE, terms)
}

fn mac_half_reduce_tree_layer(
    previous_block_size: usize,
    local_constraints: usize,
) -> Result<Layer, CircuitError> {
    debug_assert!(previous_block_size.is_power_of_two());
    debug_assert!(previous_block_size >= 2);
    let next_block_size = previous_block_size / 2;
    let mut terms = Vec::with_capacity(GF128_BITS * next_block_size * 4 + local_constraints);
    add_linear(
        &mut terms,
        mac_half_tree_const_index(),
        mac_half_tree_const_index(),
        Fp::ONE,
    );
    for bit in 0..GF128_BITS {
        for slot in 0..next_block_size {
            add_xor_value(
                &mut terms,
                mac_half_tree_value_index(bit, slot),
                mac_half_tree_value_index(bit, 2 * slot),
                mac_half_tree_value_index(bit, 2 * slot + 1),
                mac_half_tree_const_index(),
            );
        }
    }
    for index in 0..local_constraints {
        add_linear(
            &mut terms,
            mac_half_tree_local_start() + index,
            mac_half_tree_local_start() + index,
            Fp::ONE,
        );
    }

    Layer::new(MAC_HALF_TREE_LOG_SIZE, MAC_HALF_TREE_LOG_SIZE, terms)
}

fn mac_batch_reduce_tree_layer(
    previous_block_size: usize,
    local_constraints: usize,
) -> Result<Layer, CircuitError> {
    debug_assert!(previous_block_size.is_power_of_two());
    debug_assert!(previous_block_size >= 2);
    let next_block_size = previous_block_size / 2;
    let mut terms = Vec::with_capacity(
        MDOC_P4B_MAC_HALF_COUNT * (GF128_BITS * next_block_size * 4 + local_constraints),
    );
    for half in 0..MDOC_P4B_MAC_HALF_COUNT {
        add_linear(
            &mut terms,
            mac_batch_tree_const_index(half),
            mac_batch_tree_const_index(half),
            Fp::ONE,
        );
        for bit in 0..GF128_BITS {
            for slot in 0..next_block_size {
                add_xor_value(
                    &mut terms,
                    mac_batch_tree_value_index(half, bit, slot),
                    mac_batch_tree_value_index(half, bit, 2 * slot),
                    mac_batch_tree_value_index(half, bit, 2 * slot + 1),
                    mac_batch_tree_const_index(half),
                );
            }
        }
        for index in 0..local_constraints {
            add_linear(
                &mut terms,
                mac_batch_tree_local_start(half) + index,
                mac_batch_tree_local_start(half) + index,
                Fp::ONE,
            );
        }
    }

    Layer::new(MAC_BATCH_TREE_LOG_SIZE, MAC_BATCH_TREE_LOG_SIZE, terms)
}

fn mac_half_final_layer(local_constraints: usize) -> Result<Layer, CircuitError> {
    let mut terms = Vec::with_capacity(local_constraints);
    for index in 0..local_constraints {
        add_linear(
            &mut terms,
            index,
            mac_half_tree_local_start() + index,
            Fp::ONE,
        );
    }

    Layer::new(MAC_HALF_INPUT_LOG_SIZE, MAC_HALF_TREE_LOG_SIZE, terms)
}

fn mac_batch_final_layer(local_constraints: usize) -> Result<Layer, CircuitError> {
    let mut terms = Vec::with_capacity(MDOC_P4B_MAC_HALF_COUNT * local_constraints);
    for half in 0..MDOC_P4B_MAC_HALF_COUNT {
        let output_offset = half * MAC_BATCH_OUTPUT_STRIDE;
        for index in 0..local_constraints {
            add_linear(
                &mut terms,
                output_offset + index,
                mac_batch_tree_local_start(half) + index,
                Fp::ONE,
            );
        }
    }

    Layer::new(MAC_BATCH_INPUT_LOG_SIZE, MAC_BATCH_TREE_LOG_SIZE, terms)
}

fn mac_half_local_constraint_count() -> usize {
    MAC_HALF_LOCAL_CONSTRAINTS
}

const fn mac_half_tree_width() -> usize {
    1 + MAC_HALF_PRODUCT_COEFFS + GF128_BITS + GF128_BITS + MAC_HALF_LOCAL_CONSTRAINTS
}

fn mac_half_q_bit_index(bit: usize, q_bit: usize) -> usize {
    debug_assert!(bit < GF128_BITS);
    debug_assert!(q_bit < MAC_HALF_PARITY_Q_BITS);
    MAC_HALF_Q_BITS_START + bit * MAC_HALF_PARITY_Q_BITS + q_bit
}

fn mac_half_group_b_q_bit_index(bit: usize, q_bit: usize) -> usize {
    debug_assert!(bit < GF128_BITS);
    debug_assert!(q_bit < MAC_HALF_PARITY_Q_BITS);
    bit * MAC_HALF_PARITY_Q_BITS + q_bit
}

fn mac_half_tree_const_index() -> usize {
    0
}

fn mac_half_product_coeff_index(power: usize) -> usize {
    debug_assert!(power < MAC_HALF_PRODUCT_COEFFS);
    1 + power
}

fn mac_half_tree_values_start() -> usize {
    1 + MAC_HALF_PRODUCT_COEFFS
}

fn mac_half_tree_l_index(bit: usize) -> usize {
    debug_assert!(bit < GF128_BITS);
    mac_half_tree_values_start() + bit
}

fn mac_half_tree_value_index(bit: usize, slot: usize) -> usize {
    debug_assert!(bit < GF128_BITS);
    debug_assert!(slot < MAC_HALF_TREE_BLOCK_SIZE);
    mac_half_tree_l_index(bit)
}

fn mac_half_tree_u_start() -> usize {
    mac_half_tree_values_start() + GF128_BITS
}

fn mac_half_tree_qsum_start() -> usize {
    mac_half_tree_u_start()
}

fn mac_half_tree_qsum_index(bit: usize) -> usize {
    debug_assert!(bit < GF128_BITS);
    mac_half_tree_qsum_start() + bit
}

fn mac_half_tree_local_start() -> usize {
    mac_half_tree_qsum_start() + GF128_BITS
}

fn mac_batch_half_group_a_input_offset(half: usize) -> usize {
    debug_assert!(half < MDOC_P4B_MAC_HALF_COUNT);
    half * MAC_BATCH_HALF_GROUP_A_INPUT_STRIDE
}

fn mac_batch_half_group_b_input_offset(half: usize) -> usize {
    debug_assert!(half < MDOC_P4B_MAC_HALF_COUNT);
    half * MAC_BATCH_HALF_GROUP_B_INPUT_STRIDE
}

fn mac_batch_half_group_b_full_input_offset(half: usize) -> usize {
    MAC_BATCH_GROUP_B_INPUT_START + mac_batch_half_group_b_input_offset(half)
}

fn mac_batch_tree_half_start(half: usize) -> usize {
    debug_assert!(half < MDOC_P4B_MAC_HALF_COUNT);
    half * MAC_BATCH_TREE_HALF_WIDTH
}

fn mac_batch_tree_const_index(half: usize) -> usize {
    mac_batch_tree_half_start(half)
}

fn mac_batch_product_coeff_index(half: usize, power: usize) -> usize {
    mac_batch_tree_half_start(half) + mac_half_product_coeff_index(power)
}

fn mac_batch_tree_value_index(half: usize, bit: usize, slot: usize) -> usize {
    debug_assert!(bit < GF128_BITS);
    debug_assert!(slot < MAC_HALF_TREE_BLOCK_SIZE);
    mac_batch_tree_half_start(half) + mac_half_tree_value_index(bit, slot)
}

fn mac_batch_tree_l_index(half: usize, bit: usize) -> usize {
    mac_batch_tree_half_start(half) + mac_half_tree_l_index(bit)
}

fn mac_batch_tree_qsum_index(half: usize, bit: usize) -> usize {
    mac_batch_tree_half_start(half) + mac_half_tree_qsum_index(bit)
}

fn mac_batch_tree_local_start(half: usize) -> usize {
    mac_batch_tree_half_start(half) + mac_half_tree_local_start()
}

fn monomial_reduction_bits(power: usize) -> Vec<usize> {
    let mut coeffs = [false; 255];
    coeffs[power] = true;
    for high in (GF128_BITS..255).rev() {
        if coeffs[high] {
            for offset in [0usize, 1, 2, 7] {
                coeffs[high - GF128_BITS + offset] ^= true;
            }
        }
    }
    coeffs[..GF128_BITS]
        .iter()
        .enumerate()
        .filter_map(|(index, bit)| bit.then_some(index))
        .collect()
}

fn mac_half_q_witness(
    ap_bits: &[bool; GF128_BITS],
    av_bits: &[bool; GF128_BITS],
    x_bits: &[bool; GF128_BITS],
    tag_bits: &[bool; GF128_BITS],
) -> [[bool; MAC_HALF_PARITY_Q_BITS]; GF128_BITS] {
    let mut counts = [0usize; GF128_BITS];
    for ap_bit in 0..GF128_BITS {
        if !ap_bits[ap_bit] {
            continue;
        }
        for x_bit in 0..GF128_BITS {
            if !x_bits[x_bit] {
                continue;
            }
            for out_bit in monomial_reduction_bits(ap_bit + x_bit) {
                counts[out_bit] += 1;
            }
        }
    }
    let av_fold = av_linear_fold_slots(av_bits);
    for out_bit in 0..GF128_BITS {
        for x_bit in 0..GF128_BITS {
            if av_fold[out_bit][x_bit] && x_bits[x_bit] {
                counts[out_bit] += 1;
            }
        }
    }

    std::array::from_fn(|bit| {
        let tag = usize::from(tag_bits[bit]);
        debug_assert_eq!(counts[bit] & 1, tag);
        let q = (counts[bit] - tag) / 2;
        debug_assert!(q < (1usize << MAC_HALF_PARITY_Q_BITS));
        std::array::from_fn(|q_bit| ((q >> q_bit) & 1) == 1)
    })
}

fn av_linear_fold_slots(av_bits: &[bool; GF128_BITS]) -> [[bool; GF128_BITS]; GF128_BITS] {
    let mut slots = [[false; GF128_BITS]; GF128_BITS];
    for av_bit in 0..GF128_BITS {
        if !av_bits[av_bit] {
            continue;
        }
        for x_bit in 0..GF128_BITS {
            for out_bit in monomial_reduction_bits(av_bit + x_bit) {
                slots[out_bit][x_bit] ^= true;
            }
        }
    }
    slots
}

#[cfg(test)]
fn mac_reduction_max_weight() -> usize {
    (0..GF128_BITS)
        .map(|bit| {
            (0..MAC_HALF_PRODUCT_COEFFS)
                .filter(|&power| monomial_reduction_bits(power).contains(&bit))
                .map(|power| usize::min(power + 1, MAC_HALF_PRODUCT_COEFFS - power))
                .sum::<usize>()
        })
        .max()
        .unwrap_or(0)
}

#[cfg(test)]
fn mac_product_coeff_max_weight() -> usize {
    (0..MAC_HALF_PRODUCT_COEFFS)
        .map(|power| usize::min(power + 1, MAC_HALF_PRODUCT_COEFFS - power))
        .max()
        .unwrap_or(0)
}

fn add_bool_constraint(terms: &mut Vec<QuadTerm>, out: usize, wire: usize) {
    add_quadratic(terms, out, wire, wire, Fp::ONE);
    add_linear(terms, out, wire, -Fp::ONE);
}

fn add_xor_value(terms: &mut Vec<QuadTerm>, out: usize, left: usize, right: usize, one: usize) {
    add_linear_with_one(terms, out, left, Fp::ONE, one);
    add_linear_with_one(terms, out, right, Fp::ONE, one);
    add_quadratic(terms, out, left, right, -Fp::from_u64(2));
}

fn fp_from_bits_le(bits: &[bool; GF128_BITS]) -> Fp {
    let mut acc = Fp::ZERO;
    let mut power = Fp::ONE;
    for bit in bits {
        if *bit {
            acc = acc + power;
        }
        power = power + power;
    }
    acc
}

fn fp_bit(bit: bool) -> Fp {
    if bit {
        Fp::ONE
    } else {
        Fp::ZERO
    }
}

fn two_pow_128() -> Fp {
    let mut power = Fp::ONE;
    for _ in 0..GF128_BITS {
        power = power + power;
    }
    power
}

fn add_linear(terms: &mut Vec<QuadTerm>, out: usize, wire: usize, coeff: Fp) {
    add_linear_with_one(terms, out, wire, coeff, MAC_HALF_CONST_ONE_INDEX);
}

fn add_constant(terms: &mut Vec<QuadTerm>, out: usize, coeff: Fp) {
    add_quadratic(
        terms,
        out,
        MAC_HALF_CONST_ONE_INDEX,
        MAC_HALF_CONST_ONE_INDEX,
        coeff,
    );
}

fn add_linear_with_one(terms: &mut Vec<QuadTerm>, out: usize, wire: usize, coeff: Fp, one: usize) {
    add_quadratic(terms, out, wire, one, coeff);
}

fn add_quadratic(terms: &mut Vec<QuadTerm>, out: usize, left: usize, right: usize, coeff: Fp) {
    terms.push(QuadTerm {
        out: out as u32,
        l: left as u32,
        r: right as u32,
        coeff,
    });
}

pub fn build_c1_input_limbs_circuit() -> Result<Circuit, CircuitError> {
    let mut terms = Vec::with_capacity(5 * (N_LIMBS + 1));
    for value_index in 0..5u32 {
        let out = value_index;
        let value_wire = C1_VALUES_START_INDEX + value_index;
        terms.push(QuadTerm {
            out,
            l: value_wire,
            r: C1_CONST_ONE_INDEX,
            coeff: -Fp::ONE,
        });

        let mut power = Fp::ONE;
        for limb in 0..N_LIMBS as u32 {
            terms.push(QuadTerm {
                out,
                l: C1_LIMBS_START_INDEX + value_index * N_LIMBS as u32 + limb,
                r: C1_CONST_ONE_INDEX,
                coeff: power,
            });
            for _ in 0..LIMB_BITS {
                power = power + power;
            }
        }
    }

    Circuit::new(vec![Layer::new(
        C1_INPUT_LIMBS_OUTPUT_LOG_SIZE,
        C1_INPUT_LIMBS_INPUT_LOG_SIZE,
        terms,
    )?])
}

pub fn c1_input_limbs_input(
    input: &EcdsaInput,
    witness: &Witness,
) -> Result<Vec<Fp>, WitnessError> {
    if witness.values.len() != LAYOUT_LEN {
        return Err(WitnessError::LayoutMismatch);
    }
    let mut circuit_input = vec![Fp::ZERO; 1usize << C1_INPUT_LIMBS_INPUT_LOG_SIZE];
    circuit_input[C1_CONST_ONE_INDEX as usize] = Fp::ONE;
    for (offset, value) in [input.z, input.r, input.s, input.qx, input.qy]
        .into_iter()
        .enumerate()
    {
        circuit_input[C1_VALUES_START_INDEX as usize + offset] =
            Fp::from_bytes_be(value).ok_or(WitnessError::NonCanonicalCoordinate)?;
    }
    let input_limbs = layout_range(LayoutSlot::InputLimbs);
    circuit_input[C1_LIMBS_START_INDEX as usize..C1_LIMBS_START_INDEX as usize + 5 * N_LIMBS]
        .copy_from_slice(&witness.values[input_limbs]);
    Ok(circuit_input)
}

pub fn build_c2_canonicality_circuit() -> Result<Circuit, CircuitError> {
    let b = Fp::from_bytes_be(P256_B_BE).expect("P-256 b is canonical");
    let terms = vec![
        QuadTerm {
            out: 0,
            l: C2_R_INDEX,
            r: C2_R_INV_INDEX,
            coeff: Fp::ONE,
        },
        QuadTerm {
            out: 0,
            l: C2_CONST_ONE_INDEX,
            r: C2_CONST_ONE_INDEX,
            coeff: -Fp::ONE,
        },
        QuadTerm {
            out: 1,
            l: C2_S_INDEX,
            r: C2_S_INV_INDEX,
            coeff: Fp::ONE,
        },
        QuadTerm {
            out: 1,
            l: C2_CONST_ONE_INDEX,
            r: C2_CONST_ONE_INDEX,
            coeff: -Fp::ONE,
        },
        QuadTerm {
            out: 2,
            l: C2_QX2_INDEX,
            r: C2_CONST_ONE_INDEX,
            coeff: Fp::ONE,
        },
        QuadTerm {
            out: 2,
            l: C2_QX_INDEX,
            r: C2_QX_INDEX,
            coeff: -Fp::ONE,
        },
        QuadTerm {
            out: 3,
            l: C2_QY_INDEX,
            r: C2_QY_INDEX,
            coeff: Fp::ONE,
        },
        QuadTerm {
            out: 3,
            l: C2_QX_INDEX,
            r: C2_QX2_INDEX,
            coeff: -Fp::ONE,
        },
        QuadTerm {
            out: 3,
            l: C2_QX_INDEX,
            r: C2_CONST_ONE_INDEX,
            coeff: Fp::from_u64(3),
        },
        QuadTerm {
            out: 3,
            l: C2_CONST_ONE_INDEX,
            r: C2_CONST_ONE_INDEX,
            coeff: -b,
        },
    ];
    Circuit::new(vec![Layer::new(
        C2_CANONICALITY_OUTPUT_LOG_SIZE,
        C2_CANONICALITY_INPUT_LOG_SIZE,
        terms,
    )?])
}

pub fn c2_canonicality_input(input: &EcdsaInput) -> Result<Vec<Fp>, WitnessError> {
    parse_nonzero_scalar(input.r)?;
    parse_nonzero_scalar(input.s)?;

    let r = Fp::from_bytes_be(input.r).ok_or(WitnessError::NonCanonicalScalar)?;
    let s = Fp::from_bytes_be(input.s).ok_or(WitnessError::NonCanonicalScalar)?;
    let qx = parse_coordinate(input.qx)?;
    let qy = parse_coordinate(input.qy)?;

    let mut circuit_input = vec![Fp::ZERO; 1usize << C2_CANONICALITY_INPUT_LOG_SIZE];
    circuit_input[C2_CONST_ONE_INDEX as usize] = Fp::ONE;
    circuit_input[C2_R_INDEX as usize] = r;
    circuit_input[C2_S_INDEX as usize] = s;
    circuit_input[C2_R_INV_INDEX as usize] = r.inverse().ok_or(WitnessError::ZeroScalar)?;
    circuit_input[C2_S_INV_INDEX as usize] = s.inverse().ok_or(WitnessError::ZeroScalar)?;
    circuit_input[C2_QX_INDEX as usize] = qx;
    circuit_input[C2_QY_INDEX as usize] = qy;
    circuit_input[C2_QX2_INDEX as usize] = qx.square();
    Ok(circuit_input)
}

pub fn build_c3_c5_scalar_setup_circuit() -> Result<Circuit, CircuitError> {
    let n = fp_from_words(&P256_ORDER);
    let terms = vec![
        QuadTerm {
            out: 0,
            l: C3_S_INDEX,
            r: C3_SINV_INDEX,
            coeff: Fp::ONE,
        },
        QuadTerm {
            out: 0,
            l: C3_QINV_INDEX,
            r: C3_CONST_ONE_INDEX,
            coeff: -n,
        },
        QuadTerm {
            out: 0,
            l: C3_CONST_ONE_INDEX,
            r: C3_CONST_ONE_INDEX,
            coeff: -Fp::ONE,
        },
        QuadTerm {
            out: 1,
            l: C3_Z_INDEX,
            r: C3_SINV_INDEX,
            coeff: Fp::ONE,
        },
        QuadTerm {
            out: 1,
            l: C3_Q1_INDEX,
            r: C3_CONST_ONE_INDEX,
            coeff: -n,
        },
        QuadTerm {
            out: 1,
            l: C3_U1_INDEX,
            r: C3_CONST_ONE_INDEX,
            coeff: -Fp::ONE,
        },
        QuadTerm {
            out: 2,
            l: C3_R_INDEX,
            r: C3_SINV_INDEX,
            coeff: Fp::ONE,
        },
        QuadTerm {
            out: 2,
            l: C3_Q2_INDEX,
            r: C3_CONST_ONE_INDEX,
            coeff: -n,
        },
        QuadTerm {
            out: 2,
            l: C3_U2_INDEX,
            r: C3_CONST_ONE_INDEX,
            coeff: -Fp::ONE,
        },
    ];
    Circuit::new(vec![Layer::new(
        C3_C5_SCALAR_SETUP_OUTPUT_LOG_SIZE,
        C3_C5_SCALAR_SETUP_INPUT_LOG_SIZE,
        terms,
    )?])
}

pub fn c3_c5_scalar_setup_input(
    input: &EcdsaInput,
    witness: &Witness,
) -> Result<Vec<Fp>, WitnessError> {
    if witness.values.len() != LAYOUT_LEN {
        return Err(WitnessError::LayoutMismatch);
    }
    let mut circuit_input = vec![Fp::ZERO; 1usize << C3_C5_SCALAR_SETUP_INPUT_LOG_SIZE];
    circuit_input[C3_CONST_ONE_INDEX as usize] = Fp::ONE;
    circuit_input[C3_Z_INDEX as usize] =
        Fp::from_bytes_be(input.z).ok_or(WitnessError::NonCanonicalScalar)?;
    circuit_input[C3_R_INDEX as usize] =
        Fp::from_bytes_be(input.r).ok_or(WitnessError::NonCanonicalScalar)?;
    circuit_input[C3_S_INDEX as usize] =
        Fp::from_bytes_be(input.s).ok_or(WitnessError::NonCanonicalScalar)?;

    let sinv = layout_range(LayoutSlot::ScalarInverses);
    circuit_input[C3_SINV_INDEX as usize] = witness.values[sinv.start];

    let us = layout_range(LayoutSlot::UScalars);
    circuit_input[C3_U1_INDEX as usize] = witness.values[us.start];
    circuit_input[C3_U2_INDEX as usize] = witness.values[us.start + 1];

    let quotients = layout_range(LayoutSlot::ModNQuotients);
    circuit_input[C3_QINV_INDEX as usize] = witness.values[quotients.start];
    circuit_input[C3_Q1_INDEX as usize] = witness.values[quotients.start + 1];
    circuit_input[C3_Q2_INDEX as usize] = witness.values[quotients.start + 2];
    Ok(circuit_input)
}

pub fn build_c6_scalar_bits_circuit() -> Result<Circuit, CircuitError> {
    let mut terms = Vec::with_capacity(2 * 512 + 2 * 257);
    for bit in 0..512u32 {
        let bit_index = C6_BITS_START_INDEX + bit;
        terms.push(QuadTerm {
            out: bit,
            l: bit_index,
            r: bit_index,
            coeff: Fp::ONE,
        });
        terms.push(QuadTerm {
            out: bit,
            l: bit_index,
            r: C6_CONST_ONE_INDEX,
            coeff: -Fp::ONE,
        });
    }

    let mut powers = [Fp::ZERO; 256];
    let mut power = Fp::ONE;
    for slot in (0..256usize).rev() {
        powers[slot] = power;
        power = power + power;
    }
    for bit in 0..256u32 {
        terms.push(QuadTerm {
            out: C6_U1_RECOMPOSE_OUTPUT,
            l: C6_BITS_START_INDEX + bit,
            r: C6_CONST_ONE_INDEX,
            coeff: powers[bit as usize],
        });
        terms.push(QuadTerm {
            out: C6_U2_RECOMPOSE_OUTPUT,
            l: C6_BITS_START_INDEX + 256 + bit,
            r: C6_CONST_ONE_INDEX,
            coeff: powers[bit as usize],
        });
    }
    terms.push(QuadTerm {
        out: C6_U1_RECOMPOSE_OUTPUT,
        l: C6_U1_INDEX,
        r: C6_CONST_ONE_INDEX,
        coeff: -Fp::ONE,
    });
    terms.push(QuadTerm {
        out: C6_U2_RECOMPOSE_OUTPUT,
        l: C6_U2_INDEX,
        r: C6_CONST_ONE_INDEX,
        coeff: -Fp::ONE,
    });

    Circuit::new(vec![Layer::new(
        C6_SCALAR_BITS_OUTPUT_LOG_SIZE,
        C6_SCALAR_BITS_INPUT_LOG_SIZE,
        terms,
    )?])
}

pub fn c6_scalar_bits_input(witness: &Witness) -> Result<Vec<Fp>, WitnessError> {
    if witness.values.len() != LAYOUT_LEN {
        return Err(WitnessError::LayoutMismatch);
    }
    let mut input = vec![Fp::ZERO; 1usize << C6_SCALAR_BITS_INPUT_LOG_SIZE];
    input[C6_CONST_ONE_INDEX as usize] = Fp::ONE;
    let u_scalars = layout_range(LayoutSlot::UScalars);
    input[C6_U1_INDEX as usize] = witness.values[u_scalars.start];
    input[C6_U2_INDEX as usize] = witness.values[u_scalars.start + 1];

    let bits = layout_range(LayoutSlot::ScalarBits);
    input[C6_BITS_START_INDEX as usize..C6_BITS_START_INDEX as usize + 512]
        .copy_from_slice(&witness.values[bits]);
    Ok(input)
}

pub fn build_c11_final_add_circuit() -> Result<Circuit, CircuitError> {
    let terms = vec![
        QuadTerm {
            out: 0,
            l: C11_BX_INDEX,
            r: C11_DENOM_INV_INDEX,
            coeff: Fp::ONE,
        },
        QuadTerm {
            out: 0,
            l: C11_AX_INDEX,
            r: C11_DENOM_INV_INDEX,
            coeff: -Fp::ONE,
        },
        QuadTerm {
            out: 0,
            l: C11_CONST_ONE_INDEX,
            r: C11_CONST_ONE_INDEX,
            coeff: -Fp::ONE,
        },
        QuadTerm {
            out: 1,
            l: C11_LAMBDA_INDEX,
            r: C11_BX_INDEX,
            coeff: Fp::ONE,
        },
        QuadTerm {
            out: 1,
            l: C11_LAMBDA_INDEX,
            r: C11_AX_INDEX,
            coeff: -Fp::ONE,
        },
        QuadTerm {
            out: 1,
            l: C11_BY_INDEX,
            r: C11_CONST_ONE_INDEX,
            coeff: -Fp::ONE,
        },
        QuadTerm {
            out: 1,
            l: C11_AY_INDEX,
            r: C11_CONST_ONE_INDEX,
            coeff: Fp::ONE,
        },
        QuadTerm {
            out: 2,
            l: C11_LAMBDA_INDEX,
            r: C11_LAMBDA_INDEX,
            coeff: Fp::ONE,
        },
        QuadTerm {
            out: 2,
            l: C11_AX_INDEX,
            r: C11_CONST_ONE_INDEX,
            coeff: -Fp::ONE,
        },
        QuadTerm {
            out: 2,
            l: C11_BX_INDEX,
            r: C11_CONST_ONE_INDEX,
            coeff: -Fp::ONE,
        },
        QuadTerm {
            out: 2,
            l: C11_RX_INDEX,
            r: C11_CONST_ONE_INDEX,
            coeff: -Fp::ONE,
        },
        QuadTerm {
            out: 3,
            l: C11_RY_INDEX,
            r: C11_CONST_ONE_INDEX,
            coeff: Fp::ONE,
        },
        QuadTerm {
            out: 3,
            l: C11_AY_INDEX,
            r: C11_CONST_ONE_INDEX,
            coeff: Fp::ONE,
        },
        QuadTerm {
            out: 3,
            l: C11_LAMBDA_INDEX,
            r: C11_AX_INDEX,
            coeff: -Fp::ONE,
        },
        QuadTerm {
            out: 3,
            l: C11_LAMBDA_INDEX,
            r: C11_RX_INDEX,
            coeff: Fp::ONE,
        },
    ];
    Circuit::new(vec![Layer::new(
        C11_FINAL_ADD_OUTPUT_LOG_SIZE,
        C11_FINAL_ADD_INPUT_LOG_SIZE,
        terms,
    )?])
}

pub fn c11_final_add_input(witness: &Witness) -> Result<Vec<Fp>, WitnessError> {
    if witness.values.len() != LAYOUT_LEN {
        return Err(WitnessError::LayoutMismatch);
    }
    let corrected = layout_range(LayoutSlot::CorrectedEndpoints);
    let final_point = layout_range(LayoutSlot::FinalPoint);
    let ax = witness.values[corrected.start];
    let ay = witness.values[corrected.start + 1];
    let bx = witness.values[corrected.start + 2];
    let by = witness.values[corrected.start + 3];
    let rx = witness.values[final_point.start];
    let ry = witness.values[final_point.start + 1];
    let final_add_inverse = layout_range(LayoutSlot::FinalAddDenominatorInverse);
    let denom_inv = witness.values[final_add_inverse.start];
    let lambda = (by - ay) * denom_inv;

    let mut input = vec![Fp::ZERO; 1usize << C11_FINAL_ADD_INPUT_LOG_SIZE];
    input[C11_CONST_ONE_INDEX as usize] = Fp::ONE;
    input[C11_AX_INDEX as usize] = ax;
    input[C11_AY_INDEX as usize] = ay;
    input[C11_BX_INDEX as usize] = bx;
    input[C11_BY_INDEX as usize] = by;
    input[C11_RX_INDEX as usize] = rx;
    input[C11_RY_INDEX as usize] = ry;
    input[C11_LAMBDA_INDEX as usize] = lambda;
    input[C11_DENOM_INV_INDEX as usize] = denom_inv;
    Ok(input)
}

pub fn build_c12_on_curve_circuit() -> Result<Circuit, CircuitError> {
    let b = Fp::from_bytes_be(P256_B_BE).expect("P-256 b is canonical");
    let mut terms = Vec::with_capacity(C12_POINT_COUNT * 6);
    for point in 0..C12_POINT_COUNT as u32 {
        let x = C12_POINTS_START_INDEX + point * 3;
        let y = x + 1;
        let x2 = x + 2;
        let out_x2 = point * 2;
        let out_curve = out_x2 + 1;

        terms.push(QuadTerm {
            out: out_x2,
            l: x2,
            r: C12_CONST_ONE_INDEX,
            coeff: Fp::ONE,
        });
        terms.push(QuadTerm {
            out: out_x2,
            l: x,
            r: x,
            coeff: -Fp::ONE,
        });
        terms.push(QuadTerm {
            out: out_curve,
            l: y,
            r: y,
            coeff: Fp::ONE,
        });
        terms.push(QuadTerm {
            out: out_curve,
            l: x,
            r: x2,
            coeff: -Fp::ONE,
        });
        terms.push(QuadTerm {
            out: out_curve,
            l: x,
            r: C12_CONST_ONE_INDEX,
            coeff: Fp::from_u64(3),
        });
        terms.push(QuadTerm {
            out: out_curve,
            l: C12_CONST_ONE_INDEX,
            r: C12_CONST_ONE_INDEX,
            coeff: -b,
        });
    }
    Circuit::new(vec![Layer::new(
        C12_ON_CURVE_OUTPUT_LOG_SIZE,
        C12_ON_CURVE_INPUT_LOG_SIZE,
        terms,
    )?])
}

pub fn c12_on_curve_input(x: Fp, y: Fp) -> Vec<Fp> {
    let mut input = vec![Fp::ZERO; 1usize << C12_ON_CURVE_INPUT_LOG_SIZE];
    input[C12_CONST_ONE_INDEX as usize] = Fp::ONE;
    for point in 0..C12_POINT_COUNT {
        write_c12_point(&mut input, point, x, y);
    }
    input
}

pub fn c12_witness_on_curve_input(witness: &Witness) -> Result<Vec<Fp>, WitnessError> {
    if witness.values.len() != LAYOUT_LEN {
        return Err(WitnessError::LayoutMismatch);
    }
    let mut input = vec![Fp::ZERO; 1usize << C12_ON_CURVE_INPUT_LOG_SIZE];
    input[C12_CONST_ONE_INDEX as usize] = Fp::ONE;

    let mut point_index = 0usize;
    for slot in [LayoutSlot::U1GAccumulators, LayoutSlot::U2QAccumulators] {
        for point in witness.values[layout_range(slot)].chunks_exact(2) {
            write_c12_point(&mut input, point_index, point[0], point[1]);
            point_index += 1;
        }
    }
    debug_assert_eq!(point_index, C12_ACCUMULATOR_POINT_COUNT);

    let corrected = layout_range(LayoutSlot::CorrectedEndpoints);
    write_c12_point(
        &mut input,
        point_index,
        witness.values[corrected.start],
        witness.values[corrected.start + 1],
    );
    point_index += 1;
    write_c12_point(
        &mut input,
        point_index,
        witness.values[corrected.start + 2],
        witness.values[corrected.start + 3],
    );
    point_index += 1;

    let final_point = layout_range(LayoutSlot::FinalPoint);
    write_c12_point(
        &mut input,
        point_index,
        witness.values[final_point.start],
        witness.values[final_point.start + 1],
    );
    point_index += 1;
    debug_assert_eq!(point_index, C12_POINT_COUNT);
    Ok(input)
}

fn write_c12_point(input: &mut [Fp], point_index: usize, x: Fp, y: Fp) {
    let start = C12_POINTS_START_INDEX as usize + point_index * 3;
    input[start] = x;
    input[start + 1] = y;
    input[start + 2] = x.square();
}

pub fn build_c13_slope_inverses_circuit() -> Result<Circuit, CircuitError> {
    let mut terms = Vec::with_capacity(2 * C13_SLOPE_INVERSE_COUNT);
    for i in 0..C13_SLOPE_INVERSE_COUNT as u32 {
        terms.push(QuadTerm {
            out: i,
            l: C13_DENOMS_START_INDEX + i,
            r: C13_INVS_START_INDEX + i,
            coeff: Fp::ONE,
        });
        terms.push(QuadTerm {
            out: i,
            l: C13_CONST_ONE_INDEX,
            r: C13_CONST_ONE_INDEX,
            coeff: -Fp::ONE,
        });
    }
    Circuit::new(vec![Layer::new(
        C13_SLOPE_INVERSES_OUTPUT_LOG_SIZE,
        C13_SLOPE_INVERSES_INPUT_LOG_SIZE,
        terms,
    )?])
}

pub fn c13_slope_inverses_input(
    input: &EcdsaInput,
    witness: &Witness,
) -> Result<Vec<Fp>, WitnessError> {
    if witness.values.len() != LAYOUT_LEN {
        return Err(WitnessError::LayoutMismatch);
    }

    let public_key = parse_public_key(input.qx, input.qy)?;
    let mut denominators = Vec::with_capacity(C13_SLOPE_INVERSE_COUNT);
    denominators.extend(ladder_denominators_from_witness(
        ProjectivePoint::GENERATOR,
        &witness.values[layout_range(LayoutSlot::U1GAccumulators)],
    )?);
    denominators.extend(ladder_denominators_from_witness(
        ProjectivePoint::from(public_key),
        &witness.values[layout_range(LayoutSlot::U2QAccumulators)],
    )?);

    let corrected = layout_range(LayoutSlot::CorrectedEndpoints);
    denominators.push(witness.values[corrected.start + 2] - witness.values[corrected.start]);
    debug_assert_eq!(denominators.len(), C13_SLOPE_INVERSE_COUNT);

    let slopes = layout_range(LayoutSlot::SlopeInverses);
    let mut circuit_input = vec![Fp::ZERO; 1usize << C13_SLOPE_INVERSES_INPUT_LOG_SIZE];
    circuit_input[C13_CONST_ONE_INDEX as usize] = Fp::ONE;
    for (i, denominator) in denominators.into_iter().enumerate() {
        circuit_input[C13_DENOMS_START_INDEX as usize + i] = denominator;
        circuit_input[C13_INVS_START_INDEX as usize + i] = witness.values[slopes.start + i];
    }
    Ok(circuit_input)
}

pub fn build_c14_c15_final_check_circuit() -> Result<Circuit, CircuitError> {
    let n = fp_from_words(&P256_ORDER);
    let terms = vec![
        QuadTerm {
            out: 0,
            l: C14_K_INDEX,
            r: C14_K_INDEX,
            coeff: Fp::ONE,
        },
        QuadTerm {
            out: 0,
            l: C14_K_INDEX,
            r: C14_CONST_ONE_INDEX,
            coeff: -Fp::ONE,
        },
        QuadTerm {
            out: 1,
            l: C14_RX_INDEX,
            r: C14_CONST_ONE_INDEX,
            coeff: Fp::ONE,
        },
        QuadTerm {
            out: 1,
            l: C14_K_INDEX,
            r: C14_CONST_ONE_INDEX,
            coeff: -n,
        },
        QuadTerm {
            out: 1,
            l: C14_R_PRIME_INDEX,
            r: C14_CONST_ONE_INDEX,
            coeff: -Fp::ONE,
        },
        QuadTerm {
            out: 2,
            l: C14_R_PRIME_INDEX,
            r: C14_CONST_ONE_INDEX,
            coeff: Fp::ONE,
        },
        QuadTerm {
            out: 2,
            l: C14_SIGNATURE_R_INDEX,
            r: C14_CONST_ONE_INDEX,
            coeff: -Fp::ONE,
        },
        QuadTerm {
            out: 3,
            l: C15_FLAGS_START_INDEX,
            r: C14_CONST_ONE_INDEX,
            coeff: Fp::ONE,
        },
        QuadTerm {
            out: 4,
            l: C15_FLAGS_START_INDEX + 1,
            r: C14_CONST_ONE_INDEX,
            coeff: Fp::ONE,
        },
        QuadTerm {
            out: 5,
            l: C15_FLAGS_START_INDEX + 2,
            r: C14_CONST_ONE_INDEX,
            coeff: Fp::ONE,
        },
    ];

    Circuit::new(vec![Layer::new(
        C14_C15_OUTPUT_LOG_SIZE,
        C14_C15_INPUT_LOG_SIZE,
        terms,
    )?])
}

pub fn c14_c15_final_check_input(
    input: &EcdsaInput,
    witness: &Witness,
) -> Result<Vec<Fp>, WitnessError> {
    if witness.values.len() != LAYOUT_LEN {
        return Err(WitnessError::LayoutMismatch);
    }
    let mut circuit_input = vec![Fp::ZERO; 1usize << C14_C15_INPUT_LOG_SIZE];
    circuit_input[C14_CONST_ONE_INDEX as usize] = Fp::ONE;

    let final_point = layout_range(LayoutSlot::FinalPoint);
    circuit_input[C14_RX_INDEX as usize] = witness.values[final_point.start];

    let final_reduction = layout_range(LayoutSlot::FinalReduction);
    circuit_input[C14_K_INDEX as usize] = witness.values[final_reduction.start];
    circuit_input[C14_R_PRIME_INDEX as usize] = witness.values[final_reduction.start + 1];
    circuit_input[C14_SIGNATURE_R_INDEX as usize] =
        Fp::from_bytes_be(input.r).ok_or(WitnessError::NonCanonicalScalar)?;

    let flags = layout_range(LayoutSlot::InfinityFlags);
    circuit_input[C15_FLAGS_START_INDEX as usize..C15_FLAGS_START_INDEX as usize + 3]
        .copy_from_slice(&witness.values[flags]);
    Ok(circuit_input)
}

pub fn limbs_13(bytes: [u8; 32]) -> [u32; N_LIMBS] {
    let mut limbs = [0u32; N_LIMBS];
    let mut bit_pos = 0usize;

    for limb in &mut limbs {
        let mut limb_val = 0u32;
        for bit in 0..LIMB_BITS {
            if bit_pos + bit >= 256 {
                break;
            }
            let global_bit = bit_pos + bit;
            let byte_idx = 31 - (global_bit / 8);
            let bit_in_byte = global_bit % 8;
            if (bytes[byte_idx] >> bit_in_byte) & 1 == 1 {
                limb_val |= 1 << bit;
            }
        }
        *limb = limb_val;
        bit_pos += LIMB_BITS;
    }

    limbs
}

fn parse_scalar(bytes: [u8; 32]) -> Result<Scalar, WitnessError> {
    let repr = FieldBytes::from(bytes);
    Option::<Scalar>::from(Scalar::from_repr(repr)).ok_or(WitnessError::NonCanonicalScalar)
}

fn parse_nonzero_scalar(bytes: [u8; 32]) -> Result<Scalar, WitnessError> {
    let scalar = parse_scalar(bytes)?;
    if bytes.iter().all(|&byte| byte == 0) {
        return Err(WitnessError::ZeroScalar);
    }
    Ok(scalar)
}

fn parse_coordinate(bytes: [u8; 32]) -> Result<Fp, WitnessError> {
    Fp::from_bytes_be(bytes).ok_or(WitnessError::NonCanonicalCoordinate)
}

fn parse_public_key(x: [u8; 32], y: [u8; 32]) -> Result<P256AffinePoint, WitnessError> {
    parse_coordinate(x)?;
    parse_coordinate(y)?;

    let mut bytes = [0u8; 65];
    bytes[0] = 0x04;
    bytes[1..33].copy_from_slice(&x);
    bytes[33..65].copy_from_slice(&y);
    let encoded = EncodedPoint::from_bytes(bytes).map_err(|_| WitnessError::InvalidPublicKey)?;
    Option::<P256AffinePoint>::from(P256AffinePoint::from_encoded_point(&encoded))
        .ok_or(WitnessError::InvalidPublicKey)
}

fn scalar_inverse(scalar: Scalar) -> Result<Scalar, WitnessError> {
    Option::<Scalar>::from(scalar.invert()).ok_or(WitnessError::ZeroScalar)
}

fn map_scalar_error(_: ScalarArithmeticError) -> WitnessError {
    WitnessError::ScalarArithmetic
}

fn words_from_be(bytes: [u8; 32]) -> U256Words {
    let mut words = [0u64; 4];
    for (i, chunk) in bytes.chunks_exact(8).enumerate() {
        words[3 - i] = u64::from_be_bytes(chunk.try_into().expect("8-byte chunk"));
    }
    words
}

fn be_from_words(words: &U256Words) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for (i, word) in words.iter().rev().enumerate() {
        bytes[i * 8..(i + 1) * 8].copy_from_slice(&word.to_be_bytes());
    }
    bytes
}

fn fp_from_words(words: &U256Words) -> Fp {
    Fp::from_bytes_be(be_from_words(words)).expect("scalar words are below the p256 field modulus")
}

fn scalar_from_words(words: &U256Words) -> Result<Scalar, WitnessError> {
    parse_scalar(be_from_words(words))
}

fn final_point(
    public_key: &P256AffinePoint,
    u1: &U256Words,
    u2: &U256Words,
) -> Result<([u8; 32], [u8; 32]), WitnessError> {
    let u1 = scalar_from_words(u1)?;
    let u2 = scalar_from_words(u2)?;
    let u1_g = ProjectivePoint::GENERATOR * u1;
    let u2_q = ProjectivePoint::from(*public_key) * u2;
    if bool::from(u1_g.is_identity()) || bool::from(u2_q.is_identity()) {
        return Err(WitnessError::ExceptionalTrace);
    }

    let r = u1_g + u2_q;
    if bool::from(r.is_identity()) {
        return Err(WitnessError::ExceptionalTrace);
    }
    let encoded = r.to_affine().to_encoded_point(false);
    let mut x = [0u8; 32];
    let mut y = [0u8; 32];
    x.copy_from_slice(encoded.x().expect("affine point has x coordinate"));
    y.copy_from_slice(encoded.y().expect("affine point has y coordinate"));
    Ok((x, y))
}

fn write_ladder_accumulators(
    values: &mut [Fp],
    slot: LayoutSlot,
    base: ProjectivePoint,
    scalar_words: &U256Words,
) -> Result<ProjectivePoint, WitnessError> {
    let range = layout_range(slot);
    let out = &mut values[range];
    let mut acc = base;
    let mut output_index = 0usize;

    for bit in (0..256usize).rev() {
        let doubled = acc.double();
        let added = doubled + base;
        acc = if scalar_bit(scalar_words, bit) {
            added
        } else {
            doubled
        };
        if bool::from(acc.is_identity()) {
            return Err(WitnessError::ExceptionalTrace);
        }
        write_projective_point(out, output_index, acc)?;
        output_index += 2;
    }
    debug_assert_eq!(output_index, 512);
    Ok(acc)
}

fn write_ladder_slope_inverses_from_accumulators(
    out: &mut [Fp],
    base: ProjectivePoint,
    accumulators: &[Fp],
) -> Result<(), WitnessError> {
    let denominators = ladder_denominators_from_witness(base, accumulators)?;
    if out.len() != denominators.len() {
        return Err(WitnessError::LayoutMismatch);
    }
    for (i, denominator) in denominators.into_iter().enumerate() {
        write_inverse(out, i, denominator)?;
    }
    Ok(())
}

fn ladder_denominators_from_witness(
    base: ProjectivePoint,
    accumulators: &[Fp],
) -> Result<Vec<Fp>, WitnessError> {
    if accumulators.len() != 2 * C9_C10_ACCUMULATOR_POINTS_PER_SCALAR {
        return Err(WitnessError::LayoutMismatch);
    }
    let (mut prev_x, mut prev_y) = projective_point_coords(base)?;
    let (base_x, _) = projective_point_coords(base)?;
    let mut denominators = Vec::with_capacity(C13_LADDER_DENOMINATOR_COUNT);
    for pair in accumulators.chunks_exact(2) {
        let next_x = pair[0];
        let next_y = pair[1];
        let double_denominator = prev_y + prev_y;
        let doubled_x = affine_double_x(prev_x, prev_y)?;
        denominators.push(double_denominator);
        denominators.push(base_x - doubled_x);
        prev_x = next_x;
        prev_y = next_y;
    }
    let (d_x, _) = projective_point_coords(double_256(base))?;
    denominators.push(d_x - prev_x);
    debug_assert_eq!(denominators.len(), C13_LADDER_DENOMINATOR_COUNT);
    Ok(denominators)
}

pub fn ecdsa_statement_transcript_segments(
    input: &EcdsaInput,
) -> Result<Vec<Vec<u8>>, WitnessError> {
    let projection = EcdsaPublicProjection::full(input);
    Ok(ecdsa_public_projection_transcript_segments(&projection))
}

fn mix_ecdsa_public_projection(
    projection: &EcdsaPublicProjection,
    channel: &mut CoprocessorChannel,
) {
    for segment in ecdsa_public_projection_transcript_segments(projection) {
        channel.mix_bytes(&segment);
    }
}

pub fn ecdsa_public_projection_transcript_segments(
    projection: &EcdsaPublicProjection,
) -> Vec<Vec<u8>> {
    let mut segments = Vec::with_capacity(7);
    segments.push(b"s4-ecdsa-public-projection-v1".to_vec());
    for value in [
        projection.z,
        projection.r,
        projection.s,
        projection.qx,
        projection.qy,
    ] {
        match value {
            Some(bytes) => {
                segments.push(vec![1]);
                segments.push(bytes.to_vec());
            }
            None => segments.push(vec![0]),
        }
    }
    segments
}

fn double_256(mut point: ProjectivePoint) -> ProjectivePoint {
    for _ in 0..256 {
        point = point.double();
    }
    point
}

fn affine_double_x(x: Fp, y: Fp) -> Result<Fp, WitnessError> {
    let denominator = y + y;
    let denominator_inv = denominator
        .inverse()
        .ok_or(WitnessError::ExceptionalTrace)?;
    let numerator = x.square() + x.square() + x.square() - Fp::from_u64(3);
    let lambda = numerator * denominator_inv;
    Ok(lambda.square() - x - x)
}

fn final_add_denominator(u1_g: ProjectivePoint, u2_q: ProjectivePoint) -> Result<Fp, WitnessError> {
    let (ax, _) = projective_point_coords(u1_g)?;
    let (bx, _) = projective_point_coords(u2_q)?;
    Ok(bx - ax)
}

fn write_inverse(out: &mut [Fp], offset: usize, value: Fp) -> Result<(), WitnessError> {
    out[offset] = value.inverse().ok_or(WitnessError::ExceptionalTrace)?;
    Ok(())
}

fn projective_point_coords(point: ProjectivePoint) -> Result<(Fp, Fp), WitnessError> {
    if bool::from(point.is_identity()) {
        return Err(WitnessError::ExceptionalTrace);
    }
    let encoded = point.to_affine().to_encoded_point(false);
    let mut x = [0u8; 32];
    let mut y = [0u8; 32];
    x.copy_from_slice(encoded.x().expect("affine point has x coordinate"));
    y.copy_from_slice(encoded.y().expect("affine point has y coordinate"));
    Ok((
        Fp::from_bytes_be(x).expect("x is canonical"),
        Fp::from_bytes_be(y).expect("y is canonical"),
    ))
}

fn write_projective_point(
    out: &mut [Fp],
    offset: usize,
    point: ProjectivePoint,
) -> Result<(), WitnessError> {
    if bool::from(point.is_identity()) {
        return Err(WitnessError::ExceptionalTrace);
    }
    let encoded = point.to_affine().to_encoded_point(false);
    let mut x = [0u8; 32];
    let mut y = [0u8; 32];
    x.copy_from_slice(encoded.x().expect("affine point has x coordinate"));
    y.copy_from_slice(encoded.y().expect("affine point has y coordinate"));
    out[offset] = Fp::from_bytes_be(x).expect("x is canonical");
    out[offset + 1] = Fp::from_bytes_be(y).expect("y is canonical");
    Ok(())
}

fn scalar_bit(words: &U256Words, bit: usize) -> bool {
    ((words[bit / 64] >> (bit % 64)) & 1) == 1
}

fn reduce_field_x_to_scalar(x: U256Words) -> (U256Words, u8) {
    if cmp_words(&x, &P256_ORDER).is_ge() {
        (sub_words(&x, &P256_ORDER), 1)
    } else {
        (x, 0)
    }
}

fn cmp_words(lhs: &U256Words, rhs: &U256Words) -> core::cmp::Ordering {
    for (&l, &r) in lhs.iter().rev().zip(rhs.iter().rev()) {
        match l.cmp(&r) {
            core::cmp::Ordering::Equal => {}
            ordering => return ordering,
        }
    }
    core::cmp::Ordering::Equal
}

fn sub_words(lhs: &U256Words, rhs: &U256Words) -> U256Words {
    let mut out = [0u64; 4];
    let mut borrow = 0u64;
    for i in 0..4 {
        let (first, first_borrow) = lhs[i].overflowing_sub(rhs[i]);
        let (second, second_borrow) = first.overflowing_sub(borrow);
        out[i] = second;
        borrow = u64::from(first_borrow) + u64::from(second_borrow);
    }
    debug_assert_eq!(borrow, 0);
    out
}

fn write_scalar_bits(out: &mut [Fp], words: &U256Words) {
    debug_assert_eq!(out.len(), 256);
    for (slot, value) in out.iter_mut().enumerate() {
        *value = if scalar_bit(words, 255 - slot) {
            Fp::ONE
        } else {
            Fp::ZERO
        };
    }
}

fn require_equal_slot(
    slot: LayoutSlot,
    expected: &Witness,
    actual: &Witness,
) -> Result<(), WitnessError> {
    let range = layout_range(slot);
    if expected.values[range.clone()] == actual.values[range] {
        Ok(())
    } else {
        Err(WitnessError::ConstraintViolation { slot })
    }
}

fn require_circuit_satisfied(
    circuit: Result<Circuit, CircuitError>,
    input: Result<Vec<Fp>, WitnessError>,
    slot: LayoutSlot,
) -> Result<(), WitnessError> {
    let circuit = circuit.map_err(|_| WitnessError::ConstraintViolation { slot })?;
    let layers = circuit
        .evaluate_input(input?)
        .map_err(|_| WitnessError::ConstraintViolation { slot })?;
    match circuit.is_satisfied(&layers) {
        Ok(true) => Ok(()),
        Ok(false) | Err(_) => Err(WitnessError::ConstraintViolation { slot }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sumcheck::{
        prove_evaluated_circuit_sorted_sparse_profiled, verify_circuit_sorted_sparse_profiled,
    };

    fn p4b_microbench_input(seed: u8) -> EcdsaInput {
        EcdsaInput {
            z: [seed; 32],
            r: [seed.wrapping_add(1); 32],
            s: [seed.wrapping_add(2); 32],
            qx: [seed.wrapping_add(3); 32],
            qy: [seed.wrapping_add(4); 32],
        }
    }

    fn p4b_microbench_key_shares() -> MdocP4bMacKeyShares {
        MdocP4bMacKeyShares(std::array::from_fn(|half| {
            let mut share = [0u8; 16];
            for (byte_index, byte) in share.iter_mut().enumerate() {
                *byte = 0x51u8
                    .wrapping_add(half as u8 * 17)
                    .wrapping_add(byte_index as u8 * 13);
            }
            share
        }))
    }

    fn gf128_basis(bit: usize) -> Gf128 {
        let mut out = [0u8; 16];
        out[bit / 8] = 1 << (bit % 8);
        out
    }

    #[test]
    fn q024_mac_reduction_bounds_are_pinned() {
        assert_eq!(
            mac_product_coeff_max_weight(),
            GF128_BITS,
            "each unreduced C_t coefficient is a sum of at most 128 products"
        );
        assert_eq!(
            mac_reduction_max_weight(),
            MAC_HALF_PARITY_MAX_S - GF128_BITS,
            "Q024 q-bit layout depends on the exact pentanomial fanout bound"
        );
        assert!(
            (1usize << MAC_HALF_PARITY_Q_BITS) > MAC_HALF_PARITY_MAX_S / 2,
            "q bits must cover every possible (W_k + V_k - tag_k) / 2"
        );
    }

    #[test]
    fn q021_av_fold_matrix_matches_gf128_mul_basis_bits() {
        let av = draw_mdoc_p4b_av([9u8; 32], [3u8; 32]);
        let av_bits = bytes_to_bits(&av);
        let fold = av_linear_fold_slots(&av_bits);

        for x_bit in 0..GF128_BITS {
            let product_bits = bytes_to_bits(&crate::mac::gf128_mul(&av, &gf128_basis(x_bit)));
            for out_bit in 0..GF128_BITS {
                assert_eq!(
                    fold[out_bit][x_bit], product_bits[out_bit],
                    "a_v*x fold matrix mismatch at output bit {out_bit}, x bit {x_bit}"
                );
            }
        }
    }

    #[test]
    #[ignore = "microbench: isolated P4b MAC batch sumcheck prove/verify timing"]
    fn mdoc_p4b_mac_batch_sumcheck_microbench() {
        let issuer = p4b_microbench_input(11);
        let device = p4b_microbench_input(29);
        let issuer_public = EcdsaPublicProjection::issuer_key_only(issuer.qx, issuer.qy);
        let device_public = EcdsaPublicProjection::message_hash_only(device.z);
        let projections = [issuer_public, device_public];
        let transcript_seed = [7u8; 32];
        let root = [31u8; 32];
        let av = draw_mdoc_p4b_av(transcript_seed, root);
        let mac_values = mdoc_p4b_mac_values(&issuer, &device);
        let key_shares = p4b_microbench_key_shares();
        let mac_tags = key_shares
            .0
            .iter()
            .zip(mac_values.iter())
            .map(|(ap, x)| gf128_tag(ap, &av, x))
            .collect::<Vec<_>>();
        let circuit = build_mac_batch_circuit(&av, &mac_tags).unwrap();
        let input = mac_batch_input_with_av(&key_shares, &av, &mac_values, &mac_tags).unwrap();
        let layers = circuit.evaluate_input(input).unwrap();
        assert!(circuit.is_satisfied(&layers).unwrap());

        let mut generic_channel = mdoc_p4b_instance_channel(
            transcript_seed,
            root,
            MDOC_P4B_MAC_BATCH_LABEL,
            MdocP4bCircuitRole::MacBatch,
            &projections,
            &av,
            &mac_tags,
        );
        let generic_start = Instant::now();
        let generic =
            prove_evaluated_circuit(&circuit, &layers, root, &mut generic_channel).unwrap();
        let generic_prove = generic_start.elapsed();

        let mut sparse_channel = mdoc_p4b_instance_channel(
            transcript_seed,
            root,
            MDOC_P4B_MAC_BATCH_LABEL,
            MdocP4bCircuitRole::MacBatch,
            &projections,
            &av,
            &mac_tags,
        );
        let sparse_start = Instant::now();
        let (sparse, prove_profile) = prove_evaluated_circuit_sorted_sparse_profiled(
            &circuit,
            &layers,
            root,
            &mut sparse_channel,
        )
        .unwrap();
        let sparse_prove = sparse_start.elapsed();
        assert_eq!(
            bincode::serialize(&generic).unwrap(),
            bincode::serialize(&sparse).unwrap(),
            "sorted sparse MAC proof must be byte-identical to generic"
        );

        let mut verify_channel = mdoc_p4b_instance_channel(
            transcript_seed,
            root,
            MDOC_P4B_MAC_BATCH_LABEL,
            MdocP4bCircuitRole::MacBatch,
            &projections,
            &av,
            &mac_tags,
        );
        let verify_start = Instant::now();
        let (claims, verify_profile) =
            verify_circuit_sorted_sparse_profiled(&circuit, &sparse, root, &mut verify_channel)
                .unwrap();
        let sparse_verify = verify_start.elapsed();
        assert_eq!(claims, sparse.input_claims);

        let prove_terms = prove_profile
            .layers
            .iter()
            .map(|layer| layer.terms)
            .sum::<usize>();
        let verify_terms = verify_profile
            .layers
            .iter()
            .map(|layer| layer.terms)
            .sum::<usize>();
        eprintln!(
            "mdoc_p4b_mac_batch_sumcheck_microbench generic_prove_ms={} sparse_prove_ms={} sparse_verify_ms={} prove_terms={} verify_terms={}",
            generic_prove.as_millis(),
            sparse_prove.as_millis(),
            sparse_verify.as_millis(),
            prove_terms,
            verify_terms
        );
        for layer in &prove_profile.layers {
            eprintln!(
                "prove_layer={} terms={} left_nnz={} right_nnz={} build_left_ms={} left_rounds_ms={} build_right_ms={} right_rounds_ms={}",
                layer.layer_index,
                layer.terms,
                layer.left_initial_nnz,
                layer.right_initial_nnz,
                layer.build_left.as_millis(),
                layer.left_rounds.as_millis(),
                layer.build_right.as_millis(),
                layer.right_rounds.as_millis()
            );
        }
        for layer in &verify_profile.layers {
            eprintln!(
                "verify_layer={} terms={} left_rounds_ms={} right_rounds_ms={} final_eval_ms={}",
                layer.layer_index,
                layer.terms,
                layer.left_rounds.as_millis(),
                layer.right_rounds.as_millis(),
                layer.final_eval.as_millis()
            );
        }
    }
}
