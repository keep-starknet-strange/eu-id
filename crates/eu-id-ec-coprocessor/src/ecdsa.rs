use core::ops::Range;
use std::time::{Duration, Instant};

use crate::ligero::{
    commit_witness_profiled, v4_circle_params, verify_and_authenticate_split_openings,
    verify_authenticated_split_claim_batch, verify_claim_batch, verify_openings, LigeroClaimBatch,
    LigeroCode, LigeroError, LigeroLinearClaim, LigeroLinearTerm, LigeroParams,
    LigeroProximityClaim,
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
use p256::elliptic_curve::group::{Curve, Group};
use p256::elliptic_curve::sec1::{FromEncodedPoint, ToEncodedPoint};
use p256::{AffinePoint as P256AffinePoint, EncodedPoint, FieldBytes, ProjectivePoint, Scalar};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use stwo_p256_utils::scalar_arithmetic::{
    limbs_to_words, words_to_limbs, BigIntLimbs, CanonicalLtTrace, DigestReductionTrace,
    ScalarArithmeticError, ScalarFieldMulTrace, ScalarSetupTrace, U256Words, P256_ORDER,
    PRODUCT_EQUATION_LIMBS,
};

pub const LAYOUT_LEN: usize = 1135;
pub const LIMB_BITS: usize = 13;
pub const N_LIMBS: usize = 20;
pub const C1_INPUT_LIMBS_INPUT_LOG_SIZE: usize = 7;
pub const C1_INPUT_LIMBS_OUTPUT_LOG_SIZE: usize = 3;
pub const C2_CANONICALITY_INPUT_LOG_SIZE: usize = 2;
pub const C2_CANONICALITY_OUTPUT_LOG_SIZE: usize = 1;
pub const C3_C5_SCALAR_SETUP_INPUT_LOG_SIZE: usize = 13;
pub const C3_C5_SCALAR_SETUP_OUTPUT_LOG_SIZE: usize = 13;
pub const C9_C10_LADDER_INPUT_LOG_SIZE: usize = 13;
pub const C9_C10_LADDER_OUTPUT_LOG_SIZE: usize = 14;
pub const C11_FINAL_ADD_INPUT_LOG_SIZE: usize = 4;
pub const C11_FINAL_ADD_OUTPUT_LOG_SIZE: usize = 2;
pub const C12_ON_CURVE_INPUT_LOG_SIZE: usize = 11;
pub const C12_ON_CURVE_OUTPUT_LOG_SIZE: usize = 11;
pub const C14_C15_INPUT_LOG_SIZE: usize = 11;
pub const C14_C15_OUTPUT_LOG_SIZE: usize = 11;
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
const MAC_BATCH_CANONICAL_VALUE_COUNT: usize = MDOC_P4B_MAC_HALF_COUNT / 2;
const MAC_BATCH_CANONICAL_BITS: usize = 2 * GF128_BITS;
const MAC_BATCH_CANONICAL_CARRIES: usize = MAC_BATCH_CANONICAL_BITS + 1;
const MAC_BATCH_CANONICAL_SLACK_BITS_START: usize =
    MDOC_P4B_MAC_HALF_COUNT * MAC_BATCH_HALF_GROUP_A_INPUT_STRIDE;
const MAC_BATCH_CANONICAL_CARRIES_START: usize = MAC_BATCH_CANONICAL_SLACK_BITS_START
    + MAC_BATCH_CANONICAL_VALUE_COUNT * MAC_BATCH_CANONICAL_BITS;
const MAC_BATCH_CANONICAL_CONSTRAINTS_PER_VALUE: usize =
    MAC_BATCH_CANONICAL_BITS + MAC_BATCH_CANONICAL_CARRIES + 2 + MAC_BATCH_CANONICAL_BITS;
const MAC_BATCH_CANONICAL_CONSTRAINTS: usize =
    MAC_BATCH_CANONICAL_VALUE_COUNT * MAC_BATCH_CANONICAL_CONSTRAINTS_PER_VALUE;
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
pub const MDOC_P4B_MAC_COMMITTED_PRIVATE_INPUTS: usize = MDOC_P4B_MAC_HALF_COUNT
    * MAC_HALF_COMMITTED_PRIVATE_INPUTS
    + MAC_BATCH_CANONICAL_VALUE_COUNT * (MAC_BATCH_CANONICAL_BITS + MAC_BATCH_CANONICAL_CARRIES);
pub const IMPLEMENTED_CIRCUIT_FAMILY_COUNT: usize = 7;

const C1_CONST_ONE_INDEX: u32 = 0;
const C1_VALUES_START_INDEX: u32 = 1;
const C1_LIMBS_START_INDEX: u32 = 6;
const C2_CONST_ONE_INDEX: u32 = 0;
const C2_QX_INDEX: u32 = 1;
const C2_QY_INDEX: u32 = 2;
const C2_QX2_INDEX: u32 = 3;
const C3_CONST_ONE_INDEX: usize = 0;
const C3_Z_INDEX: usize = 1;
const C3_R_INDEX: usize = 2;
const C3_S_INDEX: usize = 3;
const C3_U1_INDEX: usize = 4;
const C3_U2_INDEX: usize = 5;
const C3_R_NONZERO_INV_INDEX: usize = 6;
const C3_S_NONZERO_INV_INDEX: usize = 7;
const C3_Z_GE_N_INDEX: usize = 8;
const C3_CANONICAL_SCALAR_COUNT: usize = 5;
const C3_SCALAR_R: usize = 0;
const C3_SCALAR_S: usize = 1;
const C3_SCALAR_Z_RED: usize = 2;
const C3_SCALAR_U1: usize = 3;
const C3_SCALAR_U2: usize = 4;
const C3_PRODUCT_COUNT: usize = 2;
const PRODUCT_CARRY_BITS: usize = 19;
const PRODUCT_CARRY_OFFSET: i64 = 1 << (PRODUCT_CARRY_BITS - 1);
const PRODUCT_INTERNAL_CARRIES: usize = PRODUCT_EQUATION_LIMBS - 1;
const C3_SCALAR_LIMBS_START: usize = 9;
const C3_SCALAR_BITS_START: usize = C3_SCALAR_LIMBS_START + C3_CANONICAL_SCALAR_COUNT * N_LIMBS;
const C3_SLACK_LIMBS_START: usize =
    C3_SCALAR_BITS_START + C3_CANONICAL_SCALAR_COUNT * N_LIMBS * LIMB_BITS;
const C3_SLACK_BITS_START: usize = C3_SLACK_LIMBS_START + C3_CANONICAL_SCALAR_COUNT * N_LIMBS;
const C3_LT_CARRIES_START: usize =
    C3_SLACK_BITS_START + C3_CANONICAL_SCALAR_COUNT * N_LIMBS * LIMB_BITS;
const C3_Z_LIMBS_START: usize = C3_LT_CARRIES_START + C3_CANONICAL_SCALAR_COUNT * N_LIMBS;
const C3_Z_BITS_START: usize = C3_Z_LIMBS_START + N_LIMBS;
const C3_QUOTIENT_LIMBS_START: usize = C3_Z_BITS_START + N_LIMBS * LIMB_BITS;
const C3_QUOTIENT_BITS_START: usize = C3_QUOTIENT_LIMBS_START + C3_PRODUCT_COUNT * N_LIMBS;
const C3_PRODUCT_CARRY_BITS_START: usize =
    C3_QUOTIENT_BITS_START + C3_PRODUCT_COUNT * N_LIMBS * LIMB_BITS;
const C3_DIGEST_BORROWS_START: usize =
    C3_PRODUCT_CARRY_BITS_START + C3_PRODUCT_COUNT * PRODUCT_INTERNAL_CARRIES * PRODUCT_CARRY_BITS;
const C3_Z_SLACK_LIMBS_START: usize = C3_DIGEST_BORROWS_START + N_LIMBS - 1;
const C3_Z_SLACK_BITS_START: usize = C3_Z_SLACK_LIMBS_START + N_LIMBS;
const C3_Z_LT_CARRIES_START: usize = C3_Z_SLACK_BITS_START + N_LIMBS * LIMB_BITS;
const C9_CONST_ONE_INDEX: usize = 0;
const C9_U1_INDEX: usize = 1;
const C9_U2_INDEX: usize = 2;
const C9_QX_INDEX: usize = 3;
const C9_QY_INDEX: usize = 4;
const C9_GX_INDEX: usize = 5;
const C9_GY_INDEX: usize = 6;
const C9_SCALAR_BITS: usize = 256;
const C9_LADDER_COUNT: usize = 2;
const C9_BITS_START_INDEX: usize = 7;
const C9_STARTED_START_INDEX: usize = C9_BITS_START_INDEX + C9_LADDER_COUNT * C9_SCALAR_BITS;
const C9_STEPS_START_INDEX: usize = C9_STARTED_START_INDEX + C9_LADDER_COUNT * (C9_SCALAR_BITS + 1);
const C9_STEP_WIDTH: usize = 11;
const C9_CORRECTED_START_INDEX: usize =
    C9_STEPS_START_INDEX + C9_LADDER_COUNT * C9_SCALAR_BITS * C9_STEP_WIDTH;
const C9_STEP_NEXT_X: usize = 0;
const C9_STEP_NEXT_Y: usize = 1;
const C9_STEP_DOUBLE_X: usize = 2;
const C9_STEP_DOUBLE_Y: usize = 3;
const C9_STEP_DOUBLE_LAMBDA: usize = 4;
const C9_STEP_DOUBLE_DENOM_INV: usize = 5;
const C9_STEP_ADD_LAMBDA: usize = 6;
const C9_STEP_ADD_DENOM_INV: usize = 7;
const C9_STEP_ADD_DELTA_X: usize = 8;
const C9_STEP_ADD_DELTA_Y: usize = 9;
const C9_STEP_ACTIVE_BIT: usize = 10;
const C9_CANONICAL_SLACK_START_INDEX: usize = C9_CORRECTED_START_INDEX + 4;
const C9_CANONICAL_CARRY_START_INDEX: usize =
    C9_CANONICAL_SLACK_START_INDEX + C9_LADDER_COUNT * C9_SCALAR_BITS;
const P256_ORDER_MINUS_ONE: U256Words = [
    0xf3b9_cac2_fc63_2550,
    0xbce6_faad_a717_9e84,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_0000_0000,
];
const P256_FIELD_MODULUS: U256Words = [
    0xffff_ffff_ffff_ffff,
    0x0000_0000_ffff_ffff,
    0x0000_0000_0000_0000,
    0xffff_ffff_0000_0001,
];
const P256_FIELD_MODULUS_MINUS_ONE: U256Words = [
    0xffff_ffff_ffff_fffe,
    0x0000_0000_ffff_ffff,
    0x0000_0000_0000_0000,
    0xffff_ffff_0000_0001,
];
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
const C14_CONST_ONE_INDEX: usize = 0;
const C14_RX_INDEX: usize = 1;
const C14_SIGNATURE_R_INDEX: usize = 2;
const C14_K_INDEX: usize = 3;
const C14_R_LIMBS_START: usize = 4;
const C14_R_BITS_START: usize = C14_R_LIMBS_START + N_LIMBS;
const C14_R_SLACK_LIMBS_START: usize = C14_R_BITS_START + N_LIMBS * LIMB_BITS;
const C14_R_SLACK_BITS_START: usize = C14_R_SLACK_LIMBS_START + N_LIMBS;
const C14_R_LT_CARRIES_START: usize = C14_R_SLACK_BITS_START + N_LIMBS * LIMB_BITS;
const C14_RX_LIMBS_START: usize = C14_R_LT_CARRIES_START + N_LIMBS;
const C14_RX_BITS_START: usize = C14_RX_LIMBS_START + N_LIMBS;
const C14_RX_SLACK_LIMBS_START: usize = C14_RX_BITS_START + N_LIMBS * LIMB_BITS;
const C14_RX_SLACK_BITS_START: usize = C14_RX_SLACK_LIMBS_START + N_LIMBS;
const C14_RX_LT_CARRIES_START: usize = C14_RX_SLACK_BITS_START + N_LIMBS * LIMB_BITS;
const C14_REDUCTION_BORROWS_START: usize = C14_RX_LT_CARRIES_START + N_LIMBS;
const IMPLEMENTED_BUNDLE_LIGERO_LABEL: &[u8] = b"s4-ecdsa-implemented-bundle-v2";
const COPROCESSOR_TRANSCRIPT_DOMAIN: &[u8] = b"eu-id-ec-coproc-v2";

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
    UScalars,
    U1GAccumulators,
    U2QAccumulators,
    CorrectedEndpoints,
    FinalAddDenominatorInverse,
    FinalPoint,
    FinalReduction,
    MacHalf,
}

pub fn layout_range(slot: LayoutSlot) -> Range<usize> {
    match slot {
        LayoutSlot::InputLimbs => 0..100,
        LayoutSlot::UScalars => 100..102,
        LayoutSlot::U1GAccumulators => 102..614,
        LayoutSlot::U2QAccumulators => 614..1126,
        LayoutSlot::CorrectedEndpoints => 1126..1130,
        LayoutSlot::FinalAddDenominatorInverse => 1130..1131,
        LayoutSlot::FinalPoint => 1131..1133,
        LayoutSlot::FinalReduction => 1133..1135,
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
    let _r = parse_nonzero_scalar(input.r)?;
    let s = parse_nonzero_scalar(input.s)?;
    let public_key = parse_public_key(input.qx, input.qy)?;

    let sinv_scalar = scalar_inverse(s)?;
    let z_words = words_from_be(input.z);
    let r_words = words_from_be(input.r);
    let sinv_words = words_from_be(sinv_scalar.to_repr().into());
    let z_reduction = DigestReductionTrace::new(&z_words, &P256_ORDER).map_err(map_scalar_error)?;
    let z_red_words = limbs_to_words(&z_reduction.z_red);
    let u1_trace = ScalarFieldMulTrace::new("s4_u1", &z_red_words, &sinv_words, &P256_ORDER)
        .map_err(map_scalar_error)?;
    let u2_trace = ScalarFieldMulTrace::new("s4_u2", &r_words, &sinv_words, &P256_ORDER)
        .map_err(map_scalar_error)?;
    let u1_words = u1_trace.mul.result_words();
    let u2_words = u2_trace.mul.result_words();
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

    let us_range = layout_range(LayoutSlot::UScalars);
    values[us_range.start] = fp_from_words(&u1_words);
    values[us_range.start + 1] = fp_from_words(&u2_words);

    let u1_point = write_ladder_accumulators(
        &mut values,
        LayoutSlot::U1GAccumulators,
        ProjectivePoint::GENERATOR,
        &u1_words,
    )?;
    let u2_base = ProjectivePoint::from(public_key);
    let u2_point =
        write_ladder_accumulators(&mut values, LayoutSlot::U2QAccumulators, u2_base, &u2_words)?;

    let r_point = projective_point_bytes(u1_point + u2_point)?;
    let (rx_words, reduction_flag) = reduce_field_x_to_scalar(words_from_be(r_point.0));

    let corrected = layout_range(LayoutSlot::CorrectedEndpoints);
    write_projective_point(&mut values[corrected.clone()], 0, u1_point)?;
    write_projective_point(&mut values[corrected], 2, u2_point)?;

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
        LayoutSlot::UScalars,
        LayoutSlot::U1GAccumulators,
        LayoutSlot::U2QAccumulators,
        LayoutSlot::CorrectedEndpoints,
        LayoutSlot::FinalAddDenominatorInverse,
        LayoutSlot::FinalPoint,
        LayoutSlot::FinalReduction,
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

/// Verifies only the per-family sumchecks and returns their unbound input claims.
///
/// This low-level API does **not** bind a caller statement, projected inputs, or
/// copies shared between circuit families. Production callers must use
/// [`verify_implemented_circuit_bundle`] (or its batch/projected variants), which
/// authenticates these claims against Ligero and adds all fixed and affine bindings.
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
    let sumcheck_start = Instant::now();
    let entry_results = instances
        .par_iter()
        .map(|instance| {
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
                MdocP4bCircuitRole::MacBatch => prove_evaluated_circuit_sorted_sparse(
                    &circuit,
                    &layers,
                    full_root,
                    &mut channel,
                ),
                _ => prove_evaluated_circuit(&circuit, &layers, full_root, &mut channel),
            }
            .map_err(ImplementedCircuitProofError::Sumcheck)?;
            Ok((
                ImplementedCircuitBundleEntry { proof },
                mdoc_p4b_instance_timing(instance.role, instance.label, instance_start.elapsed()),
            ))
        })
        .collect::<Result<Vec<_>, ImplementedCircuitProofError>>()?;
    let (entries, sumcheck_by_instance): (Vec<_>, Vec<_>) = entry_results.into_iter().unzip();
    profile.sumcheck_by_instance = sumcheck_by_instance;
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
    if !bundle.consistency_claim_values.is_empty() {
        return Err(ImplementedCircuitProofError::CrossFamilyBindingRejected);
    }
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
    let authenticated_openings = verify_and_authenticate_split_openings(
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
    .map_err(ImplementedCircuitProofError::Ligero)?
    .ok_or(ImplementedCircuitProofError::ProximityOpeningRejected)?;
    profile.ligero_proximity = start.elapsed();

    let mut linear_claims = Vec::new();

    // Instances are order-independent: each derives its own Fiat-Shamir channel
    // from `mdoc_p4b_instance_channel`, so the expensive sumcheck verification
    // parallelizes exactly like the prove side. Deterministic affine binding
    // claims are reconstructed below without opening their private operands.
    let verified_claims = circuits
        .par_iter()
        .zip(bundle.entries.par_iter())
        .map(|(instance, entry)| {
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
            Ok((claims, start.elapsed()))
        })
        .collect::<Result<Vec<_>, ImplementedCircuitProofError>>()?;

    for (((instance, layout), entry), (claims, elapsed)) in circuits
        .iter()
        .zip(layouts.iter())
        .zip(bundle.entries.iter())
        .zip(verified_claims)
    {
        profile.sumcheck += elapsed;
        profile.sumcheck_by_instance.push(mdoc_p4b_instance_timing(
            instance.role,
            instance.label,
            elapsed,
        ));
        let start = Instant::now();
        match instance.role {
            MdocP4bCircuitRole::MacBatch => add_mac_split_input_claims(
                &mut linear_claims,
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
                add_family_fixed_claims(
                    &mut linear_claims,
                    issuer_projection,
                    instance.label,
                    layout,
                )?;
            }
            MdocP4bCircuitRole::DeviceEcdsa => {
                add_family_fixed_claims(
                    &mut linear_claims,
                    device_projection,
                    instance.label,
                    layout,
                )?;
            }
            MdocP4bCircuitRole::RevocationEcdsa => {
                // Only reachable when the verifier expects a revocation set:
                // `circuits` contains revocation instances iff
                // `revocation_projection` is `Some`.
                add_family_fixed_claims(
                    &mut linear_claims,
                    revocation_projection.expect("revocation instances imply a projection"),
                    instance.label,
                    layout,
                )?;
            }
            MdocP4bCircuitRole::MacBatch => {
                for index in 0..MDOC_P4B_MAC_HALF_COUNT {
                    add_mac_half_public_const_claim(&mut linear_claims, layout, index);
                }
            }
        }
        profile.consistency += start.elapsed();
    }

    let start = Instant::now();
    let identities = circuits
        .iter()
        .map(|instance| (instance.role, instance.label))
        .collect::<Vec<_>>();
    add_mdoc_p4b_consistency_claims(&mut linear_claims, &identities, &layouts)?;
    profile.consistency += start.elapsed();

    let start = Instant::now();
    let claim_gamma = ligero_claim_gamma(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        full_root,
        linear_claims.len(),
        transcript_seed,
    );
    if !verify_authenticated_split_claim_batch(
        authenticated_openings,
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
    if !bundle.consistency_claim_values.is_empty() {
        return Err(ImplementedCircuitProofError::CrossFamilyBindingRejected);
    }
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

    // Every (signature, family) sumcheck derives an independent Fiat-Shamir
    // channel (seed + signature index + label + projection), so the expensive
    // verify_circuit work parallelizes like the prove side.
    let family_count = circuits.len();
    let verified_flat = (0..bundle.entries.len())
        .into_par_iter()
        .map(|idx| {
            let signature_index = idx / family_count;
            let family_index = idx % family_count;
            let projection = &projections[signature_index];
            let instance = &circuits[family_index];
            let entry = &bundle.entries[idx];
            let mut channel =
                CoprocessorChannel::from_seed(transcript_seed, COPROCESSOR_TRANSCRIPT_DOMAIN);
            mix_bundle_signature_index(signature_index, &mut channel);
            channel.mix_bytes(instance.label);
            mix_ecdsa_public_projection(projection, &mut channel);
            let start = Instant::now();
            let claims = verify_circuit(&instance.circuit, &entry.proof, bundle.root, &mut channel)
                .map_err(ImplementedCircuitProofError::Sumcheck)?;
            Ok((claims, start.elapsed()))
        })
        .collect::<Result<Vec<_>, ImplementedCircuitProofError>>()?;

    let mut linear_claims = Vec::new();
    let mut all_claims = Vec::with_capacity(projections.len());
    for (signature_index, (projection, layouts)) in
        projections.iter().zip(&signature_layouts).enumerate()
    {
        let mut verified_claims = Vec::with_capacity(circuits.len());
        for (family_index, ((instance, layout), entry)) in circuits
            .iter()
            .zip(layouts)
            .zip(
                &bundle.entries
                    [signature_index * circuits.len()..(signature_index + 1) * circuits.len()],
            )
            .enumerate()
        {
            let (claims, elapsed) = &verified_flat[signature_index * family_count + family_index];
            let claims = claims.clone();
            profile.sumcheck += *elapsed;
            profile.sumcheck_by_family[family_index] += *elapsed;

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
            add_family_fixed_claims(&mut linear_claims, projection, instance.label, layout)?;
            profile.consistency += start.elapsed();
            verified_claims.push(claims);
        }
        let start = Instant::now();
        add_ecdsa_consistency_claims(&mut linear_claims, layouts)?;
        profile.consistency += start.elapsed();
        all_claims.push(verified_claims);
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
        let is_sampleable = params.code == LigeroCode::Circle || index >= params.row_len;
        if is_sampleable && !indices.contains(&index) {
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
        build_c9_c10_ladder_circuit()?,
        build_c11_final_add_circuit()?,
        build_c12_on_curve_circuit()?,
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
        for term in &claim.terms {
            let start = term.offset / row_len;
            let end = (term.offset + term.len).div_ceil(row_len);
            rows.extend(start..end);
        }
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
            add_family_fixed_claims(&mut claims, projection, instance.label, layout)?;
        }
        add_ecdsa_consistency_claims(&mut claims, layouts)?;
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
    Ok((batch, Vec::new()))
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
    transcript_root: [u8; 32],
    transcript_seed: TranscriptSeed,
) -> Result<(LigeroClaimBatch, Vec<Fp>, MdocP4bClaimInventory), ImplementedCircuitProofError> {
    let mut claims = Vec::new();
    let group_b_offset = ligero_row_count(committed_len_a, params.row_len) * params.row_len;
    for ((instance, layout), entry) in instances.iter().zip(layouts).zip(entries) {
        match instance.role {
            MdocP4bCircuitRole::MacBatch => add_mac_split_input_claims(
                &mut claims,
                layout,
                group_b_offset,
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
                add_family_fixed_claims(&mut claims, &projections[0], instance.label, layout)?;
            }
            MdocP4bCircuitRole::DeviceEcdsa => {
                add_family_fixed_claims(&mut claims, &projections[1], instance.label, layout)?;
            }
            MdocP4bCircuitRole::RevocationEcdsa => {
                add_family_fixed_claims(&mut claims, &projections[2], instance.label, layout)?;
            }
            MdocP4bCircuitRole::MacBatch => {
                for half in 0..MDOC_P4B_MAC_HALF_COUNT {
                    add_mac_half_public_const_claim(&mut claims, layout, half);
                }
            }
        }
    }
    let identities = instances
        .iter()
        .map(|instance| (instance.role, instance.label))
        .collect::<Vec<_>>();
    add_mdoc_p4b_consistency_claims(&mut claims, &identities, layouts)?;
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
    Ok((batch, Vec::new(), inventory))
}

fn add_input_claims(
    claims: &mut Vec<LigeroLinearClaim>,
    layout: &BundleCircuitLayout,
    input_claims: &InputClaims,
) {
    for (point, value) in input_claims.points.iter().cloned().zip(input_claims.values) {
        claims.push(LigeroLinearClaim::mle(
            layout.input_offset,
            layout.input_len,
            point,
            value,
        ));
    }
}

fn add_mac_split_input_claims(
    claims: &mut Vec<LigeroLinearClaim>,
    layout_a: &BundleCircuitLayout,
    group_b_offset: usize,
    input_claims: &InputClaims,
) -> Result<(), ImplementedCircuitProofError> {
    for (point, value) in input_claims.points.iter().zip(input_claims.values) {
        if point.len() != MAC_BATCH_INPUT_LOG_SIZE {
            return Err(ImplementedCircuitProofError::InputClaimOpeningRejected);
        }
        let split = point[MAC_BATCH_GROUP_A_INPUT_LOG_SIZE];
        let subpoint = point[..MAC_BATCH_GROUP_A_INPUT_LOG_SIZE].to_vec();
        claims.push(LigeroLinearClaim::affine(
            vec![
                LigeroLinearTerm {
                    offset: layout_a.input_offset,
                    len: layout_a.input_len,
                    point: subpoint.clone(),
                    coefficient: Fp::ONE - split,
                },
                LigeroLinearTerm {
                    offset: group_b_offset,
                    len: 1usize << MAC_BATCH_GROUP_B_INPUT_LOG_SIZE,
                    point: subpoint,
                    coefficient: split,
                },
            ],
            value,
        ));
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
    claims.push(LigeroLinearClaim::mle(
        layout.pad_offset,
        layout.pad_len,
        point,
        value,
    ));
    Ok(())
}

fn add_family_fixed_claims(
    claims: &mut Vec<LigeroLinearClaim>,
    projection: &EcdsaPublicProjection,
    label: &[u8],
    layout: &BundleCircuitLayout,
) -> Result<(), ImplementedCircuitProofError> {
    match label {
        b"s4-ecdsa-c1-input-limbs" => add_c1_public_claims(claims, projection, layout)?,
        b"s4-ecdsa-c2-canonicality" => add_c2_public_claims(claims, projection, layout)?,
        b"s4-ecdsa-c3-c5-scalar-setup" => add_c3_public_claims(claims, projection, layout)?,
        b"s4-ecdsa-c9-c10-ladder" => add_c9_fixed_claims(claims, layout),
        b"s4-ecdsa-c14-c15-final-check" => add_c14_public_claims(claims, projection, layout)?,
        _ => {}
    }
    Ok(())
}

fn add_c9_fixed_claims(claims: &mut Vec<LigeroLinearClaim>, layout: &BundleCircuitLayout) {
    let (gx, gy) = projective_point_coords(ProjectivePoint::GENERATOR)
        .expect("P-256 generator is a finite affine point");
    for (index, value) in [(C9_GX_INDEX, gx), (C9_GY_INDEX, gy)] {
        add_fixed_claim(claims, layout.input_offset, layout.input_len, index, value);
    }
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
        (C3_Z_INDEX, projection.z),
        (C3_R_INDEX, projection.r),
        (C3_S_INDEX, projection.s),
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
            C14_SIGNATURE_R_INDEX,
            signature_r,
        );
    }
    Ok(())
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

fn add_ecdsa_consistency_claims(
    claims: &mut Vec<LigeroLinearClaim>,
    layouts: &[BundleCircuitLayout],
) -> Result<(), ImplementedCircuitProofError> {
    if layouts.len() != IMPLEMENTED_CIRCUIT_FAMILY_COUNT {
        return Err(ImplementedCircuitProofError::CrossFamilyBindingRejected);
    }
    let [c1, c2, c3, c9, c11, c12, c14] = layouts else {
        unreachable!("length checked");
    };
    let c1_value = |offset| C1_VALUES_START_INDEX as usize + offset;
    let c12_point =
        |point: usize, coordinate: usize| C12_POINTS_START_INDEX as usize + point * 3 + coordinate;

    for layout in layouts {
        add_fixed_claim(claims, layout.input_offset, layout.input_len, 0, Fp::ONE);
    }
    for (left_layout, left, right_layout, right) in [
        (c1, c1_value(0), c3, C3_Z_INDEX),
        (c1, c1_value(1), c3, C3_R_INDEX),
        (c3, C3_R_INDEX, c14, C14_SIGNATURE_R_INDEX),
        (c1, c1_value(2), c3, C3_S_INDEX),
        (c1, c1_value(3), c2, C2_QX_INDEX as usize),
        (c2, C2_QX_INDEX as usize, c9, C9_QX_INDEX),
        (c1, c1_value(4), c2, C2_QY_INDEX as usize),
        (c2, C2_QY_INDEX as usize, c9, C9_QY_INDEX),
        (c3, C3_U1_INDEX, c9, C9_U1_INDEX),
        (c3, C3_U2_INDEX, c9, C9_U2_INDEX),
        (c9, c9_corrected_index(0, 0), c11, C11_AX_INDEX as usize),
        (c9, c9_corrected_index(0, 1), c11, C11_AY_INDEX as usize),
        (c9, c9_corrected_index(1, 0), c11, C11_BX_INDEX as usize),
        (c9, c9_corrected_index(1, 1), c11, C11_BY_INDEX as usize),
        (
            c11,
            C11_AX_INDEX as usize,
            c12,
            c12_point(C12_ACCUMULATOR_POINT_COUNT, 0),
        ),
        (
            c11,
            C11_AY_INDEX as usize,
            c12,
            c12_point(C12_ACCUMULATOR_POINT_COUNT, 1),
        ),
        (
            c11,
            C11_BX_INDEX as usize,
            c12,
            c12_point(C12_ACCUMULATOR_POINT_COUNT + 1, 0),
        ),
        (
            c11,
            C11_BY_INDEX as usize,
            c12,
            c12_point(C12_ACCUMULATOR_POINT_COUNT + 1, 1),
        ),
        (
            c11,
            C11_RX_INDEX as usize,
            c12,
            c12_point(C12_FINAL_POINT_INDEX, 0),
        ),
        (
            c11,
            C11_RY_INDEX as usize,
            c12,
            c12_point(C12_FINAL_POINT_INDEX, 1),
        ),
        (c11, C11_RX_INDEX as usize, c14, C14_RX_INDEX),
    ] {
        add_equality_claim(claims, left_layout, left, right_layout, right);
    }
    Ok(())
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

fn add_mdoc_p4b_consistency_claims(
    claims: &mut Vec<LigeroLinearClaim>,
    identities: &[(MdocP4bCircuitRole, &'static [u8])],
    layouts: &[BundleCircuitLayout],
) -> Result<(), ImplementedCircuitProofError> {
    if identities.len() != layouts.len() {
        return Err(ImplementedCircuitProofError::CrossFamilyBindingRejected);
    }
    for role in [
        MdocP4bCircuitRole::IssuerEcdsa,
        MdocP4bCircuitRole::DeviceEcdsa,
        MdocP4bCircuitRole::RevocationEcdsa,
    ] {
        let role_layouts = identities
            .iter()
            .zip(layouts)
            .filter_map(|((instance_role, _), layout)| (*instance_role == role).then_some(*layout))
            .collect::<Vec<_>>();
        if !role_layouts.is_empty() {
            add_ecdsa_consistency_claims(claims, &role_layouts)?;
        }
    }

    let find = |role: MdocP4bCircuitRole, label: &'static [u8]| {
        identities
            .iter()
            .zip(layouts)
            .find_map(|(&(instance_role, instance_label), layout)| {
                (instance_role == role && instance_label == label).then_some(layout)
            })
            .ok_or(ImplementedCircuitProofError::CrossFamilyBindingRejected)
    };
    let issuer_c3 = find(
        MdocP4bCircuitRole::IssuerEcdsa,
        b"s4-ecdsa-c3-c5-scalar-setup",
    )?;
    let device_c2 = find(MdocP4bCircuitRole::DeviceEcdsa, b"s4-ecdsa-c2-canonicality")?;
    let mac = find(MdocP4bCircuitRole::MacBatch, MDOC_P4B_MAC_BATCH_LABEL)?;
    add_mac_field_binding(claims, issuer_c3, C3_Z_INDEX, mac, 0, 1);
    add_mac_field_binding(claims, device_c2, C2_QX_INDEX as usize, mac, 2, 3);
    add_mac_field_binding(claims, device_c2, C2_QY_INDEX as usize, mac, 4, 5);
    Ok(())
}

fn add_mac_field_binding(
    claims: &mut Vec<LigeroLinearClaim>,
    field_layout: &BundleCircuitLayout,
    field_index: usize,
    mac_layout: &BundleCircuitLayout,
    low_half: usize,
    high_half: usize,
) {
    let (point, scale) = mac_half_x_recompose_claim_point();
    let half_term = |half, coefficient| {
        let offset = mac_batch_half_group_a_input_offset(half);
        LigeroLinearTerm {
            offset: mac_layout.input_offset + offset + MAC_HALF_X_BITS_START,
            len: GF128_BITS,
            point: point.clone(),
            coefficient,
        }
    };
    claims.push(LigeroLinearClaim::affine(
        vec![
            fixed_term(field_layout, field_index, scale),
            half_term(low_half, -Fp::ONE),
            half_term(high_half, -two_pow_128()),
        ],
        Fp::ZERO,
    ));
}

fn add_equality_claim(
    claims: &mut Vec<LigeroLinearClaim>,
    left_layout: &BundleCircuitLayout,
    left_index: usize,
    right_layout: &BundleCircuitLayout,
    right_index: usize,
) {
    claims.push(LigeroLinearClaim::affine(
        vec![
            fixed_term(left_layout, left_index, Fp::ONE),
            fixed_term(right_layout, right_index, -Fp::ONE),
        ],
        Fp::ZERO,
    ));
}

fn fixed_term(layout: &BundleCircuitLayout, index: usize, coefficient: Fp) -> LigeroLinearTerm {
    LigeroLinearTerm {
        offset: layout.input_offset,
        len: layout.input_len,
        point: fixed_point(layout.input_len, index),
        coefficient,
    }
}

fn add_fixed_claim(
    claims: &mut Vec<LigeroLinearClaim>,
    offset: usize,
    len: usize,
    index: usize,
    value: Fp,
) {
    claims.push(LigeroLinearClaim::mle(
        offset,
        len,
        fixed_point(len, index),
        value,
    ));
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
            slot: LayoutSlot::UScalars,
            circuit: build_c3_c5_scalar_setup_circuit().expect("static C3-C5 circuit is valid"),
            input: c3_c5_scalar_setup_input(input, witness)?,
        },
        ProverCircuitInstance {
            label: b"s4-ecdsa-c9-c10-ladder",
            slot: LayoutSlot::U1GAccumulators,
            circuit: build_c9_c10_ladder_circuit().expect("static C9-C10 circuit is valid"),
            input: c9_c10_ladder_input(input, witness)?,
        },
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
        // C13 slope inverses removed (WO-C3): its 1,026 interior
        // denominator/inverse pairs were committed independently and never
        // cross-bound to the C12 accumulator points, so they admitted the
        // trivial extension (1, 1). Its sole bound final pair duplicated
        // C11's existing (bx - ax) * denom_inv = 1 equation. Projecting C13
        // from an old proof, or extending a new proof with those values,
        // preserves the accepted statement relation exactly.
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
            label: b"s4-ecdsa-c9-c10-ladder",
            circuit: build_c9_c10_ladder_circuit()?,
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
    write_mac_batch_canonicality(&mut input, mac_values)?;
    Ok(input)
}

fn write_mac_batch_canonicality(
    input: &mut [Fp],
    mac_values: &[Gf128; MDOC_P4B_MAC_HALF_COUNT],
) -> Result<(), WitnessError> {
    for value in 0..MAC_BATCH_CANONICAL_VALUE_COUNT {
        let words = gf128_pair_words(&mac_values[2 * value], &mac_values[2 * value + 1]);
        if cmp_words(&words, &P256_FIELD_MODULUS).is_ge() {
            return Err(WitnessError::NonCanonicalCoordinate);
        }
        let slack = sub_words(&P256_FIELD_MODULUS_MINUS_ONE, &words);
        let mut carry = false;
        input[mac_batch_canonical_carry_index(value, 0)] = Fp::ZERO;
        for bit in 0..MAC_BATCH_CANONICAL_BITS {
            let value_bit = scalar_bit(&words, bit);
            let slack_bit = scalar_bit(&slack, bit);
            debug_assert_eq!(
                input[mac_batch_canonical_value_bit_index(value, bit)],
                fp_bit(value_bit)
            );
            input[mac_batch_canonical_slack_bit_index(value, bit)] = fp_bit(slack_bit);
            let sum = u8::from(value_bit) + u8::from(slack_bit) + u8::from(carry);
            debug_assert_eq!(
                (sum & 1) != 0,
                scalar_bit(&P256_FIELD_MODULUS_MINUS_ONE, bit)
            );
            carry = sum >= 2;
            input[mac_batch_canonical_carry_index(value, bit + 1)] = fp_bit(carry);
        }
        debug_assert!(!carry);
    }
    Ok(())
}

fn gf128_pair_words(lo: &Gf128, hi: &Gf128) -> U256Words {
    let mut words = [0u64; 4];
    for (half_index, half) in [lo, hi].into_iter().enumerate() {
        for word_index in 0..2 {
            let start = word_index * 8;
            words[half_index * 2 + word_index] =
                u64::from_le_bytes(half[start..start + 8].try_into().expect("8-byte word"));
        }
    }
    words
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
    let mut canonical = 0usize;
    for value in 0..MAC_BATCH_CANONICAL_VALUE_COUNT {
        for bit in 0..MAC_BATCH_CANONICAL_BITS {
            add_bool_constraint(
                &mut terms,
                mac_batch_tree_canonical_start() + canonical,
                mac_batch_canonical_slack_bit_index(value, bit),
            );
            canonical += 1;
        }
        for bit in 0..MAC_BATCH_CANONICAL_CARRIES {
            add_bool_constraint(
                &mut terms,
                mac_batch_tree_canonical_start() + canonical,
                mac_batch_canonical_carry_index(value, bit),
            );
            canonical += 1;
        }
        for bit in [0, MAC_BATCH_CANONICAL_BITS] {
            add_linear(
                &mut terms,
                mac_batch_tree_canonical_start() + canonical,
                mac_batch_canonical_carry_index(value, bit),
                Fp::ONE,
            );
            canonical += 1;
        }
        for bit in 0..MAC_BATCH_CANONICAL_BITS {
            let out = mac_batch_tree_canonical_start() + canonical;
            add_linear(
                &mut terms,
                out,
                mac_batch_canonical_value_bit_index(value, bit),
                Fp::ONE,
            );
            add_linear(
                &mut terms,
                out,
                mac_batch_canonical_slack_bit_index(value, bit),
                Fp::ONE,
            );
            add_linear(
                &mut terms,
                out,
                mac_batch_canonical_carry_index(value, bit),
                Fp::ONE,
            );
            add_linear(
                &mut terms,
                out,
                mac_batch_canonical_carry_index(value, bit + 1),
                -Fp::from_u64(2),
            );
            if scalar_bit(&P256_FIELD_MODULUS_MINUS_ONE, bit) {
                add_constant(&mut terms, out, -Fp::ONE);
            }
            canonical += 1;
        }
    }
    debug_assert_eq!(canonical, MAC_BATCH_CANONICAL_CONSTRAINTS);
    debug_assert!(
        mac_batch_tree_canonical_start() + canonical <= 1usize << MAC_BATCH_TREE_LOG_SIZE
    );

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
    // WO-F: `monomial_reduction_bits(power)` depends only on `power`, yet the
    // triple loop below queries it `MDOC_P4B_MAC_HALF_COUNT · GF128_BITS` times
    // per power (~196k Vec allocations + linear scans, ~24 ms of setup).
    // Precompute a per-power bitmask once (255 evaluations) and test membership
    // with a shift — byte-identical `terms` in the same order.
    let reduction_masks: Vec<u128> = (0..MAC_HALF_PRODUCT_COEFFS)
        .map(|power| {
            monomial_reduction_bits(power)
                .into_iter()
                .fold(0u128, |mask, bit| mask | (1u128 << bit))
        })
        .collect();
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
                if (reduction_masks[power] >> bit) & 1 == 1 {
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
    for index in 0..MAC_BATCH_CANONICAL_CONSTRAINTS {
        add_linear(
            &mut terms,
            mac_batch_tree_canonical_start() + index,
            mac_batch_tree_canonical_start() + index,
            Fp::ONE,
        );
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
    for index in 0..MAC_BATCH_CANONICAL_CONSTRAINTS {
        add_linear(
            &mut terms,
            mac_batch_tree_canonical_start() + index,
            mac_batch_tree_canonical_start() + index,
            Fp::ONE,
        );
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
    for index in 0..MAC_BATCH_CANONICAL_CONSTRAINTS {
        add_linear(
            &mut terms,
            mac_batch_output_canonical_start() + index,
            mac_batch_tree_canonical_start() + index,
            Fp::ONE,
        );
    }
    debug_assert!(
        mac_batch_output_canonical_start() + MAC_BATCH_CANONICAL_CONSTRAINTS
            <= 1usize << MAC_BATCH_INPUT_LOG_SIZE
    );

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

fn mac_batch_canonical_slack_bit_index(value: usize, bit: usize) -> usize {
    debug_assert!(value < MAC_BATCH_CANONICAL_VALUE_COUNT);
    debug_assert!(bit < MAC_BATCH_CANONICAL_BITS);
    MAC_BATCH_CANONICAL_SLACK_BITS_START + value * MAC_BATCH_CANONICAL_BITS + bit
}

fn mac_batch_canonical_carry_index(value: usize, bit: usize) -> usize {
    debug_assert!(value < MAC_BATCH_CANONICAL_VALUE_COUNT);
    debug_assert!(bit < MAC_BATCH_CANONICAL_CARRIES);
    MAC_BATCH_CANONICAL_CARRIES_START + value * MAC_BATCH_CANONICAL_CARRIES + bit
}

fn mac_batch_canonical_value_bit_index(value: usize, bit: usize) -> usize {
    debug_assert!(value < MAC_BATCH_CANONICAL_VALUE_COUNT);
    debug_assert!(bit < MAC_BATCH_CANONICAL_BITS);
    let half = 2 * value + bit / GF128_BITS;
    mac_batch_half_group_a_input_offset(half) + MAC_HALF_X_BITS_START + bit % GF128_BITS
}

fn mac_batch_tree_half_start(half: usize) -> usize {
    debug_assert!(half < MDOC_P4B_MAC_HALF_COUNT);
    half * MAC_BATCH_TREE_HALF_WIDTH
}

fn mac_batch_tree_canonical_start() -> usize {
    MDOC_P4B_MAC_HALF_COUNT * MAC_BATCH_TREE_HALF_WIDTH
}

fn mac_batch_output_canonical_start() -> usize {
    MDOC_P4B_MAC_HALF_COUNT * MAC_BATCH_OUTPUT_STRIDE
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
            l: C2_QX2_INDEX,
            r: C2_CONST_ONE_INDEX,
            coeff: Fp::ONE,
        },
        QuadTerm {
            out: 0,
            l: C2_QX_INDEX,
            r: C2_QX_INDEX,
            coeff: -Fp::ONE,
        },
        QuadTerm {
            out: 1,
            l: C2_QY_INDEX,
            r: C2_QY_INDEX,
            coeff: Fp::ONE,
        },
        QuadTerm {
            out: 1,
            l: C2_QX_INDEX,
            r: C2_QX2_INDEX,
            coeff: -Fp::ONE,
        },
        QuadTerm {
            out: 1,
            l: C2_QX_INDEX,
            r: C2_CONST_ONE_INDEX,
            coeff: Fp::from_u64(3),
        },
        QuadTerm {
            out: 1,
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
    let qx = parse_coordinate(input.qx)?;
    let qy = parse_coordinate(input.qy)?;

    let mut circuit_input = vec![Fp::ZERO; 1usize << C2_CANONICALITY_INPUT_LOG_SIZE];
    circuit_input[C2_CONST_ONE_INDEX as usize] = Fp::ONE;
    circuit_input[C2_QX_INDEX as usize] = qx;
    circuit_input[C2_QY_INDEX as usize] = qy;
    circuit_input[C2_QX2_INDEX as usize] = qx.square();
    Ok(circuit_input)
}

pub fn build_c3_c5_scalar_setup_circuit() -> Result<Circuit, CircuitError> {
    let mut terms = Vec::with_capacity(24_000);
    let mut out = 0usize;
    let order_limbs = words_to_limbs(&P256_ORDER);

    for scalar in 0..C3_CANONICAL_SCALAR_COUNT {
        let field_index = match scalar {
            C3_SCALAR_R => Some(C3_R_INDEX),
            C3_SCALAR_S => Some(C3_S_INDEX),
            C3_SCALAR_Z_RED => None,
            C3_SCALAR_U1 => Some(C3_U1_INDEX),
            C3_SCALAR_U2 => Some(C3_U2_INDEX),
            _ => unreachable!("fixed C3 scalar inventory"),
        };
        if let Some(field_index) = field_index {
            add_limb_recomposition_constraint(&mut terms, &mut out, field_index, |limb| {
                c3_scalar_limb_index(scalar, limb)
            });
        }
        add_canonical_lt_constraints(
            &mut terms,
            &mut out,
            |limb| c3_scalar_limb_index(scalar, limb),
            |limb| c3_scalar_bit_index(scalar, limb, 0),
            |limb| c3_slack_limb_index(scalar, limb),
            |limb| c3_slack_bit_index(scalar, limb, 0),
            |limb| c3_lt_carry_index(scalar, limb),
            &order_limbs,
            LIMB_BITS,
        );
    }

    add_limb_recomposition_constraint(&mut terms, &mut out, C3_Z_INDEX, |limb| {
        C3_Z_LIMBS_START + limb
    });
    for limb in 0..N_LIMBS {
        add_limb_range_constraints(
            &mut terms,
            &mut out,
            C3_Z_LIMBS_START + limb,
            C3_Z_BITS_START + limb * LIMB_BITS,
            if limb + 1 == N_LIMBS { 9 } else { LIMB_BITS },
        );
    }
    let field_limbs = words_to_limbs(&P256_FIELD_MODULUS);
    add_canonical_lt_constraints(
        &mut terms,
        &mut out,
        |limb| C3_Z_LIMBS_START + limb,
        |limb| C3_Z_BITS_START + limb * LIMB_BITS,
        |limb| C3_Z_SLACK_LIMBS_START + limb,
        |limb| C3_Z_SLACK_BITS_START + limb * LIMB_BITS,
        |limb| C3_Z_LT_CARRIES_START + limb,
        &field_limbs,
        9,
    );

    for product in 0..C3_PRODUCT_COUNT {
        for limb in 0..N_LIMBS {
            add_limb_range_constraints(
                &mut terms,
                &mut out,
                c3_quotient_limb_index(product, limb),
                c3_quotient_bit_index(product, limb, 0),
                if limb + 1 == N_LIMBS { 9 } else { LIMB_BITS },
            );
        }
        for carry in 0..PRODUCT_INTERNAL_CARRIES {
            for bit in 0..PRODUCT_CARRY_BITS {
                add_bool_constraint(
                    &mut terms,
                    out,
                    c3_product_carry_bit_index(product, carry, bit),
                );
                out += 1;
            }
        }
    }

    add_product_limb_constraints(
        &mut terms,
        &mut out,
        C3_SCALAR_S,
        C3_SCALAR_U1,
        C3_SCALAR_Z_RED,
        0,
        &order_limbs,
    );
    add_product_limb_constraints(
        &mut terms,
        &mut out,
        C3_SCALAR_S,
        C3_SCALAR_U2,
        C3_SCALAR_R,
        1,
        &order_limbs,
    );

    add_bool_constraint(&mut terms, out, C3_Z_GE_N_INDEX);
    out += 1;
    for borrow in 0..N_LIMBS - 1 {
        add_bool_constraint(&mut terms, out, C3_DIGEST_BORROWS_START + borrow);
        out += 1;
    }
    for limb in 0..N_LIMBS {
        add_linear(&mut terms, out, C3_Z_LIMBS_START + limb, Fp::ONE);
        add_linear(
            &mut terms,
            out,
            c3_scalar_limb_index(C3_SCALAR_Z_RED, limb),
            -Fp::ONE,
        );
        add_quadratic(
            &mut terms,
            out,
            C3_Z_GE_N_INDEX,
            C3_CONST_ONE_INDEX,
            -Fp::from_u64(order_limbs[limb] as u64),
        );
        if limb > 0 {
            add_linear(
                &mut terms,
                out,
                C3_DIGEST_BORROWS_START + limb - 1,
                -Fp::ONE,
            );
        }
        if limb + 1 < N_LIMBS {
            add_linear(
                &mut terms,
                out,
                C3_DIGEST_BORROWS_START + limb,
                Fp::from_u64(1u64 << LIMB_BITS),
            );
        }
        out += 1;
    }

    for (scalar, inverse) in [
        (C3_SCALAR_R, C3_R_NONZERO_INV_INDEX),
        (C3_SCALAR_S, C3_S_NONZERO_INV_INDEX),
    ] {
        for limb in 0..N_LIMBS {
            add_quadratic(
                &mut terms,
                out,
                c3_scalar_limb_index(scalar, limb),
                inverse,
                Fp::ONE,
            );
        }
        add_constant(&mut terms, out, -Fp::ONE);
        out += 1;
    }

    const {
        assert!(C3_Z_LT_CARRIES_START + N_LIMBS <= 1usize << C3_C5_SCALAR_SETUP_INPUT_LOG_SIZE);
    }
    debug_assert!(out <= 1usize << C3_C5_SCALAR_SETUP_OUTPUT_LOG_SIZE);
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
    let z_words = words_from_be(input.z);
    let z_field = Fp::from_bytes_be(input.z).ok_or(WitnessError::NonCanonicalScalar)?;
    let z_lt_p =
        CanonicalLtTrace::new("z", &z_words, "p", &P256_FIELD_MODULUS).map_err(map_scalar_error)?;
    c3_c5_scalar_setup_input_with_z_trace(input, witness, z_field, &z_lt_p)
}

fn c3_c5_scalar_setup_input_with_z_trace(
    input: &EcdsaInput,
    witness: &Witness,
    z_field: Fp,
    z_lt_p: &CanonicalLtTrace,
) -> Result<Vec<Fp>, WitnessError> {
    let mut circuit_input = vec![Fp::ZERO; 1usize << C3_C5_SCALAR_SETUP_INPUT_LOG_SIZE];
    circuit_input[C3_CONST_ONE_INDEX] = Fp::ONE;
    circuit_input[C3_Z_INDEX] = z_field;
    circuit_input[C3_R_INDEX] =
        Fp::from_bytes_be(input.r).ok_or(WitnessError::NonCanonicalScalar)?;
    circuit_input[C3_S_INDEX] =
        Fp::from_bytes_be(input.s).ok_or(WitnessError::NonCanonicalScalar)?;
    let us = layout_range(LayoutSlot::UScalars);
    circuit_input[C3_U1_INDEX] = witness.values[us.start];
    circuit_input[C3_U2_INDEX] = witness.values[us.start + 1];

    let trace = ScalarSetupTrace::new_with_u1_u2(
        &words_from_be(input.z),
        &words_from_be(input.r),
        &words_from_be(input.s),
        &words_from_be(circuit_input[C3_U1_INDEX].to_bytes_be()),
        &words_from_be(circuit_input[C3_U2_INDEX].to_bytes_be()),
    )
    .map_err(map_scalar_error)?;
    let canonical = [
        &trace.r_lt_n,
        &trace.s_lt_n,
        &trace.z_reduction.z_red_lt_n,
        &trace.s_u1_eq.b_lt_modulus,
        &trace.s_u2_eq.b_lt_modulus,
    ];
    for (scalar, range) in canonical.into_iter().enumerate() {
        for limb in 0..N_LIMBS {
            write_limb_and_bits(
                &mut circuit_input,
                c3_scalar_limb_index(scalar, limb),
                c3_scalar_bit_index(scalar, limb, 0),
                range.value[limb],
            );
            write_limb_and_bits(
                &mut circuit_input,
                c3_slack_limb_index(scalar, limb),
                c3_slack_bit_index(scalar, limb, 0),
                range.slack[limb],
            );
            circuit_input[c3_lt_carry_index(scalar, limb)] = fp_bit(range.carries[limb] != 0);
            debug_assert!(matches!(range.carries[limb], 0 | 1));
        }
    }

    for limb in 0..N_LIMBS {
        write_limb_and_bits(
            &mut circuit_input,
            C3_Z_LIMBS_START + limb,
            C3_Z_BITS_START + limb * LIMB_BITS,
            trace.z[limb],
        );
        write_limb_and_bits(
            &mut circuit_input,
            C3_Z_SLACK_LIMBS_START + limb,
            C3_Z_SLACK_BITS_START + limb * LIMB_BITS,
            z_lt_p.slack[limb],
        );
        debug_assert!(matches!(z_lt_p.carries[limb], 0 | 1));
        circuit_input[C3_Z_LT_CARRIES_START + limb] = Fp::from_u64(z_lt_p.carries[limb] as u64);
    }
    let products = [&trace.s_u1_eq, &trace.s_u2_eq];
    for (product, trace) in products.into_iter().enumerate() {
        for limb in 0..N_LIMBS {
            write_limb_and_bits(
                &mut circuit_input,
                c3_quotient_limb_index(product, limb),
                c3_quotient_bit_index(product, limb, 0),
                trace.mul.quotient[limb],
            );
        }
        for carry in 0..PRODUCT_INTERNAL_CARRIES {
            write_signed_carry_bits(
                &mut circuit_input,
                c3_product_carry_bit_index(product, carry, 0),
                trace.mul.carries[carry],
            );
        }
        debug_assert_eq!(trace.mul.carries[PRODUCT_EQUATION_LIMBS - 1], 0);
    }

    circuit_input[C3_Z_GE_N_INDEX] = Fp::from_u64(trace.z_reduction.z_ge_n as u64);
    for borrow in 0..N_LIMBS - 1 {
        let value = -trace.z_reduction.carries[borrow];
        debug_assert!(matches!(value, 0 | 1));
        circuit_input[C3_DIGEST_BORROWS_START + borrow] = Fp::from_u64(value as u64);
    }
    debug_assert_eq!(trace.z_reduction.carries[N_LIMBS - 1], 0);

    for (scalar, inverse) in [
        (C3_SCALAR_R, C3_R_NONZERO_INV_INDEX),
        (C3_SCALAR_S, C3_S_NONZERO_INV_INDEX),
    ] {
        let sum = (0..N_LIMBS).fold(Fp::ZERO, |acc, limb| {
            acc + circuit_input[c3_scalar_limb_index(scalar, limb)]
        });
        circuit_input[inverse] = sum.inverse().ok_or(WitnessError::ZeroScalar)?;
    }
    Ok(circuit_input)
}

fn c3_scalar_limb_index(scalar: usize, limb: usize) -> usize {
    C3_SCALAR_LIMBS_START + scalar * N_LIMBS + limb
}

fn c3_scalar_bit_index(scalar: usize, limb: usize, bit: usize) -> usize {
    C3_SCALAR_BITS_START + (scalar * N_LIMBS + limb) * LIMB_BITS + bit
}

fn c3_slack_limb_index(scalar: usize, limb: usize) -> usize {
    C3_SLACK_LIMBS_START + scalar * N_LIMBS + limb
}

fn c3_slack_bit_index(scalar: usize, limb: usize, bit: usize) -> usize {
    C3_SLACK_BITS_START + (scalar * N_LIMBS + limb) * LIMB_BITS + bit
}

fn c3_lt_carry_index(scalar: usize, limb: usize) -> usize {
    C3_LT_CARRIES_START + scalar * N_LIMBS + limb
}

fn c3_quotient_limb_index(product: usize, limb: usize) -> usize {
    C3_QUOTIENT_LIMBS_START + product * N_LIMBS + limb
}

fn c3_quotient_bit_index(product: usize, limb: usize, bit: usize) -> usize {
    C3_QUOTIENT_BITS_START + (product * N_LIMBS + limb) * LIMB_BITS + bit
}

fn c3_product_carry_bit_index(product: usize, carry: usize, bit: usize) -> usize {
    C3_PRODUCT_CARRY_BITS_START
        + (product * PRODUCT_INTERNAL_CARRIES + carry) * PRODUCT_CARRY_BITS
        + bit
}

fn add_limb_recomposition_constraint(
    terms: &mut Vec<QuadTerm>,
    out: &mut usize,
    field_index: usize,
    limb_index: impl Fn(usize) -> usize,
) {
    add_linear(terms, *out, field_index, Fp::ONE);
    let mut power = Fp::ONE;
    for limb in 0..N_LIMBS {
        add_linear(terms, *out, limb_index(limb), -power);
        for _ in 0..LIMB_BITS {
            power = power + power;
        }
    }
    *out += 1;
}

fn add_limb_range_constraints(
    terms: &mut Vec<QuadTerm>,
    out: &mut usize,
    limb_index: usize,
    bits_start: usize,
    used_bits: usize,
) {
    add_linear(terms, *out, limb_index, Fp::ONE);
    let mut power = Fp::ONE;
    for bit in 0..LIMB_BITS {
        add_linear(terms, *out, bits_start + bit, -power);
        power = power + power;
    }
    *out += 1;
    for bit in 0..LIMB_BITS {
        if bit < used_bits {
            add_bool_constraint(terms, *out, bits_start + bit);
        } else {
            add_linear(terms, *out, bits_start + bit, Fp::ONE);
        }
        *out += 1;
    }
}

#[allow(clippy::too_many_arguments)]
fn add_canonical_lt_constraints(
    terms: &mut Vec<QuadTerm>,
    out: &mut usize,
    value_limb: impl Fn(usize) -> usize,
    value_bits: impl Fn(usize) -> usize,
    slack_limb: impl Fn(usize) -> usize,
    slack_bits: impl Fn(usize) -> usize,
    carry: impl Fn(usize) -> usize,
    bound: &BigIntLimbs,
    top_bits: usize,
) {
    for limb in 0..N_LIMBS {
        let used_bits = if limb + 1 == N_LIMBS {
            top_bits
        } else {
            LIMB_BITS
        };
        add_limb_range_constraints(terms, out, value_limb(limb), value_bits(limb), used_bits);
        add_limb_range_constraints(terms, out, slack_limb(limb), slack_bits(limb), used_bits);
        add_bool_constraint(terms, *out, carry(limb));
        *out += 1;
    }
    add_linear(terms, *out, carry(N_LIMBS - 1), Fp::ONE);
    *out += 1;
    for limb in 0..N_LIMBS {
        add_linear(terms, *out, value_limb(limb), Fp::ONE);
        add_linear(terms, *out, slack_limb(limb), Fp::ONE);
        if limb == 0 {
            add_constant(terms, *out, Fp::ONE);
        } else {
            add_linear(terms, *out, carry(limb - 1), Fp::ONE);
        }
        add_constant(terms, *out, -Fp::from_u64(bound[limb] as u64));
        add_linear(terms, *out, carry(limb), -Fp::from_u64(1u64 << LIMB_BITS));
        *out += 1;
    }
}

fn add_product_limb_constraints(
    terms: &mut Vec<QuadTerm>,
    out: &mut usize,
    a: usize,
    b: usize,
    result: usize,
    product: usize,
    modulus: &BigIntLimbs,
) {
    for digit in 0..PRODUCT_EQUATION_LIMBS {
        for a_limb in 0..N_LIMBS {
            let Some(b_limb) = digit.checked_sub(a_limb) else {
                continue;
            };
            if b_limb < N_LIMBS {
                add_quadratic(
                    terms,
                    *out,
                    c3_scalar_limb_index(a, a_limb),
                    c3_scalar_limb_index(b, b_limb),
                    Fp::ONE,
                );
            }
        }
        for quotient_limb in 0..N_LIMBS {
            let Some(modulus_limb) = digit.checked_sub(quotient_limb) else {
                continue;
            };
            if modulus_limb < N_LIMBS {
                add_linear(
                    terms,
                    *out,
                    c3_quotient_limb_index(product, quotient_limb),
                    -Fp::from_u64(modulus[modulus_limb] as u64),
                );
            }
        }
        if digit < N_LIMBS {
            add_linear(terms, *out, c3_scalar_limb_index(result, digit), -Fp::ONE);
        }
        if digit > 0 {
            add_signed_carry(terms, *out, product, digit - 1, Fp::ONE);
        }
        if digit + 1 < PRODUCT_EQUATION_LIMBS {
            add_signed_carry(
                terms,
                *out,
                product,
                digit,
                -Fp::from_u64(1u64 << LIMB_BITS),
            );
        }
        *out += 1;
    }
}

fn add_signed_carry(
    terms: &mut Vec<QuadTerm>,
    out: usize,
    product: usize,
    carry: usize,
    coefficient: Fp,
) {
    let mut power = Fp::ONE;
    for bit in 0..PRODUCT_CARRY_BITS {
        add_linear(
            terms,
            out,
            c3_product_carry_bit_index(product, carry, bit),
            coefficient * power,
        );
        power = power + power;
    }
    add_constant(
        terms,
        out,
        -coefficient * Fp::from_u64(PRODUCT_CARRY_OFFSET as u64),
    );
}

fn write_limb_and_bits(input: &mut [Fp], limb_index: usize, bits_start: usize, value: u32) {
    input[limb_index] = Fp::from_u64(value as u64);
    for bit in 0..LIMB_BITS {
        input[bits_start + bit] = Fp::from_u64(((value >> bit) & 1) as u64);
    }
}

fn write_signed_carry_bits(input: &mut [Fp], bits_start: usize, carry: i64) {
    let encoded = carry + PRODUCT_CARRY_OFFSET;
    debug_assert!((0..(1i64 << PRODUCT_CARRY_BITS)).contains(&encoded));
    for bit in 0..PRODUCT_CARRY_BITS {
        input[bits_start + bit] = Fp::from_u64(((encoded >> bit) & 1) as u64);
    }
}

fn c9_bit_index(ladder: usize, bit: usize) -> usize {
    C9_BITS_START_INDEX + ladder * C9_SCALAR_BITS + bit
}

fn c9_started_index(ladder: usize, step: usize) -> usize {
    C9_STARTED_START_INDEX + ladder * (C9_SCALAR_BITS + 1) + step
}

fn c9_step_index(ladder: usize, step: usize, wire: usize) -> usize {
    C9_STEPS_START_INDEX + (ladder * C9_SCALAR_BITS + step) * C9_STEP_WIDTH + wire
}

fn c9_corrected_index(ladder: usize, coordinate: usize) -> usize {
    C9_CORRECTED_START_INDEX + ladder * 2 + coordinate
}

fn c9_canonical_slack_index(ladder: usize, bit: usize) -> usize {
    C9_CANONICAL_SLACK_START_INDEX + ladder * C9_SCALAR_BITS + bit
}

fn c9_canonical_carry_index(ladder: usize, bit: usize) -> usize {
    C9_CANONICAL_CARRY_START_INDEX + ladder * (C9_SCALAR_BITS + 1) + bit
}

/// Constrains both ECDSA scalar-multiplication ladders. Each scalar is
/// bit-decomposed and recomposed, every double/add transition is checked, the
/// u2 ladder base is the same public key used by C2, and each final accumulator
/// is the corrected endpoint consumed by C11.
pub fn build_c9_c10_ladder_circuit() -> Result<Circuit, CircuitError> {
    let mut terms = Vec::with_capacity(24_000);
    let mut out = 0usize;

    for ladder in 0..C9_LADDER_COUNT {
        let u = if ladder == 0 {
            C9_U1_INDEX
        } else {
            C9_U2_INDEX
        };
        let (base_x, base_y) = if ladder == 0 {
            (C9_GX_INDEX, C9_GY_INDEX)
        } else {
            (C9_QX_INDEX, C9_QY_INDEX)
        };

        // u = sum(bit_i * 2^i), with every bit Boolean.
        let recompose_out = out;
        out += 1;
        add_linear(&mut terms, recompose_out, u, Fp::ONE);
        let mut power = Fp::ONE;
        for bit in 0..C9_SCALAR_BITS {
            let bit_wire = c9_bit_index(ladder, bit);
            add_linear(&mut terms, recompose_out, bit_wire, -power);
            add_bool_constraint(&mut terms, out, bit_wire);
            out += 1;
            power = power + power;
        }

        // Exact integer range proof: bits + slack = n - 1 with a Boolean
        // carry chain and no final carry. This removes the alternate
        // representation bits(u + p) and rejects scalars outside the group
        // order even though they are valid base-field elements.
        for bit in 0..C9_SCALAR_BITS {
            add_bool_constraint(&mut terms, out, c9_canonical_slack_index(ladder, bit));
            out += 1;
        }
        for bit in 0..=C9_SCALAR_BITS {
            add_bool_constraint(&mut terms, out, c9_canonical_carry_index(ladder, bit));
            out += 1;
        }
        add_linear(
            &mut terms,
            out,
            c9_canonical_carry_index(ladder, 0),
            Fp::ONE,
        );
        out += 1;
        add_linear(
            &mut terms,
            out,
            c9_canonical_carry_index(ladder, C9_SCALAR_BITS),
            Fp::ONE,
        );
        out += 1;
        for bit in 0..C9_SCALAR_BITS {
            add_linear(&mut terms, out, c9_bit_index(ladder, bit), Fp::ONE);
            add_linear(
                &mut terms,
                out,
                c9_canonical_slack_index(ladder, bit),
                Fp::ONE,
            );
            add_linear(
                &mut terms,
                out,
                c9_canonical_carry_index(ladder, bit),
                Fp::ONE,
            );
            add_linear(
                &mut terms,
                out,
                c9_canonical_carry_index(ladder, bit + 1),
                -Fp::from_u64(2),
            );
            if scalar_bit(&P256_ORDER_MINUS_ONE, bit) {
                add_constant(&mut terms, out, -Fp::ONE);
            }
            out += 1;
        }

        // `started` is the prefix-OR of the scalar bits. Before the first set
        // bit the affine accumulator stays at the base, avoiding an unencoded
        // point-at-infinity state. Non-zero u is required by the existing
        // witness domain.
        add_linear(&mut terms, out, c9_started_index(ladder, 0), Fp::ONE);
        out += 1;
        for step in 0..C9_SCALAR_BITS {
            let bit = c9_bit_index(ladder, C9_SCALAR_BITS - 1 - step);
            let started = c9_started_index(ladder, step);
            let next_started = c9_started_index(ladder, step + 1);
            add_linear(&mut terms, out, next_started, Fp::ONE);
            add_linear(&mut terms, out, started, -Fp::ONE);
            add_linear(&mut terms, out, bit, -Fp::ONE);
            add_quadratic(&mut terms, out, started, bit, Fp::ONE);
            out += 1;
        }
        add_linear(
            &mut terms,
            out,
            c9_started_index(ladder, C9_SCALAR_BITS),
            Fp::ONE,
        );
        add_constant(&mut terms, out, -Fp::ONE);
        out += 1;

        for step in 0..C9_SCALAR_BITS {
            let bit = c9_bit_index(ladder, C9_SCALAR_BITS - 1 - step);
            let started = c9_started_index(ladder, step);
            let (current_x, current_y) = if step == 0 {
                (base_x, base_y)
            } else {
                (
                    c9_step_index(ladder, step - 1, C9_STEP_NEXT_X),
                    c9_step_index(ladder, step - 1, C9_STEP_NEXT_Y),
                )
            };
            let next_x = c9_step_index(ladder, step, C9_STEP_NEXT_X);
            let next_y = c9_step_index(ladder, step, C9_STEP_NEXT_Y);
            let double_x = c9_step_index(ladder, step, C9_STEP_DOUBLE_X);
            let double_y = c9_step_index(ladder, step, C9_STEP_DOUBLE_Y);
            let double_lambda = c9_step_index(ladder, step, C9_STEP_DOUBLE_LAMBDA);
            let double_denom_inv = c9_step_index(ladder, step, C9_STEP_DOUBLE_DENOM_INV);
            let add_lambda = c9_step_index(ladder, step, C9_STEP_ADD_LAMBDA);
            let add_denom_inv = c9_step_index(ladder, step, C9_STEP_ADD_DENOM_INV);
            let add_delta_x = c9_step_index(ladder, step, C9_STEP_ADD_DELTA_X);
            let add_delta_y = c9_step_index(ladder, step, C9_STEP_ADD_DELTA_Y);
            let active_bit = c9_step_index(ladder, step, C9_STEP_ACTIVE_BIT);

            // Affine doubling on y^2 = x^3 - 3x + b.
            add_quadratic(
                &mut terms,
                out,
                current_y,
                double_denom_inv,
                Fp::from_u64(2),
            );
            add_constant(&mut terms, out, -Fp::ONE);
            out += 1;
            add_quadratic(&mut terms, out, double_lambda, current_y, Fp::from_u64(2));
            add_quadratic(&mut terms, out, current_x, current_x, -Fp::from_u64(3));
            add_constant(&mut terms, out, Fp::from_u64(3));
            out += 1;
            add_linear(&mut terms, out, double_x, Fp::ONE);
            add_quadratic(&mut terms, out, double_lambda, double_lambda, -Fp::ONE);
            add_linear(&mut terms, out, current_x, Fp::from_u64(2));
            out += 1;
            add_linear(&mut terms, out, double_y, Fp::ONE);
            add_quadratic(&mut terms, out, double_lambda, current_x, -Fp::ONE);
            add_quadratic(&mut terms, out, double_lambda, double_x, Fp::ONE);
            add_linear(&mut terms, out, current_y, Fp::ONE);
            out += 1;

            // Conditional mixed-add. When the scalar bit is zero, the inverse
            // and slope may be zero and the candidate delta is not selected.
            add_quadratic(&mut terms, out, base_x, add_denom_inv, Fp::ONE);
            add_quadratic(&mut terms, out, double_x, add_denom_inv, -Fp::ONE);
            add_linear(&mut terms, out, bit, -Fp::ONE);
            out += 1;
            add_quadratic(&mut terms, out, add_lambda, base_x, Fp::ONE);
            add_quadratic(&mut terms, out, add_lambda, double_x, -Fp::ONE);
            add_quadratic(&mut terms, out, bit, base_y, -Fp::ONE);
            add_quadratic(&mut terms, out, bit, double_y, Fp::ONE);
            out += 1;
            add_linear(&mut terms, out, add_delta_x, Fp::ONE);
            add_quadratic(&mut terms, out, add_lambda, add_lambda, -Fp::ONE);
            add_linear(&mut terms, out, double_x, Fp::from_u64(2));
            add_linear(&mut terms, out, base_x, Fp::ONE);
            out += 1;
            add_linear(&mut terms, out, add_delta_y, Fp::ONE);
            add_quadratic(&mut terms, out, add_lambda, add_delta_x, Fp::ONE);
            add_linear(&mut terms, out, double_y, Fp::from_u64(2));
            out += 1;

            // `active_bit = started * bit`: the candidate add is selected only
            // after the first set bit has initialized the affine accumulator.
            add_linear(&mut terms, out, active_bit, Fp::ONE);
            add_quadratic(&mut terms, out, started, bit, -Fp::ONE);
            out += 1;

            // Before the first set bit the accumulator remains `base`.
            // Afterwards it is `double`, plus the constrained add delta iff
            // `active_bit` is one. Expressing this directly saves one input
            // wire per coordinate while preserving the exact transition.
            add_linear(&mut terms, out, next_x, Fp::ONE);
            add_linear(&mut terms, out, base_x, -Fp::ONE);
            add_quadratic(&mut terms, out, started, double_x, -Fp::ONE);
            add_quadratic(&mut terms, out, started, base_x, Fp::ONE);
            add_quadratic(&mut terms, out, active_bit, add_delta_x, -Fp::ONE);
            out += 1;
            add_linear(&mut terms, out, next_y, Fp::ONE);
            add_linear(&mut terms, out, base_y, -Fp::ONE);
            add_quadratic(&mut terms, out, started, double_y, -Fp::ONE);
            add_quadratic(&mut terms, out, started, base_y, Fp::ONE);
            add_quadratic(&mut terms, out, active_bit, add_delta_y, -Fp::ONE);
            out += 1;
        }

        for coordinate in 0..2 {
            add_linear(
                &mut terms,
                out,
                c9_step_index(
                    ladder,
                    C9_SCALAR_BITS - 1,
                    if coordinate == 0 {
                        C9_STEP_NEXT_X
                    } else {
                        C9_STEP_NEXT_Y
                    },
                ),
                Fp::ONE,
            );
            add_linear(
                &mut terms,
                out,
                c9_corrected_index(ladder, coordinate),
                -Fp::ONE,
            );
            out += 1;
        }
    }

    debug_assert!(out <= 1usize << C9_C10_LADDER_OUTPUT_LOG_SIZE);
    Circuit::new(vec![Layer::new(
        C9_C10_LADDER_OUTPUT_LOG_SIZE,
        C9_C10_LADDER_INPUT_LOG_SIZE,
        terms,
    )?])
}

pub fn c9_c10_ladder_input(input: &EcdsaInput, witness: &Witness) -> Result<Vec<Fp>, WitnessError> {
    if witness.values.len() != LAYOUT_LEN {
        return Err(WitnessError::LayoutMismatch);
    }
    let mut circuit_input = vec![Fp::ZERO; 1usize << C9_C10_LADDER_INPUT_LOG_SIZE];
    circuit_input[C9_CONST_ONE_INDEX] = Fp::ONE;
    let us = layout_range(LayoutSlot::UScalars);
    circuit_input[C9_U1_INDEX] = witness.values[us.start];
    circuit_input[C9_U2_INDEX] = witness.values[us.start + 1];
    circuit_input[C9_QX_INDEX] =
        Fp::from_bytes_be(input.qx).ok_or(WitnessError::NonCanonicalCoordinate)?;
    circuit_input[C9_QY_INDEX] =
        Fp::from_bytes_be(input.qy).ok_or(WitnessError::NonCanonicalCoordinate)?;
    let (gx, gy) = projective_point_coords(ProjectivePoint::GENERATOR)?;
    circuit_input[C9_GX_INDEX] = gx;
    circuit_input[C9_GY_INDEX] = gy;

    let scalar_words = [
        words_from_be(circuit_input[C9_U1_INDEX].to_bytes_be()),
        words_from_be(circuit_input[C9_U2_INDEX].to_bytes_be()),
    ];
    let bases = [
        (gx, gy),
        (circuit_input[C9_QX_INDEX], circuit_input[C9_QY_INDEX]),
    ];
    let slots = [LayoutSlot::U1GAccumulators, LayoutSlot::U2QAccumulators];

    for ladder in 0..C9_LADDER_COUNT {
        if cmp_words(&scalar_words[ladder], &P256_ORDER).is_ge() {
            return Err(WitnessError::NonCanonicalScalar);
        }
        for bit in 0..C9_SCALAR_BITS {
            circuit_input[c9_bit_index(ladder, bit)] =
                fp_bit(scalar_bit(&scalar_words[ladder], bit));
        }

        let canonical_slack = sub_words(&P256_ORDER_MINUS_ONE, &scalar_words[ladder]);
        let mut carry = false;
        circuit_input[c9_canonical_carry_index(ladder, 0)] = Fp::ZERO;
        for bit in 0..C9_SCALAR_BITS {
            let scalar_is_set = scalar_bit(&scalar_words[ladder], bit);
            let slack_bit = scalar_bit(&canonical_slack, bit);
            circuit_input[c9_canonical_slack_index(ladder, bit)] = fp_bit(slack_bit);
            let sum = u8::from(scalar_is_set) + u8::from(slack_bit) + u8::from(carry);
            debug_assert_eq!((sum & 1) != 0, scalar_bit(&P256_ORDER_MINUS_ONE, bit),);
            carry = sum >= 2;
            circuit_input[c9_canonical_carry_index(ladder, bit + 1)] = fp_bit(carry);
        }
        debug_assert!(!carry);

        let mut started = false;
        circuit_input[c9_started_index(ladder, 0)] = Fp::ZERO;
        let accumulator_range = layout_range(slots[ladder]);
        let (base_x, base_y) = bases[ladder];
        let mut bits = Vec::with_capacity(C9_SCALAR_BITS);
        let mut started_before = Vec::with_capacity(C9_SCALAR_BITS);
        let mut current_points = Vec::with_capacity(C9_SCALAR_BITS);
        for step in 0..C9_SCALAR_BITS {
            let bit = scalar_bit(&scalar_words[ladder], C9_SCALAR_BITS - 1 - step);
            let (current_x, current_y) = if step == 0 {
                (base_x, base_y)
            } else {
                let offset = accumulator_range.start + (step - 1) * 2;
                (witness.values[offset], witness.values[offset + 1])
            };
            let next_offset = accumulator_range.start + step * 2;
            circuit_input[c9_step_index(ladder, step, C9_STEP_NEXT_X)] =
                witness.values[next_offset];
            circuit_input[c9_step_index(ladder, step, C9_STEP_NEXT_Y)] =
                witness.values[next_offset + 1];

            bits.push(bit);
            started_before.push(started);
            current_points.push((current_x, current_y));
            started |= bit;
            circuit_input[c9_started_index(ladder, step + 1)] = fp_bit(started);
        }

        let double_denominators = current_points
            .iter()
            .map(|(_, current_y)| *current_y + *current_y)
            .collect::<Vec<_>>();
        if double_denominators.contains(&Fp::ZERO) {
            return Err(WitnessError::ExceptionalTrace);
        }
        let double_denom_inverses = Fp::batch_inverse(&double_denominators);
        let doubled_points = current_points
            .iter()
            .zip(&double_denom_inverses)
            .map(|(&(current_x, current_y), &double_denom_inv)| {
                let double_lambda =
                    (Fp::from_u64(3) * current_x.square() - Fp::from_u64(3)) * double_denom_inv;
                let double_x = double_lambda.square() - current_x - current_x;
                let double_y = double_lambda * (current_x - double_x) - current_y;
                (double_x, double_y, double_lambda)
            })
            .collect::<Vec<_>>();
        let add_denominators = bits
            .iter()
            .zip(&doubled_points)
            .map(
                |(&bit, &(double_x, _, _))| {
                    if bit {
                        base_x - double_x
                    } else {
                        Fp::ZERO
                    }
                },
            )
            .collect::<Vec<_>>();
        if bits
            .iter()
            .zip(&add_denominators)
            .any(|(&bit, &denominator)| bit && denominator == Fp::ZERO)
        {
            return Err(WitnessError::ExceptionalTrace);
        }
        let add_denom_inverses = Fp::batch_inverse(&add_denominators);

        for step in 0..C9_SCALAR_BITS {
            let bit = bits[step];
            let (double_x, double_y, double_lambda) = doubled_points[step];
            let double_denom_inv = double_denom_inverses[step];
            let (add_lambda, add_denom_inv) = if bit {
                let inv = add_denom_inverses[step];
                ((base_y - double_y) * inv, inv)
            } else {
                (Fp::ZERO, Fp::ZERO)
            };
            let add_delta_x = add_lambda.square() - double_x - double_x - base_x;
            let add_delta_y = -add_lambda * add_delta_x - double_y - double_y;
            for (wire, value) in [
                (C9_STEP_DOUBLE_X, double_x),
                (C9_STEP_DOUBLE_Y, double_y),
                (C9_STEP_DOUBLE_LAMBDA, double_lambda),
                (C9_STEP_DOUBLE_DENOM_INV, double_denom_inv),
                (C9_STEP_ADD_LAMBDA, add_lambda),
                (C9_STEP_ADD_DENOM_INV, add_denom_inv),
                (C9_STEP_ADD_DELTA_X, add_delta_x),
                (C9_STEP_ADD_DELTA_Y, add_delta_y),
                (C9_STEP_ACTIVE_BIT, fp_bit(started_before[step] && bit)),
            ] {
                circuit_input[c9_step_index(ladder, step, wire)] = value;
            }
        }
    }

    let corrected = layout_range(LayoutSlot::CorrectedEndpoints);
    circuit_input[C9_CORRECTED_START_INDEX..C9_CORRECTED_START_INDEX + 4]
        .copy_from_slice(&witness.values[corrected]);
    Ok(circuit_input)
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

pub fn build_c14_c15_final_check_circuit() -> Result<Circuit, CircuitError> {
    let mut terms = Vec::with_capacity(8_000);
    let mut out = 0usize;
    let order_limbs = words_to_limbs(&P256_ORDER);
    let field_limbs = words_to_limbs(&P256_FIELD_MODULUS);

    add_limb_recomposition_constraint(&mut terms, &mut out, C14_SIGNATURE_R_INDEX, |limb| {
        C14_R_LIMBS_START + limb
    });
    add_canonical_lt_constraints(
        &mut terms,
        &mut out,
        |limb| C14_R_LIMBS_START + limb,
        |limb| C14_R_BITS_START + limb * LIMB_BITS,
        |limb| C14_R_SLACK_LIMBS_START + limb,
        |limb| C14_R_SLACK_BITS_START + limb * LIMB_BITS,
        |limb| C14_R_LT_CARRIES_START + limb,
        &order_limbs,
        LIMB_BITS,
    );

    add_limb_recomposition_constraint(&mut terms, &mut out, C14_RX_INDEX, |limb| {
        C14_RX_LIMBS_START + limb
    });
    add_canonical_lt_constraints(
        &mut terms,
        &mut out,
        |limb| C14_RX_LIMBS_START + limb,
        |limb| C14_RX_BITS_START + limb * LIMB_BITS,
        |limb| C14_RX_SLACK_LIMBS_START + limb,
        |limb| C14_RX_SLACK_BITS_START + limb * LIMB_BITS,
        |limb| C14_RX_LT_CARRIES_START + limb,
        &field_limbs,
        LIMB_BITS,
    );

    add_bool_constraint(&mut terms, out, C14_K_INDEX);
    out += 1;
    for borrow in 0..N_LIMBS - 1 {
        add_bool_constraint(&mut terms, out, C14_REDUCTION_BORROWS_START + borrow);
        out += 1;
    }
    for limb in 0..N_LIMBS {
        add_linear(&mut terms, out, C14_RX_LIMBS_START + limb, Fp::ONE);
        add_linear(&mut terms, out, C14_R_LIMBS_START + limb, -Fp::ONE);
        add_linear(
            &mut terms,
            out,
            C14_K_INDEX,
            -Fp::from_u64(order_limbs[limb] as u64),
        );
        if limb > 0 {
            add_linear(
                &mut terms,
                out,
                C14_REDUCTION_BORROWS_START + limb - 1,
                -Fp::ONE,
            );
        }
        if limb + 1 < N_LIMBS {
            add_linear(
                &mut terms,
                out,
                C14_REDUCTION_BORROWS_START + limb,
                Fp::from_u64(1u64 << LIMB_BITS),
            );
        }
        out += 1;
    }

    const {
        assert!(C14_REDUCTION_BORROWS_START + N_LIMBS - 1 <= 1usize << C14_C15_INPUT_LOG_SIZE);
    }
    debug_assert!(out <= 1usize << C14_C15_OUTPUT_LOG_SIZE);
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
    circuit_input[C14_CONST_ONE_INDEX] = Fp::ONE;

    let final_point = layout_range(LayoutSlot::FinalPoint);
    circuit_input[C14_RX_INDEX] = witness.values[final_point.start];
    circuit_input[C14_SIGNATURE_R_INDEX] =
        Fp::from_bytes_be(input.r).ok_or(WitnessError::NonCanonicalScalar)?;

    let final_reduction = layout_range(LayoutSlot::FinalReduction);
    circuit_input[C14_K_INDEX] = witness.values[final_reduction.start];
    let reduction_flag = if circuit_input[C14_K_INDEX] == Fp::ZERO {
        0u32
    } else if circuit_input[C14_K_INDEX] == Fp::ONE {
        1u32
    } else {
        return Err(WitnessError::ConstraintViolation {
            slot: LayoutSlot::FinalReduction,
        });
    };

    let r_words = words_from_be(input.r);
    let rx_words = words_from_be(circuit_input[C14_RX_INDEX].to_bytes_be());
    let r_lt_n =
        CanonicalLtTrace::new("r", &r_words, "n", &P256_ORDER).map_err(map_scalar_error)?;
    let rx_lt_p = CanonicalLtTrace::new("rx", &rx_words, "p", &P256_FIELD_MODULUS)
        .map_err(map_scalar_error)?;
    for (range, limbs_start, bits_start, slack_start, slack_bits_start, carries_start) in [
        (
            &r_lt_n,
            C14_R_LIMBS_START,
            C14_R_BITS_START,
            C14_R_SLACK_LIMBS_START,
            C14_R_SLACK_BITS_START,
            C14_R_LT_CARRIES_START,
        ),
        (
            &rx_lt_p,
            C14_RX_LIMBS_START,
            C14_RX_BITS_START,
            C14_RX_SLACK_LIMBS_START,
            C14_RX_SLACK_BITS_START,
            C14_RX_LT_CARRIES_START,
        ),
    ] {
        for limb in 0..N_LIMBS {
            write_limb_and_bits(
                &mut circuit_input,
                limbs_start + limb,
                bits_start + limb * LIMB_BITS,
                range.value[limb],
            );
            write_limb_and_bits(
                &mut circuit_input,
                slack_start + limb,
                slack_bits_start + limb * LIMB_BITS,
                range.slack[limb],
            );
            debug_assert!(matches!(range.carries[limb], 0 | 1));
            circuit_input[carries_start + limb] = Fp::from_u64(range.carries[limb] as u64);
        }
    }

    let order_limbs = words_to_limbs(&P256_ORDER);
    let mut borrow = 0i64;
    for limb in 0..N_LIMBS {
        let total = i64::from(rx_lt_p.value[limb])
            - i64::from(r_lt_n.value[limb])
            - i64::from(reduction_flag) * i64::from(order_limbs[limb])
            - borrow;
        if total % (1i64 << LIMB_BITS) != 0 {
            return Err(WitnessError::ConstraintViolation {
                slot: LayoutSlot::FinalReduction,
            });
        }
        borrow = -total / (1i64 << LIMB_BITS);
        if !matches!(borrow, 0 | 1) {
            return Err(WitnessError::ConstraintViolation {
                slot: LayoutSlot::FinalReduction,
            });
        }
        if limb + 1 < N_LIMBS {
            circuit_input[C14_REDUCTION_BORROWS_START + limb] = Fp::from_u64(borrow as u64);
        }
    }
    if borrow != 0 {
        return Err(WitnessError::ConstraintViolation {
            slot: LayoutSlot::FinalReduction,
        });
    }
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

fn projective_point_bytes(point: ProjectivePoint) -> Result<([u8; 32], [u8; 32]), WitnessError> {
    if bool::from(point.is_identity()) {
        return Err(WitnessError::ExceptionalTrace);
    }
    let encoded = point.to_affine().to_encoded_point(false);
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
    let mut acc = base;
    let mut started = false;
    let mut accumulators = [base; 256];

    for (index, bit) in (0..256usize).rev().enumerate() {
        let bit = scalar_bit(scalar_words, bit);
        if started {
            let doubled = acc.double();
            acc = if bit { doubled + base } else { doubled };
        } else if bit {
            // Start at the first set bit instead of the point at infinity. This
            // makes the last committed accumulator exactly scalar * base, so
            // the circuit can bind it directly to the corrected endpoint.
            started = true;
        }
        if bool::from(acc.is_identity()) {
            return Err(WitnessError::ExceptionalTrace);
        }
        accumulators[index] = acc;
    }
    if !started {
        return Err(WitnessError::ExceptionalTrace);
    }
    let mut normalized = [P256AffinePoint::default(); 256];
    ProjectivePoint::batch_normalize(&accumulators, &mut normalized);
    let out = &mut values[range];
    for (index, point) in normalized.iter().enumerate() {
        write_affine_point(out, index * 2, point)?;
    }
    Ok(acc)
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
    segments.push(b"s4-ecdsa-public-projection-v2".to_vec());
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
    write_affine_point(out, offset, &point.to_affine())
}

fn write_affine_point(
    out: &mut [Fp],
    offset: usize,
    point: &P256AffinePoint,
) -> Result<(), WitnessError> {
    let encoded = point.to_encoded_point(false);
    let mut x = [0u8; 32];
    let mut y = [0u8; 32];
    x.copy_from_slice(encoded.x().ok_or(WitnessError::ExceptionalTrace)?);
    y.copy_from_slice(encoded.y().ok_or(WitnessError::ExceptionalTrace)?);
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
    use p256::ecdsa::signature::Signer;
    use p256::ecdsa::{Signature as P256Signature, SigningKey};
    use sha2::Sha256;

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

    fn signed_p4b_input(secret: u8, message: &[u8]) -> EcdsaInput {
        let signing_key = SigningKey::from_bytes((&[secret; 32]).into()).unwrap();
        let signature: P256Signature = signing_key.sign(message);
        let public_key = signing_key.verifying_key().to_encoded_point(false);
        let mut qx = [0u8; 32];
        let mut qy = [0u8; 32];
        qx.copy_from_slice(public_key.x().unwrap());
        qy.copy_from_slice(public_key.y().unwrap());
        EcdsaInput {
            z: Sha256::digest(message).into(),
            r: signature.r().to_bytes().into(),
            s: signature.s().to_bytes().into(),
            qx,
            qy,
        }
    }

    #[test]
    fn c9_c10_ladder_layout_fits_declared_input_domain() {
        let last_input = c9_canonical_carry_index(C9_LADDER_COUNT - 1, C9_SCALAR_BITS);
        assert!(last_input < 1usize << C9_C10_LADDER_INPUT_LOG_SIZE);
    }

    #[test]
    fn mac_batch_rejects_base_field_alias_bits() {
        let key_shares = p4b_microbench_key_shares();
        let av = [0x5au8; 16];
        let zero_values = [[0u8; 16]; MDOC_P4B_MAC_HALF_COUNT];
        let mut alias_values = zero_values;
        let alias = gf128_halves_from_be32(be_from_words(&P256_FIELD_MODULUS));
        alias_values[4] = alias[0];
        alias_values[5] = alias[1];
        assert_eq!(
            recompose_gf128_halves(&alias[0], &alias[1]),
            Fp::ZERO,
            "p aliases zero in the base field"
        );
        assert!(
            mac_batch_group_a_input(&key_shares, &alias_values).is_err(),
            "the honest input builder must reject the non-canonical bytes"
        );

        let mut group_a =
            mac_batch_group_a_input(&key_shares, &zero_values).expect("zero values are canonical");
        for half in 4..6 {
            let offset = mac_batch_half_group_a_input_offset(half);
            let alias_half =
                mac_half_group_a_input(&key_shares.0[half], &alias_values[half]).unwrap();
            group_a[offset..offset + alias_half.len()].copy_from_slice(&alias_half);
        }
        let tags: [Gf128; MDOC_P4B_MAC_HALF_COUNT] =
            std::array::from_fn(|half| gf128_tag(&key_shares.0[half], &av, &alias_values[half]));
        let group_b = mac_batch_group_b_input(&key_shares, &av, &alias_values, &tags).unwrap();
        let mut input = vec![Fp::ZERO; 1usize << MAC_BATCH_INPUT_LOG_SIZE];
        input[..group_a.len()].copy_from_slice(&group_a);
        input[MAC_BATCH_GROUP_B_INPUT_START..MAC_BATCH_GROUP_B_INPUT_START + group_b.len()]
            .copy_from_slice(&group_b);

        let circuit = build_mac_batch_circuit(&av, &tags).expect("MAC batch circuit builds");
        let layers = circuit
            .evaluate_input(input)
            .expect("input has circuit width");
        assert!(
            !circuit
                .is_satisfied(&layers)
                .expect("circuit shape is valid"),
            "the in-circuit p-bound must reject bits that only match modulo p"
        );
    }

    #[test]
    fn c9_scalar_bits_reject_group_order() {
        // `n` is a valid P-256 base-field element but is not a canonical
        // scalar. Build the
        // otherwise-consistent wrapping slack/carry witness: every per-bit
        // addition equation holds, but the required zero final carry rejects
        // this non-canonical 256-bit representative.
        let alias = P256_ORDER;

        let mut slack = [0u64; 4];
        let mut borrow = 0u64;
        for word in 0..4 {
            let (first, first_borrow) = P256_ORDER_MINUS_ONE[word].overflowing_sub(alias[word]);
            let (value, second_borrow) = first.overflowing_sub(borrow);
            slack[word] = value;
            borrow = u64::from(first_borrow) + u64::from(second_borrow);
        }
        assert_eq!(borrow, 1, "n is larger than the canonical bound n - 1");
        let mut input = vec![Fp::ZERO; 1usize << C9_C10_LADDER_INPUT_LOG_SIZE];
        input[C9_CONST_ONE_INDEX] = Fp::ONE;
        input[C9_U1_INDEX] = fp_from_words(&alias);
        let mut carry = false;
        for bit in 0..C9_SCALAR_BITS {
            let alias_bit = scalar_bit(&alias, bit);
            let slack_bit = scalar_bit(&slack, bit);
            input[c9_bit_index(0, bit)] = fp_bit(alias_bit);
            input[c9_canonical_slack_index(0, bit)] = fp_bit(slack_bit);
            input[c9_canonical_carry_index(0, bit)] = fp_bit(carry);
            carry = u8::from(alias_bit) + u8::from(slack_bit) + u8::from(carry) >= 2;
        }
        input[c9_canonical_carry_index(0, C9_SCALAR_BITS)] = fp_bit(carry);
        assert!(carry, "n plus its wrapping slack must overflow");

        let circuit = build_c9_c10_ladder_circuit().expect("C9-C10 circuit builds");
        let layers = circuit
            .evaluate_input(input)
            .expect("input has circuit width");
        let final_carry_constraint = 1 + C9_SCALAR_BITS + C9_SCALAR_BITS + (C9_SCALAR_BITS + 1) + 1;
        assert_eq!(
            layers[0][0],
            Fp::ZERO,
            "field recomposition accepts n as a base-field element"
        );
        assert_eq!(
            layers[0][final_carry_constraint],
            Fp::ONE,
            "the canonical range proof must expose the overflow"
        );
        assert!(!circuit
            .is_satisfied(&layers)
            .expect("circuit shape is valid"));
    }

    #[test]
    fn c3_integer_trace_accepts_digest_reduction_and_rejects_trace_mutations() {
        let mut input = signed_p4b_input(7, b"c3 integer trace");
        let mut digest = P256_ORDER;
        digest[0] += 1;
        input.z = be_from_words(&digest);
        let witness = generate_witness(&input).expect("z = n + 1 has a valid scalar setup");
        let circuit = build_c3_c5_scalar_setup_circuit().expect("C3 circuit builds");
        let honest = c3_c5_scalar_setup_input(&input, &witness).expect("C3 input builds");
        let honest_layers = circuit
            .evaluate_input(honest.clone())
            .expect("input has circuit width");
        assert!(
            circuit
                .is_satisfied(&honest_layers)
                .expect("circuit shape is valid"),
            "the digest must be reduced modulo n before computing u1"
        );

        let mut bad_quotient = honest.clone();
        bad_quotient[c3_quotient_limb_index(0, 0)] =
            bad_quotient[c3_quotient_limb_index(0, 0)] + Fp::ONE;
        let layers = circuit
            .evaluate_input(bad_quotient)
            .expect("input has circuit width");
        assert!(
            !circuit
                .is_satisfied(&layers)
                .expect("circuit shape is valid"),
            "changing the integer quotient must break the product trace"
        );

        let mut bad_carry = honest;
        let carry_bit = c3_product_carry_bit_index(0, 0, 0);
        bad_carry[carry_bit] = Fp::ONE - bad_carry[carry_bit];
        let layers = circuit
            .evaluate_input(bad_carry)
            .expect("input has circuit width");
        assert!(
            !circuit
                .is_satisfied(&layers)
                .expect("circuit shape is valid"),
            "changing a signed product carry must break the integer equation"
        );
    }

    #[test]
    fn c3_rejects_digest_limb_alias_modulo_base_field() {
        let circuit = build_c3_c5_scalar_setup_circuit().expect("C3 circuit builds");

        let mut alias_words = P256_FIELD_MODULUS;
        alias_words[0] = 0;
        alias_words[1] += 1;
        let alias_limbs = words_to_limbs(&alias_words);
        let mut recomposed = Fp::ZERO;
        let mut power = Fp::ONE;
        for limb in alias_limbs {
            recomposed = recomposed + Fp::from_u64(limb as u64) * power;
            for _ in 0..LIMB_BITS {
                power = power + power;
            }
        }
        assert_eq!(recomposed, Fp::ONE, "p + 1 aliases one in Fp");
        assert!(
            CanonicalLtTrace::new("z", &alias_words, "p", &P256_FIELD_MODULUS).is_err(),
            "the canonical integer representation must exclude p + 1"
        );
        let mut alias_input = signed_p4b_input(9, b"c3 digest alias");
        alias_input.z = be_from_words(&alias_words);
        let alias_witness =
            generate_witness(&alias_input).expect("p + 1 has a complete scalar trace");
        let invalid_z_lt_p = CanonicalLtTrace {
            value_name: "z",
            bound_name: "p",
            value: alias_limbs,
            bound: words_to_limbs(&P256_FIELD_MODULUS),
            slack: Default::default(),
            carries: Default::default(),
        };
        let forged = c3_c5_scalar_setup_input_with_z_trace(
            &alias_input,
            &alias_witness,
            Fp::ONE,
            &invalid_z_lt_p,
        )
        .expect("all non-canonicality trace components are valid");
        let layers = circuit
            .evaluate_input(forged)
            .expect("input has circuit width");
        const CANONICAL_LT_CONSTRAINTS: usize = N_LIMBS * (2 * (LIMB_BITS + 1) + 1) + 1 + N_LIMBS;
        const C3_Z_LT_OUTPUT_START: usize = 4
            + C3_CANONICAL_SCALAR_COUNT * CANONICAL_LT_CONSTRAINTS
            + 1
            + N_LIMBS * (LIMB_BITS + 1);
        const C3_Z_LT_OUTPUT_END: usize = C3_Z_LT_OUTPUT_START + CANONICAL_LT_CONSTRAINTS;
        let violations = layers[0]
            .iter()
            .enumerate()
            .filter_map(|(index, value)| (*value != Fp::ZERO).then_some(index))
            .collect::<Vec<_>>();
        assert!(
            !violations.is_empty()
                && violations
                    .iter()
                    .all(|index| (C3_Z_LT_OUTPUT_START..C3_Z_LT_OUTPUT_END).contains(index)),
            "only the z < p constraint block may reject the otherwise-valid adversarial trace: \
             {violations:?}"
        );
        assert!(
            !circuit
                .is_satisfied(&layers)
                .expect("circuit shape is valid"),
            "C3 must reject a digest representation that matches only modulo p"
        );
    }

    #[test]
    fn c14_integer_reduction_rejects_base_field_wrap() {
        // The old Fp equation accepted 0 = (p - n) + n. Build that exact
        // field-level forgery with canonical range witnesses and require the
        // integer limb equations to reject it.
        let rx_words = [0u64; 4];
        let r_words = sub_words(&P256_FIELD_MODULUS, &P256_ORDER);
        assert_eq!(
            fp_from_words(&r_words) + fp_from_words(&P256_ORDER),
            Fp::ZERO,
            "the former single-field equation is vacuous on this input"
        );
        let r_lt_n = CanonicalLtTrace::new("r", &r_words, "n", &P256_ORDER).expect("p - n < n");
        let rx_lt_p = CanonicalLtTrace::new("rx", &rx_words, "p", &P256_FIELD_MODULUS)
            .expect("zero is a canonical coordinate");
        let mut input = vec![Fp::ZERO; 1usize << C14_C15_INPUT_LOG_SIZE];
        input[C14_CONST_ONE_INDEX] = Fp::ONE;
        input[C14_SIGNATURE_R_INDEX] = fp_from_words(&r_words);
        input[C14_RX_INDEX] = Fp::ZERO;
        input[C14_K_INDEX] = Fp::ONE;
        for (range, limbs_start, bits_start, slack_start, slack_bits_start, carries_start) in [
            (
                &r_lt_n,
                C14_R_LIMBS_START,
                C14_R_BITS_START,
                C14_R_SLACK_LIMBS_START,
                C14_R_SLACK_BITS_START,
                C14_R_LT_CARRIES_START,
            ),
            (
                &rx_lt_p,
                C14_RX_LIMBS_START,
                C14_RX_BITS_START,
                C14_RX_SLACK_LIMBS_START,
                C14_RX_SLACK_BITS_START,
                C14_RX_LT_CARRIES_START,
            ),
        ] {
            for limb in 0..N_LIMBS {
                write_limb_and_bits(
                    &mut input,
                    limbs_start + limb,
                    bits_start + limb * LIMB_BITS,
                    range.value[limb],
                );
                write_limb_and_bits(
                    &mut input,
                    slack_start + limb,
                    slack_bits_start + limb * LIMB_BITS,
                    range.slack[limb],
                );
                input[carries_start + limb] = Fp::from_u64(range.carries[limb] as u64);
            }
        }
        let order_limbs = words_to_limbs(&P256_ORDER);
        let mut borrow = 0i64;
        for limb in 0..N_LIMBS - 1 {
            let total = -i64::from(r_lt_n.value[limb]) - i64::from(order_limbs[limb]) - borrow;
            borrow = i64::from(total < 0);
            input[C14_REDUCTION_BORROWS_START + limb] = Fp::from_u64(borrow as u64);
        }

        let circuit = build_c14_c15_final_check_circuit().expect("C14 circuit builds");
        let layers = circuit
            .evaluate_input(input)
            .expect("input has circuit width");
        assert!(
            !circuit
                .is_satisfied(&layers)
                .expect("circuit shape is valid"),
            "the final integer limb equation must reject reduction modulo p"
        );
    }

    #[test]
    fn ecdsa_affine_claims_bind_private_family_copies_without_claim_values() {
        let input_lens = [
            1usize << C1_INPUT_LIMBS_INPUT_LOG_SIZE,
            1usize << C2_CANONICALITY_INPUT_LOG_SIZE,
            1usize << C3_C5_SCALAR_SETUP_INPUT_LOG_SIZE,
            1usize << C9_C10_LADDER_INPUT_LOG_SIZE,
            1usize << C11_FINAL_ADD_INPUT_LOG_SIZE,
            1usize << C12_ON_CURVE_INPUT_LOG_SIZE,
            1usize << C14_C15_INPUT_LOG_SIZE,
        ];
        let mut offset = 0usize;
        let layouts = input_lens
            .map(|input_len| {
                let layout = BundleCircuitLayout {
                    input_offset: offset,
                    input_len,
                    pad_offset: offset + input_len,
                    pad_len: 0,
                };
                offset += input_len;
                layout
            })
            .to_vec();
        let mut claims = Vec::new();
        add_ecdsa_consistency_claims(&mut claims, &layouts).expect("fixed family layout");
        assert_eq!(claims.len(), 28);
        assert!(
            claims[..7].iter().all(|claim| claim.value == Fp::ONE)
                && claims[7..].iter().all(|claim| claim.value == Fp::ZERO),
            "only public constant-one claims may have nonzero values"
        );

        let evaluate = |claim: &LigeroLinearClaim, values: &[Fp]| {
            claim.terms.iter().fold(Fp::ZERO, |sum, term| {
                let mle = Mle::new(values[term.offset..term.offset + term.len].to_vec());
                sum + term.coefficient * mle.eval_at(&term.point).expect("valid fixed point")
            })
        };
        let mut values = vec![Fp::from_u64(7); offset];
        for layout in &layouts {
            values[layout.input_offset] = Fp::ONE;
        }
        assert!(claims
            .iter()
            .all(|claim| evaluate(claim, &values) == claim.value));

        values[layouts[2].input_offset] = Fp::ZERO;
        assert_eq!(
            claims
                .iter()
                .filter(|claim| evaluate(claim, &values) != claim.value)
                .count(),
            1,
            "C3's constant-one wire must be verifier-fixed"
        );
        values[layouts[2].input_offset] = Fp::ONE;
        values[layouts[6].input_offset + C14_SIGNATURE_R_INDEX] = Fp::from_u64(8);
        assert_eq!(
            claims
                .iter()
                .filter(|claim| evaluate(claim, &values) != claim.value)
                .count(),
            1,
            "changing only C14.r must violate its equality with C3.r"
        );
    }

    fn median_duration(values: &mut [Duration]) -> Duration {
        values.sort_unstable();
        values[values.len() / 2]
    }

    fn compare_dense_and_structured_claim_verification(
        label: &str,
        max_structured_calls: usize,
        issuer_projection: &EcdsaPublicProjection,
        device_projection: &EcdsaPublicProjection,
        revocation_projection: Option<&EcdsaPublicProjection>,
        bundle: &ImplementedCircuitBundle,
    ) {
        let mut dense_times = Vec::with_capacity(7);
        let mut structured_times = Vec::with_capacity(7);
        let mut dense_calls = 0usize;
        let mut structured_calls = 0usize;
        for iteration in 0..7 {
            for structured in [iteration % 2 == 1, iteration % 2 == 0] {
                crate::ligero::set_structured_claims_for_test(Some(structured));
                crate::ligero::reset_circle_weight_encode_call_count();
                let profile = verify_mdoc_p4b_circuit_bundle_profiled(
                    issuer_projection,
                    device_projection,
                    revocation_projection,
                    bundle,
                    [9u8; 32],
                )
                .unwrap();
                let calls = crate::ligero::circle_weight_encode_call_count();
                if structured {
                    structured_times.push(profile.claim_batch);
                    structured_calls = calls;
                } else {
                    dense_times.push(profile.claim_batch);
                    dense_calls = calls;
                }
            }
        }
        crate::ligero::set_structured_claims_for_test(None);
        let dense = median_duration(&mut dense_times);
        let structured = median_duration(&mut structured_times);
        eprintln!(
            "{label}_claim_batch_dense_ms={:.3} structured_ms={:.3} dense_weight_encodes={} structured_weight_encodes={}",
            dense.as_secs_f64() * 1_000.0,
            structured.as_secs_f64() * 1_000.0,
            dense_calls,
            structured_calls,
        );
        assert!(
            structured_calls * 4 <= dense_calls * 3,
            "structured evaluator must cut Circle row encodes by at least 25%"
        );
        assert!(
            structured_calls <= max_structured_calls,
            "{label} used {structured_calls} structured weight encodes; gate is {max_structured_calls}"
        );
    }

    fn gf128_basis(bit: usize) -> Gf128 {
        let mut out = [0u8; 16];
        out[bit / 8] = 1 << (bit % 8);
        out
    }

    #[test]
    fn proximity_sampler_uses_full_circle_domain_but_excludes_rs_message_prefix() {
        let root = [0x51; 32];
        let seed = [0xA7; 32];

        let circle = v4_circle_params();
        let circle_indices =
            ligero_proximity_indices(IMPLEMENTED_BUNDLE_LIGERO_LABEL, root, circle, seed);
        assert_eq!(circle_indices.len(), circle.openings);
        assert!(circle_indices
            .iter()
            .all(|&index| index < circle.codeword_len));
        assert_eq!(
            circle_indices
                .iter()
                .copied()
                .collect::<std::collections::HashSet<_>>()
                .len(),
            circle.openings,
            "proximity columns must be distinct"
        );
        assert!(
            circle_indices.iter().any(|&index| index < circle.row_len),
            "circle code has no systematic prefix, so its sampler must use the full domain"
        );

        let rs = crate::ligero::v2_ligero_params();
        let rs_indices = ligero_proximity_indices(IMPLEMENTED_BUNDLE_LIGERO_LABEL, root, rs, seed);
        assert!(
            rs_indices.iter().all(|&index| index >= rs.row_len),
            "RS proximity queries must remain disjoint from systematic openings"
        );
    }

    #[test]
    #[ignore = "release gate: real default and revocation P4b old/new verifier timing"]
    fn mdoc_p4b_structured_claim_evaluator_matches_real_fixtures() {
        let issuer = signed_p4b_input(7, b"structured claim issuer");
        let device = signed_p4b_input(9, b"structured claim device");
        let revocation = signed_p4b_input(11, b"structured claim revocation");
        let issuer_projection = EcdsaPublicProjection::issuer_key_only(issuer.qx, issuer.qy);
        let device_projection = EcdsaPublicProjection::message_hash_only(device.z);
        let revocation_projection = EcdsaPublicProjection::full(&revocation);
        let issuer_witness = generate_witness(&issuer).unwrap();
        let device_witness = generate_witness(&device).unwrap();
        let revocation_witness = generate_witness(&revocation).unwrap();
        let key_shares = p4b_microbench_key_shares();

        let default_bundle = prove_mdoc_p4b_circuit_bundle(
            &issuer,
            &issuer_projection,
            &issuer_witness,
            &device,
            &device_projection,
            &device_witness,
            None,
            &key_shares,
            [9u8; 32],
        )
        .unwrap();
        compare_dense_and_structured_claim_verification(
            "mdoc_p4b_default",
            40,
            &issuer_projection,
            &device_projection,
            None,
            &default_bundle,
        );

        let revocation_bundle = prove_mdoc_p4b_circuit_bundle(
            &issuer,
            &issuer_projection,
            &issuer_witness,
            &device,
            &device_projection,
            &device_witness,
            Some((&revocation, &revocation_projection, &revocation_witness)),
            &key_shares,
            [9u8; 32],
        )
        .unwrap();
        compare_dense_and_structured_claim_verification(
            "mdoc_p4b_revocation",
            50,
            &issuer_projection,
            &device_projection,
            Some(&revocation_projection),
            &revocation_bundle,
        );
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
