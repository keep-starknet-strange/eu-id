use core::ops::Range;
use std::time::{Duration, Instant};

use crate::ligero::{
    commit_witness_with_quadratics_profiled, product_circle_params, quadratic_committed_len,
    quadratic_route_claims, verify_and_authenticate_split_openings,
    verify_authenticated_split_claim_batch, verify_claim_batch, verify_claim_blind_check,
    verify_openings, verify_quadratic_batch, verify_split_claim_blind_check, LigeroClaimBatch,
    LigeroClaimBlindCheck, LigeroError, LigeroLinearClaim, LigeroLinearTerm, LigeroParams,
    LigeroProximityClaim, LigeroQuadraticBatch, LigeroQuadraticConstraint,
    LIGERO_AUXILIARY_ROW_COUNT,
};
use crate::mac::{bytes_to_bits, gf128_tag, Gf128, GF128_BITS};
use crate::merkle::ColumnOpening;
use crate::sumcheck::{
    circuit_pad_len, circuit_quadratic_constraints, prove_circuit, prove_evaluated_circuit,
    prove_evaluated_circuit_sorted_sparse, verify_circuit, verify_circuit_sorted_sparse,
    CircuitPads, CircuitSumcheckProof, CircuitVerification, InputClaims, SumcheckError,
};
#[cfg(test)]
use crate::Mle;
use crate::{Circuit, CircuitError, CoprocessorChannel, Fp, Layer, QuadTerm, TranscriptSeed};
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
pub const C11_FINAL_ADD_INPUT_LOG_SIZE: usize = 5;
pub const C11_FINAL_ADD_OUTPUT_LOG_SIZE: usize = 5;
pub const C12_ON_CURVE_INPUT_LOG_SIZE: usize = 11;
pub const C12_ON_CURVE_OUTPUT_LOG_SIZE: usize = 11;
pub const C14_C15_INPUT_LOG_SIZE: usize = 11;
pub const C14_C15_OUTPUT_LOG_SIZE: usize = 11;
pub const MAC_HALF_GROUP_A_INPUT_LOG_SIZE: usize = 9;
pub const MAC_HALF_INPUT_LOG_SIZE: usize = 11;
pub const MAC_HALF_TREE_LOG_SIZE: usize = 11;
pub const MAC_HALF_PARITY_Q_BITS: usize = 7;
pub const MAC_HALF_PARITY_MAX_S: usize = GF128_BITS + 1;
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
/// Whole 256-bit MAC values that must be canonical P-256 base-field elements.
///
/// Only the device-key x/y coordinates use this range check. Issuer and
/// revocation digests cover the full 256-bit SHA-256 output space and bind as
/// two exact 128-bit halves instead.
const MAC_BATCH_CANONICAL_VALUE_COUNT: usize = 2;
const MAC_BATCH_CANONICAL_FIRST_HALF: usize = 2;
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
pub const MAC_HALF_GROUP_A_USED_INPUTS: usize = MAC_HALF_AP_BITS_START + GF128_BITS;
pub const MAC_HALF_GROUP_B_USED_INPUTS: usize = GF128_BITS * MAC_HALF_PARITY_Q_BITS;
pub const MAC_HALF_COMMITTED_PRIVATE_INPUTS: usize =
    (MAC_HALF_GROUP_A_USED_INPUTS - 1) + MAC_HALF_GROUP_B_USED_INPUTS;
pub const MDOC_P4B_MAC_HALF_COUNT: usize = 8;
pub const MDOC_P4B_MAC_COMMITTED_PRIVATE_INPUTS: usize = MDOC_P4B_MAC_HALF_COUNT
    * MAC_HALF_COMMITTED_PRIVATE_INPUTS
    + MAC_BATCH_CANONICAL_VALUE_COUNT * (MAC_BATCH_CANONICAL_BITS + MAC_BATCH_CANONICAL_CARRIES);
pub const IMPLEMENTED_CIRCUIT_FAMILY_COUNT: usize = 7;

const C1_CONST_ONE_INDEX: u32 = 0;
const C1_VALUES_START_INDEX: u32 = 1;
const C1_CANONICAL_FIELD_VALUE_COUNT: u32 = 4;
const C1_LIMBS_START_INDEX: u32 = C1_VALUES_START_INDEX + C1_CANONICAL_FIELD_VALUE_COUNT;
const C2_CONST_ONE_INDEX: u32 = 0;
const C2_QX_INDEX: u32 = 1;
const C2_QY_INDEX: u32 = 2;
const C2_QX2_INDEX: u32 = 3;
const C3_CONST_ONE_INDEX: usize = 0;
const C3_R_INDEX: usize = 1;
const C3_S_INDEX: usize = 2;
const C3_U1_INDEX: usize = 3;
const C3_U2_INDEX: usize = 4;
const C3_R_NONZERO_INV_INDEX: usize = 5;
const C3_S_NONZERO_INV_INDEX: usize = 6;
const C3_Z_GE_N_INDEX: usize = 7;
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
const C3_SCALAR_LIMBS_START: usize = 8;
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
const C3_U1_ZERO_INDEX: usize = C3_DIGEST_BORROWS_START + N_LIMBS - 1;
const C3_U1_NONZERO_INV_INDEX: usize = C3_U1_ZERO_INDEX + 1;
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
const C11_GENERIC_LAMBDA_INDEX: u32 = 7;
const C11_GENERIC_DENOM_INV_INDEX: u32 = 8;
const C11_U1_ZERO_INDEX: u32 = 9;
const C11_DOUBLE_SELECTOR_INDEX: u32 = 10;
const C11_GENERIC_SELECTOR_INDEX: u32 = 11;
const C11_GENERIC_X_INDEX: u32 = 12;
const C11_GENERIC_Y_INDEX: u32 = 13;
const C11_DOUBLE_LAMBDA_INDEX: u32 = 14;
const C11_DOUBLE_DENOM_INV_INDEX: u32 = 15;
const C11_DOUBLE_X_INDEX: u32 = 16;
const C11_DOUBLE_Y_INDEX: u32 = 17;
const C11_AX_SQUARED_INDEX: u32 = 18;
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
const IMPLEMENTED_BUNDLE_LIGERO_LABEL: &[u8] = b"s4-ecdsa-implemented-bundle-v4";
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

    pub fn public_key_only(qx: [u8; 32], qy: [u8; 32]) -> Self {
        Self {
            qx: Some(qx),
            qy: Some(qy),
            ..Self::default()
        }
    }

    pub fn issuer_key_only(qx: [u8; 32], qy: [u8; 32]) -> Self {
        Self::public_key_only(qx, qy)
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
    pub claim_batch: LigeroClaimBatch,
    pub claim_blind_check: LigeroClaimBlindCheck,
    pub quadratic_batch: LigeroQuadraticBatch,
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
    pub claim_batch_reconstruct: Duration,
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
    NonCanonicalBundle,
}

/// Runtime switch for the prove-side allocation log. Off unless
/// `EUID_PROVE_PROFILE=1`, so the default prove path pays one env lookup.
fn prove_profile_enabled() -> bool {
    std::env::var_os("EUID_PROVE_PROFILE").is_some_and(|value| value == "1")
}

fn mib(bytes: usize) -> f64 {
    bytes as f64 / (1024.0 * 1024.0)
}

/// Logs the matrix sizes a Ligero commitment keeps alive, so prove-side RAM can
/// be attributed without an RSS sampler. All three matrices below coexist for
/// the whole bundle prove: openings are drawn only after the last sumcheck.
fn log_ligero_matrix_footprint(
    label: &str,
    witness_values: usize,
    commitment: &crate::ligero::LigeroCommitment,
) {
    if !prove_profile_enabled() {
        return;
    }
    let footprint = commitment.matrix_footprint();
    eprintln!(
        "[euid-prove-profile] ligero-matrix {label}: rows={} row_len={} codeword_len={} \
         elem={}B witness={} values ({:.2} MiB) encoded={}x{} values ({:.2} MiB) \
         coefficients={} values ({:.2} MiB) merkle_columns={} values ({:.2} MiB) \
         merkle_nodes={:.2} MiB total={:.2} MiB",
        footprint.rows,
        footprint.row_len,
        footprint.codeword_len,
        footprint.element_bytes,
        witness_values,
        mib(witness_values * footprint.element_bytes),
        footprint.rows,
        footprint.codeword_len,
        mib(footprint.encoded_bytes()),
        footprint.coefficient_values,
        mib(footprint.coefficient_bytes()),
        footprint.merkle_column_values,
        mib(footprint.merkle_column_bytes()),
        mib(footprint.merkle_node_bytes),
        mib(footprint.total_bytes()),
    );
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
    let u1_zero = u1_words.iter().all(|&word| word == 0);
    let u1_effective_words = if u1_zero { [1, 0, 0, 0] } else { u1_words };
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
        &u1_effective_words,
    )?;
    let u2_base = ProjectivePoint::from(public_key);
    let u2_point =
        write_ladder_accumulators(&mut values, LayoutSlot::U2QAccumulators, u2_base, &u2_words)?;

    let final_point = if u1_zero {
        u2_point
    } else {
        u1_point + u2_point
    };
    let r_point = projective_point_bytes(final_point)?;
    let (rx_words, reduction_flag) = reduce_field_x_to_scalar(words_from_be(r_point.0));

    let corrected = layout_range(LayoutSlot::CorrectedEndpoints);
    write_projective_point(&mut values[corrected.clone()], 0, u1_point)?;
    write_projective_point(&mut values[corrected], 2, u2_point)?;

    let final_add_inverse = layout_range(LayoutSlot::FinalAddDenominatorInverse);
    let generic_denominator = if u1_zero {
        Fp::ZERO
    } else {
        final_add_denominator(u1_point, u2_point)?
    };
    values[final_add_inverse.start] = generic_denominator.inverse().unwrap_or(Fp::ZERO);

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
        let pads = CircuitPads::fresh(&instance.circuit);
        proofs.push(
            prove_circuit(
                &instance.circuit,
                &layers,
                &pads,
                commitment_root,
                &mut channel,
            )
            .map_err(ImplementedCircuitProofError::Sumcheck)?,
        );
    }
    Ok(ImplementedCircuitProofs { proofs })
}

/// Verifies only the per-family sumcheck transcript shape and returns its
/// masked, unbound input claims.
///
/// This low-level API does not bind the caller statement or projected inputs.
/// It also does not bind copies shared between circuit families.
/// A Ligero commitment is required to validate committed pad constraints.
/// Production callers must use [`verify_implemented_circuit_bundle`] or its variants.
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
                .map(|verification| verification.input_claims)
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

    let start = Instant::now();
    for (input, witness) in inputs.iter().zip(witnesses) {
        verify_witness(input, witness).map_err(ImplementedCircuitProofError::Witness)?;
    }
    let witness_check = start.elapsed();
    let (bundle, inner_profile) =
        prove_implemented_circuit_bundle_batch_unchecked_with_projection_profiled(
            inputs,
            projections,
            witnesses,
            transcript_seed,
        )?;
    let mut profile = inner_profile;
    profile.witness_check = witness_check;
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

    let (committed_values, all_layouts, all_pads) = prover_committed_values(&all_instances);
    let mut quadratic_constraints = Vec::new();
    for (instances, layouts) in all_instances.iter().zip(&all_layouts) {
        for (instance, layout) in instances.iter().zip(layouts) {
            append_circuit_quadratic_constraints(
                &mut quadratic_constraints,
                &instance.circuit,
                layout,
            );
        }
    }
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
    let (commitment, commit_profile) =
        commit_witness_with_quadratics_profiled(&committed_values, params, &quadratic_constraints)
            .map_err(ImplementedCircuitProofError::Ligero)?;
    profile.ligero_row_encode = commit_profile.row_encode;
    profile.ligero_merkle_build = commit_profile.merkle_build;
    profile.ligero_rows = commit_profile.rows;

    let root = commitment.root();
    let gamma = ligero_proximity_gamma(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        root,
        commitment.committed_rows(),
        transcript_seed,
    );
    let start = Instant::now();
    let proximity_claim = commitment
        .proximity_claim(&gamma)
        .map_err(ImplementedCircuitProofError::Ligero)?;
    profile.ligero_proximity_claim = start.elapsed();

    let mut entries = Vec::new();
    let mut all_verifications = Vec::with_capacity(all_instances.len());
    let start = Instant::now();
    for (signature_index, (projection, instances)) in
        projections.iter().zip(&all_instances).enumerate()
    {
        let mut verifications = Vec::with_capacity(instances.len());
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
            let mut verifier_channel = channel.clone();
            let family_start = Instant::now();
            let proof = prove_evaluated_circuit(
                &instance.circuit,
                &layers,
                &all_pads[signature_index][family_index],
                root,
                &mut channel,
            )
            .map_err(ImplementedCircuitProofError::Sumcheck)?;
            let verification =
                verify_circuit(&instance.circuit, &proof, root, &mut verifier_channel)
                    .map_err(ImplementedCircuitProofError::Sumcheck)?;
            profile.sumcheck_by_family[family_index] += family_start.elapsed();
            entries.push(ImplementedCircuitBundleEntry { proof });
            verifications.push(verification);
        }
        all_verifications.push(verifications);
    }
    profile.sumcheck = start.elapsed();
    let claim_batch = prover_claim_batch(
        &commitment,
        projections,
        &all_instances,
        &all_layouts,
        &all_verifications,
        &entries,
        committed_values.len(),
        &quadratic_constraints,
        transcript_seed,
    )?;
    let claim_blind_challenge = ligero_claim_blind_challenge(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        root,
        params,
        transcript_seed,
    );
    let claim_blind_check = commitment.claim_blind_check(claim_blind_challenge);
    let quadratic_challenges = ligero_quadratic_challenges(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        root,
        params,
        &quadratic_constraints,
        transcript_seed,
    );
    let quadratic_batch = commitment
        .quadratic_batch(&quadratic_challenges)
        .map_err(ImplementedCircuitProofError::Ligero)?;
    let start = Instant::now();
    let opening_indices = ligero_opening_indices(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        root,
        params,
        &proximity_claim,
        &entries,
        &claim_batch,
        &claim_blind_check,
        &quadratic_batch,
        transcript_seed,
    );
    let proximity_openings = commitment
        .open_columns(&opening_indices)
        .map_err(ImplementedCircuitProofError::Ligero)?;
    profile.ligero_openings = start.elapsed();

    Ok((
        ImplementedCircuitBundle {
            params,
            root,
            root_b: None,
            proximity_openings,
            proximity_openings_b: Vec::new(),
            proximity_claim,
            claim_batch,
            claim_blind_check,
            quadratic_batch,
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
    let start = Instant::now();
    verify_witness(input, witness).map_err(ImplementedCircuitProofError::Witness)?;
    let witness_check = start.elapsed();
    let (bundle, inner_profile) =
        prove_implemented_circuit_bundle_unchecked_profiled(input, witness, transcript_seed)?;
    let mut profile = inner_profile;
    profile.witness_check = witness_check;
    Ok((bundle, profile))
}

/// Proves using a witness that the caller has already checked.
///
/// The normal `prove_implemented_circuit_bundle` path remains checked. This is
/// used by the benchmark after `generate_witness` so witness generation and
/// proof generation are measured as separate BL7 buckets.
pub fn prove_implemented_circuit_bundle_unchecked_profiled(
    input: &EcdsaInput,
    witness: &Witness,
    transcript_seed: TranscriptSeed,
) -> Result<(ImplementedCircuitBundle, ImplementedCircuitProveProfile), ImplementedCircuitProofError>
{
    prove_implemented_circuit_bundle_batch_unchecked_profiled(
        std::slice::from_ref(input),
        std::slice::from_ref(witness),
        transcript_seed,
    )
}

pub fn prove_mdoc_p4b_circuit_bundle(
    issuer_input: &EcdsaInput,
    issuer_projection: &EcdsaPublicProjection,
    issuer_witness: &Witness,
    device_input: &EcdsaInput,
    device_projection: &EcdsaPublicProjection,
    device_witness: &Witness,
    revocation: (&EcdsaInput, &EcdsaPublicProjection, &Witness),
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
    revocation: (&EcdsaInput, &EcdsaPublicProjection, &Witness),
    mac_key_shares: &MdocP4bMacKeyShares,
    transcript_seed: TranscriptSeed,
) -> Result<(ImplementedCircuitBundle, MdocP4bProveProfile), ImplementedCircuitProofError> {
    let mut profile = MdocP4bProveProfile::default();
    let start = Instant::now();
    let (revocation_input, revocation_projection, revocation_witness) = revocation;
    validate_mdoc_p4b_projection_shapes(
        issuer_projection,
        device_projection,
        revocation_projection,
    )?;
    verify_witness(issuer_input, issuer_witness).map_err(ImplementedCircuitProofError::Witness)?;
    verify_witness(device_input, device_witness).map_err(ImplementedCircuitProofError::Witness)?;
    verify_witness(revocation_input, revocation_witness)
        .map_err(ImplementedCircuitProofError::Witness)?;
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
    for instance in implemented_circuit_instances(revocation_input, revocation_witness)
        .map_err(ImplementedCircuitProofError::Witness)?
    {
        instances.push(MdocP4bProverInstance::ecdsa(2, instance));
    }
    let mac_values = mdoc_p4b_mac_values(issuer_input, device_input, revocation_input);
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

    let (committed_values, layouts, pads) = mdoc_p4b_committed_values(&instances);
    let mut quadratic_constraints = Vec::new();
    for (instance, layout) in instances.iter().zip(&layouts) {
        append_circuit_quadratic_constraints(&mut quadratic_constraints, &instance.circuit, layout);
    }
    let params = implemented_circuit_ligero_params(committed_values.len());
    profile.circuit_build = start.elapsed();
    let (commitment, commit_profile) =
        commit_witness_with_quadratics_profiled(&committed_values, params, &quadratic_constraints)
            .map_err(ImplementedCircuitProofError::Ligero)?;
    profile.ligero_row_encode = commit_profile.row_encode;
    profile.ligero_merkle_build = commit_profile.merkle_build;
    log_ligero_matrix_footprint("group_a", committed_values.len(), &commitment);
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
    let (commitment_b, commit_profile_b) =
        commit_witness_with_quadratics_profiled(&committed_values_b, params_b, &[])
            .map_err(ImplementedCircuitProofError::Ligero)?;
    profile.ligero_row_encode += commit_profile_b.row_encode;
    profile.ligero_merkle_build += commit_profile_b.merkle_build;
    log_ligero_matrix_footprint("group_b", committed_values_b.len(), &commitment_b);
    if prove_profile_enabled() {
        let resident = commitment.matrix_footprint().total_bytes()
            + commitment_b.matrix_footprint().total_bytes();
        eprintln!(
            "[euid-prove-profile] ligero-matrix resident (group_a + group_b, both live until \
             openings): {:.2} MiB",
            mib(resident),
        );
    }
    let root_b = commitment_b.root();
    let full_root = mdoc_p4b_full_root(root, root_b);

    let group_a_rows = commitment.committed_rows();
    let group_b_rows = commitment_b.committed_rows();
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
    let projections = [
        *issuer_projection,
        *device_projection,
        *revocation_projection,
    ];
    let sumcheck_start = Instant::now();
    let entry_results = instances
        .par_iter()
        .enumerate()
        .map(|(instance_index, instance)| {
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
            let mut verifier_channel = channel.clone();
            let instance_start = Instant::now();
            let proof = match instance.role {
                MdocP4bCircuitRole::MacBatch => prove_evaluated_circuit_sorted_sparse(
                    &circuit,
                    &layers,
                    &pads[instance_index],
                    full_root,
                    &mut channel,
                ),
                _ => prove_evaluated_circuit(
                    &circuit,
                    &layers,
                    &pads[instance_index],
                    full_root,
                    &mut channel,
                ),
            }
            .map_err(ImplementedCircuitProofError::Sumcheck)?;
            let verification = match instance.role {
                MdocP4bCircuitRole::MacBatch => {
                    verify_circuit_sorted_sparse(&circuit, &proof, full_root, &mut verifier_channel)
                }
                _ => verify_circuit(&circuit, &proof, full_root, &mut verifier_channel),
            }
            .map_err(ImplementedCircuitProofError::Sumcheck)?;
            Ok((
                ImplementedCircuitBundleEntry { proof },
                verification,
                mdoc_p4b_instance_timing(instance.role, instance.label, instance_start.elapsed()),
            ))
        })
        .collect::<Result<Vec<_>, ImplementedCircuitProofError>>()?;
    let mut entries = Vec::with_capacity(entry_results.len());
    let mut verifications = Vec::with_capacity(entry_results.len());
    let mut sumcheck_by_instance = Vec::with_capacity(entry_results.len());
    for (entry, verification, timing) in entry_results {
        entries.push(entry);
        verifications.push(verification);
        sumcheck_by_instance.push(timing);
    }
    profile.sumcheck_by_instance = sumcheck_by_instance;
    profile.sumcheck = sumcheck_start.elapsed();

    let claim_start = Instant::now();
    let (claim_batch, claim_inventory) = mdoc_p4b_prover_claim_batch(
        &commitment,
        &commitment_b,
        params,
        &instances,
        &layouts,
        &verifications,
        &entries,
        &projections,
        committed_values.len(),
        &quadratic_constraints,
        full_root,
        transcript_seed,
    )?;
    let claim_blind_challenge = ligero_claim_blind_challenge(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        full_root,
        params,
        transcript_seed,
    );
    let claim_blind_check = commitment
        .split_claim_blind_check(&commitment_b, claim_blind_challenge)
        .map_err(ImplementedCircuitProofError::Ligero)?;
    let quadratic_challenges = ligero_quadratic_challenges(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        full_root,
        params,
        &quadratic_constraints,
        transcript_seed,
    );
    let quadratic_batch = commitment
        .quadratic_batch(&quadratic_challenges)
        .map_err(ImplementedCircuitProofError::Ligero)?;
    let opening_start = Instant::now();
    let opening_indices = ligero_opening_indices(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        full_root,
        params,
        &proximity_claim,
        &entries,
        &claim_batch,
        &claim_blind_check,
        &quadratic_batch,
        transcript_seed,
    );
    let proximity_openings = commitment
        .open_columns(&opening_indices)
        .map_err(ImplementedCircuitProofError::Ligero)?;
    let proximity_openings_b = commitment_b
        .open_columns(&opening_indices)
        .map_err(ImplementedCircuitProofError::Ligero)?;
    profile.ligero_openings = opening_start.elapsed();
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
            claim_batch,
            claim_blind_check,
            quadratic_batch,
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
    revocation_projection: &EcdsaPublicProjection,
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
    revocation_projection: &EcdsaPublicProjection,
    bundle: &ImplementedCircuitBundle,
    transcript_seed: TranscriptSeed,
) -> Result<MdocP4bVerifyProfile, ImplementedCircuitProofError> {
    let mut profile = MdocP4bVerifyProfile::default();
    let setup_start = Instant::now();
    validate_mdoc_p4b_projection_shapes(
        issuer_projection,
        device_projection,
        revocation_projection,
    )?;
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
    let projections = [
        *issuer_projection,
        *device_projection,
        *revocation_projection,
    ];
    let circuits = mdoc_p4b_verifier_instances(&av, &bundle.mac_tags)?;
    if bundle.entries.len() != circuits.len() {
        return Err(ImplementedCircuitProofError::WrongProofCount {
            expected: circuits.len(),
            actual: bundle.entries.len(),
        });
    }
    let (layouts, committed_len) = mdoc_p4b_verifier_bundle_pad_layouts(&circuits, 0);
    let mut quadratic_constraints = Vec::new();
    for (instance, layout) in circuits.iter().zip(&layouts) {
        append_circuit_quadratic_constraints(&mut quadratic_constraints, &instance.circuit, layout);
    }
    let expected_params = implemented_circuit_ligero_params(committed_len);
    if bundle.params != expected_params {
        return Err(ImplementedCircuitProofError::ProximityOpeningRejected);
    }
    let expanded_committed_len =
        quadratic_committed_len(committed_len, expected_params, quadratic_constraints.len())
            .map_err(ImplementedCircuitProofError::Ligero)?;
    let committed_len_b = 1usize << MAC_BATCH_GROUP_B_INPUT_LOG_SIZE;
    profile.setup = setup_start.elapsed();

    let start = Instant::now();
    let proximity_gamma = ligero_proximity_gamma(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        full_root,
        ligero_row_count(expanded_committed_len, bundle.params.row_len)
            + ligero_row_count(committed_len_b, bundle.params.row_len),
        transcript_seed,
    );
    verify_ligero_opening_indices(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        full_root,
        bundle.params,
        &bundle.proximity_openings,
        &bundle.proximity_claim,
        &bundle.entries,
        &bundle.claim_batch,
        &bundle.claim_blind_check,
        &bundle.quadratic_batch,
        transcript_seed,
    )?;
    verify_ligero_opening_indices(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        full_root,
        bundle.params,
        &bundle.proximity_openings_b,
        &bundle.proximity_claim,
        &bundle.entries,
        &bundle.claim_batch,
        &bundle.claim_blind_check,
        &bundle.quadratic_batch,
        transcript_seed,
    )?;
    let authenticated_openings = verify_and_authenticate_split_openings(
        bundle.root,
        root_b,
        bundle.params,
        expanded_committed_len,
        committed_len_b,
        &bundle.proximity_openings,
        &bundle.proximity_openings_b,
        &bundle.proximity_claim,
        &proximity_gamma,
    )
    .map_err(ImplementedCircuitProofError::Ligero)?
    .ok_or(ImplementedCircuitProofError::ProximityOpeningRejected)?;
    let claim_blind_challenge = ligero_claim_blind_challenge(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        full_root,
        bundle.params,
        transcript_seed,
    );
    if !verify_split_claim_blind_check(
        bundle.root,
        root_b,
        bundle.params,
        expanded_committed_len,
        committed_len_b,
        &bundle.proximity_openings,
        &bundle.proximity_openings_b,
        &bundle.claim_blind_check,
        claim_blind_challenge,
    )
    .map_err(ImplementedCircuitProofError::Ligero)?
    {
        return Err(ImplementedCircuitProofError::InputClaimOpeningRejected);
    }
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

    for ((instance, layout), (verification, elapsed)) in
        circuits.iter().zip(layouts.iter()).zip(verified_claims)
    {
        profile.sumcheck += elapsed;
        profile.sumcheck_by_instance.push(mdoc_p4b_instance_timing(
            instance.role,
            instance.label,
            elapsed,
        ));
        let start = Instant::now();
        match instance.role {
            MdocP4bCircuitRole::MacBatch => add_mac_split_circuit_verification_claims(
                &mut linear_claims,
                layout,
                expanded_committed_len,
                &verification,
            )?,
            _ => add_circuit_verification_claims(&mut linear_claims, layout, &verification),
        }
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
                add_family_fixed_claims(
                    &mut linear_claims,
                    revocation_projection,
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
    linear_claims.extend(
        quadratic_route_claims(committed_len, bundle.params, &quadratic_constraints)
            .map_err(ImplementedCircuitProofError::Ligero)?,
    );
    profile.consistency += start.elapsed();

    let quadratic_challenges = ligero_quadratic_challenges(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        full_root,
        bundle.params,
        &quadratic_constraints,
        transcript_seed,
    );
    if !verify_quadratic_batch(
        bundle.root,
        bundle.params,
        committed_len,
        quadratic_constraints.len(),
        &bundle.proximity_openings,
        &bundle.quadratic_batch,
        &quadratic_challenges,
    )
    .map_err(ImplementedCircuitProofError::Ligero)?
    {
        return Err(ImplementedCircuitProofError::InputClaimOpeningRejected);
    }

    let start = Instant::now();
    let claim_gamma = ligero_claim_gamma(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        full_root,
        &bundle.entries,
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
    if bundle.root_b.is_some()
        || !bundle.proximity_openings_b.is_empty()
        || !bundle.mac_tags.is_empty()
    {
        return Err(ImplementedCircuitProofError::NonCanonicalBundle);
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
    let mut quadratic_constraints = Vec::new();
    for layouts in &signature_layouts {
        for (instance, layout) in circuits.iter().zip(layouts) {
            append_circuit_quadratic_constraints(
                &mut quadratic_constraints,
                &instance.circuit,
                layout,
            );
        }
    }
    let expected_params = implemented_circuit_ligero_params(committed_len);
    if bundle.params != expected_params {
        return Err(ImplementedCircuitProofError::ProximityOpeningRejected);
    }
    let expanded_committed_len =
        quadratic_committed_len(committed_len, expected_params, quadratic_constraints.len())
            .map_err(ImplementedCircuitProofError::Ligero)?;
    profile.setup = setup_start.elapsed();

    let start = Instant::now();
    let proximity_gamma = ligero_proximity_gamma(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        bundle.root,
        ligero_row_count(expanded_committed_len, bundle.params.row_len),
        transcript_seed,
    );
    verify_ligero_opening_indices(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        bundle.root,
        bundle.params,
        &bundle.proximity_openings,
        &bundle.proximity_claim,
        &bundle.entries,
        &bundle.claim_batch,
        &bundle.claim_blind_check,
        &bundle.quadratic_batch,
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
    let claim_blind_challenge = ligero_claim_blind_challenge(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        bundle.root,
        bundle.params,
        transcript_seed,
    );
    if !verify_claim_blind_check(
        bundle.root,
        bundle.params,
        expanded_committed_len,
        &bundle.proximity_openings,
        &bundle.claim_blind_check,
        claim_blind_challenge,
    )
    .map_err(ImplementedCircuitProofError::Ligero)?
    {
        return Err(ImplementedCircuitProofError::InputClaimOpeningRejected);
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
        for (family_index, (instance, layout)) in circuits.iter().zip(layouts).enumerate() {
            let (verification, elapsed) =
                &verified_flat[signature_index * family_count + family_index];
            let verification = verification.clone();
            profile.sumcheck += *elapsed;
            profile.sumcheck_by_family[family_index] += *elapsed;

            let start = Instant::now();
            add_circuit_verification_claims(&mut linear_claims, layout, &verification);
            profile.input_claims += start.elapsed();

            let start = Instant::now();
            add_family_fixed_claims(&mut linear_claims, projection, instance.label, layout)?;
            profile.consistency += start.elapsed();
            verified_claims.push(verification.input_claims);
        }
        let start = Instant::now();
        add_ecdsa_consistency_claims(&mut linear_claims, layouts)?;
        profile.consistency += start.elapsed();
        all_claims.push(verified_claims);
    }
    linear_claims.extend(
        quadratic_route_claims(committed_len, bundle.params, &quadratic_constraints)
            .map_err(ImplementedCircuitProofError::Ligero)?,
    );
    let quadratic_challenges = ligero_quadratic_challenges(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        bundle.root,
        bundle.params,
        &quadratic_constraints,
        transcript_seed,
    );
    if !verify_quadratic_batch(
        bundle.root,
        bundle.params,
        committed_len,
        quadratic_constraints.len(),
        &bundle.proximity_openings,
        &bundle.quadratic_batch,
        &quadratic_challenges,
    )
    .map_err(ImplementedCircuitProofError::Ligero)?
    {
        return Err(ImplementedCircuitProofError::InputClaimOpeningRejected);
    }
    let start = Instant::now();
    let claim_gamma = ligero_claim_gamma(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        bundle.root,
        &bundle.entries,
        linear_claims.len(),
        transcript_seed,
    );
    if !verify_claim_batch(
        bundle.root,
        bundle.params,
        expanded_committed_len,
        &bundle.proximity_openings,
        &bundle.claim_batch,
        &linear_claims,
        &claim_gamma,
    )
    .map_err(ImplementedCircuitProofError::Ligero)?
    {
        return Err(ImplementedCircuitProofError::InputClaimOpeningRejected);
    }
    profile.claim_batch_reconstruct = start.elapsed();
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
    entries: &[ImplementedCircuitBundleEntry],
    claims: usize,
    transcript_seed: TranscriptSeed,
) -> Vec<Fp> {
    let mut channel = CoprocessorChannel::from_seed(transcript_seed, COPROCESSOR_TRANSCRIPT_DOMAIN);
    channel.mix_bytes(label);
    channel.mix_bytes(&root);
    channel.mix_bytes(b"s4-ligero-claim-gamma");
    mix_sumcheck_entries(&mut channel, entries);
    channel.mix_bytes(&(claims as u64).to_be_bytes());
    (0..claims).map(|_| channel.draw_fp()).collect()
}

fn ligero_claim_blind_challenge(
    label: &[u8],
    root: [u8; 32],
    params: LigeroParams,
    transcript_seed: TranscriptSeed,
) -> Fp {
    let mut channel = CoprocessorChannel::from_seed(transcript_seed, COPROCESSOR_TRANSCRIPT_DOMAIN);
    channel.mix_bytes(label);
    channel.mix_bytes(&root);
    channel.mix_bytes(b"s4-ligero-claim-blind-kernel-v1");
    for dimension in [
        params.row_len,
        params.degree_bound,
        params.codeword_len,
        params.openings,
        params.proximity_radius,
    ] {
        channel.mix_bytes(&(dimension as u64).to_be_bytes());
    }
    channel.mix_bytes(&[1]);
    channel.draw_fp()
}

fn ligero_quadratic_challenges(
    label: &[u8],
    root: [u8; 32],
    params: LigeroParams,
    constraints: &[LigeroQuadraticConstraint],
    transcript_seed: TranscriptSeed,
) -> Vec<Fp> {
    let mut channel = CoprocessorChannel::from_seed(transcript_seed, COPROCESSOR_TRANSCRIPT_DOMAIN);
    channel.mix_bytes(label);
    channel.mix_bytes(&root);
    channel.mix_bytes(b"s4-ligero-quadratic-v1");
    channel.mix_bytes(&(constraints.len() as u64).to_be_bytes());
    for constraint in constraints {
        channel.mix_bytes(&(constraint.x as u64).to_be_bytes());
        channel.mix_bytes(&(constraint.y as u64).to_be_bytes());
        channel.mix_bytes(&(constraint.z as u64).to_be_bytes());
    }
    (0..constraints.len().div_ceil(params.row_len))
        .map(|_| channel.draw_fp())
        .collect()
}

fn ligero_opening_indices(
    label: &[u8],
    root: [u8; 32],
    params: LigeroParams,
    proximity_claim: &LigeroProximityClaim,
    entries: &[ImplementedCircuitBundleEntry],
    claim_batch: &LigeroClaimBatch,
    claim_blind_check: &LigeroClaimBlindCheck,
    quadratic_batch: &LigeroQuadraticBatch,
    transcript_seed: TranscriptSeed,
) -> Vec<usize> {
    let mut channel = CoprocessorChannel::from_seed(transcript_seed, COPROCESSOR_TRANSCRIPT_DOMAIN);
    channel.mix_bytes(label);
    channel.mix_bytes(&root);
    channel.mix_bytes(b"s4-ligero-opening-transcript-v4");
    for dimension in [
        params.row_len,
        params.degree_bound,
        params.codeword_len,
        params.openings,
        params.proximity_radius,
    ] {
        channel.mix_bytes(&(dimension as u64).to_be_bytes());
    }
    channel.mix_bytes(&[1]);
    mix_fp_slice(&mut channel, &proximity_claim.combined_row);
    mix_sumcheck_entries(&mut channel, entries);
    mix_fp_slice(&mut channel, &claim_batch.coefficients);
    channel.mix_fp(claim_batch.blind_claim);
    mix_fp_slice(&mut channel, &claim_blind_check.combined_row);
    mix_fp_slice(&mut channel, &quadratic_batch.quotient);
    channel.mix_bytes(b"s4-ligero-opening-indices");
    let mut indices = Vec::with_capacity(params.openings);
    while indices.len() < params.openings {
        let bytes = channel.draw_fp().to_bytes_be();
        let mut word = [0u8; 8];
        word.copy_from_slice(&bytes[24..]);
        let index = (u64::from_be_bytes(word) as usize) % params.codeword_len;
        if !indices.contains(&index) {
            indices.push(index);
        }
    }
    indices
}

fn mix_sumcheck_entries(
    channel: &mut CoprocessorChannel,
    entries: &[ImplementedCircuitBundleEntry],
) {
    channel.mix_bytes(&(entries.len() as u64).to_be_bytes());
    for entry in entries {
        channel.mix_bytes(&(entry.proof.layers.len() as u64).to_be_bytes());
        for layer in &entry.proof.layers {
            channel.mix_bytes(&(layer.rounds.len() as u64).to_be_bytes());
            for round in &layer.rounds {
                channel.mix_fp(round[0]);
                channel.mix_fp(round[1]);
            }
            channel.mix_fp(layer.next_claims[0]);
            channel.mix_fp(layer.next_claims[1]);
        }
    }
}

fn mix_fp_slice(channel: &mut CoprocessorChannel, values: &[Fp]) {
    channel.mix_bytes(&(values.len() as u64).to_be_bytes());
    for value in values {
        channel.mix_fp(*value);
    }
}

fn verify_ligero_opening_indices(
    label: &[u8],
    root: [u8; 32],
    params: LigeroParams,
    openings: &[ColumnOpening],
    proximity_claim: &LigeroProximityClaim,
    entries: &[ImplementedCircuitBundleEntry],
    claim_batch: &LigeroClaimBatch,
    claim_blind_check: &LigeroClaimBlindCheck,
    quadratic_batch: &LigeroQuadraticBatch,
    transcript_seed: TranscriptSeed,
) -> Result<(), ImplementedCircuitProofError> {
    let expected = ligero_opening_indices(
        label,
        root,
        params,
        proximity_claim,
        entries,
        claim_batch,
        claim_blind_check,
        quadratic_batch,
        transcript_seed,
    );
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
    hasher.update(b"eu-id-s4-mdoc-p4b-two-root-v3");
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
    channel.mix_bytes(MDOC_P4B_MAC_PUBLIC_LABEL);
    channel.mix_bytes(&root);
    channel.draw_gf128(b"eu-id-p4b-affine-mac-av-v3")
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
            channel.mix_bytes(MDOC_P4B_MAC_PUBLIC_LABEL);
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

fn validate_mdoc_p4b_projection_shapes(
    issuer: &EcdsaPublicProjection,
    device: &EcdsaPublicProjection,
    revocation: &EcdsaPublicProjection,
) -> Result<(), ImplementedCircuitProofError> {
    let key_only = |projection: &EcdsaPublicProjection| {
        projection.z.is_none()
            && projection.r.is_none()
            && projection.s.is_none()
            && projection.qx.is_some()
            && projection.qy.is_some()
    };
    let message_hash_only = |projection: &EcdsaPublicProjection| {
        projection.z.is_some()
            && projection.r.is_none()
            && projection.s.is_none()
            && projection.qx.is_none()
            && projection.qy.is_none()
    };
    if !key_only(issuer) || !message_hash_only(device) || !key_only(revocation) {
        return Err(ImplementedCircuitProofError::NonCanonicalBundle);
    }
    Ok(())
}

fn mdoc_p4b_mac_values(
    issuer_input: &EcdsaInput,
    device_input: &EcdsaInput,
    revocation_input: &EcdsaInput,
) -> [Gf128; MDOC_P4B_MAC_HALF_COUNT] {
    let [issuer_z_lo, issuer_z_hi] = gf128_halves_from_be32(issuer_input.z);
    let [device_qx_lo, device_qx_hi] = gf128_halves_from_be32(device_input.qx);
    let [device_qy_lo, device_qy_hi] = gf128_halves_from_be32(device_input.qy);
    let [revocation_z_lo, revocation_z_hi] = gf128_halves_from_be32(revocation_input.z);
    [
        issuer_z_lo,
        issuer_z_hi,
        device_qx_lo,
        device_qx_hi,
        device_qy_lo,
        device_qy_hi,
        revocation_z_lo,
        revocation_z_hi,
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
    // `product_circle_params` is the single source for the live code geometry and
    // opening count. This query/PoW target is a configuration heuristic, not
    // a theorem-level composed soundness bound for the full proof.
    const PCS_PARAMETER_HEURISTIC_BITS: i32 = 128;
    let params = product_circle_params();
    debug_assert!(params.validate().is_ok());
    debug_assert!(params.soundness_error() <= 2f64.powi(-PCS_PARAMETER_HEURISTIC_BITS));
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

const MDOC_P4B_MAC_BATCH_LABEL: &[u8] = b"s4-mdoc-p4b-affine-mac-batch-v3";
const MDOC_P4B_MAC_PUBLIC_LABEL: &[u8] = b"s4-mdoc-p4b-affine-mac-public-v3";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct BundleCircuitLayout {
    input_offset: usize,
    input_len: usize,
    pad_offset: usize,
    pad_len: usize,
}

fn append_circuit_quadratic_constraints(
    out: &mut Vec<LigeroQuadraticConstraint>,
    circuit: &Circuit,
    layout: &BundleCircuitLayout,
) {
    out.extend(
        circuit_quadratic_constraints(circuit)
            .into_iter()
            .map(|constraint| LigeroQuadraticConstraint {
                x: layout.pad_offset + constraint.x,
                y: layout.pad_offset + constraint.y,
                z: layout.pad_offset + constraint.z,
            }),
    );
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
        let pad_len = circuit_pad_len(&instance.circuit);
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
        let pad_len = circuit_pad_len(&instance.circuit);
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
) -> (
    Vec<Fp>,
    Vec<Vec<BundleCircuitLayout>>,
    Vec<Vec<CircuitPads>>,
) {
    let mut committed_values = Vec::new();
    let mut all_layouts = Vec::with_capacity(all_instances.len());
    let mut all_pads = Vec::with_capacity(all_instances.len());
    for instances in all_instances {
        let mut layouts = Vec::with_capacity(instances.len());
        let mut instance_pads = Vec::with_capacity(instances.len());
        for instance in instances {
            let input_offset = committed_values.len();
            committed_values.extend_from_slice(&instance.input);
            let input_len = instance.input.len();
            let pads = CircuitPads::fresh(&instance.circuit);
            let pad_offset = committed_values.len();
            let pad_len = pads.values().len();
            committed_values.extend_from_slice(pads.values());
            layouts.push(BundleCircuitLayout {
                input_offset,
                input_len,
                pad_offset,
                pad_len,
            });
            instance_pads.push(pads);
        }
        all_layouts.push(layouts);
        all_pads.push(instance_pads);
    }
    (committed_values, all_layouts, all_pads)
}

fn mdoc_p4b_committed_values(
    instances: &[MdocP4bProverInstance],
) -> (Vec<Fp>, Vec<BundleCircuitLayout>, Vec<CircuitPads>) {
    let mut committed_values = Vec::new();
    let mut layouts = Vec::with_capacity(instances.len());
    let mut all_pads = Vec::with_capacity(instances.len());
    for instance in instances {
        let input_offset = committed_values.len();
        committed_values.extend_from_slice(&instance.input);
        let input_len = instance.input.len();
        let pads = CircuitPads::fresh(&instance.circuit);
        let pad_offset = committed_values.len();
        let pad_len = pads.values().len();
        committed_values.extend_from_slice(pads.values());
        layouts.push(BundleCircuitLayout {
            input_offset,
            input_len,
            pad_offset,
            pad_len,
        });
        all_pads.push(pads);
    }
    (committed_values, layouts, all_pads)
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
        committed_rows: encoded_rows_total.saturating_sub(LIGERO_AUXILIARY_ROW_COUNT),
        encoded_rows_total,
        ecdsa_input_values,
        ecdsa_input_rows,
        mac_input_values,
        mac_input_rows,
        otp_pad_values,
        otp_pad_rows,
        blind_rows: LIGERO_AUXILIARY_ROW_COUNT,
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
    for instance in
        implemented_circuit_verifier_instances().map_err(ImplementedCircuitProofError::Circuit)?
    {
        instances.push(MdocP4bVerifierInstance {
            label: instance.label,
            role: MdocP4bCircuitRole::RevocationEcdsa,
            circuit: instance.circuit,
        });
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
    all_verifications: &[Vec<CircuitVerification>],
    entries: &[ImplementedCircuitBundleEntry],
    committed_len: usize,
    quadratic_constraints: &[LigeroQuadraticConstraint],
    transcript_seed: TranscriptSeed,
) -> Result<LigeroClaimBatch, ImplementedCircuitProofError> {
    let mut claims = Vec::new();
    for (((projection, instances), layouts), verifications) in projections
        .iter()
        .zip(all_instances.iter())
        .zip(all_layouts.iter())
        .zip(all_verifications)
    {
        for ((instance, layout), verification) in instances.iter().zip(layouts).zip(verifications) {
            add_circuit_verification_claims(&mut claims, layout, verification);
            add_family_fixed_claims(&mut claims, projection, instance.label, layout)?;
        }
        add_ecdsa_consistency_claims(&mut claims, layouts)?;
    }
    claims.extend(
        quadratic_route_claims(committed_len, commitment.params(), quadratic_constraints)
            .map_err(ImplementedCircuitProofError::Ligero)?,
    );
    let gamma = ligero_claim_gamma(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        commitment.root(),
        entries,
        claims.len(),
        transcript_seed,
    );
    let batch = commitment
        .claim_batch(&claims, &gamma)
        .map_err(ImplementedCircuitProofError::Ligero)?;
    Ok(batch)
}

fn mdoc_p4b_prover_claim_batch(
    commitment: &crate::ligero::LigeroCommitment,
    commitment_b: &crate::ligero::LigeroCommitment,
    params: LigeroParams,
    instances: &[MdocP4bProverInstance],
    layouts: &[BundleCircuitLayout],
    verifications: &[CircuitVerification],
    entries: &[ImplementedCircuitBundleEntry],
    projections: &[EcdsaPublicProjection],
    committed_len_a: usize,
    quadratic_constraints: &[LigeroQuadraticConstraint],
    transcript_root: [u8; 32],
    transcript_seed: TranscriptSeed,
) -> Result<(LigeroClaimBatch, MdocP4bClaimInventory), ImplementedCircuitProofError> {
    let mut claims = Vec::new();
    let group_b_offset =
        quadratic_committed_len(committed_len_a, params, quadratic_constraints.len())
            .map_err(ImplementedCircuitProofError::Ligero)?;
    for ((instance, layout), verification) in instances.iter().zip(layouts).zip(verifications) {
        match instance.role {
            MdocP4bCircuitRole::MacBatch => add_mac_split_circuit_verification_claims(
                &mut claims,
                layout,
                group_b_offset,
                verification,
            )?,
            _ => add_circuit_verification_claims(&mut claims, layout, verification),
        }
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
    claims.extend(
        quadratic_route_claims(committed_len_a, params, quadratic_constraints)
            .map_err(ImplementedCircuitProofError::Ligero)?,
    );
    let gamma = ligero_claim_gamma(
        IMPLEMENTED_BUNDLE_LIGERO_LABEL,
        transcript_root,
        entries,
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
    Ok((batch, inventory))
}

fn add_circuit_verification_claims(
    claims: &mut Vec<LigeroLinearClaim>,
    layout: &BundleCircuitLayout,
    verification: &CircuitVerification,
) {
    for constraint in &verification.layer_constraints {
        claims.push(LigeroLinearClaim::affine(
            constraint
                .terms
                .iter()
                .map(|term| LigeroLinearTerm {
                    offset: layout.pad_offset + term.pad_offset,
                    len: 1,
                    point: Vec::new(),
                    coefficient: term.coefficient,
                })
                .collect(),
            constraint.value,
        ));
    }
    let beta = verification.input_challenge;
    claims.push(LigeroLinearClaim::affine(
        vec![
            LigeroLinearTerm {
                offset: layout.input_offset,
                len: layout.input_len,
                point: verification.input_claims.points[0].clone(),
                coefficient: Fp::ONE,
            },
            LigeroLinearTerm {
                offset: layout.input_offset,
                len: layout.input_len,
                point: verification.input_claims.points[1].clone(),
                coefficient: beta,
            },
            LigeroLinearTerm {
                offset: layout.pad_offset + verification.input_pad_offsets[0],
                len: 1,
                point: Vec::new(),
                coefficient: -Fp::ONE,
            },
            LigeroLinearTerm {
                offset: layout.pad_offset + verification.input_pad_offsets[1],
                len: 1,
                point: Vec::new(),
                coefficient: -beta,
            },
        ],
        verification.input_claims.values[0] + beta * verification.input_claims.values[1],
    ));
}

fn add_mac_split_circuit_verification_claims(
    claims: &mut Vec<LigeroLinearClaim>,
    layout_a: &BundleCircuitLayout,
    group_b_offset: usize,
    verification: &CircuitVerification,
) -> Result<(), ImplementedCircuitProofError> {
    for constraint in &verification.layer_constraints {
        claims.push(LigeroLinearClaim::affine(
            constraint
                .terms
                .iter()
                .map(|term| LigeroLinearTerm {
                    offset: layout_a.pad_offset + term.pad_offset,
                    len: 1,
                    point: Vec::new(),
                    coefficient: term.coefficient,
                })
                .collect(),
            constraint.value,
        ));
    }

    let beta = verification.input_challenge;
    let mut terms = Vec::with_capacity(6);
    for (point, coefficient) in verification.input_claims.points.iter().zip([Fp::ONE, beta]) {
        if point.len() != MAC_BATCH_INPUT_LOG_SIZE {
            return Err(ImplementedCircuitProofError::InputClaimOpeningRejected);
        }
        let split = point[MAC_BATCH_GROUP_A_INPUT_LOG_SIZE];
        let subpoint = point[..MAC_BATCH_GROUP_A_INPUT_LOG_SIZE].to_vec();
        terms.push(LigeroLinearTerm {
            offset: layout_a.input_offset,
            len: layout_a.input_len,
            point: subpoint.clone(),
            coefficient: coefficient * (Fp::ONE - split),
        });
        terms.push(LigeroLinearTerm {
            offset: group_b_offset,
            len: 1usize << MAC_BATCH_GROUP_B_INPUT_LOG_SIZE,
            point: subpoint,
            coefficient: coefficient * split,
        });
    }
    terms.push(LigeroLinearTerm {
        offset: layout_a.pad_offset + verification.input_pad_offsets[0],
        len: 1,
        point: Vec::new(),
        coefficient: -Fp::ONE,
    });
    terms.push(LigeroLinearTerm {
        offset: layout_a.pad_offset + verification.input_pad_offsets[1],
        len: 1,
        point: Vec::new(),
        coefficient: -beta,
    });
    claims.push(LigeroLinearClaim::affine(
        terms,
        verification.input_claims.values[0] + beta * verification.input_claims.values[1],
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
    if let Some(z) = projection.z {
        for (limb, value) in limbs_13(z).into_iter().enumerate() {
            add_fixed_claim(
                claims,
                layout.input_offset,
                layout.input_len,
                C1_LIMBS_START_INDEX as usize + limb,
                Fp::from_u64(u64::from(value)),
            );
        }
    }
    for (input_value_index, bytes) in [projection.r, projection.s, projection.qx, projection.qy]
        .into_iter()
        .enumerate()
        .filter_map(|(input_value_index, bytes)| bytes.map(|bytes| (input_value_index, bytes)))
    {
        let value =
            Fp::from_bytes_be(bytes).ok_or(ImplementedCircuitProofError::InputBindingRejected)?;
        add_fixed_claim(
            claims,
            layout.input_offset,
            layout.input_len,
            C1_VALUES_START_INDEX as usize + input_value_index,
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
    // Exact public z bytes bind through C1's 20 small limbs. C1 and C3 bind
    // those limbs pairwise below, so no whole-field digest claim is needed.
    for (index, bytes) in [(C3_R_INDEX, projection.r), (C3_S_INDEX, projection.s)]
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
    let c1_value = |input_value_index: usize| {
        debug_assert!((1..=4).contains(&input_value_index));
        C1_VALUES_START_INDEX as usize + input_value_index - 1
    };
    let c12_point =
        |point: usize, coordinate: usize| C12_POINTS_START_INDEX as usize + point * 3 + coordinate;

    for layout in layouts {
        add_fixed_claim(claims, layout.input_offset, layout.input_len, 0, Fp::ONE);
    }
    for (left_layout, left, right_layout, right) in [
        (c1, c1_value(1), c3, C3_R_INDEX),
        (c3, C3_R_INDEX, c14, C14_SIGNATURE_R_INDEX),
        (c1, c1_value(2), c3, C3_S_INDEX),
        (c1, c1_value(3), c2, C2_QX_INDEX as usize),
        (c2, C2_QX_INDEX as usize, c9, C9_QX_INDEX),
        (c1, c1_value(4), c2, C2_QY_INDEX as usize),
        (c2, C2_QY_INDEX as usize, c9, C9_QY_INDEX),
        (c3, C3_U2_INDEX, c9, C9_U2_INDEX),
        (c3, C3_U1_ZERO_INDEX, c11, C11_U1_ZERO_INDEX as usize),
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
    claims.push(LigeroLinearClaim::affine(
        vec![
            fixed_term(c9, C9_U1_INDEX, Fp::ONE),
            fixed_term(c3, C3_U1_INDEX, -Fp::ONE),
            fixed_term(c3, C3_U1_ZERO_INDEX, -Fp::ONE),
        ],
        Fp::ZERO,
    ));
    for limb in 0..N_LIMBS {
        add_equality_claim(
            claims,
            c1,
            C1_LIMBS_START_INDEX as usize + limb,
            c3,
            C3_Z_LIMBS_START + limb,
        );
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
        add_ecdsa_consistency_claims(claims, &role_layouts)?;
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
    add_mac_digest_binding(claims, issuer_c3, mac, 0, 1);
    add_mac_field_binding(claims, device_c2, C2_QX_INDEX as usize, mac, 2, 3);
    add_mac_field_binding(claims, device_c2, C2_QY_INDEX as usize, mac, 4, 5);
    let revocation_c3 = find(
        MdocP4bCircuitRole::RevocationEcdsa,
        b"s4-ecdsa-c3-c5-scalar-setup",
    )?;
    add_mac_digest_binding(claims, revocation_c3, mac, 6, 7);
    Ok(())
}

/// Bind an exact 256-bit C3 digest to its two MAC halves.
///
/// C3 and the MAC store bits least-significant first. Each separate 128-bit
/// recomposition is strictly below Fp, so neither half can alias modulo the
/// base-field modulus.
fn add_mac_digest_binding(
    claims: &mut Vec<LigeroLinearClaim>,
    c3_layout: &BundleCircuitLayout,
    mac_layout: &BundleCircuitLayout,
    low_half: usize,
    high_half: usize,
) {
    let (point, _) = mac_half_x_recompose_claim_point();
    for (digest_bit_start, mac_half) in [
        (C3_Z_BITS_START, low_half),
        (C3_Z_BITS_START + GF128_BITS, high_half),
    ] {
        claims.push(LigeroLinearClaim::affine(
            vec![
                LigeroLinearTerm {
                    offset: c3_layout.input_offset + digest_bit_start,
                    len: GF128_BITS,
                    point: point.clone(),
                    coefficient: Fp::ONE,
                },
                LigeroLinearTerm {
                    offset: mac_layout.input_offset
                        + mac_batch_half_group_a_input_offset(mac_half)
                        + MAC_HALF_X_BITS_START,
                    len: GF128_BITS,
                    point: point.clone(),
                    coefficient: -Fp::ONE,
                },
            ],
            Fp::ZERO,
        ));
    }
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
        // C13 slope inverses do not bind to C12 accumulator points.
        // The final pair also duplicates the C11 inverse equation.
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
    Circuit::new(vec![
        mac_half_final_layer(local_constraints)?,
        mac_half_parity_layer(&tag_bits, local_constraints)?,
        mac_half_input_layer(&av_bits)?,
    ])
}

fn build_mac_batch_circuit(av: &Gf128, tags: &[Gf128]) -> Result<Circuit, CircuitError> {
    if tags.len() != MDOC_P4B_MAC_HALF_COUNT {
        return Err(CircuitError::InvalidTermIndex);
    }
    let av_bits = bytes_to_bits(av);
    let tag_bits: [[bool; GF128_BITS]; MDOC_P4B_MAC_HALF_COUNT] =
        std::array::from_fn(|index| bytes_to_bits(&tags[index]));
    let local_constraints = mac_half_local_constraint_count();
    Circuit::new(vec![
        mac_batch_final_layer(local_constraints)?,
        mac_batch_parity_layer(&tag_bits, local_constraints)?,
        mac_batch_input_layer(&av_bits)?,
    ])
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
        let first_half = MAC_BATCH_CANONICAL_FIRST_HALF + 2 * value;
        let words = gf128_pair_words(&mac_values[first_half], &mac_values[first_half + 1]);
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
    let mut terms = Vec::new();
    add_linear(
        &mut terms,
        mac_half_tree_const_index(),
        MAC_HALF_CONST_ONE_INDEX,
        Fp::ONE,
    );
    for (out_bit, leaves) in av_fold.iter().enumerate() {
        add_linear(
            &mut terms,
            mac_half_tree_count_index(out_bit),
            MAC_HALF_AP_BITS_START + out_bit,
            Fp::ONE,
        );
        for (x_bit, present) in leaves.iter().copied().enumerate() {
            if present {
                add_linear(
                    &mut terms,
                    mac_half_tree_count_index(out_bit),
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
    let mut terms = Vec::new();
    for half in 0..MDOC_P4B_MAC_HALF_COUNT {
        let input_offset = mac_batch_half_group_a_input_offset(half);
        let b_input_offset = mac_batch_half_group_b_full_input_offset(half);
        add_linear(
            &mut terms,
            mac_batch_tree_const_index(half),
            input_offset + MAC_HALF_CONST_ONE_INDEX,
            Fp::ONE,
        );
        for (out_bit, leaves) in av_fold.iter().enumerate() {
            add_linear(
                &mut terms,
                mac_batch_tree_count_index(half, out_bit),
                input_offset + MAC_HALF_AP_BITS_START + out_bit,
                Fp::ONE,
            );
            for (x_bit, present) in leaves.iter().copied().enumerate() {
                if present {
                    add_linear(
                        &mut terms,
                        mac_batch_tree_count_index(half, out_bit),
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

fn mac_half_parity_layer(
    tag_bits: &[bool; GF128_BITS],
    local_constraints: usize,
) -> Result<Layer, CircuitError> {
    let mut terms = Vec::new();
    add_linear(
        &mut terms,
        mac_half_tree_const_index(),
        mac_half_tree_const_index(),
        Fp::ONE,
    );
    for bit in 0..GF128_BITS {
        let tag_pin = mac_half_tree_local_start() + MAC_HALF_BOOL_CONSTRAINTS + bit;
        add_linear(&mut terms, tag_pin, mac_half_tree_count_index(bit), Fp::ONE);
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

fn mac_batch_parity_layer(
    tag_bits: &[[bool; GF128_BITS]; MDOC_P4B_MAC_HALF_COUNT],
    local_constraints: usize,
) -> Result<Layer, CircuitError> {
    let mut terms = Vec::new();
    for half in 0..MDOC_P4B_MAC_HALF_COUNT {
        add_linear(
            &mut terms,
            mac_batch_tree_const_index(half),
            mac_batch_tree_const_index(half),
            Fp::ONE,
        );
        for bit in 0..GF128_BITS {
            let tag_pin = mac_batch_tree_local_start(half) + MAC_HALF_BOOL_CONSTRAINTS + bit;
            add_linear(
                &mut terms,
                tag_pin,
                mac_batch_tree_count_index(half, bit),
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
    1 + GF128_BITS + GF128_BITS + MAC_HALF_LOCAL_CONSTRAINTS
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

fn mac_half_tree_count_index(bit: usize) -> usize {
    debug_assert!(bit < GF128_BITS);
    1 + bit
}

fn mac_half_tree_qsum_start() -> usize {
    1 + GF128_BITS
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
    let half = MAC_BATCH_CANONICAL_FIRST_HALF + 2 * value + bit / GF128_BITS;
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

fn mac_batch_tree_count_index(half: usize, bit: usize) -> usize {
    mac_batch_tree_half_start(half) + mac_half_tree_count_index(bit)
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
    for bit in 0..GF128_BITS {
        counts[bit] = usize::from(ap_bits[bit]);
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

fn add_bool_constraint(terms: &mut Vec<QuadTerm>, out: usize, wire: usize) {
    add_quadratic(terms, out, wire, wire, Fp::ONE);
    add_linear(terms, out, wire, -Fp::ONE);
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
    let mut terms = Vec::with_capacity(C1_CANONICAL_FIELD_VALUE_COUNT as usize * (N_LIMBS + 1));
    // z is deliberately absent here: a SHA-256 digest is an arbitrary 256-bit
    // integer, not necessarily a canonical Fp element. Its exact C1 limbs bind
    // to the range-constrained C3 limbs through authenticated linear claims.
    for field_value_index in 0..C1_CANONICAL_FIELD_VALUE_COUNT {
        let input_value_index = field_value_index + 1;
        let out = field_value_index;
        let value_wire = C1_VALUES_START_INDEX + field_value_index;
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
                l: C1_LIMBS_START_INDEX + input_value_index * N_LIMBS as u32 + limb,
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
    for (field_value_index, value) in [input.r, input.s, input.qx, input.qy]
        .into_iter()
        .enumerate()
    {
        circuit_input[C1_VALUES_START_INDEX as usize + field_value_index] =
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

    for limb in 0..N_LIMBS {
        add_limb_range_constraints(
            &mut terms,
            &mut out,
            C3_Z_LIMBS_START + limb,
            C3_Z_BITS_START + limb * LIMB_BITS,
            if limb + 1 == N_LIMBS { 9 } else { LIMB_BITS },
        );
    }
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

    add_bool_constraint(&mut terms, out, C3_U1_ZERO_INDEX);
    out += 1;
    add_quadratic(&mut terms, out, C3_U1_INDEX, C3_U1_ZERO_INDEX, Fp::ONE);
    out += 1;
    add_quadratic(
        &mut terms,
        out,
        C3_U1_INDEX,
        C3_U1_NONZERO_INV_INDEX,
        Fp::ONE,
    );
    add_linear(&mut terms, out, C3_U1_ZERO_INDEX, Fp::ONE);
    add_constant(&mut terms, out, -Fp::ONE);
    out += 1;
    add_quadratic(
        &mut terms,
        out,
        C3_U1_ZERO_INDEX,
        C3_U1_NONZERO_INV_INDEX,
        Fp::ONE,
    );
    out += 1;

    const {
        assert!(C3_U1_NONZERO_INV_INDEX < 1usize << C3_C5_SCALAR_SETUP_INPUT_LOG_SIZE);
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
    let mut circuit_input = vec![Fp::ZERO; 1usize << C3_C5_SCALAR_SETUP_INPUT_LOG_SIZE];
    circuit_input[C3_CONST_ONE_INDEX] = Fp::ONE;
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
    let u1 = circuit_input[C3_U1_INDEX];
    if u1 == Fp::ZERO {
        circuit_input[C3_U1_ZERO_INDEX] = Fp::ONE;
        circuit_input[C3_U1_NONZERO_INV_INDEX] = Fp::ZERO;
    } else {
        circuit_input[C3_U1_ZERO_INDEX] = Fp::ZERO;
        circuit_input[C3_U1_NONZERO_INV_INDEX] =
            u1.inverse().expect("nonzero field element has an inverse");
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

/// Constrains both ECDSA scalar-multiplication ladders.
///
/// The circuit decomposes and recomposes each scalar.
/// It checks each double and add transition.
/// The u2 ladder uses the public key from C2.
/// C11 consumes each corrected final accumulator.
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
            // Afterward, it is `double` plus the constrained add delta if and only if
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
    let u1 = witness.values[us.start];
    circuit_input[C9_U1_INDEX] = if u1 == Fp::ZERO { Fp::ONE } else { u1 };
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
    let mut terms = Vec::new();
    let mut out = 0;

    for selector in [
        C11_U1_ZERO_INDEX,
        C11_DOUBLE_SELECTOR_INDEX,
        C11_GENERIC_SELECTOR_INDEX,
    ] {
        add_bool_constraint(&mut terms, out, selector as usize);
        out += 1;
    }

    // Exactly one branch supplies R: u1 = 0 selects B, A = B selects 2A,
    // and all other affine pairs use the generic addition formula.
    for selector in [
        C11_U1_ZERO_INDEX,
        C11_DOUBLE_SELECTOR_INDEX,
        C11_GENERIC_SELECTOR_INDEX,
    ] {
        add_linear(&mut terms, out, selector as usize, Fp::ONE);
    }
    add_constant(&mut terms, out, -Fp::ONE);
    out += 1;

    // The double branch is available only when A and B are the same point.
    add_quadratic(
        &mut terms,
        out,
        C11_DOUBLE_SELECTOR_INDEX as usize,
        C11_BX_INDEX as usize,
        Fp::ONE,
    );
    add_quadratic(
        &mut terms,
        out,
        C11_DOUBLE_SELECTOR_INDEX as usize,
        C11_AX_INDEX as usize,
        -Fp::ONE,
    );
    out += 1;
    add_quadratic(
        &mut terms,
        out,
        C11_DOUBLE_SELECTOR_INDEX as usize,
        C11_BY_INDEX as usize,
        Fp::ONE,
    );
    add_quadratic(
        &mut terms,
        out,
        C11_DOUBLE_SELECTOR_INDEX as usize,
        C11_AY_INDEX as usize,
        -Fp::ONE,
    );
    out += 1;

    // Generic denominator inverse: (Bx - Ax) * inverse = generic_selector.
    add_quadratic(
        &mut terms,
        out,
        C11_BX_INDEX as usize,
        C11_GENERIC_DENOM_INV_INDEX as usize,
        Fp::ONE,
    );
    add_quadratic(
        &mut terms,
        out,
        C11_AX_INDEX as usize,
        C11_GENERIC_DENOM_INV_INDEX as usize,
        -Fp::ONE,
    );
    add_linear(
        &mut terms,
        out,
        C11_GENERIC_SELECTOR_INDEX as usize,
        -Fp::ONE,
    );
    out += 1;

    // Keep inactive generic auxiliaries deterministic.
    add_linear(
        &mut terms,
        out,
        C11_GENERIC_DENOM_INV_INDEX as usize,
        Fp::ONE,
    );
    add_quadratic(
        &mut terms,
        out,
        C11_GENERIC_SELECTOR_INDEX as usize,
        C11_GENERIC_DENOM_INV_INDEX as usize,
        -Fp::ONE,
    );
    out += 1;
    add_linear(&mut terms, out, C11_GENERIC_LAMBDA_INDEX as usize, Fp::ONE);
    add_quadratic(
        &mut terms,
        out,
        C11_GENERIC_SELECTOR_INDEX as usize,
        C11_GENERIC_LAMBDA_INDEX as usize,
        -Fp::ONE,
    );
    out += 1;

    // lambda_g * (Bx - Ax) = g * (By - Ay).
    add_quadratic(
        &mut terms,
        out,
        C11_GENERIC_LAMBDA_INDEX as usize,
        C11_BX_INDEX as usize,
        Fp::ONE,
    );
    add_quadratic(
        &mut terms,
        out,
        C11_GENERIC_LAMBDA_INDEX as usize,
        C11_AX_INDEX as usize,
        -Fp::ONE,
    );
    add_quadratic(
        &mut terms,
        out,
        C11_GENERIC_SELECTOR_INDEX as usize,
        C11_BY_INDEX as usize,
        -Fp::ONE,
    );
    add_quadratic(
        &mut terms,
        out,
        C11_GENERIC_SELECTOR_INDEX as usize,
        C11_AY_INDEX as usize,
        Fp::ONE,
    );
    out += 1;

    // Xg = lambda_g^2 - Ax - Bx.
    // Yg = lambda_g * (Ax - Xg) - Ay.
    add_linear(&mut terms, out, C11_GENERIC_X_INDEX as usize, Fp::ONE);
    add_quadratic(
        &mut terms,
        out,
        C11_GENERIC_LAMBDA_INDEX as usize,
        C11_GENERIC_LAMBDA_INDEX as usize,
        -Fp::ONE,
    );
    add_linear(&mut terms, out, C11_AX_INDEX as usize, Fp::ONE);
    add_linear(&mut terms, out, C11_BX_INDEX as usize, Fp::ONE);
    out += 1;
    add_linear(&mut terms, out, C11_GENERIC_Y_INDEX as usize, Fp::ONE);
    add_quadratic(
        &mut terms,
        out,
        C11_GENERIC_LAMBDA_INDEX as usize,
        C11_AX_INDEX as usize,
        -Fp::ONE,
    );
    add_quadratic(
        &mut terms,
        out,
        C11_GENERIC_LAMBDA_INDEX as usize,
        C11_GENERIC_X_INDEX as usize,
        Fp::ONE,
    );
    add_linear(&mut terms, out, C11_AY_INDEX as usize, Fp::ONE);
    out += 1;

    // P-256 has a = -3. Compute 2A for every branch so the selected double
    // candidate is fully constrained without selector-gated auxiliaries.
    add_linear(&mut terms, out, C11_AX_SQUARED_INDEX as usize, Fp::ONE);
    add_quadratic(
        &mut terms,
        out,
        C11_AX_INDEX as usize,
        C11_AX_INDEX as usize,
        -Fp::ONE,
    );
    out += 1;
    add_quadratic(
        &mut terms,
        out,
        C11_AY_INDEX as usize,
        C11_DOUBLE_DENOM_INV_INDEX as usize,
        Fp::from_u64(2),
    );
    add_constant(&mut terms, out, -Fp::ONE);
    out += 1;
    add_quadratic(
        &mut terms,
        out,
        C11_AY_INDEX as usize,
        C11_DOUBLE_LAMBDA_INDEX as usize,
        Fp::from_u64(2),
    );
    add_linear(
        &mut terms,
        out,
        C11_AX_SQUARED_INDEX as usize,
        -Fp::from_u64(3),
    );
    add_constant(&mut terms, out, Fp::from_u64(3));
    out += 1;
    add_linear(&mut terms, out, C11_DOUBLE_X_INDEX as usize, Fp::ONE);
    add_quadratic(
        &mut terms,
        out,
        C11_DOUBLE_LAMBDA_INDEX as usize,
        C11_DOUBLE_LAMBDA_INDEX as usize,
        -Fp::ONE,
    );
    add_linear(&mut terms, out, C11_AX_INDEX as usize, Fp::from_u64(2));
    out += 1;
    add_linear(&mut terms, out, C11_DOUBLE_Y_INDEX as usize, Fp::ONE);
    add_quadratic(
        &mut terms,
        out,
        C11_DOUBLE_LAMBDA_INDEX as usize,
        C11_AX_INDEX as usize,
        -Fp::ONE,
    );
    add_quadratic(
        &mut terms,
        out,
        C11_DOUBLE_LAMBDA_INDEX as usize,
        C11_DOUBLE_X_INDEX as usize,
        Fp::ONE,
    );
    add_linear(&mut terms, out, C11_AY_INDEX as usize, Fp::ONE);
    out += 1;

    // R = f*B + d*(2A) + g*(A+B), with f implicit from f+d+g=1.
    for (result, base, generic, doubled) in [
        (
            C11_RX_INDEX,
            C11_BX_INDEX,
            C11_GENERIC_X_INDEX,
            C11_DOUBLE_X_INDEX,
        ),
        (
            C11_RY_INDEX,
            C11_BY_INDEX,
            C11_GENERIC_Y_INDEX,
            C11_DOUBLE_Y_INDEX,
        ),
    ] {
        add_linear(&mut terms, out, result as usize, Fp::ONE);
        add_linear(&mut terms, out, base as usize, -Fp::ONE);
        add_quadratic(
            &mut terms,
            out,
            C11_GENERIC_SELECTOR_INDEX as usize,
            generic as usize,
            -Fp::ONE,
        );
        add_quadratic(
            &mut terms,
            out,
            C11_GENERIC_SELECTOR_INDEX as usize,
            base as usize,
            Fp::ONE,
        );
        add_quadratic(
            &mut terms,
            out,
            C11_DOUBLE_SELECTOR_INDEX as usize,
            doubled as usize,
            -Fp::ONE,
        );
        add_quadratic(
            &mut terms,
            out,
            C11_DOUBLE_SELECTOR_INDEX as usize,
            base as usize,
            Fp::ONE,
        );
        out += 1;
    }

    debug_assert!(out <= 1usize << C11_FINAL_ADD_OUTPUT_LOG_SIZE);
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
    let generic_denom_inv = witness.values[final_add_inverse.start];
    let u1 = witness.values[layout_range(LayoutSlot::UScalars).start];
    let u1_zero = u1 == Fp::ZERO;
    let double_selector = !u1_zero && ax == bx && ay == by;
    let generic_selector = !u1_zero && !double_selector;
    if generic_selector && (bx - ax) * generic_denom_inv != Fp::ONE {
        return Err(WitnessError::ExceptionalTrace);
    }
    let generic_lambda = if generic_selector {
        (by - ay) * generic_denom_inv
    } else {
        Fp::ZERO
    };
    let generic_x = generic_lambda.square() - ax - bx;
    let generic_y = generic_lambda * (ax - generic_x) - ay;
    let ax_squared = ax.square();
    let double_denom_inv = (ay + ay).inverse().ok_or(WitnessError::ExceptionalTrace)?;
    let double_lambda = (Fp::from_u64(3) * ax_squared - Fp::from_u64(3)) * double_denom_inv;
    let double_x = double_lambda.square() - ax - ax;
    let double_y = double_lambda * (ax - double_x) - ay;

    let mut input = vec![Fp::ZERO; 1usize << C11_FINAL_ADD_INPUT_LOG_SIZE];
    input[C11_CONST_ONE_INDEX as usize] = Fp::ONE;
    input[C11_AX_INDEX as usize] = ax;
    input[C11_AY_INDEX as usize] = ay;
    input[C11_BX_INDEX as usize] = bx;
    input[C11_BY_INDEX as usize] = by;
    input[C11_RX_INDEX as usize] = rx;
    input[C11_RY_INDEX as usize] = ry;
    input[C11_GENERIC_LAMBDA_INDEX as usize] = generic_lambda;
    input[C11_GENERIC_DENOM_INV_INDEX as usize] = generic_denom_inv;
    input[C11_U1_ZERO_INDEX as usize] = fp_bit(u1_zero);
    input[C11_DOUBLE_SELECTOR_INDEX as usize] = fp_bit(double_selector);
    input[C11_GENERIC_SELECTOR_INDEX as usize] = fp_bit(generic_selector);
    input[C11_GENERIC_X_INDEX as usize] = generic_x;
    input[C11_GENERIC_Y_INDEX as usize] = generic_y;
    input[C11_DOUBLE_LAMBDA_INDEX as usize] = double_lambda;
    input[C11_DOUBLE_DENOM_INV_INDEX as usize] = double_denom_inv;
    input[C11_DOUBLE_X_INDEX as usize] = double_x;
    input[C11_DOUBLE_Y_INDEX as usize] = double_y;
    input[C11_AX_SQUARED_INDEX as usize] = ax_squared;
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
    use p256::ecdsa::signature::hazmat::{PrehashSigner, PrehashVerifier};
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
        signed_p4b_input_for_digest(secret, Sha256::digest(message).into())
    }

    fn signed_p4b_input_for_digest(secret: u8, z: [u8; 32]) -> EcdsaInput {
        let signing_key = SigningKey::from_bytes((&[secret; 32]).into()).unwrap();
        let signature: P256Signature = signing_key.sign_prehash(&z).unwrap();
        let public_key = signing_key.verifying_key().to_encoded_point(false);
        let mut qx = [0u8; 32];
        let mut qy = [0u8; 32];
        qx.copy_from_slice(public_key.x().unwrap());
        qy.copy_from_slice(public_key.y().unwrap());
        EcdsaInput {
            z,
            r: signature.r().to_bytes().into(),
            s: signature.s().to_bytes().into(),
            qx,
            qy,
        }
    }

    fn d1_manual_signature_input(z: U256Words, nonce_point: ProjectivePoint) -> EcdsaInput {
        let mut secret = [0u8; 32];
        secret[31] = 1;
        let signing_key = SigningKey::from_bytes((&secret).into()).expect("d = 1 is valid");
        let (qx, qy) = projective_point_bytes(ProjectivePoint::GENERATOR).unwrap();
        let (nonce_x, _) = projective_point_bytes(nonce_point).unwrap();
        let (r_words, _) = reduce_field_x_to_scalar(words_from_be(nonce_x));
        let r = be_from_words(&r_words);
        let input = EcdsaInput {
            z: be_from_words(&z),
            r,
            s: r,
            qx,
            qy,
        };
        let signature = P256Signature::from_scalars(input.r, input.s).expect("r and s are valid");
        signing_key
            .verifying_key()
            .verify_prehash(&input.z, &signature)
            .expect("manual d=1 ECDSA vector verifies");
        input
    }

    fn words_plus_one(mut words: U256Words) -> U256Words {
        let mut carry = true;
        for word in &mut words {
            if !carry {
                break;
            }
            let (value, overflow) = word.overflowing_add(1);
            *word = value;
            carry = overflow;
        }
        assert!(!carry, "test vector must remain below 2^256");
        words
    }

    #[test]
    fn c9_c10_ladder_layout_fits_declared_input_domain() {
        let last_input = c9_canonical_carry_index(C9_LADDER_COUNT - 1, C9_SCALAR_BITS);
        assert!(last_input < 1usize << C9_C10_LADDER_INPUT_LOG_SIZE);
    }

    #[test]
    fn p4b_public_key_projection_hides_digest_and_signature() {
        let issuer = p4b_microbench_input(17);
        let device = p4b_microbench_input(19);
        let revocation = p4b_microbench_input(23);
        let issuer_projection = EcdsaPublicProjection::public_key_only(issuer.qx, issuer.qy);
        let device_projection = EcdsaPublicProjection::message_hash_only(device.z);
        let revocation_projection =
            EcdsaPublicProjection::public_key_only(revocation.qx, revocation.qy);
        assert_eq!(revocation_projection.qx, Some(revocation.qx));
        assert_eq!(revocation_projection.qy, Some(revocation.qy));
        assert_eq!(revocation_projection.z, None);
        assert_eq!(revocation_projection.r, None);
        assert_eq!(revocation_projection.s, None);
        validate_mdoc_p4b_projection_shapes(
            &issuer_projection,
            &device_projection,
            &revocation_projection,
        )
        .unwrap();
        assert!(validate_mdoc_p4b_projection_shapes(
            &issuer_projection,
            &device_projection,
            &EcdsaPublicProjection::message_hash_only(revocation.z),
        )
        .is_err());
        assert!(validate_mdoc_p4b_projection_shapes(
            &issuer_projection,
            &device_projection,
            &EcdsaPublicProjection::full(&revocation),
        )
        .is_err());
    }

    #[test]
    fn p4b_mac_layout_covers_fixed_revocation_halves() {
        let issuer = p4b_microbench_input(19);
        let device = p4b_microbench_input(23);
        let revocation = p4b_microbench_input(29);
        let key_shares = p4b_microbench_key_shares();
        let av = [0x5au8; 16];
        let values = mdoc_p4b_mac_values(&issuer, &device, &revocation);
        assert_eq!(
            mac_batch_group_a_input(&key_shares, &values).unwrap().len(),
            1usize << MAC_BATCH_GROUP_A_INPUT_LOG_SIZE
        );
        let tags: [Gf128; MDOC_P4B_MAC_HALF_COUNT] =
            std::array::from_fn(|half| gf128_tag(&key_shares.0[half], &av, &values[half]));
        assert_eq!(
            mac_batch_group_b_input(&key_shares, &av, &values, &tags)
                .unwrap()
                .len(),
            1usize << MAC_BATCH_GROUP_B_INPUT_LOG_SIZE
        );
        let circuit = build_mac_batch_circuit(&av, &tags).unwrap();
        assert_eq!(
            circuit.layers().first().unwrap().out_log_size(),
            MAC_BATCH_INPUT_LOG_SIZE
        );
        assert_eq!(
            circuit.layers().last().unwrap().next_log_size(),
            MAC_BATCH_INPUT_LOG_SIZE
        );
        assert_eq!([values[6], values[7]], gf128_halves_from_be32(revocation.z));
    }

    #[test]
    fn digest_mac_half_claims_reject_alias_swap_and_independent_tampering() {
        let p_plus_one = words_plus_one(P256_FIELD_MODULUS);
        let digest = be_from_words(&p_plus_one);
        let input = signed_p4b_input_for_digest(13, digest);
        let witness = generate_witness(&input).expect("boundary digest witness");
        let c3_input = c3_c5_scalar_setup_input(&input, &witness).expect("C3 input");

        let key_shares = p4b_microbench_key_shares();
        let mut mac_values = [[0u8; 16]; MDOC_P4B_MAC_HALF_COUNT];
        [mac_values[0], mac_values[1]] = gf128_halves_from_be32(digest);
        let mac_input = mac_batch_group_a_input(&key_shares, &mac_values).expect("MAC input");
        let c3_layout = BundleCircuitLayout {
            input_offset: 0,
            input_len: c3_input.len(),
            pad_offset: c3_input.len(),
            pad_len: 0,
        };
        let mac_layout = BundleCircuitLayout {
            input_offset: c3_input.len(),
            input_len: mac_input.len(),
            pad_offset: c3_input.len() + mac_input.len(),
            pad_len: 0,
        };
        let mut committed = c3_input;
        committed.extend(mac_input);
        let mut claims = Vec::new();
        add_mac_digest_binding(&mut claims, &c3_layout, &mac_layout, 0, 1);
        assert_eq!(claims.len(), 2);
        let evaluate = |claim: &LigeroLinearClaim, values: &[Fp]| {
            claim.terms.iter().fold(Fp::ZERO, |sum, term| {
                let mle = Mle::new(values[term.offset..term.offset + term.len].to_vec());
                sum + term.coefficient * mle.eval_at(&term.point).unwrap()
            })
        };
        assert!(claims
            .iter()
            .all(|claim| evaluate(claim, &committed) == claim.value));

        let mac_low = mac_layout.input_offset
            + mac_batch_half_group_a_input_offset(0)
            + MAC_HALF_X_BITS_START;
        let mac_high = mac_layout.input_offset
            + mac_batch_half_group_a_input_offset(1)
            + MAC_HALF_X_BITS_START;
        committed[mac_low] = Fp::ONE - committed[mac_low];
        assert_ne!(evaluate(&claims[0], &committed), claims[0].value);
        assert_eq!(evaluate(&claims[1], &committed), claims[1].value);
        committed[mac_low] = Fp::ONE - committed[mac_low];
        committed[mac_high] = Fp::ONE - committed[mac_high];
        assert_eq!(evaluate(&claims[0], &committed), claims[0].value);
        assert_ne!(evaluate(&claims[1], &committed), claims[1].value);
        committed[mac_high] = Fp::ONE - committed[mac_high];

        for bit in 0..GF128_BITS {
            committed.swap(mac_low + bit, mac_high + bit);
        }
        assert!(
            claims
                .iter()
                .any(|claim| evaluate(claim, &committed) != claim.value),
            "low/high digest halves must not be interchangeable"
        );
        for bit in 0..GF128_BITS {
            committed.swap(mac_low + bit, mac_high + bit);
        }

        let one_halves = gf128_halves_from_be32(be_from_words(&[1, 0, 0, 0]));
        assert_eq!(
            recompose_gf128_halves(&mac_values[0], &mac_values[1]),
            recompose_gf128_halves(&one_halves[0], &one_halves[1]),
            "p+1 aliases one only under a whole-field recomposition"
        );
        for (half, replacement) in one_halves.into_iter().enumerate() {
            let replacement_input =
                mac_half_group_a_input(&key_shares.0[half], &replacement).unwrap();
            let offset = mac_layout.input_offset + mac_batch_half_group_a_input_offset(half);
            committed[offset..offset + replacement_input.len()].copy_from_slice(&replacement_input);
        }
        assert!(
            claims
                .iter()
                .any(|claim| evaluate(claim, &committed) != claim.value),
            "separate 128-bit claims must reject the p+1 versus one alias"
        );
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
    fn c3_accepts_full_digest_space_and_rejects_bit_tampering() {
        let circuit = build_c3_c5_scalar_setup_circuit().expect("C3 circuit builds");
        let p_plus_one = words_plus_one(P256_FIELD_MODULUS);
        for (label, words) in [
            ("zero", [0; 4]),
            ("n-1", P256_ORDER_MINUS_ONE),
            ("n", P256_ORDER),
            ("p", P256_FIELD_MODULUS),
            ("p+1", p_plus_one),
            ("2^256-1", [u64::MAX; 4]),
        ] {
            let input = signed_p4b_input_for_digest(9, be_from_words(&words));
            let witness = generate_witness(&input)
                .unwrap_or_else(|error| panic!("z={label} boundary witness failed: {error:?}"));
            let mut c3_input = c3_c5_scalar_setup_input(&input, &witness).expect("C3 input builds");
            let layers = circuit
                .evaluate_input(c3_input.clone())
                .expect("input has circuit width");
            assert!(
                circuit
                    .is_satisfied(&layers)
                    .expect("circuit shape is valid"),
                "valid prehash signature at z={label} must satisfy C3"
            );

            if label == "zero" {
                let mut bad_flag = c3_input.clone();
                bad_flag[C3_U1_ZERO_INDEX] = Fp::ZERO;
                let layers = circuit
                    .evaluate_input(bad_flag)
                    .expect("input has circuit width");
                assert!(
                    !circuit.is_satisfied(&layers).expect("valid circuit shape"),
                    "u1=0 must require the zero-scalar flag"
                );

                let mut bad_inverse = c3_input.clone();
                bad_inverse[C3_U1_NONZERO_INV_INDEX] = Fp::ONE;
                let layers = circuit
                    .evaluate_input(bad_inverse)
                    .expect("input has circuit width");
                assert!(
                    !circuit.is_satisfied(&layers).expect("valid circuit shape"),
                    "the zero branch must constrain its nominal inverse to zero"
                );
            }

            c3_input[C3_Z_BITS_START] = Fp::ONE - c3_input[C3_Z_BITS_START];
            let tampered = circuit
                .evaluate_input(c3_input)
                .expect("input has circuit width");
            assert!(
                !circuit
                    .is_satisfied(&tampered)
                    .expect("circuit shape is valid"),
                "changing one exact digest bit at z={label} must fail"
            );
        }
    }

    #[test]
    fn c9_c11_accept_zero_double_and_generic_branches_and_reject_mutations() {
        let generator = ProjectivePoint::GENERATOR;
        let doubled_generator = generator + generator;
        let (doubled_x, _) = projective_point_bytes(doubled_generator).unwrap();
        let (doubled_r, _) = reduce_field_x_to_scalar(words_from_be(doubled_x));
        let cases = [
            ("z=0", d1_manual_signature_input([0; 4], generator), 0),
            ("z=n", d1_manual_signature_input(P256_ORDER, generator), 0),
            (
                "A=B",
                d1_manual_signature_input(doubled_r, doubled_generator),
                1,
            ),
            ("generic", signed_p4b_input(11, b"generic C11 branch"), 2),
        ];
        let circuit = build_c11_final_add_circuit().expect("C11 circuit builds");
        let is_satisfied = |input: Vec<Fp>| {
            let layers = circuit.evaluate_input(input).expect("C11 input width");
            circuit.is_satisfied(&layers).expect("C11 circuit shape")
        };

        let mut branch_inputs = Vec::new();
        for (label, input, expected_branch) in cases {
            let witness = generate_witness(&input)
                .unwrap_or_else(|error| panic!("{label} witness failed: {error:?}"));
            verify_implemented_circuits(&input, &witness)
                .unwrap_or_else(|error| panic!("{label} circuits failed: {error:?}"));
            let c11_input = c11_final_add_input(&witness).expect("C11 input builds");
            assert!(is_satisfied(c11_input.clone()), "{label} must satisfy C11");
            assert_eq!(
                [
                    c11_input[C11_U1_ZERO_INDEX as usize],
                    c11_input[C11_DOUBLE_SELECTOR_INDEX as usize],
                    c11_input[C11_GENERIC_SELECTOR_INDEX as usize],
                ],
                std::array::from_fn(|branch| fp_bit(branch == expected_branch)),
                "{label} must select exactly the expected branch"
            );
            branch_inputs.push((label, c11_input));
        }

        for (label, input) in &branch_inputs {
            let selected = [
                C11_U1_ZERO_INDEX as usize,
                C11_DOUBLE_SELECTOR_INDEX as usize,
                C11_GENERIC_SELECTOR_INDEX as usize,
            ]
            .into_iter()
            .find(|&index| input[index] == Fp::ONE)
            .unwrap();
            let mut mutated = input.clone();
            mutated[selected] = Fp::ZERO;
            assert!(
                !is_satisfied(mutated),
                "{label} one-hot selector mutation must fail"
            );
        }

        for result in [C11_RX_INDEX as usize, C11_RY_INDEX as usize] {
            let mut mutated = branch_inputs[0].1.clone();
            mutated[result] = mutated[result] + Fp::ONE;
            assert!(
                !is_satisfied(mutated),
                "the zero-scalar branch must bind selected result wire {result}"
            );
        }

        for (label, branch, indices) in [
            (
                "generic",
                3usize,
                [
                    C11_GENERIC_DENOM_INV_INDEX as usize,
                    C11_GENERIC_LAMBDA_INDEX as usize,
                    C11_GENERIC_X_INDEX as usize,
                    C11_GENERIC_Y_INDEX as usize,
                    C11_RX_INDEX as usize,
                    C11_RY_INDEX as usize,
                ],
            ),
            (
                "double",
                2usize,
                [
                    C11_DOUBLE_DENOM_INV_INDEX as usize,
                    C11_DOUBLE_LAMBDA_INDEX as usize,
                    C11_DOUBLE_X_INDEX as usize,
                    C11_DOUBLE_Y_INDEX as usize,
                    C11_RX_INDEX as usize,
                    C11_RY_INDEX as usize,
                ],
            ),
        ] {
            for index in indices {
                let mut mutated = branch_inputs[branch].1.clone();
                mutated[index] = mutated[index] + Fp::ONE;
                assert!(
                    !is_satisfied(mutated),
                    "{label} auxiliary/result wire {index} mutation must fail"
                );
            }
        }

        // A and -A have the same x coordinate, so affine addition returns the
        // identity. No C11 branch represents the identity.
        let mut opposite = branch_inputs[2].1.clone();
        opposite[C11_BY_INDEX as usize] = -opposite[C11_AY_INDEX as usize];
        opposite[C11_DOUBLE_SELECTOR_INDEX as usize] = Fp::ZERO;
        opposite[C11_GENERIC_SELECTOR_INDEX as usize] = Fp::ONE;
        opposite[C11_GENERIC_DENOM_INV_INDEX as usize] = Fp::ZERO;
        opposite[C11_GENERIC_LAMBDA_INDEX as usize] = Fp::ZERO;
        opposite[C11_GENERIC_X_INDEX as usize] =
            -opposite[C11_AX_INDEX as usize] - opposite[C11_BX_INDEX as usize];
        opposite[C11_GENERIC_Y_INDEX as usize] = -opposite[C11_AY_INDEX as usize];
        opposite[C11_RX_INDEX as usize] = opposite[C11_GENERIC_X_INDEX as usize];
        opposite[C11_RY_INDEX as usize] = opposite[C11_GENERIC_Y_INDEX as usize];
        assert!(
            !is_satisfied(opposite.clone()),
            "A + (-A) must be rejected in the generic branch"
        );
        let mut wrong_double = opposite;
        wrong_double[C11_DOUBLE_SELECTOR_INDEX as usize] = Fp::ONE;
        wrong_double[C11_GENERIC_SELECTOR_INDEX as usize] = Fp::ZERO;
        wrong_double[C11_RX_INDEX as usize] = wrong_double[C11_DOUBLE_X_INDEX as usize];
        wrong_double[C11_RY_INDEX as usize] = wrong_double[C11_DOUBLE_Y_INDEX as usize];
        assert!(
            !is_satisfied(wrong_double),
            "A + (-A) must not be misclassified as the double branch"
        );

        let double_input = d1_manual_signature_input(doubled_r, doubled_generator);
        let mut opposite_witness = generate_witness(&double_input).unwrap();
        let corrected = layout_range(LayoutSlot::CorrectedEndpoints);
        opposite_witness.values[corrected.start + 3] =
            -opposite_witness.values[corrected.start + 1];
        opposite_witness.values[layout_range(LayoutSlot::FinalAddDenominatorInverse).start] =
            Fp::ZERO;
        assert_eq!(
            c11_final_add_input(&opposite_witness),
            Err(WitnessError::ExceptionalTrace),
            "the input builder must reject an identity-producing affine pair"
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
    fn ecdsa_affine_claims_bind_private_family_copies() {
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
        assert_eq!(claims.len(), 48);
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
        values[layouts[2].input_offset + C3_U1_ZERO_INDEX] = Fp::ZERO;
        values[layouts[4].input_offset + C11_U1_ZERO_INDEX as usize] = Fp::ZERO;
        assert!(claims
            .iter()
            .all(|claim| evaluate(claim, &values) == claim.value));

        let p_plus_one = words_plus_one(P256_FIELD_MODULUS);
        for (limb, value) in words_to_limbs(&p_plus_one).into_iter().enumerate() {
            values[layouts[0].input_offset + C1_LIMBS_START_INDEX as usize + limb] =
                Fp::from_u64(u64::from(value));
            values[layouts[2].input_offset + C3_Z_LIMBS_START + limb] =
                Fp::from_u64(u64::from(value));
        }
        assert!(claims
            .iter()
            .all(|claim| evaluate(claim, &values) == claim.value));
        for (limb, value) in words_to_limbs(&[1, 0, 0, 0]).into_iter().enumerate() {
            values[layouts[0].input_offset + C1_LIMBS_START_INDEX as usize + limb] =
                Fp::from_u64(u64::from(value));
        }
        assert!(
            claims
                .iter()
                .any(|claim| evaluate(claim, &values) != claim.value),
            "p+1 and 1 must not alias across the exact C1/C3 limb claims"
        );
        for (limb, value) in words_to_limbs(&p_plus_one).into_iter().enumerate() {
            values[layouts[0].input_offset + C1_LIMBS_START_INDEX as usize + limb] =
                Fp::from_u64(u64::from(value));
        }

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
        values[layouts[6].input_offset + C14_SIGNATURE_R_INDEX] = Fp::from_u64(7);
        values[layouts[2].input_offset + C3_U1_ZERO_INDEX] = Fp::ONE;
        values[layouts[4].input_offset + C11_U1_ZERO_INDEX as usize] = Fp::ONE;
        values[layouts[3].input_offset + C9_U1_INDEX] = Fp::from_u64(8);
        assert!(
            claims
                .iter()
                .all(|claim| evaluate(claim, &values) == claim.value),
            "the effective-u1 affine claim must accept u1_eff = u1 + zero_flag"
        );
        values[layouts[4].input_offset + C11_U1_ZERO_INDEX as usize] = Fp::ZERO;
        assert!(
            claims
                .iter()
                .any(|claim| evaluate(claim, &values) != claim.value),
            "C3 and C11 must authenticate the same zero-scalar branch flag"
        );
    }

    #[test]
    fn c1_public_digest_limb_claims_reject_p_plus_one_as_one() {
        let p_plus_one = words_plus_one(P256_FIELD_MODULUS);
        let projection = EcdsaPublicProjection::message_hash_only(be_from_words(&p_plus_one));
        let layout = BundleCircuitLayout {
            input_offset: 0,
            input_len: 1usize << C1_INPUT_LIMBS_INPUT_LOG_SIZE,
            pad_offset: 1usize << C1_INPUT_LIMBS_INPUT_LOG_SIZE,
            pad_len: 0,
        };
        let mut claims = Vec::new();
        add_c1_public_claims(&mut claims, &projection, &layout).expect("public z limbs bind");
        assert_eq!(claims.len(), N_LIMBS);

        let evaluate = |claim: &LigeroLinearClaim, values: &[Fp]| {
            claim.terms.iter().fold(Fp::ZERO, |sum, term| {
                let mle = Mle::new(values[term.offset..term.offset + term.len].to_vec());
                sum + term.coefficient * mle.eval_at(&term.point).unwrap()
            })
        };
        let mut committed = vec![Fp::ZERO; layout.input_len];
        for (limb, value) in words_to_limbs(&p_plus_one).into_iter().enumerate() {
            committed[C1_LIMBS_START_INDEX as usize + limb] = Fp::from_u64(u64::from(value));
        }
        assert!(claims
            .iter()
            .all(|claim| evaluate(claim, &committed) == claim.value));

        for (limb, value) in words_to_limbs(&[1, 0, 0, 0]).into_iter().enumerate() {
            committed[C1_LIMBS_START_INDEX as usize + limb] = Fp::from_u64(u64::from(value));
        }
        assert!(
            claims
                .iter()
                .any(|claim| evaluate(claim, &committed) != claim.value),
            "public p+1 and one digests must not alias through Fp"
        );
    }

    fn median_duration(values: &mut [Duration]) -> Duration {
        values.sort_unstable();
        values[values.len() / 2]
    }

    fn compare_dense_and_structured_claim_verification(
        label: &str,
        issuer_projection: &EcdsaPublicProjection,
        device_projection: &EcdsaPublicProjection,
        revocation_projection: &EcdsaPublicProjection,
        bundle: &ImplementedCircuitBundle,
    ) {
        let mut dense_times = Vec::with_capacity(7);
        let mut structured_times = Vec::with_capacity(7);
        let mut dense_calls = None;
        let mut structured_calls = None;
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
                    if let Some(expected) = structured_calls {
                        assert_eq!(
                            calls, expected,
                            "structured Circle row-encode count changed between runs"
                        );
                    } else {
                        structured_calls = Some(calls);
                    }
                } else {
                    dense_times.push(profile.claim_batch);
                    if let Some(expected) = dense_calls {
                        assert_eq!(
                            calls, expected,
                            "dense Circle row-encode count changed between runs"
                        );
                    } else {
                        dense_calls = Some(calls);
                    }
                }
            }
        }
        crate::ligero::set_structured_claims_for_test(None);
        let dense_calls = dense_calls.expect("dense verifier ran");
        let structured_calls = structured_calls.expect("structured verifier ran");
        let dense = median_duration(&mut dense_times);
        let structured = median_duration(&mut structured_times);
        eprintln!(
            "{label}_claim_batch_dense_ms={:.3} structured_ms={:.3} dense_weight_encodes={} structured_weight_encodes={}",
            dense.as_secs_f64() * 1_000.0,
            structured.as_secs_f64() * 1_000.0,
            dense_calls,
            structured_calls,
        );
        assert!(dense_calls > 0, "dense verifier must encode Circle rows");
        assert!(
            structured_calls * 4 <= dense_calls * 3,
            "structured evaluator must cut Circle row encodes by at least 25%"
        );
    }

    fn gf128_basis(bit: usize) -> Gf128 {
        let mut out = [0u8; 16];
        out[bit / 8] = 1 << (bit % 8);
        out
    }

    #[test]
    fn product_proximity_sampler_uses_full_circle_domain() {
        let root = [0x51; 32];
        let seed = [0xA7; 32];
        let proximity_claim = LigeroProximityClaim {
            combined_row: vec![Fp::ZERO],
        };
        let entries = Vec::new();
        let claim_batch = LigeroClaimBatch {
            coefficients: Vec::new(),
            blind_claim: Fp::ZERO,
        };
        let claim_blind_check = LigeroClaimBlindCheck {
            combined_row: Vec::new(),
        };
        let quadratic_batch = LigeroQuadraticBatch::default();

        let circle = product_circle_params();
        let circle_indices = ligero_opening_indices(
            IMPLEMENTED_BUNDLE_LIGERO_LABEL,
            root,
            circle,
            &proximity_claim,
            &entries,
            &claim_batch,
            &claim_blind_check,
            &quadratic_batch,
            seed,
        );
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
    }

    #[test]
    fn opening_indices_bind_every_prover_response() {
        let params = product_circle_params();
        let root = [0x31; 32];
        let seed = [0x79; 32];
        let proximity_claim = LigeroProximityClaim {
            combined_row: vec![Fp::from_u64(2), Fp::from_u64(3)],
        };
        let entries = vec![ImplementedCircuitBundleEntry {
            proof: CircuitSumcheckProof {
                layers: vec![crate::sumcheck::CircuitLayerProof {
                    rounds: vec![[Fp::from_u64(5), Fp::from_u64(7)]],
                    next_claims: [Fp::from_u64(11), Fp::from_u64(13)],
                }],
            },
        }];
        let claim_batch = LigeroClaimBatch {
            coefficients: vec![Fp::from_u64(17), Fp::from_u64(19)],
            blind_claim: Fp::from_u64(23),
        };
        let claim_blind_check = LigeroClaimBlindCheck {
            combined_row: vec![Fp::from_u64(29), Fp::from_u64(31)],
        };
        let quadratic_batch = LigeroQuadraticBatch {
            quotient: vec![Fp::from_u64(37), Fp::from_u64(41)],
        };
        let baseline = ligero_opening_indices(
            IMPLEMENTED_BUNDLE_LIGERO_LABEL,
            root,
            params,
            &proximity_claim,
            &entries,
            &claim_batch,
            &claim_blind_check,
            &quadratic_batch,
            seed,
        );

        let mut changed_proximity = proximity_claim.clone();
        changed_proximity.combined_row[0] = changed_proximity.combined_row[0] + Fp::ONE;
        assert_ne!(
            baseline,
            ligero_opening_indices(
                IMPLEMENTED_BUNDLE_LIGERO_LABEL,
                root,
                params,
                &changed_proximity,
                &entries,
                &claim_batch,
                &claim_blind_check,
                &quadratic_batch,
                seed,
            )
        );

        let mut changed_entries = entries.clone();
        changed_entries[0].proof.layers[0].rounds[0][0] =
            changed_entries[0].proof.layers[0].rounds[0][0] + Fp::ONE;
        assert_ne!(
            baseline,
            ligero_opening_indices(
                IMPLEMENTED_BUNDLE_LIGERO_LABEL,
                root,
                params,
                &proximity_claim,
                &changed_entries,
                &claim_batch,
                &claim_blind_check,
                &quadratic_batch,
                seed,
            )
        );

        let mut changed_claim_batch = claim_batch.clone();
        changed_claim_batch.blind_claim = changed_claim_batch.blind_claim + Fp::ONE;
        assert_ne!(
            baseline,
            ligero_opening_indices(
                IMPLEMENTED_BUNDLE_LIGERO_LABEL,
                root,
                params,
                &proximity_claim,
                &entries,
                &changed_claim_batch,
                &claim_blind_check,
                &quadratic_batch,
                seed,
            )
        );

        let mut changed_claim_blind_check = claim_blind_check.clone();
        changed_claim_blind_check.combined_row[0] =
            changed_claim_blind_check.combined_row[0] + Fp::ONE;
        assert_ne!(
            baseline,
            ligero_opening_indices(
                IMPLEMENTED_BUNDLE_LIGERO_LABEL,
                root,
                params,
                &proximity_claim,
                &entries,
                &claim_batch,
                &changed_claim_blind_check,
                &quadratic_batch,
                seed,
            )
        );

        let mut changed_quadratic = quadratic_batch.clone();
        changed_quadratic.quotient[0] = changed_quadratic.quotient[0] + Fp::ONE;
        assert_ne!(
            baseline,
            ligero_opening_indices(
                IMPLEMENTED_BUNDLE_LIGERO_LABEL,
                root,
                params,
                &proximity_claim,
                &entries,
                &claim_batch,
                &claim_blind_check,
                &changed_quadratic,
                seed,
            )
        );
    }

    #[test]
    #[ignore = "release gate: real P4b structured/dense verifier timing"]
    fn mdoc_p4b_structured_claim_evaluator_matches_real_fixtures() {
        let issuer = signed_p4b_input(7, b"structured claim issuer");
        let device = signed_p4b_input(9, b"structured claim device");
        let revocation = signed_p4b_input(11, b"structured claim revocation");
        let issuer_projection = EcdsaPublicProjection::issuer_key_only(issuer.qx, issuer.qy);
        let device_projection = EcdsaPublicProjection::message_hash_only(device.z);
        let revocation_projection =
            EcdsaPublicProjection::public_key_only(revocation.qx, revocation.qy);
        let issuer_witness = generate_witness(&issuer).unwrap();
        let device_witness = generate_witness(&device).unwrap();
        let revocation_witness = generate_witness(&revocation).unwrap();
        let key_shares = p4b_microbench_key_shares();

        let revocation_bundle = prove_mdoc_p4b_circuit_bundle(
            &issuer,
            &issuer_projection,
            &issuer_witness,
            &device,
            &device_projection,
            &device_witness,
            (&revocation, &revocation_projection, &revocation_witness),
            &key_shares,
            [9u8; 32],
        )
        .unwrap();
        compare_dense_and_structured_claim_verification(
            "mdoc_p4b_revocation",
            &issuer_projection,
            &device_projection,
            &revocation_projection,
            &revocation_bundle,
        );
    }

    #[test]
    #[allow(clippy::assertions_on_constants)]
    fn q024_affine_mac_parity_bound_is_pinned() {
        assert_eq!(
            MAC_HALF_PARITY_MAX_S,
            GF128_BITS + 1,
            "each output count contains one pad bit and at most 128 public-fold terms"
        );
        assert_eq!(
            MAC_HALF_PARITY_Q_BITS, 7,
            "the affine parity quotient needs seven committed bits"
        );
        assert!(
            (1usize << MAC_HALF_PARITY_Q_BITS) > MAC_HALF_PARITY_MAX_S / 2,
            "q bits must cover every possible (a_p,k + V_k - tag_k) / 2"
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
        let revocation = p4b_microbench_input(31);
        let issuer_public = EcdsaPublicProjection::issuer_key_only(issuer.qx, issuer.qy);
        let device_public = EcdsaPublicProjection::message_hash_only(device.z);
        let revocation_public =
            EcdsaPublicProjection::public_key_only(revocation.qx, revocation.qy);
        let projections = [issuer_public, device_public, revocation_public];
        let transcript_seed = [7u8; 32];
        let root = [31u8; 32];
        let av = draw_mdoc_p4b_av(transcript_seed, root);
        let mac_values = mdoc_p4b_mac_values(&issuer, &device, &revocation);
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
        let pads = CircuitPads::fresh(&circuit);
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
            prove_evaluated_circuit(&circuit, &layers, &pads, root, &mut generic_channel).unwrap();
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
            &pads,
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
        let mut generic_verify_channel = mdoc_p4b_instance_channel(
            transcript_seed,
            root,
            MDOC_P4B_MAC_BATCH_LABEL,
            MdocP4bCircuitRole::MacBatch,
            &projections,
            &av,
            &mac_tags,
        );
        let generic_claims =
            verify_circuit(&circuit, &sparse, root, &mut generic_verify_channel).unwrap();
        assert_eq!(claims, generic_claims);

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
