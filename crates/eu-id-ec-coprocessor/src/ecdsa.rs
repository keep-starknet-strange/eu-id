use core::ops::Range;
use std::time::{Duration, Instant};

use crate::ligero::{
    commit_witness_profiled, v1_ligero_params, verify_openings, LigeroError, LigeroParams,
    LigeroProximityClaim,
};
use crate::merkle::{verify_column, ColumnOpening};
use crate::sumcheck::{
    circuit_otp_pad_values, proof_otp_pad_values, prove_circuit, prove_evaluated_circuit,
    verify_circuit, CircuitSumcheckProof, InputClaims, SumcheckError,
};
use crate::{Circuit, CircuitError, CoprocessorChannel, Fp, Layer, Mle, QuadTerm, TranscriptSeed};
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
pub const C9_C10_ACCUMULATOR_ON_CURVE_INPUT_LOG_SIZE: usize = 11;
pub const C9_C10_ACCUMULATOR_ON_CURVE_OUTPUT_LOG_SIZE: usize = 10;
pub const C11_FINAL_ADD_INPUT_LOG_SIZE: usize = 4;
pub const C11_FINAL_ADD_OUTPUT_LOG_SIZE: usize = 2;
pub const C12_ON_CURVE_INPUT_LOG_SIZE: usize = 11;
pub const C12_ON_CURVE_OUTPUT_LOG_SIZE: usize = 11;
pub const C13_SLOPE_INVERSES_INPUT_LOG_SIZE: usize = 12;
pub const C13_SLOPE_INVERSES_OUTPUT_LOG_SIZE: usize = 11;
pub const C14_C15_INPUT_LOG_SIZE: usize = 3;
pub const C14_C15_OUTPUT_LOG_SIZE: usize = 3;
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
const C9_C10_ACCUMULATOR_POINT_COUNT: usize = 512;
const C9_C10_ACCUMULATOR_POINTS_PER_SCALAR: usize = 256;
const C9_C10_CONST_ONE_INDEX: u32 = 0;
const C9_C10_POINTS_START_INDEX: u32 = 1;
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
    pub openings: Vec<ColumnOpening>,
    pub proximity_openings: Vec<ColumnOpening>,
    pub proximity_claim: LigeroProximityClaim,
    pub entries: Vec<ImplementedCircuitBundleEntry>,
}

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

pub fn prove_implemented_circuit_bundle_batch_profiled(
    inputs: &[EcdsaInput],
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

    let mut profile = ImplementedCircuitProveProfile::default();
    let start = Instant::now();
    for (input, witness) in inputs.iter().zip(witnesses) {
        verify_witness(input, witness).map_err(ImplementedCircuitProofError::Witness)?;
    }
    profile.witness_check = start.elapsed();
    let (bundle, inner_profile) = prove_implemented_circuit_bundle_batch_unchecked_profiled(
        inputs,
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
    if inputs.len() != witnesses.len() {
        return Err(ImplementedCircuitProofError::SignatureCountMismatch {
            inputs: inputs.len(),
            witnesses: witnesses.len(),
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

    let mut committed_values = Vec::new();
    for (witness, instances) in witnesses.iter().zip(&all_instances) {
        committed_values.extend_from_slice(&witness.values);
        for instance in instances {
            committed_values.extend(circuit_otp_pad_values(&instance.circuit));
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
    let openings = commitment
        .open_systematic_columns()
        .map_err(ImplementedCircuitProofError::Ligero)?;
    profile.ligero_openings = start.elapsed();

    let mut entries = Vec::new();
    let start = Instant::now();
    for (signature_index, (input, instances)) in inputs.iter().zip(all_instances).enumerate() {
        for (family_index, instance) in instances.into_iter().enumerate() {
            let layers = instance
                .circuit
                .evaluate_input(instance.input)
                .map_err(ImplementedCircuitProofError::Circuit)?;
            let mut channel =
                CoprocessorChannel::from_seed(transcript_seed, COPROCESSOR_TRANSCRIPT_DOMAIN);
            mix_bundle_signature_index(signature_index, &mut channel);
            channel.mix_bytes(instance.label);
            mix_ecdsa_statement(input, &mut channel)
                .map_err(ImplementedCircuitProofError::Witness)?;
            let family_start = Instant::now();
            let proof = prove_evaluated_circuit(&instance.circuit, &layers, root, &mut channel)
                .map_err(ImplementedCircuitProofError::Sumcheck)?;
            profile.sumcheck_by_family[family_index] += family_start.elapsed();
            entries.push(ImplementedCircuitBundleEntry { proof });
        }
    }
    profile.sumcheck = start.elapsed();

    Ok((
        ImplementedCircuitBundle {
            params,
            root,
            openings,
            proximity_openings,
            proximity_claim,
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

    let mut committed_values = witness.values.clone();
    for instance in &instances {
        committed_values.extend(circuit_otp_pad_values(&instance.circuit));
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
    let openings = commitment
        .open_systematic_columns()
        .map_err(ImplementedCircuitProofError::Ligero)?;
    profile.ligero_openings = start.elapsed();

    let mut entries = Vec::new();
    let start = Instant::now();
    for (index, instance) in instances.into_iter().enumerate() {
        let layers = instance
            .circuit
            .evaluate_input(instance.input)
            .map_err(ImplementedCircuitProofError::Circuit)?;
        let mut channel =
            CoprocessorChannel::from_seed(transcript_seed, COPROCESSOR_TRANSCRIPT_DOMAIN);
        channel.mix_bytes(instance.label);
        mix_ecdsa_statement(input, &mut channel).map_err(ImplementedCircuitProofError::Witness)?;
        let family_start = Instant::now();
        let proof = prove_evaluated_circuit(&instance.circuit, &layers, root, &mut channel)
            .map_err(ImplementedCircuitProofError::Sumcheck)?;
        profile.sumcheck_by_family[index] = family_start.elapsed();
        entries.push(ImplementedCircuitBundleEntry { proof });
    }
    profile.sumcheck = start.elapsed();

    Ok((
        ImplementedCircuitBundle {
            params,
            root,
            openings,
            proximity_openings,
            proximity_claim,
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

pub fn verify_implemented_circuit_bundle_batch_profiled(
    inputs: &[EcdsaInput],
    bundle: &ImplementedCircuitBundle,
    transcript_seed: TranscriptSeed,
) -> Result<(Vec<Vec<InputClaims>>, ImplementedCircuitVerifyProfile), ImplementedCircuitProofError>
{
    let mut profile = ImplementedCircuitVerifyProfile::default();
    let setup_start = Instant::now();
    let circuits =
        implemented_circuit_verifier_instances().map_err(ImplementedCircuitProofError::Circuit)?;
    let expected_entries = inputs.len() * circuits.len();
    if bundle.entries.len() != expected_entries {
        return Err(ImplementedCircuitProofError::WrongProofCount {
            expected: expected_entries,
            actual: bundle.entries.len(),
        });
    }

    let mut signature_layouts = Vec::with_capacity(inputs.len());
    let mut offset = 0;
    for _ in inputs {
        let witness_offset = offset;
        offset += LAYOUT_LEN;
        let (layouts, next_offset) = verifier_bundle_pad_layouts(&circuits, offset);
        signature_layouts.push((witness_offset, layouts));
        offset = next_offset;
    }
    let committed_len = offset;
    if bundle.params != implemented_circuit_ligero_params(committed_len) {
        return Err(ImplementedCircuitProofError::ProximityOpeningRejected);
    }
    let opened_rows = systematic_opening_row_count(bundle.params, &bundle.openings)?;
    if committed_len > opened_rows * bundle.params.row_len {
        return Err(ImplementedCircuitProofError::Ligero(
            LigeroError::WrongPointLength,
        ));
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

    let start = Instant::now();
    for opening in &bundle.openings {
        if !verify_column(bundle.root, opening)
            .map_err(|err| ImplementedCircuitProofError::Ligero(LigeroError::Merkle(err)))?
        {
            return Err(ImplementedCircuitProofError::InputClaimOpeningRejected);
        }
    }
    let opened_values = systematic_opened_values(bundle.params, &bundle.openings)?;
    profile.systematic_reconstruct = start.elapsed();

    let mut all_claims = Vec::with_capacity(inputs.len());
    for (signature_index, (input, (witness_offset, layouts))) in
        inputs.iter().zip(signature_layouts).enumerate()
    {
        let opened_witness_values = opened_values
            .get(witness_offset..witness_offset + LAYOUT_LEN)
            .ok_or(ImplementedCircuitProofError::InputClaimOpeningRejected)?
            .to_vec();
        let opened_witness = Witness {
            values: opened_witness_values,
        };
        let expected_instances = implemented_circuit_instances(input, &opened_witness)
            .map_err(ImplementedCircuitProofError::Witness)?;
        let mut verified_claims = Vec::with_capacity(circuits.len());
        let mut u_scalars_from_c3 = None;
        let mut u_scalars_from_c6 = None;
        let mut accumulator_endpoints_from_c9_c10 = None;
        let mut add_inputs_from_c11 = None;
        let mut denom_inv_from_c11 = None;
        let mut final_from_c11 = None;
        let mut c12_boundaries = None;
        let mut c13_boundary_values = None;
        let mut rx_from_c14 = None;
        for (family_index, (((instance, expected), layout), entry)) in circuits
            .iter()
            .zip(&expected_instances)
            .zip(&layouts)
            .zip(
                &bundle.entries
                    [signature_index * circuits.len()..(signature_index + 1) * circuits.len()],
            )
            .enumerate()
        {
            debug_assert_eq!(instance.label, expected.label);
            let mut channel =
                CoprocessorChannel::from_seed(transcript_seed, COPROCESSOR_TRANSCRIPT_DOMAIN);
            mix_bundle_signature_index(signature_index, &mut channel);
            channel.mix_bytes(instance.label);
            mix_ecdsa_statement(input, &mut channel)
                .map_err(ImplementedCircuitProofError::Witness)?;
            let start = Instant::now();
            let claims = verify_circuit(&instance.circuit, &entry.proof, bundle.root, &mut channel)
                .map_err(ImplementedCircuitProofError::Sumcheck)?;
            let elapsed = start.elapsed();
            profile.sumcheck += elapsed;
            profile.sumcheck_by_family[family_index] += elapsed;

            let values = expected.input.as_slice();
            let committed_pads = opened_values
                .get(layout.pad_offset..layout.pad_offset + layout.pad_len)
                .ok_or(ImplementedCircuitProofError::InputClaimOpeningRejected)?;
            let start = Instant::now();
            if !verify_input_claims_from_values(values, &claims)? {
                return Err(ImplementedCircuitProofError::InputClaimOpeningRejected);
            }
            profile.input_claims += start.elapsed();

            let start = Instant::now();
            verify_committed_otp_pads(&instance.circuit, &entry.proof, committed_pads)?;
            if family_index == 0 {
                verify_c1_caller_input_binding(input, values)?;
            }
            match instance.label {
                b"s4-ecdsa-c2-canonicality" => {
                    verify_c2_caller_input_binding(input, values)?;
                }
                b"s4-ecdsa-c3-c5-scalar-setup" => {
                    verify_c3_caller_input_binding(input, values)?;
                    u_scalars_from_c3 =
                        Some((values[C3_U1_INDEX as usize], values[C3_U2_INDEX as usize]));
                }
                b"s4-ecdsa-c6-scalar-bits" => {
                    u_scalars_from_c6 =
                        Some((values[C6_U1_INDEX as usize], values[C6_U2_INDEX as usize]));
                }
                b"s4-ecdsa-c9-c10-accumulator-on-curve" => {
                    accumulator_endpoints_from_c9_c10 = Some(c9_c10_accumulator_endpoints(values)?);
                }
                b"s4-ecdsa-c11-final-add" => {
                    add_inputs_from_c11 = Some((
                        (values[C11_AX_INDEX as usize], values[C11_AY_INDEX as usize]),
                        (values[C11_BX_INDEX as usize], values[C11_BY_INDEX as usize]),
                    ));
                    denom_inv_from_c11 = Some(values[C11_DENOM_INV_INDEX as usize]);
                    final_from_c11 =
                        Some((values[C11_RX_INDEX as usize], values[C11_RY_INDEX as usize]));
                }
                b"s4-ecdsa-c12-final-on-curve" => {
                    c12_boundaries = Some(c12_boundary_values_from_openings(values)?);
                }
                b"s4-ecdsa-c13-slope-inverses" => {
                    c13_boundary_values = Some(c13_boundary_values_from_openings(values)?);
                }
                b"s4-ecdsa-c14-c15-final-check" => {
                    let signature_r = Fp::from_bytes_be(input.r)
                        .ok_or(ImplementedCircuitProofError::InputBindingRejected)?;
                    if values[C14_SIGNATURE_R_INDEX as usize] != signature_r {
                        return Err(ImplementedCircuitProofError::InputBindingRejected);
                    }
                    rx_from_c14 = Some(values[C14_RX_INDEX as usize]);
                }
                _ => {}
            }
            profile.consistency += start.elapsed();
            verified_claims.push(claims);
        }
        let start = Instant::now();
        verify_u_scalar_cross_family(u_scalars_from_c3, u_scalars_from_c6)?;
        verify_accumulator_endpoint_cross_family(
            accumulator_endpoints_from_c9_c10,
            c12_boundaries.map(|boundaries| boundaries.raw_accumulators),
        )?;
        verify_corrected_endpoint_cross_family(
            c12_boundaries.map(|boundaries| boundaries.corrected_endpoints),
            add_inputs_from_c11,
        )?;
        verify_c13_boundary_cross_family(
            input,
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
    Ok((all_claims, profile))
}

pub fn verify_implemented_circuit_bundle_profiled(
    input: &EcdsaInput,
    bundle: &ImplementedCircuitBundle,
    transcript_seed: TranscriptSeed,
) -> Result<(Vec<InputClaims>, ImplementedCircuitVerifyProfile), ImplementedCircuitProofError> {
    let mut profile = ImplementedCircuitVerifyProfile::default();
    let setup_start = Instant::now();
    let circuits =
        implemented_circuit_verifier_instances().map_err(ImplementedCircuitProofError::Circuit)?;
    if bundle.entries.len() != circuits.len() {
        return Err(ImplementedCircuitProofError::WrongProofCount {
            expected: circuits.len(),
            actual: bundle.entries.len(),
        });
    }
    let (pad_layouts, committed_len) = verifier_bundle_pad_layouts(&circuits, LAYOUT_LEN);
    if bundle.params != implemented_circuit_ligero_params(committed_len) {
        return Err(ImplementedCircuitProofError::ProximityOpeningRejected);
    }
    let opened_rows = systematic_opening_row_count(bundle.params, &bundle.openings)?;
    if committed_len > opened_rows * bundle.params.row_len {
        return Err(ImplementedCircuitProofError::Ligero(
            LigeroError::WrongPointLength,
        ));
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

    let start = Instant::now();
    for opening in &bundle.openings {
        if !verify_column(bundle.root, opening)
            .map_err(|err| ImplementedCircuitProofError::Ligero(LigeroError::Merkle(err)))?
        {
            return Err(ImplementedCircuitProofError::InputClaimOpeningRejected);
        }
    }
    let opened_values = systematic_opened_values(bundle.params, &bundle.openings)?;
    profile.systematic_reconstruct = start.elapsed();

    let opened_witness_values = opened_values
        .get(..LAYOUT_LEN)
        .ok_or(ImplementedCircuitProofError::InputClaimOpeningRejected)?
        .to_vec();
    let opened_witness = Witness {
        values: opened_witness_values,
    };
    let expected_instances = implemented_circuit_instances(input, &opened_witness)
        .map_err(ImplementedCircuitProofError::Witness)?;
    let mut verified_claims = Vec::with_capacity(bundle.entries.len());
    let mut u_scalars_from_c3 = None;
    let mut u_scalars_from_c6 = None;
    let mut accumulator_endpoints_from_c9_c10 = None;
    let mut add_inputs_from_c11 = None;
    let mut denom_inv_from_c11 = None;
    let mut final_from_c11 = None;
    let mut c12_boundaries = None;
    let mut c13_boundary_values = None;
    let mut rx_from_c14 = None;
    for (index, (((instance, entry), expected), layout)) in circuits
        .into_iter()
        .zip(&bundle.entries)
        .zip(&expected_instances)
        .zip(&pad_layouts)
        .enumerate()
    {
        debug_assert_eq!(instance.label, expected.label);
        let mut channel =
            CoprocessorChannel::from_seed(transcript_seed, COPROCESSOR_TRANSCRIPT_DOMAIN);
        channel.mix_bytes(instance.label);
        mix_ecdsa_statement(input, &mut channel).map_err(ImplementedCircuitProofError::Witness)?;
        let start = Instant::now();
        let claims = verify_circuit(&instance.circuit, &entry.proof, bundle.root, &mut channel)
            .map_err(ImplementedCircuitProofError::Sumcheck)?;
        let elapsed = start.elapsed();
        profile.sumcheck += elapsed;
        profile.sumcheck_by_family[index] = elapsed;

        let values = expected.input.as_slice();
        let committed_pads = opened_values
            .get(layout.pad_offset..layout.pad_offset + layout.pad_len)
            .ok_or(ImplementedCircuitProofError::InputClaimOpeningRejected)?;
        let start = Instant::now();
        if !verify_input_claims_from_values(values, &claims)? {
            return Err(ImplementedCircuitProofError::InputClaimOpeningRejected);
        }
        profile.input_claims += start.elapsed();

        let start = Instant::now();
        verify_committed_otp_pads(&instance.circuit, &entry.proof, committed_pads)?;
        if index == 0 {
            verify_c1_caller_input_binding(input, values)?;
        }
        match instance.label {
            b"s4-ecdsa-c2-canonicality" => {
                verify_c2_caller_input_binding(input, &values)?;
            }
            b"s4-ecdsa-c3-c5-scalar-setup" => {
                verify_c3_caller_input_binding(input, &values)?;
                u_scalars_from_c3 =
                    Some((values[C3_U1_INDEX as usize], values[C3_U2_INDEX as usize]));
            }
            b"s4-ecdsa-c6-scalar-bits" => {
                u_scalars_from_c6 =
                    Some((values[C6_U1_INDEX as usize], values[C6_U2_INDEX as usize]));
            }
            b"s4-ecdsa-c9-c10-accumulator-on-curve" => {
                accumulator_endpoints_from_c9_c10 = Some(c9_c10_accumulator_endpoints(&values)?);
            }
            b"s4-ecdsa-c11-final-add" => {
                add_inputs_from_c11 = Some((
                    (values[C11_AX_INDEX as usize], values[C11_AY_INDEX as usize]),
                    (values[C11_BX_INDEX as usize], values[C11_BY_INDEX as usize]),
                ));
                denom_inv_from_c11 = Some(values[C11_DENOM_INV_INDEX as usize]);
                final_from_c11 =
                    Some((values[C11_RX_INDEX as usize], values[C11_RY_INDEX as usize]));
            }
            b"s4-ecdsa-c12-final-on-curve" => {
                c12_boundaries = Some(c12_boundary_values_from_openings(&values)?);
            }
            b"s4-ecdsa-c13-slope-inverses" => {
                c13_boundary_values = Some(c13_boundary_values_from_openings(&values)?);
            }
            b"s4-ecdsa-c14-c15-final-check" => {
                let signature_r = Fp::from_bytes_be(input.r)
                    .ok_or(ImplementedCircuitProofError::InputBindingRejected)?;
                if values[C14_SIGNATURE_R_INDEX as usize] != signature_r {
                    return Err(ImplementedCircuitProofError::InputBindingRejected);
                }
                rx_from_c14 = Some(values[C14_RX_INDEX as usize]);
            }
            _ => {}
        }
        profile.consistency += start.elapsed();
        verified_claims.push(claims);
    }
    let start = Instant::now();
    verify_u_scalar_cross_family(u_scalars_from_c3, u_scalars_from_c6)?;
    verify_accumulator_endpoint_cross_family(
        accumulator_endpoints_from_c9_c10,
        c12_boundaries.map(|boundaries| boundaries.raw_accumulators),
    )?;
    verify_corrected_endpoint_cross_family(
        c12_boundaries.map(|boundaries| boundaries.corrected_endpoints),
        add_inputs_from_c11,
    )?;
    verify_c13_boundary_cross_family(
        input,
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
    Ok((verified_claims, profile))
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

fn verify_input_claims_from_values(
    values: &[Fp],
    claims: &InputClaims,
) -> Result<bool, ImplementedCircuitProofError> {
    let mle = Mle::new(values.to_vec());
    for (point, value) in claims.points.iter().zip(claims.values) {
        if point.len() != mle.num_vars() {
            return Err(ImplementedCircuitProofError::Ligero(
                LigeroError::WrongPointLength,
            ));
        }
        if mle
            .eval_at(point)
            .map_err(|err| ImplementedCircuitProofError::Ligero(LigeroError::Mle(err)))?
            != value
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn verify_accumulator_endpoint_cross_family(
    c9_c10: Option<((Fp, Fp), (Fp, Fp))>,
    c12: Option<((Fp, Fp), (Fp, Fp))>,
) -> Result<(), ImplementedCircuitProofError> {
    let (Some(c9_c10), Some(c12)) = (c9_c10, c12) else {
        return Err(ImplementedCircuitProofError::CrossFamilyBindingRejected);
    };
    if c9_c10 != c12 {
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
    raw_accumulators: ((Fp, Fp), (Fp, Fp)),
    corrected_endpoints: ((Fp, Fp), (Fp, Fp)),
    final_point: (Fp, Fp),
}

fn verify_c13_boundary_cross_family(
    _input: &EcdsaInput,
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

fn c9_c10_accumulator_endpoints(
    values: &[Fp],
) -> Result<((Fp, Fp), (Fp, Fp)), ImplementedCircuitProofError> {
    let u1 = c9_c10_point(values, C9_C10_ACCUMULATOR_POINTS_PER_SCALAR - 1)?;
    let u2 = c9_c10_point(values, C9_C10_ACCUMULATOR_POINT_COUNT - 1)?;
    Ok((u1, u2))
}

fn c12_boundary_values_from_openings(
    values: &[Fp],
) -> Result<C12BoundaryValues, ImplementedCircuitProofError> {
    Ok(C12BoundaryValues {
        raw_accumulators: (
            c12_point(values, C9_C10_ACCUMULATOR_POINTS_PER_SCALAR - 1)?,
            c12_point(values, C9_C10_ACCUMULATOR_POINT_COUNT - 1)?,
        ),
        corrected_endpoints: (
            c12_point(values, C12_ACCUMULATOR_POINT_COUNT)?,
            c12_point(values, C12_ACCUMULATOR_POINT_COUNT + 1)?,
        ),
        final_point: c12_point(values, C12_FINAL_POINT_INDEX)?,
    })
}

fn c13_boundary_values_from_openings(
    values: &[Fp],
) -> Result<C13BoundaryValues, ImplementedCircuitProofError> {
    Ok(C13BoundaryValues {
        final_add_denominator: c13_denominator(values, C13_FINAL_ADD_DENOM_INDEX)?,
        final_add_inverse: c13_inverse(values, C13_FINAL_ADD_DENOM_INDEX)?,
    })
}

fn c13_denominator(values: &[Fp], index: usize) -> Result<Fp, ImplementedCircuitProofError> {
    values
        .get(C13_DENOMS_START_INDEX as usize + index)
        .copied()
        .ok_or(ImplementedCircuitProofError::InputClaimOpeningRejected)
}

fn c13_inverse(values: &[Fp], index: usize) -> Result<Fp, ImplementedCircuitProofError> {
    values
        .get(C13_INVS_START_INDEX as usize + index)
        .copied()
        .ok_or(ImplementedCircuitProofError::InputClaimOpeningRejected)
}

fn c9_c10_point(
    values: &[Fp],
    point_index: usize,
) -> Result<(Fp, Fp), ImplementedCircuitProofError> {
    let x = C9_C10_POINTS_START_INDEX as usize + point_index * 3;
    let y = x + 1;
    match (values.get(x), values.get(y)) {
        (Some(&x), Some(&y)) => Ok((x, y)),
        _ => Err(ImplementedCircuitProofError::InputClaimOpeningRejected),
    }
}

fn c12_point(values: &[Fp], point_index: usize) -> Result<(Fp, Fp), ImplementedCircuitProofError> {
    let x = C12_POINTS_START_INDEX as usize + point_index * 3;
    let y = x + 1;
    match (values.get(x), values.get(y)) {
        (Some(&x), Some(&y)) => Ok((x, y)),
        _ => Err(ImplementedCircuitProofError::InputClaimOpeningRejected),
    }
}

fn verify_c2_caller_input_binding(
    input: &EcdsaInput,
    values: &[Fp],
) -> Result<(), ImplementedCircuitProofError> {
    let expected = [
        (C2_R_INDEX as usize, input.r),
        (C2_S_INDEX as usize, input.s),
        (C2_QX_INDEX as usize, input.qx),
        (C2_QY_INDEX as usize, input.qy),
    ];
    for (index, bytes) in expected {
        let expected_value =
            Fp::from_bytes_be(bytes).ok_or(ImplementedCircuitProofError::InputBindingRejected)?;
        if values.get(index) != Some(&expected_value) {
            return Err(ImplementedCircuitProofError::InputBindingRejected);
        }
    }
    Ok(())
}

fn verify_c3_caller_input_binding(
    input: &EcdsaInput,
    values: &[Fp],
) -> Result<(), ImplementedCircuitProofError> {
    let expected = [
        (C3_Z_INDEX as usize, input.z),
        (C3_R_INDEX as usize, input.r),
        (C3_S_INDEX as usize, input.s),
    ];
    for (index, bytes) in expected {
        let expected_value =
            Fp::from_bytes_be(bytes).ok_or(ImplementedCircuitProofError::InputBindingRejected)?;
        if values.get(index) != Some(&expected_value) {
            return Err(ImplementedCircuitProofError::InputBindingRejected);
        }
    }
    Ok(())
}

fn verify_c1_caller_input_binding(
    input: &EcdsaInput,
    values: &[Fp],
) -> Result<(), ImplementedCircuitProofError> {
    let expected = [
        Fp::from_bytes_be(input.z).ok_or(ImplementedCircuitProofError::InputBindingRejected)?,
        Fp::from_bytes_be(input.r).ok_or(ImplementedCircuitProofError::InputBindingRejected)?,
        Fp::from_bytes_be(input.s).ok_or(ImplementedCircuitProofError::InputBindingRejected)?,
        Fp::from_bytes_be(input.qx).ok_or(ImplementedCircuitProofError::InputBindingRejected)?,
        Fp::from_bytes_be(input.qy).ok_or(ImplementedCircuitProofError::InputBindingRejected)?,
    ];
    for (offset, expected_value) in expected.into_iter().enumerate() {
        if values.get(C1_VALUES_START_INDEX as usize + offset) != Some(&expected_value) {
            return Err(ImplementedCircuitProofError::InputBindingRejected);
        }
    }
    Ok(())
}

fn verify_committed_otp_pads(
    circuit: &Circuit,
    proof: &CircuitSumcheckProof,
    committed_pads: &[Fp],
) -> Result<(), ImplementedCircuitProofError> {
    let proof_pads = proof_otp_pad_values(proof);
    let expected_pads = circuit_otp_pad_values(circuit);
    if proof_pads != expected_pads {
        return Err(ImplementedCircuitProofError::InputClaimOpeningRejected);
    }
    if committed_pads != proof_pads.as_slice() {
        return Err(ImplementedCircuitProofError::InputClaimOpeningRejected);
    }
    Ok(())
}

fn systematic_opened_values(
    params: LigeroParams,
    openings: &[ColumnOpening],
) -> Result<Vec<Fp>, ImplementedCircuitProofError> {
    let rows = systematic_opening_row_count(params, openings)?;
    let mut sorted = openings.to_vec();
    sorted.sort_by_key(|opening| opening.index);

    let mut values = Vec::with_capacity(rows * params.row_len);
    for row in 0..rows {
        for opening in &sorted {
            values.push(opening.column[row]);
        }
    }
    Ok(values)
}

fn systematic_opening_row_count(
    params: LigeroParams,
    openings: &[ColumnOpening],
) -> Result<usize, ImplementedCircuitProofError> {
    if openings.len() != params.row_len {
        return Err(ImplementedCircuitProofError::Ligero(
            LigeroError::WrongOpeningCount,
        ));
    }
    let mut sorted = openings.to_vec();
    sorted.sort_by_key(|opening| opening.index);
    for (expected, opening) in sorted.iter().enumerate() {
        if opening.index != expected {
            return Err(ImplementedCircuitProofError::Ligero(
                LigeroError::ColumnOutOfRange,
            ));
        }
    }

    let rows = sorted.first().map(|opening| opening.column.len()).ok_or(
        ImplementedCircuitProofError::Ligero(LigeroError::WrongOpeningCount),
    )?;
    if sorted.iter().any(|opening| opening.column.len() != rows) {
        return Err(ImplementedCircuitProofError::Ligero(
            LigeroError::WrongGammaLength,
        ));
    }
    Ok(rows)
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
        if !indices.contains(&index) {
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

fn mix_bundle_signature_index(signature_index: usize, channel: &mut CoprocessorChannel) {
    channel.mix_bytes(b"s4-ecdsa-bundle-signature-index");
    channel.mix_bytes(&(signature_index as u64).to_be_bytes());
}

pub fn implemented_circuit_gate_count() -> Result<usize, CircuitError> {
    Ok([
        build_c1_input_limbs_circuit()?,
        build_c2_canonicality_circuit()?,
        build_c3_c5_scalar_setup_circuit()?,
        build_c6_scalar_bits_circuit()?,
        build_c9_c10_accumulator_on_curve_circuit()?,
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
    let params = v1_ligero_params();
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
struct BundleCircuitLayout {
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
        let pad_len = circuit_otp_pad_values(&instance.circuit).len();
        layouts.push(BundleCircuitLayout {
            pad_offset: offset,
            pad_len,
        });
        offset += pad_len;
    }
    (layouts, offset)
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
        ProverCircuitInstance {
            label: b"s4-ecdsa-c9-c10-accumulator-on-curve",
            slot: LayoutSlot::U1GAccumulators,
            circuit: build_c9_c10_accumulator_on_curve_circuit()
                .expect("static C9/C10 circuit is valid"),
            input: c9_c10_accumulator_on_curve_input(witness)?,
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
            label: b"s4-ecdsa-c9-c10-accumulator-on-curve",
            circuit: build_c9_c10_accumulator_on_curve_circuit()?,
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

pub fn build_c9_c10_accumulator_on_curve_circuit() -> Result<Circuit, CircuitError> {
    let b = Fp::from_bytes_be(P256_B_BE).expect("P-256 b is canonical");
    let mut terms = Vec::with_capacity(C9_C10_ACCUMULATOR_POINT_COUNT * 7);
    for point in 0..C9_C10_ACCUMULATOR_POINT_COUNT as u32 {
        let x = C9_C10_POINTS_START_INDEX + point * 3;
        let y = x + 1;
        let x2 = x + 2;
        let out_x2 = point * 2;
        let out_curve = out_x2 + 1;

        terms.push(QuadTerm {
            out: out_x2,
            l: x2,
            r: C9_C10_CONST_ONE_INDEX,
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
            r: C9_C10_CONST_ONE_INDEX,
            coeff: Fp::from_u64(3),
        });
        terms.push(QuadTerm {
            out: out_curve,
            l: C9_C10_CONST_ONE_INDEX,
            r: C9_C10_CONST_ONE_INDEX,
            coeff: -b,
        });
    }

    Circuit::new(vec![Layer::new(
        C9_C10_ACCUMULATOR_ON_CURVE_OUTPUT_LOG_SIZE,
        C9_C10_ACCUMULATOR_ON_CURVE_INPUT_LOG_SIZE,
        terms,
    )?])
}

pub fn c9_c10_accumulator_on_curve_input(witness: &Witness) -> Result<Vec<Fp>, WitnessError> {
    if witness.values.len() != LAYOUT_LEN {
        return Err(WitnessError::LayoutMismatch);
    }
    let mut input = vec![Fp::ZERO; 1usize << C9_C10_ACCUMULATOR_ON_CURVE_INPUT_LOG_SIZE];
    input[C9_C10_CONST_ONE_INDEX as usize] = Fp::ONE;

    let mut cursor = C9_C10_POINTS_START_INDEX as usize;
    for slot in [LayoutSlot::U1GAccumulators, LayoutSlot::U2QAccumulators] {
        for point in witness.values[layout_range(slot)].chunks_exact(2) {
            input[cursor] = point[0];
            input[cursor + 1] = point[1];
            input[cursor + 2] = point[0].square();
            cursor += 3;
        }
    }
    debug_assert_eq!(
        cursor,
        C9_C10_POINTS_START_INDEX as usize + C9_C10_ACCUMULATOR_POINT_COUNT * 3
    );
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

fn mix_ecdsa_statement(
    input: &EcdsaInput,
    channel: &mut CoprocessorChannel,
) -> Result<(), WitnessError> {
    for segment in ecdsa_statement_transcript_segments(input)? {
        channel.mix_bytes(&segment);
    }
    Ok(())
}

pub fn ecdsa_statement_transcript_segments(
    input: &EcdsaInput,
) -> Result<Vec<Vec<u8>>, WitnessError> {
    let mut segments = Vec::with_capacity(15);
    segments.push(b"s4-ecdsa-public-statement-v1".to_vec());
    for bytes in [input.z, input.r, input.s, input.qx, input.qy] {
        segments.push(bytes.to_vec());
    }

    push_blind_statement_point_segments(&mut segments, 0, ProjectivePoint::GENERATOR)?;
    let public_key = parse_public_key(input.qx, input.qy)?;
    push_blind_statement_point_segments(&mut segments, 0, ProjectivePoint::from(public_key))?;
    Ok(segments)
}

fn push_blind_statement_point_segments(
    segments: &mut Vec<Vec<u8>>,
    blind_index: u64,
    base: ProjectivePoint,
) -> Result<(), WitnessError> {
    segments.push(blind_index.to_be_bytes().to_vec());
    let (bx, by) = projective_point_coords(base)?;
    let (dx, dy) = projective_point_coords(double_256(base))?;
    for value in [bx, by, dx, dy] {
        segments.push(value.to_bytes_be().to_vec());
    }
    Ok(())
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
