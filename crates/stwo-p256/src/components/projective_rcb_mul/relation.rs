//! Lookup relations for the projective RCB multiplication AIR family.
//!
//! Split out of `mod.rs` (pure relocation, no behavioral change).

use stwo::core::{
    air::Component,
    channel::Channel,
    fields::{m31::M31, qm31::SecureField},
    pcs::{CommitmentSchemeVerifier, PcsConfig, TreeVec},
    poly::circle::CanonicCoset,
    proof::StarkProof,
    utils::{bit_reverse_index, coset_index_to_circle_domain_index},
    verifier::verify,
    ColumnVec,
};
use stwo::prover::backend::simd::{
    m31::{LOG_N_LANES, N_LANES},
    qm31::PackedQM31,
    SimdBackend,
};
use stwo::prover::backend::BackendForChannel;
use stwo::prover::poly::circle::PolyOps;
use stwo::prover::{prove, CommitmentSchemeProver, ComponentProver};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator,
};
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};
use stwo_p256_utils::solinas::REDUCTION_MATRIX;

use crate::constants::{P256_B, P256_MODULUS};
use crate::field_ops::{add_mod_witness, sub_mod_witness};
use crate::fp_solinas::{
    FpSolinasError, FpSolinasMulTrace, FP_SOLINAS_LIMB_BASE, FP_SOLINAS_RAW_LIMBS,
    M31_CENTERED_BOUND,
};
use crate::fp_solinas_air::{
    add_fp_solinas_reduction_digit, FpSolinasReductionDigitColumns, FpSolinasReductionRelations,
    FpSolinasReductionTraceClaim, FpSolinasReductionTraceError,
    FP_SOLINAS_CORRECTION_PRODUCT_MAX_ABS_DIGIT, FP_SOLINAS_REDUCTION_DIGITS,
    FP_SOLINAS_REDUCTION_DIGIT_TRACE_COLUMNS,
};
use crate::limbs::{EvalP256BigIntExt, P256EvalBigInt};
use crate::prepared_table::PreparedAffinePoint;
use crate::projective::{
    ProjectiveEcError, ProjectiveEcOp, ProjectiveEcRow, ProjectiveEcTraceClaim, ProjectivePoint,
};
use crate::range_checks::{
    add_range_check, RangeCheckClaim, RangeCheckComponent, RangeCheckEval,
    RangeCheckInteractionClaim, RangeCheckRelation, SignedCarryRangeClaim,
    SignedCarryRangeComponent, SignedCarryRangeEval, RANGE13_BITS,
};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};
use crate::types::U256;
use super::*;

pub const PROJECTIVE_RCB_MUL_LIMB_RELATION_ARITY: usize = 5;

pub const PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGIT_RELATION_ARITY: usize = 6;

pub const PROJECTIVE_RCB_FOLDED_CONTRIBUTION_RELATION_ARITY: usize = 5;

pub const PROJECTIVE_RCB_FOLDED_DIGIT_RELATION_ARITY: usize = 4;

pub const PROJECTIVE_RCB_FOLDED_CARRY_RELATION_ARITY: usize = 4;

relation!(
    ProjectiveRcbMulLimbRelation,
    PROJECTIVE_RCB_MUL_LIMB_RELATION_ARITY
);

relation!(
    ProjectiveRcbRawProductChunkDigitRelation,
    PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGIT_RELATION_ARITY
);

relation!(
    ProjectiveRcbFoldedContributionRelation,
    PROJECTIVE_RCB_FOLDED_CONTRIBUTION_RELATION_ARITY
);

relation!(
    ProjectiveRcbFoldedDigitRelation,
    PROJECTIVE_RCB_FOLDED_DIGIT_RELATION_ARITY
);

relation!(
    ProjectiveRcbFoldedCarryRelation,
    PROJECTIVE_RCB_FOLDED_CARRY_RELATION_ARITY
);

#[derive(Clone, Debug)]
pub struct ProjectiveRcbMulComponentRelations {
    pub range13: RangeCheckRelation,
    pub signed_carry: RangeCheckRelation,
    pub mul_limb: ProjectiveRcbMulLimbRelation,
    pub raw_product_chunk_digit: ProjectiveRcbRawProductChunkDigitRelation,
    pub folded_contribution: ProjectiveRcbFoldedContributionRelation,
    pub folded_digit: ProjectiveRcbFoldedDigitRelation,
    pub folded_carry: ProjectiveRcbFoldedCarryRelation,
}

impl ProjectiveRcbMulComponentRelations {
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            range13: RangeCheckRelation::draw(channel),
            signed_carry: RangeCheckRelation::draw(channel),
            mul_limb: ProjectiveRcbMulLimbRelation::draw(channel),
            raw_product_chunk_digit: ProjectiveRcbRawProductChunkDigitRelation::draw(channel),
            folded_contribution: ProjectiveRcbFoldedContributionRelation::draw(channel),
            folded_digit: ProjectiveRcbFoldedDigitRelation::draw(channel),
            folded_carry: ProjectiveRcbFoldedCarryRelation::draw(channel),
        }
    }

    pub fn dummy() -> Self {
        Self {
            range13: RangeCheckRelation::dummy(),
            signed_carry: RangeCheckRelation::dummy(),
            mul_limb: ProjectiveRcbMulLimbRelation::dummy(),
            raw_product_chunk_digit: ProjectiveRcbRawProductChunkDigitRelation::dummy(),
            folded_contribution: ProjectiveRcbFoldedContributionRelation::dummy(),
            folded_digit: ProjectiveRcbFoldedDigitRelation::dummy(),
            folded_carry: ProjectiveRcbFoldedCarryRelation::dummy(),
        }
    }

    pub fn as_refs(&self) -> ProjectiveRcbMulRelations<'_> {
        ProjectiveRcbMulRelations {
            range13: &self.range13,
            signed_carry: &self.signed_carry,
            mul_limb: &self.mul_limb,
            raw_product_chunk_digit: &self.raw_product_chunk_digit,
            folded_contribution: &self.folded_contribution,
            folded_digit: &self.folded_digit,
            folded_carry: &self.folded_carry,
        }
    }
}

#[derive(Clone, Copy)]
pub struct ProjectiveRcbMulRelations<'a> {
    pub range13: &'a RangeCheckRelation,
    pub signed_carry: &'a RangeCheckRelation,
    pub mul_limb: &'a ProjectiveRcbMulLimbRelation,
    pub raw_product_chunk_digit: &'a ProjectiveRcbRawProductChunkDigitRelation,
    pub folded_contribution: &'a ProjectiveRcbFoldedContributionRelation,
    pub folded_digit: &'a ProjectiveRcbFoldedDigitRelation,
    pub folded_carry: &'a ProjectiveRcbFoldedCarryRelation,
}
