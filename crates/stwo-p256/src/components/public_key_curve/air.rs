//! Standalone provable + verifiable slice proving that a P-256 public key
//! `(x, y)` lies on the curve, i.e. `y^2 = x^3 - 3x + b (mod p)`.
//!
//! # What this proves
//!
//! Given a P-256 public key `(x, y)` (with `x, y` canonical, `< p`), the slice
//! proves the affine short-Weierstrass identity
//!
//! ```text
//! y^2 + 3x ≡ x^3 + b   (mod p)
//! ```
//!
//! using four modular multiplications proven by the *exact* `projective_air`
//! mod-`p` mul machinery (the same Solinas raw-product / matrix-fold /
//! reduction families used by the projective EC double/add AIR), plus one
//! mod-`p` limb-reduction identity that ties the four mul results together.
//!
//! # Architecture
//!
//! The four multiplications are laid out as a single-source [`ProjectiveRcbAirTraceClaim`]
//! row carrying four [`ProjectiveRcbMulRow`]s:
//!
//! | `mul_index` | computes        | result    |
//! |-------------|-----------------|-----------|
//! | 0           | `y * y`         | `y2`      |
//! | 1           | `x * x`         | `x2`      |
//! | 2           | `x2 * x`        | `x3`      |
//! | 3           | `3 * x`         | `three_x` |
//!
//! The three non-mul families (`raw_product_chunk`, `folded_contribution`,
//! `folded_digit`) and the two shared range providers (`range13`,
//! `signed_carry`) are reused **unchanged** from `projective_air`. Only the
//! mul family swaps in [`PublicKeyMulEval`], which proves each mul exactly as
//! [`ProjectiveRcbMulEval`] does and then *provides* (yields, multiplicity
//! `-active`) one [`PublicKeyMulResultRelation`] tuple per limb for the lhs,
//! rhs and result of that mul.
//!
//! A dedicated [`PublicKeyCurveCheckEval`] component holds the native witness
//! `x, y, x2, x3, three_x, y2` and:
//!
//! * *consumes* (uses, multiplicity `+active`) the mul provider tuples using
//!   its own witnessed limb columns as the looked-up value. LogUp balance then
//!   forces every witnessed column to equal the corresponding proven mul
//!   operand/result (mul 3's lhs is consumed as the fixed constant `3`).
//! * enforces the curve identity `(y2 + three_x) - (x3 + b) - q·p = 0` with a
//!   13-bit-limb signed-carry recurrence, boolean-ish quotient `q ∈ {-1,0,1}`
//!   and final carry `0`.
//!
//! For this standalone slice `x, y` are witnessed and checked internally
//! consistent. When wired into the monolithic proof, `x, y` would additionally
//! be bound to `PublicEcdsaInstanceRelation` (the public-key columns), exactly
//! as `scalar/setup_air.rs` binds its public instance.

use serde::{Deserialize, Serialize};
use stwo::core::{
    air::Component,
    channel::Channel,
    fields::{m31::M31, qm31::SecureField},
    utils::{bit_reverse_index, coset_index_to_circle_domain_index},
    ColumnVec,
};
use stwo::prover::backend::simd::{
    m31::{LOG_N_LANES, N_LANES},
    qm31::PackedQM31,
    SimdBackend,
};
use stwo::prover::ComponentProver;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator,
};
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};

use crate::components::gamma_digest::{
    gamma_digest_of_values, gamma_digest_tuple, gen_gamma_tall_base_trace,
    gen_gamma_tall_interaction_trace, gen_gamma_tall_preprocessed_trace, yield_gamma_digest,
    GammaChallenge, GammaDigestRelation, GammaTallComponent, GammaTallEval, GammaTallInstance,
    GammaTallInteractionClaim, GammaTallLayout, GAMMA_TAG_PKC_RANGE13, GAMMA_TAG_PKC_SIGNED,
};
use crate::constants::{P256_B, P256_MODULUS};
use crate::limbs::{EvalP256BigIntExt, P256EvalBigInt, P256M31BigInt};
use crate::projective::{ProjectiveEcOp, ProjectivePoint};
use crate::projective_air::{
    projective_rcb_signed_carry_bound, projective_rcb_signed_carry_log_size, ProjectiveRcbAirError,
    ProjectiveRcbAirRow, ProjectiveRcbAirTraceClaim, ProjectiveRcbMulResultRelation,
    ProjectiveRcbMulRow, ProjectiveRcbMulStep, PROJECTIVE_RCB_MUL_ROLE_LHS,
    PROJECTIVE_RCB_MUL_ROLE_RESULT, PROJECTIVE_RCB_MUL_ROLE_RHS,
    PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
};
use crate::public_inputs::PublicEcdsaInputClaim;
use crate::public_key_check::{PublicKeyOnCurveClaim, PublicKeyOnCurveError};
use crate::range_checks::{
    encode_signed_carry, range_check_value_column_id, signed_carry_active_column_id,
    signed_carry_value_column_id, RangeCheckClaim, RangeCheckComponent, RangeCheckEval,
    RangeCheckInteractionClaim, RangeCheckRelation, SignedCarryRangeClaim,
    SignedCarryRangeComponent, SignedCarryRangeEval, RANGE13_BITS,
};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};
use crate::types::U256;

/// Number of mul rows in a single public-key curve check (`y^2`, `x^2`,
/// `x^3`, `3x`).
pub const PUBLIC_KEY_MUL_COUNT: usize = 4;

/// Arity of [`PublicKeyMulResultRelation`]: `[mul_index, role, limb_index, limb]`.
pub const PUBLIC_KEY_MUL_RESULT_ARITY: usize = 4;

/// Arity of [`PublicKeyPointRelation`]: `[sig_id, x_limbs.., y_limbs..]`.
///
/// This is the binding tuple. The scalar-setup component *provides* it from the
/// public-key columns (`pub_x`, `pub_y`) that are themselves bound to the public
/// ECDSA instance; the curve-check component *consumes* it with its witnessed
/// `(sig_id, x, y)`. LogUp balance then forces the curve-checked `(x, y)` to
/// equal the verifier's public key for the matching `sig_id`.
pub const PUBLIC_KEY_POINT_ARITY: usize = 1 + 2 * N_LIMBS;

/// Roles inside [`PublicKeyMulResultRelation`] (re-export the mul-family role
/// constants so producers and consumers cannot drift).
pub const ROLE_LHS: u32 = PROJECTIVE_RCB_MUL_ROLE_LHS;
pub const ROLE_RHS: u32 = PROJECTIVE_RCB_MUL_ROLE_RHS;
pub const ROLE_RESULT: u32 = PROJECTIVE_RCB_MUL_ROLE_RESULT;

/// `mul_index` of each multiplication.
const MUL_Y_SQUARED: u32 = 0;
const MUL_X_SQUARED: u32 = 1;
const MUL_X_CUBED: u32 = 2;
const MUL_THREE_X: u32 = 3;

/// Quotient witness `q` for the curve identity lives in `{-1, 0, 1}`.
///
/// `y2 + three_x ∈ [0, 2p-2]` and `x3 + b ∈ [0, 2p-2]`, so their difference
/// lies in `[-(2p-2), 2p-2]`; being an exact integer multiple of `p` it equals
/// `q·p` with `q ∈ {-1, 0, 1}` (verified in `curve_identity_quotient_in_range`).
const CURVE_QUOTIENT_BOUND: i64 = 1;

/// The base-trace column layout of the curve-check component, in
/// `next_trace_mask` order. Keep this list and [`PublicKeyCurveCheckColumns::read`]
/// in lockstep with [`gen_curve_check_base_trace`].
const CURVE_CHECK_TRACE_COLUMNS: usize = 1            // active
    + 1                                               // sig_id (binding)
    + N_LIMBS                                         // x
    + N_LIMBS                                         // y
    + N_LIMBS                                         // x2
    + N_LIMBS                                         // x3
    + N_LIMBS                                         // three_x
    + N_LIMBS                                         // y2
    + 1                                               // q (signed)
    + N_LIMBS                                         // carries (signed)
    + 1                                               // q_pos (q == 1)
    + 1; // q_neg (q == -1)

relation!(PublicKeyPointRelation, PUBLIC_KEY_POINT_ARITY);

// ---------------------------------------------------------------------------
// Native claim
// ---------------------------------------------------------------------------

/// Fully checked native witness for the standalone public-key curve slice.
#[derive(Clone, Debug)]
pub struct PublicKeyCurveSliceClaim {
    /// The four mod-`p` multiplications, expressed through the shared
    /// `projective_air` mul machinery (one source row, four mul rows).
    pub mul_trace: ProjectiveRcbAirTraceClaim,
    /// First hinted-mul `source_index` reserved for this claim's four muls.
    pub hinted_source_offset: u32,
    /// Signature/public-key identifier. Binds the curve-checked `(x, y)` to the
    /// public ECDSA instance of the same `sig_id` via [`PublicKeyPointRelation`].
    pub sig_id: M31,
    /// Canonical `x` limbs.
    pub x: P256M31BigInt,
    /// Canonical `y` limbs.
    pub y: P256M31BigInt,
    /// `x^2 mod p`.
    pub x2: P256M31BigInt,
    /// `x^3 mod p`.
    pub x3: P256M31BigInt,
    /// `3x mod p`.
    pub three_x: P256M31BigInt,
    /// `y^2 mod p`.
    pub y2: P256M31BigInt,
    /// Curve-identity quotient `q ∈ {-1, 0, 1}`.
    pub q: i64,
    /// 13-bit-limb signed carries of the curve identity (`carries[N-1] == 0`).
    pub carries: [i64; N_LIMBS],
}

impl PublicKeyCurveSliceClaim {
    /// Build a slice claim from a fully verified [`PublicKeyOnCurveClaim`].
    ///
    /// Exactly one row is supported by this standalone slice. The native
    /// claim is re-verified so that an inconsistent or off-curve witness is
    /// rejected before any trace is generated.
    pub fn from_public_key_claim(
        claim: &PublicKeyOnCurveClaim,
        hinted_source_offset: u32,
    ) -> Result<Self, PublicKeyCurveSliceError> {
        if claim.rows.len() != 1 {
            return Err(PublicKeyCurveSliceError::UnsupportedRowCount {
                actual: claim.rows.len(),
            });
        }
        claim.verify()?;
        let row = &claim.rows[0];

        let x = row.x.to_u256();
        let y = row.y.to_u256();

        // Re-derive the four mul rows through the shared machinery so the
        // standard mul families (raw product / fold / reduction) are proven
        // exactly as in `projective_air`. `step` is a pure label and never
        // constrained.
        let mut muls = Vec::with_capacity(PUBLIC_KEY_MUL_COUNT);
        let y2 = push_mul(&mut muls, &y, &y)?;
        let x2 = push_mul(&mut muls, &x, &x)?;
        let x3 = push_mul(&mut muls, &x2, &x)?;
        let three_x = push_mul(&mut muls, &U256::from_le_u64s(&[3, 0, 0, 0]), &x)?;

        let air_row = ProjectiveRcbAirRow {
            source_index: 0,
            sig_id: M31::from_u32_unchecked(0),
            cert_id: M31::from_u32_unchecked(0),
            // `op` / `output_projective` are unused by constraint evaluation;
            // they only label projective EC rows. Dummies keep the slice
            // self-contained.
            op: ProjectiveEcOp::Double,
            output_projective: ProjectivePoint::infinity(),
            muls,
        };
        let mul_trace = ProjectiveRcbAirTraceClaim {
            rows: vec![air_row],
        };

        // Curve identity: (y2 + three_x) - (x3 + b) - q·p = 0 over 13-bit limbs.
        let modulus = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS));
        let b = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_B));
        let y2_limbs = P256M31BigInt::from_u256(&y2);
        let x2_limbs = P256M31BigInt::from_u256(&x2);
        let x3_limbs = P256M31BigInt::from_u256(&x3);
        let three_x_limbs = P256M31BigInt::from_u256(&three_x);
        let (q, carries) =
            solve_curve_identity(&y2_limbs, &three_x_limbs, &x3_limbs, &b, &modulus)?;

        let claim = Self {
            mul_trace,
            hinted_source_offset,
            sig_id: row.sig_id,
            x: row.x.clone(),
            y: row.y.clone(),
            x2: x2_limbs,
            x3: x3_limbs,
            three_x: three_x_limbs,
            y2: y2_limbs,
            q,
            carries,
        };
        claim.verify()?;
        Ok(claim)
    }

    /// Re-check the native witness: the mul trace, and the curve-identity
    /// recurrence with `q ∈ {-1,0,1}` and final carry `0`.
    pub fn verify(&self) -> Result<(), PublicKeyCurveSliceError> {
        if self.mul_trace.rows.len() != 1
            || self.mul_trace.rows[0].muls.len() != PUBLIC_KEY_MUL_COUNT
        {
            return Err(PublicKeyCurveSliceError::UnsupportedRowCount {
                actual: self.mul_trace.rows.len(),
            });
        }
        // Re-verify every mul row (raw product / fold / reduction sub-traces).
        for row in &self.mul_trace.rows {
            row.verify().map_err(PublicKeyCurveSliceError::MulTrace)?;
        }

        // The four mul results must match the witnessed copies.
        let muls = &self.mul_trace.rows[0].muls;
        require_eq("y2", &muls[MUL_Y_SQUARED as usize].trace.result, &self.y2)?;
        require_eq("x2", &muls[MUL_X_SQUARED as usize].trace.result, &self.x2)?;
        require_eq("x3", &muls[MUL_X_CUBED as usize].trace.result, &self.x3)?;
        require_eq(
            "three_x",
            &muls[MUL_THREE_X as usize].trace.result,
            &self.three_x,
        )?;
        // The mul operands must match the witnessed copies (these are exactly
        // the bindings the AIR enforces via LogUp).
        require_eq("y", &muls[MUL_Y_SQUARED as usize].trace.lhs, &self.y)?;
        require_eq("y", &muls[MUL_Y_SQUARED as usize].trace.rhs, &self.y)?;
        require_eq("x", &muls[MUL_X_SQUARED as usize].trace.lhs, &self.x)?;
        require_eq("x", &muls[MUL_X_SQUARED as usize].trace.rhs, &self.x)?;
        require_eq("x2", &muls[MUL_X_CUBED as usize].trace.lhs, &self.x2)?;
        require_eq("x", &muls[MUL_X_CUBED as usize].trace.rhs, &self.x)?;
        require_eq(
            "three",
            &muls[MUL_THREE_X as usize].trace.lhs,
            &P256M31BigInt::from_u256(&U256::from_le_u64s(&[3, 0, 0, 0])),
        )?;
        require_eq("x", &muls[MUL_THREE_X as usize].trace.rhs, &self.x)?;

        // Curve-identity recurrence.
        if !(-CURVE_QUOTIENT_BOUND..=CURVE_QUOTIENT_BOUND).contains(&self.q) {
            return Err(PublicKeyCurveSliceError::QuotientOutOfRange { q: self.q });
        }
        let modulus = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS));
        let b = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_B));
        let mut prev = 0i64;
        let base = 1i64 << LIMB_BITS;
        for i in 0..N_LIMBS {
            let combined = i64::from(self.y2.limbs()[i].0) + i64::from(self.three_x.limbs()[i].0)
                - i64::from(self.x3.limbs()[i].0)
                - i64::from(b.limbs()[i].0)
                - self.q * i64::from(modulus.limbs()[i].0);
            let value = combined + prev - base * self.carries[i];
            if value != 0 {
                return Err(PublicKeyCurveSliceError::CurveIdentityMismatch { limb: i, value });
            }
            if self.carries[i].abs() > projective_rcb_signed_carry_bound() {
                return Err(PublicKeyCurveSliceError::CarryOutOfRange {
                    limb: i,
                    carry: self.carries[i],
                });
            }
            prev = self.carries[i];
        }
        if self.carries[N_LIMBS - 1] != 0 {
            return Err(PublicKeyCurveSliceError::FinalCarryNonZero {
                carry: self.carries[N_LIMBS - 1],
            });
        }
        Ok(())
    }
}

fn push_mul(
    muls: &mut Vec<ProjectiveRcbMulRow>,
    lhs: &U256,
    rhs: &U256,
) -> Result<U256, PublicKeyCurveSliceError> {
    // `ProjectiveRcbMulStep` is a pure label; reuse one valid variant.
    let row = ProjectiveRcbMulRow::new_lite(ProjectiveRcbMulStep::DoubleX1Squared, lhs, rhs)
        .map_err(PublicKeyCurveSliceError::MulTrace)?;
    let result = row.trace.result.to_u256();
    muls.push(row);
    Ok(result)
}

fn require_eq(
    field: &'static str,
    actual: &P256M31BigInt,
    expected: &P256M31BigInt,
) -> Result<(), PublicKeyCurveSliceError> {
    if actual == expected {
        Ok(())
    } else {
        Err(PublicKeyCurveSliceError::WitnessMismatch { field })
    }
}

/// Solve `(y2 + three_x) - (x3 + b) - q·p = 0` for `q ∈ {-1,0,1}` and its
/// 13-bit-limb signed carries with final carry `0`.
fn solve_curve_identity(
    y2: &P256M31BigInt,
    three_x: &P256M31BigInt,
    x3: &P256M31BigInt,
    b: &P256M31BigInt,
    modulus: &P256M31BigInt,
) -> Result<(i64, [i64; N_LIMBS]), PublicKeyCurveSliceError> {
    for q in [-1i64, 0, 1] {
        if let Some(carries) = try_curve_carries(y2, three_x, x3, b, modulus, q) {
            return Ok((q, carries));
        }
    }
    Err(PublicKeyCurveSliceError::PointOffCurveNative)
}

fn try_curve_carries(
    y2: &P256M31BigInt,
    three_x: &P256M31BigInt,
    x3: &P256M31BigInt,
    b: &P256M31BigInt,
    modulus: &P256M31BigInt,
    q: i64,
) -> Option<[i64; N_LIMBS]> {
    let base = 1i64 << LIMB_BITS;
    let mut carries = [0i64; N_LIMBS];
    let mut prev = 0i64;
    for (i, carry) in carries.iter_mut().enumerate() {
        let combined = i64::from(y2.limbs()[i].0) + i64::from(three_x.limbs()[i].0)
            - i64::from(x3.limbs()[i].0)
            - i64::from(b.limbs()[i].0)
            - q * i64::from(modulus.limbs()[i].0);
        let total = combined + prev;
        if total % base != 0 {
            return None;
        }
        *carry = total / base;
        prev = *carry;
    }
    if carries[N_LIMBS - 1] == 0 {
        Some(carries)
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Mul family evaluator (swaps in for `ProjectiveRcbMulEval`)
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Curve-check evaluator (the four muls are proven by hinted-mul rows)
// ---------------------------------------------------------------------------

type PublicKeyCurveCheckComponent = FrameworkComponent<PublicKeyCurveCheckEval>;

struct PublicKeyCurveCheckColumns<E: EvalAtRow> {
    active: E::F,
    sig_id: E::F,
    x: P256EvalBigInt<E>,
    y: P256EvalBigInt<E>,
    x2: P256EvalBigInt<E>,
    x3: P256EvalBigInt<E>,
    three_x: P256EvalBigInt<E>,
    y2: P256EvalBigInt<E>,
    q: E::F,
    carries: [E::F; N_LIMBS],
    /// Witnessed boolean split of `q ∈ {-1, 0, 1}`: `q = q_pos − q_neg` with
    /// `q_pos, q_neg ∈ {0, 1}` mutually exclusive (lessons.md #44 idiom). The
    /// inline quartic `q·(q−1)·(q+1)` is degree 4, over the `log_size + 1`
    /// (degree-2) composition budget — a latent completeness hazard that
    /// activates once no larger component pads the global composition domain.
    q_pos: E::F,
    q_neg: E::F,
}

impl<E: EvalAtRow> PublicKeyCurveCheckColumns<E> {
    fn read(eval: &mut E) -> Self {
        Self {
            active: eval.next_trace_mask(),
            sig_id: eval.next_trace_mask(),
            x: eval.next_p256_bigint(),
            y: eval.next_p256_bigint(),
            x2: eval.next_p256_bigint(),
            x3: eval.next_p256_bigint(),
            three_x: eval.next_p256_bigint(),
            y2: eval.next_p256_bigint(),
            q: eval.next_trace_mask(),
            carries: core::array::from_fn(|_| eval.next_trace_mask()),
            q_pos: eval.next_trace_mask(),
            q_neg: eval.next_trace_mask(),
        }
    }
}

#[derive(Clone)]
struct PublicKeyCurveCheckEval {
    log_size: u32,
    mul_result: ProjectiveRcbMulResultRelation,
    /// First hinted-mul `source_index` reserved for the curve-check muls (the
    /// row's source is `hinted_source_offset + sig_id`).
    hinted_source_offset: u32,
    point_relation: PublicKeyPointRelation,
    /// When `true`, the curve-check consumes the [`PublicKeyPointRelation`]
    /// binding tuple `[sig_id, x.., y..]` (the monolithic proof, where
    /// `scalar/setup_air.rs` provides it from the public-input-bound public key).
    /// When `false` (the standalone slice), no binding tuple is emitted so the
    /// slice's interaction trace stays self-balanced.
    bind_to_public: bool,
    /// γ-digest reshape: the witnessed limbs' range13 uses and the curve
    /// identity's signed-carry uses are bound into two per-row digests; the
    /// slice's tall expanders re-expand them against the local providers.
    gamma_digest: GammaDigestRelation,
    gamma_challenge: GammaChallenge,
}

impl FrameworkEval for PublicKeyCurveCheckEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let one = E::F::from(M31::from_u32_unchecked(1));
        let columns = PublicKeyCurveCheckColumns::read(&mut eval);

        // `active` is boolean.
        eval.add_constraint(columns.active.clone() * (one.clone() - columns.active.clone()));

        // Gate all witness limbs to zero on padding rows so disabled rows can
        // never expose a usable witness.
        for limb in columns
            .x
            .limbs()
            .iter()
            .chain(columns.y.limbs())
            .chain(columns.x2.limbs())
            .chain(columns.x3.limbs())
            .chain(columns.three_x.limbs())
            .chain(columns.y2.limbs())
        {
            eval.add_constraint((one.clone() - columns.active.clone()) * limb.clone());
        }
        eval.add_constraint((one.clone() - columns.active.clone()) * columns.q.clone());
        // `sig_id` is part of the binding tuple; gate it to zero on padding rows
        // so disabled rows cannot consume a usable `PublicKeyPointRelation` tuple.
        eval.add_constraint((one.clone() - columns.active.clone()) * columns.sig_id.clone());

        // Bind the witnessed limbs to the proven mul operands/results by
        // consuming (use, `+active`) the mul provider tuples using the
        // witnessed column as the looked-up value.
        let mul_source =
            E::F::from(M31::from_u32_unchecked(self.hinted_source_offset)) + columns.sig_id.clone();
        consume_mul_limbs(
            &mut eval,
            &self.mul_result,
            &columns.active,
            &mul_source,
            MUL_Y_SQUARED,
            ROLE_LHS,
            columns.y.limbs(),
        );
        consume_mul_limbs(
            &mut eval,
            &self.mul_result,
            &columns.active,
            &mul_source,
            MUL_Y_SQUARED,
            ROLE_RHS,
            columns.y.limbs(),
        );
        consume_mul_limbs(
            &mut eval,
            &self.mul_result,
            &columns.active,
            &mul_source,
            MUL_Y_SQUARED,
            ROLE_RESULT,
            columns.y2.limbs(),
        );

        consume_mul_limbs(
            &mut eval,
            &self.mul_result,
            &columns.active,
            &mul_source,
            MUL_X_SQUARED,
            ROLE_LHS,
            columns.x.limbs(),
        );
        consume_mul_limbs(
            &mut eval,
            &self.mul_result,
            &columns.active,
            &mul_source,
            MUL_X_SQUARED,
            ROLE_RHS,
            columns.x.limbs(),
        );
        consume_mul_limbs(
            &mut eval,
            &self.mul_result,
            &columns.active,
            &mul_source,
            MUL_X_SQUARED,
            ROLE_RESULT,
            columns.x2.limbs(),
        );

        consume_mul_limbs(
            &mut eval,
            &self.mul_result,
            &columns.active,
            &mul_source,
            MUL_X_CUBED,
            ROLE_LHS,
            columns.x2.limbs(),
        );
        consume_mul_limbs(
            &mut eval,
            &self.mul_result,
            &columns.active,
            &mul_source,
            MUL_X_CUBED,
            ROLE_RHS,
            columns.x.limbs(),
        );
        consume_mul_limbs(
            &mut eval,
            &self.mul_result,
            &columns.active,
            &mul_source,
            MUL_X_CUBED,
            ROLE_RESULT,
            columns.x3.limbs(),
        );

        // mul 3 lhs is the fixed constant 3 (limb 0 = 3, rest 0).
        consume_three_constant(&mut eval, &self.mul_result, &columns.active, &mul_source);
        consume_mul_limbs(
            &mut eval,
            &self.mul_result,
            &columns.active,
            &mul_source,
            MUL_THREE_X,
            ROLE_RHS,
            columns.x.limbs(),
        );
        consume_mul_limbs(
            &mut eval,
            &self.mul_result,
            &columns.active,
            &mul_source,
            MUL_THREE_X,
            ROLE_RESULT,
            columns.three_x.limbs(),
        );

        // Bind the witnessed `(x, y)` to the verifier public key: consume (use,
        // `+active`) the `PublicKeyPointRelation` tuple `[sig_id, x.., y..]`.
        // The scalar-setup component provides exactly this tuple from its
        // public-input-bound `pub_x`/`pub_y` columns, so LogUp balance forces
        // `(x, y) == (pub_x, pub_y)` for the matching `sig_id`. Standalone (no
        // public binding) emits nothing here.
        if self.bind_to_public {
            consume_public_key_point(&mut eval, &self.point_relation, &columns);
        }

        // Collect every witnessed limb for the range13 γ-digest (self-
        // contained domain enforcement via the tall expander; also guarantees
        // the 13-bit headroom used by the identity below).
        let range13_values: Vec<E::F> = columns
            .x
            .limbs()
            .iter()
            .chain(columns.y.limbs())
            .chain(columns.x2.limbs())
            .chain(columns.x3.limbs())
            .chain(columns.three_x.limbs())
            .chain(columns.y2.limbs())
            .cloned()
            .collect();

        // Curve identity: (y2 + three_x) - (x3 + b) - q·p = 0 over 13-bit
        // limbs with a signed-carry recurrence and final carry 0; the carries
        // are collected for the signed γ-digest.
        let signed_carry_values = add_curve_identity(&mut eval, &columns);

        // γ-digest yields. The slice covers ONE signature, so the digest
        // row_index is the constant 0 (the talls' single scheduled group).
        let row_zero = E::F::from(M31::from_u32_unchecked(0));
        yield_gamma_digest(
            &mut eval,
            &self.gamma_digest,
            &self.gamma_challenge,
            GAMMA_TAG_PKC_RANGE13,
            row_zero.clone(),
            columns.active.clone(),
            M31::from_u32_unchecked(0),
            &range13_values,
        );
        yield_gamma_digest(
            &mut eval,
            &self.gamma_digest,
            &self.gamma_challenge,
            GAMMA_TAG_PKC_SIGNED,
            row_zero,
            columns.active.clone(),
            encode_signed_carry(0),
            &signed_carry_values,
        );

        eval.finalize_logup_in_pairs();
        eval
    }
}

fn consume_mul_limbs<E: EvalAtRow>(
    eval: &mut E,
    relation: &ProjectiveRcbMulResultRelation,
    active: &E::F,
    source_index: &E::F,
    mul_index: u32,
    role: u32,
    limbs: &[E::F; N_LIMBS],
) {
    let mut values = Vec::with_capacity(3 + N_LIMBS);
    values.push(source_index.clone());
    values.push(E::F::from(M31::from_u32_unchecked(mul_index)));
    values.push(E::F::from(M31::from_u32_unchecked(role)));
    values.extend(limbs.iter().cloned());
    eval.add_to_relation(RelationEntry::new(
        relation,
        E::EF::from(active.clone()),
        &values,
    ));
}

/// Consume `mul 3`'s lhs as the fixed constant `3` (limb 0 = 3, rest 0). This
/// binds the proven `3x` mul's left operand to the literal `3`.
fn consume_three_constant<E: EvalAtRow>(
    eval: &mut E,
    relation: &ProjectiveRcbMulResultRelation,
    active: &E::F,
    source_index: &E::F,
) {
    let mut values = Vec::with_capacity(3 + N_LIMBS);
    values.push(source_index.clone());
    values.push(E::F::from(M31::from_u32_unchecked(MUL_THREE_X)));
    values.push(E::F::from(M31::from_u32_unchecked(ROLE_LHS)));
    for limb_index in 0..N_LIMBS {
        let value = if limb_index == 0 { 3 } else { 0 };
        values.push(E::F::from(M31::from_u32_unchecked(value)));
    }
    eval.add_to_relation(RelationEntry::new(
        relation,
        E::EF::from(active.clone()),
        &values,
    ));
}

/// Consume the binding tuple `[sig_id, x.., y..]` (use, `+active`) on the
/// [`PublicKeyPointRelation`]. Keep the value order in lockstep with the
/// provider in `scalar/setup_air.rs` and with [`point_consume_fraction_pair`].
fn consume_public_key_point<E: EvalAtRow>(
    eval: &mut E,
    relation: &PublicKeyPointRelation,
    columns: &PublicKeyCurveCheckColumns<E>,
) {
    let mut values = Vec::with_capacity(PUBLIC_KEY_POINT_ARITY);
    values.push(columns.sig_id.clone());
    values.extend(columns.x.limbs().iter().cloned());
    values.extend(columns.y.limbs().iter().cloned());
    eval.add_to_relation(RelationEntry::new(
        relation,
        E::EF::from(columns.active.clone()),
        &values,
    ));
}

/// Returns the curve-identity carries (in limb order) for the signed-carry
/// γ-digest.
fn add_curve_identity<E: EvalAtRow>(
    eval: &mut E,
    columns: &PublicKeyCurveCheckColumns<E>,
) -> Vec<E::F> {
    let zero = E::F::from(M31::from_u32_unchecked(0));
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    let modulus = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS));
    let b = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_B));

    // q ∈ {-1, 0, 1} via the witnessed boolean split `q = q_pos − q_neg`
    // (lessons.md #44): the inline quartic `active·q·(q−1)·(q+1)` is degree 4,
    // over the log_size + 1 (degree-2) composition budget. All four
    // constraints are ungated (padding rows hold q = q_pos = q_neg = 0) and
    // strictly stronger than the former active-gated quartic.
    let one = E::F::from(M31::from_u32_unchecked(1));
    eval.add_constraint(columns.q.clone() - columns.q_pos.clone() + columns.q_neg.clone());
    eval.add_constraint(columns.q_pos.clone() * (one.clone() - columns.q_pos.clone()));
    eval.add_constraint(columns.q_neg.clone() * (one - columns.q_neg.clone()));
    eval.add_constraint(columns.q_pos.clone() * columns.q_neg.clone());

    let mut carries = Vec::with_capacity(N_LIMBS);
    for i in 0..N_LIMBS {
        carries.push(columns.carries[i].clone());

        let prev_carry = if i == 0 {
            zero.clone()
        } else {
            columns.carries[i - 1].clone()
        };
        let recurrence = columns.y2.limbs()[i].clone() + columns.three_x.limbs()[i].clone()
            - columns.x3.limbs()[i].clone()
            - fixed_limb::<E>(&b, i)
            - columns.q.clone() * fixed_limb::<E>(&modulus, i)
            + prev_carry
            - limb_base.clone() * columns.carries[i].clone();
        eval.add_constraint(columns.active.clone() * recurrence);
    }
    eval.add_constraint(columns.active.clone() * columns.carries[N_LIMBS - 1].clone());
    carries
}

fn fixed_limb<E: EvalAtRow>(value: &P256M31BigInt, index: usize) -> E::F {
    E::F::from(value.limbs()[index])
}

// ---------------------------------------------------------------------------
// Components bundle
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct PublicKeyCurveSliceLogSizes {
    curve_check: u32,
    /// First hinted-mul `source_index` reserved for the curve-check muls.
    pub(crate) hinted_source_offset: u32,
}

impl PublicKeyCurveSliceLogSizes {
    fn from_claim(claim: &PublicKeyCurveSliceClaim) -> Self {
        Self {
            curve_check: padded_log_size(claim.mul_trace.rows.len()),
            hinted_source_offset: claim.hinted_source_offset,
        }
    }
}

#[derive(Clone)]
pub(crate) struct PublicKeyCurveSliceRelations {
    /// SHARED with the hinted-mul provider in the monolith (the standalone
    /// slice draws its own instance; its mul consumes are unbalanced there,
    /// which only the monolithic balance accounting observes).
    mul_result: ProjectiveRcbMulResultRelation,
    range13: RangeCheckRelation,
    signed_carry: RangeCheckRelation,
    point: PublicKeyPointRelation,
    /// γ-digest relation + challenge (SHARED with every adopter in the
    /// monolith; the standalone slice draws/builds its own).
    gamma_digest: GammaDigestRelation,
    gamma_challenge: GammaChallenge,
}

impl PublicKeyCurveSliceRelations {
    /// Standalone draw (test-only): the monolith shares instances via
    /// [`Self::draw_with_point`].
    #[cfg(test)]
    fn draw(channel: &mut impl Channel) -> Self {
        Self {
            mul_result: ProjectiveRcbMulResultRelation::draw(channel),
            range13: RangeCheckRelation::draw(channel),
            signed_carry: RangeCheckRelation::draw(channel),
            point: PublicKeyPointRelation::draw(channel),
            gamma_digest: GammaDigestRelation::draw(channel),
            gamma_challenge: GammaChallenge::draw(channel, pkc_gamma_max_padded_values()),
        }
    }

    fn dummy() -> Self {
        Self {
            mul_result: ProjectiveRcbMulResultRelation::dummy(),
            range13: RangeCheckRelation::dummy(),
            signed_carry: RangeCheckRelation::dummy(),
            point: PublicKeyPointRelation::dummy(),
            gamma_digest: GammaDigestRelation::dummy(),
            gamma_challenge: GammaChallenge::from_gamma(
                SecureField::from(M31::from_u32_unchecked(2)),
                pkc_gamma_max_padded_values(),
            ),
        }
    }

    /// Draw the public-key sub-graph's internal relations (`mul`, `result`)
    /// fresh, but reuse a `point` relation shared with the
    /// `scalar/setup_air.rs` provider so the binding tuple links the two
    /// components. Used by the monolithic proof.
    pub(crate) fn draw_with_point(
        channel: &mut impl Channel,
        point: PublicKeyPointRelation,
        mul_result: ProjectiveRcbMulResultRelation,
        gamma_digest: GammaDigestRelation,
        gamma_challenge: GammaChallenge,
    ) -> Self {
        Self {
            mul_result,
            range13: RangeCheckRelation::draw(channel),
            signed_carry: RangeCheckRelation::draw(channel),
            point,
            gamma_digest,
            gamma_challenge,
        }
    }

    /// Dummy variant with a caller-supplied `point` relation (for preprocessed
    /// column / degree-bound queries in the monolith).
    pub(crate) fn dummy_with_point(
        point: PublicKeyPointRelation,
        mul_result: ProjectiveRcbMulResultRelation,
        gamma_digest: GammaDigestRelation,
        gamma_challenge: GammaChallenge,
    ) -> Self {
        Self {
            mul_result,
            range13: RangeCheckRelation::dummy(),
            signed_carry: RangeCheckRelation::dummy(),
            point,
            gamma_digest,
            gamma_challenge,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PublicKeyCurveSliceInteractionClaim {
    claimed_sum: SecureField,
    range13: RangeCheckInteractionClaim,
    signed_carry: RangeCheckInteractionClaim,
    /// γ-digest tall expanders (range13 kind, signed kind).
    gamma_range13: GammaTallInteractionClaim,
    gamma_signed: GammaTallInteractionClaim,
}

impl PublicKeyCurveSliceInteractionClaim {
    fn zero() -> Self {
        let zero = secure_zero();
        Self {
            claimed_sum: zero,
            range13: RangeCheckInteractionClaim { claimed_sum: zero },
            signed_carry: RangeCheckInteractionClaim { claimed_sum: zero },
            gamma_range13: GammaTallInteractionClaim::zero(),
            gamma_signed: GammaTallInteractionClaim::zero(),
        }
    }

    /// Aggregate claimed sum over every public-key sub-graph component.
    pub(crate) fn total(&self) -> SecureField {
        self.claimed_sum
            + self.range13.claimed_sum
            + self.signed_carry.claimed_sum
            + self.gamma_range13.claimed_sum
            + self.gamma_signed.claimed_sum
    }

    fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[
            self.claimed_sum,
            self.range13.claimed_sum,
            self.signed_carry.claimed_sum,
        ]);
        self.gamma_range13.mix_into(channel);
        self.gamma_signed.mix_into(channel);
    }
}

pub(crate) struct PublicKeyCurveSliceComponents {
    curve_check: PublicKeyCurveCheckComponent,
    gamma_range13: GammaTallComponent,
    gamma_signed: GammaTallComponent,
    range13: RangeCheckComponent,
    signed_carry: SignedCarryRangeComponent,
}

impl PublicKeyCurveSliceComponents {
    pub(crate) fn new(
        allocator: &mut TraceLocationAllocator,
        log_sizes: PublicKeyCurveSliceLogSizes,
        interaction_claim: &PublicKeyCurveSliceInteractionClaim,
        relations: &PublicKeyCurveSliceRelations,
        bind_to_public: bool,
    ) -> Self {
        Self {
            curve_check: PublicKeyCurveCheckComponent::new(
                allocator,
                PublicKeyCurveCheckEval {
                    log_size: log_sizes.curve_check,
                    mul_result: relations.mul_result.clone(),
                    hinted_source_offset: log_sizes.hinted_source_offset,
                    point_relation: relations.point.clone(),
                    bind_to_public,
                    gamma_digest: relations.gamma_digest.clone(),
                    gamma_challenge: relations.gamma_challenge.clone(),
                },
                interaction_claim.claimed_sum,
            ),
            gamma_range13: GammaTallComponent::new(
                allocator,
                GammaTallEval {
                    layout: pkc_gamma_layouts()[0],
                    challenge: relations.gamma_challenge.clone(),
                    digest: relations.gamma_digest.clone(),
                    range: relations.range13.clone(),
                },
                interaction_claim.gamma_range13.claimed_sum,
            ),
            gamma_signed: GammaTallComponent::new(
                allocator,
                GammaTallEval {
                    layout: pkc_gamma_layouts()[1],
                    challenge: relations.gamma_challenge.clone(),
                    digest: relations.gamma_digest.clone(),
                    range: relations.signed_carry.clone(),
                },
                interaction_claim.gamma_signed.claimed_sum,
            ),
            range13: RangeCheckComponent::new(
                allocator,
                RangeCheckEval::new(relations.range13.clone(), RANGE13_BITS),
                interaction_claim.range13.claimed_sum,
            ),
            signed_carry: SignedCarryRangeComponent::new(
                allocator,
                SignedCarryRangeEval::new(
                    relations.signed_carry.clone(),
                    projective_rcb_signed_carry_log_size(),
                    PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
                ),
                interaction_claim.signed_carry.claimed_sum,
            ),
        }
    }

    pub(crate) fn components(&self) -> Vec<&dyn Component> {
        vec![
            &self.curve_check as &dyn Component,
            &self.gamma_range13 as &dyn Component,
            &self.gamma_signed as &dyn Component,
            &self.range13 as &dyn Component,
            &self.signed_carry as &dyn Component,
        ]
    }

    pub(crate) fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            &self.curve_check as &dyn ComponentProver<SimdBackend>,
            &self.gamma_range13 as &dyn ComponentProver<SimdBackend>,
            &self.gamma_signed as &dyn ComponentProver<SimdBackend>,
            &self.range13 as &dyn ComponentProver<SimdBackend>,
            &self.signed_carry as &dyn ComponentProver<SimdBackend>,
        ]
    }

    #[cfg(test)]
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.components()
            .into_iter()
            .map(|component| component.max_constraint_log_degree_bound())
            .max()
            .unwrap_or(0)
    }
}

// ---------------------------------------------------------------------------
// Proof claim + proof object
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PublicKeyCurveSliceProofClaim {
    log_sizes: PublicKeyCurveSliceLogSizes,
}

impl PublicKeyCurveSliceProofClaim {
    pub(crate) fn from_claim(claim: &PublicKeyCurveSliceClaim) -> Self {
        Self {
            log_sizes: PublicKeyCurveSliceLogSizes::from_claim(claim),
        }
    }

    pub(crate) fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_sizes.curve_check as u64);
        channel.mix_u64(self.log_sizes.hinted_source_offset as u64);
    }

    pub(crate) fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut allocator = TraceLocationAllocator::default();
        let _ = PublicKeyCurveSliceComponents::new(
            &mut allocator,
            self.log_sizes,
            &PublicKeyCurveSliceInteractionClaim::zero(),
            &PublicKeyCurveSliceRelations::dummy(),
            false,
        );
        allocator.preprocessed_columns().clone()
    }

    #[cfg(test)]
    fn max_constraint_log_degree_bound(&self, ids: &[PreProcessedColumnId]) -> u32 {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = PublicKeyCurveSliceComponents::new(
            &mut allocator,
            self.log_sizes,
            &PublicKeyCurveSliceInteractionClaim::zero(),
            &PublicKeyCurveSliceRelations::dummy(),
            false,
        );
        components.max_constraint_log_degree_bound()
    }
}

// ---------------------------------------------------------------------------
// Trace generation
// ---------------------------------------------------------------------------

pub(crate) fn gen_slice_preprocessed_trace(
    _claim: &PublicKeyCurveSliceClaim,
    ids: &[PreProcessedColumnId],
) -> Result<Vec<M31ColumnEval>, PublicKeyCurveSliceError> {
    // Local range13 / signed-carry provider columns plus the γ-digest tall
    // schedules; the four muls are proven by the shared hinted provider.
    let range13 = RangeCheckClaim::new(RANGE13_BITS);
    let signed_carry = slice_signed_carry_claim();
    let mut columns: Vec<(PreProcessedColumnId, M31ColumnEval)> = vec![
        (
            range_check_value_column_id(RANGE13_BITS),
            range13.gen_preprocessed_column(),
        ),
        (
            signed_carry_value_column_id(PROJECTIVE_RCB_SIGNED_CARRY_EQUATION),
            signed_carry.gen_value_column(),
        ),
        (
            signed_carry_active_column_id(PROJECTIVE_RCB_SIGNED_CARRY_EQUATION),
            signed_carry.gen_active_column(),
        ),
    ];
    for layout in pkc_gamma_layouts() {
        columns.extend(
            crate::components::gamma_digest::gamma_tall_preprocessed_ids(layout.tag)
                .into_iter()
                .zip(gen_gamma_tall_preprocessed_trace(&layout)),
        );
    }

    ids.iter()
        .map(|id| {
            columns
                .iter()
                .find_map(|(column_id, eval)| (column_id == id).then(|| eval.clone()))
                .ok_or_else(|| PublicKeyCurveSliceError::PreprocessedColumnMissing {
                    id: id.id.clone(),
                })
        })
        .collect()
}

/// γ-digest value lists for the (single-row) curve-check slice. Range13:
/// every witnessed limb in [`PublicKeyCurveCheckEval`]'s collection order
/// (x, y, x2, x3, three_x, y2); signed: the curve-identity carries.
fn pkc_gamma_range13_values(claim: &PublicKeyCurveSliceClaim) -> Vec<M31> {
    [
        &claim.x,
        &claim.y,
        &claim.x2,
        &claim.x3,
        &claim.three_x,
        &claim.y2,
    ]
    .iter()
    .flat_map(|value| value.limbs().iter().copied())
    .collect()
}

fn pkc_gamma_signed_values(claim: &PublicKeyCurveSliceClaim) -> Vec<M31> {
    claim
        .carries
        .iter()
        .copied()
        .map(encode_signed_carry)
        .collect()
}

const PKC_GAMMA_RANGE13_VALUES: usize = 6 * N_LIMBS;
const PKC_GAMMA_SIGNED_VALUES: usize = N_LIMBS;

pub(crate) fn pkc_gamma_max_padded_values() -> usize {
    crate::components::gamma_digest::gamma_padded_values(PKC_GAMMA_RANGE13_VALUES).max(
        crate::components::gamma_digest::gamma_padded_values(PKC_GAMMA_SIGNED_VALUES),
    )
}

/// The slice covers exactly one signature ⇒ one digest group per kind.
pub(crate) fn pkc_gamma_layouts() -> [GammaTallLayout; 2] {
    [
        GammaTallLayout {
            tag: GAMMA_TAG_PKC_RANGE13,
            group_count: 1,
            values_per_group: PKC_GAMMA_RANGE13_VALUES,
        },
        GammaTallLayout {
            tag: GAMMA_TAG_PKC_SIGNED,
            group_count: 1,
            values_per_group: PKC_GAMMA_SIGNED_VALUES,
        },
    ]
}

pub(crate) fn pkc_gamma_instances(claim: &PublicKeyCurveSliceClaim) -> [GammaTallInstance; 2] {
    [
        GammaTallInstance::new(
            GAMMA_TAG_PKC_RANGE13,
            PKC_GAMMA_RANGE13_VALUES,
            M31::from_u32_unchecked(0),
            vec![pkc_gamma_range13_values(claim)],
        ),
        GammaTallInstance::new(
            GAMMA_TAG_PKC_SIGNED,
            PKC_GAMMA_SIGNED_VALUES,
            encode_signed_carry(0),
            vec![pkc_gamma_signed_values(claim)],
        ),
    ]
}

fn slice_signed_carry_claim() -> SignedCarryRangeClaim {
    SignedCarryRangeClaim::new(
        projective_rcb_signed_carry_log_size(),
        projective_rcb_signed_carry_bound(),
        PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
    )
}

pub(crate) fn gen_slice_base_trace(
    claim: &PublicKeyCurveSliceClaim,
) -> Result<Vec<M31ColumnEval>, PublicKeyCurveSliceError> {
    let log_sizes = PublicKeyCurveSliceLogSizes::from_claim(claim);
    let mut trace = Vec::new();

    // Curve-check family (the four muls are proven by hinted-mul rows).
    trace.extend(gen_curve_check_base_trace(claim, log_sizes.curve_check));

    // γ-digest tall value grids, then the local range providers' multiplicity
    // columns (tallying the talls' uses), in component order.
    let [gamma_range13_instance, gamma_signed_instance] = pkc_gamma_instances(claim);
    trace.extend(gen_gamma_tall_base_trace(&gamma_range13_instance));
    trace.extend(gen_gamma_tall_base_trace(&gamma_signed_instance));
    let range13 = RangeCheckClaim::new(RANGE13_BITS);
    trace.push(range13.gen_multiplicity_trace(slice_range13_uses(claim)));
    let signed_carry = slice_signed_carry_claim();
    trace.push(signed_carry.gen_multiplicity_trace(slice_signed_carry_uses(claim)));

    Ok(trace)
}

fn gen_curve_check_base_trace(
    claim: &PublicKeyCurveSliceClaim,
    log_size: u32,
) -> Vec<M31ColumnEval> {
    let row_count = 1usize << log_size;
    let mut columns = vec![vec![M31::from_u32_unchecked(0); row_count]; CURVE_CHECK_TRACE_COLUMNS];

    // Single active row at coset index 0.
    let mut offset = 0usize;
    columns[offset][0] = M31::from_u32_unchecked(1);
    offset += 1;
    columns[offset][0] = claim.sig_id;
    offset += 1;
    write_limbs(&mut columns, &mut offset, &claim.x, 0);
    write_limbs(&mut columns, &mut offset, &claim.y, 0);
    write_limbs(&mut columns, &mut offset, &claim.x2, 0);
    write_limbs(&mut columns, &mut offset, &claim.x3, 0);
    write_limbs(&mut columns, &mut offset, &claim.three_x, 0);
    write_limbs(&mut columns, &mut offset, &claim.y2, 0);
    columns[offset][0] = encode_signed_carry(claim.q);
    offset += 1;
    for carry in claim.carries {
        columns[offset][0] = encode_signed_carry(carry);
        offset += 1;
    }
    // Witnessed boolean split of q ∈ {-1, 0, 1} (padding rows stay all-zero,
    // satisfying the ungated split constraints with q = 0).
    debug_assert!((-1..=1).contains(&claim.q), "curve-identity q ∈ {{-1,0,1}}");
    columns[offset][0] = M31::from_u32_unchecked(u32::from(claim.q == 1));
    offset += 1;
    columns[offset][0] = M31::from_u32_unchecked(u32::from(claim.q == -1));
    offset += 1;
    debug_assert_eq!(offset, CURVE_CHECK_TRACE_COLUMNS);

    columns
        .into_iter()
        .map(|values| m31_column_eval(log_size, values))
        .collect()
}

fn write_limbs(columns: &mut [Vec<M31>], offset: &mut usize, value: &P256M31BigInt, row: usize) {
    for limb in value.limbs() {
        columns[*offset][row] = *limb;
        *offset += 1;
    }
}

/// Range13 uses across the slice: the γ-digest tall expander's grid (the
/// curve-check witnessed limbs, lane-padded). The tall instance is the single
/// source of truth, so the provider tally cannot drift from the consumption.
fn slice_range13_uses(claim: &PublicKeyCurveSliceClaim) -> Vec<M31> {
    let [r13, _] = pkc_gamma_instances(claim);
    r13.all_scheduled_values()
}

/// Signed-carry uses: the signed tall expander's grid (the curve-identity
/// carries, lane-padded with `encode_signed_carry(0)`), decoded.
fn slice_signed_carry_uses(claim: &PublicKeyCurveSliceClaim) -> Vec<i64> {
    let [_, signed] = pkc_gamma_instances(claim);
    signed
        .all_scheduled_values()
        .into_iter()
        .map(crate::range_checks::decode_signed_carry)
        .collect()
}

pub(crate) fn gen_slice_interaction_trace(
    claim: &PublicKeyCurveSliceClaim,
    relations: &PublicKeyCurveSliceRelations,
    bind_to_public: bool,
) -> Result<(Vec<M31ColumnEval>, PublicKeyCurveSliceInteractionClaim), PublicKeyCurveSliceError> {
    let log_sizes = PublicKeyCurveSliceLogSizes::from_claim(claim);
    let mut trace = Vec::new();

    // Curve-check family (consumers). The four muls are proven by hinted-mul
    // rows; the check consumes them via wide tuples against the shared
    // `ProjectiveRcbMulResult` relation. In the monolith (`bind_to_public`) it
    // also emits the `PublicKeyPointRelation` consume that binds `(x, y)` to
    // the public key; the standalone slice emits no binding tuple.
    let (curve_trace, curve_claim, _mul_result_sum, _gamma_yield_sum) =
        gen_curve_check_interaction_trace(claim, relations, log_sizes.curve_check, bind_to_public);
    trace.extend(curve_trace);

    // γ-digest tall expanders (range13 kind, signed kind).
    let [gamma_range13_instance, gamma_signed_instance] = pkc_gamma_instances(claim);
    let (gamma_range13_trace, gamma_range13_claim) = gen_gamma_tall_interaction_trace(
        &gamma_range13_instance,
        &relations.gamma_challenge,
        &relations.gamma_digest,
        &relations.range13,
    );
    trace.extend(gamma_range13_trace);
    let (gamma_signed_trace, gamma_signed_claim) = gen_gamma_tall_interaction_trace(
        &gamma_signed_instance,
        &relations.gamma_challenge,
        &relations.gamma_digest,
        &relations.signed_carry,
    );
    trace.extend(gamma_signed_trace);

    // Local range providers.
    let range13 = RangeCheckClaim::new(RANGE13_BITS);
    let range13_values = range13.gen_preprocessed_column();
    let range13_multiplicity = range13.gen_multiplicity_trace(slice_range13_uses(claim));
    let (range13_trace, range13_claim) = RangeCheckInteractionClaim::gen_interaction_trace(
        &range13_multiplicity,
        &range13_values,
        &relations.range13,
    );
    trace.extend(range13_trace);

    let signed_carry = slice_signed_carry_claim();
    let signed_carry_values = signed_carry.gen_value_column();
    let signed_carry_multiplicity =
        signed_carry.gen_multiplicity_trace(slice_signed_carry_uses(claim));
    let (signed_carry_trace, signed_carry_claim) =
        RangeCheckInteractionClaim::gen_interaction_trace(
            &signed_carry_multiplicity,
            &signed_carry_values,
            &relations.signed_carry,
        );
    trace.extend(signed_carry_trace);

    Ok((
        trace,
        PublicKeyCurveSliceInteractionClaim {
            claimed_sum: curve_claim,
            range13: range13_claim,
            signed_carry: signed_carry_claim,
            gamma_range13: gamma_range13_claim,
            gamma_signed: gamma_signed_claim,
        },
    ))
}

fn gen_curve_check_interaction_trace(
    claim: &PublicKeyCurveSliceClaim,
    relations: &PublicKeyCurveSliceRelations,
    log_size: u32,
    bind_to_public: bool,
) -> (
    ColumnVec<M31ColumnEval>,
    SecureField,
    SecureField,
    SecureField,
) {
    let padded_rows = 1usize << log_size;
    let (fractions, mul_result_sum, gamma_yield_sum) =
        curve_check_fraction_pairs(claim, relations, bind_to_public);
    let fraction_count = fractions.len();

    // Single active row at coset index 0; everything else is padding.
    let active_row = bit_reverse_index(coset_index_to_circle_domain_index(0, log_size), log_size);
    let mut storage: Vec<Vec<(SecureField, SecureField)>> = (0..padded_rows)
        .map(|_| vec![(secure_zero(), secure_one()); fraction_count])
        .collect();
    storage[active_row] = fractions;

    let mut logup = LogupTraceGenerator::new(log_size);
    for column in (0..fraction_count).step_by(2) {
        let mut col = logup.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let mut numerators = [secure_zero(); N_LANES];
            let mut denominators = [secure_one(); N_LANES];
            for lane in 0..N_LANES {
                let row = vec_row * N_LANES + lane;
                let (mut numerator, mut denominator) = storage[row][column];
                if let Some((next_numerator, next_denominator)) =
                    storage[row].get(column + 1).copied()
                {
                    numerator = numerator * next_denominator + next_numerator * denominator;
                    denominator *= next_denominator;
                }
                numerators[lane] = numerator;
                denominators[lane] = denominator;
            }
            col.write_frac(
                vec_row,
                PackedQM31::from_array(numerators),
                PackedQM31::from_array(denominators),
            );
        }
        col.finalize_col();
    }
    let (trace, curve_sum) = logup.finalize_last();
    (trace, curve_sum, mul_result_sum, gamma_yield_sum)
}

/// Curve-check consumer fractions, in the exact order
/// [`PublicKeyCurveCheckEval::evaluate`] emits them:
/// 1. wide mul-result consume tuples (mul 0..3, roles lhs/rhs/result),
/// 2. (monolith only) the `PublicKeyPointRelation` binding consume,
/// 3. the two γ-digest yields (range13 kind, signed kind).
///
/// Also returns the mul-result boundary sum and the γ-yield sum.
fn curve_check_fraction_pairs(
    claim: &PublicKeyCurveSliceClaim,
    relations: &PublicKeyCurveSliceRelations,
    bind_to_public: bool,
) -> (Vec<(SecureField, SecureField)>, SecureField, SecureField) {
    let mut pairs = Vec::new();

    // 1. mul-result consumes (use, +1): wide tuples against the hinted
    //    provider, in the exact order the eval emits them. The `MUL_THREE_X`
    //    lhs is the fixed constant `3` (limbs [3, 0, ..]), matching
    //    [`consume_three_constant`].
    let mut mul_result_sum = secure_zero();
    let mul_source = M31::from_u32_unchecked(claim.hinted_source_offset) + claim.sig_id;
    let mut consume = |pairs: &mut Vec<(SecureField, SecureField)>,
                       mul_index: u32,
                       role: u32,
                       value: &P256M31BigInt| {
        let mut values = Vec::with_capacity(3 + N_LIMBS);
        values.push(mul_source);
        values.push(M31::from_u32_unchecked(mul_index));
        values.push(M31::from_u32_unchecked(role));
        values.extend(value.limbs().iter().copied());
        let denom = relations.mul_result.combine(&values);
        pairs.push((secure_from_i64(1), denom));
        mul_result_sum += secure_from_i64(1) / denom;
    };
    let three = P256M31BigInt::from_u256(&U256::from_le_u64s(&[3, 0, 0, 0]));

    consume(&mut pairs, MUL_Y_SQUARED, ROLE_LHS, &claim.y);
    consume(&mut pairs, MUL_Y_SQUARED, ROLE_RHS, &claim.y);
    consume(&mut pairs, MUL_Y_SQUARED, ROLE_RESULT, &claim.y2);

    consume(&mut pairs, MUL_X_SQUARED, ROLE_LHS, &claim.x);
    consume(&mut pairs, MUL_X_SQUARED, ROLE_RHS, &claim.x);
    consume(&mut pairs, MUL_X_SQUARED, ROLE_RESULT, &claim.x2);

    consume(&mut pairs, MUL_X_CUBED, ROLE_LHS, &claim.x2);
    consume(&mut pairs, MUL_X_CUBED, ROLE_RHS, &claim.x);
    consume(&mut pairs, MUL_X_CUBED, ROLE_RESULT, &claim.x3);

    consume(&mut pairs, MUL_THREE_X, ROLE_LHS, &three);
    consume(&mut pairs, MUL_THREE_X, ROLE_RHS, &claim.x);
    consume(&mut pairs, MUL_THREE_X, ROLE_RESULT, &claim.three_x);

    // 2. (monolith only) PublicKeyPoint binding consume (use, +1).
    if bind_to_public {
        pairs.push(point_consume_fraction_pair(claim, &relations.point));
    }

    // 3. γ-digest yields (−1 on the single active row), range13 kind then
    //    signed kind, mirroring the eval's collection order.
    let mut gamma_yield_sum = secure_zero();
    for instance in pkc_gamma_instances(claim) {
        let digest = gamma_digest_of_values(
            &relations.gamma_challenge,
            instance.pad_value,
            &instance.padded_group_values(0),
        );
        let tuple = gamma_digest_tuple(instance.layout.tag, M31::from_u32_unchecked(0), digest);
        let denom: SecureField = relations.gamma_digest.combine(&tuple);
        pairs.push((secure_from_i64(-1), denom));
        gamma_yield_sum += secure_from_i64(-1) / denom;
    }

    (pairs, mul_result_sum, gamma_yield_sum)
}

#[cfg(test)]
fn curve_mul_result_consumer_sum(
    claim: &PublicKeyCurveSliceClaim,
    relations: &PublicKeyCurveSliceRelations,
    bind_to_public: bool,
) -> SecureField {
    let (_, mul_result_sum, _) = curve_check_fraction_pairs(claim, relations, bind_to_public);
    mul_result_sum
}

/// The single `(numerator, denominator)` pair for the `PublicKeyPointRelation`
/// binding consume, in the exact value order [`consume_public_key_point`] emits:
/// `[sig_id, x.., y..]` with numerator `+1` (use).
fn point_consume_fraction_pair(
    claim: &PublicKeyCurveSliceClaim,
    point: &PublicKeyPointRelation,
) -> (SecureField, SecureField) {
    let mut values = Vec::with_capacity(PUBLIC_KEY_POINT_ARITY);
    values.push(claim.sig_id);
    values.extend(claim.x.limbs().iter().copied());
    values.extend(claim.y.limbs().iter().copied());
    (secure_from_i64(1), point.combine(&values))
}

// ---------------------------------------------------------------------------
// Prove / verify
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Errors + small helpers
// ---------------------------------------------------------------------------

/// Errors raised while building, proving or verifying the slice.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PublicKeyCurveSliceError {
    /// The underlying native public-key claim failed verification.
    PublicKey(PublicKeyOnCurveError),
    /// A mul-machinery trace error.
    MulTrace(ProjectiveRcbAirError),
    /// This standalone slice supports exactly one public key.
    UnsupportedRowCount { actual: usize },
    /// A witnessed limb did not match the proven mul operand/result.
    WitnessMismatch { field: &'static str },
    /// The point is not on the curve (no `q ∈ {-1,0,1}` solves the identity).
    PointOffCurveNative,
    /// The curve-identity quotient is outside `{-1, 0, 1}`.
    QuotientOutOfRange { q: i64 },
    /// A curve-identity limb recurrence did not vanish.
    CurveIdentityMismatch { limb: usize, value: i64 },
    /// A curve-identity carry exceeded the shared signed-carry bound.
    CarryOutOfRange { limb: usize, carry: i64 },
    /// The final curve-identity carry was nonzero.
    FinalCarryNonZero { carry: i64 },
    /// A required preprocessed column was not produced.
    PreprocessedColumnMissing { id: String },
    /// The interaction claim did not balance to zero.
    RelationImbalance,
    /// The underlying stwo prover/verifier rejected the proof.
    ProofLayer(String),
}

impl From<PublicKeyOnCurveError> for PublicKeyCurveSliceError {
    fn from(value: PublicKeyOnCurveError) -> Self {
        Self::PublicKey(value)
    }
}

fn secure_zero() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(0))
}

fn secure_one() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(1))
}

fn secure_from_i64(value: i64) -> SecureField {
    const M31_MODULUS: i128 = (1i128 << 31) - 1;
    SecureField::from(M31::from_u32_unchecked(
        i128::from(value).rem_euclid(M31_MODULUS) as u32,
    ))
}

/// Build a slice claim directly from a [`PublicEcdsaInputClaim`] (test/helper).
pub fn public_key_curve_slice_claim_from_public_inputs(
    public_inputs: &PublicEcdsaInputClaim,
) -> Result<PublicKeyCurveSliceClaim, PublicKeyCurveSliceError> {
    let on_curve = PublicKeyOnCurveClaim::from_public_inputs(public_inputs)?;
    // The standalone slice has no hinted provider; source offset 0 is a label.
    PublicKeyCurveSliceClaim::from_public_key_claim(&on_curve, 0)
}

// ---------------------------------------------------------------------------
// Monolithic-proof integration surface
// ---------------------------------------------------------------------------
//
// The monolithic current-AIR proof reuses the slice machinery above with
// `bind_to_public = true`, drawing the `PublicKeyPointRelation` once and sharing
// it with the `scalar/setup_air.rs` provider so the curve-checked `(x, y)` is
// LogUp-bound to the verifier public key.

impl PublicKeyCurveSliceProofClaim {
    pub(crate) fn log_sizes(&self) -> PublicKeyCurveSliceLogSizes {
        self.log_sizes
    }
}

impl PublicKeyCurveSliceInteractionClaim {
    /// Mix the public-key sub-graph claimed sums into the transcript (monolith).
    pub(crate) fn mix_into_monolithic(&self, channel: &mut impl Channel) {
        self.mix_into(channel);
    }

    pub(crate) fn zero_claim() -> Self {
        Self::zero()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY};
    use crate::fp_solinas::M31_CENTERED_BOUND;
    use crate::types::{AffinePoint, EcdsaVerifyInput, Signature};
    use stwo::core::fri::FriConfig;
    use stwo::core::pcs::PcsConfig;
    use stwo::core::poly::circle::CanonicCoset;
    use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
    use stwo::prover::poly::circle::PolyOps;
    use stwo::prover::{prove, CommitmentSchemeProver};

    fn generator_inputs() -> PublicEcdsaInputClaim {
        PublicEcdsaInputClaim::from_inputs(&[EcdsaVerifyInput {
            message_hash: scalar(42),
            signature: Signature {
                r: scalar(77),
                s: scalar(1),
            },
            public_key: AffinePoint {
                x: U256::from_le_u64s(&P256_GX),
                y: U256::from_le_u64s(&P256_GY),
            },
        }])
    }

    fn scalar(value: u64) -> U256 {
        U256::from_le_u64s(&[value, 0, 0, 0])
    }

    fn slice_config(claim: &PublicKeyCurveSliceClaim) -> PcsConfig {
        let proof_claim = PublicKeyCurveSliceProofClaim::from_claim(claim);
        let ids = proof_claim.preprocessed_column_ids();
        let max_bound = proof_claim.max_constraint_log_degree_bound(&ids);
        let fri_config = FriConfig::new(5, 4, 64, 1);
        PcsConfig {
            pow_bits: 0,
            fri_config,
            lifting_log_size: Some((max_bound + fri_config.log_blowup_factor).max(10)),
        }
    }

    #[test]
    fn curve_identity_quotient_in_range() {
        // y2 + three_x ∈ [0, 2p-2] and x3 + b ∈ [0, 2p-2], so the difference
        // is in [-(2p-2), 2p-2]; being a multiple of p it equals q·p with
        // q ∈ {-1, 0, 1}. We confirm the generator's quotient lands there.
        let claim =
            public_key_curve_slice_claim_from_public_inputs(&generator_inputs()).expect("on-curve");
        assert!((-CURVE_QUOTIENT_BOUND..=CURVE_QUOTIENT_BOUND).contains(&claim.q));
    }

    #[test]
    fn curve_identity_headroom_fits_m31() {
        // max |recurrence| = 3·(2^13-1) + carry_bound·(1 + 2^13) < M31 centered bound.
        let base = 1i64 << LIMB_BITS;
        let carry_bound = projective_rcb_signed_carry_bound();
        let max_term = 3 * (base - 1) + carry_bound + base * carry_bound;
        assert!(max_term < M31_CENTERED_BOUND as i64);
    }

    #[test]
    fn public_key_on_curve_slice_rejects_off_curve() {
        // 1. The native pipeline rejects an off-curve public key outright:
        //    `PublicKeyOnCurveClaim::from_public_inputs` checks `y^2 == rhs`.
        let mut off_inputs = generator_inputs();
        off_inputs.instances[0].pub_y = P256M31BigInt::from_u256(&scalar(1));
        assert!(matches!(
            public_key_curve_slice_claim_from_public_inputs(&off_inputs),
            Err(PublicKeyCurveSliceError::PublicKey(
                PublicKeyOnCurveError::PointOffCurve { .. }
            ))
        ));

        // 2. The provable layer also rejects a forged witness. A malicious
        //    prover who wants to prove an off-curve `(x, y')` must keep the
        //    real `y^2` mul (then the curve identity cannot vanish for `y'`)
        //    or lie about the witnessed `y` binding. We model the binding lie:
        //    corrupt the witnessed `y` consumed by the curve check while the
        //    `y^2` mul still proves the *original* `y`.
        //
        //    Per lessons.md #18 the rejection oracle is the relation-balance
        //    audit (not `assert_constraints`, which double-panics on a failing
        //    LogUp). The muls are proven by the shared hinted provider, which
        //    yields wide tuples for the real `y` limbs on
        //    `ProjectiveRcbMulResult`; the curve check consumes the corrupted
        //    limbs, so the cross-component boundary can no longer balance.
        let mut forged =
            public_key_curve_slice_claim_from_public_inputs(&generator_inputs()).expect("on-curve");
        forged.y.limbs_mut()[0] = M31::from_u32_unchecked(forged.y.limbs()[0].0 ^ 1);

        // Native re-verification rejects the forged binding.
        assert!(matches!(
            forged.verify(),
            Err(PublicKeyCurveSliceError::WitnessMismatch { .. })
        ));

        // The mul-result boundary residue is nonzero: the corrupted `y`
        // consume tuples (mul 0, roles lhs/rhs) no longer cancel the hinted
        // provider's real-`y` yield tuples (modelled by
        // `hinted_provider_sum`, the exact wide tuples the monolithic
        // hinted-mul component yields for this claim's `mul_trace`).
        let mut channel = stwo::core::channel::Blake2sChannel::default();
        let relations = PublicKeyCurveSliceRelations::draw(&mut channel);
        let honest =
            public_key_curve_slice_claim_from_public_inputs(&generator_inputs()).expect("on-curve");
        let (_, _honest_claim) =
            gen_slice_interaction_trace(&honest, &relations, false).expect("trace builds");
        let honest_mul_consumer = curve_mul_result_consumer_sum(&honest, &relations, false);
        assert_eq!(
            honest_mul_consumer + hinted_provider_sum(&honest, &relations),
            secure_zero()
        );
        let (_, _interaction_claim) =
            gen_slice_interaction_trace(&forged, &relations, false).expect("trace builds");
        let forged_mul_consumer = curve_mul_result_consumer_sum(&forged, &relations, false);
        assert_ne!(
            forged_mul_consumer + hinted_provider_sum(&forged, &relations),
            secure_zero()
        );

        // 3. The complementary attack — bindings made self-consistent for the
        //    wrong `y'` (the `y^2` mul squares `y'`, `y2 = y'^2`) but the
        //    curve identity now cannot vanish for any `q in {-1,0,1}` — is
        //    caught by the polynomial recurrence at prove time. There is no
        //    valid carry witness, so we keep the stale on-curve carries and
        //    assert the prover rejects the trace.
        let mut consistent_off = consistent_off_curve_claim();
        // Sanity: bindings are internally consistent (mul squares y'), so the
        // mul-result relation balances; only the curve identity is violated.
        let mut audit_channel = stwo::core::channel::Blake2sChannel::default();
        let audit_relations = PublicKeyCurveSliceRelations::draw(&mut audit_channel);
        let (_, balanced) = gen_slice_interaction_trace(&consistent_off, &audit_relations, false)
            .expect("trace builds");
        let balanced_mul_consumer =
            curve_mul_result_consumer_sum(&consistent_off, &audit_relations, false);
        assert_eq!(balanced.total() - balanced_mul_consumer, secure_zero());
        assert_eq!(
            balanced_mul_consumer + hinted_provider_sum(&consistent_off, &audit_relations),
            secure_zero()
        );
        // But the prover rejects it (curve-identity recurrence does not vanish).
        let config = slice_config(&consistent_off);
        // `prove_*` first calls `claim.verify()`, which catches the off-curve
        // identity natively; bypass that and drive the prover directly.
        consistent_off_assert_prove_fails(&mut consistent_off, config);
    }

    /// The hinted-mul provider's `ProjectiveRcbMulResult` yields (yield, −1)
    /// for the slice's four muls — the monolithic counterpart of the slice's
    /// consumer boundary sum recomputed by `curve_mul_result_consumer_sum`.
    fn hinted_provider_sum(
        claim: &PublicKeyCurveSliceClaim,
        relations: &PublicKeyCurveSliceRelations,
    ) -> SecureField {
        let mut sum = secure_zero();
        let source = M31::from_u32_unchecked(claim.hinted_source_offset) + claim.sig_id;
        for (mul_index, mul) in claim.mul_trace.rows[0].muls.iter().enumerate() {
            for (role, value) in [
                (ROLE_LHS, &mul.trace.lhs),
                (ROLE_RHS, &mul.trace.rhs),
                (ROLE_RESULT, &mul.trace.result),
            ] {
                let mut values = Vec::with_capacity(3 + N_LIMBS);
                values.push(source);
                values.push(M31::from_u32_unchecked(mul_index as u32));
                values.push(M31::from_u32_unchecked(role));
                values.extend(value.limbs().iter().copied());
                let denom: SecureField = relations.mul_result.combine(&values);
                sum += secure_from_i64(-1) / denom;
            }
        }
        sum
    }

    /// Build an off-curve claim whose bindings are self-consistent for `y'`
    /// (so the mul-result LogUp balances) but whose curve identity is violated
    /// (stale on-curve carries kept).
    fn consistent_off_curve_claim() -> PublicKeyCurveSliceClaim {
        let mut claim =
            public_key_curve_slice_claim_from_public_inputs(&generator_inputs()).expect("on-curve");
        let mut wrong_y = claim.y.clone();
        wrong_y.limbs_mut()[0] = M31::from_u32_unchecked(wrong_y.limbs()[0].0 ^ 1);
        let y_u = wrong_y.to_u256();
        let new_y2 =
            ProjectiveRcbMulRow::new_lite(ProjectiveRcbMulStep::DoubleX1Squared, &y_u, &y_u)
                .expect("mul builds");
        claim.y2 = new_y2.trace.result.clone();
        claim.mul_trace.rows[0].muls[MUL_Y_SQUARED as usize] = new_y2;
        claim.y = wrong_y;
        // q / carries are left as the original on-curve witness, which no
        // longer satisfies the recurrence for `y'^2`.
        claim
    }

    fn consistent_off_assert_prove_fails(claim: &mut PublicKeyCurveSliceClaim, config: PcsConfig) {
        // Drive the slice prover stages directly but skip the native
        // `claim.verify()` guard so the prover itself is the oracle.
        let proof_claim = PublicKeyCurveSliceProofClaim::from_claim(claim);
        let ids = proof_claim.preprocessed_column_ids();
        let max_bound = proof_claim.max_constraint_log_degree_bound(&ids);
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(
                config
                    .lifting_log_size
                    .unwrap_or(max_bound + config.fri_config.log_blowup_factor),
            )
            .circle_domain()
            .half_coset,
        );
        let mut channel = stwo::core::channel::Blake2sChannel::default();
        let mut commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);
        commitment_scheme.set_store_polynomials_coefficients();

        let preprocessed = gen_slice_preprocessed_trace(claim, &ids).expect("preprocessed");
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(preprocessed);
        tree_builder.commit(&mut channel);

        proof_claim.mix_into(&mut channel);
        let base = gen_slice_base_trace(claim).expect("base");
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(base);
        tree_builder.commit(&mut channel);

        let relations = PublicKeyCurveSliceRelations::draw(&mut channel);
        let (interaction, interaction_claim) =
            gen_slice_interaction_trace(claim, &relations, false).expect("interaction");
        interaction_claim.mix_into(&mut channel);
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(interaction);
        tree_builder.commit(&mut channel);

        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
        let components = PublicKeyCurveSliceComponents::new(
            &mut allocator,
            proof_claim.log_sizes,
            &interaction_claim,
            &relations,
            false,
        );
        let result = prove(
            &components.component_provers(),
            &mut channel,
            commitment_scheme,
        );
        assert!(
            result.is_err(),
            "prover must reject the off-curve identity (constraints not satisfied)"
        );
    }
}
