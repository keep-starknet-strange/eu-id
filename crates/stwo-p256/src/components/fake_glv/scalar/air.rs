//! Binds each certificate scalar `u` to a fake-GLV decomposition.
//!
//! The AIR proves `s1 + u · s2 ≡ 0 (mod n)`.
//!
//! # Zero-scalar behavior
//!
//! ECDSA permits `u1 = z · s⁻¹ mod n` to equal zero.
//! Thus, the AIR accepts zero scalars.
//!
//! - For `u = 0`, `cert_active` is zero.
//!   The AIR sets each hint cell to zero.
//!   The EC chain produces the point at infinity for that certificate.
//! - An active certificate requires nonzero `s2_abs`.
//!   A degree-one M31 inverse constraint enforces this condition.
//! - `ScalarModMul` proves `u · s2_abs ≡ ±s1 (mod n)`.
//!   This relation prevents `s1 = 0` on an active certificate.
//!
//! `FakeGlvScalarHintRow::verify` also rejects zero `s1` during witness construction.
//! This native check gives an early error but does not provide verifier soundness.

use serde::{Deserialize, Serialize};
use std::fmt;

use stwo::core::{
    air::Component,
    channel::Channel,
    fields::{m31::M31, qm31::SecureField},
    pcs::TreeVec,
    ColumnVec,
};
use stwo::prover::{
    backend::simd::{
        m31::{PackedM31, LOG_N_LANES},
        qm31::PackedQM31,
        SimdBackend,
    },
    ComponentProver,
};
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator,
};
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};
use stwo_p256_utils::scalar_arithmetic::{words_to_limbs, P256_ORDER};

use crate::limbs::{P256BigInt, P256M31BigInt};
use crate::range_checks::write_batched_logup_columns;
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};

use crate::final_add_air::FinalAddSignRelation;
use crate::scalar::cert_bind::{
    CertScalarInputClaim, CertScalarInputRelation, CertScalarInputRow,
    CERT_SCALAR_INPUT_RELATION_ARITY,
};
use crate::scalar::scalar_mod_mul::relation::ScalarLimbRelation;
// Role constants for the `ScalarLimbRelation` tuples emitted by the
// `FakeGlvScalarAirEval` provider (see `add_scalar_mod_mul_limb_links` below).
// The matching consumer rows are built in `proof.rs::fake_glv_scalar_mod_mul_rows`.
use crate::scalar::scalar_mod_mul::{ROLE_A, ROLE_B, ROLE_QUOTIENT, ROLE_RESULT};

/// Mul-ID namespace base for fake-GLV scalar-mod-mul rows. Disjoint from the
/// scalar-setup mod-mul IDs (which live in `[0, 2 · num_signatures)`).
/// Each active fake-GLV cert produces one mul-row at
/// `FAKE_GLV_SCALAR_MUL_ID_BASE + 2 · sig_id + cert_id`.
pub const FAKE_GLV_SCALAR_MUL_ID_BASE: u32 = 1_000_000;

pub const FAKE_GLV_SMALL_LIMBS: usize = 10;
pub const FAKE_GLV_TOP_LIMB_BITS: u32 = 11;
pub const FAKE_GLV_SCALAR_RELATION_ARITY: usize = 2 + 2 * FAKE_GLV_SMALL_LIMBS + 2;

relation!(FakeGlvScalarRelation, FAKE_GLV_SCALAR_RELATION_ARITY);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FakeGlvScalarHintClaim {
    pub rows: Vec<FakeGlvScalarHintRow>,
}

impl FakeGlvScalarHintClaim {
    pub fn from_cert_inputs(
        certs: &CertScalarInputClaim,
        hints: Vec<FakeGlvScalarHint>,
    ) -> Result<Self, FakeGlvScalarHintError> {
        if certs.rows.len() != hints.len() {
            return Err(FakeGlvScalarHintError::HintCountMismatch {
                cert_rows: certs.rows.len(),
                hints: hints.len(),
            });
        }
        let rows = certs
            .rows
            .iter()
            .zip(hints)
            .map(|(cert, hint)| FakeGlvScalarHintRow::new(cert, hint))
            .collect::<Vec<_>>();
        let claim = Self { rows };
        claim.verify()?;
        Ok(claim)
    }

    pub fn verify(&self) -> Result<(), FakeGlvScalarHintError> {
        for row in &self.rows {
            row.verify()?;
        }
        Ok(())
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.rows.len() as u64);
        for row in &self.rows {
            channel.mix_u64(row.sig_id.0 as u64);
            channel.mix_u64(row.cert_id.0 as u64);
        }
    }
}

pub type FakeGlvScalarAirComponent = FrameworkComponent<FakeGlvScalarAirEval>;

pub const FAKE_GLV_SCALAR_TRACE_COLUMNS: usize =
    1 + CERT_SCALAR_INPUT_RELATION_ARITY + FAKE_GLV_SCALAR_ROW_COLUMNS;
/// Trace columns per `FakeGlvScalarAirRow`:
/// - `sig_id`, `cert_id`, `cert_active`, `cert_zero_active`             (4)
/// - `scalar` (full 256-bit cert scalar, in `N_LIMBS` 13-bit limbs)
/// - `s1`, `s2_abs`                                                     (2 · FAKE_GLV_SMALL_LIMBS)
/// - `s2_sign_bit`                                                      (1)
/// - `q`                                                                (FAKE_GLV_SMALL_LIMBS)
/// - `active_bit` = `cert_active · s2_sign_bit`                         (1)
/// - `selected_s1` ≡ `k · s2_abs (mod n)` in `N_LIMBS` 13-bit limbs     (N_LIMBS)
/// - `selected_borrow` chain for the `n − s1` branch                    (N_LIMBS − 1)
const FAKE_GLV_SCALAR_ROW_COLUMNS: usize = 4
    + N_LIMBS
    + 2 * FAKE_GLV_SMALL_LIMBS
    + 1
    + FAKE_GLV_SMALL_LIMBS
    + 1
    + N_LIMBS
    + (N_LIMBS - 1)
    // s2_abs_inv: witnessed inverse for the Garaga `s2_abs != 0` check.
    + 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FakeGlvScalarAirProofClaim {
    pub log_size: u32,
}

impl FakeGlvScalarAirProofClaim {
    pub fn from_claim(claim: &FakeGlvScalarHintClaim) -> Self {
        Self {
            log_size: padded_log_size(claim.rows.len()),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FakeGlvScalarAirInteractionClaim {
    pub claimed_sum: SecureField,
}

impl FakeGlvScalarAirInteractionClaim {
    pub fn zero() -> Self {
        Self {
            claimed_sum: secure_zero(),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}

pub struct FakeGlvScalarAirComponents {
    pub scalar: FakeGlvScalarAirComponent,
}

impl FakeGlvScalarAirComponents {
    pub(crate) fn new(
        allocator: &mut TraceLocationAllocator,
        claim: FakeGlvScalarAirProofClaim,
        interaction_claim: &FakeGlvScalarAirInteractionClaim,
        cert_relation: &CertScalarInputRelation,
        scalar_relation: &FakeGlvScalarRelation,
        scalar_limb_relation: &ScalarLimbRelation,
        sign_relation: &FinalAddSignRelation,
    ) -> Self {
        Self {
            scalar: FakeGlvScalarAirComponent::new(
                allocator,
                FakeGlvScalarAirEval {
                    log_size: claim.log_size,
                    cert_relation: cert_relation.clone(),
                    scalar_relation: scalar_relation.clone(),
                    scalar_limb_relation: scalar_limb_relation.clone(),
                    sign_relation: sign_relation.clone(),
                },
                interaction_claim.claimed_sum,
            ),
        }
    }

    pub fn components(&self) -> Vec<&dyn Component> {
        vec![&self.scalar as &dyn Component]
    }

    pub fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![&self.scalar as &dyn ComponentProver<SimdBackend>]
    }

    pub fn trace_log_degree_bounds(&self) -> TreeVec<ColumnVec<u32>> {
        self.scalar.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self) -> u32 {
        self.scalar.max_constraint_log_degree_bound()
    }
}

#[derive(Clone)]
pub struct FakeGlvScalarAirEval {
    pub log_size: u32,
    pub cert_relation: CertScalarInputRelation,
    pub scalar_relation: FakeGlvScalarRelation,
    /// External-limb provider relation feeding `(mul_id, role, limb_index,
    /// limb_value)` tuples into each active cert's `ScalarModMul`
    /// component, where `mul_id = FAKE_GLV_SCALAR_MUL_ID_BASE + 2 · sig_id
    ///   + cert_id`. Closes the `scalar · s2_abs ≡ selected_s1 (mod n)`
    ///     algebraic identity in-AIR.
    pub scalar_limb_relation: ScalarLimbRelation,
    /// Provider relation forwarding each cert's PROVEN `s2_sign_bit` to the
    /// final-add sub-graph (consumer: `FinalAddCheckEval`).
    pub sign_relation: FinalAddSignRelation,
}

impl FrameworkEval for FakeGlvScalarAirEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.next_trace_mask();
        let cert = read_cert_relation_values(&mut eval);
        let row = FakeGlvScalarAirRow::read(&mut eval);
        let one = E::F::from(M31::from_u32_unchecked(1));

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        for value in cert.iter().cloned().chain(row.values()) {
            eval.add_constraint((one.clone() - active.clone()) * value);
        }
        eval.add_to_relation(RelationEntry::base(
            &self.cert_relation,
            active.clone(),
            &cert,
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.scalar_relation,
            -active.clone(),
            &scalar_relation_eval_values(&row),
        ));
        // Yield each active cert's PROVEN s2_sign_bit to the final-add sub-graph
        // (consumer: FinalAddCheckEval). Numerator `-cert_active`: only active
        // certs contribute (zero/inactive certs and padding yield nothing). MUST
        // mirror the interaction-trace column order (right after the scalar
        // provide, before the scalar-mod-mul limb links).
        eval.add_to_relation(RelationEntry::base(
            &self.sign_relation,
            -(row.cert_active.clone()),
            &[
                row.sig_id.clone(),
                row.cert_id.clone(),
                row.s2_sign_bit.clone(),
            ],
        ));
        add_scalar_mod_mul_limb_links(&mut eval, &self.scalar_limb_relation, &row);
        constrain_fake_glv_scalar_general(&mut eval, active, &cert, &row);
        eval.finalize_logup_in_pairs();
        eval
    }
}

/// Provider yields into the per-cert `ScalarModMul` external-limb relation.
/// For each active cert (gated by `row.cert_active`), emits 4 · `N_LIMBS`
/// `(mul_id, role, limb_index, limb_value)` tuples with `mul_id =
/// FAKE_GLV_SCALAR_MUL_ID_BASE + 2 · sig_id + cert_id`:
///   - Role A   ⇒ full 256-bit `scalar` (N_LIMBS limbs)
///   - Role B   ⇒ `s2_abs` for limbs `0..FAKE_GLV_SMALL_LIMBS`, zero above
///   - Role Q   ⇒ `q` for limbs `0..FAKE_GLV_SMALL_LIMBS`, zero above
///   - Role R   ⇒ `selected_s1` (full N_LIMBS, holds canonical residue mod n)
///
/// On padding rows `cert_active == 0` so no tuple contributes. The numerator
/// polarity (`+cert_active`) mirrors `setup_air::add_scalar_limb_link` so the
/// matching `ScalarModMul` consumer (negative numerator) cancels.
fn add_scalar_mod_mul_limb_links<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarLimbRelation,
    row: &FakeGlvScalarAirRow<E::F>,
) {
    let zero = E::F::from(M31::from_u32_unchecked(0));
    let base = E::F::from(M31::from_u32_unchecked(FAKE_GLV_SCALAR_MUL_ID_BASE));
    let two = E::F::from(M31::from_u32_unchecked(2));
    let mul_id = base + two * row.sig_id.clone() + row.cert_id.clone();
    let numerator = row.cert_active.clone();
    for limb in 0..N_LIMBS {
        emit_scalar_limb_link(
            eval,
            relation,
            numerator.clone(),
            mul_id.clone(),
            ROLE_A,
            limb,
            row.scalar.limbs()[limb].clone(),
        );
        let b_value = if limb < FAKE_GLV_SMALL_LIMBS {
            row.s2_abs[limb].clone()
        } else {
            zero.clone()
        };
        emit_scalar_limb_link(
            eval,
            relation,
            numerator.clone(),
            mul_id.clone(),
            ROLE_B,
            limb,
            b_value,
        );
        let q_value = if limb < FAKE_GLV_SMALL_LIMBS {
            row.q[limb].clone()
        } else {
            zero.clone()
        };
        emit_scalar_limb_link(
            eval,
            relation,
            numerator.clone(),
            mul_id.clone(),
            ROLE_QUOTIENT,
            limb,
            q_value,
        );
        emit_scalar_limb_link(
            eval,
            relation,
            numerator.clone(),
            mul_id.clone(),
            ROLE_RESULT,
            limb,
            row.selected_s1[limb].clone(),
        );
    }
}

fn emit_scalar_limb_link<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarLimbRelation,
    numerator: E::F,
    mul_id: E::F,
    role: u32,
    limb: usize,
    value: E::F,
) {
    eval.add_to_relation(RelationEntry::base(
        relation,
        numerator,
        &[
            mul_id,
            E::F::from(M31::from_u32_unchecked(role)),
            E::F::from(M31::from_u32_unchecked(limb as u32)),
            value,
        ],
    ));
}

fn scalar_relation_eval_values<F: Clone>(
    row: &FakeGlvScalarAirRow<F>,
) -> [F; FAKE_GLV_SCALAR_RELATION_ARITY] {
    let mut values = Vec::with_capacity(FAKE_GLV_SCALAR_RELATION_ARITY);
    values.push(row.sig_id.clone());
    values.push(row.cert_id.clone());
    values.extend(row.s1.iter().cloned());
    values.extend(row.s2_abs.iter().cloned());
    values.push(row.s2_sign_bit.clone());
    values.push(row.cert_active.clone());
    values
        .try_into()
        .unwrap_or_else(|_| panic!("scalar relation arity mismatch"))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FakeGlvScalarHintRow {
    pub sig_id: M31,
    pub cert_id: M31,
    pub cert_active: M31,
    pub cert_zero_active: M31,
    pub scalar: P256M31BigInt,
    pub hint: FakeGlvScalarHint,
}

impl FakeGlvScalarHintRow {
    pub fn new(cert: &CertScalarInputRow, hint: FakeGlvScalarHint) -> Self {
        Self {
            sig_id: cert.sig_id,
            cert_id: cert.cert_id,
            cert_active: cert.cert_active,
            cert_zero_active: cert.cert_zero_active,
            scalar: cert.scalar.clone(),
            hint,
        }
    }

    pub fn verify(&self) -> Result<(), FakeGlvScalarHintError> {
        require_bool("cert_active", self.cert_active)?;
        require_bool("cert_zero_active", self.cert_zero_active)?;
        require_bool("s2_sign_bit", self.hint.s2_sign_bit)?;
        self.hint.s1.require_128_bit_bound("s1")?;
        self.hint.s2_abs.require_128_bit_bound("s2_abs")?;
        self.hint.q.require_128_bit_bound("q")?;

        if self.cert_active.0 == 0 {
            if self.hint.is_zero() {
                return Ok(());
            }
            return Err(FakeGlvScalarHintError::InactiveHintNonZero {
                sig_id: self.sig_id.0,
                cert_id: self.cert_id.0,
            });
        }

        if self.hint.s1.is_zero() {
            return Err(FakeGlvScalarHintError::ZeroSmallScalar { field: "s1" });
        }
        if self.hint.s2_abs.is_zero() {
            return Err(FakeGlvScalarHintError::ZeroSmallScalar { field: "s2_abs" });
        }
        verify_scalar_equation(&self.scalar, &self.hint)
    }
}

#[derive(Clone)]
struct FakeGlvScalarAirRow<F> {
    sig_id: F,
    cert_id: F,
    cert_active: F,
    cert_zero_active: F,
    scalar: P256BigInt<F>,
    s1: [F; FAKE_GLV_SMALL_LIMBS],
    s2_abs: [F; FAKE_GLV_SMALL_LIMBS],
    s2_sign_bit: F,
    q: [F; FAKE_GLV_SMALL_LIMBS],
    /// `cert_active · s2_sign_bit` — witnessed to keep the
    /// `selected_s1 = ±s1 mod n` selector at degree 2.
    active_bit: F,
    /// Canonical positive residue of `±s1 (mod n)`.
    ///
    /// `ScalarModMul` consumes this value as `Result`.
    /// The sign convention is:
    /// `bit = 1 ⇒ selected_s1 = s1`. `bit = 0 ⇒ selected_s1 = n − s1`.
    selected_s1: [F; N_LIMBS],
    /// Borrow chain witnessing the `n − s1` subtraction limb-by-limb when
    /// `bit = 0`. `selected_borrow[i]` is the borrow OUT of limb `i`. The
    /// top borrow (`selected_borrow[N_LIMBS − 1]`) is implicitly zero
    /// because `n − s1 ∈ [1, n)` fits in `N_LIMBS` limbs, so we only
    /// witness `N_LIMBS − 1` cells. When `bit = 1` these are all zero.
    selected_borrow: [F; N_LIMBS - 1],
    /// Witnessed inverse of the `s2_abs` limb sum: proves `s2_abs != 0` on the
    /// nonzero branch (Garaga `assert(_s2_abs != 0)`, ec_ops.cairo:254). Zero on
    /// the zero / inactive branch.
    s2_abs_inv: F,
}

impl<F: Clone> FakeGlvScalarAirRow<F> {
    fn values(&self) -> Vec<F> {
        let mut values = Vec::with_capacity(FAKE_GLV_SCALAR_ROW_COLUMNS);
        values.push(self.sig_id.clone());
        values.push(self.cert_id.clone());
        values.push(self.cert_active.clone());
        values.push(self.cert_zero_active.clone());
        values.extend(self.scalar.limbs().iter().cloned());
        values.extend(self.s1.iter().cloned());
        values.extend(self.s2_abs.iter().cloned());
        values.push(self.s2_sign_bit.clone());
        values.extend(self.q.iter().cloned());
        values.push(self.active_bit.clone());
        values.extend(self.selected_s1.iter().cloned());
        values.extend(self.selected_borrow.iter().cloned());
        values.push(self.s2_abs_inv.clone());
        values
    }
}

impl<F> FakeGlvScalarAirRow<F> {
    fn read<E: EvalAtRow<F = F>>(eval: &mut E) -> Self {
        Self {
            sig_id: eval.next_trace_mask(),
            cert_id: eval.next_trace_mask(),
            cert_active: eval.next_trace_mask(),
            cert_zero_active: eval.next_trace_mask(),
            scalar: P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask())),
            s1: core::array::from_fn(|_| eval.next_trace_mask()),
            s2_abs: core::array::from_fn(|_| eval.next_trace_mask()),
            s2_sign_bit: eval.next_trace_mask(),
            q: core::array::from_fn(|_| eval.next_trace_mask()),
            active_bit: eval.next_trace_mask(),
            selected_s1: core::array::from_fn(|_| eval.next_trace_mask()),
            selected_borrow: core::array::from_fn(|_| eval.next_trace_mask()),
            s2_abs_inv: eval.next_trace_mask(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FakeGlvScalarHint {
    pub s1: FakeGlvSmallScalar,
    pub s2_abs: FakeGlvSmallScalar,
    pub s2_sign_bit: M31,
    pub q: FakeGlvSmallScalar,
}

impl FakeGlvScalarHint {
    pub const fn zero() -> Self {
        Self {
            s1: FakeGlvSmallScalar::zero(),
            s2_abs: FakeGlvSmallScalar::zero(),
            s2_sign_bit: M31::from_u32_unchecked(0),
            q: FakeGlvSmallScalar::zero(),
        }
    }

    pub fn trivial_for_small_scalar(
        scalar: &P256M31BigInt,
    ) -> Result<Self, FakeGlvScalarHintError> {
        let s = FakeGlvSmallScalar::from_p256_if_128_bit(scalar)
            .ok_or(FakeGlvScalarHintError::ScalarDoesNotFitTrivialHint)?;
        if s.is_zero() {
            return Ok(Self::zero());
        }
        Ok(Self {
            s1: s,
            s2_abs: FakeGlvSmallScalar::one(),
            s2_sign_bit: M31::from_u32_unchecked(1),
            q: FakeGlvSmallScalar::zero(),
        })
    }

    /// Builds a bounded fake-GLV hint for a scalar in `[0, n)`.
    ///
    /// The function uses Garaga `precompute_lattice`.
    ///
    /// Returns [`FakeGlvScalarHintError::ScalarDoesNotFitTrivialHint`] for an invalid decomposition.
    /// Each value in `(s1, s2_abs, q)` must be less than `2^128`.
    pub fn decompose(scalar: &P256M31BigInt) -> Result<Self, FakeGlvScalarHintError> {
        use crate::scalar::fake_glv_decompose::decompose_scalar_mod_n;
        let decomposition = decompose_scalar_mod_n(&scalar.to_u256())
            .ok_or(FakeGlvScalarHintError::ScalarDoesNotFitTrivialHint)?;
        Ok(Self {
            s1: FakeGlvSmallScalar::from_p256_if_128_bit(&P256M31BigInt::from_u256(
                &decomposition.s1,
            ))
            .ok_or(FakeGlvScalarHintError::ScalarDoesNotFitTrivialHint)?,
            s2_abs: FakeGlvSmallScalar::from_p256_if_128_bit(&P256M31BigInt::from_u256(
                &decomposition.s2_abs,
            ))
            .ok_or(FakeGlvScalarHintError::ScalarDoesNotFitTrivialHint)?,
            s2_sign_bit: M31::from_u32_unchecked(decomposition.s2_sign_bit as u32),
            q: FakeGlvSmallScalar::from_p256_if_128_bit(&P256M31BigInt::from_u256(
                &decomposition.q,
            ))
            .ok_or(FakeGlvScalarHintError::ScalarDoesNotFitTrivialHint)?,
        })
    }

    fn is_zero(&self) -> bool {
        self.s1.is_zero() && self.s2_abs.is_zero() && self.s2_sign_bit.0 == 0 && self.q.is_zero()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FakeGlvSmallScalar {
    pub limbs: [M31; FAKE_GLV_SMALL_LIMBS],
}

impl FakeGlvSmallScalar {
    pub const fn zero() -> Self {
        Self {
            limbs: [M31::from_u32_unchecked(0); FAKE_GLV_SMALL_LIMBS],
        }
    }

    pub fn one() -> Self {
        let mut scalar = Self::zero();
        scalar.limbs[0] = M31::from_u32_unchecked(1);
        scalar
    }

    pub fn from_u64(value: u64) -> Self {
        let p256 = P256M31BigInt::from_u256(&crate::types::U256::from_le_u64s(&[value, 0, 0, 0]));
        Self::from_p256_if_128_bit(&p256).expect("u64 fits in fake-GLV small scalar")
    }

    pub fn from_p256_if_128_bit(value: &P256M31BigInt) -> Option<Self> {
        let limbs = value.limbs();
        let upper_zero = limbs[FAKE_GLV_SMALL_LIMBS..].iter().all(|limb| limb.0 == 0);
        let top_fits = limbs[FAKE_GLV_SMALL_LIMBS - 1].0 < (1 << FAKE_GLV_TOP_LIMB_BITS);
        (upper_zero && top_fits).then(|| Self {
            limbs: limbs[..FAKE_GLV_SMALL_LIMBS]
                .try_into()
                .expect("fixed slice length"),
        })
    }

    pub fn is_zero(&self) -> bool {
        self.limbs.iter().all(|limb| limb.0 == 0)
    }

    /// Convert to `[u64; 4]` little-endian word layout used by
    /// `ScalarFieldMulTrace::new`. Lifts the 10 13-bit limbs (≤ 2^130 raw
    /// shape, ≤ 2^128 after `require_128_bit_bound`) into the full 256-bit
    /// representation by zero-padding the upper words.
    /// Free-function alias: [`fake_glv_small_to_le_u64s`].
    pub fn to_le_u64s(&self) -> [u64; 4] {
        let mut value: u128 = 0;
        for (i, limb) in self.limbs.iter().enumerate() {
            value |= (u128::from(limb.0)) << (i * LIMB_BITS);
        }
        [value as u64, (value >> 64) as u64, 0, 0]
    }
}

/// Free-function alias for [`FakeGlvSmallScalar::to_le_u64s`], for callers
/// that prefer the standalone form.
pub fn fake_glv_small_to_le_u64s(value: &FakeGlvSmallScalar) -> [u64; 4] {
    value.to_le_u64s()
}

impl FakeGlvSmallScalar {
    fn require_128_bit_bound(self, field: &'static str) -> Result<(), FakeGlvScalarHintError> {
        for (index, limb) in self.limbs.iter().enumerate() {
            let bound = if index == FAKE_GLV_SMALL_LIMBS - 1 {
                1 << FAKE_GLV_TOP_LIMB_BITS
            } else {
                1 << LIMB_BITS
            };
            if limb.0 >= bound {
                return Err(FakeGlvScalarHintError::SmallScalarOutOfRange {
                    field,
                    limb: index,
                    value: limb.0,
                    bound,
                });
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FakeGlvScalarHintError {
    HintCountMismatch {
        cert_rows: usize,
        hints: usize,
    },
    NonBooleanFlag {
        field: &'static str,
        actual: u32,
    },
    SmallScalarOutOfRange {
        field: &'static str,
        limb: usize,
        value: u32,
        bound: u32,
    },
    ZeroSmallScalar {
        field: &'static str,
    },
    InactiveHintNonZero {
        sig_id: u32,
        cert_id: u32,
    },
    ScalarDoesNotFitTrivialHint,
    ScalarEquationMismatch {
        digit: usize,
        residue: i128,
    },
    ScalarEquationCarryMismatch {
        carry: i128,
    },
}

impl fmt::Display for FakeGlvScalarHintError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::HintCountMismatch { cert_rows, hints } => write!(
                f,
                "fake-GLV hint count mismatch: {cert_rows} cert rows, {hints} hints"
            ),
            Self::NonBooleanFlag { field, actual } => {
                write!(f, "fake-GLV flag {field} must be boolean, got {actual}")
            }
            Self::SmallScalarOutOfRange {
                field,
                limb,
                value,
                bound,
            } => write!(
                f,
                "fake-GLV scalar {field}[{limb}] out of range: value {value}, bound {bound}"
            ),
            Self::ZeroSmallScalar { field } => {
                write!(f, "fake-GLV nonzero branch requires {field} > 0")
            }
            Self::InactiveHintNonZero { sig_id, cert_id } => write!(
                f,
                "inactive fake-GLV hint for signature {sig_id}, certificate {cert_id} must be zero"
            ),
            Self::ScalarDoesNotFitTrivialHint => write!(
                f,
                "scalar does not fit the trivial fake-GLV small-scalar hint"
            ),
            Self::ScalarEquationMismatch { digit, residue } => write!(
                f,
                "fake-GLV scalar equation has nonzero residue {residue} at digit {digit}"
            ),
            Self::ScalarEquationCarryMismatch { carry } => write!(
                f,
                "fake-GLV scalar equation ended with nonzero carry {carry}"
            ),
        }
    }
}

impl std::error::Error for FakeGlvScalarHintError {}

pub fn gen_fake_glv_scalar_air_base_trace(
    certs: &CertScalarInputClaim,
    scalars: &FakeGlvScalarHintClaim,
    proof_claim: FakeGlvScalarAirProofClaim,
) -> ColumnVec<M31ColumnEval> {
    let row_count = 1usize << proof_claim.log_size;
    assert!(scalars.rows.len() <= row_count);
    assert_eq!(certs.rows.len(), scalars.rows.len());
    let mut columns =
        vec![vec![M31::from_u32_unchecked(0); row_count]; FAKE_GLV_SCALAR_TRACE_COLUMNS];
    for (row_index, (cert, scalar)) in certs.rows.iter().zip(&scalars.rows).enumerate() {
        let mut offset = 0usize;
        columns[offset][row_index] = M31::from_u32_unchecked(1);
        offset += 1;
        write_cert_relation_values(&mut columns, &mut offset, cert, row_index);
        write_fake_glv_scalar_row(&mut columns, &mut offset, scalar, row_index);
        debug_assert_eq!(offset, FAKE_GLV_SCALAR_TRACE_COLUMNS);
    }
    columns
        .into_iter()
        .map(|values| m31_column_eval(proof_claim.log_size, values))
        .collect()
}

pub(crate) fn gen_fake_glv_scalar_air_interaction_trace(
    base: &[M31ColumnEval],
    cert_relation: &CertScalarInputRelation,
    scalar_relation: &FakeGlvScalarRelation,
    scalar_limb_relation: &ScalarLimbRelation,
    sign_relation: &FinalAddSignRelation,
) -> (ColumnVec<M31ColumnEval>, FakeGlvScalarAirInteractionClaim) {
    assert_eq!(base.len(), FAKE_GLV_SCALAR_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let vec_rows = 1 << (log_size - LOG_N_LANES);
    let mut entries = Vec::new();

    append_relation_entry(&mut entries, vec_rows, |vec_row| {
        (
            PackedQM31::from(base[0].data[vec_row]),
            cert_relation.combine(&cert_packed_values_from_base(base, vec_row)),
        )
    });
    append_relation_entry(&mut entries, vec_rows, |vec_row| {
        (
            -PackedQM31::from(base[0].data[vec_row]),
            scalar_relation.combine(&scalar_packed_values_from_base(base, vec_row)),
        )
    });

    // Sign-bit provider column: yield each active cert's s2_sign_bit to the
    // final-add sub-graph. Numerator `-cert_active`. Tuple (sig_id, cert_id,
    // s2_sign_bit) read from the scalar relation packed values (positions 0, 1,
    // and 2 + 2·FAKE_GLV_SMALL_LIMBS). MUST mirror the AIR-eval emission order
    // (right after the scalar provide).
    append_relation_entry(&mut entries, vec_rows, |vec_row| {
        let scalar_vals = scalar_packed_values_from_base(base, vec_row);
        let sign_tuple = [
            scalar_vals[0],
            scalar_vals[1],
            scalar_vals[2 + 2 * FAKE_GLV_SMALL_LIMBS],
        ];
        (
            -PackedQM31::from(base[SCALAR_ROW_CERT_ACTIVE].data[vec_row]),
            sign_relation.combine(&sign_tuple),
        )
    });

    // Per-(role, limb) ScalarModMul external-limb provider columns. Numerator
    // is `cert_active` (not the storage flag), mirroring
    // `add_scalar_mod_mul_limb_links` in the AIR-eval. Order MUST match the
    // AIR-eval's `add_to_relation` order: for each limb in `0..N_LIMBS`, emit
    // tuples in the order (A, B, Quotient, Result).
    for limb in 0..N_LIMBS {
        for role_value_col in scalar_mod_mul_limb_value_columns(limb) {
            let (role, value_col) = role_value_col;
            append_scalar_mod_mul_limb_entry(
                &mut entries,
                base,
                scalar_limb_relation,
                role,
                limb,
                value_col,
            );
        }
    }

    let mut logup = LogupTraceGenerator::new(log_size);
    write_batched_logup_columns(&mut logup, &entries, 2);
    let (trace, claimed_sum) = logup.finalize_last();
    (trace, FakeGlvScalarAirInteractionClaim { claimed_sum })
}

/// Returns provider column tuples for one limb.
///
/// The AIR and interaction generator use the same tuple order.
/// Roles B and Quotient use zero above `FAKE_GLV_SMALL_LIMBS`.
/// `SCALAR_ROW_ZERO_PAD_COL` selects an explicit zero value.
fn scalar_mod_mul_limb_value_columns(limb: usize) -> [(u32, usize); 4] {
    let b_col = if limb < FAKE_GLV_SMALL_LIMBS {
        SCALAR_ROW_S2_ABS_START + limb
    } else {
        SCALAR_ROW_ZERO_PAD_COL
    };
    let q_col = if limb < FAKE_GLV_SMALL_LIMBS {
        SCALAR_ROW_Q_START + limb
    } else {
        SCALAR_ROW_ZERO_PAD_COL
    };
    [
        (ROLE_A, SCALAR_ROW_SCALAR_START + limb),
        (ROLE_B, b_col),
        (ROLE_QUOTIENT, q_col),
        (ROLE_RESULT, SCALAR_ROW_SELECTED_S1_START + limb),
    ]
}

type LogupEntry = (Vec<PackedQM31>, Vec<PackedQM31>);

fn append_relation_entry(
    entries: &mut Vec<LogupEntry>,
    vec_rows: usize,
    fraction: impl Fn(usize) -> (PackedQM31, PackedQM31),
) {
    let mut numerators = Vec::with_capacity(vec_rows);
    let mut denominators = Vec::with_capacity(vec_rows);
    for vec_row in 0..vec_rows {
        let (numerator, denominator) = fraction(vec_row);
        numerators.push(numerator);
        denominators.push(denominator);
    }
    entries.push((numerators, denominators));
}

fn append_scalar_mod_mul_limb_entry(
    entries: &mut Vec<LogupEntry>,
    base: &[M31ColumnEval],
    relation: &ScalarLimbRelation,
    role: u32,
    limb: usize,
    value_col: usize,
) {
    let log_size = base[0].domain.log_size();
    let vec_rows = 1 << (log_size - LOG_N_LANES);
    let role_packed = PackedM31::from(M31::from_u32_unchecked(role));
    let limb_packed = PackedM31::from(M31::from_u32_unchecked(limb as u32));
    let zero_packed = PackedM31::from(M31::from_u32_unchecked(0));
    append_relation_entry(entries, vec_rows, |vec_row| {
        let mul_id = scalar_mod_mul_mul_id_packed(base, vec_row);
        let value = if value_col == SCALAR_ROW_ZERO_PAD_COL {
            zero_packed
        } else {
            base[value_col].data[vec_row]
        };
        let denom = relation.combine(&[mul_id, role_packed, limb_packed, value]);
        let numerator = PackedQM31::from(base[SCALAR_ROW_CERT_ACTIVE].data[vec_row]);
        (numerator, denom)
    });
}

fn scalar_mod_mul_mul_id_packed(base: &[M31ColumnEval], vec_row: usize) -> PackedM31 {
    let base_m31 = PackedM31::from(M31::from_u32_unchecked(FAKE_GLV_SCALAR_MUL_ID_BASE));
    let two = PackedM31::from(M31::from_u32_unchecked(2));
    base_m31 + two * base[SCALAR_ROW_SIG_ID].data[vec_row] + base[SCALAR_ROW_CERT_ID].data[vec_row]
}

/// Verify the unified scalar equation
/// ```text
///     scalar · s2_abs − q · n − selected_s1 = 0   (over Z)
/// ```
/// Use `selected_s1 = s1` when `s2_sign_bit == 1`.
/// Use `selected_s1 = n − s1` when `s2_sign_bit == 0`.
/// This exactly matches ScalarModMul's `A · B = Q · n + R` equation.
/// Here, `A = scalar`, `B = s2_abs`, `Q = q`, and `R = selected_s1`.
/// Therefore, the AIR-provided `q` limbs balance the external limbs consumed by
/// the per-certificate ScalarModMul component.
fn verify_scalar_equation(
    scalar: &P256M31BigInt,
    hint: &FakeGlvScalarHint,
) -> Result<(), FakeGlvScalarHintError> {
    const EQUATION_LIMBS: usize = N_LIMBS + FAKE_GLV_SMALL_LIMBS;
    let mut coeffs = [0i128; EQUATION_LIMBS];
    let n = words_to_limbs(&P256_ORDER);

    // + scalar · s2_abs
    for (i, scalar_limb) in scalar.limbs().iter().enumerate() {
        for j in 0..FAKE_GLV_SMALL_LIMBS {
            coeffs[i + j] += scalar_limb.0 as i128 * hint.s2_abs.limbs[j].0 as i128;
        }
    }

    // − n · q
    for (i, n_limb) in n.iter().enumerate() {
        for j in 0..FAKE_GLV_SMALL_LIMBS {
            coeffs[i + j] -= *n_limb as i128 * hint.q.limbs[j].0 as i128;
        }
    }

    // − selected_s1, where selected_s1 = (bit == 1 ? s1 : n − s1).
    // bit = 1: subtract s1 limb-wise (only the lower FAKE_GLV_SMALL_LIMBS).
    // bit = 0: subtract (n − s1) limb-wise, i.e. −n + s1.
    if hint.s2_sign_bit.0 == 1 {
        for (coeff, s1_limb) in coeffs
            .iter_mut()
            .zip(hint.s1.limbs)
            .take(FAKE_GLV_SMALL_LIMBS)
        {
            *coeff -= s1_limb.0 as i128;
        }
    } else {
        // − (n − s1) = −n + s1: subtract n's full N_LIMBS span, then add s1
        // limbs back over the FAKE_GLV_SMALL_LIMBS span.
        for (coeff, n_limb) in coeffs.iter_mut().zip(n.iter()).take(N_LIMBS) {
            *coeff -= *n_limb as i128;
        }
        for (coeff, s1_limb) in coeffs
            .iter_mut()
            .zip(hint.s1.limbs)
            .take(FAKE_GLV_SMALL_LIMBS)
        {
            *coeff += s1_limb.0 as i128;
        }
    }

    let base = 1i128 << LIMB_BITS;
    let mut carry = 0i128;
    for (digit, coeff) in coeffs.into_iter().enumerate() {
        let total = coeff + carry;
        let residue = total.rem_euclid(base);
        if residue != 0 {
            return Err(FakeGlvScalarHintError::ScalarEquationMismatch { digit, residue });
        }
        carry = total.div_euclid(base);
    }
    if carry != 0 {
        return Err(FakeGlvScalarHintError::ScalarEquationCarryMismatch { carry });
    }
    Ok(())
}

fn require_bool(field: &'static str, value: M31) -> Result<(), FakeGlvScalarHintError> {
    if value.0 <= 1 {
        return Ok(());
    }
    Err(FakeGlvScalarHintError::NonBooleanFlag {
        field,
        actual: value.0,
    })
}

fn read_cert_relation_values<E: EvalAtRow>(
    eval: &mut E,
) -> [E::F; CERT_SCALAR_INPUT_RELATION_ARITY] {
    core::array::from_fn(|_| eval.next_trace_mask())
}

/// General fake-GLV scalar AIR constraint. Replaces
/// `constrain_fake_glv_scalar_trivial`.
///
/// Proves, for each active row, the eu-id-form fake-GLV identity
/// ```text
///     k · s2_abs − q · n ± s1 = 0  (over Z)
/// ```
/// where the sign is `+` when `s2_sign_bit = 0` (Garaga `s2_signed = +s2_abs`)
/// and `−` when `s2_sign_bit = 1` (Garaga `s2_signed = −s2_abs`).
///
/// An external `ScalarModMul` component proves the algebraic multiplication.
/// This helper:
/// 1. Bind cert/flags/scalar/zero-active hint to existing trace cells.
/// 2. Witness `selected_s1 ≡ k · s2_abs (mod n)` as the canonical positive
///    residue in `[0, n)`, with the correct sign-dependent value:
///    `bit = 1 ⇒ selected_s1 = s1`
///    `bit = 0 ⇒ selected_s1 = n − s1`
/// 3. Constrain `selected_s1` against `(s1, s2_sign_bit, n)` so that an
///    adversary cannot decouple it from the witnessed hint.
///
/// `ScalarModMul` receives `selected_s1` as `Result`.
/// It receives `scalar` as `A`, `s2_abs` as `B`, and `q` as `Quotient`.
fn constrain_fake_glv_scalar_general<E: EvalAtRow>(
    eval: &mut E,
    active: E::F,
    cert: &[E::F; CERT_SCALAR_INPUT_RELATION_ARITY],
    row: &FakeGlvScalarAirRow<E::F>,
) {
    let zero = E::F::from(M31::from_u32_unchecked(0));
    let one = E::F::from(M31::from_u32_unchecked(1));
    let base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    let cert_scalar_start = 2;
    let cert_active = cert[2 + 3 * N_LIMBS + 3].clone();
    let cert_zero_active = cert[2 + 3 * N_LIMBS + 4].clone();

    // (1) Cert and flag bindings (unchanged from the trivial helper, plus
    //     boolean constraints for the new `active_bit` and `selected_borrow`).
    eval.add_constraint(active.clone() * (row.sig_id.clone() - cert[0].clone()));
    eval.add_constraint(active.clone() * (row.cert_id.clone() - cert[1].clone()));
    eval.add_constraint(active.clone() * (row.cert_active.clone() - cert_active.clone()));
    eval.add_constraint(active.clone() * (row.cert_zero_active.clone() - cert_zero_active.clone()));
    for flag in [
        row.cert_active.clone(),
        row.cert_zero_active.clone(),
        row.s2_sign_bit.clone(),
        row.active_bit.clone(),
    ] {
        eval.add_constraint(flag.clone() * (flag - one.clone()));
    }
    for limb in 0..(N_LIMBS - 1) {
        eval.add_constraint(
            row.selected_borrow[limb].clone() * (row.selected_borrow[limb].clone() - one.clone()),
        );
    }

    // Require a nonzero second lattice component on an active certificate.
    // Otherwise, zero scalar values could accept an arbitrary hint point.
    // Range13 checks prevent the limb sum from wrapping M31.
    // The inverse constraint proves that the sum is nonzero.
    let s2_abs_sum = row
        .s2_abs
        .iter()
        .cloned()
        .fold(zero.clone(), |acc, limb| acc + limb);
    eval.add_constraint(s2_abs_sum * row.s2_abs_inv.clone() - row.cert_active.clone());
    //      Pin the inverse witness on the zero branch (kept determined like the
    //      other zero-branch cells).
    eval.add_constraint(cert_zero_active.clone() * row.s2_abs_inv.clone());

    // (2) Bind the witnessed `scalar` to the cert input. The trivial helper
    //     additionally forced the upper `N_LIMBS − FAKE_GLV_SMALL_LIMBS` limbs
    //     to zero — that constraint is gone now, because we want to admit
    //     full-width `[0, n)` scalars.
    for limb in 0..N_LIMBS {
        eval.add_constraint(
            active.clone()
                * (row.scalar.limbs()[limb].clone() - cert[cert_scalar_start + limb].clone()),
        );
    }

    // (3) Set hint and derived values to zero on the zero branch.
    // Other constraints set all padding values to zero.
    for limb in 0..FAKE_GLV_SMALL_LIMBS {
        eval.add_constraint(cert_zero_active.clone() * row.s1[limb].clone());
        eval.add_constraint(cert_zero_active.clone() * row.s2_abs[limb].clone());
        eval.add_constraint(cert_zero_active.clone() * row.q[limb].clone());
    }
    eval.add_constraint(cert_zero_active.clone() * row.s2_sign_bit.clone());
    eval.add_constraint(cert_zero_active.clone() * row.active_bit.clone());
    for limb in 0..N_LIMBS {
        eval.add_constraint(cert_zero_active.clone() * row.selected_s1[limb].clone());
    }
    for limb in 0..(N_LIMBS - 1) {
        eval.add_constraint(cert_zero_active.clone() * row.selected_borrow[limb].clone());
    }

    // (4) Witness composition: `active_bit = cert_active · s2_sign_bit`.
    //     Used as a degree-1 selector for the bit = 1 branch (and via
    //     `cert_active − active_bit` for the bit = 0 branch), keeping the
    //     selected-s1 constraints at degree 2.
    eval.add_constraint(row.active_bit.clone() - cert_active.clone() * row.s2_sign_bit.clone());

    // (5) bit = 1 branch  ⇒  selected_s1 = s1  (with s1[i] = 0 for
    //     i ≥ FAKE_GLV_SMALL_LIMBS).
    for limb in 0..FAKE_GLV_SMALL_LIMBS {
        eval.add_constraint(
            row.active_bit.clone() * (row.selected_s1[limb].clone() - row.s1[limb].clone()),
        );
    }
    for limb in FAKE_GLV_SMALL_LIMBS..N_LIMBS {
        eval.add_constraint(row.active_bit.clone() * row.selected_s1[limb].clone());
    }

    // (6) bit = 0 branch  ⇒  selected_s1 = n − s1, limb-by-limb with borrows.
    //     Gate selector: `cert_active_neg_bit = cert_active − active_bit`.
    //     Per-limb identity:
    //         selected_s1[i] + s1[i] − n[i] + borrow_in[i] − BASE · borrow_out[i] = 0
    //     where `borrow_in[0] = 0`, `borrow_in[i] = selected_borrow[i − 1]`
    //     for `i ≥ 1`, and `borrow_out[N_LIMBS − 1] = 0` (n − s1 ≥ 0 fits
    //     in N_LIMBS limbs).
    let cert_active_neg_bit = cert_active.clone() - row.active_bit.clone();
    let n_limbs = words_to_limbs(&P256_ORDER);
    for (limb, n_limb) in n_limbs.iter().copied().enumerate().take(N_LIMBS) {
        let n_limb = E::F::from(M31::from_u32_unchecked(n_limb));
        let s1_limb = if limb < FAKE_GLV_SMALL_LIMBS {
            row.s1[limb].clone()
        } else {
            zero.clone()
        };
        let borrow_in = if limb == 0 {
            zero.clone()
        } else {
            row.selected_borrow[limb - 1].clone()
        };
        let borrow_out_term = if limb < N_LIMBS - 1 {
            base.clone() * row.selected_borrow[limb].clone()
        } else {
            zero.clone()
        };
        eval.add_constraint(
            cert_active_neg_bit.clone()
                * (row.selected_s1[limb].clone() + s1_limb - n_limb + borrow_in - borrow_out_term),
        );
    }
}

fn write_cert_relation_values(
    columns: &mut [Vec<M31>],
    offset: &mut usize,
    row: &CertScalarInputRow,
    row_index: usize,
) {
    let values = cert_relation_values(row);
    for value in values {
        columns[*offset][row_index] = value;
        *offset += 1;
    }
}

fn cert_relation_values(row: &CertScalarInputRow) -> [M31; CERT_SCALAR_INPUT_RELATION_ARITY] {
    core::array::from_fn(|index| {
        if index == 0 {
            return row.sig_id;
        }
        if index == 1 {
            return row.cert_id;
        }
        let offset = index - 2;
        if offset < N_LIMBS {
            return row.scalar.limbs()[offset];
        }
        if offset < 2 * N_LIMBS {
            return row.base_x.limbs()[offset - N_LIMBS];
        }
        if offset < 3 * N_LIMBS {
            return row.base_y.limbs()[offset - 2 * N_LIMBS];
        }
        match offset - 3 * N_LIMBS {
            0 => row.base_inf,
            1 => row.scalar_is_zero,
            2 => row.scalar_is_nonzero,
            3 => row.cert_active,
            4 => row.cert_zero_active,
            _ => panic!("cert relation index {index} out of range"),
        }
    })
}

fn write_fake_glv_scalar_row(
    columns: &mut [Vec<M31>],
    offset: &mut usize,
    row: &FakeGlvScalarHintRow,
    row_index: usize,
) {
    columns[*offset][row_index] = row.sig_id;
    *offset += 1;
    columns[*offset][row_index] = row.cert_id;
    *offset += 1;
    columns[*offset][row_index] = row.cert_active;
    *offset += 1;
    columns[*offset][row_index] = row.cert_zero_active;
    *offset += 1;
    for value in row.scalar.limbs() {
        columns[*offset][row_index] = *value;
        *offset += 1;
    }
    for value in row.hint.s1.limbs {
        columns[*offset][row_index] = value;
        *offset += 1;
    }
    for value in row.hint.s2_abs.limbs {
        columns[*offset][row_index] = value;
        *offset += 1;
    }
    columns[*offset][row_index] = row.hint.s2_sign_bit;
    *offset += 1;
    for value in row.hint.q.limbs {
        columns[*offset][row_index] = value;
        *offset += 1;
    }
    let (active_bit, selected_s1, selected_borrow) = derive_selected_s1_witness(row);
    columns[*offset][row_index] = active_bit;
    *offset += 1;
    for value in selected_s1 {
        columns[*offset][row_index] = value;
        *offset += 1;
    }
    for value in selected_borrow {
        columns[*offset][row_index] = value;
        *offset += 1;
    }
    columns[*offset][row_index] = fake_glv_small_scalar_nonzero_inverse(row);
    *offset += 1;
}

/// Compute the trace-row witnesses derived from a fake-GLV hint row:
///   - `active_bit = cert_active · s2_sign_bit`
///   - `selected_s1 = bit ? s1 : (n − s1)` as `N_LIMBS` 13-bit limbs
///   - `selected_borrow[i]` = borrow OUT of limb `i` during the `n − s1`
///     subtraction (`N_LIMBS − 1` cells, the top borrow is zero by
///     construction since `n − s1 ∈ [1, n)` fits in `N_LIMBS` limbs).
///
/// On inactive rows or in the `cert_zero_active` branch, every output is
/// zero — keeping the universal zero-on-inactive constraints satisfied.
fn derive_selected_s1_witness(
    row: &FakeGlvScalarHintRow,
) -> (M31, [M31; N_LIMBS], [M31; N_LIMBS - 1]) {
    let zero = M31::from_u32_unchecked(0);
    let active_bit = M31::from_u32_unchecked(row.cert_active.0 * row.hint.s2_sign_bit.0);

    // Inactive or zero-active rows ⇒ all derived witnesses zero.
    if row.cert_active.0 == 0 {
        return (active_bit, [zero; N_LIMBS], [zero; N_LIMBS - 1]);
    }

    // Lift `s1` (≤ 2^128, held in `FAKE_GLV_SMALL_LIMBS` 13-bit limbs) into
    // the full `N_LIMBS` layout by zero-padding the upper limbs.
    let mut s1_full = [0u32; N_LIMBS];
    for (dst, src) in s1_full.iter_mut().zip(row.hint.s1.limbs.iter()) {
        *dst = src.0;
    }

    if row.hint.s2_sign_bit.0 == 1 {
        // bit = 1 ⇒ selected_s1 = s1.
        let selected_s1 = core::array::from_fn(|i| M31::from_u32_unchecked(s1_full[i]));
        return (active_bit, selected_s1, [zero; N_LIMBS - 1]);
    }

    // bit = 0 ⇒ selected_s1 = n − s1 (limb-by-limb subtraction).
    let n_limbs = words_to_limbs(&P256_ORDER);
    let base = 1i64 << LIMB_BITS;
    let mut selected_s1 = [zero; N_LIMBS];
    let mut selected_borrow = [zero; N_LIMBS - 1];
    let mut borrow_in: i64 = 0;
    for i in 0..N_LIMBS {
        let diff = i64::from(n_limbs[i]) - i64::from(s1_full[i]) - borrow_in;
        let (limb, borrow_out) = if diff < 0 {
            ((diff + base) as u32, 1u32)
        } else {
            (diff as u32, 0u32)
        };
        selected_s1[i] = M31::from_u32_unchecked(limb);
        if i < N_LIMBS - 1 {
            selected_borrow[i] = M31::from_u32_unchecked(borrow_out);
        } else {
            // `n − s1 ≥ 0`, so the top limb must not borrow out.
            assert_eq!(
                borrow_out, 0,
                "borrow out of top limb during `n − s1` (n={n_limbs:?}, s1={s1_full:?})",
            );
        }
        borrow_in = i64::from(borrow_out);
    }
    (active_bit, selected_s1, selected_borrow)
}

/// Witness for the Garaga `s2_abs != 0` check (`assert(_s2_abs != 0)`,
/// `src/src/ec/ec_ops.cairo:254`). On the nonzero branch (`cert_active == 1`)
/// returns the M31 inverse of the `s2_abs` limb sum. The limbs are 13-bit
/// (range-checked through the `ScalarModMul` role-`B` link), so the sum never
/// wraps M31.
/// It is nonzero if and only if `s2_abs` is nonzero.
/// It is zero on the inactive branch.
fn fake_glv_small_scalar_nonzero_inverse(row: &FakeGlvScalarHintRow) -> M31 {
    if row.cert_active.0 != 1 {
        return M31::from_u32_unchecked(0);
    }
    let sum = row
        .hint
        .s2_abs
        .limbs
        .iter()
        .fold(0u64, |acc, limb| acc + u64::from(limb.0));
    assert!(
        sum > 0,
        "nonzero fake-GLV s2_abs must have a nonzero limb sum"
    );
    m31_inverse(M31::from_u32_unchecked(sum as u32))
}

/// `value^(p - 2) mod p` — the M31 multiplicative inverse via Fermat.
fn m31_inverse(value: M31) -> M31 {
    const MODULUS: u64 = (1u64 << 31) - 1;
    let mut base = u64::from(value.0);
    let mut exp = MODULUS - 2;
    let mut acc = 1u64;
    while exp != 0 {
        if exp & 1 == 1 {
            acc = (acc * base) % MODULUS;
        }
        base = (base * base) % MODULUS;
        exp >>= 1;
    }
    M31::from_u32_unchecked(acc as u32)
}

fn cert_packed_values_from_base(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; CERT_SCALAR_INPUT_RELATION_ARITY] {
    core::array::from_fn(|index| base[1 + index].data[vec_row])
}

const SCALAR_ROW_START: usize = 1 + CERT_SCALAR_INPUT_RELATION_ARITY;
const SCALAR_ROW_SIG_ID: usize = SCALAR_ROW_START;
const SCALAR_ROW_CERT_ID: usize = SCALAR_ROW_START + 1;
const SCALAR_ROW_CERT_ACTIVE: usize = SCALAR_ROW_START + 2;
const SCALAR_ROW_SCALAR_START: usize = SCALAR_ROW_START + 4;
const SCALAR_ROW_S1_START: usize = SCALAR_ROW_START + 4 + N_LIMBS;
const SCALAR_ROW_S2_ABS_START: usize = SCALAR_ROW_S1_START + FAKE_GLV_SMALL_LIMBS;
const SCALAR_ROW_S2_SIGN_BIT: usize = SCALAR_ROW_S2_ABS_START + FAKE_GLV_SMALL_LIMBS;
const SCALAR_ROW_Q_START: usize = SCALAR_ROW_S2_SIGN_BIT + 1;
const SCALAR_ROW_SELECTED_S1_START: usize = SCALAR_ROW_Q_START + FAKE_GLV_SMALL_LIMBS + 1;
/// Marks a relation value that must use constant zero.
///
/// Callers use `M31(0)` or `PackedM31(0)` instead of a base-trace column.
const SCALAR_ROW_ZERO_PAD_COL: usize = usize::MAX;

fn scalar_relation_column_index(index: usize) -> usize {
    match index {
        0 => SCALAR_ROW_SIG_ID,
        1 => SCALAR_ROW_CERT_ID,
        idx if idx < 2 + FAKE_GLV_SMALL_LIMBS => SCALAR_ROW_S1_START + (idx - 2),
        idx if idx < 2 + 2 * FAKE_GLV_SMALL_LIMBS => {
            SCALAR_ROW_S2_ABS_START + (idx - 2 - FAKE_GLV_SMALL_LIMBS)
        }
        idx if idx == 2 + 2 * FAKE_GLV_SMALL_LIMBS => SCALAR_ROW_S2_SIGN_BIT,
        idx if idx == FAKE_GLV_SCALAR_RELATION_ARITY - 1 => SCALAR_ROW_CERT_ACTIVE,
        _ => panic!("scalar relation index {index} out of range"),
    }
}

fn scalar_packed_values_from_base(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; FAKE_GLV_SCALAR_RELATION_ARITY] {
    core::array::from_fn(|index| base[scalar_relation_column_index(index)].data[vec_row])
}

fn secure_zero() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(0))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY};
    use crate::public_inputs::{
        public_ecdsa_consumer_claimed_sum, PublicEcdsaInputClaim, PublicEcdsaInstanceRelation,
    };
    use crate::scalar::cert_bind::CertScalarInputClaim;
    use crate::scalar::setup_air::ScalarSetupClaim;
    use crate::types::{AffinePoint, EcdsaVerifyInput, Signature, U256};
    use stwo::core::fields::qm31::SecureField;

    fn test_input(message_hash: u64, r: u64, s: u64) -> EcdsaVerifyInput {
        EcdsaVerifyInput {
            message_hash: scalar(message_hash),
            signature: Signature {
                r: scalar(r),
                s: scalar(s),
            },
            public_key: AffinePoint {
                x: U256::from_le_u64s(&P256_GX),
                y: U256::from_le_u64s(&P256_GY),
            },
        }
    }

    fn scalar(value: u64) -> U256 {
        U256::from_le_u64s(&[value, 0, 0, 0])
    }

    fn trivial_hints(certs: &CertScalarInputClaim) -> Vec<FakeGlvScalarHint> {
        certs
            .rows
            .iter()
            .map(|row| FakeGlvScalarHint::trivial_for_small_scalar(&row.scalar).unwrap())
            .collect()
    }

    #[test]
    fn fake_glv_scalar_hints_verify_trivial_small_scalars() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(42, 77, 1)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let hints = trivial_hints(&certs);

        let fake_glv = FakeGlvScalarHintClaim::from_cert_inputs(&certs, hints)
            .expect("valid fake-GLV scalar hints");

        fake_glv.verify().expect("fake-GLV scalar hints verify");
        assert_eq!(fake_glv.rows.len(), 2);
    }

    #[test]
    fn fake_glv_scalar_e2e_keeps_public_logup_balanced() {
        let relation = PublicEcdsaInstanceRelation::dummy();
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(42, 77, 1)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let fake_glv = FakeGlvScalarHintClaim::from_cert_inputs(&certs, trivial_hints(&certs))
            .expect("valid fake-GLV scalar hints");
        let public_interaction = public_claim.initial_logup_claim(&relation);
        let vm_consumers =
            public_ecdsa_consumer_claimed_sum(&scalar_setup.public_consumers(), &relation);

        scalar_setup.verify().expect("scalar setup verifies");
        certs.verify().expect("cert inputs verify");
        fake_glv.verify().expect("fake-GLV scalar hints verify");
        assert_eq!(
            public_interaction.claimed_sum + vm_consumers,
            SecureField::from(M31::from_u32_unchecked(0))
        );
    }

    #[test]
    fn fake_glv_scalar_hints_allow_zero_branch_with_zero_hint() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(0, 77, 1)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let fake_glv = FakeGlvScalarHintClaim::from_cert_inputs(&certs, trivial_hints(&certs))
            .expect("valid fake-GLV scalar hints");

        assert_eq!(fake_glv.rows[0].cert_active.0, 0);
        assert!(fake_glv.rows[0].hint.is_zero());
        assert_eq!(fake_glv.rows[1].cert_active.0, 1);
        fake_glv.verify().expect("zero branch verifies");
    }

    #[test]
    fn fake_glv_scalar_hints_reject_mutated_s1() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(42, 77, 1)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let mut fake_glv = FakeGlvScalarHintClaim::from_cert_inputs(&certs, trivial_hints(&certs))
            .expect("valid fake-GLV scalar hints");
        fake_glv.rows[0].hint.s1.limbs[0] = M31::from_u32_unchecked(43);

        let err = fake_glv.verify().expect_err("mutated s1 must fail");

        assert!(matches!(
            err,
            FakeGlvScalarHintError::ScalarEquationMismatch { .. }
        ));
    }

    #[test]
    fn fake_glv_scalar_hints_reject_flipped_sign() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(42, 77, 1)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let mut fake_glv = FakeGlvScalarHintClaim::from_cert_inputs(&certs, trivial_hints(&certs))
            .expect("valid fake-GLV scalar hints");
        fake_glv.rows[0].hint.s2_sign_bit = M31::from_u32_unchecked(0);

        let err = fake_glv.verify().expect_err("flipped sign must fail");

        assert!(matches!(
            err,
            FakeGlvScalarHintError::ScalarEquationMismatch { .. }
        ));
    }

    #[test]
    fn fake_glv_scalar_hints_reject_zero_s2_abs_on_nonzero_branch() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(42, 77, 1)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let mut fake_glv = FakeGlvScalarHintClaim::from_cert_inputs(&certs, trivial_hints(&certs))
            .expect("valid fake-GLV scalar hints");
        fake_glv.rows[0].hint.s2_abs = FakeGlvSmallScalar::zero();

        let err = fake_glv
            .verify()
            .expect_err("zero s2_abs must fail on nonzero branch");

        assert!(matches!(
            err,
            FakeGlvScalarHintError::ZeroSmallScalar { field: "s2_abs" }
        ));
    }

    #[test]
    fn fake_glv_scalar_hints_mix_into_transcript() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(42, 77, 1)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let fake_glv = FakeGlvScalarHintClaim::from_cert_inputs(&certs, trivial_hints(&certs))
            .expect("valid fake-GLV scalar hints");
        let mut channel = stwo::core::channel::Blake2sM31Channel::default();

        fake_glv.mix_into(&mut channel);
    }

    /// Confirms decomposition of a full-width scalar near `n`.
    ///
    /// The hint must satisfy the scalar equation and all 128-bit bounds.
    #[test]
    fn fake_glv_hint_supports_near_order_scalar() {
        use stwo_p256_utils::scalar_arithmetic::P256_ORDER;
        let scalar = P256M31BigInt::from_u256(&U256::from_le_u64s(&[
            P256_ORDER[0] - 123,
            P256_ORDER[1],
            P256_ORDER[2],
            P256_ORDER[3],
        ]));
        let hint = FakeGlvScalarHint::decompose(&scalar)
            .expect("full-width scalar should have a bounded fake-GLV hint");
        verify_scalar_equation(&scalar, &hint).expect("hint equation must verify");
        hint.s1.require_128_bit_bound("s1").expect("s1 bound");
        hint.s2_abs
            .require_128_bit_bound("s2_abs")
            .expect("s2 bound");
        hint.q.require_128_bit_bound("q").expect("q bound");
    }
}
