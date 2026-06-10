use stwo::core::{
    air::Component, fields::m31::M31, fields::qm31::SecureField, pcs::TreeVec, ColumnVec,
};
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::ComponentProver;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{FrameworkComponent, TraceLocationAllocator};
use stwo_p256_utils::constants::N_LIMBS;

use crate::prepared_point::TABLE16_INDEX;
use crate::projective::ProjectiveEcOp;

pub mod air;
pub mod interaction;
pub mod relation;
pub mod trace;

pub use air::*;
pub use interaction::*;
pub use relation::*;
pub use trace::*;

#[cfg(test)]
mod tests;

/// `FinalCheckHintRelation` tuple arity:
/// `(sig_id, cert_id, point[PREPARED_TABLE_EC_POINT_COLUMNS])`.
pub const FINAL_CHECK_HINT_RELATION_ARITY: usize = 2 + PREPARED_TABLE_EC_POINT_COLUMNS;

/// `CertBaseRelation` tuple arity: `(sig_id, cert_id, base_x[N_LIMBS], base_y[N_LIMBS])`.
pub const CERT_BASE_RELATION_ARITY: usize = 2 + 2 * N_LIMBS;

/// `PreparedTableCanonicalRelation` tuple arity:
/// `(sig_id, cert_id, role, point[PREPARED_TABLE_EC_POINT_COLUMNS])`.
pub const PREPARED_TABLE_CANONICAL_RELATION_ARITY: usize = 3 + PREPARED_TABLE_EC_POINT_COLUMNS;

// Canonical roles. P is handled by `CertBaseRelation`; these cover the rest.
pub const PREPARED_TABLE_CANONICAL_ROLE_P3: u32 = 0;
pub const PREPARED_TABLE_CANONICAL_ROLE_R: u32 = 1;
pub const PREPARED_TABLE_CANONICAL_ROLE_R3: u32 = 2;
pub const PREPARED_TABLE_CANONICAL_ROLE_NEG_R: u32 = 3;
pub const PREPARED_TABLE_CANONICAL_ROLE_NEG_R3: u32 = 4;
pub const PREPARED_TABLE_CANONICAL_ROLE_P2: u32 = 5;
pub const PREPARED_TABLE_CANONICAL_ROLE_R2: u32 = 6;

pub type PreparedTableEcRowComponent = FrameworkComponent<PreparedTableEcRowEval>;

pub const PREPARED_TABLE_EC_KIND_FLAGS: usize = 13;
pub const PREPARED_TABLE_EC_KIND_DOUBLE_P: usize = 0;
pub const PREPARED_TABLE_EC_KIND_ADD_P2P: usize = 1;
pub const PREPARED_TABLE_EC_KIND_DOUBLE_R: usize = 2;
pub const PREPARED_TABLE_EC_KIND_ADD_R2R: usize = 3;
pub const PREPARED_TABLE_EC_KIND_BASE_START: usize = 4;
pub const PREPARED_TABLE_EC_KIND_TABLE16: usize = 12;
pub const PREPARED_TABLE_EC_OP_MIXED_ADD: u32 = 0;
pub const PREPARED_TABLE_EC_OP_DOUBLE: u32 = 1;
pub const PREPARED_TABLE_EC_POINT_COLUMNS: usize = 2 * N_LIMBS + 1;
pub const PREPARED_TABLE_EC_ROW_RELATION_ARITY: usize = 5 + 3 * PREPARED_TABLE_EC_POINT_COLUMNS;

/// Number of signed carry columns for the in-AIR negation identity
/// `neg.y + src.y = p` (one carry per limb; the top carry is constrained to 0).
pub const PREPARED_TABLE_EC_NEG_CARRY_COLUMNS: usize = N_LIMBS;

/// The negation aux block appended to every EC-row's base trace: a full point
/// `neg` (= `-src`) plus its `neg.y + src.y = p` carries. Populated with `-R`
/// on `DoubleR` rows and `-R3` on `AddR2R` rows; zero elsewhere.
pub const PREPARED_TABLE_EC_NEG_AUX_COLUMNS: usize =
    PREPARED_TABLE_EC_POINT_COLUMNS + PREPARED_TABLE_EC_NEG_CARRY_COLUMNS;

pub const PREPARED_TABLE_EC_ROW_TRACE_COLUMNS: usize =
    1 + 3 + PREPARED_TABLE_EC_KIND_FLAGS + 2 + 3 * PREPARED_TABLE_EC_POINT_COLUMNS
        + PREPARED_TABLE_EC_NEG_AUX_COLUMNS;
pub const PREPARED_TABLE_PROJECTIVE_SOURCE_TRACE_COLUMNS: usize = 1
    + 5
    + 3 * PREPARED_TABLE_EC_POINT_COLUMNS
    + crate::projective_air::CONSUMED_MUL_LIMBS_COLUMNS
    + super::ec_source::double_formula::DOUBLE_FORMULA_COLUMNS
    + super::ec_source::mixed_add_formula::MIXED_ADD_FORMULA_COLUMNS;
/// Column index of the C5 consumed-mul block's `has_muls` flag (appended LAST so
/// existing relation-value column offsets are unchanged; limbs follow at `+ 1`).
pub const PREPARED_TABLE_PROJECTIVE_SOURCE_HAS_MULS_COL: usize =
    1 + 5 + 3 * PREPARED_TABLE_EC_POINT_COLUMNS;
/// Column index where the C5 consumed-mul LIMB block begins (after `has_muls`).
pub const PREPARED_TABLE_PROJECTIVE_SOURCE_MUL_LIMB_OFFSET: usize =
    PREPARED_TABLE_PROJECTIVE_SOURCE_HAS_MULS_COL + 1;
/// Column index where the C5-2 Double-formula block begins (after the
/// consumed-mul block).
pub const PREPARED_TABLE_PROJECTIVE_SOURCE_DOUBLE_FORMULA_OFFSET: usize = 1
    + 5
    + 3 * PREPARED_TABLE_EC_POINT_COLUMNS
    + crate::projective_air::CONSUMED_MUL_LIMBS_COLUMNS;
/// Column index where the C5-2 MixedAdd-formula block begins (right after the
/// Double-formula block).
pub const PREPARED_TABLE_PROJECTIVE_SOURCE_MIXED_ADD_FORMULA_OFFSET: usize =
    PREPARED_TABLE_PROJECTIVE_SOURCE_DOUBLE_FORMULA_OFFSET
        + super::ec_source::double_formula::DOUBLE_FORMULA_COLUMNS;

const PREPARED_TABLE_EC_ROW_INDEX_COLUMN: &str = "p256_prepared_table_ec_row_index";

pub type PreparedTableProjectiveSourceComponent =
    FrameworkComponent<PreparedTableProjectiveSourceEval>;

pub struct PreparedTableProjectiveSourceComponents {
    pub provider: PreparedTableEcRowComponent,
    pub consumer: PreparedTableProjectiveSourceComponent,
    /// C5-2: self-contained Range13 provider for the prepared-table formula
    /// coordinate limb range checks (mirrors the fake-GLV projective source).
    pub range13: crate::range_checks::RangeCheckComponent,
    /// C5-2: self-contained signed-carry provider for the prepared-table
    /// formula reduction carries.
    pub signed_carry: crate::range_checks::SignedCarryRangeComponent,
}

impl PreparedTableProjectiveSourceComponents {
    pub fn new(
        allocator: &mut TraceLocationAllocator,
        log_size: u32,
        interaction_claim: &PreparedTableProjectiveSourceInteractionClaim,
        relation: &PreparedTableEcRowRelation,
        mul_relations: &crate::projective_air::ProjectiveRcbMulComponentRelations,
        range13: &crate::range_checks::RangeCheckRelation,
        signed_carry: &crate::range_checks::RangeCheckRelation,
    ) -> Self {
        Self::new_inner(
            allocator,
            log_size,
            interaction_claim,
            relation,
            mul_relations,
            range13,
            signed_carry,
            None,
        )
    }

    /// Monolithic constructor: the provider additionally pins the table to
    /// `cert.base` via `CertBaseRelation` and `PreparedTableCanonicalRelation`.
    /// `provider_total_claimed_sum` is the provider's full logup total
    /// (`PreparedTableEcRowPinnedInteractionClaim::total_claimed_sum`).
    #[allow(clippy::too_many_arguments)]
    pub fn new_pinned(
        allocator: &mut TraceLocationAllocator,
        log_size: u32,
        provider_total_claimed_sum: SecureField,
        consumer_interaction: &PreparedTableProjectiveSourceInteractionClaim,
        relation: &PreparedTableEcRowRelation,
        pinning: &PreparedTablePinningRelations,
        mul_relations: &crate::projective_air::ProjectiveRcbMulComponentRelations,
        range13: &crate::range_checks::RangeCheckRelation,
        signed_carry: &crate::range_checks::RangeCheckRelation,
    ) -> Self {
        let interaction_claim = PreparedTableProjectiveSourceInteractionClaim {
            provider_claimed_sum: provider_total_claimed_sum,
            ..consumer_interaction.clone()
        };
        Self::new_inner(
            allocator,
            log_size,
            &interaction_claim,
            relation,
            mul_relations,
            range13,
            signed_carry,
            Some(pinning.clone()),
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn new_inner(
        allocator: &mut TraceLocationAllocator,
        log_size: u32,
        interaction_claim: &PreparedTableProjectiveSourceInteractionClaim,
        relation: &PreparedTableEcRowRelation,
        mul_relations: &crate::projective_air::ProjectiveRcbMulComponentRelations,
        range13: &crate::range_checks::RangeCheckRelation,
        signed_carry: &crate::range_checks::RangeCheckRelation,
        pinning: Option<PreparedTablePinningRelations>,
    ) -> Self {
        Self {
            provider: PreparedTableEcRowComponent::new(
                allocator,
                PreparedTableEcRowEval {
                    log_size,
                    relation: relation.clone(),
                    pinning,
                },
                interaction_claim.provider_claimed_sum,
            ),
            consumer: PreparedTableProjectiveSourceComponent::new(
                allocator,
                PreparedTableProjectiveSourceEval {
                    log_size,
                    relation: relation.clone(),
                    mul_relations: mul_relations.clone(),
                    range13: range13.clone(),
                    signed_carry: signed_carry.clone(),
                },
                // EC-row + mul-result + range13 + signed-carry consumes share
                // one interaction trace.
                interaction_claim.consumer_component_claimed_sum(),
            ),
            range13: crate::range_checks::RangeCheckComponent::new(
                allocator,
                crate::range_checks::RangeCheckEval::new(
                    range13.clone(),
                    crate::range_checks::RANGE13_BITS,
                ),
                interaction_claim.range13.claimed_sum,
            ),
            signed_carry: crate::range_checks::SignedCarryRangeComponent::new(
                allocator,
                crate::range_checks::SignedCarryRangeEval::new(
                    signed_carry.clone(),
                    crate::projective_air::projective_rcb_signed_carry_log_size(),
                    crate::projective_air::PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
                ),
                interaction_claim.signed_carry.claimed_sum,
            ),
        }
    }

    pub fn components(&self) -> Vec<&dyn Component> {
        vec![
            &self.provider as &dyn Component,
            &self.consumer as &dyn Component,
            &self.range13 as &dyn Component,
            &self.signed_carry as &dyn Component,
        ]
    }

    pub fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            &self.provider as &dyn ComponentProver<SimdBackend>,
            &self.consumer as &dyn ComponentProver<SimdBackend>,
            &self.range13 as &dyn ComponentProver<SimdBackend>,
            &self.signed_carry as &dyn ComponentProver<SimdBackend>,
        ]
    }

    pub fn trace_log_degree_bounds(&self) -> TreeVec<ColumnVec<u32>> {
        TreeVec::concat_cols(
            self.components()
                .into_iter()
                .map(|component| component.trace_log_degree_bounds()),
        )
    }

    pub fn max_constraint_log_degree_bound(&self) -> u32 {
        self.components()
            .into_iter()
            .map(|component| component.max_constraint_log_degree_bound())
            .max()
            .unwrap_or(0)
    }
}

/// Which point in the row supplies a pinning tuple.
#[derive(Clone, Copy)]
enum PinPoint {
    Lhs,
    Rhs,
    Output,
    Neg,
    ConstThreeG,
}

/// Which relation a pinning entry targets.
#[derive(Clone, Copy)]
enum PinRelation {
    /// `CertBaseRelation`: tuple `(sig, cert, base_x, base_y)`.
    CertBase,
    /// `PreparedTableCanonicalRelation`: tuple `(sig, cert, role, point)`.
    Canonical(u32),
}

/// One row-local pinning emission.
#[derive(Clone, Copy)]
struct PinEntry {
    relation: PinRelation,
    point: PinPoint,
    /// Signed multiplicity: `+1` for a use (consumer), `-count` for a yield
    /// (provider). Multiplied by the gate product to form the numerator.
    mult: i32,
    /// Kind flags whose product gates this emission (e.g. `[BASE_START+1]`).
    kinds: &'static [usize],
    /// If `true`, additionally gate by `is_cert0 = active - cert_id`.
    cert0_only: bool,
}

const fn base_kind(i: usize) -> usize {
    PREPARED_TABLE_EC_KIND_BASE_START + i
}

/// The fixed pinning schedule (30 entries), identical in order to the manual
/// enumeration verified for per-cert balance.
const PIN_SCHEDULE: &[PinEntry] = &[
    // CertBase consumers (use +1) on each P-cell.
    PinEntry { relation: PinRelation::CertBase, point: PinPoint::Lhs, mult: 1, kinds: &[base_kind(1)], cert0_only: false },
    PinEntry { relation: PinRelation::CertBase, point: PinPoint::Lhs, mult: 1, kinds: &[base_kind(2)], cert0_only: false },
    PinEntry { relation: PinRelation::CertBase, point: PinPoint::Lhs, mult: 1, kinds: &[base_kind(5)], cert0_only: false },
    PinEntry { relation: PinRelation::CertBase, point: PinPoint::Lhs, mult: 1, kinds: &[base_kind(6)], cert0_only: false },
    PinEntry { relation: PinRelation::CertBase, point: PinPoint::Lhs, mult: 1, kinds: &[PREPARED_TABLE_EC_KIND_DOUBLE_P], cert0_only: false },
    PinEntry { relation: PinRelation::CertBase, point: PinPoint::Rhs, mult: 1, kinds: &[PREPARED_TABLE_EC_KIND_ADD_P2P], cert0_only: false },
    // Canonical providers (yield -count).
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_P3), point: PinPoint::Output, mult: -4, kinds: &[PREPARED_TABLE_EC_KIND_ADD_P2P], cert0_only: false },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_P3), point: PinPoint::ConstThreeG, mult: -4, kinds: &[PREPARED_TABLE_EC_KIND_DOUBLE_R], cert0_only: true },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_R), point: PinPoint::Lhs, mult: -3, kinds: &[PREPARED_TABLE_EC_KIND_DOUBLE_R], cert0_only: false },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_R3), point: PinPoint::Output, mult: -3, kinds: &[PREPARED_TABLE_EC_KIND_ADD_R2R], cert0_only: false },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_NEG_R), point: PinPoint::Neg, mult: -2, kinds: &[PREPARED_TABLE_EC_KIND_DOUBLE_R], cert0_only: false },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_NEG_R3), point: PinPoint::Neg, mult: -2, kinds: &[PREPARED_TABLE_EC_KIND_ADD_R2R], cert0_only: false },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_P2), point: PinPoint::Output, mult: -1, kinds: &[PREPARED_TABLE_EC_KIND_DOUBLE_P], cert0_only: false },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_R2), point: PinPoint::Output, mult: -1, kinds: &[PREPARED_TABLE_EC_KIND_DOUBLE_R], cert0_only: false },
    // Canonical consumers (use +1).
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_P3), point: PinPoint::Lhs, mult: 1, kinds: &[base_kind(0)], cert0_only: false },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_P3), point: PinPoint::Lhs, mult: 1, kinds: &[base_kind(3)], cert0_only: false },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_P3), point: PinPoint::Lhs, mult: 1, kinds: &[base_kind(4)], cert0_only: false },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_P3), point: PinPoint::Lhs, mult: 1, kinds: &[base_kind(7)], cert0_only: false },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_R), point: PinPoint::Rhs, mult: 1, kinds: &[PREPARED_TABLE_EC_KIND_ADD_R2R], cert0_only: false },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_R), point: PinPoint::Rhs, mult: 1, kinds: &[base_kind(2)], cert0_only: false },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_R), point: PinPoint::Rhs, mult: 1, kinds: &[base_kind(3)], cert0_only: false },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_R3), point: PinPoint::Rhs, mult: 1, kinds: &[base_kind(6)], cert0_only: false },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_R3), point: PinPoint::Rhs, mult: 1, kinds: &[base_kind(7)], cert0_only: false },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_R3), point: PinPoint::Rhs, mult: 1, kinds: &[PREPARED_TABLE_EC_KIND_TABLE16], cert0_only: false },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_NEG_R), point: PinPoint::Rhs, mult: 1, kinds: &[base_kind(0)], cert0_only: false },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_NEG_R), point: PinPoint::Rhs, mult: 1, kinds: &[base_kind(1)], cert0_only: false },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_NEG_R3), point: PinPoint::Rhs, mult: 1, kinds: &[base_kind(4)], cert0_only: false },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_NEG_R3), point: PinPoint::Rhs, mult: 1, kinds: &[base_kind(5)], cert0_only: false },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_P2), point: PinPoint::Lhs, mult: 1, kinds: &[PREPARED_TABLE_EC_KIND_ADD_P2P], cert0_only: false },
    PinEntry { relation: PinRelation::Canonical(PREPARED_TABLE_CANONICAL_ROLE_R2), point: PinPoint::Lhs, mult: 1, kinds: &[PREPARED_TABLE_EC_KIND_ADD_R2R], cert0_only: false },
];

/// Number of pinning logup fractions emitted per EC row (one per schedule entry).
pub const PREPARED_TABLE_PINNING_FRACTIONS: usize = 30;

const _: () = assert!(PIN_SCHEDULE.len() == PREPARED_TABLE_PINNING_FRACTIONS);

trait PreparedTableEcPointLike<F: Clone> {
    fn relation_values(&self) -> [F; PREPARED_TABLE_EC_POINT_COLUMNS];
}

fn kind_flags(kind: PreparedTableEcRowKind) -> [M31; PREPARED_TABLE_EC_KIND_FLAGS] {
    let mut flags = [M31::from_u32_unchecked(0); PREPARED_TABLE_EC_KIND_FLAGS];
    flags[prepared_table_ec_kind_flag_index(kind)] = M31::from_u32_unchecked(1);
    flags
}

fn prepared_table_ec_kind_flag_index(kind: PreparedTableEcRowKind) -> usize {
    match kind {
        PreparedTableEcRowKind::DoubleP => PREPARED_TABLE_EC_KIND_DOUBLE_P,
        PreparedTableEcRowKind::AddP2P => PREPARED_TABLE_EC_KIND_ADD_P2P,
        PreparedTableEcRowKind::DoubleR => PREPARED_TABLE_EC_KIND_DOUBLE_R,
        PreparedTableEcRowKind::AddR2R => PREPARED_TABLE_EC_KIND_ADD_R2R,
        PreparedTableEcRowKind::Base(index) => PREPARED_TABLE_EC_KIND_BASE_START + index as usize,
        PreparedTableEcRowKind::Table16 => PREPARED_TABLE_EC_KIND_TABLE16,
    }
}

fn prepared_table_ec_op_code(kind: PreparedTableEcRowKind) -> M31 {
    let code = match kind {
        PreparedTableEcRowKind::DoubleP | PreparedTableEcRowKind::DoubleR => {
            PREPARED_TABLE_EC_OP_DOUBLE
        }
        PreparedTableEcRowKind::AddP2P
        | PreparedTableEcRowKind::AddR2R
        | PreparedTableEcRowKind::Base(_)
        | PreparedTableEcRowKind::Table16 => PREPARED_TABLE_EC_OP_MIXED_ADD,
    };
    M31::from_u32_unchecked(code)
}

fn projective_ec_op_code(op: ProjectiveEcOp) -> M31 {
    let code = match op {
        ProjectiveEcOp::Double => PREPARED_TABLE_EC_OP_DOUBLE,
        ProjectiveEcOp::MixedAdd => PREPARED_TABLE_EC_OP_MIXED_ADD,
    };
    M31::from_u32_unchecked(code)
}

fn prepared_table_ec_table_index(kind: PreparedTableEcRowKind) -> M31 {
    let index = match kind {
        PreparedTableEcRowKind::Base(index) => index,
        PreparedTableEcRowKind::Table16 => TABLE16_INDEX,
        PreparedTableEcRowKind::DoubleP
        | PreparedTableEcRowKind::AddP2P
        | PreparedTableEcRowKind::DoubleR
        | PreparedTableEcRowKind::AddR2R => 0,
    };
    M31::from_u32_unchecked(index)
}

fn prepared_table_ec_row_index_column_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: PREPARED_TABLE_EC_ROW_INDEX_COLUMN.into(),
    }
}

fn secure_zero() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(0))
}

