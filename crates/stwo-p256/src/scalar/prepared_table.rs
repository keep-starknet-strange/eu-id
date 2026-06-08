use stwo::core::{
    air::Component,
    channel::Channel,
    fields::{m31::M31, qm31::SecureField},
    pcs::{CommitmentSchemeVerifier, PcsConfig, TreeVec},
    poly::circle::CanonicCoset,
    proof::StarkProof,
    verifier::verify,
    ColumnVec,
};
use stwo::prover::{
    backend::{
        simd::{
            m31::{PackedM31, LOG_N_LANES},
            qm31::PackedQM31,
            SimdBackend,
        },
        BackendForChannel,
    },
    poly::circle::PolyOps,
    prove, CommitmentSchemeProver, ComponentProver,
};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator,
};
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};

use crate::constants::{P256_3GX, P256_3GY, P256_MODULUS};
use crate::curve::{point_add, point_double, scalar_mul};
use crate::field_ops::{add_mod_witness, sub_mod_witness};
use crate::limbs::P256M31BigInt;
use crate::prepared_point::{
    PreparedPointInstance, PreparedPointTraceClaim, PreparedPointUseCountClaim,
    PREPARED_BASE_COUNT, TABLE16_INDEX,
};
use crate::projective::{ProjectiveEcOp, ProjectiveEcTraceClaim};
use crate::types::{AffinePoint, U256};

use super::cert_bind::{CertScalarInputClaim, CertScalarInputRow, CERT_ID_U1_GENERATOR};
use super::fake_glv_scalar::{FakeGlvScalarHintClaim, FakeGlvScalarHintRow};
use super::fake_glv_selector::{FakeGlvSelectorClaim, FakeGlvSelectorRow};
use super::fake_glv_selector_lookup::Selector16DecodeEntry;
use super::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};

relation!(
    PreparedTableEcRowRelation,
    PREPARED_TABLE_EC_ROW_RELATION_ARITY
);

// --- PreparedTablePoints pinning relations (full table-pinning, Phase 2) ---
//
// `CertBaseRelation` binds every prepared-table cell that must equal the cert
// base point `P` (= G for cert0, = public key Q for cert1) to the in-AIR
// `cert.base` proven in `cert_bind.rs`. Provider: `CertScalarInputAirEval`
// (yield `-m(cert_id)`). Consumer: `PreparedTableEcRowEval` (use `+1` per P-cell).
relation!(CertBaseRelation, CERT_BASE_RELATION_ARITY);

// `PreparedTableCanonicalRelation` ties every other prepared-table operand
// (`P3 = 3P`, `R`, `R3 = 3R`, `-R`, `-R3`, `2P`, `2R`) to a single canonical
// per-(sig,cert,role) value. Both providers and consumers are prepared-table
// rows (self-balancing within `PreparedTableEcRowEval`), except cert0's `P3`
// which is provided as the fixed constant `3·G`.
relation!(
    PreparedTableCanonicalRelation,
    PREPARED_TABLE_CANONICAL_RELATION_ARITY
);

// `FinalCheckHintRelation` forwards the in-AIR-pinned signed hint point `R_i`
// (= `±h_i`; for active certs `s2_sign_bit == 1` is forced in `fake_glv_scalar`,
// so `R_i = -h_i`) from the prepared table to the FinalEcdsaCheck component.
// Provider: `PreparedTableEcRowEval` yields `R_i` (= the `DoubleR` row's `lhs`,
// which role-`R` pinning already binds to the canonical per-cert value) once per
// active `DoubleR` row, gated `active * DoubleR_flag`, multiplicity `-1`.
// Consumer: `FinalEcdsaCheck` uses `R_1` at `(sig, 0)` and `R_2` at `(sig, 1)`.
relation!(FinalCheckHintRelation, FINAL_CHECK_HINT_RELATION_ARITY);

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
pub const PREPARED_TABLE_PROJECTIVE_SOURCE_TRACE_COLUMNS: usize =
    1 + 5 + 3 * PREPARED_TABLE_EC_POINT_COLUMNS;

const PREPARED_TABLE_EC_ROW_INDEX_COLUMN: &str = "p256_prepared_table_ec_row_index";

pub type PreparedTableProjectiveSourceComponent =
    FrameworkComponent<PreparedTableProjectiveSourceEval>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedTableClaim {
    pub certs: Vec<PreparedTableCert>,
}

impl PreparedTableClaim {
    pub fn from_claims(
        cert_inputs: &CertScalarInputClaim,
        fake_glv_scalars: &FakeGlvScalarHintClaim,
        selectors: &FakeGlvSelectorClaim,
    ) -> Result<Self, PreparedTableError> {
        if cert_inputs.rows.len() != fake_glv_scalars.rows.len()
            || cert_inputs.rows.len() != selectors.rows.len()
        {
            return Err(PreparedTableError::RowCountMismatch {
                certs: cert_inputs.rows.len(),
                fake_glv: fake_glv_scalars.rows.len(),
                selectors: selectors.rows.len(),
            });
        }

        let certs = cert_inputs
            .rows
            .iter()
            .zip(&fake_glv_scalars.rows)
            .zip(&selectors.rows)
            .map(|((cert, fake_glv), selector)| PreparedTableCert::new(cert, fake_glv, selector))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self { certs })
    }

    pub fn verify(&self) -> Result<(), PreparedTableError> {
        for cert in &self.certs {
            cert.verify()?;
        }
        Ok(())
    }

    pub fn prepared_point_trace(
        &self,
        use_counts: &PreparedPointUseCountClaim,
    ) -> Result<PreparedPointTraceClaim, PreparedTableError> {
        if self.certs.len() != use_counts.certs.len() {
            return Err(PreparedTableError::UseCountCountMismatch {
                tables: self.certs.len(),
                use_counts: use_counts.certs.len(),
            });
        }

        Ok(PreparedPointTraceClaim::from_use_counts(
            use_counts,
            |sig_id, cert_id, table_index| {
                self.instance(sig_id, cert_id, table_index)
                    .unwrap_or_else(|| PreparedPointInstance::dummy(sig_id, cert_id, table_index))
            },
        ))
    }

    pub fn verify_prepared_point_trace(
        &self,
        use_counts: &PreparedPointUseCountClaim,
        trace: &PreparedPointTraceClaim,
    ) -> Result<(), PreparedTableError> {
        let expected = self.prepared_point_trace(use_counts)?;
        if &expected == trace {
            Ok(())
        } else {
            Err(PreparedTableError::PreparedPointTraceMismatch)
        }
    }

    pub fn instance(
        &self,
        sig_id: M31,
        cert_id: M31,
        table_index: u32,
    ) -> Option<PreparedPointInstance<M31>> {
        self.certs
            .iter()
            .find(|cert| cert.sig_id == sig_id && cert.cert_id == cert_id)
            .and_then(|cert| cert.instance(table_index))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedTableEcTraceClaim {
    pub rows: Vec<PreparedTableEcRow>,
}

impl PreparedTableEcTraceClaim {
    pub fn from_claims(
        cert_inputs: &CertScalarInputClaim,
        fake_glv_scalars: &FakeGlvScalarHintClaim,
        selectors: &FakeGlvSelectorClaim,
        table: &PreparedTableClaim,
    ) -> Result<Self, PreparedTableError> {
        if cert_inputs.rows.len() != fake_glv_scalars.rows.len()
            || cert_inputs.rows.len() != selectors.rows.len()
            || cert_inputs.rows.len() != table.certs.len()
        {
            return Err(PreparedTableError::EcTraceCountMismatch {
                certs: cert_inputs.rows.len(),
                fake_glv: fake_glv_scalars.rows.len(),
                selectors: selectors.rows.len(),
                tables: table.certs.len(),
            });
        }

        let mut rows = Vec::new();
        for (((cert, fake_glv), selector), table_cert) in cert_inputs
            .rows
            .iter()
            .zip(&fake_glv_scalars.rows)
            .zip(&selectors.rows)
            .zip(&table.certs)
        {
            rows.extend(prepared_table_ec_rows_for_cert(
                cert, fake_glv, selector, table_cert,
            )?);
        }
        let claim = Self { rows };
        claim.verify()?;
        Ok(claim)
    }

    pub fn verify(&self) -> Result<(), PreparedTableError> {
        for row in &self.rows {
            row.verify()?;
        }
        Ok(())
    }

    pub fn active_row_count(&self) -> usize {
        self.rows.len()
    }

    pub fn verify_against_table(
        &self,
        table: &PreparedTableClaim,
    ) -> Result<(), PreparedTableError> {
        for cert in &table.certs {
            let cert_rows = self
                .rows
                .iter()
                .filter(|row| row.sig_id == cert.sig_id && row.cert_id == cert.cert_id)
                .collect::<Vec<_>>();
            if cert.cert_active.0 == 0 {
                if cert_rows.is_empty() {
                    continue;
                }
                return Err(PreparedTableError::InactiveEcTraceRows {
                    sig_id: cert.sig_id.0,
                    cert_id: cert.cert_id.0,
                });
            }

            let expected_rows = if cert.cert_id.0 == CERT_ID_U1_GENERATOR {
                PREPARED_BASE_COUNT + 3
            } else {
                PREPARED_BASE_COUNT + 5
            };
            if cert_rows.len() != expected_rows {
                return Err(PreparedTableError::EcTraceCertRowCountMismatch {
                    sig_id: cert.sig_id.0,
                    cert_id: cert.cert_id.0,
                    expected: expected_rows,
                    actual: cert_rows.len(),
                });
            }

            require_unique_output(
                &cert_rows,
                cert.sig_id,
                cert.cert_id,
                PreparedTableEcRowKind::AddR2R,
                "R3",
                &cert.r3,
            )?;
            for (index, point) in cert.base.iter().enumerate() {
                require_unique_output(
                    &cert_rows,
                    cert.sig_id,
                    cert.cert_id,
                    PreparedTableEcRowKind::Base(index as u32),
                    "Base",
                    point,
                )?;
            }
            require_unique_output(
                &cert_rows,
                cert.sig_id,
                cert.cert_id,
                PreparedTableEcRowKind::Table16,
                "Table16",
                &cert.table16,
            )?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PreparedTableEcRowProofClaim {
    pub log_size: u32,
}

impl PreparedTableEcRowProofClaim {
    pub fn from_trace(trace: &PreparedTableEcTraceClaim) -> Self {
        Self {
            log_size: padded_log_size(trace.rows.len()),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    pub fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut allocator = TraceLocationAllocator::default();
        let _ = PreparedTableEcRowComponent::new(
            &mut allocator,
            PreparedTableEcRowEval {
                log_size: self.log_size,
                relation: PreparedTableEcRowRelation::dummy(),
                pinning: None,
            },
            secure_zero(),
        );
        allocator.preprocessed_columns().clone()
    }

    pub fn trace_log_degree_bounds(&self, ids: &[PreProcessedColumnId]) -> TreeVec<ColumnVec<u32>> {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let component = PreparedTableEcRowComponent::new(
            &mut allocator,
            PreparedTableEcRowEval {
                log_size: self.log_size,
                relation: PreparedTableEcRowRelation::dummy(),
                pinning: None,
            },
            secure_zero(),
        );
        component.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self, ids: &[PreProcessedColumnId]) -> u32 {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let component = PreparedTableEcRowComponent::new(
            &mut allocator,
            PreparedTableEcRowEval {
                log_size: self.log_size,
                relation: PreparedTableEcRowRelation::dummy(),
                pinning: None,
            },
            secure_zero(),
        );
        component.max_constraint_log_degree_bound()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PreparedTableEcRowInteractionClaim {
    pub claimed_sum: SecureField,
}

impl PreparedTableEcRowInteractionClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PreparedTableProjectiveSourceProofClaim {
    pub log_size: u32,
}

impl PreparedTableProjectiveSourceProofClaim {
    pub fn from_prepared_trace(trace: &PreparedTableEcTraceClaim) -> Self {
        Self {
            log_size: padded_log_size(trace.rows.len()),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    pub fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut allocator = TraceLocationAllocator::default();
        let _ = PreparedTableProjectiveSourceComponents::new(
            &mut allocator,
            self.log_size,
            &PreparedTableProjectiveSourceInteractionClaim::zero(),
            &PreparedTableEcRowRelation::dummy(),
        );
        allocator.preprocessed_columns().clone()
    }

    pub fn trace_log_degree_bounds(&self, ids: &[PreProcessedColumnId]) -> TreeVec<ColumnVec<u32>> {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = PreparedTableProjectiveSourceComponents::new(
            &mut allocator,
            self.log_size,
            &PreparedTableProjectiveSourceInteractionClaim::zero(),
            &PreparedTableEcRowRelation::dummy(),
        );
        components.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self, ids: &[PreProcessedColumnId]) -> u32 {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = PreparedTableProjectiveSourceComponents::new(
            &mut allocator,
            self.log_size,
            &PreparedTableProjectiveSourceInteractionClaim::zero(),
            &PreparedTableEcRowRelation::dummy(),
        );
        components.max_constraint_log_degree_bound()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PreparedTableProjectiveSourceInteractionClaim {
    pub provider_claimed_sum: SecureField,
    pub consumer_claimed_sum: SecureField,
}

impl PreparedTableProjectiveSourceInteractionClaim {
    pub fn zero() -> Self {
        Self {
            provider_claimed_sum: secure_zero(),
            consumer_claimed_sum: secure_zero(),
        }
    }

    pub fn total(self) -> SecureField {
        self.provider_claimed_sum + self.consumer_claimed_sum
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.provider_claimed_sum, self.consumer_claimed_sum]);
    }
}

pub struct PreparedTableProjectiveSourceComponents {
    pub provider: PreparedTableEcRowComponent,
    pub consumer: PreparedTableProjectiveSourceComponent,
}

impl PreparedTableProjectiveSourceComponents {
    pub fn new(
        allocator: &mut TraceLocationAllocator,
        log_size: u32,
        interaction_claim: &PreparedTableProjectiveSourceInteractionClaim,
        relation: &PreparedTableEcRowRelation,
    ) -> Self {
        Self::new_inner(allocator, log_size, interaction_claim, relation, None)
    }

    /// Monolithic constructor: the provider additionally pins the table to
    /// `cert.base` via `CertBaseRelation` and `PreparedTableCanonicalRelation`.
    /// `provider_total_claimed_sum` is the provider's full logup total
    /// (`PreparedTableEcRowPinnedInteractionClaim::total_claimed_sum`).
    pub fn new_pinned(
        allocator: &mut TraceLocationAllocator,
        log_size: u32,
        provider_total_claimed_sum: SecureField,
        consumer_claimed_sum: SecureField,
        relation: &PreparedTableEcRowRelation,
        pinning: &PreparedTablePinningRelations,
    ) -> Self {
        let interaction_claim = PreparedTableProjectiveSourceInteractionClaim {
            provider_claimed_sum: provider_total_claimed_sum,
            consumer_claimed_sum,
        };
        Self::new_inner(
            allocator,
            log_size,
            &interaction_claim,
            relation,
            Some(pinning.clone()),
        )
    }

    fn new_inner(
        allocator: &mut TraceLocationAllocator,
        log_size: u32,
        interaction_claim: &PreparedTableProjectiveSourceInteractionClaim,
        relation: &PreparedTableEcRowRelation,
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
                },
                interaction_claim.consumer_claimed_sum,
            ),
        }
    }

    pub fn components(&self) -> Vec<&dyn Component> {
        vec![
            &self.provider as &dyn Component,
            &self.consumer as &dyn Component,
        ]
    }

    pub fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            &self.provider as &dyn ComponentProver<SimdBackend>,
            &self.consumer as &dyn ComponentProver<SimdBackend>,
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

/// Relations the `PreparedTableEcRowEval` provider consumes/provides to pin the
/// prepared table to the cert base point. `Some` in the monolithic STARK (where
/// `cert_bind` provides `CertBaseRelation`); `None` for the legacy standalone
/// slice, which emits only `PreparedTableEcRowRelation`.
///
/// The in-AIR negation (`neg.y + src.y = p`) needs `neg`/`src` limbs bounded to
/// 13 bits; that bound is inherited transitively — the canonical relation ties
/// each `neg`/`src` to a base-row operand which feeds the projective EC-add,
/// where every affine limb is already `Range13`-checked. So no extra range
/// lookup is consumed here.
#[derive(Clone)]
pub struct PreparedTablePinningRelations {
    pub cert_base: CertBaseRelation,
    pub canonical: PreparedTableCanonicalRelation,
    /// Forwards the pinned signed hint `R_i` (the `DoubleR` row's `lhs`) to the
    /// FinalEcdsaCheck component. `None` for paths that do not consume it.
    pub final_check_hint: Option<FinalCheckHintRelation>,
}

#[derive(Clone)]
pub struct PreparedTableEcRowEval {
    pub log_size: u32,
    pub relation: PreparedTableEcRowRelation,
    /// Monolithic full-table pinning relations. `None` => legacy slice.
    pub pinning: Option<PreparedTablePinningRelations>,
}

impl FrameworkEval for PreparedTableEcRowEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let row_index = eval.get_preprocessed_column(prepared_table_ec_row_index_column_id());
        let active = eval.next_trace_mask();
        let source_index = eval.next_trace_mask();
        let sig_id = eval.next_trace_mask();
        let cert_id = eval.next_trace_mask();
        let kind_flags: [E::F; PREPARED_TABLE_EC_KIND_FLAGS] =
            core::array::from_fn(|_| eval.next_trace_mask());
        let op = eval.next_trace_mask();
        let table_index = eval.next_trace_mask();
        let lhs = PreparedTableEcEvalPoint::read(&mut eval);
        let rhs = PreparedTableEcEvalPoint::read(&mut eval);
        let output = PreparedTableEcEvalPoint::read(&mut eval);
        let neg = PreparedTableEcEvalPoint::read(&mut eval);
        let neg_carries: [E::F; PREPARED_TABLE_EC_NEG_CARRY_COLUMNS] =
            core::array::from_fn(|_| eval.next_trace_mask());
        let one = E::F::from(M31::from_u32_unchecked(1));

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint(active.clone() * (source_index.clone() - row_index));

        let mut kind_sum = E::F::from(M31::from_u32_unchecked(0));
        for flag in &kind_flags {
            eval.add_constraint(flag.clone() * (flag.clone() - one.clone()));
            eval.add_constraint((one.clone() - active.clone()) * flag.clone());
            kind_sum += flag.clone();
        }
        eval.add_constraint(active.clone() * (kind_sum - one.clone()));

        let double_flag = kind_flags[PREPARED_TABLE_EC_KIND_DOUBLE_P].clone()
            + kind_flags[PREPARED_TABLE_EC_KIND_DOUBLE_R].clone();
        eval.add_constraint(active.clone() * (op.clone() - double_flag.clone()));

        let mut expected_table_index = E::F::from(M31::from_u32_unchecked(0));
        for base_index in 0..PREPARED_BASE_COUNT {
            expected_table_index += kind_flags[PREPARED_TABLE_EC_KIND_BASE_START + base_index]
                .clone()
                * E::F::from(M31::from_u32_unchecked(base_index as u32));
        }
        expected_table_index += kind_flags[PREPARED_TABLE_EC_KIND_TABLE16].clone()
            * E::F::from(M31::from_u32_unchecked(TABLE16_INDEX));
        eval.add_constraint(active.clone() * (table_index.clone() - expected_table_index));

        eval.add_constraint(double_flag.clone() * (rhs.inf.clone() - one.clone()));
        lhs.add_constraints(&mut eval, &active, &one);
        rhs.add_constraints(&mut eval, &active, &one);
        output.add_constraints(&mut eval, &active, &one);
        neg.add_constraints(&mut eval, &active, &one);

        // In-AIR negation: on DoubleR, `neg = -lhs (= -R)`; on AddR2R,
        // `neg = -output (= -R3)`. Prove `neg.x = src.x` and the limb addition
        // `neg.y + src.y = p` via the witnessed boolean carries. On all other
        // rows `neg = 0` and `neg_carries = 0` (gated away below).
        let neg_flag = kind_flags[PREPARED_TABLE_EC_KIND_DOUBLE_R].clone()
            + kind_flags[PREPARED_TABLE_EC_KIND_ADD_R2R].clone();
        let src = prepared_table_ec_negation_source::<E>(&kind_flags, &lhs, &output);
        add_negation_constraints(&mut eval, &neg_flag, &src, &neg, &neg_carries, &one);
        // Rows that do not witness a negation must carry `neg = 0` and zero carries.
        let not_neg = active.clone() - neg_flag.clone();
        for value in neg
            .x
            .iter()
            .chain(neg.y.iter())
            .cloned()
            .chain(core::iter::once(neg.inf.clone()))
            .chain(neg_carries.iter().cloned())
        {
            eval.add_constraint(not_neg.clone() * value);
        }

        for value in [
            source_index.clone(),
            sig_id.clone(),
            cert_id.clone(),
            op.clone(),
            table_index.clone(),
        ] {
            eval.add_constraint((one.clone() - active.clone()) * value);
        }

        let relation_values = prepared_table_ec_row_relation_values(
            &[
                source_index,
                sig_id.clone(),
                cert_id.clone(),
                op,
                table_index,
            ],
            &lhs,
            &rhs,
            &output,
        );
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(active.clone()),
            &relation_values,
        ));

        if let Some(pinning) = &self.pinning {
            // cert_id must be boolean so `is_cert0 = 1 - cert_id` selects cert0.
            eval.add_constraint(active.clone() * cert_id.clone() * (cert_id.clone() - one.clone()));
            add_pinning_emissions(
                &mut eval,
                pinning,
                &active,
                &sig_id,
                &cert_id,
                &kind_flags,
                &lhs,
                &rhs,
                &output,
                &neg,
            );
        }

        eval.finalize_logup();
        eval
    }
}

// --- Shared pinning emission schedule ---------------------------------------
//
// Both `add_pinning_emissions` (AIR) and `gen_prepared_table_ec_row_pinned_*`
// (interaction trace) iterate this single static list so the AIR numerators and
// the committed logup fractions are the SAME low-degree polynomials in the same
// order (lessons.md #39, #42). Each entry contributes exactly one logup fraction
// per row; the numerator is the signed multiplicity times the gate product
// (which is zero unless the row's kind/cert matches).

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

/// Select the negation source point: `lhs` on `DoubleR` rows, `output` on
/// `AddR2R` rows, `0` elsewhere. Exactly one kind flag is set on a neg row.
fn prepared_table_ec_negation_source<E: EvalAtRow>(
    kind_flags: &[E::F; PREPARED_TABLE_EC_KIND_FLAGS],
    lhs: &PreparedTableEcEvalPoint<E::F>,
    output: &PreparedTableEcEvalPoint<E::F>,
) -> PreparedTableEcEvalPoint<E::F> {
    let double_r = kind_flags[PREPARED_TABLE_EC_KIND_DOUBLE_R].clone();
    let add_r2r = kind_flags[PREPARED_TABLE_EC_KIND_ADD_R2R].clone();
    let select = |a: &E::F, b: &E::F| double_r.clone() * a.clone() + add_r2r.clone() * b.clone();
    PreparedTableEcEvalPoint {
        x: core::array::from_fn(|i| select(&lhs.x[i], &output.x[i])),
        y: core::array::from_fn(|i| select(&lhs.y[i], &output.y[i])),
        inf: select(&lhs.inf, &output.inf),
    }
}

/// Constrain `neg = -src` (gated by `neg_flag`): `neg.x = src.x`, `neg.inf =
/// src.inf`, and the limb addition `neg.y + src.y = p` via boolean carries. All
/// constraints stay degree ≤ 2: the boolean carry constraint is ungated (carries
/// on non-neg rows are forced to zero by the `not_neg` padding loop).
fn add_negation_constraints<E: EvalAtRow>(
    eval: &mut E,
    neg_flag: &E::F,
    src: &PreparedTableEcEvalPoint<E::F>,
    neg: &PreparedTableEcEvalPoint<E::F>,
    neg_carries: &[E::F; PREPARED_TABLE_EC_NEG_CARRY_COLUMNS],
    one: &E::F,
) {
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    let p_limbs = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS));
    eval.add_constraint(neg_flag.clone() * (neg.inf.clone() - src.inf.clone()));
    for i in 0..N_LIMBS {
        eval.add_constraint(neg_flag.clone() * (neg.x[i].clone() - src.x[i].clone()));
        // Boolean carry (ungated; degree 2).
        let carry = neg_carries[i].clone();
        eval.add_constraint(carry.clone() * (carry.clone() - one.clone()));
        let prev_carry = if i == 0 {
            E::F::from(M31::from_u32_unchecked(0))
        } else {
            neg_carries[i - 1].clone()
        };
        let p_limb = E::F::from(p_limbs.limbs()[i]);
        // neg.y[i] + src.y[i] + prev_carry - p[i] - carry * 2^13 = 0.
        eval.add_constraint(
            neg_flag.clone()
                * (neg.y[i].clone() + src.y[i].clone() + prev_carry
                    - p_limb
                    - carry * limb_base.clone()),
        );
    }
    // The most-significant carry must vanish: neg.y + src.y == p exactly.
    eval.add_constraint(neg_flag.clone() * neg_carries[N_LIMBS - 1].clone());
}

/// Build a `CertBaseRelation` tuple `(sig_id, cert_id, point.x[..], point.y[..])`
/// for the cell's base point.
fn cert_base_relation_values<F: Clone + From<M31>>(
    sig_id: &F,
    cert_id: &F,
    point: &PreparedTableEcEvalPoint<F>,
) -> [F; CERT_BASE_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0 => sig_id.clone(),
        1 => cert_id.clone(),
        2..=21 => point.x[index - 2].clone(),
        22..=41 => point.y[index - 2 - N_LIMBS].clone(),
        _ => unreachable!("cert base relation index in range"),
    })
}

/// Build a `PreparedTableCanonicalRelation` tuple `(sig_id, cert_id, role, point[41])`.
fn canonical_relation_values<F: Clone + From<M31>>(
    sig_id: &F,
    cert_id: &F,
    role: u32,
    point: &PreparedTableEcEvalPoint<F>,
) -> [F; PREPARED_TABLE_CANONICAL_RELATION_ARITY] {
    let point_values = point.relation_values();
    core::array::from_fn(|index| match index {
        0 => sig_id.clone(),
        1 => cert_id.clone(),
        2 => F::from(M31::from_u32_unchecked(role)),
        3..=43 => point_values[index - 3].clone(),
        _ => unreachable!("canonical relation index in range"),
    })
}

/// The fixed constant `3·G` as an eval point (cert0's pinned `P3`).
fn three_g_point<F: Clone + From<M31>>() -> PreparedTableEcEvalPoint<F> {
    let x = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_3GX));
    let y = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_3GY));
    PreparedTableEcEvalPoint {
        x: core::array::from_fn(|i| F::from(x.limbs()[i])),
        y: core::array::from_fn(|i| F::from(y.limbs()[i])),
        inf: F::from(M31::from_u32_unchecked(0)),
    }
}

/// Emit the fixed `PIN_SCHEDULE` of `CertBaseRelation` +
/// `PreparedTableCanonicalRelation` fractions for one EC row. Every row emits the
/// SAME ordered set of entries; numerators are gated to zero when the row's
/// kind/cert does not match. Mirrored exactly by
/// `gen_prepared_table_ec_row_pinned_interaction_trace`.
#[allow(clippy::too_many_arguments)]
fn add_pinning_emissions<E: EvalAtRow>(
    eval: &mut E,
    pinning: &PreparedTablePinningRelations,
    active: &E::F,
    sig_id: &E::F,
    cert_id: &E::F,
    kind_flags: &[E::F; PREPARED_TABLE_EC_KIND_FLAGS],
    lhs: &PreparedTableEcEvalPoint<E::F>,
    rhs: &PreparedTableEcEvalPoint<E::F>,
    output: &PreparedTableEcEvalPoint<E::F>,
    neg: &PreparedTableEcEvalPoint<E::F>,
) {
    let is_cert0 = active.clone() - cert_id.clone();
    let three_g = three_g_point::<E::F>();
    for entry in PIN_SCHEDULE {
        let mut gate = E::F::from(M31::from_u32_unchecked(1));
        for &k in entry.kinds {
            gate = gate * kind_flags[k].clone();
        }
        if entry.cert0_only {
            gate = gate * is_cert0.clone();
        }
        let point = match entry.point {
            PinPoint::Lhs => lhs,
            PinPoint::Rhs => rhs,
            PinPoint::Output => output,
            PinPoint::Neg => neg,
            PinPoint::ConstThreeG => &three_g,
        };
        let numerator = signed_numerator::<E>(gate, entry.mult);
        match entry.relation {
            PinRelation::CertBase => eval.add_to_relation(RelationEntry::new(
                &pinning.cert_base,
                numerator,
                &cert_base_relation_values::<E::F>(sig_id, cert_id, point),
            )),
            PinRelation::Canonical(role) => eval.add_to_relation(RelationEntry::new(
                &pinning.canonical,
                numerator,
                &canonical_relation_values::<E::F>(sig_id, cert_id, role, point),
            )),
        }
    }

    // FinalCheckHint: yield `R_i` (= `lhs`) once per active `DoubleR` row, gated
    // `active * DoubleR_flag`, multiplicity `-1`. Always emitted (one fraction
    // per row) so the AIR numerator and the interaction trace stay in lockstep;
    // the numerator is zero on non-`DoubleR`/padding rows. The relation tuple is
    // the canonical-pinned `R_i`, so this forwards an already-bound value.
    if let Some(final_check_hint) = &pinning.final_check_hint {
        let gate = active.clone() * kind_flags[PREPARED_TABLE_EC_KIND_DOUBLE_R].clone();
        eval.add_to_relation(RelationEntry::new(
            final_check_hint,
            -E::EF::from(gate),
            &final_check_hint_relation_values::<E::F>(sig_id, cert_id, lhs),
        ));
    }
}

/// Build a `FinalCheckHintRelation` tuple `(sig_id, cert_id, point[41])`.
fn final_check_hint_relation_values<F: Clone + From<M31>>(
    sig_id: &F,
    cert_id: &F,
    point: &PreparedTableEcEvalPoint<F>,
) -> [F; FINAL_CHECK_HINT_RELATION_ARITY] {
    let point_values = point.relation_values();
    core::array::from_fn(|index| match index {
        0 => sig_id.clone(),
        1 => cert_id.clone(),
        2..=42 => point_values[index - 2].clone(),
        _ => unreachable!("final check hint relation index in range"),
    })
}

/// `mult · gate` as an extension-field numerator (`mult` may be negative).
fn signed_numerator<E: EvalAtRow>(gate: E::F, mult: i32) -> E::EF {
    let magnitude = E::F::from(M31::from_u32_unchecked(mult.unsigned_abs()));
    let scaled = E::EF::from(gate * magnitude);
    if mult < 0 {
        -scaled
    } else {
        scaled
    }
}

#[derive(Clone)]
pub struct PreparedTableProjectiveSourceEval {
    pub log_size: u32,
    pub relation: PreparedTableEcRowRelation,
}

impl FrameworkEval for PreparedTableProjectiveSourceEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.next_trace_mask();
        let source_index = eval.next_trace_mask();
        let sig_id = eval.next_trace_mask();
        let cert_id = eval.next_trace_mask();
        let op = eval.next_trace_mask();
        let table_index = eval.next_trace_mask();
        let lhs = PreparedTableEcEvalPoint::read(&mut eval);
        let rhs = PreparedTableEcEvalPoint::read(&mut eval);
        let output = PreparedTableEcEvalPoint::read(&mut eval);
        let one = E::F::from(M31::from_u32_unchecked(1));

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        lhs.add_constraints(&mut eval, &active, &one);
        rhs.add_constraints(&mut eval, &active, &one);
        output.add_constraints(&mut eval, &active, &one);

        for value in [
            source_index.clone(),
            sig_id.clone(),
            cert_id.clone(),
            op.clone(),
            table_index.clone(),
        ] {
            eval.add_constraint((one.clone() - active.clone()) * value);
        }

        let relation_values = prepared_table_ec_row_relation_values(
            &[source_index, sig_id, cert_id, op, table_index],
            &lhs,
            &rhs,
            &output,
        );
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            E::EF::from(active),
            &relation_values,
        ));
        eval.finalize_logup();
        eval
    }
}

#[derive(Clone, Debug)]
pub(crate) struct PreparedTableEcEvalPoint<F> {
    x: [F; N_LIMBS],
    y: [F; N_LIMBS],
    inf: F,
}

impl<F: Clone> PreparedTableEcEvalPoint<F> {
    pub(crate) fn relation_values(&self) -> [F; PREPARED_TABLE_EC_POINT_COLUMNS] {
        core::array::from_fn(|index| match index {
            0..=19 => self.x[index].clone(),
            20..=39 => self.y[index - N_LIMBS].clone(),
            40 => self.inf.clone(),
            _ => unreachable!("prepared-table EC point relation index is in range"),
        })
    }
}

impl<F> PreparedTableEcEvalPoint<F> {
    pub(crate) fn read<E: EvalAtRow<F = F>>(eval: &mut E) -> Self {
        Self {
            x: core::array::from_fn(|_| eval.next_trace_mask()),
            y: core::array::from_fn(|_| eval.next_trace_mask()),
            inf: eval.next_trace_mask(),
        }
    }
}

impl<F> PreparedTableEcEvalPoint<F>
where
    F: Clone + core::ops::Add<Output = F> + core::ops::Sub<Output = F> + core::ops::Mul<Output = F>,
{
    pub(crate) fn add_constraints<E: EvalAtRow<F = F>>(&self, eval: &mut E, active: &F, one: &F) {
        eval.add_constraint(self.inf.clone() * (self.inf.clone() - one.clone()));
        for limb in self.x.iter().chain(self.y.iter()) {
            eval.add_constraint(self.inf.clone() * limb.clone());
            eval.add_constraint((one.clone() - active.clone()) * limb.clone());
        }
        eval.add_constraint((one.clone() - active.clone()) * self.inf.clone());
    }
}

pub(crate) fn gen_prepared_table_ec_row_preprocessed_trace(
    log_size: u32,
    ids: &[PreProcessedColumnId],
) -> Result<ColumnVec<M31ColumnEval>, PreparedTableError> {
    ids.iter()
        .map(|id| {
            if id == &prepared_table_ec_row_index_column_id() {
                Ok(m31_column_eval(
                    log_size,
                    (0..(1usize << log_size))
                        .map(|index| M31::from_u32_unchecked(index as u32))
                        .collect(),
                ))
            } else {
                Err(PreparedTableError::PreprocessedColumnMissing)
            }
        })
        .collect()
}

pub(crate) fn gen_prepared_table_ec_row_base_trace(
    trace: &PreparedTableEcTraceClaim,
    log_size: u32,
) -> Result<ColumnVec<M31ColumnEval>, PreparedTableError> {
    let padded_rows = 1usize << log_size;
    if trace.rows.len() > padded_rows {
        return Err(PreparedTableError::EcTraceRowsExceedDomain {
            rows: trace.rows.len(),
            domain: padded_rows,
        });
    }
    let mut rows = trace
        .rows
        .iter()
        .enumerate()
        .map(|(source_index, row)| prepared_table_ec_row_trace_values(source_index, row))
        .collect::<Vec<_>>();
    rows.resize(
        padded_rows,
        [M31::from_u32_unchecked(0); PREPARED_TABLE_EC_ROW_TRACE_COLUMNS],
    );
    Ok(columns_from_rows(log_size, rows))
}

pub(crate) fn gen_prepared_table_projective_source_base_trace(
    prepared: &PreparedTableEcTraceClaim,
    projective: &ProjectiveEcTraceClaim,
    log_size: u32,
) -> Result<ColumnVec<M31ColumnEval>, PreparedTableError> {
    let padded_rows = 1usize << log_size;
    if prepared.rows.len() > padded_rows {
        return Err(PreparedTableError::EcTraceRowsExceedDomain {
            rows: prepared.rows.len(),
            domain: padded_rows,
        });
    }
    if projective.rows.len() < prepared.rows.len() {
        return Err(PreparedTableError::ProjectiveSourcePrefixTooShort {
            prepared: prepared.rows.len(),
            projective: projective.rows.len(),
        });
    }
    let mut rows = prepared
        .rows
        .iter()
        .zip(projective.rows.iter())
        .enumerate()
        .map(|(source_index, (prepared_row, projective_row))| {
            prepared_table_projective_source_trace_values(
                source_index,
                prepared_row,
                projective_row,
            )
        })
        .collect::<Vec<_>>();
    rows.resize(
        padded_rows,
        [M31::from_u32_unchecked(0); PREPARED_TABLE_PROJECTIVE_SOURCE_TRACE_COLUMNS],
    );
    Ok(columns_from_rows(log_size, rows))
}

pub(crate) fn gen_prepared_table_ec_row_interaction_trace(
    base: &[M31ColumnEval],
    relation: &PreparedTableEcRowRelation,
) -> (ColumnVec<M31ColumnEval>, PreparedTableEcRowInteractionClaim) {
    assert_eq!(base.len(), PREPARED_TABLE_EC_ROW_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let values = prepared_table_ec_row_packed_relation_values(base, vec_row);
        let numerator = -PackedQM31::from(base[0].data[vec_row]);
        let denominator: PackedQM31 = relation.combine(&values);
        col.write_frac(vec_row, numerator, denominator);
    }
    col.finalize_col();
    let (trace, claimed_sum) = logup.finalize_last();
    (trace, PreparedTableEcRowInteractionClaim { claimed_sum })
}

// Base-trace column offsets for the EC-row provider (used by the pinned
// interaction trace generator). Layout: active, source_index, sig_id, cert_id,
// kind_flags[13], op, table_index, lhs[41], rhs[41], output[41], neg[41],
// neg_carries[20].
const PREPARED_TABLE_EC_COL_SIG_ID: usize = 2;
const PREPARED_TABLE_EC_COL_CERT_ID: usize = 3;
const PREPARED_TABLE_EC_COL_KIND_FLAGS: usize = 4;
const PREPARED_TABLE_EC_COL_LHS: usize = 4 + PREPARED_TABLE_EC_KIND_FLAGS + 2;
const PREPARED_TABLE_EC_COL_RHS: usize = PREPARED_TABLE_EC_COL_LHS + PREPARED_TABLE_EC_POINT_COLUMNS;
const PREPARED_TABLE_EC_COL_OUTPUT: usize =
    PREPARED_TABLE_EC_COL_RHS + PREPARED_TABLE_EC_POINT_COLUMNS;
const PREPARED_TABLE_EC_COL_NEG: usize =
    PREPARED_TABLE_EC_COL_OUTPUT + PREPARED_TABLE_EC_POINT_COLUMNS;

fn pin_point_column_offset(point: PinPoint) -> Option<usize> {
    match point {
        PinPoint::Lhs => Some(PREPARED_TABLE_EC_COL_LHS),
        PinPoint::Rhs => Some(PREPARED_TABLE_EC_COL_RHS),
        PinPoint::Output => Some(PREPARED_TABLE_EC_COL_OUTPUT),
        PinPoint::Neg => Some(PREPARED_TABLE_EC_COL_NEG),
        PinPoint::ConstThreeG => None,
    }
}

/// Per-relation claimed sums of the pinned EC-row provider's logup trace. `total`
/// is what the provider component declares; the breakdown lets `verify_balanced`
/// check each relation independently.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PreparedTableEcRowPinnedInteractionClaim {
    pub total_claimed_sum: SecureField,
    pub prepared_table_provider_claimed_sum: SecureField,
    pub cert_base_consumer_claimed_sum: SecureField,
    pub canonical_claimed_sum: SecureField,
    /// FinalCheckHint provider sum (yield `-1` per active `DoubleR` row). Zero
    /// when no `final_check_hint` relation is forwarded.
    pub final_check_hint_claimed_sum: SecureField,
}

impl PreparedTableEcRowPinnedInteractionClaim {
    pub fn zero() -> Self {
        Self {
            total_claimed_sum: secure_zero(),
            prepared_table_provider_claimed_sum: secure_zero(),
            cert_base_consumer_claimed_sum: secure_zero(),
            canonical_claimed_sum: secure_zero(),
            final_check_hint_claimed_sum: secure_zero(),
        }
    }
}

/// Interaction trace for the monolithic EC-row provider: the base
/// `PreparedTableEcRowRelation` yield plus the 30 `PIN_SCHEDULE` fractions, in
/// the exact order emitted by `PreparedTableEcRowEval::evaluate`. When
/// `final_check_hint` is `Some`, one more fraction is appended (the `DoubleR`
/// `R_i` yield) to mirror the AIR's FinalCheckHint emission.
pub(crate) fn gen_prepared_table_ec_row_pinned_interaction_trace(
    base: &[M31ColumnEval],
    relation: &PreparedTableEcRowRelation,
    cert_base: &CertBaseRelation,
    canonical: &PreparedTableCanonicalRelation,
    final_check_hint: Option<&FinalCheckHintRelation>,
) -> (ColumnVec<M31ColumnEval>, PreparedTableEcRowPinnedInteractionClaim) {
    assert_eq!(base.len(), PREPARED_TABLE_EC_ROW_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let n_vec_rows = 1 << (log_size - LOG_N_LANES);
    let mut logup = LogupTraceGenerator::new(log_size);

    // Column 0: the existing PreparedTableEcRowRelation yield (-active).
    let mut col = logup.new_col();
    for vec_row in 0..n_vec_rows {
        let values = prepared_table_ec_row_packed_relation_values(base, vec_row);
        col.write_frac(
            vec_row,
            -PackedQM31::from(base[0].data[vec_row]),
            relation.combine(&values),
        );
    }
    col.finalize_col();

    let three_g_x = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_3GX));
    let three_g_y = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_3GY));

    // Columns 1..=30: the pinning schedule, one fraction per entry.
    for entry in PIN_SCHEDULE {
        let mut col = logup.new_col();
        for vec_row in 0..n_vec_rows {
            let sig = base[PREPARED_TABLE_EC_COL_SIG_ID].data[vec_row];
            let cert = base[PREPARED_TABLE_EC_COL_CERT_ID].data[vec_row];
            let active = base[0].data[vec_row];
            // Gate = product of kind flags (× is_cert0 = active - cert_id).
            let mut gate = PackedM31::broadcast(M31::from_u32_unchecked(1));
            for &k in entry.kinds {
                gate *= base[PREPARED_TABLE_EC_COL_KIND_FLAGS + k].data[vec_row];
            }
            if entry.cert0_only {
                gate *= active - cert;
            }
            let magnitude = PackedM31::broadcast(M31::from_u32_unchecked(entry.mult.unsigned_abs()));
            let scaled = PackedQM31::from(gate * magnitude);
            let numerator = if entry.mult < 0 { -scaled } else { scaled };
            let denominator: PackedQM31 = match entry.relation {
                PinRelation::CertBase => {
                    let offset = pin_point_column_offset(entry.point)
                        .expect("CertBase entries use a trace point");
                    cert_base.combine(&cert_base_packed_tuple(base, vec_row, sig, cert, offset))
                }
                PinRelation::Canonical(role) => {
                    let tuple = match pin_point_column_offset(entry.point) {
                        Some(offset) => {
                            canonical_packed_tuple_from_columns(base, vec_row, sig, cert, role, offset)
                        }
                        None => canonical_packed_tuple_const(
                            sig,
                            cert,
                            role,
                            &three_g_x,
                            &three_g_y,
                        ),
                    };
                    canonical.combine(&tuple)
                }
            };
            col.write_frac(vec_row, numerator, denominator);
        }
        col.finalize_col();
    }

    // Optional FinalCheckHint column: yield `R_i` (= `lhs`) gated `active *
    // DoubleR_flag`, multiplicity `-1`. Emitted iff a relation is supplied, in
    // lockstep with the AIR's `if let Some(final_check_hint)` emission.
    if let Some(final_check_hint) = final_check_hint {
        let mut col = logup.new_col();
        for vec_row in 0..n_vec_rows {
            let sig = base[PREPARED_TABLE_EC_COL_SIG_ID].data[vec_row];
            let cert = base[PREPARED_TABLE_EC_COL_CERT_ID].data[vec_row];
            let active = base[0].data[vec_row];
            let double_r = base
                [PREPARED_TABLE_EC_COL_KIND_FLAGS + PREPARED_TABLE_EC_KIND_DOUBLE_R]
                .data[vec_row];
            let gate = active * double_r;
            let numerator = -PackedQM31::from(gate);
            let denominator = final_check_hint.combine(&final_check_hint_packed_tuple(
                base,
                vec_row,
                sig,
                cert,
                PREPARED_TABLE_EC_COL_LHS,
            ));
            col.write_frac(vec_row, numerator, denominator);
        }
        col.finalize_col();
    }

    let (trace, total_claimed_sum) = logup.finalize_last();

    // Per-relation breakdown over storage rows (active rows only).
    let mut prepared_table_provider_claimed_sum = secure_zero();
    let mut cert_base_consumer_claimed_sum = secure_zero();
    let mut canonical_claimed_sum = secure_zero();
    let mut final_check_hint_claimed_sum = secure_zero();
    for row in prepared_table_ec_storage_rows(base) {
        let active = row[0];
        if active == M31::from_u32_unchecked(0) {
            continue;
        }
        let sig = row[PREPARED_TABLE_EC_COL_SIG_ID];
        let cert = row[PREPARED_TABLE_EC_COL_CERT_ID];
        // Existing relation yield (-active).
        let values = prepared_table_ec_row_unpacked_relation_values(&row);
        let existing_denom: SecureField = relation.combine(&values);
        prepared_table_provider_claimed_sum += -SecureField::from(active) / existing_denom;
        // FinalCheckHint yield (-1) on active DoubleR rows.
        if let Some(final_check_hint) = final_check_hint {
            let double_r = row[PREPARED_TABLE_EC_COL_KIND_FLAGS + PREPARED_TABLE_EC_KIND_DOUBLE_R];
            if double_r != M31::from_u32_unchecked(0) {
                let denom: SecureField = final_check_hint.combine(&final_check_hint_unpacked_tuple(
                    &row,
                    sig,
                    cert,
                    PREPARED_TABLE_EC_COL_LHS,
                ));
                final_check_hint_claimed_sum += -SecureField::from(active * double_r) / denom;
            }
        }
        for entry in PIN_SCHEDULE {
            let mut gate = M31::from_u32_unchecked(1);
            for &k in entry.kinds {
                gate *= row[PREPARED_TABLE_EC_COL_KIND_FLAGS + k];
            }
            if entry.cert0_only {
                gate *= active - cert;
            }
            if gate == M31::from_u32_unchecked(0) {
                continue;
            }
            let magnitude = M31::from_u32_unchecked(entry.mult.unsigned_abs());
            let scaled = SecureField::from(gate * magnitude);
            let numerator = if entry.mult < 0 { -scaled } else { scaled };
            match entry.relation {
                PinRelation::CertBase => {
                    let offset = pin_point_column_offset(entry.point).unwrap();
                    let denom: SecureField =
                        cert_base.combine(&cert_base_unpacked_tuple(&row, sig, cert, offset));
                    cert_base_consumer_claimed_sum += numerator / denom;
                }
                PinRelation::Canonical(role) => {
                    let tuple = match pin_point_column_offset(entry.point) {
                        Some(offset) => {
                            canonical_unpacked_tuple_from_columns(&row, sig, cert, role, offset)
                        }
                        None => {
                            canonical_unpacked_tuple_const(sig, cert, role, &three_g_x, &three_g_y)
                        }
                    };
                    let denom: SecureField = canonical.combine(&tuple);
                    canonical_claimed_sum += numerator / denom;
                }
            }
        }
    }

    (
        trace,
        PreparedTableEcRowPinnedInteractionClaim {
            total_claimed_sum,
            prepared_table_provider_claimed_sum,
            cert_base_consumer_claimed_sum,
            canonical_claimed_sum,
            final_check_hint_claimed_sum,
        },
    )
}

fn final_check_hint_packed_tuple(
    base: &[M31ColumnEval],
    vec_row: usize,
    sig: PackedM31,
    cert: PackedM31,
    point_offset: usize,
) -> [PackedM31; FINAL_CHECK_HINT_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0 => sig,
        1 => cert,
        2..=21 => base[point_offset + (index - 2)].data[vec_row],
        22..=41 => base[point_offset + N_LIMBS + (index - 22)].data[vec_row],
        42 => base[point_offset + 2 * N_LIMBS].data[vec_row],
        _ => unreachable!("final check hint tuple index in range"),
    })
}

fn final_check_hint_unpacked_tuple(
    row: &[M31],
    sig: M31,
    cert: M31,
    point_offset: usize,
) -> [M31; FINAL_CHECK_HINT_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0 => sig,
        1 => cert,
        2..=21 => row[point_offset + (index - 2)],
        22..=41 => row[point_offset + N_LIMBS + (index - 22)],
        42 => row[point_offset + 2 * N_LIMBS],
        _ => unreachable!("final check hint tuple index in range"),
    })
}

fn cert_base_packed_tuple(
    base: &[M31ColumnEval],
    vec_row: usize,
    sig: PackedM31,
    cert: PackedM31,
    point_offset: usize,
) -> [PackedM31; CERT_BASE_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0 => sig,
        1 => cert,
        2..=21 => base[point_offset + (index - 2)].data[vec_row],
        22..=41 => base[point_offset + N_LIMBS + (index - 22)].data[vec_row],
        _ => unreachable!("cert base tuple index in range"),
    })
}

fn cert_base_unpacked_tuple(
    row: &[M31],
    sig: M31,
    cert: M31,
    point_offset: usize,
) -> [M31; CERT_BASE_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0 => sig,
        1 => cert,
        2..=21 => row[point_offset + (index - 2)],
        22..=41 => row[point_offset + N_LIMBS + (index - 22)],
        _ => unreachable!("cert base tuple index in range"),
    })
}

fn canonical_packed_tuple_from_columns(
    base: &[M31ColumnEval],
    vec_row: usize,
    sig: PackedM31,
    cert: PackedM31,
    role: u32,
    point_offset: usize,
) -> [PackedM31; PREPARED_TABLE_CANONICAL_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0 => sig,
        1 => cert,
        2 => PackedM31::broadcast(M31::from_u32_unchecked(role)),
        3..=43 => base[point_offset + (index - 3)].data[vec_row],
        _ => unreachable!("canonical tuple index in range"),
    })
}

fn canonical_packed_tuple_const(
    sig: PackedM31,
    cert: PackedM31,
    role: u32,
    x: &P256M31BigInt,
    y: &P256M31BigInt,
) -> [PackedM31; PREPARED_TABLE_CANONICAL_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0 => sig,
        1 => cert,
        2 => PackedM31::broadcast(M31::from_u32_unchecked(role)),
        3..=22 => PackedM31::broadcast(x.limbs()[index - 3]),
        23..=42 => PackedM31::broadcast(y.limbs()[index - 23]),
        43 => PackedM31::broadcast(M31::from_u32_unchecked(0)),
        _ => unreachable!("canonical const tuple index in range"),
    })
}

fn canonical_unpacked_tuple_from_columns(
    row: &[M31],
    sig: M31,
    cert: M31,
    role: u32,
    point_offset: usize,
) -> [M31; PREPARED_TABLE_CANONICAL_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0 => sig,
        1 => cert,
        2 => M31::from_u32_unchecked(role),
        3..=43 => row[point_offset + (index - 3)],
        _ => unreachable!("canonical tuple index in range"),
    })
}

fn canonical_unpacked_tuple_const(
    sig: M31,
    cert: M31,
    role: u32,
    x: &P256M31BigInt,
    y: &P256M31BigInt,
) -> [M31; PREPARED_TABLE_CANONICAL_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0 => sig,
        1 => cert,
        2 => M31::from_u32_unchecked(role),
        3..=22 => x.limbs()[index - 3],
        23..=42 => y.limbs()[index - 23],
        43 => M31::from_u32_unchecked(0),
        _ => unreachable!("canonical const tuple index in range"),
    })
}

fn prepared_table_ec_storage_rows(base: &[M31ColumnEval]) -> impl Iterator<Item = Vec<M31>> + '_ {
    let row_count = base[0].domain.size();
    (0..row_count).map(move |row| {
        let vec_row = row / (1 << LOG_N_LANES);
        let lane = row % (1 << LOG_N_LANES);
        base.iter()
            .map(|column| column.data[vec_row].to_array()[lane])
            .collect::<Vec<_>>()
    })
}

fn prepared_table_ec_row_unpacked_relation_values(
    row: &[M31],
) -> [M31; PREPARED_TABLE_EC_ROW_RELATION_ARITY] {
    core::array::from_fn(|index| {
        let column = match index {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 17,
            4 => 18,
            5..=127 => 19 + (index - 5),
            _ => unreachable!("prepared-table EC relation index is in range"),
        };
        row[column]
    })
}

pub(crate) fn gen_prepared_table_projective_source_interaction_trace(
    base: &[M31ColumnEval],
    relation: &PreparedTableEcRowRelation,
) -> (ColumnVec<M31ColumnEval>, PreparedTableEcRowInteractionClaim) {
    assert_eq!(base.len(), PREPARED_TABLE_PROJECTIVE_SOURCE_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let values = prepared_table_projective_source_packed_relation_values(base, vec_row);
        let numerator = PackedQM31::from(base[0].data[vec_row]);
        let denominator: PackedQM31 = relation.combine(&values);
        col.write_frac(vec_row, numerator, denominator);
    }
    col.finalize_col();
    let (trace, claimed_sum) = logup.finalize_last();
    (trace, PreparedTableEcRowInteractionClaim { claimed_sum })
}

fn prepared_table_ec_row_packed_relation_values(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; PREPARED_TABLE_EC_ROW_RELATION_ARITY] {
    core::array::from_fn(|index| {
        let column = match index {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 17,
            4 => 18,
            5..=127 => 19 + (index - 5),
            _ => unreachable!("prepared-table EC packed relation index is in range"),
        };
        base[column].data[vec_row]
    })
}

fn prepared_table_projective_source_packed_relation_values(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; PREPARED_TABLE_EC_ROW_RELATION_ARITY] {
    core::array::from_fn(|index| {
        let column = match index {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 4,
            4 => 5,
            5..=127 => 6 + (index - 5),
            _ => unreachable!("prepared-table projective source relation index is in range"),
        };
        base[column].data[vec_row]
    })
}

fn prepared_table_ec_row_index_column_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: PREPARED_TABLE_EC_ROW_INDEX_COLUMN.into(),
    }
}

fn prepared_table_ec_row_trace_values(
    source_index: usize,
    row: &PreparedTableEcRow,
) -> [M31; PREPARED_TABLE_EC_ROW_TRACE_COLUMNS] {
    let mut values = [M31::from_u32_unchecked(0); PREPARED_TABLE_EC_ROW_TRACE_COLUMNS];
    let mut column = 0;
    values[column] = M31::from_u32_unchecked(1);
    column += 1;
    values[column] = M31::from_u32_unchecked(source_index as u32);
    column += 1;
    values[column] = row.sig_id;
    column += 1;
    values[column] = row.cert_id;
    column += 1;
    for flag in kind_flags(row.kind) {
        values[column] = flag;
        column += 1;
    }
    values[column] = prepared_table_ec_op_code(row.kind);
    column += 1;
    values[column] = prepared_table_ec_table_index(row.kind);
    column += 1;
    for value in prepared_table_ec_point_values(&row.lhs) {
        values[column] = value;
        column += 1;
    }
    for value in prepared_table_ec_point_values(&row.rhs) {
        values[column] = value;
        column += 1;
    }
    for value in prepared_table_ec_point_values(&row.output) {
        values[column] = value;
        column += 1;
    }
    // Negation aux block: `neg = -src` plus `neg.y + src.y = p` carries.
    //   DoubleR: src = lhs (= R)   -> neg = -R
    //   AddR2R:  src = output (= R3) -> neg = -R3
    //   otherwise: neg = 0, carries = 0 (padding-gated in the AIR).
    let neg_source = match row.kind {
        PreparedTableEcRowKind::DoubleR => Some(&row.lhs),
        PreparedTableEcRowKind::AddR2R => Some(&row.output),
        _ => None,
    };
    let (neg_point, neg_carries) = match neg_source {
        Some(src) => prepared_table_ec_negation_witness(src),
        None => (
            PreparedAffinePoint::from_zero_limbs(),
            [M31::from_u32_unchecked(0); PREPARED_TABLE_EC_NEG_CARRY_COLUMNS],
        ),
    };
    for value in prepared_table_ec_point_values(&neg_point) {
        values[column] = value;
        column += 1;
    }
    for carry in neg_carries {
        values[column] = carry;
        column += 1;
    }
    debug_assert_eq!(column, PREPARED_TABLE_EC_ROW_TRACE_COLUMNS);
    values
}

/// Witness the negation `neg = -src` (canonical limbs) together with the boolean
/// carries of the limb addition `neg.y + src.y = p`. Because `neg.y, src.y < p`
/// and (for a finite `src`) `neg.y + src.y = p` exactly, every carry is in
/// `{0, 1}` and the top carry vanishes.
fn prepared_table_ec_negation_witness(
    src: &PreparedAffinePoint,
) -> (
    PreparedAffinePoint,
    [M31; PREPARED_TABLE_EC_NEG_CARRY_COLUMNS],
) {
    let neg = prepared(negate_optional(src.to_option()));
    let p_limbs = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS));
    let mut carries = [M31::from_u32_unchecked(0); PREPARED_TABLE_EC_NEG_CARRY_COLUMNS];
    let mut carry: u32 = 0;
    let limb_modulus = 1u32 << LIMB_BITS;
    for i in 0..N_LIMBS {
        let sum = neg.y.limbs()[i].0 + src.y.limbs()[i].0 + carry;
        carry = sum / limb_modulus;
        debug_assert!(carry <= 1, "negation carry must be boolean");
        debug_assert_eq!(
            sum % limb_modulus,
            p_limbs.limbs()[i].0,
            "negation limb addition must reconstruct the modulus"
        );
        carries[i] = M31::from_u32_unchecked(carry);
    }
    debug_assert_eq!(carry, 0, "negation top carry must vanish");
    (neg, carries)
}

fn prepared_table_projective_source_trace_values(
    source_index: usize,
    prepared_row: &PreparedTableEcRow,
    projective_row: &crate::projective::ProjectiveEcRow,
) -> [M31; PREPARED_TABLE_PROJECTIVE_SOURCE_TRACE_COLUMNS] {
    let mut values = [M31::from_u32_unchecked(0); PREPARED_TABLE_PROJECTIVE_SOURCE_TRACE_COLUMNS];
    let mut column = 0;
    values[column] = M31::from_u32_unchecked(1);
    column += 1;
    values[column] = M31::from_u32_unchecked(source_index as u32);
    column += 1;
    values[column] = projective_row.sig_id;
    column += 1;
    values[column] = projective_row.cert_id;
    column += 1;
    values[column] = projective_ec_op_code(projective_row.op);
    column += 1;
    values[column] = prepared_table_ec_table_index(prepared_row.kind);
    column += 1;
    for value in prepared_table_ec_point_values(&projective_row.lhs_affine) {
        values[column] = value;
        column += 1;
    }
    for value in prepared_table_ec_point_values(&projective_row.rhs_affine) {
        values[column] = value;
        column += 1;
    }
    for value in prepared_table_ec_point_values(&projective_row.output_affine) {
        values[column] = value;
        column += 1;
    }
    debug_assert_eq!(column, PREPARED_TABLE_PROJECTIVE_SOURCE_TRACE_COLUMNS);
    values
}

fn prepared_table_ec_row_relation_values<F: Clone>(
    header: &[F; 5],
    lhs: &impl PreparedTableEcPointLike<F>,
    rhs: &impl PreparedTableEcPointLike<F>,
    output: &impl PreparedTableEcPointLike<F>,
) -> [F; PREPARED_TABLE_EC_ROW_RELATION_ARITY] {
    let lhs = lhs.relation_values();
    let rhs = rhs.relation_values();
    let output = output.relation_values();
    core::array::from_fn(|index| match index {
        0..=4 => header[index].clone(),
        5..=45 => lhs[index - 5].clone(),
        46..=86 => rhs[index - 46].clone(),
        87..=127 => output[index - 87].clone(),
        _ => unreachable!("prepared-table EC row relation index is in range"),
    })
}

trait PreparedTableEcPointLike<F: Clone> {
    fn relation_values(&self) -> [F; PREPARED_TABLE_EC_POINT_COLUMNS];
}

impl<F: Clone> PreparedTableEcPointLike<F> for PreparedTableEcEvalPoint<F> {
    fn relation_values(&self) -> [F; PREPARED_TABLE_EC_POINT_COLUMNS] {
        self.relation_values()
    }
}

#[derive(Clone, Debug)]
struct PreparedTableEcPointValues {
    x: [M31; N_LIMBS],
    y: [M31; N_LIMBS],
    inf: M31,
}

impl PreparedTableEcPointValues {
    fn from_prepared(point: &PreparedAffinePoint) -> Self {
        Self {
            x: *point.x.limbs(),
            y: *point.y.limbs(),
            inf: point.inf,
        }
    }
}

impl PreparedTableEcPointLike<M31> for PreparedTableEcPointValues {
    fn relation_values(&self) -> [M31; PREPARED_TABLE_EC_POINT_COLUMNS] {
        core::array::from_fn(|index| match index {
            0..=19 => self.x[index],
            20..=39 => self.y[index - N_LIMBS],
            40 => self.inf,
            _ => unreachable!("prepared-table EC point relation index is in range"),
        })
    }
}

pub(crate) fn prepared_table_ec_point_values(
    point: &PreparedAffinePoint,
) -> [M31; PREPARED_TABLE_EC_POINT_COLUMNS] {
    PreparedTableEcPointValues::from_prepared(point).relation_values()
}

fn columns_from_rows<const N: usize>(
    log_size: u32,
    rows: Vec<[M31; N]>,
) -> ColumnVec<M31ColumnEval> {
    (0..N)
        .map(|column| m31_column_eval(log_size, rows.iter().map(|row| row[column]).collect()))
        .collect()
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

fn secure_zero() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(0))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedTableEcRow {
    pub sig_id: M31,
    pub cert_id: M31,
    pub kind: PreparedTableEcRowKind,
    pub lhs: PreparedAffinePoint,
    pub rhs: PreparedAffinePoint,
    pub output: PreparedAffinePoint,
}

impl PreparedTableEcRow {
    fn double(
        sig_id: M31,
        cert_id: M31,
        kind: PreparedTableEcRowKind,
        input: PreparedAffinePoint,
        output: PreparedAffinePoint,
    ) -> Self {
        Self {
            sig_id,
            cert_id,
            kind,
            lhs: input,
            rhs: PreparedAffinePoint::infinity(),
            output,
        }
    }

    fn add(
        sig_id: M31,
        cert_id: M31,
        kind: PreparedTableEcRowKind,
        lhs: PreparedAffinePoint,
        rhs: PreparedAffinePoint,
        output: PreparedAffinePoint,
    ) -> Self {
        Self {
            sig_id,
            cert_id,
            kind,
            lhs,
            rhs,
            output,
        }
    }

    pub fn verify(&self) -> Result<(), PreparedTableError> {
        self.lhs.verify()?;
        self.rhs.verify()?;
        self.output.verify()?;
        let expected = match self.kind {
            PreparedTableEcRowKind::DoubleP | PreparedTableEcRowKind::DoubleR => {
                double_optional(self.lhs.to_option())
            }
            PreparedTableEcRowKind::AddP2P
            | PreparedTableEcRowKind::AddR2R
            | PreparedTableEcRowKind::Base(_)
            | PreparedTableEcRowKind::Table16 => {
                add_optional_points(self.lhs.to_option(), self.rhs.to_option())
            }
        };
        let expected = prepared(expected);
        if self.output == expected {
            Ok(())
        } else {
            Err(PreparedTableError::EcTraceOutputMismatch {
                sig_id: self.sig_id.0,
                cert_id: self.cert_id.0,
                kind: self.kind,
            })
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreparedTableEcRowKind {
    DoubleP,
    AddP2P,
    DoubleR,
    AddR2R,
    Base(u32),
    Table16,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedTableCert {
    pub sig_id: M31,
    pub cert_id: M31,
    pub cert_active: M31,
    pub base: [PreparedAffinePoint; PREPARED_BASE_COUNT],
    pub r3: PreparedAffinePoint,
    pub table16: PreparedAffinePoint,
}

impl PreparedTableCert {
    fn new(
        cert: &CertScalarInputRow,
        fake_glv: &FakeGlvScalarHintRow,
        selector: &FakeGlvSelectorRow,
    ) -> Result<Self, PreparedTableError> {
        require_same_id("fake_glv", cert, fake_glv.sig_id, fake_glv.cert_id)?;
        require_same_id("selector", cert, selector.sig_id, selector.cert_id)?;

        if cert.cert_active.0 == 0 {
            return Ok(Self {
                sig_id: cert.sig_id,
                cert_id: cert.cert_id,
                cert_active: cert.cert_active,
                base: core::array::from_fn(|_| PreparedAffinePoint::infinity()),
                r3: PreparedAffinePoint::infinity(),
                table16: PreparedAffinePoint::infinity(),
            });
        }

        let p = AffinePoint {
            x: cert.base_x.to_u256(),
            y: cert.base_y.to_u256(),
        };
        let h =
            scalar_mul(&cert.scalar.to_u256(), &p).ok_or(PreparedTableError::MissingHintPoint {
                sig_id: cert.sig_id.0,
                cert_id: cert.cert_id.0,
            })?;
        let r = signed_hint_point(&h, fake_glv.hint.s2_sign_bit)?;
        let p3 = scalar_mul(&U256::from_le_u64s(&[3, 0, 0, 0]), &p).ok_or(
            PreparedTableError::MissingTriplePoint {
                point: "P",
                sig_id: cert.sig_id.0,
                cert_id: cert.cert_id.0,
            },
        )?;
        let r3 = scalar_mul(&U256::from_le_u64s(&[3, 0, 0, 0]), &r).ok_or(
            PreparedTableError::MissingTriplePoint {
                point: "R",
                sig_id: cert.sig_id.0,
                cert_id: cert.cert_id.0,
            },
        )?;

        let base = [
            prepared(add_optional_points(
                Some(p3.clone()),
                negate_optional(Some(r.clone())),
            )),
            prepared(add_optional_points(
                Some(p.clone()),
                negate_optional(Some(r.clone())),
            )),
            prepared(add_optional_points(Some(p.clone()), Some(r.clone()))),
            prepared(add_optional_points(Some(p3.clone()), Some(r.clone()))),
            prepared(add_optional_points(
                Some(p3.clone()),
                negate_optional(Some(r3.clone())),
            )),
            prepared(add_optional_points(
                Some(p.clone()),
                negate_optional(Some(r3.clone())),
            )),
            prepared(add_optional_points(Some(p.clone()), Some(r3.clone()))),
            prepared(add_optional_points(Some(p3.clone()), Some(r3.clone()))),
        ];

        let selector0 =
            Selector16DecodeEntry::from_selector(selector.selectors[0]).map_err(|_| {
                PreparedTableError::InvalidSelector {
                    selector: selector.selectors[0].0,
                }
            })?;
        let selected = apply_selector(&base, selector0)?;
        let table16 = prepared(add_optional_points(selected.to_option(), Some(r3.clone())));

        Ok(Self {
            sig_id: cert.sig_id,
            cert_id: cert.cert_id,
            cert_active: cert.cert_active,
            base,
            r3: prepared(Some(r3)),
            table16,
        })
    }

    /// Test-only variant of [`Self::new`] that substitutes an injected hint
    /// point `R'` for the production `R = signed_hint(scalar_mul(u, base))`.
    /// Every R-derived cell (`R3 = 3R'`, `base[]`, `table16`) is recomputed
    /// from `R'` so the resulting cert is internally consistent for an
    /// arbitrary (possibly wrong) `R'`. Used to probe whether the in-AIR
    /// scalar multiplication binds `R` to `u·base`.
    #[cfg(test)]
    pub(crate) fn new_with_r_override(
        cert: &CertScalarInputRow,
        _fake_glv: &FakeGlvScalarHintRow,
        selector: &FakeGlvSelectorRow,
        r_override: AffinePoint,
    ) -> Result<Self, PreparedTableError> {
        assert_eq!(cert.cert_active.0, 1, "override path requires active cert");
        let p = AffinePoint {
            x: cert.base_x.to_u256(),
            y: cert.base_y.to_u256(),
        };
        let r = r_override;
        let p3 = scalar_mul(&U256::from_le_u64s(&[3, 0, 0, 0]), &p).ok_or(
            PreparedTableError::MissingTriplePoint {
                point: "P",
                sig_id: cert.sig_id.0,
                cert_id: cert.cert_id.0,
            },
        )?;
        let r3 = scalar_mul(&U256::from_le_u64s(&[3, 0, 0, 0]), &r).ok_or(
            PreparedTableError::MissingTriplePoint {
                point: "R",
                sig_id: cert.sig_id.0,
                cert_id: cert.cert_id.0,
            },
        )?;

        let base = [
            prepared(add_optional_points(
                Some(p3.clone()),
                negate_optional(Some(r.clone())),
            )),
            prepared(add_optional_points(
                Some(p.clone()),
                negate_optional(Some(r.clone())),
            )),
            prepared(add_optional_points(Some(p.clone()), Some(r.clone()))),
            prepared(add_optional_points(Some(p3.clone()), Some(r.clone()))),
            prepared(add_optional_points(
                Some(p3.clone()),
                negate_optional(Some(r3.clone())),
            )),
            prepared(add_optional_points(
                Some(p.clone()),
                negate_optional(Some(r3.clone())),
            )),
            prepared(add_optional_points(Some(p.clone()), Some(r3.clone()))),
            prepared(add_optional_points(Some(p3.clone()), Some(r3.clone()))),
        ];

        let selector0 =
            Selector16DecodeEntry::from_selector(selector.selectors[0]).map_err(|_| {
                PreparedTableError::InvalidSelector {
                    selector: selector.selectors[0].0,
                }
            })?;
        let selected = apply_selector(&base, selector0)?;
        let table16 = prepared(add_optional_points(selected.to_option(), Some(r3.clone())));

        Ok(Self {
            sig_id: cert.sig_id,
            cert_id: cert.cert_id,
            cert_active: cert.cert_active,
            base,
            r3: prepared(Some(r3)),
            table16,
        })
    }

    pub fn verify(&self) -> Result<(), PreparedTableError> {
        if self.cert_active.0 > 1 {
            return Err(PreparedTableError::NonBooleanFlag {
                field: "cert_active",
                actual: self.cert_active.0,
            });
        }
        for point in &self.base {
            point.verify()?;
        }
        self.r3.verify()?;
        self.table16.verify()?;
        Ok(())
    }

    pub fn instance(&self, table_index: u32) -> Option<PreparedPointInstance<M31>> {
        let point = match table_index {
            0..=7 => self.base[table_index as usize].clone(),
            TABLE16_INDEX => self.table16.clone(),
            _ => return None,
        };
        Some(point.instance(self.sig_id, self.cert_id, table_index))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedAffinePoint {
    pub x: P256M31BigInt,
    pub y: P256M31BigInt,
    pub inf: M31,
}

impl PreparedAffinePoint {
    pub const fn infinity() -> Self {
        Self {
            x: P256M31BigInt::zero(),
            y: P256M31BigInt::zero(),
            inf: M31::from_u32_unchecked(1),
        }
    }

    pub fn from_affine(point: AffinePoint) -> Self {
        Self {
            x: P256M31BigInt::from_u256(&point.x),
            y: P256M31BigInt::from_u256(&point.y),
            inf: M31::from_u32_unchecked(0),
        }
    }

    /// All-zero point (`x = y = 0`, `inf = 0`). Used as the inert filler for the
    /// negation aux block on rows that do not witness a negation; distinct from
    /// [`Self::infinity`] (which sets `inf = 1`).
    pub const fn from_zero_limbs() -> Self {
        Self {
            x: P256M31BigInt::zero(),
            y: P256M31BigInt::zero(),
            inf: M31::from_u32_unchecked(0),
        }
    }

    pub fn verify(&self) -> Result<(), PreparedTableError> {
        if self.inf.0 > 1 {
            return Err(PreparedTableError::NonBooleanFlag {
                field: "inf",
                actual: self.inf.0,
            });
        }
        if self.inf.0 == 1 && (self.x != P256M31BigInt::zero() || self.y != P256M31BigInt::zero()) {
            return Err(PreparedTableError::NonCanonicalInfinity);
        }
        Ok(())
    }

    pub fn to_option(&self) -> Option<AffinePoint> {
        (self.inf.0 == 0).then(|| AffinePoint {
            x: self.x.to_u256(),
            y: self.y.to_u256(),
        })
    }

    pub fn instance(
        &self,
        sig_id: M31,
        cert_id: M31,
        table_index: u32,
    ) -> PreparedPointInstance<M31> {
        PreparedPointInstance {
            sig_id,
            cert_id,
            table_index: M31::from_u32_unchecked(table_index),
            x: self.x.clone(),
            y: self.y.clone(),
            inf: self.inf,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreparedTableError {
    RowCountMismatch {
        certs: usize,
        fake_glv: usize,
        selectors: usize,
    },
    UseCountCountMismatch {
        tables: usize,
        use_counts: usize,
    },
    EcTraceCountMismatch {
        certs: usize,
        fake_glv: usize,
        selectors: usize,
        tables: usize,
    },
    IdMismatch {
        source: &'static str,
        cert_sig_id: u32,
        cert_cert_id: u32,
        other_sig_id: u32,
        other_cert_id: u32,
    },
    InvalidSelector {
        selector: u32,
    },
    NonBooleanFlag {
        field: &'static str,
        actual: u32,
    },
    MissingHintPoint {
        sig_id: u32,
        cert_id: u32,
    },
    MissingTriplePoint {
        point: &'static str,
        sig_id: u32,
        cert_id: u32,
    },
    EcTraceOutputMismatch {
        sig_id: u32,
        cert_id: u32,
        kind: PreparedTableEcRowKind,
    },
    PreparedTableOutputMismatch {
        sig_id: u32,
        cert_id: u32,
        table_index: u32,
    },
    PreparedPointTraceMismatch,
    InactiveEcTraceRows {
        sig_id: u32,
        cert_id: u32,
    },
    EcTraceCertRowCountMismatch {
        sig_id: u32,
        cert_id: u32,
        expected: usize,
        actual: usize,
    },
    EcTraceExpectedOutputMissing {
        sig_id: u32,
        cert_id: u32,
        label: &'static str,
    },
    EcTraceExpectedOutputDuplicate {
        sig_id: u32,
        cert_id: u32,
        label: &'static str,
    },
    EcTraceExpectedOutputMismatch {
        sig_id: u32,
        cert_id: u32,
        label: &'static str,
    },
    EcTraceRowsExceedDomain {
        rows: usize,
        domain: usize,
    },
    ProjectiveSourcePrefixTooShort {
        prepared: usize,
        projective: usize,
    },
    ProjectiveSourceInvalid,
    RelationImbalance {
        relation: &'static str,
    },
    PreprocessedColumnMissing,
    NonCanonicalInfinity,
    ProofLayer,
}

fn require_unique_output(
    rows: &[&PreparedTableEcRow],
    sig_id: M31,
    cert_id: M31,
    kind: PreparedTableEcRowKind,
    label: &'static str,
    expected: &PreparedAffinePoint,
) -> Result<(), PreparedTableError> {
    let matches = rows
        .iter()
        .copied()
        .filter(|row| row.kind == kind)
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [] => Err(PreparedTableError::EcTraceExpectedOutputMissing {
            sig_id: sig_id.0,
            cert_id: cert_id.0,
            label,
        }),
        [row] if &row.output == expected => Ok(()),
        [_row] => Err(PreparedTableError::EcTraceExpectedOutputMismatch {
            sig_id: sig_id.0,
            cert_id: cert_id.0,
            label,
        }),
        _ => Err(PreparedTableError::EcTraceExpectedOutputDuplicate {
            sig_id: sig_id.0,
            cert_id: cert_id.0,
            label,
        }),
    }
}

fn prepared_table_ec_rows_for_cert(
    cert: &CertScalarInputRow,
    fake_glv: &FakeGlvScalarHintRow,
    selector: &FakeGlvSelectorRow,
    table: &PreparedTableCert,
) -> Result<Vec<PreparedTableEcRow>, PreparedTableError> {
    require_same_id("fake_glv", cert, fake_glv.sig_id, fake_glv.cert_id)?;
    require_same_id("selector", cert, selector.sig_id, selector.cert_id)?;
    if cert.sig_id != table.sig_id || cert.cert_id != table.cert_id {
        return Err(PreparedTableError::IdMismatch {
            source: "prepared_table",
            cert_sig_id: cert.sig_id.0,
            cert_cert_id: cert.cert_id.0,
            other_sig_id: table.sig_id.0,
            other_cert_id: table.cert_id.0,
        });
    }
    if cert.cert_active.0 == 0 {
        return Ok(Vec::new());
    }

    let sig_id = cert.sig_id;
    let cert_id = cert.cert_id;
    let p = PreparedAffinePoint::from_affine(AffinePoint {
        x: cert.base_x.to_u256(),
        y: cert.base_y.to_u256(),
    });
    let h = scalar_mul(
        &cert.scalar.to_u256(),
        &p.to_option().expect("base point finite"),
    )
    .ok_or(PreparedTableError::MissingHintPoint {
        sig_id: cert.sig_id.0,
        cert_id: cert.cert_id.0,
    })?;
    let r = PreparedAffinePoint::from_affine(signed_hint_point(&h, fake_glv.hint.s2_sign_bit)?);

    let mut rows = Vec::new();
    let p3 = if cert.cert_id.0 == CERT_ID_U1_GENERATOR {
        PreparedAffinePoint::from_affine(
            scalar_mul(&U256::from_le_u64s(&[3, 0, 0, 0]), &p.to_option().unwrap()).ok_or(
                PreparedTableError::MissingTriplePoint {
                    point: "P",
                    sig_id: cert.sig_id.0,
                    cert_id: cert.cert_id.0,
                },
            )?,
        )
    } else {
        let p2 = prepared(double_optional(p.to_option()));
        rows.push(PreparedTableEcRow::double(
            sig_id,
            cert_id,
            PreparedTableEcRowKind::DoubleP,
            p.clone(),
            p2.clone(),
        ));
        let p3 = prepared(add_optional_points(p2.to_option(), p.to_option()));
        rows.push(PreparedTableEcRow::add(
            sig_id,
            cert_id,
            PreparedTableEcRowKind::AddP2P,
            p2,
            p.clone(),
            p3.clone(),
        ));
        p3
    };

    let r2 = prepared(double_optional(r.to_option()));
    rows.push(PreparedTableEcRow::double(
        sig_id,
        cert_id,
        PreparedTableEcRowKind::DoubleR,
        r.clone(),
        r2.clone(),
    ));
    rows.push(PreparedTableEcRow::add(
        sig_id,
        cert_id,
        PreparedTableEcRowKind::AddR2R,
        r2.clone(),
        r.clone(),
        table.r3.clone(),
    ));

    let base_operands = [
        (p3.clone(), prepared(negate_optional(r.to_option()))),
        (p.clone(), prepared(negate_optional(r.to_option()))),
        (p.clone(), r.clone()),
        (p3.clone(), r.clone()),
        (p3.clone(), prepared(negate_optional(table.r3.to_option()))),
        (p.clone(), prepared(negate_optional(table.r3.to_option()))),
        (p.clone(), table.r3.clone()),
        (p3.clone(), table.r3.clone()),
    ];

    for (index, (lhs, rhs)) in base_operands.into_iter().enumerate() {
        let output = table.base[index].clone();
        rows.push(PreparedTableEcRow::add(
            sig_id,
            cert_id,
            PreparedTableEcRowKind::Base(index as u32),
            lhs.clone(),
            rhs.clone(),
            output.clone(),
        ));
        let expected = prepared(add_optional_points(lhs.to_option(), rhs.to_option()));
        if output != expected {
            return Err(PreparedTableError::PreparedTableOutputMismatch {
                sig_id: sig_id.0,
                cert_id: cert_id.0,
                table_index: index as u32,
            });
        }
    }

    let selector0 = Selector16DecodeEntry::from_selector(selector.selectors[0]).map_err(|_| {
        PreparedTableError::InvalidSelector {
            selector: selector.selectors[0].0,
        }
    })?;
    let selected = apply_selector(&table.base, selector0)?;
    rows.push(PreparedTableEcRow::add(
        sig_id,
        cert_id,
        PreparedTableEcRowKind::Table16,
        selected.clone(),
        table.r3.clone(),
        table.table16.clone(),
    ));
    let expected_table16 = prepared(add_optional_points(
        selected.to_option(),
        table.r3.to_option(),
    ));
    if table.table16 != expected_table16 {
        return Err(PreparedTableError::PreparedTableOutputMismatch {
            sig_id: sig_id.0,
            cert_id: cert_id.0,
            table_index: TABLE16_INDEX,
        });
    }

    Ok(rows)
}

/// Test-only variant of [`prepared_table_ec_rows_for_cert`] that uses an
/// injected `R'` instead of the production `R`. Mirrors the production row
/// shape exactly, sourcing R-derived outputs from `table` (which must itself
/// be built from the same `R'`). The internal `output == expected` checks are
/// kept verbatim so trace fidelity is preserved for an arbitrary `R'`.
#[cfg(test)]
fn prepared_table_ec_rows_for_cert_with_r_override(
    cert: &CertScalarInputRow,
    selector: &FakeGlvSelectorRow,
    table: &PreparedTableCert,
    r_override: AffinePoint,
) -> Result<Vec<PreparedTableEcRow>, PreparedTableError> {
    assert_eq!(cert.cert_active.0, 1, "override path requires active cert");
    let sig_id = cert.sig_id;
    let cert_id = cert.cert_id;
    let p = PreparedAffinePoint::from_affine(AffinePoint {
        x: cert.base_x.to_u256(),
        y: cert.base_y.to_u256(),
    });
    let r = PreparedAffinePoint::from_affine(r_override);

    let mut rows = Vec::new();
    let p3 = if cert.cert_id.0 == CERT_ID_U1_GENERATOR {
        PreparedAffinePoint::from_affine(
            scalar_mul(&U256::from_le_u64s(&[3, 0, 0, 0]), &p.to_option().unwrap()).ok_or(
                PreparedTableError::MissingTriplePoint {
                    point: "P",
                    sig_id: cert.sig_id.0,
                    cert_id: cert.cert_id.0,
                },
            )?,
        )
    } else {
        let p2 = prepared(double_optional(p.to_option()));
        rows.push(PreparedTableEcRow::double(
            sig_id,
            cert_id,
            PreparedTableEcRowKind::DoubleP,
            p.clone(),
            p2.clone(),
        ));
        let p3 = prepared(add_optional_points(p2.to_option(), p.to_option()));
        rows.push(PreparedTableEcRow::add(
            sig_id,
            cert_id,
            PreparedTableEcRowKind::AddP2P,
            p2,
            p.clone(),
            p3.clone(),
        ));
        p3
    };

    let r2 = prepared(double_optional(r.to_option()));
    rows.push(PreparedTableEcRow::double(
        sig_id,
        cert_id,
        PreparedTableEcRowKind::DoubleR,
        r.clone(),
        r2.clone(),
    ));
    rows.push(PreparedTableEcRow::add(
        sig_id,
        cert_id,
        PreparedTableEcRowKind::AddR2R,
        r2.clone(),
        r.clone(),
        table.r3.clone(),
    ));

    let base_operands = [
        (p3.clone(), prepared(negate_optional(r.to_option()))),
        (p.clone(), prepared(negate_optional(r.to_option()))),
        (p.clone(), r.clone()),
        (p3.clone(), r.clone()),
        (p3.clone(), prepared(negate_optional(table.r3.to_option()))),
        (p.clone(), prepared(negate_optional(table.r3.to_option()))),
        (p.clone(), table.r3.clone()),
        (p3.clone(), table.r3.clone()),
    ];

    for (index, (lhs, rhs)) in base_operands.into_iter().enumerate() {
        let output = table.base[index].clone();
        rows.push(PreparedTableEcRow::add(
            sig_id,
            cert_id,
            PreparedTableEcRowKind::Base(index as u32),
            lhs.clone(),
            rhs.clone(),
            output.clone(),
        ));
        let expected = prepared(add_optional_points(lhs.to_option(), rhs.to_option()));
        if output != expected {
            return Err(PreparedTableError::PreparedTableOutputMismatch {
                sig_id: sig_id.0,
                cert_id: cert_id.0,
                table_index: index as u32,
            });
        }
    }

    let selector0 = Selector16DecodeEntry::from_selector(selector.selectors[0]).map_err(|_| {
        PreparedTableError::InvalidSelector {
            selector: selector.selectors[0].0,
        }
    })?;
    let selected = apply_selector(&table.base, selector0)?;
    rows.push(PreparedTableEcRow::add(
        sig_id,
        cert_id,
        PreparedTableEcRowKind::Table16,
        selected.clone(),
        table.r3.clone(),
        table.table16.clone(),
    ));
    let expected_table16 = prepared(add_optional_points(
        selected.to_option(),
        table.r3.to_option(),
    ));
    if table.table16 != expected_table16 {
        return Err(PreparedTableError::PreparedTableOutputMismatch {
            sig_id: sig_id.0,
            cert_id: cert_id.0,
            table_index: TABLE16_INDEX,
        });
    }

    Ok(rows)
}

/// Test-only: build a [`PreparedTableEcTraceClaim`] where the cert at
/// `override_cert_index` uses the injected `R'`; all other certs use the
/// production path. Skips the cross-`verify` against the native (true-R)
/// derivation so a wrong-`R'` trace can be assembled.
#[cfg(test)]
impl PreparedTableEcTraceClaim {
    pub(crate) fn from_claims_with_r_override(
        cert_inputs: &CertScalarInputClaim,
        fake_glv_scalars: &FakeGlvScalarHintClaim,
        selectors: &FakeGlvSelectorClaim,
        table: &PreparedTableClaim,
        override_cert_index: usize,
        r_override: AffinePoint,
    ) -> Result<Self, PreparedTableError> {
        let mut rows = Vec::new();
        for (index, (((cert, fake_glv), selector), table_cert)) in cert_inputs
            .rows
            .iter()
            .zip(&fake_glv_scalars.rows)
            .zip(&selectors.rows)
            .zip(&table.certs)
            .enumerate()
        {
            if index == override_cert_index {
                rows.extend(prepared_table_ec_rows_for_cert_with_r_override(
                    cert,
                    selector,
                    table_cert,
                    r_override.clone(),
                )?);
            } else {
                rows.extend(prepared_table_ec_rows_for_cert(
                    cert, fake_glv, selector, table_cert,
                )?);
            }
        }
        Ok(Self { rows })
    }
}

/// Test-only: build a [`PreparedTableClaim`] where the cert at
/// `override_cert_index` is rebuilt from the injected `R'`.
#[cfg(test)]
impl PreparedTableClaim {
    pub(crate) fn from_claims_with_r_override(
        cert_inputs: &CertScalarInputClaim,
        fake_glv_scalars: &FakeGlvScalarHintClaim,
        selectors: &FakeGlvSelectorClaim,
        override_cert_index: usize,
        r_override: AffinePoint,
    ) -> Result<Self, PreparedTableError> {
        let certs = cert_inputs
            .rows
            .iter()
            .zip(&fake_glv_scalars.rows)
            .zip(&selectors.rows)
            .enumerate()
            .map(|(index, ((cert, fake_glv), selector))| {
                if index == override_cert_index {
                    PreparedTableCert::new_with_r_override(
                        cert,
                        fake_glv,
                        selector,
                        r_override.clone(),
                    )
                } else {
                    PreparedTableCert::new(cert, fake_glv, selector)
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self { certs })
    }
}

fn require_same_id(
    source: &'static str,
    cert: &CertScalarInputRow,
    other_sig_id: M31,
    other_cert_id: M31,
) -> Result<(), PreparedTableError> {
    if cert.sig_id == other_sig_id && cert.cert_id == other_cert_id {
        Ok(())
    } else {
        Err(PreparedTableError::IdMismatch {
            source,
            cert_sig_id: cert.sig_id.0,
            cert_cert_id: cert.cert_id.0,
            other_sig_id: other_sig_id.0,
            other_cert_id: other_cert_id.0,
        })
    }
}

fn signed_hint_point(h: &AffinePoint, s2_sign_bit: M31) -> Result<AffinePoint, PreparedTableError> {
    match s2_sign_bit.0 {
        0 => Ok(h.clone()),
        1 => Ok(negate_point(h)),
        actual => Err(PreparedTableError::NonBooleanFlag {
            field: "s2_sign_bit",
            actual,
        }),
    }
}

fn apply_selector(
    base: &[PreparedAffinePoint; PREPARED_BASE_COUNT],
    selector: Selector16DecodeEntry,
) -> Result<PreparedAffinePoint, PreparedTableError> {
    let base_index = selector.base_index.0 as usize;
    let point = base
        .get(base_index)
        .cloned()
        .ok_or(PreparedTableError::InvalidSelector {
            selector: selector.selector.0,
        })?;
    if selector.neg_bit.0 == 0 {
        Ok(point)
    } else if selector.neg_bit.0 == 1 {
        Ok(prepared(negate_optional(point.to_option())))
    } else {
        Err(PreparedTableError::NonBooleanFlag {
            field: "selector.neg_bit",
            actual: selector.neg_bit.0,
        })
    }
}

fn prepared(point: Option<AffinePoint>) -> PreparedAffinePoint {
    point.map_or_else(
        PreparedAffinePoint::infinity,
        PreparedAffinePoint::from_affine,
    )
}

fn add_optional_points(lhs: Option<AffinePoint>, rhs: Option<AffinePoint>) -> Option<AffinePoint> {
    match (lhs, rhs) {
        (None, None) => None,
        (Some(point), None) | (None, Some(point)) => Some(point),
        (Some(lhs), Some(rhs)) if lhs == rhs => Some(point_double(&lhs).output),
        (Some(lhs), Some(rhs)) if is_additive_inverse(&lhs, &rhs) => None,
        (Some(lhs), Some(rhs)) => Some(point_add(&lhs, &rhs).output),
    }
}

fn double_optional(point: Option<AffinePoint>) -> Option<AffinePoint> {
    point.map(|point| point_double(&point).output)
}

fn negate_optional(point: Option<AffinePoint>) -> Option<AffinePoint> {
    point.map(|point| negate_point(&point))
}

fn negate_point(point: &AffinePoint) -> AffinePoint {
    AffinePoint {
        x: point.x.clone(),
        y: sub_mod_witness(
            &U256::from_le_u64s(&P256_MODULUS),
            &point.y,
            &U256::from_le_u64s(&P256_MODULUS),
        )
        .result
        .to_u256(),
    }
}

fn is_additive_inverse(lhs: &AffinePoint, rhs: &AffinePoint) -> bool {
    lhs.x == rhs.x
        && add_mod_witness(&lhs.y, &rhs.y, &U256::from_le_u64s(&P256_MODULUS))
            .result
            .to_u256()
            == U256::ZERO
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY};
    use crate::scalar::cert_bind::CERT_ID_U2_PUBLIC_KEY;
    use crate::fake_glv_chain::FakeGlvPrimitiveEcTraceClaim;
    use crate::projective::ProjectiveEcTraceClaim;
    use crate::public_inputs::PublicEcdsaInputClaim;
    use crate::scalar::cert_bind::CertScalarInputClaim;
    use crate::scalar::fake_glv_scalar::{FakeGlvScalarHint, FakeGlvScalarHintClaim};
    use crate::scalar::fake_glv_selector::FakeGlvSelectorClaim;
    use crate::scalar::setup_air::ScalarSetupClaim;
    use crate::types::{Signature, U256};
    use stwo::core::channel::Blake2sChannel;
    use stwo::core::fri::FriConfig;
    use stwo::core::pcs::PcsConfig;
    use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
    use stwo_constraint_framework::assert_constraints_on_polys;

    fn test_input(message_hash: u64, r: u64, s: u64) -> crate::types::EcdsaVerifyInput {
        crate::types::EcdsaVerifyInput {
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

    fn build_table(
        message_hash: u64,
    ) -> (
        CertScalarInputClaim,
        FakeGlvScalarHintClaim,
        FakeGlvSelectorClaim,
        PreparedTableClaim,
    ) {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(message_hash, 77, 1)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let hints = certs
            .rows
            .iter()
            .map(|row| FakeGlvScalarHint::trivial_for_small_scalar(&row.scalar).unwrap())
            .collect();
        let fake_glv =
            FakeGlvScalarHintClaim::from_cert_inputs(&certs, hints).expect("valid hints");
        let selectors =
            FakeGlvSelectorClaim::from_scalar_hints(&fake_glv).expect("valid selectors");
        let table =
            PreparedTableClaim::from_claims(&certs, &fake_glv, &selectors).expect("valid table");
        (certs, fake_glv, selectors, table)
    }

    #[test]
    fn prepared_table_generates_active_base_and_table16_points() {
        let (_, _, _, table) = build_table(42);

        assert_eq!(table.certs.len(), 2);
        for cert in &table.certs {
            assert_eq!(cert.cert_active.0, 1);
            for point in &cert.base {
                point.verify().expect("base point is canonical");
            }
            assert_eq!(cert.r3.inf.0, 0);
            assert_eq!(cert.table16.inf.0, 0);
        }
    }

    #[test]
    fn prepared_table_table16_matches_selector0_plus_r3() {
        let (_, _, selectors, table) = build_table(42);

        for (selector, cert) in selectors.rows.iter().zip(&table.certs) {
            let decoded = Selector16DecodeEntry::from_selector(selector.selectors[0]).unwrap();
            let selected = apply_selector(&cert.base, decoded).unwrap();
            let expected = prepared(add_optional_points(
                selected.to_option(),
                cert.r3.to_option(),
            ));

            assert_eq!(cert.table16, expected);
        }
    }

    #[test]
    fn prepared_table_inactive_cert_is_canonical_infinity() {
        let (_, _, _, table) = build_table(0);

        assert_eq!(table.certs[0].cert_active.0, 0);
        assert_eq!(
            table.certs[0].base,
            core::array::from_fn(|_| PreparedAffinePoint::infinity())
        );
        assert_eq!(table.certs[0].r3, PreparedAffinePoint::infinity());
        assert_eq!(table.certs[0].table16, PreparedAffinePoint::infinity());
        assert_eq!(table.certs[1].cert_active.0, 1);
    }

    #[test]
    fn prepared_table_ec_trace_records_expected_active_rows() {
        let (certs, fake_glv, selectors, table) = build_table(42);
        let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
            .expect("valid ec trace");

        trace.verify().expect("ec trace verifies");
        assert_eq!(trace.active_row_count(), 24);
        assert!(trace
            .rows
            .iter()
            .any(|row| row.kind == PreparedTableEcRowKind::Base(0)));
        assert!(trace
            .rows
            .iter()
            .any(|row| row.kind == PreparedTableEcRowKind::Table16));
    }

    #[test]
    fn prepared_table_ec_trace_skips_inactive_zero_branch() {
        let (certs, fake_glv, selectors, table) = build_table(0);
        let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
            .expect("valid ec trace");

        assert_eq!(table.certs[0].cert_active.0, 0);
        assert_eq!(trace.active_row_count(), 13);
        assert!(trace
            .rows
            .iter()
            .all(|row| row.cert_id == table.certs[1].cert_id));
    }

    #[test]
    fn prepared_table_ec_trace_detects_mutated_output() {
        let (certs, fake_glv, selectors, table) = build_table(42);
        let mut trace =
            PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
                .expect("valid ec trace");
        trace.rows[0].output = PreparedAffinePoint::infinity();

        let err = trace.verify().expect_err("mutated output must fail");

        assert!(matches!(
            err,
            PreparedTableError::EcTraceOutputMismatch { .. }
        ));
    }

    #[test]
    fn prepared_table_ec_trace_links_outputs_to_table_points() {
        let (certs, fake_glv, selectors, table) = build_table(42);
        let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
            .expect("valid ec trace");

        trace
            .verify_against_table(&table)
            .expect("ec trace outputs match table points");
    }

    #[test]
    fn prepared_table_ec_row_constraints_pass_for_honest_trace() {
        let (certs, fake_glv, selectors, table) = build_table(42);
        let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
            .expect("valid ec trace");
        let claim = PreparedTableEcRowProofClaim::from_trace(&trace);
        let ids = claim.preprocessed_column_ids();
        let preprocessed =
            gen_prepared_table_ec_row_preprocessed_trace(claim.log_size, &ids).unwrap();
        let base = gen_prepared_table_ec_row_base_trace(&trace, claim.log_size).unwrap();
        let mut channel = Blake2sChannel::default();
        let relation = PreparedTableEcRowRelation::draw(&mut channel);
        let (interaction, interaction_claim) =
            gen_prepared_table_ec_row_interaction_trace(&base, &relation);
        let trace_polys = TreeVec::new(vec![preprocessed, base, interaction]).map(|trace| {
            trace
                .into_iter()
                .map(|column| column.interpolate())
                .collect::<Vec<_>>()
        });

        assert_constraints_on_polys(
            &trace_polys,
            CanonicCoset::new(claim.log_size),
            |eval| {
                PreparedTableEcRowEval {
                    log_size: claim.log_size,
                    relation: relation.clone(),
                    pinning: None,
                }
                .evaluate(eval);
            },
            interaction_claim.claimed_sum,
        );
    }

    #[test]
    fn prepared_table_ec_trace_detects_mutated_table_output_link() {
        let (certs, fake_glv, selectors, mut table) = build_table(42);
        let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
            .expect("valid ec trace");
        table.certs[0].base[0] = PreparedAffinePoint::infinity();

        let err = trace
            .verify_against_table(&table)
            .expect_err("mutated table output link must fail");

        assert!(matches!(
            err,
            PreparedTableError::EcTraceExpectedOutputMismatch { label: "Base", .. }
        ));
    }

    #[test]
    fn prepared_table_prepared_point_trace_matches_table_and_use_counts() {
        let (_, _, selectors, table) = build_table(42);
        let use_counts =
            PreparedPointUseCountClaim::from_selector_claim(&selectors).expect("valid counts");
        let prepared_trace = table
            .prepared_point_trace(&use_counts)
            .expect("prepared trace generates");

        table
            .verify_prepared_point_trace(&use_counts, &prepared_trace)
            .expect("prepared providers match table");
    }

    #[test]
    fn prepared_table_prepared_point_trace_detects_mutated_provider() {
        let (_, _, selectors, table) = build_table(42);
        let use_counts =
            PreparedPointUseCountClaim::from_selector_claim(&selectors).expect("valid counts");
        let mut prepared_trace = table
            .prepared_point_trace(&use_counts)
            .expect("prepared trace generates");
        prepared_trace.providers[0].instance.x = P256M31BigInt::zero();

        let err = table
            .verify_prepared_point_trace(&use_counts, &prepared_trace)
            .expect_err("mutated provider must fail");

        assert_eq!(err, PreparedTableError::PreparedPointTraceMismatch);
    }

    // --- Full-table pinning adversarial audits (rejection oracle = relation
    // balance, lessons.md #18). The honest table must keep `CertBase` and
    // `PreparedTableCanonical` balanced; a wrong base or inconsistent operand
    // must imbalance the matching relation. ---

    /// Draw the three pinning relations from one channel and compute, for the
    /// given (possibly mutated) EC base trace + cert base trace, the
    /// `CertBase` and `PreparedTableCanonical` net sums (zero iff balanced).
    fn pinned_relation_balances(
        certs: &CertScalarInputClaim,
        ec_base: &[M31ColumnEval],
        scalar_setup: &crate::scalar::setup_air::ScalarSetupClaim,
    ) -> (SecureField, SecureField) {
        use crate::scalar::cert_bind::{
            gen_cert_scalar_input_air_base_trace, gen_cert_scalar_input_air_interaction_trace,
            CertScalarInputAirProofClaim, CertScalarInputRelation,
        };
        use crate::scalar::setup_air::ScalarSetupOutputRelation;

        let mut channel = Blake2sChannel::default();
        let setup_relation = ScalarSetupOutputRelation::draw(&mut channel);
        let cert_relation = CertScalarInputRelation::draw(&mut channel);
        let cert_base = CertBaseRelation::draw(&mut channel);
        let prepared_table = PreparedTableEcRowRelation::draw(&mut channel);
        let canonical = PreparedTableCanonicalRelation::draw(&mut channel);

        let cert_claim = CertScalarInputAirProofClaim::from_claim(scalar_setup);
        let cert_base_trace =
            gen_cert_scalar_input_air_base_trace(scalar_setup, certs, cert_claim);
        let (_, cert_interaction) = gen_cert_scalar_input_air_interaction_trace(
            &cert_base_trace,
            &setup_relation,
            &cert_relation,
            Some(&cert_base),
        );

        let (_, pinned) = gen_prepared_table_ec_row_pinned_interaction_trace(
            ec_base,
            &prepared_table,
            &cert_base,
            &canonical,
            None,
        );

        (
            pinned.cert_base_consumer_claimed_sum + cert_interaction.cert_base_provider_claimed_sum,
            pinned.canonical_claimed_sum,
        )
    }

    fn pinning_audit_fixture(
        message_hash: u64,
    ) -> (
        CertScalarInputClaim,
        crate::scalar::setup_air::ScalarSetupClaim,
        PreparedTableEcTraceClaim,
        u32,
    ) {
        use crate::scalar::setup_air::ScalarSetupClaim;
        let public_claim =
            PublicEcdsaInputClaim::from_inputs(&[test_input(message_hash, 77, 1)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let hints = certs
            .rows
            .iter()
            .map(|row| FakeGlvScalarHint::trivial_for_small_scalar(&row.scalar).unwrap())
            .collect();
        let fake_glv =
            FakeGlvScalarHintClaim::from_cert_inputs(&certs, hints).expect("valid hints");
        let selectors =
            FakeGlvSelectorClaim::from_scalar_hints(&fake_glv).expect("valid selectors");
        let table =
            PreparedTableClaim::from_claims(&certs, &fake_glv, &selectors).expect("valid table");
        let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
            .expect("valid ec trace");
        let log_size = PreparedTableEcRowProofClaim::from_trace(&trace).log_size;
        (certs, scalar_setup, trace, log_size)
    }

    #[test]
    fn pinning_honest_trace_balances_cert_base_and_canonical() {
        let (certs, scalar_setup, trace, log_size) = pinning_audit_fixture(42);
        let base = gen_prepared_table_ec_row_base_trace(&trace, log_size).unwrap();
        let (cert_base_balance, canonical_balance) =
            pinned_relation_balances(&certs, &base, &scalar_setup);
        assert_eq!(cert_base_balance, secure_zero(), "CertBase must balance");
        assert_eq!(
            canonical_balance,
            secure_zero(),
            "PreparedTableCanonical must balance"
        );
    }

    #[test]
    fn pinning_honest_trace_balances_with_inactive_cert0_zero_branch() {
        // u1 == 0 => cert0 inactive: no cert0 EC rows, cert-base provider yields
        // `-4·cert_active = 0`. Both relations must still net to zero.
        let (certs, scalar_setup, trace, log_size) = pinning_audit_fixture(0);
        assert_eq!(certs.rows[0].cert_active.0, 0, "cert0 inactive in fixture");
        let base = gen_prepared_table_ec_row_base_trace(&trace, log_size).unwrap();
        let (cert_base_balance, canonical_balance) =
            pinned_relation_balances(&certs, &base, &scalar_setup);
        assert_eq!(cert_base_balance, secure_zero(), "CertBase must balance");
        assert_eq!(
            canonical_balance,
            secure_zero(),
            "PreparedTableCanonical must balance"
        );
    }

    /// Locate the `trace.rows` index for `(cert_id, kind)`.
    fn find_row_index(
        trace: &PreparedTableEcTraceClaim,
        cert_id: u32,
        kind: PreparedTableEcRowKind,
    ) -> usize {
        trace
            .rows
            .iter()
            .position(|row| row.cert_id.0 == cert_id && row.kind == kind)
            .expect("row exists")
    }

    /// Add `1` to limb 0 of `point.x` (a self-consistent, off-cell mutation that
    /// only the pinning relations can detect).
    fn bump_x(point: &mut PreparedAffinePoint) {
        let mut limbs = *point.x.limbs();
        limbs[0] += M31::from_u32_unchecked(1);
        point.x = P256M31BigInt::from_limbs(limbs);
    }

    #[test]
    fn pinning_rejects_cert0_prepared_p_not_equal_generator() {
        // cert0 base must equal G; mutating a cert0 P-cell (Base(1).lhs) away
        // from G leaves the CertBase consumer demanding a point the cert-base
        // provider never yields.
        let (certs, scalar_setup, mut trace, log_size) = pinning_audit_fixture(42);
        let row = find_row_index(&trace, CERT_ID_U1_GENERATOR, PreparedTableEcRowKind::Base(1));
        bump_x(&mut trace.rows[row].lhs);
        let base = gen_prepared_table_ec_row_base_trace(&trace, log_size).unwrap();
        let (cert_base_balance, _) = pinned_relation_balances(&certs, &base, &scalar_setup);
        assert_ne!(
            cert_base_balance,
            secure_zero(),
            "wrong cert0 base P must imbalance CertBase"
        );
    }

    #[test]
    fn pinning_rejects_cert1_prepared_p_not_equal_public_key() {
        // cert1 base must equal the public key Q; mutating a cert1 P-cell
        // (Base(2).lhs) away from Q imbalances CertBase.
        let (certs, scalar_setup, mut trace, log_size) = pinning_audit_fixture(42);
        let row = find_row_index(&trace, CERT_ID_U2_PUBLIC_KEY, PreparedTableEcRowKind::Base(2));
        bump_x(&mut trace.rows[row].lhs);
        let base = gen_prepared_table_ec_row_base_trace(&trace, log_size).unwrap();
        let (cert_base_balance, _) = pinned_relation_balances(&certs, &base, &scalar_setup);
        assert_ne!(
            cert_base_balance,
            secure_zero(),
            "wrong cert1 base P must imbalance CertBase"
        );
    }

    #[test]
    fn pinning_rejects_inconsistent_r_between_base_rows() {
        // Base(2).rhs and Base(3).rhs both consume canonical R. Mutating only
        // Base(2).rhs makes it demand an R the DoubleR provider never yields,
        // imbalancing PreparedTableCanonical.
        let (certs, scalar_setup, mut trace, log_size) = pinning_audit_fixture(42);
        let row = find_row_index(&trace, CERT_ID_U2_PUBLIC_KEY, PreparedTableEcRowKind::Base(2));
        bump_x(&mut trace.rows[row].rhs);
        let base = gen_prepared_table_ec_row_base_trace(&trace, log_size).unwrap();
        let (_, canonical_balance) = pinned_relation_balances(&certs, &base, &scalar_setup);
        assert_ne!(
            canonical_balance,
            secure_zero(),
            "inconsistent R must imbalance PreparedTableCanonical"
        );
    }
}
