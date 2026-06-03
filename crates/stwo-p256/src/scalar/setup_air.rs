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
use stwo_p256_utils::scalar_arithmetic::{
    words_to_limbs, BigIntLimbs, CanonicalLtTrace, ScalarArithmeticError, P256_ORDER,
};

use crate::limbs::{P256BigInt, P256EvalBigInt, P256M31BigInt};
use crate::public_inputs::{
    add_public_ecdsa_instance_consumer, PublicEcdsaInputClaim, PublicEcdsaInstance,
    PublicEcdsaInstanceRelation, PUBLIC_ECDSA_INSTANCE_ARITY,
};
use crate::range_checks::{
    add_range_check, decode_signed_carry, encode_signed_carry, range_check_value_column_id,
    signed_carry_active_column_id, signed_carry_value_column_id, RangeCheckClaim,
    RangeCheckComponent, RangeCheckEval, RangeCheckInteractionClaim, RangeCheckRelation,
    SignedCarryRangeClaim, SignedCarryRangeComponent, SignedCarryRangeEval, RANGE13_BITS,
    RANGE9_BITS,
};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};
use crate::scalar::scalar_mod_mul::relation::ScalarModMulLookupRelations;
use crate::scalar::scalar_mod_mul::{
    ScalarLimbRelation, ROLE_A, ROLE_B, ROLE_QUOTIENT, ROLE_RESULT,
};
use crate::types::U256;

use super::canonical_lt::{add_canonical_lt_fixed_bound, CanonicalLtRelations};
use super::setup_witness::ScalarSetupWitness;

pub const DIGEST_TOP_LIMB_BITS: u32 = 9;
pub const DIGEST_REDUCTION_CARRY_BOUND: i64 = 1;
pub const FULL_FNMUL_MAX_ABS_COMBINED_EXPR: i64 = 5_368_045_569;
pub const M31_CENTERED_BOUND: i64 = (1i64 << 30) - 1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarSetupClaim {
    pub rows: Vec<ScalarSetupRow>,
}

impl ScalarSetupClaim {
    pub fn from_public_inputs(
        public_claim: &PublicEcdsaInputClaim,
    ) -> Result<Self, ScalarSetupClaimError> {
        let rows = public_claim
            .instances
            .iter()
            .map(ScalarSetupRow::from_public_instance)
            .collect::<Result<Vec<_>, _>>()?;
        let claim = Self { rows };
        claim.verify()?;
        Ok(claim)
    }

    pub fn verify(&self) -> Result<(), ScalarSetupClaimError> {
        for row in &self.rows {
            row.verify()?;
        }
        Ok(())
    }

    pub fn public_consumers(&self) -> Vec<PublicEcdsaInstance<M31>> {
        self.rows.iter().map(|row| row.public.clone()).collect()
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.rows.len() as u64);
        for row in &self.rows {
            channel.mix_u64(row.sig_id_u32() as u64);
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarSetupRow {
    pub public: PublicEcdsaInstance<M31>,
    pub witness: ScalarSetupWitness,
    pub output: ScalarSetupOutput<M31>,
}

impl ScalarSetupRow {
    pub fn from_public_instance(
        public: &PublicEcdsaInstance<M31>,
    ) -> Result<Self, ScalarSetupClaimError> {
        let z = public.z.to_u256();
        let r = public.r.to_u256();
        let s = public.s.to_u256();
        let witness = ScalarSetupWitness::new(&z, &r, &s)?;
        let u1 = U256::from_le_u64s(&witness.u1());
        let u2 = U256::from_le_u64s(&witness.u2());
        let row = Self {
            public: public.clone(),
            output: ScalarSetupOutput {
                sig_id: public.sig_id,
                u1: P256M31BigInt::from_u256(&u1),
                u2: P256M31BigInt::from_u256(&u2),
                r: public.r.clone(),
                pub_x: public.pub_x.clone(),
                pub_y: public.pub_y.clone(),
            },
            witness,
        };
        row.verify()?;
        Ok(row)
    }

    pub fn verify(&self) -> Result<(), ScalarSetupClaimError> {
        self.witness.verify()?;
        require_matching_limbs("z", self.public.z.limbs(), &self.witness.trace.z)?;
        require_matching_limbs("r", self.public.r.limbs(), &self.witness.trace.r)?;
        require_matching_limbs("s", self.public.s.limbs(), &self.witness.trace.s)?;
        require_matching_limbs("u1", self.output.u1.limbs(), &self.witness.trace.u1)?;
        require_matching_limbs("u2", self.output.u2.limbs(), &self.witness.trace.u2)?;
        require_matching_limbs("output.r", self.output.r.limbs(), &self.witness.trace.r)?;
        if self.output.sig_id != self.public.sig_id {
            return Err(ScalarSetupClaimError::PublicInputMismatch {
                field: "sig_id",
                limb: 0,
                public: self.public.sig_id.0,
                witness: self.output.sig_id.0,
            });
        }
        Ok(())
    }

    pub const fn sig_id_u32(&self) -> u32 {
        self.public.sig_id.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarSetupOutput<F> {
    pub sig_id: F,
    pub u1: P256BigInt<F>,
    pub u2: P256BigInt<F>,
    pub r: P256BigInt<F>,
    pub pub_x: P256BigInt<F>,
    pub pub_y: P256BigInt<F>,
}

relation!(ScalarSetupOutputRelation, SCALAR_SETUP_OUTPUT_ARITY);

pub type ScalarSetupAirComponent = FrameworkComponent<ScalarSetupAirEval>;

pub const SCALAR_SETUP_OUTPUT_ARITY: usize = 1 + 5 * N_LIMBS;
pub const SCALAR_SETUP_TRACE_COLUMNS: usize = 1
    + PUBLIC_ECDSA_INSTANCE_ARITY
    + 3 * N_LIMBS
    + 2 * N_LIMBS
    + 2 * N_LIMBS
    + 2 * N_LIMBS
    + 1
    + N_LIMBS
    + 2 * N_LIMBS
    + 2;
const SCALAR_SETUP_SIGNED_CARRY_EQUATION: &str = "scalar_setup_digest";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ScalarSetupAirProofClaim {
    pub log_size: u32,
}

impl ScalarSetupAirProofClaim {
    pub fn from_claim(claim: &ScalarSetupClaim) -> Self {
        Self {
            log_size: padded_log_size(claim.rows.len()),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }
}

#[derive(Clone, Debug)]
pub struct ScalarSetupAirInteractionClaim {
    pub component_claimed_sum: SecureField,
    pub public_consumer_claimed_sum: SecureField,
    pub scalar_limb_consumer_claimed_sum: SecureField,
    pub range13_consumer_claimed_sum: SecureField,
    pub range9_consumer_claimed_sum: SecureField,
    pub signed_carry_consumer_claimed_sum: SecureField,
    pub range13_provider: RangeCheckInteractionClaim,
    pub range9_provider: RangeCheckInteractionClaim,
    pub signed_carry_provider: RangeCheckInteractionClaim,
}

impl ScalarSetupAirInteractionClaim {
    pub fn zero() -> Self {
        let zero = secure_zero();
        Self {
            component_claimed_sum: zero,
            public_consumer_claimed_sum: zero,
            scalar_limb_consumer_claimed_sum: zero,
            range13_consumer_claimed_sum: zero,
            range9_consumer_claimed_sum: zero,
            signed_carry_consumer_claimed_sum: zero,
            range13_provider: RangeCheckInteractionClaim { claimed_sum: zero },
            range9_provider: RangeCheckInteractionClaim { claimed_sum: zero },
            signed_carry_provider: RangeCheckInteractionClaim { claimed_sum: zero },
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[
            self.component_claimed_sum,
            self.range13_provider.claimed_sum,
            self.range9_provider.claimed_sum,
            self.signed_carry_provider.claimed_sum,
        ]);
    }

    pub fn total(&self) -> SecureField {
        self.component_claimed_sum
            + self.range13_provider.claimed_sum
            + self.range9_provider.claimed_sum
            + self.signed_carry_provider.claimed_sum
    }
}

pub struct ScalarSetupAirComponents {
    pub setup: ScalarSetupAirComponent,
    pub range13: RangeCheckComponent,
    pub range9: RangeCheckComponent,
    pub signed_carry: SignedCarryRangeComponent,
}

impl ScalarSetupAirComponents {
    pub(crate) fn new(
        allocator: &mut TraceLocationAllocator,
        claim: ScalarSetupAirProofClaim,
        interaction_claim: &ScalarSetupAirInteractionClaim,
        relations: &ScalarSetupAirRelations,
    ) -> Self {
        let providers = scalar_setup_lookup_provider_claims();
        Self {
            setup: ScalarSetupAirComponent::new(
                allocator,
                ScalarSetupAirEval {
                    log_size: claim.log_size,
                    public_relation: relations.public_inputs.clone(),
                    scalar_limb_relation: relations.scalar_mod_mul.scalar_limb.clone(),
                    range13: relations.range13.clone(),
                    range9: relations.range9.clone(),
                    signed_carry: relations.signed_carry.clone(),
                },
                interaction_claim.component_claimed_sum,
            ),
            range13: RangeCheckComponent::new(
                allocator,
                RangeCheckEval::new(relations.range13.clone(), RANGE13_BITS),
                interaction_claim.range13_provider.claimed_sum,
            ),
            range9: RangeCheckComponent::new(
                allocator,
                RangeCheckEval::new(relations.range9.clone(), RANGE9_BITS),
                interaction_claim.range9_provider.claimed_sum,
            ),
            signed_carry: SignedCarryRangeComponent::new(
                allocator,
                SignedCarryRangeEval::new(
                    relations.signed_carry.clone(),
                    providers.signed_carry.log_size,
                    SCALAR_SETUP_SIGNED_CARRY_EQUATION,
                ),
                interaction_claim.signed_carry_provider.claimed_sum,
            ),
        }
    }

    pub fn components(&self) -> Vec<&dyn Component> {
        vec![
            &self.setup as &dyn Component,
            &self.range13 as &dyn Component,
            &self.range9 as &dyn Component,
            &self.signed_carry as &dyn Component,
        ]
    }

    pub fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            &self.setup as &dyn ComponentProver<SimdBackend>,
            &self.range13 as &dyn ComponentProver<SimdBackend>,
            &self.range9 as &dyn ComponentProver<SimdBackend>,
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

#[derive(Clone)]
pub(crate) struct ScalarSetupAirRelations {
    pub(crate) public_inputs: PublicEcdsaInstanceRelation,
    pub(crate) scalar_mod_mul: ScalarModMulLookupRelations,
    pub(crate) range13: RangeCheckRelation,
    pub(crate) range9: RangeCheckRelation,
    pub(crate) signed_carry: RangeCheckRelation,
}

impl ScalarSetupAirRelations {
    pub(crate) fn dummy() -> Self {
        Self {
            public_inputs: PublicEcdsaInstanceRelation::dummy(),
            scalar_mod_mul: ScalarModMulLookupRelations::dummy(),
            range13: RangeCheckRelation::dummy(),
            range9: RangeCheckRelation::dummy(),
            signed_carry: RangeCheckRelation::dummy(),
        }
    }
}

#[derive(Clone)]
pub struct ScalarSetupAirEval {
    pub log_size: u32,
    pub public_relation: PublicEcdsaInstanceRelation,
    pub scalar_limb_relation: ScalarLimbRelation,
    pub range13: RangeCheckRelation,
    pub range9: RangeCheckRelation,
    pub signed_carry: RangeCheckRelation,
}

impl FrameworkEval for ScalarSetupAirEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.next_trace_mask();
        let public = read_public_instance(&mut eval);
        let z_red = P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask()));
        let u1 = P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask()));
        let u2 = P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask()));
        let q1 = P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask()));
        let q2 = P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask()));
        let r_lt_slack = P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask()));
        let r_lt_carries = core::array::from_fn(|_| eval.next_trace_mask());
        let s_lt_slack = P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask()));
        let s_lt_carries = core::array::from_fn(|_| eval.next_trace_mask());
        let z_ge_n = eval.next_trace_mask();
        let digest_carries = core::array::from_fn(|_| eval.next_trace_mask());
        let z_red_lt_slack =
            P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask()));
        let z_red_lt_carries = core::array::from_fn(|_| eval.next_trace_mask());
        let r_nonzero_inv = eval.next_trace_mask();
        let s_nonzero_inv = eval.next_trace_mask();
        let one = E::F::from(M31::from_u32_unchecked(1));

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        for value in public.relation_values() {
            eval.add_constraint((one.clone() - active.clone()) * value);
        }
        for limb in z_red
            .limbs()
            .iter()
            .chain(u1.limbs())
            .chain(u2.limbs())
            .chain(q1.limbs())
            .chain(q2.limbs())
        {
            eval.add_constraint((one.clone() - active.clone()) * limb.clone());
        }

        add_public_ecdsa_instance_consumer(
            &mut eval,
            &self.public_relation,
            active.clone(),
            &public,
        );

        add_canonical_lt_fixed_bound(
            &mut eval,
            CanonicalLtRelations {
                limb_range: &self.range13,
            },
            active.clone(),
            &public.r,
            &words_to_limbs(&P256_ORDER),
            &r_lt_slack,
            &r_lt_carries,
        );
        add_canonical_lt_fixed_bound(
            &mut eval,
            CanonicalLtRelations {
                limb_range: &self.range13,
            },
            active.clone(),
            &public.s,
            &words_to_limbs(&P256_ORDER),
            &s_lt_slack,
            &s_lt_carries,
        );
        add_digest_reduction(
            &mut eval,
            DigestReductionRelations {
                range13: &self.range13,
                range9: &self.range9,
                signed_carry: &self.signed_carry,
            },
            active.clone(),
            &DigestReductionColumns {
                z: public.z.clone(),
                z_red: z_red.clone(),
                z_ge_n,
                carries: digest_carries,
                z_red_lt_n_slack: z_red_lt_slack,
                z_red_lt_n_carries: z_red_lt_carries,
            },
        );

        enforce_nonzero(&mut eval, active.clone(), public.r.limbs(), r_nonzero_inv);
        enforce_nonzero(&mut eval, active.clone(), public.s.limbs(), s_nonzero_inv);

        add_scalar_limb_links(
            &mut eval,
            &self.scalar_limb_relation,
            active,
            &public,
            &z_red,
            &u1,
            &u2,
            &q1,
            &q2,
        );
        eval.finalize_logup();
        eval
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ScalarSetupClaimError {
    ScalarArithmetic(ScalarArithmeticError),
    PublicInputMismatch {
        field: &'static str,
        limb: usize,
        public: u32,
        witness: u32,
    },
}

impl fmt::Display for ScalarSetupClaimError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ScalarArithmetic(err) => err.fmt(f),
            Self::PublicInputMismatch {
                field,
                limb,
                public,
                witness,
            } => write!(
                f,
                "scalar setup public binding mismatch for {field}[{limb}]: public={public}, witness={witness}"
            ),
        }
    }
}

impl std::error::Error for ScalarSetupClaimError {}

impl From<ScalarArithmeticError> for ScalarSetupClaimError {
    fn from(error: ScalarArithmeticError) -> Self {
        Self::ScalarArithmetic(error)
    }
}

/// Range-check relations consumed by [`add_digest_reduction`].
#[derive(Clone, Copy)]
pub struct DigestReductionRelations<'a> {
    /// 13-bit range table for ordinary 20x13 limbs.
    pub range13: &'a RangeCheckRelation,
    /// 9-bit range table for the top digest limb, enforcing `z < 2^256`.
    pub range9: &'a RangeCheckRelation,
    /// Signed carry table for the digest-reduction recurrence.
    ///
    /// Must be configured with [`DIGEST_REDUCTION_CARRY_BOUND`].
    pub signed_carry: &'a RangeCheckRelation,
}

pub struct DigestReductionColumns<E: EvalAtRow> {
    pub z: P256EvalBigInt<E>,
    pub z_red: P256EvalBigInt<E>,
    pub z_ge_n: E::F,
    pub carries: [E::F; N_LIMBS],
    pub z_red_lt_n_slack: P256EvalBigInt<E>,
    pub z_red_lt_n_carries: [E::F; N_LIMBS],
}

/// Enforce `z_red = z mod n` for a 256-bit digest.
///
/// The helper proves:
///
/// ```text
/// z - z_red - z_ge_n * n = 0
/// z_ge_n in {0, 1}
/// z < 2^256          (top limb Range9)
/// z_red < n          (canonical less-than helper)
/// ```
///
/// Soundness relies on `2^256 < 2n`, so one subtraction is sufficient.
/// `gate` must be the same 0/1 selector used by consumers of the reduced
/// digest.
pub fn add_digest_reduction<E: EvalAtRow>(
    eval: &mut E,
    relations: DigestReductionRelations<'_>,
    gate: E::F,
    columns: &DigestReductionColumns<E>,
) {
    let one = E::F::from(M31::from_u32_unchecked(1));
    let zero = E::F::from(M31::from_u32_unchecked(0));
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    let n_limbs = words_to_limbs(&P256_ORDER);

    eval.add_constraint(gate.clone() * columns.z_ge_n.clone() * (columns.z_ge_n.clone() - one));

    for i in 0..N_LIMBS {
        let z_range = if i == N_LIMBS - 1 {
            relations.range9
        } else {
            relations.range13
        };
        add_range_check(eval, z_range, gate.clone(), columns.z.limbs()[i].clone());
        add_range_check(
            eval,
            relations.signed_carry,
            gate.clone(),
            columns.carries[i].clone(),
        );

        let prev_carry = if i == 0 {
            zero.clone()
        } else {
            columns.carries[i - 1].clone()
        };
        let recurrence = columns.z.limbs()[i].clone()
            - columns.z_red.limbs()[i].clone()
            - columns.z_ge_n.clone() * fixed_limb::<E>(&n_limbs, i)
            + prev_carry
            - limb_base.clone() * columns.carries[i].clone();
        eval.add_constraint(gate.clone() * recurrence);
    }
    eval.add_constraint(gate.clone() * columns.carries[N_LIMBS - 1].clone());

    add_canonical_lt_fixed_bound(
        eval,
        CanonicalLtRelations {
            limb_range: relations.range13,
        },
        gate,
        &columns.z_red,
        &n_limbs,
        &columns.z_red_lt_n_slack,
        &columns.z_red_lt_n_carries,
    );
}

pub fn scalar_setup_lookup_provider_claims() -> ScalarSetupLookupProviderClaims {
    ScalarSetupLookupProviderClaims {
        range13: RangeCheckClaim::new(RANGE13_BITS),
        range9: RangeCheckClaim::new(RANGE9_BITS),
        signed_carry: SignedCarryRangeClaim::new(
            LOG_N_LANES,
            DIGEST_REDUCTION_CARRY_BOUND,
            SCALAR_SETUP_SIGNED_CARRY_EQUATION,
        ),
    }
}

#[derive(Clone, Debug)]
pub struct ScalarSetupLookupProviderClaims {
    pub range13: RangeCheckClaim,
    pub range9: RangeCheckClaim,
    pub signed_carry: SignedCarryRangeClaim,
}

pub fn scalar_setup_air_preprocessed_column_ids(
) -> Vec<stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId> {
    let mut allocator = TraceLocationAllocator::default();
    let _ = ScalarSetupAirComponents::new(
        &mut allocator,
        ScalarSetupAirProofClaim {
            log_size: LOG_N_LANES,
        },
        &ScalarSetupAirInteractionClaim::zero(),
        &ScalarSetupAirRelations::dummy(),
    );
    allocator.preprocessed_columns().clone()
}

pub fn gen_scalar_setup_air_preprocessed_trace(
    ids: &[stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId],
) -> ColumnVec<M31ColumnEval> {
    let providers = scalar_setup_lookup_provider_claims();
    let range13_value = providers.range13.gen_preprocessed_column();
    let range9_value = providers.range9.gen_preprocessed_column();
    let signed_value = providers.signed_carry.gen_value_column();
    let signed_active = providers.signed_carry.gen_active_column();

    ids.iter()
        .map(|id| {
            if *id == range_check_value_column_id(RANGE13_BITS) {
                range13_value.clone()
            } else if *id == range_check_value_column_id(RANGE9_BITS) {
                range9_value.clone()
            } else if *id == signed_carry_value_column_id(SCALAR_SETUP_SIGNED_CARRY_EQUATION) {
                signed_value.clone()
            } else if *id == signed_carry_active_column_id(SCALAR_SETUP_SIGNED_CARRY_EQUATION) {
                signed_active.clone()
            } else {
                panic!("missing scalar setup preprocessed column {}", id.id)
            }
        })
        .collect()
}

pub fn gen_scalar_setup_air_base_trace(
    claim: &ScalarSetupClaim,
    proof_claim: ScalarSetupAirProofClaim,
) -> ColumnVec<M31ColumnEval> {
    let row_count = 1usize << proof_claim.log_size;
    assert!(claim.rows.len() <= row_count);
    let mut columns = vec![vec![M31::from_u32_unchecked(0); row_count]; SCALAR_SETUP_TRACE_COLUMNS];
    fill_padding_lt_witnesses(&mut columns, row_count);

    for (row_index, row) in claim.rows.iter().enumerate() {
        let mut offset = 0usize;
        columns[offset][row_index] = M31::from_u32_unchecked(1);
        offset += 1;

        for value in row.public.relation_values() {
            columns[offset][row_index] = value;
            offset += 1;
        }
        write_limbs(
            &mut columns,
            &mut offset,
            row.witness.trace.z_reduction.z_red,
            row_index,
        );
        write_limbs(&mut columns, &mut offset, row.witness.trace.u1, row_index);
        write_limbs(&mut columns, &mut offset, row.witness.trace.u2, row_index);
        write_limbs(
            &mut columns,
            &mut offset,
            row.witness.trace.s_u1_eq.mul.quotient,
            row_index,
        );
        write_limbs(
            &mut columns,
            &mut offset,
            row.witness.trace.s_u2_eq.mul.quotient,
            row_index,
        );
        write_limbs(
            &mut columns,
            &mut offset,
            row.witness.trace.r_lt_n.slack,
            row_index,
        );
        write_signed_carries(
            &mut columns,
            &mut offset,
            row.witness.trace.r_lt_n.carries,
            row_index,
        );
        write_limbs(
            &mut columns,
            &mut offset,
            row.witness.trace.s_lt_n.slack,
            row_index,
        );
        write_signed_carries(
            &mut columns,
            &mut offset,
            row.witness.trace.s_lt_n.carries,
            row_index,
        );
        columns[offset][row_index] = M31::from_u32_unchecked(row.witness.trace.z_reduction.z_ge_n);
        offset += 1;
        write_signed_carries(
            &mut columns,
            &mut offset,
            row.witness.trace.z_reduction.carries,
            row_index,
        );
        write_limbs(
            &mut columns,
            &mut offset,
            row.witness.trace.z_reduction.z_red_lt_n.slack,
            row_index,
        );
        write_signed_carries(
            &mut columns,
            &mut offset,
            row.witness.trace.z_reduction.z_red_lt_n.carries,
            row_index,
        );
        columns[offset][row_index] = nonzero_inverse(row.public.r.limbs());
        offset += 1;
        columns[offset][row_index] = nonzero_inverse(row.public.s.limbs());
        offset += 1;
        debug_assert_eq!(offset, SCALAR_SETUP_TRACE_COLUMNS);
    }

    columns
        .into_iter()
        .map(|values| m31_column_eval(proof_claim.log_size, values))
        .collect()
}

pub(crate) fn gen_scalar_setup_air_lookup_provider_base_trace(
    setup_base: &[M31ColumnEval],
) -> ColumnVec<M31ColumnEval> {
    let providers = scalar_setup_lookup_provider_claims();
    vec![
        providers
            .range13
            .gen_multiplicity_trace(scalar_setup_range13_uses_from_base(setup_base)),
        providers
            .range9
            .gen_multiplicity_trace(scalar_setup_range9_uses_from_base(setup_base)),
        providers
            .signed_carry
            .gen_multiplicity_trace(scalar_setup_signed_carry_uses_from_base(setup_base)),
    ]
}

pub(crate) fn gen_scalar_setup_air_interaction_trace(
    base: &[M31ColumnEval],
    relations: &ScalarSetupAirRelations,
) -> (ColumnVec<M31ColumnEval>, ScalarSetupAirInteractionClaim) {
    assert_eq!(base.len(), SCALAR_SETUP_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut offset = 0usize;
    let active_col = offset;
    offset += 1;
    let public_col = offset;
    offset += PUBLIC_ECDSA_INSTANCE_ARITY;
    let z_red_col = offset;
    offset += N_LIMBS;
    let u1_col = offset;
    offset += N_LIMBS;
    let u2_col = offset;
    offset += N_LIMBS;
    let q1_col = offset;
    offset += N_LIMBS;
    let q2_col = offset;
    offset += N_LIMBS;
    let r_slack_col = offset;
    offset += N_LIMBS;
    let _r_carry_col = offset;
    offset += N_LIMBS;
    let s_slack_col = offset;
    offset += N_LIMBS;
    let _s_carry_col = offset;
    offset += N_LIMBS;
    let _z_ge_n_col = offset;
    offset += 1;
    let digest_carry_col = offset;
    offset += N_LIMBS;
    let z_red_slack_col = offset;
    offset += N_LIMBS;
    let _z_red_carry_col = offset;
    offset += N_LIMBS;
    let _r_inv_col = offset;
    offset += 1;
    let _s_inv_col = offset;
    offset += 1;
    debug_assert_eq!(offset, SCALAR_SETUP_TRACE_COLUMNS);

    let mut logup = LogupTraceGenerator::new(log_size);
    let mut public_sum = secure_zero();
    let mut scalar_limb_sum = secure_zero();
    let mut range13_sum = secure_zero();
    let mut range9_sum = secure_zero();
    let mut signed_carry_sum = secure_zero();

    append_relation_column(&mut logup, base, active_col, |vec_row| {
        let values: [PackedM31; PUBLIC_ECDSA_INSTANCE_ARITY] =
            core::array::from_fn(|index| base[public_col + index].data[vec_row]);
        relations.public_inputs.combine(&values)
    });
    public_sum += packed_relation_sum(base, active_col, |row| {
        let values: [M31; PUBLIC_ECDSA_INSTANCE_ARITY] =
            core::array::from_fn(|index| row[public_col + index]);
        relations.public_inputs.combine(&values)
    });

    for limb in 0..N_LIMBS {
        append_range_column(
            &mut logup,
            base,
            active_col,
            &relations.range13,
            public_r_col(limb),
        );
        append_range_column(
            &mut logup,
            base,
            active_col,
            &relations.range13,
            r_slack_col + limb,
        );
        range13_sum += range_sum(base, active_col, &relations.range13, public_r_col(limb));
        range13_sum += range_sum(base, active_col, &relations.range13, r_slack_col + limb);
    }
    for limb in 0..N_LIMBS {
        append_range_column(
            &mut logup,
            base,
            active_col,
            &relations.range13,
            public_s_col(limb),
        );
        append_range_column(
            &mut logup,
            base,
            active_col,
            &relations.range13,
            s_slack_col + limb,
        );
        range13_sum += range_sum(base, active_col, &relations.range13, public_s_col(limb));
        range13_sum += range_sum(base, active_col, &relations.range13, s_slack_col + limb);
    }
    for limb in 0..N_LIMBS {
        let relation = if limb == N_LIMBS - 1 {
            &relations.range9
        } else {
            &relations.range13
        };
        append_range_column(&mut logup, base, active_col, relation, public_z_col(limb));
        if limb == N_LIMBS - 1 {
            range9_sum += range_sum(base, active_col, relation, public_z_col(limb));
        } else {
            range13_sum += range_sum(base, active_col, relation, public_z_col(limb));
        }
        append_range_column(
            &mut logup,
            base,
            active_col,
            &relations.signed_carry,
            digest_carry_col + limb,
        );
        signed_carry_sum += range_sum(
            base,
            active_col,
            &relations.signed_carry,
            digest_carry_col + limb,
        );
    }
    for limb in 0..N_LIMBS {
        append_range_column(
            &mut logup,
            base,
            active_col,
            &relations.range13,
            z_red_col + limb,
        );
        append_range_column(
            &mut logup,
            base,
            active_col,
            &relations.range13,
            z_red_slack_col + limb,
        );
        range13_sum += range_sum(base, active_col, &relations.range13, z_red_col + limb);
        range13_sum += range_sum(base, active_col, &relations.range13, z_red_slack_col + limb);
    }

    for limb in 0..N_LIMBS {
        for (mul_offset, b_col, q_col, result_col) in [
            (0u32, u1_col, q1_col, z_red_col),
            (1u32, u2_col, q2_col, public_r_col(0)),
        ] {
            for (role, value_col) in [
                (ROLE_A, public_s_col(limb)),
                (ROLE_B, b_col + limb),
                (ROLE_QUOTIENT, q_col + limb),
                (ROLE_RESULT, result_col + limb),
            ] {
                append_scalar_limb_column(
                    &mut logup,
                    base,
                    active_col,
                    public_sig_id_col(),
                    mul_offset,
                    role,
                    limb as u32,
                    value_col,
                    &relations.scalar_mod_mul.scalar_limb,
                );
                scalar_limb_sum += scalar_limb_sum_for_column(
                    base,
                    active_col,
                    public_sig_id_col(),
                    mul_offset,
                    role,
                    limb as u32,
                    value_col,
                    &relations.scalar_mod_mul.scalar_limb,
                );
            }
        }
    }

    let (mut trace, component_claimed_sum) = logup.finalize_last();

    let providers = scalar_setup_lookup_provider_claims();
    let range13_values = providers.range13.gen_preprocessed_column();
    let range13_uses = scalar_setup_range13_uses_from_base(base);
    let range13_multiplicity = providers.range13.gen_multiplicity_trace(range13_uses);
    let (range13_trace, range13_provider) = RangeCheckInteractionClaim::gen_interaction_trace(
        &range13_multiplicity,
        &range13_values,
        &relations.range13,
    );
    let range9_values = providers.range9.gen_preprocessed_column();
    let range9_uses = scalar_setup_range9_uses_from_base(base);
    let range9_multiplicity = providers.range9.gen_multiplicity_trace(range9_uses);
    let (range9_trace, range9_provider) = RangeCheckInteractionClaim::gen_interaction_trace(
        &range9_multiplicity,
        &range9_values,
        &relations.range9,
    );
    let signed_values = providers.signed_carry.gen_value_column();
    let signed_uses = scalar_setup_signed_carry_uses_from_base(base);
    let signed_multiplicity = providers.signed_carry.gen_multiplicity_trace(signed_uses);
    let (signed_trace, signed_carry_provider) = RangeCheckInteractionClaim::gen_interaction_trace(
        &signed_multiplicity,
        &signed_values,
        &relations.signed_carry,
    );

    trace.extend(range13_trace);
    trace.extend(range9_trace);
    trace.extend(signed_trace);

    (
        trace,
        ScalarSetupAirInteractionClaim {
            component_claimed_sum,
            public_consumer_claimed_sum: public_sum,
            scalar_limb_consumer_claimed_sum: scalar_limb_sum,
            range13_consumer_claimed_sum: range13_sum,
            range9_consumer_claimed_sum: range9_sum,
            signed_carry_consumer_claimed_sum: signed_carry_sum,
            range13_provider,
            range9_provider,
            signed_carry_provider,
        },
    )
}

fn read_public_instance<E: EvalAtRow>(eval: &mut E) -> PublicEcdsaInstance<E::F> {
    PublicEcdsaInstance {
        sig_id: eval.next_trace_mask(),
        z: P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask())),
        r: P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask())),
        s: P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask())),
        pub_x: P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask())),
        pub_y: P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask())),
    }
}

fn enforce_nonzero<E: EvalAtRow>(eval: &mut E, gate: E::F, limbs: &[E::F; N_LIMBS], inverse: E::F) {
    let one = E::F::from(M31::from_u32_unchecked(1));
    let sum = limbs
        .iter()
        .cloned()
        .fold(E::F::from(M31::from_u32_unchecked(0)), |acc, limb| {
            acc + limb
        });
    eval.add_constraint(gate * (sum * inverse - one));
}

fn add_scalar_limb_links<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarLimbRelation,
    gate: E::F,
    public: &PublicEcdsaInstance<E::F>,
    z_red: &P256EvalBigInt<E>,
    u1: &P256EvalBigInt<E>,
    u2: &P256EvalBigInt<E>,
    q1: &P256EvalBigInt<E>,
    q2: &P256EvalBigInt<E>,
) {
    for limb in 0..N_LIMBS {
        add_scalar_limb_link(
            eval,
            relation,
            gate.clone(),
            public.sig_id.clone(),
            0,
            ROLE_A,
            limb,
            public.s.limbs()[limb].clone(),
        );
        add_scalar_limb_link(
            eval,
            relation,
            gate.clone(),
            public.sig_id.clone(),
            0,
            ROLE_B,
            limb,
            u1.limbs()[limb].clone(),
        );
        add_scalar_limb_link(
            eval,
            relation,
            gate.clone(),
            public.sig_id.clone(),
            0,
            ROLE_QUOTIENT,
            limb,
            q1.limbs()[limb].clone(),
        );
        add_scalar_limb_link(
            eval,
            relation,
            gate.clone(),
            public.sig_id.clone(),
            0,
            ROLE_RESULT,
            limb,
            z_red.limbs()[limb].clone(),
        );
        add_scalar_limb_link(
            eval,
            relation,
            gate.clone(),
            public.sig_id.clone(),
            1,
            ROLE_A,
            limb,
            public.s.limbs()[limb].clone(),
        );
        add_scalar_limb_link(
            eval,
            relation,
            gate.clone(),
            public.sig_id.clone(),
            1,
            ROLE_B,
            limb,
            u2.limbs()[limb].clone(),
        );
        add_scalar_limb_link(
            eval,
            relation,
            gate.clone(),
            public.sig_id.clone(),
            1,
            ROLE_QUOTIENT,
            limb,
            q2.limbs()[limb].clone(),
        );
        add_scalar_limb_link(
            eval,
            relation,
            gate.clone(),
            public.sig_id.clone(),
            1,
            ROLE_RESULT,
            limb,
            public.r.limbs()[limb].clone(),
        );
    }
}

fn add_scalar_limb_link<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarLimbRelation,
    gate: E::F,
    sig_id: E::F,
    mul_offset: u32,
    role: u32,
    limb: usize,
    value: E::F,
) {
    let two = E::F::from(M31::from_u32_unchecked(2));
    let mul_id = sig_id * two + E::F::from(M31::from_u32_unchecked(mul_offset));
    eval.add_to_relation(RelationEntry::new(
        relation,
        E::EF::from(gate),
        &[
            mul_id,
            E::F::from(M31::from_u32_unchecked(role)),
            E::F::from(M31::from_u32_unchecked(limb as u32)),
            value,
        ],
    ));
}

fn append_relation_column(
    logup: &mut LogupTraceGenerator,
    base: &[M31ColumnEval],
    active_col: usize,
    mut denominator: impl FnMut(usize) -> PackedQM31,
) {
    let log_size = base[0].domain.log_size();
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        col.write_frac(
            vec_row,
            PackedQM31::from(base[active_col].data[vec_row]),
            denominator(vec_row),
        );
    }
    col.finalize_col();
}

fn append_range_column(
    logup: &mut LogupTraceGenerator,
    base: &[M31ColumnEval],
    active_col: usize,
    relation: &RangeCheckRelation,
    value_col: usize,
) {
    append_relation_column(logup, base, active_col, |vec_row| {
        relation.combine(&[base[value_col].data[vec_row]])
    });
}

fn append_scalar_limb_column(
    logup: &mut LogupTraceGenerator,
    base: &[M31ColumnEval],
    active_col: usize,
    sig_id_col: usize,
    mul_offset: u32,
    role: u32,
    limb: u32,
    value_col: usize,
    relation: &ScalarLimbRelation,
) {
    append_relation_column(logup, base, active_col, |vec_row| {
        let mul_id = base[sig_id_col].data[vec_row] * PackedM31::from(M31::from_u32_unchecked(2))
            + PackedM31::from(M31::from_u32_unchecked(mul_offset));
        relation.combine(&[
            mul_id,
            PackedM31::from(M31::from_u32_unchecked(role)),
            PackedM31::from(M31::from_u32_unchecked(limb)),
            base[value_col].data[vec_row],
        ])
    });
}

fn packed_relation_sum(
    base: &[M31ColumnEval],
    active_col: usize,
    mut denominator: impl FnMut(&[M31]) -> SecureField,
) -> SecureField {
    storage_rows(base)
        .filter(|row| row[active_col] != M31::from_u32_unchecked(0))
        .map(|row| SecureField::from(row[active_col]) / denominator(&row))
        .sum()
}

fn range_sum(
    base: &[M31ColumnEval],
    active_col: usize,
    relation: &RangeCheckRelation,
    value_col: usize,
) -> SecureField {
    packed_relation_sum(base, active_col, |row| relation.combine(&[row[value_col]]))
}

fn scalar_limb_sum_for_column(
    base: &[M31ColumnEval],
    active_col: usize,
    sig_id_col: usize,
    mul_offset: u32,
    role: u32,
    limb: u32,
    value_col: usize,
    relation: &ScalarLimbRelation,
) -> SecureField {
    packed_relation_sum(base, active_col, |row| {
        let mul_id = row[sig_id_col].0 * 2 + mul_offset;
        relation.combine(&[
            M31::from_u32_unchecked(mul_id),
            M31::from_u32_unchecked(role),
            M31::from_u32_unchecked(limb),
            row[value_col],
        ])
    })
}

fn scalar_setup_range13_uses_from_base(base: &[M31ColumnEval]) -> Vec<M31> {
    let mut uses = Vec::new();
    for row in storage_rows(base).filter(|row| row[0] != M31::from_u32_unchecked(0)) {
        for limb in 0..N_LIMBS {
            uses.push(row[public_r_col(limb)]);
            uses.push(row[public_s_col(limb)]);
            if limb != N_LIMBS - 1 {
                uses.push(row[public_z_col(limb)]);
            }
            uses.push(row[z_red_col() + limb]);
            uses.push(row[r_slack_col() + limb]);
            uses.push(row[s_slack_col() + limb]);
            uses.push(row[z_red_slack_col() + limb]);
        }
    }
    uses
}

fn scalar_setup_range9_uses_from_base(base: &[M31ColumnEval]) -> Vec<M31> {
    storage_rows(base)
        .filter(|row| row[0] != M31::from_u32_unchecked(0))
        .map(|row| row[public_z_col(N_LIMBS - 1)])
        .collect()
}

fn scalar_setup_signed_carry_uses_from_base(base: &[M31ColumnEval]) -> Vec<i64> {
    storage_rows(base)
        .filter(|row| row[0] != M31::from_u32_unchecked(0))
        .flat_map(|row| {
            (0..N_LIMBS).map(move |limb| decode_signed_carry(row[digest_carry_col() + limb]))
        })
        .collect()
}

fn storage_rows(base: &[M31ColumnEval]) -> impl Iterator<Item = Vec<M31>> + '_ {
    let row_count = base[0].domain.size();
    (0..row_count).map(|row| {
        let vec_row = row / (1 << LOG_N_LANES);
        let lane = row % (1 << LOG_N_LANES);
        base.iter()
            .map(|column| column.data[vec_row].to_array()[lane])
            .collect::<Vec<_>>()
    })
}

fn fill_padding_lt_witnesses(columns: &mut [Vec<M31>], row_count: usize) {
    let zero = [0u64; 4];
    let padding = CanonicalLtTrace::new("padding", &zero, "n", &P256_ORDER)
        .expect("0 is below the P-256 scalar order");
    for row in 0..row_count {
        write_limbs(columns, &mut r_slack_col(), padding.slack, row);
        write_signed_carries(columns, &mut r_carry_col(), padding.carries, row);
        write_limbs(columns, &mut s_slack_col(), padding.slack, row);
        write_signed_carries(columns, &mut s_carry_col(), padding.carries, row);
        write_limbs(columns, &mut z_red_slack_col(), padding.slack, row);
        write_signed_carries(columns, &mut z_red_carry_col(), padding.carries, row);
    }
}

fn write_limbs(columns: &mut [Vec<M31>], offset: &mut usize, limbs: [u32; N_LIMBS], row: usize) {
    for limb in limbs {
        columns[*offset][row] = M31::from_u32_unchecked(limb);
        *offset += 1;
    }
}

fn write_signed_carries(
    columns: &mut [Vec<M31>],
    offset: &mut usize,
    carries: [i64; N_LIMBS],
    row: usize,
) {
    for carry in carries {
        columns[*offset][row] = encode_signed_carry(carry);
        *offset += 1;
    }
}

fn nonzero_inverse(limbs: &[M31; N_LIMBS]) -> M31 {
    let sum = limbs.iter().fold(0u64, |acc, limb| acc + u64::from(limb.0));
    assert!(sum > 0, "nonzero scalar limbs must have nonzero limb sum");
    m31_inverse(M31::from_u32_unchecked(sum as u32))
}

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

fn secure_zero() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(0))
}

const fn public_sig_id_col() -> usize {
    1
}

const fn public_z_col(limb: usize) -> usize {
    2 + limb
}

const fn public_r_col(limb: usize) -> usize {
    2 + N_LIMBS + limb
}

const fn public_s_col(limb: usize) -> usize {
    2 + 2 * N_LIMBS + limb
}

const fn z_red_col() -> usize {
    1 + PUBLIC_ECDSA_INSTANCE_ARITY
}

const fn r_slack_col() -> usize {
    1 + PUBLIC_ECDSA_INSTANCE_ARITY + 5 * N_LIMBS
}

const fn r_carry_col() -> usize {
    r_slack_col() + N_LIMBS
}

const fn s_slack_col() -> usize {
    r_carry_col() + N_LIMBS
}

const fn s_carry_col() -> usize {
    s_slack_col() + N_LIMBS
}

const fn digest_carry_col() -> usize {
    s_carry_col() + N_LIMBS + 1
}

const fn z_red_slack_col() -> usize {
    digest_carry_col() + N_LIMBS
}

const fn z_red_carry_col() -> usize {
    z_red_slack_col() + N_LIMBS
}

pub fn full_fnmul_requires_split() -> bool {
    FULL_FNMUL_MAX_ABS_COMBINED_EXPR > M31_CENTERED_BOUND
}

fn require_matching_limbs(
    field: &'static str,
    public: &[M31; N_LIMBS],
    witness: &[u32; N_LIMBS],
) -> Result<(), ScalarSetupClaimError> {
    for (limb, (public, witness)) in public.iter().zip(witness).enumerate() {
        if public.0 != *witness {
            return Err(ScalarSetupClaimError::PublicInputMismatch {
                field,
                limb,
                public: public.0,
                witness: *witness,
            });
        }
    }
    Ok(())
}

fn fixed_limb<E: EvalAtRow>(limbs: &BigIntLimbs, index: usize) -> E::F {
    E::F::from(M31::from_u32_unchecked(limbs[index]))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY};
    use crate::public_inputs::{
        public_ecdsa_consumer_claimed_sum, PublicEcdsaInputClaim, PublicEcdsaInstanceRelation,
    };
    use crate::types::{AffinePoint, EcdsaVerifyInput, Signature};
    use stwo::core::fields::qm31::SecureField;

    const M31_MODULUS: i64 = (1i64 << 31) - 1;
    const LIMB_BOUND: i64 = 1i64 << LIMB_BITS;

    fn test_input(r: u64) -> EcdsaVerifyInput {
        EcdsaVerifyInput {
            message_hash: scalar(42),
            signature: Signature {
                r: scalar(r),
                s: scalar(11),
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

    #[test]
    fn digest_reduction_limb_expression_has_m31_headroom() {
        let max = (LIMB_BOUND - 1)
            + DIGEST_REDUCTION_CARRY_BOUND
            + LIMB_BOUND * DIGEST_REDUCTION_CARRY_BOUND;
        let min = -(LIMB_BOUND - 1)
            - (LIMB_BOUND - 1)
            - DIGEST_REDUCTION_CARRY_BOUND
            - LIMB_BOUND * DIGEST_REDUCTION_CARRY_BOUND;

        assert!(max < M31_MODULUS);
        assert!(min > -M31_MODULUS);
    }

    #[test]
    fn digest_top_limb_uses_nine_bits() {
        assert_eq!(DIGEST_TOP_LIMB_BITS, 9);
        assert_eq!(N_LIMBS * LIMB_BITS, 260);
        assert_eq!(
            (N_LIMBS - 1) * LIMB_BITS + DIGEST_TOP_LIMB_BITS as usize,
            256
        );
    }

    #[test]
    fn full_fnmul_is_not_direct_m31_safe() {
        assert!(full_fnmul_requires_split());
    }

    #[test]
    fn scalar_setup_claim_consumes_public_inputs_and_exposes_outputs() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(77), test_input(78)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");

        scalar_setup.verify().expect("scalar setup verifies");
        assert_eq!(scalar_setup.rows.len(), 2);
        assert_eq!(
            scalar_setup.rows[0].output.sig_id,
            M31::from_u32_unchecked(0)
        );
        assert_eq!(
            scalar_setup.rows[1].output.sig_id,
            M31::from_u32_unchecked(1)
        );
        assert_eq!(
            scalar_setup.rows[0].output.u1.limbs(),
            scalar_setup.rows[0]
                .witness
                .trace
                .u1
                .map(M31::from_u32_unchecked)
                .as_ref()
        );
        assert_eq!(
            scalar_setup.rows[0].output.u2.limbs(),
            scalar_setup.rows[0]
                .witness
                .trace
                .u2
                .map(M31::from_u32_unchecked)
                .as_ref()
        );
    }

    #[test]
    fn scalar_setup_e2e_balances_public_logup_consumers() {
        let relation = PublicEcdsaInstanceRelation::dummy();
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(77), test_input(78)]);
        let public_interaction = public_claim.initial_logup_claim(&relation);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");

        scalar_setup.verify().expect("scalar setup verifies");
        let vm_consumers =
            public_ecdsa_consumer_claimed_sum(&scalar_setup.public_consumers(), &relation);

        assert_eq!(
            public_interaction.claimed_sum + vm_consumers,
            SecureField::from(M31::from_u32_unchecked(0))
        );
    }

    #[test]
    fn scalar_setup_rejects_public_tuple_mismatch() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(77)]);
        let mut scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        scalar_setup.rows[0].public.r.limbs_mut()[0] = M31::from_u32_unchecked(78);

        let err = scalar_setup
            .verify()
            .expect_err("mutated public input must fail binding");

        assert!(matches!(
            err,
            ScalarSetupClaimError::PublicInputMismatch { field: "r", .. }
        ));
    }

    #[test]
    fn scalar_setup_rejects_mutated_arithmetic_witness() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(77)]);
        let mut scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        scalar_setup.rows[0].witness.trace.s_u1_eq.mul.result[0] ^= 1;

        let err = scalar_setup
            .verify()
            .expect_err("mutated scalar setup witness must fail");

        assert!(matches!(
            err,
            ScalarSetupClaimError::ScalarArithmetic(_)
                | ScalarSetupClaimError::PublicInputMismatch { .. }
        ));
    }

    #[test]
    fn scalar_setup_claim_mixes_into_transcript() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(77)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let mut channel = stwo::core::channel::Blake2sM31Channel::default();

        scalar_setup.mix_into(&mut channel);
    }
}
