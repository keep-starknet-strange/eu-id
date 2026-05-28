use std::fmt;

use stwo::core::channel::Channel;
use stwo::core::fields::m31::M31;
use stwo_constraint_framework::EvalAtRow;
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};
use stwo_p256_utils::scalar_arithmetic::{
    words_to_limbs, BigIntLimbs, ScalarArithmeticError, P256_ORDER,
};

use crate::limbs::{P256BigInt, P256EvalBigInt, P256M31BigInt};
use crate::public_inputs::{PublicEcdsaInputClaim, PublicEcdsaInstance};
use crate::range_checks::{add_range_check, RangeCheckRelation};
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
