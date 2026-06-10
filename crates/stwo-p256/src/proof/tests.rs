use super::*;
use crate::constants::{P256_GX, P256_GY, P256_MODULUS, P256_ORDER};
use crate::curve::{mod_inverse, scalar_mul};
use crate::debug::MockCommitmentScheme;
use crate::field_ops::mul_mod_witness;
use crate::fp_solinas_air::FP_SOLINAS_REDUCTION_DIGITS;
use crate::limbs::P256M31BigInt;
use crate::fake_glv_chain::FakeGlvChainCert;
use crate::prepared_table::{PreparedAffinePoint, PreparedTableCert};
use crate::projective_air::{
    PROJECTIVE_RCB_FOLDED_CONTRIBUTION_ROWS, PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS,
    PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TRACE_COLUMNS, PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS,
    PROJECTIVE_RCB_FOLDED_DIGIT_TRACE_COLUMNS, PROJECTIVE_RCB_MUL_SILO_TRACE_COLUMNS,
    PROJECTIVE_RCB_MUL_TRACE_COLUMNS,
    PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS, PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS,
    PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS,
};
use crate::scalar::scalar_mod_mul::interaction_claim::zero_interaction_claim;
use crate::scalar::scalar_mod_mul::layout::{
    ScalarModMulFamilyTraces, PRODUCT_METADATA_TRACE_COLUMNS,
};
use crate::scalar::scalar_mod_mul::schedule::ScalarModMulFixedSchedule;
use crate::scalar::scalar_mod_mul::{
    SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS, SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS,
};
use crate::types::{field_modulus, AffinePoint, Signature, U256};
use core::cmp::Ordering;
use std::collections::BTreeMap;
use std::ops::Deref;
use stwo::core::channel::Blake2sM31Channel;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::Column;
use stwo_constraint_framework::{
    assert_constraints_on_polys, assert_constraints_on_trace, FrameworkComponent, FrameworkEval,
    PREPROCESSED_TRACE_IDX,
};

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

fn generator_point() -> AffinePoint {
    AffinePoint {
        x: U256::from_le_u64s(&P256_GX),
        y: U256::from_le_u64s(&P256_GY),
    }
}

fn valid_real_input_with_small_u_scalars(u1: u64, u2: u64) -> EcdsaVerifyInput {
    assert_ne!(u2, 0, "u2 must use the active fake-GLV branch");
    let n = U256::from_le_u64s(&P256_ORDER);
    let public_key = generator_point();
    let r_point = scalar_mul(&scalar(u1 + u2), &public_key).expect("nonzero R");
    let r = x_mod_order(&r_point.x);
    let u2_inv = mod_inverse(&scalar(u2), &n);
    let s = mul_mod_witness(&r, &u2_inv, &n).result.to_u256();
    let message_hash = mul_mod_witness(&scalar(u1), &s, &n).result.to_u256();

    EcdsaVerifyInput {
        message_hash,
        signature: Signature { r, s },
        public_key,
    }
}

/// Like `valid_real_input_with_small_u_scalars`, but builds a real ECDSA
/// statement for arbitrary full-width `u1`, `u2 ∈ [1, n)`. This stresses
/// the fake-GLV scalar AIR with scalars that do not fit a trivial hint.
fn valid_real_input_with_u_scalars(u1: U256, u2: U256) -> EcdsaVerifyInput {
    assert_ne!(u2, U256::ZERO, "u2 must be nonzero for ECDSA setup");
    let n = U256::from_le_u64s(&P256_ORDER);
    let public_key = generator_point();
    let u_sum = add_mod_u256(&u1, &u2, &n);
    let r_point = scalar_mul(&u_sum, &public_key).expect("nonzero R");
    let r = x_mod_order(&r_point.x);
    let u2_inv = mod_inverse(&u2, &n);
    let s = mul_mod_witness(&r, &u2_inv, &n).result.to_u256();
    let message_hash = mul_mod_witness(&u1, &s, &n).result.to_u256();

    EcdsaVerifyInput {
        message_hash,
        signature: Signature { r, s },
        public_key,
    }
}

/// Returns `n - delta` as a full-width 256-bit scalar — convenient for
/// generating arbitrary scalars that live in the upper end of `[0, n)`
/// and therefore cannot satisfy the trivial fake-GLV hint.
fn scalar_near_order(delta: u64) -> U256 {
    let n = U256::from_le_u64s(&P256_ORDER);
    sub_mod_u256(&n, &U256::from_le_u64s(&[delta, 0, 0, 0]), &n)
}

fn add_mod_u256(a: &U256, b: &U256, modulus: &U256) -> U256 {
    crate::field_ops::add_mod_witness(a, b, modulus).result.to_u256()
}

fn sub_mod_u256(a: &U256, b: &U256, modulus: &U256) -> U256 {
    crate::field_ops::sub_mod_witness(a, b, modulus).result.to_u256()
}

/// Deterministic real-world ECDSA fixture from the `p256` crate. Signs
/// a known message with a fixed signing key, runs the result through
/// SHA-256 for the message hash, and returns an `EcdsaVerifyInput`
/// laid out for the monolithic AIR. This exercises the production
/// arbitrary-fake-GLV path with a signature that wasn't constructed
/// to fit the trivial hint.
fn p256_crate_signed_input() -> EcdsaVerifyInput {
    use ::ecdsa::signature::Signer;
    use p256::ecdsa::{Signature as P256Signature, SigningKey};
    use sha2::{Digest, Sha256};

    let signing_key = SigningKey::from_bytes((&[7u8; 32]).into()).expect("valid signing key");
    let verifying_key = signing_key.verifying_key();
    let message = b"stwo-p256 arbitrary signature air fixture";
    let digest = Sha256::digest(message);
    let signature: P256Signature = signing_key.sign(message);
    let encoded = verifying_key.to_encoded_point(false);

    let r_bytes: [u8; 32] = signature.r().to_bytes().into();
    let s_bytes: [u8; 32] = signature.s().to_bytes().into();
    let x_bytes: [u8; 32] = encoded.x().expect("x").as_slice().try_into().expect("x len");
    let y_bytes: [u8; 32] = encoded.y().expect("y").as_slice().try_into().expect("y len");

    EcdsaVerifyInput {
        message_hash: U256(digest.into()),
        signature: Signature {
            r: U256(r_bytes),
            s: U256(s_bytes),
        },
        public_key: AffinePoint {
            x: U256(x_bytes),
            y: U256(y_bytes),
        },
    }
}

fn x_mod_order(x: &U256) -> U256 {
    let n = U256::from_le_u64s(&P256_ORDER);
    if cmp_u256(x, &n).is_lt() {
        return x.clone();
    }
    let x_words = x.to_le_u64s();
    let n_words = P256_ORDER;
    let mut diff = [0u64; 4];
    let mut borrow = 0u64;
    for i in 0..4 {
        let (s1, c1) = x_words[i].overflowing_sub(n_words[i]);
        let (s2, c2) = s1.overflowing_sub(borrow);
        diff[i] = s2;
        borrow = (c1 as u64) + (c2 as u64);
    }
    U256::from_le_u64s(&diff)
}

fn cmp_u256(lhs: &U256, rhs: &U256) -> Ordering {
    let lhs = lhs.to_le_u64s();
    let rhs = rhs.to_le_u64s();
    for i in (0..4).rev() {
        match lhs[i].cmp(&rhs[i]) {
            Ordering::Equal => {}
            ordering => return ordering,
        }
    }
    Ordering::Equal
}

#[test]
fn current_p256_proof_pipeline_links_all_implemented_components() {
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(7, 11),
        valid_real_input_with_small_u_scalars(13, 17),
    ])
    .expect("current pipeline builds");

    proof.verify_current_e2e().expect("current e2e verifies");
    assert_eq!(proof.claim.public_inputs.instances.len(), 2);
    assert_eq!(proof.claim.public_key_check.rows.len(), 2);
    assert_eq!(
        proof.claim.public_key_check.solinas_reduction_row_count(),
        224
    );
    assert_eq!(proof.claim.scalar_setup.rows.len(), 2);
    assert_eq!(proof.claim.cert_inputs.rows.len(), 4);
    assert_eq!(proof.claim.fake_glv_scalars.rows.len(), 4);
    assert_eq!(proof.claim.fake_glv_selectors.rows.len(), 4);
    assert_eq!(proof.claim.selector_requests.final_selector.len(), 4);
    assert_eq!(proof.claim.prepared_table.certs.len(), 4);
    assert_eq!(proof.claim.prepared_table_ec_trace.active_row_count(), 48);
    assert_eq!(proof.claim.fake_glv_chain.active_row_count(), 260);
    assert_eq!(proof.claim.fake_glv_ec_trace.active_row_count(), 760);
    assert_eq!(proof.claim.projective_ec_trace.active_row_count(), 808);
    assert_eq!(proof.claim.projective_rcb_air_trace.active_row_count(), 808);
    assert_eq!(
        proof.claim.projective_rcb_air_trace.mul_row_count(),
        804 * 15
    );
    // Lite (hinted-mul era) claim: the schoolbook sub-families are not built.
    // Identity rows keep their fixed-width zeroed reduction rows; lite rows
    // carry none.
    assert_eq!(
        proof.claim.projective_rcb_air_trace.reduction_row_count(),
        (proof.claim.projective_rcb_air_trace.mul_row_count()
            - proof.claim.projective_rcb_air_trace.non_identity_mul_row_count())
            * FP_SOLINAS_REDUCTION_DIGITS
    );
    assert_eq!(proof.claim.projective_rcb_air_trace.folded_digit_row_count(), 0);
    assert_eq!(
        proof
            .claim
            .projective_rcb_air_trace
            .folded_contribution_row_count(),
        0
    );
    assert_eq!(proof.claim.projective_rcb_air_trace.raw_product_chunk_count(), 0);
    assert_eq!(proof.claim.final_check.rows.len(), 2);
    assert_eq!(proof.claim.prepared_use_counts.certs.len(), 4);
    for provider in &proof.claim.prepared_trace.providers {
        assert_eq!(
            Some(provider.instance.clone()),
            proof.claim.prepared_table.instance(
                provider.instance.sig_id,
                provider.instance.cert_id,
                provider.instance.table_index.0,
            )
        );
    }
    let interaction_claim = proof.interaction_claim();
    assert_eq!(interaction_claim.public_inputs.total(), zero());
    assert_eq!(interaction_claim.selector_lookups.total(), zero());
    assert_eq!(interaction_claim.prepared_points.total(), zero());
    assert_eq!(interaction_claim.range7.total(), zero());
}

#[test]
fn current_p256_proof_pipeline_accepts_real_valid_signature_input() {
    let input = valid_real_input_with_small_u_scalars(7, 11);

    assert!(ecdsa_verify(&input));
    let proof = P256ProofDraft::from_verified_inputs_with_trivial_fake_glv_hints(vec![input])
        .expect("real valid input feeds current AIR pipeline");

    proof
        .verify_current_e2e()
        .expect("real input current e2e verifies");
    assert_eq!(
        proof.claim.scalar_setup.rows[0].output.u1,
        P256M31BigInt::from_u256(&scalar(7))
    );
    assert_eq!(
        proof.claim.scalar_setup.rows[0].output.u2,
        P256M31BigInt::from_u256(&scalar(11))
    );
    assert_eq!(proof.claim.fake_glv_chain.active_row_count(), 130);
    assert_eq!(proof.claim.fake_glv_ec_trace.active_row_count(), 380);
    assert_eq!(proof.claim.projective_ec_trace.active_row_count(), 404);
    assert_eq!(proof.claim.projective_rcb_air_trace.active_row_count(), 404);
    assert_eq!(
        proof.claim.projective_rcb_air_trace.mul_row_count(),
        402 * 15
    );
    // Lite (hinted-mul era) claim: the schoolbook sub-families are not built.
    // Identity rows keep their fixed-width zeroed reduction rows; lite rows
    // carry none.
    assert_eq!(
        proof.claim.projective_rcb_air_trace.reduction_row_count(),
        (proof.claim.projective_rcb_air_trace.mul_row_count()
            - proof.claim.projective_rcb_air_trace.non_identity_mul_row_count())
            * FP_SOLINAS_REDUCTION_DIGITS
    );
    assert_eq!(proof.claim.projective_rcb_air_trace.folded_digit_row_count(), 0);
    assert_eq!(
        proof
            .claim
            .projective_rcb_air_trace
            .folded_contribution_row_count(),
        0
    );
    assert_eq!(proof.claim.projective_rcb_air_trace.raw_product_chunk_count(), 0);
    assert_eq!(
        proof.claim.public_key_check.solinas_reduction_row_count(),
        112
    );
    let interaction_claim = proof.interaction_claim();
    assert_eq!(interaction_claim.public_inputs.total(), zero());
    assert_eq!(interaction_claim.selector_lookups.total(), zero());
    assert_eq!(interaction_claim.prepared_points.total(), zero());
    assert_eq!(interaction_claim.range7.total(), zero());
}

/// Arbitrary full-width scalars build a claim via
/// `from_inputs_with_arbitrary_fake_glv_hints` (Garaga-style decomposer +
/// the general selector AIR). Formerly the RED test for that pipeline.
#[test]
fn arbitrary_full_width_u_scalars_build_a_current_air_claim() {
    let input = valid_real_input_with_u_scalars(scalar_near_order(123), scalar_near_order(456));
    assert!(
        ecdsa_verify(&input),
        "synthetic arbitrary-width input must be valid",
    );

    P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![input])
        .expect("arbitrary full-width valid signature should build a proof draft");
}

/// End-to-end: prove + verify a real `p256`-crate signature through the
/// monolithic current AIR via the production arbitrary-fake-GLV path.
///
/// This is the headline soundness milestone: the `fake_glv_selector` AIR now
/// reconstructs an ARBITRARY decomposition (`constrain_selector_from_scalar`
/// binds both the `s1` and `s2_abs` 13-bit carry chains to the scalar relation),
/// so a genuine non-trivial `(s1, s2_abs, s2_sign_bit)` no longer trips the
/// selector constraints. The heavy release run is gated behind `--ignored` only
/// for wall-clock (a full STARK prove/verify), not because it is expected to
/// fail.
#[test]
#[cfg_attr(debug_assertions, ignore = "release-only: full STARK prove/verify is slow in debug")]
fn current_p256_monolithic_proves_real_p256_crate_signature() {
    let input = p256_crate_signed_input();
    assert!(ecdsa_verify(&input), "native verifier must accept the fixture");
    let proof = P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![input])
        .expect("real p256-crate signature builds a proof draft")
        .prove_current_air_monolithic::<Blake2sMerkleChannel>()
        .expect("real p256-crate signature proof generates");
    verify_current_air_monolithic::<Blake2sMerkleChannel>(proof)
        .expect("real p256-crate signature proof verifies");
}

/// Task 6 end-to-end: force `u1 == u2` so `R_1 = R_2` and the
/// FinalAdd AIR's finite-doubling branch is exercised inside the
/// monolithic proof.
#[test]
fn current_p256_monolithic_proves_arbitrary_doubling_final_add() {
    let input = valid_real_input_with_small_u_scalars(99, 99);
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![input])
        .expect("u1 == u2 doubling draft builds")
        .prove_current_air_monolithic::<Blake2sMerkleChannel>()
        .expect("u1 == u2 doubling proof generates");
    verify_current_air_monolithic::<Blake2sMerkleChannel>(proof)
        .expect("u1 == u2 doubling proof verifies");
}

#[test]
fn current_p256_proof_pipeline_rejects_invalid_real_signature_input() {
    let mut input = valid_real_input_with_small_u_scalars(7, 11);
    input.message_hash = scalar(123);

    assert!(!ecdsa_verify(&input));
    let err = P256ProofDraft::from_verified_inputs_with_trivial_fake_glv_hints(vec![input])
        .expect_err("invalid native signature must not enter current AIR pipeline");

    assert_eq!(err, P256ProofError::InvalidNativeEcdsaInput { index: 0 });
}

#[test]
fn current_p256_monolithic_proof_rejects_mutated_public_input_binding() {
    let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(7, 11),
    ])
    .expect("current pipeline builds");
    proof.claim.public_inputs.instances[0].r = P256M31BigInt::zero();

    let err = proof
        .prove_current_air_monolithic::<Blake2sMerkleChannel>()
        .expect_err("public tuple mismatch must reject before proving");

    assert_eq!(
        err,
        P256ProofError::RelationImbalance {
            relation: "PublicEcdsaInstance"
        }
    );
}

#[test]
fn current_p256_monolithic_verifier_rejects_mutated_public_r() {
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(7, 11),
    ])
    .expect("current pipeline builds");
    let mut monolithic = proof
        .prove_current_air_monolithic::<Blake2sMerkleChannel>()
        .expect("current AIR monolithic proof proves");
    monolithic.claim.public_inputs.instances[0].r = P256M31BigInt::zero();

    let err = verify_current_air_monolithic::<Blake2sMerkleChannel>(monolithic)
        .expect_err("mutated verifier public r must reject");

    assert!(matches!(err, P256ProofError::ProofLayer(_)));
}

/// The verifier must reject non-canonical public-key coordinates before any
/// proof work: the AIR's curve check works mod p, so a non-canonical
/// representative (`x + p`, or limbs above the 13-bit base) of a valid point
/// would otherwise pass. One honest prove, three mutation probes on clones.
#[test]
fn current_p256_monolithic_verifier_rejects_non_canonical_public_key() {
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(7, 11),
    ])
    .expect("current pipeline builds");
    let monolithic = proof
        .prove_current_air_monolithic::<Blake2sMerkleChannel>()
        .expect("current AIR monolithic proof proves");

    // pub_x := p (>= p, the non-canonical representative of 0).
    let mut forged = monolithic.clone();
    forged.claim.public_inputs.instances[0].pub_x = P256M31BigInt::from_u256(&field_modulus());
    let err = verify_current_air_monolithic::<Blake2sMerkleChannel>(forged)
        .expect_err("pub_x = p must reject");
    assert_eq!(
        err,
        P256ProofError::NonCanonicalPublicKey {
            index: 0,
            field: "pub_x",
        }
    );

    // pub_y := p + 41 (a non-canonical representative of 41; p + 41 < 2^256).
    let mut forged = monolithic.clone();
    forged.claim.public_inputs.instances[0].pub_y = P256M31BigInt::from_u256(&add_u256(
        &field_modulus(),
        &U256::from_le_u64s(&[41, 0, 0, 0]),
    ));
    let err = verify_current_air_monolithic::<Blake2sMerkleChannel>(forged)
        .expect_err("pub_y = p + 41 must reject");
    assert_eq!(
        err,
        P256ProofError::NonCanonicalPublicKey {
            index: 0,
            field: "pub_y",
        }
    );

    // A limb above the 13-bit base breaks the positional representation the
    // lexicographic `< p` comparison relies on; it must be rejected outright.
    let mut forged = monolithic;
    forged.claim.public_inputs.instances[0].pub_x.limbs_mut()[0] =
        M31::from_u32_unchecked(1 << 13);
    let err = verify_current_air_monolithic::<Blake2sMerkleChannel>(forged)
        .expect_err("out-of-range pub_x limb must reject");
    assert_eq!(
        err,
        P256ProofError::NonCanonicalPublicKey {
            index: 0,
            field: "pub_x",
        }
    );
}

#[test]
fn current_p256_monolithic_proof_rejects_mutated_cert_base() {
    let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(7, 11),
    ])
    .expect("current pipeline builds");
    proof.claim.cert_inputs.rows[1].base_x.limbs_mut()[0] = M31::from_u32_unchecked(1234);

    let err = proof
        .prove_current_air_monolithic::<Blake2sMerkleChannel>()
        .expect_err("mutated cert base must reject in the monolithic AIR");

    // Phase 2's prepared-table base pinning now catches a wrong cert base at
    // the interaction-balance check: cert_bind yields the mutated base on
    // CertBaseRelation while the prepared-table provider still consumes the
    // bound G/Q, so the relation no longer balances (a stronger, earlier
    // rejection than the previous PCS-layer ConstraintsNotSatisfied).
    assert!(
        matches!(err, P256ProofError::RelationImbalance { relation: "CertBase" }),
        "expected CertBase imbalance, got {err:?}"
    );
}

#[test]
fn current_p256_monolithic_verifier_rejects_mutated_fake_glv_scalar_claim() {
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(7, 11),
    ])
    .expect("current pipeline builds");
    let mut monolithic = proof
        .prove_current_air_monolithic::<Blake2sMerkleChannel>()
        .expect("current AIR monolithic proof proves");
    monolithic.claim.fake_glv_scalar_air.log_size += 1;

    let err = verify_current_air_monolithic::<Blake2sMerkleChannel>(monolithic)
        .expect_err("mutated fake-GLV scalar AIR claim must reject");

    assert!(matches!(err, P256ProofError::ProofLayer(_)));
}

#[test]
fn current_p256_monolithic_verifier_rejects_mutated_fake_glv_selector_claim() {
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(7, 11),
    ])
    .expect("current pipeline builds");
    let mut monolithic = proof
        .prove_current_air_monolithic::<Blake2sMerkleChannel>()
        .expect("current AIR monolithic proof proves");
    monolithic.claim.fake_glv_selector_air.log_size += 1;

    let err = verify_current_air_monolithic::<Blake2sMerkleChannel>(monolithic)
        .expect_err("mutated fake-GLV selector AIR claim must reject");

    assert!(matches!(err, P256ProofError::ProofLayer(_)));
}

#[test]
fn current_p256_monolithic_verifier_rejects_unbalanced_ecdsa_result_sum() {
    use num_traits::One;
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(7, 11),
    ])
    .expect("current pipeline builds");
    let mut monolithic = proof
        .prove_current_air_monolithic::<Blake2sMerkleChannel>()
        .expect("current AIR monolithic proof proves");
    monolithic
        .interaction_claim
        .ecdsa_result_provider_claimed_sum += SecureField::one();

    let err = verify_current_air_monolithic::<Blake2sMerkleChannel>(monolithic)
        .expect_err("EcdsaResult balance must reject mutated provider sum");

    assert!(matches!(
        err,
        P256ProofError::RelationImbalance {
            relation: "EcdsaResult"
        }
    ));
}

#[test]
fn current_p256_monolithic_verifier_rejects_unbalanced_range7_consumer_sum() {
    use num_traits::One;
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(7, 11),
    ])
    .expect("current pipeline builds");
    let mut monolithic = proof
        .prove_current_air_monolithic::<Blake2sMerkleChannel>()
        .expect("current AIR monolithic proof proves");
    monolithic
        .interaction_claim
        .fake_glv_prepared_point_source
        .range7_consumer_claimed_sum += SecureField::one();

    let err = verify_current_air_monolithic::<Blake2sMerkleChannel>(monolithic)
        .expect_err("Range7 balance must reject mutated consumer sum");

    assert!(matches!(
        err,
        P256ProofError::RelationImbalance { relation: "Range7" }
    ));
}

#[test]
fn current_p256_monolithic_verifier_rejects_unbalanced_scalar_consumer_sum() {
    use num_traits::One;
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(7, 11),
    ])
    .expect("current pipeline builds");
    let mut monolithic = proof
        .prove_current_air_monolithic::<Blake2sMerkleChannel>()
        .expect("current AIR monolithic proof proves");
    monolithic
        .interaction_claim
        .fake_glv_selector_air
        .scalar_consumer_claimed_sum += SecureField::one();

    let err = verify_current_air_monolithic::<Blake2sMerkleChannel>(monolithic)
        .expect_err("scalar relation balance must reject mutated consumer sum");

    assert!(matches!(
        err,
        P256ProofError::RelationImbalance {
            relation: "FakeGlvScalar"
        }
    ));
}

#[test]
fn current_p256_proof_pipeline_rejects_invalid_final_signature_linkage() {
    let err =
        P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![test_input(42, 77, 1)])
            .expect_err("invalid final signature linkage must fail");

    assert!(matches!(
        err,
        P256ProofError::FinalEcdsaCheck(FinalEcdsaCheckError::SignatureRMismatch { .. })
    ));
}

#[test]
fn current_p256_proof_pipeline_rejects_public_key_off_curve() {
    let mut input = valid_real_input_with_small_u_scalars(7, 11);
    input.public_key.y = scalar(1);

    let err = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![input])
        .expect_err("off-curve public key must fail");

    assert!(matches!(
        err,
        P256ProofError::PublicKeyOnCurve(PublicKeyOnCurveError::PointOffCurve { .. })
    ));
}

/// In-AIR public-key-on-curve binding: the monolithic STARK proves the
/// public key lies on the curve via a dedicated curve-check component whose
/// witnessed `(x, y)` is LogUp-bound to the public input through
/// `PublicKeyPointRelation` (provided by scalar_setup, consumed by the
/// curve-check). Mutating the public-input `pub_y` after the draft is built
/// makes the scalar_setup provider emit a `pub_y'` that no longer matches
/// the curve-check's witnessed `y`, so the regenerated prover-side
/// `PublicKeyPoint` balance is non-zero and proving is rejected. Per
/// lessons.md #18 the rejection oracle is the relation-balance audit
/// (`RelationImbalance`), not `assert_constraints`.
#[test]
fn current_p256_proof_pipeline_rejects_public_key_off_curve_in_air() {
    let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(7, 11),
    ])
    .expect("current pipeline builds");

    // Swap the curve-check witness to a *different* valid on-curve public
    // key (2*G) while leaving scalar_setup and the public input bound to the
    // real key (G). Everything else still balances; only the
    // `PublicKeyPoint` binding tuple drifts: the curve check now consumes
    // (sig_id, 2G_x, 2G_y) while scalar_setup provides (sig_id, G_x, G_y).
    // This is exactly the soundness property the binding enforces - the
    // curve-checked point must equal the public key - and it is caught by
    // the relation-balance audit (lessons.md #18), not assert_constraints.
    let two_g = scalar_mul(&scalar(2), &generator_point()).expect("2*G is finite");
    let other_inputs = PublicEcdsaInputClaim::from_inputs(&[EcdsaVerifyInput {
        message_hash: scalar(42),
        signature: Signature {
            r: scalar(77),
            s: scalar(11),
        },
        public_key: two_g,
    }]);
    proof.claim.public_key_check =
        PublicKeyOnCurveClaim::from_public_inputs(&other_inputs).expect("2*G is on curve");

    let err = proof
        .prove_current_air_monolithic::<Blake2sMerkleChannel>()
        .expect_err("curve-check (x,y) unbound from public key must reject in the AIR");

    assert_eq!(
        err,
        P256ProofError::RelationImbalance {
            relation: "PublicKeyPoint"
        }
    );
}

/// The verifier independently enforces the `PublicKeyPoint` binding balance:
/// tampering with the scalar_setup provider's claimed sum on a fully valid
/// monolithic proof is rejected by `verify_current_air_monolithic`.
#[test]
fn current_p256_monolithic_verifier_rejects_unbalanced_public_key_point_sum() {
    use num_traits::One;
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(7, 11),
    ])
    .expect("current pipeline builds");
    let mut monolithic = proof
        .prove_current_air_monolithic::<Blake2sMerkleChannel>()
        .expect("current AIR monolithic proof proves");
    monolithic
        .interaction_claim
        .scalar_setup
        .point_provider_claimed_sum += SecureField::one();

    let err = verify_current_air_monolithic::<Blake2sMerkleChannel>(monolithic)
        .expect_err("PublicKeyPoint balance must reject a mutated provider sum");

    assert!(matches!(
        err,
        P256ProofError::RelationImbalance {
            relation: "PublicKeyPoint"
        }
    ));
}

#[test]
fn current_p256_proof_pipeline_allows_zero_u1_branch() {
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(0, 11),
    ])
    .expect("zero branch pipeline builds");

    proof.verify_current_e2e().expect("zero branch verifies");
    assert_eq!(proof.claim.cert_inputs.rows[0].cert_active.0, 0);
    assert_eq!(
        proof.claim.prepared_use_counts.certs[0].total_use_count(),
        0
    );
    assert_eq!(
        proof.claim.prepared_use_counts.certs[1].total_use_count(),
        65
    );
    assert_eq!(proof.claim.fake_glv_chain.active_row_count(), 65);
    assert_eq!(proof.claim.fake_glv_ec_trace.active_row_count(), 190);
    assert_eq!(proof.claim.projective_ec_trace.active_row_count(), 203);
    assert_eq!(
        proof.claim.final_check.rows[0].h1,
        PreparedAffinePoint::infinity()
    );
}

#[test]
fn current_p256_proof_pipeline_proves_and_verifies_current_air_monolithic_proof() {
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(0, 11),
    ])
    .expect("zero branch pipeline builds");
    proof.verify_current_e2e().expect("zero branch verifies");

    let monolithic = proof
        .prove_current_air_monolithic::<Blake2sMerkleChannel>()
        .expect("current AIR monolithic proof proves");

    verify_current_air_monolithic::<Blake2sMerkleChannel>(monolithic)
        .expect("current AIR monolithic proof verifies");
}

/// Full monolithic prove/verify on the DISTINCT-finite-points branch
/// `(u1, u2) = (7, 11)` (both `h1, h2` finite, `x1 != x2`). This exercises
/// the final-add chord-addition identities with `both_finite = 1` through
/// the full PCS/OODS composition (the primary gate uses the zero-`u1`
/// branch where `both_finite = 0`), confirming the witnessed
/// `dx_inv_result` LogUp tuple matches off-domain.
#[test]
fn current_p256_proof_pipeline_proves_and_verifies_monolithic_distinct_branch() {
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(7, 11),
    ])
    .expect("distinct branch pipeline builds");
    proof.verify_current_e2e().expect("distinct branch verifies");

    let monolithic = proof
        .prove_current_air_monolithic::<Blake2sMerkleChannel>()
        .expect("distinct branch monolithic proof proves");

    verify_current_air_monolithic::<Blake2sMerkleChannel>(monolithic)
        .expect("distinct branch monolithic proof verifies");
}

#[test]
#[ignore = "prints and asserts current AIR constraints component by component"]
fn current_p256_air_constraint_diagnostic() {
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(0, 11),
    ])
    .expect("zero branch pipeline builds");
    proof.verify_current_e2e().expect("zero branch verifies");

    assert_current_air_constraints(&proof);
}

#[test]
#[ignore = "diagnostic: row-by-row constraint dump for a real p256-crate \
    signature (the general selector AIR now accepts arbitrary s2_abs / sign; \
    this passes — kept as a slow manual diagnostic)"]
fn current_p256_air_constraint_diagnostic_real_p256() {
    let proof = P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![
        p256_crate_signed_input(),
    ])
    .expect("real p256 pipeline builds");
    proof.verify_current_e2e().expect("real p256 e2e verifies");

    assert_current_air_constraints(&proof);
}

/// EXPERIMENT (Phase A — feasibility probe): for ONE active cert, rebuild
/// the prepared table and fake-GLV chain from a WRONG hint point
/// `R' != ±u·base` (a valid curve point) while keeping `u`, the public
/// input and the selectors (= digits of `u`) UNCHANGED. Report whether the
/// chain's internal `final_acc == r3` gate holds for the wrong `R'`. If it
/// FAILS, no globally consistent wrong-`R` chain exists (the windowed
/// accumulation itself binds `R`). If it HOLDS, the accumulation does not
/// bind `R` and the full prove/verify experiment is worth running.
#[test]
fn wrong_r_chain_feasibility_probe() {
    let inputs = vec![valid_real_input_with_small_u_scalars(7, 11)];
    let claim = P256ProofClaim::from_inputs_with_trivial_fake_glv_hints(&inputs)
        .expect("valid claim builds");

    for cert_index in 0..claim.cert_inputs.rows.len() {
        let cert = &claim.cert_inputs.rows[cert_index];
        if cert.cert_active.0 == 0 {
            eprintln!("cert {cert_index}: inactive, skipping");
            continue;
        }
        let fake_glv = &claim.fake_glv_scalars.rows[cert_index];
        let selector = &claim.fake_glv_selectors.rows[cert_index];

        // Sanity: reconstruct the TRUE R the production pipeline used.
        let base = AffinePoint {
            x: cert.base_x.to_u256(),
            y: cert.base_y.to_u256(),
        };
        let u = cert.scalar.to_u256();
        let h = scalar_mul(&u, &base).expect("u*base finite");
        let true_r = match fake_glv.hint.s2_sign_bit.0 {
            0 => h.clone(),
            1 => negate_affine(&h),
            _ => panic!("bad sign bit"),
        };

        // Pick a WRONG R' that is a valid curve point but != ±u·base:
        // R' = (u+1)*base.
        let u_plus_1 = add_u256(&u, &U256::from_le_u64s(&[1, 0, 0, 0]));
        let wrong_r = scalar_mul(&u_plus_1, &base).expect("(u+1)*base finite");
        assert_ne!(wrong_r, true_r, "R' must differ from the true R");
        assert_ne!(wrong_r, negate_affine(&true_r), "R' must differ from -R");

        // Rebuild table + chain from R' using the production algorithm.
        let wrong_table =
            PreparedTableCert::new_with_r_override(cert, fake_glv, selector, wrong_r.clone())
                .expect("override table builds");
        let wrong_chain = FakeGlvChainCert::from_claims_with_r_override(
            cert,
            selector,
            &wrong_table,
            wrong_r.clone(),
        )
        .expect("override chain builds");

        let gate_holds = wrong_chain.final_acc == wrong_chain.r3;
        let verify_result = wrong_chain.verify();
        eprintln!(
            "cert {cert_index} (cert_id={}): WRONG-R final_acc==r3 gate holds = {gate_holds}; chain.verify() = {:?}",
            cert.cert_id.0, verify_result
        );

        // Cross-check: the SAME rebuild with the TRUE R must satisfy the gate.
        let true_table =
            PreparedTableCert::new_with_r_override(cert, fake_glv, selector, true_r.clone())
                .expect("true override table builds");
        let true_chain = FakeGlvChainCert::from_claims_with_r_override(
            cert,
            selector,
            &true_table,
            true_r.clone(),
        )
        .expect("true override chain builds");
        assert_eq!(
            true_chain.final_acc, true_chain.r3,
            "sanity: the TRUE R rebuild must satisfy final_acc==r3 (override harness fidelity)"
        );
        assert!(
            true_chain.verify().is_ok(),
            "sanity: TRUE R chain verifies"
        );
    }
}

fn true_r_for_cert(claim: &P256ProofClaim, cert_index: usize) -> AffinePoint {
    let cert = &claim.cert_inputs.rows[cert_index];
    let fake_glv = &claim.fake_glv_scalars.rows[cert_index];
    let base = AffinePoint {
        x: cert.base_x.to_u256(),
        y: cert.base_y.to_u256(),
    };
    let h = scalar_mul(&cert.scalar.to_u256(), &base).expect("u*base finite");
    match fake_glv.hint.s2_sign_bit.0 {
        0 => h,
        1 => negate_affine(&h),
        _ => panic!("bad sign bit"),
    }
}

/// FIDELITY CONTROL for the wrong-R AIR oracle: drive the *same* override
/// build path with the TRUE `R`. If `assert_current_air_constraints`
/// passes cleanly here, the override harness is faithful and the Phase C
/// constraint violation is attributable to the wrong `R'`, not to the
/// harness.
#[test]
fn wrong_r_harness_fidelity_true_r_air_constraints_pass() {
    let inputs = vec![valid_real_input_with_small_u_scalars(7, 11)];
    let base_claim = P256ProofClaim::from_inputs_with_trivial_fake_glv_hints(&inputs)
        .expect("valid claim builds");
    let true_r = true_r_for_cert(&base_claim, 0);

    let rebuilt =
        P256ProofClaim::from_inputs_with_wrong_r_for_cert(&inputs, 0, true_r.clone())
            .expect("true-R rebuild via override path assembles");
    // The override path must reproduce the production claim exactly.
    assert_eq!(
        rebuilt.prepared_table, base_claim.prepared_table,
        "override prepared_table with TRUE R must equal production"
    );
    assert_eq!(
        rebuilt.fake_glv_chain, base_claim.fake_glv_chain,
        "override chain with TRUE R must equal production"
    );

    let relations = P256ProofRelations::dummy();
    let draft = P256ProofDraft {
        inputs,
        claim: rebuilt,
        relations,
    };
    assert_current_air_constraints(&draft);
    eprintln!("FIDELITY: TRUE-R override path passes assert_current_air_constraints cleanly.");
}

fn wrong_r_for_cert(claim: &P256ProofClaim, cert_index: usize) -> AffinePoint {
    let cert = &claim.cert_inputs.rows[cert_index];
    let base = AffinePoint {
        x: cert.base_x.to_u256(),
        y: cert.base_y.to_u256(),
    };
    let u = cert.scalar.to_u256();
    let u_plus_1 = add_u256(&u, &U256::from_le_u64s(&[1, 0, 0, 0]));
    scalar_mul(&u_plus_1, &base).expect("(u+1)*base finite")
}

/// EXPERIMENT (Phase B — full monolithic pipeline on a wrong-`R` witness).
/// Builds a globally consistent claim whose cert-0 prepared table + chain
/// use `R' = (u+1)*base != ±u*base`, then drives
/// `prove_current_air_monolithic`. Reports the exact observed outcome.
#[test]
fn wrong_r_monolithic_prove_outcome() {
    let inputs = vec![valid_real_input_with_small_u_scalars(7, 11)];
    let base_claim = P256ProofClaim::from_inputs_with_trivial_fake_glv_hints(&inputs)
        .expect("valid claim builds");
    let r_prime = wrong_r_for_cert(&base_claim, 0);

    let wrong_claim =
        P256ProofClaim::from_inputs_with_wrong_r_for_cert(&inputs, 0, r_prime.clone())
            .expect("wrong-R claim assembles (no native gate in override builders)");

    // Build the draft manually: no draft builder exists for a wrong-R claim
    // (the `from_inputs_*` builders run a native ECDSA gate that rejects it).
    let relations = P256ProofRelations::dummy();
    let draft = P256ProofDraft {
        inputs: inputs.clone(),
        claim: wrong_claim,
        relations,
    };

    // (1) Does the native pre-check inside prove reject?
    match draft.prove_current_air_monolithic::<Blake2sMerkleChannel>() {
        Ok(_) => eprintln!(
            "PHASE B: prove_current_air_monolithic SUCCEEDED on wrong-R witness (UNEXPECTED — would indicate acceptance)"
        ),
        Err(e) => eprintln!("PHASE B: prove_current_air_monolithic REJECTED wrong-R: {e:?}"),
    }
}

/// EXPERIMENT (Phase C — DECISIVE AIR oracle). Runs `assert_constraints`
/// directly on the wrong-`R` trace, bypassing every native shape check.
/// A clean return == AIR ACCEPTS (soundness gap). A panic/abort == AIR
/// REJECTS (sound). This isolates whether the monolithic AIR *constraints*
/// bind `R` to `u*base`, independent of native validation.
#[test]
#[ignore = "decisive manual wrong-R AIR oracle: assert_current_air_constraints \
            panics (clean single polynomial-constraint panic at \
            fake_glv_chain_continuity final_acc==r3) when the AIR correctly \
            rejects a wrong R (sound). Run with --ignored. Not auto-run to avoid \
            the lessons.md #18 double-panic/SIGABRT risk in the shared suite."]
fn wrong_r_air_constraints_oracle() {
    let inputs = vec![valid_real_input_with_small_u_scalars(7, 11)];
    let base_claim = P256ProofClaim::from_inputs_with_trivial_fake_glv_hints(&inputs)
        .expect("valid claim builds");
    let r_prime = wrong_r_for_cert(&base_claim, 0);

    let wrong_claim =
        P256ProofClaim::from_inputs_with_wrong_r_for_cert(&inputs, 0, r_prime.clone())
            .expect("wrong-R claim assembles");
    let relations = P256ProofRelations::dummy();
    let draft = P256ProofDraft {
        inputs,
        claim: wrong_claim,
        relations,
    };

    eprintln!(
        "PHASE C: running assert_current_air_constraints on wrong-R trace; \
         a clean PASS == AIR accepts (gap), a panic/abort == AIR rejects (sound)."
    );
    assert_current_air_constraints(&draft);
    eprintln!(
        "PHASE C: assert_current_air_constraints RETURNED CLEANLY on wrong-R trace \
         => AIR ACCEPTED the wrong R (soundness gap confirmed)."
    );
}

fn negate_affine(p: &AffinePoint) -> AffinePoint {
    let m = U256::from_le_u64s(&P256_MODULUS);
    AffinePoint {
        x: p.x.clone(),
        y: crate::field_ops::sub_mod_witness(&m, &p.y, &m).result.to_u256(),
    }
}

fn add_u256(a: &U256, b: &U256) -> U256 {
    let a = a.to_le_u64s();
    let b = b.to_le_u64s();
    let mut out = [0u64; 4];
    let mut carry = 0u128;
    for i in 0..4 {
        let sum = a[i] as u128 + b[i] as u128 + carry;
        out[i] = sum as u64;
        carry = sum >> 64;
    }
    U256::from_le_u64s(&out)
}

/// Re-run the monolithic interaction-trace generation for `draft` and return
/// the resulting interaction claim, with relations drawn from the real
/// transcript. The per-relation LogUp balance it carries is the in-AIR
/// rejection oracle (lessons.md #18); a tampered witness that unbalances any
/// relation is caught by `verify_balanced` (first imbalance) or surfaced in
/// full by `relation_audit`.
fn monolithic_interaction_claim(draft: &P256ProofDraft) -> P256CurrentAirInteractionClaim {
    let proof_claim = P256CurrentAirProofClaim::from_claim(&draft.claim);
    let ids = proof_claim.preprocessed_column_ids();
    let max_bound = proof_claim.max_constraint_log_degree_bound(&ids);
    let config = p256_stark_monolithic_profile_config(max_bound);
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(config.lifting_log_size.unwrap_or(
            max_bound + config.fri_config.log_blowup_factor,
        ))
        .circle_domain()
        .half_coset,
    );
    let mut channel = <Blake2sMerkleChannel as MerkleChannel>::C::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);
    let preprocessed = draft
        .gen_current_air_preprocessed_trace(&proof_claim, &ids)
        .expect("preprocessed trace");
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(preprocessed);
    tree_builder.commit(&mut channel);
    proof_claim.mix_into(&mut channel);
    let mut base = draft.gen_current_air_base_trace(&proof_claim).expect("base trace");
    let base_columns = std::mem::take(&mut base.columns);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(base_columns);
    tree_builder.commit(&mut channel);
    let relations = P256CurrentAirRelations::draw(&mut channel);
    let (_, interaction_claim) = draft
        .gen_current_air_interaction_trace(&base, &relations)
        .expect("interaction trace");
    interaction_claim
}

/// The per-relation balance result for `draft` (the first-imbalance oracle
/// the adversarial tests assert on).
fn monolithic_balance_outcome(draft: &P256ProofDraft) -> Result<(), P256ProofError> {
    monolithic_interaction_claim(draft).verify_balanced()
}

#[test]
fn relation_audit_lists_all_imbalances_and_dead_links() {
    let nonzero = SecureField::from(M31::from_u32_unchecked(1));
    let audit = P256CurrentAirRelationAudit {
        balances: vec![
            ("Alpha", zero()),
            ("Beta", nonzero),
            ("Gamma", zero()),
            ("Delta", nonzero),
        ],
        liveness: vec![("LiveOk", nonzero), ("DeadLink", zero())],
    };
    // Reports ALL imbalances at once, not just the first.
    assert_eq!(audit.imbalanced(), vec!["Beta", "Delta"]);
    assert_eq!(audit.first_imbalance(), Some("Beta"));
    assert!(!audit.is_balanced());
    // A boundary relation that emitted nothing is flagged even though it
    // "balances" (0 + 0 == 0) — the unlinked-sub-graph case.
    assert_eq!(audit.dead_links(), vec!["DeadLink"]);
    assert_eq!(audit.relation_names(), vec!["Alpha", "Beta", "Gamma", "Delta"]);

    let healthy = P256CurrentAirRelationAudit {
        balances: vec![("A", zero())],
        liveness: vec![("L", nonzero)],
    };
    assert!(healthy.is_balanced());
    assert!(healthy.imbalanced().is_empty());
    assert!(healthy.dead_links().is_empty());
}

#[test]
fn monolithic_relation_audit_is_balanced_and_fully_linked() {
    // Both certs active (u1, u2 != 0), so every boundary relation must be live.
    let draft = valid_draft_for_balance(7, 11);
    let audit = monolithic_interaction_claim(&draft).relation_audit();
    assert!(
        audit.is_balanced(),
        "honest proof has unbalanced relations: {:?}",
        audit.imbalanced()
    );
    assert!(
        audit.dead_links().is_empty(),
        "honest active proof has unlinked boundary relations: {:?}",
        audit.dead_links()
    );
    // The audit covers the full relation surface, including the four
    // verifier-facing ECDSA bindings.
    // The audit covers the full relation surface, in `relation_balances()`
    // order. EXHAUSTIVE on purpose: adding a relation to the proof without
    // registering it in the audit (or removing/renaming one) must fail here
    // with the exact name, not a bare count mismatch.
    let expected = [
        "PublicEcdsaInstance",
        "ScalarSetupOutput",
        "CertScalarInput",
        "FakeGlvScalar",
        "ScalarSetupRange13",
        "ScalarSetupRange9",
        "ScalarSetupSignedCarry",
        "ScalarSetupModMul",
        "FakeGlvScalarModMul",
        "PreparedTablePinnedConsistency",
        "PreparedTablePinnedBreakdown",
        "PreparedTableProjectiveSource",
        // C5-2: the prepared-table projective-source formula self-contained
        // Range13 / signed-carry providers (the table-build EC arithmetic).
        "PreparedTableProjectiveRange13",
        "PreparedTableProjectiveSignedCarry",
        "CertBase",
        "PreparedTableCanonical",
        "FakeGlvProjectiveSource",
        // C5-2: the fake-GLV projective-source Double/MixedAdd-formula
        // self-contained Range13 / signed-carry providers.
        "FakeGlvProjectiveRange13",
        "FakeGlvProjectiveSignedCarry",
        // C5 plumbing: the RCB silo → projective-source mul-result link.
        "ProjectiveRcbMulResult",
        "FakeGlvChainExpansion",
        "FakeGlvChainContinuity",
        "FakeGlvDirectPreparedOperand",
        "FakeGlvSignedSelectorOperand",
        "FakeGlvLsbCorrectionOperand",
        "FakeGlvPreparedPointSource",
        "Range7",
        "EcdsaResult",
        "PublicKeyPoint",
        "HintedMulRange13",
        "HintedMulSignedH",
        "HintedMulTotalConsistency",
        "FinalCheckHint",
        "FinalAddInternal",
        "FinalAddOutput",
    ];
    assert_eq!(
        audit.relation_names(),
        expected,
        "relation audit must cover exactly the proof's relation surface"
    );
}

/// Build a valid single-signature draft for the in-AIR adversarial tests.
fn valid_draft_for_balance(u1: u64, u2: u64) -> P256ProofDraft {
    let relations = P256ProofRelations::dummy();
    let claim = P256ProofClaim::from_inputs_with_trivial_fake_glv_hints(&[
        valid_real_input_with_small_u_scalars(u1, u2),
    ])
    .expect("valid claim");
    P256ProofDraft {
        inputs: vec![valid_real_input_with_small_u_scalars(u1, u2)],
        claim,
        relations,
    }
}

fn bump_limb0(value: &crate::limbs::P256M31BigInt) -> crate::limbs::P256M31BigInt {
    let mut limbs = *value.limbs();
    limbs[0] = limbs[0] + M31::from_u32_unchecked(1);
    crate::limbs::P256M31BigInt::from_limbs(limbs)
}

/// Extract an `M31ColumnEval`'s cells into a per-row `Vec<M31>` in the column's
/// own storage order (used to forge one cell and rebuild the column).
fn column_to_values(column: &crate::scalar::scalar_mod_mul::columns::M31ColumnEval) -> Vec<M31> {
    let mut out = Vec::new();
    for packed in &column.data {
        out.extend_from_slice(&packed.to_array());
    }
    out
}

/// C5-2a-ii IN-AIR oracle: forging a Double-op `output_affine.x` limb on the
/// fake-GLV projective-source consumer must make the consumer's AIR constraints
/// UNSATISFIABLE — the affine-normalization binding `R13 == x3` (gated by
/// `out_finite`, with the silo's `R13 = output.x · z3`) fires. This isolates the
/// Double-formula coordinate binding: the forge is applied to the COMMITTED
/// `output.x` column AFTER native trace generation (which would otherwise reject
/// a wrong affine), so the rejection is the AIR constraint itself, not the
/// native `verify()`. Pre-this-change (no Double-formula constraints) the same
/// committed forge satisfied every consumer constraint (the EC-row self-loop
/// cancels regardless of the output value) — i.e. the proof VERIFIED — which was
/// the C5 hole. A clean honest control runs first.
#[test]
fn current_p256_monolithic_rejects_forged_double_op_output() {
    use crate::scalar::prepared_table::PREPARED_TABLE_EC_POINT_COLUMNS;

    // u1 == u2 drives the doubling ladder, so the projective EC trace contains
    // active Double ops. The forge target is the committed Double-op
    // `output_affine.x` (limb 0) on the fake-GLV projective-source CONSUMER.
    //
    // Oracle: the per-relation LogUp balance (lessons.md #18 — `verify_balanced`,
    // not `assert_constraints`, which double-panics on a failing row via the
    // `LogupAtRow::drop` finalize assert). The forge is applied to the COMMITTED
    // base trace AFTER native trace generation (which would otherwise reject a
    // wrong affine via `ProjectiveEcRow::verify`), so the rejection is the AIR's
    // own balance, not the native check.
    //
    // The committed `output.x` participates in the `FakeGlvProjectiveSource`
    // EC-row relation (consumer use vs provider yield) AND, post-C5-2, in the
    // Double-formula `M13.lhs == output.x` operand binding — so a forged
    // `output.x` both unbalances the EC-row relation and violates the in-AIR
    // Double binding. Either way the proof is rejected.
    let op_col = 4usize;
    let output_x0_col = 5 + 2 * PREPARED_TABLE_EC_POINT_COLUMNS;
    let double_op =
        M31::from_u32_unchecked(crate::scalar::prepared_table::PREPARED_TABLE_EC_OP_DOUBLE);

    let honest = forged_double_output_balance_outcome(99, 99, None);
    honest.expect("honest doubling proof balances");

    let err = forged_double_output_balance_outcome(99, 99, Some((op_col, output_x0_col, double_op)))
        .expect_err("forged Double-op output.x must be rejected by the monolithic AIR");
    // The forged committed output.x unbalances the EC-row relation that binds the
    // consumer's output to the provider's (and, via C5-2, to double(input)).
    assert!(
        matches!(
            err,
            P256ProofError::RelationImbalance {
                relation: "FakeGlvProjectiveSource"
            }
        ),
        "expected FakeGlvProjectiveSource imbalance from forged Double output, got {err:?}"
    );
}

/// C5-2b sibling of `current_p256_monolithic_rejects_forged_double_op_output`,
/// for the MixedAdd-op coordinate formula. The distinct branch (`u1 != u2`)
/// drives the chain's DOUBLE/DOUBLE/ADD ladder, so the projective EC trace
/// contains active MixedAdd ops (op-code 0). The forge target is the committed
/// MixedAdd-op `output_affine.x` (limb 0) on the fake-GLV projective-source
/// CONSUMER.
///
/// Oracle: the same per-relation LogUp balance. The committed `output.x`
/// participates in the `FakeGlvProjectiveSource` EC-row relation (consumer use
/// vs provider yield) AND, post-C5-2b, in the MixedAdd-formula `M13.lhs ==
/// output.x` operand binding — so a forged `output.x` unbalances the EC-row
/// relation. (The dedicated binding-isolating tests are C5-3; this is the
/// end-to-end rejection.) A clean honest control runs first.
#[test]
fn current_p256_monolithic_rejects_forged_mixed_add_op_output() {
    use crate::scalar::prepared_table::PREPARED_TABLE_EC_POINT_COLUMNS;

    let op_col = 4usize;
    let output_x0_col = 5 + 2 * PREPARED_TABLE_EC_POINT_COLUMNS;
    let mixed_add_op =
        M31::from_u32_unchecked(crate::scalar::prepared_table::PREPARED_TABLE_EC_OP_MIXED_ADD);

    // Distinct branch (u1 != u2) so the ladder runs real mixed-adds.
    let honest = forged_double_output_balance_outcome(7, 11, None);
    honest.expect("honest distinct-branch proof balances");

    let err =
        forged_double_output_balance_outcome(7, 11, Some((op_col, output_x0_col, mixed_add_op)))
            .expect_err("forged MixedAdd-op output.x must be rejected by the monolithic AIR");
    assert!(
        matches!(
            err,
            P256ProofError::RelationImbalance {
                relation: "FakeGlvProjectiveSource"
            }
        ),
        "expected FakeGlvProjectiveSource imbalance from forged MixedAdd output, got {err:?}"
    );
}

/// Build the monolithic interaction claim for a `u1`/`u2` doubling draft and
/// return its `verify_balanced()` outcome. If `forge` is `Some((op_col,
/// limb_col, double_op))`, the COMMITTED fake-GLV projective-source CONSUMER base
/// column `limb_col` is bumped by 1 on the first active row whose op-code column
/// `op_col` equals `double_op` — a post-trace-gen forge of a Double-op output
/// limb that exercises the in-AIR rejection (balance) rather than the native
/// `ProjectiveEcRow::verify`.
fn forged_double_output_balance_outcome(
    u1: u64,
    u2: u64,
    forge: Option<(usize, usize, M31)>,
) -> Result<(), P256ProofError> {
    use stwo::core::poly::circle::CanonicCoset as CoreCanonicCoset;

    let input = valid_real_input_with_small_u_scalars(u1, u2);
    let draft = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![input])
        .expect("doubling draft builds");
    let proof_claim = P256CurrentAirProofClaim::from_claim(&draft.claim);
    let ids = proof_claim.preprocessed_column_ids();
    let max_bound = proof_claim.max_constraint_log_degree_bound(&ids);
    let config = p256_stark_monolithic_profile_config(max_bound);
    let twiddles = SimdBackend::precompute_twiddles(
        CoreCanonicCoset::new(
            config
                .lifting_log_size
                .unwrap_or(max_bound + config.fri_config.log_blowup_factor),
        )
        .circle_domain()
        .half_coset,
    );
    let mut channel = <Blake2sMerkleChannel as MerkleChannel>::C::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);
    let preprocessed = draft
        .gen_current_air_preprocessed_trace(&proof_claim, &ids)
        .expect("preprocessed trace");
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(preprocessed);
    tree_builder.commit(&mut channel);
    proof_claim.mix_into(&mut channel);

    let mut base = draft.gen_current_air_base_trace(&proof_claim).expect("base trace");

    // Optional forge: bump one committed CONSUMER limb on the first active Double
    // row (post-trace-gen, so native verification has already passed).
    if let Some((op_col, limb_col, double_op)) = forge {
        let consumer = &mut base.fake_glv_projective_consumer;
        let log_size = consumer[0].domain.log_size();
        let row_count = 1usize << log_size;
        let active_vals = column_to_values(&consumer[0]);
        let op_vals = column_to_values(&consumer[op_col]);
        let mut limb_vals = column_to_values(&consumer[limb_col]);
        let forge_row = (0..row_count)
            .find(|&row| {
                active_vals[row] != M31::from_u32_unchecked(0) && op_vals[row] == double_op
            })
            .expect("doubling proof must contain an active Double row to forge");
        limb_vals[forge_row] = limb_vals[forge_row] + M31::from_u32_unchecked(1);
        let forged_col = stwo::prover::poly::circle::CircleEvaluation::new(
            consumer[limb_col].domain,
            stwo::prover::backend::simd::column::BaseColumn::from_iter(limb_vals),
        );
        consumer[limb_col] = forged_col;
        // Re-flatten the forged consumer columns into the monolithic `columns`
        // so the committed trace reflects the forge. The consumer block is a
        // contiguous slice; rebuild `base.columns` from the per-sub-graph fields
        // is overkill, so instead recompute the interaction directly below from
        // the (forged) `base` fields the interaction generator reads.
    }

    let base_columns = std::mem::take(&mut base.columns);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(base_columns);
    tree_builder.commit(&mut channel);
    let relations = P256CurrentAirRelations::draw(&mut channel);
    let (_, interaction_claim) = draft
        .gen_current_air_interaction_trace(&base, &relations)
        .expect("interaction trace");
    interaction_claim.verify_balanced()
}

/// IN-AIR oracle: mutating the proven final-add output `x3` (= `R_final.x`)
/// away from the value the final check consumes as `r_x` unbalances the
/// `FinalAddOutput` relation, so `verify_balanced` rejects.
#[test]
fn monolithic_rejects_mutated_final_add_x3() {
    let mut draft = valid_draft_for_balance(7, 11);
    monolithic_balance_outcome(&draft).expect("honest draft balances");
    draft.claim.final_add.x3 = bump_limb0(&draft.claim.final_add.x3);
    let err = monolithic_balance_outcome(&draft).expect_err("mutated x3 must reject");
    assert!(
        matches!(err, P256ProofError::RelationImbalance { relation: "FinalAddOutput" }),
        "expected FinalAddOutput imbalance, got {err:?}"
    );
}

/// IN-AIR oracle: mutating a consumed hint point `R_1` unbalances the
/// `FinalCheckHint` relation (the prepared table still yields the true,
/// pinned `R_1`), so `verify_balanced` rejects.
#[test]
fn monolithic_rejects_mutated_consumed_hint() {
    let mut draft = valid_draft_for_balance(7, 11);
    monolithic_balance_outcome(&draft).expect("honest draft balances");
    let new_x = bump_limb0(&draft.claim.final_add.r1.x);
    draft.claim.final_add.r1.x = new_x;
    let err = monolithic_balance_outcome(&draft).expect_err("mutated R_1 must reject");
    assert!(
        matches!(err, P256ProofError::RelationImbalance { relation: "FinalCheckHint" }),
        "expected FinalCheckHint imbalance, got {err:?}"
    );
}

/// IN-AIR oracle: mutating the public signature `r` unbalances the public
/// relations binding `r`. The public `r` is provided on BOTH
/// `PublicEcdsaInstance` (the full instance tuple) and `EcdsaResult` (the
/// write-back the final check consumes as `r_check = r_x mod n`). Either
/// imbalance proves the public `r` is bound to the proven computation;
/// `verify_balanced` reports whichever it checks first.
#[test]
fn monolithic_rejects_mutated_public_r() {
    let mut draft = valid_draft_for_balance(7, 11);
    monolithic_balance_outcome(&draft).expect("honest draft balances");
    draft.claim.public_inputs.instances[0].r =
        bump_limb0(&draft.claim.public_inputs.instances[0].r);
    let err = monolithic_balance_outcome(&draft).expect_err("mutated public r must reject");
    assert!(
        matches!(
            err,
            P256ProofError::RelationImbalance {
                relation: "EcdsaResult" | "PublicEcdsaInstance"
            }
        ),
        "expected EcdsaResult/PublicEcdsaInstance imbalance, got {err:?}"
    );
}

#[test]
#[ignore = "proves scalar setup mod-mul rows through PCS for degree/profile diagnostics"]
fn scalar_setup_mod_mul_pcs_diagnostic() {
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(0, 11),
    ])
    .expect("zero branch pipeline builds");
    let rows = scalar_setup_mod_mul_rows(&proof.claim).expect("scalar mod-mul rows generate");

    for rows in &rows {
        prove_scalar_mod_mul_rows_for_diagnostic(rows);
    }
}

#[test]
#[ignore = "proves fake-GLV scalar and selector AIR rows through PCS for degree/profile diagnostics"]
fn fake_glv_scalar_selector_pcs_diagnostic() {
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(0, 11),
    ])
    .expect("zero branch pipeline builds");

    prove_fake_glv_scalar_air_for_diagnostic(&proof);
    prove_fake_glv_selector_air_for_diagnostic(&proof);
}

#[test]
#[ignore = "checks scalar setup mod-mul AB schedule/base row order"]
fn scalar_setup_mod_mul_ab_row_order_diagnostic() {
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(0, 11),
    ])
    .expect("zero branch pipeline builds");
    let rows = scalar_setup_mod_mul_rows(&proof.claim).expect("scalar mod-mul rows generate");

    for rows in &rows {
        assert_ab_schedule_base_row_order(rows);
    }
}

#[test]
#[ignore = "checks scalar setup mod-mul AB decomposition in logical and storage order"]
fn scalar_setup_mod_mul_ab_decomposition_row_order_diagnostic() {
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(0, 11),
    ])
    .expect("zero branch pipeline builds");
    let rows = scalar_setup_mod_mul_rows(&proof.claim).expect("scalar mod-mul rows generate");

    for rows in &rows {
        assert_ab_decomposition_columns(rows);
    }
}

fn assert_ab_schedule_base_row_order(rows: &ScalarModMulTraceRows) {
    let traces = ScalarModMulFamilyTraces::from_rows(rows);
    let schedule = ScalarModMulFixedSchedule::from_rows(rows);
    let trace_evals = traces.to_circle_evaluations();
    let schedule_evals = schedule.to_circle_evaluations();

    let terms = SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS;
    let digits = SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS;
    let mut comparisons = vec![(0, 0, "active"), (1, 1, "coeff"), (2, 2, "chunk")];

    for term in 0..terms {
        comparisons.push((3 + term, 3 + 3 * term, "term_active"));
        comparisons.push((3 + terms + term, 3 + 3 * term + 1, "lhs_index"));
        comparisons.push((3 + 2 * terms + term, 3 + 3 * term + 2, "rhs_index"));
    }
    for offset in 0..digits {
        comparisons.push((
            3 + 3 * terms + offset,
            3 + 3 * terms + offset,
            "digit_active",
        ));
    }
    assert_eq!(comparisons.len(), PRODUCT_METADATA_TRACE_COLUMNS);

    for (base_col, schedule_col, name) in comparisons {
        assert_eq!(
            traces.ab_chunks.columns[base_col], schedule.ab_chunks[schedule_col].values,
            "logical AB {name} column mismatch for mul_id={} base_col={base_col} schedule_col={schedule_col}",
            rows.mul_id,
        );
        assert_eq!(
            trace_evals.ab_chunks[base_col].values.to_cpu(),
            schedule_evals.ab_chunks[schedule_col].values.to_cpu(),
            "storage-order AB {name} column mismatch for mul_id={} base_col={base_col} schedule_col={schedule_col}",
            rows.mul_id,
        );
    }
}

fn assert_ab_decomposition_columns(rows: &ScalarModMulTraceRows) {
    let traces = ScalarModMulFamilyTraces::from_rows(rows);
    assert_ab_decomposition_column_set(
        rows.mul_id,
        "logical",
        traces.ab_chunks.columns.iter().map(Vec::as_slice).collect(),
    );

    let evals = traces.to_circle_evaluations();
    let storage_columns = evals
        .ab_chunks
        .iter()
        .map(|column| column.values.to_cpu())
        .collect::<Vec<_>>();
    assert_ab_decomposition_column_set(
        rows.mul_id,
        "storage",
        storage_columns.iter().map(Vec::as_slice).collect(),
    );
}

fn assert_ab_decomposition_column_set(mul_id: u32, order: &str, columns: Vec<&[M31]>) {
    let terms = SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS;
    let limb_base = M31::from_u32_unchecked(1u32 << stwo_p256_utils::constants::LIMB_BITS);
    let digit_start = PRODUCT_METADATA_TRACE_COLUMNS + 3 * terms;
    for row in 0..columns[0].len() {
        let mut product_sum = M31::from_u32_unchecked(0);
        for term in 0..terms {
            let term_active = columns[3 + term][row];
            let product = columns[PRODUCT_METADATA_TRACE_COLUMNS + 3 * term + 2][row];
            product_sum += term_active * product;
        }
        let decomposition = product_sum
            - columns[digit_start][row]
            - limb_base * columns[digit_start + 1][row]
            - limb_base * limb_base * columns[digit_start + 2][row];
        assert_eq!(
            columns[0][row] * decomposition,
            M31::from_u32_unchecked(0),
            "AB decomposition mismatch mul_id={mul_id} order={order} row={row}",
        );
    }
}

fn prove_scalar_mod_mul_rows_for_diagnostic(rows: &ScalarModMulTraceRows) {
    eprintln!("prove scalar_mod_mul {} aggregate", rows.mul_id);
    let lookup_claims = LookupProviderClaims::scalar_mod_mul();
    let claim = ScalarModMulClaim::from_rows(rows);
    let ids = scalar_mod_mul_preprocessed_column_ids(&claim, &lookup_claims);
    let max_constraint_log_degree_bound = {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
        let components = ScalarModMulComponents::new(
            &mut allocator,
            &claim,
            &zero_interaction_claim(),
            &lookup_claims,
            &ScalarModMulLookupRelations::dummy(),
        );
        scalar_mod_mul_max_constraint_log_degree_bound(&components)
    };
    let config = p256_stark_slice_low_ram_config(max_constraint_log_degree_bound);
    eprintln!(
        "scalar_mod_mul {} pcs max_bound={} blowup={} lifting={:?}",
        rows.mul_id,
        max_constraint_log_degree_bound,
        config.fri_config.log_blowup_factor,
        config.lifting_log_size
    );
    let twiddles =
        SimdBackend::precompute_twiddles(
            CanonicCoset::new(config.lifting_log_size.unwrap_or(
                max_constraint_log_degree_bound + config.fri_config.log_blowup_factor,
            ))
            .circle_domain()
            .half_coset,
        );
    let mut channel = <Blake2sMerkleChannel as MerkleChannel>::C::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);
    let preprocessed = gen_scalar_mod_mul_preprocessed_trace(rows, &lookup_claims, &ids);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(preprocessed);
    tree_builder.commit(&mut channel);

    claim.mix_into(&mut channel);
    let base = gen_scalar_mod_mul_base_trace(rows, &lookup_claims);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(base);
    tree_builder.commit(&mut channel);

    let relations = ScalarModMulLookupRelations::draw(&mut channel);
    let claim = ScalarModMulClaim::from_rows(rows);
    let (interaction, interaction_claim) =
        gen_scalar_mod_mul_interaction_trace(rows, &claim, &lookup_claims, &relations);
    interaction_claim.scalar_mod_mul.mix_into(&mut channel);
    interaction_claim.range13.mix_into(&mut channel);
    interaction_claim.signed_carry.mix_into(&mut channel);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction);
    tree_builder.commit(&mut channel);

    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let components = ScalarModMulComponents::new(
        &mut allocator,
        &claim,
        &interaction_claim,
        &lookup_claims,
        &relations,
    );
    let component_provers = scalar_mod_mul_component_provers(&components);
    prove(&component_provers, &mut channel, commitment_scheme)
        .expect("scalar mod-mul PCS proof proves");
}

fn prove_fake_glv_scalar_air_for_diagnostic(proof: &P256ProofDraft) {
    eprintln!("prove fake_glv_scalar_air aggregate");
    let claim = FakeGlvScalarAirProofClaim::from_claim(&proof.claim.fake_glv_scalars);
    let max_constraint_log_degree_bound = {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&[]);
        let components = FakeGlvScalarAirComponents::new(
            &mut allocator,
            claim,
            &FakeGlvScalarAirInteractionClaim::zero(),
            &CertScalarInputRelation::dummy(),
            &FakeGlvScalarRelation::dummy(),
            &crate::scalar::scalar_mod_mul::relation::ScalarLimbRelation::dummy(),
        );
        components.max_constraint_log_degree_bound()
    };
    let config = p256_stark_slice_low_ram_config(max_constraint_log_degree_bound);
    eprintln!(
        "fake_glv_scalar_air pcs max_bound={} blowup={} lifting={:?}",
        max_constraint_log_degree_bound, config.fri_config.log_blowup_factor, config.lifting_log_size
    );
    let twiddles =
        SimdBackend::precompute_twiddles(
            CanonicCoset::new(config.lifting_log_size.unwrap_or(
                max_constraint_log_degree_bound + config.fri_config.log_blowup_factor,
            ))
            .circle_domain()
            .half_coset,
        );
    let mut channel = <Blake2sMerkleChannel as MerkleChannel>::C::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);
    commitment_scheme.set_store_polynomials_coefficients();

    let tree_builder = commitment_scheme.tree_builder();
    tree_builder.commit(&mut channel);

    claim.mix_into(&mut channel);
    let base = gen_fake_glv_scalar_air_base_trace(
        &proof.claim.cert_inputs,
        &proof.claim.fake_glv_scalars,
        claim,
    );
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(base.clone());
    tree_builder.commit(&mut channel);

    let cert_relation = CertScalarInputRelation::draw(&mut channel);
    let scalar_relation = FakeGlvScalarRelation::draw(&mut channel);
    let scalar_limb_relation =
        crate::scalar::scalar_mod_mul::relation::ScalarLimbRelation::dummy();
    let (interaction, interaction_claim) = gen_fake_glv_scalar_air_interaction_trace(
        &base,
        &cert_relation,
        &scalar_relation,
        &scalar_limb_relation,
    );
    interaction_claim.mix_into(&mut channel);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction);
    tree_builder.commit(&mut channel);

    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&[]);
    let components = FakeGlvScalarAirComponents::new(
        &mut allocator,
        claim,
        &interaction_claim,
        &cert_relation,
        &scalar_relation,
        &scalar_limb_relation,
    );
    prove(
        &components.component_provers(),
        &mut channel,
        commitment_scheme,
    )
    .expect("fake-GLV scalar AIR PCS proof proves");
}

fn prove_fake_glv_selector_air_for_diagnostic(proof: &P256ProofDraft) {
    eprintln!("prove fake_glv_selector_air aggregate");
    let claim = FakeGlvSelectorAirProofClaim::from_claim(&proof.claim.fake_glv_selectors);
    let max_constraint_log_degree_bound = {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&[]);
        let components = FakeGlvSelectorAirComponents::new(
            &mut allocator,
            claim,
            &FakeGlvSelectorAirInteractionClaim::zero(),
            &FakeGlvScalarRelation::dummy(),
        );
        components.max_constraint_log_degree_bound()
    };
    let config = p256_stark_slice_low_ram_config(max_constraint_log_degree_bound);
    eprintln!(
        "fake_glv_selector_air pcs max_bound={} blowup={} lifting={:?}",
        max_constraint_log_degree_bound,
        config.fri_config.log_blowup_factor,
        config.lifting_log_size
    );
    let twiddles =
        SimdBackend::precompute_twiddles(
            CanonicCoset::new(config.lifting_log_size.unwrap_or(
                max_constraint_log_degree_bound + config.fri_config.log_blowup_factor,
            ))
            .circle_domain()
            .half_coset,
        );
    let mut channel = <Blake2sMerkleChannel as MerkleChannel>::C::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);
    commitment_scheme.set_store_polynomials_coefficients();

    let tree_builder = commitment_scheme.tree_builder();
    tree_builder.commit(&mut channel);

    claim.mix_into(&mut channel);
    let base = gen_fake_glv_selector_air_base_trace(
        &proof.claim.fake_glv_scalars,
        &proof.claim.fake_glv_selectors,
        claim,
    );
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(base.clone());
    tree_builder.commit(&mut channel);

    let scalar_relation = FakeGlvScalarRelation::draw(&mut channel);
    let (interaction, interaction_claim) =
        gen_fake_glv_selector_air_interaction_trace(&base, &scalar_relation);
    interaction_claim.mix_into(&mut channel);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction);
    tree_builder.commit(&mut channel);

    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&[]);
    let components = FakeGlvSelectorAirComponents::new(
        &mut allocator,
        claim,
        &interaction_claim,
        &scalar_relation,
    );
    prove(
        &components.component_provers(),
        &mut channel,
        commitment_scheme,
    )
    .expect("fake-GLV selector AIR PCS proof proves");
}

fn scalar_mod_mul_max_constraint_log_degree_bound(components: &ScalarModMulComponents) -> u32 {
    [
        components.canonical.max_constraint_log_degree_bound(),
        components.ab_chunks.max_constraint_log_degree_bound(),
        components.qn_chunks.max_constraint_log_degree_bound(),
        components.accumulators.max_constraint_log_degree_bound(),
        components
            .reduction_digits
            .max_constraint_log_degree_bound(),
        components.range13.max_constraint_log_degree_bound(),
        components.signed_carry.max_constraint_log_degree_bound(),
    ]
    .into_iter()
    .max()
    .unwrap_or(0)
}

fn scalar_mod_mul_component_provers(
    components: &ScalarModMulComponents,
) -> Vec<&dyn ComponentProver<SimdBackend>> {
    vec![
        &components.canonical as &dyn ComponentProver<SimdBackend>,
        &components.ab_chunks as &dyn ComponentProver<SimdBackend>,
        &components.qn_chunks as &dyn ComponentProver<SimdBackend>,
        &components.accumulators as &dyn ComponentProver<SimdBackend>,
        &components.reduction_digits as &dyn ComponentProver<SimdBackend>,
        &components.range13 as &dyn ComponentProver<SimdBackend>,
        &components.signed_carry as &dyn ComponentProver<SimdBackend>,
    ]
}

fn assert_current_air_constraints(proof: &P256ProofDraft) {
    let claim = P256CurrentAirProofClaim::from_claim(&proof.claim);
    let ids = claim.preprocessed_column_ids();
    let preprocessed = proof
        .gen_current_air_preprocessed_trace(&claim, &ids)
        .expect("current AIR preprocessed trace generates");
    let base = proof
        .gen_current_air_base_trace(&claim)
        .expect("current AIR base trace generates");
    let mut dummy_channel = Blake2sM31Channel::default();
    let relations = P256CurrentAirRelations::draw(&mut dummy_channel);
    let (interaction, interaction_claim) = proof
        .gen_current_air_interaction_trace(&base, &relations)
        .expect("current AIR interaction trace generates");

    let mut commitment_scheme = MockCommitmentScheme::default();
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(preprocessed);
    tree_builder.finalize_interaction();

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(base.columns);
    tree_builder.finalize_interaction();

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction);
    tree_builder.finalize_interaction();

    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let components =
        P256CurrentAirComponents::new(&mut allocator, &claim, &interaction_claim, &relations);
    let trace = commitment_scheme.trace_domain_evaluations();

    assert_component_named("scalar_setup.setup", &components.scalar_setup.setup, &trace);
    assert_component_named(
        "scalar_setup.range13",
        &components.scalar_setup.range13,
        &trace,
    );
    assert_component_named(
        "scalar_setup.range9",
        &components.scalar_setup.range9,
        &trace,
    );
    assert_component_named(
        "scalar_setup.signed_carry",
        &components.scalar_setup.signed_carry,
        &trace,
    );
    assert_component_named(
        "cert_scalar_inputs",
        &components.cert_scalar_inputs.certs,
        &trace,
    );
    assert_component_named(
        "fake_glv_scalar_air",
        &components.fake_glv_scalar_air.scalar,
        &trace,
    );
    assert_component_named(
        "fake_glv_selector_air",
        &components.fake_glv_selector_air.selector,
        &trace,
    );
    for (index, scalar_mod_mul) in components.scalar_setup_mod_muls.iter().enumerate() {
        assert_scalar_mod_mul_components_named(index, scalar_mod_mul, &trace);
    }
    assert_component_named(
        "prepared_table_projective_source.provider",
        &components.prepared_table_projective_source.provider,
        &trace,
    );
    assert_component_named(
        "prepared_table_projective_source.consumer",
        &components.prepared_table_projective_source.consumer,
        &trace,
    );
    assert_component_named(
        "fake_glv_projective_source.provider",
        &components.fake_glv_projective_source.provider,
        &trace,
    );
    assert_component_named(
        "fake_glv_projective_source.consumer",
        &components.fake_glv_projective_source.consumer,
        &trace,
    );
    assert_component_named(
        "fake_glv_chain_expansion.expansion",
        &components.fake_glv_chain_expansion.expansion,
        &trace,
    );
    assert_component_named(
        "fake_glv_chain_expansion.primitive",
        &components.fake_glv_chain_expansion.primitive,
        &trace,
    );
    assert_component_named(
        "fake_glv_chain_continuity",
        &components.fake_glv_chain_continuity,
        &trace,
    );
    assert_component_named(
        "fake_glv_chain_schedule",
        &components.fake_glv_chain_schedule,
        &trace,
    );
    assert_component_named(
        "fake_glv_direct_prepared_operand.provider",
        &components.fake_glv_direct_prepared_operand.provider,
        &trace,
    );
    assert_component_named(
        "fake_glv_direct_prepared_operand.consumer",
        &components.fake_glv_direct_prepared_operand.consumer,
        &trace,
    );
    assert_component_named(
        "fake_glv_signed_selector_operand.provider",
        &components.fake_glv_signed_selector_operand.provider,
        &trace,
    );
    assert_component_named(
        "fake_glv_signed_selector_operand.consumer",
        &components.fake_glv_signed_selector_operand.consumer,
        &trace,
    );
    assert_component_named(
        "fake_glv_lsb_correction_operand.provider",
        &components.fake_glv_lsb_correction_operand.provider,
        &trace,
    );
    assert_component_named(
        "fake_glv_lsb_correction_operand.consumer",
        &components.fake_glv_lsb_correction_operand.consumer,
        &trace,
    );
    assert_component_named(
        "fake_glv_prepared_point_source.provider",
        &components.fake_glv_prepared_point_source.provider,
        &trace,
    );
    assert_component_named(
        "fake_glv_prepared_point_source.consumer",
        &components.fake_glv_prepared_point_source.consumer,
        &trace,
    );
    assert_component_named(
        "prepared_point_range7",
        &components.prepared_point_range7,
        &trace,
    );
    assert_component_named(
        "fake_glv_final_check",
        &components.final_check.check,
        &trace,
    );
    assert_component_named("hinted_mul.check", &components.hinted_mul.check, &trace);
    assert_component_named("hinted_mul.range13", &components.hinted_mul.range13, &trace);
    assert_component_named("hinted_mul.signed_h", &components.hinted_mul.signed_h, &trace);
}

fn assert_scalar_mod_mul_components_named(
    index: usize,
    components: &ScalarModMulComponents,
    trace: &TreeVec<Vec<&Vec<M31>>>,
) {
    assert_component_named(
        &format!("scalar_setup_mod_mul_{index}.canonical"),
        &components.canonical,
        trace,
    );
    assert_component_named(
        &format!("scalar_setup_mod_mul_{index}.ab_chunks"),
        &components.ab_chunks,
        trace,
    );
    assert_component_named(
        &format!("scalar_setup_mod_mul_{index}.qn_chunks"),
        &components.qn_chunks,
        trace,
    );
    assert_component_named(
        &format!("scalar_setup_mod_mul_{index}.accumulators"),
        &components.accumulators,
        trace,
    );
    assert_component_named(
        &format!("scalar_setup_mod_mul_{index}.reduction_digits"),
        &components.reduction_digits,
        trace,
    );
    assert_component_named(
        &format!("scalar_setup_mod_mul_{index}.range13"),
        &components.range13,
        trace,
    );
    assert_component_named(
        &format!("scalar_setup_mod_mul_{index}.signed_carry"),
        &components.signed_carry,
        trace,
    );
}

fn assert_component_named<E: FrameworkEval + Sync>(
    name: &str,
    component: &FrameworkComponent<E>,
    trace: &TreeVec<Vec<&Vec<M31>>>,
) {
    eprintln!("assert {name}");
    let mut component_trace = trace
        .sub_tree(component.trace_locations())
        .map(|tree| tree.into_iter().cloned().collect::<Vec<_>>());
    component_trace[PREPROCESSED_TRACE_IDX] = component
        .preprocessed_column_indices()
        .iter()
        .map(|index| trace[PREPROCESSED_TRACE_IDX][*index])
        .collect();

    let component_eval = component.deref();
    assert_constraints_on_trace(
        &component_trace,
        component.log_size(),
        |eval| {
            let _ = component_eval.evaluate(eval);
        },
        component.claimed_sum(),
    );
}

#[test]
#[ignore = "diagnostic: prints the serialized proof-size estimate and its breakdown"]
fn current_p256_proof_size_diagnostic() {
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(7, 11),
    ])
    .expect("pipeline builds")
    .prove_current_air_monolithic::<Blake2sMerkleChannel>()
    .expect("proof generates");
    let stark = &proof.stark_proof;
    let breakdown = stark.size_breakdown_estimate();
    eprintln!("PROOF SIZE estimate: {} bytes", stark.size_estimate());
    eprintln!("  oods_samples:        {}", breakdown.oods_samples);
    eprintln!("  queries_values:      {}", breakdown.queries_values);
    eprintln!("  fri_samples:         {}", breakdown.fri_samples);
    eprintln!("  fri_decommitments:   {}", breakdown.fri_decommitments);
    eprintln!("  trace_decommitments: {}", breakdown.trace_decommitments);
}

#[test]
#[ignore = "prints current AIR row/column shape for performance diagnostics"]
fn current_p256_air_shape_diagnostic() {
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(0, 11),
    ])
    .expect("zero branch pipeline builds");
    proof.verify_current_e2e().expect("zero branch verifies");

    let claim = P256CurrentAirProofClaim::from_claim(&proof.claim);
    let ids = claim.preprocessed_column_ids();
    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let components = P256CurrentAirComponents::new(
        &mut allocator,
        &claim,
        &P256CurrentAirInteractionClaim::zero(),
        &P256CurrentAirRelations::dummy(),
    );

    eprintln!("current-air unique_preprocessed_columns={}", ids.len());
    eprintln!(
        "current-air max_constraint_log_degree_bound={}",
        claim.max_constraint_log_degree_bound(&ids)
    );
    eprintln!(
        "native rows: prepared_ec={} fake_glv_chain={} fake_glv_primitive_ec={} projective_ec={} projective_rcb_active={} projective_mul={}",
        proof.claim.prepared_table_ec_trace.active_row_count(),
        proof.claim.fake_glv_chain.active_row_count(),
        proof.claim.fake_glv_ec_trace.active_row_count(),
        proof.claim.projective_ec_trace.active_row_count(),
        proof.claim.projective_rcb_air_trace.active_row_count(),
        proof.claim.projective_rcb_air_trace.mul_row_count(),
    );
    eprintln!(
        "projective row families: raw_chunks={} folded_contributions={} folded_digits={} reductions={}",
        proof.claim.projective_rcb_air_trace.raw_product_chunk_count(),
        proof.claim.projective_rcb_air_trace.folded_contribution_row_count(),
        proof.claim.projective_rcb_air_trace.folded_digit_row_count(),
        proof.claim.projective_rcb_air_trace.reduction_row_count(),
    );

    for (index, scalar_mod_mul) in components.scalar_setup_mod_muls.iter().enumerate() {
        print_component_shape(
            &format!("scalar_setup_mod_mul_{index}"),
            scalar_mod_mul_component_bounds(scalar_mod_mul),
        );
    }
    print_component_shape(
        "prepared_table_projective_source",
        components
            .prepared_table_projective_source
            .trace_log_degree_bounds(),
    );
    print_component_shape(
        "fake_glv_projective_source",
        components
            .fake_glv_projective_source
            .trace_log_degree_bounds(),
    );
    print_component_shape(
        "fake_glv_chain_expansion",
        components
            .fake_glv_chain_expansion
            .trace_log_degree_bounds(),
    );
    print_component_shape(
        "fake_glv_chain_continuity",
        components
            .fake_glv_chain_continuity
            .trace_log_degree_bounds(),
    );
    print_component_shape(
        "fake_glv_chain_schedule",
        components.fake_glv_chain_schedule.trace_log_degree_bounds(),
    );
    print_component_shape(
        "fake_glv_direct_prepared_operand",
        components
            .fake_glv_direct_prepared_operand
            .trace_log_degree_bounds(),
    );
    print_component_shape(
        "fake_glv_signed_selector_operand",
        components
            .fake_glv_signed_selector_operand
            .trace_log_degree_bounds(),
    );
    print_component_shape(
        "fake_glv_lsb_correction_operand",
        components
            .fake_glv_lsb_correction_operand
            .trace_log_degree_bounds(),
    );
    print_component_shape(
        "fake_glv_prepared_point_source",
        components
            .fake_glv_prepared_point_source
            .trace_log_degree_bounds(),
    );
    print_component_shape(
        "hinted_mul.check",
        stwo::core::air::Component::trace_log_degree_bounds(&components.hinted_mul.check),
    );
    print_component_shape(
        "hinted_mul.range13",
        stwo::core::air::Component::trace_log_degree_bounds(&components.hinted_mul.range13),
    );
    print_component_shape(
        "hinted_mul.signed_h",
        stwo::core::air::Component::trace_log_degree_bounds(&components.hinted_mul.signed_h),
    );
    print_component_shape("current_air_total", components.trace_log_degree_bounds());
}

fn print_component_shape(name: &str, bounds: TreeVec<ColumnVec<u32>>) {
    let labels = ["preprocessed", "base", "interaction"];
    for (tree, columns) in bounds.0.iter().enumerate() {
        let mut by_log_size = BTreeMap::new();
        for log_size in columns {
            *by_log_size.entry(*log_size).or_insert(0usize) += 1;
        }
        eprintln!(
            "shape {name} {} columns={} by_log_size={:?}",
            labels.get(tree).copied().unwrap_or("extra"),
            columns.len(),
            by_log_size
        );
    }
}

fn scalar_mod_mul_component_bounds(
    components: &ScalarModMulComponents,
) -> TreeVec<ColumnVec<u32>> {
    TreeVec::concat_cols(
        [
            components.canonical.trace_log_degree_bounds(),
            components.ab_chunks.trace_log_degree_bounds(),
            components.qn_chunks.trace_log_degree_bounds(),
            components.accumulators.trace_log_degree_bounds(),
            components.reduction_digits.trace_log_degree_bounds(),
            components.range13.trace_log_degree_bounds(),
            components.signed_carry.trace_log_degree_bounds(),
        ]
        .into_iter(),
    )
}

#[test]
fn current_p256_proof_pipeline_reports_pending_full_proof_slots() {
    let pending = P256_PROOF_COMPONENT_SLOTS
        .iter()
        .filter(|slot| slot.status == P256ProofComponentStatus::Pending)
        .map(|slot| slot.name)
        .collect::<Vec<_>>();
    let implemented = P256_PROOF_COMPONENT_SLOTS
        .iter()
        .filter(|slot| slot.status == P256ProofComponentStatus::Implemented)
        .map(|slot| slot.name)
        .collect::<Vec<_>>();

    assert!(implemented.contains(&"PublicEcdsaInput"));
    assert!(implemented.contains(&"PublicKeyOnCurve"));
    assert!(implemented.contains(&"SolinasReductionTraceRows"));
    assert!(!pending.contains(&"PublicKeyOnCurve"));
    assert!(!pending.contains(&"SolinasReductionTraceRows"));
    assert!(implemented.contains(&"ScalarSetup"));
    assert!(implemented.contains(&"CertScalarInput"));
    assert!(implemented.contains(&"FakeGlvSelector"));
    assert!(implemented.contains(&"PreparedPointUseCounts"));
    assert!(implemented.contains(&"PreparedTablePoints"));
    assert!(!pending.contains(&"PreparedTablePoints"));
    assert!(implemented.contains(&"PreparedTableEcTrace"));
    assert!(implemented.contains(&"PreparedTableEcRows"));
    assert!(implemented.contains(&"FakeGlvChainTrace"));
    assert!(implemented.contains(&"FakeGlvPrimitiveEcTrace"));
    assert!(implemented.contains(&"FakeGlvEcChainRows"));
    assert!(implemented.contains(&"ProjectiveRcbEcTrace"));
    assert!(implemented.contains(&"ProjectiveRcbAirRows"));
    // FinalEcdsaCheck is now AIR-proven: `r_x` is bound in-AIR to
    // x(u1·G + u2·Q) via the FinalCheckHint forward + final-add sub-graph.
    assert!(implemented.contains(&"FinalEcdsaCheck"));
    assert!(!pending.contains(&"FinalEcdsaCheck"));
    assert!(implemented.contains(&"StarkProveVerify"));
    assert!(!pending.contains(&"PreparedTableEcRows"));
    assert!(!pending.contains(&"FakeGlvScalarHint"));
    assert!(!pending.contains(&"FakeGlvEcChainRows"));
}

/// Close-out gate: every full-proof component slot is now AIR-proven (no slot is
/// `Pending`). Enabled once the real-signature e2e
/// (`current_p256_monolithic_proves_real_p256_crate_signature`) proves green via
/// the production arbitrary-fake-GLV path.
#[test]
fn full_p256_signature_proof_has_no_pending_component_slots() {
    let pending = P256_PROOF_COMPONENT_SLOTS
        .iter()
        .filter(|slot| slot.status == P256ProofComponentStatus::Pending)
        .map(|slot| slot.name)
        .collect::<Vec<_>>();

    assert!(
        pending.is_empty(),
        "full P-256 signature proof still has pending AIR slots: {pending:?}"
    );
}

#[test]
fn current_p256_proof_pipeline_detects_public_relation_imbalance() {
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(7, 11),
    ])
    .expect("current pipeline builds");
    let mut interaction_claim = proof.interaction_claim();
    interaction_claim.public_inputs.consumer_claimed_sum = zero();

    let err = interaction_claim
        .verify_balanced()
        .expect_err("mutated public consumer sum must fail");

    assert_eq!(
        err,
        P256ProofError::RelationImbalance {
            relation: "PublicEcdsaInstance",
        }
    );
}

#[test]
fn current_p256_proof_pipeline_detects_selector_lookup_imbalance() {
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(7, 11),
    ])
    .expect("current pipeline builds");
    let mut interaction_claim = proof.interaction_claim();
    interaction_claim
        .selector_lookups
        .consumer_claimed_sum = zero();

    let err = interaction_claim
        .verify_balanced()
        .expect_err("mutated selector consumer sum must fail");

    assert_eq!(
        err,
        P256ProofError::RelationImbalance {
            relation: "SelectorLookups",
        }
    );
}

#[test]
fn current_p256_proof_pipeline_detects_prepared_point_imbalance() {
    let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
        valid_real_input_with_small_u_scalars(7, 11),
    ])
    .expect("current pipeline builds");
    let mut interaction_claim = proof.interaction_claim();
    interaction_claim.prepared_points.consumer_claimed_sum = zero();

    let err = interaction_claim
        .verify_balanced()
        .expect_err("mutated prepared consumer sum must fail");

    assert_eq!(
        err,
        P256ProofError::RelationImbalance {
            relation: "PreparedPoint",
        }
    );
}
