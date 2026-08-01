//! Standalone proof and verification tests for `mldsa_coeffs`.
//!
//! The tests use oracle-generated ML-DSA-65 signatures and verify that each
//! adversarial mutation is rejected.

mod common;

use common::witness_and_input;

use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::PcsConfig;

use stwo_mldsa::coeffs::layout::N_GROUPS;
use stwo_mldsa::profile::ML_DSA_65;
use stwo_mldsa::proof::{prove_coeffs, verify_coeffs, CoeffsProof};
use stwo_mldsa::MlDsaVerifyInput;

fn prove_case(seed: u64, msg: &[u8]) -> CoeffsProof {
    let (witness, input) = witness_and_input(seed, msg);
    prove_coeffs(witness, input, PcsConfig::default()).expect("prove")
}

/// A witness mutation is REJECTED if proving fails, panics (e.g. an out-of-range
/// digit overflowing a table index), or the resulting proof fails to verify.
fn rejected(witness: stwo_mldsa::witness::MlDsaWitness, input: MlDsaVerifyInput) -> bool {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        match prove_coeffs(witness, input, PcsConfig::default()) {
            Ok(proof) => verify_coeffs(&proof, PcsConfig::default()).is_err(),
            Err(_) => true, // prover rejected (ConstraintsNotSatisfied / imbalance)
        }
    }));
    // A panic inside the prover (bad table index, i128 assert) is also a rejection.
    result.unwrap_or(true)
}

// =====================================================================
// Positive: prove+verify over ≥20 oracle signatures.
// =====================================================================

#[test]
fn coeffs_proves_and_verifies_over_20_signatures() {
    let mut ok = 0;
    for i in 0..20u64 {
        let msg = format!("mldsa-coeffs-case-{i}").into_bytes();
        let proof = prove_case(1000 + i, &msg);
        verify_coeffs(&proof, PcsConfig::default())
            .unwrap_or_else(|e| panic!("case {i}: verify failed: {e:?}"));
        assert_eq!(proof.group_evals.len(), N_GROUPS);
        ok += 1;
    }
    assert_eq!(ok, 20);
}

#[test]
fn coeffs_rejects_proof_under_different_pcs_policy() {
    let proof = prove_case(1999, b"pcs-policy");
    let mut wrong = PcsConfig::default();
    wrong.pow_bits += 1;
    assert!(
        verify_coeffs(&proof, wrong).is_err(),
        "a proof must not select its own PCS policy"
    );
}

// =====================================================================
// Negatives — each must be rejected by verify_coeffs.
// =====================================================================

// --- Proof-level negatives (mutate the emitted proof) ---

/// Change a claimed EvalAtRs sum. This makes the native fold nonzero and
/// breaks the EvalAtRs balance.
#[test]
fn negative_tampered_claimed_eval() {
    let mut proof = prove_case(2001, b"tamper-eval");
    proof.group_evals[17] += SecureField::from(stwo::core::fields::m31::M31::from_u32_unchecked(1));
    assert!(
        verify_coeffs(&proof, PcsConfig::default()).is_err(),
        "a changed claimed evaluation must be rejected"
    );
}

/// Verify against a different public key so `ExpandA(ρ′) ≠ ExpandA(ρ)`.
#[test]
fn negative_wrong_pk_rho() {
    let mut proof = prove_case(2002, b"wrong-rho");
    proof.input.rho[0] ^= 1;
    assert!(
        verify_coeffs(&proof, PcsConfig::default()).is_err(),
        "an incorrect ρ must be rejected"
    );
}

/// Corrupt a coeffs claimed sum → logup balance no longer cancels.
#[test]
fn negative_tampered_claimed_sum() {
    let mut proof = prove_case(2003, b"tamper-sum");
    proof.coeffs_claimed_sum +=
        SecureField::from(stwo::core::fields::m31::M31::from_u32_unchecked(1));
    assert!(
        verify_coeffs(&proof, PcsConfig::default()).is_err(),
        "a changed claimed sum must be rejected"
    );
}

// --- Witness-level negatives (mutate the witness before proving) ---

/// Change one v digit so the bivariate identity fails at `(r,s)`.
#[test]
fn negative_perturb_v_digit() {
    let (mut w, input) = witness_and_input(3001, b"v-digit");
    w.digits.v[2][100][3] += 1; // v_2, coeff 100, digit t=3
    assert!(rejected(w, input), "perturbed v digit must be rejected");
}

/// Swap the z_0 and z_1 digit tables. The group Horner evaluations then use
/// the wrong polynomial identifier, and the native fold balance fails.
#[test]
fn negative_swap_two_polys() {
    let (mut w, input) = witness_and_input(3002, b"swap-polys");
    w.digits.z.swap(0, 1);
    assert!(rejected(w, input), "swapping two polys must be rejected");
}

/// Swap two digits with different weights in one row. This changes
/// `Σ d_t·B^t` and breaks the recomposition binding.
#[test]
fn negative_swap_digits_across_t() {
    let (mut w, input) = witness_and_input(3003, b"swap-digits");
    let row = &mut w.digits.z[0][50];
    row.swap(0, 2); // swap digit t=0 and t=2 (distinct weights B^0 vs B^2)
    assert!(
        rejected(w, input),
        "swapping digits across t must be rejected"
    );
}

/// Set a digit to +257, outside the balanced `[−256,256)` range. The rc9 table
/// has no matching row.
#[test]
fn negative_out_of_range_digit() {
    let (mut w, input) = witness_and_input(3004, b"oor-digit");
    w.digits.w[1][30][0] = 257; // outside [−256, 256)
    assert!(rejected(w, input), "out-of-range digit must be rejected");
}

/// Change a carry cell so the `(s−B)·Ĉ` term makes the fold nonzero.
#[test]
fn negative_tampered_carry() {
    let (mut w, input) = witness_and_input(3005, b"carry");
    w.rows[0].carry[10][2] += 1;
    assert!(rejected(w, input), "tampered carry must be rejected");
}

/// Change a z digit without changing the coefficient that the norm consumes.
/// The constraint `cell = Σ d_t·B^t` binds them, so the change is rejected.
#[test]
fn negative_recomp_binding_mismatch() {
    let (mut w, input) = witness_and_input(3006, b"recomp");
    // Bump the top z digit by 1 (changes Σ d_t·B^t but the norm/aux still target
    // the recomposed cell) — the value committed by the AIR diverges.
    w.digits.z[3][77][2] += 1;
    assert!(
        rejected(w, input),
        "recomposition mismatch must be rejected"
    );
}

/// A packed row's second z coefficient must participate in the same Horner
/// evaluation as its first coefficient. Coefficient 76 is the second slot of
/// the physical row `(77, 76)`; a live in-range mutation must not disappear.
#[test]
fn negative_packed_second_z_coefficient_is_bound() {
    let (mut w, input) = witness_and_input(3007, b"packed-z-second");
    let digit = &mut w.digits.z[2][76][1];
    *digit += if *digit < 255 { 1 } else { -1 };
    assert!(
        rejected(w, input),
        "packed second z coefficient must be bound into the group evaluation"
    );
}

/// The second packed w coefficient keeps its assigned `w_bind_id = i·N+m` and
/// recomposed value. The standalone WCell balancer consumes the unmodified
/// coefficient, so changing only its second-slot digits must reject.
#[test]
fn negative_packed_second_wcell_is_bound() {
    let (mut w, input) = witness_and_input(3008, b"packed-w-second");
    let digit = &mut w.digits.w[1][30][0];
    *digit += if *digit < 255 { 1 } else { -1 };
    assert!(
        rejected(w, input),
        "packed second w coefficient must retain its WCell key/value binding"
    );
}

/// The exact z-norm gate accepts `|z| ≤ γ1−β−1 = 524_091` and rejects
/// `|z| = γ1−β = 524_092`. The AIR C5 predicate is
/// `a = z + bound ∈ [0,2^20)` and `b = bound − z ∈ [0,2^20)`,
/// both pinned by rc13+rc7. A full proof also checks the SZ identity, so this
/// test isolates the norm gate at the same arithmetic level as the AIR.
#[test]
fn z_norm_gate_is_exact() {
    let bound = stwo_mldsa::coeffs::z_norm_bound(ML_DSA_65) as i128; // 524_091
    let in_range = |v: i128| (0..(1i128 << 20)).contains(&v);
    let accepts = |z: i128| in_range(z + bound) && in_range(bound - z);

    assert!(accepts(0));
    assert!(accepts(bound), "z = γ1−β−1 (524_091) must PASS");
    assert!(accepts(-bound), "z = −(γ1−β−1) must PASS");
    assert!(!accepts(bound + 1), "z = γ1−β (524_092) must REJECT");
    assert!(!accepts(-(bound + 1)), "z = −(γ1−β) must REJECT");
    // A naive single 2^20 window (`z + 2^19 ∈ [0,2^20)`) over-accepts up to
    // 2^19−1 = 524_287 (196 past the bound); the exact two-sided gate does not.
    let naive_window = |z: i128| in_range(z + (1i128 << 19));
    assert!(
        naive_window(bound + 100),
        "naive window over-accepts z = bound+100..."
    );
    assert!(
        !accepts(bound + 100),
        "...but the exact two-sided gate rejects it"
    );
}

#[test]
fn paired_zw_shape_is_log13_and_batch4_legal() {
    use stwo_mldsa::coeffs::{
        coeffs_preprocessed_ids, layout, LOGUP_BATCH, N_BASE_COLS, N_INTERACTION_COLS,
        N_LOGUP_COLS, N_LOGUP_ENTRIES, N_RANGE_STREAMS,
    };

    let active = layout::active_rows();
    let log_size = stwo_mldsa::air_util::padded_log_size(active);
    let rows = 1usize << log_size;

    assert_eq!(active, 7796);
    assert_eq!(log_size, 13);
    assert_eq!(rows, 8192);
    assert_eq!(
        N_BASE_COLS, 16,
        "z/w reuse six digit columns; two dedicated norm highs prevent carry-stream aliasing"
    );
    assert_eq!(coeffs_preprocessed_ids(ML_DSA_65).len(), 12);
    assert_eq!(N_RANGE_STREAMS, 14);
    assert_eq!(N_LOGUP_ENTRIES, 18);
    assert_eq!(LOGUP_BATCH, 4);
    assert_eq!(N_LOGUP_COLS, N_LOGUP_ENTRIES.div_ceil(LOGUP_BATCH));
    assert_eq!(N_LOGUP_COLS, 5);
    assert_eq!(N_INTERACTION_COLS, 24);
    assert_eq!(
        (coeffs_preprocessed_ids(ML_DSA_65).len() + N_BASE_COLS + N_INTERACTION_COLS) * rows,
        425_984
    );
}

/// Each mutation fixture proves and verifies before the mutation.
#[test]
fn mutation_fixtures_verify_without_mutation() {
    for (seed, msg) in [
        (3001u64, &b"v-digit"[..]),
        (3002, b"swap-polys"),
        (3005, b"carry"),
        (3006, b"recomp"),
        (3007, b"packed-z-second"),
        (3008, b"packed-w-second"),
    ] {
        let (w, input) = witness_and_input(seed, msg);
        let proof = prove_coeffs(w, input, PcsConfig::default())
            .unwrap_or_else(|e| panic!("seed {seed}: honest prove failed: {e:?}"));
        verify_coeffs(&proof, PcsConfig::default())
            .unwrap_or_else(|e| panic!("seed {seed}: honest verify failed: {e:?}"));
    }
}
