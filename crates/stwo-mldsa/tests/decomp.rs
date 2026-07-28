//! M5 acceptance for `mldsa_decomp` ([DECOMP]+[HINT]): standalone prove+verify
//! over ≥20 oracle ML-DSA-65 signatures, plus the S5 §5 negative matrix. The
//! w-cell binding and w1Encode byte emission are balanced test-side (a wcell
//! provider + a hashio consumer) since coeffs/the sponge are not in this
//! composition; M6 replaces the balancers with the real components.

mod common;

use common::{standalone_pcs_config as pcs_config, witness_and_input};

use stwo_mldsa::decomp::proof::{prove_decomp, verify_decomp};
use stwo_mldsa::witness::MlDsaWitness;

/// Legacy witness-mutation oracle: proving failure, panic, or verification
/// failure all count as rejection. Trace-level soundness tests must not use it.
fn rejected_or_panicked(witness: MlDsaWitness) -> bool {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        match prove_decomp(witness, pcs_config()) {
            Ok(proof) => verify_decomp(&proof, pcs_config()).is_err(),
            Err(_) => true,
        }
    }));
    r.unwrap_or(true)
}

// =====================================================================
// Positive.
// =====================================================================

#[test]
fn decomp_proves_and_verifies_over_20_signatures() {
    let mut ok = 0;
    for i in 0..20u64 {
        let msg = format!("mldsa-decomp-case-{i}").into_bytes();
        let (w, _) = witness_and_input(5000 + i, &msg);
        let proof = prove_decomp(w, pcs_config()).expect("prove");
        verify_decomp(&proof, pcs_config())
            .unwrap_or_else(|e| panic!("case {i}: verify failed: {e:?}"));
        ok += 1;
    }
    assert_eq!(ok, 20);
}

#[test]
fn decomp_rejects_proof_under_different_pcs_policy() {
    let (w, _) = witness_and_input(5999, b"pcs-policy");
    let proof = prove_decomp(w, pcs_config()).expect("prove");
    let mut wrong = pcs_config();
    wrong.pow_bits += 1;
    assert!(
        verify_decomp(&proof, wrong).is_err(),
        "a proof must not select its own PCS policy"
    );
}

/// Control: the negatives' seeds prove+verify cleanly without mutation.
#[test]
fn decomp_seeds_honest_without_mutation() {
    for (seed, msg) in [
        (6001u64, &b"drop-digit"[..]),
        (6002, b"flip-hint"),
        (6003, b"w-tamper"),
        (6005, b"w0-range"),
    ] {
        let (w, _) = witness_and_input(seed, msg);
        let proof = prove_decomp(w, pcs_config())
            .unwrap_or_else(|e| panic!("seed {seed}: honest prove failed: {e:?}"));
        verify_decomp(&proof, pcs_config())
            .unwrap_or_else(|e| panic!("seed {seed}: honest verify failed: {e:?}"));
    }
}

// =====================================================================
// Negatives.
// =====================================================================

/// Dropped w1' digit emission: flip a w1' value so the emitted byte diverges →
/// the HashIo yield no longer matches the (honest) test-side consumer byte.
/// We simulate by mutating the reference w1 (= w1') in the witness.
#[test]
fn negative_dropped_w1_digit() {
    let (mut w, _) = witness_and_input(6001, b"drop-digit");
    w.decomp.w1[0][4] = (w.decomp.w1[0][4] + 1) % 16;
    assert!(
        rejected_or_panicked(w),
        "a changed w1' must break the w1Encode/UseHint balance"
    );
}

/// Flip one hint bit: UseHint output diverges from w1' ⇒ the UseHint constraint
/// (w1' = w1 + h·δ + 16·wrap16) cannot be satisfied with the honest w1'.
#[test]
fn negative_flip_hint_bit() {
    let (mut w, _) = witness_and_input(6002, b"flip-hint");
    // Find a coefficient with a hint set and flip it.
    let (mut fi, mut fm) = (0usize, 0usize);
    'outer: for i in 0..stwo_mldsa::constants::K {
        for m in 0..stwo_mldsa::constants::N {
            if w.decomp.hint[i][m] == 1 {
                fi = i;
                fm = m;
                break 'outer;
            }
        }
    }
    w.decomp.hint[fi][fm] ^= 1;
    assert!(
        rejected_or_panicked(w),
        "a flipped hint bit must be rejected"
    );
}

/// w-binding tamper: change a w value so the decomp USE no longer matches the
/// (honest) coeffs-side wcell yield.
#[test]
fn negative_w_binding_tamper() {
    let (mut w, _) = witness_and_input(6003, b"w-tamper");
    w.rows[1].w[10] = (w.rows[1].w[10] + 1) % stwo_mldsa::constants::Q;
    assert!(
        rejected_or_panicked(w),
        "a tampered w must break the w-binding"
    );
}

/// w0 out of centered range (§5 row I-3a): push one `w0` above γ2. The
/// [DECOMP] centered-range gate is the exact two-sided rc `a = w0+γ2−1`,
/// `b = γ2−w0`, both required in `[0, 2γ2)`. Setting `w0 = γ2+1` makes
/// `b = γ2 − (γ2+1) = −1`, which has no row in the range table ⇒ reject.
#[test]
fn negative_w0_out_of_range() {
    let (mut w, _) = witness_and_input(6005, b"w0-range");
    // γ2 is the upper bound of the centered window (w0 ∈ (−γ2, γ2]); one past it
    // is out of range on the `b = γ2 − w0` side.
    w.decomp.w0[0][0] = stwo_mldsa::constants::GAMMA2 as i32 + 1;
    assert!(
        rejected_or_panicked(w),
        "w0 = γ2+1 must be rejected by the centered-range lookup"
    );
}
