//! M5 acceptance for `mldsa_decomp` ([DECOMP]+[HINT]): standalone prove+verify
//! over ≥20 oracle ML-DSA-65 signatures, plus the S5 §5 negative matrix. The
//! w-cell binding and w1Encode byte emission are balanced test-side (a wcell
//! provider + a hashio consumer) since coeffs/the sponge are not in this
//! composition; M6 replaces the balancers with the real components.

use ml_dsa::signature::{Keypair, Signer, Verifier};
use ml_dsa::{EncodedSignature, EncodedVerifyingKey, MlDsa65, SigningKey};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use stwo::core::pcs::PcsConfig;

use stwo_mldsa::decomp::proof::{prove_decomp, verify_decomp};
use stwo_mldsa::reference::encoding::{pk_decode, sig_decode};
use stwo_mldsa::reference::sponge::shake256;
use stwo_mldsa::witness::{generate_witness, MlDsaWitness};
use stwo_mldsa::MlDsaVerifyInput;

fn oracle_input(seed: u64, msg: &[u8]) -> MlDsaVerifyInput {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut sk_seed = [0u8; 32];
    rng.fill(&mut sk_seed);
    let sk = SigningKey::<MlDsa65>::from_seed(&sk_seed.into());
    let vk = sk.verifying_key();
    let sig = sk.sign(msg);
    assert!(vk.verify(msg, &sig).is_ok(), "oracle self-check");
    let vk_bytes: EncodedVerifyingKey<MlDsa65> = vk.encode();
    let sig_bytes: EncodedSignature<MlDsa65> = sig.encode();
    let pk = pk_decode(vk_bytes.as_slice()).expect("pk_decode");
    let sp = sig_decode(sig_bytes.as_slice()).expect("sig_decode");
    let (tr_vec, _) = shake256(&[vk_bytes.as_slice()], 64);
    let mut tr = [0u8; 64];
    tr.copy_from_slice(&tr_vec);
    MlDsaVerifyInput::from_decoded(&pk, &sp, tr, msg.to_vec())
}

fn witness_and_input(seed: u64, msg: &[u8]) -> (MlDsaWitness, MlDsaVerifyInput) {
    let input = oracle_input(seed, msg);
    let witness = generate_witness(&input).expect("witness");
    (witness, input)
}

/// A witness mutation is REJECTED if proving fails/panics or verify fails.
fn rejected(witness: MlDsaWitness) -> bool {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        match prove_decomp(witness, PcsConfig::default()) {
            Ok(proof) => verify_decomp(&proof).is_err(),
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
        let proof = prove_decomp(w, PcsConfig::default()).expect("prove");
        verify_decomp(&proof).unwrap_or_else(|e| panic!("case {i}: verify failed: {e:?}"));
        ok += 1;
    }
    assert_eq!(ok, 20);
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
        let proof = prove_decomp(w, PcsConfig::default())
            .unwrap_or_else(|e| panic!("seed {seed}: honest prove failed: {e:?}"));
        verify_decomp(&proof).unwrap_or_else(|e| panic!("seed {seed}: honest verify failed: {e:?}"));
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
    assert!(rejected(w), "a changed w1' must break the w1Encode/UseHint balance");
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
    assert!(rejected(w), "a flipped hint bit must be rejected");
}

/// w-binding tamper: change a w value so the decomp USE no longer matches the
/// (honest) coeffs-side wcell yield.
#[test]
fn negative_w_binding_tamper() {
    let (mut w, _) = witness_and_input(6003, b"w-tamper");
    w.rows[1].w[10] = (w.rows[1].w[10] + 1) % stwo_mldsa::constants::Q;
    assert!(rejected(w), "a tampered w must break the w-binding");
}

/// Σh = ω+1: force the hint weight over ω. We add hints until the total is 56.
#[test]
fn negative_hint_weight_over_omega() {
    let (mut w, _) = witness_and_input(6004, b"omega");
    let total: usize = w.decomp.hint.iter().flatten().map(|&h| h as usize).sum();
    // Set additional hints (on zero-hint coefficients) to push total to ω+1.
    let target = stwo_mldsa::constants::OMEGA + 1;
    let mut cur = total;
    'fill: for i in 0..stwo_mldsa::constants::K {
        for m in 0..stwo_mldsa::constants::N {
            if cur >= target {
                break 'fill;
            }
            if w.decomp.hint[i][m] == 0 {
                w.decomp.hint[i][m] = 1;
                cur += 1;
            }
        }
    }
    assert!(cur >= target, "must reach ω+1 hints");
    assert!(rejected(w), "Σh = ω+1 must be rejected by the accumulator gate");
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
        rejected(w),
        "w0 = γ2+1 must be rejected by the centered-range lookup"
    );
}
