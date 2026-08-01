//! Property test for the witness generator.
//!
//! Generates ≥1000 random ML-DSA-65 signatures via the `ml-dsa` oracle (varying
//! message length, including 1–2 KB Sig_structure-sized messages), and for each:
//!
//! - `generate_witness` succeeds;
//! - the generator's own asserts (limb identity `E_{m,t} == 0`, exact
//!   q-divisibility, every digit in `[−256,256)`, `|C| ≤ 2^20`, recomposition
//!   binding) all pass.
//!
//! For a sample of 50 it ALSO re-derives `u_i` from scratch and independently
//! checks the ℤ[X] identity `u = w + q·e + (X^256+1)·v` in `i128`.
//!
//! It prints the observed maximum for each digit family and carry. It fails if
//! a value exceeds its fixed bound.

// This is a numeric property test; explicit index loops are the readable form,
// and `i % n == 0` is the divisibility idiom we mean.
#![allow(clippy::needless_range_loop)]
#![allow(clippy::manual_is_multiple_of)]

use ml_dsa::signature::{Keypair, Signer, Verifier};
use ml_dsa::{EncodedSignature, EncodedVerifyingKey, MlDsa65, SigningKey};
use rand::{rngs::StdRng, Rng, SeedableRng};

use stwo_mldsa::constants::{D, K, N, Q};
use stwo_mldsa::profile::ML_DSA_65;
use stwo_mldsa::reference::encoding::{pk_decode, sig_decode};
use stwo_mldsa::reference::expand_a::expand_a;
use stwo_mldsa::reference::ntt::ntt_inverse;
use stwo_mldsa::reference::sample_in_ball::sample_in_ball;
use stwo_mldsa::reference::sponge::shake256;
use stwo_mldsa::witness::{generate_witness, B, CARRY_BOUND};
use stwo_mldsa::MlDsaVerifyInput;

/// Number of random signatures.
const N_SIGS: usize = 1000;
/// How many get the independent from-scratch `u = w + q·e + (X^256+1)·v` recheck.
const N_INDEPENDENT: usize = 50;

// Fixed bounds for adversarial digit values. Committed polynomials can be ±256
// regardless of the honest value.
//
// The digit *window* is the half-open `[−256, 256)`, so the lowest digit `−256`
// is valid while `+256` is not. §5's magnitude budget treats the digit ceiling
// as `|digit| ≤ 256` (it sums `±256` conservatively), so the magnitude gate is
// inclusive `≤ 256`; the *range* invariant `[−256, 256)` is checked separately.
const BOUND_DIGIT_MAG: i128 = 256; // Inclusive magnitude limit.
const BOUND_CARRY: i128 = CARRY_BOUND; // 2^20 rc pin
/// Maximum total row magnitude before carry, approximately `2^29.42`.
const BOUND_PARTIAL: i128 = 716_382_976;

fn oracle_keypair(rng: &mut StdRng) -> SigningKey<MlDsa65> {
    let mut seed = [0u8; 32];
    rng.fill(&mut seed);
    SigningKey::<MlDsa65>::from_seed(&seed.into())
}

/// Sign `msg` (pure, empty ctx) and decode into an `MlDsaVerifyInput`.
fn oracle_input(sk: &SigningKey<MlDsa65>, msg: &[u8]) -> MlDsaVerifyInput {
    let vk = sk.verifying_key();
    let sig = sk.sign(msg);
    assert!(vk.verify(msg, &sig).is_ok(), "oracle self-check");
    let vk_bytes: EncodedVerifyingKey<MlDsa65> = vk.encode();
    let sig_bytes: EncodedSignature<MlDsa65> = sig.encode();
    let pk_slice: &[u8] = vk_bytes.as_slice();
    let sig_slice: &[u8] = sig_bytes.as_slice();

    let pk = pk_decode(ML_DSA_65, pk_slice).expect("pk_decode");
    let sp = sig_decode(ML_DSA_65, sig_slice).expect("sig_decode");
    // tr = H(pk, 512).
    let (tr_vec, _) = shake256(&[pk_slice], 64);
    let mut tr = [0u8; 64];
    tr.copy_from_slice(&tr_vec);

    MlDsaVerifyInput::from_decoded(ML_DSA_65, &pk, &sp, tr, msg.to_vec())
}

/// Message length for case `i`: mostly small, but every 7th is 1–2 KB to
/// exercise Sig_structure-sized inputs.
fn msg_len(i: usize) -> usize {
    if i % 7 == 0 {
        1024 + (i % 1024) // 1–2 KB
    } else {
        1 + (i % 200)
    }
}

/// Independent ℤ[X] recompute: `u_i = Σ_j A_ij·z_j − c·t1_i·2^d`, then assert
/// `u = w + q·e + (X^256+1)·v` coefficient-wise in i128, from the witness's own
/// v, e, w — recomputing u from A/z/c/t1 without touching the generator's `u`.
fn independent_check(input: &MlDsaVerifyInput, w: &stwo_mldsa::witness::MlDsaWitness) {
    let q = Q as i128;
    let two_d = 1i128 << D;
    let a_hat = expand_a(ML_DSA_65, &input.rho);

    // Decoded integer A, z, c, t1·2^d.
    let mut a_int = vec![vec![[0i128; N]; 5]; K];
    for i in 0..K {
        for j in 0..5 {
            let p = ntt_inverse(&a_hat.matrix[i][j]);
            for m in 0..N {
                a_int[i][j][m] = p[m] as i128;
            }
        }
    }
    let c = sample_in_ball(ML_DSA_65, &input.c_tilde)
        .expect("sample in ball")
        .c;
    let c_int: Vec<i128> = c.iter().map(|&x| x as i128).collect();

    for i in 0..K {
        // Recompute u_i as a full ℤ[X] convolution (deg ≤ 510).
        let mut u = vec![0i128; 2 * N - 1];
        for j in 0..5 {
            for a in 0..N {
                let av = a_int[i][j][a];
                if av == 0 {
                    continue;
                }
                for z in 0..N {
                    u[a + z] += av * input.z[j][z] as i128;
                }
            }
        }
        for ci in 0..N {
            let cc = c_int[ci];
            if cc == 0 {
                continue;
            }
            for ti in 0..N {
                u[ci + ti] -= cc * (input.t1[i][ti] as i128 * two_d);
            }
        }

        // Assemble w + q·e + (X^256+1)·v from the witness and compare to u.
        let row = &w.rows[i];
        for m in 0..(2 * N - 1) {
            let w_m = if m < N { row.w[m] as i128 } else { 0 };
            let e_m = if m < N { row.e[m] } else { 0 };
            let v_lo = if m < row.v.len() { row.v[m] } else { 0 }; // "+1"·v
            let v_hi = if m >= N && (m - N) < row.v.len() {
                row.v[m - N]
            } else {
                0
            }; // X^256·v
            let rhs = w_m + q * e_m + v_lo + v_hi;
            assert_eq!(
                u[m], rhs,
                "independent identity u = w + q·e + (X^256+1)·v failed: i={i} m={m}"
            );
        }
    }
}

#[test]
fn witness_property_over_1000_signatures() {
    let t0 = std::time::Instant::now();
    let mut rng = StdRng::seed_from_u64(0xD5A6_0000_2222);

    let mut max_digit_z = 0i128;
    let mut max_digit_w = 0i128;
    let mut max_digit_e = 0i128;
    let mut max_digit_v = 0i128;
    let mut max_carry = 0i128;
    let mut max_partial = 0i128;
    let mut max_hint_total = 0usize;

    for i in 0..N_SIGS {
        let sk = oracle_keypair(&mut rng);
        let mut msg = vec![0u8; msg_len(i)];
        rng.fill(msg.as_mut_slice());
        let input = oracle_input(&sk, &msg);

        let witness = generate_witness(ML_DSA_65, &input)
            .unwrap_or_else(|e| panic!("case {i}: generate_witness failed: {e}"));

        // Aggregate observed maxima.
        let m = &witness.maxima;
        max_digit_z = max_digit_z.max(m.max_digit_z);
        max_digit_w = max_digit_w.max(m.max_digit_w);
        max_digit_e = max_digit_e.max(m.max_digit_e);
        max_digit_v = max_digit_v.max(m.max_digit_v);
        max_carry = max_carry.max(m.max_carry);
        max_partial = max_partial.max(m.max_partial_before_carry);
        let ht: usize = witness.decomp.hint_weight.iter().sum();
        max_hint_total = max_hint_total.max(ht);

        // Independent recheck for the first N_INDEPENDENT cases.
        if i < N_INDEPENDENT {
            independent_check(&input, &witness);
        }
    }

    let dt = t0.elapsed();

    eprintln!("=== witness property test: {N_SIGS} signatures in {dt:?} ===");
    eprintln!("(independent u = w + q·e + (X^256+1)·v recheck on first {N_INDEPENDENT})");
    eprintln!("digit base B = {B}, digit window [−256, 256)");
    eprintln!("observed maxima and fixed bounds:");
    eprintln!("  max |digit z|       = {max_digit_z:>13}  (mag bound {BOUND_DIGIT_MAG})");
    eprintln!("  max |digit w|       = {max_digit_w:>13}  (mag bound {BOUND_DIGIT_MAG})");
    eprintln!("  max |digit e|       = {max_digit_e:>13}  (mag bound {BOUND_DIGIT_MAG})");
    eprintln!("  max |digit v|       = {max_digit_v:>13}  (mag bound {BOUND_DIGIT_MAG})");
    eprintln!("  max honest |carry|  = {max_carry:>13}  (rc bound {BOUND_CARRY} = 2^20)");
    eprintln!("  max |partial|       = {max_partial:>13}  (bound {BOUND_PARTIAL} = 2^29.42)");
    eprintln!(
        "  max Σ hint bits     = {max_hint_total:>13}  (ω bound {})",
        stwo_mldsa::constants::OMEGA
    );

    // Each observed value must be within its bound. Digits use the inclusive
    // magnitude limit. The window `[−256,256)` permits −256, whose magnitude
    // is 256. The strict half-open range is enforced inside
    // the generator's `balanced_digits` (debug_assert, active in test builds).
    assert!(
        max_digit_z <= BOUND_DIGIT_MAG,
        "z digit exceeded bound: {max_digit_z}"
    );
    assert!(
        max_digit_w <= BOUND_DIGIT_MAG,
        "w digit exceeded bound: {max_digit_w}"
    );
    assert!(
        max_digit_e <= BOUND_DIGIT_MAG,
        "e digit exceeded bound: {max_digit_e}"
    );
    assert!(
        max_digit_v <= BOUND_DIGIT_MAG,
        "v digit exceeded bound: {max_digit_v}"
    );
    assert!(max_carry <= BOUND_CARRY, "carry exceeded 2^20: {max_carry}");
    assert!(
        max_partial <= BOUND_PARTIAL,
        "partial before carry exceeded its bound: {max_partial} > {BOUND_PARTIAL}"
    );
    assert!(
        max_hint_total <= stwo_mldsa::constants::OMEGA,
        "hint weight exceeded ω: {max_hint_total}"
    );
}
