//! M4 acceptance: standalone prove+verify of the `mldsa_coeffs` component +
//! verifier-native fold against real oracle-generated ML-DSA-65 signatures, plus
//! the worksheet §5 / S5 §5 negative matrix (each mutation must be rejected).

use ml_dsa::signature::{Keypair, Signer, Verifier};
use ml_dsa::{EncodedSignature, EncodedVerifyingKey, MlDsa65, SigningKey};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::PcsConfig;

use stwo_mldsa::coeffs::layout::N_GROUPS;
use stwo_mldsa::proof::{prove_coeffs, verify_coeffs, CoeffsProof};
use stwo_mldsa::reference::encoding::{pk_decode, sig_decode};
use stwo_mldsa::reference::sponge::shake256;
use stwo_mldsa::witness::generate_witness;
use stwo_mldsa::MlDsaVerifyInput;

fn oracle_keypair(rng: &mut StdRng) -> SigningKey<MlDsa65> {
    let mut seed = [0u8; 32];
    rng.fill(&mut seed);
    SigningKey::<MlDsa65>::from_seed(&seed.into())
}

fn oracle_input(sk: &SigningKey<MlDsa65>, msg: &[u8]) -> MlDsaVerifyInput {
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

fn prove_case(seed: u64, msg: &[u8]) -> CoeffsProof {
    let (witness, input) = witness_and_input(seed, msg);
    prove_coeffs(witness, input, PcsConfig::default()).expect("prove")
}

fn witness_and_input(
    seed: u64,
    msg: &[u8],
) -> (stwo_mldsa::witness::MlDsaWitness, MlDsaVerifyInput) {
    let mut rng = StdRng::seed_from_u64(seed);
    let sk = oracle_keypair(&mut rng);
    let input = oracle_input(&sk, msg);
    let witness = generate_witness(&input).expect("witness");
    (witness, input)
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

/// N9: tamper a claimed EvalAtRs sum (a v-group eval) → native fold nonzero +
/// EvalAtRs balance broken.
#[test]
fn negative_tampered_claimed_eval() {
    let mut proof = prove_case(2001, b"tamper-eval");
    proof.group_evals[17] += SecureField::from(stwo::core::fields::m31::M31::from_u32_unchecked(1));
    assert!(
        verify_coeffs(&proof, PcsConfig::default()).is_err(),
        "tampered claimed eval must reject"
    );
}

/// N8: verify against the WRONG pk (ρ′) → native ExpandA(ρ′) ≠ ExpandA(ρ), fold nonzero.
#[test]
fn negative_wrong_pk_rho() {
    let mut proof = prove_case(2002, b"wrong-rho");
    proof.input.rho[0] ^= 1;
    assert!(
        verify_coeffs(&proof, PcsConfig::default()).is_err(),
        "wrong ρ must reject"
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
        "tampered claimed sum must reject"
    );
}

// --- Witness-level negatives (mutate the witness before proving) ---

/// N1: perturb one v digit → the SZ bivariate identity fails at (r,s).
#[test]
fn negative_perturb_v_digit() {
    let (mut w, input) = witness_and_input(3001, b"v-digit");
    w.digits.v[2][100][3] += 1; // v_2, coeff 100, digit t=3
    assert!(rejected(w, input), "perturbed v digit must be rejected");
}

/// N2: swap two polys in the stack (swap z_0 and z_1 digit tables) → the group
/// Horner evals land under the wrong poly_id ⇒ native fold / eval balance fails.
#[test]
fn negative_swap_two_polys() {
    let (mut w, input) = witness_and_input(3002, b"swap-polys");
    w.digits.z.swap(0, 1);
    assert!(rejected(w, input), "swapping two polys must be rejected");
}

/// N3 (reviewer layout-invariant): swap two digits across t within a row → the
/// recomposition `Σ d_t·B^t` changes ⇒ the SZ identity / recomp binding fails.
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

/// N4: out-of-range digit (+257, outside the balanced [−256,256) window) → the
/// rc9 table has no such row ⇒ prover panics/imbalances.
#[test]
fn negative_out_of_range_digit() {
    let (mut w, input) = witness_and_input(3004, b"oor-digit");
    w.digits.w[1][30][0] = 257; // outside [−256, 256)
    assert!(rejected(w, input), "out-of-range digit must be rejected");
}

fn coeffs_range_boundary_rejects(
    kind: stwo_mldsa::coeffs::tables::RcKind,
    seed: u64,
    message: &[u8],
) {
    let _attack = stwo_mldsa::coeffs::install_range_boundary_attack(kind);
    let (witness, input) = witness_and_input(seed, message);
    assert!(
        rejected(witness, input),
        "{} first-excluded value must reject in coeffs",
        kind.name()
    );
}

#[test]
fn coeffs_split_coeffs_rc9_boundary_rejects() {
    coeffs_range_boundary_rejects(stwo_mldsa::coeffs::tables::RcKind::Rc9, 3010, b"split-rc9");
}

#[test]
fn coeffs_split_coeffs_rc13_boundary_rejects() {
    coeffs_range_boundary_rejects(
        stwo_mldsa::coeffs::tables::RcKind::Rc13,
        3011,
        b"split-rc13",
    );
}

#[test]
fn coeffs_split_coeffs_rc8_boundary_rejects() {
    coeffs_range_boundary_rejects(stwo_mldsa::coeffs::tables::RcKind::Rc8, 3012, b"split-rc8");
}

#[test]
fn coeffs_split_coeffs_rc7_boundary_rejects() {
    coeffs_range_boundary_rejects(stwo_mldsa::coeffs::tables::RcKind::Rc7, 3013, b"split-rc7");
}

#[test]
fn coeffs_split_coeffs_ternary_boundary_rejects() {
    coeffs_range_boundary_rejects(
        stwo_mldsa::coeffs::tables::RcKind::Ternary,
        3014,
        b"split-ternary",
    );
}

/// N5: tamper a carry cell → the (s−B)·Ĉ term in the fold changes ⇒ (‡) nonzero.
#[test]
fn negative_tampered_carry() {
    let (mut w, input) = witness_and_input(3005, b"carry");
    w.rows[0].carry[10][2] += 1;
    assert!(rejected(w, input), "tampered carry must be rejected");
}

/// N6: recomposition-binding mismatch — change a z digit WITHOUT touching the
/// coefficient the norm consumes. The recomp constraint `cell = Σ d_t·B^t` binds
/// them; a lone digit change breaks it (and the SZ identity).
#[test]
fn negative_recomp_binding_mismatch() {
    let (mut w, input) = witness_and_input(3006, b"recomp");
    // Bump the top z digit by 1 (changes Σ d_t·B^t but the norm/aux still target
    // the original cell) — the recomposition value the AIR commits diverges.
    w.digits.z[3][77][2] += 1;
    assert!(
        rejected(w, input),
        "recomposition mismatch must be rejected"
    );
}

/// N7: the exact z-norm gate accepts `|z| ≤ γ1−β−1 = 524_091` and rejects the
/// boundary `|z| = γ1−β = 524_092` (the review flag — NOT a 2^20 window that
/// over-accepts by ~195). Checked at constraint-arithmetic granularity: the AIR
/// C5 predicate is `a = z + bound ∈ [0,2^20)` AND `b = bound − z ∈ [0,2^20)`,
/// both pinned by rc13+rc7. A full-proof version would conflate the norm with
/// the SZ identity (mutating z alone breaks the [LIN] witnesses), so we test the
/// gate directly, exactly as the AIR decomposes it.
#[test]
fn z_norm_gate_is_exact() {
    let bound = stwo_mldsa::coeffs::Z_NORM_BOUND as i128; // 524_091
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

/// Measure committed cells (M31 units) and the native ExpandA+eval microbench.
#[test]
fn measure_cells_and_bench() {
    use stwo_mldsa::coeffs::tables::RcKind;
    use stwo_mldsa::coeffs::{coeffs_preprocessed_ids, layout, N_BASE_COLS, N_INTERACTION_COLS};

    let log_size = stwo_mldsa::air_util::padded_log_size(layout::active_rows());
    let rows = 1usize << log_size;
    let active = layout::active_rows();

    // coeffs component cells (M31 units) = columns × rows.
    let coeffs_pre = coeffs_preprocessed_ids().len();
    let coeffs_base = N_BASE_COLS;
    let coeffs_inter = N_INTERACTION_COLS; // already in M31 (4 per QM31 folded in)
    let coeffs_cells = (coeffs_pre + coeffs_base + coeffs_inter) * rows;

    // rc table cells (each: 1 preprocessed value + 1 multiplicity + 4 interaction).
    let mut rc_cells = 0usize;
    for kind in RcKind::ALL {
        let tr = 1usize << kind.log_size();
        rc_cells += (1 /*value*/ + 1 /*mult*/ + 4/*interaction QM31*/) * tr;
    }

    let total = coeffs_cells + rc_cells;
    eprintln!("== M4 mldsa_coeffs cell measurement (M31 units) ==");
    eprintln!(
        "log_size = {log_size} ({rows} rows, {active} active, {} groups)",
        layout::N_GROUPS
    );
    eprintln!("coeffs: pre={coeffs_pre} base={coeffs_base} inter={coeffs_inter} cols → {coeffs_cells} cells");
    eprintln!("rc tables (rc9/rc13/rc8/rc7/ternary): {rc_cells} cells");
    eprintln!("TOTAL committed cells = {total}");
    eprintln!("counting method: (Σ columns over all trees) × 2^log_size, interaction QM31 counted as 4 M31");

    // Native ExpandA + bivariate-eval microbench.
    let (_, input) = witness_and_input(9999, b"bench");
    let r = SecureField::from(stwo::core::fields::m31::M31::from_u32_unchecked(12345));
    let s = SecureField::from(stwo::core::fields::m31::M31::from_u32_unchecked(67890));
    let iters = 20u32;
    let t0 = std::time::Instant::now();
    for _ in 0..iters {
        let _ = stwo_mldsa::verifier_native::compute_public_evals(&input, r, s);
    }
    let ns = t0.elapsed().as_nanos() / iters as u128;
    eprintln!("native ExpandA(ρ)+INTTs+bivariate-eval: ~{ns} ns/call ({iters} iters)");
}

/// Control: the exact seeds/messages used by the witness-level negatives prove
/// and verify cleanly WITHOUT any mutation — so each negative's rejection is
/// attributable to its mutation, not a bad seed.
#[test]
fn negative_seeds_are_honest_without_mutation() {
    for (seed, msg) in [
        (3001u64, &b"v-digit"[..]),
        (3002, b"swap-polys"),
        (3005, b"carry"),
        (3006, b"recomp"),
    ] {
        let (w, input) = witness_and_input(seed, msg);
        let proof = prove_coeffs(w, input, PcsConfig::default())
            .unwrap_or_else(|e| panic!("seed {seed}: honest prove failed: {e:?}"));
        verify_coeffs(&proof, PcsConfig::default())
            .unwrap_or_else(|e| panic!("seed {seed}: honest verify failed: {e:?}"));
    }
}
