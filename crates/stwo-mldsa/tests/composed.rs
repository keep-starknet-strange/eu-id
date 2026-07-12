//! M6 acceptance for the composed in-circuit ML-DSA-65 statement
//! (`stwo_mldsa::statement`): ONE `air-core` proof stitching coeffs + decomp +
//! sib + three SHAKE-256 sponge chains + msglink + bridges/sinks. Positive over
//! 10 oracle signatures with ≥1 KiB messages, a control, the negative matrix
//! a–f, and an (ignored) numbers probe.
//!
//! Run single-threaded: `RAYON_NUM_THREADS=1 cargo test -p stwo-mldsa
//! --test composed -- --test-threads=1`.

use ml_dsa::signature::{Keypair, Signer, Verifier};
use ml_dsa::{EncodedSignature, EncodedVerifyingKey, MlDsa65, SigningKey};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use stwo::core::fri::FriConfig;
use stwo::core::pcs::PcsConfig;

use stwo_mldsa::reference::encoding::{pk_decode, sig_decode};
use stwo_mldsa::reference::sponge::shake256;
use stwo_mldsa::statement::{prove_mldsa, verify_mldsa, PermIdPlan};
use stwo_mldsa::witness::{generate_witness, MlDsaWitness};
use stwo_mldsa::MlDsaVerifyInput;

/// The SHAKE consumers (keccak_round, sponge_v) declare constraint degree
/// bound `log_size + 2` (LogUp batch 4), so constraint evaluation needs
/// `log_blowup >= 2` to reuse committed evaluations (production runs blowup 3;
/// `pcs_config()` has blowup 1, which would require stored
/// polynomial coefficients).
fn pcs_config() -> PcsConfig {
    PcsConfig {
        pow_bits: 10,
        fri_config: FriConfig::new(0, 2, 3, 1),
        lifting_log_size: None,
    }
}

// =====================================================================
// Helpers (model: tests/decomp.rs + tests/sampleinball.rs).
// =====================================================================

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

/// A ≥1 KiB message (padding a per-case tag out to 1024..2048 bytes).
fn big_msg(tag: &str, len: usize) -> Vec<u8> {
    let mut m = tag.as_bytes().to_vec();
    m.resize(len, 0x5a);
    m
}

/// A mutated (witness, input) pair is REJECTED if proving fails/panics or the
/// verify errs.
fn rejected(witness: MlDsaWitness, input: MlDsaVerifyInput) -> bool {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        match prove_mldsa(witness, input, pcs_config()) {
            Ok(proof) => verify_mldsa(&proof).is_err(),
            Err(_) => true,
        }
    }));
    r.unwrap_or(true)
}

// =====================================================================
// Positive: 10 sigs, ≥1 KiB messages varied 1024..2048 bytes.
// =====================================================================

#[test]
fn composed_proves_and_verifies_10_sigs() {
    let mut ok = 0;
    for i in 0..10u64 {
        let len = 1024 + (i as usize) * 100; // 1024..1924, all ≥ 1 KiB
        let msg = big_msg(&format!("mldsa-composed-{i}"), len);
        let (w, input) = witness_and_input(7000 + i, &msg);

        // KAT: the native SIB commit c̃' equals the public c̃, and the native
        // reference verify accepts.
        assert_eq!(
            &w.sponge.c_tilde_squeezed[..48],
            &input.c_tilde[..],
            "case {i}: KAT c̃ mismatch"
        );
        let pk = input.encode_pk();
        let sig = input.encode_sig();
        assert!(
            stwo_mldsa::verify(&pk, &msg, &sig),
            "case {i}: native reference verify must accept"
        );

        let proof = prove_mldsa(w, input, pcs_config()).expect("prove");
        verify_mldsa(&proof).unwrap_or_else(|e| panic!("case {i}: verify failed: {e:?}"));
        ok += 1;
    }
    assert_eq!(ok, 10);
}

// =====================================================================
// Control: an honest, unmutated witness on the negative seeds proves+verifies.
// =====================================================================

#[test]
fn composed_control_honest_proves() {
    for seed in [8001u64, 8002, 8003, 8004, 8006] {
        let msg = big_msg(&format!("control-{seed}"), 1024);
        let (w, input) = witness_and_input(seed, &msg);
        let proof = prove_mldsa(w, input, pcs_config()).expect("control prove");
        verify_mldsa(&proof).expect("control verify");
    }
}

// =====================================================================
// Negatives a–f.
// =====================================================================

/// a) tamper µ-absorb message byte (66+k) with `input.message` unchanged →
///    the msglink producer + µ-absorb bridge/consume no longer balance.
#[test]
fn composed_negative_a_mu_absorb_message_tamper() {
    let msg = big_msg("neg-a", 1024);
    let (mut w, input) = witness_and_input(8001, &msg);
    // Flip a byte of M inside the µ-absorb transcript (offset 66 = tr(64)+00+00).
    w.sponge.mu_absorbed[66 + 10] ^= 1;
    assert!(
        rejected(w, input),
        "µ-absorb message tamper must be rejected"
    );
}

/// b) chain-seam: flip a byte of the µ bytes entering the c̃ absorb.
#[test]
fn composed_negative_b_chain_seam_ct_absorb() {
    let msg = big_msg("neg-b", 1024);
    let (mut w, input) = witness_and_input(8002, &msg);
    w.sponge.c_tilde_absorbed[3] ^= 1;
    assert!(rejected(w, input), "c̃-absorb seam tamper must be rejected");
}

/// c) w1Encode flip: flip a w1 coefficient the decomp component emits.
#[test]
fn composed_negative_c_w1encode_flip() {
    let msg = big_msg("neg-c", 1024);
    let (mut w, input) = witness_and_input(8003, &msg);
    w.decomp.w1[0][0] ^= 1;
    assert!(rejected(w, input), "w1Encode flip must be rejected");
}

/// d) swap-placement: same mutation as sampleinball's placement-permuted gate.
#[test]
fn composed_negative_d_placement_permuted() {
    let msg = big_msg("neg-d", 1024);
    let (mut w, input) = witness_and_input(8004, &msg);
    let n = stwo_mldsa::constants::N;
    let p = (0..n)
        .find(|&m| w.digits.c[m] != 0)
        .expect("a nonzero coeff");
    let q = (0..n).find(|&m| w.digits.c[m] == 0).expect("a zero coeff");
    assert_ne!(p, q);
    let moved = w.digits.c[p];
    w.digits.c[p] = 0;
    w.digits.c[q] = moved;
    let sumsq: i128 = w.digits.c.iter().map(|&x| x * x).sum();
    assert_eq!(
        sumsq as usize,
        stwo_mldsa::constants::TAU,
        "Σc² must stay τ"
    );
    assert!(rejected(w, input), "placement permutation must be rejected");
}

/// e) perm-id namespacing: the three chains' perm bases are the running perm
///    counts, so their id ranges are disjoint by construction — a cross-chain
///    KeccakState collision is STRUCTURALLY IMPOSSIBLE in this composition.
#[test]
fn composed_negative_e_perm_id_namespacing() {
    // µ (66+|M|=1090 bytes ⇒ n_absorb=9, n_squeeze=1 ⇒ 9 perms),
    // c̃ (832 bytes ⇒ n_absorb=7, +1 ⇒ 7 perms). Any counts work; assert the
    // structural disjointness invariant.
    for (n_mu, n_ct) in [(9usize, 7usize), (1, 1), (13, 5), (16, 16)] {
        let plan = PermIdPlan::new(n_mu, n_ct);
        assert_eq!(plan.mu_base, 0);
        assert_eq!(plan.c_tilde_base, n_mu, "c̃ base = running count after µ");
        assert_eq!(
            plan.sib_base,
            n_mu + n_ct,
            "SIB base = running count after c̃"
        );
        // Ranges [0,n_mu), [n_mu,n_mu+n_ct), [n_mu+n_ct, ..) never overlap: each
        // chain's ids live in [base, base+n_chain) and the next base IS the prior
        // running total, so overlap is arithmetically impossible.
        assert!(plan.mu_base + n_mu <= plan.c_tilde_base);
        assert!(plan.c_tilde_base + n_ct <= plan.sib_base);
    }
}

/// f) wrong pk: flip `input.rho[0]` after witness generation → the
///    verifier-native fold binds against the tampered ρ and rejects.
#[test]
fn composed_negative_f_wrong_pk_rho() {
    let msg = big_msg("neg-f", 1024);
    let (w, mut input) = witness_and_input(8006, &msg);
    input.rho[0] ^= 1;
    assert!(rejected(w, input), "wrong-pk ρ flip must fail the fold");
}

// =====================================================================
// Preprocessed-root pin (F-ROOT hardening): `verify_mldsa` recomputes the
// tree-0 root from the public input and rejects a forged preprocessed tree
// fail-closed, before any STARK work.
// =====================================================================

/// Control: an honest proof's committed tree-0 root equals the root
/// `verify_mldsa` derives from the public input, so verify accepts.
#[test]
fn composed_preprocessed_root_pin_control() {
    let msg = big_msg("froot-control", 1024);
    let (w, input) = witness_and_input(8101, &msg);
    let proof = prove_mldsa(w, input, pcs_config()).expect("prove");
    verify_mldsa(&proof).expect("honest proof must verify under the root pin");
}

/// Negative: tamper the proof's tree-0 (preprocessed) commitment root. The pin
/// recomputes the honest root from `proof.input` and rejects the mismatch
/// fail-closed — the forged tree never reaches the STARK verifier. This is the
/// F-ROOT class: a forged range table / schedule / constant column would carry
/// a different tree-0 root, caught here.
#[test]
fn composed_preprocessed_root_pin_rejects_tampered_root() {
    let msg = big_msg("froot-neg", 1024);
    let (w, input) = witness_and_input(8102, &msg);
    let mut proof = prove_mldsa(w, input, pcs_config()).expect("prove");
    // Sanity: unmutated verifies (shares the seed with the mutation below).
    verify_mldsa(&proof).expect("control leg must verify before tamper");
    // Flip one byte of the committed preprocessed root.
    proof.stark_proof.0.commitments[0].0[0] ^= 1;
    assert!(
        verify_mldsa(&proof).is_err(),
        "tampered preprocessed root must reject at the pin (not just constraints)"
    );
}

// =====================================================================
// Numbers (ignored): cells, perms, prove/verify ms, proof bytes.
// =====================================================================

#[test]
#[ignore]
fn composed_numbers() {
    use std::time::Instant;

    let msg = big_msg("numbers", 1024);
    let (w, input) = witness_and_input(9001, &msg);

    // Total committed M31 cells = Σ over layout() (preprocessed + trace +
    // interaction) of 2^log_size per column. Recompute via the public layout by
    // instrumenting through a prove + inspecting the proof's tree sizes is not
    // exposed, so we sum from the reconstructed layout below via a dry probe.
    let t0 = Instant::now();
    let proof = prove_mldsa(w.clone(), input.clone(), pcs_config()).expect("prove");
    let prove_ms = t0.elapsed().as_millis();

    let t1 = Instant::now();
    verify_mldsa(&proof).expect("verify");
    let verify_ms = t1.elapsed().as_millis();

    // Perm count (µ + c̃ + SIB permutations).
    let plan_perms = {
        // Reproduce the sponge shapes to count perms.
        let mu_absorb = w.sponge.mu_absorbed.len();
        let ct_absorb = w.sponge.c_tilde_absorbed.len();
        let sib_absorb = w.sponge.sample_in_ball_absorbed.len();
        // n_absorb = ceil((L+1)/136); n_perms = n_absorb + n_squeeze - 1.
        let n_absorb = |l: usize| (l + 1).div_ceil(136);
        let sib_stream = proof.sib_stream_len;
        let n_sq_sib = sib_stream.div_ceil(136).max(1);
        (n_absorb(mu_absorb) + 1 - 1)
            + (n_absorb(ct_absorb) + 1 - 1)
            + (n_absorb(sib_absorb) + n_sq_sib - 1)
    };

    // Total cells from the serialized proof structure is not directly a cell
    // count; report the committed-column cell total via the layout probe.
    let cells = total_committed_cells(&input, proof.sib_stream_len, proof.sib_squeezed_len);

    // Proof bytes = bincode(stark_proof) + the statement fields.
    let stark_bytes = bincode::serialize(&proof.stark_proof)
        .expect("bincode stark")
        .len();
    let full_bytes = bincode::serialize(&proof).expect("bincode proof").len();

    println!("=== composed_numbers ===");
    println!("message_len       : {}", msg.len());
    println!("sib_stream_len    : {}", proof.sib_stream_len);
    println!("total M31 cells   : {cells}");
    println!("perm count        : {plan_perms}");
    println!("prove ms          : {prove_ms}");
    println!("verify ms         : {verify_ms}");
    println!("stark_proof bytes : {stark_bytes}");
    println!("full proof bytes  : {full_bytes}");
}

/// Sum 2^log_size over every committed column (preprocessed + trace +
/// interaction) via the public statement layout.
fn total_committed_cells(
    input: &MlDsaVerifyInput,
    sib_stream_len: usize,
    sib_squeezed_len: usize,
) -> u64 {
    let layout = stwo_mldsa::statement::debug_layout(input, sib_stream_len, sib_squeezed_len);
    layout
        .preprocessed
        .iter()
        .chain(layout.trace.iter())
        .chain(layout.interaction.iter())
        .map(|&ls| 1u64 << ls)
        .sum()
}
