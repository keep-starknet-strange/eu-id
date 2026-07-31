//! Standalone proof and verification tests for `sampleinball_fsm`.
//!
//! The tests use at least 20 oracle ML-DSA-65 signatures and adversarial
//! mutations. A HashIo producer and a CCell provider balance the squeeze stream
//! and coefficient C cells in this standalone test. The composed statement
//! uses the proven sponge and coefficient C group.

mod common;

use common::{standalone_pcs_config as pcs_config, witness_for};

use stwo_mldsa::sampleinball::proof::{prove_sib, verify_sib};
use stwo_mldsa::witness::MlDsaWitness;

/// A witness mutation is REJECTED if proving fails/panics or verify fails.
fn rejected(witness: MlDsaWitness) -> bool {
    let w2 = witness.clone();
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        match prove_sib(witness, pcs_config()) {
            Ok(proof) => verify_sib(&proof, &w2, pcs_config()).is_err(),
            Err(_) => true,
        }
    }));
    r.unwrap_or(true)
}

// =====================================================================
// Positive.
// =====================================================================

#[test]
fn sib_proves_and_verifies_over_20_signatures() {
    let mut ok = 0;
    for i in 0..20u64 {
        let msg = format!("mldsa-sib-case-{i}").into_bytes();
        let w = witness_for(7000 + i, &msg);
        let proof = prove_sib(w.clone(), pcs_config()).expect("prove");
        verify_sib(&proof, &w, pcs_config())
            .unwrap_or_else(|e| panic!("case {i}: verify failed: {e:?}"));
        ok += 1;
    }
    assert_eq!(ok, 20);
}

#[test]
fn sib_rejects_proof_under_different_pcs_policy() {
    let w = witness_for(7999, b"pcs-policy");
    let proof = prove_sib(w.clone(), pcs_config()).expect("prove");
    let mut wrong = pcs_config();
    wrong.pow_bits += 1;
    assert!(
        verify_sib(&proof, &w, wrong).is_err(),
        "a proof must not select its own PCS policy"
    );
}

/// Control: the negatives' seeds prove+verify cleanly without mutation.
#[test]
fn sib_seeds_honest_without_mutation() {
    for (seed, msg) in [
        (8001u64, &b"tau"[..]),
        (8002, b"c-bind"),
        (8003, b"rej"),
        (8007, b"sign-decomposition"),
        (8008, b"index-progression"),
        (8009, b"sorted-classification"),
    ] {
        let w = witness_for(seed, msg);
        let proof = prove_sib(w.clone(), pcs_config())
            .unwrap_or_else(|e| panic!("seed {seed}: honest prove failed: {e:?}"));
        verify_sib(&proof, &w, pcs_config())
            .unwrap_or_else(|e| panic!("seed {seed}: honest verify failed: {e:?}"));
    }
}

// =====================================================================
// Negatives.
// =====================================================================

/// c with τ+2 nonzeros: add two extra ±1 to c → Σc² = τ+2 ≠ τ, the accumulator
/// gate rejects (and the c-binding to coeffs breaks).
#[test]
fn negative_c_extra_nonzeros() {
    let mut w = witness_for(8001, b"tau");
    // Find two zero positions and set them to +1.
    let mut set = 0;
    for m in 0..stwo_mldsa::constants::N {
        if w.digits.c[m] == 0 {
            w.digits.c[m] = 1;
            set += 1;
            if set == 2 {
                break;
            }
        }
    }
    assert_eq!(set, 2);
    assert!(rejected(w), "c with τ+2 nonzeros must be rejected");
}

/// c-binding tamper: corrupt the emitted `ccell_claimed_sum` so the c-binding
/// logup no longer cancels. (In standalone the ccell provider reads the same
/// witness `c` as the FSM, so a witness-level c change moves both sides together;
/// The composed statement makes coeffs the independent producer. This test changes the proof directly,
/// proving the c-binding is load-bearing.)
#[test]
fn negative_c_binding_tamper() {
    let w = witness_for(8002, b"c-bind");
    let mut proof = prove_sib(w.clone(), pcs_config()).expect("prove");
    proof.ccell_claimed_sum += stwo::core::fields::qm31::SecureField::from(
        stwo::core::fields::m31::M31::from_u32_unchecked(1),
    );
    assert!(
        verify_sib(&proof, &w, pcs_config()).is_err(),
        "a broken c-binding balance must be rejected"
    );
}

/// Stream tamper: corrupt the emitted `hashio_claimed_sum` so the stream-consume
/// logup no longer cancels — the FSM's byte-by-byte stream binding is load-
/// bearing. (A witness-level stream edit is re-derived consistently by both the
/// FSM and the test producer; the composed statement uses the proven sponge.)
#[test]
fn negative_stream_binding_tamper() {
    let w = witness_for(8003, b"rej");
    let mut proof = prove_sib(w.clone(), pcs_config()).expect("prove");
    proof.hashio_claimed_sum += stwo::core::fields::qm31::SecureField::from(
        stwo::core::fields::m31::M31::from_u32_unchecked(1),
    );
    assert!(
        verify_sib(&proof, &w, pcs_config()).is_err(),
        "a broken stream-consume balance must be rejected"
    );
}

/// c placed at a rejected index (τ+1 nonzeros): set one extra c to −1 → Σc² =
/// τ+1 ≠ τ, rejected by the accumulator gate (distinct path from the +2 test).
#[test]
fn negative_c_one_extra_nonzero() {
    let mut w = witness_for(8004, b"one-extra");
    for m in 0..stwo_mldsa::constants::N {
        if w.digits.c[m] == 0 {
            w.digits.c[m] = -1;
            break;
        }
    }
    assert!(
        rejected(w),
        "c with τ+1 nonzeros must be rejected by the Σc²=τ gate"
    );
}

/// PLACEMENT PERMUTATION (the swap-replay hole). Move a ±1 from a slot where
/// SampleInBall placed it to a slot it never placed one, keeping the multiset of
/// ±1 values, the support size, AND Σc² = τ all UNCHANGED. Σc² stays τ (we swap a
/// nonzero with a zero, count preserved), the ternary/support checks stay green,
/// and the c-binding still cancels (standalone ccell provider reads the same
/// mutated `c`). ONLY the offline-memory (Mem) swap-replay can catch it: the
/// replay derives the true placement from the UNCHANGED squeeze stream, so the
/// SORTED view carries the true final array while the FINAL-read (+) emits the
/// committed permuted `c` — the internal Mem multiset no longer balances ⇒ reject.
#[test]
fn negative_placement_permuted() {
    let mut w = witness_for(8005, b"placement");
    // Find p<q with c[p] nonzero and c[q]==0, then SWAP (move the ±1 to q).
    let n = stwo_mldsa::constants::N;
    let p = (0..n)
        .find(|&m| w.digits.c[m] != 0)
        .expect("a nonzero coeff");
    let q = (0..n).find(|&m| w.digits.c[m] == 0).expect("a zero coeff");
    assert_ne!(p, q);
    let moved = w.digits.c[p];
    w.digits.c[p] = 0;
    w.digits.c[q] = moved;
    // Σc² is unchanged (still exactly τ nonzeros): confirm the gate that catches
    // this is the Mem replay, not the accumulator.
    let sumsq: i128 = w.digits.c.iter().map(|&x| x * x).sum();
    assert_eq!(
        sumsq as usize,
        stwo_mldsa::constants::TAU,
        "Σc² must stay τ"
    );
    assert!(
        rejected(w),
        "a placement permutation must be rejected by the Mem swap-replay gate"
    );
}

/// Inject a forged core access list through the test hook. The
/// Swap, StepVal, and SignBit channels must bind the unsorted core columns to
/// the FSM and reject a memory-consistent but incorrect history.
///
/// The forged list passes the sorted-view continuity check and reaches the same
/// final array as the committed `c`. It redirects the first read to a different
/// zero cell, so `(step_no, u_addr)` does not match `(idx−(N−τ), byte)`. The
/// Swap channel must reject it.
#[test]
fn negative_forged_access_list() {
    use stwo_mldsa::sampleinball::{honest_core_accesses, install_forged_core};

    let w = witness_for(8006, b"forged-access");
    // Honest core list: N init writes (addr=k,val=0,ts=k), then per step
    // read/write-i/write-j. Index N is step 0's READ: (j_0, old_j=0, ts=N, read).
    let mut core = honest_core_accesses(&w);
    let n = stwo_mldsa::constants::N as u32;
    let (j0, val0, _ts0, is_write0) = core[stwo_mldsa::constants::N];
    assert!(!is_write0, "index N must be step 0's read");
    assert_eq!(val0, 0, "step 0 reads a still-zero cell (old_j = 0)");
    // Redirect the read to a DIFFERENT still-zero address (any cell is 0 at ts=N,
    // only inits have run) — value stays 0, final array + Mem balance unchanged.
    let k = (j0 + 1) % n;
    assert_ne!(k, j0);
    core[stwo_mldsa::constants::N].0 = k;

    // Sanity: the honest witness proves+verifies WITHOUT the forgery installed.
    let honest = prove_sib(w.clone(), pcs_config()).expect("honest prove");
    verify_sib(&honest, &w, pcs_config()).expect("honest verify");

    // Install the forgery and assert prove+verify REJECTS (Swap channel imbalance).
    let guard = install_forged_core(core);
    let forged_rejected =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            match prove_sib(w.clone(), pcs_config()) {
                Ok(proof) => verify_sib(&proof, &w, pcs_config()).is_err(),
                Err(_) => true,
            }
        }))
        .unwrap_or(true);
    drop(guard);
    assert!(
        forged_rejected,
        "a forged (FSM-mismatched) core access list must be rejected by the Swap channel"
    );
}

/// The sign-bit columns must be the little-endian decomposition of the eight
/// HashIo-bound sign bytes. Flip one decomposed bit while leaving the stream and
/// memory replay honest: byte recomposition and SignBit balance must reject it.
#[test]
fn negative_wrong_sign_decomposition() {
    use stwo_mldsa::sampleinball::install_forged_sign_bytes;

    let w = witness_for(8007, b"sign-decomposition");
    let mut sign_bytes: [u8; 8] = w.sponge.sample_in_ball_squeezed[..8]
        .try_into()
        .expect("eight sign bytes");
    sign_bytes[0] ^= 1;

    let guard = install_forged_sign_bytes(sign_bytes);
    let forged_rejected = rejected(w);
    drop(guard);
    assert!(
        forged_rejected,
        "sign-bit columns inconsistent with the HashIo-bound byte must be rejected"
    );
}

/// Every placement row must start at the preceding stream row's state-after
/// value. Corrupt the final sign row's state while keeping every byte, accept
/// bit, and lookup tuple otherwise self-consistent; the ordered FSM must reject.
#[test]
fn negative_wrong_index_progression() {
    use stwo_mldsa::sampleinball::{honest_stream_rows, install_forged_stream_indices};

    let w = witness_for(8008, b"index-progression");
    let mut indices: Vec<u32> = honest_stream_rows(&w)
        .into_iter()
        .map(|(_, index, _)| index)
        .collect();
    indices[7] += 1;

    let guard = install_forged_stream_indices(indices);
    let forged_rejected = rejected(w);
    drop(guard);
    assert!(
        forged_rejected,
        "a discontinuous SampleInBall index history must be rejected"
    );
}

/// The active prefix cannot stop before the 49th accepted placement. Turning
/// off its final active row leaves `i < 256`, violating the inactive-state pin.
#[test]
fn negative_active_prefix_stops_early() {
    use stwo_mldsa::sampleinball::{honest_active_rows, install_forged_active};

    let w = witness_for(8010, b"active-boundary");
    let mut active = honest_active_rows(&w);
    let padding_start = active
        .iter()
        .position(|&value| !value)
        .expect("five-block stream has padding");
    active[padding_start - 1] = false;

    let guard = install_forged_active(active);
    let forged_rejected = rejected(w);
    drop(guard);
    assert!(
        forged_rejected,
        "the active prefix must extend through the 49th accepted placement"
    );
}

/// Once the FSM reaches `i = 256`, padding cannot reactivate consumption.
/// Re-enabling the first padding row without another accept breaks the active
/// placement partition; fabricating an extra accept would instead break the
/// fixed 49-step Swap balance.
#[test]
fn active_prefix_cannot_restart_after_the_final_accept() {
    use stwo_mldsa::sampleinball::{honest_active_rows, install_forged_active};

    let w = witness_for(8011, b"active-reactivation");
    let mut active = honest_active_rows(&w);
    let padding_start = active
        .iter()
        .position(|&value| !value)
        .expect("five-block stream has padding");
    active[padding_start] = true;

    let guard = install_forged_active(active);
    let forged_rejected = rejected(w);
    drop(guard);
    assert!(
        forged_rejected,
        "consumption must not reactivate after the 49th accept"
    );
}

/// A mutation in the unconsumed witness tail does not move
/// the FSM boundary: the static component and Keccak producer both derive and
/// bind the canonical five-block stream from the SIB absorb input.
#[test]
fn unconsumed_witness_tail_does_not_move_the_fsm_boundary() {
    let mut w = witness_for(8012, b"padding-byte");
    let padding_start = stwo_mldsa::sampleinball::validate_stream(&w).expect("valid stream");
    assert!(padding_start < w.sponge.sample_in_ball_squeezed.len());
    w.sponge.sample_in_ball_squeezed[padding_start] ^= 1;

    let proof = prove_sib(w.clone(), pcs_config()).expect("padding is outside consumption");
    verify_sib(&proof, &w, pcs_config())
        .expect("unconsumed bytes cannot shift the constrained prefix");
}

/// An oversized witness returns a typed error before trace allocation.
#[test]
fn over_five_blocks_is_typed_error_not_panic() {
    let mut w = witness_for(8013, b"resource-cap");
    w.sponge
        .sample_in_ball_squeezed
        .resize(stwo_mldsa::sampleinball::MAX_SIB_SQUEEZE_BYTES + 1, 0);

    let validation = std::panic::catch_unwind(|| stwo_mldsa::sampleinball::validate_stream(&w));
    assert!(matches!(validation, Ok(Err(_))));
    let proving =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| prove_sib(w, pcs_config())));
    assert!(matches!(proving, Ok(Err(_))));
}

/// The memory permutation tuple must bind read/write classification. Relabel a
/// sorted read as a write without changing its address, value, or timestamp;
/// this used to disable read continuity when `MemRelation` omitted `is_write`.
#[test]
fn negative_sorted_read_write_reclassification() {
    use stwo_mldsa::sampleinball::{honest_sorted_accesses, install_forged_sorted_writes};

    let w = witness_for(8009, b"sorted-classification");
    let sorted = honest_sorted_accesses(&w);
    let mut writes: Vec<bool> = sorted.iter().map(|access| access.3).collect();
    let read = sorted
        .iter()
        .enumerate()
        .find(|(row, access)| *row > 0 && !access.3 && access.0 == sorted[*row - 1].0)
        .map(|(row, _)| row)
        .expect("a non-initial sorted read");
    writes[read] = true;

    let guard = install_forged_sorted_writes(writes);
    let forged_rejected = rejected(w);
    drop(guard);
    assert!(
        forged_rejected,
        "sorted read/write reclassification must break the Mem permutation"
    );
}
