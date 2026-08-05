//! Prove → verify round-trip tests for the standalone SHA-256 component.
//!
//! Each test in this file exercises the full pipeline end-to-end:
//!
//! - The six-component composition: the main SHA evaluator, the digest
//!   bridge, and four `Range_k` producers.
//! - The preprocessed-trace commitment (15 columns).
//! - The base-trace commitment: `Layout::TOTAL_COLS` main columns, 32 digest
//!   bridge columns, and four producer multiplicity columns.
//! - The LogUp interaction trace across every component, with
//!   consumer ⇄ producer sums totalling zero — the soundness backbone.
//! - The Blake2s channel + PCS commitment scheme + FRI proof flow.
//! - The Sha256VerifyError surface (the soundness gate that catches a
//!   non-zero claimed-sum total).
//!
//! These are the slowest tests in the suite because they build real release
//! STARK proofs. Marked `#[ignore]` so `cargo test` stays quick; run
//! explicitly with `cargo test -p stwo-sha256 --release
//! prove_verify_round_trip -- --ignored`.

use stwo_sha256::stark::{
    build_trace_for, native_digest, prove_sha256, prove_sha256_from_witness, public_inputs_for,
    verify_sha256_proof, ProverConfig,
};
use stwo_sha256::trace::min_log_size;
use stwo_sha256::witness::compute_sha256_witness;

type BaseTrace = Vec<
    stwo::prover::poly::circle::CircleEvaluation<
        stwo::prover::backend::simd::SimdBackend,
        stwo::core::fields::m31::BaseField,
        stwo::prover::poly::BitReversedOrder,
    >,
>;

/// Prove and verify with a base trace built from `witness` at `log_n_rows`,
/// mutated by `mutate` before it is committed. Returns `Ok(())` only if
/// BOTH prove and verify succeed; any failure in either phase is folded
/// into a single `Err` so callers can assert "the pipeline rejects this"
/// without caring which phase caught it.
///
/// Used by the C10 alias adversarial tests below, which plant a cell no
/// witness-level mutation can reach (`is_last_block` outside its true row,
/// an enabler prefix that isn't block-aligned) — `Sha256Prover::with_base`
/// (test-only, `#[doc(hidden)]`) is the only entry point that accepts a
/// pre-built, hand-mutated trace instead of regenerating one from the
/// witness.
fn prove_and_verify_mutated_base(
    witness: &stwo_sha256::types::Sha256Witness,
    log_n_rows: u32,
    mutate: impl FnOnce(&mut BaseTrace),
) -> Result<(), String> {
    use stwo_sha256::air::{build_base_trace, Sha256Prover, Sha256Verifier};
    use stwo_sha256::field_exposure::FieldExposure;

    let mut base = build_base_trace(witness, log_n_rows, &FieldExposure::empty(), true);
    mutate(&mut base);

    let mut prover = Sha256Prover::new(witness, log_n_rows).with_base(base);
    let pcs_config = ProverConfig::default().pcs_config;
    let stark_proof = match air_core::prove(&mut [&mut prover], pcs_config) {
        Err(e) => return Err(format!("prove rejected: {e:?}")),
        Ok(proof) => proof,
    };
    let interaction_claim = prover.interaction_claim().clone();
    let mut verifier = Sha256Verifier::new(log_n_rows, interaction_claim);
    match air_core::verify(&mut [&mut verifier], &stark_proof) {
        Err(e) => Err(format!("verify rejected: {e:?}")),
        Ok(()) => Ok(()),
    }
}

/// Build a `ProverConfig` whose `log_n_rows` is the smallest value that
/// fits `n_blocks` padded blocks (and at least the SIMD floor).
fn config_for(n_blocks: usize) -> ProverConfig {
    ProverConfig {
        log_n_rows: min_log_size(n_blocks),
        ..ProverConfig::default()
    }
}

/// Run prove + verify on `msg` and assert success and digest agreement
/// with the native reference. Returns the `n_blocks` count for callers
/// to spot-check the padded shape.
fn prove_and_verify(msg: &[u8]) -> usize {
    let witness = compute_sha256_witness(msg);
    let config = config_for(witness.blocks.len());
    let proof = prove_sha256(msg, &config).expect("prove_sha256");
    assert_eq!(proof.digest, native_digest(msg).0);
    assert_eq!(proof.n_blocks, witness.blocks.len());
    verify_sha256_proof(&proof).expect("verify_sha256_proof");
    proof.n_blocks
}

/// FIPS 180-4 Appendix B.1 test vector — single padded block.
#[ignore = "slow: builds a real release STARK proof; run in release with --ignored"]
#[test]
fn prove_and_verify_abc() {
    assert_eq!(prove_and_verify(b"abc"), 1);
}

/// Multi-block round-trip — exercises the block-chain copy constraint,
/// the multi-block padding flag layout (marker block ≠ length block),
/// and the multi-block `Range_k` consumer lookups end-to-end. None of
/// these constraints fire on the single-block `b"abc"` case.
#[ignore = "slow: builds a real release STARK proof; run in release with --ignored"]
#[test]
fn prove_and_verify_multi_block() {
    // 200 bytes ⇒ 200 + 9 = 209 padding bytes ⇒ 4 padded blocks. The
    // last block is a length-only block (marker lives in block 3, length
    // in block 4); blocks 1..3 trigger the block-chain copy constraint.
    let n_blocks = prove_and_verify(&[0xABu8; 200]);
    assert!(n_blocks >= 2, "test message must span multiple blocks");
}

/// Long-message round-trip at log size 13.
///
/// This case checks cross-row masks and component allocation when the main
/// trace is much larger than the range tables and digest bridge.
#[ignore = "slow: builds a real release STARK proof; run in release with --ignored"]
#[test]
fn prove_and_verify_long_message() {
    // The message needs 65 padded blocks. Each block uses 67 rows. The
    // strictly larger trace domain has 8 192 rows, so its log size is 13.
    let n_blocks = prove_and_verify(&[0x55u8; 4096]);
    assert_eq!(min_log_size(n_blocks), 13);
}

/// Padding-boundary round-trips — every FIPS 180-4 §5.1.1 edge case that
/// changes the marker/length layout exercises a different P.* family of
/// padding constraints. These boundaries are covered at the witness and
/// trace layer but not at the end-to-end prove/verify boundary anywhere
/// else in the suite.
#[ignore = "slow: builds a real release STARK proof; run in release with --ignored"]
#[test]
fn prove_and_verify_padding_boundaries() {
    // Empty message — single marker+length block, marker at byte 0 of W[0].
    assert_eq!(prove_and_verify(b""), 1);
    // 55 bytes — last possible single-block message (55 + 1 marker + 8
    // length = 64). Marker sits at byte 55; length fills W[14]/W[15].
    assert_eq!(prove_and_verify(&[0x42u8; 55]), 1);
    // 56 bytes — first message that spills the length into a second
    // block. Block 0 carries the marker (no length); block 1 is
    // length-only (no marker).
    assert_eq!(prove_and_verify(&[0x42u8; 56]), 2);
    // 64 bytes — exactly one input block of preimage; padding occupies
    // a full second block (marker at W[0] byte 0, length in W[14]/W[15]).
    assert_eq!(prove_and_verify(&[0x42u8; 64]), 2);
}

/// `prove_sha256_from_witness` is publicly exposed so integration-stream
/// callers can supply a pre-built witness (e.g. coming from a credential
/// builder, not raw bytes). Pin the contract that it produces a proof
/// indistinguishable from `prove_sha256` on the same message.
#[ignore = "slow: builds a real release STARK proof; run in release with --ignored"]
#[test]
fn prove_sha256_from_witness_matches_prove_sha256() {
    let msg = b"abc";
    let witness = compute_sha256_witness(msg);
    let config = config_for(witness.blocks.len());

    let proof_from_witness =
        prove_sha256_from_witness(&witness, &config).expect("prove_sha256_from_witness");
    assert_eq!(proof_from_witness.digest, native_digest(msg).0);
    assert_eq!(proof_from_witness.n_blocks, witness.blocks.len());
    verify_sha256_proof(&proof_from_witness).expect("verify witness-built proof");

    // The public-input contract this proof carries must equal what
    // `public_inputs_for(msg)` predicts from the message alone — the
    // shared-contract invariant between the pre-prove and post-prove
    // entry points.
    assert_eq!(proof_from_witness.public_inputs(), public_inputs_for(msg));

    // The `build_trace_for` helper is another public entry point in the
    // same family; calling it here pins that it agrees with the witness
    // emitter on column count and witness shape.
    let (built_witness, trace) = build_trace_for(msg, &config).expect("build_trace_for");
    assert_eq!(built_witness.blocks.len(), witness.blocks.len());
    assert_eq!(
        trace.len(),
        stwo_sha256::trace::Layout::TOTAL_COLS,
        "build_trace_for column count"
    );
}

/// Negative half of the closure: mutating the proof's claimed-sum
/// surface to a non-zero total trips the `LogupSumNonZero` gate before
/// the Stwo verifier even runs. Pins the soundness-backbone check.
#[ignore = "slow: produces a real proof first; same cost as prove_and_verify_abc"]
#[test]
fn verify_rejects_logup_sum_mutation() {
    use num_traits::One;
    use stwo::core::fields::qm31::SecureField;
    use stwo_sha256::stark::Sha256VerifyError;

    let msg = b"abc";
    let config = ProverConfig::default();
    let mut proof = prove_sha256(msg, &config).expect("prove_sha256 on b\"abc\"");

    // Bump one of the producer-side claimed sums by 1. The total now
    // differs from zero by 1, so the soundness gate catches it.
    proof.interaction_claim.range[0].claimed_sum += SecureField::one();

    match verify_sha256_proof(&proof) {
        Err(Sha256VerifyError::LogupSumNonZero) => {}
        other => panic!("expected LogupSumNonZero, got {other:?}"),
    }
}

/// A witness that violates the AIR carry bounds cannot produce an accepted
/// proof.
///
/// Bumps the last block's finalization-add carry on word 7 from its
/// honest value (`< 2`, since finalization is a 2-addend add) to `5` —
/// outside the `Range_2` bound the AIR's carry range-check enforces.
/// The mutation simultaneously breaks the mod-2³² linear identity
/// `h_in[7] + state[7] = h_out[7] + carry · 2¹⁶` and the `Range_2`
/// lookup soundness, so the system must reject at one of:
///   - the prover's constraint-vanishing check (`Sha256ProveError::StwoProveFailed`), or
///   - the verifier's downstream gate (any `Sha256VerifyError` variant).
///
/// This complements
/// [`verify_rejects_range_k_claimed_sum_mutations`]: that test mutates
/// the *proof* to isolate the `Range_k` LogUp loop; this one mutates the
/// *witness* end-to-end.
#[ignore = "slow: builds a real release STARK proof; run in release with --ignored"]
#[test]
fn rejects_out_of_range_carry_witness_mutation() {
    let msg = b"abc";
    let mut witness = compute_sha256_witness(msg);
    let last = witness.blocks.last_mut().expect("at least one block");
    last.finalization_carries[7].lo = 5;

    let config = config_for(witness.blocks.len());
    // The prover can reject the witness, or the verifier can reject the proof.
    match prove_sha256_from_witness(&witness, &config) {
        Err(_) => {} // prover caught it — pass
        Ok(proof) => {
            verify_sha256_proof(&proof)
                .expect_err("verifier must reject a proof from an out-of-range-carry witness");
        }
    }
}

/// Carry-out-of-range soundness coverage for the four `Range_k`
/// channels (`Range_2`/`Range_4`/`Range_5`/`Range_8`). Bumping any one
/// producer's claimed sum makes the per-component sums no longer total zero,
/// so the `LogupSumNonZero` gate rejects.
///
/// **Why this is the meaningful test rather than a witness-mutation
/// prove-and-reject:** an out-of-range carry that *also* keeps the
/// mod-2³² linear identity satisfied requires cascading edits to the
/// downstream `e_new`/`a_new`/finalization cells that consume it. The
/// soundness-gate test isolates the `Range_k` LogUp loop without that
/// cascade; the linear-path negative for carries is already covered by
/// `tests/constraint_negative.rs::rejects_swapped_carry_within_row`.
#[ignore = "slow: produces a real proof first; same cost as prove_and_verify_abc"]
#[test]
fn verify_rejects_range_k_claimed_sum_mutations() {
    use num_traits::One;
    use stwo::core::fields::qm31::SecureField;
    use stwo_sha256::stark::Sha256VerifyError;

    let msg = b"abc";
    let config = ProverConfig::default();
    let proof = prove_sha256(msg, &config).expect("prove_sha256 on b\"abc\"");

    // Sanity-check the baseline accepts before we exercise the four
    // range mutations.
    verify_sha256_proof(&proof).expect("baseline proof must verify");

    // For each of the four `Range_k` producers (indexes 0 through 3 correspond
    // to `RANGE_TABLES` order: Range_2, Range_4, Range_5, Range_8),
    // bump that producer's claimed sum and assert the soundness gate
    // rejects. Iterating in-place catches a regression on any one
    // channel.
    for kind_idx in 0..4 {
        let mut mutated = proof.clone();
        mutated.interaction_claim.range[kind_idx].claimed_sum += SecureField::one();
        match verify_sha256_proof(&mutated) {
            Err(Sha256VerifyError::LogupSumNonZero) => {}
            other => panic!(
                "Range channel #{kind_idx} mutation: expected LogupSumNonZero, got {other:?}"
            ),
        }
    }
}

/// Prove with the digest provider enabled.
///
/// The prover must accept the digest yield. The standalone verifier must
/// reject it because no consumer cancels the provider term.
#[ignore = "slow: produces a real proof first; same cost as prove_and_verify_abc"]
#[test]
fn digest_provider_proof_is_unbalanced_without_consumer() {
    use num_traits::Zero;
    use stwo::core::fields::qm31::SecureField;
    use stwo_sha256::air::{Sha256Prover, Sha256Verifier};

    let witness = compute_sha256_witness(b"abc");
    let config = config_for(witness.blocks.len());

    let mut prover = Sha256Prover::new(&witness, config.log_n_rows).with_digest_provider();
    let stark_proof = air_core::prove(&mut [&mut prover], config.pcs_config)
        .expect("prove with digest provider must succeed");
    let interaction_claim = prover.interaction_claim().clone();

    // (1) The exposed digest leaves the module's claimed sums unbalanced.
    assert_ne!(
        interaction_claim.total(),
        SecureField::zero(),
        "exposing the digest must leave an outstanding provider term",
    );

    // (2) The verifier's global LogUp balance check rejects it.
    let mut verifier =
        Sha256Verifier::new(config.log_n_rows, interaction_claim).with_digest_provider();
    assert!(
        air_core::verify(&mut [&mut verifier], &stark_proof).is_err(),
        "an unbalanced digest yield (no consumer) must fail verification",
    );
}

/// Sanity baseline for [`prove_and_verify_mutated_base`]: rebuilding the
/// base trace via `build_base_trace` and feeding it back unmutated through
/// `with_base` must reproduce an ordinary honest proof. If this fails, the
/// t1/t6 rejections below would be meaningless (they could be rejecting
/// the plumbing, not the mutation).
#[ignore = "slow: builds a real release STARK proof; run in release with --ignored"]
#[test]
fn with_base_roundtrip_matches_honest_proof_when_unmutated() {
    let witness = compute_sha256_witness(b"abc");
    let log_n_rows = config_for(witness.blocks.len()).log_n_rows;
    prove_and_verify_mutated_base(&witness, log_n_rows, |_base| {})
        .expect("unmutated with_base round trip must succeed");
}

/// t1 (C10 alias adversarial plan): planting `is_last_block = 1` at a
/// `t = 15` row must reject through the real prove/verify pipeline, not
/// just the hand-rolled `constraint_negative` evaluator — `is_last_block`
/// is never aliased (`crate::trace::Layout::COL_IS_LAST_BLOCK` keeps its
/// own column precisely to close the digest-substitution attack this
/// tests), and its cross-relation consequence (the digest LogUp yield at
/// the wrong row, against an interaction trace built from the honest
/// witness) can only be exercised by a real STARK proof —
/// `tests/constraint_negative.rs`'s collector no-ops `add_to_relation`
/// (file-level docs, `:214-227`) and cannot see it.
#[ignore = "slow: builds a real release STARK proof; run in release with --ignored"]
#[test]
fn verify_rejects_is_last_block_planted_at_round_15() {
    use stwo::core::fields::m31::BaseField;
    use stwo::prover::backend::Column;
    use stwo_sha256::trace::Layout;

    let witness = compute_sha256_witness(b"abc");
    let log_n_rows = config_for(witness.blocks.len()).log_n_rows;
    let slot = Layout::round_row_slot(0, 15, log_n_rows);

    let result = prove_and_verify_mutated_base(&witness, log_n_rows, |base| {
        base[Layout::COL_IS_LAST_BLOCK]
            .values
            .set(slot, BaseField::from(1u32));
    });
    assert!(
        result.is_err(),
        "planting is_last_block = 1 at a t = 15 row must reject (prove or verify), got Ok",
    );
}

/// t6 (C10 alias adversarial plan): an enabler prefix whose length is not
/// a multiple of `ROWS_PER_BLOCK = 67` (here, one extra enabled row past
/// the true final block) must fail verification — `is_last_block`'s
/// defining equality `enabler · is_round_63 · (1 − enabler_next)` no
/// longer identifies the true completion row once `enabler_next` at the
/// real `t = 63` row flips to 1, so no row yields a digest and the digest
/// bridge (which always expects exactly one) cannot balance. Requires the
/// real pipeline for the same reason as t1: the failure surfaces through
/// relation/interaction-trace consistency, not a local polynomial identity
/// `constraint_negative`'s collector can see.
#[ignore = "slow: builds a real release STARK proof; run in release with --ignored"]
#[test]
fn verify_rejects_enabler_prefix_not_block_aligned() {
    use stwo::core::fields::m31::BaseField;
    use stwo::prover::backend::Column;
    use stwo_sha256::trace::Layout;

    let witness = compute_sha256_witness(b"abc"); // 1 block, 67 real rows.
    assert_eq!(witness.blocks.len(), 1);
    let log_n_rows = config_for(witness.blocks.len()).log_n_rows;
    // First padding row (natural row 67, block 1's seed row 0) — enabling
    // it makes the enabled-row count 68 ≢ 0 (mod 67).
    let extra_row_natural = stwo_sha256::trace::ROWS_PER_BLOCK;
    let slot = Layout::row_slot(extra_row_natural, log_n_rows);

    let result = prove_and_verify_mutated_base(&witness, log_n_rows, |base| {
        base[Layout::COL_ENABLER]
            .values
            .set(slot, BaseField::from(1u32));
    });
    assert!(
        result.is_err(),
        "an enabler prefix not aligned to ROWS_PER_BLOCK must reject (prove or verify), got Ok",
    );
}

/// Prove with the complete padded message stream exposed.
///
/// The prover must accept the field yields. The standalone verifier must
/// reject them because no consumer cancels the provider terms.
#[ignore = "slow: produces a real proof first; same cost as prove_and_verify_abc"]
#[test]
fn full_padded_stream_provider_proof_is_unbalanced_without_consumer() {
    use num_traits::Zero;
    use stwo::core::fields::qm31::SecureField;
    use stwo_sha256::air::{Sha256Prover, Sha256Verifier};
    use stwo_sha256::field_exposure::FieldExposure;

    let message: Vec<u8> = (0..70).map(|i| (i * 13 + 7) as u8).collect();
    let witness = compute_sha256_witness(&message);
    assert_eq!(witness.blocks.len(), 2);
    let exposure = FieldExposure::from_full_padded_stream(77, witness.padding.padded.len());
    let config = config_for(witness.blocks.len());

    let mut prover =
        Sha256Prover::new(&witness, config.log_n_rows).with_field_provider(exposure.clone());
    let stark_proof = air_core::prove(&mut [&mut prover], config.pcs_config)
        .expect("prove with full padded-stream provider");
    let interaction_claim = prover.interaction_claim().clone();
    assert_ne!(
        interaction_claim.total(),
        SecureField::zero(),
        "stream provider must leave outstanding field terms",
    );

    let mut verifier =
        Sha256Verifier::new(config.log_n_rows, interaction_claim).with_field_provider(exposure);
    assert!(
        air_core::verify(&mut [&mut verifier], &stark_proof).is_err(),
        "an unconsumed full padded-stream provider must fail global balance",
    );
}
