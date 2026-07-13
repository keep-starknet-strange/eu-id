//! Prove → verify round-trip tests for the standalone SHA-256 component.
//!
//! Each test in this file exercises the full pipeline end-to-end:
//!
//! - The entire 23-component composition (`Sha256Eval` consumer +
//!   8 σ/Σ decode producers + 1 packed Maj/Ch + 1 xor_8 + 4 round
//!   split-pack + 4 σ split-pack + 4 `Range_k` producers).
//! - The preprocessed-trace commitment (85 columns at W=6).
//! - The base-trace commitment (`Layout::TOTAL_COLS` SHA-256 columns +
//!   23 producer multiplicity columns).
//! - The LogUp interaction trace across every component, with
//!   consumer ⇄ producer sums totalling zero — the soundness backbone.
//! - The Blake2s channel + PCS commitment scheme + FRI proof flow.
//! - The Sha256VerifyError surface (the soundness gate that catches a
//!   non-zero claimed-sum total).
//!
//! These are the slowest tests in the suite — the packed Maj/Ch table is
//! 2¹⁸ rows (W=6), so the preprocessed trace generation and commitment
//! dominate. Marked `#[ignore]` so `cargo test` stays quick; run
//! explicitly with `cargo test -p stwo-sha256 --release
//! prove_verify_round_trip -- --ignored`.

use stwo_sha256::stark::{
    build_trace_for, native_digest, prove_sha256, prove_sha256_from_witness, public_inputs_for,
    verify_sha256_proof, ProverConfig,
};
use stwo_sha256::trace::min_log_size;
use stwo_sha256::witness::compute_sha256_witness;

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
#[ignore = "slow: 2^18-row Maj/Ch preprocessed trace dominates; run in release with --ignored"]
#[test]
fn prove_and_verify_abc() {
    assert_eq!(prove_and_verify(b"abc"), 1);
}

/// Multi-block round-trip — exercises the §10.3 chain copy constraint,
/// the multi-block padding flag layout (marker block ≠ length block),
/// and the multi-block `Range_k` consumer lookups end-to-end. None of
/// these constraints fire on the single-block `b"abc"` case.
#[ignore = "slow: 2^18-row Maj/Ch preprocessed trace dominates; run in release with --ignored"]
#[test]
fn prove_and_verify_multi_block() {
    // 200 bytes ⇒ 200 + 9 = 209 padding bytes ⇒ 4 padded blocks. The
    // last block is a length-only block (marker lives in block 3, length
    // in block 4); blocks 1..3 trigger the §10.3 chain copy constraint.
    let n_blocks = prove_and_verify(&[0xABu8; 200]);
    assert!(n_blocks >= 2, "test message must span multiple blocks");
}

/// Long-message round-trip — the only end-to-end test whose SHA-256
/// component trace exceeds the SIMD floor (`log_n_rows > LOG_N_LANES`).
///
/// All other round-trip tests fit inside `2^LOG_N_LANES = 16` rows so they
/// run at the SIMD minimum. A regression that only fires past the floor
/// — for example, a cross-row mask computation that mis-handles the
/// `bit_reverse_index` walk when `log_n_rows ≠ LOG_N_LANES`, or a
/// component allocator that mis-orders preprocessed IDs when the SHA-256
/// component is larger than the smaller producer tables — would slip
/// through the other coverage. A 4 096-byte message produces ~65 padded
/// blocks ⇒ `log_n_rows = 7`, three bits above the floor.
#[ignore = "slow: 2^18-row Maj/Ch preprocessed trace dominates; run in release with --ignored"]
#[test]
fn prove_and_verify_long_message() {
    // 4 096 bytes ⇒ 4 096 + 9 = 4 105 padding bytes ⇒ ceil(4 105 / 64) =
    // 65 padded blocks ⇒ min_log_size = 7 (next power of two ≥ 65 is 128).
    let n_blocks = prove_and_verify(&[0x55u8; 4096]);
    // SIMD floor is `LOG_N_LANES = 4`. `min_log_size` clamps to that
    // floor, so a strict inequality pins that this message genuinely
    // exceeds the floor rather than being clamped up to it.
    const SIMD_FLOOR_LOG: u32 = 4;
    assert!(
        min_log_size(n_blocks) > SIMD_FLOOR_LOG,
        "long-message test must exceed the SIMD-floor log size (n_blocks = {n_blocks})",
    );
}

/// Padding-boundary round-trips — every FIPS 180-4 §5.1.1 edge case that
/// changes the marker/length layout exercises a different P.* family of
/// padding constraints. These boundaries are covered at the witness and
/// trace layer but not at the end-to-end prove/verify boundary anywhere
/// else in the suite.
#[ignore = "slow: 2^18-row Maj/Ch preprocessed trace dominates; run in release with --ignored"]
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
#[ignore = "slow: 2^18-row Maj/Ch preprocessed trace dominates; run in release with --ignored"]
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

/// Audit-lesson L4 closure: a witness that violates the AIR's documented
/// bounds cannot produce an accepted proof.
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
/// This is the complementary half of
/// [`verify_rejects_range_k_claimed_sum_mutations`]: that test mutates
/// the *proof* to isolate the `Range_k` LogUp loop; this one mutates the
/// *witness* end-to-end. Together they cover the L4 audit lesson from
/// both directions.
#[ignore = "slow: 2^18-row Maj/Ch preprocessed trace dominates; run in release with --ignored"]
#[test]
fn rejects_out_of_range_carry_witness_mutation() {
    let msg = b"abc";
    let mut witness = compute_sha256_witness(msg);
    let last = witness.blocks.last_mut().expect("at least one block");
    last.finalization_carries[7].lo = 5;

    let config = config_for(witness.blocks.len());
    // Either the prover refuses to produce a proof, or the verifier
    // refuses to accept one. Both close L4; the *meaningful* failure
    // mode is "no accepted proof exists for this witness".
    match prove_sha256_from_witness(&witness, &config) {
        Err(_) => {} // prover caught it — pass
        Ok(proof) => {
            verify_sha256_proof(&proof)
                .expect_err("verifier must reject a proof from an out-of-range-carry witness");
        }
    }
}

/// Carry-out-of-range soundness coverage for the four new `Range_k`
/// channels (`Range_2`/`Range_4`/`Range_5`/`Range_16`). Each is verified
/// the same way as the `xor_8` channel in [`verify_rejects_logup_sum_mutation`]:
/// bumping any one producer's claimed sum makes the per-component sums no
/// longer total zero, so the `LogupSumNonZero` gate rejects.
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

    // For each of the four `Range_k` producers (index 0..4 corresponds
    // to `RANGE_TABLES` order: Range_2, Range_4, Range_5, Range_16),
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

/// Digest-provider producer-half end-to-end: prove the SHA module with the digest
/// provider **on** and confirm two things in a *real* proof (not just the
/// claimed-sum algebra the unit smoke test checks):
///
/// 1. The Stwo prover **accepts** the digest yield — its constraint is
///    satisfiable and degree ≤ 2, and the extra interaction column lines up
///    with the `add_to_relation` the AIR emits. A degree blow-up or a
///    provider/consumer tuple desync would fail here, at prove time.
/// 2. The verifier **rejects** the module on its own — the yield has no
///    consumer, so the `air_core` global LogUp balance is non-zero. This is
///    the whole point of the digest provider: the digest term enters the global balance and
///    only cancels once a consumer (the P256 `z` binding) requires the
///    same bytes. The matching positive case — a consumer that *does* balance
///    it — lands with that binding.
#[ignore = "slow: produces a real proof first; same cost as prove_and_verify_abc"]
#[test]
fn digest_provider_proof_is_unbalanced_without_consumer() {
    use num_traits::Zero;
    use stwo::core::fields::qm31::SecureField;
    use stwo_sha256::air::{Sha256Prover, Sha256Verifier};

    let witness = compute_sha256_witness(b"abc");
    let config = config_for(witness.blocks.len());

    let mut prover =
        Sha256Prover::new(&witness, config.log_n_rows, config.group_width).with_digest_provider();
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
        Sha256Verifier::new(config.log_n_rows, config.group_width, interaction_claim)
            .with_digest_provider();
    assert!(
        air_core::verify(&mut [&mut verifier], &stark_proof).is_err(),
        "an unbalanced digest yield (no consumer) must fail verification",
    );
}

/// Credential-field end-to-end: a real proof exposing the credential field windows
/// (date of birth + nationality). Mirrors the digest test above, exercising the
/// full constraint + trace + interaction field path (the byte-decomposition
/// columns, the `is_first_block`-gated yields, and the claimed-sum fold) at
/// prove time. Two assertions:
///
/// 1. The proof **succeeds**, so the AIR's field columns, decomposition
///    constraints, and per-yield lookups are internally consistent and the
///    interaction trace matches the constraint firing order — a provider tuple
///    desync would fail here.
/// 2. The verifier **rejects** the module on its own — the field yields have no
///    predicate consumer yet, so the global LogUp balance is
///    non-zero and fails closed. The matching positive case lands with the
///    age/nat credential bindings.
#[ignore = "slow: produces a real proof first; same cost as prove_and_verify_abc"]
#[test]
fn field_provider_proof_is_unbalanced_without_consumer() {
    use air_core::relations::field_id;
    use num_traits::Zero;
    use stwo::core::fields::qm31::SecureField;
    use stwo_sha256::air::{Sha256Prover, Sha256Verifier};
    use stwo_sha256::field_exposure::FieldExposure;

    // A credential-shaped preimage: "EUID" | ver | 2007-03-15 | DE(276).
    let credential: [u8; 11] = [b'E', b'U', b'I', b'D', 1, 0x07, 0xD7, 3, 15, 0x01, 0x14];
    let exposure = FieldExposure::from_preimage_windows(&[
        (field_id::DOB, 5, 4),
        (field_id::NATIONALITY, 9, 2),
    ]);

    let witness = compute_sha256_witness(&credential);
    let config = config_for(witness.blocks.len());

    let mut prover = Sha256Prover::new(&witness, config.log_n_rows, config.group_width)
        .with_field_provider(exposure.clone());
    let stark_proof = air_core::prove(&mut [&mut prover], config.pcs_config)
        .expect("prove with field provider must succeed");
    let interaction_claim = prover.interaction_claim().clone();

    // (1) The exposed field windows leave the module's claimed sums unbalanced.
    assert_ne!(
        interaction_claim.total(),
        SecureField::zero(),
        "exposing the credential fields must leave outstanding provider terms",
    );

    // (2) The verifier's global LogUp balance check rejects it (no consumer).
    let mut verifier =
        Sha256Verifier::new(config.log_n_rows, config.group_width, interaction_claim)
            .with_field_provider(exposure);
    assert!(
        air_core::verify(&mut [&mut verifier], &stark_proof).is_err(),
        "unbalanced field yields (no consumer) must fail verification",
    );
}

/// Same end-to-end field-provider proof gate as
/// [`field_provider_proof_is_unbalanced_without_consumer`], but with field
/// windows in blocks 0, 1, and 2. This specifically exercises the dynamic
/// target-block selector columns and the block counter in the AIR, not just the
/// legacy block-0 path.
#[ignore = "slow: produces a real proof first; same cost as prove_and_verify_multi_block"]
#[test]
fn multi_block_field_provider_proof_is_unbalanced_without_consumer() {
    use air_core::relations::field_id;
    use num_traits::Zero;
    use stwo::core::fields::qm31::SecureField;
    use stwo_sha256::air::{Sha256Prover, Sha256Verifier};
    use stwo_sha256::constants::BLOCK_BYTES;
    use stwo_sha256::field_exposure::FieldExposure;

    let msg: Vec<u8> = (0..150).map(|i| (i % 251) as u8).collect();
    let witness = compute_sha256_witness(&msg);
    assert_eq!(witness.blocks.len(), 3, "test message must span 3 blocks");
    let exposure = FieldExposure::from_preimage_windows_multi(&[
        (field_id::DOB, 5, 4),
        (field_id::NATIONALITY, BLOCK_BYTES + 8, 2),
        (99, 2 * BLOCK_BYTES + 12, 3),
    ]);
    let config = config_for(witness.blocks.len());

    let mut prover = Sha256Prover::new(&witness, config.log_n_rows, config.group_width)
        .with_field_provider(exposure.clone());
    let stark_proof = air_core::prove(&mut [&mut prover], config.pcs_config)
        .expect("prove with multi-block field provider must succeed");
    let interaction_claim = prover.interaction_claim().clone();

    assert_ne!(
        interaction_claim.total(),
        SecureField::zero(),
        "exposing multi-block field windows must leave outstanding provider terms",
    );

    let mut verifier =
        Sha256Verifier::new(config.log_n_rows, config.group_width, interaction_claim)
            .with_field_provider(exposure);
    assert!(
        air_core::verify(&mut [&mut verifier], &stark_proof).is_err(),
        "unbalanced multi-block field yields (no consumer) must fail verification",
    );
}
