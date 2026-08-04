//! Prove → verify round-trip tests for the standalone SHA-256 component.
//!
//! These tests cover the SHA consumer, four active `Range_k` producers, trace
//! commitments, LogUp balance, PCS, FRI, and typed verification errors.
//!
//! Real proof construction is slow in debug workflows. The tests have
//! `#[ignore]` attributes. Run them in release mode with `--ignored`.

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
#[ignore = "slow: creates a real STARK proof; run in release with --ignored"]
#[test]
fn prove_and_verify_abc() {
    assert_eq!(prove_and_verify(b"abc"), 1);
}

/// Multi-block round-trip — exercises the §10.3 chain copy constraint,
/// the multi-block padding flag layout (marker block ≠ length block),
/// and the multi-block `Range_k` consumer lookups end-to-end. None of
/// these constraints fire on the single-block `b"abc"` case.
#[ignore = "slow: creates a real STARK proof; run in release with --ignored"]
#[test]
fn prove_and_verify_multi_block() {
    // 200 bytes ⇒ 200 + 9 = 209 padding bytes ⇒ 4 padded blocks. The
    // last block is a length-only block (marker lives in block 3, length
    // in block 4). Blocks 1..3 trigger the §10.3 chain copy constraint.
    let n_blocks = prove_and_verify(&[0xABu8; 200]);
    assert!(n_blocks >= 2, "test message must span multiple blocks");
}

/// Check a long message above the minimum single-block trace size.
///
/// This case checks cross-row masks and component allocation at a larger log
/// size. A 4,096-byte message has 65 padded blocks and uses `log_n_rows = 13`.
#[ignore = "slow: creates a real STARK proof; run in release with --ignored"]
#[test]
fn prove_and_verify_long_message() {
    // 4,096 bytes plus padding give 65 blocks and 4,160 real rows.
    // The next power-of-two trace has log size 13.
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
#[ignore = "slow: creates a real STARK proof; run in release with --ignored"]
#[test]
fn prove_and_verify_padding_boundaries() {
    // Empty message — single marker+length block, marker at byte 0 of W[0].
    assert_eq!(prove_and_verify(b""), 1);
    // 55 bytes — last possible single-block message (55 + 1 marker + 8
    // length = 64). The marker is at byte 55. The length fills W[14]/W[15].
    assert_eq!(prove_and_verify(&[0x42u8; 55]), 1);
    // 56 bytes — first message that spills the length into a second
    // block. Block 0 carries the marker (no length). Block 1 is
    // length-only (no marker).
    assert_eq!(prove_and_verify(&[0x42u8; 56]), 2);
    // 64 bytes — exactly one input block of preimage. Padding occupies
    // a full second block (marker at W[0] byte 0, length in W[14]/W[15]).
    assert_eq!(prove_and_verify(&[0x42u8; 64]), 2);
}

/// `prove_sha256_from_witness` is publicly exposed so integration-stream
/// callers can supply a pre-built witness (e.g. coming from a credential
/// builder, not raw bytes). Pin the contract that it produces a proof
/// indistinguishable from `prove_sha256` on the same message.
#[ignore = "slow: creates a real STARK proof; run in release with --ignored"]
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
    // same family. Calling it here pins that it agrees with the witness
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

/// Check that an out-of-range carry cannot produce an accepted proof.
///
/// Change one finalization carry to five. `Range_2` permits only zero or one.
/// The mutation breaks the mod-2³² linear identity and Range_2 lookup soundness.
/// The identity is `h_in[7] + state[7] = h_out[7] + carry · 2¹⁶`.
/// Therefore, the system must reject at one of these points:
///   - the prover's constraint-vanishing check (`Sha256ProveError::StwoProveFailed`), or
///   - the verifier's downstream gate (any `Sha256VerifyError` variant).
///
/// This is the complementary half of
/// [`verify_rejects_range_k_claimed_sum_mutations`]: that test mutates
/// the *proof* to isolate the `Range_k` LogUp loop. This one mutates the
/// *witness* end-to-end. Together they test both directions.
#[ignore = "slow: creates a real STARK proof; run in release with --ignored"]
#[test]
fn rejects_out_of_range_carry_witness_mutation() {
    let msg = b"abc";
    let mut witness = compute_sha256_witness(msg);
    let last = witness.blocks.last_mut().expect("at least one block");
    last.finalization_carries[7].lo = 5;

    let config = config_for(witness.blocks.len());
    // Either the prover refuses to produce a proof, or the verifier
    // refuses to accept one. No accepted proof can exist for this witness.
    match prove_sha256_from_witness(&witness, &config) {
        Err(_) => {} // prover caught it — pass
        Ok(proof) => {
            verify_sha256_proof(&proof)
                .expect_err("verifier must reject a proof from an out-of-range-carry witness");
        }
    }
}

/// Check claimed-sum rejection for all four `Range_k` channels.
///
/// A change to one producer sum makes the global sum nonzero. This test
/// isolates the LogUp gate from the addition identities.
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

    // Test each of the four `Range_k` producers. Indices 0 through 3 follow
    // `RANGE_TABLES`: Range_2, Range_4, Range_5, and Range_8. Increment each
    // producer's claimed sum and require rejection. This catches a regression in
    // any channel.
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

/// Check a digest provider without a matching consumer.
///
/// 1. The Stwo prover accepts the digest yield because its degree-two constraint
///    is satisfiable. The interaction column matches the AIR's `add_to_relation`
///    call. A degree increase or tuple mismatch would fail during proving.
/// 2. The verifier rejects the isolated module. No consumer cancels its digest
///    term. A composed proof needs a consumer with identical bytes.
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

/// Check credential-field exposure without predicate consumers.
///
/// This test covers byte decomposition, first-block gates, and claimed sums.
///
/// 1. The proof succeeds. Its field columns, decomposition constraints, and
///    per-yield lookups are consistent. The interaction trace follows the
///    constraint order. A provider tuple mismatch would fail here.
/// 2. The verifier rejects the isolated module because its field yields have no
///    predicate consumers. The global LogUp balance is nonzero and fails closed.
///    Credential composition supplies matching age and nationality consumers.
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

    let mut prover =
        Sha256Prover::new(&witness, config.log_n_rows).with_field_provider(exposure.clone());
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
        Sha256Verifier::new(config.log_n_rows, interaction_claim).with_field_provider(exposure);
    assert!(
        air_core::verify(&mut [&mut verifier], &stark_proof).is_err(),
        "unbalanced field yields (no consumer) must fail verification",
    );
}

/// Same end-to-end field-provider proof gate as
/// [`field_provider_proof_is_unbalanced_without_consumer`], but with field
/// windows in blocks 0, 1, and 2. This specifically exercises the dynamic
/// target-block selector columns and the block counter in the AIR, not just the
/// fixed-block-0 optimization.
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
    let exposure = FieldExposure::from_preimage_windows(&[
        (field_id::DOB, 5, 4),
        (field_id::NATIONALITY, BLOCK_BYTES + 8, 2),
        (99, 2 * BLOCK_BYTES + 12, 3),
    ]);
    let config = config_for(witness.blocks.len());

    let mut prover =
        Sha256Prover::new(&witness, config.log_n_rows).with_field_provider(exposure.clone());
    let stark_proof = air_core::prove(&mut [&mut prover], config.pcs_config)
        .expect("prove with multi-block field provider must succeed");
    let interaction_claim = prover.interaction_claim().clone();

    assert_ne!(
        interaction_claim.total(),
        SecureField::zero(),
        "exposing multi-block field windows must leave outstanding provider terms",
    );

    let mut verifier =
        Sha256Verifier::new(config.log_n_rows, interaction_claim).with_field_provider(exposure);
    assert!(
        air_core::verify(&mut [&mut verifier], &stark_proof).is_err(),
        "unbalanced multi-block field yields (no consumer) must fail verification",
    );
}

/// Full padded-stream provider gate. The interaction width must remain 64
/// sites while all three padded blocks emit distinct absolute byte indices.
#[ignore = "slow: produces a real proof first; same cost as prove_and_verify_multi_block"]
#[test]
fn padded_stream_provider_proof_is_unbalanced_without_consumer() {
    use num_traits::Zero;
    use stwo::core::fields::qm31::SecureField;
    use stwo_sha256::air::{Sha256Prover, Sha256Verifier};
    use stwo_sha256::constants::BLOCK_BYTES;
    use stwo_sha256::field_exposure::FieldExposure;

    const STREAM_FIELD_ID: u32 = 99;
    let msg: Vec<u8> = (0..150).map(|i| (i % 251) as u8).collect();
    let witness = compute_sha256_witness(&msg);
    assert_eq!(witness.blocks.len(), 3, "test message must span 3 blocks");
    let exposure = FieldExposure::empty().with_padded_stream(STREAM_FIELD_ID);
    assert_eq!(exposure.n_yields(), BLOCK_BYTES);
    let config = config_for(witness.blocks.len());

    let mut prover =
        Sha256Prover::new(&witness, config.log_n_rows).with_field_provider(exposure.clone());
    let stark_proof = air_core::prove(&mut [&mut prover], config.pcs_config)
        .expect("prove with padded stream provider must succeed");
    let interaction_claim = prover.interaction_claim().clone();

    assert_ne!(
        interaction_claim.total(),
        SecureField::zero(),
        "padded stream must leave outstanding provider terms",
    );
    let mut verifier =
        Sha256Verifier::new(config.log_n_rows, interaction_claim).with_field_provider(exposure);
    assert!(
        air_core::verify(&mut [&mut verifier], &stark_proof).is_err(),
        "unbalanced padded stream (no consumer) must fail verification",
    );
}
