use air_core::Air;
use num_traits::{One, Zero};
use stwo_sha256::air::{Sha256Prover, Sha256Verifier};
use stwo_sha256::interaction::InteractionClaim;
use stwo_sha256::stark::{prove_sha256, verify_sha256_proof, ProverConfig, Sha256ProveError};
use stwo_sha256::trace::{generate_trace, min_log_size, Layout, ROWS_PER_BLOCK};
use stwo_sha256::witness::{compute_packed_sha256_witness, PackedSha256Error};

fn packed(message_set: &[&[u8]]) -> stwo_sha256::PackedSha256Witness {
    compute_packed_sha256_witness(message_set).expect("packed witness")
}

#[test]
fn packed_trace_contains_four_messages_in_structural_order() {
    let messages: [&[u8]; 4] = [b"issuer", b"mso", &[0x20; 20], &[0x44; 1024]];
    let witness = packed(&messages);
    let blocks = [1usize, 1, 1, 17];
    let log_size = min_log_size(blocks.iter().sum());
    let trace = generate_trace(&witness, log_size);

    let mut global_block = 0;
    for (message_id, &message_blocks) in blocks.iter().enumerate() {
        for block in 0..message_blocks {
            let slot = Layout::round_row_slot(global_block, 0, log_size);
            assert_eq!(trace[Layout::COL_MSG_ID][slot].0, message_id as u32);
            assert_eq!(trace[Layout::COL_MSG_BLOCK][slot].0, block as u32);
            assert_eq!(trace[Layout::COL_MSG_START][slot].0, u32::from(block == 0));
            global_block += 1;
        }
    }
    let enabled = (0..(1usize << log_size))
        .map(|row| trace[Layout::COL_ENABLER][Layout::row_slot(row, log_size)].0)
        .sum::<u32>();
    assert_eq!(
        enabled as usize,
        blocks.iter().sum::<usize>() * ROWS_PER_BLOCK
    );
}

#[test]
fn unsupported_prover_log_sizes_fail_before_trace_allocation() {
    let witness = packed(&[b"abc"]);
    assert!(matches!(
        Sha256Prover::new(&witness, 3),
        Err(PackedSha256Error::UnsupportedLogNRows { log_n_rows: 3, .. })
    ));
    assert!(matches!(
        Sha256Prover::new(&witness, 31),
        Err(PackedSha256Error::UnsupportedLogNRows { log_n_rows: 31, .. })
    ));
}

#[test]
fn verifier_rejects_wrong_range_claim_shape() {
    let zero = stwo::core::fields::qm31::SecureField::zero();
    let claim = InteractionClaim {
        sha256: stwo_sha256::interaction::ComponentClaim { claimed_sum: zero },
        range: vec![],
    };
    assert!(Sha256Verifier::new(9, claim).validate_structure().is_err());
}

#[test]
fn standalone_facade_rejects_message_that_does_not_fit_configured_trace() {
    let config = ProverConfig {
        log_n_rows: 4,
        ..ProverConfig::default()
    };
    assert!(matches!(
        stwo_sha256::stark::prove_sha256(&[0u8; 5000], &config),
        Err(Sha256ProveError::TraceTooSmall { .. })
    ));
}

#[test]
fn malformed_claim_is_rejected_before_stark_verification() {
    let config = ProverConfig {
        log_n_rows: min_log_size(1),
        ..ProverConfig::default()
    };
    let mut proof = prove_sha256(b"abc", &config).expect("honest proof");
    proof.interaction_claim.sha256.claimed_sum += stwo::core::fields::qm31::SecureField::one();
    assert!(matches!(
        verify_sha256_proof(&proof),
        Err(stwo_sha256::stark::Sha256VerifyError::LogupSumNonZero)
    ));
}

#[ignore = "slow: creates a real packed STARK proof"]
#[test]
fn standalone_packed_proof_round_trip() {
    let message = b"abc";
    let config = ProverConfig {
        log_n_rows: min_log_size(1),
        ..ProverConfig::default()
    };
    let proof = stwo_sha256::stark::prove_sha256(message, &config).expect("prove");
    verify_sha256_proof(&proof).expect("verify");
}
