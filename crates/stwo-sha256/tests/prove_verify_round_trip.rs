use air_core::Air;
use num_traits::{One, Zero};
use sha2::{Digest, Sha256};
use stwo_sha256::air::{Sha256Prover, Sha256Verifier};
use stwo_sha256::interaction::InteractionClaim;
use stwo_sha256::stark::{prove_sha256, verify_sha256_proof, ProverConfig, Sha256ProveError};
use stwo_sha256::trace::{generate_trace, min_log_size, Layout, ROWS_PER_BLOCK};
use stwo_sha256::types::PackedSha256Witness;
use stwo_sha256::witness::{compute_packed_sha256_witness, PackedSha256Error};

fn packed(message_set: &[&[u8]]) -> PackedSha256Witness {
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
fn packed_four_and_five_message_traces_match_native_sha_and_geometry() {
    let four: Vec<Vec<u8>> = vec![
        vec![0x11; 55],
        vec![0x22; 56],
        vec![0x33; 63],
        vec![0x44; 64],
    ];
    let five: Vec<Vec<u8>> = vec![
        vec![0x11; 55],
        vec![0x22; 56],
        vec![0x33; 63],
        vec![0x44; 64],
        vec![0x55; 128],
    ];

    for messages in [&four[..], &five[..]] {
        let refs: Vec<&[u8]> = messages.iter().map(Vec::as_slice).collect();
        let witness = packed(&refs);
        let blocks: Vec<usize> = messages
            .iter()
            .map(|message| stwo_sha256::native::n_blocks_for(message.len()))
            .collect();
        let log_size = min_log_size(blocks.iter().sum());
        let trace = generate_trace(&witness, log_size);
        let mut next_block = 0;

        for (message_id, message) in messages.iter().enumerate() {
            for block in 0..blocks[message_id] {
                let start = Layout::round_row_slot(next_block + block, 0, log_size);
                assert_eq!(trace[Layout::COL_MSG_ID][start].0, message_id as u32);
                assert_eq!(trace[Layout::COL_MSG_BLOCK][start].0, block as u32);
                assert_eq!(trace[Layout::COL_MSG_START][start].0, u32::from(block == 0));
                for t in 0..ROWS_PER_BLOCK {
                    let slot = Layout::round_row_slot(next_block + block, t, log_size);
                    assert_eq!(trace[Layout::COL_MSG_ID][slot].0, message_id as u32);
                    assert_eq!(trace[Layout::COL_MSG_BLOCK][slot].0, block as u32);
                }
                if block == 0 {
                    for word in 0..8 {
                        let (lo, hi) = Layout::h_in_word(word);
                        let iv = stwo_sha256::constants::IV[word];
                        assert_eq!(trace[lo][start].0, iv & 0xffff);
                        assert_eq!(trace[hi][start].0, iv >> 16);
                    }
                }
            }

            next_block += stwo_sha256::native::n_blocks_for(message.len());
            let terminal_block = next_block - 1;
            let slot = Layout::row_slot(terminal_block * ROWS_PER_BLOCK + 63, log_size);
            let actual: Vec<u8> = (0..32)
                .map(|index| trace[Layout::digest_byte(index)][slot].0 as u8)
                .collect();
            let expected = Sha256::digest(message);
            assert_eq!(actual.as_slice(), &expected[..]);
        }
        assert!(
            (1usize << log_size) - next_block * ROWS_PER_BLOCK >= ROWS_PER_BLOCK,
            "packed trace must retain a complete disabled block"
        );
    }
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
fn verifier_accepts_local_and_rejects_wrong_range_claim_shape() {
    let zero = stwo::core::fields::qm31::SecureField::zero();
    let local = InteractionClaim {
        sha256: stwo_sha256::interaction::ComponentClaim { claimed_sum: zero },
        range: (0..4)
            .map(|_| stwo_sha256::interaction::ComponentClaim { claimed_sum: zero })
            .collect(),
    };
    assert!(Sha256Verifier::new(9, local).validate_structure().is_ok());
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
