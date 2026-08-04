use air_core::claim_mask::{
    ClaimMaskChallengeModule, ClaimMaskRing, SharedClaimMaskChallenge, CLAIM_MASK_MIN_LOG_SIZE,
    CLAIM_MASK_TRACE_COLUMNS,
};
use air_core::{Air, AirProver};
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::PcsConfig;
use stwo_sha256::air::{Sha256Prover, Sha256Verifier};
use stwo_sha256::claim_mask::ShaClaimMaskConfigError;
use stwo_sha256::components::RANGE_TABLES;
use stwo_sha256::field_exposure::FieldExposure;
use stwo_sha256::interaction::{ComponentClaim, InteractionClaim};
use stwo_sha256::relations::SharedShaTableRelations;
use stwo_sha256::shared_tables::{
    ShaTableMultiplicities, ShaTablesInteractionClaim, ShaTablesProver, ShaTablesVerifier,
};
use stwo_sha256::trace::min_log_size;
use stwo_sha256::witness::compute_sha256_witness;

fn pcs_config() -> PcsConfig {
    PcsConfig {
        fri_config: stwo::core::fri::FriConfig::new(0, 2, 3, 1),
        ..PcsConfig::default()
    }
}

fn take_masks(
    ring: &mut ClaimMaskRing,
    log_sizes: &[u32],
) -> Vec<air_core::claim_mask::ClaimMaskTrace> {
    log_sizes
        .iter()
        .map(|&log_size| ring.take(log_size).expect("declared mask order"))
        .collect()
}

#[test]
fn verifier_rejects_unbound_extra_claim_entries() {
    let zero = SecureField::from(BaseField::from(0));
    let component_claim = || ComponentClaim { claimed_sum: zero };

    let table_claim = ShaTablesInteractionClaim {
        pairs: (0..4).map(|_| component_claim()).collect(),
    };
    let table_verifier = ShaTablesVerifier::new(table_claim, SharedShaTableRelations::new());
    assert!(table_verifier.validate_structure().is_err());

    let shared_sha_claim = InteractionClaim {
        sha256: component_claim(),
        range: vec![component_claim()],
    };
    let shared_sha_verifier =
        Sha256Verifier::new(9, shared_sha_claim).with_shared_tables(SharedShaTableRelations::new());
    assert!(shared_sha_verifier.validate_structure().is_err());

    let local_sha_claim = InteractionClaim {
        sha256: component_claim(),
        range: (0..5).map(|_| component_claim()).collect(),
    };
    let local_sha_verifier = Sha256Verifier::new(9, local_sha_claim);
    assert!(local_sha_verifier.validate_structure().is_err());
}

#[test]
fn sha_claim_mask_configuration_rejects_count_and_order_mismatch() {
    let witness = compute_sha256_witness(&[0x42; 200]);
    let log_n_rows = min_log_size(witness.blocks.len());
    assert_eq!(log_n_rows, CLAIM_MASK_MIN_LOG_SIZE);

    let shared_tables = SharedShaTableRelations::new();
    let sha = Sha256Prover::new(&witness, log_n_rows).with_shared_tables(shared_tables.clone());
    assert_eq!(sha.ordered_claim_mask_log_sizes(), [log_n_rows]);

    let mut count_ring = ClaimMaskRing::new(&[log_n_rows, log_n_rows]).unwrap();
    let count_error = sha
        .with_claim_masks(
            take_masks(&mut count_ring, &[log_n_rows, log_n_rows]),
            SharedClaimMaskChallenge::new(),
        )
        .err()
        .expect("extra mask trace must be rejected");
    assert_eq!(
        count_error,
        ShaClaimMaskConfigError::Count {
            expected: 1,
            actual: 2,
        }
    );

    let sha = Sha256Prover::new(&witness, log_n_rows).with_shared_tables(shared_tables);
    let mut order_ring = ClaimMaskRing::new(&[log_n_rows + 1, log_n_rows]).unwrap();
    let wrong = order_ring.take(log_n_rows + 1).unwrap();
    let order_error = sha
        .with_claim_masks(vec![wrong], SharedClaimMaskChallenge::new())
        .err()
        .expect("out-of-order mask log size must be rejected");
    assert_eq!(
        order_error,
        ShaClaimMaskConfigError::LogSize {
            index: 0,
            expected: log_n_rows,
            actual: log_n_rows + 1,
        }
    );
}

#[test]
fn shared_sha_mask_layout_is_exact_and_every_component_is_at_least_log9() {
    let witness = compute_sha256_witness(&[0x42; 200]);
    let consumers = [(&witness, FieldExposure::empty())];
    let shared = SharedShaTableRelations::new();
    let unmasked = ShaTablesProver::new(
        ShaTableMultiplicities::from_consumers(&consumers),
        shared.clone(),
    );

    let log_sizes = unmasked.ordered_claim_mask_log_sizes();
    assert_eq!(log_sizes.len(), 3);
    assert!(
        log_sizes
            .iter()
            .all(|&log_size| log_size >= CLAIM_MASK_MIN_LOG_SIZE),
        "every claim-bearing shared component must support hidden masks"
    );
    assert_eq!(log_sizes, [9, 9, 9]);

    let unmasked_layout = unmasked.layout();
    assert_eq!(unmasked_layout.trace.len(), RANGE_TABLES.len());
    assert_eq!(
        unmasked_layout.interaction.len(),
        3 * stwo::core::fields::qm31::SECURE_EXTENSION_DEGREE
    );

    let mut ring = ClaimMaskRing::new(&log_sizes).unwrap();
    let masked = unmasked
        .with_claim_masks(
            take_masks(&mut ring, &log_sizes),
            SharedClaimMaskChallenge::new(),
        )
        .unwrap();
    ring.finish().unwrap();

    let layout = masked.layout();
    assert_eq!(
        layout.trace.len(),
        RANGE_TABLES.len() + log_sizes.len() * CLAIM_MASK_TRACE_COLUMNS
    );
    // Logical sites per component are [producer+mask] = [2, 3, 2], hence
    // paired interaction columns [1, 2, 1], each four base-field columns.
    assert_eq!(
        layout.interaction.len(),
        4 * stwo::core::fields::qm31::SECURE_EXTENSION_DEGREE
    );
    assert!(layout.trace.iter().all(|&log_size| log_size == 9));
    assert!(layout.interaction.iter().all(|&log_size| log_size == 9));
}

#[ignore = "proof-level claimed-sum masking gate"]
#[test]
fn masked_shared_sha_round_trip_and_claim_tamper_rejection() {
    let witness = compute_sha256_witness(&[0x42; 200]);
    let log_n_rows = min_log_size(witness.blocks.len());
    assert_eq!(log_n_rows, CLAIM_MASK_MIN_LOG_SIZE);
    let consumers = [(&witness, FieldExposure::empty())];

    let relations = SharedShaTableRelations::new();
    let table = ShaTablesProver::new(
        ShaTableMultiplicities::from_consumers(&consumers),
        relations.clone(),
    );
    let sha = Sha256Prover::new(&witness, log_n_rows).with_shared_tables(relations);

    let table_sizes = table.ordered_claim_mask_log_sizes();
    let sha_sizes = sha.ordered_claim_mask_log_sizes();
    let all_sizes: Vec<_> = table_sizes.iter().chain(&sha_sizes).copied().collect();
    let mut ring = ClaimMaskRing::new(&all_sizes).unwrap();
    let challenge = SharedClaimMaskChallenge::new();
    let mut table = table
        .with_claim_masks(take_masks(&mut ring, &table_sizes), challenge.clone())
        .unwrap();
    let mut sha = sha
        .with_claim_masks(take_masks(&mut ring, &sha_sizes), challenge.clone())
        .unwrap();
    ring.finish().unwrap();
    let mut anchor = ClaimMaskChallengeModule::new(challenge, all_sizes.clone()).unwrap();

    let mut provers: [&mut dyn AirProver; 3] = [&mut table, &mut sha, &mut anchor];
    let proof = air_core::prove(&mut provers, pcs_config()).expect("masked SHA proof");
    let table_claim = table.interaction_claim().clone();
    let sha_claim = sha.interaction_claim().clone();

    let verifier_relations = SharedShaTableRelations::new();
    let verifier_challenge = SharedClaimMaskChallenge::new();
    let mut table_verifier =
        ShaTablesVerifier::new(table_claim.clone(), verifier_relations.clone())
            .with_claim_masks(verifier_challenge.clone());
    let mut sha_verifier = Sha256Verifier::new(log_n_rows, sha_claim.clone())
        .with_shared_tables(verifier_relations)
        .with_claim_masks(verifier_challenge.clone());
    let mut verifier_anchor =
        ClaimMaskChallengeModule::new(verifier_challenge, all_sizes.clone()).unwrap();
    let mut verifiers: [&mut dyn Air; 3] =
        [&mut table_verifier, &mut sha_verifier, &mut verifier_anchor];
    air_core::verify(&mut verifiers, &proof).expect("masked SHA proof verifies");

    let mut tampered_table_claim = table_claim;
    tampered_table_claim.pairs[0].claimed_sum += SecureField::from(BaseField::from(1));
    let verifier_relations = SharedShaTableRelations::new();
    let verifier_challenge = SharedClaimMaskChallenge::new();
    let mut table_verifier =
        ShaTablesVerifier::new(tampered_table_claim, verifier_relations.clone())
            .with_claim_masks(verifier_challenge.clone());
    let mut sha_verifier = Sha256Verifier::new(log_n_rows, sha_claim)
        .with_shared_tables(verifier_relations)
        .with_claim_masks(verifier_challenge.clone());
    let mut verifier_anchor = ClaimMaskChallengeModule::new(verifier_challenge, all_sizes).unwrap();
    let mut verifiers: [&mut dyn Air; 3] =
        [&mut table_verifier, &mut sha_verifier, &mut verifier_anchor];
    let error =
        air_core::verify(&mut verifiers, &proof).expect_err("tampered masked claim must reject");
    assert!(
        format!("{error:?}").contains("LogUp claimed sums do not cancel"),
        "unexpected rejection: {error:?}"
    );
}

#[ignore = "proof-level local-range claimed-sum masking gate"]
#[test]
fn masked_standalone_sha_covers_every_local_range_claim() {
    let witness = compute_sha256_witness(&[0x24; 200]);
    let log_n_rows = min_log_size(witness.blocks.len());
    let sha = Sha256Prover::new(&witness, log_n_rows);
    let log_sizes = sha.ordered_claim_mask_log_sizes();
    assert_eq!(log_sizes.len(), 1 + RANGE_TABLES.len());
    assert!(log_sizes
        .iter()
        .all(|&log_size| log_size >= CLAIM_MASK_MIN_LOG_SIZE));

    let mut ring = ClaimMaskRing::new(&log_sizes).unwrap();
    let challenge = SharedClaimMaskChallenge::new();
    let mut sha = sha
        .with_claim_masks(take_masks(&mut ring, &log_sizes), challenge.clone())
        .unwrap();
    ring.finish().unwrap();
    let mut anchor = ClaimMaskChallengeModule::new(challenge, log_sizes.clone()).unwrap();
    let mut provers: [&mut dyn AirProver; 2] = [&mut sha, &mut anchor];
    let proof = air_core::prove(&mut provers, pcs_config()).expect("masked standalone SHA proof");

    let verifier_challenge = SharedClaimMaskChallenge::new();
    let mut verifier = Sha256Verifier::new(log_n_rows, sha.interaction_claim().clone())
        .with_claim_masks(verifier_challenge.clone());
    let mut verifier_anchor = ClaimMaskChallengeModule::new(verifier_challenge, log_sizes).unwrap();
    let mut verifiers: [&mut dyn Air; 2] = [&mut verifier, &mut verifier_anchor];
    air_core::verify(&mut verifiers, &proof).expect("masked standalone SHA proof verifies");
}
