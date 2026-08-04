//! End-to-end coverage for shared SHA table providers.
//!
//! These tests compose one shared provider with several SHA consumers. They
//! cover module order, relation handles, and global LogUp balance.

use air_core::{Air, AirProver};
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::PcsConfig;
use stwo_sha256::air::{Sha256Prover, Sha256Verifier};
use stwo_sha256::field_exposure::FieldExposure;
use stwo_sha256::relations::SharedShaTableRelations;
use stwo_sha256::shared_tables::{ShaTableMultiplicities, ShaTablesProver, ShaTablesVerifier};
use stwo_sha256::trace::min_log_size;
use stwo_sha256::witness::compute_sha256_witness;

/// Return the blowup-two PCS configuration.
///
/// Batch-four LogUp uses composition split `K = 2`. Blowup two keeps
/// `K <= log_blowup` in subdomain mode.
fn pcs_config() -> PcsConfig {
    PcsConfig {
        fri_config: stwo::core::fri::FriConfig::new(0, 2, 3, 1),
        ..PcsConfig::default()
    }
}

fn witnesses() -> Vec<stwo_sha256::types::Sha256Witness> {
    [b"" as &[u8], b"a", b"abc", &[0x42u8; 200]]
        .into_iter()
        .map(compute_sha256_witness)
        .collect()
}

#[ignore = "slow: proves a five-module shared SHA composition"]
#[test]
fn shared_sha_table_union_with_heterogeneous_messages_balances() {
    let witnesses = witnesses();
    let log_n_rows = witnesses
        .iter()
        .map(|witness| min_log_size(witness.blocks.len()))
        .max()
        .expect("non-empty witnesses");
    let consumers: Vec<_> = witnesses
        .iter()
        .map(|witness| (witness, FieldExposure::empty()))
        .collect();

    let shared = SharedShaTableRelations::new();
    let mut sha_tables = ShaTablesProver::new(
        ShaTableMultiplicities::from_consumers(&consumers),
        shared.clone(),
    );
    let mut sha0 = Sha256Prover::new(&witnesses[0], log_n_rows).with_shared_tables(shared.clone());
    let mut sha1 = Sha256Prover::new(&witnesses[1], log_n_rows).with_shared_tables(shared.clone());
    let mut sha2 = Sha256Prover::new(&witnesses[2], log_n_rows).with_shared_tables(shared.clone());
    let mut sha3 = Sha256Prover::new(&witnesses[3], log_n_rows).with_shared_tables(shared.clone());

    let mut provers: [&mut dyn AirProver; 5] =
        [&mut sha_tables, &mut sha0, &mut sha1, &mut sha2, &mut sha3];
    let proof =
        air_core::prove(&mut provers, pcs_config()).expect("shared SHA table composition proves");

    let shared = SharedShaTableRelations::new();
    let mut table_verifier =
        ShaTablesVerifier::new(sha_tables.interaction_claim().clone(), shared.clone());
    let mut sha0_verifier = Sha256Verifier::new(log_n_rows, sha0.interaction_claim().clone())
        .with_shared_tables(shared.clone());
    let mut sha1_verifier = Sha256Verifier::new(log_n_rows, sha1.interaction_claim().clone())
        .with_shared_tables(shared.clone());
    let mut sha2_verifier = Sha256Verifier::new(log_n_rows, sha2.interaction_claim().clone())
        .with_shared_tables(shared.clone());
    let mut sha3_verifier = Sha256Verifier::new(log_n_rows, sha3.interaction_claim().clone())
        .with_shared_tables(shared);

    let mut verifiers: [&mut dyn Air; 5] = [
        &mut table_verifier,
        &mut sha0_verifier,
        &mut sha1_verifier,
        &mut sha2_verifier,
        &mut sha3_verifier,
    ];
    air_core::verify(&mut verifiers, &proof).expect("shared SHA table composition verifies");
}

#[ignore = "slow: proves a five-module shared SHA composition before rejection"]
#[test]
fn corrupt_shared_sha_table_provider_claim_rejects() {
    let witnesses = witnesses();
    let log_n_rows = witnesses
        .iter()
        .map(|witness| min_log_size(witness.blocks.len()))
        .max()
        .expect("non-empty witnesses");
    let consumers: Vec<_> = witnesses
        .iter()
        .map(|witness| (witness, FieldExposure::empty()))
        .collect();

    let shared = SharedShaTableRelations::new();
    let mut sha_tables = ShaTablesProver::new(
        ShaTableMultiplicities::from_consumers(&consumers),
        shared.clone(),
    );
    let mut sha0 = Sha256Prover::new(&witnesses[0], log_n_rows).with_shared_tables(shared.clone());
    let mut sha1 = Sha256Prover::new(&witnesses[1], log_n_rows).with_shared_tables(shared.clone());
    let mut sha2 = Sha256Prover::new(&witnesses[2], log_n_rows).with_shared_tables(shared.clone());
    let mut sha3 = Sha256Prover::new(&witnesses[3], log_n_rows).with_shared_tables(shared);

    let mut provers: [&mut dyn AirProver; 5] =
        [&mut sha_tables, &mut sha0, &mut sha1, &mut sha2, &mut sha3];
    let proof = air_core::prove(&mut provers, pcs_config())
        .expect("honest shared SHA table composition proves");

    let mut corrupted_claim = sha_tables.interaction_claim().clone();
    corrupted_claim.pairs[0].claimed_sum += SecureField::from(BaseField::from(1));

    let shared = SharedShaTableRelations::new();
    let mut table_verifier = ShaTablesVerifier::new(corrupted_claim, shared.clone());
    let mut sha0_verifier = Sha256Verifier::new(log_n_rows, sha0.interaction_claim().clone())
        .with_shared_tables(shared.clone());
    let mut sha1_verifier = Sha256Verifier::new(log_n_rows, sha1.interaction_claim().clone())
        .with_shared_tables(shared.clone());
    let mut sha2_verifier = Sha256Verifier::new(log_n_rows, sha2.interaction_claim().clone())
        .with_shared_tables(shared.clone());
    let mut sha3_verifier = Sha256Verifier::new(log_n_rows, sha3.interaction_claim().clone())
        .with_shared_tables(shared);

    let mut verifiers: [&mut dyn Air; 5] = [
        &mut table_verifier,
        &mut sha0_verifier,
        &mut sha1_verifier,
        &mut sha2_verifier,
        &mut sha3_verifier,
    ];
    match air_core::verify(&mut verifiers, &proof) {
        Ok(_) => panic!("corrupt shared SHA table provider claim unexpectedly verified"),
        Err(error) => assert!(
            format!("{error:?}").contains("LogUp claimed sums do not cancel"),
            "unexpected error: {error:?}",
        ),
    }
}

/// Check the Class-D dummy region without a full proof.
///
/// Each shared multiplicity column has a deterministic real lower half and a
/// random dummy upper half.
/// - the stored multiplicity vector is `2^(L+1)` rows (domain 2× extended).
/// - the real lower half is DETERMINISTIC across two builds of the same
///   consumers (it is the honest union count).
/// - the dummy upper half DIFFERS across two builds (fresh random mask) — this
///   is the leak the blinding closes.
#[test]
fn class_d_sha_tables_dummy_region_is_doubled_and_randomised() {
    use stwo_sha256::components::{SharedProducer, RANGE_TABLES};

    let witnesses = witnesses();
    let consumers: Vec<_> = witnesses
        .iter()
        .map(|witness| (witness, FieldExposure::empty()))
        .collect();

    let a = ShaTableMultiplicities::from_consumers(&consumers);
    let b = ShaTableMultiplicities::from_consumers(&consumers);

    // Every producer's committed multiplicity column is doubled and split into a
    // deterministic real half + a randomised dummy half.
    let check = |producer: SharedProducer, va: &[u32], vb: &[u32]| {
        let blind = 1usize << producer.blind_log_size();
        let real = blind / 2;
        assert_eq!(blind, 2 * real, "blind domain is one log larger");
        assert_eq!(
            va.len(),
            blind,
            "{:?}: committed column is 2^(L+1)",
            producer
        );
        assert_eq!(vb.len(), blind);
        // Real lower half is the honest union count — deterministic.
        assert_eq!(
            &va[..real],
            &vb[..real],
            "{:?}: real multiplicities must be deterministic",
            producer,
        );
        // Dummy upper half is a fresh random mask — must differ across proofs.
        // (Collision of two independent 2^16-cell uniform masks is ~0.)
        assert_ne!(
            &va[real..],
            &vb[real..],
            "{:?}: dummy multiplicities must be freshly randomised per proof",
            producer,
        );
    };

    for (i, &kind) in RANGE_TABLES.iter().enumerate() {
        check(SharedProducer::Range(kind), &a.range[i], &b.range[i]);
    }
}

/// Check Class-D claimed-sum tamper rejection.
///
/// The dummy gate preserves the global balance without a free term. A
/// one-unit change to a published claimed sum must fail verification.
#[ignore = "slow: proves the shared SHA composition before tampering a Class-D claimed sum"]
#[test]
fn class_d_sha_table_balance_tamper_rejected() {
    let witnesses = witnesses();
    let log_n_rows = witnesses
        .iter()
        .map(|witness| min_log_size(witness.blocks.len()))
        .max()
        .expect("non-empty witnesses");
    let consumers: Vec<_> = witnesses
        .iter()
        .map(|witness| (witness, FieldExposure::empty()))
        .collect();

    let shared = SharedShaTableRelations::new();
    let mut sha_tables = ShaTablesProver::new(
        ShaTableMultiplicities::from_consumers(&consumers),
        shared.clone(),
    );
    let mut sha0 = Sha256Prover::new(&witnesses[0], log_n_rows).with_shared_tables(shared.clone());
    let mut sha1 = Sha256Prover::new(&witnesses[1], log_n_rows).with_shared_tables(shared.clone());
    let mut sha2 = Sha256Prover::new(&witnesses[2], log_n_rows).with_shared_tables(shared.clone());
    let mut sha3 = Sha256Prover::new(&witnesses[3], log_n_rows).with_shared_tables(shared);

    let mut provers: [&mut dyn AirProver; 5] =
        [&mut sha_tables, &mut sha0, &mut sha1, &mut sha2, &mut sha3];
    let proof = air_core::prove(&mut provers, pcs_config())
        .expect("honest Class-D shared SHA table composition proves");

    // Tamper the LAST producer pair's published claimed sum — the range tables,
    // whose blinded dummy region carries the random mask. The twin must not let
    // this shift cancel.
    let mut corrupted_claim = sha_tables.interaction_claim().clone();
    let last = corrupted_claim.pairs.len() - 1;
    corrupted_claim.pairs[last].claimed_sum += SecureField::from(BaseField::from(1));

    let shared = SharedShaTableRelations::new();
    let mut table_verifier = ShaTablesVerifier::new(corrupted_claim, shared.clone());
    let mut sha0_verifier = Sha256Verifier::new(log_n_rows, sha0.interaction_claim().clone())
        .with_shared_tables(shared.clone());
    let mut sha1_verifier = Sha256Verifier::new(log_n_rows, sha1.interaction_claim().clone())
        .with_shared_tables(shared.clone());
    let mut sha2_verifier = Sha256Verifier::new(log_n_rows, sha2.interaction_claim().clone())
        .with_shared_tables(shared.clone());
    let mut sha3_verifier = Sha256Verifier::new(log_n_rows, sha3.interaction_claim().clone())
        .with_shared_tables(shared);

    let mut verifiers: [&mut dyn Air; 5] = [
        &mut table_verifier,
        &mut sha0_verifier,
        &mut sha1_verifier,
        &mut sha2_verifier,
        &mut sha3_verifier,
    ];
    match air_core::verify(&mut verifiers, &proof) {
        Ok(_) => panic!("tampered Class-D SHA table claimed sum unexpectedly verified"),
        Err(error) => assert!(
            format!("{error:?}").contains("LogUp claimed sums do not cancel"),
            "unexpected error: {error:?}",
        ),
    }
}
