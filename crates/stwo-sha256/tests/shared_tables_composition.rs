//! End-to-end coverage for shared SHA table providers.
//!
//! These tests compose the shared provider with several real SHA consumers so
//! they exercise air-core's module ordering, relation handles, and global LogUp
//! balance instead of unit-level helpers.

use air_core::{Air, AirProver};
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::PcsConfig;
use stwo_sha256::air::{Sha256Prover, Sha256Verifier};
use stwo_sha256::field_exposure::FieldExposure;
use stwo_sha256::partitions::MAX_ROUND_GROUP_BITS;
use stwo_sha256::relations::SharedShaTableRelations;
use stwo_sha256::shared_tables::{ShaTableMultiplicities, ShaTablesProver, ShaTablesVerifier};
use stwo_sha256::stark::{prove_sha256, ProverConfig};
use stwo_sha256::trace::min_log_size;
use stwo_sha256::witness::compute_sha256_witness;

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
    let mut sha0 = Sha256Prover::new(&witnesses[0], log_n_rows, MAX_ROUND_GROUP_BITS)
        .with_shared_tables(shared.clone());
    let mut sha1 = Sha256Prover::new(&witnesses[1], log_n_rows, MAX_ROUND_GROUP_BITS)
        .with_shared_tables(shared.clone());
    let mut sha2 = Sha256Prover::new(&witnesses[2], log_n_rows, MAX_ROUND_GROUP_BITS)
        .with_shared_tables(shared.clone());
    let mut sha3 = Sha256Prover::new(&witnesses[3], log_n_rows, MAX_ROUND_GROUP_BITS)
        .with_shared_tables(shared.clone());

    let mut provers: [&mut dyn AirProver; 5] =
        [&mut sha_tables, &mut sha0, &mut sha1, &mut sha2, &mut sha3];
    let proof = air_core::prove(&mut provers, PcsConfig::default())
        .expect("shared SHA table composition proves");

    let shared = SharedShaTableRelations::new();
    let mut table_verifier =
        ShaTablesVerifier::new(sha_tables.interaction_claim().clone(), shared.clone());
    let mut sha0_verifier = Sha256Verifier::new(
        log_n_rows,
        MAX_ROUND_GROUP_BITS,
        sha0.interaction_claim().clone(),
    )
    .with_shared_tables(shared.clone());
    let mut sha1_verifier = Sha256Verifier::new(
        log_n_rows,
        MAX_ROUND_GROUP_BITS,
        sha1.interaction_claim().clone(),
    )
    .with_shared_tables(shared.clone());
    let mut sha2_verifier = Sha256Verifier::new(
        log_n_rows,
        MAX_ROUND_GROUP_BITS,
        sha2.interaction_claim().clone(),
    )
    .with_shared_tables(shared.clone());
    let mut sha3_verifier = Sha256Verifier::new(
        log_n_rows,
        MAX_ROUND_GROUP_BITS,
        sha3.interaction_claim().clone(),
    )
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
    let mut sha0 = Sha256Prover::new(&witnesses[0], log_n_rows, MAX_ROUND_GROUP_BITS)
        .with_shared_tables(shared.clone());
    let mut sha1 = Sha256Prover::new(&witnesses[1], log_n_rows, MAX_ROUND_GROUP_BITS)
        .with_shared_tables(shared.clone());
    let mut sha2 = Sha256Prover::new(&witnesses[2], log_n_rows, MAX_ROUND_GROUP_BITS)
        .with_shared_tables(shared.clone());
    let mut sha3 = Sha256Prover::new(&witnesses[3], log_n_rows, MAX_ROUND_GROUP_BITS)
        .with_shared_tables(shared);

    let mut provers: [&mut dyn AirProver; 5] =
        [&mut sha_tables, &mut sha0, &mut sha1, &mut sha2, &mut sha3];
    let proof = air_core::prove(&mut provers, PcsConfig::default())
        .expect("honest shared SHA table composition proves");

    let mut corrupted_claim = sha_tables.interaction_claim().clone();
    corrupted_claim.round_split_pack[0].claimed_sum += SecureField::from(BaseField::from(1));

    let shared = SharedShaTableRelations::new();
    let mut table_verifier = ShaTablesVerifier::new(corrupted_claim, shared.clone());
    let mut sha0_verifier = Sha256Verifier::new(
        log_n_rows,
        MAX_ROUND_GROUP_BITS,
        sha0.interaction_claim().clone(),
    )
    .with_shared_tables(shared.clone());
    let mut sha1_verifier = Sha256Verifier::new(
        log_n_rows,
        MAX_ROUND_GROUP_BITS,
        sha1.interaction_claim().clone(),
    )
    .with_shared_tables(shared.clone());
    let mut sha2_verifier = Sha256Verifier::new(
        log_n_rows,
        MAX_ROUND_GROUP_BITS,
        sha2.interaction_claim().clone(),
    )
    .with_shared_tables(shared.clone());
    let mut sha3_verifier = Sha256Verifier::new(
        log_n_rows,
        MAX_ROUND_GROUP_BITS,
        sha3.interaction_claim().clone(),
    )
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

#[ignore = "slow: proves standalone SHA to pin bincode proof bytes"]
#[test]
fn standalone_sha_proof_bytes_unchanged_by_shared_tables_feature() {
    let proof = prove_sha256(b"abc", &ProverConfig::default()).expect("standalone SHA proves");
    let bytes = bincode::serialize(&proof.stark_proof).expect("standalone SHA proof serializes");
    let expected = if cfg!(debug_assertions) {
        56_905
    } else {
        55_817
    };
    assert_eq!(bytes.len(), expected);
}
