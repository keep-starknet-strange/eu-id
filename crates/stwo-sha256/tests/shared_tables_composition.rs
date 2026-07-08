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
    corrupted_claim.pairs[0].claimed_sum += SecureField::from(BaseField::from(1));

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

#[ignore = "slow: proves standalone SHA to bound bincode proof bytes"]
#[test]
fn standalone_sha_proof_bytes_unchanged_by_shared_tables_feature() {
    // The standalone SHA proof size is NO LONGER an exact pin: padding rows are
    // now filled with fresh random SHA decoys (masking) and the shared SHA
    // tables carry Class-D random dummy multiplicities, so FRI query openings
    // (hence serialized bytes) vary per proof by design (Q-015 §5: two proofs of
    // one witness share no opened values). We therefore bound the size rather
    // than pin it — the intent (enabling shared tables must not BLOAT the
    // standalone proof) survives as an upper bound. Observed ~57.5–58.1 KB
    // release / ~59 KB debug; band leaves margin for opening-count jitter.
    let proof = prove_sha256(b"abc", &ProverConfig::default()).expect("standalone SHA proves");
    let bytes = bincode::serialize(&proof.stark_proof).expect("standalone SHA proof serializes");
    let upper = if cfg!(debug_assertions) {
        62_000
    } else {
        61_000
    };
    assert!(
        bytes.len() <= upper,
        "standalone SHA proof {} bytes exceeds {upper} — shared-tables/blinding bloat?",
        bytes.len(),
    );
    // Sanity floor: a real proof is never trivially small.
    assert!(
        bytes.len() >= 40_000,
        "suspiciously small proof: {}",
        bytes.len()
    );
}

/// Class-D dummy-region blinding (Q-015 §4b / p4c Class D): every shared SHA
/// producer's committed multiplicity column is doubled — the real lower half is
/// the deterministic union count, the reserved dummy upper half holds fresh
/// per-proof random cells. This test pins the three observable Class-D
/// properties without paying for a full proof:
/// - the stored multiplicity vector is `2^(L+1)` rows (domain 2× extended);
/// - the real lower half is DETERMINISTIC across two builds of the same
///   consumers (it is the honest union count);
/// - the dummy upper half DIFFERS across two builds (fresh random mask) — this
///   is the leak the blinding closes.
#[test]
fn class_d_sha_tables_dummy_region_is_doubled_and_randomised() {
    use stwo_sha256::components::{
        SharedProducer, RANGE_TABLES, ROUND_SPLIT_TABLES, SIGMA_SPLIT_TABLES,
    };

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
        let real = 1usize << producer.log_size();
        let blind = 1usize << producer.blind_log_size();
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

    for (i, &(p, h)) in ROUND_SPLIT_TABLES.iter().enumerate() {
        check(
            SharedProducer::RoundSplit(p, h),
            &a.round_split_pack[i],
            &b.round_split_pack[i],
        );
    }
    for (i, &(p, h)) in SIGMA_SPLIT_TABLES.iter().enumerate() {
        check(
            SharedProducer::SigmaSplit(p, h),
            &a.sigma_split_pack[i],
            &b.sigma_split_pack[i],
        );
    }
    for (i, &kind) in RANGE_TABLES.iter().enumerate() {
        check(SharedProducer::Range(kind), &a.range[i], &b.range[i]);
    }
}

/// Class-D balance-tamper rejection at the stwo-sha256 layer (mirror of the
/// p256 bridge's `class_d_bridge_balance_tamper_rejected`). The cancelling twin
/// (`-mult + is_dummy·mult`) preserves the global LogUp balance and gives the
/// prover NO free claimed-sum term: shifting a blinded table's published
/// claimed sum by a single field unit must fail verification. This proves the
/// blinding did not open a soundness hole in the claimed-sum split.
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
        .expect("honest Class-D shared SHA table composition proves");

    // Tamper the LAST producer pair's published claimed sum — the range tables,
    // whose blinded dummy region carries the random mask. The twin must not let
    // this shift cancel.
    let mut corrupted_claim = sha_tables.interaction_claim().clone();
    let last = corrupted_claim.pairs.len() - 1;
    corrupted_claim.pairs[last].claimed_sum += SecureField::from(BaseField::from(1));

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
        Ok(_) => panic!("tampered Class-D SHA table claimed sum unexpectedly verified"),
        Err(error) => assert!(
            format!("{error:?}").contains("LogUp claimed sums do not cancel"),
            "unexpected error: {error:?}",
        ),
    }
}
