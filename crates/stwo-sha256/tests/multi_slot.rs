//! Multi-slot merged consumer (S8) — end-to-end composition and LogUp
//! attribution coverage. Design/audit record: tasks/sha-multimessage-design.md.

use air_core::{Air, AirProver};
use stwo::core::channel::Blake2sChannel;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::PcsConfig;
use stwo_constraint_framework::Relation;
use stwo_sha256::air::{Sha256MultiProver, Sha256MultiVerifier};
use stwo_sha256::field_exposure::FieldExposure;
use stwo_sha256::interaction::generate_multi_consumer_interaction_trace;
use stwo_sha256::relations::{Sha256Relations, SharedShaTableRelations, SlotIoRelations};
use stwo_sha256::shared_tables::{ShaTableMultiplicities, ShaTablesProver, ShaTablesVerifier};
use stwo_sha256::slots::{MultiSlotConfig, SlotSpec};
use stwo_sha256::trace::h_out_digest_bytes;
use stwo_sha256::types::Sha256Witness;
use stwo_sha256::witness::compute_sha256_witness;

use num_traits::{One, Zero};

fn plain_slots(n: usize) -> Vec<SlotSpec> {
    (0..n)
        .map(|_| SlotSpec {
            expose_digest: false,
            field_exposure: FieldExposure::empty(),
        })
        .collect()
}

/// Full [tables, merged-multi] composition round trip: three heterogeneous
/// messages in one merged instance, no cross-module exposure (the module is
/// self-balancing). Exercises the schedule preprocessed columns, per-slot
/// IV/chain/finalization, per-slot zk decoy padding, and the layout /
/// transcript surfaces on both sides.
#[ignore = "slow: proves a shared-tables + merged multi-slot composition"]
#[test]
fn multi_slot_composition_round_trips() {
    let witnesses: Vec<Sha256Witness> = [b"" as &[u8], b"abc", &[0x42u8; 150]]
        .into_iter()
        .map(compute_sha256_witness)
        .collect();
    let refs: Vec<&Sha256Witness> = witnesses.iter().collect();
    let config = MultiSlotConfig::new(8, plain_slots(3));
    let log_n_rows = config.min_log_n_rows();

    let consumers: Vec<_> = witnesses
        .iter()
        .map(|w| (w, FieldExposure::empty()))
        .collect();
    let shared = SharedShaTableRelations::new();
    let mut sha_tables = ShaTablesProver::new(
        ShaTableMultiplicities::from_consumers(&consumers),
        shared.clone(),
    );
    let mut merged = Sha256MultiProver::new(refs, log_n_rows, config.clone(), shared.clone());

    let mut provers: [&mut dyn AirProver; 2] = [&mut sha_tables, &mut merged];
    let proof = air_core::prove(&mut provers, PcsConfig::default())
        .expect("multi-slot composition proves");

    let shared = SharedShaTableRelations::new();
    let mut table_verifier =
        ShaTablesVerifier::new(sha_tables.interaction_claim().clone(), shared.clone());
    let mut merged_verifier = Sha256MultiVerifier::new(
        log_n_rows,
        config,
        shared,
        merged.interaction_claim().clone(),
    );
    let mut verifiers: [&mut dyn Air; 2] = [&mut table_verifier, &mut merged_verifier];
    air_core::verify(&mut verifiers, &proof).expect("multi-slot composition verifies");
}

// ---------------------------------------------------------------------------
// Per-slot LogUp attribution at the claimed-sum level (T1 of the S8 plan)
// ---------------------------------------------------------------------------

/// The S8-shaped exposure fixture: slot 0 revocation-like (legacy block-0
/// field window), slots 1–2 attribute-like (digest + a field window; slot
/// 2's window sits in block 1 so the selector/counter tail is exercised).
fn exposure_fixture() -> (Vec<Sha256Witness>, MultiSlotConfig) {
    let witnesses = vec![
        compute_sha256_witness(&[0x11u8; 20]),
        compute_sha256_witness(b"abc"),
        compute_sha256_witness(&[0x42u8; 100]),
    ];
    let config = MultiSlotConfig::new(
        8,
        vec![
            SlotSpec {
                expose_digest: false,
                field_exposure: FieldExposure::from_preimage_windows(&[(7, 0, 4)]),
            },
            SlotSpec {
                expose_digest: true,
                field_exposure: FieldExposure::empty(),
            },
            SlotSpec {
                expose_digest: true,
                field_exposure: FieldExposure::from_preimage_windows_multi(&[(9, 66, 2)]),
            },
        ],
    );
    (witnesses, config)
}

struct Drawn {
    relations: Sha256Relations,
    slot_relations: Vec<SlotIoRelations>,
}

fn draw(n_slots: usize) -> Drawn {
    let channel = &mut Blake2sChannel::default();
    // The shared-table channels do not need to match a real provider here —
    // their uses cancel in the with/without-exposure DIFFERENCE below.
    let relations = Sha256Relations::draw(channel);
    let slot_relations = SlotIoRelations::draw_per_slot(channel, n_slots);
    Drawn {
        relations,
        slot_relations,
    }
}

fn total(
    drawn: &Drawn,
    witnesses: &[Sha256Witness],
    config: &MultiSlotConfig,
) -> SecureField {
    let refs: Vec<&Sha256Witness> = witnesses.iter().collect();
    let (_, claim) = generate_multi_consumer_interaction_trace(
        &drawn.relations,
        &drawn.slot_relations,
        &refs,
        config.min_log_n_rows(),
        config,
    );
    claim.total()
}

/// The module's OUTSTANDING cross-module terms: total(with exposures) −
/// total(exposures off). The 66 base table-use sites are identical in both,
/// so the difference is exactly the digest yields + field yields + the
/// field-byte Range16 uses.
fn outstanding(drawn: &Drawn, witnesses: &[Sha256Witness], config: &MultiSlotConfig) -> SecureField {
    let plain = MultiSlotConfig::new(config.slot_log, plain_slots(config.n_slots()));
    total(drawn, witnesses, config) - total(drawn, witnesses, &plain)
}

fn require(denom: SecureField) -> SecureField {
    assert_ne!(denom, SecureField::zero());
    SecureField::one() / denom
}

/// Synthetic per-slot consumers + the verifier-side Range16 accounting
/// cancel the outstanding terms EXACTLY — and only when each slot's digest
/// is required over that slot's OWN relation (per-slot attribution).
#[test]
fn multi_slot_yields_balance_per_slot_and_reject_cross_slot_swap() {
    let (witnesses, config) = exposure_fixture();
    let drawn = draw(config.n_slots());
    let out = outstanding(&drawn, &witnesses, &config);
    assert_ne!(out, SecureField::zero(), "exposures leave outstanding terms");

    // Field-byte Range16 uses (2 per exposed byte column on the hot row,
    // positive) — cancel them with the matching negative terms.
    let mut cancel = SecureField::zero();
    for (s, spec) in config.slots.iter().enumerate() {
        let exposure = &spec.field_exposure;
        if exposure.is_empty() {
            continue;
        }
        // Hot block: 0 for legacy, each target block for multi-block.
        let targets: Vec<usize> = if exposure.needs_block_witness() {
            exposure.target_blocks().to_vec()
        } else {
            vec![0]
        };
        for target in targets {
            let block = &witnesses[s].blocks[target];
            for &word_idx in exposure.decomposed_words() {
                let limb = block.schedule[word_idx];
                for byte in stwo_sha256::field_exposure::word_be_bytes(limb.lo, limb.hi) {
                    for value in [
                        byte,
                        byte + stwo_sha256::field_exposure::BYTE_RANGE_CHECK_OFFSET,
                    ] {
                        let denom = drawn
                            .relations
                            .range
                            .range_16
                            .combine(&[BaseField::from(value)]);
                        cancel -= require(denom);
                    }
                }
            }
        }
        // Field yields: require each (field_id, byte_index, byte) tuple over
        // the slot's OWN field relation.
        for y in exposure.yields() {
            let block = &witnesses[s].blocks[y.block_idx];
            let limb = block.schedule[y.word_idx];
            let byte =
                stwo_sha256::field_exposure::word_be_bytes(limb.lo, limb.hi)[y.byte_in_word];
            let denom = drawn.slot_relations[s].field.field.combine(&[
                BaseField::from(y.field_id),
                BaseField::from(y.byte_index),
                BaseField::from(byte),
            ]);
            cancel += require(denom);
        }
    }
    // Digest requires over each digest slot's OWN relation.
    let digest_require = |s: usize, rel_slot: usize| -> SecureField {
        let bytes = h_out_digest_bytes(&witnesses[s].blocks.last().unwrap().h_out);
        let values: Vec<BaseField> = bytes.iter().map(|&b| BaseField::from(b)).collect();
        require(drawn.slot_relations[rel_slot].digest.digest.combine(&values))
    };
    let honest = out + cancel + digest_require(1, 1) + digest_require(2, 2);
    assert_eq!(
        honest,
        SecureField::zero(),
        "per-slot consumers must cancel the outstanding terms exactly",
    );

    // T1 — cross-slot digest swap: requiring slot 1's digest over slot 2's
    // relation (and vice versa) must NOT balance. With per-slot relations a
    // multiset swap is inexpressible.
    let swapped = out + cancel + digest_require(1, 2) + digest_require(2, 1);
    assert_ne!(
        swapped,
        SecureField::zero(),
        "cross-slot digest attribution must not balance",
    );
}

/// A consumer requiring a tampered field byte from the revocation-like slot
/// does not balance — the merged instance still binds the exact hashed
/// bytes per slot.
#[test]
fn multi_slot_rejects_mismatched_field_consumer() {
    let (witnesses, config) = exposure_fixture();
    let drawn = draw(config.n_slots());
    let out = outstanding(&drawn, &witnesses, &config);

    // Honest cancellation of everything EXCEPT slot 0's first field yield,
    // which we tamper by one.
    let mut cancel = SecureField::zero();
    for (s, spec) in config.slots.iter().enumerate() {
        let exposure = &spec.field_exposure;
        if exposure.is_empty() {
            continue;
        }
        let targets: Vec<usize> = if exposure.needs_block_witness() {
            exposure.target_blocks().to_vec()
        } else {
            vec![0]
        };
        for target in targets {
            let block = &witnesses[s].blocks[target];
            for &word_idx in exposure.decomposed_words() {
                let limb = block.schedule[word_idx];
                for byte in stwo_sha256::field_exposure::word_be_bytes(limb.lo, limb.hi) {
                    for value in [
                        byte,
                        byte + stwo_sha256::field_exposure::BYTE_RANGE_CHECK_OFFSET,
                    ] {
                        let denom = drawn
                            .relations
                            .range
                            .range_16
                            .combine(&[BaseField::from(value)]);
                        cancel -= require(denom);
                    }
                }
            }
        }
        for (i, y) in exposure.yields().iter().enumerate() {
            let block = &witnesses[s].blocks[y.block_idx];
            let limb = block.schedule[y.word_idx];
            let mut byte =
                stwo_sha256::field_exposure::word_be_bytes(limb.lo, limb.hi)[y.byte_in_word];
            if s == 0 && i == 0 {
                byte += 1; // tampered require
            }
            let denom = drawn.slot_relations[s].field.field.combine(&[
                BaseField::from(y.field_id),
                BaseField::from(y.byte_index),
                BaseField::from(byte),
            ]);
            cancel += require(denom);
        }
    }
    let digest_require = |s: usize| -> SecureField {
        let bytes = h_out_digest_bytes(&witnesses[s].blocks.last().unwrap().h_out);
        let values: Vec<BaseField> = bytes.iter().map(|&b| BaseField::from(b)).collect();
        require(drawn.slot_relations[s].digest.digest.combine(&values))
    };
    let with_tamper = out + cancel + digest_require(1) + digest_require(2);
    assert_ne!(
        with_tamper,
        SecureField::zero(),
        "a tampered field-byte require must not balance",
    );
}
