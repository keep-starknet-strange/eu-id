use std::hint::black_box;
use std::time::Duration;

use criterion::Criterion;
use ecdsa::signature::Signer;
use p256::ecdsa::{Signature as P256Signature, SigningKey};
use sha2::{Digest, Sha256};
use stwo_p256::proof::air::{prove_current_air, verify_current_air};
use stwo_p256::proof::P256ProofDraft;
use stwo_p256::types::{AffinePoint, EcdsaVerifyInput, Signature, U256};
use stwo_sha256::stark::{prove_sha256_from_witness, verify_sha256_proof, ProverConfig};
use stwo_sha256::trace::min_log_size;
use stwo_sha256::witness::compute_sha256_witness;

const SHA_BLOCK_COUNTS: &[usize] = &[1, 2, 4, 8, 16, 32, 33];
const P256_SIGNATURE_COUNTS: &[usize] = &[1, 2, 3];

pub fn bench_longfellow_equiv(c: &mut Criterion) {
    bench_sha(c);
    bench_p256(c);
}

fn bench_sha(c: &mut Criterion) {
    let mut group = c.benchmark_group("longfellow_equiv_sha");
    group.sample_size(10);
    group.warm_up_time(Duration::from_millis(500));

    for &blocks in SHA_BLOCK_COUNTS {
        let prove_name = format!("longfellow_equiv_sha/BM_ShaZK_equiv/{blocks}/prove");
        let verify_name = format!("longfellow_equiv_sha/BM_ShaZK_equiv/{blocks}/verify");
        if !should_register(&prove_name) && !should_register(&verify_name) {
            continue;
        }

        let message = longfellow_sha_message(blocks);
        let witness = compute_sha256_witness(&message);
        assert_eq!(witness.blocks.len(), blocks);
        let config = ProverConfig {
            log_n_rows: min_log_size(blocks),
            ..ProverConfig::default()
        };

        if should_register(&prove_name) {
            group.bench_function(format!("BM_ShaZK_equiv/{blocks}/prove"), |b| {
                b.iter(|| {
                    black_box(
                        prove_sha256_from_witness(&witness, &config)
                            .expect("SHA comparison proof builds"),
                    );
                });
            });
        }

        if should_register(&verify_name) {
            let proof =
                prove_sha256_from_witness(&witness, &config).expect("SHA comparison proof builds");
            group.bench_function(format!("BM_ShaZK_equiv/{blocks}/verify"), |b| {
                b.iter(|| verify_sha256_proof(black_box(&proof)).expect("SHA proof verifies"));
            });
        }
    }

    group.finish();
}

fn bench_p256(c: &mut Criterion) {
    let mut group = c.benchmark_group("longfellow_equiv_p256");
    group.sample_size(10);
    group.warm_up_time(Duration::from_millis(500));

    for &num_sigs in P256_SIGNATURE_COUNTS {
        let prove_name = format!("longfellow_equiv_p256/BM_ECDSAZKProver_equiv/{num_sigs}");
        let verify_name = format!("longfellow_equiv_p256/BM_ECDSAZKVerifier_equiv/{num_sigs}");
        if !should_register(&prove_name) && !should_register(&verify_name) {
            continue;
        }

        let drafts = p256_drafts(num_sigs);

        if should_register(&prove_name) {
            group.bench_function(format!("BM_ECDSAZKProver_equiv/{num_sigs}"), |b| {
                b.iter(|| {
                    for draft in &drafts {
                        black_box(prove_current_air(draft).expect("P256 comparison proof builds"));
                    }
                });
            });
        }

        if should_register(&verify_name) {
            let proofs = drafts
                .iter()
                .map(|draft| prove_current_air(draft).expect("P256 comparison proof builds"))
                .collect::<Vec<_>>();
            let expected = proofs
                .iter()
                .map(|proof| proof.claim.public_inputs.instances.clone())
                .collect::<Vec<_>>();
            group.bench_function(format!("BM_ECDSAZKVerifier_equiv/{num_sigs}"), |b| {
                b.iter(|| {
                    for (proof, expected) in proofs.iter().zip(&expected) {
                        verify_current_air(black_box(proof.clone()), black_box(expected))
                            .expect("P256 proof verifies");
                    }
                });
            });
        }
    }

    group.finish();
}

fn should_register(full_name: &str) -> bool {
    let filters: Vec<String> = std::env::args()
        .skip(1)
        .filter(|arg| arg != "--bench" && !arg.starts_with('-'))
        .collect();
    filters.is_empty()
        || filters
            .iter()
            .any(|filter| full_name.contains(filter) || filter.contains(full_name))
}

fn longfellow_sha_message(blocks: usize) -> Vec<u8> {
    assert!(blocks > 0);
    vec![b'a'; 50 + 64 * (blocks - 1)]
}

fn p256_drafts(num_sigs: usize) -> Vec<P256ProofDraft> {
    p256_inputs(num_sigs)
        .into_iter()
        .map(|input| {
            P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![input])
                .expect("P256 comparison draft builds")
        })
        .collect()
}

fn p256_inputs(num_sigs: usize) -> Vec<EcdsaVerifyInput> {
    let signing_key = SigningKey::from_bytes((&[7u8; 32]).into()).expect("valid signing key");
    let verifying_key = signing_key.verifying_key();
    let encoded = verifying_key.to_encoded_point(false);
    let qx = bytes32(encoded.x().expect("x coordinate"));
    let qy = bytes32(encoded.y().expect("y coordinate"));

    (0..num_sigs)
        .map(|i| {
            let message = format!("longfellow-equiv-p256-{i}");
            let digest: [u8; 32] = Sha256::digest(message.as_bytes()).into();
            let signature: P256Signature = signing_key.sign(message.as_bytes());
            EcdsaVerifyInput {
                message_hash: U256(digest),
                signature: Signature {
                    r: U256(signature.r().to_bytes().into()),
                    s: U256(signature.s().to_bytes().into()),
                },
                public_key: AffinePoint {
                    x: U256(qx),
                    y: U256(qy),
                },
            }
        })
        .collect()
}

fn bytes32(bytes: &[u8]) -> [u8; 32] {
    bytes.try_into().expect("expected 32 bytes")
}
