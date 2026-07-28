#![allow(dead_code)]

use ml_dsa::signature::{Keypair, Signer, Verifier};
use ml_dsa::{EncodedSignature, EncodedVerifyingKey, MlDsa65, SigningKey};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use stwo::core::fri::FriConfig;
use stwo::core::pcs::PcsConfig;
use stwo_mldsa::reference::encoding::{pk_decode, sig_decode};
use stwo_mldsa::reference::sponge::shake256;
use stwo_mldsa::witness::{generate_witness, MlDsaWitness};
use stwo_mldsa::MlDsaVerifyInput;

/// Batch-4 LogUp constraints have log-degree excess 2, so proving needs
/// `log_blowup >= 2` (production uses 3).
pub fn standalone_pcs_config() -> PcsConfig {
    PcsConfig {
        fri_config: FriConfig::new(0, 2, 3, 1),
        ..PcsConfig::default()
    }
}

/// The composed statement keeps the historical direct-Keccak test PCS.
pub fn composed_pcs_config() -> PcsConfig {
    PcsConfig {
        pow_bits: 10,
        fri_config: FriConfig::new(0, 2, 3, 1),
        lifting_log_size: None,
    }
}

pub fn oracle_keypair(seed: u64) -> SigningKey<MlDsa65> {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut sk_seed = [0u8; 32];
    rng.fill(&mut sk_seed);
    SigningKey::<MlDsa65>::from_seed(&sk_seed.into())
}

pub fn oracle_input_from_key(sk: &SigningKey<MlDsa65>, msg: &[u8]) -> MlDsaVerifyInput {
    let vk = sk.verifying_key();
    let sig = sk.sign(msg);
    assert!(vk.verify(msg, &sig).is_ok(), "oracle self-check");
    let vk_bytes: EncodedVerifyingKey<MlDsa65> = vk.encode();
    let sig_bytes: EncodedSignature<MlDsa65> = sig.encode();
    let pk = pk_decode(vk_bytes.as_slice()).expect("pk_decode");
    let sp = sig_decode(sig_bytes.as_slice()).expect("sig_decode");
    let (tr_vec, _) = shake256(&[vk_bytes.as_slice()], 64);
    let mut tr = [0u8; 64];
    tr.copy_from_slice(&tr_vec);
    MlDsaVerifyInput::from_decoded(&pk, &sp, tr, msg.to_vec())
}

pub fn oracle_input(seed: u64, msg: &[u8]) -> MlDsaVerifyInput {
    oracle_input_from_key(&oracle_keypair(seed), msg)
}

pub fn witness_and_input(seed: u64, msg: &[u8]) -> (MlDsaWitness, MlDsaVerifyInput) {
    let input = oracle_input(seed, msg);
    let witness = generate_witness(&input).expect("witness");
    (witness, input)
}

pub fn witness_for(seed: u64, msg: &[u8]) -> MlDsaWitness {
    witness_and_input(seed, msg).0
}
