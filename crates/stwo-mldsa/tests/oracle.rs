//! Property-test the reference verifier against the RustCrypto `ml-dsa` oracle.
//!
//! `ml-dsa` (FIPS 204 final) generates keypairs + pure-mode signatures; our
//! from-scratch reference must accept every honest one and reject every
//! mutated one. Our runtime code never depends on `ml-dsa` — it is a
//! dev-dependency, used only here to manufacture ground-truth vectors.

use ml_dsa::signature::{Keypair, Signer, Verifier};
use ml_dsa::{EncodedSignature, EncodedVerifyingKey, MlDsa44, MlDsa65, SigningKey};
use rand::{rngs::StdRng, Rng, SeedableRng};
use stwo_mldsa::profile::{ML_DSA_44, ML_DSA_65};
use stwo_mldsa::reference::encoding::{pk_decode_for, sig_decode_for};
use stwo_mldsa::reference::verify::{verify, verify_internals, verify_internals_for};

/// N random keypairs + signatures; the reference accepts all.
const N: usize = 200;

fn oracle_keypair(rng: &mut StdRng) -> SigningKey<MlDsa65> {
    let mut seed = [0u8; 32];
    rng.fill(&mut seed);
    SigningKey::<MlDsa65>::from_seed(&seed.into())
}

/// Sign `msg` (pure, empty context — `Signer::sign`) and return encoded
/// `(pk, sig)` byte vectors, matching what our reference ingests.
fn oracle_sign(sk: &SigningKey<MlDsa65>, msg: &[u8]) -> (Vec<u8>, Vec<u8>) {
    let vk = sk.verifying_key();
    let sig = sk.sign(msg);
    // Sanity: the oracle itself accepts what it produced.
    assert!(vk.verify(msg, &sig).is_ok());
    let vk_bytes: EncodedVerifyingKey<MlDsa65> = vk.encode();
    let sig_bytes: EncodedSignature<MlDsa65> = sig.encode();
    (vk_bytes.to_vec(), sig_bytes.to_vec())
}

fn oracle_sign44(sk: &SigningKey<MlDsa44>, msg: &[u8]) -> (Vec<u8>, Vec<u8>) {
    let vk = sk.verifying_key();
    let sig = sk.sign(msg);
    assert!(vk.verify(msg, &sig).is_ok());
    let vk_bytes: EncodedVerifyingKey<MlDsa44> = vk.encode();
    let sig_bytes: EncodedSignature<MlDsa44> = sig.encode();
    (vk_bytes.to_vec(), sig_bytes.to_vec())
}

#[test]
fn reference_interoperates_with_rustcrypto_mldsa44() {
    let mut rng = StdRng::seed_from_u64(0xD5A4_4000_0001);
    let mut seed = [0u8; 32];
    rng.fill(&mut seed);
    let key = SigningKey::<MlDsa44>::from_seed(&seed.into());
    let message = b"RustCrypto ML-DSA-44 device authentication";
    let (public_key, signature) = oracle_sign44(&key, message);

    let trace = verify_internals_for(ML_DSA_44, &public_key, message, &signature)
        .expect("decode RustCrypto ML-DSA-44 signature");
    assert!(trace.accepted, "accept RustCrypto ML-DSA-44 signature");
    assert_eq!(trace.c_tilde_prime, trace.c_tilde);
}

#[test]
fn profile_specific_decoders_reject_cross_profile_wires() {
    let mut rng = StdRng::seed_from_u64(0xD5A4_4000_0002);
    let mut seed44 = [0u8; 32];
    let mut seed65 = [0u8; 32];
    rng.fill(&mut seed44);
    rng.fill(&mut seed65);
    let key44 = SigningKey::<MlDsa44>::from_seed(&seed44.into());
    let key65 = SigningKey::<MlDsa65>::from_seed(&seed65.into());
    let (pk44, sig44) = oracle_sign44(&key44, b"profile 44");
    let (pk65, sig65) = oracle_sign(&key65, b"profile 65");

    assert!(pk_decode_for(ML_DSA_65, &pk44).is_err());
    assert!(sig_decode_for(ML_DSA_65, &sig44).is_err());
    assert!(pk_decode_for(ML_DSA_44, &pk65).is_err());
    assert!(sig_decode_for(ML_DSA_44, &sig65).is_err());
}

#[test]
fn reference_accepts_all_oracle_signatures() {
    let mut rng = StdRng::seed_from_u64(0xD5A6_5000_0001);
    for i in 0..N {
        let sk = oracle_keypair(&mut rng);
        let mut msg = vec![0u8; 1 + (i % 64)];
        rng.fill(msg.as_mut_slice());
        let (pk, sig) = oracle_sign(&sk, &msg);

        let trace = verify_internals(&pk, &msg, &sig)
            .unwrap_or_else(|e| panic!("case {i}: decode error {e}"));
        assert!(
            trace.accepted,
            "case {i}: reference rejected a valid oracle signature: {:?}",
            trace.reason
        );
        // The recomputed commitment must equal the signature's c̃.
        assert_eq!(trace.c_tilde_prime, trace.c_tilde, "case {i}: c̃ mismatch");
    }
}

#[test]
fn reference_rejects_mutations() {
    let mut rng = StdRng::seed_from_u64(0xD5A6_5000_0002);
    let mut mutations = 0usize;
    for i in 0..N {
        let sk = oracle_keypair(&mut rng);
        let mut msg = vec![0u8; 8 + (i % 40)];
        rng.fill(msg.as_mut_slice());
        let (pk, sig) = oracle_sign(&sk, &msg);
        assert!(verify(&pk, &msg, &sig), "baseline must verify (case {i})");

        // (a) flip a byte deep in the signature's z region (past c̃).
        let mut bad_sig = sig.clone();
        let z_off = stwo_mldsa::constants::C_TILDE_BYTES + 100;
        bad_sig[z_off] ^= 0x01;
        assert!(
            !verify(&pk, &msg, &bad_sig),
            "case {i}: mutated signature verified"
        );
        mutations += 1;

        // (b) flip a byte in the message.
        let mut bad_msg = msg.clone();
        bad_msg[0] ^= 0x80;
        assert!(
            !verify(&pk, &bad_msg, &sig),
            "case {i}: mutated message verified"
        );
        mutations += 1;

        // (c) flip a byte in t1 region of the public key (past ρ).
        let mut bad_pk = pk.clone();
        bad_pk[40] ^= 0x01;
        assert!(
            !verify(&bad_pk, &msg, &sig),
            "case {i}: mutated public key verified"
        );
        mutations += 1;
    }
    assert_eq!(mutations, N * 3, "expected 3 mutation-negatives per case");
    eprintln!("mutation-negatives exercised: {mutations}");
}
