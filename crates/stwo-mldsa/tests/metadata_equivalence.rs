//! Differential checks for witness metadata that is built before relation
//! challenges. Each direct census must match the full interaction output for
//! an ACVP vector and a seeded oracle signature.

use ml_dsa::signature::{Keypair, Signer};
use ml_dsa::{EncodedSignature, EncodedVerifyingKey, MlDsa65, SigningKey};
use num_traits::Zero;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use serde::Deserialize;
use stwo::core::fields::qm31::SecureField;

use stwo_mldsa::air_util::padded_log_size;
use stwo_mldsa::binding::{STREAM_ID_CTILDE_ABSORB, STREAM_ID_SIB_SQUEEZE};
use stwo_mldsa::coeffs::relations::CoeffsRelations;
use stwo_mldsa::coeffs::tables::RcKind as CoeffsRcKind;
use stwo_mldsa::coeffs::{gen_coeffs_interaction, gen_coeffs_rc_uses, layout as coeffs_layout};
use stwo_mldsa::constants::{K, N};
use stwo_mldsa::decomp::relations::DecompRelations;
use stwo_mldsa::decomp::{gen_decomp_interaction, gen_decomp_metadata, N_ROWS};
use stwo_mldsa::profile::ML_DSA_65;
use stwo_mldsa::reference::encoding::{pk_decode, sig_decode};
use stwo_mldsa::reference::sponge::shake256;
use stwo_mldsa::sampleinball::relations::SibRelations;
use stwo_mldsa::sampleinball::{
    gen_sib_interaction, gen_sib_metadata, MAX_SIB_SQUEEZE_BYTES, N_ACCESSES,
};
use stwo_mldsa::witness::{generate_witness, MlDsaWitness};
use stwo_mldsa::MlDsaVerifyInput;

fn input_from_wire(pk_bytes: &[u8], message: Vec<u8>, signature: &[u8]) -> MlDsaVerifyInput {
    let pk = pk_decode(ML_DSA_65, pk_bytes).expect("pk_decode");
    let signature = sig_decode(ML_DSA_65, signature).expect("sig_decode");
    let (tr, _) = shake256(&[pk_bytes], 64);
    let mut tr_array = [0u8; 64];
    tr_array.copy_from_slice(&tr);
    MlDsaVerifyInput::from_decoded(ML_DSA_65, &pk, &signature, tr_array, message)
}

#[derive(Deserialize)]
struct AcvpVectors {
    cases: Vec<AcvpCase>,
}

#[derive(Deserialize)]
struct AcvpCase {
    pk: String,
    message: String,
    #[serde(default)]
    context: String,
    signature: String,
    #[serde(rename = "testPassed")]
    test_passed: bool,
}

fn acvp_witness() -> MlDsaWitness {
    let vectors: AcvpVectors =
        serde_json::from_str(include_str!("vectors/mldsa65_sigver.json")).expect("ACVP vectors");
    let case = vectors
        .cases
        .into_iter()
        .find(|case| case.test_passed && case.context.is_empty())
        .expect("valid pure-mode ACVP case");
    let pk = hex::decode(case.pk).expect("ACVP pk hex");
    let message = hex::decode(case.message).expect("ACVP message hex");
    let signature = hex::decode(case.signature).expect("ACVP signature hex");
    generate_witness(ML_DSA_65, &input_from_wire(&pk, message, &signature)).expect("ACVP witness")
}

fn seeded_oracle_witness() -> MlDsaWitness {
    let mut rng = StdRng::seed_from_u64(0x4d45_5441_4441_5441);
    let mut seed = [0u8; 32];
    rng.fill(&mut seed);
    let signing_key = SigningKey::<MlDsa65>::from_seed(&seed.into());
    let verifying_key = signing_key.verifying_key();
    let message = b"metadata-equivalence-property".to_vec();
    let signature = signing_key.sign(&message);
    let pk: EncodedVerifyingKey<MlDsa65> = verifying_key.encode();
    let signature: EncodedSignature<MlDsa65> = signature.encode();
    generate_witness(
        ML_DSA_65,
        &input_from_wire(pk.as_slice(), message, signature.as_slice()),
    )
    .expect("seeded oracle witness")
}

fn encode_signed(value: i128) -> u32 {
    const P: i128 = (1 << 31) - 1;
    value.rem_euclid(P) as u32
}

#[test]
fn direct_metadata_matches_full_dry_interactions() {
    for (case, witness) in [
        ("acvp-kat", acvp_witness()),
        ("seeded-oracle", seeded_oracle_witness()),
    ] {
        let direct = gen_coeffs_rc_uses(&witness);
        let interaction = gen_coeffs_interaction(
            &witness,
            padded_log_size(coeffs_layout::active_rows()),
            SecureField::zero(),
            SecureField::zero(),
            &CoeffsRelations::dummy(),
        );
        for kind in CoeffsRcKind::ALL {
            assert_eq!(
                direct.for_kind(kind),
                interaction.rc_uses.for_kind(kind),
                "{case}: coeffs {kind:?}"
            );
        }
        drop(interaction);

        let direct = gen_decomp_metadata(&witness);
        let interaction = gen_decomp_interaction(
            &witness,
            padded_log_size(N_ROWS),
            STREAM_ID_CTILDE_ABSORB,
            &DecompRelations::dummy(),
        );
        for kind in CoeffsRcKind::ALL {
            assert_eq!(
                direct.rc_uses.for_kind(kind),
                interaction.rc_uses.for_kind(kind),
                "{case}: decomp {kind:?}"
            );
        }
        assert_eq!(
            direct.w1_encode_bytes, interaction.w1_encode_bytes,
            "{case}: decomp w1Encode"
        );
        let rows = &witness.rows;
        let expected_wcell_uses: Vec<_> = (0..K)
            .flat_map(|i| (0..N).map(move |m| ((i * N + m) as u32, rows[i].w[m])))
            .collect();
        assert_eq!(
            expected_wcell_uses, interaction.wcell_uses,
            "{case}: decomp WCell uses"
        );
        drop(interaction);

        let direct = gen_sib_metadata(&witness);
        let interaction = gen_sib_interaction(
            &witness,
            padded_log_size((MAX_SIB_SQUEEZE_BYTES + N).max(N_ACCESSES)),
            STREAM_ID_SIB_SQUEEZE,
            &SibRelations::dummy(),
        );
        for kind in CoeffsRcKind::ALL {
            assert_eq!(
                direct.rc_uses.for_kind(kind),
                interaction.rc_uses.for_kind(kind),
                "{case}: SIB {kind:?}"
            );
        }
        assert_eq!(
            direct.stream_bytes, interaction.stream_bytes,
            "{case}: SIB stream bytes"
        );
        let expected_ccell_uses: Vec<_> = witness
            .digits
            .c
            .iter()
            .enumerate()
            .map(|(m, &c)| (m as u32, encode_signed(c)))
            .collect();
        assert_eq!(
            expected_ccell_uses, interaction.ccell_uses,
            "{case}: SIB CCell uses"
        );
    }
}
