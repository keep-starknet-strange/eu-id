//! Feature-gated WO-S1 helpers for proving the SHA `xor_8` lookup relation
//! with Stwo's GKR LogUp argument.
//!
//! This module is intentionally SHA-local. The default LogUp path does not
//! import or call it unless `gkr-spike` is enabled.

use num_traits::{One, Zero};
use stwo::core::channel::Channel;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::Fraction;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::lookups::gkr_prover::{prove_batch, Layer};
use stwo::prover::lookups::gkr_verifier::{
    partially_verify_batch, Gate, GkrArtifact, GkrBatchProof, GkrError,
};
use stwo::prover::lookups::mle::Mle;
use stwo::prover::lookups::sumcheck::SumcheckProof;
use stwo::prover::lookups::utils::UnivariatePoly;
use stwo_constraint_framework::Relation;

use crate::constants::N_ROUNDS;
use crate::multiplicities::xor_8_multiplicities;
use crate::preprocessed::LOG_SIZE_16;
use crate::relations::Sha256Relations;
use crate::tables::build_xor_8_table;
use crate::trace::Layout;
use crate::types::{LimbPairBytes, Sha256Witness, SigmaDecodeWitness};

pub const XOR_8_GKR_INSTANCE_COUNT: usize = 17;

pub struct Xor8GkrProof {
    pub proof: GkrBatchProof,
    pub artifact: GkrArtifact,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Xor8GkrProofWire {
    pub sumcheck_round_polys: Vec<Vec<Vec<SecureField>>>,
    pub layer_masks_by_instance: Vec<Vec<Vec<[SecureField; 2]>>>,
    pub output_claims_by_instance: Vec<Vec<SecureField>>,
}

impl From<&GkrBatchProof> for Xor8GkrProofWire {
    fn from(proof: &GkrBatchProof) -> Self {
        Self {
            sumcheck_round_polys: proof
                .sumcheck_proofs
                .iter()
                .map(|sumcheck| {
                    sumcheck
                        .round_polys
                        .iter()
                        .map(|poly| poly.iter().copied().collect())
                        .collect()
                })
                .collect(),
            layer_masks_by_instance: proof
                .layer_masks_by_instance
                .iter()
                .map(|instance| {
                    instance
                        .iter()
                        .map(|mask| mask.columns().to_vec())
                        .collect()
                })
                .collect(),
            output_claims_by_instance: proof.output_claims_by_instance.clone(),
        }
    }
}

impl From<Xor8GkrProofWire> for GkrBatchProof {
    fn from(wire: Xor8GkrProofWire) -> Self {
        Self {
            sumcheck_proofs: wire
                .sumcheck_round_polys
                .into_iter()
                .map(|round_polys| SumcheckProof {
                    round_polys: round_polys.into_iter().map(UnivariatePoly::new).collect(),
                })
                .collect(),
            layer_masks_by_instance: wire
                .layer_masks_by_instance
                .into_iter()
                .map(|instance| {
                    instance
                        .into_iter()
                        .map(stwo::prover::lookups::gkr_verifier::GkrMask::new)
                        .collect()
                })
                .collect(),
            output_claims_by_instance: wire.output_claims_by_instance,
        }
    }
}

pub fn prove_xor_8_gkr(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    log_n_rows: u32,
    channel: &mut impl Channel,
) -> Xor8GkrProof {
    let layers = xor_8_layers(relations, witness, log_n_rows);
    let (proof, artifact) = prove_batch(channel, layers);
    Xor8GkrProof { proof, artifact }
}

pub fn verify_xor_8_gkr(
    proof: &GkrBatchProof,
    channel: &mut impl Channel,
) -> Result<GkrArtifact, GkrError> {
    partially_verify_batch(vec![Gate::LogUp; XOR_8_GKR_INSTANCE_COUNT], proof, channel)
}

pub fn xor_8_output_claims_balance(proof: &GkrBatchProof) -> bool {
    let sum = proof
        .output_claims_by_instance
        .iter()
        .map(|claims| {
            assert_eq!(claims.len(), 2, "LogUp output claim shape");
            Fraction::new(claims[0], claims[1])
        })
        .sum::<Fraction<SecureField, SecureField>>();
    sum.numerator == SecureField::zero()
}

pub fn xor_8_layers(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    log_n_rows: u32,
) -> Vec<Layer<SimdBackend>> {
    let mut layers = Vec::with_capacity(XOR_8_GKR_INSTANCE_COUNT);
    layers.push(xor_8_table_layer(relations, witness));
    layers.extend(xor_8_consumer_layers(relations, witness, log_n_rows));
    layers
}

fn xor_8_table_layer(relations: &Sha256Relations, witness: &Sha256Witness) -> Layer<SimdBackend> {
    let mults = xor_8_multiplicities(witness);
    let rows = build_xor_8_table();
    let mut numerators = Vec::with_capacity(1 << LOG_SIZE_16);
    let mut denominators = Vec::with_capacity(1 << LOG_SIZE_16);
    for (mult, row) in mults.into_iter().zip(rows) {
        numerators.push(-SecureField::from(BaseField::from(mult)));
        denominators.push(xor_8_denominator(relations, row.x, row.y, row.z));
    }
    Layer::LogUpGeneric {
        numerators: Mle::<SimdBackend, SecureField>::new(numerators.into_iter().collect()),
        denominators: Mle::<SimdBackend, SecureField>::new(denominators.into_iter().collect()),
    }
}

fn xor_8_consumer_layers(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    log_n_rows: u32,
) -> Vec<Layer<SimdBackend>> {
    let n_rows = 1usize << log_n_rows;
    let mut columns = (0..16)
        .map(|_| {
            (
                vec![SecureField::zero(); n_rows],
                vec![SecureField::one(); n_rows],
            )
        })
        .collect::<Vec<_>>();

    for (block_idx, block) in witness.blocks.iter().enumerate() {
        for t in 0..N_ROUNDS {
            let slot = Layout::round_row_slot(block_idx, t, log_n_rows);
            if t >= 16 {
                let entry = &block.schedule_entries[t - 16];
                fill_decode_layers(&mut columns, 0, slot, relations, &entry.lower_sigma0_decode);
                fill_decode_layers(&mut columns, 4, slot, relations, &entry.lower_sigma1_decode);
            }
            let round = &block.rounds[t];
            fill_decode_layers(&mut columns, 8, slot, relations, &round.sigma0_decode);
            fill_decode_layers(&mut columns, 12, slot, relations, &round.sigma1_decode);
        }
    }

    columns
        .into_iter()
        .map(|(numerators, denominators)| Layer::LogUpGeneric {
            numerators: Mle::<SimdBackend, SecureField>::new(numerators.into_iter().collect()),
            denominators: Mle::<SimdBackend, SecureField>::new(denominators.into_iter().collect()),
        })
        .collect()
}

fn fill_decode_layers(
    columns: &mut [(Vec<SecureField>, Vec<SecureField>)],
    base: usize,
    slot: usize,
    relations: &Sha256Relations,
    decode: &SigmaDecodeWitness,
) {
    for (chunk, (x, y, z)) in xor_8_chunks(decode).into_iter().enumerate() {
        columns[base + chunk].0[slot] = SecureField::one();
        columns[base + chunk].1[slot] = xor_8_denominator(relations, x, y, z);
    }
}

fn xor_8_chunks(decode: &SigmaDecodeWitness) -> [(u32, u32, u32); 4] {
    let s = decode.o2_chunks_s;
    let sc = decode.o2_chunks_s_complement;
    let combined = decode.o2_chunks_combined;
    [
        chunk_tuple(s, sc, combined, |chunks| chunks.lo.b0),
        chunk_tuple(s, sc, combined, |chunks| chunks.lo.b1),
        chunk_tuple(s, sc, combined, |chunks| chunks.hi.b0),
        chunk_tuple(s, sc, combined, |chunks| chunks.hi.b1),
    ]
}

fn chunk_tuple(
    s: LimbPairBytes,
    sc: LimbPairBytes,
    combined: LimbPairBytes,
    select: impl Fn(LimbPairBytes) -> u32,
) -> (u32, u32, u32) {
    (select(s), select(sc), select(combined))
}

fn xor_8_denominator(relations: &Sha256Relations, x: u32, y: u32, z: u32) -> SecureField {
    relations
        .xor_8
        .combine(&[BaseField::from(x), BaseField::from(y), BaseField::from(z)])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::relations::Sha256Relations;
    use crate::trace::min_log_size;
    use crate::witness::compute_sha256_witness;
    use stwo::core::channel::Blake2sChannel;

    #[test]
    fn xor_8_gkr_round_trip_balances_one_block() {
        let witness = compute_sha256_witness(b"abc");
        let log_n_rows = min_log_size(witness.blocks.len());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let mut prover_channel = Blake2sChannel::default();
        let gkr = prove_xor_8_gkr(&relations, &witness, log_n_rows, &mut prover_channel);

        assert!(xor_8_output_claims_balance(&gkr.proof));
        let mut verifier_channel = Blake2sChannel::default();
        let artifact =
            verify_xor_8_gkr(&gkr.proof, &mut verifier_channel).expect("GKR proof verifies");

        assert_eq!(
            artifact.n_variables_by_instance.len(),
            XOR_8_GKR_INSTANCE_COUNT
        );
        assert_eq!(artifact.n_variables_by_instance[0], LOG_SIZE_16 as usize);
        assert!(artifact.n_variables_by_instance[1..]
            .iter()
            .all(|&n| n == log_n_rows as usize));
    }

    #[test]
    fn xor_8_gkr_rejects_output_claim_tamper() {
        let witness = compute_sha256_witness(b"abc");
        let log_n_rows = min_log_size(witness.blocks.len());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let mut gkr = prove_xor_8_gkr(
            &relations,
            &witness,
            log_n_rows,
            &mut Blake2sChannel::default(),
        );
        gkr.proof.output_claims_by_instance[0][0] += SecureField::one();

        assert!(!xor_8_output_claims_balance(&gkr.proof));
        assert!(
            verify_xor_8_gkr(&gkr.proof, &mut Blake2sChannel::default()).is_err(),
            "tampered output claim must reject"
        );
    }

    #[test]
    fn xor_8_gkr_detects_consumer_chunk_mutation() {
        let mut witness = compute_sha256_witness(b"abc");
        let log_n_rows = min_log_size(witness.blocks.len());
        witness.blocks[0].rounds[0]
            .sigma0_decode
            .o2_chunks_combined
            .lo
            .b0 ^= 1;

        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let gkr = prove_xor_8_gkr(
            &relations,
            &witness,
            log_n_rows,
            &mut Blake2sChannel::default(),
        );

        assert!(
            !xor_8_output_claims_balance(&gkr.proof),
            "corrupted xor_8 consumer tuple must not balance against table multiplicities"
        );
    }

    #[test]
    fn xor_8_gkr_padding_rows_are_zero() {
        let witness = compute_sha256_witness(b"abc");
        let log_n_rows = min_log_size(witness.blocks.len()) + 1;
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let gkr = prove_xor_8_gkr(
            &relations,
            &witness,
            log_n_rows,
            &mut Blake2sChannel::default(),
        );

        assert!(xor_8_output_claims_balance(&gkr.proof));
        verify_xor_8_gkr(&gkr.proof, &mut Blake2sChannel::default())
            .expect("GKR proof verifies with zero-fraction padding rows");
    }
}
