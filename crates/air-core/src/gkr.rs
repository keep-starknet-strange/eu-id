//! Serializable transport for Stwo's [`GkrBatchProof`].
//!
//! A module that offloads part of its LogUp into a GKR proof cannot ship that
//! proof inside the [`StarkProof`](stwo::core::proof::StarkProof) it commits —
//! `GkrBatchProof` is not part of the STARK wire. Instead the orchestrator
//! carries an opaque per-module byte payload beside the `StarkProof`
//! (`prove_with_post_interaction` → `verify_with_expected_preprocessed_root_and_payloads`),
//! and the module (de)serializes its own GKR proof with the helpers here.
//!
//! `GkrBatchProof` is a foreign type with no `serde` derives, so we mirror it
//! with owned `serde` structs built purely from its public accessors and
//! constructors ([`GkrMask::new`], [`SumcheckProof.round_polys`],
//! [`UnivariatePoly::new`]). The mirror is a faithful, lossless copy: encode
//! then decode round-trips to an identical proof.
//!
//! # Soundness
//!
//! This transport carries data only. It performs no verification. The GKR proof
//! is bound to the transcript when the module *replays* it against the shared
//! Fiat-Shamir channel inside `verify_post_interaction` (via
//! [`partially_verify_batch`](stwo::prover::lookups::gkr_verifier::partially_verify_batch)):
//! the channel state at that point already commits trees 1/2, the drawn
//! relations, and the claimed sums, so a tampered blob desynchronises the
//! channel and the sumcheck/circuit checks reject. Corruption of the bytes here
//! only ever produces a proof that fails that replay — it can never make a false
//! statement verify.

use bincode::Options;
use serde::{Deserialize, Serialize};
use stwo::core::fields::qm31::QM31;
use stwo::prover::lookups::gkr_verifier::{GkrBatchProof, GkrMask};
use stwo::prover::lookups::sumcheck::SumcheckProof;
use stwo::prover::lookups::utils::UnivariatePoly;

const TS13_DEMO_GKR_VARIABLE_COUNT: usize = 23;
const TS13_DEMO_GKR_MASK_COLUMN_COUNT: usize = 2;
const TS13_DEMO_GKR_OUTPUT_CLAIM_COUNT: usize = 2;
const TS13_DEMO_GKR_MAX_POLYNOMIAL_COEFFICIENTS: usize = 4;

/// Maximum canonical GKR payload size accepted by the TS13 demo profile.
pub const TS13_DEMO_GKR_MAX_PAYLOAD_BYTES: usize = 20_128;

/// `serde` mirror of [`GkrBatchProof`], built from its public surface.
#[derive(Serialize, Deserialize)]
struct GkrProofWire {
    /// Per layer: the sumcheck round polynomials, each a coefficient vector.
    /// `Vec<SumcheckProof>` → `Vec<round_polys>` → `Vec<UnivariatePoly>` → coeffs.
    sumcheck_round_polys: Vec<Vec<Vec<QM31>>>,
    /// Per instance, per layer: the mask columns (each column is two evals).
    layer_masks: Vec<Vec<Vec<[QM31; 2]>>>,
    /// Per instance: the output-layer column claims.
    output_claims: Vec<Vec<QM31>>,
}

/// Return whether an opaque payload has the frozen TS13 demo GKR wire shape.
///
/// This is a bounded, read-only structural check. It does not verify the GKR
/// proof; callers must still replay the decoded proof against the transcript.
pub fn is_ts13_demo_gkr_batch_proof_wire(bytes: &[u8]) -> bool {
    if bytes.len() > TS13_DEMO_GKR_MAX_PAYLOAD_BYTES {
        return false;
    }
    let Ok(wire) = bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_limit(TS13_DEMO_GKR_MAX_PAYLOAD_BYTES as u64)
        .reject_trailing_bytes()
        .deserialize::<GkrProofWire>(bytes)
    else {
        return false;
    };

    wire.sumcheck_round_polys.len() == TS13_DEMO_GKR_VARIABLE_COUNT
        && wire
            .sumcheck_round_polys
            .iter()
            .enumerate()
            .all(|(round, polynomials)| {
                polynomials.len() == round
                    && polynomials.iter().all(|coefficients| {
                        coefficients.len() <= TS13_DEMO_GKR_MAX_POLYNOMIAL_COEFFICIENTS
                    })
            })
        && matches!(
            wire.layer_masks.as_slice(),
            [layers]
                if layers.len() == TS13_DEMO_GKR_VARIABLE_COUNT
                    && layers
                        .iter()
                        .all(|columns| columns.len() == TS13_DEMO_GKR_MASK_COLUMN_COUNT)
        )
        && matches!(
            wire.output_claims.as_slice(),
            [claims] if claims.len() == TS13_DEMO_GKR_OUTPUT_CLAIM_COUNT
        )
}

/// Serialize a [`GkrBatchProof`] to an opaque byte payload.
pub fn encode_gkr_batch_proof(proof: &GkrBatchProof) -> Vec<u8> {
    let sumcheck_round_polys = proof
        .sumcheck_proofs
        .iter()
        .map(|sc| sc.round_polys.iter().map(|poly| poly.to_vec()).collect())
        .collect();
    let layer_masks = proof
        .layer_masks_by_instance
        .iter()
        .map(|layers| layers.iter().map(|mask| mask.columns().to_vec()).collect())
        .collect();
    let output_claims = proof.output_claims_by_instance.clone();
    let wire = GkrProofWire {
        sumcheck_round_polys,
        layer_masks,
        output_claims,
    };
    bincode::serialize(&wire).expect("GKR proof mirror serializes")
}

/// Reconstruct a [`GkrBatchProof`] from a byte payload produced by
/// [`encode_gkr_batch_proof`]. Returns `Err` on malformed bytes; callers must
/// treat that as a verification failure (fail-closed).
pub fn decode_gkr_batch_proof(bytes: &[u8]) -> Result<GkrBatchProof, bincode::Error> {
    let wire: GkrProofWire = bincode::deserialize(bytes)?;
    let sumcheck_proofs = wire
        .sumcheck_round_polys
        .into_iter()
        .map(|polys| SumcheckProof {
            round_polys: polys.into_iter().map(UnivariatePoly::new).collect(),
        })
        .collect();
    let layer_masks_by_instance = wire
        .layer_masks
        .into_iter()
        .map(|layers| layers.into_iter().map(GkrMask::new).collect())
        .collect();
    Ok(GkrBatchProof {
        sumcheck_proofs,
        layer_masks_by_instance,
        output_claims_by_instance: wire.output_claims,
    })
}

#[cfg(test)]
mod tests {
    use num_traits::Zero;

    use super::*;

    fn valid_ts13_demo_wire() -> GkrProofWire {
        let zero = QM31::zero();
        GkrProofWire {
            sumcheck_round_polys: (0..TS13_DEMO_GKR_VARIABLE_COUNT)
                .map(|round| {
                    (0..round)
                        .map(|_| vec![zero; TS13_DEMO_GKR_MAX_POLYNOMIAL_COEFFICIENTS])
                        .collect()
                })
                .collect(),
            layer_masks: vec![vec![
                vec![[zero; 2]; TS13_DEMO_GKR_MASK_COLUMN_COUNT];
                TS13_DEMO_GKR_VARIABLE_COUNT
            ]],
            output_claims: vec![vec![zero; TS13_DEMO_GKR_OUTPUT_CLAIM_COUNT]],
        }
    }

    fn encode_wire(wire: &GkrProofWire) -> Vec<u8> {
        bincode::serialize(wire).expect("test GKR wire serializes")
    }

    #[test]
    fn accepts_the_maximal_ts13_demo_wire() {
        let bytes = encode_wire(&valid_ts13_demo_wire());

        assert_eq!(bytes.len(), TS13_DEMO_GKR_MAX_PAYLOAD_BYTES);
        assert!(is_ts13_demo_gkr_batch_proof_wire(&bytes));
    }

    #[test]
    fn rejects_wrong_sumcheck_and_polynomial_counts() {
        let mut wrong_sumcheck_count = valid_ts13_demo_wire();
        wrong_sumcheck_count.sumcheck_round_polys.pop();
        assert!(!is_ts13_demo_gkr_batch_proof_wire(&encode_wire(
            &wrong_sumcheck_count
        )));

        let mut wrong_polynomial_count = valid_ts13_demo_wire();
        wrong_polynomial_count.sumcheck_round_polys[0].push(Vec::new());
        assert!(!is_ts13_demo_gkr_batch_proof_wire(&encode_wire(
            &wrong_polynomial_count
        )));
    }

    #[test]
    fn rejects_polynomials_above_the_coefficient_bound() {
        let mut wire = valid_ts13_demo_wire();
        wire.sumcheck_round_polys[1][0].push(QM31::zero());

        assert!(!is_ts13_demo_gkr_batch_proof_wire(&encode_wire(&wire)));
    }

    #[test]
    fn rejects_wrong_layer_mask_dimensions() {
        let mut wrong_instance_count = valid_ts13_demo_wire();
        wrong_instance_count.layer_masks.push(Vec::new());
        assert!(!is_ts13_demo_gkr_batch_proof_wire(&encode_wire(
            &wrong_instance_count
        )));

        let mut wrong_layer_count = valid_ts13_demo_wire();
        wrong_layer_count.layer_masks[0].pop();
        assert!(!is_ts13_demo_gkr_batch_proof_wire(&encode_wire(
            &wrong_layer_count
        )));

        let mut wrong_column_count = valid_ts13_demo_wire();
        wrong_column_count.layer_masks[0][0].pop();
        assert!(!is_ts13_demo_gkr_batch_proof_wire(&encode_wire(
            &wrong_column_count
        )));
    }

    #[test]
    fn rejects_wrong_output_claim_dimensions() {
        let mut wrong_instance_count = valid_ts13_demo_wire();
        wrong_instance_count.output_claims.push(Vec::new());
        assert!(!is_ts13_demo_gkr_batch_proof_wire(&encode_wire(
            &wrong_instance_count
        )));

        let mut wrong_claim_count = valid_ts13_demo_wire();
        wrong_claim_count.output_claims[0].pop();
        assert!(!is_ts13_demo_gkr_batch_proof_wire(&encode_wire(
            &wrong_claim_count
        )));
    }

    #[test]
    fn rejects_oversized_and_trailing_payloads() {
        let mut oversized = encode_wire(&valid_ts13_demo_wire());
        oversized.push(0);
        assert!(!is_ts13_demo_gkr_batch_proof_wire(&oversized));

        let mut shorter = valid_ts13_demo_wire();
        shorter.sumcheck_round_polys[1][0].pop();
        let mut trailing = encode_wire(&shorter);
        trailing.push(0);
        assert!(trailing.len() <= TS13_DEMO_GKR_MAX_PAYLOAD_BYTES);
        assert!(!is_ts13_demo_gkr_batch_proof_wire(&trailing));
    }
}
