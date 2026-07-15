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

use serde::{Deserialize, Serialize};
use stwo::core::fields::qm31::QM31;
use stwo::prover::lookups::gkr_verifier::{GkrBatchProof, GkrMask};
use stwo::prover::lookups::sumcheck::SumcheckProof;
use stwo::prover::lookups::utils::UnivariatePoly;

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
