//! Current ISO mdoc PID proof implementation used by the SDK.
//!
//! The proof uses one source-bound profile. It checks issuer and device P-256
//! signatures, signed attribute digests, device binding, strict validity,
//! private predicates, request context, and sorted-pair revocation.
//! “Private” describes witness placement. Full transcript zero knowledge is
//! future work.
pub mod mdoc;
pub(crate) mod mdoc_cbor_stream;
pub(crate) mod mdoc_mac;
pub(crate) mod mdoc_scope;
mod mdoc_validity;
pub mod product_profile;
pub mod ts13;

pub use mdoc::{
    MdocCircuitProof as MdocProof, MdocPidRequest, MdocPublicStatement as MdocStatement,
    MdocRevocationRequest,
};
pub use predicates::Date;
pub use product_profile::{is_assigned_iso_alpha2, Policy};

/// Build and prove the product mdoc circuit from the full document, verifier
/// request, and public policy. Returns both the proof and verifier statement.
pub fn prove_mdoc(
    document: &[u8],
    request: &MdocPidRequest,
    policy: Policy,
) -> Result<(MdocProof, MdocStatement), Error> {
    if request.request_binding == [0; 32] {
        return Err(Error::RequestBindingMissing);
    }
    let verification_time_epoch_seconds = request.verification_time_epoch_seconds;
    let revocation = &request.revocation;
    mdoc::validate_product_mdoc_request(request).map_err(Error::Mdoc)?;
    if document.len() > mdoc::PRODUCT_MDOC_CBOR_MAX_BYTES {
        return Err(Error::Mdoc(mdoc::MdocError::InputTooLarge {
            input: "document",
            actual: document.len(),
            maximum: mdoc::PRODUCT_MDOC_CBOR_MAX_BYTES,
        }));
    }
    mdoc::validate_product_mdoc_cbor_structure(document).map_err(Error::Mdoc)?;
    let extracted = mdoc::extract_product_pid_mdoc(document, request).map_err(Error::Mdoc)?;
    let statement = mdoc::MdocCircuitStatement::from_extracted_at(
        &extracted,
        policy,
        verification_time_epoch_seconds,
    )
    .map_err(Error::Mdoc)?;
    let public_statement = ts13::Ts13RevocationStatement {
        revocation_public_key: revocation.public_inputs.revocation_public_key.clone(),
        epoch: revocation.public_inputs.epoch,
    };
    let id = ts13::ts13_mso_derived_revocation_id(&extracted.mso);
    let private_witness = ts13::Ts13RevocationWitness {
        id,
        id_lo: revocation.id_lo,
        id_hi: revocation.id_hi,
        epoch: revocation.public_inputs.epoch,
        signature: revocation.signature.clone(),
    };
    public_statement
        .verify_witness(&extracted, &private_witness)
        .map_err(Error::Revocation)?;
    let expected_range = mdoc::MdocRevocationRangeWitness {
        id,
        id_lo: revocation.id_lo,
        id_hi: revocation.id_hi,
    };
    if statement.ts13_revocation != revocation.public_inputs {
        return Err(Error::Mdoc(mdoc::MdocError::RevocationRequestMismatch(
            "public inputs",
        )));
    }
    if statement.ts13_revocation_range != expected_range {
        return Err(Error::Mdoc(mdoc::MdocError::RevocationRequestMismatch(
            "range witness",
        )));
    }
    if statement.ts13_revocation_signature != revocation.signature {
        return Err(Error::Mdoc(mdoc::MdocError::RevocationRequestMismatch(
            "authority signature",
        )));
    }
    let proof = mdoc::prove_mdoc_circuit(&extracted, &statement)?;
    Ok((proof, MdocStatement::from_circuit(&statement)))
}

/// Verify the source-bound product profile, including mandatory revocation and
/// bounded proof shape.
pub fn verify_product_mdoc(proof: &MdocProof, statement: &MdocStatement) -> Result<(), Error> {
    mdoc::verify_product_mdoc_public_statement(proof, statement)
}

use blake2::{Blake2s256, Digest as BlakeDigest};
use stwo::core::channel::Channel;
use stwo::core::pcs::PcsConfig;

pub(crate) mod ec_coprocessor {
    use eu_id_ec_coprocessor::ecdsa::{
        EcdsaInput as S4EcdsaInput, EcdsaPublicProjection as S4EcdsaPublicProjection,
        ImplementedCircuitBundle, ImplementedCircuitProofError, ValidatedWitness, WitnessError,
    };
    use eu_id_ec_coprocessor::TranscriptSeed;
    use stwo_p256::types::EcdsaVerifyInput;

    fn input_from_stwo(input: &EcdsaVerifyInput) -> S4EcdsaInput {
        S4EcdsaInput {
            z: input.message_hash.0,
            r: input.signature.r.0,
            s: input.signature.s.0,
            qx: input.public_key.x.0,
            qy: input.public_key.y.0,
        }
    }

    pub(crate) fn public_key_projection_from_stwo(
        input: &EcdsaVerifyInput,
    ) -> S4EcdsaPublicProjection {
        S4EcdsaPublicProjection::public_key_only(input.public_key.x.0, input.public_key.y.0)
    }

    pub(crate) fn issuer_key_projection_from_stwo(
        input: &EcdsaVerifyInput,
    ) -> S4EcdsaPublicProjection {
        public_key_projection_from_stwo(input)
    }

    pub(crate) fn message_hash_projection_from_stwo(
        input: &EcdsaVerifyInput,
    ) -> S4EcdsaPublicProjection {
        S4EcdsaPublicProjection::message_hash_only(input.message_hash.0)
    }

    pub(crate) fn generate_validated_witness_from_stwo(
        input: &EcdsaVerifyInput,
    ) -> Result<ValidatedWitness, WitnessError> {
        ValidatedWitness::generate(input_from_stwo(input))
    }

    pub(crate) fn implemented_circuit_transcript_shapes_from_stwo() -> Result<
        Vec<eu_id_ec_coprocessor::ecdsa::CircuitTranscriptShape>,
        eu_id_ec_coprocessor::CircuitError,
    > {
        eu_id_ec_coprocessor::ecdsa::implemented_circuit_transcript_shapes()
    }

    pub(crate) fn public_projection_transcript_segments(
        projection: &S4EcdsaPublicProjection,
    ) -> Vec<Vec<u8>> {
        eu_id_ec_coprocessor::ecdsa::ecdsa_public_projection_transcript_segments(projection)
    }

    pub(crate) fn prove_mdoc_p4b_circuit_bundle_from_validated(
        issuer: &ValidatedWitness,
        device: &ValidatedWitness,
        revocation: &ValidatedWitness,
        mac_key_shares: &eu_id_ec_coprocessor::ecdsa::MdocP4bMacKeyShares,
        transcript_seed: TranscriptSeed,
    ) -> Result<ImplementedCircuitBundle, ImplementedCircuitProofError> {
        eu_id_ec_coprocessor::ecdsa::prove_mdoc_p4b_circuit_bundle_from_validated(
            issuer,
            device,
            revocation,
            mac_key_shares,
            transcript_seed,
        )
    }

    pub(crate) fn verify_mdoc_p4b_circuit_bundle_from_stwo(
        issuer_projection: &S4EcdsaPublicProjection,
        device_projection: &S4EcdsaPublicProjection,
        revocation_projection: &S4EcdsaPublicProjection,
        bundle: &ImplementedCircuitBundle,
        transcript_seed: TranscriptSeed,
    ) -> Result<(), ImplementedCircuitProofError> {
        eu_id_ec_coprocessor::ecdsa::verify_mdoc_p4b_circuit_bundle(
            issuer_projection,
            device_projection,
            revocation_projection,
            bundle,
            transcript_seed,
        )
    }

    pub(crate) fn mdoc_p4b_av_from_bundle(
        bundle: &ImplementedCircuitBundle,
        transcript_seed: TranscriptSeed,
    ) -> eu_id_ec_coprocessor::mac::Gf128 {
        eu_id_ec_coprocessor::ecdsa::mdoc_p4b_av_from_root(transcript_seed, bundle.root)
    }
}

/// Errors from proving or verifying the product mdoc proof.
#[derive(Debug)]
pub enum Error {
    AgePrepare(predicates::Error),
    NatPrepare(predicates::NatError),
    Mdoc(mdoc::MdocError),
    RequestBindingMissing,
    Revocation(ts13::Ts13RevocationError),
    Prove(String),
    P256InstanceMismatch,
    AgePolicyMismatch,
    NatPolicyMismatch,
    CoprocessorMissing,
    CoprocessorWitness(eu_id_ec_coprocessor::ecdsa::WitnessError),
    Verify(String),
    WeakConfig {
        got: PcsConfig,
        expected: PcsConfig,
    },
    PreprocessedRootMismatch {
        got: air_core::CommitmentRoot,
        expected: air_core::CommitmentRoot,
    },
}

fn mix_channel_bytes(channel: &mut air_core::Ch, bytes: &[u8]) {
    channel.mix_u64(bytes.len() as u64);
    let mut words = Vec::with_capacity(bytes.len().div_ceil(4));
    for chunk in bytes.chunks(4) {
        let mut word = [0u8; 4];
        word[..chunk.len()].copy_from_slice(chunk);
        words.push(u32::from_le_bytes(word));
    }
    channel.mix_u32s(&words);
}

fn draw_coprocessor_seed(channel: &mut air_core::Ch) -> eu_id_ec_coprocessor::TranscriptSeed {
    let words = channel.draw_u32s();
    assert_eq!(words.len(), 8, "Blake2s channel draws 32 bytes");
    let mut seed = [0u8; 32];
    for (chunk, word) in seed.chunks_exact_mut(4).zip(words) {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    seed
}

#[cfg(test)]
fn channel_digest(channel: &air_core::Ch) -> [u8; 32] {
    channel.digest().0
}

fn mix_coprocessor_tagged_projections(
    channel: &mut air_core::Ch,
    tagged_projections: &[(&[u8], &eu_id_ec_coprocessor::ecdsa::EcdsaPublicProjection)],
) -> Result<(), String> {
    mix_channel_bytes(channel, b"eu-id-ec-coproc-v2");
    mix_channel_bytes(channel, b"s4-ecdsa-circuit-shape-v2");
    let shapes = ec_coprocessor::implemented_circuit_transcript_shapes_from_stwo()
        .map_err(|error| format!("{error:?}"))?;
    channel.mix_u64(shapes.len() as u64);
    for shape in shapes {
        mix_channel_bytes(channel, shape.label);
        channel.mix_u64(shape.layers.len() as u64);
        for (output_log_size, input_log_size) in shape.layers {
            channel.mix_u64(output_log_size as u64);
            channel.mix_u64(input_log_size as u64);
        }
    }

    mix_channel_bytes(channel, b"eu-id-ec-coproc-public-projections-v2");
    channel.mix_u64(tagged_projections.len() as u64);
    for (tag, projection) in tagged_projections {
        mix_channel_bytes(channel, tag);
        for segment in ec_coprocessor::public_projection_transcript_segments(projection) {
            mix_channel_bytes(channel, &segment);
        }
    }
    Ok(())
}

fn coprocessor_bundle_hash(
    bundle: &eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle,
) -> Result<[u8; 32], String> {
    let bytes = bincode::serialize(bundle).map_err(|error| error.to_string())?;
    let digest = Blake2s256::digest(bytes);
    let mut output = [0u8; 32];
    output.copy_from_slice(&digest);
    Ok(output)
}

fn mix_coprocessor_rejoin(
    channel: &mut air_core::Ch,
    bundle: &eu_id_ec_coprocessor::ecdsa::ImplementedCircuitBundle,
) -> Result<(), String> {
    let hash = coprocessor_bundle_hash(bundle)?;
    mix_channel_bytes(channel, b"eu-id-ec-coproc-rejoin-v1");
    mix_channel_bytes(channel, &hash);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn product_prove_rejects_zero_request_binding_before_proving() {
        let fixture = mdoc::demo_mdoc_circuit_fixture();
        let mut request = fixture.request;
        request.request_binding = [0; 32];
        assert!(matches!(
            prove_mdoc(&fixture.document, &request, fixture.statement.policy),
            Err(Error::RequestBindingMissing)
        ));
    }
}
