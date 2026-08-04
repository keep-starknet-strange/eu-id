//! Sorted-pair revocation primitives used by the product mdoc proof.

use ecdsa::signature::hazmat::PrehashVerifier;
use p256::ecdsa::{Signature as P256Signature, VerifyingKey};
use p256::EncodedPoint;
use sha2::{Digest, Sha256};
use stwo_p256::types::{AffinePoint, Signature, U256};

use crate::mdoc::{ExtractedPidMdoc, MdocRevocationPublicInputs};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ts13RevocationStatement {
    pub revocation_public_key: AffinePoint,
    pub epoch: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Revocation values that the prover uses.
///
/// Keep this value on the prover side. Do not serialize it into a public proof
/// envelope.
pub struct Ts13RevocationWitness {
    pub id: u64,
    pub id_lo: u64,
    pub id_hi: u64,
    pub epoch: u32,
    pub signature: Signature,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ts13RevocationError {
    DerivedIdMismatch,
    SentinelId,
    Range,
    Epoch,
    InvalidPublicKey,
    InvalidSignatureEncoding,
    InvalidSignature,
}

impl From<&Ts13RevocationStatement> for MdocRevocationPublicInputs {
    fn from(statement: &Ts13RevocationStatement) -> Self {
        Self {
            revocation_public_key: statement.revocation_public_key.clone(),
            epoch: statement.epoch,
        }
    }
}

impl Ts13RevocationStatement {
    pub fn verify_witness(
        &self,
        extracted: &ExtractedPidMdoc,
        witness: &Ts13RevocationWitness,
    ) -> Result<(), Ts13RevocationError> {
        let derived_id = ts13_mso_derived_revocation_id(&extracted.mso);
        if derived_id == 0 || derived_id == u64::MAX {
            return Err(Ts13RevocationError::SentinelId);
        }
        if witness.id != derived_id {
            return Err(Ts13RevocationError::DerivedIdMismatch);
        }
        if !(witness.id_lo < witness.id && witness.id < witness.id_hi) {
            return Err(Ts13RevocationError::Range);
        }
        if witness.epoch != self.epoch {
            return Err(Ts13RevocationError::Epoch);
        }

        let verifying_key = verifying_key_from_affine(&self.revocation_public_key)?;
        let signature = p256_signature_from_stwo(&witness.signature)?;
        let message_hash =
            ts13_revocation_message_hash(witness.id_lo, witness.id_hi, witness.epoch);
        verifying_key
            .verify_prehash(&message_hash, &signature)
            .map_err(|_| Ts13RevocationError::InvalidSignature)
    }
}

/// Builds deterministic demo revocation inputs.
///
/// Product tests and benchmarks use these inputs.
/// They use a fixed authority key, epoch 51, and adjacent sorted-pair bounds.
pub fn demo_ts13_revocation_inputs(mso: &[u8]) -> (Ts13RevocationStatement, Ts13RevocationWitness) {
    use ecdsa::signature::hazmat::PrehashSigner;
    use p256::ecdsa::SigningKey;

    let signing_key = SigningKey::from_bytes((&[33u8; 32]).into()).expect("demo revocation key");
    let encoded = signing_key.verifying_key().to_encoded_point(false);
    let x: [u8; 32] = encoded.x().expect("x")[..].try_into().expect("x len");
    let y: [u8; 32] = encoded.y().expect("y")[..].try_into().expect("y len");
    let statement = Ts13RevocationStatement {
        revocation_public_key: AffinePoint {
            x: U256(x),
            y: U256(y),
        },
        epoch: 51,
    };
    let id = ts13_mso_derived_revocation_id(mso);
    let (id_lo, id_hi) = (id.saturating_sub(1), id.saturating_add(1));
    let message_hash = ts13_revocation_message_hash(id_lo, id_hi, statement.epoch);
    let pair_signature: P256Signature = signing_key
        .sign_prehash(&message_hash)
        .expect("demo revocation prehash signs");
    let r: [u8; 32] = pair_signature.r().to_bytes().into();
    let s: [u8; 32] = pair_signature.s().to_bytes().into();
    let witness = Ts13RevocationWitness {
        id,
        id_lo,
        id_hi,
        epoch: statement.epoch,
        signature: Signature {
            r: U256(r),
            s: U256(s),
        },
    };
    (statement, witness)
}

pub fn ts13_mso_derived_revocation_id(mso: &[u8]) -> u64 {
    let digest = Sha256::digest(mso);
    let bytes: [u8; 8] = digest[..8]
        .try_into()
        .expect("SHA-256 digest always has at least eight bytes");
    u64::from_le_bytes(bytes)
}

pub fn ts13_revocation_message_hash(id_lo: u64, id_hi: u64, epoch: u32) -> [u8; 32] {
    let mut message = Vec::with_capacity(20);
    message.extend_from_slice(&id_lo.to_le_bytes());
    message.extend_from_slice(&id_hi.to_le_bytes());
    message.extend_from_slice(&epoch.to_le_bytes());
    Sha256::digest(message).into()
}

fn verifying_key_from_affine(
    public_key: &AffinePoint,
) -> Result<VerifyingKey, Ts13RevocationError> {
    let encoded = EncodedPoint::from_affine_coordinates(
        (&public_key.x.0).into(),
        (&public_key.y.0).into(),
        false,
    );
    VerifyingKey::from_encoded_point(&encoded).map_err(|_| Ts13RevocationError::InvalidPublicKey)
}

fn p256_signature_from_stwo(signature: &Signature) -> Result<P256Signature, Ts13RevocationError> {
    let mut bytes = Vec::with_capacity(64);
    bytes.extend_from_slice(&signature.r.0);
    bytes.extend_from_slice(&signature.s.0);
    P256Signature::from_slice(&bytes).map_err(|_| Ts13RevocationError::InvalidSignatureEncoding)
}
