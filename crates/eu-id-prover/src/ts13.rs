//! Sorted-pair revocation primitives used by the product mdoc proof.

use ecdsa::signature::hazmat::PrehashVerifier;
use p256::ecdsa::{Signature as P256Signature, SigningKey, VerifyingKey};
use p256::EncodedPoint;
use sha2::{Digest, Sha256};
use stwo_p256::types::{AffinePoint, Signature, U256};

use crate::mdoc::{ExtractedPidMdoc, MdocRevocationPublicInputs};
use crate::product_profile::PRODUCT_TS13_REVOCATION_MESSAGE_BYTES;

const DEMO_TS13_REVOCATION_SIGNING_KEY: [u8; 32] = [33; 32];
const DEMO_TS13_REVOCATION_EPOCH: u32 = 51;

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

fn demo_ts13_revocation_signing_key() -> SigningKey {
    SigningKey::from_bytes((&DEMO_TS13_REVOCATION_SIGNING_KEY).into()).expect("demo revocation key")
}

/// Returns the fixed public P-256 authority statement used by demo TS13 revocation inputs.
pub fn demo_ts13_revocation_statement() -> Ts13RevocationStatement {
    let signing_key = demo_ts13_revocation_signing_key();
    let encoded = signing_key.verifying_key().to_encoded_point(false);
    let x: [u8; 32] = encoded.x().expect("x")[..].try_into().expect("x len");
    let y: [u8; 32] = encoded.y().expect("y")[..].try_into().expect("y len");
    Ts13RevocationStatement {
        revocation_public_key: AffinePoint {
            x: U256(x),
            y: U256(y),
        },
        epoch: DEMO_TS13_REVOCATION_EPOCH,
    }
}

/// Builds deterministic demo revocation inputs.
///
/// Product tests and benchmarks use these inputs.
/// They use a fixed authority key, epoch 51, and adjacent sorted-pair bounds.
pub fn demo_ts13_revocation_inputs(mso: &[u8]) -> (Ts13RevocationStatement, Ts13RevocationWitness) {
    use ecdsa::signature::hazmat::PrehashSigner;

    let statement = demo_ts13_revocation_statement();
    let id = ts13_mso_derived_revocation_id(mso);
    let (id_lo, id_hi) = (id.saturating_sub(1), id.saturating_add(1));
    let message_hash = ts13_revocation_message_hash(id_lo, id_hi, statement.epoch);
    let pair_signature: P256Signature = demo_ts13_revocation_signing_key()
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
    Sha256::digest(ts13_revocation_message_bytes(id_lo, id_hi, epoch)).into()
}

pub(crate) fn ts13_revocation_message_bytes(
    id_lo: u64,
    id_hi: u64,
    epoch: u32,
) -> [u8; PRODUCT_TS13_REVOCATION_MESSAGE_BYTES] {
    let mut message = [0u8; PRODUCT_TS13_REVOCATION_MESSAGE_BYTES];
    message[..8].copy_from_slice(&id_lo.to_le_bytes());
    message[8..16].copy_from_slice(&id_hi.to_le_bytes());
    message[16..].copy_from_slice(&epoch.to_le_bytes());
    message
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
    let mut bytes = [0u8; 64];
    bytes[..32].copy_from_slice(&signature.r.0);
    bytes[32..].copy_from_slice(&signature.s.0);
    P256Signature::from_slice(&bytes).map_err(|_| Ts13RevocationError::InvalidSignatureEncoding)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn demo_inputs_use_the_canonical_public_statement() {
        let (statement, witness) = demo_ts13_revocation_inputs(b"demo mso");

        assert_eq!(statement, demo_ts13_revocation_statement());
        assert_eq!(witness.epoch, statement.epoch);
    }

    #[test]
    fn demo_public_statement_verifies_the_input_signature() {
        let (statement, witness) = demo_ts13_revocation_inputs(b"demo mso");
        let verifying_key = verifying_key_from_affine(&statement.revocation_public_key)
            .expect("demo public key is valid");
        let signature =
            p256_signature_from_stwo(&witness.signature).expect("demo signature is valid");
        let message_hash =
            ts13_revocation_message_hash(witness.id_lo, witness.id_hi, witness.epoch);

        verifying_key
            .verify_prehash(&message_hash, &signature)
            .expect("demo statement and witness use the same authority");
    }

    #[test]
    fn revocation_message_has_the_canonical_little_endian_layout() {
        let message = ts13_revocation_message_bytes(
            0x0706_0504_0302_0100,
            0x0f0e_0d0c_0b0a_0908,
            0x1312_1110,
        );
        assert_eq!(
            message,
            [
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
                0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13,
            ]
        );
    }
}
