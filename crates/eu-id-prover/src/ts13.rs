//! TS13 profile capacity limits and revocation encodings.
//!
//! ## Revocation binding
//!
//! The revocation ID derives from the MSO bytes.
//! The revocation message encodes the sorted ID pair and the epoch.
//! The revocation authority signs this message with ML-DSA.

use sha2::{Digest, Sha256};

/// Maximum MSO payload length in bytes that the TS13 profile accepts.
pub const TS13_MAX_MSO_PAYLOAD_BYTES: usize = 4_096;
/// Maximum issuer ML-DSA message length in bytes that the TS13 profile accepts.
pub const TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES: usize = 4_160;
/// Maximum mdoc document length in bytes that the TS13 profile accepts.
pub const TS13_MAX_DOCUMENT_BYTES: usize = 16_384;

/// Derive the revocation ID from the first eight SHA-256 digest bytes of the MSO, in
/// little-endian order.
pub fn ts13_mso_derived_revocation_id(mso: &[u8]) -> u64 {
    let digest = Sha256::digest(mso);
    let bytes: [u8; 8] = digest[..8]
        .try_into()
        .expect("SHA-256 output has at least eight bytes");
    u64::from_le_bytes(bytes)
}

/// Encode the sorted revocation pair and the epoch as 20 little-endian bytes.
///
/// Supply `id_lo` and `id_hi` in sorted order.
pub fn ts13_revocation_message(id_lo: u64, id_hi: u64, epoch: u32) -> [u8; 20] {
    let mut message = [0u8; 20];
    message[..8].copy_from_slice(&id_lo.to_le_bytes());
    message[8..16].copy_from_slice(&id_hi.to_le_bytes());
    message[16..].copy_from_slice(&epoch.to_le_bytes());
    message
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn revocation_id_uses_the_first_eight_sha256_bytes_in_little_endian_order() {
        assert_eq!(ts13_mso_derived_revocation_id(&[]), 0x141c_fc98_42c4_b0e3);
    }

    #[test]
    fn revocation_message_is_the_canonical_sorted_pair_encoding() {
        assert_eq!(
            ts13_revocation_message(0x0102_0304_0506_0708, 0x1112_1314_1516_1718, 0x2122_2324,),
            [
                0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01, 0x18, 0x17, 0x16, 0x15, 0x14, 0x13,
                0x12, 0x11, 0x24, 0x23, 0x22, 0x21,
            ]
        );
    }
}
