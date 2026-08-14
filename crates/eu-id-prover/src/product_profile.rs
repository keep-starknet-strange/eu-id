//! Source-bound identifiers for the classical P-256 identity profile.

use predicates::{Date, NatPublicInput, PublicInput as AgePublicInput};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use stwo_sha256::constants::BLOCK_BYTES;
use stwo_sha256::native::n_blocks_for;

use crate::mdoc_cbor_stream::MDOC_CBOR_BLIND_ROWS;

/// Returns whether `code` is an assigned ISO 3166-1 alpha-2 code.
pub fn is_assigned_iso_alpha2(code: [u8; 2]) -> bool {
    predicates::is_assigned_iso_alpha2(predicates::pack_alpha2(code))
}

/// The relying party's public policy — exactly the statement the combined
/// verifier will check against. The date of birth, the nationality, and the
/// digest are *proven*, never supplied.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Policy {
    /// Reference "today" the age check is evaluated against.
    pub current_date: Date,
    /// Minimum age in years (the PRD headline is 18).
    pub min_age_years: u32,
    /// Canonical accepted ISO 3166-1 alpha-2 codes.
    ///
    /// Each entry is two uppercase ASCII bytes. The caller binds this exact
    /// sorted set into the verifier request.
    pub accepted_nationalities: Vec<[u8; 2]>,
}

impl Policy {
    /// The age predicate's public input for this policy.
    pub fn age_public_input(&self) -> AgePublicInput {
        AgePublicInput::new(self.current_date, self.min_age_years)
    }

    /// The nationality predicate's public input over ISO 3166-1 alpha-2 codes.
    pub fn nat_public_input(&self) -> NatPublicInput {
        NatPublicInput::new(
            self.accepted_nationalities
                .iter()
                .map(|&code| predicates::pack_alpha2(code))
                .collect(),
        )
    }

    /// The cutoff date a date of birth must be on-or-before to satisfy the age
    /// check (`current` shifted back `min_age_years`).
    pub fn age_cutoff(&self) -> Date {
        self.age_public_input().cutoff_date()
    }
}

// Canonical identifiers shared by the SDK request and the mdoc circuit.
pub const PRODUCT_SPEC_ID: &str = "stwo-euid-pid-v1";
pub const PRODUCT_STATEMENT_VERSION: u32 = 2;
pub const PRODUCT_PROFILE_ID: &str = "eudi-pid-p256-identity";
pub const PRODUCT_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
pub const PRODUCT_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
pub const PRODUCT_BIRTH_DATE_ELEMENT: &str = "birth_date";
pub const PRODUCT_NATIONALITY_ELEMENT: &str = "nationality";
pub const PRODUCT_MAX_ATTRIBUTES: usize = 2;
// The MSO payload cap is sized for the real PID credential (~1-2 KiB of
// value-digests plus device key and validity) with ~2x headroom, not a
// theoretical maximum. Together with the packed digest-id universe this keeps
// the scope walk at log14, which halves the STARK composition/FRI domain.
pub const PRODUCT_MAX_MSO_PAYLOAD_BYTES: usize = 3584;
pub const PRODUCT_ISSUER_SIG_STRUCTURE_MAX_OVERHEAD_BYTES: usize = 20;
pub const PRODUCT_MAX_ISSUER_SIG_STRUCTURE_BYTES: usize =
    PRODUCT_MAX_MSO_PAYLOAD_BYTES + PRODUCT_ISSUER_SIG_STRUCTURE_MAX_OVERHEAD_BYTES;
pub const PRODUCT_MAX_SELECTED_ITEM_BYTES: usize = 1_024;
pub const PRODUCT_SHA_LOG_N_ROWS: u32 = 14;
// Issuer Sig_structure, MSO, and revocation message precede selected items.
pub const PRODUCT_FIXED_PACKED_SHA_MESSAGES: usize = 3;
pub const PRODUCT_MAX_PACKED_SHA_MESSAGES: usize =
    PRODUCT_FIXED_PACKED_SHA_MESSAGES + PRODUCT_MAX_ATTRIBUTES;
pub const PRODUCT_TS13_REVOCATION_MESSAGE_BYTES: usize =
    2 * core::mem::size_of::<u64>() + core::mem::size_of::<u32>();
pub const PRODUCT_MAX_CBOR_LOG_SIZE: u32 = 12;
pub const PRODUCT_ITEM_CBOR_LOG_SIZE: u32 = 11;
pub const PRODUCT_MAX_SCOPE_LOG_SIZE: u32 = 14;
pub const PRODUCT_MAX_SCOPE_ACTIVE_ROWS: usize = 2 * PRODUCT_MAX_ISSUER_SIG_STRUCTURE_BYTES
    + PRODUCT_MAX_MSO_PAYLOAD_BYTES
    + 2 * PRODUCT_MAX_ATTRIBUTES * PRODUCT_MAX_SELECTED_ITEM_BYTES;

const _: () =
    assert!(stwo_sha256::native::n_blocks_for(PRODUCT_MAX_ISSUER_SIG_STRUCTURE_BYTES) == 57);
const _: () = assert!(stwo_sha256::native::n_blocks_for(PRODUCT_MAX_MSO_PAYLOAD_BYTES) == 57);
const _: () =
    assert!(stwo_sha256::native::n_blocks_for(PRODUCT_TS13_REVOCATION_MESSAGE_BYTES) == 1);
const _: () = assert!(stwo_sha256::native::n_blocks_for(PRODUCT_MAX_SELECTED_ITEM_BYTES) == 17);
const PRODUCT_MAX_PACKED_SHA_BLOCKS: usize = n_blocks_for(PRODUCT_MAX_ISSUER_SIG_STRUCTURE_BYTES)
    + n_blocks_for(PRODUCT_MAX_MSO_PAYLOAD_BYTES)
    + n_blocks_for(PRODUCT_TS13_REVOCATION_MESSAGE_BYTES)
    + PRODUCT_MAX_ATTRIBUTES * n_blocks_for(PRODUCT_MAX_SELECTED_ITEM_BYTES);
const _: () = assert!(PRODUCT_MAX_PACKED_SHA_BLOCKS == 149);
const _: () = assert!(PRODUCT_MAX_PACKED_SHA_BLOCKS <= 255);
const _: () = assert!(PRODUCT_MAX_PACKED_SHA_MESSAGES == 5);
const _: () = assert!(PRODUCT_SHA_LOG_N_ROWS == 14);
const _: () = assert!(
    n_blocks_for(PRODUCT_MAX_ISSUER_SIG_STRUCTURE_BYTES) * BLOCK_BYTES + MDOC_CBOR_BLIND_ROWS
        <= 1usize << PRODUCT_MAX_CBOR_LOG_SIZE
);
const _: () = assert!(
    n_blocks_for(PRODUCT_MAX_SELECTED_ITEM_BYTES) * BLOCK_BYTES + MDOC_CBOR_BLIND_ROWS
        <= 1usize << PRODUCT_ITEM_CBOR_LOG_SIZE
);
const _: () = assert!(
    PRODUCT_MAX_SCOPE_ACTIVE_ROWS + crate::mdoc_scope::MDOC_SCOPE_BLIND_ROWS
        <= 1usize << PRODUCT_MAX_SCOPE_LOG_SIZE
);

const PROFILE_MANIFEST: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../artifacts/product-p256-identity/profile-manifest.json"
));
const ROOT_POLICY_MANIFEST: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../artifacts/product-p256-identity/root-policy-manifest.json"
));

pub fn product_circuit_hash() -> String {
    hex_digest(PROFILE_MANIFEST)
}

pub fn product_root_policy_hash() -> [u8; 32] {
    Sha256::digest(ROOT_POLICY_MANIFEST).into()
}

pub fn product_profile_pin_is_supported(
    profile_id: &str,
    circuit_hash: &str,
    root_policy_hash: &[u8],
) -> bool {
    profile_id == PRODUCT_PROFILE_ID
        && circuit_hash == product_circuit_hash()
        && root_policy_hash == product_root_policy_hash()
}

fn hex_digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use stwo_sha256::trace::ROWS_PER_BLOCK;

    #[test]
    fn product_profile_pin_is_exact() {
        let circuit_hash = product_circuit_hash();
        let root_policy_hash = product_root_policy_hash();
        assert!(product_profile_pin_is_supported(
            PRODUCT_PROFILE_ID,
            &circuit_hash,
            &root_policy_hash,
        ));

        let mut wrong_root = root_policy_hash;
        wrong_root[0] ^= 1;
        assert!(!product_profile_pin_is_supported(
            PRODUCT_PROFILE_ID,
            &circuit_hash,
            &wrong_root,
        ));
        assert!(!product_profile_pin_is_supported(
            PRODUCT_PROFILE_ID,
            &"00".repeat(32),
            &root_policy_hash,
        ));
    }

    #[test]
    fn manifest_parameters_match_live_product_configuration() {
        let manifest: serde_json::Value =
            serde_json::from_slice(PROFILE_MANIFEST).expect("profile manifest is JSON");
        let config = crate::mdoc::mdoc_production_pcs_config();
        assert_eq!(manifest["pcs"]["pow_bits"], config.pow_bits);
        assert_eq!(
            manifest["pcs"]["log_blowup_factor"],
            config.fri_config.log_blowup_factor
        );
        assert_eq!(
            manifest["pcs"]["queries"],
            u64::try_from(config.fri_config.n_queries).unwrap()
        );
        assert_eq!(manifest["pcs"]["fold_step"], config.fri_config.fold_step);
        assert_eq!(
            manifest["product_bounds"]["max_attributes"],
            PRODUCT_MAX_ATTRIBUTES
        );
        assert_eq!(
            manifest["product_bounds"]["max_mso_payload_bytes"],
            PRODUCT_MAX_MSO_PAYLOAD_BYTES
        );
        assert_eq!(
            manifest["product_bounds"]["max_issuer_sig_structure_bytes"],
            PRODUCT_MAX_ISSUER_SIG_STRUCTURE_BYTES
        );
        assert_eq!(
            manifest["product_bounds"]["max_selected_item_bytes"],
            PRODUCT_MAX_SELECTED_ITEM_BYTES
        );
        assert_eq!(
            manifest["product_bounds"]["sha_log_n_rows"],
            PRODUCT_SHA_LOG_N_ROWS
        );
        assert_eq!(
            manifest["product_bounds"]["max_packed_sha_messages"],
            PRODUCT_MAX_PACKED_SHA_MESSAGES
        );
        assert_eq!(
            manifest["product_bounds"]["packed_sha_message_order"],
            serde_json::json!([
                "issuer_sig_structure",
                "mso",
                "revocation",
                "selected_item_0",
                "selected_item_1_if_and",
            ])
        );
        assert_eq!(
            manifest["product_bounds"]["max_cbor_log_size"],
            PRODUCT_MAX_CBOR_LOG_SIZE
        );
        assert_eq!(
            manifest["product_bounds"]["item_cbor_log_size"],
            PRODUCT_ITEM_CBOR_LOG_SIZE
        );
        assert_eq!(
            manifest["product_bounds"]["max_scope_log_size"],
            PRODUCT_MAX_SCOPE_LOG_SIZE
        );
        assert_eq!(
            manifest["product_bounds"]["item_digest_log_size"],
            crate::mdoc_scope::ITEM_DIGEST_LOG_SIZE
        );
    }

    #[test]
    fn packed_sha_product_capacity_is_exact() {
        assert_eq!(n_blocks_for(PRODUCT_MAX_ISSUER_SIG_STRUCTURE_BYTES), 57);
        assert_eq!(n_blocks_for(PRODUCT_MAX_MSO_PAYLOAD_BYTES), 57);
        assert_eq!(n_blocks_for(PRODUCT_TS13_REVOCATION_MESSAGE_BYTES), 1);
        assert_eq!(n_blocks_for(PRODUCT_MAX_SELECTED_ITEM_BYTES), 17);
        assert_eq!(PRODUCT_MAX_PACKED_SHA_BLOCKS, 149);
        let max_real_blocks = ((1usize << PRODUCT_SHA_LOG_N_ROWS) - 1) / ROWS_PER_BLOCK;
        assert_eq!(max_real_blocks, 244);
        assert_eq!(max_real_blocks - PRODUCT_MAX_PACKED_SHA_BLOCKS, 95);
        assert!(max_real_blocks - PRODUCT_MAX_PACKED_SHA_BLOCKS >= 1);
    }
}
