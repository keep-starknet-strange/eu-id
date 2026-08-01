//! SHA-256 AIR over the M31 field for the eu-id credential pipeline.
//!
//! The identity proof hashes each `IssuerSignedItem` and the complete
//! `MobileSecurityObject`. Each hash can span multiple blocks. LogUp relations
//! bind the digest and selected preimage bytes to the other proof components.

pub mod air;
pub mod components;
pub mod constants;
pub mod constraints;
pub mod digest_bridge;
pub mod field_exposure;
pub mod headroom;
pub mod interaction;
pub mod multiplicities;
pub mod native;
pub mod preprocessed;
pub mod relations;
pub mod shared_tables;
pub mod stark;
pub mod tables_local;
pub mod trace;
pub mod types;
pub mod witness;
