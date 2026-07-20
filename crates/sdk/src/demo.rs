//! Compile-parity stubs for the P-256 build.
//!
//! These four `demo_*` functions are the ONLY surface that diverges between the
//! ML-DSA and P-256 SDK branches (on ML-DSA they perform the demo in-memory
//! re-sign; there is no P-256 equivalent). Exposing them here — with identical
//! UniFFI signatures — lets the wallet and verifier compile from a SINGLE source
//! set against either SDK, dispatching at runtime on `zk_system()`.
//!
//! Every caller guards these behind `zk_system() == MlDsa`, so on a P-256 build
//! they are never reached; they fail loudly if that guarantee is ever broken.
//! Keep the signatures (names, params, returns) byte-identical to the ML-DSA
//! branch's `demo.rs`, or the generated Kotlin bindings drift.

use crate::ZkError;

const UNAVAILABLE: &str = "demo ML-DSA issuance is unavailable in the P-256 build";

/// ML-DSA demo issuer key — unavailable on P-256; guarded by `zk_system() == MlDsa`.
#[uniffi::export]
pub fn demo_issuer_public_key() -> Vec<u8> {
    unreachable!("{UNAVAILABLE}")
}

#[allow(unused_variables)]
#[uniffi::export]
pub fn demo_mint_ml_dsa_signed_pid_mdoc(
    p256_issuer_signed: Vec<u8>,
    device_public_key: Vec<u8>,
) -> Result<Vec<u8>, ZkError> {
    Err(ZkError::InvalidInput(UNAVAILABLE.to_string()))
}

#[allow(unused_variables)]
#[uniffi::export]
pub fn demo_device_auth_sig_structure(
    session_transcript: Vec<u8>,
    doctype: String,
) -> Result<Vec<u8>, ZkError> {
    Err(ZkError::InvalidInput(UNAVAILABLE.to_string()))
}

#[allow(unused_variables)]
#[uniffi::export]
pub fn demo_build_ml_dsa_witness(
    ml_dsa_issuer_signed: Vec<u8>,
    session_transcript: Vec<u8>,
    doctype: String,
    device_signature: Vec<u8>,
) -> Result<Vec<u8>, ZkError> {
    Err(ZkError::InvalidInput(UNAVAILABLE.to_string()))
}
