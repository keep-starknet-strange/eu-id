//! Quantum-safe prover for the TS13 identity profile.
//!
//! One STARK proves the issuer, device, attribute, validity, and revocation
//! constraints.

pub(crate) mod claimed_sum_blinder;
pub mod mdoc;
mod mdoc_cbor_stream;
mod mdoc_private_device_key_bind;
mod mdoc_private_item_bind;
mod mdoc_private_message;
mod mdoc_private_mso_bind;
mod mdoc_private_mso_validity;
#[cfg(test)]
mod mdoc_real_vectors;
#[cfg(test)]
extern crate self as eu_id_prover;
mod mdoc_value_digests_scan;
#[cfg(test)]
#[allow(dead_code)]
#[path = "../tests/support/mldsa_fixture.rs"]
mod mldsa_test_fixture;
mod policy;
pub mod ts13;
#[doc(hidden)]
pub mod ts13_artifact;
pub mod ts13_demo;
#[doc(hidden)]
pub mod ts13_demo_artifact_constants {
    include!("generated/ts13_demo_artifact.rs");
}

use stwo::core::pcs::PcsConfig;

fn timing_json(enabled: bool, scope: &str, phase: &str, elapsed_us: u128) -> Option<String> {
    enabled.then(|| {
        format!(
            r#"EUID_PROVE_TIMING {{"scope":"{scope}","phase":"{phase}","elapsed_us":{elapsed_us}}}"#
        )
    })
}

/// Emit one opt-in machine-readable proving-time record.
///
/// This is public only so the SDK can use the same diagnostic sink. It is not
/// part of the UniFFI API.
#[doc(hidden)]
pub fn report_prove_timing(scope: &str, phase: &str, elapsed: std::time::Duration) {
    if let Some(line) = timing_json(
        std::env::var_os("EUID_PROVE_TIMING").is_some(),
        scope,
        phase,
        elapsed.as_micros(),
    ) {
        eprintln!("{line}");
        let Some(path) = std::env::var_os("EUID_PROVE_TIMING_FILE") else {
            return;
        };
        let result = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .and_then(|mut file| {
                use std::io::Write as _;
                writeln!(file, "{line}")
            });
        if let Err(error) = result {
            eprintln!("EUID_PROVE_TIMING_WRITE_ERROR {error}");
        }
    }
}

pub use mdoc::{MdocPidRequest, MdocProof, MdocTs13DemoCircuitPublicInput};
/// Prove the fixed public-input-unlinkable TS13 age-over-18 theorem.
///
/// The returned proof contains no serialized semantic statement. The SDK
/// places it in the fixed-capacity identity envelope.
pub fn prove_mdoc_ts13_demo(
    document: &[u8],
    request: &MdocPidRequest,
    public: &MdocTs13DemoCircuitPublicInput,
    id_lo: u64,
    id_hi: u64,
    signature: mdoc::MdocRevocationSignature,
) -> Result<MdocProof, Error> {
    let extract_start = std::time::Instant::now();
    if document.len() > ts13::TS13_MAX_DOCUMENT_BYTES {
        return Err(Error::UnsupportedDemoCredentialShape);
    }
    let extracted = mdoc::extract_pid_mdoc(document, request).map_err(Error::Mdoc)?;
    let id = ts13::ts13_mso_derived_revocation_id(&extracted.mso);
    report_prove_timing(
        "eu_id_prover",
        "credential_extract",
        extract_start.elapsed(),
    );
    mdoc::prove_mdoc_ts13_demo_circuit(
        &extracted,
        public,
        mdoc::MdocRevocationRangeWitness { id, id_lo, id_hi },
        signature,
    )
}

#[cfg(test)]
mod timing_tests {
    use super::timing_json;

    #[test]
    fn timing_output_is_opt_in_and_machine_readable() {
        assert_eq!(timing_json(false, "scope", "phase", 17), None);
        assert_eq!(
            timing_json(true, "eu_id_prover", "witness_generation", 17),
            Some(
                r#"EUID_PROVE_TIMING {"scope":"eu_id_prover","phase":"witness_generation","elapsed_us":17}"#
                    .to_string()
            )
        );
    }
}

pub fn verify_mdoc_ts13_demo(
    proof: &MdocProof,
    public: &MdocTs13DemoCircuitPublicInput,
) -> Result<(), Error> {
    mdoc::verify_mdoc_ts13_demo_circuit(proof, public)
}

/// Errors from preparing, proving, or verifying an identity proof.
#[derive(Debug)]
pub enum Error {
    Mdoc(mdoc::MdocError),
    Prove(String),
    Verify(String),
    UnsupportedDemoCredentialShape,
    WeakConfig {
        got: PcsConfig,
        expected: PcsConfig,
    },
    PreprocessedRootMismatch {
        got: air_core::CommitmentRoot,
        expected: air_core::CommitmentRoot,
    },
}
