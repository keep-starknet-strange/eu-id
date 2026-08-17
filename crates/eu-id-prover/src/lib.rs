//! Quantum-safe prover for the TS13 identity profile.
//!
//! ## Scope
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
mod randomness;
pub mod ts13;
#[doc(hidden)]
pub mod ts13_artifact;
pub mod ts13_demo;
#[doc(hidden)]
pub mod ts13_demo_artifact_constants {
    include!("generated/ts13_demo_artifact.rs");
}

use air_core::{process_memory_kib, ProcessMemoryKib};
use stwo::core::pcs::PcsConfig;

fn optional_number(value: Option<u64>) -> String {
    value.map_or_else(|| "null".to_string(), |value| value.to_string())
}

fn timing_json(
    scope: &str,
    phase: &str,
    elapsed_us: u128,
    rayon_threads: usize,
    memory: ProcessMemoryKib,
) -> String {
    let vm_rss_kib = optional_number(memory.vm_rss);
    let vm_hwm_kib = optional_number(memory.vm_hwm);
    format!(
        r#"EUID_PROVE_TIMING {{"scope":"{scope}","phase":"{phase}","elapsed_us":{elapsed_us},"rayon_threads":{rayon_threads},"vm_rss_kib":{vm_rss_kib},"vm_hwm_kib":{vm_hwm_kib}}}"#
    )
}

fn runtime_configuration_json(
    proof_thread_stack_bytes: usize,
    proof_worker_stack_bytes: usize,
    rayon_threads: usize,
    memory: ProcessMemoryKib,
) -> String {
    let vm_rss_kib = optional_number(memory.vm_rss);
    let vm_hwm_kib = optional_number(memory.vm_hwm);
    format!(
        r#"EUID_PROVE_TIMING {{"scope":"sdk","phase":"runtime_configuration","elapsed_us":0,"rayon_threads":{rayon_threads},"proof_thread_stack_bytes":{proof_thread_stack_bytes},"proof_worker_stack_bytes":{proof_worker_stack_bytes},"vm_rss_kib":{vm_rss_kib},"vm_hwm_kib":{vm_hwm_kib}}}"#
    )
}

fn emit_timing_line(line: &str) {
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

/// Emit one opt-in machine-readable proving-time record.
///
/// This is public only so the SDK can use the same diagnostic sink. It is not
/// part of the UniFFI API.
#[doc(hidden)]
pub fn report_prove_timing(scope: &str, phase: &str, elapsed: std::time::Duration) {
    if std::env::var_os("EUID_PROVE_TIMING").is_none() {
        return;
    }
    emit_timing_line(&timing_json(
        scope,
        phase,
        elapsed.as_micros(),
        rayon::current_num_threads(),
        process_memory_kib(),
    ));
}

/// Emit the opt-in SDK proof runtime configuration.
///
/// This function is public only for the SDK. It is not part of the UniFFI API.
#[doc(hidden)]
pub fn report_prove_runtime_configuration(
    proof_thread_stack_bytes: usize,
    proof_worker_stack_bytes: usize,
) {
    if std::env::var_os("EUID_PROVE_TIMING").is_none() {
        return;
    }
    emit_timing_line(&runtime_configuration_json(
        proof_thread_stack_bytes,
        proof_worker_stack_bytes,
        rayon::current_num_threads(),
        process_memory_kib(),
    ));
}

pub use mdoc::{MdocPidRequest, MdocProof, MdocTs13DemoCircuitPublicInput};
pub use policy::iso_alpha2_to_numeric;

fn extract_ts13_demo(
    document: &[u8],
    request: &MdocPidRequest,
) -> Result<(mdoc::ExtractedPidMdoc, u64), Error> {
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
    Ok((extracted, id))
}

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
    let (extracted, id) = extract_ts13_demo(document, request)?;
    mdoc::prove_mdoc_ts13_demo_circuit(
        &extracted,
        public,
        mdoc::MdocRevocationRangeWitness { id, id_lo, id_hi },
        signature,
    )
}

pub(crate) fn prove_mdoc_ts13_demo_for_artifact(
    document: &[u8],
    request: &MdocPidRequest,
    public: &MdocTs13DemoCircuitPublicInput,
    id_lo: u64,
    id_hi: u64,
    signature: mdoc::MdocRevocationSignature,
) -> Result<(MdocProof, mdoc::MdocTs13DemoCircuitGeometry), Error> {
    let (extracted, id) = extract_ts13_demo(document, request)?;
    mdoc::prove_mdoc_ts13_demo_circuit_for_artifact(
        &extracted,
        public,
        mdoc::MdocRevocationRangeWitness { id, id_lo, id_hi },
        signature,
    )
}

#[cfg(test)]
mod timing_tests {
    use super::{runtime_configuration_json, timing_json, ProcessMemoryKib};

    #[test]
    fn timing_output_is_machine_readable() {
        let memory = ProcessMemoryKib {
            vm_rss: Some(1024),
            vm_hwm: Some(2048),
        };
        assert_eq!(
            timing_json("eu_id_prover", "witness_generation", 17, 6, memory),
            r#"EUID_PROVE_TIMING {"scope":"eu_id_prover","phase":"witness_generation","elapsed_us":17,"rayon_threads":6,"vm_rss_kib":1024,"vm_hwm_kib":2048}"#
        );
        assert_eq!(
            runtime_configuration_json(64, 32, 6, ProcessMemoryKib::default()),
            r#"EUID_PROVE_TIMING {"scope":"sdk","phase":"runtime_configuration","elapsed_us":0,"rayon_threads":6,"proof_thread_stack_bytes":64,"proof_worker_stack_bytes":32,"vm_rss_kib":null,"vm_hwm_kib":null}"#
        );
    }
}

/// Verify one TS13 demo identity proof against its public input.
pub fn verify_mdoc_ts13_demo(
    proof: &MdocProof,
    public: &MdocTs13DemoCircuitPublicInput,
) -> Result<(), Error> {
    mdoc::verify_mdoc_ts13_demo_circuit(proof, public)
}

/// Errors from preparing, proving, or verifying an identity proof.
#[derive(Debug)]
pub enum Error {
    /// The mdoc parse or extraction failed.
    Mdoc(mdoc::MdocError),
    /// The prover rejected the witness or the configuration.
    Prove(String),
    /// The verifier rejected the proof.
    Verify(String),
    /// The credential shape does not match the fixed TS13 demo circuit.
    UnsupportedDemoCredentialShape,
    /// The proof carries a PCS configuration weaker than the fixed parameters.
    WeakConfig {
        /// The PCS configuration that the proof carries.
        got: PcsConfig,
        /// The PCS configuration that the verifier requires.
        expected: PcsConfig,
    },
    /// The recomputed preprocessed commitment root differs from the cached root.
    PreprocessedRootMismatch {
        /// The root that the verifier recomputed.
        got: air_core::CommitmentRoot,
        /// The root that the verifier expected.
        expected: air_core::CommitmentRoot,
    },
}
