use crate::types::EcdsaVerifyInput;

/// Configuration for proof generation.
pub struct ProverConfig {
    pub log_n_rows: u32,
}

impl Default for ProverConfig {
    fn default() -> Self {
        Self { log_n_rows: 5 }
    }
}

/// A STARK proof that an ECDSA P-256 signature is valid.
/// Wraps the Stwo proof with the public inputs.
pub struct EcdsaProof {
    pub public_key_x: [u8; 32],
    pub public_key_y: [u8; 32],
    pub message_hash: [u8; 32],
    // proof: StarkProof<Blake2sHash>, // TODO: add once trace/constraints are wired
}

/// Generate a STARK proof that the given ECDSA signature is valid.
///
/// This is the main entry point. Will be implemented once trace generation
/// and constraints are complete.
pub fn prove_ecdsa_verification(
    _input: &EcdsaVerifyInput,
    _config: &ProverConfig,
) -> Result<EcdsaProof, String> {
    todo!("STARK proof generation - requires trace + constraints implementation")
}

/// Verify a STARK proof of ECDSA signature validity.
pub fn verify_ecdsa_proof(_proof: &EcdsaProof) -> Result<bool, String> {
    todo!("STARK proof verification - requires trace + constraints implementation")
}
