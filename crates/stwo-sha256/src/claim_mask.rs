//! SHA-specific validation for the shared claimed-sum masking protocol.

use std::fmt;

use air_core::claim_mask::ClaimMaskTrace;

/// Invalid ordered mask-trace configuration supplied to a SHA prover module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShaClaimMaskConfigError {
    /// The module received a different number of masks than claim-bearing
    /// components.
    Count { expected: usize, actual: usize },
    /// A mask trace was supplied out of component order.
    LogSize {
        index: usize,
        expected: u32,
        actual: u32,
    },
}

impl fmt::Display for ShaClaimMaskConfigError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Count { expected, actual } => write!(
                formatter,
                "SHA claim masking expected {expected} traces, got {actual}"
            ),
            Self::LogSize {
                index,
                expected,
                actual,
            } => write!(
                formatter,
                "SHA claim mask {index} expected log size {expected}, got {actual}"
            ),
        }
    }
}

impl std::error::Error for ShaClaimMaskConfigError {}

pub(crate) fn validate_claim_masks(
    expected_log_sizes: &[u32],
    traces: &[ClaimMaskTrace],
) -> Result<(), ShaClaimMaskConfigError> {
    if traces.len() != expected_log_sizes.len() {
        return Err(ShaClaimMaskConfigError::Count {
            expected: expected_log_sizes.len(),
            actual: traces.len(),
        });
    }
    for (index, (&expected, trace)) in expected_log_sizes.iter().zip(traces).enumerate() {
        let actual = trace.log_size();
        if actual != expected {
            return Err(ShaClaimMaskConfigError::LogSize {
                index,
                expected,
                actual,
            });
        }
    }
    Ok(())
}
