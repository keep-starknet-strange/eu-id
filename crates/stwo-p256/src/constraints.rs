use stwo_constraint_framework::{EvalAtRow, FrameworkEval};

/// AIR evaluator for the modular multiplication constraint.
///
/// Enforces: a * b = q * modulus + result (limb-by-limb with carries)
///
/// This is the fundamental building block. Point operations and ECDSA
/// verification are composed from multiple mul_mod and add_mod constraints.
///
/// Will be implemented once trace layout is finalized.
#[derive(Clone)]
pub struct MulModEval {
    pub log_n_rows: u32,
}

impl FrameworkEval for MulModEval {
    fn log_size(&self) -> u32 {
        self.log_n_rows
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_n_rows + 1
    }

    fn evaluate<E: EvalAtRow>(&self, eval: E) -> E {
        // TODO: Read N_LIMBS columns for a, b, result, quotient, and carries.
        // Constrain:
        //   For each output limb position i (0..2*N_LIMBS):
        //     sum(a[j]*b[i-j] for valid j) = sum(q[j]*p[i-j] for valid j) + r[i] + carry[i]*2^LIMB_BITS - carry[i-1]
        //
        // Where carry[-1] = 0 and r[i] = 0 for i >= N_LIMBS.
        //
        // Additionally constrain that each carry fits in the expected range.
        eval
    }
}

/// Placeholder for the full ECDSA verification AIR.
/// Composes mul_mod, add_mod, sub_mod constraints for each step
/// of the ECDSA algorithm.
#[derive(Clone)]
pub struct EcdsaVerifyEval {
    pub log_n_rows: u32,
}

impl FrameworkEval for EcdsaVerifyEval {
    fn log_size(&self) -> u32 {
        self.log_n_rows
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_n_rows + 1
    }

    fn evaluate<E: EvalAtRow>(&self, eval: E) -> E {
        // TODO: Full ECDSA constraint composition.
        eval
    }
}
