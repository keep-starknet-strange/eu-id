use stwo::core::fields::m31::BaseField;

use crate::ecdsa::EcdsaVerifyWitness;
use crate::ops::consts::N_LIMBS;

/// Number of columns for a single modular multiplication witness in the trace.
/// Layout: a (N_LIMBS) + b (N_LIMBS) + result (N_LIMBS) + quotient (N_LIMBS) + carries (2*N_LIMBS)
pub const MUL_MOD_COLS: usize = 6 * N_LIMBS;

/// Number of columns for a single modular add/sub witness.
/// Layout: a (N_LIMBS) + b (N_LIMBS) + result (N_LIMBS) + flag (1) + carries (N_LIMBS + 1)
pub const ADD_SUB_MOD_COLS: usize = 3 * N_LIMBS + 1 + N_LIMBS + 1;

/// Placeholder: will generate a full Stwo execution trace from an ECDSA verification witness.
///
/// The trace encodes every intermediate value of the computation as M31 columns
/// so that the AIR constraints can enforce correctness.
///
/// This is the next major implementation target.
pub fn generate_ecdsa_trace(
    _witness: &EcdsaVerifyWitness,
    _log_n_rows: u32,
) -> Vec<Vec<BaseField>> {
    todo!("Trace generation from ECDSA witness - next implementation step")
}

#[cfg(test)]
mod tests {
    use crate::ops::mul_mod_witness;
    use crate::ops::consts::N_LIMBS;
    use crypto_bigint::{NonZero, U256};

    /// Prints a CSV of two trace rows so the column layout is visible.
    ///
    /// Column layout (120 columns total):
    ///   a[0..20]        — left operand limbs (least significant first)
    ///   b[0..20]        — right operand limbs
    ///   result[0..20]   — result = a*b mod p
    ///   quotient[0..20] — quotient q, where a*b = q*p + result
    ///   carry[0..40]    — carries propagated limb by limb
    #[test]
    fn print_mul_mod_trace_csv() {
        let b = U256::from_u64(11);
        let p = NonZero::new(U256::from_u64(100)).unwrap();

        // Row 0: 7 * 11 mod 100 = 77, quotient = 0  (no reduction needed)
        let w0 = mul_mod_witness(&U256::from_u64(7), &b, &p);
        // Row 1: 13 * 11 mod 100 = 43, quotient = 1 (143 - 1*100 = 43)
        let w1 = mul_mod_witness(&U256::from_u64(13), &b, &p);

        let mut headers: Vec<String> = Vec::new();
        for i in 0..N_LIMBS     { headers.push(format!("a[{i}]")); }
        for i in 0..N_LIMBS     { headers.push(format!("b[{i}]")); }
        for i in 0..N_LIMBS     { headers.push(format!("result[{i}]")); }
        for i in 0..N_LIMBS     { headers.push(format!("quotient[{i}]")); }
        for i in 0..2 * N_LIMBS { headers.push(format!("carry[{i}]")); }

        println!("\n=== MulMod Trace (a*b mod p, limb layout) ===");
        println!("{}", headers.join(","));

        for w in [&w0, &w1] {
            let mut row: Vec<String> = Vec::new();
            for i in 0..N_LIMBS     { row.push(w.a.0[i].0.to_string()); }
            for i in 0..N_LIMBS     { row.push(w.b.0[i].0.to_string()); }
            for i in 0..N_LIMBS     { row.push(w.result.0[i].0.to_string()); }
            for i in 0..N_LIMBS     { row.push(w.quotient.0[i].0.to_string()); }
            for i in 0..2 * N_LIMBS { row.push(w.carries[i].to_string()); }
            println!("{}", row.join(","));
        }
        println!("=== end ===\n");
    }
}
