//! Hinted mod-`p` multiplication with carry polynomials.
//!
//! The component uses one row for each multiplication.
//! Three polynomial carry identities prove correctness.
//! The verifier checks them at one channel challenge `z ∈ QM31`.
//! The channel draws `z` after the base-trace commitment.
//!
//! # Property
//!
//! For 20×13-bit-limb values `a, b` (each `< 2^260` by Range13) the component
//! proves there exists `r < 2^260` with
//!
//! ```text
//! a · b ≡ r (mod p)        (p = the P-256 field prime)
//! ```
//!
//! `r` keeps the existing silo invariant: it is *a* 256-bit representative of
//! the residue class (the honest witness writes the canonical one). Boundaries
//! that publish or compare values pin canonicality separately (final_check's
//! `r_x < p`, the public-key gate).
//!
//! # Why three identities (the integer-lifting bounds worksheet)
//!
//! Encode values as polynomials in the limb base `β = 2^13`:
//! `A(X) = Σ a_i X^i` with `A(β) = a`. A Schwartz–Zippel check at `z` proves a
//! POLYNOMIAL identity over QM31, i.e. coefficient-wise equality **mod
//! p_M31 = 2^31 − 1**. The identity only lifts to the integers (and hence to
//! `a·b ≡ r mod p`) if no coefficient relation can wrap mod `p_M31` within the
//! committed range bounds.
//!
//! The single identity `A·B − Q·P − R = (X−β)·H` does not lift safely.
//! A 20-by-20 limb convolution has up to 20 terms in each coefficient.
//! Its coefficient and carry bounds permit a wrap by `±p_M31`.
//! Such a wrap could prove an incorrect result.
//! Thus, the component uses three identities.
//!
//! Splitting `b = b_lo + β^10·b_hi` (limbs 0..10 / 10..20 — note
//! `2^130 = β^10`, so the recombination is a pure `X^10` shift, no constant
//! multiplication) caps every convolution at 11 terms:
//!
//! ```text
//! (1)  A·B_lo − Q1·P − M1 = (X−β)·H1        a·b_lo = q1·p + m1
//! (2)  A·B_hi − Q2·P − M2 = (X−β)·H2        a·b_hi = q2·p + m2
//! (3)  M1 + X^10·M2 − Q3·P − R = (X−β)·H3   m1 + β^10·m2 = q3·p + r
//! ⟹    a·b = (q1 + β^10·q2 + q3)·p + r  ⟹  a·b ≡ r (mod p)
//! ```
//!
//! Worksheet (all identities share these bounds, see the constants in
//! [`witness`]):
//!
//! ```text
//! β = 2^13 = 8192,  β−1 = 8191,  p_M31 = 2^31 − 1 = 2,147,483,647
//! A: 20 limbs.  B_lo, B_hi: 10 limbs.  Q1,Q2,Q3: 11 limbs
//!   (a < 2^260, b_half < 2^130 ⟹ a·b_half < 2^390 ⟹ q < 2^134 ≤ 11 limbs;
//!    m1 + β^10·m2 < 2^391 ⟹ q3 < 2^135 ≤ 11 limbs).
//! M1, M2, R: 20 limbs.
//! Convolution terms per coefficient: A·B_half ≤ 10, Q·P ≤ 11.
//! MAX_C   = 11·(β−1)² + (β−1) = (β−1)·(11·(β−1)+1) = 738,025,482
//! H bound = MAX_C/(β−1)  (honest, exact)    ≤        90,102
//! H coefficients: deg(Q·P) = 10+19 = 29 ⟹ C has 30 coefficients, H has 29.
//! H range check: h = h_lo + β·h_hi, h_lo ∈ [0, β) (Range13),
//!                h_hi ∈ [−12, 12] (small signed table)
//!   ⟹ adversarial |h| ≤ 12·β + (β−1)        =       106,495
//! Wrap slack per coefficient relation:
//!   MAX_C + |h| + β·|h| ≤ 738,025,482 + 106,495·8193 = 1,610,539,017
//!                                              < p_M31 ✓ (25% margin)
//! ```
//!
//! Each coefficient relation stays below the M31 modulus.
//! Thus, the relation holds over the integers.
//! The telescoping sum at `X = β` gives the integer equation for each identity.
//! Each multiplication is integer-exact.
//!
//! Each identity is a degree-29 polynomial.
//! With one `z` for all rows, the union bound is
//! `3 · rows · 29 / |QM31| ≈ 2^-105` for 4096 rows.
//!
//! # AIR shape
//!
//! Each multiplication uses one row.
//! The base trace has 307 columns:
//!
//! ```text
//! a[20] b[20] q1[11] m1[20] h1_lo[29] h1_hi[29]
//! q2[11] m2[20] h2_lo[29] h2_hi[29]
//! q3[11] r[20] h3_lo[29] h3_hi[29]
//! ```
//!
//! Three ungated extension-field constraints prove the identities.
//! Each constraint has degree two.
//! Zero padding rows satisfy them.
//!
//! Range13 checks every limb.
//! A signed table checks `h_hi` in `[−12, 12]`.
//! Each row provides the same `ProjectiveRcbMulResultRelation` tuples as the silo.

pub mod air;
pub mod formula_bind;
pub mod trace;
pub mod wide;
pub mod witness;

use stwo_constraint_framework::relation;

/// Links each projective-source operation row to its silo group header.
///
/// The tuple is `(source_index, op, output_inf, lhs_inf, rhs_inf)`.
///
/// Each projective-source consumer provides a tuple for an operation with silo multiplications.
/// The silo consumes it at the first multiplication row.
/// An infinity mixed-add row has no silo multiplication and emits no tuple.
pub const EC_OP_HEADER_RELATION_ARITY: usize = 5;

relation!(EcOpHeaderRelation, EC_OP_HEADER_RELATION_ARITY);
