//! Hinted mod-p multiplication with carry polynomials (P5 rewrite).
//!
//! Replaces the schoolbook Solinas silo (`projective_rcb_mul`'s raw-product /
//! folded / reduction families, ~290 trace rows per mul) with one row per mul
//! whose correctness is enforced by three polynomial carry identities checked
//! at a single channel-drawn point `z ∈ QM31` (drawn AFTER the base trace is
//! committed, exactly where the LogUp relations are drawn).
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
//! the residue class (the honest witness writes the canonical one); boundaries
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
//! The naive single identity `A·B − Q·P − R = (X−β)·H` does NOT lift: a 20×20
//! limb convolution has up to 20 terms per coefficient, so coefficients reach
//! `20·(β−1)² ≈ 1.342e9`, the carry values reach `≈ maxC/(β−1)`, and the
//! per-coefficient relation `c_k − h_{k−1} + β·h_k ≡ 0 (mod p_M31)` has slack
//! `maxC + β·H_range + H_range ≈ 2.68e9 > p_M31` — an adversary can wrap a
//! coefficient by `±p_M31` *within range bounds* and forge `a·b ≡ r' (mod p)`
//! with a wrong `r'`. This is a soundness requirement, not hygiene.
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
//! Worksheet (all identities share these bounds; see the constants in
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
//! No coefficient relation can wrap ⟹ each relation holds over ℤ ⟹ the
//! telescoping sum at `X = β` gives the integer equation per identity ⟹ the
//! mul is integer-exact. Schwartz–Zippel error: each identity is a degree-29
//! polynomial; with one `z` for all rows, union bound
//! `3 · rows · 29 / |QM31| ≈ 2^-105` for 4096 rows.
//!
//! # AIR shape (P5.2)
//!
//! One row per mul. Base columns: `a[20] b[20] q1[11] m1[20] h1_lo[29]
//! h1_hi[29] q2[11] m2[20] h2_lo[29] h2_hi[29] q3[11] r[20] h3_lo[29]
//! h3_hi[29]` = 307. Three UNGATED degree-2 EF constraints (per identity, the
//! products of two degree-1 limb combinations with constant `z`-power
//! coefficients; all-zero padding rows satisfy them trivially). Every limb
//! Range13-checked; `h_hi` checked against the `[−12, 12]` signed table. The
//! row provides the same `ProjectiveRcbMulResultRelation` tuples
//! `(source_index, mul_index, role, limb_index, limb)` the silo provides
//! today, so the EC-formula consumers are untouched.

pub mod wide;
pub mod witness;
