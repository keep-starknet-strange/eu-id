//! Witness and hint generator for in-circuit ML-DSA verification.
//!
//! This module contains native Rust and no AIR code. [`generate_witness`] runs
//! the reference verifier ([`crate::verify_internals`]) and materializes each
//! value that the integer-lift AIR commits.
//!
//! ## Integer-lift identity
//!
//! For each active row `i ∈ [k]`, the verifier's linear obligation [LIN] is the
//! `R_q` identity `Σ_j A_ij·z_j − c·(t1_i·2^d) ≡ w_i`. We prove the equivalent
//! **ℤ[X]** identity with committed quotient witnesses `v_i` (the X²⁵⁶ fold) and
//! `e_i` (the q fold):
//!
//! ```text
//!   u_i(X) := Σ_j A_ij·z_j − c·t1_i·2^d                            (deg ≤ 510)
//!   u_i(X) = w_i + q·e_i + (X^256 + 1)·v_i        over ℤ[X]        (†)
//! ```
//!
//! where `A_ij = NTT⁻¹(Â_ij)` are the **integer** matrix polynomials (coeffs in
//! `[0, q)`), `z` is centered, `c` is ternary, and `w_i` is the canonical `R_q`
//! commitment from the reference (`VerifyTrace::w_approx`).
//!
//! ## Witness layout
//!
//! - `u[i]`: the ℤ[X] products in `i128`, with degree at most 510.
//! - `v[i]` and `e[i]`: the two quotient witnesses.
//! - Balanced base-512 digits for z, w, e, v, and c.
//! - Carries `C[i][m][t]` for `m ∈ [0,510]` and `t ∈ [0,4]`.
//! - Recomposition values that bind the z and w digits.
//! - `decomp`: w1, w0, hint, and UseHint values.
//! - `sponge`: µ, c̃, and SampleInBall byte streams.
//!
//! The generator checks each integer invariant in `i128` with no field
//! reduction. It checks each limb equation `E_{m,t} == 0`, exact
//! q-divisibility of `e`, every digit in `[−256, 256)`, every honest carry
//! `|C| ≤ 2^20`, and the recomposition binding. Invalid input causes witness
//! generation to fail.

// This module is a numeric kernel: `A_ij[m]`, `u[a+z]`, `F[m][t]` and the
// convolution loops carry mathematical meaning in their indices, so explicit
// `for i in 0..N` indexing is the readable form here.
#![allow(clippy::needless_range_loop)]
// `x % m == 0` is the divisibility check we mean; `is_multiple_of` is not stable
// for `i128` on this toolchain.
#![allow(clippy::manual_is_multiple_of)]

use crate::constants::{D, K, L, N, Q};
use crate::profile::MlDsaProfile;
use crate::reference::ntt::ntt_inverse;
use crate::reference::verify::VerifyTrace;
use crate::types::MlDsaVerifyInput;
use crate::MlDsaError;

// ---------------------------------------------------------------------------
// Integer-lift layout constants.
// ---------------------------------------------------------------------------

/// Balanced-digit base `B = 2^9 = 512`, with a 3.0× lift margin.
pub const B: i128 = 512;

/// Half-base: digits live in the half-open window `[−HALF_B, HALF_B) = [−256, 256)`.
pub const HALF_B: i128 = B / 2;

/// Degree bound of the ℤ[X] product `u_i`: `deg ≤ 510` ⇒ 511 coefficients.
pub const U_LEN: usize = 2 * N - 1; // 511

/// Digit counts for each polynomial kind.
pub const T_Z: usize = 3;
/// `w_i` digit count.
pub const T_W: usize = 3;
/// `e_i` digit count.
pub const T_E: usize = 4;
/// `v_i` digit count.
pub const T_V: usize = 6;
/// `A_ij` (public) digit count.
pub const T_A: usize = 3;
/// `t1_i·2^d` (public) digit count.
pub const T_T1: usize = 3;

/// Highest carry index `T_max = 4`. Carry columns exist for `t ∈ [0, 4]`.
/// The Y-degree of `F̂` is at most 5, and honest `C_{m,t}=0` for `t ≥ 5`.
pub const T_MAX: usize = 4;

/// Carry range bound. Honest `|C| ≤ 2^18.42`, and the range check uses `2^20`.
pub const CARRY_BOUND: i128 = 1 << 20;

/// `q` in balanced base-B digits at `B = 2^9`.
/// `1 − 16·512 + 32·512² = 8_380_417 = q`.
pub const Q_DIGITS: [i128; 3] = [1, -16, 32];

// ---------------------------------------------------------------------------
// Witness sub-structures.
// ---------------------------------------------------------------------------

/// Per-row limb-identity witness for one `i ∈ [k]`.
#[derive(Clone, Debug)]
pub struct RowWitness {
    /// `v_i`: high half of `u_i`, `v_{i,m} = u_{i,m+256}`, `m ∈ [0,254]`.
    pub v: Vec<i128>,
    /// `e_i`: `e_{i,m} = (u_{i,m} − w_{i,m} − v_{i,m})/q`, `m ∈ [0,255]` (exact).
    pub e: Vec<i128>,
    /// `w_i`: the canonical `R_q` commitment coefficients (from `VerifyTrace`).
    pub w: [u32; N],
    /// Carries `carry[m][t]` for `m ∈ [0,510]`, `t ∈ [0, T_MAX]`.
    pub carry: Vec<[i128; T_MAX + 1]>,
}

/// Balanced-digit tables for all committed polynomials. Each
/// inner `Vec` is indexed by coefficient `m`; each row holds that coefficient's
/// low-first digits.
#[derive(Clone, Debug, Default)]
pub struct DigitTables {
    /// `z_digits[j][m]` — 3 digits per coefficient (`T_Z`), `j ∈ [l]`.
    pub z: Vec<Vec<[i128; T_Z]>>,
    /// `w_digits[i][m]` — 3 digits (`T_W`), `i ∈ [k]`.
    pub w: Vec<Vec<[i128; T_W]>>,
    /// `e_digits[i][m]` — 4 digits (`T_E`).
    pub e: Vec<Vec<[i128; T_E]>>,
    /// `v_digits[i][m]` — 6 digits (`T_V`).
    pub v: Vec<Vec<[i128; T_V]>>,
    /// `a_digits[i][j][m]` — 3 digits (`T_A`), public `A_ij = NTT⁻¹(Â_ij)`.
    pub a: Vec<Vec<Vec<[i128; T_A]>>>,
    /// `t1_digits[i][m]` — 3 digits (`T_T1`), public `t1_i·2^d`.
    pub t1: Vec<Vec<[i128; T_T1]>>,
    /// `c_digits[m]` — the challenge `c`; ternary is its own single digit.
    pub c: Vec<i128>,
}

/// Decompose and hint witness from `VerifyTrace`.
#[derive(Clone, Debug)]
pub struct DecompWitness {
    /// `w1[i][m]` is in the selected profile's high-bit range.
    pub w1: [[u32; N]; K],
    /// `w0[i][m]` — centered low part in `(−γ2, γ2]`, plus the FIPS wrap
    /// special case `−γ2` when the pre-hint high part is zero.
    pub w0: [[i32; N]; K],
    /// `hint[i][m] ∈ {0,1}` — the hint bits.
    pub hint: [[u8; N]; K],
    /// `hint_weight[i] = Σ_m hint[i][m]` (must satisfy `Σ_i ≤ ω`).
    pub hint_weight: [usize; K],
}

/// SHAKE absorb and squeeze streams from the reference sponge.
#[derive(Clone, Debug)]
pub struct SpongeWitness {
    /// `µ = H(tr ‖ 0x00 ‖ |ctx| ‖ ctx ‖ M)` absorb+squeeze.
    pub mu_absorbed: Vec<u8>,
    /// Squeezed `µ` bytes.
    pub mu_squeezed: Vec<u8>,
    /// `c̃' = H(µ ‖ w1Encode(w1'))` absorb.
    pub c_tilde_absorbed: Vec<u8>,
    /// Squeezed `c̃'` bytes.
    pub c_tilde_squeezed: Vec<u8>,
    /// `SampleInBall(c̃)` absorb (the seed `c̃`).
    pub sample_in_ball_absorbed: Vec<u8>,
    /// `SampleInBall` squeezed stream (sign bits + placement bytes).
    pub sample_in_ball_squeezed: Vec<u8>,
}

/// Maximum values observed while the generator builds one witness.
#[derive(Clone, Copy, Debug, Default)]
pub struct ObservedMaxima {
    /// Max `|E_{m,t}|` **before** the `B·C_out − C_in` carry terms are applied
    /// (i.e. the product/witness residual the carry must absorb).
    pub max_partial_before_carry: i128,
    /// Max honest `|C_{m,t}|`.
    pub max_carry: i128,
    /// Max `|digit|` over z polynomials.
    pub max_digit_z: i128,
    /// Max `|digit|` over w polynomials.
    pub max_digit_w: i128,
    /// Max `|digit|` over e polynomials.
    pub max_digit_e: i128,
    /// Max `|digit|` over v polynomials.
    pub max_digit_v: i128,
}

/// The complete witness for one ML-DSA signature.
#[derive(Clone, Debug)]
pub struct MlDsaWitness {
    /// Verifier-selected parameter set used to build this witness.
    pub profile: MlDsaProfile,
    /// Per-row limb-identity witness (`u`, `v`, `e`, `w`, carries).
    pub rows: Vec<RowWitness>,
    /// Balanced-digit tables for all committed + public polynomials.
    pub digits: DigitTables,
    /// Decompose / hint witness.
    pub decomp: DecompWitness,
    /// SHAKE transcripts.
    pub sponge: SpongeWitness,
    /// Empirical maxima observed during construction.
    pub maxima: ObservedMaxima,
}

/// Errors from witness generation.
#[derive(Debug)]
pub enum WitnessError {
    /// The fixed-size internal input contains data outside the selected wire
    /// profile.
    InvalidInput(&'static str),
    /// The reference verifier reported a decode or structure error.
    Reference(MlDsaError),
    /// The reference verified the signature as **invalid** (norm or commitment
    /// mismatch): there is no honest witness to generate.
    NotAccepted(crate::RejectReason),
}

impl core::fmt::Display for WitnessError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidInput(message) => write!(f, "invalid profiled input: {message}"),
            Self::Reference(e) => write!(f, "reference decode error: {e}"),
            Self::NotAccepted(r) => write!(f, "signature not accepted by reference: {r:?}"),
        }
    }
}

impl std::error::Error for WitnessError {}

// ---------------------------------------------------------------------------
// Balanced base-B digit decomposition.
// ---------------------------------------------------------------------------

/// Decompose signed `x` into exactly `T` balanced base-B digits in `[−256, 256)`,
/// low-first. Panics if `x` does not fit in `T` digits (a soundness assert: the
/// digit-count budget in §3.1 must cover every honest coefficient).
pub(crate) fn balanced_digits<const T: usize>(mut x: i128) -> [i128; T] {
    let mut out = [0i128; T];
    for slot in out.iter_mut() {
        // Centered remainder: r ∈ [−B/2, B/2).
        let mut r = x.rem_euclid(B);
        if r >= HALF_B {
            r -= B;
        }
        debug_assert!((-HALF_B..HALF_B).contains(&r));
        *slot = r;
        x = (x - r) / B;
    }
    assert_eq!(
        x, 0,
        "balanced_digits: value does not fit in {T} base-{B} digits"
    );
    out
}

/// Recompose balanced digits as `Σ_t d_t·B^t`.
fn recompose(digits: &[i128]) -> i128 {
    let mut acc = 0i128;
    let mut weight = 1i128;
    for &d in digits {
        acc += d * weight;
        weight *= B;
    }
    acc
}

// ---------------------------------------------------------------------------
// The generator.
// ---------------------------------------------------------------------------

/// Run the reference verifier and materialize the integer-lift witness.
///
/// Check each integer invariant over ℤ (`i128`). Return
/// [`WitnessError`] on a decode error or a non-accepted signature.
pub fn generate_witness(
    profile: MlDsaProfile,
    input: &MlDsaVerifyInput,
) -> Result<MlDsaWitness, WitnessError> {
    input
        .validate_public_key(profile)
        .map_err(WitnessError::InvalidInput)?;
    input
        .validate_signature(profile)
        .map_err(WitnessError::InvalidInput)?;
    let pk = input.encode_pk(profile);
    let sig = input.encode_sig(profile);
    let trace = crate::reference::verify::verify_internals(profile, &pk, &input.message, &sig)
        .map_err(WitnessError::Reference)?;
    if !trace.accepted {
        return Err(WitnessError::NotAccepted(trace.reason));
    }
    build_from_trace(profile, input, &trace)
}

/// Core builder, split out so tests can drive it from a `VerifyTrace` directly.
fn build_from_trace(
    profile: MlDsaProfile,
    input: &MlDsaVerifyInput,
    trace: &VerifyTrace,
) -> Result<MlDsaWitness, WitnessError> {
    let q = Q as i128;
    let two_d = 1i128 << D;

    // --- Public integer matrix A_ij = NTT⁻¹(Â_ij), coeffs in [0,q) --------
    // Recompute Â = ExpandA(ρ) and invert each entry into the integer domain.
    let a_hat = crate::reference::expand_a::expand_a(profile, &trace.rho);
    let mut a_int = vec![vec![[0i128; N]; L]; K];
    for i in 0..K {
        for j in 0..L {
            let poly = ntt_inverse(&a_hat.matrix[i][j]); // [u32; N] in [0,q)
            for m in 0..N {
                a_int[i][j][m] = poly[m] as i128;
            }
        }
    }

    // --- c (ternary, {−1,0,1}) and z (centered) as integers ---------------
    let c_int: Vec<i128> = trace.c.iter().map(|&x| x as i128).collect();
    let z_int: Vec<[i128; N]> = trace
        .z
        .iter()
        .map(|poly| {
            let mut out = [0i128; N];
            for m in 0..N {
                out[m] = poly[m] as i128;
            }
            out
        })
        .collect();

    // --- t1_i·2^d (public), integer coeffs in [0, 2^23) -------------------
    let mut t1_2d = vec![[0i128; N]; K];
    for i in 0..K {
        for m in 0..N {
            t1_2d[i][m] = input.t1[i][m] as i128 * two_d;
        }
    }

    let mut maxima = ObservedMaxima::default();
    let mut rows: Vec<RowWitness> = Vec::with_capacity(K);
    let mut digits = DigitTables {
        a: vec![Vec::new(); K],
        t1: vec![Vec::new(); K],
        w: vec![Vec::new(); K],
        e: vec![Vec::new(); K],
        v: vec![Vec::new(); K],
        z: Vec::with_capacity(L),
        c: c_int.clone(),
    };

    // Digit tables for z (shared across rows).
    for j in 0..L {
        let mut per_coeff = Vec::with_capacity(N);
        for m in 0..N {
            let d = balanced_digits::<T_Z>(z_int[j][m]);
            for &dig in &d {
                maxima.max_digit_z = maxima.max_digit_z.max(dig.abs());
            }
            // Recomposition binding (§3.4): cell == Σ_t digit·B^t.
            assert_eq!(
                recompose(&d),
                z_int[j][m],
                "z recomposition binding failed (§3.4): j={j} m={m}"
            );
            per_coeff.push(d);
        }
        digits.z.push(per_coeff);
    }

    // Per-row: u, v, e, w, carries, and A/t1/w/e/v digit tables.
    for i in 0..K {
        // u_i(X) = Σ_j A_ij·z_j − c·t1_i·2^d, as a ℤ[X] convolution (deg ≤ 510).
        let mut u = vec![0i128; U_LEN];
        // Σ_j A_ij · z_j (negacyclic-free: this is the *ℤ[X]* product, no fold).
        for j in 0..L {
            for a_idx in 0..N {
                let a_coeff = a_int[i][j][a_idx];
                if a_coeff == 0 {
                    continue;
                }
                for z_idx in 0..N {
                    u[a_idx + z_idx] += a_coeff * z_int[j][z_idx];
                }
            }
        }
        // − c · (t1_i·2^d): ℤ[X] product of c and t1_2d[i].
        for c_idx in 0..N {
            let cc = c_int[c_idx];
            if cc == 0 {
                continue;
            }
            for t_idx in 0..N {
                u[c_idx + t_idx] -= cc * t1_2d[i][t_idx];
            }
        }

        // w_i: canonical R_q commitment from the reference.
        let w = trace.w_approx[i];

        // v_i: high half, v_{i,m} = u_{i,m+256}, m ∈ [0,254] (deg v ≤ 254).
        let v: Vec<i128> = u[N..].to_vec(); // 255 coeffs (indices 256..510)

        // e_i: (u_m − w_m − v_m)/q, m ∈ [0,255], exact divisibility.
        // For m ∈ [0,255]: (X^256+1)·v contributes v_m (the "+1" part; v_{m-256}
        // is 0 since m < 256). v_255 = 0 (deg v ≤ 254).
        let mut e = vec![0i128; N];
        for m in 0..N {
            let v_m = if m < N - 1 { v[m] } else { 0 };
            let num = u[m] - w[m] as i128 - v_m;
            assert!(num % q == 0, "e divisibility failed: i={i} m={m} num={num}");
            e[m] = num / q;
        }

        for &vv in &v {
            for d in balanced_digits::<T_V>(vv) {
                maxima.max_digit_v = maxima.max_digit_v.max(d.abs());
            }
        }
        for &ee in &e {
            for d in balanced_digits::<T_E>(ee) {
                maxima.max_digit_e = maxima.max_digit_e.max(d.abs());
            }
        }

        // --- Digit tables for this row --------------------------------------
        let mut a_row = Vec::with_capacity(L);
        for j in 0..L {
            let mut per = Vec::with_capacity(N);
            for m in 0..N {
                per.push(balanced_digits::<T_A>(a_int[i][j][m]));
            }
            a_row.push(per);
        }
        digits.a[i] = a_row;

        let mut t1_row = Vec::with_capacity(N);
        for m in 0..N {
            t1_row.push(balanced_digits::<T_T1>(t1_2d[i][m]));
        }
        digits.t1[i] = t1_row;

        let mut w_row = Vec::with_capacity(N);
        for m in 0..N {
            let d = balanced_digits::<T_W>(w[m] as i128);
            for &dig in &d {
                maxima.max_digit_w = maxima.max_digit_w.max(dig.abs());
            }
            assert_eq!(
                recompose(&d),
                w[m] as i128,
                "w recomposition binding failed (§3.4): i={i} m={m}"
            );
            w_row.push(d);
        }
        digits.w[i] = w_row;

        let mut e_row = Vec::with_capacity(N);
        for m in 0..N {
            e_row.push(balanced_digits::<T_E>(e[m]));
        }
        digits.e[i] = e_row;

        let mut v_row = Vec::with_capacity(N - 1);
        for m in 0..(N - 1) {
            v_row.push(balanced_digits::<T_V>(v[m]));
        }
        digits.v[i] = v_row;

        // --- Carries C_{m,t} and the limb identity E_{m,t} == 0 (§3.3) ------
        let carry = compute_carries(
            &digits.a[i],
            &digits.z,
            &digits.c,
            &digits.t1[i],
            &digits.w[i],
            &digits.v[i],
            &digits.e[i],
            &mut maxima,
        );

        rows.push(RowWitness { v, e, w, carry });
    }

    // Decompose and hint witness.
    let decomp = build_decomp(profile, trace);

    // SHAKE transcripts.
    let sponge = SpongeWitness {
        mu_absorbed: trace.mu_transcript.absorbed.clone(),
        mu_squeezed: trace.mu_transcript.squeezed.clone(),
        c_tilde_absorbed: trace.c_tilde_transcript.absorbed.clone(),
        c_tilde_squeezed: trace.c_tilde_transcript.squeezed.clone(),
        sample_in_ball_absorbed: trace.sample_in_ball_transcript.absorbed.clone(),
        sample_in_ball_squeezed: trace.sample_in_ball_transcript.squeezed.clone(),
    };

    Ok(MlDsaWitness {
        profile,
        rows,
        digits,
        decomp,
        sponge,
        maxima,
    })
}

/// Compute the per-limb carries and assert the limb identity `E_{m,t} == 0` for
/// every `m ∈ [0,510]` and `t ∈ [0, T_MAX+1]`.
///
/// The bivariate check `D̂ = F̂ − (Y−B)·Ĉ` has Y-degree `T_MAX+1 = 5` (the
/// `q̂·ê` term reaches `t = 2+3 = 5`), so there is one identity equation per
/// `t ∈ [0, 5]`, while the carry polynomial `Ĉ` has columns only for
/// `t ∈ [0, T_MAX=4]` (`C_{m,−1} = C_{m,5} = 0` structurally):
///
/// ```text
///   E_{m,t} = F_{m,t} − C_{m,t−1} + B·C_{m,t} = 0        (sign of −(Y−B)Ĉ)
///     t = 0 :  C_{m,0} = −F_{m,0}/B
///     t ∈ [1,4] :  C_{m,t} = (C_{m,t−1} − F_{m,t})/B
///     t = 5 :  F_{m,5} − C_{m,4} = 0   (boundary, no carry-out)
/// ```
///
/// We assert exact `B`-divisibility at each carry step and that the closing
/// `t = 5` boundary equation holds (this is what forces the carry chain to zero
/// out. No explicit boundary constraint is necessary.
#[allow(clippy::too_many_arguments)]
fn compute_carries(
    a_digits: &[Vec<[i128; T_A]>], // a_digits[j][m]
    z_digits: &[Vec<[i128; T_Z]>], // z_digits[j][m]
    c_digits: &[i128],             // c_digits[m]  (single digit each)
    t1_digits: &[[i128; T_T1]],    // t1_digits[m]
    w_digits: &[[i128; T_W]],      // w_digits[m]
    v_digits: &[[i128; T_V]],      // v_digits[m]  (m ∈ [0,254])
    e_digits: &[[i128; T_E]],      // e_digits[m]
    maxima: &mut ObservedMaxima,
) -> Vec<[i128; T_MAX + 1]> {
    // Residual table F[m][t], t ∈ [0, T_MAX+1] (the extra top row t=5 is the
    // closing boundary — the `q̂·ê` term reaches t=5). Built once in a single
    // digit-convolution pass, then swept for carries.
    let f = build_residual_table(
        a_digits, z_digits, c_digits, t1_digits, w_digits, v_digits, e_digits,
    );

    let mut carry = vec![[0i128; T_MAX + 1]; U_LEN];
    for m in 0..U_LEN {
        let mut c_prev = 0i128; // C_{m,−1} = 0 (structural).
                                // Carry columns t ∈ [0, T_MAX]: solve E_{m,t}=0 for the carry-out.
        for t in 0..=T_MAX {
            // E_{m,t} = F_{m,t} − C_prev + B·C_out = 0  ⇒  C_out = (C_prev − F)/B.
            let partial = f[m][t] - c_prev;
            maxima.max_partial_before_carry = maxima.max_partial_before_carry.max(partial.abs());
            assert!(
                partial % B == 0,
                "limb identity is not B-divisible at m={m} t={t}: F−C_prev={partial}"
            );
            let c_out = -partial / B;

            carry[m][t] = c_out;
            maxima.max_carry = maxima.max_carry.max(c_out.abs());
            assert!(
                c_out.abs() <= CARRY_BOUND,
                "honest carry exceeds 2^20 at m={m} t={t}: {c_out}"
            );
            c_prev = c_out;
        }
        // Closing boundary t = T_MAX+1 = 5: no carry-out column (C_{m,5}=0), so
        // E_{m,5} = F_{m,5} − C_{m,4} must be zero.
        let boundary = f[m][T_MAX + 1] - c_prev;
        maxima.max_partial_before_carry = maxima.max_partial_before_carry.max(boundary.abs());
        assert_eq!(
            boundary,
            0,
            "closing limb identity E_{{m,5}} != 0 at m={m}: \
             F_{{m,5}}={} C_{{m,4}}={c_prev}",
            f[m][T_MAX + 1]
        );
    }

    carry
}

/// Build the residual table `F[m][t]` at limb `(m,t)`.
///
/// The table contains the product terms minus the w, v, and q·e terms. It
/// excludes the carry term `−C_{m,t−1} + B·C_{m,t}`. The range of `t` is
/// `[0, T_MAX+1]`. One pass processes each digit pair.
#[allow(clippy::too_many_arguments)]
fn build_residual_table(
    a_digits: &[Vec<[i128; T_A]>],
    z_digits: &[Vec<[i128; T_Z]>],
    c_digits: &[i128],
    t1_digits: &[[i128; T_T1]],
    w_digits: &[[i128; T_W]],
    v_digits: &[[i128; T_V]],
    e_digits: &[[i128; T_E]],
) -> Vec<[i128; T_MAX + 2]> {
    let mut f = vec![[0i128; T_MAX + 2]; U_LEN];

    // + Σ_j Σ_a Σ_b Σ_{t1,t2} A_{j,a,t1}·z_{j,b,t2}  at (m=a+b, t=t1+t2).
    for j in 0..a_digits.len() {
        for a_pos in 0..N {
            let a_arr = &a_digits[j][a_pos];
            for b_pos in 0..N {
                let m = a_pos + b_pos;
                let z_arr = &z_digits[j][b_pos];
                let row = &mut f[m];
                for (t1, &ad) in a_arr.iter().enumerate() {
                    if ad == 0 {
                        continue;
                    }
                    for (t2, &zd) in z_arr.iter().enumerate() {
                        row[t1 + t2] += ad * zd;
                    }
                }
            }
        }
    }

    // − (c · t1_i·2^d): c is a single digit at weight-index 0, so pairing with
    // t1 digit index t1 lands at t = t1, m = a+b.
    for a_pos in 0..N {
        let cc = c_digits[a_pos];
        if cc == 0 {
            continue;
        }
        for b_pos in 0..N {
            let m = a_pos + b_pos;
            let t1 = &t1_digits[b_pos];
            let row = &mut f[m];
            for (t, &td) in t1.iter().enumerate() {
                row[t] -= cc * td;
            }
        }
    }

    // − w_{m,t}
    for (m, wd) in w_digits.iter().enumerate() {
        for (t, &d) in wd.iter().enumerate() {
            f[m][t] -= d;
        }
    }

    // − v-part: (X^256+1)·v contributes v at index m ("+1") and m+256 (X^256).
    for (m, vd) in v_digits.iter().enumerate() {
        for (t, &d) in vd.iter().enumerate() {
            f[m][t] -= d; // "+1"·v at coeff m
            f[m + N][t] -= d; // X^256·v at coeff m+256
        }
    }

    // − (q̂ · e)_{m,t} = − Σ_{t1+t2=t} q_{t1}·e_{m,t2}, q̂ = (1,−16,32).
    for (m, ed) in e_digits.iter().enumerate() {
        for (t1, &qd) in Q_DIGITS.iter().enumerate() {
            for (t2, &ev) in ed.iter().enumerate() {
                f[m][t1 + t2] -= qd * ev;
            }
        }
    }

    f
}

/// Build the decompose/hint witness from the reference trace: recover `w0` (the
/// centered low part) alongside the reference's `w1` and hint bits.
fn build_decomp(profile: MlDsaProfile, trace: &VerifyTrace) -> DecompWitness {
    let mut w0 = [[0i32; N]; K];
    let mut hint = [[0u8; N]; K];
    let mut hint_weight = [0usize; K];

    // Reconstruct the hint bits and w0 from w_approx. The reference exposes w1
    // (post-UseHint) and w_approx; the hint bit is recoverable as
    // hint = (w1 != HighBits(w_approx)). w0 is Decompose(w_approx).1.
    for i in 0..profile.k() {
        for m in 0..N {
            let r = trace.w_approx[i][m];
            let (r1, r0) = crate::reference::decompose::decompose(profile, r);
            w0[i][m] = r0;
            let h = if trace.w1[i][m] as i32 != r1 { 1 } else { 0 };
            hint[i][m] = h;
            hint_weight[i] += h as usize;
        }
    }

    DecompWitness {
        w1: trace.w1,
        w0,
        hint,
        hint_weight,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn q_digits_recompose_to_q() {
        assert_eq!(
            recompose(&Q_DIGITS),
            Q as i128,
            "q̂ = (1,−16,32) must equal q"
        );
    }

    #[test]
    fn balanced_digits_round_trip() {
        for &x in &[
            0i128,
            1,
            -1,
            255,
            -256,
            511,
            -512,
            8_380_416,
            -8_380_416,
            1 << 40,
        ] {
            let d = balanced_digits::<6>(x);
            assert!(
                d.iter().all(|&v| (-256..256).contains(&v)),
                "digit out of range for {x}"
            );
            assert_eq!(recompose(&d), x, "recompose mismatch for {x}");
        }
    }
}
