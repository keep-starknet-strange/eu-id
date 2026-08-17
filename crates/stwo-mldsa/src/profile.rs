//! Verifier-selected FIPS 204 parameter sets used by the TS13 theorem.

use crate::constants::{D, N, Q, T1_BITS};

/// A fixed ML-DSA parameter set.
///
/// This value is circuit configuration. It is never read from a proof or
/// credential witness. The TS13 verifier selects ML-DSA-65 for issuer,
/// device, and revocation authentication.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MlDsaProfile {
    /// ML-DSA-44 parameter set (FIPS 204 §4, Table 1).
    MlDsa44,
    /// ML-DSA-65 parameter set (FIPS 204 §4, Table 1).
    MlDsa65,
}

impl MlDsaProfile {
    /// Rows of the matrix `A` / length of the `t`, `w`, `s2` vectors.
    pub const fn k(self) -> usize {
        match self {
            Self::MlDsa44 => 4,
            Self::MlDsa65 => 6,
        }
    }

    /// Columns of `A` / length of the `z`, `s1`, `y` vectors.
    pub const fn l(self) -> usize {
        match self {
            Self::MlDsa44 => 4,
            Self::MlDsa65 => 5,
        }
    }

    /// Number of ±1 entries in the challenge polynomial `c`.
    pub const fn tau(self) -> usize {
        match self {
            Self::MlDsa44 => 39,
            Self::MlDsa65 => 49,
        }
    }

    /// Coefficient range of the mask `y` and signature part `z`.
    pub const fn gamma1(self) -> u32 {
        match self {
            Self::MlDsa44 => 1 << 17,
            Self::MlDsa65 => 1 << 19,
        }
    }

    /// Low-order rounding range (`(q − 1) / 88` for ML-DSA-44,
    /// `(q − 1) / 32` for ML-DSA-65).
    pub const fn gamma2(self) -> u32 {
        match self {
            Self::MlDsa44 => (Q - 1) / 88,
            Self::MlDsa65 => (Q - 1) / 32,
        }
    }

    /// Secret-key coefficient bound `η`.
    pub const fn eta(self) -> u32 {
        match self {
            Self::MlDsa44 => 2,
            Self::MlDsa65 => 4,
        }
    }

    /// Rejection bound `β = τ · η`.
    pub const fn beta(self) -> u32 {
        self.tau() as u32 * self.eta()
    }

    /// Maximum number of `1`s in the hint `h`.
    pub const fn omega(self) -> usize {
        match self {
            Self::MlDsa44 => 80,
            Self::MlDsa65 => 55,
        }
    }

    /// Collision-strength parameter `λ` in bits.
    pub const fn lambda(self) -> usize {
        match self {
            Self::MlDsa44 => 128,
            Self::MlDsa65 => 192,
        }
    }

    /// Byte length of the commitment hash `c̃`: `2λ/8`.
    pub const fn c_tilde_bytes(self) -> usize {
        2 * self.lambda() / 8
    }

    /// Bit width used to pack each `z` coefficient: `1 + bitlen(γ1 − 1)`.
    pub const fn z_bits(self) -> usize {
        match self {
            Self::MlDsa44 => 18,
            Self::MlDsa65 => 20,
        }
    }

    /// Bit width used to pack each `w1` coefficient in `w1Encode`.
    pub const fn w1_bits(self) -> usize {
        match self {
            Self::MlDsa44 => 6,
            Self::MlDsa65 => 4,
        }
    }

    /// Number of possible `w1` values: `(q − 1) / (2·γ2)`.
    pub const fn w1_values(self) -> u32 {
        (Q - 1) / (2 * self.gamma2())
    }

    /// Encoded public-key length in bytes (FIPS 204 Algorithm 22 `pkEncode`).
    pub const fn pk_bytes(self) -> usize {
        32 + self.k() * (N * T1_BITS / 8)
    }

    /// Encoded signature length in bytes (FIPS 204 Algorithm 26 `sigEncode`).
    pub const fn sig_bytes(self) -> usize {
        self.c_tilde_bytes() + self.l() * (N * self.z_bits() / 8) + self.omega() + self.k()
    }

    /// Byte length of `w1Encode(w1)` for the full `w1` vector.
    pub const fn w1_encoded_bytes(self) -> usize {
        self.k() * N * self.w1_bits() / 8
    }

    /// Number of matrix polynomials: `k · l`.
    pub const fn matrix_polys(self) -> usize {
        self.k() * self.l()
    }

    /// COSE algorithm identifier (RFC 9964).
    pub const fn cose_alg(self) -> i64 {
        match self {
            Self::MlDsa44 => -48,
            Self::MlDsa65 => -49,
        }
    }

    /// Profile tag mixed into the Fiat–Shamir transcript.
    pub const fn transcript_tag(self) -> u64 {
        match self {
            Self::MlDsa44 => 44,
            Self::MlDsa65 => 65,
        }
    }

    /// Number of SHAKE-256 rate blocks the SampleInBall chain may squeeze.
    pub const fn sample_in_ball_squeeze_blocks(self) -> usize {
        match self {
            Self::MlDsa44 => 1,
            Self::MlDsa65 => 2,
        }
    }
}

/// ML-DSA-44 profile constant.
pub const ML_DSA_44: MlDsaProfile = MlDsaProfile::MlDsa44;
/// ML-DSA-65 profile constant.
pub const ML_DSA_65: MlDsaProfile = MlDsaProfile::MlDsa65;

const _: () = {
    assert!(D == 13);
    assert!(ML_DSA_44.pk_bytes() == 1_312);
    assert!(ML_DSA_44.sig_bytes() == 2_420);
    assert!(ML_DSA_44.w1_encoded_bytes() == 768);
    assert!(ML_DSA_44.w1_values() == 44);
    assert!(ML_DSA_65.pk_bytes() == 1_952);
    assert!(ML_DSA_65.sig_bytes() == 3_309);
    assert!(ML_DSA_65.w1_encoded_bytes() == 768);
    assert!(ML_DSA_65.w1_values() == 16);
};
