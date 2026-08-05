//! Verifier-selected FIPS 204 parameter sets used by the TS13 theorem.

use crate::constants::{D, N, Q, T1_BITS};

/// A fixed ML-DSA parameter set.
///
/// This value is circuit configuration. It is never read from a proof or
/// credential witness. The TS13 verifier selects ML-DSA-65 for issuer,
/// device, and revocation authentication.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MlDsaProfile {
    MlDsa44,
    MlDsa65,
}

impl MlDsaProfile {
    pub const fn k(self) -> usize {
        match self {
            Self::MlDsa44 => 4,
            Self::MlDsa65 => 6,
        }
    }

    pub const fn l(self) -> usize {
        match self {
            Self::MlDsa44 => 4,
            Self::MlDsa65 => 5,
        }
    }

    pub const fn tau(self) -> usize {
        match self {
            Self::MlDsa44 => 39,
            Self::MlDsa65 => 49,
        }
    }

    pub const fn gamma1(self) -> u32 {
        match self {
            Self::MlDsa44 => 1 << 17,
            Self::MlDsa65 => 1 << 19,
        }
    }

    pub const fn gamma2(self) -> u32 {
        match self {
            Self::MlDsa44 => (Q - 1) / 88,
            Self::MlDsa65 => (Q - 1) / 32,
        }
    }

    pub const fn eta(self) -> u32 {
        match self {
            Self::MlDsa44 => 2,
            Self::MlDsa65 => 4,
        }
    }

    pub const fn beta(self) -> u32 {
        self.tau() as u32 * self.eta()
    }

    pub const fn omega(self) -> usize {
        match self {
            Self::MlDsa44 => 80,
            Self::MlDsa65 => 55,
        }
    }

    pub const fn lambda(self) -> usize {
        match self {
            Self::MlDsa44 => 128,
            Self::MlDsa65 => 192,
        }
    }

    pub const fn c_tilde_bytes(self) -> usize {
        2 * self.lambda() / 8
    }

    pub const fn z_bits(self) -> usize {
        match self {
            Self::MlDsa44 => 18,
            Self::MlDsa65 => 20,
        }
    }

    pub const fn w1_bits(self) -> usize {
        match self {
            Self::MlDsa44 => 6,
            Self::MlDsa65 => 4,
        }
    }

    pub const fn w1_values(self) -> u32 {
        (Q - 1) / (2 * self.gamma2())
    }

    pub const fn pk_bytes(self) -> usize {
        32 + self.k() * (N * T1_BITS / 8)
    }

    pub const fn sig_bytes(self) -> usize {
        self.c_tilde_bytes() + self.l() * (N * self.z_bits() / 8) + self.omega() + self.k()
    }

    pub const fn w1_encoded_bytes(self) -> usize {
        self.k() * N * self.w1_bits() / 8
    }

    pub const fn matrix_polys(self) -> usize {
        self.k() * self.l()
    }

    pub const fn cose_alg(self) -> i64 {
        match self {
            Self::MlDsa44 => -48,
            Self::MlDsa65 => -49,
        }
    }

    pub const fn transcript_tag(self) -> u64 {
        match self {
            Self::MlDsa44 => 44,
            Self::MlDsa65 => 65,
        }
    }

    pub const fn sample_in_ball_squeeze_blocks(self) -> usize {
        match self {
            Self::MlDsa44 => 1,
            Self::MlDsa65 => 2,
        }
    }
}

pub const ML_DSA_44: MlDsaProfile = MlDsaProfile::MlDsa44;
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
