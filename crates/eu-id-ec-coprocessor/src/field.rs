use core::ops::{Add, Mul, Neg, Sub};
#[cfg(feature = "count-ops")]
use core::sync::atomic::{AtomicU64, Ordering};

use p256::elliptic_curve::ff::PrimeField;
use p256::elliptic_curve::rand_core::RngCore;
use p256::{FieldBytes, FieldElement};
use serde::de::Error as _;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

const P_BE: [u8; 32] = [
    0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];

#[cfg(feature = "count-ops")]
static FP_MUL_COUNT: AtomicU64 = AtomicU64::new(0);
#[cfg(feature = "count-ops")]
static FP_ADD_COUNT: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Fp(FieldElement);

impl Fp {
    pub const ZERO: Self = Self(FieldElement::ZERO);
    pub const ONE: Self = Self(FieldElement::ONE);

    pub fn from_bytes_be(bytes: [u8; 32]) -> Option<Self> {
        let repr = FieldBytes::from(bytes);
        let parsed: Option<FieldElement> = FieldElement::from_repr(repr).into();
        parsed.map(Self)
    }

    pub fn to_bytes_be(self) -> [u8; 32] {
        let repr = self.0.to_repr();
        let mut out = [0u8; 32];
        out.copy_from_slice(&repr);
        out
    }

    pub fn from_u64(value: u64) -> Self {
        Self(FieldElement::from(value))
    }

    /// Reduces 32 transcript bytes into F_p256. G0 accepts the tiny reduction
    /// bias, and canonical public decoding still uses `from_bytes_be`.
    pub fn random(bytes: [u8; 32]) -> Self {
        let reduced = if cmp_be(&bytes, &P_BE).is_ge() {
            sub_be(bytes, P_BE)
        } else {
            bytes
        };
        Self::from_bytes_be(reduced).expect("one subtraction maps 256-bit input below p")
    }

    /// Samples uniformly from F_p by rejecting the tiny `2^256 - p` tail.
    ///
    /// Fiat–Shamir challenges deliberately retain the historical reduction in
    /// [`Self::random`]. Secret masks use this method so their distribution is
    /// exactly uniform, as required by the committed-mask ZK argument.
    pub fn random_uniform(rng: &mut impl RngCore) -> Self {
        loop {
            let mut bytes = [0u8; 32];
            rng.fill_bytes(&mut bytes);
            if let Some(value) = Self::from_bytes_be(bytes) {
                return value;
            }
        }
    }

    pub fn square(self) -> Self {
        #[cfg(feature = "count-ops")]
        FP_MUL_COUNT.fetch_add(1, Ordering::Relaxed);
        Self(self.0.square())
    }

    pub fn inverse(self) -> Option<Self> {
        let inv: Option<FieldElement> = self.0.invert().into();
        inv.map(Self)
    }

    pub fn pow(self, exponent_be: [u8; 32]) -> Self {
        let mut words = [0u64; 4];
        for (i, chunk) in exponent_be.chunks_exact(8).enumerate() {
            words[3 - i] = u64::from_be_bytes(chunk.try_into().expect("8-byte chunk"));
        }
        Self(self.0.pow_vartime(&words))
    }

    pub fn batch_inverse(values: &[Self]) -> Vec<Self> {
        let mut out = vec![Self::ZERO; values.len()];
        let mut prefix = Vec::with_capacity(values.len());
        let mut acc = Self::ONE;
        for value in values {
            prefix.push(acc);
            if *value != Self::ZERO {
                acc = acc * *value;
            }
        }

        let Some(mut inv_acc) = acc.inverse() else {
            return out;
        };

        for (i, value) in values.iter().enumerate().rev() {
            if *value == Self::ZERO {
                continue;
            }
            out[i] = inv_acc * prefix[i];
            inv_acc = inv_acc * *value;
        }
        out
    }
}

#[cfg(feature = "count-ops")]
pub fn reset_fp_mul_count() {
    FP_MUL_COUNT.store(0, Ordering::Relaxed);
    FP_ADD_COUNT.store(0, Ordering::Relaxed);
}

#[cfg(feature = "count-ops")]
pub fn fp_mul_count() -> u64 {
    FP_MUL_COUNT.load(Ordering::Relaxed)
}

#[cfg(feature = "count-ops")]
pub fn fp_add_count() -> u64 {
    FP_ADD_COUNT.load(Ordering::Relaxed)
}

impl Serialize for Fp {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.to_bytes_be().serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Fp {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let bytes = <[u8; 32]>::deserialize(deserializer)?;
        Self::from_bytes_be(bytes).ok_or_else(|| D::Error::custom("non-canonical Fp encoding"))
    }
}

impl Add for Fp {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        #[cfg(feature = "count-ops")]
        FP_ADD_COUNT.fetch_add(1, Ordering::Relaxed);
        Self(self.0 + rhs.0)
    }
}

impl Sub for Fp {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        #[cfg(feature = "count-ops")]
        FP_ADD_COUNT.fetch_add(1, Ordering::Relaxed);
        Self(self.0 - rhs.0)
    }
}

impl Mul for Fp {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        #[cfg(feature = "count-ops")]
        FP_MUL_COUNT.fetch_add(1, Ordering::Relaxed);
        Self(self.0 * rhs.0)
    }
}

impl Neg for Fp {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self(-self.0)
    }
}

fn cmp_be(lhs: &[u8; 32], rhs: &[u8; 32]) -> core::cmp::Ordering {
    lhs.cmp(rhs)
}

fn sub_be(mut lhs: [u8; 32], rhs: [u8; 32]) -> [u8; 32] {
    let mut borrow = 0u16;
    for (a, b) in lhs.iter_mut().rev().zip(rhs.iter().rev()) {
        let ai = *a as u16;
        let bi = *b as u16 + borrow;
        if ai >= bi {
            *a = (ai - bi) as u8;
            borrow = 0;
        } else {
            *a = ((ai + 256) - bi) as u8;
            borrow = 1;
        }
    }
    debug_assert_eq!(borrow, 0);
    lhs
}
