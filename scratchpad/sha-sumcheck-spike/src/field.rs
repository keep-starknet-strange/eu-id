//! Two field encodings for the SHA boolean circuit.
//!
//! (a) M31: the Mersenne-31 prime field, bit-per-wire. Wires hold {0,1} ⊂ M31.
//!     Quadratic gate identities: AND(a,b)=a·b, XOR(a,b)=a+b−2ab, NOT(a)=1−a.
//! (b) GF(2^128): packed-XOR (Longfellow-style). XOR = field addition. The
//!     gf128_mul carryless-multiply is COPIED from
//!     crates/eu-id-ec-coprocessor/src/mac.rs (bit-serial reference form) so
//!     the build stays isolated.

// ---------------------------------------------------------------------------
// M31
// ---------------------------------------------------------------------------

pub const M31_P: u64 = (1 << 31) - 1;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct M31(pub u32);

impl M31 {
    #[inline(always)]
    pub const fn new(v: u32) -> Self {
        M31(v % (M31_P as u32))
    }
    #[inline(always)]
    pub fn zero() -> Self {
        M31(0)
    }
    #[inline(always)]
    pub fn one() -> Self {
        M31(1)
    }
    #[inline(always)]
    pub fn add(self, o: Self) -> Self {
        let s = self.0 as u64 + o.0 as u64;
        let s = if s >= M31_P { s - M31_P } else { s };
        M31(s as u32)
    }
    #[inline(always)]
    pub fn sub(self, o: Self) -> Self {
        let s = self.0 as u64 + M31_P - o.0 as u64;
        let s = if s >= M31_P { s - M31_P } else { s };
        M31(s as u32)
    }
    #[inline(always)]
    pub fn mul(self, o: Self) -> Self {
        // 31-bit × 31-bit = 62-bit; reduce mod 2^31−1 via fold.
        let prod = self.0 as u64 * o.0 as u64;
        let lo = prod & M31_P;
        let hi = prod >> 31;
        let s = lo + hi;
        let s = if s >= M31_P { s - M31_P } else { s };
        M31(s as u32)
    }
}

// ---------------------------------------------------------------------------
// GF(2^128)
// ---------------------------------------------------------------------------

/// Little-endian 128-bit element as two u64 limbs (lo, hi).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Gf128(pub u64, pub u64);

impl Gf128 {
    #[inline(always)]
    pub fn zero() -> Self {
        Gf128(0, 0)
    }
    #[inline(always)]
    pub fn from_bit(b: bool) -> Self {
        Gf128(b as u64, 0)
    }
    /// XOR = field addition.
    #[inline(always)]
    pub fn add(self, o: Self) -> Self {
        Gf128(self.0 ^ o.0, self.1 ^ o.1)
    }
    /// Hardware carryless multiply (ARM PMULL / `vmull_p64`) + GHASH reduction.
    /// This is the credible Longfellow-style GF(2^128) mul; the bit-serial
    /// `mul_bitserial` below (copied from mac.rs) is kept only for the KAT.
    #[cfg(target_arch = "aarch64")]
    #[inline]
    pub fn mul(self, o: Self) -> Self {
        use std::arch::aarch64::*;
        // Bit conventions: mac.rs treats bit i as coefficient of x^i with
        // little-endian byte/bit order; that matches limb bit i here. PMULL
        // multiplies polynomials with the same convention. Reduction taps
        // {0,1,2,7} ⇒ modulus x^128 + x^7 + x^2 + x + 1.
        unsafe {
            let a = self.0 as u128 | ((self.1 as u128) << 64);
            let b = o.0 as u128 | ((o.1 as u128) << 64);
            let a_lo = a as u64;
            let a_hi = (a >> 64) as u64;
            let b_lo = b as u64;
            let b_hi = (b >> 64) as u64;
            // Karatsuba: 3 PMULLs.
            let z0 = vmull_p64(a_lo, b_lo); // low 128
            let z2 = vmull_p64(a_hi, b_hi); // high 128
            let z1 = vmull_p64(a_lo ^ a_hi, b_lo ^ b_hi);
            let z0u = z0 as u128;
            let z2u = z2 as u128;
            let mid = (z1 as u128) ^ z0u ^ z2u;
            // 256-bit product split into lo (bits 0..128) and hi (128..256)
            let lo = z0u ^ (mid << 64);
            let hi = z2u ^ (mid >> 64);
            // Reduce hi·x^128 mod (x^128 + x^7 + x^2 + x + 1). Fold twice.
            let reduced = Self::reduce256(lo, hi);
            Gf128(reduced as u64, (reduced >> 64) as u64)
        }
    }

    /// Fold the high 128 bits into the low 128 using taps {0,1,2,7}.
    #[cfg(target_arch = "aarch64")]
    #[inline]
    fn reduce256(lo: u128, hi: u128) -> u128 {
        // For each set bit h (128..256) i.e. bit (h-128) of `hi`, XOR taps at
        // (h-128)+{0,1,2,7}. Do it as two carryless folds by the tap poly
        // R = x^7+x^2+x+1 (0x87 low byte). Standard GHASH double-fold.
        // hi represents coefficients of x^128..x^255.
        // Step 1: multiply hi by R into a 128+7 bit intermediate, split again.
        let r: u128 = 0x87; // x^7+x^2+x+1
        // carryless mul hi * r, bit-serial over the 8 low bits of r (cheap: 4 taps)
        let mut fold_lo: u128 = 0;
        let mut fold_hi: u128 = 0;
        for off in [0u32, 1, 2, 7] {
            fold_lo ^= hi << off;
            if off > 0 {
                fold_hi ^= hi >> (128 - off);
            }
        }
        let _ = r;
        // fold_hi are bits >=128 again; fold once more (its top is < 2^7 so single pass)
        let mut extra: u128 = 0;
        for off in [0u32, 1, 2, 7] {
            extra ^= fold_hi << off;
        }
        lo ^ fold_lo ^ extra
    }

    /// Bit-serial carryless multiply COPIED from
    /// crates/eu-id-ec-coprocessor/src/mac.rs::gf128_mul (portable reference,
    /// used for the correctness KAT against the hardware path).
    #[cfg(not(target_arch = "aarch64"))]
    #[inline]
    pub fn mul(self, o: Self) -> Self {
        self.mul_bitserial(o)
    }

    #[inline]
    pub fn mul_bitserial(self, o: Self) -> Self {
        // 255-bit product, stored as 4 u64 limbs (bit 255 unused).
        let a = [self.0, self.1];
        let b = [o.0, o.1];
        let mut prod = [0u64; 4];
        for i in 0..128 {
            if (a[i >> 6] >> (i & 63)) & 1 == 0 {
                continue;
            }
            // prod ^= b << i
            let word = i >> 6;
            let shift = i & 63;
            if shift == 0 {
                prod[word] ^= b[0];
                prod[word + 1] ^= b[1];
            } else {
                prod[word] ^= b[0] << shift;
                prod[word + 1] ^= (b[0] >> (64 - shift)) ^ (b[1] << shift);
                prod[word + 2] ^= b[1] >> (64 - shift);
            }
        }
        // Reduce bits [128..255): for each set high bit h, XOR taps at
        // h-128+{0,1,2,7}. Process high→low.
        for h in (128..255).rev() {
            let word = h >> 6;
            let shift = h & 63;
            if (prod[word] >> shift) & 1 == 0 {
                continue;
            }
            prod[word] ^= 1u64 << shift; // clear
            let base = h - 128;
            for off in [0usize, 1, 2, 7] {
                let t = base + off;
                prod[t >> 6] ^= 1u64 << (t & 63);
            }
        }
        Gf128(prod[0], prod[1])
    }
}
