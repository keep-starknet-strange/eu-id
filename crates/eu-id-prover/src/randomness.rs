use rand::RngCore;
use stwo::core::fields::m31::M31;

/// Sample one uniform M31 value.
pub(crate) fn random_m31(rng: &mut impl RngCore) -> M31 {
    loop {
        let candidate = rng.next_u32() & 0x7fff_ffff;
        if candidate != 0x7fff_ffff {
            return M31::from_u32_unchecked(candidate);
        }
    }
}

/// Sample one uniform bit as an M31 value.
pub(crate) fn random_bit(rng: &mut impl RngCore) -> M31 {
    M31::from_u32_unchecked(rng.next_u32() & 1)
}

#[cfg(test)]
mod tests {
    use rand::rngs::mock::StepRng;
    use stwo::core::fields::m31::M31;

    use super::{random_bit, random_m31};

    #[test]
    fn m31_sampler_rejects_the_modulus() {
        let mut rng = StepRng::new(0x7fff_ffff, u64::MAX);
        assert_eq!(random_m31(&mut rng), M31::from_u32_unchecked(0x7fff_fffe));
    }

    #[test]
    fn bit_sampler_returns_the_low_bit() {
        let mut rng = StepRng::new(2, 1);
        assert_eq!(random_bit(&mut rng), M31::from_u32_unchecked(0));
        assert_eq!(random_bit(&mut rng), M31::from_u32_unchecked(1));
    }
}
