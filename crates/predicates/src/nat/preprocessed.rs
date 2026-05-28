use crate::nat::types::PublicInput;
use crate::types::Trace;
use stwo::core::fields::m31::M31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::Column;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::TreeBuilder;

pub(super) struct Preprocessed {
    pub acceptable: Trace,
}

impl Preprocessed {
    pub fn new(public: &PublicInput) -> Self {
        let log_size = public.log_size();
        let total_size = 1 << log_size;
        let domain = CanonicCoset::new(log_size).circle_domain();

        let mut col = BaseColumn::zeros(total_size);
        for (i, &nat_code) in public.acceptable.iter().enumerate() {
            col.set(i, M31::from_u32_unchecked(nat_code));
        }
        // Padding rows remain 0 — no valid ISO code is 0, so they are never matched.

        Self {
            acceptable: vec![CircleEvaluation::new(domain, col)],
        }
    }

    pub fn extend_evals(&self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        tb.extend_evals(self.acceptable.clone());
    }
}
