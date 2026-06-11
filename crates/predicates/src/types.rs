use stwo::core::fields::m31::M31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;

pub type Column = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
pub type Trace = Vec<Column>;
