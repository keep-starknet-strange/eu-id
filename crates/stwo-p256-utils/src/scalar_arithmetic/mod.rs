mod carries;
mod error;
mod limbs;
mod mul;
mod mul_split;
mod setup;
mod types;
mod validation;
mod words;

pub use error::ScalarArithmeticError;
pub use limbs::{limbs_to_words, words_to_limbs};
pub use mul::{FnMulTrace, ScalarFieldMulTrace};
pub use mul_split::{
    ProductChunk, SplitProductTrace, CHUNK_DIGITS, CHUNK_TOP_DIGIT_MAX, FNMUL_CHUNK_TERMS,
    PRODUCT_CHUNKS, PRODUCT_COEFFICIENTS,
};
pub use setup::ScalarSetupTrace;
pub use types::{
    BigIntCarries, BigIntLimbs, ProductCarries, U256Words, P256_ORDER, PRODUCT_EQUATION_LIMBS,
};
pub use validation::{require_nonzero, CanonicalLtTrace, DigestReductionTrace};
