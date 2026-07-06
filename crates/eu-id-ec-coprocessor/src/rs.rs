#[cfg(test)]
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::OnceLock;

use crate::Fp;

const V1_DEGREE_BOUND: usize = 64;
const V1_CODEWORD_LEN: usize = 512;
const V2A_ROW_DEGREE_BOUND: usize = 234;
const V2A_CLAIM_DEGREE_BOUND: usize = 297;
const V2A_WEIGHT_DEGREE_BOUND: usize = 64;
const V2A_CODEWORD_LEN: usize = 2048;
const V2B_ROW_DEGREE_BOUND: usize = 289;
const V2B_CLAIM_DEGREE_BOUND: usize = 352;
const V2B_WEIGHT_DEGREE_BOUND: usize = 64;
const V2B_CODEWORD_LEN: usize = 1024;

static V1_ENCODER: OnceLock<RsEncoder> = OnceLock::new();
static V2A_ROW_ENCODER: OnceLock<RsEncoder> = OnceLock::new();
static V2A_CLAIM_ENCODER: OnceLock<RsEncoder> = OnceLock::new();
static V2A_WEIGHT_ENCODER: OnceLock<RsEncoder> = OnceLock::new();
static V2B_ROW_ENCODER: OnceLock<RsEncoder> = OnceLock::new();
static V2B_CLAIM_ENCODER: OnceLock<RsEncoder> = OnceLock::new();
static V2B_WEIGHT_ENCODER: OnceLock<RsEncoder> = OnceLock::new();
#[cfg(test)]
static RS_ENCODE_PADDED_CALLS: AtomicUsize = AtomicUsize::new(0);
#[cfg(test)]
static RS_ENCODE_PADDED_CACHED_CALLS: AtomicUsize = AtomicUsize::new(0);
#[cfg(test)]
static RS_ENCODE_PADDED_V2A_ROW_CACHED_CALLS: AtomicUsize = AtomicUsize::new(0);
#[cfg(test)]
static RS_ENCODE_PADDED_V2A_CLAIM_CACHED_CALLS: AtomicUsize = AtomicUsize::new(0);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RsError {
    EmptyMessage,
    WrongMessageLength,
    CodewordTooShort,
    IndexOutOfRange,
}

pub fn rs_encode(message: &[Fp], codeword_len: usize) -> Result<Vec<Fp>, RsError> {
    if let Some(encoder) = cached_encoder(message.len(), codeword_len) {
        return Ok(encoder.encode(message).expect("length checked"));
    }
    RsEncoder::new(message.len(), codeword_len)?.encode(message)
}

pub fn rs_encode_padded(
    message_prefix: &[Fp],
    message_len: usize,
    codeword_len: usize,
) -> Result<Vec<Fp>, RsError> {
    #[cfg(test)]
    RS_ENCODE_PADDED_CALLS.fetch_add(1, Ordering::Relaxed);
    if let Some(encoder) = cached_encoder(message_len, codeword_len) {
        #[cfg(test)]
        record_cached_encoder_hit(message_len, codeword_len);
        return encoder.encode_padded(message_prefix);
    }
    RsEncoder::new(message_len, codeword_len)?.encode_padded(message_prefix)
}

#[cfg(test)]
fn record_cached_encoder_hit(message_len: usize, codeword_len: usize) {
    RS_ENCODE_PADDED_CACHED_CALLS.fetch_add(1, Ordering::Relaxed);
    match (message_len, codeword_len) {
        (V2A_ROW_DEGREE_BOUND, V2A_CODEWORD_LEN) => {
            RS_ENCODE_PADDED_V2A_ROW_CACHED_CALLS.fetch_add(1, Ordering::Relaxed);
        }
        (V2A_CLAIM_DEGREE_BOUND, V2A_CODEWORD_LEN) => {
            RS_ENCODE_PADDED_V2A_CLAIM_CACHED_CALLS.fetch_add(1, Ordering::Relaxed);
        }
        _ => {}
    }
}

#[cfg(test)]
pub(crate) fn reset_rs_encode_padded_call_count() {
    RS_ENCODE_PADDED_CALLS.store(0, Ordering::Relaxed);
    RS_ENCODE_PADDED_CACHED_CALLS.store(0, Ordering::Relaxed);
    RS_ENCODE_PADDED_V2A_ROW_CACHED_CALLS.store(0, Ordering::Relaxed);
    RS_ENCODE_PADDED_V2A_CLAIM_CACHED_CALLS.store(0, Ordering::Relaxed);
}

#[cfg(test)]
pub(crate) fn rs_encode_padded_call_count() -> usize {
    RS_ENCODE_PADDED_CALLS.load(Ordering::Relaxed)
}

#[cfg(test)]
pub(crate) fn rs_encode_padded_v2a_cached_call_counts() -> (usize, usize) {
    (
        RS_ENCODE_PADDED_V2A_ROW_CACHED_CALLS.load(Ordering::Relaxed),
        RS_ENCODE_PADDED_V2A_CLAIM_CACHED_CALLS.load(Ordering::Relaxed),
    )
}

pub fn is_codeword(codeword: &[Fp], message_len: usize) -> Result<bool, RsError> {
    if message_len == 0 {
        return Err(RsError::EmptyMessage);
    }
    if codeword.len() < message_len {
        return Err(RsError::CodewordTooShort);
    }
    Ok(rs_encode(&codeword[..message_len], codeword.len())? == codeword)
}

pub fn rs_evaluate(message: &[Fp], codeword_len: usize, index: usize) -> Result<Fp, RsError> {
    if let Some(encoder) = cached_encoder(message.len(), codeword_len) {
        return encoder.evaluate(message, index);
    }
    RsEncoder::new(message.len(), codeword_len)?.evaluate(message, index)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RsEncoder {
    message_len: usize,
    codeword_len: usize,
    extension_coefficients: Vec<Vec<Fp>>,
}

fn v1_encoder() -> &'static RsEncoder {
    V1_ENCODER.get_or_init(|| {
        RsEncoder::new(V1_DEGREE_BOUND, V1_CODEWORD_LEN).expect("static v1 RS params are valid")
    })
}

fn cached_encoder(message_len: usize, codeword_len: usize) -> Option<&'static RsEncoder> {
    match (message_len, codeword_len) {
        (V1_DEGREE_BOUND, V1_CODEWORD_LEN) => Some(v1_encoder()),
        (V2A_ROW_DEGREE_BOUND, V2A_CODEWORD_LEN) => Some(V2A_ROW_ENCODER.get_or_init(|| {
            RsEncoder::new(V2A_ROW_DEGREE_BOUND, V2A_CODEWORD_LEN)
                .expect("static v2 A row RS params are valid")
        })),
        (V2A_CLAIM_DEGREE_BOUND, V2A_CODEWORD_LEN) => Some(V2A_CLAIM_ENCODER.get_or_init(|| {
            RsEncoder::new(V2A_CLAIM_DEGREE_BOUND, V2A_CODEWORD_LEN)
                .expect("static v2 A claim RS params are valid")
        })),
        (V2A_WEIGHT_DEGREE_BOUND, V2A_CODEWORD_LEN) => Some(V2A_WEIGHT_ENCODER.get_or_init(|| {
            RsEncoder::new(V2A_WEIGHT_DEGREE_BOUND, V2A_CODEWORD_LEN)
                .expect("static v2 A weight RS params are valid")
        })),
        (V2B_ROW_DEGREE_BOUND, V2B_CODEWORD_LEN) => Some(V2B_ROW_ENCODER.get_or_init(|| {
            RsEncoder::new(V2B_ROW_DEGREE_BOUND, V2B_CODEWORD_LEN)
                .expect("static v2 B row RS params are valid")
        })),
        (V2B_CLAIM_DEGREE_BOUND, V2B_CODEWORD_LEN) => Some(V2B_CLAIM_ENCODER.get_or_init(|| {
            RsEncoder::new(V2B_CLAIM_DEGREE_BOUND, V2B_CODEWORD_LEN)
                .expect("static v2 B claim RS params are valid")
        })),
        (V2B_WEIGHT_DEGREE_BOUND, V2B_CODEWORD_LEN) => Some(V2B_WEIGHT_ENCODER.get_or_init(|| {
            RsEncoder::new(V2B_WEIGHT_DEGREE_BOUND, V2B_CODEWORD_LEN)
                .expect("static v2 B weight RS params are valid")
        })),
        _ => None,
    }
}

impl RsEncoder {
    pub fn new(message_len: usize, codeword_len: usize) -> Result<Self, RsError> {
        if message_len == 0 {
            return Err(RsError::EmptyMessage);
        }
        if codeword_len < message_len {
            return Err(RsError::CodewordTooShort);
        }

        let weights = lagrange_weights(message_len);
        let extension_coefficients = (message_len..codeword_len)
            .map(|x| extension_coefficients(message_len, &weights, Fp::from_u64(x as u64)))
            .collect();

        Ok(Self {
            message_len,
            codeword_len,
            extension_coefficients,
        })
    }

    pub fn encode(&self, message: &[Fp]) -> Result<Vec<Fp>, RsError> {
        if message.len() != self.message_len {
            return Err(RsError::WrongMessageLength);
        }
        self.encode_padded(message)
    }

    pub fn encode_padded(&self, message_prefix: &[Fp]) -> Result<Vec<Fp>, RsError> {
        if message_prefix.len() > self.message_len {
            return Err(RsError::WrongMessageLength);
        }
        let mut message = Vec::with_capacity(self.message_len);
        message.extend_from_slice(message_prefix);
        message.resize(self.message_len, Fp::ZERO);
        Ok(equispaced_codeword(message, self.codeword_len))
    }

    pub fn evaluate(&self, message: &[Fp], index: usize) -> Result<Fp, RsError> {
        if message.len() != self.message_len {
            return Err(RsError::WrongMessageLength);
        }
        if index >= self.codeword_len {
            return Err(RsError::IndexOutOfRange);
        }
        if index < self.message_len {
            return Ok(message[index]);
        }
        Ok(message
            .iter()
            .copied()
            .zip(
                self.extension_coefficients[index - self.message_len]
                    .iter()
                    .copied(),
            )
            .fold(Fp::ZERO, |acc, (value, coeff)| acc + value * coeff))
    }
}

fn equispaced_codeword(mut values: Vec<Fp>, codeword_len: usize) -> Vec<Fp> {
    debug_assert!(!values.is_empty());
    debug_assert!(codeword_len >= values.len());
    if values.len() == codeword_len {
        return values;
    }

    let mut tail_diffs = tail_differences(&values);

    while values.len() < codeword_len {
        advance_tail_differences_one(&mut tail_diffs);
        values.push(tail_diffs[0]);
    }
    values
}

fn tail_differences(values: &[Fp]) -> Vec<Fp> {
    let mut diffs = values.to_vec();
    let mut tail_diffs = Vec::with_capacity(diffs.len());
    tail_diffs.push(*diffs.last().expect("non-empty"));
    for level in 1..diffs.len() {
        for index in 0..diffs.len() - level {
            diffs[index] = diffs[index + 1] - diffs[index];
        }
        tail_diffs.push(diffs[diffs.len() - level - 1]);
    }
    tail_diffs
}

fn advance_tail_differences_one(tail_diffs: &mut [Fp]) {
    for level in (1..tail_diffs.len()).rev() {
        tail_diffs[level - 1] = tail_diffs[level - 1] + tail_diffs[level];
    }
}

fn lagrange_weights(len: usize) -> Vec<Fp> {
    let denominators = (0..len)
        .map(|i| {
            let x_i = Fp::from_u64(i as u64);
            (0..len)
                .filter(|&j| j != i)
                .fold(Fp::ONE, |acc, j| acc * (x_i - Fp::from_u64(j as u64)))
        })
        .collect::<Vec<_>>();
    Fp::batch_inverse(&denominators)
}

fn extension_coefficients(message_len: usize, weights: &[Fp], x: Fp) -> Vec<Fp> {
    let offsets = (0..message_len)
        .map(|i| x - Fp::from_u64(i as u64))
        .collect::<Vec<_>>();
    let numerator = offsets.iter().copied().fold(Fp::ONE, |acc, v| acc * v);
    let offset_inverses = Fp::batch_inverse(&offsets);

    weights
        .iter()
        .copied()
        .zip(offset_inverses)
        .map(|(weight, offset_inverse)| numerator * offset_inverse * weight)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reusable_encoder_matches_one_shot_encoding_for_multiple_rows() {
        let encoder = RsEncoder::new(8, 16).unwrap();
        let rows = [
            (0u64..8).map(Fp::from_u64).collect::<Vec<_>>(),
            (10u64..18).map(Fp::from_u64).collect::<Vec<_>>(),
        ];

        for row in rows {
            assert_eq!(encoder.encode(&row).unwrap(), rs_encode(&row, 16).unwrap());
        }
    }

    #[test]
    fn reusable_encoder_evaluates_encoded_positions() {
        let encoder = RsEncoder::new(8, 16).unwrap();
        let row = (3u64..11).map(Fp::from_u64).collect::<Vec<_>>();
        let encoded = encoder.encode(&row).unwrap();

        for (index, expected) in encoded.into_iter().enumerate() {
            assert_eq!(encoder.evaluate(&row, index).unwrap(), expected);
        }
    }

    #[test]
    fn padded_encoder_matches_full_zero_padded_message() {
        let encoder = RsEncoder::new(8, 16).unwrap();
        let prefix = (3u64..7).map(Fp::from_u64).collect::<Vec<_>>();
        let mut padded = prefix.clone();
        padded.resize(8, Fp::ZERO);

        assert_eq!(
            encoder.encode_padded(&prefix).unwrap(),
            encoder.encode(&padded).unwrap()
        );
    }

    #[test]
    fn v1_row64_encoder_matches_dense_zero_padded_codeword() {
        let prefix = (10u64..74).map(Fp::from_u64).collect::<Vec<_>>();
        let mut padded = prefix.clone();
        padded.resize(V1_DEGREE_BOUND, Fp::ZERO);

        assert_eq!(
            rs_encode_padded(&prefix, V1_DEGREE_BOUND, V1_CODEWORD_LEN).unwrap(),
            equispaced_codeword(padded, V1_CODEWORD_LEN)
        );
    }
}
