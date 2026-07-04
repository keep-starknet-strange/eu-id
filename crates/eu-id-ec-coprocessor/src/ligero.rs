use crate::merkle::{commit_columns, verify_column, ColumnOpening, MerkleCommitment, MerkleError};
use crate::rs::{rs_encode_padded, rs_evaluate, RsError};
use crate::sumcheck::InputClaims;
use crate::{Fp, Mle, MleError};
use serde::{Deserialize, Serialize};
use std::time::{Duration, Instant};

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct LigeroParams {
    pub row_len: usize,
    pub degree_bound: usize,
    pub codeword_len: usize,
    pub openings: usize,
    pub proximity_radius: usize,
}

pub const V1_NON_ZK: bool = true;
pub const V1_MIN_OPENINGS: usize = 156;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LigeroCommitment {
    params: LigeroParams,
    encoded_rows: Vec<Vec<Fp>>,
    merkle: MerkleCommitment,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct LigeroCommitProfile {
    pub row_encode: Duration,
    pub merkle_build: Duration,
    pub rows: usize,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct LigeroProximityClaim {
    pub combined_row: Vec<Fp>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LigeroError {
    EmptyWitness,
    EmptyGamma,
    InvalidRowLength,
    InvalidDegreeBound,
    CodewordTooShort,
    TooManyOpenings,
    ProximityRadiusTooLarge,
    WrongOpeningCount,
    WrongGammaLength,
    WrongClaimLength,
    WrongPointLength,
    ColumnOutOfRange,
    Merkle(MerkleError),
    Rs(RsError),
    Mle(MleError),
}

impl LigeroParams {
    pub fn validate(self) -> Result<(), LigeroError> {
        if self.row_len == 0 {
            return Err(LigeroError::InvalidRowLength);
        }
        if self.degree_bound < self.row_len {
            return Err(LigeroError::InvalidDegreeBound);
        }
        if self.codeword_len <= self.degree_bound {
            return Err(LigeroError::CodewordTooShort);
        }
        if self.openings > self.codeword_len {
            return Err(LigeroError::TooManyOpenings);
        }
        if 2 * self.proximity_radius >= self.codeword_len - self.degree_bound {
            return Err(LigeroError::ProximityRadiusTooLarge);
        }
        if self.codeword_len <= 2 * self.degree_bound + self.proximity_radius {
            return Err(LigeroError::CodewordTooShort);
        }
        Ok(())
    }

    pub fn soundness_error(self) -> f64 {
        let n = self.codeword_len as f64;
        let k = self.degree_bound as f64;
        let ell = self.row_len as f64;
        let t = self.openings as f64;
        let e = self.proximity_radius as f64;
        (1.0 - e / n).powf(t)
            + (2.0 * k / n).powf(t)
            + ((k + ell) / n).powf(t)
            + (n + 3.0) / 2f64.powi(256)
    }
}

pub fn v1_ligero_params() -> LigeroParams {
    // k >= ell + t is required when ZK rows land in v2. The v1 tuple is
    // explicitly non-ZK and keeps only k >= ell, per Q-027.
    debug_assert!(V1_NON_ZK);
    LigeroParams {
        row_len: 64,
        degree_bound: 64,
        codeword_len: 512,
        openings: 160,
        proximity_radius: 223,
    }
}

pub fn commit_witness(
    witness: &[Fp],
    params: LigeroParams,
) -> Result<LigeroCommitment, LigeroError> {
    commit_witness_profiled(witness, params).map(|(commitment, _)| commitment)
}

pub fn commit_witness_profiled(
    witness: &[Fp],
    params: LigeroParams,
) -> Result<(LigeroCommitment, LigeroCommitProfile), LigeroError> {
    params.validate()?;
    if witness.is_empty() {
        return Err(LigeroError::EmptyWitness);
    }

    let row_encode_start = Instant::now();
    let mut encoded_rows = Vec::new();
    for chunk in witness.chunks(params.row_len) {
        encoded_rows.push(
            rs_encode_padded(chunk, params.degree_bound, params.codeword_len)
                .map_err(LigeroError::Rs)?,
        );
    }
    let row_encode = row_encode_start.elapsed();
    let merkle_start = Instant::now();
    let merkle = commit_columns(&encoded_rows).map_err(LigeroError::Merkle)?;
    let merkle_build = merkle_start.elapsed();
    let rows = encoded_rows.len();
    Ok((
        LigeroCommitment {
            params,
            encoded_rows,
            merkle,
        },
        LigeroCommitProfile {
            row_encode,
            merkle_build,
            rows,
        },
    ))
}

impl LigeroCommitment {
    pub fn root(&self) -> [u8; 32] {
        self.merkle.root()
    }

    pub fn open_columns(&self, indices: &[usize]) -> Result<Vec<ColumnOpening>, LigeroError> {
        if indices.len() != self.params.openings {
            return Err(LigeroError::WrongOpeningCount);
        }
        indices
            .iter()
            .map(|&index| self.merkle.open(index).map_err(LigeroError::Merkle))
            .collect()
    }

    pub fn open_systematic_columns(&self) -> Result<Vec<ColumnOpening>, LigeroError> {
        (0..self.params.row_len)
            .map(|index| self.merkle.open(index).map_err(LigeroError::Merkle))
            .collect()
    }

    pub fn proximity_claim(&self, gamma: &[Fp]) -> Result<LigeroProximityClaim, LigeroError> {
        if gamma.is_empty() {
            return Err(LigeroError::EmptyGamma);
        }
        if gamma.len() != self.encoded_rows.len() {
            return Err(LigeroError::WrongGammaLength);
        }

        let mut combined_row = vec![Fp::ZERO; self.params.degree_bound];
        for (coeff, row) in gamma.iter().copied().zip(&self.encoded_rows) {
            for (out, value) in combined_row.iter_mut().zip(row) {
                *out = *out + coeff * *value;
            }
        }
        Ok(LigeroProximityClaim { combined_row })
    }
}

pub fn verify_input_claims_from_systematic_openings(
    root: [u8; 32],
    params: LigeroParams,
    openings: &[ColumnOpening],
    claims: &InputClaims,
) -> Result<bool, LigeroError> {
    let rows = openings
        .first()
        .map(|opening| opening.column.len())
        .ok_or(LigeroError::WrongOpeningCount)?;
    verify_input_claims_from_systematic_openings_with_len(
        root,
        params,
        openings,
        claims,
        rows * params.row_len,
    )
}

pub fn verify_input_claims_from_systematic_openings_with_len(
    root: [u8; 32],
    params: LigeroParams,
    openings: &[ColumnOpening],
    claims: &InputClaims,
    input_len: usize,
) -> Result<bool, LigeroError> {
    verify_input_claims_from_systematic_openings_with_range(
        root, params, openings, claims, 0, input_len,
    )
}

pub fn verify_input_claims_from_systematic_openings_with_range(
    root: [u8; 32],
    params: LigeroParams,
    openings: &[ColumnOpening],
    claims: &InputClaims,
    input_offset: usize,
    input_len: usize,
) -> Result<bool, LigeroError> {
    params.validate()?;
    if openings.len() != params.row_len {
        return Err(LigeroError::WrongOpeningCount);
    }

    let mut sorted = openings.to_vec();
    sorted.sort_by_key(|opening| opening.index);
    for (expected, opening) in sorted.iter().enumerate() {
        if opening.index != expected {
            return Err(LigeroError::ColumnOutOfRange);
        }
        if !verify_column(root, opening).map_err(LigeroError::Merkle)? {
            return Ok(false);
        }
    }

    let rows = sorted
        .first()
        .map(|opening| opening.column.len())
        .ok_or(LigeroError::WrongOpeningCount)?;
    if sorted.iter().any(|opening| opening.column.len() != rows) {
        return Err(LigeroError::WrongGammaLength);
    }
    if input_offset + input_len > rows * params.row_len {
        return Err(LigeroError::WrongPointLength);
    }

    let mut values = Vec::with_capacity(rows * params.row_len);
    for row in 0..rows {
        for opening in &sorted {
            values.push(opening.column[row]);
        }
    }
    let values = values[input_offset..input_offset + input_len].to_vec();
    let mle = Mle::new(values);
    for (point, value) in claims.points.iter().zip(claims.values) {
        if point.len() != mle.num_vars() {
            return Err(LigeroError::WrongPointLength);
        }
        if mle.eval_at(point).map_err(LigeroError::Mle)? != value {
            return Ok(false);
        }
    }
    Ok(true)
}

pub fn verify_openings(
    root: [u8; 32],
    params: LigeroParams,
    openings: &[ColumnOpening],
    claim: &LigeroProximityClaim,
    gamma: &[Fp],
) -> Result<bool, LigeroError> {
    params.validate()?;
    if openings.len() != params.openings {
        return Err(LigeroError::WrongOpeningCount);
    }
    if gamma.is_empty() {
        return Err(LigeroError::EmptyGamma);
    }
    if claim.combined_row.len() != params.degree_bound {
        return Err(LigeroError::WrongClaimLength);
    }
    for opening in openings {
        if opening.index >= params.codeword_len {
            return Err(LigeroError::ColumnOutOfRange);
        }
        if opening.column.len() != gamma.len() {
            return Err(LigeroError::WrongGammaLength);
        }
        if !verify_column(root, opening).map_err(LigeroError::Merkle)? {
            return Ok(false);
        }
        let combined = gamma
            .iter()
            .copied()
            .zip(&opening.column)
            .fold(Fp::ZERO, |acc, (coeff, value)| acc + coeff * *value);
        let expected = rs_evaluate(&claim.combined_row, params.codeword_len, opening.index)
            .map_err(LigeroError::Rs)?;
        if expected != combined {
            return Ok(false);
        }
    }
    Ok(true)
}
