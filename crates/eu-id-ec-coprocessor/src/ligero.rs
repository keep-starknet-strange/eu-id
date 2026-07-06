use crate::merkle::{commit_columns, verify_column, ColumnOpening, MerkleCommitment, MerkleError};
use crate::rs::{rs_encode_padded, rs_evaluate, RsError};
use crate::sumcheck::InputClaims;
use crate::{CoprocessorChannel, Fp, Mle, MleError};
use p256::elliptic_curve::rand_core::{OsRng, RngCore};
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

pub const V1_MIN_OPENINGS: usize = 156;
pub const V2_ZK_OPENINGS: bool = true;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LigeroCommitment {
    params: LigeroParams,
    witness_rows: usize,
    proximity_mask_row: usize,
    claim_blind_row: usize,
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

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct LigeroLinearClaim {
    pub offset: usize,
    pub len: usize,
    pub point: Vec<Fp>,
    pub value: Fp,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct LigeroClaimBatch {
    pub coefficients: Vec<Fp>,
    pub blind_claim: Fp,
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
        if self.degree_bound < self.row_len + self.openings {
            return Err(LigeroError::InvalidDegreeBound);
        }
        if self.codeword_len <= self.degree_bound {
            return Err(LigeroError::CodewordTooShort);
        }
        if self.openings > self.codeword_len {
            return Err(LigeroError::TooManyOpenings);
        }
        if 2 * self.proximity_radius >= self.codeword_len - self.claim_degree_bound() {
            return Err(LigeroError::ProximityRadiusTooLarge);
        }
        if self.codeword_len <= 2 * self.degree_bound + self.proximity_radius {
            return Err(LigeroError::CodewordTooShort);
        }
        Ok(())
    }

    pub fn claim_degree_bound(self) -> usize {
        self.degree_bound + self.row_len - 1
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
    LigeroParams {
        row_len: 64,
        degree_bound: 64,
        codeword_len: 512,
        openings: 160,
        proximity_radius: 223,
    }
}

pub fn v2_ligero_params() -> LigeroParams {
    LigeroParams {
        row_len: 64,
        degree_bound: 234,
        codeword_len: 2048,
        openings: 170,
        proximity_radius: 875,
    }
}

pub fn v2_ligero_params_b() -> LigeroParams {
    LigeroParams {
        row_len: 64,
        degree_bound: 289,
        codeword_len: 1024,
        openings: 225,
        proximity_radius: 335,
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
    let mut pads = fresh_pad_channel();
    for chunk in witness.chunks(params.row_len) {
        let mut row = Vec::with_capacity(params.degree_bound);
        row.extend_from_slice(chunk);
        row.resize(params.row_len, Fp::ZERO);
        while row.len() < params.degree_bound {
            row.push(pads.draw_fp());
        }
        encoded_rows.push(
            rs_encode_padded(&row, params.degree_bound, params.codeword_len)
                .map_err(LigeroError::Rs)?,
        );
    }
    let witness_rows = encoded_rows.len();
    let mut mask_row = Vec::with_capacity(params.degree_bound);
    while mask_row.len() < params.degree_bound {
        mask_row.push(pads.draw_fp());
    }
    let proximity_mask_row = encoded_rows.len();
    encoded_rows.push(
        rs_encode_padded(&mask_row, params.degree_bound, params.codeword_len)
            .map_err(LigeroError::Rs)?,
    );
    let claim_degree_bound = params.claim_degree_bound();
    let mut blind_row = Vec::with_capacity(claim_degree_bound);
    while blind_row.len() < claim_degree_bound {
        blind_row.push(pads.draw_fp());
    }
    let claim_blind_row = encoded_rows.len();
    encoded_rows.push(
        rs_encode_padded(&blind_row, claim_degree_bound, params.codeword_len)
            .map_err(LigeroError::Rs)?,
    );
    let row_encode = row_encode_start.elapsed();
    let merkle_start = Instant::now();
    let merkle = commit_columns(&encoded_rows).map_err(LigeroError::Merkle)?;
    let merkle_build = merkle_start.elapsed();
    let rows = encoded_rows.len();
    Ok((
        LigeroCommitment {
            params,
            witness_rows,
            proximity_mask_row,
            claim_blind_row,
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
        if gamma.len() != self.witness_rows {
            return Err(LigeroError::WrongGammaLength);
        }

        let mask_row = &self.encoded_rows[self.proximity_mask_row];
        let mut combined_row = mask_row[..self.params.degree_bound].to_vec();
        for (coeff, row) in gamma
            .iter()
            .copied()
            .zip(&self.encoded_rows[..self.witness_rows])
        {
            for (out, value) in combined_row.iter_mut().zip(row) {
                *out = *out + coeff * *value;
            }
        }
        Ok(LigeroProximityClaim { combined_row })
    }

    pub fn split_proximity_claim(
        &self,
        other: &Self,
        gamma: &[Fp],
    ) -> Result<LigeroProximityClaim, LigeroError> {
        if self.params != other.params {
            return Err(LigeroError::InvalidRowLength);
        }
        if gamma.is_empty() {
            return Err(LigeroError::EmptyGamma);
        }
        if gamma.len() != self.witness_rows + other.witness_rows {
            return Err(LigeroError::WrongGammaLength);
        }

        let mask_a = &self.encoded_rows[self.proximity_mask_row];
        let mask_b = &other.encoded_rows[other.proximity_mask_row];
        let mut combined_row = mask_a[..self.params.degree_bound].to_vec();
        for (out, value) in combined_row
            .iter_mut()
            .zip(&mask_b[..other.params.degree_bound])
        {
            *out = *out + *value;
        }
        for (coeff, row) in gamma[..self.witness_rows]
            .iter()
            .copied()
            .zip(&self.encoded_rows[..self.witness_rows])
        {
            for (out, value) in combined_row.iter_mut().zip(row) {
                *out = *out + coeff * *value;
            }
        }
        for (coeff, row) in gamma[self.witness_rows..]
            .iter()
            .copied()
            .zip(&other.encoded_rows[..other.witness_rows])
        {
            for (out, value) in combined_row.iter_mut().zip(row) {
                *out = *out + coeff * *value;
            }
        }
        Ok(LigeroProximityClaim { combined_row })
    }

    pub fn claim_batch(
        &self,
        claims: &[LigeroLinearClaim],
        gamma: &[Fp],
    ) -> Result<LigeroClaimBatch, LigeroError> {
        if claims.is_empty() || gamma.is_empty() {
            return Err(LigeroError::EmptyGamma);
        }
        if claims.len() != gamma.len() {
            return Err(LigeroError::WrongGammaLength);
        }
        let claim_degree_bound = self.params.claim_degree_bound();
        let blind_row = &self.encoded_rows[self.claim_blind_row];
        let mut coefficients = blind_row[..claim_degree_bound].to_vec();

        for (row, weights) in batched_row_weights(self.params, self.witness_rows, claims, gamma)? {
            let weight_evals = weight_evaluations(self.params, &weights, 0..claim_degree_bound)?;
            for x in 0..claim_degree_bound {
                let row_value = self.encoded_rows[row][x];
                coefficients[x] = coefficients[x] + weight_evals[x] * row_value;
            }
        }

        let blind_claim = blind_row[..self.params.row_len]
            .iter()
            .copied()
            .fold(Fp::ZERO, |acc, value| acc + value);
        Ok(LigeroClaimBatch {
            coefficients,
            blind_claim,
        })
    }

    pub fn split_claim_batch(
        &self,
        other: &Self,
        claims: &[LigeroLinearClaim],
        gamma: &[Fp],
    ) -> Result<LigeroClaimBatch, LigeroError> {
        if self.params != other.params {
            return Err(LigeroError::InvalidRowLength);
        }
        if claims.is_empty() || gamma.is_empty() {
            return Err(LigeroError::EmptyGamma);
        }
        if claims.len() != gamma.len() {
            return Err(LigeroError::WrongGammaLength);
        }
        let claim_degree_bound = self.params.claim_degree_bound();
        let blind_a = &self.encoded_rows[self.claim_blind_row];
        let blind_b = &other.encoded_rows[other.claim_blind_row];
        let mut coefficients = blind_a[..claim_degree_bound].to_vec();
        for (out, value) in coefficients.iter_mut().zip(&blind_b[..claim_degree_bound]) {
            *out = *out + *value;
        }

        let combined_rows = self.witness_rows + other.witness_rows;
        for (row, weights) in batched_row_weights(self.params, combined_rows, claims, gamma)? {
            let weight_evals = weight_evaluations(self.params, &weights, 0..claim_degree_bound)?;
            let encoded_row = if row < self.witness_rows {
                &self.encoded_rows[row]
            } else {
                &other.encoded_rows[row - self.witness_rows]
            };
            for x in 0..claim_degree_bound {
                coefficients[x] = coefficients[x] + weight_evals[x] * encoded_row[x];
            }
        }

        let blind_claim = blind_a[..self.params.row_len]
            .iter()
            .chain(&blind_b[..self.params.row_len])
            .copied()
            .fold(Fp::ZERO, |acc, value| acc + value);
        Ok(LigeroClaimBatch {
            coefficients,
            blind_claim,
        })
    }
}

pub fn verify_split_openings(
    root_a: [u8; 32],
    root_b: [u8; 32],
    params: LigeroParams,
    committed_len_a: usize,
    committed_len_b: usize,
    openings_a: &[ColumnOpening],
    openings_b: &[ColumnOpening],
    claim: &LigeroProximityClaim,
    gamma: &[Fp],
) -> Result<bool, LigeroError> {
    params.validate()?;
    if openings_a.len() != params.openings || openings_b.len() != params.openings {
        return Err(LigeroError::WrongOpeningCount);
    }
    if openings_a.len() != openings_b.len() {
        return Err(LigeroError::WrongOpeningCount);
    }
    if gamma.is_empty() {
        return Err(LigeroError::EmptyGamma);
    }
    if claim.combined_row.len() != params.degree_bound {
        return Err(LigeroError::WrongClaimLength);
    }
    let rows_a = committed_len_a.div_ceil(params.row_len);
    let rows_b = committed_len_b.div_ceil(params.row_len);
    if gamma.len() != rows_a + rows_b {
        return Err(LigeroError::WrongGammaLength);
    }

    for (opening_a, opening_b) in openings_a.iter().zip(openings_b) {
        if opening_a.index != opening_b.index {
            return Err(LigeroError::ColumnOutOfRange);
        }
        if opening_a.index >= params.codeword_len {
            return Err(LigeroError::ColumnOutOfRange);
        }
        if opening_a.column.len() != rows_a + 2 || opening_b.column.len() != rows_b + 2 {
            return Err(LigeroError::WrongGammaLength);
        }
        if !verify_column(root_a, opening_a).map_err(LigeroError::Merkle)?
            || !verify_column(root_b, opening_b).map_err(LigeroError::Merkle)?
        {
            return Ok(false);
        }
        let mask_value = opening_a.column[rows_a] + opening_b.column[rows_b];
        let combined_a = gamma[..rows_a]
            .iter()
            .copied()
            .zip(&opening_a.column[..rows_a])
            .fold(mask_value, |acc, (coeff, value)| acc + coeff * *value);
        let combined = gamma[rows_a..]
            .iter()
            .copied()
            .zip(&opening_b.column[..rows_b])
            .fold(combined_a, |acc, (coeff, value)| acc + coeff * *value);
        let expected = rs_evaluate(&claim.combined_row, params.codeword_len, opening_a.index)
            .map_err(LigeroError::Rs)?;
        if expected != combined {
            return Ok(false);
        }
    }
    Ok(true)
}

pub fn verify_split_claim_batch(
    root_a: [u8; 32],
    root_b: [u8; 32],
    params: LigeroParams,
    committed_len_a: usize,
    committed_len_b: usize,
    openings_a: &[ColumnOpening],
    openings_b: &[ColumnOpening],
    batch: &LigeroClaimBatch,
    claims: &[LigeroLinearClaim],
    gamma: &[Fp],
) -> Result<bool, LigeroError> {
    params.validate()?;
    if openings_a.len() != params.openings || openings_b.len() != params.openings {
        return Err(LigeroError::WrongOpeningCount);
    }
    if openings_a.len() != openings_b.len() {
        return Err(LigeroError::WrongOpeningCount);
    }
    if claims.is_empty() || gamma.is_empty() {
        return Err(LigeroError::EmptyGamma);
    }
    if claims.len() != gamma.len() {
        return Err(LigeroError::WrongGammaLength);
    }
    let claim_degree_bound = params.claim_degree_bound();
    if batch.coefficients.len() != claim_degree_bound {
        return Err(LigeroError::WrongClaimLength);
    }
    let rows_a = committed_len_a.div_ceil(params.row_len);
    let rows_b = committed_len_b.div_ceil(params.row_len);
    let combined_rows = rows_a + rows_b;
    let batched_row_weights = batched_row_weights(params, combined_rows, claims, gamma)?;
    let opening_indices = openings_a
        .iter()
        .map(|opening| opening.index)
        .collect::<Vec<_>>();
    let row_weights_at_openings = batched_row_weights
        .iter()
        .map(|(row, weights)| {
            Ok::<_, LigeroError>((
                *row,
                weight_evaluations(params, weights, opening_indices.iter().copied())?,
            ))
        })
        .collect::<Result<Vec<_>, _>>()?;

    for (opening_position, (opening_a, opening_b)) in openings_a.iter().zip(openings_b).enumerate()
    {
        if opening_a.index != opening_b.index {
            return Err(LigeroError::ColumnOutOfRange);
        }
        if opening_a.index >= params.codeword_len {
            return Err(LigeroError::ColumnOutOfRange);
        }
        if opening_a.column.len() != rows_a + 2 || opening_b.column.len() != rows_b + 2 {
            return Err(LigeroError::WrongGammaLength);
        }
        if !verify_column(root_a, opening_a).map_err(LigeroError::Merkle)?
            || !verify_column(root_b, opening_b).map_err(LigeroError::Merkle)?
        {
            return Ok(false);
        }
        let blind_value = opening_a.column[rows_a + 1] + opening_b.column[rows_b + 1];
        let mut combined = blind_value;
        for (row, weights_at_openings) in &row_weights_at_openings {
            let value = if *row < rows_a {
                opening_a.column[*row]
            } else {
                opening_b.column[*row - rows_a]
            };
            combined = combined + weights_at_openings[opening_position] * value;
        }
        let expected = rs_evaluate(&batch.coefficients, params.codeword_len, opening_a.index)
            .map_err(LigeroError::Rs)?;
        if expected != combined {
            return Ok(false);
        }
    }

    let q_sum = batch.coefficients[..params.row_len]
        .iter()
        .copied()
        .fold(Fp::ZERO, |acc, value| acc + value);
    let claim_sum = claims
        .iter()
        .zip(gamma.iter().copied())
        .fold(batch.blind_claim, |acc, (claim, coeff)| {
            acc + coeff * claim.value
        });
    Ok(q_sum == claim_sum)
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

fn fresh_pad_channel() -> CoprocessorChannel {
    let mut seed = [0u8; 32];
    OsRng.fill_bytes(&mut seed);
    CoprocessorChannel::from_seed(seed, b"eu-id-s4-ligero-v2-pad")
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
        if opening.column.len() != gamma.len() + 2 {
            return Err(LigeroError::WrongGammaLength);
        }
        if !verify_column(root, opening).map_err(LigeroError::Merkle)? {
            return Ok(false);
        }
        let mask_value = opening.column[gamma.len()];
        let combined = gamma
            .iter()
            .copied()
            .zip(&opening.column)
            .fold(mask_value, |acc, (coeff, value)| acc + coeff * *value);
        let expected = rs_evaluate(&claim.combined_row, params.codeword_len, opening.index)
            .map_err(LigeroError::Rs)?;
        if expected != combined {
            return Ok(false);
        }
    }
    Ok(true)
}

pub fn verify_claim_batch(
    root: [u8; 32],
    params: LigeroParams,
    committed_len: usize,
    openings: &[ColumnOpening],
    batch: &LigeroClaimBatch,
    claims: &[LigeroLinearClaim],
    gamma: &[Fp],
) -> Result<bool, LigeroError> {
    params.validate()?;
    if openings.len() != params.openings {
        return Err(LigeroError::WrongOpeningCount);
    }
    if claims.is_empty() || gamma.is_empty() {
        return Err(LigeroError::EmptyGamma);
    }
    if claims.len() != gamma.len() {
        return Err(LigeroError::WrongGammaLength);
    }
    let claim_degree_bound = params.claim_degree_bound();
    if batch.coefficients.len() != claim_degree_bound {
        return Err(LigeroError::WrongClaimLength);
    }
    let committed_rows = committed_len.div_ceil(params.row_len);
    let expected_rows = committed_rows + 2;
    let batched_row_weights = batched_row_weights(params, committed_rows, claims, gamma)?;
    for opening in openings {
        if opening.index >= params.codeword_len {
            return Err(LigeroError::ColumnOutOfRange);
        }
        if opening.column.len() != expected_rows {
            return Err(LigeroError::WrongGammaLength);
        }
    }
    let opening_indices = openings
        .iter()
        .map(|opening| opening.index)
        .collect::<Vec<_>>();
    let row_weights_at_openings = batched_row_weights
        .iter()
        .map(|(row, weights)| {
            Ok::<_, LigeroError>((
                *row,
                weight_evaluations(params, weights, opening_indices.iter().copied())?,
            ))
        })
        .collect::<Result<Vec<_>, _>>()?;

    for (opening_position, opening) in openings.iter().enumerate() {
        if opening.index >= params.codeword_len {
            return Err(LigeroError::ColumnOutOfRange);
        }
        if opening.column.len() != expected_rows {
            return Err(LigeroError::WrongGammaLength);
        }
        if !verify_column(root, opening).map_err(LigeroError::Merkle)? {
            return Ok(false);
        }
        let blind_value = opening.column[committed_rows + 1];
        let mut combined = blind_value;
        for (row, weights_at_openings) in &row_weights_at_openings {
            combined = combined + weights_at_openings[opening_position] * opening.column[*row];
        }
        let expected = rs_evaluate(&batch.coefficients, params.codeword_len, opening.index)
            .map_err(LigeroError::Rs)?;
        if expected != combined {
            return Ok(false);
        }
    }

    let q_sum = batch.coefficients[..params.row_len]
        .iter()
        .copied()
        .fold(Fp::ZERO, |acc, value| acc + value);
    let claim_sum = claims
        .iter()
        .zip(gamma.iter().copied())
        .fold(batch.blind_claim, |acc, (claim, coeff)| {
            acc + coeff * claim.value
        });
    Ok(q_sum == claim_sum)
}

fn validate_linear_claim(
    params: LigeroParams,
    committed_rows: usize,
    claim: &LigeroLinearClaim,
) -> Result<(), LigeroError> {
    if claim.len == 0 {
        return Err(LigeroError::WrongPointLength);
    }
    let expected_point_len = claim.len.next_power_of_two().ilog2() as usize;
    if claim.point.len() != expected_point_len {
        return Err(LigeroError::WrongPointLength);
    }
    if claim.offset + claim.len > committed_rows * params.row_len {
        return Err(LigeroError::WrongPointLength);
    }
    Ok(())
}

#[cfg(test)]
fn row_weight_values(params: LigeroParams, claim: &LigeroLinearClaim, row: usize) -> Vec<Fp> {
    (0..params.row_len)
        .map(|column| {
            let global = row * params.row_len + column;
            linear_claim_weight(claim, global)
        })
        .collect()
}

fn batched_row_weights(
    params: LigeroParams,
    committed_rows: usize,
    claims: &[LigeroLinearClaim],
    gamma: &[Fp],
) -> Result<Vec<(usize, Vec<Fp>)>, LigeroError> {
    if claims.is_empty() || gamma.is_empty() {
        return Err(LigeroError::EmptyGamma);
    }
    if claims.len() != gamma.len() {
        return Err(LigeroError::WrongGammaLength);
    }

    let mut rows = vec![vec![Fp::ZERO; params.row_len]; committed_rows];
    for (claim, coeff) in claims.iter().zip(gamma.iter().copied()) {
        validate_linear_claim(params, committed_rows, claim)?;
        let start = claim.offset / params.row_len;
        let end = (claim.offset + claim.len).div_ceil(params.row_len);
        for (row, weights) in rows.iter_mut().enumerate().take(end).skip(start) {
            for (column, out) in weights.iter_mut().enumerate() {
                let global = row * params.row_len + column;
                *out = *out + coeff * linear_claim_weight(claim, global);
            }
        }
    }

    Ok(rows
        .into_iter()
        .enumerate()
        .filter(|(_, weights)| weights.iter().any(|&weight| weight != Fp::ZERO))
        .collect())
}

fn weight_evaluations(
    params: LigeroParams,
    weights: &[Fp],
    indices: impl IntoIterator<Item = usize>,
) -> Result<Vec<Fp>, LigeroError> {
    indices
        .into_iter()
        .map(|index| rs_evaluate(weights, params.codeword_len, index).map_err(LigeroError::Rs))
        .collect()
}

fn linear_claim_weight(claim: &LigeroLinearClaim, global_index: usize) -> Fp {
    if global_index < claim.offset || global_index >= claim.offset + claim.len {
        return Fp::ZERO;
    }
    let local = global_index - claim.offset;
    claim
        .point
        .iter()
        .enumerate()
        .fold(Fp::ONE, |acc, (bit, &challenge)| {
            if ((local >> bit) & 1) == 1 {
                acc * challenge
            } else {
                acc * (Fp::ONE - challenge)
            }
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rs::{
        reset_rs_encode_padded_call_count, rs_encode_padded_call_count,
        rs_encode_padded_v2a_cached_call_counts,
    };
    use std::sync::Mutex;

    static RS_COUNTER_TEST_LOCK: Mutex<()> = Mutex::new(());

    fn small_params() -> LigeroParams {
        LigeroParams {
            row_len: 4,
            degree_bound: 8,
            codeword_len: 32,
            openings: 3,
            proximity_radius: 1,
        }
    }

    fn claim_for(values: &[Fp], offset: usize, point: Vec<Fp>) -> LigeroLinearClaim {
        let len = 1usize << point.len();
        let value = Mle::new(values[offset..offset + len].to_vec())
            .eval_at(&point)
            .unwrap();
        LigeroLinearClaim {
            offset,
            len,
            point,
            value,
        }
    }

    #[test]
    fn batched_row_weights_match_separate_claim_weights() {
        let params = small_params();
        let claims = vec![
            LigeroLinearClaim {
                offset: 0,
                len: 8,
                point: vec![Fp::from_u64(3), Fp::from_u64(5), Fp::from_u64(7)],
                value: Fp::ZERO,
            },
            LigeroLinearClaim {
                offset: 4,
                len: 4,
                point: vec![Fp::from_u64(11), Fp::from_u64(13)],
                value: Fp::ZERO,
            },
        ];
        let gamma = [Fp::from_u64(17), Fp::from_u64(19)];

        let batched = batched_row_weights(params, 3, &claims, &gamma).unwrap();

        for (row, weights) in batched {
            let mut expected = vec![Fp::ZERO; params.row_len];
            for (claim, coeff) in claims.iter().zip(gamma) {
                for (out, weight) in expected
                    .iter_mut()
                    .zip(row_weight_values(params, claim, row))
                {
                    *out = *out + coeff * weight;
                }
            }
            assert_eq!(weights, expected);
        }
    }

    #[test]
    fn verifier_claim_batch_does_not_rs_encode() {
        let _lock = RS_COUNTER_TEST_LOCK.lock().unwrap();
        let params = small_params();
        let values = (0..12)
            .map(|value| Fp::from_u64(value + 1))
            .collect::<Vec<_>>();
        let claims = vec![
            claim_for(&values, 0, vec![Fp::from_u64(3), Fp::from_u64(5)]),
            claim_for(&values, 4, vec![Fp::from_u64(7), Fp::from_u64(11)]),
        ];
        let gamma = [Fp::from_u64(13), Fp::from_u64(17)];
        let (commitment, _) = commit_witness_profiled(&values, params).unwrap();
        let batch = commitment.claim_batch(&claims, &gamma).unwrap();
        let openings = commitment.open_columns(&[8, 13, 21]).unwrap();

        reset_rs_encode_padded_call_count();
        assert!(verify_claim_batch(
            commitment.root(),
            params,
            values.len(),
            &openings,
            &batch,
            &claims,
            &gamma,
        )
        .unwrap());
        assert_eq!(rs_encode_padded_call_count(), 0);
    }

    #[test]
    fn v2_commit_rows_use_cached_rs_encoder() {
        let _lock = RS_COUNTER_TEST_LOCK.lock().unwrap();
        let params = v2_ligero_params();
        let values = (0..params.row_len * 3 + 7)
            .map(|value| Fp::from_u64(value as u64 + 1))
            .collect::<Vec<_>>();

        reset_rs_encode_padded_call_count();
        let (_commitment, profile) = commit_witness_profiled(&values, params).unwrap();
        let (row_cached, claim_cached) = rs_encode_padded_v2a_cached_call_counts();

        assert_eq!(profile.rows, 6);
        assert_eq!(row_cached, 5);
        assert_eq!(claim_cached, 1);
    }
}
