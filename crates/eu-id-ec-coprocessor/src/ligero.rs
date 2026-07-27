use crate::circle_fft::{
    circle_data_sum, circle_divide_data_vanishing, circle_encode, circle_encode_row,
    circle_evaluate, circle_multiply_data_vanishing, circle_product_fft, circle_product_ifft,
    circle_weight_coeffs, CircleGeom, CircleRsError, CIRCLE_GEOM_L128, CIRCLE_GEOM_L256,
    CIRCLE_GEOM_L64,
};
use crate::merkle::{commit_columns, verify_column, ColumnOpening, MerkleCommitment, MerkleError};
use crate::rs::{rs_encode_padded, rs_evaluate, RsError};
use crate::sumcheck::InputClaims;
use crate::{Fp, Mle, MleError};
use p256::elliptic_curve::rand_core::{OsRng, RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::time::{Duration, Instant};

/// Which linear code the Ligero matrix rows are encoded with.
///
/// `Rs`: systematic equispaced Reed–Solomon (finite-difference encoder,
/// message = evaluations at `0..degree_bound`). `Circle`: the Q-025 circle-FFT
/// code — message = 256 values on the disjoint message domain (64 data values
/// at the fixed data window + 192 random pads), sent/checked in universal-
/// basis coefficients.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum LigeroCode {
    Rs,
    Circle,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct LigeroParams {
    pub row_len: usize,
    pub degree_bound: usize,
    pub codeword_len: usize,
    pub openings: usize,
    pub proximity_radius: usize,
    pub code: LigeroCode,
}

pub const V1_MIN_OPENINGS: usize = 156;
pub const V2_ZK_OPENINGS: bool = true;
pub const LIGERO_AUXILIARY_ROW_COUNT: usize = 4;

const PROXIMITY_MASK_ROW_OFFSET: usize = 0;
const CLAIM_BLIND_ROW_OFFSET: usize = 1;
const CLAIM_BLIND_MASK_ROW_OFFSET: usize = 2;
const QUADRATIC_BLIND_ROW_OFFSET: usize = 3;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LigeroCommitment {
    params: LigeroParams,
    witness_rows: usize,
    quadratic_triples: usize,
    committed_rows: usize,
    proximity_mask_row: usize,
    claim_blind_row: usize,
    claim_blind_mask_row: usize,
    quadratic_blind_row: usize,
    encoded_rows: Vec<Vec<Fp>>,
    /// Circle code only: universal-basis coefficients per row (parallel to
    /// `encoded_rows`; the code is not systematic, so the message is not a
    /// codeword prefix). Empty for `LigeroCode::Rs`.
    coefficient_rows: Vec<Vec<Fp>>,
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
pub struct LigeroLinearTerm {
    pub offset: usize,
    pub len: usize,
    pub point: Vec<Fp>,
    pub coefficient: Fp,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct LigeroLinearClaim {
    pub terms: Vec<LigeroLinearTerm>,
    pub value: Fp,
}

impl LigeroLinearClaim {
    pub fn mle(offset: usize, len: usize, point: Vec<Fp>, value: Fp) -> Self {
        Self::affine(
            vec![LigeroLinearTerm {
                offset,
                len,
                point,
                coefficient: Fp::ONE,
            }],
            value,
        )
    }

    pub fn affine(terms: Vec<LigeroLinearTerm>, value: Fp) -> Self {
        Self { terms, value }
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct LigeroClaimBatch {
    pub coefficients: Vec<Fp>,
    pub blind_claim: Fp,
}

/// Zero-knowledge proof response that the committed claim-blind row lies in
/// the kernel of the fixed claim-extraction functional.
///
/// If `B` is the claim blind and `M` is an independently committed uniform
/// kernel mask, this carries the coefficients of `M + rho * B`. The verifier
/// checks both the opened-column identity and that its extraction is zero.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct LigeroClaimBlindCheck {
    pub combined_row: Vec<Fp>,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct LigeroQuadraticConstraint {
    pub x: usize,
    pub y: usize,
    pub z: usize,
}

#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
pub struct LigeroQuadraticBatch {
    /// Coefficients of `Q / Z_W`, where `Q` is the blinded, randomly batched
    /// quadratic residual and `Z_W` vanishes on every committed data slot.
    pub quotient: Vec<Fp>,
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
    InvalidQuadraticConstraint,
    ColumnOutOfRange,
    UnsupportedCode,
    Merkle(MerkleError),
    Rs(RsError),
    Circle(CircleRsError),
    Mle(MleError),
}

impl LigeroParams {
    /// The circle-code geometry these params select, matched by aspect ratio.
    /// `None` for the RS code (or an unrecognised circle size).
    pub fn circle_geom(self) -> Option<CircleGeom> {
        if self.code != LigeroCode::Circle {
            return None;
        }
        [CIRCLE_GEOM_L64, CIRCLE_GEOM_L128, CIRCLE_GEOM_L256]
            .into_iter()
            .find(|geom| {
                self.row_len == geom.data_slots
                    && self.degree_bound == geom.row_message_len
                    && self.codeword_len == geom.codeword_len
            })
    }

    pub fn validate(self) -> Result<(), LigeroError> {
        if self.row_len == 0 {
            return Err(LigeroError::InvalidRowLength);
        }
        if self.code == LigeroCode::Circle && self.circle_geom().is_none() {
            return Err(LigeroError::InvalidRowLength);
        }
        if self.degree_bound < self.row_len {
            return Err(LigeroError::InvalidDegreeBound);
        }
        if self
            .row_len
            .checked_add(self.openings)
            .is_none_or(|required| self.degree_bound < required)
        {
            return Err(LigeroError::InvalidDegreeBound);
        }
        if self.codeword_len <= self.degree_bound {
            return Err(LigeroError::CodewordTooShort);
        }
        if self.openings > self.codeword_len {
            return Err(LigeroError::TooManyOpenings);
        }
        let claim_bound = self.claim_degree_bound();
        let Some(claim_distance) = self.codeword_len.checked_sub(claim_bound) else {
            return Err(LigeroError::CodewordTooShort);
        };
        if self.proximity_radius.saturating_mul(2) >= claim_distance {
            return Err(LigeroError::ProximityRadiusTooLarge);
        }
        if self.codeword_len
            <= self
                .degree_bound
                .saturating_mul(2)
                .saturating_add(self.proximity_radius)
        {
            return Err(LigeroError::CodewordTooShort);
        }
        Ok(())
    }

    pub fn claim_degree_bound(self) -> usize {
        match self.code {
            LigeroCode::Rs => self
                .degree_bound
                .saturating_add(self.row_len)
                .saturating_sub(1),
            // W ∈ F_64 × R ∈ F_256 lands in F_322: the y² = 1 − x² fold adds
            // x-degree 2, so the product bound is a + b + 2, not a + b − 1
            // (Q-025 §params; the F_322 tail-zero test in circle_fft pins it).
            LigeroCode::Circle => self
                .degree_bound
                .saturating_add(self.row_len)
                .saturating_add(2),
        }
    }

    pub fn quadratic_degree_bound(self) -> usize {
        match self.code {
            LigeroCode::Rs => self.degree_bound.saturating_mul(2).saturating_sub(1),
            LigeroCode::Circle => self.degree_bound.saturating_mul(2).saturating_add(2),
        }
    }

    pub fn validate_quadratic(self) -> Result<(), LigeroError> {
        self.validate()?;
        let bound = self.quadratic_degree_bound();
        if bound > self.codeword_len {
            return Err(LigeroError::CodewordTooShort);
        }
        if self.code == LigeroCode::Circle
            && self
                .circle_geom()
                .is_none_or(|geom| bound > geom.product_domain_len)
        {
            return Err(LigeroError::InvalidDegreeBound);
        }
        let Some(distance) = self.codeword_len.checked_sub(bound) else {
            return Err(LigeroError::CodewordTooShort);
        };
        if self.proximity_radius.saturating_mul(2) >= distance {
            return Err(LigeroError::ProximityRadiusTooLarge);
        }
        if self.codeword_len <= bound.saturating_add(self.proximity_radius) {
            return Err(LigeroError::CodewordTooShort);
        }
        Ok(())
    }

    pub fn soundness_error(self) -> f64 {
        let n = self.codeword_len as f64;
        let k = self.degree_bound as f64;
        let t = self.openings as f64;
        let e = self.proximity_radius as f64;
        let claim = (self.claim_degree_bound() + 1) as f64;
        let quadratic = (self.quadratic_degree_bound() + 1) as f64;
        (1.0 - e / n).powf(t)
            + (2.0 * k / n).powf(t)
            + (claim / n).powf(t)
            + (claim / n).powf(t)
            + (quadratic / n).powf(t)
            + 2.0 * (n + 4.0) / 2f64.powi(256)
    }
}

pub fn v1_ligero_params() -> LigeroParams {
    LigeroParams {
        row_len: 64,
        degree_bound: 64,
        codeword_len: 512,
        openings: 160,
        proximity_radius: 223,
        code: LigeroCode::Rs,
    }
}

pub fn v2_ligero_params() -> LigeroParams {
    LigeroParams {
        row_len: 64,
        degree_bound: 234,
        codeword_len: 2048,
        openings: 170,
        proximity_radius: 875,
        code: LigeroCode::Rs,
    }
}

pub fn v2_ligero_params_b() -> LigeroParams {
    LigeroParams {
        row_len: 64,
        degree_bound: 289,
        codeword_len: 1024,
        openings: 225,
        proximity_radius: 335,
        code: LigeroCode::Rs,
    }
}

/// Q-025 circle-FFT params: k = 256 (64 data + 192 value-pads per row),
/// claim bound 322, e = 862 (2e < 2048 − 322). Soundness ≈ 2^−134:
/// (1 − 862/2048)^170 + (512/2048)^170 + 2·(323/2048)^170
/// + 2·(n+4)/2^256. The factor two conservatively accounts for the channel's
/// one-subtraction reduction from 256-bit strings into the field.
pub fn v2_circle_params() -> LigeroParams {
    LigeroParams {
        row_len: CIRCLE_GEOM_L64.data_slots,
        degree_bound: CIRCLE_GEOM_L64.row_message_len,
        codeword_len: CIRCLE_GEOM_L64.codeword_len,
        openings: 170,
        proximity_radius: 862,
        code: LigeroCode::Circle,
    }
}

/// WO-P6 ℓ=128 circle-FFT params: k = 512 (128 data + 384 value-pads per row),
/// claim bound 128 + 512 + 2 = 642, e = 1726 (2e < 4096 − 642), openings 168.
/// Soundness ≈ 2^−132.6, dominated by the proximity term:
/// (1 − 1726/4096)^168 = 2^−132.61; (2·512/4096)^168 = 2^−336;
/// 2·(643/4096)^168 < 2^−447.78; 2·(4096+4)/2^256 < 2^−242.99. Pad budget
/// 512 − 128 = 384 ≥ t = 168. (`v3_soundness_error_meets_target` pins it.)
pub fn v3_circle_params() -> LigeroParams {
    LigeroParams {
        row_len: CIRCLE_GEOM_L128.data_slots,
        degree_bound: CIRCLE_GEOM_L128.row_message_len,
        codeword_len: CIRCLE_GEOM_L128.codeword_len,
        openings: 168,
        proximity_radius: 1726,
        code: LigeroCode::Circle,
    }
}

/// Committed-mask v4 parameters. The largest response is the quadratic check,
/// with bound `2*512 + 2 = 1026`; `e = 1534` is maximal because
/// `2e < 4096 - 1026`. With `t = 196`, the proximity term is below 2^-132,
/// and the 256 row-pad slots still exceed the opening count.
pub fn v4_circle_params() -> LigeroParams {
    LigeroParams {
        row_len: CIRCLE_GEOM_L256.data_slots,
        degree_bound: CIRCLE_GEOM_L256.row_message_len,
        codeword_len: CIRCLE_GEOM_L256.codeword_len,
        openings: 196,
        proximity_radius: 1534,
        code: LigeroCode::Circle,
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
    commit_witness_with_quadratics_profiled(witness, params, &[])
}

pub fn commit_witness_with_quadratics_profiled(
    witness: &[Fp],
    params: LigeroParams,
    quadratic_constraints: &[LigeroQuadraticConstraint],
) -> Result<(LigeroCommitment, LigeroCommitProfile), LigeroError> {
    params.validate()?;
    if !quadratic_constraints.is_empty() {
        params.validate_quadratic()?;
    }
    if witness.is_empty() {
        return Err(LigeroError::EmptyWitness);
    }
    if !quadratic_constraints.is_empty() && params.code != LigeroCode::Circle {
        return Err(LigeroError::UnsupportedCode);
    }
    validate_quadratic_constraints(witness, quadratic_constraints)?;

    let row_encode_start = Instant::now();
    let mut encoded_rows;
    let mut coefficient_rows;
    let mut pads = fresh_pad_rng();
    let claim_degree_bound = params.claim_degree_bound();
    match params.code {
        LigeroCode::Rs => {
            let row_pads = witness
                .chunks(params.row_len)
                .map(|_| draw_uniform_fps(&mut pads, params.degree_bound - params.row_len))
                .collect::<Vec<_>>();
            encoded_rows = witness
                .par_chunks(params.row_len)
                .zip(row_pads.into_par_iter())
                .map(|(chunk, row_pads)| {
                    let mut row = Vec::with_capacity(params.degree_bound);
                    row.extend_from_slice(chunk);
                    row.resize(params.row_len, Fp::ZERO);
                    row.extend(row_pads);
                    rs_encode_padded(&row, params.degree_bound, params.codeword_len)
                        .map_err(LigeroError::Rs)
                })
                .collect::<Result<Vec<_>, _>>()?;
            coefficient_rows = Vec::new();
        }
        LigeroCode::Circle => {
            let geom = params.circle_geom().expect("validated circle params");
            // Draw pads serially to preserve the channel order, then encode
            // independent rows in parallel without changing their order.
            let row_pads = witness
                .chunks(params.row_len)
                .map(|_| draw_uniform_fps(&mut pads, geom.row_message_len - geom.data_slots))
                .collect::<Vec<_>>();
            let rows = witness
                .par_chunks(params.row_len)
                .zip(row_pads.into_par_iter())
                .map(|(chunk, row_pads)| {
                    let mut row_pads = row_pads.into_iter();
                    circle_encode_row(geom, chunk, || {
                        row_pads.next().expect("row pad budget exhausted")
                    })
                    .map_err(LigeroError::Circle)
                })
                .collect::<Result<Vec<_>, _>>()?;
            (coefficient_rows, encoded_rows) = rows.into_iter().unzip();
        }
    }
    let witness_rows = encoded_rows.len();
    let quadratic_triples = quadratic_constraints.len().div_ceil(params.row_len);
    append_quadratic_rows(
        witness,
        quadratic_constraints,
        params,
        &mut pads,
        &mut coefficient_rows,
        &mut encoded_rows,
    )?;
    let committed_rows = encoded_rows.len();
    // WO-P2: bulk-draw the proximity-mask row's coefficients.
    let mask_row = draw_uniform_fps(&mut pads, params.degree_bound);
    let proximity_mask_row = encoded_rows.len();
    match params.code {
        LigeroCode::Rs => encoded_rows.push(
            rs_encode_padded(&mask_row, params.degree_bound, params.codeword_len)
                .map_err(LigeroError::Rs)?,
        ),
        LigeroCode::Circle => {
            // A uniform coefficient vector is a uniform message-space element —
            // the same distribution the value-side draw would give.
            let geom = params.circle_geom().expect("validated circle params");
            encoded_rows.push(
                circle_encode(geom, &mask_row, params.degree_bound).map_err(LigeroError::Circle)?,
            );
            coefficient_rows.push(mask_row.clone());
        }
    }
    // The claim blind and its independent check mask are both sampled
    // uniformly from the kernel of the fixed extraction functional. The
    // verifier proves this committed invariant with a masked random linear
    // combination, rather than trusting honest-prover construction.
    let blind_row = claim_blind_row_coefficients(params, &mut pads);
    let claim_blind_row = encoded_rows.len();
    match params.code {
        LigeroCode::Rs => encoded_rows.push(
            rs_encode_padded(&blind_row, claim_degree_bound, params.codeword_len)
                .map_err(LigeroError::Rs)?,
        ),
        LigeroCode::Circle => {
            let geom = params.circle_geom().expect("validated circle params");
            encoded_rows.push(
                circle_encode(geom, &blind_row, claim_degree_bound).map_err(LigeroError::Circle)?,
            );
            coefficient_rows.push(blind_row);
        }
    }
    let blind_mask_row = claim_blind_row_coefficients(params, &mut pads);
    let claim_blind_mask_row = encoded_rows.len();
    match params.code {
        LigeroCode::Rs => encoded_rows.push(
            rs_encode_padded(&blind_mask_row, claim_degree_bound, params.codeword_len)
                .map_err(LigeroError::Rs)?,
        ),
        LigeroCode::Circle => {
            let geom = params.circle_geom().expect("validated circle params");
            encoded_rows.push(
                circle_encode(geom, &blind_mask_row, claim_degree_bound)
                    .map_err(LigeroError::Circle)?,
            );
            coefficient_rows.push(blind_mask_row);
        }
    }
    let quadratic_blind_row = encoded_rows.len();
    let quadratic_blind_degree = if quadratic_constraints.is_empty() {
        params.degree_bound
    } else {
        params.quadratic_degree_bound()
    };
    let quadratic_blind =
        quadratic_blind_row_coefficients(params, quadratic_blind_degree, &mut pads)?;
    match params.code {
        LigeroCode::Rs => encoded_rows.push(
            rs_encode_padded(
                &quadratic_blind,
                quadratic_blind_degree,
                params.codeword_len,
            )
            .map_err(LigeroError::Rs)?,
        ),
        LigeroCode::Circle => {
            let geom = params.circle_geom().expect("validated circle params");
            encoded_rows.push(
                circle_encode(geom, &quadratic_blind, quadratic_blind_degree)
                    .map_err(LigeroError::Circle)?,
            );
            coefficient_rows.push(quadratic_blind);
        }
    }
    debug_assert_eq!(
        proximity_mask_row,
        committed_rows + PROXIMITY_MASK_ROW_OFFSET
    );
    debug_assert_eq!(claim_blind_row, committed_rows + CLAIM_BLIND_ROW_OFFSET);
    debug_assert_eq!(
        claim_blind_mask_row,
        committed_rows + CLAIM_BLIND_MASK_ROW_OFFSET
    );
    debug_assert_eq!(
        quadratic_blind_row,
        committed_rows + QUADRATIC_BLIND_ROW_OFFSET
    );
    debug_assert_eq!(
        encoded_rows.len(),
        committed_rows + LIGERO_AUXILIARY_ROW_COUNT
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
            quadratic_triples,
            committed_rows,
            proximity_mask_row,
            claim_blind_row,
            claim_blind_mask_row,
            quadratic_blind_row,
            encoded_rows,
            coefficient_rows,
            merkle,
        },
        LigeroCommitProfile {
            row_encode,
            merkle_build,
            rows,
        },
    ))
}

fn validate_quadratic_constraints(
    witness: &[Fp],
    constraints: &[LigeroQuadraticConstraint],
) -> Result<(), LigeroError> {
    for constraint in constraints {
        if [constraint.x, constraint.y, constraint.z]
            .into_iter()
            .any(|index| index >= witness.len())
            || witness[constraint.x] * witness[constraint.y] != witness[constraint.z]
        {
            return Err(LigeroError::InvalidQuadraticConstraint);
        }
    }
    Ok(())
}

fn append_quadratic_rows(
    witness: &[Fp],
    constraints: &[LigeroQuadraticConstraint],
    params: LigeroParams,
    rng: &mut ChaCha20Rng,
    coefficient_rows: &mut Vec<Vec<Fp>>,
    encoded_rows: &mut Vec<Vec<Fp>>,
) -> Result<(), LigeroError> {
    if constraints.is_empty() {
        return Ok(());
    }

    let triples = constraints.len().div_ceil(params.row_len);
    let mut x_rows = vec![vec![Fp::ZERO; params.row_len]; triples];
    let mut y_rows = vec![vec![Fp::ZERO; params.row_len]; triples];
    let mut z_rows = vec![vec![Fp::ZERO; params.row_len]; triples];
    for (index, constraint) in constraints.iter().enumerate() {
        let row = index / params.row_len;
        let column = index % params.row_len;
        x_rows[row][column] = witness[constraint.x];
        y_rows[row][column] = witness[constraint.y];
        z_rows[row][column] = witness[constraint.z];
    }

    for rows in [&x_rows, &y_rows, &z_rows] {
        for data in rows {
            match params.code {
                LigeroCode::Rs => {
                    let mut message = data.clone();
                    message.extend(draw_uniform_fps(rng, params.degree_bound - params.row_len));
                    encoded_rows.push(
                        rs_encode_padded(&message, params.degree_bound, params.codeword_len)
                            .map_err(LigeroError::Rs)?,
                    );
                }
                LigeroCode::Circle => {
                    let geom = params.circle_geom().expect("validated circle params");
                    let mut row_pads =
                        draw_uniform_fps(rng, geom.row_message_len - geom.data_slots).into_iter();
                    let (coefficients, codeword) = circle_encode_row(geom, data, || {
                        row_pads.next().expect("quadratic row pad budget exhausted")
                    })
                    .map_err(LigeroError::Circle)?;
                    coefficient_rows.push(coefficients);
                    encoded_rows.push(codeword);
                }
            }
        }
    }
    Ok(())
}

fn claim_blind_row_coefficients(params: LigeroParams, rng: &mut ChaCha20Rng) -> Vec<Fp> {
    let mut row = draw_uniform_fps(rng, params.claim_degree_bound());
    match params.code {
        LigeroCode::Rs => {
            let sum = row[..params.row_len]
                .iter()
                .copied()
                .fold(Fp::ZERO, |acc, value| acc + value);
            row[0] = row[0] - sum;
        }
        LigeroCode::Circle => {
            // b_0 ≡ 1 at every data point. Adjusting c_0 by −L(row)/d
            // projects a uniform coefficient vector uniformly onto ker L.
            let geom = params.circle_geom().expect("validated circle params");
            let sum = circle_data_sum(geom, &row);
            let slots_inv = Fp::from_u64(geom.data_slots as u64)
                .inverse()
                .expect("power of two is invertible mod p");
            row[0] = row[0] - sum * slots_inv;
        }
    }
    row
}

fn quadratic_blind_row_coefficients(
    params: LigeroParams,
    degree_bound: usize,
    rng: &mut ChaCha20Rng,
) -> Result<Vec<Fp>, LigeroError> {
    match params.code {
        LigeroCode::Rs => {
            let mut row = vec![Fp::ZERO; params.row_len];
            row.extend(draw_uniform_fps(rng, degree_bound - params.row_len));
            Ok(row)
        }
        LigeroCode::Circle => {
            let geom = params.circle_geom().expect("validated circle params");
            let quotient = draw_uniform_fps(rng, degree_bound - geom.data_slots);
            circle_multiply_data_vanishing(geom, &quotient, degree_bound)
                .map_err(LigeroError::Circle)
        }
    }
}

impl LigeroCommitment {
    pub fn root(&self) -> [u8; 32] {
        self.merkle.root()
    }

    pub fn committed_rows(&self) -> usize {
        self.committed_rows
    }

    pub fn params(&self) -> LigeroParams {
        self.params
    }

    pub fn quadratic_batch(&self, challenges: &[Fp]) -> Result<LigeroQuadraticBatch, LigeroError> {
        if self.quadratic_triples == 0 {
            if challenges.is_empty() {
                return Ok(LigeroQuadraticBatch::default());
            }
            return Err(LigeroError::WrongGammaLength);
        }
        self.params.validate_quadratic()?;
        if self.params.code != LigeroCode::Circle {
            return Err(LigeroError::UnsupportedCode);
        }
        if challenges.len() != self.quadratic_triples {
            return Err(LigeroError::WrongGammaLength);
        }

        let geom = self.params.circle_geom().expect("validated circle params");
        let degree_bound = self.params.quadratic_degree_bound();
        let mut response_values =
            circle_product_fft(geom, &self.coefficient_rows[self.quadratic_blind_row])
                .map_err(LigeroError::Circle)?;
        let x_start = self.witness_rows;
        let y_start = x_start + self.quadratic_triples;
        let z_start = y_start + self.quadratic_triples;
        for (index, challenge) in challenges.iter().copied().enumerate() {
            let x = circle_product_fft(geom, &self.coefficient_rows[x_start + index])
                .map_err(LigeroError::Circle)?;
            let y = circle_product_fft(geom, &self.coefficient_rows[y_start + index])
                .map_err(LigeroError::Circle)?;
            let z = circle_product_fft(geom, &self.coefficient_rows[z_start + index])
                .map_err(LigeroError::Circle)?;
            for (((response, x), y), z) in response_values.iter_mut().zip(x).zip(y).zip(z) {
                *response = *response + challenge * (z - x * y);
            }
        }
        let coefficients =
            circle_product_ifft(geom, response_values).map_err(LigeroError::Circle)?;
        if coefficients[degree_bound..]
            .iter()
            .any(|&coefficient| coefficient != Fp::ZERO)
        {
            return Err(LigeroError::InvalidQuadraticConstraint);
        }
        let quotient =
            circle_divide_data_vanishing(geom, &coefficients[..degree_bound], degree_bound)
                .map_err(LigeroError::Circle)?;
        Ok(LigeroQuadraticBatch { quotient })
    }

    /// The message vector of a committed row: the systematic codeword prefix
    /// for RS, the stored universal-basis coefficients for the circle code.
    fn row_message(&self, row: usize) -> &[Fp] {
        match self.params.code {
            LigeroCode::Rs => &self.encoded_rows[row][..self.params.degree_bound],
            LigeroCode::Circle => &self.coefficient_rows[row],
        }
    }

    fn claim_row_message(&self, row: usize) -> &[Fp] {
        match self.params.code {
            LigeroCode::Rs => &self.encoded_rows[row][..self.params.claim_degree_bound()],
            LigeroCode::Circle => &self.coefficient_rows[row],
        }
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
        if gamma.len() != self.committed_rows {
            return Err(LigeroError::WrongGammaLength);
        }

        let mut combined_row = self.row_message(self.proximity_mask_row).to_vec();
        for (index, coeff) in gamma.iter().copied().enumerate() {
            for (out, value) in combined_row.iter_mut().zip(self.row_message(index)) {
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
        if gamma.len() != self.committed_rows + other.committed_rows {
            return Err(LigeroError::WrongGammaLength);
        }

        let mut combined_row = self.row_message(self.proximity_mask_row).to_vec();
        for (out, value) in combined_row
            .iter_mut()
            .zip(other.row_message(other.proximity_mask_row))
        {
            *out = *out + *value;
        }
        for (index, coeff) in gamma[..self.committed_rows].iter().copied().enumerate() {
            for (out, value) in combined_row.iter_mut().zip(self.row_message(index)) {
                *out = *out + coeff * *value;
            }
        }
        for (index, coeff) in gamma[self.committed_rows..].iter().copied().enumerate() {
            for (out, value) in combined_row.iter_mut().zip(other.row_message(index)) {
                *out = *out + coeff * *value;
            }
        }
        Ok(LigeroProximityClaim { combined_row })
    }

    pub fn claim_blind_check(&self, challenge: Fp) -> LigeroClaimBlindCheck {
        let mut combined_row = self.claim_row_message(self.claim_blind_mask_row).to_vec();
        for (out, blind) in combined_row
            .iter_mut()
            .zip(self.claim_row_message(self.claim_blind_row))
        {
            *out = *out + challenge * *blind;
        }
        LigeroClaimBlindCheck { combined_row }
    }

    pub fn split_claim_blind_check(
        &self,
        other: &Self,
        challenge: Fp,
    ) -> Result<LigeroClaimBlindCheck, LigeroError> {
        if self.params != other.params {
            return Err(LigeroError::InvalidRowLength);
        }
        let mut combined_row = self.claim_row_message(self.claim_blind_mask_row).to_vec();
        for (out, value) in combined_row
            .iter_mut()
            .zip(other.claim_row_message(other.claim_blind_mask_row))
        {
            *out = *out + *value;
        }
        for (out, blind) in combined_row
            .iter_mut()
            .zip(self.claim_row_message(self.claim_blind_row))
        {
            *out = *out + challenge * *blind;
        }
        for (out, blind) in combined_row
            .iter_mut()
            .zip(other.claim_row_message(other.claim_blind_row))
        {
            *out = *out + challenge * *blind;
        }
        Ok(LigeroClaimBlindCheck { combined_row })
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
        if self.params.code == LigeroCode::Circle {
            return self.circle_claim_batch(None, claims, gamma);
        }
        let claim_degree_bound = self.params.claim_degree_bound();
        let blind_row = &self.encoded_rows[self.claim_blind_row];
        let mut coefficients = blind_row[..claim_degree_bound].to_vec();

        for (row, weights) in batched_row_weights(self.params, self.committed_rows, claims, gamma)?
        {
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

    /// Q-025 circle claim batch: Q = blind + Σ_r W_r·R_r. WO-P1 computes the
    /// product on the 512-point domain D512 instead of the 2048-codeword: each
    /// factor lives in F_322 ⊂ F_512-representable message space (W ∈ F_64,
    /// R ∈ F_256, product bound 322 < 512), so a 512-point evaluation domain
    /// determines Q exactly at ~1/4 the per-row cost. One IFFT512 recovers the
    /// coefficients (the universal basis is domain-independent). The blind row
    /// is committed with a zero data-window sum, so blind_claim is identically
    /// zero.
    fn circle_claim_batch(
        &self,
        other: Option<&Self>,
        claims: &[LigeroLinearClaim],
        gamma: &[Fp],
    ) -> Result<LigeroClaimBatch, LigeroError> {
        let geom = self.params.circle_geom().expect("validated circle params");
        let claim_degree_bound = self.params.claim_degree_bound();
        // Blind coefficients → product-domain evaluations, the accumulator.
        let mut blind_coeffs = self.coefficient_rows[self.claim_blind_row].clone();
        if let Some(other) = other {
            for (out, value) in blind_coeffs
                .iter_mut()
                .zip(&other.coefficient_rows[other.claim_blind_row])
            {
                *out = *out + *value;
            }
        }
        let mut q_values = circle_product_fft(geom, &blind_coeffs).map_err(LigeroError::Circle)?;

        let combined_rows = self.committed_rows + other.map_or(0, |o| o.committed_rows);
        let row_weights = batched_row_weights(self.params, combined_rows, claims, gamma)?;
        let row_products = row_weights
            .par_iter()
            .map(|(row, weights)| {
                let w_coeffs = circle_weight_coeffs(geom, weights).map_err(LigeroError::Circle)?;
                let w_values = circle_product_fft(geom, &w_coeffs).map_err(LigeroError::Circle)?;
                let row_coeffs = if *row < self.committed_rows {
                    &self.coefficient_rows[*row]
                } else {
                    &other
                        .expect("row index beyond first group")
                        .coefficient_rows[*row - self.committed_rows]
                };
                let r_values = circle_product_fft(geom, row_coeffs).map_err(LigeroError::Circle)?;
                Ok(w_values
                    .into_iter()
                    .zip(r_values)
                    .map(|(w, r)| w * r)
                    .collect::<Vec<_>>())
            })
            .collect::<Result<Vec<_>, LigeroError>>()?;
        for row_product in row_products {
            for (out, product) in q_values.iter_mut().zip(row_product) {
                *out = *out + product;
            }
        }
        let coefficients = circle_product_ifft(geom, q_values).map_err(LigeroError::Circle)?;
        debug_assert_eq!(coefficients.len(), geom.product_domain_len);
        assert!(
            coefficients[claim_degree_bound..]
                .iter()
                .all(|&c| c == Fp::ZERO),
            "circle claim batch escaped F_{claim_degree_bound} (Q-025 tail-zero gate, D512)"
        );
        Ok(LigeroClaimBatch {
            coefficients: coefficients[..claim_degree_bound].to_vec(),
            blind_claim: Fp::ZERO,
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
        if self.params.code == LigeroCode::Circle {
            return self.circle_claim_batch(Some(other), claims, gamma);
        }
        let claim_degree_bound = self.params.claim_degree_bound();
        let blind_a = &self.encoded_rows[self.claim_blind_row];
        let blind_b = &other.encoded_rows[other.claim_blind_row];
        let mut coefficients = blind_a[..claim_degree_bound].to_vec();
        for (out, value) in coefficients.iter_mut().zip(&blind_b[..claim_degree_bound]) {
            *out = *out + *value;
        }

        let combined_rows = self.committed_rows + other.committed_rows;
        for (row, weights) in batched_row_weights(self.params, combined_rows, claims, gamma)? {
            let weight_evals = weight_evaluations(self.params, &weights, 0..claim_degree_bound)?;
            let encoded_row = if row < self.committed_rows {
                &self.encoded_rows[row]
            } else {
                &other.encoded_rows[row - self.committed_rows]
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

fn committed_opening_rows(
    committed_len: usize,
    row_len: usize,
) -> Result<(usize, usize), LigeroError> {
    if row_len == 0 {
        return Err(LigeroError::InvalidRowLength);
    }
    let committed_rows = committed_len.div_ceil(row_len);
    let opening_rows = committed_rows
        .checked_add(LIGERO_AUXILIARY_ROW_COUNT)
        .ok_or(LigeroError::InvalidRowLength)?;
    Ok((committed_rows, opening_rows))
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
    let (rows_a, opening_rows_a) = committed_opening_rows(committed_len_a, params.row_len)?;
    let (rows_b, opening_rows_b) = committed_opening_rows(committed_len_b, params.row_len)?;
    let combined_rows = rows_a
        .checked_add(rows_b)
        .ok_or(LigeroError::InvalidRowLength)?;
    if gamma.len() != combined_rows {
        return Err(LigeroError::WrongGammaLength);
    }

    for (opening_a, opening_b) in openings_a.iter().zip(openings_b) {
        if opening_a.index != opening_b.index {
            return Err(LigeroError::ColumnOutOfRange);
        }
        if opening_a.index >= params.codeword_len {
            return Err(LigeroError::ColumnOutOfRange);
        }
        if opening_a.column.len() != opening_rows_a || opening_b.column.len() != opening_rows_b {
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
        let expected = code_evaluate(params, &claim.combined_row, opening_a.index)?;
        if expected != combined {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(crate) struct AuthenticatedSplitOpenings<'a> {
    params: LigeroParams,
    committed_len_a: usize,
    committed_len_b: usize,
    openings_a: &'a [ColumnOpening],
    openings_b: &'a [ColumnOpening],
}

pub(crate) fn verify_and_authenticate_split_openings<'a>(
    root_a: [u8; 32],
    root_b: [u8; 32],
    params: LigeroParams,
    committed_len_a: usize,
    committed_len_b: usize,
    openings_a: &'a [ColumnOpening],
    openings_b: &'a [ColumnOpening],
    claim: &LigeroProximityClaim,
    gamma: &[Fp],
) -> Result<Option<AuthenticatedSplitOpenings<'a>>, LigeroError> {
    if !verify_split_openings(
        root_a,
        root_b,
        params,
        committed_len_a,
        committed_len_b,
        openings_a,
        openings_b,
        claim,
        gamma,
    )? {
        return Ok(None);
    }
    Ok(Some(AuthenticatedSplitOpenings {
        params,
        committed_len_a,
        committed_len_b,
        openings_a,
        openings_b,
    }))
}

pub fn verify_claim_blind_check(
    root: [u8; 32],
    params: LigeroParams,
    committed_len: usize,
    openings: &[ColumnOpening],
    check: &LigeroClaimBlindCheck,
    challenge: Fp,
) -> Result<bool, LigeroError> {
    params.validate()?;
    if openings.len() != params.openings {
        return Err(LigeroError::WrongOpeningCount);
    }
    if check.combined_row.len() != params.claim_degree_bound() {
        return Err(LigeroError::WrongClaimLength);
    }
    if claim_extraction_sum(params, &check.combined_row) != Fp::ZERO {
        return Ok(false);
    }
    let (committed_rows, expected_rows) = committed_opening_rows(committed_len, params.row_len)?;
    for opening in openings {
        if opening.index >= params.codeword_len {
            return Err(LigeroError::ColumnOutOfRange);
        }
        if opening.column.len() != expected_rows {
            return Err(LigeroError::WrongGammaLength);
        }
        if !verify_column(root, opening).map_err(LigeroError::Merkle)? {
            return Ok(false);
        }
        let expected = code_evaluate(params, &check.combined_row, opening.index)?;
        let actual = opening.column[committed_rows + CLAIM_BLIND_MASK_ROW_OFFSET]
            + challenge * opening.column[committed_rows + CLAIM_BLIND_ROW_OFFSET];
        if expected != actual {
            return Ok(false);
        }
    }
    Ok(true)
}

#[allow(clippy::too_many_arguments)]
pub fn verify_split_claim_blind_check(
    root_a: [u8; 32],
    root_b: [u8; 32],
    params: LigeroParams,
    committed_len_a: usize,
    committed_len_b: usize,
    openings_a: &[ColumnOpening],
    openings_b: &[ColumnOpening],
    check: &LigeroClaimBlindCheck,
    challenge: Fp,
) -> Result<bool, LigeroError> {
    params.validate()?;
    if openings_a.len() != params.openings || openings_b.len() != params.openings {
        return Err(LigeroError::WrongOpeningCount);
    }
    if openings_a.len() != openings_b.len() {
        return Err(LigeroError::WrongOpeningCount);
    }
    if check.combined_row.len() != params.claim_degree_bound() {
        return Err(LigeroError::WrongClaimLength);
    }
    if claim_extraction_sum(params, &check.combined_row) != Fp::ZERO {
        return Ok(false);
    }
    let (rows_a, opening_rows_a) = committed_opening_rows(committed_len_a, params.row_len)?;
    let (rows_b, opening_rows_b) = committed_opening_rows(committed_len_b, params.row_len)?;
    for (opening_a, opening_b) in openings_a.iter().zip(openings_b) {
        if opening_a.index != opening_b.index || opening_a.index >= params.codeword_len {
            return Err(LigeroError::ColumnOutOfRange);
        }
        if opening_a.column.len() != opening_rows_a || opening_b.column.len() != opening_rows_b {
            return Err(LigeroError::WrongGammaLength);
        }
        if !verify_column(root_a, opening_a).map_err(LigeroError::Merkle)?
            || !verify_column(root_b, opening_b).map_err(LigeroError::Merkle)?
        {
            return Ok(false);
        }
        let expected = code_evaluate(params, &check.combined_row, opening_a.index)?;
        let actual = opening_a.column[rows_a + CLAIM_BLIND_MASK_ROW_OFFSET]
            + opening_b.column[rows_b + CLAIM_BLIND_MASK_ROW_OFFSET]
            + challenge
                * (opening_a.column[rows_a + CLAIM_BLIND_ROW_OFFSET]
                    + opening_b.column[rows_b + CLAIM_BLIND_ROW_OFFSET]);
        if expected != actual {
            return Ok(false);
        }
    }
    Ok(true)
}

const STRUCTURED_CLAIM_MIN_ROWS: usize = 4;

struct ClaimWeightTemplate {
    values: Vec<Fp>,
    row_scales: Vec<(usize, Fp)>,
}

struct ClaimWeightPlan {
    residual_rows: Vec<(usize, Vec<Fp>)>,
    templates: Vec<ClaimWeightTemplate>,
}

struct EvaluatedWeightTemplate {
    values: Vec<Fp>,
    row_scales: Vec<(usize, Fp)>,
}

struct EvaluatedClaimWeights {
    residual_rows: Vec<(usize, Vec<Fp>)>,
    templates: Vec<EvaluatedWeightTemplate>,
}

#[cfg(test)]
thread_local! {
    static STRUCTURED_CLAIM_OVERRIDE: std::cell::Cell<Option<bool>> = const { std::cell::Cell::new(None) };
    static CIRCLE_WEIGHT_ENCODE_CALLS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

fn structured_claims_enabled() -> bool {
    #[cfg(test)]
    {
        STRUCTURED_CLAIM_OVERRIDE.with(|value| value.get().unwrap_or(true))
    }
    #[cfg(not(test))]
    {
        true
    }
}

#[cfg(test)]
pub(crate) fn set_structured_claims_for_test(enabled: Option<bool>) {
    STRUCTURED_CLAIM_OVERRIDE.with(|value| value.set(enabled));
}

#[cfg(test)]
pub(crate) fn reset_circle_weight_encode_call_count() {
    CIRCLE_WEIGHT_ENCODE_CALLS.with(|calls| calls.set(0));
}

#[cfg(test)]
pub(crate) fn circle_weight_encode_call_count() -> usize {
    CIRCLE_WEIGHT_ENCODE_CALLS.with(std::cell::Cell::get)
}

fn add_claim_weight_template(
    templates: &mut Vec<ClaimWeightTemplate>,
    values: Vec<Fp>,
    row: usize,
    scale: Fp,
) {
    if scale == Fp::ZERO {
        return;
    }
    let template = if let Some(index) = templates.iter().position(|entry| entry.values == values) {
        &mut templates[index]
    } else {
        templates.push(ClaimWeightTemplate {
            values,
            row_scales: Vec::new(),
        });
        templates.last_mut().expect("just pushed a template")
    };
    if let Some((_, existing)) = template
        .row_scales
        .iter_mut()
        .find(|(existing_row, _)| *existing_row == row)
    {
        *existing = *existing + scale;
    } else {
        template.row_scales.push((row, scale));
    }
}

fn factor_claim_term_weights(
    params: LigeroParams,
    term: &LigeroLinearTerm,
    scale: Fp,
    templates: &mut Vec<ClaimWeightTemplate>,
) {
    // For row_len = 2^r, eq(point, i) factors into independent low-r-bit
    // (column) and high-bit (row) tensors. An unaligned term block crosses
    // at most two physical rows, so each block is a scaled copy of one of two
    // shifted column templates; only the final partial block can add a third.
    let row_len = params.row_len;
    let row_log = row_len.ilog2() as usize;
    let low = eq_tensor(&term.point[..row_log]);
    let high = eq_tensor(&term.point[row_log..]);
    let base_row = term.offset / row_len;
    let shift = term.offset % row_len;

    for (block, high_weight) in high
        .iter()
        .copied()
        .take(term.len.div_ceil(row_len))
        .enumerate()
    {
        let valid = row_len.min(term.len - block * row_len);
        let block_scale = scale * high_weight;
        let first_len = valid.min(row_len - shift);
        if first_len > 0 {
            let mut first = vec![Fp::ZERO; row_len];
            first[shift..shift + first_len].copy_from_slice(&low[..first_len]);
            add_claim_weight_template(templates, first, base_row + block, block_scale);
        }
        if valid > first_len {
            let second_len = valid - first_len;
            let mut second = vec![Fp::ZERO; row_len];
            second[..second_len]
                .copy_from_slice(&low[row_len - shift..row_len - shift + second_len]);
            add_claim_weight_template(templates, second, base_row + block + 1, block_scale);
        }
    }
}

fn claim_weight_plan(
    params: LigeroParams,
    committed_rows: usize,
    claims: &[LigeroLinearClaim],
    gamma: &[Fp],
    structured: bool,
) -> Result<ClaimWeightPlan, LigeroError> {
    let mut rows = vec![vec![Fp::ZERO; params.row_len]; committed_rows];
    let mut templates = Vec::new();
    for (claim, coeff) in claims.iter().zip(gamma.iter().copied()) {
        validate_linear_claim(params, committed_rows, claim)?;
        for term in &claim.terms {
            let scale = coeff * term.coefficient;
            let row_span = ((term.offset % params.row_len) + term.len).div_ceil(params.row_len);
            let fixed = term
                .point
                .iter()
                .all(|&value| value == Fp::ZERO || value == Fp::ONE);
            let factor = structured
                && params.code == LigeroCode::Circle
                && params.row_len.is_power_of_two()
                && row_span >= STRUCTURED_CLAIM_MIN_ROWS
                && !fixed;
            if factor {
                factor_claim_term_weights(params, term, scale, &mut templates);
                continue;
            }

            let eq = eq_tensor(&term.point);
            for (local, &weight) in eq.iter().enumerate().take(term.len) {
                let global = term.offset + local;
                let cell = &mut rows[global / params.row_len][global % params.row_len];
                *cell = *cell + scale * weight;
            }
        }
    }
    Ok(ClaimWeightPlan {
        residual_rows: rows
            .into_iter()
            .enumerate()
            .filter(|(_, weights)| weights.iter().any(|&weight| weight != Fp::ZERO))
            .collect(),
        templates,
    })
}

fn evaluate_claim_weight_plan(
    plan: ClaimWeightPlan,
    column_eval: &ClaimBatchColumnEval,
) -> Result<EvaluatedClaimWeights, LigeroError> {
    #[cfg(test)]
    if matches!(column_eval, ClaimBatchColumnEval::Circle { .. }) {
        let evaluations = plan.residual_rows.len() + plan.templates.len();
        CIRCLE_WEIGHT_ENCODE_CALLS.with(|calls| calls.set(calls.get() + evaluations));
    }
    let residual_rows = plan
        .residual_rows
        .into_par_iter()
        .map(|(row, weights)| Ok((row, column_eval.eval_weights(&weights)?)))
        .collect::<Result<Vec<_>, LigeroError>>()?;
    let templates = plan
        .templates
        .into_par_iter()
        .map(|template| {
            Ok(EvaluatedWeightTemplate {
                values: column_eval.eval_weights(&template.values)?,
                row_scales: template.row_scales,
            })
        })
        .collect::<Result<Vec<_>, LigeroError>>()?;
    Ok(EvaluatedClaimWeights {
        residual_rows,
        templates,
    })
}

#[cfg(test)]
fn evaluate_claim_weight_plan_serial(
    plan: ClaimWeightPlan,
    column_eval: &ClaimBatchColumnEval,
) -> Result<EvaluatedClaimWeights, LigeroError> {
    let residual_rows = plan
        .residual_rows
        .into_iter()
        .map(|(row, weights)| Ok((row, column_eval.eval_weights(&weights)?)))
        .collect::<Result<Vec<_>, LigeroError>>()?;
    let templates = plan
        .templates
        .into_iter()
        .map(|template| {
            Ok(EvaluatedWeightTemplate {
                values: column_eval.eval_weights(&template.values)?,
                row_scales: template.row_scales,
            })
        })
        .collect::<Result<Vec<_>, LigeroError>>()?;
    Ok(EvaluatedClaimWeights {
        residual_rows,
        templates,
    })
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
    verify_split_claim_batch_inner(
        SplitOpeningAuthentication::Verify { root_a, root_b },
        params,
        committed_len_a,
        committed_len_b,
        openings_a,
        openings_b,
        batch,
        claims,
        gamma,
    )
}

pub(crate) fn verify_authenticated_split_claim_batch(
    authenticated: AuthenticatedSplitOpenings<'_>,
    batch: &LigeroClaimBatch,
    claims: &[LigeroLinearClaim],
    gamma: &[Fp],
) -> Result<bool, LigeroError> {
    verify_split_claim_batch_inner(
        SplitOpeningAuthentication::AlreadyVerified,
        authenticated.params,
        authenticated.committed_len_a,
        authenticated.committed_len_b,
        authenticated.openings_a,
        authenticated.openings_b,
        batch,
        claims,
        gamma,
    )
}

#[derive(Clone, Copy)]
enum SplitOpeningAuthentication {
    Verify { root_a: [u8; 32], root_b: [u8; 32] },
    AlreadyVerified,
}

#[allow(clippy::too_many_arguments)]
fn verify_split_claim_batch_inner(
    authentication: SplitOpeningAuthentication,
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
    // C-p4b-blind-claim: a prover-chosen blind_claim can compensate any
    // tampered claim value; the blind row is committed sum-zero, so anything
    // other than zero here is a forgery attempt.
    if batch.blind_claim != Fp::ZERO {
        return Ok(false);
    }
    let (rows_a, opening_rows_a) = committed_opening_rows(committed_len_a, params.row_len)?;
    let (rows_b, opening_rows_b) = committed_opening_rows(committed_len_b, params.row_len)?;
    let combined_rows = rows_a
        .checked_add(rows_b)
        .ok_or(LigeroError::InvalidRowLength)?;
    // Validate every attacker-carried index and row shape before using an
    // index to gather an encoded response value.
    for (opening_a, opening_b) in openings_a.iter().zip(openings_b) {
        if opening_a.index != opening_b.index || opening_a.index >= params.codeword_len {
            return Err(LigeroError::ColumnOutOfRange);
        }
        if opening_a.column.len() != opening_rows_a || opening_b.column.len() != opening_rows_b {
            return Err(LigeroError::WrongGammaLength);
        }
    }
    let opening_indices = openings_a
        .iter()
        .map(|opening| opening.index)
        .collect::<Vec<_>>();
    // WO-P7: precompute the per-column evaluator once (circle: one basis per
    // opened column, plus the weight-inverse-folded basis) so the batch and
    // every row's weights are dot products sharing it, instead of rebuilding
    // the basis per (row, column).
    let column_eval = ClaimBatchColumnEval::new(params, &opening_indices)?;
    let batch_at_openings = column_eval.eval_message(&batch.coefficients)?;
    let weight_evaluations = evaluate_claim_weight_plan(
        claim_weight_plan(
            params,
            combined_rows,
            claims,
            gamma,
            structured_claims_enabled(),
        )?,
        &column_eval,
    )?;

    for (opening_position, (opening_a, opening_b)) in openings_a.iter().zip(openings_b).enumerate()
    {
        if let SplitOpeningAuthentication::Verify { root_a, root_b } = authentication {
            if !verify_column(root_a, opening_a).map_err(LigeroError::Merkle)?
                || !verify_column(root_b, opening_b).map_err(LigeroError::Merkle)?
            {
                return Ok(false);
            }
        }
        let blind_value = opening_a.column[rows_a + CLAIM_BLIND_ROW_OFFSET]
            + opening_b.column[rows_b + CLAIM_BLIND_ROW_OFFSET];
        let mut combined = blind_value;
        for (row, weights_at_openings) in &weight_evaluations.residual_rows {
            let value = if *row < rows_a {
                opening_a.column[*row]
            } else {
                opening_b.column[*row - rows_a]
            };
            combined = combined + weights_at_openings[opening_position] * value;
        }
        for template in &weight_evaluations.templates {
            let opened = template
                .row_scales
                .iter()
                .fold(Fp::ZERO, |acc, (row, scale)| {
                    let value = if *row < rows_a {
                        opening_a.column[*row]
                    } else {
                        opening_b.column[*row - rows_a]
                    };
                    acc + *scale * value
                });
            combined = combined + template.values[opening_position] * opened;
        }
        if batch_at_openings[opening_position] != combined {
            return Ok(false);
        }
    }

    let q_sum = claim_extraction_sum(params, &batch.coefficients);
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
    params.validate()?;
    let rows = openings
        .first()
        .map(|opening| opening.column.len())
        .ok_or(LigeroError::WrongOpeningCount)?;
    let input_len = rows
        .checked_mul(params.row_len)
        .ok_or(LigeroError::WrongPointLength)?;
    verify_input_claims_from_systematic_openings_with_len(root, params, openings, claims, input_len)
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
    if params.code != LigeroCode::Rs {
        // The circle code has no systematic columns to read values from.
        return Err(LigeroError::UnsupportedCode);
    }
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
    let total_values = rows
        .checked_mul(params.row_len)
        .ok_or(LigeroError::WrongPointLength)?;
    let input_end = input_offset
        .checked_add(input_len)
        .ok_or(LigeroError::WrongPointLength)?;
    if input_end > total_values {
        return Err(LigeroError::WrongPointLength);
    }

    let mut values = Vec::with_capacity(total_values);
    for row in 0..rows {
        for opening in &sorted {
            values.push(opening.column[row]);
        }
    }
    let values = values[input_offset..input_end].to_vec();
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

fn fresh_pad_rng() -> ChaCha20Rng {
    let mut seed = [0u8; 32];
    OsRng.fill_bytes(&mut seed);
    ChaCha20Rng::from_seed(seed)
}

fn draw_uniform_fps(rng: &mut ChaCha20Rng, count: usize) -> Vec<Fp> {
    (0..count).map(|_| Fp::random_uniform(rng)).collect()
}

pub fn quadratic_committed_len(
    committed_len: usize,
    params: LigeroParams,
    quadratic_constraints: usize,
) -> Result<usize, LigeroError> {
    params.validate()?;
    let witness_rows = committed_len.div_ceil(params.row_len);
    let quadratic_triples = quadratic_constraints.div_ceil(params.row_len);
    witness_rows
        .checked_add(
            quadratic_triples
                .checked_mul(3)
                .ok_or(LigeroError::InvalidRowLength)?,
        )
        .and_then(|rows| rows.checked_mul(params.row_len))
        .ok_or(LigeroError::InvalidRowLength)
}

pub fn quadratic_route_claims(
    committed_len: usize,
    params: LigeroParams,
    constraints: &[LigeroQuadraticConstraint],
) -> Result<Vec<LigeroLinearClaim>, LigeroError> {
    params.validate()?;
    let witness_rows = committed_len.div_ceil(params.row_len);
    let quadratic_triples = constraints.len().div_ceil(params.row_len);
    let x_start = witness_rows
        .checked_mul(params.row_len)
        .ok_or(LigeroError::InvalidQuadraticConstraint)?;
    let triple_span = quadratic_triples
        .checked_mul(params.row_len)
        .ok_or(LigeroError::InvalidQuadraticConstraint)?;
    let y_start = x_start
        .checked_add(triple_span)
        .ok_or(LigeroError::InvalidQuadraticConstraint)?;
    let z_start = y_start
        .checked_add(triple_span)
        .ok_or(LigeroError::InvalidQuadraticConstraint)?;
    z_start
        .checked_add(triple_span)
        .ok_or(LigeroError::InvalidQuadraticConstraint)?;
    let capacity = constraints
        .len()
        .checked_mul(3)
        .ok_or(LigeroError::InvalidQuadraticConstraint)?;
    let mut claims = Vec::with_capacity(capacity);
    for (index, constraint) in constraints.iter().enumerate() {
        if [constraint.x, constraint.y, constraint.z]
            .into_iter()
            .any(|offset| offset >= committed_len)
        {
            return Err(LigeroError::InvalidQuadraticConstraint);
        }
        let destinations = [
            x_start
                .checked_add(index)
                .ok_or(LigeroError::InvalidQuadraticConstraint)?,
            y_start
                .checked_add(index)
                .ok_or(LigeroError::InvalidQuadraticConstraint)?,
            z_start
                .checked_add(index)
                .ok_or(LigeroError::InvalidQuadraticConstraint)?,
        ];
        for (source, destination) in [constraint.x, constraint.y, constraint.z]
            .into_iter()
            .zip(destinations)
        {
            claims.push(LigeroLinearClaim::affine(
                vec![
                    LigeroLinearTerm {
                        offset: source,
                        len: 1,
                        point: Vec::new(),
                        coefficient: -Fp::ONE,
                    },
                    LigeroLinearTerm {
                        offset: destination,
                        len: 1,
                        point: Vec::new(),
                        coefficient: Fp::ONE,
                    },
                ],
                Fp::ZERO,
            ));
        }
    }
    Ok(claims)
}

pub fn verify_quadratic_batch(
    root: [u8; 32],
    params: LigeroParams,
    committed_len: usize,
    quadratic_constraints: usize,
    openings: &[ColumnOpening],
    batch: &LigeroQuadraticBatch,
    challenges: &[Fp],
) -> Result<bool, LigeroError> {
    params.validate()?;
    if quadratic_constraints == 0 {
        return Ok(batch.quotient.is_empty() && challenges.is_empty());
    }
    params.validate_quadratic()?;
    if params.code != LigeroCode::Circle {
        return Err(LigeroError::UnsupportedCode);
    }
    if openings.len() != params.openings {
        return Err(LigeroError::WrongOpeningCount);
    }
    let quadratic_triples = quadratic_constraints.div_ceil(params.row_len);
    if challenges.len() != quadratic_triples {
        return Err(LigeroError::WrongGammaLength);
    }
    let quotient_bound = params.quadratic_degree_bound() - params.row_len;
    if batch.quotient.len() != quotient_bound {
        return Err(LigeroError::WrongClaimLength);
    }
    let witness_rows = committed_len.div_ceil(params.row_len);
    let expanded_committed_len =
        quadratic_committed_len(committed_len, params, quadratic_constraints)?;
    let (committed_rows, expected_rows) =
        committed_opening_rows(expanded_committed_len, params.row_len)?;
    let geom = params.circle_geom().expect("validated circle params");
    let response_coefficients =
        circle_multiply_data_vanishing(geom, &batch.quotient, params.quadratic_degree_bound())
            .map_err(LigeroError::Circle)?;
    let response_codeword = circle_encode(
        geom,
        &response_coefficients,
        params.quadratic_degree_bound(),
    )
    .map_err(LigeroError::Circle)?;
    let x_start = witness_rows;
    let y_start = x_start + quadratic_triples;
    let z_start = y_start + quadratic_triples;

    for opening in openings {
        if opening.index >= params.codeword_len {
            return Err(LigeroError::ColumnOutOfRange);
        }
        if opening.column.len() != expected_rows {
            return Err(LigeroError::WrongGammaLength);
        }
        if !verify_column(root, opening).map_err(LigeroError::Merkle)? {
            return Ok(false);
        }
        let mut combined = opening.column[committed_rows + QUADRATIC_BLIND_ROW_OFFSET];
        for (index, challenge) in challenges.iter().copied().enumerate() {
            let x = opening.column[x_start + index];
            let y = opening.column[y_start + index];
            let z = opening.column[z_start + index];
            combined = combined + challenge * (z - x * y);
        }
        if response_codeword[opening.index] != combined {
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
    let expected_rows = gamma
        .len()
        .checked_add(LIGERO_AUXILIARY_ROW_COUNT)
        .ok_or(LigeroError::WrongGammaLength)?;
    for opening in openings {
        if opening.index >= params.codeword_len {
            return Err(LigeroError::ColumnOutOfRange);
        }
        if opening.column.len() != expected_rows {
            return Err(LigeroError::WrongGammaLength);
        }
        if !verify_column(root, opening).map_err(LigeroError::Merkle)? {
            return Ok(false);
        }
        let mask_value = opening.column[gamma.len() + PROXIMITY_MASK_ROW_OFFSET];
        let combined = gamma
            .iter()
            .copied()
            .zip(&opening.column)
            .fold(mask_value, |acc, (coeff, value)| acc + coeff * *value);
        let expected = code_evaluate(params, &claim.combined_row, opening.index)?;
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
    // C-p4b-blind-claim: see verify_split_claim_batch.
    if batch.blind_claim != Fp::ZERO {
        return Ok(false);
    }
    let (committed_rows, expected_rows) = committed_opening_rows(committed_len, params.row_len)?;
    for opening in openings {
        if opening.index >= params.codeword_len {
            return Err(LigeroError::ColumnOutOfRange);
        }
        if opening.column.len() != expected_rows {
            return Err(LigeroError::WrongGammaLength);
        }
    }
    let batched_row_weights = batched_row_weights(params, committed_rows, claims, gamma)?;
    let opening_indices = openings
        .iter()
        .map(|opening| opening.index)
        .collect::<Vec<_>>();
    // WO-P7: see verify_split_claim_batch — one per-column evaluator shared by
    // the batch coefficients and every row's weights.
    let column_eval = ClaimBatchColumnEval::new(params, &opening_indices)?;
    let batch_at_openings = column_eval.eval_message(&batch.coefficients)?;
    let row_weights_at_openings = batched_row_weights
        .iter()
        .map(|(row, weights)| Ok::<_, LigeroError>((*row, column_eval.eval_weights(weights)?)))
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
        let blind_value = opening.column[committed_rows + CLAIM_BLIND_ROW_OFFSET];
        let mut combined = blind_value;
        for (row, weights_at_openings) in &row_weights_at_openings {
            combined = combined + weights_at_openings[opening_position] * opening.column[*row];
        }
        if batch_at_openings[opening_position] != combined {
            return Ok(false);
        }
    }

    let q_sum = claim_extraction_sum(params, &batch.coefficients);
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
    if claim.terms.is_empty() {
        return Err(LigeroError::WrongPointLength);
    }
    let committed_cells = committed_rows
        .checked_mul(params.row_len)
        .ok_or(LigeroError::WrongPointLength)?;
    for term in &claim.terms {
        if term.len == 0 {
            return Err(LigeroError::WrongPointLength);
        }
        let expected_point_len = term
            .len
            .checked_next_power_of_two()
            .ok_or(LigeroError::WrongPointLength)?
            .ilog2() as usize;
        if term.point.len() != expected_point_len {
            return Err(LigeroError::WrongPointLength);
        }
        if term
            .offset
            .checked_add(term.len)
            .is_none_or(|end| end > committed_cells)
        {
            return Err(LigeroError::WrongPointLength);
        }
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
        // WO-P1: expand each term's eq bit-product into a dense 2^m tensor
        // once by doubling (O(2^m) instead of m mults per cell), then scatter
        // gamma·term_coefficient·eq[local] into the row/column windows.
        for term in &claim.terms {
            let scale = coeff * term.coefficient;
            let eq = eq_tensor(&term.point);
            for local in 0..term.len {
                let global = term.offset + local;
                let cell = &mut rows[global / params.row_len][global % params.row_len];
                *cell = *cell + scale * eq[local];
            }
        }
    }

    Ok(rows
        .into_iter()
        .enumerate()
        .filter(|(_, weights)| weights.iter().any(|&weight| weight != Fp::ZERO))
        .collect())
}

/// Evaluates a message vector at one codeword position, per the params' code.
fn code_evaluate(params: LigeroParams, message: &[Fp], index: usize) -> Result<Fp, LigeroError> {
    match params.code {
        LigeroCode::Rs => rs_evaluate(message, params.codeword_len, index).map_err(LigeroError::Rs),
        LigeroCode::Circle => {
            let geom = params.circle_geom().expect("validated circle params");
            circle_evaluate(geom, message, index).map_err(LigeroError::Circle)
        }
    }
}

/// RS prover claim-batch weight evaluations (the RS `claim_batch`/
/// `split_claim_batch` paths). The circle prover uses `circle_claim_batch` and
/// the circle *verifier* uses [`ClaimBatchColumnEval`] (WO-P7), so this is
/// RS-only.
fn weight_evaluations(
    params: LigeroParams,
    weights: &[Fp],
    indices: impl IntoIterator<Item = usize>,
) -> Result<Vec<Fp>, LigeroError> {
    debug_assert_eq!(params.code, LigeroCode::Rs, "weight_evaluations is RS-only");
    indices
        .into_iter()
        .map(|index| rs_evaluate(weights, params.codeword_len, index).map_err(LigeroError::Rs))
        .collect()
}

/// Per-opened-column evaluator for the claim-batch verifier. Both the batch
/// coefficients and every per-row weight interpolant have to be evaluated at
/// the same `t` opened columns.
///
/// WO-C2: for the circle code, one full-codeword circle FFT
/// (`(n/2)·log₂n ≈ 24.6k mults at ℓ=256`) followed by gathering the opened
/// positions is cheaper than `t` per-column dot products
/// (`t · claim_degree_bound ≈ 176 · 256`), and the cost no longer scales with
/// `t`. `circle_encode(coeffs)[index]` is byte-identical to the previous
/// per-column basis dot (`encode_matches_direct_basis_evaluation` pins
/// `codeword[index] == circle_evaluate(index)`), so soundness is unchanged.
/// The dominant cost is the per-row weight FFT (`combined_rows` of them), which
/// this replaces `combined_rows · t` per-column dots with. For RS it holds the
/// indices and defers to `rs_evaluate` (already cheap, no per-call redundancy).
enum ClaimBatchColumnEval {
    Rs {
        codeword_len: usize,
        indices: Vec<usize>,
    },
    Circle {
        indices: Vec<usize>,
        geom: CircleGeom,
    },
}

impl ClaimBatchColumnEval {
    fn new(params: LigeroParams, indices: &[usize]) -> Result<Self, LigeroError> {
        match params.code {
            LigeroCode::Rs => Ok(Self::Rs {
                codeword_len: params.codeword_len,
                indices: indices.to_vec(),
            }),
            LigeroCode::Circle => {
                let geom = params.circle_geom().expect("validated circle params");
                Ok(Self::Circle {
                    indices: indices.to_vec(),
                    geom,
                })
            }
        }
    }

    /// Evaluates a coefficient vector (`≤ degree_bound` coeffs) at every opened
    /// column, one entry per opening (same order as `indices`).
    fn eval_coeffs(&self, coeffs: &[Fp], degree_bound: usize) -> Result<Vec<Fp>, LigeroError> {
        match self {
            Self::Rs {
                codeword_len,
                indices,
            } => indices
                .iter()
                .map(|&index| rs_evaluate(coeffs, *codeword_len, index).map_err(LigeroError::Rs))
                .collect(),
            Self::Circle { indices, geom } => {
                let codeword =
                    circle_encode(*geom, coeffs, degree_bound).map_err(LigeroError::Circle)?;
                Ok(indices.iter().map(|&index| codeword[index]).collect())
            }
        }
    }

    /// Evaluates the batch coefficients (`claim_degree_bound` coeffs) at every
    /// opened column. `degree_bound == message.len()` here (`circle_encode`
    /// zero-pads to `codeword_len` regardless; the bound is only a validation
    /// guard), so the batch is evaluated exactly at its own length.
    fn eval_message(&self, message: &[Fp]) -> Result<Vec<Fp>, LigeroError> {
        self.eval_coeffs(message, message.len())
    }

    /// Evaluates a row's batched weights at every opened column. For RS the
    /// weights are themselves the codeword message; for the circle code the
    /// weights interpolate to their `F_{data_slots}` coefficients in one window
    /// IFFT (`O(d log d)` — the window is a twin-coset FFT domain), then a
    /// single full-codeword FFT evaluates them at every opening (WO-C2).
    fn eval_weights(&self, weights: &[Fp]) -> Result<Vec<Fp>, LigeroError> {
        match self {
            Self::Rs { .. } => self.eval_message(weights),
            Self::Circle { geom, .. } => {
                let coeffs = circle_weight_coeffs(*geom, weights).map_err(LigeroError::Circle)?;
                self.eval_coeffs(&coeffs, geom.data_slots)
            }
        }
    }
}

/// The claim-batch extraction functional: Σ over the systematic prefix for
/// RS, Σ over the data-window points for the circle code (Q-025 §3).
fn claim_extraction_sum(params: LigeroParams, coefficients: &[Fp]) -> Fp {
    match params.code {
        LigeroCode::Rs => coefficients[..params.row_len]
            .iter()
            .copied()
            .fold(Fp::ZERO, |acc, value| acc + value),
        LigeroCode::Circle => {
            let geom = params.circle_geom().expect("validated circle params");
            circle_data_sum(geom, coefficients)
        }
    }
}

/// Per-cell affine weight, kept as the independent test reference that
/// `batched_row_weights_match_separate_claim_weights` cross-checks the tensor
/// scatter against (WO-P1: the production path uses [`eq_tensor`]).
#[cfg(test)]
fn linear_claim_weight(claim: &LigeroLinearClaim, global_index: usize) -> Fp {
    claim.terms.iter().fold(Fp::ZERO, |acc, term| {
        acc + term.coefficient * linear_term_weight(term, global_index)
    })
}

#[cfg(test)]
fn linear_term_weight(term: &LigeroLinearTerm, global_index: usize) -> Fp {
    if global_index < term.offset || global_index >= term.offset + term.len {
        return Fp::ZERO;
    }
    let local = global_index - term.offset;
    term.point
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

/// The dense eq-tensor of `point`: `eq[i] = Π_b (i_b ? point[b] : 1 − point[b])`
/// over bits `b` of `i`, built by doubling in O(2^m). `eq[local]` equals the
/// per-cell `linear_term_weight` bit-product for `local < 2^m`.
fn eq_tensor(point: &[Fp]) -> Vec<Fp> {
    let mut eq = vec![Fp::ONE; 1usize << point.len()];
    let mut half = 1usize;
    for &challenge in point {
        let one_minus = Fp::ONE - challenge;
        for i in 0..half {
            let hi = eq[i] * challenge;
            eq[i] = eq[i] * one_minus;
            eq[i + half] = hi;
        }
        half <<= 1;
    }
    eq
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
            code: LigeroCode::Rs,
        }
    }

    fn claim_for(values: &[Fp], offset: usize, point: Vec<Fp>) -> LigeroLinearClaim {
        let len = 1usize << point.len();
        let value = Mle::new(values[offset..offset + len].to_vec())
            .eval_at(&point)
            .unwrap();
        LigeroLinearClaim::mle(offset, len, point, value)
    }

    fn cell_term(offset: usize, coefficient: Fp) -> LigeroLinearTerm {
        LigeroLinearTerm {
            offset,
            len: 1,
            point: Vec::new(),
            coefficient,
        }
    }

    fn make_claim_blind_non_kernel(commitment: &mut LigeroCommitment) {
        let params = commitment.params;
        let row = commitment.claim_blind_row;
        match params.code {
            LigeroCode::Rs => {
                let mut message =
                    commitment.encoded_rows[row][..params.claim_degree_bound()].to_vec();
                message[0] = message[0] + Fp::ONE;
                commitment.encoded_rows[row] =
                    rs_encode_padded(&message, params.claim_degree_bound(), params.codeword_len)
                        .expect("valid adversarial RS row");
            }
            LigeroCode::Circle => {
                let geom = params.circle_geom().expect("validated circle params");
                let coefficients = &mut commitment.coefficient_rows[row];
                coefficients[0] = coefficients[0] + Fp::ONE;
                commitment.encoded_rows[row] =
                    circle_encode(geom, coefficients, params.claim_degree_bound())
                        .expect("valid adversarial Circle row");
            }
        }
        commitment.merkle =
            commit_columns(&commitment.encoded_rows).expect("recommit adversarial row");
    }

    #[test]
    fn batched_row_weights_match_separate_claim_weights() {
        let params = small_params();
        let claims = vec![
            LigeroLinearClaim::mle(
                0,
                8,
                vec![Fp::from_u64(3), Fp::from_u64(5), Fp::from_u64(7)],
                Fp::ZERO,
            ),
            LigeroLinearClaim::mle(4, 4, vec![Fp::from_u64(11), Fp::from_u64(13)], Fp::ZERO),
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
    fn structured_claim_plan_matches_dense_for_shifts_lengths_and_overlaps() {
        let params = v4_circle_params();
        let committed_rows = 100;
        let shapes: [(usize, usize); 9] = [
            (0, 8192),
            (1, 2048),
            (255, 777),
            (512 + 127, 512),
            (3000, 511),
            (4001, 257),
            (5000 + 255, 256),
            (6000 + 127, 255),
            (7000, 128),
        ];
        let mut claims = shapes
            .into_iter()
            .enumerate()
            .map(|(claim_index, (offset, len))| {
                let point = (0..len.next_power_of_two().ilog2())
                    .map(|bit| Fp::from_u64(3 + claim_index as u64 * 17 + bit as u64 * 5))
                    .collect();
                LigeroLinearClaim::mle(offset, len, point, Fp::ZERO)
            })
            .collect::<Vec<_>>();
        claims.push(LigeroLinearClaim::affine(
            vec![
                LigeroLinearTerm {
                    offset: 8_000,
                    len: 8_192,
                    point: (0..13).map(|bit| Fp::from_u64(71 + bit * 3)).collect(),
                    coefficient: Fp::from_u64(3),
                },
                LigeroLinearTerm {
                    offset: 20_000,
                    len: 2_048,
                    point: (0..11).map(|bit| Fp::from_u64(113 + bit * 5)).collect(),
                    coefficient: -Fp::from_u64(5),
                },
            ],
            Fp::ZERO,
        ));
        let gamma = (0..claims.len())
            .map(|index| Fp::from_u64(101 + index as u64 * 13))
            .collect::<Vec<_>>();

        let dense = batched_row_weights(params, committed_rows, &claims, &gamma).unwrap();
        let plan = claim_weight_plan(params, committed_rows, &claims, &gamma, true).unwrap();
        assert!(!plan.templates.is_empty(), "long claims must be factored");
        let mut reconstructed = vec![vec![Fp::ZERO; params.row_len]; committed_rows];
        for (row, weights) in plan.residual_rows {
            for (out, weight) in reconstructed[row].iter_mut().zip(weights) {
                *out = *out + weight;
            }
        }
        for template in plan.templates {
            for (row, scale) in template.row_scales {
                for (out, weight) in reconstructed[row].iter_mut().zip(&template.values) {
                    *out = *out + scale * *weight;
                }
            }
        }
        let reconstructed = reconstructed
            .into_iter()
            .enumerate()
            .filter(|(_, weights)| weights.iter().any(|&weight| weight != Fp::ZERO))
            .collect::<Vec<_>>();
        assert_eq!(reconstructed, dense);
    }

    #[test]
    fn parallel_claim_weight_evaluation_matches_serial_order_and_values() {
        let params = v4_circle_params();
        let committed_rows = 8;
        let claims = vec![
            LigeroLinearClaim::mle(
                0,
                1024,
                (0..10).map(|bit| Fp::from_u64(3 + bit * 5)).collect(),
                Fp::ZERO,
            ),
            LigeroLinearClaim::mle(
                1024,
                256,
                (0..8).map(|bit| Fp::from_u64(71 + bit * 7)).collect(),
                Fp::ZERO,
            ),
        ];
        let gamma = [Fp::from_u64(131), Fp::from_u64(137)];
        let indices = (0..params.openings)
            .map(|index| (index * 19 + 3) % params.codeword_len)
            .collect::<Vec<_>>();
        let column_eval = ClaimBatchColumnEval::new(params, &indices).unwrap();
        let serial = evaluate_claim_weight_plan_serial(
            claim_weight_plan(params, committed_rows, &claims, &gamma, true).unwrap(),
            &column_eval,
        )
        .unwrap();
        let parallel = evaluate_claim_weight_plan(
            claim_weight_plan(params, committed_rows, &claims, &gamma, true).unwrap(),
            &column_eval,
        )
        .unwrap();

        assert!(
            !serial.residual_rows.is_empty() && !serial.templates.is_empty(),
            "fixture must exercise both ordered collections"
        );
        assert_eq!(parallel.residual_rows, serial.residual_rows);
        assert_eq!(parallel.templates.len(), serial.templates.len());
        for (parallel, serial) in parallel.templates.iter().zip(&serial.templates) {
            assert_eq!(parallel.values, serial.values);
            assert_eq!(parallel.row_scales, serial.row_scales);
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
    fn claim_blind_kernel_check_accepts_honest_and_rejects_non_kernel_rows() {
        for params in [small_params(), v4_circle_params()] {
            let values = (0..params.row_len + 3)
                .map(|value| Fp::from_u64(value as u64 + 1))
                .collect::<Vec<_>>();
            let challenge = Fp::from_u64(17);
            let indices = (0..params.openings)
                .map(|index| match params.code {
                    LigeroCode::Rs => params.row_len + index,
                    LigeroCode::Circle => index,
                })
                .collect::<Vec<_>>();

            let commitment = commit_witness(&values, params).unwrap();
            let check = commitment.claim_blind_check(challenge);
            let openings = commitment.open_columns(&indices).unwrap();
            assert_eq!(claim_extraction_sum(params, &check.combined_row), Fp::ZERO);
            assert!(verify_claim_blind_check(
                commitment.root(),
                params,
                values.len(),
                &openings,
                &check,
                challenge,
            )
            .unwrap());

            let mut adversarial = commitment;
            make_claim_blind_non_kernel(&mut adversarial);
            let adversarial_check = adversarial.claim_blind_check(challenge);
            let adversarial_openings = adversarial.open_columns(&indices).unwrap();
            assert_ne!(
                claim_extraction_sum(params, &adversarial_check.combined_row),
                Fp::ZERO,
                "nonzero challenge must expose a non-kernel claim blind"
            );
            assert!(!verify_claim_blind_check(
                adversarial.root(),
                params,
                values.len(),
                &adversarial_openings,
                &adversarial_check,
                challenge,
            )
            .unwrap());
        }
    }

    #[test]
    fn split_claim_blind_kernel_check_binds_both_roots() {
        let params = small_params();
        let values_a = (0..12)
            .map(|value| Fp::from_u64(value + 1))
            .collect::<Vec<_>>();
        let values_b = (0..9)
            .map(|value| Fp::from_u64(value + 101))
            .collect::<Vec<_>>();
        let commitment_a = commit_witness(&values_a, params).unwrap();
        let commitment_b = commit_witness(&values_b, params).unwrap();
        let challenge = Fp::from_u64(19);
        let indices = [8, 13, 21];
        let openings_a = commitment_a.open_columns(&indices).unwrap();
        let openings_b = commitment_b.open_columns(&indices).unwrap();
        let check = commitment_a
            .split_claim_blind_check(&commitment_b, challenge)
            .unwrap();
        assert!(verify_split_claim_blind_check(
            commitment_a.root(),
            commitment_b.root(),
            params,
            values_a.len(),
            values_b.len(),
            &openings_a,
            &openings_b,
            &check,
            challenge,
        )
        .unwrap());

        let mut adversarial_a = commitment_a;
        make_claim_blind_non_kernel(&mut adversarial_a);
        let adversarial_openings_a = adversarial_a.open_columns(&indices).unwrap();
        let adversarial_check = adversarial_a
            .split_claim_blind_check(&commitment_b, challenge)
            .unwrap();
        assert!(!verify_split_claim_blind_check(
            adversarial_a.root(),
            commitment_b.root(),
            params,
            values_a.len(),
            values_b.len(),
            &adversarial_openings_a,
            &openings_b,
            &adversarial_check,
            challenge,
        )
        .unwrap());
    }

    #[test]
    fn claim_blind_kernel_response_is_fresh_for_the_same_witness() {
        let params = small_params();
        let values = (0..12)
            .map(|value| Fp::from_u64(value + 1))
            .collect::<Vec<_>>();
        let challenge = Fp::from_u64(23);
        let first = commit_witness(&values, params).unwrap();
        let second = commit_witness(&values, params).unwrap();
        let first_check = first.claim_blind_check(challenge);
        let second_check = second.claim_blind_check(challenge);

        assert_ne!(first.root(), second.root());
        assert_ne!(
            first_check, second_check,
            "the independent kernel mask must hide repeated-witness responses"
        );
        assert_eq!(
            claim_extraction_sum(params, &first_check.combined_row),
            Fp::ZERO
        );
        assert_eq!(
            claim_extraction_sum(params, &second_check.combined_row),
            Fp::ZERO
        );
    }

    #[test]
    fn malformed_params_and_claim_lengths_return_errors_without_panicking() {
        let mut invalid_params = small_params();
        invalid_params.row_len = 0;
        let params_verdict = std::panic::catch_unwind(|| {
            verify_quadratic_batch(
                [0u8; 32],
                invalid_params,
                0,
                0,
                &[],
                &LigeroQuadraticBatch::default(),
                &[],
            )
        });
        assert!(params_verdict.is_ok(), "invalid params must not panic");
        assert_eq!(params_verdict.unwrap(), Err(LigeroError::InvalidRowLength));

        let oversized_claim = LigeroLinearClaim::mle(0, usize::MAX, Vec::new(), Fp::ZERO);
        let claim_verdict =
            std::panic::catch_unwind(|| validate_linear_claim(small_params(), 1, &oversized_claim));
        assert!(claim_verdict.is_ok(), "oversized claims must not panic");
        assert_eq!(claim_verdict.unwrap(), Err(LigeroError::WrongPointLength));
    }

    #[test]
    fn split_circle_claim_rejects_out_of_range_index_without_panicking() {
        let params = v2_circle_params();
        let values_a = (0..200)
            .map(|value| Fp::from_u64(value + 1))
            .collect::<Vec<_>>();
        let values_b = (0..200)
            .map(|value| Fp::from_u64(value + 501))
            .collect::<Vec<_>>();
        let commitment_a = commit_witness(&values_a, params).unwrap();
        let commitment_b = commit_witness(&values_b, params).unwrap();
        let claims = [LigeroLinearClaim::mle(0, 1, Vec::new(), values_a[0])];
        let gamma = [Fp::from_u64(29)];
        let batch = commitment_a
            .split_claim_batch(&commitment_b, &claims, &gamma)
            .unwrap();
        let indices = (0..params.openings).collect::<Vec<_>>();
        let mut openings_a = commitment_a.open_columns(&indices).unwrap();
        let mut openings_b = commitment_b.open_columns(&indices).unwrap();
        openings_a[0].index = params.codeword_len;
        openings_b[0].index = params.codeword_len;

        let verdict = std::panic::catch_unwind(|| {
            verify_split_claim_batch(
                commitment_a.root(),
                commitment_b.root(),
                params,
                values_a.len(),
                values_b.len(),
                &openings_a,
                &openings_b,
                &batch,
                &claims,
                &gamma,
            )
        });
        assert!(verdict.is_ok(), "malformed proof input must not panic");
        assert_eq!(verdict.unwrap(), Err(LigeroError::ColumnOutOfRange));
    }

    #[test]
    fn affine_claim_accepts_equal_private_cells_and_rejects_different_cells() {
        let params = small_params();
        let claim = LigeroLinearClaim::affine(
            vec![cell_term(1, Fp::ONE), cell_term(9, -Fp::ONE)],
            Fp::ZERO,
        );
        let gamma = [Fp::from_u64(13)];
        let indices = [8, 13, 21];

        let mut equal_values = (0..12)
            .map(|value| Fp::from_u64(value + 1))
            .collect::<Vec<_>>();
        equal_values[9] = equal_values[1];
        let equal_commitment = commit_witness(&equal_values, params).unwrap();
        let equal_batch = equal_commitment
            .claim_batch(std::slice::from_ref(&claim), &gamma)
            .unwrap();
        let equal_openings = equal_commitment.open_columns(&indices).unwrap();
        assert!(verify_claim_batch(
            equal_commitment.root(),
            params,
            equal_values.len(),
            &equal_openings,
            &equal_batch,
            std::slice::from_ref(&claim),
            &gamma,
        )
        .unwrap());

        let mut different_values = equal_values;
        different_values[9] = different_values[9] + Fp::ONE;
        let different_commitment = commit_witness(&different_values, params).unwrap();
        let different_batch = different_commitment
            .claim_batch(std::slice::from_ref(&claim), &gamma)
            .unwrap();
        let different_openings = different_commitment.open_columns(&indices).unwrap();
        assert!(!verify_claim_batch(
            different_commitment.root(),
            params,
            different_values.len(),
            &different_openings,
            &different_batch,
            std::slice::from_ref(&claim),
            &gamma,
        )
        .unwrap());
    }

    #[test]
    fn split_affine_claim_binds_private_cells_across_roots() {
        let params = small_params();
        let values_a = (0..12)
            .map(|value| Fp::from_u64(value + 1))
            .collect::<Vec<_>>();
        let mut values_b = (0..12)
            .map(|value| Fp::from_u64(value + 101))
            .collect::<Vec<_>>();
        values_b[2] = values_a[7];
        let commitment_a = commit_witness(&values_a, params).unwrap();
        let commitment_b = commit_witness(&values_b, params).unwrap();
        let b_offset = commitment_a.witness_rows * params.row_len + 2;
        let claim = LigeroLinearClaim::affine(
            vec![cell_term(7, Fp::ONE), cell_term(b_offset, -Fp::ONE)],
            Fp::ZERO,
        );
        let gamma = [Fp::from_u64(17)];
        let batch = commitment_a
            .split_claim_batch(&commitment_b, std::slice::from_ref(&claim), &gamma)
            .unwrap();
        let indices = [8, 13, 21];
        let openings_a = commitment_a.open_columns(&indices).unwrap();
        let openings_b = commitment_b.open_columns(&indices).unwrap();
        assert!(verify_split_claim_batch(
            commitment_a.root(),
            commitment_b.root(),
            params,
            values_a.len(),
            values_b.len(),
            &openings_a,
            &openings_b,
            &batch,
            std::slice::from_ref(&claim),
            &gamma,
        )
        .unwrap());

        values_b[2] = values_b[2] + Fp::ONE;
        let different_b = commit_witness(&values_b, params).unwrap();
        let different_batch = commitment_a
            .split_claim_batch(&different_b, std::slice::from_ref(&claim), &gamma)
            .unwrap();
        let different_openings_b = different_b.open_columns(&indices).unwrap();
        assert!(!verify_split_claim_batch(
            commitment_a.root(),
            different_b.root(),
            params,
            values_a.len(),
            values_b.len(),
            &openings_a,
            &different_openings_b,
            &different_batch,
            std::slice::from_ref(&claim),
            &gamma,
        )
        .unwrap());
    }

    #[test]
    fn authenticated_split_claim_path_matches_public_and_rejects_tamper() {
        let params = small_params();
        let values_a = (0..12)
            .map(|value| Fp::from_u64(value + 1))
            .collect::<Vec<_>>();
        let mut values_b = (0..12)
            .map(|value| Fp::from_u64(value + 101))
            .collect::<Vec<_>>();
        values_b[2] = values_a[7];
        let commitment_a = commit_witness(&values_a, params).unwrap();
        let commitment_b = commit_witness(&values_b, params).unwrap();
        let b_offset = commitment_a.witness_rows * params.row_len + 2;
        let claim = LigeroLinearClaim::affine(
            vec![cell_term(7, Fp::ONE), cell_term(b_offset, -Fp::ONE)],
            Fp::ZERO,
        );
        let claims = [claim];
        let gamma = [Fp::from_u64(17)];
        let batch = commitment_a
            .split_claim_batch(&commitment_b, &claims, &gamma)
            .unwrap();
        let proximity_gamma = (0..commitment_a.witness_rows + commitment_b.witness_rows)
            .map(|index| Fp::from_u64(31 + index as u64))
            .collect::<Vec<_>>();
        let proximity_claim = commitment_a
            .split_proximity_claim(&commitment_b, &proximity_gamma)
            .unwrap();
        let indices = [8, 13, 21];
        let openings_a = commitment_a.open_columns(&indices).unwrap();
        let openings_b = commitment_b.open_columns(&indices).unwrap();

        let public = verify_split_claim_batch(
            commitment_a.root(),
            commitment_b.root(),
            params,
            values_a.len(),
            values_b.len(),
            &openings_a,
            &openings_b,
            &batch,
            &claims,
            &gamma,
        )
        .unwrap();
        let authenticated = verify_and_authenticate_split_openings(
            commitment_a.root(),
            commitment_b.root(),
            params,
            values_a.len(),
            values_b.len(),
            &openings_a,
            &openings_b,
            &proximity_claim,
            &proximity_gamma,
        )
        .unwrap()
        .expect("honest split openings authenticate");
        let reused =
            verify_authenticated_split_claim_batch(authenticated, &batch, &claims, &gamma).unwrap();
        assert_eq!(reused, public);
        assert!(reused);

        let mut tampered_batch = batch.clone();
        tampered_batch.coefficients[0] = tampered_batch.coefficients[0] + Fp::ONE;
        let public_tamper = verify_split_claim_batch(
            commitment_a.root(),
            commitment_b.root(),
            params,
            values_a.len(),
            values_b.len(),
            &openings_a,
            &openings_b,
            &tampered_batch,
            &claims,
            &gamma,
        )
        .unwrap();
        let authenticated = verify_and_authenticate_split_openings(
            commitment_a.root(),
            commitment_b.root(),
            params,
            values_a.len(),
            values_b.len(),
            &openings_a,
            &openings_b,
            &proximity_claim,
            &proximity_gamma,
        )
        .unwrap()
        .expect("batch tamper does not alter opening authentication");
        let reused_tamper =
            verify_authenticated_split_claim_batch(authenticated, &tampered_batch, &claims, &gamma)
                .unwrap();
        assert_eq!(reused_tamper, public_tamper);
        assert!(!reused_tamper);

        let mut tampered_openings_a = openings_a.clone();
        tampered_openings_a[0].column[0] = tampered_openings_a[0].column[0] + Fp::ONE;
        assert!(verify_and_authenticate_split_openings(
            commitment_a.root(),
            commitment_b.root(),
            params,
            values_a.len(),
            values_b.len(),
            &tampered_openings_a,
            &openings_b,
            &proximity_claim,
            &proximity_gamma,
        )
        .unwrap()
        .is_none());

        let mut wrong_root_b = commitment_b.root();
        wrong_root_b[0] ^= 1;
        assert!(verify_and_authenticate_split_openings(
            commitment_a.root(),
            wrong_root_b,
            params,
            values_a.len(),
            values_b.len(),
            &openings_a,
            &openings_b,
            &proximity_claim,
            &proximity_gamma,
        )
        .unwrap()
        .is_none());
    }

    #[test]
    fn claim_batch_rejects_compensated_value_tamper() {
        // C-p4b-blind-claim forgery: tamper a claim value and send the
        // blind_claim that re-balances the q_sum identity. Pre-fix this
        // verified; it must reject now and forever.
        let params = small_params();
        let values = (0..12)
            .map(|value| Fp::from_u64(value + 1))
            .collect::<Vec<_>>();
        let claims = vec![
            claim_for(&values, 0, vec![Fp::from_u64(3), Fp::from_u64(5)]),
            claim_for(&values, 4, vec![Fp::from_u64(7), Fp::from_u64(11)]),
        ];
        let gamma = [Fp::from_u64(13), Fp::from_u64(17)];
        let commitment = commit_witness(&values, params).unwrap();
        let batch = commitment.claim_batch(&claims, &gamma).unwrap();
        let openings = commitment.open_columns(&[8, 13, 21]).unwrap();

        // The committed blind row is sum-zero, so the honest scalar is zero.
        assert_eq!(batch.blind_claim, Fp::ZERO);
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

        let mut forged_claims = claims.clone();
        forged_claims[0].value = forged_claims[0].value + Fp::ONE;
        let mut forged_batch = batch;
        forged_batch.blind_claim = Fp::ZERO - gamma[0];
        assert!(!verify_claim_batch(
            commitment.root(),
            params,
            values.len(),
            &openings,
            &forged_batch,
            &forged_claims,
            &gamma,
        )
        .unwrap());
    }

    fn circle_claim_batch_roundtrip_body(params: LigeroParams) {
        let values = (0..200)
            .map(|value| Fp::from_u64(value + 1))
            .collect::<Vec<_>>();
        let claims = vec![
            claim_for(&values, 0, vec![Fp::from_u64(3), Fp::from_u64(5)]),
            claim_for(&values, 64, vec![Fp::from_u64(7), Fp::from_u64(11)]),
        ];
        let gamma = [Fp::from_u64(13), Fp::from_u64(17)];
        let commitment = commit_witness(&values, params).unwrap();
        let batch = commitment.claim_batch(&claims, &gamma).unwrap();
        assert_eq!(batch.coefficients.len(), params.claim_degree_bound());
        assert_eq!(batch.blind_claim, Fp::ZERO);
        let indices = (0..params.openings).map(|i| i * 12 + 1).collect::<Vec<_>>();
        let openings = commitment.open_columns(&indices).unwrap();

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

        // Compensated forgery: tampered value + rebalancing blind_claim.
        let mut forged_claims = claims.clone();
        forged_claims[0].value = forged_claims[0].value + Fp::ONE;
        let mut forged_batch = batch.clone();
        forged_batch.blind_claim = Fp::ZERO - gamma[0];
        assert!(!verify_claim_batch(
            commitment.root(),
            params,
            values.len(),
            &openings,
            &forged_batch,
            &forged_claims,
            &gamma,
        )
        .unwrap());

        // Uncompensated value tamper fails the extraction functional.
        assert!(!verify_claim_batch(
            commitment.root(),
            params,
            values.len(),
            &openings,
            &batch,
            &forged_claims,
            &gamma,
        )
        .unwrap());
    }

    /// WO-P7 byte-identity of the check: the new per-column basis evaluator
    /// ([`ClaimBatchColumnEval`]) must reproduce, element-for-element, the OLD
    /// verifier evaluation path (per-column `circle_evaluate` of the batch and of
    /// each row's `circle_weight_coeffs` interpolant) — same batch-at-column
    /// values, same per-row weights-at-column values, same accept, same q_sum.
    fn circle_claim_batch_byte_identity_body(params: LigeroParams) {
        let geom = params.circle_geom().unwrap();
        let values = (0..200).map(|v| Fp::from_u64(v + 1)).collect::<Vec<_>>();
        let claims = vec![
            claim_for(&values, 0, vec![Fp::from_u64(3), Fp::from_u64(5)]),
            claim_for(&values, 64, vec![Fp::from_u64(7), Fp::from_u64(11)]),
        ];
        let gamma = [Fp::from_u64(13), Fp::from_u64(17)];
        let commitment = commit_witness(&values, params).unwrap();
        let batch = commitment.claim_batch(&claims, &gamma).unwrap();
        let indices = (0..params.openings).map(|i| i * 12 + 1).collect::<Vec<_>>();

        // NEW path.
        let column_eval = ClaimBatchColumnEval::new(params, &indices).unwrap();
        let new_batch_at = column_eval.eval_message(&batch.coefficients).unwrap();

        // OLD path: direct per-column basis recompute.
        let old_batch_at = indices
            .iter()
            .map(|&i| circle_evaluate(geom, &batch.coefficients, i).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(new_batch_at, old_batch_at, "batch-at-column mismatch");

        let committed_rows = values.len().div_ceil(params.row_len);
        for (_row, weights) in batched_row_weights(params, committed_rows, &claims, &gamma).unwrap()
        {
            let new_w = column_eval.eval_weights(&weights).unwrap();
            let w_coeffs = circle_weight_coeffs(geom, &weights).unwrap();
            let old_w = indices
                .iter()
                .map(|&i| circle_evaluate(geom, &w_coeffs, i).unwrap())
                .collect::<Vec<_>>();
            assert_eq!(new_w, old_w, "row weights-at-column mismatch");
        }

        // Same accept decision.
        let openings = commitment.open_columns(&indices).unwrap();
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
    }

    #[test]
    fn circle_claim_batch_byte_identity_v2_and_v3() {
        circle_claim_batch_byte_identity_body(v2_circle_params());
        circle_claim_batch_byte_identity_body(v3_circle_params());
    }

    #[test]
    fn circle_claim_batch_roundtrip_and_rejects_compensated_tamper() {
        circle_claim_batch_roundtrip_body(v2_circle_params());
    }

    #[test]
    fn v3_circle_claim_batch_roundtrip_and_rejects_compensated_tamper() {
        circle_claim_batch_roundtrip_body(v3_circle_params());
    }

    #[test]
    #[ignore = "release gate: structured split claim-batch tamper negatives"]
    fn structured_split_claim_batch_rejects_required_tampers() {
        let params = v4_circle_params();
        let values_a = (0..1024)
            .map(|value| Fp::from_u64(value + 1))
            .collect::<Vec<_>>();
        let values_b = (0..1024)
            .map(|value| Fp::from_u64(value + 2049))
            .collect::<Vec<_>>();
        let commitment_a = commit_witness(&values_a, params).unwrap();
        let commitment_b = commit_witness(&values_b, params).unwrap();
        let mut claims = vec![
            claim_for(
                &values_a,
                0,
                (0..10).map(|bit| Fp::from_u64(3 + bit * 2)).collect(),
            ),
            claim_for(
                &values_b,
                0,
                (0..10).map(|bit| Fp::from_u64(29 + bit * 2)).collect(),
            ),
        ];
        claims[1].terms[0].offset = commitment_a.witness_rows * params.row_len;
        let gamma = [Fp::from_u64(53), Fp::from_u64(59)];
        let batch = commitment_a
            .split_claim_batch(&commitment_b, &claims, &gamma)
            .unwrap();
        let indices = (0..params.openings)
            .map(|index| (index * 19 + 3) % params.codeword_len)
            .collect::<Vec<_>>();
        let openings_a = commitment_a.open_columns(&indices).unwrap();
        let openings_b = commitment_b.open_columns(&indices).unwrap();
        let verify = |batch: &LigeroClaimBatch,
                      claims: &[LigeroLinearClaim],
                      openings_a: &[ColumnOpening],
                      openings_b: &[ColumnOpening]| {
            verify_split_claim_batch(
                commitment_a.root(),
                commitment_b.root(),
                params,
                values_a.len(),
                values_b.len(),
                openings_a,
                openings_b,
                batch,
                claims,
                &gamma,
            )
            .unwrap()
        };

        assert!(verify(&batch, &claims, &openings_a, &openings_b));

        let mut compensated_claims = claims.clone();
        compensated_claims[0].value = compensated_claims[0].value + Fp::ONE;
        let mut compensated_batch = batch.clone();
        compensated_batch.blind_claim = Fp::ZERO - gamma[0];
        assert!(!verify(
            &compensated_batch,
            &compensated_claims,
            &openings_a,
            &openings_b
        ));

        let mut coefficient_tamper = batch.clone();
        coefficient_tamper.coefficients[0] = coefficient_tamper.coefficients[0] + Fp::ONE;
        assert!(!verify(
            &coefficient_tamper,
            &claims,
            &openings_a,
            &openings_b
        ));

        let mut blind_tamper = batch.clone();
        blind_tamper.blind_claim = Fp::ONE;
        assert!(!verify(&blind_tamper, &claims, &openings_a, &openings_b));

        let mut opening_tamper = openings_a.clone();
        opening_tamper[0].column[0] = opening_tamper[0].column[0] + Fp::ONE;
        assert!(!verify(&batch, &claims, &opening_tamper, &openings_b));
    }

    /// WO-P6: the ℓ=128 params must hit the 2^-132 soundness target. The
    /// derivation (per-term exponents) is recorded in the WO report; the
    /// dominant term is the proximity `(1 − e/n)^t = 2^-132.61`.
    #[test]
    fn v3_soundness_error_meets_target() {
        let params = v3_circle_params();
        assert!(params.validate().is_ok());
        assert_eq!(params.openings, 168);
        assert_eq!(params.proximity_radius, 1726);
        assert_eq!(params.claim_degree_bound(), 642);
        let se = params.soundness_error();
        assert!(
            se <= 2f64.powi(-132),
            "v3 soundness {se:e} (log2 {}) exceeds 2^-132",
            se.log2()
        );
        // t = 168 is the minimum: t = 167 misses the target.
        let mut weaker = params;
        weaker.openings = 167;
        assert!(
            weaker.soundness_error() > 2f64.powi(-132),
            "t = 167 should NOT reach 2^-132 (t = 168 is the exact minimum)"
        );
    }

    /// v4 (ℓ=256) committed-mask soundness pin. The quadratic response has
    /// degree bound 1026, forcing `e = 1534`; `t = 196` leaves a one-opening
    /// margin over the first count that keeps the total error below 2^-132.
    #[test]
    fn v4_soundness_error_meets_target() {
        let params = v4_circle_params();
        assert!(params.validate().is_ok());
        assert!(params.validate_quadratic().is_ok());
        assert_eq!(params.openings, 196);
        assert_eq!(params.proximity_radius, 1534);
        assert_eq!(params.claim_degree_bound(), 770);
        assert_eq!(params.quadratic_degree_bound(), 1026);
        assert_eq!(
            params
                .circle_geom()
                .expect("v4 uses a Circle code")
                .product_domain_len,
            2048
        );
        // Value-pad ZK budget: every opening consumes one per-row pad slot.
        assert!(params.degree_bound - params.row_len >= params.openings);
        let se = params.soundness_error();
        assert!(
            se <= 2f64.powi(-132),
            "v4 soundness {se:e} (log2 {}) exceeds 2^-132",
            se.log2()
        );
        // t = 194 misses the target; production keeps one opening of margin
        // over the exact minimum of 195.
        let mut weaker = params;
        weaker.openings = 194;
        assert!(
            weaker.soundness_error() > 2f64.powi(-132),
            "t = 194 should NOT reach 2^-132 (production uses t = 196)"
        );
    }

    #[test]
    fn committed_quadratic_batch_accepts_products_and_rejects_tampering() {
        let params = v4_circle_params();
        let values = vec![Fp::from_u64(7), Fp::from_u64(9), Fp::from_u64(63)];
        let constraints = [LigeroQuadraticConstraint { x: 0, y: 1, z: 2 }];
        let (commitment, _) =
            commit_witness_with_quadratics_profiled(&values, params, &constraints)
                .expect("valid product commitment");
        let challenges = [Fp::from_u64(17)];
        let batch = commitment
            .quadratic_batch(&challenges)
            .expect("quadratic quotient");
        let indices = (0..params.openings).collect::<Vec<_>>();
        let openings = commitment
            .open_columns(&indices)
            .expect("quadratic openings");

        assert!(verify_quadratic_batch(
            commitment.root(),
            params,
            values.len(),
            constraints.len(),
            &openings,
            &batch,
            &challenges,
        )
        .expect("quadratic verification"));

        let route_claims =
            quadratic_route_claims(values.len(), params, &constraints).expect("route claims");
        let route_gamma = [Fp::from_u64(19), Fp::from_u64(23), Fp::from_u64(29)];
        let route_batch = commitment
            .claim_batch(&route_claims, &route_gamma)
            .expect("route batch");
        assert!(verify_claim_batch(
            commitment.root(),
            params,
            quadratic_committed_len(values.len(), params, constraints.len())
                .expect("valid quadratic committed length"),
            &openings,
            &route_batch,
            &route_claims,
            &route_gamma,
        )
        .expect("route verification"));

        let mut tampered_quotient = batch.clone();
        tampered_quotient.quotient[0] = tampered_quotient.quotient[0] + Fp::ONE;
        assert!(!verify_quadratic_batch(
            commitment.root(),
            params,
            values.len(),
            constraints.len(),
            &openings,
            &tampered_quotient,
            &challenges,
        )
        .expect("tampered quadratic verification"));

        let mut tampered_routes = route_claims;
        tampered_routes[0].value = Fp::ONE;
        assert!(!verify_claim_batch(
            commitment.root(),
            params,
            quadratic_committed_len(values.len(), params, constraints.len())
                .expect("valid quadratic committed length"),
            &openings,
            &route_batch,
            &tampered_routes,
            &route_gamma,
        )
        .expect("tampered route verification"));

        let invalid_values = vec![Fp::from_u64(7), Fp::from_u64(9), Fp::from_u64(62)];
        assert_eq!(
            commit_witness_with_quadratics_profiled(&invalid_values, params, &constraints)
                .map(|_| ()),
            Err(LigeroError::InvalidQuadraticConstraint)
        );
    }

    /// WO-P6 config-pin negative: a claim-batch proof produced with v2 params
    /// must be rejected when verified against v3 params (the production path
    /// pins v3; a mismatched-params bundle is caught before this check in
    /// ecdsa, but the batch verifier itself must also reject on the size
    /// mismatch — the coefficient/opening lengths no longer line up).
    #[test]
    fn v3_verifier_rejects_v2_params_batch() {
        let values = (0..200)
            .map(|value| Fp::from_u64(value + 1))
            .collect::<Vec<_>>();
        let claims = vec![
            claim_for(&values, 0, vec![Fp::from_u64(3), Fp::from_u64(5)]),
            claim_for(&values, 64, vec![Fp::from_u64(7), Fp::from_u64(11)]),
        ];
        let gamma = [Fp::from_u64(13), Fp::from_u64(17)];

        // Prover commits + batches under v2.
        let v2 = v2_circle_params();
        let commitment = commit_witness(&values, v2).unwrap();
        let batch = commitment.claim_batch(&claims, &gamma).unwrap();
        let indices = (0..v2.openings).map(|i| i * 11 + 1).collect::<Vec<_>>();
        let openings = commitment.open_columns(&indices).unwrap();

        // Verifier expects v3: the opening count (v2=170 vs v3=168) and the
        // claim-degree bound (322 vs 642) both differ, so it must reject.
        let v3 = v3_circle_params();
        assert_ne!(v2, v3);
        let verdict = verify_claim_batch(
            commitment.root(),
            v3,
            values.len(),
            &openings,
            &batch,
            &claims,
            &gamma,
        );
        // Either a structural error or a `false` verdict — never `Ok(true)`.
        assert!(
            !matches!(verdict, Ok(true)),
            "v2-params batch verified under v3: {verdict:?}"
        );
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

        assert_eq!(profile.rows, 8);
        assert_eq!(row_cached, 6);
        assert_eq!(claim_cached, 2);
    }

    /// WO-P1 byte-identical gate: the D512 product path must reproduce, coeff
    /// for coeff, the reference Q = blind + Σ W_r·R_r computed on the 2048
    /// codeword domain (the mathematically-defined Q-025 route the old path
    /// used). Covers BOTH the single (`claim_batch`) and split
    /// (`split_claim_batch`) circle paths.
    fn reference_circle_batch(
        commitments: &[&LigeroCommitment],
        claims: &[LigeroLinearClaim],
        gamma: &[Fp],
    ) -> Vec<Fp> {
        use crate::circle_fft::{circle_encode, circle_ifft_codeword, circle_weight_coeffs};
        let params = commitments[0].params;
        let geom = params.circle_geom().expect("circle params");
        let claim_degree_bound = params.claim_degree_bound();
        // Blind: sum the committed blind coefficient rows, encode to the
        // codeword domain.
        let mut blind = commitments[0].coefficient_rows[commitments[0].claim_blind_row].clone();
        for c in &commitments[1..] {
            for (out, v) in blind.iter_mut().zip(&c.coefficient_rows[c.claim_blind_row]) {
                *out = *out + *v;
            }
        }
        let mut q = circle_encode(geom, &blind, claim_degree_bound).unwrap();
        let combined_rows: usize = commitments.iter().map(|c| c.witness_rows).sum();
        for (row, weights) in batched_row_weights(params, combined_rows, claims, gamma).unwrap() {
            let w_coeffs = circle_weight_coeffs(geom, &weights).unwrap();
            let w_cw = circle_encode(geom, &w_coeffs, geom.data_slots).unwrap();
            // Locate the row's committed coefficients across the group.
            let mut base = 0;
            let mut row_coeffs = None;
            for c in commitments {
                if row < base + c.witness_rows {
                    row_coeffs = Some(&c.coefficient_rows[row - base]);
                    break;
                }
                base += c.witness_rows;
            }
            let row_coeffs = row_coeffs.expect("row index within group");
            let r_cw = circle_encode(geom, row_coeffs, geom.row_message_len).unwrap();
            for ((out, w), r) in q.iter_mut().zip(&w_cw).zip(&r_cw) {
                *out = *out + *w * *r;
            }
        }
        let coeffs = circle_ifft_codeword(geom, q).unwrap();
        coeffs[..claim_degree_bound].to_vec()
    }

    #[test]
    fn circle_claim_batch_d512_matches_2048_reference() {
        let params = v2_circle_params();
        let values: Vec<Fp> = (0..200).map(|v| Fp::from_u64(v * 7 + 3)).collect();
        let claims = vec![
            claim_for(
                &values,
                0,
                vec![Fp::from_u64(3), Fp::from_u64(5), Fp::from_u64(9)],
            ),
            claim_for(&values, 64, vec![Fp::from_u64(7), Fp::from_u64(11)]),
            claim_for(
                &values,
                128,
                vec![Fp::from_u64(2), Fp::from_u64(4), Fp::from_u64(6)],
            ),
        ];
        let gamma = [Fp::from_u64(13), Fp::from_u64(17), Fp::from_u64(23)];

        // Single path.
        let commitment = commit_witness(&values, params).unwrap();
        let batch = commitment.claim_batch(&claims, &gamma).unwrap();
        let reference = reference_circle_batch(&[&commitment], &claims, &gamma);
        assert_eq!(batch.coefficients.len(), params.claim_degree_bound());
        assert_eq!(
            batch.coefficients, reference,
            "D512 single-path batch diverges from the 2048 reference"
        );

        // Split path: two commitments over the same value layout.
        let a = commit_witness(&values, params).unwrap();
        let b = commit_witness(&values, params).unwrap();
        let split_claims = vec![
            claim_for(&values, 0, vec![Fp::from_u64(3), Fp::from_u64(5)]),
            // Second claim indexes into the b-commitment's rows (combined
            // layout). value is irrelevant to the batch (weights depend only on
            // offset/len/point), so build it directly.
            LigeroLinearClaim::mle(
                a.witness_rows * params.row_len + 64,
                4,
                vec![Fp::from_u64(7), Fp::from_u64(11)],
                Fp::ZERO,
            ),
        ];
        let split_gamma = [Fp::from_u64(29), Fp::from_u64(31)];
        let split = a
            .split_claim_batch(&b, &split_claims, &split_gamma)
            .unwrap();
        let split_reference = reference_circle_batch(&[&a, &b], &split_claims, &split_gamma);
        assert_eq!(
            split.coefficients, split_reference,
            "D512 split-path batch diverges from the 2048 reference"
        );
    }
}
