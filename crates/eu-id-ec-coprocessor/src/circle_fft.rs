//! Circle-group FFT Reed–Solomon encoder over F_p256 (Q-025 protocol).
//!
//! `v2(p-1) = 1`, so no multiplicative-subgroup FFT exists over the P-256
//! base field. But `v2(p+1) = 96`, so the circle group
//! `C = {(x, y) : x^2 + y^2 = 1}` (order `p + 1`, since `p = 3 mod 4`) has a
//! subgroup of order `2^k` for any `k <= 96`. This module implements the
//! circle-FFT construction (circle-STARK style, cf. stwo) over that group.
//!
//! * Codeword domain `Dn = { (2i+1)·q : i = 0..n }` where `q` has exact
//!   order `2n`. Closed under negation (`-D[i] = D[n-1-i]`), which drives the
//!   mirror-pair butterflies below.
//! * Universal basis: coefficient index `j` maps to
//!   `b_j(x, y) = y^{j_0} * prod_k pi^{k-1}(x)^{j_k}` with `pi(x) = 2x^2 - 1`.
//!   The x-part for `m = j >> 1` has degree exactly `m`, so the prefix
//!   `{b_0, ..., b_{d-1}}` spans a dimension-`d` space with at most `d` zeros
//!   on the circle (Bezout with the conic): a true RS-rate code. The basis
//!   depends only on the doubling-map tower, NOT on the domain, so
//!   coefficients produced by an IFFT on one domain evaluate consistently on
//!   any other.
//! * Systematic-by-interpolation rows (Q-025): a row message is
//!   `row_message_len` values on the disjoint message domain (generator of
//!   order `2·row_message_len`; every codeword point has order `2·codeword_len`
//!   so the domains cannot intersect). The `data_slots` data values sit at the
//!   fixed `data_window()` slots, the remaining slots carry random pads.
//!   IFFT_message → coefficients → FFT_codeword → codeword.
//! * Claim batching keeps the fixed extraction functional: sum of the batch
//!   polynomial over the data points ([`circle_data_sum`]); per-row MLE weights
//!   become the unique `F_{data_slots}` interpolant through the data points
//!   ([`circle_weight_coeffs`], via a precomputed `data_slots`×`data_slots`
//!   inverse).
//!
//! WO-P6: the whole module is parametrized by a [`CircleGeom`] so two aspect
//! ratios coexist — ℓ=64 (v2: 64 data / 256 message / 2048 codeword / 512
//! product) and ℓ=128 (v3: 128 / 512 / 4096 / 1024). Every `Tables`/
//! `DataWindow` is cached per geometry; the universal basis is shared.

use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

use crate::Fp;

// ℓ=64 (v2) geometry constants — kept as named anchors for the legacy params.
pub const CIRCLE_CODEWORD_LEN: usize = 2048;
pub const CIRCLE_ROW_MESSAGE_LEN: usize = 256;
pub const CIRCLE_DATA_SLOTS: usize = 64;
/// Claim-batch product domain (WO-P1): the batch polynomial
/// `Q = blind + Σ W_r·R_r` lives in `F_322` (W ∈ F_64, R ∈ F_256, product bound
/// 64 + 256 + 2 = 322 per the y² = 1 − x² fold), so any evaluation domain of
/// size > 322 determines it exactly. 512 is the smallest power of two above the
/// bound; the domain generator has exact order 1024. This is disjoint from both
/// the message domain (order 512) and codeword domain (order 4096), but the
/// universal basis is domain-independent, so an IFFT512 recovers the same
/// coefficients.
pub const CIRCLE_PRODUCT_DOMAIN_LEN: usize = 512;

/// One circle-code aspect ratio. All sizes are powers of two; the product
/// domain is derived as the smallest power of two strictly above the claim
/// bound `data_slots + row_message_len + 2`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct CircleGeom {
    pub data_slots: usize,
    pub row_message_len: usize,
    pub codeword_len: usize,
    pub product_domain_len: usize,
}

impl CircleGeom {
    const fn message_log_n(self) -> usize {
        self.row_message_len.trailing_zeros() as usize
    }
    const fn codeword_log_n(self) -> usize {
        self.codeword_len.trailing_zeros() as usize
    }
    const fn product_log_n(self) -> usize {
        self.product_domain_len.trailing_zeros() as usize
    }
}

/// ℓ=64 geometry (v2 params).
pub const CIRCLE_GEOM_L64: CircleGeom = CircleGeom {
    data_slots: 64,
    row_message_len: 256,
    codeword_len: 2048,
    product_domain_len: 512,
};

/// ℓ=128 geometry (v3 params, WO-P6). Claim bound 128 + 512 + 2 = 642 ⇒
/// product domain 1024 (smallest pow2 > 642).
pub const CIRCLE_GEOM_L128: CircleGeom = CircleGeom {
    data_slots: 128,
    row_message_len: 512,
    codeword_len: 4096,
    product_domain_len: 1024,
};

/// (p + 1) / 2^96 for the P-256 base prime: the odd cofactor of the circle
/// group order, 0xffffffff00000001000000000000000000000001.
const ODD_COFACTOR_BE: [u8; 20] = [
    0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x01,
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CircleRsError {
    EmptyMessage,
    WrongMessageLength,
    IndexOutOfRange,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CirclePoint {
    x: Fp,
    y: Fp,
}

const IDENTITY: CirclePoint = CirclePoint {
    x: Fp::ONE,
    y: Fp::ZERO,
};

fn circle_add(a: CirclePoint, b: CirclePoint) -> CirclePoint {
    CirclePoint {
        x: a.x * b.x - a.y * b.y,
        y: a.x * b.y + a.y * b.x,
    }
}

fn circle_double(a: CirclePoint) -> CirclePoint {
    circle_add(a, a)
}

fn scalar_mul(point: CirclePoint, scalar_be: &[u8]) -> CirclePoint {
    let mut acc = IDENTITY;
    for &byte in scalar_be {
        for bit in (0..8).rev() {
            acc = circle_double(acc);
            if (byte >> bit) & 1 == 1 {
                acc = circle_add(acc, point);
            }
        }
    }
    acc
}

/// Deterministically finds a circle point of exact order `2^(log_n + 1)`.
fn generator(log_n: usize) -> CirclePoint {
    // Rational parametrization ((1 - t^2)/(1 + t^2), 2t/(1 + t^2)) hits every
    // circle point except (-1, 0); scan small t until the 2-Sylow projection
    // has full order.
    for t in 1u64..64 {
        let tf = Fp::from_u64(t);
        let t2 = tf.square();
        let Some(inv) = (Fp::ONE + t2).inverse() else {
            continue;
        };
        let base = CirclePoint {
            x: (Fp::ONE - t2) * inv,
            y: (tf + tf) * inv,
        };
        // Order of `base` divides p + 1 = 2^96 * odd; kill the odd part, then
        // reduce 2^96 -> 2^(log_n + 1).
        let mut g = scalar_mul(base, &ODD_COFACTOR_BE);
        for _ in 0..(96 - log_n - 1) {
            g = circle_double(g);
        }
        let mut probe = g;
        for _ in 0..log_n {
            probe = circle_double(probe);
        }
        if probe == IDENTITY {
            continue; // order too small
        }
        assert_eq!(
            circle_double(probe),
            IDENTITY,
            "2^(log_n + 1) * q must be the identity"
        );
        return g;
    }
    panic!(
        "no circle point of order 2^{} found in t = 1..64",
        log_n + 1
    );
}

struct Tables {
    log_n: usize,
    /// `domain[i] = (2i + 1) * q`; closed under negation via `i <-> n - 1 - i`.
    domain: Vec<CirclePoint>,
    /// `tw[0][k] = y(domain[k])` (k < n/2); `tw[l][k] = pi^{l-1}(x(domain[k]))`
    /// (k < 2^{log_n - 1 - l}) for l >= 1. Level `l` serves blocks of size
    /// `2^{log_n - l}`.
    tw: Vec<Vec<Fp>>,
    inv_tw: Vec<Vec<Fp>>,
    n_inv: Fp,
}

impl Tables {
    fn new(log_n: usize) -> Self {
        let n = 1usize << log_n;
        let half = n / 2;
        let q = generator(log_n);
        let step = circle_double(q);
        let mut domain = Vec::with_capacity(n);
        let mut point = q;
        for _ in 0..n {
            domain.push(point);
            point = circle_add(point, step);
        }
        debug_assert_eq!(point, q, "domain must wrap after n steps");

        let mut tw: Vec<Vec<Fp>> = Vec::with_capacity(log_n);
        tw.push(domain[..half].iter().map(|p| p.y).collect());
        let mut cur: Vec<Fp> = domain[..half].iter().map(|p| p.x).collect();
        for level in 1..log_n {
            let count = 1 << (log_n - 1 - level);
            tw.push(cur[..count].to_vec());
            // pi(x) = 2x^2 - 1 (the x-coordinate doubling map).
            cur = cur[..count]
                .iter()
                .map(|&x| x.square() + x.square() - Fp::ONE)
                .collect();
        }
        let inv_tw = tw.iter().map(|level| Fp::batch_inverse(level)).collect();

        Tables {
            log_n,
            domain,
            tw,
            inv_tw,
            n_inv: Fp::from_u64(n as u64)
                .inverse()
                .expect("power of two is invertible mod p"),
        }
    }
}

/// Per-`log_n` cache of FFT tables, shared by every geometry that uses that
/// size (e.g. the ℓ=64 product domain 512 and the ℓ=128 message domain 512
/// coincide, so the tables are built once).
fn tables_for(log_n: usize) -> &'static Tables {
    static CACHE: OnceLock<Mutex<HashMap<usize, &'static Tables>>> = OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let mut guard = cache.lock().expect("tables cache poisoned");
    guard
        .entry(log_n)
        .or_insert_with(|| Box::leak(Box::new(Tables::new(log_n))))
}

fn codeword_tables(geom: CircleGeom) -> &'static Tables {
    tables_for(geom.codeword_log_n())
}

fn message_tables(geom: CircleGeom) -> &'static Tables {
    tables_for(geom.message_log_n())
}

fn product_tables(geom: CircleGeom) -> &'static Tables {
    tables_for(geom.product_log_n())
}

fn bit_reverse(values: &mut [Fp], log_n: usize) {
    debug_assert_eq!(values.len(), 1usize << log_n);
    for i in 0..values.len() {
        let j = i.reverse_bits() >> (usize::BITS as usize - log_n);
        if i < j {
            values.swap(i, j);
        }
    }
}

/// Forward butterflies for one block: slots `[0, m/2)` hold the sub-FFT of the
/// even coefficients (values of `f0` on the level grid, natural order), slots
/// `[m/2, m)` the odd ones (`f1`). Writes `f0(u_k) +/- w_k * f1(u_k)` to slots
/// `k` and `m-1-k` — the domain's mirror pairing (`u_{m-1-k} = -u_k`).
fn combine(block: &mut [Fp], tw: &[Fp]) {
    let m = block.len();
    let half = m / 2;
    let (mut k, mut r) = (0usize, half - 1);
    while k < r {
        let lo_k = block[k];
        let hi_k = block[half + k];
        let lo_r = block[r];
        let hi_r = block[m - 1 - k]; // slot half + r
        let t_k = tw[k] * hi_k;
        let t_r = tw[r] * hi_r;
        block[k] = lo_k + t_k;
        block[m - 1 - k] = lo_k - t_k;
        block[r] = lo_r + t_r;
        block[half + k] = lo_r - t_r; // slot m - 1 - r
        k += 1;
        r -= 1;
    }
    if k == r {
        let lo = block[k];
        let hi = block[half + k];
        let t = tw[k] * hi;
        block[k] = lo + t;
        block[m - 1 - k] = lo - t;
    }
}

/// Exact inverse of `combine`, with the 1/2 factors deferred to the final
/// `n_inv` scaling in `ifft`.
fn icombine(block: &mut [Fp], inv_tw: &[Fp]) {
    let m = block.len();
    let half = m / 2;
    let (mut k, mut r) = (0usize, half - 1);
    while k < r {
        let p_k = block[k];
        let q_k = block[m - 1 - k];
        let p_r = block[r];
        let q_r = block[half + k]; // slot m - 1 - r
        block[k] = p_k + q_k;
        block[half + k] = (p_k - q_k) * inv_tw[k];
        block[r] = p_r + q_r;
        block[m - 1 - k] = (p_r - q_r) * inv_tw[r];
        k += 1;
        r -= 1;
    }
    if k == r {
        let p = block[k];
        let q = block[m - 1 - k];
        block[k] = p + q;
        block[half + k] = (p - q) * inv_tw[k];
    }
}

/// In-place circle FFT: coefficients (universal basis, natural index order) ->
/// evaluations on the tables' domain (natural index order).
fn fft(values: &mut [Fp], tables: &Tables) {
    assert_eq!(values.len(), 1usize << tables.log_n);
    bit_reverse(values, tables.log_n);
    for level in (0..tables.log_n).rev() {
        let m = 1 << (tables.log_n - level);
        let tw = &tables.tw[level];
        for block in values.chunks_exact_mut(m) {
            combine(block, tw);
        }
    }
}

/// In-place inverse circle FFT: evaluations -> coefficients.
fn ifft(values: &mut [Fp], tables: &Tables) {
    assert_eq!(values.len(), 1usize << tables.log_n);
    for level in 0..tables.log_n {
        let m = 1 << (tables.log_n - level);
        let inv_tw = &tables.inv_tw[level];
        for block in values.chunks_exact_mut(m) {
            icombine(block, inv_tw);
        }
    }
    bit_reverse(values, tables.log_n);
    for value in values.iter_mut() {
        *value = *value * tables.n_inv;
    }
}

/// Encodes `message_prefix` (coefficients, zero-padded to `degree_bound`) into
/// a `geom.codeword_len`-point circle codeword of dimension `degree_bound` and
/// minimum distance >= `codeword_len - degree_bound`.
pub fn circle_encode(
    geom: CircleGeom,
    message_prefix: &[Fp],
    degree_bound: usize,
) -> Result<Vec<Fp>, CircleRsError> {
    if degree_bound == 0 {
        return Err(CircleRsError::EmptyMessage);
    }
    if message_prefix.len() > degree_bound || degree_bound > geom.codeword_len {
        return Err(CircleRsError::WrongMessageLength);
    }
    let mut values = vec![Fp::ZERO; geom.codeword_len];
    values[..message_prefix.len()].copy_from_slice(message_prefix);
    fft(&mut values, codeword_tables(geom));
    Ok(values)
}

/// Evaluations on the codeword domain -> full `codeword_len`-vector of
/// coefficients.
pub fn circle_ifft_codeword(
    geom: CircleGeom,
    mut codeword: Vec<Fp>,
) -> Result<Vec<Fp>, CircleRsError> {
    if codeword.len() != geom.codeword_len {
        return Err(CircleRsError::WrongMessageLength);
    }
    ifft(&mut codeword, codeword_tables(geom));
    Ok(codeword)
}

/// FFT `coeffs` (universal-basis, zero-padded to `product_domain_len`) onto the
/// claim-batch product domain. `coeffs.len()` must be ≤ `product_domain_len`
/// (WO-P1/WO-P6).
pub fn circle_product_fft(geom: CircleGeom, coeffs: &[Fp]) -> Result<Vec<Fp>, CircleRsError> {
    if coeffs.len() > geom.product_domain_len {
        return Err(CircleRsError::WrongMessageLength);
    }
    let mut values = vec![Fp::ZERO; geom.product_domain_len];
    values[..coeffs.len()].copy_from_slice(coeffs);
    fft(&mut values, product_tables(geom));
    Ok(values)
}

/// Inverse of [`circle_product_fft`]: product-domain evaluations →
/// `product_domain_len` coefficients.
pub fn circle_product_ifft(geom: CircleGeom, mut evals: Vec<Fp>) -> Result<Vec<Fp>, CircleRsError> {
    if evals.len() != geom.product_domain_len {
        return Err(CircleRsError::WrongMessageLength);
    }
    ifft(&mut evals, product_tables(geom));
    Ok(evals)
}

fn evaluate_at(message_prefix: &[Fp], point: CirclePoint) -> Fp {
    // pis[k] = pi^{k+1-1}(x) ... pis[0] = x, pis[k] = pi(pis[k-1]); basis for
    // index j uses y^{j_0} and pis[k]^{bit k+1 of j}.
    let pi_count = if message_prefix.len() <= 2 {
        0
    } else {
        usize::BITS as usize - (message_prefix.len() - 1).leading_zeros() as usize - 1
    };
    let mut pis = Vec::with_capacity(pi_count);
    if pi_count > 0 {
        pis.push(point.x);
        for _ in 1..pi_count {
            let last = *pis.last().expect("non-empty");
            pis.push(last.square() + last.square() - Fp::ONE);
        }
    }
    let mut acc = Fp::ZERO;
    for (j, &coeff) in message_prefix.iter().enumerate() {
        let mut basis = if j & 1 == 1 { point.y } else { Fp::ONE };
        for (k, &pi) in pis.iter().enumerate() {
            if (j >> (k + 1)) & 1 == 1 {
                basis = basis * pi;
            }
        }
        acc = acc + coeff * basis;
    }
    acc
}

/// Direct per-column evaluation `sum_j m_j * b_j(domain[index])` — the
/// verifier-side check for a single codeword position, independent of the FFT.
pub fn circle_evaluate(
    geom: CircleGeom,
    message_prefix: &[Fp],
    index: usize,
) -> Result<Fp, CircleRsError> {
    if index >= geom.codeword_len {
        return Err(CircleRsError::IndexOutOfRange);
    }
    Ok(evaluate_at(
        message_prefix,
        codeword_tables(geom).domain[index],
    ))
}

/// The universal-basis value vector `[b_0(P), .., b_{len-1}(P)]` at one codeword
/// column `P = domain[index]`, built by tensor doubling in O(len) mults (WO-P7).
///
/// `basis[j] = y^{j&1} * prod_k pi^k(x)^{bit(j, k+1)}`; starting from `[1, y]`,
/// each pi level `l` extends the built prefix by multiplying its second half by
/// `pi^l(x)`. This is the same tensor structure as [`evaluate_at`], materialized
/// once so that every message evaluation at this column is a dot product
/// ([`CircleColumnBasis::eval`]) sharing the vector — the verifier evaluates the
/// batch (claim_degree_bound coeffs) and every per-row weight (data_slots coeffs)
/// against it without recomputing the pi-tower per call.
pub struct CircleColumnBasis {
    basis: Vec<Fp>,
}

impl CircleColumnBasis {
    /// Precomputes the length-`len` basis vector at `domain[index]`. `len` need
    /// not be a power of two; the vector is truncated to exactly `len`.
    pub fn new(geom: CircleGeom, index: usize, len: usize) -> Result<Self, CircleRsError> {
        if index >= geom.codeword_len {
            return Err(CircleRsError::IndexOutOfRange);
        }
        if len == 0 {
            return Err(CircleRsError::EmptyMessage);
        }
        let point = codeword_tables(geom).domain[index];
        // Round the working length up to a power of two so the doubling fills
        // full halves; truncate to `len` at the end.
        let cap = len.next_power_of_two();
        let mut basis = Vec::with_capacity(cap);
        basis.push(Fp::ONE);
        if cap >= 2 {
            basis.push(point.y);
        }
        // pi^0(x) = x, pi^{l}(x) = 2·pi^{l-1}(x)^2 - 1. Level `l` doubles the
        // prefix of size 2^{l+1} into 2^{l+2}.
        let mut pi = point.x;
        let mut filled = 2usize;
        while filled < cap {
            for i in 0..filled {
                basis.push(basis[i] * pi);
            }
            filled <<= 1;
            pi = pi.square() + pi.square() - Fp::ONE;
        }
        basis.truncate(len);
        Ok(Self { basis })
    }

    /// `sum_j coeffs[j] * basis[j]`. `coeffs.len()` must be ≤ the basis length.
    pub fn eval(&self, coeffs: &[Fp]) -> Fp {
        debug_assert!(coeffs.len() <= self.basis.len());
        coeffs
            .iter()
            .zip(&self.basis)
            .fold(Fp::ZERO, |acc, (&c, &b)| acc + c * b)
    }

    /// Folds this column's basis through the weight-interpolation inverse so a
    /// raw weight vector evaluates in one dot product (WO-P7): for weights `w`,
    /// `W_r(P) = basis · (M⁻¹ w) = (M⁻ᵀ basis) · w`. Returns
    /// `folded[c] = Σ_j inv[j][c] · basis[j]` (length `data_slots`), so
    /// [`CircleColumnBasis::eval`] of `folded` against raw weights equals
    /// `circle_evaluate(circle_weight_coeffs(w), index)` — without the per-row
    /// `data_slots × data_slots` interpolation. Precompute once per column.
    pub fn fold_weight_inverse(&self, geom: CircleGeom) -> Self {
        let window = data_window(geom);
        let inv = &window.interpolation_inverse; // inv[j][c], j,c < data_slots
        let folded = (0..geom.data_slots)
            .map(|c| {
                inv.iter()
                    .zip(&self.basis)
                    .fold(Fp::ZERO, |acc, (row, &b)| acc + row[c] * b)
            })
            .collect();
        Self { basis: folded }
    }
}

struct DataWindow {
    start: usize,
    /// Values at the window's `data_slots` points -> unique `F_{data_slots}`
    /// interpolant, as a `data_slots`×`data_slots` matrix (row-major:
    /// coeffs[j] = sum_c inv[j][c] * values[c]).
    interpolation_inverse: Vec<Vec<Fp>>,
}

/// Inverts a square matrix over Fp by Gauss–Jordan; None if singular.
fn invert_matrix(matrix: &[Vec<Fp>]) -> Option<Vec<Vec<Fp>>> {
    let n = matrix.len();
    let mut a: Vec<Vec<Fp>> = matrix.to_vec();
    let mut inv: Vec<Vec<Fp>> = (0..n)
        .map(|i| {
            (0..n)
                .map(|j| if i == j { Fp::ONE } else { Fp::ZERO })
                .collect()
        })
        .collect();
    for col in 0..n {
        let pivot = (col..n).find(|&r| a[r][col] != Fp::ZERO)?;
        a.swap(col, pivot);
        inv.swap(col, pivot);
        let scale = a[col][col].inverse()?;
        for j in 0..n {
            a[col][j] = a[col][j] * scale;
            inv[col][j] = inv[col][j] * scale;
        }
        for row in 0..n {
            if row == col || a[row][col] == Fp::ZERO {
                continue;
            }
            let factor = a[row][col];
            for j in 0..n {
                a[row][j] = a[row][j] - factor * a[col][j];
                inv[row][j] = inv[row][j] - factor * inv[col][j];
            }
        }
    }
    Some(inv)
}

fn build_data_window(geom: CircleGeom) -> DataWindow {
    // Setup asserts (Q-025): message/codeword domains are disjoint because
    // every codeword point has exact order 2·codeword_len and every message
    // point exact order 2·row_message_len (odd multiples of exact-order
    // generators, distinct orders); the generator order assertions live in
    // `generator`. Domain-disjointness sanity check: the two log sizes differ,
    // so the 2-Sylow orders differ and the sets cannot intersect.
    assert_ne!(
        geom.message_log_n(),
        geom.codeword_log_n(),
        "message and codeword domains must have distinct orders (disjointness)"
    );
    assert!(
        geom.product_domain_len > geom.data_slots + geom.row_message_len + 1,
        "product domain must exceed the claim bound"
    );
    let tables = message_tables(geom);
    // Deterministically pick the first natural-order window of `data_slots`
    // message-domain points on which F_{data_slots} interpolation is
    // invertible (slides on singularity).
    for start in 0..=(geom.row_message_len - geom.data_slots) {
        let matrix: Vec<Vec<Fp>> = (0..geom.data_slots)
            .map(|c| {
                let point = tables.domain[start + c];
                (0..geom.data_slots)
                    .map(|j| {
                        let mut unit = vec![Fp::ZERO; j + 1];
                        unit[j] = Fp::ONE;
                        evaluate_at(&unit, point)
                    })
                    .collect()
            })
            .collect();
        if let Some(interpolation_inverse) = invert_matrix(&matrix) {
            return DataWindow {
                start,
                interpolation_inverse,
            };
        }
    }
    panic!(
        "no invertible {}-point data window in the message domain",
        geom.data_slots
    );
}

fn data_window(geom: CircleGeom) -> &'static DataWindow {
    static CACHE: OnceLock<Mutex<HashMap<CircleGeom, &'static DataWindow>>> = OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let mut guard = cache.lock().expect("data-window cache poisoned");
    guard
        .entry(geom)
        .or_insert_with(|| Box::leak(Box::new(build_data_window(geom))))
}

/// Encodes one witness row: `data` (at most `data_slots` values) at the
/// data-window slots, `pads` filling the other message slots. Returns the
/// row's `row_message_len` coefficients and its codeword.
pub fn circle_encode_row(
    geom: CircleGeom,
    data: &[Fp],
    mut pads: impl FnMut() -> Fp,
) -> Result<(Vec<Fp>, Vec<Fp>), CircleRsError> {
    if data.len() > geom.data_slots {
        return Err(CircleRsError::WrongMessageLength);
    }
    let window = data_window(geom);
    let mut values = Vec::with_capacity(geom.row_message_len);
    for slot in 0..geom.row_message_len {
        if slot >= window.start && slot < window.start + geom.data_slots {
            values.push(data.get(slot - window.start).copied().unwrap_or(Fp::ZERO));
        } else {
            values.push(pads());
        }
    }
    ifft(&mut values, message_tables(geom));
    let coefficients = values;
    let codeword = circle_encode(geom, &coefficients, geom.row_message_len)?;
    Ok((coefficients, codeword))
}

/// The fixed claim-extraction functional: the sum of the function's values
/// over the data points (Q-025 §3).
pub fn circle_data_sum(geom: CircleGeom, message_prefix: &[Fp]) -> Fp {
    let window = data_window(geom);
    let tables = message_tables(geom);
    (0..geom.data_slots).fold(Fp::ZERO, |acc, c| {
        acc + evaluate_at(message_prefix, tables.domain[window.start + c])
    })
}

/// The unique `F_{data_slots}` interpolant through `(data point c, weights[c])`,
/// as `data_slots` universal-basis coefficients (Q-025 §1/§2).
pub fn circle_weight_coeffs(geom: CircleGeom, weights: &[Fp]) -> Result<Vec<Fp>, CircleRsError> {
    if weights.len() != geom.data_slots {
        return Err(CircleRsError::WrongMessageLength);
    }
    let window = data_window(geom);
    Ok(window
        .interpolation_inverse
        .iter()
        .map(|row| {
            row.iter()
                .zip(weights)
                .fold(Fp::ZERO, |acc, (&m, &w)| acc + m * w)
        })
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn splitmix(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn rand_fp(state: &mut u64) -> Fp {
        let mut bytes = [0u8; 32];
        for chunk in bytes.chunks_exact_mut(8) {
            chunk.copy_from_slice(&splitmix(state).to_be_bytes());
        }
        Fp::random(bytes)
    }

    fn rand_row(state: &mut u64, len: usize) -> Vec<Fp> {
        (0..len).map(|_| rand_fp(state)).collect()
    }

    const GEOMS: [CircleGeom; 2] = [CIRCLE_GEOM_L64, CIRCLE_GEOM_L128];

    #[test]
    fn fft_ifft_roundtrip_all_domains() {
        let mut state = 1u64;
        for geom in GEOMS {
            for tables in [
                codeword_tables(geom),
                message_tables(geom),
                product_tables(geom),
            ] {
                let original = rand_row(&mut state, 1 << tables.log_n);
                let mut forward = original.clone();
                fft(&mut forward, tables);
                assert_ne!(forward, original);
                ifft(&mut forward, tables);
                assert_eq!(forward, original);
            }
        }
    }

    #[test]
    fn encode_matches_direct_basis_evaluation() {
        let mut state = 7u64;
        for geom in GEOMS {
            let bound = geom.data_slots + geom.row_message_len + 2; // claim bound
            let message = rand_row(&mut state, bound);
            let codeword = circle_encode(geom, &message, bound).unwrap();
            for _ in 0..5 {
                let index = (splitmix(&mut state) % geom.codeword_len as u64) as usize;
                assert_eq!(
                    codeword[index],
                    circle_evaluate(geom, &message, index).unwrap(),
                    "codeword mismatch at column {index}"
                );
            }
        }
    }

    #[test]
    fn ifft_codeword_recovers_coefficients() {
        let mut state = 13u64;
        for geom in GEOMS {
            let bound = geom.data_slots + geom.row_message_len + 2;
            let message = rand_row(&mut state, bound);
            let codeword = circle_encode(geom, &message, bound).unwrap();
            let coeffs = circle_ifft_codeword(geom, codeword).unwrap();
            assert_eq!(&coeffs[..bound], &message[..]);
            assert!(coeffs[bound..].iter().all(|&c| c == Fp::ZERO));
        }
    }

    /// Q-025 basis-consistency gate: message-domain IFFT coefficients must be
    /// systematic (reproduce the data at the window) AND evaluate consistently
    /// through the codeword-domain FFT and the direct basis evaluation.
    #[test]
    fn row_encode_is_systematic_at_data_window_and_basis_consistent() {
        let mut state = 21u64;
        for geom in GEOMS {
            let data = rand_row(&mut state, geom.data_slots);
            let mut pad_state = 99u64;
            let (coefficients, codeword) =
                circle_encode_row(geom, &data, || rand_fp(&mut pad_state)).unwrap();

            // Systematic: coefficients evaluate back to the data at the window.
            let window = data_window(geom);
            let tables = message_tables(geom);
            for (c, &expected) in data.iter().enumerate() {
                assert_eq!(
                    evaluate_at(&coefficients, tables.domain[window.start + c]),
                    expected,
                    "data slot {c} not reproduced"
                );
            }
            // Basis-consistent: FFT codeword agrees with direct evaluation.
            for _ in 0..8 {
                let index = (splitmix(&mut state) % geom.codeword_len as u64) as usize;
                assert_eq!(
                    codeword[index],
                    circle_evaluate(geom, &coefficients, index).unwrap(),
                    "codeword mismatch at column {index}"
                );
            }
        }
    }

    #[test]
    fn weight_coeffs_interpolate_and_extraction_functional_matches() {
        let mut state = 31u64;
        for geom in GEOMS {
            let bound = geom.data_slots + geom.row_message_len + 2;
            let data = rand_row(&mut state, geom.data_slots);
            let weights = rand_row(&mut state, geom.data_slots);
            let mut pad_state = 5u64;
            let (row_coeffs, _) =
                circle_encode_row(geom, &data, || rand_fp(&mut pad_state)).unwrap();
            let w_coeffs = circle_weight_coeffs(geom, &weights).unwrap();

            // W interpolates the weights at the data points.
            let window = data_window(geom);
            let tables = message_tables(geom);
            for (c, &expected) in weights.iter().enumerate() {
                assert_eq!(
                    evaluate_at(&w_coeffs, tables.domain[window.start + c]),
                    expected
                );
            }

            // sum_{s in S_data} W(s)·R(s) == <weights, data> despite the pads:
            // check via the product codeword route the prover uses.
            let w_cw = circle_encode(geom, &w_coeffs, geom.data_slots).unwrap();
            let r_cw = circle_encode(geom, &row_coeffs, geom.row_message_len).unwrap();
            let product: Vec<Fp> = w_cw.iter().zip(&r_cw).map(|(&w, &r)| w * r).collect();
            let product_coeffs = circle_ifft_codeword(geom, product).unwrap();
            assert!(
                product_coeffs[bound..].iter().all(|&c| c == Fp::ZERO),
                "W·R must lie in F_{bound}"
            );
            let expected = weights
                .iter()
                .zip(&data)
                .fold(Fp::ZERO, |acc, (&w, &d)| acc + w * d);
            assert_eq!(circle_data_sum(geom, &product_coeffs[..bound]), expected);
        }
    }

    /// The product-domain FFT must agree with the codeword-domain encoding on
    /// the shared coefficients: an IFFT_product ∘ (pointwise product on the
    /// product domain) recovers the same F_bound coefficients as the codeword
    /// route (basis is domain-independent, WO-P1/P6).
    #[test]
    fn product_domain_matches_codeword_route() {
        let mut state = 41u64;
        for geom in GEOMS {
            let bound = geom.data_slots + geom.row_message_len + 2;
            let weights = rand_row(&mut state, geom.data_slots);
            let data = rand_row(&mut state, geom.data_slots);
            let mut pad_state = 3u64;
            let (row_coeffs, _) =
                circle_encode_row(geom, &data, || rand_fp(&mut pad_state)).unwrap();
            let w_coeffs = circle_weight_coeffs(geom, &weights).unwrap();

            // Product-domain route.
            let w_p = circle_product_fft(geom, &w_coeffs).unwrap();
            let r_p = circle_product_fft(geom, &row_coeffs).unwrap();
            let prod_p: Vec<Fp> = w_p.iter().zip(&r_p).map(|(&w, &r)| w * r).collect();
            let coeffs_p = circle_product_ifft(geom, prod_p).unwrap();
            assert!(
                coeffs_p[bound..].iter().all(|&c| c == Fp::ZERO),
                "product-domain W·R escaped F_{bound}"
            );

            // Codeword route.
            let w_cw = circle_encode(geom, &w_coeffs, geom.data_slots).unwrap();
            let r_cw = circle_encode(geom, &row_coeffs, geom.row_message_len).unwrap();
            let prod_cw: Vec<Fp> = w_cw.iter().zip(&r_cw).map(|(&w, &r)| w * r).collect();
            let coeffs_cw = circle_ifft_codeword(geom, prod_cw).unwrap();

            assert_eq!(&coeffs_p[..bound], &coeffs_cw[..bound]);
        }
    }

    #[test]
    fn distinct_messages_differ_in_many_positions() {
        let mut state = 11u64;
        for geom in GEOMS {
            let degree_bound = geom.row_message_len;
            let floor = geom.codeword_len - 2 * degree_bound;

            let m1 = rand_row(&mut state, degree_bound);
            let mut m2 = m1.clone();
            m2[degree_bound - 1] = m2[degree_bound - 1] + Fp::ONE;
            let c1 = circle_encode(geom, &m1, degree_bound).unwrap();
            let c2 = circle_encode(geom, &m2, degree_bound).unwrap();
            let diff = c1.iter().zip(&c2).filter(|(a, b)| a != b).count();
            assert!(
                diff > floor,
                "distance smoke: only {diff} differing positions"
            );
        }
    }

    /// WO-P7 byte-identity: the precomputed per-column basis dot product must
    /// equal the direct `circle_evaluate` for every message length the verifier
    /// uses (data_slots weight coeffs, row_message_len, claim bound).
    #[test]
    fn column_basis_matches_circle_evaluate() {
        let mut state = 71u64;
        for geom in GEOMS {
            let bound = geom.data_slots + geom.row_message_len + 2;
            let message = rand_row(&mut state, bound);
            for _ in 0..6 {
                let index = (splitmix(&mut state) % geom.codeword_len as u64) as usize;
                let basis = CircleColumnBasis::new(geom, index, bound).unwrap();
                for len in [geom.data_slots, geom.row_message_len, bound] {
                    assert_eq!(
                        basis.eval(&message[..len]),
                        circle_evaluate(geom, &message[..len], index).unwrap(),
                        "basis dot mismatch at column {index}, len {len}"
                    );
                }
            }
        }
    }

    #[test]
    fn encode_rejects_bad_lengths() {
        let geom = CIRCLE_GEOM_L64;
        assert_eq!(
            circle_encode(geom, &[], 0),
            Err(CircleRsError::EmptyMessage)
        );
        assert_eq!(
            circle_encode(geom, &[Fp::ONE; 3], 2),
            Err(CircleRsError::WrongMessageLength)
        );
        assert!(circle_evaluate(geom, &[Fp::ONE], geom.codeword_len).is_err());
        assert!(circle_weight_coeffs(geom, &[Fp::ONE; 3]).is_err());
        assert!(circle_encode_row(geom, &[Fp::ONE; 65], || Fp::ZERO).is_err());
    }
}
