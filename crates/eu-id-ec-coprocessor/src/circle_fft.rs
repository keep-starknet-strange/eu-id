//! Circle-group FFT Reed-Solomon encoder over F_p256.
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
//!   The x-part for `m = j >> 1` has degree `m`.
//!   Thus, the prefix `{b_0, ..., b_{d-1}}` spans a dimension-`d` space.
//!   It has at most `d` zeros on the circle by Bezout.
//!   The basis depends only on the doubling-map tower.
//!   IFFT coefficients from one domain evaluate consistently on another domain.
//! * Systematic interpolation: a row message is
//!   `row_message_len` values on the disjoint message domain (generator of
//!   order `2·row_message_len`. Every codeword point has order `2·codeword_len`
//!   so the domains cannot intersect). The `data_slots` data values sit at the
//!   fixed `data_window()` slots, the remaining slots carry random pads.
//!   IFFT_message → coefficients → FFT_codeword → codeword.
//! * Claim batching keeps the fixed extraction functional: sum of the batch
//!   polynomial over the data points ([`circle_data_sum`]). Per-row MLE weights
//!   become the unique `F_{data_slots}` interpolant through the data points
//!   ([`circle_weight_coeffs`], via a precomputed `data_slots`×`data_slots`
//!   inverse).
//!
//! The product geometry uses 256 data, 512 message, 4096 codeword, and 2048 product values.
//! It caches its `Tables` and `DataWindow`.

use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

use rayon::prelude::*;

use crate::Fp;

/// The circle-code geometry. All sizes are powers of two.
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

/// Product geometry. The committed-mask layer proves products of two
/// degree-1024 rows, whose circle-basis bound is `2*1024 + 2 = 2050`. Thus,
/// the product domain is 4096, the smallest power of two strictly above that
/// bound. The per-row value-pad budget is `1024 − 512 = 512`. The 2× aspect
/// ratio (row_len 512 vs the prior 256) halves the opened-row count at a fixed
/// soundness target, shrinking the proof's dominant opened-columns term.
pub const PRODUCT_CIRCLE_GEOM: CircleGeom = CircleGeom {
    data_slots: 512,
    row_message_len: 1024,
    codeword_len: 8192,
    product_domain_len: 4096,
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
    // circle point except (-1, 0). Scan small t until the 2-Sylow projection
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
        // Order of `base` divides p + 1 = 2^96 * odd. Kill the odd part, then
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
    /// `domain[i] = (2i + 1) * q`. Closed under negation via `i <-> n - 1 - i`.
    domain: Vec<CirclePoint>,
    /// `tw[0][k] = y(domain[k])` (k < n/2). `tw[l][k] = pi^{l-1}(x(domain[k]))`
    /// (k < 2^{log_n - 1 - l}) for l >= 1. Level `l` serves blocks of size
    /// `2^{log_n - l}`.
    tw: Vec<Vec<Fp>>,
    inv_tw: Vec<Vec<Fp>>,
    n_inv: Fp,
}

impl Tables {
    fn new(log_n: usize) -> Self {
        let n = 1usize << log_n;
        let q = generator(log_n);
        let step = circle_double(q);
        let mut domain = Vec::with_capacity(n);
        let mut point = q;
        for _ in 0..n {
            domain.push(point);
            point = circle_add(point, step);
        }
        debug_assert_eq!(point, q, "domain must wrap after n steps");
        Self::from_domain(log_n, domain)
    }

    /// Builds the twiddle tower for a mirror-paired domain.
    ///
    /// The domain satisfies `domain[n-1-i] = -domain[i]`.
    /// The recursion uses only the point set and doubling map.
    /// Thus, it supports canonical domains and twin-coset subdomains.
    /// Round-trip tests check each domain.
    fn from_domain(log_n: usize, domain: Vec<CirclePoint>) -> Self {
        let n = 1usize << log_n;
        debug_assert_eq!(domain.len(), n);
        let half = n / 2;
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

/// Cache of FFT tables for each `log_n`.
///
/// Geometries with the same size share one table.
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

/// Applies forward butterflies to one block.
///
/// Slots `[0, m/2)` contain the even-coefficient sub-FFT.
/// Slots `[m/2, m)` contain the odd-coefficient sub-FFT.
/// The function writes paired results to slots `k` and `m-1-k`.
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

/// Exact inverse of `combine`.
///
/// `ifft` applies the 1/2 factors during its final `n_inv` scaling.
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
/// claim-batch product domain.
///
/// `coeffs.len()` must not exceed `product_domain_len`.
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

/// Multiplies `factor` by the fixed data-window vanishing polynomial
/// `Z_W = b_data_slots`.
///
/// The result is represented in the universal circle basis and truncated to
/// `degree_bound`. Multiplication is performed on the disjoint product domain,
/// where `Z_W` is non-zero at every point.
pub fn circle_multiply_data_vanishing(
    geom: CircleGeom,
    factor: &[Fp],
    degree_bound: usize,
) -> Result<Vec<Fp>, CircleRsError> {
    if degree_bound <= geom.data_slots
        || degree_bound > geom.product_domain_len
        || factor.len() > degree_bound - geom.data_slots
    {
        return Err(CircleRsError::WrongMessageLength);
    }
    let mut zw = vec![Fp::ZERO; geom.data_slots + 1];
    zw[geom.data_slots] = Fp::ONE;
    let mut product = circle_product_fft(geom, factor)?;
    let zw_values = circle_product_fft(geom, &zw)?;
    for (value, zw_value) in product.iter_mut().zip(zw_values) {
        *value = *value * zw_value;
    }
    let coefficients = circle_product_ifft(geom, product)?;
    if coefficients[degree_bound..]
        .iter()
        .any(|&coefficient| coefficient != Fp::ZERO)
    {
        return Err(CircleRsError::WrongMessageLength);
    }
    Ok(coefficients[..degree_bound].to_vec())
}

/// Divides a polynomial that vanishes on the data window by `Z_W`.
///
/// This quotient representation proves that the hidden quadratic response
/// vanishes at every committed data slot without exposing any response value.
pub fn circle_divide_data_vanishing(
    geom: CircleGeom,
    polynomial: &[Fp],
    degree_bound: usize,
) -> Result<Vec<Fp>, CircleRsError> {
    if degree_bound <= geom.data_slots
        || degree_bound > geom.product_domain_len
        || polynomial.len() > degree_bound
    {
        return Err(CircleRsError::WrongMessageLength);
    }
    let quotient_bound = degree_bound - geom.data_slots;
    let mut zw = vec![Fp::ZERO; geom.data_slots + 1];
    zw[geom.data_slots] = Fp::ONE;
    let zw_values = circle_product_fft(geom, &zw)?;
    if zw_values.contains(&Fp::ZERO) {
        return Err(CircleRsError::WrongMessageLength);
    }
    let inverse_zw = Fp::batch_inverse(&zw_values);
    let mut quotient_values = circle_product_fft(geom, polynomial)?;
    for (value, inverse) in quotient_values.iter_mut().zip(inverse_zw) {
        *value = *value * inverse;
    }
    let coefficients = circle_product_ifft(geom, quotient_values)?;
    if coefficients[quotient_bound..]
        .iter()
        .any(|&coefficient| coefficient != Fp::ZERO)
    {
        return Err(CircleRsError::WrongMessageLength);
    }
    Ok(coefficients[..quotient_bound].to_vec())
}

fn evaluate_at(message_prefix: &[Fp], point: CirclePoint) -> Fp {
    // pis[k] = pi^{k+1-1}(x) ... pis[0] = x, pis[k] = pi(pis[k-1]). Basis for
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

struct DataWindow {
    /// FFT tables for the canonical `data_slots` window domain.
    ///
    /// Its 2-Sylow order differs from all other domain orders.
    /// [`ifft`] returns the unique universal-basis interpolant in `O(d log d)`.
    tables: &'static Tables,
    /// The window's vanishing polynomial `Z_W = π^(log d − 1)(x)` (the single
    /// universal-basis element `b_{data_slots}`), evaluated on the message
    /// domain. Row pads use `Z_W · P` for uniform `P` in `F_{k−d}`.
    /// `Z_W` vanishes on each window point.
    /// Thus, padded rows preserve their window data.
    /// Multiplication is injective, so the pad space keeps rank `k − d`.
    /// `Z_W` is nonzero outside the window, so codeword evaluations stay masked.
    zw_on_message: Vec<Fp>,
    /// Per-basis window sums `basis_sums[j] = Σ_{s ∈ window} b_j(s)` for
    /// `j < product_domain_len`. The claim-extraction functional
    /// [`circle_data_sum`] is `Σ_s Σ_j c_j b_j(s)`. Distributing the finite-field
    /// sum gives `Σ_j c_j · basis_sums[j]`, a single dot product instead of one
    /// full basis re-evaluation per window point. Exact field identity, so the
    /// result is byte-identical to the per-point evaluation. Sized to the product
    /// domain (≥ the claim bound, so it covers every batch polynomial). Longer
    /// inputs fall back to the per-point sum.
    basis_sums: Vec<Fp>,
}

/// `basis_sums[j] = Σ_{s ∈ domain} b_j(s)` for `j < len`, built by accumulating
/// each window point's universal-basis vector — the transpose of summing
/// [`evaluate_at`] over the domain, so `Σ_j c_j·basis_sums[j]` equals
/// `Σ_s evaluate_at(c, s)` exactly.
fn build_basis_sums(domain: &[CirclePoint], len: usize) -> Vec<Fp> {
    if len == 0 {
        return Vec::new();
    }
    let pi_count = if len <= 2 {
        0
    } else {
        usize::BITS as usize - (len - 1).leading_zeros() as usize - 1
    };
    // Each window point contributes an independent basis vector into `sums`, so
    // accumulate per-task partial sums in parallel and combine them. Base-field
    // addition is exact and associative, so the result is bit-identical to the
    // serial accumulation — the cached table contents are unchanged.
    let zero = || vec![Fp::ZERO; len];
    domain
        .par_iter()
        .fold(zero, |mut sums, &point| {
            let mut pis = Vec::with_capacity(pi_count);
            if pi_count > 0 {
                pis.push(point.x);
                for _ in 1..pi_count {
                    let last = *pis.last().expect("non-empty");
                    pis.push(last.square() + last.square() - Fp::ONE);
                }
            }
            for (j, sum) in sums.iter_mut().enumerate() {
                let mut basis = if j & 1 == 1 { point.y } else { Fp::ONE };
                for (k, &pi) in pis.iter().enumerate() {
                    if (j >> (k + 1)) & 1 == 1 {
                        basis = basis * pi;
                    }
                }
                *sum = *sum + basis;
            }
            sums
        })
        .reduce(zero, |mut left, right| {
            for (dst, src) in left.iter_mut().zip(right) {
                *dst = *dst + src;
            }
            left
        })
}

fn build_data_window(geom: CircleGeom) -> DataWindow {
    // Confirm that all four domains are disjoint.
    // Each canonical point has the exact generator order.
    // The four domains have different log sizes.
    assert_ne!(
        geom.message_log_n(),
        geom.codeword_log_n(),
        "message and codeword domains must have distinct orders (disjointness)"
    );
    let d = geom.data_slots;
    let window_log_n = d.trailing_zeros() as usize;
    assert_ne!(
        window_log_n,
        geom.message_log_n(),
        "window and message domains must have distinct orders (disjointness)"
    );
    assert_ne!(
        window_log_n,
        geom.codeword_log_n(),
        "window and codeword domains must have distinct orders (disjointness)"
    );
    assert!(
        geom.product_domain_len > geom.data_slots + geom.row_message_len + 1,
        "product domain must exceed the claim bound"
    );
    let tables = tables_for(window_log_n);
    // Z_W(x) = π^(log d − 1)(x).
    // Each window point P has order 2d.
    // Thus, x(2^(log d − 1)·P) is the zero coordinate of an order-4 point.
    let zw_on_message = message_tables(geom)
        .domain
        .iter()
        .map(|point| {
            let mut x = point.x;
            for _ in 0..window_log_n.saturating_sub(1) {
                x = x.square() + x.square() - Fp::ONE;
            }
            x
        })
        .collect();
    let basis_sums = build_basis_sums(&tables.domain, geom.product_domain_len);
    DataWindow {
        tables,
        zw_on_message,
        basis_sums,
    }
}

fn data_window(geom: CircleGeom) -> &'static DataWindow {
    static CACHE: OnceLock<Mutex<HashMap<CircleGeom, &'static DataWindow>>> = OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let mut guard = cache.lock().expect("data-window cache poisoned");
    guard
        .entry(geom)
        .or_insert_with(|| Box::leak(Box::new(build_data_window(geom))))
}

/// Eagerly builds and caches the data-window tables for `geom`.
///
/// Call this from a single-threaded context *before* parallel row encoding.
/// Otherwise the first `circle_encode_row` inside a `par_chunks` builds the
/// tables while every other rayon worker blocks on the cache `Mutex`, leaving
/// the one-time build effectively single-threaded.
pub fn warm_circle_tables(geom: CircleGeom) {
    let _ = data_window(geom);
}

/// Encodes one masked witness row.
///
/// The row interpolates `(window point c, data[c])`.
/// It adds `Z_W · P` for a uniform `F_{k−d}` pad.
/// The row preserves all window data.
/// The pad masks each off-window evaluation.
/// Returns `row_message_len` coefficients and the codeword.
pub fn circle_encode_row(
    geom: CircleGeom,
    data: &[Fp],
    mut pads: impl FnMut() -> Fp,
) -> Result<(Vec<Fp>, Vec<Fp>), CircleRsError> {
    if data.len() > geom.data_slots {
        return Err(CircleRsError::WrongMessageLength);
    }
    let window = data_window(geom);
    let d = geom.data_slots;
    let k = geom.row_message_len;
    let mut coefficients = data.to_vec();
    coefficients.resize(d, Fp::ZERO);
    ifft(&mut coefficients, window.tables);
    coefficients.resize(k, Fp::ZERO);
    // Z_W·P via the message domain: P coefficients -> values, pointwise Z_W,
    // back to coefficients (Z_W·P ∈ F_k exactly).
    let mut masked_pads = Vec::with_capacity(k);
    for _ in 0..(k - d) {
        masked_pads.push(pads());
    }
    masked_pads.resize(k, Fp::ZERO);
    fft(&mut masked_pads, message_tables(geom));
    for (value, &zw) in masked_pads.iter_mut().zip(&window.zw_on_message) {
        *value = *value * zw;
    }
    ifft(&mut masked_pads, message_tables(geom));
    for (coefficient, pad) in coefficients.iter_mut().zip(&masked_pads) {
        *coefficient = *coefficient + *pad;
    }
    let codeword = circle_encode(geom, &coefficients, k)?;
    Ok((coefficients, codeword))
}

/// Returns the sum of the function values over the fixed data points.
///
/// `Σ_s Σ_j c_j b_j(s) = Σ_j c_j (Σ_s b_j(s))`.
/// This identity gives a dot product against the
/// precomputed `DataWindow::basis_sums` instead of one full basis
/// re-evaluation per window point (byte-identical, an exact finite-field
/// identity). Inputs longer than the precomputed table fall back to the direct
/// per-point sum.
pub fn circle_data_sum(geom: CircleGeom, message_prefix: &[Fp]) -> Fp {
    let window = data_window(geom);
    if message_prefix.len() <= window.basis_sums.len() {
        message_prefix
            .iter()
            .zip(&window.basis_sums)
            .fold(Fp::ZERO, |acc, (&coeff, &sum)| acc + coeff * sum)
    } else {
        window.tables.domain.iter().fold(Fp::ZERO, |acc, &point| {
            acc + evaluate_at(message_prefix, point)
        })
    }
}

/// Returns the interpolant through `(data point c, weights[c])`.
///
/// The result contains `data_slots` universal-basis coefficients.
/// A twin-coset IFFT computes it in `O(d log d)`.
/// The coefficients evaluate consistently on the codeword domain.
pub fn circle_weight_coeffs(geom: CircleGeom, weights: &[Fp]) -> Result<Vec<Fp>, CircleRsError> {
    if weights.len() != geom.data_slots {
        return Err(CircleRsError::WrongMessageLength);
    }
    let window = data_window(geom);
    let mut values = weights.to_vec();
    ifft(&mut values, &window.tables);
    Ok(values)
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

    const GEOMS: [CircleGeom; 1] = [PRODUCT_CIRCLE_GEOM];

    /// Confirms that the twin-coset IFFT recovers random basis coefficients.
    ///
    /// Direct evaluation supplies the window values.
    /// This test checks the FFT domain and universal-basis consistency.
    #[test]
    fn window_ifft_matches_direct_evaluation() {
        let mut state = 0xD1CEu64;
        for geom in GEOMS {
            let coeffs = rand_row(&mut state, geom.data_slots);
            let window_points: Vec<CirclePoint> = data_window(geom).tables.domain.clone();
            let values: Vec<Fp> = window_points
                .iter()
                .map(|&point| evaluate_at(&coeffs, point))
                .collect();
            let recovered = circle_weight_coeffs(geom, &values).expect("window interpolates");
            assert_eq!(recovered, coeffs, "geom {geom:?}");
        }
    }

    /// Confirms that `Z_W = b_{data_slots}` vanishes only on window points.
    ///
    /// Thus, rows preserve window data and mask every open codeword column.
    #[test]
    fn zw_vanishes_on_window_only() {
        for geom in GEOMS {
            let mut zw = vec![Fp::ZERO; geom.data_slots + 1];
            zw[geom.data_slots] = Fp::ONE;
            for (c, &point) in data_window(geom).tables.domain.iter().enumerate() {
                assert_eq!(
                    evaluate_at(&zw, point),
                    Fp::ZERO,
                    "Z_W must vanish at window point {c} (geom {geom:?})"
                );
            }
            for index in 0..geom.codeword_len {
                assert_ne!(
                    circle_evaluate(geom, &zw, index).expect("Z_W evaluates"),
                    Fp::ZERO,
                    "Z_W must not vanish at codeword column {index} (geom {geom:?})"
                );
            }
        }
    }

    #[test]
    fn data_window_vanishing_quotient_roundtrips_at_quadratic_bound() {
        let geom = PRODUCT_CIRCLE_GEOM;
        let degree_bound = 2 * geom.row_message_len + 2;
        let quotient_bound = degree_bound - geom.data_slots;
        let mut state = 0x5155_4F54u64;
        let factor = rand_row(&mut state, quotient_bound);

        let product =
            circle_multiply_data_vanishing(geom, &factor, degree_bound).expect("Z_W product");
        assert_eq!(product.len(), degree_bound);
        for (index, &point) in data_window(geom).tables.domain.iter().enumerate() {
            assert_eq!(
                evaluate_at(&product, point),
                Fp::ZERO,
                "Z_W product did not vanish at data slot {index}"
            );
        }
        assert_eq!(
            circle_divide_data_vanishing(geom, &product, degree_bound).expect("exact Z_W quotient"),
            factor
        );

        let mut non_multiple = product;
        non_multiple[0] = non_multiple[0] + Fp::ONE;
        assert_eq!(
            circle_divide_data_vanishing(geom, &non_multiple, degree_bound),
            Err(CircleRsError::WrongMessageLength)
        );
    }

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

    /// Confirms basis consistency.
    ///
    /// IFFT coefficients must reproduce window data.
    /// Codeword FFT and direct basis evaluation must agree.
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
            for (c, &expected) in data.iter().enumerate() {
                assert_eq!(
                    evaluate_at(&coefficients, window.tables.domain[c]),
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
            for (c, &expected) in weights.iter().enumerate() {
                assert_eq!(evaluate_at(&w_coeffs, window.tables.domain[c]), expected);
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

    /// Confirms that product-domain and codeword-domain coefficients agree.
    ///
    /// The basis is domain independent.
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

    /// Confirms that `basis_sums` matches direct window evaluation.
    ///
    /// The fallback for longer inputs must also match.
    #[test]
    fn data_sum_fast_path_matches_direct_evaluation() {
        let mut state = 0x5A5Au64;
        for geom in GEOMS {
            let direct = |coeffs: &[Fp]| {
                data_window(geom)
                    .tables
                    .domain
                    .iter()
                    .fold(Fp::ZERO, |acc, &point| acc + evaluate_at(coeffs, point))
            };
            // Fast path: lengths from 0 up to the precomputed product domain.
            for len in [0usize, 1, 2, 3, geom.data_slots, geom.product_domain_len] {
                let coeffs = rand_row(&mut state, len);
                assert_eq!(
                    circle_data_sum(geom, &coeffs),
                    direct(&coeffs),
                    "fast-path len {len} geom {geom:?}"
                );
            }
            // Fallback path: longer than basis_sums.
            let long = rand_row(&mut state, geom.product_domain_len + 5);
            assert_eq!(
                circle_data_sum(geom, &long),
                direct(&long),
                "fallback geom {geom:?}"
            );
        }
    }

    #[test]
    fn encode_rejects_bad_lengths() {
        let geom = PRODUCT_CIRCLE_GEOM;
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
        assert!(circle_encode_row(geom, &vec![Fp::ONE; geom.data_slots + 1], || Fp::ZERO).is_err());
    }
}
