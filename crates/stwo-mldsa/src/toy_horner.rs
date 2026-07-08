//! DE-RISKING SPIKE (M4 plan risk: framework friction). NOT production code.
//!
//! Confirms the one load-bearing unknown before building `mldsa_coeffs`: that
//! stwo can express a **bivariate Horner accumulator over challenges (r,s) drawn
//! AFTER the base commit**, living in the interaction tree, with a group-boundary
//! reset and a per-group claimed evaluation emitted into a relation — the exact
//! shape the worksheet §3.2 needs. Modeled on `stwo-p256`'s gamma_digest gadget.
//!
//! Toy: two polynomials, each 4 coefficients, each coefficient carrying 2 digits.
//! Per row we form `digit_row(s) = d0 + d1·s`, and accumulate
//! `acc' = (1−start)·acc_prev·r + digit_row(s)` (Horner in r). At each group end
//! the accumulator equals `P̂(r,s) = Σ_m (d0_m + d1_m·s)·r^(M−1−m)`, emitted into
//! an `EvalAtRs` relation. A trivial native check re-folds the two claimed evals.
//!
//! If this proves+verifies, the framework can express the real gadget. Delete
//! after M4 lands.

#![allow(clippy::needless_range_loop)]

use num_traits::{One, Zero};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::core::pcs::PcsConfig;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof::StarkProof;
use stwo::core::utils::{bit_reverse_index, coset_index_to_circle_domain_index};
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;
use stwo::core::verifier::VerificationError;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{ComponentProver, ProvingError, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator, INTERACTION_TRACE_IDX,
};

use air_core::{Air, AirProver, PreprocessedColumnFingerprint, TreeLayout};

const N_POLYS: usize = 2;
const N_COEFFS: usize = 4;
const N_DIGITS: usize = 2;
const ACTIVE_ROWS: usize = N_POLYS * N_COEFFS; // 8
const LOG_SIZE: u32 = LOG_N_LANES; // 16 rows ≥ 8 active

/// `(poly_id, e0, e1, e2, e3)` — the claimed QM31 eval as 4 M31 coords.
const EVAL_ARITY: usize = 1 + SECURE_EXTENSION_DEGREE;
relation!(EvalAtRs, EVAL_ARITY);

type ColEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;

fn m31(v: u32) -> M31 {
    M31::from_u32_unchecked(v)
}

fn col_eval(values: Vec<M31>) -> ColEval {
    let rows = 1usize << LOG_SIZE;
    let mut ordered = vec![m31(0); rows];
    for (coset, v) in values.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset, LOG_SIZE),
            LOG_SIZE,
        );
        ordered[row] = v;
    }
    CircleEvaluation::new(CanonicCoset::new(LOG_SIZE).circle_domain(), BaseColumn::from_iter(ordered))
}

/// Digit tables: `digits[poly][coeff][digit]`.
fn toy_digits() -> [[[M31; N_DIGITS]; N_COEFFS]; N_POLYS] {
    let mut d = [[[m31(0); N_DIGITS]; N_COEFFS]; N_POLYS];
    for p in 0..N_POLYS {
        for c in 0..N_COEFFS {
            for k in 0..N_DIGITS {
                d[p][c][k] = m31((7 * p + 3 * c + 11 * k + 1) as u32 % 97);
            }
        }
    }
    d
}

/// Native `P̂(r,s) = Σ_m (d0_m + d1_m·s)·r^(M−1−m)`.
fn native_eval(poly: &[[M31; N_DIGITS]; N_COEFFS], r: SecureField, s: SecureField) -> SecureField {
    let mut acc = SecureField::zero();
    for coeff in poly.iter() {
        let digit_row = SecureField::from(coeff[0]) + SecureField::from(coeff[1]) * s;
        acc = acc * r + digit_row;
    }
    acc
}

// ── preprocessed selectors ──

fn pre_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId { id: format!("toy_horner_{name}") }
}

fn pre_ids() -> Vec<PreProcessedColumnId> {
    ["start", "end", "poly_id"].into_iter().map(pre_id).collect()
}

fn gen_preprocessed() -> Vec<ColEval> {
    let rows = 1usize << LOG_SIZE;
    let mut start = vec![m31(0); rows];
    let mut end = vec![m31(0); rows];
    let mut poly_id = vec![m31(0); rows];
    for row in 0..ACTIVE_ROWS {
        start[row] = m31(u32::from(row % N_COEFFS == 0));
        end[row] = m31(u32::from(row % N_COEFFS == N_COEFFS - 1));
        poly_id[row] = m31((row / N_COEFFS) as u32);
    }
    [start, end, poly_id].into_iter().map(col_eval).collect()
}

fn gen_base(digits: &[[[M31; N_DIGITS]; N_COEFFS]; N_POLYS]) -> Vec<ColEval> {
    let rows = 1usize << LOG_SIZE;
    let mut enabler = vec![m31(0); rows];
    let mut d0 = vec![m31(0); rows];
    let mut d1 = vec![m31(0); rows];
    for row in 0..ACTIVE_ROWS {
        let (p, c) = (row / N_COEFFS, row % N_COEFFS);
        enabler[row] = m31(1);
        d0[row] = digits[p][c][0];
        d1[row] = digits[p][c][1];
    }
    [enabler, d0, d1].into_iter().map(col_eval).collect()
}

#[derive(Clone)]
struct ToyEval {
    r: SecureField,
    s: SecureField,
    eval_rel: EvalAtRs,
}

impl FrameworkEval for ToyEval {
    fn log_size(&self) -> u32 {
        LOG_SIZE
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        LOG_SIZE + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let start = eval.get_preprocessed_column(pre_id("start"));
        let end = eval.get_preprocessed_column(pre_id("end"));
        let poly_id = eval.get_preprocessed_column(pre_id("poly_id"));
        let _enabler = eval.next_trace_mask();
        let d0 = eval.next_trace_mask();
        let d1 = eval.next_trace_mask();

        let coords: [[E::F; 2]; SECURE_EXTENSION_DEGREE] =
            core::array::from_fn(|_| eval.next_interaction_mask(INTERACTION_TRACE_IDX, [-1, 0]));
        let acc_prev = E::combine_ef(coords.each_ref().map(|pair| pair[0].clone()));
        let acc = E::combine_ef(coords.each_ref().map(|pair| pair[1].clone()));

        // acc = (1 − start)·acc_prev·r + (d0 + d1·s). Degree 2 (r,s constants).
        let one = E::F::from(M31::one());
        let digit_row = E::EF::from(d0) + E::EF::from(self.s) * E::EF::from(d1);
        let expected = E::EF::from(one - start.clone()) * acc_prev * E::EF::from(self.r) + digit_row;
        eval.add_constraint(acc.clone() - expected);

        // YIELD the claimed eval at each group end (negative = supply). The
        // verifier-native fold USES (positive) the same tuple, so the two cancel
        // iff the committed accumulator equals the natively-recomputed eval.
        let mut tuple = Vec::with_capacity(EVAL_ARITY);
        tuple.push(poly_id);
        tuple.extend(coords.iter().map(|pair| pair[1].clone()));
        eval.add_to_relation(RelationEntry::base(&self.eval_rel, -end, &tuple));

        eval.finalize_logup();
        eval
    }
}

fn gen_interaction(
    digits: &[[[M31; N_DIGITS]; N_COEFFS]; N_POLYS],
    r: SecureField,
    s: SecureField,
    eval_rel: &EvalAtRs,
) -> (Vec<ColEval>, SecureField, Vec<SecureField>) {
    let rows = 1usize << LOG_SIZE;
    // Accumulator chain (coset order).
    let mut acc = vec![SecureField::zero(); rows];
    for row in 0..rows {
        // Reset ONLY where the preprocessed `start` column is 1 (active group
        // heads). Padding rows keep multiplying the chain by r (start = 0), which
        // is exactly what the ungated constraint enforces. Coset row 0 is a group
        // head, so its `[-1]` wrap is killed by start = 1 regardless.
        let start = row < ACTIVE_ROWS && row % N_COEFFS == 0;
        let prev = if start || row == 0 { SecureField::zero() } else { acc[row - 1] };
        let (active, digit_row) = if row < ACTIVE_ROWS {
            let (p, c) = (row / N_COEFFS, row % N_COEFFS);
            (
                true,
                SecureField::from(digits[p][c][0]) + SecureField::from(digits[p][c][1]) * s,
            )
        } else {
            (false, SecureField::zero())
        };
        acc[row] = if active { prev * r + digit_row } else { prev * r };
    }
    let mut group_evals = Vec::new();
    for p in 0..N_POLYS {
        group_evals.push(acc[p * N_COEFFS + N_COEFFS - 1]);
    }

    let mut trace: Vec<ColEval> = (0..SECURE_EXTENSION_DEGREE)
        .map(|coord| col_eval(acc.iter().map(|v| v.to_m31_array()[coord]).collect()))
        .collect();

    // Logup: one digest use per group-end row.
    // Map circle-domain rows → coset for packing.
    let vec_rows = 1usize << (LOG_SIZE - LOG_N_LANES);
    let mut row_lookup = vec![0usize; rows];
    for coset in 0..rows {
        let dr = bit_reverse_index(coset_index_to_circle_domain_index(coset, LOG_SIZE), LOG_SIZE);
        row_lookup[dr] = coset;
    }
    use stwo::prover::backend::simd::m31::N_LANES;
    use stwo::prover::backend::simd::qm31::PackedQM31;
    let one = SecureField::one();
    let zero = SecureField::zero();
    let mut numerators = Vec::with_capacity(vec_rows);
    let mut denominators = Vec::with_capacity(vec_rows);
    let mut claimed = zero;
    for vr in 0..vec_rows {
        let mut num = [zero; N_LANES];
        let mut den = [one; N_LANES];
        for lane in 0..N_LANES {
            let coset = row_lookup[vr * N_LANES + lane];
            let is_end = coset < ACTIVE_ROWS && coset % N_COEFFS == N_COEFFS - 1;
            let poly_id = (coset / N_COEFFS) as u32;
            let coords = acc[coset].to_m31_array();
            let tuple = [m31(poly_id), coords[0], coords[1], coords[2], coords[3]];
            let d: SecureField = eval_rel.combine(&tuple);
            // YIELD (negative numerator) — mirrors the AIR's `-end`.
            num[lane] = if is_end { -one } else { zero };
            den[lane] = d;
            if is_end {
                claimed += -one / d;
            }
        }
        numerators.push(PackedQM31::from_array(num));
        denominators.push(PackedQM31::from_array(den));
    }
    let mut logup = LogupTraceGenerator::new(LOG_SIZE);
    let mut col = logup.new_col();
    for vr in 0..vec_rows {
        col.write_frac(vr, numerators[vr], denominators[vr]);
    }
    col.finalize_col();
    let (logup_trace, claimed_sum) = logup.finalize_last();
    trace.extend(logup_trace);
    assert_eq!(claimed_sum, claimed);
    (trace, claimed_sum, group_evals)
}

// ── air-core module ──

pub struct ToyModule {
    digits: [[[M31; N_DIGITS]; N_COEFFS]; N_POLYS],
    r: SecureField,
    s: SecureField,
    eval_rel: Option<EvalAtRs>,
    claimed_sum: Option<SecureField>,
    component: Option<FrameworkComponent<ToyEval>>,
    /// Native provider term: the verifier folds the two claimed evals and
    /// balances the AIR's group-end yields by requiring them here.
    native_use_sum: Option<SecureField>,
}

impl ToyModule {
    fn new(digits: [[[M31; N_DIGITS]; N_COEFFS]; N_POLYS]) -> Self {
        Self {
            digits,
            r: SecureField::zero(),
            s: SecureField::zero(),
            eval_rel: None,
            claimed_sum: None,
            component: None,
            native_use_sum: None,
        }
    }
}

impl Air for ToyModule {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(N_POLYS as u64);
    }
    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        // r, s drawn AFTER the base commit (air-core calls this post tree-1).
        self.r = channel.draw_secure_felt();
        self.s = channel.draw_secure_felt();
        self.eval_rel = Some(EvalAtRs::draw(channel));
    }
    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![LOG_SIZE; pre_ids().len()],
            trace: vec![LOG_SIZE; 3],
            interaction: vec![LOG_SIZE; SECURE_EXTENSION_DEGREE * 2],
        }
    }
    fn claimed_sums(&self) -> Vec<SecureField> {
        // The AIR's group-end yields (claimed_sum) plus the native fold's uses
        // (native_use_sum). They must cancel: native re-consumes each eval.
        vec![
            self.claimed_sum.expect("interaction written"),
            self.native_use_sum.expect("native fold computed"),
        ]
    }
    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        pre_ids()
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.component = Some(FrameworkComponent::new(
            allocator,
            ToyEval {
                r: self.r,
                s: self.s,
                eval_rel: self.eval_rel.clone().expect("relations drawn"),
            },
            self.claimed_sum.expect("interaction written"),
        ));
    }
    fn components(&self) -> Vec<&dyn Component> {
        vec![self.component.as_ref().expect("built")]
    }
}

impl AirProver for ToyModule {
    fn max_log_size(&self) -> u32 {
        LOG_SIZE
    }
    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(gen_preprocessed());
    }
    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        air_core::fingerprint_preprocessed_columns("ToyModule", &pre_ids(), &gen_preprocessed())
    }
    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(gen_base(&self.digits));
    }
    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let eval_rel = self.eval_rel.clone().expect("relations drawn");
        let (trace, claimed_sum, group_evals) =
            gen_interaction(&self.digits, self.r, self.s, &eval_rel);
        tb.extend_evals(trace);
        self.claimed_sum = Some(claimed_sum);
        // Native fold: the verifier recomputes each poly's eval and requires it
        // (positive sign) — cancelling the AIR's group-end yield (negative). If
        // the AIR's committed acc disagrees with native_eval, the sums don't
        // cancel and air-core rejects.
        let one = SecureField::one();
        let mut native = SecureField::zero();
        for (p, claimed) in group_evals.iter().enumerate() {
            let native_val = native_eval(&self.digits[p], self.r, self.s);
            assert_eq!(*claimed, native_val, "toy: AIR eval must match native");
            let coords = native_val.to_m31_array();
            let tuple = [m31(p as u32), coords[0], coords[1], coords[2], coords[3]];
            let denom: SecureField = eval_rel.combine(&tuple);
                native += one / denom;
        }
        self.native_use_sum = Some(native);
    }
    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![self.component.as_ref().expect("built")]
    }
}

pub fn toy_prove() -> Result<(StarkProof<Blake2sMerkleHasher>, PcsConfig), ProvingError> {
    let config = PcsConfig::default();
    let mut module = ToyModule::new(toy_digits());
    let proof = air_core::prove(&mut [&mut module], config)?;
    Ok((proof, config))
}

pub fn toy_verify(proof: &StarkProof<Blake2sMerkleHasher>) -> Result<(), VerificationError> {
    // Verifier re-derives r,s in draw_relations and re-folds natively; it needs
    // the digits publicly here (in the toy they're a fixed constant).
    let mut module = ToyModule::new(toy_digits());
    // The verifier must reproduce claimed_sum + native_use_sum. It has no
    // interaction trace, so it recomputes both from the public digits after
    // drawing r,s. We stash them in a pre-pass mirroring the prover.
    // Simplest: run the same interaction-gen (verifier knows digits publicly).
    module.claimed_sum = Some(SecureField::zero()); // placeholder, filled below
    // We reuse the Air trait's draw ordering by letting air_core::verify call
    // draw_relations, but claimed_sums must be known before that. So precompute:
    let mut channel = Blake2sChannel::default();
    proof.config.mix_into(&mut channel);
    // Mirror air_core::verify's pre-relation transcript is complex; instead the
    // toy verifier recomputes sums inside a wrapper module below.
    let _ = &mut module;
    let _ = channel;
    toy_verify_inner(proof)
}

/// Verifier that recomputes both claimed sums from public digits.
fn toy_verify_inner(proof: &StarkProof<Blake2sMerkleHasher>) -> Result<(), VerificationError> {
    struct V {
        digits: [[[M31; N_DIGITS]; N_COEFFS]; N_POLYS],
        r: SecureField,
        s: SecureField,
        eval_rel: Option<EvalAtRs>,
        claimed_sum: SecureField,
        native_use_sum: SecureField,
        component: Option<FrameworkComponent<ToyEval>>,
    }
    impl Air for V {
        fn mix_public(&self, channel: &mut Blake2sChannel) {
            channel.mix_u64(N_POLYS as u64);
        }
        fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
            self.r = channel.draw_secure_felt();
            self.s = channel.draw_secure_felt();
            let eval_rel = EvalAtRs::draw(channel);
            // Recompute both sums now that r,s,rel are known.
            let (_trace, claimed_sum, group_evals) =
                gen_interaction(&self.digits, self.r, self.s, &eval_rel);
            self.claimed_sum = claimed_sum;
            let one = SecureField::one();
            let mut native = SecureField::zero();
            for (p, _claimed) in group_evals.iter().enumerate() {
                let native_val = native_eval(&self.digits[p], self.r, self.s);
                let coords = native_val.to_m31_array();
                let tuple = [m31(p as u32), coords[0], coords[1], coords[2], coords[3]];
                let denom: SecureField = eval_rel.combine(&tuple);
                native += one / denom;
            }
            self.native_use_sum = native;
            self.eval_rel = Some(eval_rel);
        }
        fn layout(&self) -> TreeLayout {
            TreeLayout {
                preprocessed: vec![LOG_SIZE; pre_ids().len()],
                trace: vec![LOG_SIZE; 3],
                interaction: vec![LOG_SIZE; SECURE_EXTENSION_DEGREE * 2],
            }
        }
        fn claimed_sums(&self) -> Vec<SecureField> {
            vec![self.claimed_sum, self.native_use_sum]
        }
        fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
            pre_ids()
        }
        fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
            self.component = Some(FrameworkComponent::new(
                allocator,
                ToyEval { r: self.r, s: self.s, eval_rel: self.eval_rel.clone().unwrap() },
                self.claimed_sum,
            ));
        }
        fn components(&self) -> Vec<&dyn Component> {
            vec![self.component.as_ref().unwrap()]
        }
    }
    let mut v = V {
        digits: toy_digits(),
        r: SecureField::zero(),
        s: SecureField::zero(),
        eval_rel: None,
        claimed_sum: SecureField::zero(),
        native_use_sum: SecureField::zero(),
        component: None,
    };
    air_core::verify(&mut [&mut v], proof)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn toy_bivariate_horner_proves_and_verifies() {
        let (proof, _config) = toy_prove().expect("prove");
        toy_verify(&proof).expect("verify");
    }

    #[test]
    fn toy_tampered_eval_rejected() {
        // Sanity: if we forge one digit on the verifier's public side only, the
        // native fold no longer matches the committed acc ⇒ sums don't cancel.
        let (proof, _config) = toy_prove().expect("prove");
        // Re-verify with mutated digits inside a bespoke verifier.
        struct V2 {
            r: SecureField,
            s: SecureField,
            eval_rel: Option<EvalAtRs>,
            claimed_sum: SecureField,
            native_use_sum: SecureField,
            component: Option<FrameworkComponent<ToyEval>>,
        }
        impl Air for V2 {
            fn mix_public(&self, channel: &mut Blake2sChannel) {
                channel.mix_u64(N_POLYS as u64);
            }
            fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
                self.r = channel.draw_secure_felt();
                self.s = channel.draw_secure_felt();
                let eval_rel = EvalAtRs::draw(channel);
                // Honest committed side.
                let (_t, claimed_sum, _g) = gen_interaction(&toy_digits(), self.r, self.s, &eval_rel);
                self.claimed_sum = claimed_sum;
                // FORGED native side: flip one digit.
                let mut forged = toy_digits();
                forged[1][2][0] = m31(forged[1][2][0].0 ^ 1);
                let one = SecureField::one();
                let mut native = SecureField::zero();
                for p in 0..N_POLYS {
                    let native_val = native_eval(&forged[p], self.r, self.s);
                    let coords = native_val.to_m31_array();
                    let tuple = [m31(p as u32), coords[0], coords[1], coords[2], coords[3]];
                    let denom: SecureField = eval_rel.combine(&tuple);
                native += one / denom;
                }
                self.native_use_sum = native;
                self.eval_rel = Some(eval_rel);
            }
            fn layout(&self) -> TreeLayout {
                TreeLayout {
                    preprocessed: vec![LOG_SIZE; pre_ids().len()],
                    trace: vec![LOG_SIZE; 3],
                    interaction: vec![LOG_SIZE; SECURE_EXTENSION_DEGREE * 2],
                }
            }
            fn claimed_sums(&self) -> Vec<SecureField> {
                vec![self.claimed_sum, self.native_use_sum]
            }
            fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
                pre_ids()
            }
            fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
                self.component = Some(FrameworkComponent::new(
                    allocator,
                    ToyEval { r: self.r, s: self.s, eval_rel: self.eval_rel.clone().unwrap() },
                    self.claimed_sum,
                ));
            }
            fn components(&self) -> Vec<&dyn Component> {
                vec![self.component.as_ref().unwrap()]
            }
        }
        let mut v = V2 {
            r: SecureField::zero(),
            s: SecureField::zero(),
            eval_rel: None,
            claimed_sum: SecureField::zero(),
            native_use_sum: SecureField::zero(),
            component: None,
        };
        let res = air_core::verify(&mut [&mut v], &proof);
        assert!(res.is_err(), "forged native fold must be rejected");
    }
}
