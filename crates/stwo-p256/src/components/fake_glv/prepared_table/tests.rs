//! Tests for the prepared-table AIR family.
//!
//! Relocated verbatim out of `mod.rs` (test module body, dedented one level).

use super::*;
use crate::constants::{P256_GX, P256_GY};
use crate::limbs::P256M31BigInt;
use crate::prepared_point::PreparedPointUseCountClaim;
use crate::public_inputs::PublicEcdsaInputClaim;
use crate::scalar::cert_bind::{CertScalarInputClaim, CERT_ID_U1_GENERATOR, CERT_ID_U2_PUBLIC_KEY};
use crate::scalar::fake_glv_scalar::{FakeGlvScalarHint, FakeGlvScalarHintClaim};
use crate::scalar::fake_glv_selector::FakeGlvSelectorClaim;
use crate::scalar::fake_glv_selector_lookup::Selector16DecodeEntry;
use crate::scalar::scalar_mod_mul::columns::M31ColumnEval;
use crate::scalar::setup_air::ScalarSetupClaim;
use crate::types::{AffinePoint, Signature, U256};
use stwo::core::channel::Blake2sChannel;
use stwo::core::poly::circle::CanonicCoset;
use stwo_constraint_framework::{assert_constraints_on_polys, FrameworkEval};

fn test_input(message_hash: u64, r: u64, s: u64) -> crate::types::EcdsaVerifyInput {
    crate::types::EcdsaVerifyInput {
        message_hash: scalar(message_hash),
        signature: Signature {
            r: scalar(r),
            s: scalar(s),
        },
        public_key: AffinePoint {
            x: U256::from_le_u64s(&P256_GX),
            y: U256::from_le_u64s(&P256_GY),
        },
    }
}

fn scalar(value: u64) -> U256 {
    U256::from_le_u64s(&[value, 0, 0, 0])
}

fn build_table(
    message_hash: u64,
) -> (
    CertScalarInputClaim,
    FakeGlvScalarHintClaim,
    FakeGlvSelectorClaim,
    PreparedTableClaim,
) {
    let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(message_hash, 77, 1)]);
    let scalar_setup =
        ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
    let certs =
        CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
    let hints = certs
        .rows
        .iter()
        .map(|row| FakeGlvScalarHint::trivial_for_small_scalar(&row.scalar).unwrap())
        .collect();
    let fake_glv =
        FakeGlvScalarHintClaim::from_cert_inputs(&certs, hints).expect("valid hints");
    let selectors =
        FakeGlvSelectorClaim::from_scalar_hints(&fake_glv).expect("valid selectors");
    let table =
        PreparedTableClaim::from_claims(&certs, &fake_glv, &selectors).expect("valid table");
    (certs, fake_glv, selectors, table)
}

#[test]
fn prepared_table_generates_active_base_and_table16_points() {
    let (_, _, _, table) = build_table(42);

    assert_eq!(table.certs.len(), 2);
    for cert in &table.certs {
        assert_eq!(cert.cert_active.0, 1);
        for point in &cert.base {
            point.verify().expect("base point is canonical");
        }
        assert_eq!(cert.r3.inf.0, 0);
        assert_eq!(cert.table16.inf.0, 0);
    }
}

#[test]
fn prepared_table_table16_matches_selector0_plus_r3() {
    let (_, _, selectors, table) = build_table(42);

    for (selector, cert) in selectors.rows.iter().zip(&table.certs) {
        let decoded = Selector16DecodeEntry::from_selector(selector.selectors[0]).unwrap();
        let selected = apply_selector(&cert.base, decoded).unwrap();
        let expected = prepared(add_optional_points(
            selected.to_option(),
            cert.r3.to_option(),
        ));

        assert_eq!(cert.table16, expected);
    }
}

#[test]
fn prepared_table_inactive_cert_is_canonical_infinity() {
    let (_, _, _, table) = build_table(0);

    assert_eq!(table.certs[0].cert_active.0, 0);
    assert_eq!(
        table.certs[0].base,
        core::array::from_fn(|_| PreparedAffinePoint::infinity())
    );
    assert_eq!(table.certs[0].r3, PreparedAffinePoint::infinity());
    assert_eq!(table.certs[0].table16, PreparedAffinePoint::infinity());
    assert_eq!(table.certs[1].cert_active.0, 1);
}

#[test]
fn prepared_table_ec_trace_records_expected_active_rows() {
    let (certs, fake_glv, selectors, table) = build_table(42);
    let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
        .expect("valid ec trace");

    trace.verify().expect("ec trace verifies");
    assert_eq!(trace.active_row_count(), 24);
    assert!(trace
        .rows
        .iter()
        .any(|row| row.kind == PreparedTableEcRowKind::Base(0)));
    assert!(trace
        .rows
        .iter()
        .any(|row| row.kind == PreparedTableEcRowKind::Table16));
}

#[test]
fn prepared_table_ec_trace_skips_inactive_zero_branch() {
    let (certs, fake_glv, selectors, table) = build_table(0);
    let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
        .expect("valid ec trace");

    assert_eq!(table.certs[0].cert_active.0, 0);
    assert_eq!(trace.active_row_count(), 13);
    assert!(trace
        .rows
        .iter()
        .all(|row| row.cert_id == table.certs[1].cert_id));
}

#[test]
fn prepared_table_ec_trace_detects_mutated_output() {
    let (certs, fake_glv, selectors, table) = build_table(42);
    let mut trace =
        PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
            .expect("valid ec trace");
    trace.rows[0].output = PreparedAffinePoint::infinity();

    let err = trace.verify().expect_err("mutated output must fail");

    assert!(matches!(
        err,
        PreparedTableError::EcTraceOutputMismatch { .. }
    ));
}

#[test]
fn prepared_table_ec_trace_links_outputs_to_table_points() {
    let (certs, fake_glv, selectors, table) = build_table(42);
    let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
        .expect("valid ec trace");

    trace
        .verify_against_table(&table)
        .expect("ec trace outputs match table points");
}

#[test]
fn prepared_table_ec_row_constraints_pass_for_honest_trace() {
    let (certs, fake_glv, selectors, table) = build_table(42);
    let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
        .expect("valid ec trace");
    let claim = PreparedTableEcRowProofClaim::from_trace(&trace);
    let ids = claim.preprocessed_column_ids();
    let preprocessed =
        gen_prepared_table_ec_row_preprocessed_trace(claim.log_size, 0, &ids).unwrap();
    let base = gen_prepared_table_ec_row_base_trace(&trace, claim.log_size).unwrap();
    let mut channel = Blake2sChannel::default();
    let relation = PreparedTableEcRowRelation::draw(&mut channel);
    let (interaction, interaction_claim) =
        gen_prepared_table_ec_row_interaction_trace(&base, &relation);
    let trace_polys = TreeVec::new(vec![preprocessed, base, interaction]).map(|trace| {
        trace
            .into_iter()
            .map(|column| column.interpolate())
            .collect::<Vec<_>>()
    });

    assert_constraints_on_polys(
        &trace_polys,
        CanonicCoset::new(claim.log_size),
        |eval| {
            PreparedTableEcRowEval {
                log_size: claim.log_size,
                relation: relation.clone(),
                pinning: None,
            }
            .evaluate(eval);
        },
        interaction_claim.claimed_sum,
    );
}

#[test]
fn prepared_table_ec_trace_detects_mutated_table_output_link() {
    let (certs, fake_glv, selectors, mut table) = build_table(42);
    let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
        .expect("valid ec trace");
    table.certs[0].base[0] = PreparedAffinePoint::infinity();

    let err = trace
        .verify_against_table(&table)
        .expect_err("mutated table output link must fail");

    assert!(matches!(
        err,
        PreparedTableError::EcTraceExpectedOutputMismatch { label: "Base", .. }
    ));
}

#[test]
fn prepared_table_prepared_point_trace_matches_table_and_use_counts() {
    let (_, _, selectors, table) = build_table(42);
    let use_counts =
        PreparedPointUseCountClaim::from_selector_claim(&selectors).expect("valid counts");
    let prepared_trace = table
        .prepared_point_trace(&use_counts)
        .expect("prepared trace generates");

    table
        .verify_prepared_point_trace(&use_counts, &prepared_trace)
        .expect("prepared providers match table");
}

#[test]
fn prepared_table_prepared_point_trace_detects_mutated_provider() {
    let (_, _, selectors, table) = build_table(42);
    let use_counts =
        PreparedPointUseCountClaim::from_selector_claim(&selectors).expect("valid counts");
    let mut prepared_trace = table
        .prepared_point_trace(&use_counts)
        .expect("prepared trace generates");
    prepared_trace.providers[0].instance.x = P256M31BigInt::zero();

    let err = table
        .verify_prepared_point_trace(&use_counts, &prepared_trace)
        .expect_err("mutated provider must fail");

    assert_eq!(err, PreparedTableError::PreparedPointTraceMismatch);
}

// --- Full-table pinning adversarial audits (rejection oracle = relation
// balance, lessons.md #18). The honest table must keep `CertBase` and
// `PreparedTableCanonical` balanced; a wrong base or inconsistent operand
// must imbalance the matching relation. ---

/// Draw the three pinning relations from one channel and compute, for the
/// given (possibly mutated) EC base trace + cert base trace, the
/// `CertBase` and `PreparedTableCanonical` net sums (zero iff balanced).
fn pinned_relation_balances(
    certs: &CertScalarInputClaim,
    ec_base: &[M31ColumnEval],
    scalar_setup: &crate::scalar::setup_air::ScalarSetupClaim,
) -> (SecureField, SecureField) {
    use crate::scalar::cert_bind::{
        debug_cert_scalar_input_air_relation_sums, gen_cert_scalar_input_air_base_trace,
        CertScalarInputAirProofClaim,
    };

    let mut channel = Blake2sChannel::default();
    let cert_base = CertBaseRelation::draw(&mut channel);
    let prepared_table = PreparedTableEcRowRelation::draw(&mut channel);
    let canonical = PreparedTableCanonicalRelation::draw(&mut channel);

    let cert_claim = CertScalarInputAirProofClaim::from_claim(scalar_setup);
    let cert_base_trace =
        gen_cert_scalar_input_air_base_trace(scalar_setup, certs, cert_claim);
    let cert_sums =
        debug_cert_scalar_input_air_relation_sums(&cert_base_trace, Some(&cert_base));

    let (_, cert_base_consumer, canonical_claimed) = debug_prepared_table_pinned_relation_sums(
        ec_base,
        &prepared_table,
        &cert_base,
        &canonical,
    );

    (
        cert_base_consumer + cert_sums.cert_base_provider_claimed_sum,
        canonical_claimed,
    )
}

fn pinning_audit_fixture(
    message_hash: u64,
) -> (
    CertScalarInputClaim,
    crate::scalar::setup_air::ScalarSetupClaim,
    PreparedTableEcTraceClaim,
    u32,
) {
    use crate::scalar::setup_air::ScalarSetupClaim;
    let public_claim =
        PublicEcdsaInputClaim::from_inputs(&[test_input(message_hash, 77, 1)]);
    let scalar_setup =
        ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
    let certs =
        CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
    let hints = certs
        .rows
        .iter()
        .map(|row| FakeGlvScalarHint::trivial_for_small_scalar(&row.scalar).unwrap())
        .collect();
    let fake_glv =
        FakeGlvScalarHintClaim::from_cert_inputs(&certs, hints).expect("valid hints");
    let selectors =
        FakeGlvSelectorClaim::from_scalar_hints(&fake_glv).expect("valid selectors");
    let table =
        PreparedTableClaim::from_claims(&certs, &fake_glv, &selectors).expect("valid table");
    let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
        .expect("valid ec trace");
    let log_size = PreparedTableEcRowProofClaim::from_trace(&trace).log_size;
    (certs, scalar_setup, trace, log_size)
}

#[test]
fn pinning_honest_trace_balances_cert_base_and_canonical() {
    let (certs, scalar_setup, trace, log_size) = pinning_audit_fixture(42);
    let base = gen_prepared_table_ec_row_base_trace(&trace, log_size).unwrap();
    let (cert_base_balance, canonical_balance) =
        pinned_relation_balances(&certs, &base, &scalar_setup);
    assert_eq!(cert_base_balance, secure_zero(), "CertBase must balance");
    assert_eq!(
        canonical_balance,
        secure_zero(),
        "PreparedTableCanonical must balance"
    );
}

#[test]
fn pinning_honest_trace_balances_with_inactive_cert0_zero_branch() {
    // u1 == 0 => cert0 inactive: no cert0 EC rows, cert-base provider yields
    // `-4·cert_active = 0`. Both relations must still net to zero.
    let (certs, scalar_setup, trace, log_size) = pinning_audit_fixture(0);
    assert_eq!(certs.rows[0].cert_active.0, 0, "cert0 inactive in fixture");
    let base = gen_prepared_table_ec_row_base_trace(&trace, log_size).unwrap();
    let (cert_base_balance, canonical_balance) =
        pinned_relation_balances(&certs, &base, &scalar_setup);
    assert_eq!(cert_base_balance, secure_zero(), "CertBase must balance");
    assert_eq!(
        canonical_balance,
        secure_zero(),
        "PreparedTableCanonical must balance"
    );
}

/// Locate the `trace.rows` index for `(cert_id, kind)`.
fn find_row_index(
    trace: &PreparedTableEcTraceClaim,
    cert_id: u32,
    kind: PreparedTableEcRowKind,
) -> usize {
    trace
        .rows
        .iter()
        .position(|row| row.cert_id.0 == cert_id && row.kind == kind)
        .expect("row exists")
}

/// Add `1` to limb 0 of `point.x` (a self-consistent, off-cell mutation that
/// only the pinning relations can detect).
fn bump_x(point: &mut PreparedAffinePoint) {
    let mut limbs = *point.x.limbs();
    limbs[0] += M31::from_u32_unchecked(1);
    point.x = P256M31BigInt::from_limbs(limbs);
}

#[test]
fn pinning_rejects_cert0_prepared_p_not_equal_generator() {
    // cert0 base must equal G; mutating a cert0 P-cell (Base(1).lhs) away
    // from G leaves the CertBase consumer demanding a point the cert-base
    // provider never yields.
    let (certs, scalar_setup, mut trace, log_size) = pinning_audit_fixture(42);
    let row = find_row_index(&trace, CERT_ID_U1_GENERATOR, PreparedTableEcRowKind::Base(1));
    bump_x(&mut trace.rows[row].lhs);
    let base = gen_prepared_table_ec_row_base_trace(&trace, log_size).unwrap();
    let (cert_base_balance, _) = pinned_relation_balances(&certs, &base, &scalar_setup);
    assert_ne!(
        cert_base_balance,
        secure_zero(),
        "wrong cert0 base P must imbalance CertBase"
    );
}

#[test]
fn pinning_rejects_cert1_prepared_p_not_equal_public_key() {
    // cert1 base must equal the public key Q; mutating a cert1 P-cell
    // (Base(2).lhs) away from Q imbalances CertBase.
    let (certs, scalar_setup, mut trace, log_size) = pinning_audit_fixture(42);
    let row = find_row_index(&trace, CERT_ID_U2_PUBLIC_KEY, PreparedTableEcRowKind::Base(2));
    bump_x(&mut trace.rows[row].lhs);
    let base = gen_prepared_table_ec_row_base_trace(&trace, log_size).unwrap();
    let (cert_base_balance, _) = pinned_relation_balances(&certs, &base, &scalar_setup);
    assert_ne!(
        cert_base_balance,
        secure_zero(),
        "wrong cert1 base P must imbalance CertBase"
    );
}

#[test]
fn pinning_rejects_inconsistent_r_between_base_rows() {
    // Base(2).rhs and Base(3).rhs both consume canonical R. Mutating only
    // Base(2).rhs makes it demand an R the DoubleR provider never yields,
    // imbalancing PreparedTableCanonical.
    let (certs, scalar_setup, mut trace, log_size) = pinning_audit_fixture(42);
    let row = find_row_index(&trace, CERT_ID_U2_PUBLIC_KEY, PreparedTableEcRowKind::Base(2));
    bump_x(&mut trace.rows[row].rhs);
    let base = gen_prepared_table_ec_row_base_trace(&trace, log_size).unwrap();
    let (_, canonical_balance) = pinned_relation_balances(&certs, &base, &scalar_setup);
    assert_ne!(
        canonical_balance,
        secure_zero(),
        "inconsistent R must imbalance PreparedTableCanonical"
    );
}

/// Minimal recording `EvalAtRow` for `PreparedTableProjectiveSourceEval`: the
/// consumer reads only same-row base-trace masks (no preprocessed columns), so
/// this serves base columns by read order and records each polynomial
/// constraint instead of asserting. LogUp emissions are skipped — the C5-2
/// coordinate-formula pins are pure polynomial constraints, so a forge that
/// keeps every relation balanced (e.g. forging provider AND consumer in
/// lockstep) is still caught here. Mirrors
/// `projective_rcb_mul::tests::RecordingMulEvaluator` (lessons.md #18: no
/// `LogupAtRow`, so a violated constraint is a recorded non-zero, not an
/// uncatchable abort).
struct RecordingSourceEvaluator<'a> {
    base: &'a [Vec<M31>],
    col_index: usize,
    row: usize,
    constraints: Vec<stwo::core::fields::qm31::SecureField>,
}

impl stwo_constraint_framework::EvalAtRow for RecordingSourceEvaluator<'_> {
    type F = M31;
    type EF = stwo::core::fields::qm31::SecureField;

    fn next_interaction_mask<const N: usize>(
        &mut self,
        interaction: usize,
        offsets: [isize; N],
    ) -> [Self::F; N] {
        if interaction == stwo_constraint_framework::PREPROCESSED_TRACE_IDX {
            // The γ-digest row-index read: only used as a LogUp tuple value
            // (ignored by this recorder), never in a polynomial constraint.
            return offsets.map(|_| M31::from_u32_unchecked(self.row as u32));
        }
        assert_eq!(
            interaction, 1,
            "projective-source consumer reads only the base trace"
        );
        let col = self.col_index;
        self.col_index += 1;
        offsets.map(|offset| {
            assert_eq!(offset, 0, "projective-source consumer reads offset-0 masks");
            self.base[col][self.row]
        })
    }

    fn add_constraint<G>(&mut self, constraint: G)
    where
        Self::EF: std::ops::Mul<G, Output = Self::EF> + From<G>,
    {
        self.constraints.push(Self::EF::from(constraint));
    }

    fn combine_ef(values: [Self::F; 4]) -> Self::EF {
        Self::EF::from_m31_array(values)
    }

    fn add_to_relation<R: stwo_constraint_framework::Relation<Self::F, Self::EF>>(
        &mut self,
        _entry: stwo_constraint_framework::RelationEntry<'_, Self::F, Self::EF, R>,
    ) {
    }

    fn finalize_logup(&mut self) {}

    fn finalize_logup_in_pairs(&mut self) {}

    fn finalize_logup_batched(&mut self, _batching: &Vec<usize>) {}
}

/// Whether every polynomial constraint of `PreparedTableProjectiveSourceEval`
/// holds on all rows of the given base columns.
fn projective_source_constraints_hold(log_size: u32, base: &[Vec<M31>]) -> bool {
    use num_traits::Zero;
    for row in 0..(1usize << log_size) {
        let recorder = RecordingSourceEvaluator {
            base,
            col_index: 0,
            row,
            constraints: Vec::new(),
        };
        let recorder = PreparedTableProjectiveSourceEval {
            log_size,
            relation: PreparedTableEcRowRelation::dummy(),
            mul_result: crate::projective_air::ProjectiveRcbMulResultRelation::dummy(),
            gamma_digest: crate::components::gamma_digest::GammaDigestRelation::dummy(),
            gamma_challenge: super::trace::prepared_dummy_gamma_challenge(),
        }
        .evaluate(recorder);
        if recorder.constraints.iter().any(|value| !value.is_zero()) {
            return false;
        }
    }
    true
}

/// C5-2 binding isolation for the prepared table: forging a committed
/// `output_affine.x` limb on a Double / MixedAdd source row must violate the
/// coordinate-formula POLYNOMIAL constraints themselves — independent of any
/// LogUp relation, so a prover who forges the provider and consumer in lockstep
/// (keeping `PreparedTableProjectiveSource` balanced) is still rejected. Before
/// this change the source had "no coordinate constraints yet" and both forges
/// satisfied every polynomial constraint of the consumer.
#[test]
fn prepared_table_projective_source_rejects_forged_op_outputs() {
    use crate::scalar::scalar_mod_mul::columns::padded_log_size;

    let (certs, fake_glv, selectors, table) = build_table(42);
    let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
        .expect("valid ec trace");
    let fake_glv_ec = crate::fake_glv_chain::FakeGlvPrimitiveEcTraceClaim { rows: Vec::new() };
    let projective = crate::projective::ProjectiveEcTraceClaim::from_native_traces(
        &trace,
        &fake_glv_ec,
    )
    .expect("projective trace generates");
    let log_size = padded_log_size(trace.rows.len());
    let base: Vec<Vec<M31>> =
        gen_prepared_table_projective_source_base_trace(&trace, &projective, log_size)
            .expect("source base trace generates")
            .into_iter()
            .map(|column| column.to_cpu().values)
            .collect();

    assert!(
        projective_source_constraints_hold(log_size, &base),
        "honest prepared-table source trace must satisfy the polynomial constraints"
    );

    // Operand dedup moved the affine-normalization OPERAND binding (3a) out of
    // the polynomial constraints and into the consume tuples: M13.lhs's value
    // IS the committed `output.x`, pinned to the silo's proven operand by the
    // `ProjectiveRcbMulResult` balance. A forged `output.x` therefore no
    // longer trips a polynomial constraint — the oracle is the consumer's
    // mul-result sum drifting from the (unchanged) provider yield.
    let mut channel = stwo::core::channel::Blake2sChannel::default();
    let ec_row_relation = PreparedTableEcRowRelation::draw(&mut channel);
    let mul_result_relation =
        crate::projective_air::ProjectiveRcbMulResultRelation::draw(&mut channel);
    let gamma_digest_relation =
        crate::components::gamma_digest::GammaDigestRelation::draw(&mut channel);
    let gamma_challenge = super::trace::prepared_dummy_gamma_challenge();
    let consumer_mul_sum = |columns: &[Vec<M31>]| {
        let evals: Vec<_> = columns
            .iter()
            .map(|values| {
                crate::scalar::scalar_mod_mul::columns::m31_column_eval(log_size, values.clone())
            })
            .collect();
        super::interaction::gen_prepared_table_projective_source_consumer_interaction_trace(
            &evals,
            &ec_row_relation,
            &mul_result_relation,
            &gamma_digest_relation,
            &gamma_challenge,
        )
        .mul_result_sum
    };
    let honest_mul_sum = consumer_mul_sum(&base);

    let op_col = 4usize;
    let output_x0_col = 6 + 2 * PREPARED_TABLE_EC_POINT_COLUMNS;
    let rows = 1usize << log_size;
    for (op_code, op_name) in [
        (PREPARED_TABLE_EC_OP_DOUBLE, "Double"),
        (PREPARED_TABLE_EC_OP_MIXED_ADD, "MixedAdd"),
    ] {
        let forge_row = (0..rows)
            .find(|&row| {
                base[0][row] != M31::from_u32_unchecked(0)
                    && base[op_col][row] == M31::from_u32_unchecked(op_code)
            })
            .unwrap_or_else(|| panic!("table must contain an active {op_name} row"));
        let mut forged = base.clone();
        forged[output_x0_col][forge_row] =
            forged[output_x0_col][forge_row] + M31::from_u32_unchecked(1);
        assert_ne!(
            consumer_mul_sum(&forged),
            honest_mul_sum,
            "forged {op_name} output.x must drift the M13.lhs consume from the \
             silo provider's yield (ProjectiveRcbMulResult imbalance)"
        );
    }
}
